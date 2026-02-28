
#include <stdbool.h>        // for bool, true, false
#include <stdio.h>          // for fclose, fflush_unlocked, fopen, snprintf
#include <stdlib.h>         // for free
#include <string.h>         // for memcpy
#include <time.h>           // for clock, CLOCKS_PER_SEC, clock_t
#include <assert.h>         // asserts
#include <unistd.h>         // for write

#include "secret.h"
#include "trusted_utils.h"  // for trusted_utils_read_int, trusted_utils_log...
#include "checker_interface.h"
#include "confirm.h"        // for confirm_result
#include "hash.h"              // for hash_table_find
#include "siphash.h"

#if IMPCHECK_WRITE_DIRECTIVES
#include "../writer.h"
#endif

// Use this line to produce a text file qualified by the PID
// that logs all ffi calls.
// #define IMPCHECK_DEBUG_FILE

// Instantiate int_vec
#define TYPE int
#define TYPED(THING) int_ ## THING
#include "vec.h"
#undef TYPED
#undef TYPE

// Instantiate u64_vec
#define TYPE u64
#define TYPED(THING) u64_ ## THING
#include "vec.h"
#undef TYPED
#undef TYPE

FILE* input; // named pipe
FILE* output; // named pipe
int nb_vars; // # variables in formula
signature formula_sig; // formula signature

signature buf_sig;
struct int_vec* buf_lits;
struct u64_vec* orig_clauses;
u64 nb_loaded_clauses = 0;
struct int_vec* clause_to_add;
struct int_vec* vec_read_lits;

// State passed from ffistep to other FFIs
u64 fake_import_id;      // Next clause ID to replay in import phase
u64 last_eid;            // External ID from most recent ffistep
struct u64_vec* last_hints; // External hint IDs from most recent ffihints
int* last_cls_data;      // non-NULL during simulated import phase
int last_nb_lits;        // Expected clause size for next fficlause call
int last_read_directive_char;

struct hash_table* id_table;
struct u64_vec* id_queue;
u64 next_id_to_allocate;
u64 max_eid;

/* exported in cake.S */
extern int cml_main(void);
extern void *cml_heap;
extern void *cml_stack;
extern void *cml_stackend;

// Counters and error state, shared between tc_run and fficallback
u64 nb_produced, nb_imported, nb_deleted;
bool all_ok;
bool reported_error;

// These are unused
extern char cake_text_begin;
extern char cake_codebuffer_begin;
extern char cake_codebuffer_end;

#ifdef IMPCHECK_DEBUG_FILE
FILE* f_dbg;
#endif

void compute_clause_signature(u64 id, const int* lits, int nb_lits, u8* out) {
  siphash_reset();
  siphash_update((u8*) &id, sizeof(u64));
  siphash_update((u8*) lits, nb_lits*sizeof(int));
  siphash_update(formula_sig, SIG_SIZE_BYTES);
  const u8* hash_out = siphash_digest();
  trusted_utils_copy_bytes(out, hash_out, SIG_SIZE_BYTES);
}

void say(bool ok) {
#if IMPCHECK_WRITE_DIRECTIVES
    writer_flush();
#endif
    trusted_utils_write_char(ok ? TRUSTED_CHK_RES_ACCEPT : TRUSTED_CHK_RES_ERROR, output);
#if IMPCHECK_FLUSH_ALWAYS
    UNLOCKED_IO(fflush)(output);
#endif
}
void say_with_flush(bool ok) {
    say(ok);
    UNLOCKED_IO(fflush)(output);
}

void read_literals(int nb_lits) {
    int_vec_reserve(buf_lits, nb_lits);
    trusted_utils_read_ints(buf_lits->data, nb_lits, input);
}

void tc_init(const char* fifo_in, const char* fifo_out) {
    input = fopen(fifo_in, "r");
    if (!input) trusted_utils_exit_eof();
    output = fopen(fifo_out, "w");
    if (!output) trusted_utils_exit_eof();
    buf_lits = int_vec_init(1 << 14);
    vec_read_lits = int_vec_init(1024);
    last_hints = u64_vec_init(1 << 10);
    id_table = hash_table_init(10);
    id_queue = u64_vec_init(1024);
    next_id_to_allocate = 1;
}

void tc_end(void) {
    u64_vec_free(id_queue);
    hash_table_free(id_table, false);
    u64_vec_free(last_hints);
    int_vec_free(buf_lits);
    fclose(output);
    fclose(input);
}

void print_stats_at_exit(clock_t start) {
    float elapsed = (float) (clock() - start) / CLOCKS_PER_SEC;
    snprintf(trusted_utils_msgstr, 512, "cpu:%.3f prod:%lu imp:%lu del:%lu maxid=%lu",
      elapsed, nb_produced, nb_imported, nb_deleted, next_id_to_allocate-1);
    trusted_utils_log(trusted_utils_msgstr);
}

u64 external_to_internal_id(u64 eid) {
  // check if already mapped
  u64 existing = (u64)hash_table_find(id_table, eid);
  if (existing) return existing;
  if (eid > max_eid) max_eid = eid;
  // allocate a new internal ID
  u64 iid;
  if (id_queue->size == 0) {
    // allocate a new ID
    iid = next_id_to_allocate;
    next_id_to_allocate += 1;
  } else {
    // remove a previous ID from the queue
    iid = id_queue->data[id_queue->size - 1];
    id_queue->size--;
  }
  // remember the mapping!
  bool ok = hash_table_insert(id_table, eid, (void*)iid);
  assert(ok);
  return iid;
}
void free_id(u64 eid) {
  // delete mapping from the table
  u64 iid = (u64)hash_table_find(id_table, eid);
  assert(iid);
  bool ok = hash_table_delete_last_found(id_table);
  assert(ok);
  // push the now unused ID to the queue
  u64_vec_push(id_queue, iid);
}

int tc_run(bool check_model, bool lenient, long producer_id, long producer_count, int heap_megabytes) {
    clock_t start = clock();
    nb_produced = 0;
    nb_imported = 0;
    nb_deleted = 0;

    reported_error = false;

    // TODO: use ImpCheck's command line to set these
    unsigned long sz = 1024*1024; // 1 MB unit
    unsigned long cml_heap_sz = heap_megabytes * sz;    // Default: 1 GB heap
    unsigned long cml_stack_sz = 48 * sz;   // Default: 1 GB stack

    // Min sizes for CML heap and stack
    if(cml_heap_sz < sz || cml_stack_sz < sz || cml_heap_sz + cml_stack_sz < 8192)
    {
      // TODO: use proper ImpCheck exit mechanism
      #ifdef STDERR_MEM_EXHAUST
      fprintf(stderr,"Too small requested heap (%lu) or stack (%lu) size in bytes.\n",cml_heap_sz, cml_stack_sz);
      #endif
      exit(3);
    }

    cml_heap = malloc(cml_heap_sz + cml_stack_sz); // allocate both heap and stack at once

    if(cml_heap == NULL)
    {
      #ifdef STDERR_MEM_EXHAUST
      fprintf(stderr,"failed to allocate sufficient CakeML heap and stack space.\n");
      perror("malloc");
      #endif
      exit(3);
    }

    cml_stack = (char*)cml_heap + cml_heap_sz;
    cml_stackend = (char*)cml_stack + cml_stack_sz;

#ifdef IMPCHECK_DEBUG_FILE
    char fname_dbg[512];
    fname_dbg[511] = '\0';
    snprintf(fname_dbg, 511, "impchkdbg.%i", getpid());
    f_dbg = fopen(fname_dbg, "w");
#endif

    // Formula loading phase (INIT, LOAD, END_LOAD) handled in C
    bool ended_loading = false;
    all_ok = true;
    while (true) {
        last_read_directive_char = trusted_utils_read_char(input);
        int c = last_read_directive_char;
        if (c == TRUSTED_CHK_INIT) {

            nb_vars = trusted_utils_read_int(input);
            siphash_init(SECRET_KEY);
            orig_clauses = u64_vec_init(4096);
            clause_to_add = int_vec_init(512);

            trusted_utils_read_sig(formula_sig, input);
            say_with_flush(true);

        } else if (c == TRUSTED_CHK_LOAD) {

            const int nb_lits = trusted_utils_read_int(input);
            int_vec_reserve(vec_read_lits, nb_lits);
            trusted_utils_read_ints(vec_read_lits->data, nb_lits, input);
            for (int i = 0; i < nb_lits; i++) {
              int lit = vec_read_lits->data[i];
              int_vec_push(clause_to_add, lit);
              if (lit == 0) {
                int clslen = clause_to_add->size;
                int* cls = trusted_utils_calloc(clslen+1, sizeof(int));
                for (int i = 0; i < clslen; i++) cls[i] = clause_to_add->data[i];
                cls[clslen] = 0;
                u64_vec_push(orig_clauses, *(u64*)&cls);
                siphash_update((u8*) clause_to_add->data, clause_to_add->size*sizeof(int));
                int_vec_clear(clause_to_add);
              }
            }
            // NO FEEDBACK

        } else if (c == TRUSTED_CHK_CLS_DELETE) {
            // We internally process deletion statements that come directly after loading
            // since this can reduce the set of clauses forwarded to CakeML.

            // Header layout: [type(1) | nb_hints(4)]
            const int nb_hints = trusted_utils_read_int(input);
            u64_vec_reserve(last_hints, nb_hints);
            trusted_utils_read_uls(last_hints->data, nb_hints, input);
            last_hints->size = nb_hints;
            for (int i = 0; i < nb_hints; i++) {
              u64 hint = last_hints->data[i];
#ifdef IMPCHECK_DEBUG_FILE
              fprintf(f_dbg, "delete cls %lu\n", hint); fflush(f_dbg);
#endif
              int* cls = (int*) orig_clauses->data[hint-1];
              if (!cls) {
                // ERROR - clause already deleted
                snprintf(trusted_utils_msgstr, 512, "Cannot load deleted clause %lu!", hint);
                trusted_utils_log_err(trusted_utils_msgstr);
                all_ok = false;
              } else {
                free(cls);
                orig_clauses->data[hint-1] = 0;
              }
            }
            say(all_ok);

        } else if (c == TRUSTED_CHK_END_LOAD) {

            siphash_pad(2); // two-byte padding for formula signature input
            u8* out_sig = siphash_digest();
            all_ok &= trusted_utils_equal_signatures(out_sig, formula_sig);
            if (!all_ok) snprintf(trusted_utils_msgstr, 512, "Formula signature check failed");
            int_vec_clear(vec_read_lits);
            vec_read_lits = 0;
            nb_loaded_clauses = orig_clauses->size;
            say_with_flush(all_ok);
            ended_loading = true;

        } else if (c == TRUSTED_CHK_TERMINATE) {

            say_with_flush(true); // TERMINATE response
            print_stats_at_exit(start);
            exit(0);

        } else {
            if (!ended_loading) {
              snprintf(trusted_utils_msgstr, 512, "Invalid directive \"%c\" (%i) during formula loading!", c, c);
              trusted_utils_log_err(trusted_utils_msgstr);
            }
            break;
        }

#if IMPCHECK_WRITE_DIRECTIVES
        writer_flush();
#endif

        if (MALLOB_UNLIKELY(!all_ok)) {
            if (!reported_error) {
                trusted_utils_log_err(trusted_utils_msgstr);
                reported_error = true;
            }
        }
    }

    fake_import_id = 1;

    // *************************************************************
    int cml_ret = cml_main(); // Passing main loop control to CakeML
    // *************************************************************

#ifdef IMPCHECK_DEBUG_FILE
    fprintf(f_dbg, "END OF MAIN ret=%i\n", cml_ret); fflush(f_dbg);
#endif
    if (cml_ret != 0) {
        snprintf(trusted_utils_msgstr, 512, "CakeML exited with code %d", cml_ret);
        trusted_utils_log(trusted_utils_msgstr);
        all_ok = false;
    }

    say_with_flush(true); // TERMINATE response
    print_stats_at_exit(start);
    return 0;
}

// CakeML FFIs

void cml_exit(int arg) {
  // TODO: use ImpCheck's error mechanisms
  if (arg != 0) {
    fprintf(stderr,"CakeML exited with nonzero exit code.\n");
    exit(arg);
  }
}

void cml_clear(void) {
  // should never be called
  assert(false);
}

void cml_err(int arg) {
  if (arg == 3) {
    fprintf(stderr,"Memory not ready for entry. You may have not run the init code yet, or be trying to enter during an FFI call.\n");
  }

  cml_exit(arg);
}

int byte2_to_int(unsigned char *b){
    return ((b[0] << 8) | b[1]);
}

int byte8_to_int(unsigned char *b){
    return (((long long) b[0] << 56) | ((long long) b[1] << 48) |
             ((long long) b[2] << 40) | ((long long) b[3] << 32) |
             (b[4] << 24) | (b[5] << 16) | (b[6] << 8) | b[7]);
}

void int_to_byte2(int i, unsigned char *b){
    /* i is encoded on 2 bytes */
    b[0] = (i >> 8) & 0xFF;
    b[1] = i & 0xFF;
}

void ffiwrite (unsigned char *c, long clen, unsigned char *a, long alen){
  (void)clen; (void)alen;
#ifdef IMPCHECK_DEBUG_FILE
  fprintf(f_dbg, "ffiwrite\n"); fflush(f_dbg);
#endif
  assert(clen == 8);
  int fd = byte8_to_int(c);
  int n = byte2_to_int(a);
  int off = byte2_to_int(&a[2]);
  assert(alen >= n + off + 4);
  int nw = write(fd, &a[4 + off], n);
  if(nw < 0){
      a[0] = 1;
  }
  else{
    a[0] = 0;
    int_to_byte2(nw,&a[1]);
  }
}

// fficlause: CakeML calls this to fetch the next clause
// c[0]: nonzero = trusted (import), 0 = untrusted (produce)
// c[1..4]: nb_lits as little-endian int
void fficlause (unsigned char *c, long clen, unsigned char *a, long alen){
  (void)clen; (void)alen;
  assert(clen == 5);
#ifdef IMPCHECK_DEBUG_FILE
  fprintf(f_dbg, "fficlause\n"); fflush(f_dbg);
#endif

  bool trusted = c[0];
  int nb_lits;
  memcpy(&nb_lits, &c[1], sizeof(int));
  assert(nb_lits == last_nb_lits);
  assert((long)(nb_lits * sizeof(int)) <= alen);

  if (trusted) {
      if (last_cls_data) {
          memcpy(a, last_cls_data, nb_lits * sizeof(int));
      } else {
          // Read literals into buf_lits (for fficallback), then copy to CakeML
          read_literals(nb_lits);
          memcpy(a, buf_lits->data, nb_lits * sizeof(int));
      }
  } else {
      // Untrusted clause literals already read by ffistep into buf_lits
      memcpy(a, buf_lits->data, nb_lits * sizeof(int));
  }
#ifdef IMPCHECK_DEBUG_FILE
  fprintf(f_dbg, "- ret\n"); fflush(f_dbg);
#endif
}

// ffihints: CakeML calls this to fetch the next hint
// c[0..3]: nb_hints as little-endian hint
void ffihints (unsigned char *c, long clen, unsigned char *a, long alen){
  (void)clen; (void)alen;
  assert(clen == 4);
#ifdef IMPCHECK_DEBUG_FILE
  fprintf(f_dbg, "ffihints\n"); fflush(f_dbg);
#endif

  int nb_hints;
  memcpy(&nb_hints, c, sizeof(int));
  assert((long)(nb_hints * sizeof(u64)) <= alen);

  // Read external hints, save originals, write internal IDs to CakeML's array
  u64_vec_reserve(last_hints, nb_hints);
  trusted_utils_read_uls(last_hints->data, nb_hints, input);
  last_hints->size = nb_hints;
  for (int i = 0; i < nb_hints; i++) {
    ((u64*)a)[i] = external_to_internal_id(last_hints->data[i]);
  }
}

// fficallback: CakeML reports result, C performs I/O response.
// c[0]: result byte ('0' = error, nonzero = ok)
// c[1..clen-1]: error message from CakeML (if any)
// a: the same 17-byte step header from ffistep
// buf_lits is guaranteed to contain the clause for PRODUCE and IMPORT
void fficallback (unsigned char *c, long clen, unsigned char *a, long alen){
  (void)alen;
  assert(clen >= 1);
  assert(alen == 17);

  bool cml_ok = c[0] != '0';
  if (!cml_ok && clen > 1) {
      // Copy CakeML error message into trusted_utils_msgstr
      long msglen = clen - 1;
      if (msglen > 511) msglen = 511;
      memcpy(trusted_utils_msgstr, &c[1], msglen);
      trusted_utils_msgstr[msglen] = '\0';
  }
  all_ok = cml_ok && all_ok;

  if (!last_cls_data) {

  int directive = a[0];
#ifdef IMPCHECK_DEBUG_FILE
  fprintf(f_dbg, "fficallback %c %i\n", (char)directive, all_ok?1:0); fflush(f_dbg);
#endif

  if (directive == TRUSTED_CHK_CLS_PRODUCE) {

      const bool share = trusted_utils_read_bool(input);

      // CakeML handles RUP checking; C computes signature if sharing
      // Only need to compute signature if in a valid state
      if (all_ok && share) {
          compute_clause_signature(last_eid, buf_lits->data, last_nb_lits, buf_sig);
      }

      say(all_ok);
      if (share) trusted_utils_write_sig(buf_sig, output);
#if IMPCHECK_FLUSH_ALWAYS
      UNLOCKED_IO(fflush)(output);
#endif
      nb_produced++;

  } else if (directive == TRUSTED_CHK_CLS_IMPORT) {

      trusted_utils_read_sig(buf_sig, input);
      signature computed_sig;
      compute_clause_signature(last_eid, buf_lits->data, last_nb_lits, computed_sig);
      if (!trusted_utils_equal_signatures(buf_sig, computed_sig)) {
          snprintf(trusted_utils_msgstr, 512, "Signature check of clause %lu failed", last_eid);
          all_ok = false;
      }
      say(all_ok);
      nb_imported++;

  } else if (directive == TRUSTED_CHK_CLS_DELETE) {

      // Free internal IDs for each deleted clause
      for (u64 i = 0; i < last_hints->size; i++) {
          free_id(last_hints->data[i]);
      }
      say(all_ok);
      nb_deleted += last_hints->size;

  } else if (directive == TRUSTED_CHK_VALIDATE_UNSAT) {

      // CakeML checks empty clause; C computes result signature
      if (all_ok) confirm_result(formula_sig, 20, buf_sig);
      say(all_ok);
      trusted_utils_write_sig(buf_sig, output);
      UNLOCKED_IO(fflush)(output);
      if (all_ok) trusted_utils_log("UNSAT validated");

  }

  } // end if (!last_cls_data)

#if IMPCHECK_WRITE_DIRECTIVES
  writer_flush();
#endif

  if (MALLOB_UNLIKELY(!all_ok)) {
      if (!reported_error) {
          trusted_utils_log_err(trusted_utils_msgstr);
          reported_error = true;
      }
  }
}

// ffistep: CakeML calls this to get the header for the next instruction
// {'a' | nb_lits | nb_hints} - produce
// {'i' | nb_lits} - import
// {'d' | nb_hints} - delete
// {'T'} - terminate
// {'V'} - validate UNSAT
void ffistep (unsigned char *empty, long clen, unsigned char *a, long alen){
  (void)empty; (void)clen; (void)alen;
  assert(clen == 0);
  assert(alen == 17);

  // 1 byte for initial step symbol
  // max of 1 + 8 + 4 + 4 for TRUSTED_CHK_CLS_PRODUCE

  // Simulated import phase: replay loaded formula clauses to CakeML
  // as import steps.
  while (fake_import_id <= nb_loaded_clauses) {

      const u64 eid = fake_import_id;
      int* cls = *(int**)& orig_clauses->data[eid - 1];
      if (!cls) {
        // Clause was deleted: skip
#ifdef IMPCHECK_DEBUG_FILE
        fprintf(f_dbg, "skip deleted clause %lu\n", eid); fflush(f_dbg);
#endif
        fake_import_id++;
        continue;
      }

#ifdef IMPCHECK_DEBUG_FILE
      fprintf(f_dbg, "ffistep (pre) %lu\n", fake_import_id); fflush(f_dbg);
#endif

      last_eid = eid;
      const u64 iid = external_to_internal_id(eid);

      // count literals (always zero-terminated)
      int nb_lits = 0;
      while (cls[nb_lits] != 0) nb_lits++;

      // store pointer for fficlause to copy from
      last_cls_data = cls;
      last_nb_lits = nb_lits;
      // Header layout: [type(1) | iid(8) | nb_lits(4)]
      a[0] = TRUSTED_CHK_CLS_IMPORT;
      memcpy(&a[1], &iid, sizeof(iid));
      memcpy(&a[1 + sizeof(iid)], &nb_lits, sizeof(nb_lits));

      fake_import_id++;
      return;
  }

  // All original problem clauses have been imported: Delete entire clause table
  if (orig_clauses) {
    for (u64 i = 0; i < orig_clauses->size; i++) {
      int* cls = (int*) orig_clauses->data[i];
      if (cls) free(cls);
    }
    u64_vec_free(orig_clauses);
    orig_clauses = 0;
  }

  // Regular phase: parse directive from pipe.
  last_cls_data = NULL;
  if (MALLOB_LIKELY(!last_read_directive_char))
    last_read_directive_char = trusted_utils_read_char(input);
  int c = last_read_directive_char;
  last_read_directive_char = 0;
  a[0] = c; // Pass the initial character to CakeML

#ifdef IMPCHECK_DEBUG_FILE
  fprintf(f_dbg, "ffistep (post) %c\n", c); fflush(f_dbg);
#endif

  if (c == TRUSTED_CHK_CLS_PRODUCE) {

      // Header layout: [type(1) | iid(8) | nb_lits(4) | nb_hints(4)]
      const u64 eid = trusted_utils_read_ul(input);
      last_eid = eid;
      const u64 iid = external_to_internal_id(eid);
      const int nb_lits = trusted_utils_read_int(input);
      read_literals(nb_lits);
      const int nb_hints = trusted_utils_read_int(input);
      last_nb_lits = nb_lits;

      memcpy(&a[1], &iid, sizeof(iid));
      memcpy(&a[1 + sizeof(iid)], &nb_lits, sizeof(nb_lits));
      memcpy(&a[1 + sizeof(iid) + sizeof(nb_lits)], &nb_hints, sizeof(nb_hints));

  } else if (c == TRUSTED_CHK_CLS_IMPORT) {

      // Header layout: [type(1) | iid(8) | nb_lits(4)]
      const u64 eid = trusted_utils_read_ul(input);
      last_eid = eid;
      const u64 iid = external_to_internal_id(eid);
      const int nb_lits = trusted_utils_read_int(input);
      last_nb_lits = nb_lits;

      memcpy(&a[1], &iid, sizeof(iid));
      memcpy(&a[1 + sizeof(iid)], &nb_lits, sizeof(nb_lits));

  } else if (c == TRUSTED_CHK_CLS_DELETE) {

      // Header layout: [type(1) | nb_hints(4)]
      const int nb_hints = trusted_utils_read_int(input);

      memcpy(&a[1], &nb_hints, sizeof(nb_hints));

  } else if (c == TRUSTED_CHK_VALIDATE_SAT) {
      trusted_utils_log_err("SAT validation (M) not supported with CakeML");

  } else if (c != TRUSTED_CHK_VALIDATE_UNSAT && c != TRUSTED_CHK_TERMINATE) {
      snprintf(trusted_utils_msgstr, sizeof(trusted_utils_msgstr),
               "Invalid directive in ffistep: '%c' (%d)", c, c);
      trusted_utils_log_err(trusted_utils_msgstr);
  }
}

