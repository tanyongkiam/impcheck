
#include <stdbool.h>        // for bool, true, false
#include <stdio.h>          // for fclose, fflush_unlocked, fopen, snprintf
#include <stdlib.h>         // for free
#include <string.h>         // for memcpy
#include <time.h>           // for clock, CLOCKS_PER_SEC, clock_t
#include "top_check.h"      // for top_check_commit_formula_sig, top_check_d...
#include "trusted_utils.h"  // for trusted_utils_read_int, trusted_utils_log...
#include "checker_interface.h"

#include <assert.h>         // asserts
#include <unistd.h>         // for write
#include "hash.h"           // for hash_table_find

#if IMPCHECK_WRITE_DIRECTIVES
#include "../writer.h"
#endif

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

bool do_logging = true;

// Buffering.
signature buf_sig;
struct int_vec* buf_lits;
struct u64_vec* buf_hints;

/* from lrat_check.c */
extern struct hash_table* clause_table;
extern u64 nb_loaded_clauses;

/* exported in cake.S */
extern void cml_main(void);
extern void *cml_heap;
extern void *cml_stack;
extern void *cml_stackend;

// These are unused
extern char cake_text_begin;
extern char cake_codebuffer_begin;
extern char cake_codebuffer_end;

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

void read_hints(int nb_hints) {
    u64_vec_reserve(buf_hints, nb_hints);
    trusted_utils_read_uls(buf_hints->data, nb_hints, input);
}

void tc_init(const char* fifo_in, const char* fifo_out) {
    input = fopen(fifo_in, "r");
    if (!input) trusted_utils_exit_eof();
    output = fopen(fifo_out, "w");
    if (!output) trusted_utils_exit_eof();
    buf_lits = int_vec_init(1 << 14);
    buf_hints = u64_vec_init(1 << 14);
}

void tc_end(void) {
    int_vec_free(buf_lits);
    u64_vec_free(buf_hints);
    fclose(output);
    fclose(input);
}

// Counters and error state, shared between tc_run and fficallback
u64 nb_produced, nb_imported, nb_deleted;
bool reported_error;

// Next clause ID to replay during simulated import phase (1..nb_loaded_clauses)
u64 fake_import_id;

// State saved by ffistep for fficallback to perform I/O response
int last_directive;  // directive type char, or 0 during simulated import phase
int last_nb_hints;   // hint count (delete), for counter update
bool last_share;     // whether to return signature (produce)
#ifdef IMPCHECK_DOUBLE_CHECK
u64 last_id;         // clause ID (produce, import)
int last_nb_lits;    // literal count (produce, import)
#endif

int tc_run(bool check_model, bool lenient) {
    clock_t start = clock();
    nb_produced = 0;
    nb_imported = 0;
    nb_deleted = 0;

    reported_error = false;

    // TODO: use ImpCheck's command line to set these
    unsigned long sz = 1024*1024; // 1 MB unit
    unsigned long cml_heap_sz = 1024 * sz;    // Default: 1 GB heap
    unsigned long cml_stack_sz = 1024 * sz;   // Default: 1 GB stack

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

    // Formula loading phase (INIT, LOAD, END_LOAD) handled in C
    while (true) {
        int c = trusted_utils_read_char(input);
        if (c == TRUSTED_CHK_INIT) {

            nb_vars = trusted_utils_read_int(input);
            top_check_init(nb_vars, check_model, lenient);
            trusted_utils_read_sig(formula_sig, input);
            top_check_commit_formula_sig(formula_sig);
            say_with_flush(true);

        } else if (c == TRUSTED_CHK_LOAD) {

            const int nb_lits = trusted_utils_read_int(input);
            read_literals(nb_lits);
            for (int i = 0; i < nb_lits; i++) top_check_load(buf_lits->data[i]);
            // NO FEEDBACK

        } else if (c == TRUSTED_CHK_END_LOAD) {

            say_with_flush(top_check_end_load());
            break;

        } else {
            trusted_utils_log_err("Invalid directive during formula loading!");
            break;
        }
    }

    fake_import_id = 1;
    cml_main(); // Passing main loop control to CakeML

    printf("DEBUG: control returned\n");

    float elapsed = (float) (clock() - start) / CLOCKS_PER_SEC;
    snprintf(trusted_utils_msgstr, 512, "cpu:%.3f prod:%lu imp:%lu del:%lu", elapsed, nb_produced, nb_imported, nb_deleted);
    trusted_utils_log(trusted_utils_msgstr);

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
  (void)c; (void)clen; (void)a; (void)alen;
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

void ffiarr (unsigned char *c, long clen, unsigned char *a, long alen){
  (void)alen;
  if (clen == 8 && memcmp(c, "buf_lits", 8) == 0) {
      memcpy(a, buf_lits->data, alen);
  }
  else if (clen == 9 && memcmp(c, "buf_hints", 9) == 0) {
      memcpy(a, buf_hints->data, alen);
  }
  else
    assert(false);
}

void fficallback (unsigned char *c, long clen, unsigned char *a, long alen){
  (void)a; (void)alen; (void)clen;
  assert(clen == 1);

  bool res = (c[0] == '1');

  if (last_directive == TRUSTED_CHK_CLS_PRODUCE) {

#ifdef IMPCHECK_DOUBLE_CHECK
      bool c_res = top_check_produce(last_id, buf_lits->data, last_nb_lits,
          buf_hints->data, last_nb_hints, last_share ? buf_sig : 0);
      assert(res == c_res);
#endif
      say(res);
      if (last_share) trusted_utils_write_sig(buf_sig, output);
#if IMPCHECK_FLUSH_ALWAYS
      UNLOCKED_IO(fflush)(output);
#endif
      nb_produced++;

  } else if (last_directive == TRUSTED_CHK_CLS_IMPORT) {

#ifdef IMPCHECK_DOUBLE_CHECK
      bool c_res = top_check_import(last_id, buf_lits->data, last_nb_lits, buf_sig);
      assert(res == c_res);
#endif
      say(res);
      nb_imported++;

  } else if (last_directive == TRUSTED_CHK_CLS_DELETE) {

#ifdef IMPCHECK_DOUBLE_CHECK
      bool c_res = top_check_delete(buf_hints->data, last_nb_hints);
      assert(res == c_res);
#endif
      say(res);
      nb_deleted += last_nb_hints;

  } else if (last_directive == TRUSTED_CHK_VALIDATE_UNSAT) {

#ifdef IMPCHECK_DOUBLE_CHECK
      bool c_res = top_check_validate_unsat(buf_sig);
      assert(res == c_res);
#endif
      say(res);
      trusted_utils_write_sig(buf_sig, output);
      UNLOCKED_IO(fflush)(output);
      if (res) trusted_utils_log("UNSAT validated");

  } else if (last_directive == TRUSTED_CHK_TERMINATE) {

      say_with_flush(true);
  }

#if IMPCHECK_WRITE_DIRECTIVES
  writer_flush();
#endif
}

void ffistep (unsigned char *empty, long clen, unsigned char *a, long alen){
  (void)empty; (void)clen; (void)a; (void)alen;
  assert(clen == 0);
  assert(alen == 17);
  // 1 byte for initial step symbol
  // 8 + 4 + 4 for TRUSTED_CHK_CLS_PRODUCE

  // Simulated import phase: replay loaded formula clauses to CakeML
  // as import steps.
  if (fake_import_id <= nb_loaded_clauses) {

      const u64 id = fake_import_id;
      int* cls = (int*) hash_table_find(clause_table, id);

      // count literals (zero-terminated)
      int nb_lits = 0;
      while (cls[nb_lits] != 0) nb_lits++;

      // copy into buf_lits
      int_vec_reserve(buf_lits, nb_lits);
      memcpy(buf_lits->data, cls, nb_lits * sizeof(int));

      // fill CakeML step buffer as import directive
      a[0] = TRUSTED_CHK_CLS_IMPORT;
      memcpy(&a[1], &id, sizeof(id));
      memcpy(&a[1 + sizeof(id)], &nb_lits, sizeof(nb_lits));

      last_directive = 0;
      fake_import_id++;
      return;
  }

  // Regular phase: parse directive from pipe, save state for fficallback.
  int c = trusted_utils_read_char(input);
  a[0] = c; // Pass the initial character to CakeML
  last_directive = c;

  if (c == TRUSTED_CHK_CLS_PRODUCE) {

      // parse
      const u64 id = trusted_utils_read_ul(input);
      const int nb_lits = trusted_utils_read_int(input);
      read_literals(nb_lits);
      last_nb_hints = trusted_utils_read_int(input);
      read_hints(last_nb_hints);
      last_share = trusted_utils_read_bool(input);
#ifdef IMPCHECK_DOUBLE_CHECK
      last_id = id;
      last_nb_lits = nb_lits;
#endif

      // copy id (8 bytes), nb_lits (4 bytes), nb_hints (4 bytes) into a[1] onwards
      memcpy(&a[1], &id, sizeof(id));
      memcpy(&a[1 + sizeof(id)], &nb_lits, sizeof(nb_lits));
      memcpy(&a[1 + sizeof(id) + sizeof(nb_lits)], &last_nb_hints, sizeof(last_nb_hints));

  } else if (c == TRUSTED_CHK_CLS_IMPORT) {

      // parse
      const u64 id = trusted_utils_read_ul(input);
      const int nb_lits = trusted_utils_read_int(input);
      read_literals(nb_lits);
      trusted_utils_read_sig(buf_sig, input);
#ifdef IMPCHECK_DOUBLE_CHECK
      last_id = id;
      last_nb_lits = nb_lits;
#endif

      // copy id (8 bytes), nb_lits (4 bytes) into a[1] onwards
      memcpy(&a[1], &id, sizeof(id));
      memcpy(&a[1 + sizeof(id)], &nb_lits, sizeof(nb_lits));

  } else if (c == TRUSTED_CHK_CLS_DELETE) {

      // parse
      last_nb_hints = trusted_utils_read_int(input);
      read_hints(last_nb_hints);

      // copy nb_hints (4 bytes) into a[1]
      memcpy(&a[1], &last_nb_hints, sizeof(last_nb_hints));
  }
  // VALIDATE_UNSAT, TERMINATE: no payload to parse
}

