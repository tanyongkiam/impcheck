
#include <stdbool.h>          // for bool, false
#include <stdio.h>            // for fflush, stdout
#include "secret.h"
#include "trusted_checker.h"  // for tc_init, tc_run
#include "trusted_utils.h"    // for trusted_utils_try_match_arg, trusted_ut...
#if IMPCHECK_WRITE_DIRECTIVES
#include <unistd.h>
#include "../writer.h"
#endif

int main(int argc, char *argv[]) {

    const char *fifo_directives = "", *fifo_feedback = "", *seed_str = "0";
    bool check_model = false, lenient = false;
    long producer_id = 0, producer_count = 0, heap_megabytes = 2048;
    for (int i = 1; i < argc; i++) {
        trusted_utils_try_match_arg(argv[i], "-directives=", &fifo_directives);
        trusted_utils_try_match_arg(argv[i], "-feedback=", &fifo_feedback);
        trusted_utils_try_match_arg(argv[i], "-key-seed=", &seed_str);
        trusted_utils_try_match_long(argv[i], "-producer-id=", &producer_id);
        trusted_utils_try_match_long(argv[i], "-producer-count=", &producer_count);
        trusted_utils_try_match_long(argv[i], "-heap-mbs=", &heap_megabytes);

        trusted_utils_try_match_flag(argv[i], "-check-model", &check_model);
        trusted_utils_try_match_flag(argv[i], "-lenient", &lenient);
    }
    generate_key(seed_str);

#if IMPCHECK_WRITE_DIRECTIVES
    char output_path[512];
    snprintf(output_path, 512, "directives.%i.impcheck", getpid());
    writer_init(output_path);
#endif

    tc_init(fifo_directives, fifo_feedback);
    int res = tc_run(check_model, lenient, producer_id, producer_count, heap_megabytes);
    tc_end();
    fflush(stdout);
    return res;
}
