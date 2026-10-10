/**
 * @file
 *
 * Shared entry-point helpers for the test/benchmark binaries.
 *
 * Every `evmlr_*.c` file compiles, under -DMAIN, into a standalone binary whose
 * main() seeds a FLINT RNG and then runs a test suite and a benchmark suite.
 * This header holds the parts that used to be copy-pasted into each of those
 * main() functions, and adds a mode switch so that the (fast) tests can be run
 * without the (much slower) benchmarks.
 */

#ifndef EVMLR_MAIN_H
#define EVMLR_MAIN_H

#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/random.h>

#include "flint/flint.h"

#include "test.h"

/**
 * Which suites a test binary should run, selected by argv[1].
 */
typedef enum {
    EVMLR_RUN_ALL,   /**< tests followed by benchmarks (the default) */
    EVMLR_RUN_TEST,  /**< tests only; fast enough for an edit-compile-run loop */
    EVMLR_RUN_BENCH  /**< benchmarks only */
} evmlr_mode_t;

/**
 * Parses the run mode from the command line.
 *
 * Accepts "test", "bench" or "all"; anything else (including no argument at
 * all) selects EVMLR_RUN_ALL, so invoking a binary bare behaves as before.
 */
static inline evmlr_mode_t evmlr_mode(int argc, char *argv[]) {
    if (argc > 1) {
        if (strcmp(argv[1], "test") == 0)  return EVMLR_RUN_TEST;
        if (strcmp(argv[1], "bench") == 0) return EVMLR_RUN_BENCH;
        if (strcmp(argv[1], "all") != 0) {
            fprintf(stderr, "%s: unknown mode '%s', running everything "
                            "(expected 'test', 'bench' or 'all')\n",
                    argv[0], argv[1]);
        }
    }
    return EVMLR_RUN_ALL;
}

/** Whether @p mode asks for the test suite. */
static inline int evmlr_runs_tests(evmlr_mode_t mode) {
    return mode != EVMLR_RUN_BENCH;
}

/** Whether @p mode asks for the benchmark suite. */
static inline int evmlr_runs_benches(evmlr_mode_t mode) {
    return mode != EVMLR_RUN_TEST;
}

/**
 * Initialises @p state and seeds it from the operating system.
 */
static inline void evmlr_rand_init(flint_rand_t state) {
    ulong seed[2];
    flint_rand_init(state);
    if (getrandom(seed, sizeof(seed), 0) != (ssize_t) sizeof(seed)) {
        perror("evmlr: getrandom");
        abort();
    }
    flint_rand_set_seed(state, seed[0], seed[1]);
}

#endif /* EVMLR_MAIN_H */
