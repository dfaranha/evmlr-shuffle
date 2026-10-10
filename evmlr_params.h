#ifndef EVMLR_SHUFFLE_EVMLR_PARAMS_H

#include "flint/nmod_poly.h"
#include "flint/nmod_poly_mat.h"
#include <stdlib.h>
#include <stddef.h>

#define MOD_Q 3109
#define DEGREE_N 512
#define K_LWE 2
#define K_LWR 1
#define K_SIS 2
#define ETA 2
#define ZETA 6
#define M_LEN 1
#define LOG_Q_CEIL 12

// Decomposition parameter for the compressed-hint linear proof: every
// coefficient is written as r_1*ALPHA + r_0 with |r_0| <= ALPHA/2.
//
// ALPHA must divide MOD_Q - 1 (so the r_1 classes wrap cleanly) and must be
// EVEN. With an odd ALPHA the class that wraps is one element wider than
// ALPHA, so |r_0| reaches ALPHA/2 + 1 -- one past what a one-bit hint can
// correct -- and verification fails for those coefficients. MOD_Q - 1 = 3108
// = 2^2 * 3 * 7 * 37, so the legal values are
//   2, 4, 6, 12, 14, 28, 42, 74, 84, 148, 222, 444, 518, 1036, 1554, 3108.
// Larger ALPHA means fewer classes and a lower prover rejection rate.
#define ALPHA 259
#define ALPHA_HALF (ALPHA / 2)
#define ALPHA_CLASSES ((MOD_Q - 1) / ALPHA)

#define NONZERO 36

#ifndef SHUFFLE_N_MSGS
#define SHUFFLE_N_MSGS 10 // Number of messages to shuffle, for testing and benchmarking
#endif

#define EVMLR_SHUFFLE_EVMLR_PARAMS_H

#endif //EVMLR_SHUFFLE_EVMLR_PARAMS_H
