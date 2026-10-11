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


#ifndef SHUFFLE_N_MSGS
#define SHUFFLE_N_MSGS 10 // Number of messages to shuffle, for testing and benchmarking
#endif

#define EVMLR_SHUFFLE_EVMLR_PARAMS_H

#endif //EVMLR_SHUFFLE_EVMLR_PARAMS_H
