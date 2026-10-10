#ifndef EVMLR_SHUFFLE_EVMLR_ZK_H
#define EVMLR_SHUFFLE_EVMLR_ZK_H

/**
 * @file
 *
 * Arithmetic for ZK⋆, the proof system of the shuffle (SHUFFLE-ZK.md).
 *
 * Statements live in R_q = Z_q[x]/(x^n + 1) with q = MOD_Q, which is far too
 * small for a lattice proof to be sound in. Proofs therefore run in
 * R_p = Z_p[x]/(x^n + 1) for a prime p much larger than q, with the same n.
 * p = 5 (mod 8), so that x^n + 1 splits into two irreducible factors mod p,
 * as Lemma 1 of the paper needs for challenge differences to be invertible.
 */

#include <stdint.h>
#include "flint/nmod.h"
#include "flint/nmod_poly.h"
#include "fastrandombytes.h"
#include "evmlr_params.h"

/** The proof modulus: 2^52 - 395, the largest prime below 2^52 that is 5 mod 8.
 * The binary claim needs it above the square of the bound certified on the
 * witness, about 2^49.9 at N = 1000 messages (SHUFFLE-ZK.md, section 7). */
#define ZK_P 4503599627370101UL
#define ZK_P_BITS 52
/** A square root of -1 mod ZK_P; x^(n/2) +- ZK_P_SQRT_M1 are the factors. */
#define ZK_P_SQRT_M1 1158839398463783UL

/**
 * Challenges are fixed by the automorphism sigma(x) = x^-1: c_0 = 0, and for
 * ZK_NU indices 0 < i < n/2, c_i = +-1 and c_(n-i) = -c_i. That gives
 * 2^ZK_NU * C(n/2 - 1, ZK_NU) = 2^130.9 challenges and ||c||_1 = 2 * ZK_NU.
 */
#define ZK_NU 23

/** The modulus p, for nmod arithmetic. */
const nmod_t *evmlr_zk_mod(void);

/** Initialises @p a as a polynomial mod p. */
void evmlr_zk_init(nmod_poly_t a);

/** r = a * b in R_p. r may alias a or b. */
void evmlr_zk_mul(nmod_poly_t r, const nmod_poly_t a, const nmod_poly_t b);

/** r = sigma(a) = a(x^-1) in R_p: r_0 = a_0 and r_(n-i) = -a_i. */
void evmlr_zk_sigma(nmod_poly_t r, const nmod_poly_t a);

/** The constant coefficient of @p a. ct(sigma(a) b) = <a, b> mod p. */
ulong evmlr_zk_ct(const nmod_poly_t a);

/** r = the all-ones polynomial 1 + x + ... + x^(n-1). */
void evmlr_zk_ones(nmod_poly_t r);

/**
 * r = the element of R_q @p a lifted to R_p through its centred
 * representative: a coefficient v > q/2 becomes p - (q - v).
 */
void evmlr_zk_lift(nmod_poly_t r, const nmod_poly_t a);

/** r = a challenge from the stream @p prg (see ZK_NU). */
void evmlr_zk_challenge(nmod_poly_t r, prg_t *prg);

/**
 * r = a polynomial with n coefficients uniform mod p, from @p prg, by
 * rejecting the incomplete top copy of the range.
 */
void evmlr_zk_uniform(nmod_poly_t r, prg_t *prg);

/**
 * Keys the stream @p prg for the element (@p row, @p col) of the public matrix
 * named @p domain, expanded from the 32-byte @p seed. Public matrices are
 * generated an element at a time this way, so none is ever held whole.
 */
void evmlr_zk_prg_for(prg_t *prg, const uint8_t seed[32], uint32_t domain,
                      uint64_t row, uint64_t col);

#endif // EVMLR_SHUFFLE_EVMLR_ZK_H
