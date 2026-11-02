#ifndef EVMLR_SHUFFLE_EVMLR_UTILS_H
#define EVMLR_SHUFFLE_EVMLR_UTILS_H
#include "evmlr_params.h"

// 2 Preliminaries
// 2.2 Polynomial Ring

int evmlr_utils_is_poly_bin(const nmod_poly_t poly);
// R_q^* -> {True, False}. Takes a vector over Rq and evaluates to True
// if all the coefficients of all its elements are in {0, 1}, and
// to False otherwise.
/**
 * Check if a all coefficients from all polynomials in the vector are in {0, 1}.
 * @param poly Pointer to an array of nmod_poly_t polynomials.
 * @param len Length of the array.
 * @return 1 if all coefficients are in {0, 1}, 0 otherwise.
 */
int evmlr_utils_is_bin(const nmod_poly_t* poly, slong len);

int evmlr_utils_is_mat_bin(const nmod_poly_mat_t mat);

// {0, ..., 2^{n} - 1} -> R_q. Maps an integer in the domain to the ring element
/**
 * Maps an integer to a polynomial whose coefficients are the binary representation of the integer.
 * The least significant bit is in the constant coefficient.
 * @param poly The polynomial to be filled with the binary representation.
 * @param n the integer to be converted.
 */
void evmlr_utils_int_to_bin(nmod_poly_t poly, ulong n);

void evmlr_utils_poly_decompose(nmod_poly_mat_t bin_vec, slong mat_col, const nmod_poly_t poly, int bits, int base);

// R_q^N \times \N -> (R_q^N)^*. Binary decomposition of (a vector of) ring elements
/**
 * Decomposes a vector of polynomials into b binary polynomial vectors.
 *
 * The caller owns @p bin_vec and must have initialised it as a
 * b x nmod_poly_mat_nrows(ring_vec) matrix over modulus 2, and must clear it.
 * Any previous contents are overwritten.
 *
 * @param bin_vec Output matrix, b rows (one per bit plane), initialised by the caller.
 * @param ring_vec Input array of polynomials to be decomposed.
 * @param b Number of bits for the binary decomposition.
 */
void evmlr_utils_ring_to_bin(nmod_poly_mat_t bin_vec, const nmod_poly_mat_t ring_vec, int b);

/**
 * Stacks the binary vectors into a single vector.
 *
 * The caller owns @p stack and must have initialised it with
 * bin_vec->r * bin_vec->c rows and one column, and must clear it.
 *
 * @param stack output stacked vector of length bits * len, initialised by the caller
 * @param bin_vec input binary vectors of size bits, each of length len
 */
void evmlr_utils_stack(nmod_poly_mat_t stack, const nmod_poly_mat_t bin_vec);

/**
 * Creates the Gadget matrix G of size N x (b*N) as defined in the paper.
 * G = (I_N | 2*I_N | ... | -2^(b-1)*I_N)
 *
 * The caller owns @p G and must have initialised it as an N x (b*N) matrix over
 * @p mod, and must clear it. Any previous contents are overwritten.
 *
 * @param G         The output nmod_poly_mat_t matrix, initialised by the caller.
 * @param N         The dimension of the identity matrix blocks.
 * @param b         The number of blocks (bits for decomposition).
 * @param mod       The modulus for the polynomial coefficients.
 */
void evmlr_utils_gadget_matrix(nmod_poly_mat_t G, slong N, int b, ulong mod);


/**
 * Compress polynomials mapping points to boundaries in S (bucket width ALPHA)
 */
void evmlr_utils_highs_mat(nmod_poly_mat_t out, const nmod_poly_mat_t in);
void evmlr_utils_lows_mat(nmod_poly_mat_t out, const nmod_poly_mat_t in);
void evmlr_utils_make_hint_mat(nmod_poly_mat_t h, const nmod_poly_mat_t z, const nmod_poly_mat_t ct0);
void evmlr_utils_use_hint_mat(nmod_poly_mat_t out, const nmod_poly_mat_t h, const nmod_poly_mat_t z);

/**
 * Sample from a centered binomial distribution with a given center.
 * @param center  The center of the binomial distribution, which is also the number of trials.
 * @return An integer sampled from the centered binomial distribution.
 */
/**
 * Fills @p buf with @p len bytes from the operating system, retrying short
 * reads and interrupted calls, and aborts if the kernel cannot supply them:
 * secrets must never silently come from whatever was in the buffer.
 */
void evmlr_utils_random(void *buf, size_t len);

int evmlr_utils_binom_sample(int center);

// we are sampling an element of Rq by sampling each of its coefficients independently according to B^*_η
void evmlr_utils_binom_sample_ring(nmod_poly_t poly, int center);

void evmlr_utils_binom_sample_mat_ring(nmod_poly_mat_t mat, int center);

/**
 * Returns a value uniform in [0, @p bound), from the operating system, by
 * rejecting the incomplete top copy of the range rather than reducing it.
 */
ulong evmlr_utils_uniform_below(ulong bound);

/**
 * Sets the first @p len coefficients of @p poly uniformly modulo its modulus,
 * from the operating system. Public matrices, keys and blinding masks need
 * this; FLINT's randtest functions favour small, sparse values on purpose.
 */
void evmlr_utils_uniform_poly(nmod_poly_t poly, slong len);

/** Sets every entry of @p mat to a uniform polynomial of degree < DEGREE_N. */
void evmlr_utils_uniform_mat(nmod_poly_mat_t mat);

void evmlr_utils_sample_binary_poly(nmod_poly_t poly, slong degree);

void evmlr_utils_sample_binary_poly_mat(nmod_poly_mat_t mat, slong degree);

/**
 * Generates a new random permutation of length `len` and stores it in the `perm` array.
 * @param perm Pointer to an array where the permutation will be stored.
 * @param len Length of the permutation array.
 */
void evmlr_utils_new_perm(ulong* perm, size_t len);

void nmod_poly_mat_mulmod(nmod_poly_mat_t res, const nmod_poly_mat_t mat1, const nmod_poly_mat_t mat2, const nmod_poly_t mod);

nmod_poly_struct* nmod_poly_vec_entry(const nmod_poly_mat_t mat, slong i);

void evmlr_utils_linear_sample_mat_ring(nmod_poly_mat_t mat, slong beta);
int evmlr_utils_is_bounded(const nmod_poly_mat_t mat, slong beta);

#endif // EVMLR_SHUFFLE_EVMLR_UTILS_H