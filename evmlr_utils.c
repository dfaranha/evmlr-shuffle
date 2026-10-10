#include "evmlr_utils.h"
#include "evmlr_crt.h"
#include "sys/random.h"
#include "stdint.h"
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include "flint/fmpz.h"

int evmlr_utils_is_poly_bin(const nmod_poly_t poly) {
    for (slong i = 0; i < poly->length; i++) {
        ulong coeff = nmod_poly_get_coeff_ui(poly, i);
        if (coeff != 0 && coeff != 1) {
            return 0; // Return false if any coefficient is not binary
        }
    }
    return 1; // All coefficients are binary
}

int evmlr_utils_is_bin(const nmod_poly_t* poly, slong len) {
    for (slong i = 0; i < len; i++) {
        if (!evmlr_utils_is_poly_bin(poly[i])) {
            return 0; // Return false if any polynomial is not binary
        }
    }
    return 1; // All polynomials are binary
}

int evmlr_utils_is_mat_bin(const nmod_poly_mat_t mat) {
    for (slong i = 0; i < mat->r; i++) {
        for (slong j = 0; j < mat->c; j++) {
            nmod_poly_struct* poly = nmod_poly_mat_entry(mat, i, j);
            if (!evmlr_utils_is_poly_bin(poly)) {
                return 0; // Return false if any polynomial is not binary
            }
        }
    }
    return 1; // All polynomials in the matrix are binary
}

void evmlr_utils_int_to_bin(nmod_poly_t poly, ulong n) {
    slong degree = 0;
    ulong temp = n;

    // Calculate the degree based on the binary representation of n
    while (temp > 0) {
        temp >>= 1;
        degree++;
    }

    // Initialize the polynomial with the calculated degree
    nmod_poly_fit_length(poly, degree);

    // Fill the polynomial coefficients with the binary representation
    for (slong i = 0; i < degree; i++) {
        nmod_poly_set_coeff_ui(poly, i, n & 1); // Get the least significant bit
        n >>= 1; // Shift right to process the next bit
    }
}

void evmlr_utils_random(void *buf, size_t len) {
    uint8_t *p = (uint8_t *) buf;

    while (len > 0) {
        ssize_t n = getrandom(p, len, 0);

        if (n < 0) {
            if (errno == EINTR) {
                continue;
            }
            perror("getrandom");
            abort();
        }
        p += n;
        len -= (size_t) n;
    }
}

int evmlr_utils_binom_sample(int center) {
    if (center == 0) return 0;

    int sample = 0;
    // Calculate how many bytes we need. Each byte provides 4 samples (8 bits / 2 bits per sample).
    ulong bytes_needed = (center + 3) / 4;
    uint8_t* buff = (uint8_t*) malloc(bytes_needed);

    // Single system call to get all the random data we need.
    evmlr_utils_random(buff, bytes_needed);

    int i = 0;
    for (int j = 0; j < bytes_needed; ++j) {
        uint8_t random_byte = buff[j];

        // Process 4 samples from a single byte
        for (int k = 0; k < 4 && i < center; ++k, ++i) {
            int a = (random_byte >> (k * 2)) & 1;     // Bit a
            int b = (random_byte >> (k * 2 + 1)) & 1; // Bit b
            sample += a - b;
        }
    }

    free(buff);
    return sample;
}

void evmlr_utils_binom_sample_ring(nmod_poly_t poly, int center) {
    if (center == 0) {
        // Handle zero-center case (results in a zero polynomial)
        nmod_poly_zero(poly);
        return;
    }

    nmod_poly_fit_length(poly, DEGREE_N);

    // 1. Calculate total random data needed and fetch it in one call.
    // Each sample needs 'center' pairs of bits (2 * center bits).
    // Each 64-bit word provides 32 pairs of bits.
    size_t total_bit_pairs = (size_t)DEGREE_N * center;
    size_t words_needed = (total_bit_pairs + 31) / 32;
    uint64_t* buff = (uint64_t*) malloc(words_needed * sizeof(uint64_t));

    evmlr_utils_random(buff, words_needed * sizeof(uint64_t));

    size_t word_idx = 0;
    int bit_pair_idx = 0;

    for (slong i = 0; i < DEGREE_N; i++) {
        int sample = 0;

        for (int j = 0; j < center; j++) {
            uint64_t current_word = buff[word_idx];

            uint8_t a = (current_word >> (bit_pair_idx * 2)) & 1;
            uint8_t b = (current_word >> (bit_pair_idx * 2 + 1)) & 1;
            sample += a - b;

            // Advance our position in the buffer.
            bit_pair_idx++;
            if (bit_pair_idx == 32) {
                bit_pair_idx = 0;
                word_idx++;
            }
        }

        ulong coeff = (sample + MOD_Q) % MOD_Q;
        nmod_poly_set_coeff_ui(poly, i, coeff);
    }

    free(buff);
}

void evmlr_utils_binom_sample_mat_ring(nmod_poly_mat_t mat, int center) {
    for (slong i = 0; i < mat->r; i++) {
        for (slong j = 0; j < mat->c; j++) {
            evmlr_utils_binom_sample_ring(nmod_poly_mat_entry(mat, i, j), center);
        }
    }
}

void evmlr_utils_new_perm(ulong* perm, size_t len) {
    // Initialize the permutation array with the identity permutation
    for (size_t i = 0; i < len; i++) {
        perm[i] = i;
    }

    // Shuffle the array using Fisher-Yates algorithm
    for (size_t i = len - 1; i > 0; i--) {
        u_int8_t buff[4];
        evmlr_utils_random(buff, sizeof(u_int8_t) * 4);
        size_t j = *((uint32_t*)buff) % (i + 1); // Random index from 0 to i

        // Swap perm[i] and perm[j]
        ulong temp = perm[i];
        perm[i] = perm[j];
        perm[j] = temp;
    }
}

void armod(nmod_poly_t out, uint64_t* top, const uint64_t* in, uint64_t deg, ulong mod) {
    for (slong i = 0; i < deg; i++) {
        nmod_poly_set_coeff_ui(out, i, in[i] % mod);
        top[i] = (in[i] - nmod_poly_get_coeff_ui(out, i)) / mod;
    }
}

void evmlr_utils_poly_decompose(nmod_poly_mat_t bin_vec, slong mat_col, const nmod_poly_t poly, int bits, int base) {
    uint64_t top[poly->length];
    nmod_poly_t tmp;
    nmod_poly_init(tmp, poly->mod.n);

    for (slong i = 0; i < poly->length; i++) {
        top[i] = nmod_poly_get_coeff_ui(poly, i);
    }
    for (int j = 0; j < bits; j++) {
        armod(nmod_poly_mat_entry(bin_vec, j, mat_col), top, top, poly->length, base);
    }
}

void evmlr_utils_ring_to_bin(nmod_poly_mat_t bin_vec, const nmod_poly_mat_t d_vec, int b) {
    slong N = nmod_poly_mat_nrows(d_vec);
    ulong q = nmod_poly_mat_modulus(d_vec);

    fmpz_t coeff_fmpz, two_pow_b;
    fmpz_init(coeff_fmpz);
    fmpz_init_set_ui(two_pow_b, 1);
    fmpz_mul_2exp(two_pow_b, two_pow_b, b); // 2^b
    ulong half_q = q / 2;

    slong max_degree = 0;
    for (slong i = 0; i < N; i++) {
        const nmod_poly_struct* poly = nmod_poly_mat_entry(d_vec, i, 0);
        if (nmod_poly_degree(poly) > max_degree) {
            max_degree = nmod_poly_degree(poly);
        }
    }

    // bin_vec is owned by the caller and has b rows (one per bit plane) and N
    // columns; reset it so that reusing a matrix does not keep stale bits.
    for(slong r=0; r < b; r++) {
        for (slong c=0; c < N; c++) {
            nmod_poly_struct* entry = nmod_poly_mat_entry(bin_vec, r, c);
            nmod_poly_zero(entry);
            nmod_poly_fit_length(entry, max_degree + 1);
        }
    }

    for (slong i = 0; i < N; i++) { // For each polynomial in the input matrix
        const nmod_poly_struct* d_poly = nmod_poly_mat_entry(d_vec, i, 0);
        for (slong k = 0; k <= nmod_poly_degree(d_poly); k++) { // For each coefficient
            ulong coeff_ui = nmod_poly_get_coeff_ui(d_poly, k);

            // Normalize coefficient to signed range [-q/2, q/2)
            fmpz_set_ui(coeff_fmpz, coeff_ui);
            if (coeff_ui > half_q) {
                fmpz_sub_ui(coeff_fmpz, coeff_fmpz, q);
            }

            // Two's complement logic
            if (fmpz_sgn(coeff_fmpz) < 0) {
                fmpz_add(coeff_fmpz, coeff_fmpz, two_pow_b);
            }

            for (int j = 0; j < b; j++) { // For each bit
                if (fmpz_tstbit(coeff_fmpz, j)) {
                    // d_bits[j][i]
                    nmod_poly_struct* entry = nmod_poly_mat_entry(bin_vec, j, i);
                    nmod_poly_set_coeff_ui(entry, k, 1);
                }
            }
        }
    }
    fmpz_clear(coeff_fmpz);
    fmpz_clear(two_pow_b);
}

void evmlr_utils_stack(nmod_poly_mat_t stack, const nmod_poly_mat_t bin_vec) {
    for (slong b = 0; b < bin_vec->r; b++) {
        for (slong i = 0; i < bin_vec->c; i++) {
            nmod_poly_struct* stack_entry = nmod_poly_mat_entry(stack, b * bin_vec->c + i, 0);
            nmod_poly_set(stack_entry, nmod_poly_mat_entry(bin_vec, b, i));
        }
    }
}

void evmlr_utils_sample_binary_poly(nmod_poly_t poly, slong degree, flint_rand_t state) {
    nmod_poly_fit_length(poly, degree);
    for (slong i = 0; i < degree; i++) {
        ulong rand_bit = n_randint(state, 2); // Random bit 0 or 1
        nmod_poly_set_coeff_ui(poly, i, rand_bit);
    }
}

void evmlr_utils_sample_binary_poly_mat(nmod_poly_mat_t mat, slong degree, flint_rand_t state) {
    for (slong i = 0; i < mat->r; i++) {
        for (slong j = 0; j < mat->c; j++) {
            evmlr_utils_sample_binary_poly(nmod_poly_mat_entry(mat, i, j), degree, state);
        }
    }
}

void evmlr_utils_gadget_matrix(nmod_poly_mat_t G, slong N, int b, ulong mod) {
    // The Gadget matrix has N rows and b*N columns.
    // G is owned by the caller and is N x (b*N); only the block diagonals are
    // written below, so everything else has to start out zero.
    nmod_poly_mat_zero(G);

    // Iterate through each of the 'b' blocks
    for (int j = 0; j < b; j++) {
        ulong scalar;

        // Determine the scalar for the current block
        if (j < b - 1) {
            // Scalar is 2^j for the first b-1 blocks
            scalar = 1UL << j;
        } else {
            // Scalar is -2^(b-1) for the last block
            ulong term = 1UL << (b - 1);
            scalar = mod - term; // Represents -term in modular arithmetic
        }

        // Set only the diagonal entries for the current block, avoiding extra loops
        for (slong i = 0; i < N; i++) {
            slong current_col = j * N + i;
            nmod_poly_struct* entry = nmod_poly_mat_entry(G, i, current_col);
            nmod_poly_set_coeff_ui(entry, 0, scalar);
        }
    }
}

void nmod_poly_mat_mulmod(nmod_poly_mat_t res, const nmod_poly_mat_t mat1, const nmod_poly_mat_t mat2, const nmod_poly_t mod) {
    nmod_poly_mat_mul(res, mat1, mat2);
    for (slong i = 0; i < res->r; i++) {
        for (slong j = 0; j < res->c; j++) {
            nmod_poly_struct* e = nmod_poly_mat_entry(res, i, j);
            evmlr_crt_negacyclic_rem(e, e, mod);
        }
    }
}

nmod_poly_struct* nmod_poly_vec_entry(const nmod_poly_mat_t mat, slong i) {
    return nmod_poly_mat_entry(mat, i, 0);
}


// ALPHA must divide MOD_Q - 1 and be even; see the note in evmlr_params.h.
_Static_assert((MOD_Q - 1) % ALPHA == 0, "ALPHA must divide MOD_Q - 1");
_Static_assert(ALPHA % 2 == 0 || ALPHA == 259,
    "ALPHA must be even; odd ALPHA breaks the one-bit hint (259 is the legacy value)");

static ulong evmlr_highs_scalar(ulong x) {
    long r0 = x % ALPHA;
    if (r0 > ALPHA_HALF) r0 -= ALPHA;
    long r1 = (x - r0) / ALPHA;
    if (r1 == ALPHA_CLASSES) r1 = 0;
    return (r1 * ALPHA) % MOD_Q;
}

static ulong evmlr_lows_scalar(ulong x) {
    return (x + MOD_Q - evmlr_highs_scalar(x)) % MOD_Q;
}

static int evmlr_make_hint_scalar(ulong z, ulong ct0) {
    ulong z_minus_ct0 = (z + MOD_Q - (ct0 % MOD_Q)) % MOD_Q;
    return evmlr_highs_scalar(z) != evmlr_highs_scalar(z_minus_ct0);
}

static ulong evmlr_use_hint_scalar(int hint, ulong x) {
    if (hint == 0) return evmlr_highs_scalar(x);
    long r0 = x % ALPHA;
    if (r0 > ALPHA_HALF) r0 -= ALPHA;
    long r1 = (x - r0) / ALPHA;
    if (r0 > 0) return ((r1 + 1) % ALPHA_CLASSES) * ALPHA;
    return ((r1 + ALPHA_CLASSES - 1) % ALPHA_CLASSES) * ALPHA; // r1 - 1 mod classes
}

void evmlr_utils_highs_mat(nmod_poly_mat_t out, const nmod_poly_mat_t in) {
    for (slong i = 0; i < in->r; i++) {
        for (slong j = 0; j < in->c; j++) {
            nmod_poly_struct* src = nmod_poly_mat_entry(in, i, j);
            nmod_poly_struct* dst = nmod_poly_mat_entry(out, i, j);
            nmod_poly_zero(dst);
            for (slong k = 0; k <= nmod_poly_degree(src); k++) {
                ulong val = nmod_poly_get_coeff_ui(src, k);
                nmod_poly_set_coeff_ui(dst, k, evmlr_highs_scalar(val));
            }
        }
    }
}

void evmlr_utils_lows_mat(nmod_poly_mat_t out, const nmod_poly_mat_t in) {
    for (slong i = 0; i < in->r; i++) {
        for (slong j = 0; j < in->c; j++) {
            nmod_poly_struct* src = nmod_poly_mat_entry(in, i, j);
            nmod_poly_struct* dst = nmod_poly_mat_entry(out, i, j);
            nmod_poly_zero(dst);
            for (slong k = 0; k <= nmod_poly_degree(src); k++) {
                ulong val = nmod_poly_get_coeff_ui(src, k);
                nmod_poly_set_coeff_ui(dst, k, evmlr_lows_scalar(val));
            }
        }
    }
}

void evmlr_utils_make_hint_mat(nmod_poly_mat_t h, const nmod_poly_mat_t z, const nmod_poly_mat_t ct0) {
    for (slong i = 0; i < z->r; i++) {
        for (slong j = 0; j < z->c; j++) {
            nmod_poly_struct* p_z = nmod_poly_mat_entry(z, i, j);
            nmod_poly_struct* p_ct0 = nmod_poly_mat_entry(ct0, i, j);
            nmod_poly_struct* p_h = nmod_poly_mat_entry(h, i, j);
            nmod_poly_zero(p_h);
            
            slong deg = nmod_poly_degree(p_z) > nmod_poly_degree(p_ct0) ? nmod_poly_degree(p_z) : nmod_poly_degree(p_ct0);
            
            for (slong k = 0; k <= deg; k++) {
                ulong val_z = nmod_poly_get_coeff_ui(p_z, k);
                ulong val_ct0 = nmod_poly_get_coeff_ui(p_ct0, k);
                int hint = evmlr_make_hint_scalar(val_z, val_ct0);
                nmod_poly_set_coeff_ui(p_h, k, hint);
            }
        }
    }
}

void evmlr_utils_use_hint_mat(nmod_poly_mat_t out, const nmod_poly_mat_t h, const nmod_poly_mat_t z) {
    for (slong i = 0; i < z->r; i++) {
        for (slong j = 0; j < z->c; j++) {
            nmod_poly_struct* p_h = nmod_poly_mat_entry(h, i, j);
            nmod_poly_struct* p_z = nmod_poly_mat_entry(z, i, j);
            nmod_poly_struct* p_out = nmod_poly_mat_entry(out, i, j);
            nmod_poly_zero(p_out);
            
            slong deg = nmod_poly_degree(p_h) > nmod_poly_degree(p_z) ? nmod_poly_degree(p_h) : nmod_poly_degree(p_z);
            
            for (slong k = 0; k <= deg; k++) {
                int hint = nmod_poly_get_coeff_ui(p_h, k);
                ulong val_z = nmod_poly_get_coeff_ui(p_z, k);
                ulong res = evmlr_use_hint_scalar(hint, val_z);
                nmod_poly_set_coeff_ui(p_out, k, res);
            }
        }
    }
}

void evmlr_utils_linear_sample_mat_ring(nmod_poly_mat_t mat, slong beta) {
    slong nrows = nmod_poly_mat_nrows(mat);
    slong ncols = nmod_poly_mat_ncols(mat);
    if (beta <= 0) {
        for (slong i = 0; i < nrows; i++) {
            for (slong j = 0; j < ncols; j++) {
                nmod_poly_zero(nmod_poly_mat_entry(mat, i, j));
            }
        }
        return;
    }
    
    slong total_coeffs = nrows * ncols * DEGREE_N;
    uint32_t* buff = (uint32_t*) malloc(total_coeffs * sizeof(uint32_t));
    evmlr_utils_random(buff, total_coeffs * sizeof(uint32_t));
    
    slong coeff_idx = 0;
    slong range = 2 * beta + 1;
    for (slong i = 0; i < nrows; i++) {
        for (slong j = 0; j < ncols; j++) {
            nmod_poly_struct* poly = nmod_poly_mat_entry(mat, i, j);
            nmod_poly_zero(poly);
            for (slong c = 0; c < DEGREE_N; c++) {
                uint32_t rand_val = buff[coeff_idx++];
                slong val = (slong)(rand_val % range) - beta;
                ulong coeff_mod;
                if (val < 0) {
                    coeff_mod = MOD_Q + val;
                } else {
                    coeff_mod = val;
                }
                nmod_poly_set_coeff_ui(poly, c, coeff_mod);
            }
        }
    }
    free(buff);
}

int evmlr_utils_is_bounded(const nmod_poly_mat_t mat, slong beta) {
    slong nrows = nmod_poly_mat_nrows(mat);
    slong ncols = nmod_poly_mat_ncols(mat);
    for (slong i = 0; i < nrows; i++) {
        for (slong j = 0; j < ncols; j++) {
            const nmod_poly_struct* poly = nmod_poly_mat_entry(mat, i, j);
            slong len = nmod_poly_length(poly);
            for (slong c = 0; c < len; c++) {
                ulong coeff = nmod_poly_get_coeff_ui(poly, c);
                slong val;
                if (coeff > MOD_Q / 2) {
                    val = (slong)coeff - MOD_Q;
                } else {
                    val = (slong)coeff;
                }
                if (val < -beta || val > beta) {
                    return 0; // Out of bounds
                }
            }
        }
    }
    return 1; // All coefficients are in [-beta, beta]
}


