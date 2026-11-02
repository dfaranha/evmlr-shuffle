#include "evmlr_crt.h"
#include "evmlr_bin_proof.h"
#include "evmlr_utils.h"
#include "evmlr_challenge.h"
#include "fastrandombytes.h"
#include <math.h>

static int64_t nmod_poly_mat_sq_norm(const nmod_poly_mat_t mat) {
    int64_t norm = 0;
    slong r = nmod_poly_mat_nrows(mat);
    slong c = nmod_poly_mat_ncols(mat);
    for (slong i = 0; i < r; i++) {
        for (slong j = 0; j < c; j++) {
            const nmod_poly_struct* poly = nmod_poly_mat_entry(mat, i, j);
            slong len = poly->length;
            for (slong k = 0; k < len; k++) {
                int64_t coeff = nmod_poly_get_coeff_ui(poly, k);
                if (coeff > MOD_Q / 2) {
                    coeff -= MOD_Q;
                }
                norm += coeff * coeff;
            }
        }
    }
    return norm;
}

static int64_t nmod_poly_mat_dot_product(const nmod_poly_mat_t mat1, const nmod_poly_mat_t mat2) {
    int64_t dot = 0;
    slong r = nmod_poly_mat_nrows(mat1);
    slong c = nmod_poly_mat_ncols(mat1);
    for (slong i = 0; i < r; i++) {
        for (slong j = 0; j < c; j++) {
            const nmod_poly_struct* poly1 = nmod_poly_mat_entry(mat1, i, j);
            const nmod_poly_struct* poly2 = nmod_poly_mat_entry(mat2, i, j);
            slong len1 = poly1->length;
            slong len2 = poly2->length;
            slong len = len1 > len2 ? len1 : len2;
            for (slong k = 0; k < len; k++) {
                int64_t coeff1 = nmod_poly_get_coeff_ui(poly1, k);
                int64_t coeff2 = nmod_poly_get_coeff_ui(poly2, k);
                if (coeff1 > MOD_Q / 2) {
                    coeff1 -= MOD_Q;
                }
                if (coeff2 > MOD_Q / 2) {
                    coeff2 -= MOD_Q;
                }
                dot += coeff1 * coeff2;
            }
        }
    }
    return dot;
}

void evmlr_bin_proof_ctx_init(evmlr_bin_proof_ctx_t ctx, slong k, slong m, slong L) {
    ctx->k = k;
    ctx->m = m;
    ctx->L = L;
    nmod_poly_init(ctx->cyclo_poly, MOD_Q);
    nmod_poly_set_coeff_ui(ctx->cyclo_poly, DEGREE_N, 1);
    nmod_poly_set_coeff_ui(ctx->cyclo_poly, 0, 1);
    ctx->beta = 2000;
    ctx->use_gaussian = 0;
    ctx->sigma_m = 0.0;
    ctx->sigma_r = 0.0;
    ctx->s2_m = 0;
    ctx->s2_r = 0;
    discrete_gaussian_ctx_init(ctx->dg_ctx_m, 1.0);
    discrete_gaussian_ctx_init(ctx->dg_ctx_r, 1.0);
}

void evmlr_bin_proof_ctx_clear(evmlr_bin_proof_ctx_t ctx) {
    nmod_poly_clear(ctx->cyclo_poly);
    discrete_gaussian_ctx_clear(ctx->dg_ctx_m);
    discrete_gaussian_ctx_clear(ctx->dg_ctx_r);
}

void evmlr_bin_proof_ctx_set_linear(evmlr_bin_proof_ctx_t ctx, slong beta) {
    ctx->use_gaussian = 0;
    ctx->beta = beta;
}

void evmlr_bin_proof_ctx_set_gaussian(evmlr_bin_proof_ctx_t ctx) {
    ctx->use_gaussian = 1;
    double bound_infty = ETA;
    
    double sigma_m = 11.0 * 1 * (double)NONZERO * sqrt((double)DEGREE_N * (double)ctx->L);
    double sigma_r = 11.0 * bound_infty * (double)NONZERO * sqrt((double)DEGREE_N * (double)ctx->m);
    
    ctx->sigma_m = sigma_m;
    ctx->sigma_r = sigma_r;
    ctx->s2_m = (uint64_t)(sigma_m * sigma_m + 0.5);
    ctx->s2_r = (uint64_t)(sigma_r * sigma_r + 0.5);
    
    discrete_gaussian_ctx_clear(ctx->dg_ctx_m);
    discrete_gaussian_ctx_clear(ctx->dg_ctx_r);
    
    discrete_gaussian_ctx_init(ctx->dg_ctx_m, sigma_m);
    discrete_gaussian_ctx_init(ctx->dg_ctx_r, sigma_r);
}

void evmlr_bin_proof_init(evmlr_bin_proof_t proof, const evmlr_bin_proof_ctx_t ctx) {
    // We need a commitment context to initialize the sub-commitments c_g, c_g1
    // We can just construct a dummy context for com_ctx because evmlr_commit_t only holds K_SIS polynomials
    // and doesn't rely on the context for initialization of its own fields.
    // Wait, let's look at evmlr_commit.h: typedef struct { nmod_poly_mat_t c; } evmlr_commit_struct;
    // So evmlr_commit_t is just a nmod_poly_mat_t of size K_SIS x 1.
    // We can initialize it directly with nmod_poly_mat_init(proof->c_g->c, ctx->k, 1, MOD_Q)
    nmod_poly_mat_init(proof->c_g->c, ctx->k, 1, MOD_Q);
    nmod_poly_mat_init(proof->c_g1->c, ctx->k, 1, MOD_Q);
    
    nmod_poly_mat_init(proof->w, ctx->k, 1, MOD_Q);
    nmod_poly_mat_init(proof->w_g, ctx->k, 1, MOD_Q);
    nmod_poly_mat_init(proof->w_g1, ctx->k, 1, MOD_Q);
    
    nmod_poly_init(proof->h, MOD_Q);
    nmod_poly_init(proof->v, MOD_Q);
    
    nmod_poly_mat_init(proof->z_m, ctx->L, 1, MOD_Q);
    nmod_poly_mat_init(proof->z_r, ctx->m, 1, MOD_Q);
    nmod_poly_init(proof->z_g, MOD_Q);
    nmod_poly_mat_init(proof->z_rg, ctx->m, 1, MOD_Q);
    nmod_poly_init(proof->z_g1, MOD_Q);
    nmod_poly_mat_init(proof->z_rg1, ctx->m, 1, MOD_Q);
}

void evmlr_bin_proof_clear(evmlr_bin_proof_t proof) {
    evmlr_commit_clear(proof->c_g);
    evmlr_commit_clear(proof->c_g1);
    
    nmod_poly_mat_clear(proof->w);
    nmod_poly_mat_clear(proof->w_g);
    nmod_poly_mat_clear(proof->w_g1);
    
    nmod_poly_clear(proof->h);
    nmod_poly_clear(proof->v);
    
    nmod_poly_mat_clear(proof->z_m);
    nmod_poly_mat_clear(proof->z_r);
    nmod_poly_clear(proof->z_g);
    nmod_poly_mat_clear(proof->z_rg);
    nmod_poly_clear(proof->z_g1);
    nmod_poly_mat_clear(proof->z_rg1);
}



// Compute automorphism \sigma_{-1}(P)(X) = P(X^{-1}) in R_q
static void poly_automorphism_minus1(nmod_poly_t out, const nmod_poly_t in) {
    nmod_poly_zero(out);
    slong len = nmod_poly_length(in);
    if (len > 0) {
        nmod_poly_set_coeff_ui(out, 0, nmod_poly_get_coeff_ui(in, 0));
    }
    for (slong i = 1; i < DEGREE_N; i++) {
        ulong coeff = 0;
        if (i < len) {
            coeff = nmod_poly_get_coeff_ui(in, i);
        }
        if (coeff > 0) {
            nmod_poly_set_coeff_ui(out, DEGREE_N - i, MOD_Q - coeff);
        }
    }
}

int evmlr_bin_prove(evmlr_bin_proof_t proof,
                    const nmod_poly_mat_t A_1,
                    const nmod_poly_mat_t A_2,
                    const nmod_poly_mat_t m,
                    const nmod_poly_mat_t r,
                    const nmod_poly_mat_t c,
                    const evmlr_bin_proof_ctx_t ctx,
                    flint_rand_t state) {
    
    // We need BDLOP commitment context to make commitments
    evmlr_commit_ctx_t com_ctx;
    com_ctx->b_sqr = 0; // not used in evmlr_commit
    com_ctx->N = ctx->L;
    nmod_poly_mat_init(com_ctx->A_1, ctx->k, ctx->L, MOD_Q);
    nmod_poly_mat_set(com_ctx->A_1, A_1);
    nmod_poly_mat_init(com_ctx->A_2, ctx->k, ctx->m, MOD_Q);
    nmod_poly_mat_set(com_ctx->A_2, A_2);
    nmod_poly_init(com_ctx->cyclo_poly, MOD_Q);
    nmod_poly_set(com_ctx->cyclo_poly, ctx->cyclo_poly);

    nmod_poly_t one;
    nmod_poly_init(one, MOD_Q);
    nmod_poly_one(one);

    // 1. Prover samples g with g_0 = 0
    nmod_poly_t g;
    nmod_poly_init(g, MOD_Q);
    // Sample g coefficients, forcing g_0 = 0
    evmlr_utils_uniform_poly(g, DEGREE_N);
    nmod_poly_set_coeff_ui(g, 0, 0);
    
    nmod_poly_mat_t g_vec;
    nmod_poly_mat_init(g_vec, ctx->L, 1, MOD_Q);
    nmod_poly_mat_zero(g_vec);
    nmod_poly_set(nmod_poly_mat_entry(g_vec, 0, 0), g);

    nmod_poly_mat_t r_g;
    nmod_poly_mat_init(r_g, 2 * K_SIS, 1, MOD_Q);
    evmlr_commit_sample_r(r_g);

    // c_g was initialised by evmlr_bin_proof_init; evmlr_commit only fills it in.
    evmlr_commit(proof->c_g, g_vec, r_g, com_ctx);

    // 2. Prover samples masking vectors
    nmod_poly_mat_t y_m, y_r, y_rg, y_rg1;
    nmod_poly_t y_g, y_g1;
    nmod_poly_mat_init(y_m, ctx->L, 1, MOD_Q);
    nmod_poly_mat_init(y_r, ctx->m, 1, MOD_Q);
    nmod_poly_mat_init(y_rg, ctx->m, 1, MOD_Q);
    nmod_poly_mat_init(y_rg1, ctx->m, 1, MOD_Q);
    nmod_poly_init(y_g, MOD_Q);
    nmod_poly_init(y_g1, MOD_Q);

    nmod_poly_mat_t tmp_mat;
    nmod_poly_mat_init(tmp_mat, ctx->k, 1, MOD_Q);
    nmod_poly_mat_t y_g_vec;
    nmod_poly_mat_init(y_g_vec, ctx->L, 1, MOD_Q);
    
    nmod_poly_t F_j, m_j_minus1, sigma_m_j, sigma_y_j, term1, term2, term3;
    nmod_poly_init(F_j, MOD_Q);
    nmod_poly_init(m_j_minus1, MOD_Q);
    nmod_poly_init(sigma_m_j, MOD_Q);
    nmod_poly_init(sigma_y_j, MOD_Q);
    nmod_poly_init(term1, MOD_Q);
    nmod_poly_init(term2, MOD_Q);
    nmod_poly_init(term3, MOD_Q);

    nmod_poly_t poly_ones;
    nmod_poly_init(poly_ones, MOD_Q);
    for (slong i = 0; i < DEGREE_N; i++) {
        nmod_poly_set_coeff_ui(poly_ones, i, 1);
    }

    nmod_poly_t g_1;
    nmod_poly_init(g_1, MOD_Q);

    nmod_poly_mat_t g1_vec;
    nmod_poly_mat_init(g1_vec, ctx->L, 1, MOD_Q);

    nmod_poly_mat_t r_g1;
    nmod_poly_mat_init(r_g1, 2 * K_SIS, 1, MOD_Q);

    nmod_poly_mat_t y_g1_vec;
    nmod_poly_mat_init(y_g1_vec, ctx->L, 1, MOD_Q);

    nmod_poly_t c_chal;
    nmod_poly_init(c_chal, MOD_Q);

    nmod_poly_t cs_i;
    nmod_poly_init(cs_i, MOD_Q);

    ulong* mu = malloc(ctx->L * sizeof(ulong));

    // Shift matrices for Gaussian rejection sampling
    nmod_poly_mat_t v_m, v_r, v_rg, v_rg1;
    if (ctx->use_gaussian) {
        nmod_poly_mat_init(v_m, ctx->L, 1, MOD_Q);
        nmod_poly_mat_init(v_r, ctx->m, 1, MOD_Q);
        nmod_poly_mat_init(v_rg, ctx->m, 1, MOD_Q);
        nmod_poly_mat_init(v_rg1, ctx->m, 1, MOD_Q);
    }

    int success = 0;
    while (!success) {
        if (ctx->use_gaussian) {
            // Sample y_m using dg_ctx_m
            discrete_gaussian_ctx_struct* dg_m = (discrete_gaussian_ctx_struct*)ctx->dg_ctx_m;
            for (slong i = 0; i < ctx->L; i++) {
                nmod_poly_struct* poly = nmod_poly_mat_entry(y_m, i, 0);
                nmod_poly_zero(poly);
                for (slong d = 0; d < DEGREE_N; d++) {
                    int64_t val = discrete_gaussian(0.0, dg_m);
                    ulong val_mod = (val % MOD_Q + MOD_Q) % MOD_Q;
                    nmod_poly_set_coeff_ui(poly, d, val_mod);
                }
            }
            // Sample y_r, y_rg, y_rg1 using dg_ctx_r
            discrete_gaussian_ctx_struct* dg_r = (discrete_gaussian_ctx_struct*)ctx->dg_ctx_r;
            nmod_poly_mat_t* mats[3] = {&y_r, &y_rg, &y_rg1};
            for (int m_idx = 0; m_idx < 3; m_idx++) {
                nmod_poly_mat_t* mat = mats[m_idx];
                for (slong i = 0; i < ctx->m; i++) {
                    nmod_poly_struct* poly = nmod_poly_mat_entry(*mat, i, 0);
                    nmod_poly_zero(poly);
                    for (slong d = 0; d < DEGREE_N; d++) {
                        int64_t val = discrete_gaussian(0.0, dg_r);
                        ulong val_mod = (val % MOD_Q + MOD_Q) % MOD_Q;
                        nmod_poly_set_coeff_ui(poly, d, val_mod);
                    }
                }
            }
        } else {
            // Resample masking vectors using linear sampling based on the papers
            evmlr_utils_linear_sample_mat_ring(y_m, ctx->beta);
            evmlr_utils_linear_sample_mat_ring(y_r, ctx->beta);
            evmlr_utils_linear_sample_mat_ring(y_rg, ctx->beta);
            evmlr_utils_linear_sample_mat_ring(y_rg1, ctx->beta);
        }
        
        // Sample y_g with y_g_0 = 0
        evmlr_utils_uniform_poly(y_g, DEGREE_N);
        nmod_poly_set_coeff_ui(y_g, 0, 0);
        // Sample y_g1 normally
        evmlr_utils_uniform_poly(y_g1, DEGREE_N);

        // 3. Prover computes masking commitments w, w_g
        nmod_poly_mat_mul(proof->w, A_1, y_m);
        for (slong i = 0; i < ctx->k; i++) {
            nmod_poly_struct* w_i = nmod_poly_mat_entry(proof->w, i, 0);
            evmlr_crt_mulmod(w_i, w_i, one, ctx->cyclo_poly);
        }
        nmod_poly_mat_mul(tmp_mat, A_2, y_r);
        for (slong i = 0; i < ctx->k; i++) {
            nmod_poly_struct* tmp_i = nmod_poly_mat_entry(tmp_mat, i, 0);
            evmlr_crt_mulmod(tmp_i, tmp_i, one, ctx->cyclo_poly);
        }
        nmod_poly_mat_add(proof->w, proof->w, tmp_mat);

        nmod_poly_mat_zero(y_g_vec);
        nmod_poly_set(nmod_poly_mat_entry(y_g_vec, 0, 0), y_g);
        
        nmod_poly_mat_mul(proof->w_g, A_1, y_g_vec);
        for (slong i = 0; i < ctx->k; i++) {
            nmod_poly_struct* w_i = nmod_poly_mat_entry(proof->w_g, i, 0);
            evmlr_crt_mulmod(w_i, w_i, one, ctx->cyclo_poly);
        }
        nmod_poly_mat_mul(tmp_mat, A_2, y_rg);
        for (slong i = 0; i < ctx->k; i++) {
            nmod_poly_struct* tmp_i = nmod_poly_mat_entry(tmp_mat, i, 0);
            evmlr_crt_mulmod(tmp_i, tmp_i, one, ctx->cyclo_poly);
        }
        nmod_poly_mat_add(proof->w_g, proof->w_g, tmp_mat);

        // 4. Generate first round challenges: \mu_j and \gamma
        evmlr_challenge_t chal;
        evmlr_challenge_init(chal);
        evmlr_challenge_add_matrix(chal, A_1);
        evmlr_challenge_add_matrix(chal, A_2);
        evmlr_challenge_add_matrix(chal, c);
        evmlr_challenge_add_matrix(chal, proof->c_g->c);
        evmlr_challenge_add_matrix(chal, proof->w);
        evmlr_challenge_add_matrix(chal, proof->w_g);

        evmlr_challenge_get_vector(mu, ctx->L, chal);

        ulong gamma_val;
        evmlr_challenge_get_val(&gamma_val, chal);

        // 5. Prover computes h, g_1, commitment c_g1, and v
        nmod_poly_zero(proof->h);
        nmod_poly_zero(g_1);

        for (slong j = 0; j < ctx->L; j++) {
            nmod_poly_struct* m_j = nmod_poly_mat_entry(m, j, 0);
            nmod_poly_struct* y_m_j = nmod_poly_mat_entry(y_m, j, 0);

            // F_j(m) = \sigma_{-1}(m_j) * (m_j - \mathbf{1})
            poly_automorphism_minus1(sigma_m_j, m_j);
            nmod_poly_sub(m_j_minus1, m_j, poly_ones);
            evmlr_crt_mulmod(F_j, sigma_m_j, m_j_minus1, ctx->cyclo_poly);

            // h += mu_j * F_j
            nmod_poly_scalar_mul_nmod(F_j, F_j, mu[j]);
            nmod_poly_add(proof->h, proof->h, F_j);

            // g_1 += mu_j * ( \sigma_{-1}(m_j) y_{m, j} + \sigma_{-1}(y_{m, j}) (m_j - 1) )
            poly_automorphism_minus1(sigma_y_j, y_m_j);
            evmlr_crt_mulmod(term1, sigma_m_j, y_m_j, ctx->cyclo_poly);
            evmlr_crt_mulmod(term2, sigma_y_j, m_j_minus1, ctx->cyclo_poly);
            nmod_poly_add(term3, term1, term2);
            nmod_poly_scalar_mul_nmod(term3, term3, mu[j]);
            nmod_poly_add(g_1, g_1, term3);
        }
        // h = g + gamma * h
        nmod_poly_scalar_mul_nmod(proof->h, proof->h, gamma_val);
        nmod_poly_add(proof->h, proof->h, g);

        // g_1 = gamma * g_1 + y_g
        nmod_poly_scalar_mul_nmod(g_1, g_1, gamma_val);
        nmod_poly_add(g_1, g_1, y_g);

        nmod_poly_mat_zero(g1_vec);
        nmod_poly_set(nmod_poly_mat_entry(g1_vec, 0, 0), g_1);

        evmlr_commit_sample_r(r_g1);
        // c_g1 was initialised by evmlr_bin_proof_init.
        evmlr_commit(proof->c_g1, g1_vec, r_g1, com_ctx);

        // w_g1
        nmod_poly_mat_zero(y_g1_vec);
        nmod_poly_set(nmod_poly_mat_entry(y_g1_vec, 0, 0), y_g1);

        nmod_poly_mat_mul(proof->w_g1, A_1, y_g1_vec);
        for (slong i = 0; i < ctx->k; i++) {
            nmod_poly_struct* w_i = nmod_poly_mat_entry(proof->w_g1, i, 0);
            evmlr_crt_mulmod(w_i, w_i, one, ctx->cyclo_poly);
        }
        nmod_poly_mat_mul(tmp_mat, A_2, y_rg1);
        for (slong i = 0; i < ctx->k; i++) {
            nmod_poly_struct* tmp_i = nmod_poly_mat_entry(tmp_mat, i, 0);
            evmlr_crt_mulmod(tmp_i, tmp_i, one, ctx->cyclo_poly);
        }
        nmod_poly_mat_add(proof->w_g1, proof->w_g1, tmp_mat);

        // v = gamma * \sum mu_j * \sigma_{-1}(y_{m, j}) * y_{m, j} - y_g1
        nmod_poly_zero(proof->v);
        for (slong j = 0; j < ctx->L; j++) {
            nmod_poly_struct* y_m_j = nmod_poly_mat_entry(y_m, j, 0);
            poly_automorphism_minus1(sigma_y_j, y_m_j);
            evmlr_crt_mulmod(term1, sigma_y_j, y_m_j, ctx->cyclo_poly);
            nmod_poly_scalar_mul_nmod(term1, term1, mu[j]);
            nmod_poly_add(proof->v, proof->v, term1);
        }
        nmod_poly_scalar_mul_nmod(proof->v, proof->v, gamma_val);
        nmod_poly_sub(proof->v, proof->v, y_g1);

        // 6. Generate second round challenge: c_chal
        evmlr_challenge_init(chal);
        evmlr_challenge_add_matrix(chal, A_1);
        evmlr_challenge_add_matrix(chal, A_2);
        evmlr_challenge_add_matrix(chal, c);
        evmlr_challenge_add_matrix(chal, proof->c_g->c);
        evmlr_challenge_add_matrix(chal, proof->c_g1->c);
        evmlr_challenge_add_matrix(chal, proof->w);
        evmlr_challenge_add_matrix(chal, proof->w_g);
        evmlr_challenge_add_matrix(chal, proof->w_g1);
        evmlr_challenge_add_poly(chal, proof->h);
        evmlr_challenge_add_poly(chal, proof->v);

        evmlr_challenge_get_poly_symmetric(c_chal, chal);

        // 7. Compute responses
        // z_m = c_chal * m + y_m
        for (slong i = 0; i < ctx->L; i++) {
            evmlr_crt_mulmod(cs_i, c_chal, nmod_poly_mat_entry(m, i, 0), ctx->cyclo_poly);
            nmod_poly_add(nmod_poly_mat_entry(proof->z_m, i, 0), nmod_poly_mat_entry(y_m, i, 0), cs_i);
        }
        // z_r = c_chal * r + y_r
        for (slong i = 0; i < ctx->m; i++) {
            evmlr_crt_mulmod(cs_i, c_chal, nmod_poly_mat_entry(r, i, 0), ctx->cyclo_poly);
            nmod_poly_add(nmod_poly_mat_entry(proof->z_r, i, 0), nmod_poly_mat_entry(y_r, i, 0), cs_i);
        }
        // z_g = c_chal * g + y_g
        evmlr_crt_mulmod(proof->z_g, c_chal, g, ctx->cyclo_poly);
        nmod_poly_add(proof->z_g, proof->z_g, y_g);
        // z_rg = c_chal * r_g + y_rg
        for (slong i = 0; i < ctx->m; i++) {
            evmlr_crt_mulmod(cs_i, c_chal, nmod_poly_mat_entry(r_g, i, 0), ctx->cyclo_poly);
            nmod_poly_add(nmod_poly_mat_entry(proof->z_rg, i, 0), nmod_poly_mat_entry(y_rg, i, 0), cs_i);
        }
        // z_g1 = c_chal * g_1 + y_g1
        evmlr_crt_mulmod(proof->z_g1, c_chal, g_1, ctx->cyclo_poly);
        nmod_poly_add(proof->z_g1, proof->z_g1, y_g1);
        // z_rg1 = c_chal * r_g1 + y_rg1
        for (slong i = 0; i < ctx->m; i++) {
            evmlr_crt_mulmod(cs_i, c_chal, nmod_poly_mat_entry(r_g1, i, 0), ctx->cyclo_poly);
            nmod_poly_add(nmod_poly_mat_entry(proof->z_rg1, i, 0), nmod_poly_mat_entry(y_rg1, i, 0), cs_i);
        }

        // Rejection Check
        if (ctx->use_gaussian) {
            // Compute shift vectors
            for (slong i = 0; i < ctx->L; i++) {
                evmlr_crt_mulmod(nmod_poly_mat_entry(v_m, i, 0), c_chal, nmod_poly_mat_entry(m, i, 0), ctx->cyclo_poly);
            }
            for (slong i = 0; i < ctx->m; i++) {
                evmlr_crt_mulmod(nmod_poly_mat_entry(v_r, i, 0), c_chal, nmod_poly_mat_entry(r, i, 0), ctx->cyclo_poly);
            }
            for (slong i = 0; i < ctx->m; i++) {
                evmlr_crt_mulmod(nmod_poly_mat_entry(v_rg, i, 0), c_chal, nmod_poly_mat_entry(r_g, i, 0), ctx->cyclo_poly);
            }
            for (slong i = 0; i < ctx->m; i++) {
                evmlr_crt_mulmod(nmod_poly_mat_entry(v_rg1, i, 0), c_chal, nmod_poly_mat_entry(r_g1, i, 0), ctx->cyclo_poly);
            }

            success = 1;
            double M = 1.75;
            uint64_t rnd;
            double u;

            // z_m check
            int64_t dot_m = nmod_poly_mat_dot_product(proof->z_m, v_m);
            int64_t norm_m = nmod_poly_mat_sq_norm(v_m);
            double r_m_val = -2.0 * (double)dot_m + (double)norm_m;
            r_m_val = r_m_val / (2.0 * (double)ctx->s2_m);
            r_m_val = exp(r_m_val) / M;
            fastrandombytes((unsigned char*)&rnd, sizeof(rnd));
            u = (double)(rnd & 0x1FFFFFFFFFFFFFULL) / (double)(1ULL << 53);
            if (u > r_m_val) success = 0;

            // z_r check
            if (success) {
                int64_t dot_r = nmod_poly_mat_dot_product(proof->z_r, v_r);
                int64_t norm_r = nmod_poly_mat_sq_norm(v_r);
                double r_r_val = -2.0 * (double)dot_r + (double)norm_r;
                r_r_val = r_r_val / (2.0 * (double)ctx->s2_r);
                r_r_val = exp(r_r_val) / M;
                fastrandombytes((unsigned char*)&rnd, sizeof(rnd));
                u = (double)(rnd & 0x1FFFFFFFFFFFFFULL) / (double)(1ULL << 53);
                if (u > r_r_val) success = 0;
            }

            // z_rg check
            if (success) {
                int64_t dot_rg = nmod_poly_mat_dot_product(proof->z_rg, v_rg);
                int64_t norm_rg = nmod_poly_mat_sq_norm(v_rg);
                double r_rg_val = -2.0 * (double)dot_rg + (double)norm_rg;
                r_rg_val = r_rg_val / (2.0 * (double)ctx->s2_r);
                r_rg_val = exp(r_rg_val) / M;
                fastrandombytes((unsigned char*)&rnd, sizeof(rnd));
                u = (double)(rnd & 0x1FFFFFFFFFFFFFULL) / (double)(1ULL << 53);
                if (u > r_rg_val) success = 0;
            }

            // z_rg1 check
            if (success) {
                int64_t dot_rg1 = nmod_poly_mat_dot_product(proof->z_rg1, v_rg1);
                int64_t norm_rg1 = nmod_poly_mat_sq_norm(v_rg1);
                double r_rg1_val = -2.0 * (double)dot_rg1 + (double)norm_rg1;
                r_rg1_val = r_rg1_val / (2.0 * (double)ctx->s2_r);
                r_rg1_val = exp(r_rg1_val) / M;
                fastrandombytes((unsigned char*)&rnd, sizeof(rnd));
                u = (double)(rnd & 0x1FFFFFFFFFFFFFULL) / (double)(1ULL << 53);
                if (u > r_rg1_val) success = 0;
            }
            
            // Norm checks
            if (success) {
                int64_t sq_norm_m = nmod_poly_mat_sq_norm(proof->z_m);
                double bound_m = 4.0 * (double)DEGREE_N * (double)ctx->s2_m;
                if ((double)sq_norm_m > bound_m) success = 0;
            }
            if (success) {
                int64_t sq_norm_r = nmod_poly_mat_sq_norm(proof->z_r);
                double bound_r = 4.0 * (double)DEGREE_N * (double)ctx->s2_r;
                if ((double)sq_norm_r > bound_r) success = 0;
            }
            if (success) {
                int64_t sq_norm_rg = nmod_poly_mat_sq_norm(proof->z_rg);
                double bound_rg = 4.0 * (double)DEGREE_N * (double)ctx->s2_r;
                if ((double)sq_norm_rg > bound_rg) success = 0;
            }
            if (success) {
                int64_t sq_norm_rg1 = nmod_poly_mat_sq_norm(proof->z_rg1);
                double bound_rg1 = 4.0 * (double)DEGREE_N * (double)ctx->s2_r;
                if ((double)sq_norm_rg1 > bound_rg1) success = 0;
            }
        } else {
            // Rejection Check: verify all small responses are bounded by beta
            success = 1;
            if (!evmlr_utils_is_bounded(proof->z_m, ctx->beta)) success = 0;
            if (!evmlr_utils_is_bounded(proof->z_r, ctx->beta)) success = 0;
            if (!evmlr_utils_is_bounded(proof->z_rg, ctx->beta)) success = 0;
            if (!evmlr_utils_is_bounded(proof->z_rg1, ctx->beta)) success = 0;
        }

    }

    // Cleanup
    if (ctx->use_gaussian) {
        nmod_poly_mat_clear(v_m);
        nmod_poly_mat_clear(v_r);
        nmod_poly_mat_clear(v_rg);
        nmod_poly_mat_clear(v_rg1);
    }

    free(mu);
    nmod_poly_clear(one);
    nmod_poly_clear(g);
    nmod_poly_mat_clear(g_vec);
    nmod_poly_mat_clear(r_g);
    nmod_poly_mat_clear(r_g1);
    nmod_poly_mat_clear(y_m);
    nmod_poly_mat_clear(y_r);
    nmod_poly_mat_clear(y_rg);
    nmod_poly_mat_clear(y_rg1);
    nmod_poly_clear(y_g);
    nmod_poly_clear(y_g1);
    nmod_poly_mat_clear(tmp_mat);
    nmod_poly_mat_clear(y_g_vec);
    nmod_poly_clear(F_j);
    nmod_poly_clear(m_j_minus1);
    nmod_poly_clear(sigma_m_j);
    nmod_poly_clear(sigma_y_j);
    nmod_poly_clear(term1);
    nmod_poly_clear(term2);
    nmod_poly_clear(term3);
    nmod_poly_clear(g_1);
    nmod_poly_mat_clear(g1_vec);
    nmod_poly_mat_clear(y_g1_vec);
    nmod_poly_clear(c_chal);
    nmod_poly_clear(cs_i);
    nmod_poly_clear(poly_ones);
    evmlr_commit_ctx_clear(com_ctx);

    return 1;
}

int evmlr_bin_verify(const evmlr_bin_proof_t proof,
                     const nmod_poly_mat_t A_1,
                     const nmod_poly_mat_t A_2,
                     const nmod_poly_mat_t c,
                     const evmlr_bin_proof_ctx_t ctx) {
    nmod_poly_t one, poly_ones;
    nmod_poly_init(one, MOD_Q);
    nmod_poly_one(one);
    nmod_poly_init(poly_ones, MOD_Q);
    for (slong i = 0; i < DEGREE_N; i++) {
        nmod_poly_set_coeff_ui(poly_ones, i, 1);
    }

    // 1. Generate first round challenges: \mu_j and \gamma
    evmlr_challenge_t chal;
    evmlr_challenge_init(chal);
    evmlr_challenge_add_matrix(chal, A_1);
    evmlr_challenge_add_matrix(chal, A_2);
    evmlr_challenge_add_matrix(chal, c);
    evmlr_challenge_add_matrix(chal, proof->c_g->c);
    evmlr_challenge_add_matrix(chal, proof->w);
    evmlr_challenge_add_matrix(chal, proof->w_g);

    ulong* mu = malloc(ctx->L * sizeof(ulong));
    evmlr_challenge_get_vector(mu, ctx->L, chal);

    ulong gamma_val;
    evmlr_challenge_get_val(&gamma_val, chal);

    // 2. Generate second round challenge: c_chal
    evmlr_challenge_init(chal);
    evmlr_challenge_add_matrix(chal, A_1);
    evmlr_challenge_add_matrix(chal, A_2);
    evmlr_challenge_add_matrix(chal, c);
    evmlr_challenge_add_matrix(chal, proof->c_g->c);
    evmlr_challenge_add_matrix(chal, proof->c_g1->c);
    evmlr_challenge_add_matrix(chal, proof->w);
    evmlr_challenge_add_matrix(chal, proof->w_g);
    evmlr_challenge_add_matrix(chal, proof->w_g1);
    evmlr_challenge_add_poly(chal, proof->h);
    evmlr_challenge_add_poly(chal, proof->v);

    nmod_poly_t c_chal;
    nmod_poly_init(c_chal, MOD_Q);
    evmlr_challenge_get_poly_symmetric(c_chal, chal);

    int valid = 1;

    // Check 1: A_1 z_m + A_2 z_r - c_chal * c == w
    nmod_poly_mat_t lhs, ct;
    nmod_poly_mat_init(lhs, ctx->k, 1, MOD_Q);
    nmod_poly_mat_init(ct, ctx->k, 1, MOD_Q);

    nmod_poly_mat_mulmod(lhs, A_1, proof->z_m, ctx->cyclo_poly);
    nmod_poly_mat_t tmp_mat;
    nmod_poly_mat_init(tmp_mat, ctx->k, 1, MOD_Q);
    nmod_poly_mat_mulmod(tmp_mat, A_2, proof->z_r, ctx->cyclo_poly);
    nmod_poly_mat_add(lhs, lhs, tmp_mat);

    for (slong i = 0; i < ctx->k; i++) {
        evmlr_crt_mulmod(nmod_poly_mat_entry(ct, i, 0), c_chal, nmod_poly_mat_entry(c, i, 0), ctx->cyclo_poly);
    }
    nmod_poly_mat_sub(lhs, lhs, ct);
    int check1 = nmod_poly_mat_equal(lhs, proof->w);
    valid &= check1;

    // Check 2: A_{1,0} z_g + A_2 z_rg - c_chal * c_g == w_g
    nmod_poly_mat_t A1_col0;
    nmod_poly_mat_init(A1_col0, ctx->k, 1, MOD_Q);
    for (slong i = 0; i < ctx->k; i++) {
        nmod_poly_set(nmod_poly_mat_entry(A1_col0, i, 0), nmod_poly_mat_entry(A_1, i, 0));
    }
    
    nmod_poly_mat_t z_g_vec;
    nmod_poly_mat_init(z_g_vec, 1, 1, MOD_Q);
    nmod_poly_set(nmod_poly_mat_entry(z_g_vec, 0, 0), proof->z_g);

    nmod_poly_mat_mulmod(lhs, A1_col0, z_g_vec, ctx->cyclo_poly);
    nmod_poly_mat_mulmod(tmp_mat, A_2, proof->z_rg, ctx->cyclo_poly);
    nmod_poly_mat_add(lhs, lhs, tmp_mat);

    for (slong i = 0; i < ctx->k; i++) {
        evmlr_crt_mulmod(nmod_poly_mat_entry(ct, i, 0), c_chal, nmod_poly_mat_entry(proof->c_g->c, i, 0), ctx->cyclo_poly);
    }
    nmod_poly_mat_sub(lhs, lhs, ct);
    int check2 = nmod_poly_mat_equal(lhs, proof->w_g);
    valid &= check2;

    // Check 3: A_{1,0} z_g1 + A_2 z_rg1 - c_chal * c_g1 == w_g1
    nmod_poly_mat_t z_g1_vec;
    nmod_poly_mat_init(z_g1_vec, 1, 1, MOD_Q);
    nmod_poly_set(nmod_poly_mat_entry(z_g1_vec, 0, 0), proof->z_g1);

    nmod_poly_mat_mulmod(lhs, A1_col0, z_g1_vec, ctx->cyclo_poly);
    nmod_poly_mat_mulmod(tmp_mat, A_2, proof->z_rg1, ctx->cyclo_poly);
    nmod_poly_mat_add(lhs, lhs, tmp_mat);

    for (slong i = 0; i < ctx->k; i++) {
        evmlr_crt_mulmod(nmod_poly_mat_entry(ct, i, 0), c_chal, nmod_poly_mat_entry(proof->c_g1->c, i, 0), ctx->cyclo_poly);
    }
    nmod_poly_mat_sub(lhs, lhs, ct);
    int check3 = nmod_poly_mat_equal(lhs, proof->w_g1);
    valid &= check3;

    // Check 4: Constant coefficient of h is 0
    int check4 = (nmod_poly_get_coeff_ui(proof->h, 0) == 0);
    valid &= check4;

    // Check 5: LHS - z_g1 == v
    // LHS = \gamma \sum \mu_j \sigma_{-1}(z_{m, j}) z_{m, j} + c_chal * z_g - \gamma * c_chal * \sum \mu_j \sigma_{-1}(z_{m, j}) - c_chal^2 * h
    nmod_poly_t lhs_poly, sum_quad, sum_lin, sigma_z_j, term1;
    nmod_poly_init(lhs_poly, MOD_Q);
    nmod_poly_init(sum_quad, MOD_Q);
    nmod_poly_init(sum_lin, MOD_Q);
    nmod_poly_init(sigma_z_j, MOD_Q);
    nmod_poly_init(term1, MOD_Q);

    nmod_poly_zero(sum_quad);
    nmod_poly_zero(sum_lin);

    for (slong j = 0; j < ctx->L; j++) {
        nmod_poly_struct* z_m_j = nmod_poly_mat_entry(proof->z_m, j, 0);
        poly_automorphism_minus1(sigma_z_j, z_m_j);
        
        // quad = \sigma_{-1}(z_{m, j}) * z_{m, j}
        evmlr_crt_mulmod(term1, sigma_z_j, z_m_j, ctx->cyclo_poly);
        nmod_poly_scalar_mul_nmod(term1, term1, mu[j]);
        nmod_poly_add(sum_quad, sum_quad, term1);

        // lin = \sigma_{-1}(z_{m, j}) * \mathbf{1}
        evmlr_crt_mulmod(term1, sigma_z_j, poly_ones, ctx->cyclo_poly);
        nmod_poly_scalar_mul_nmod(term1, term1, mu[j]);
        nmod_poly_add(sum_lin, sum_lin, term1);
    }

    // lhs_poly = gamma * sum_quad
    nmod_poly_scalar_mul_nmod(lhs_poly, sum_quad, gamma_val);
    
    // + c_chal * z_g
    evmlr_crt_mulmod(term1, c_chal, proof->z_g, ctx->cyclo_poly);
    nmod_poly_add(lhs_poly, lhs_poly, term1);

    // - gamma * c_chal * sum_lin
    evmlr_crt_mulmod(term1, c_chal, sum_lin, ctx->cyclo_poly);
    nmod_poly_scalar_mul_nmod(term1, term1, gamma_val);
    nmod_poly_sub(lhs_poly, lhs_poly, term1);

    // - c_chal^2 * h
    evmlr_crt_mulmod(term1, c_chal, c_chal, ctx->cyclo_poly);
    evmlr_crt_mulmod(term1, term1, proof->h, ctx->cyclo_poly);
    nmod_poly_sub(lhs_poly, lhs_poly, term1);

    // LHS - z_g1
    nmod_poly_sub(lhs_poly, lhs_poly, proof->z_g1);

    int check5 = nmod_poly_equal(lhs_poly, proof->v);
    valid &= check5;

    // Check 6: Small responses are bounded by beta or Gaussian norm checked
    int check6 = 1;
    if (ctx->use_gaussian) {
        int64_t sq_norm_m = nmod_poly_mat_sq_norm(proof->z_m);
        double bound_m = 4.0 * (double)DEGREE_N * (double)ctx->s2_m;
        if ((double)sq_norm_m > bound_m) check6 = 0;

        int64_t sq_norm_r = nmod_poly_mat_sq_norm(proof->z_r);
        double bound_r = 4.0 * (double)DEGREE_N * (double)ctx->s2_r;
        if ((double)sq_norm_r > bound_r) check6 = 0;

        int64_t sq_norm_rg = nmod_poly_mat_sq_norm(proof->z_rg);
        double bound_rg = 4.0 * (double)DEGREE_N * (double)ctx->s2_r;
        if ((double)sq_norm_rg > bound_rg) check6 = 0;

        int64_t sq_norm_rg1 = nmod_poly_mat_sq_norm(proof->z_rg1);
        double bound_rg1 = 4.0 * (double)DEGREE_N * (double)ctx->s2_r;
        if ((double)sq_norm_rg1 > bound_rg1) check6 = 0;
    } else {
        if (!evmlr_utils_is_bounded(proof->z_m, ctx->beta)) check6 = 0;
        if (!evmlr_utils_is_bounded(proof->z_r, ctx->beta)) check6 = 0;
        if (!evmlr_utils_is_bounded(proof->z_rg, ctx->beta)) check6 = 0;
        if (!evmlr_utils_is_bounded(proof->z_rg1, ctx->beta)) check6 = 0;
    }
    valid &= check6;

    // Cleanup
    free(mu);
    nmod_poly_clear(one);
    nmod_poly_clear(poly_ones);
    nmod_poly_clear(c_chal);
    nmod_poly_mat_clear(lhs);
    nmod_poly_mat_clear(ct);
    nmod_poly_mat_clear(tmp_mat);
    nmod_poly_mat_clear(A1_col0);
    nmod_poly_mat_clear(z_g_vec);
    nmod_poly_mat_clear(z_g1_vec);
    nmod_poly_clear(lhs_poly);
    nmod_poly_clear(sum_quad);
    nmod_poly_clear(sum_lin);
    nmod_poly_clear(sigma_z_j);
    nmod_poly_clear(term1);

    return valid;
}

#ifdef MAIN
#include "evmlr_main.h"

#include "test.h"
#include "bench.h"

void test_bin(evmlr_bin_proof_ctx_t ctx, flint_rand_t state) {
    nmod_poly_mat_t A_1, A_2, m, r;
    evmlr_commit_t com_c;
    evmlr_bin_proof_t proof;

    nmod_poly_mat_init(A_1, ctx->k, ctx->L, MOD_Q);
    nmod_poly_mat_init(A_2, ctx->k, ctx->m, MOD_Q);
    nmod_poly_mat_init(m, ctx->L, 1, MOD_Q);
    nmod_poly_mat_init(r, ctx->m, 1, MOD_Q);

    // Random A_1, A_2
    nmod_poly_mat_randtest(A_1, state, DEGREE_N);
    nmod_poly_mat_randtest(A_2, state, DEGREE_N);

    // Binary m
    nmod_poly_mat_zero(m);
    for (slong i = 0; i < ctx->L; i++) {
        // Sample binary coefficients
        for (slong coeff = 0; coeff < DEGREE_N; coeff++) {
            nmod_poly_set_coeff_ui(nmod_poly_mat_entry(m, i, 0), coeff, n_randint(state, 2));
        }
    }
    
    // Small r
    evmlr_utils_binom_sample_mat_ring(r, ETA);

    // Calculate c = A_1 m + A_2 r
    evmlr_commit_ctx_t com_ctx;
    com_ctx->N = ctx->L;
    com_ctx->b_sqr = 0;
    nmod_poly_mat_init(com_ctx->A_1, ctx->k, ctx->L, MOD_Q);
    nmod_poly_mat_set(com_ctx->A_1, A_1);
    nmod_poly_mat_init(com_ctx->A_2, ctx->k, ctx->m, MOD_Q);
    nmod_poly_mat_set(com_ctx->A_2, A_2);
    nmod_poly_init(com_ctx->cyclo_poly, MOD_Q);
    nmod_poly_set(com_ctx->cyclo_poly, ctx->cyclo_poly);

    evmlr_commit_init(com_c);
    evmlr_commit(com_c, m, r, com_ctx);

    evmlr_bin_proof_init(proof, ctx);

    TEST_BEGIN("binary proof can be created and verified") {
        int res = evmlr_bin_prove(proof, A_1, A_2, m, r, com_c->c, ctx, state);
        TEST_ASSERT(res == 1, end);
        int valid = evmlr_bin_verify(proof, A_1, A_2, com_c->c, ctx);
        TEST_ASSERT(valid == 1, end);
    } TEST_END;

    end:
        evmlr_bin_proof_clear(proof);
        nmod_poly_mat_clear(A_1);
        nmod_poly_mat_clear(A_2);
        nmod_poly_mat_clear(m);
        nmod_poly_mat_clear(r);
        evmlr_commit_clear(com_c);
        evmlr_commit_ctx_clear(com_ctx);
}

int main(int argc, char *argv[]) {
    evmlr_mode_t mode = evmlr_mode(argc, argv);

    flint_rand_t state;
    evmlr_rand_init(state);

    evmlr_bin_proof_ctx_t ctx;
    evmlr_bin_proof_ctx_init(ctx, K_SIS, 2 * K_SIS, M_LEN);

    if (evmlr_runs_tests(mode)) {
        // Test with linear sampling
        test_bin(ctx, state);

        // Test with Gaussian sampling
        evmlr_bin_proof_ctx_set_gaussian(ctx);
        test_bin(ctx, state);
    }

    evmlr_bin_proof_ctx_clear(ctx);
    flint_rand_clear(state);
    return test_status();
}
#endif
