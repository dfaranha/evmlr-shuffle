#include "evmlr_crt.h"
#include "evmlr_shuffle.h"
#include "evmlr_challenge.h"
#include "evmlr_utils.h"

#ifdef MAIN
#include "test.h"
#include "bench.h"
#endif

void lambda_setup(nmod_poly_mat_t Lambda, const nmod_poly_t lambda, const nmod_poly_t cyclo_poly, slong L);

void evmlr_shuffle_ctx_init(evmlr_shuffle_ctx_t ctx, slong N, slong L, flint_rand_t state) {
    slong com_N = N * (LOG_Q_CEIL > (2*ETA) * (K_LWE + L)
            ? LOG_Q_CEIL
            : (2*ETA) * (K_LWE + L)); // initialize with the biggest vector len used
    evmlr_commit_ctx_init(ctx->com_ctx, com_N, state);
    evmlr_hpke_ctx_init(ctx->hpke_ctx, L, state);
    ctx->N = N;
    ctx->L = L;
}

void evmlr_shuffle_ctx_clear(evmlr_shuffle_ctx_t ctx) {
    evmlr_commit_ctx_clear(ctx->com_ctx);
    evmlr_hpke_ctx_clear(ctx->hpke_ctx);
}

void evmlr_proof_init(evmlr_shuffle_proof_t proof, const evmlr_shuffle_ctx_t ctx) {
    nmod_poly_mat_init(proof->u, ctx->N - 1, 1, MOD_Q);

    evmlr_bin_proof_ctx_t ctx_com;
    evmlr_bin_proof_ctx_init(ctx_com, K_SIS, 2 * K_SIS, ctx->com_ctx->N);
    evmlr_bin_proof_init(proof->proof_D, ctx_com);
    evmlr_bin_proof_init(proof->proof_P, ctx_com);
    evmlr_bin_proof_init(proof->proof_W, ctx_com);
    evmlr_bin_proof_ctx_clear(ctx_com);

    evmlr_lin_proof_ctx_t ctx_u;
    evmlr_lin_proof_ctx_init(ctx_u, ctx->N, ctx->N * (LOG_Q_CEIL + 1 + 2*ETA*(K_LWE + ctx->L)));
    evmlr_lin_proof_init(proof->proof_u, ctx_u);
    evmlr_lin_proof_ctx_clear(ctx_u);
}

void evmlr_proof_clear(evmlr_shuffle_proof_t proof, const evmlr_shuffle_ctx_t ctx) {
    nmod_poly_mat_clear(proof->u);
    evmlr_commit_clear(proof->P);
    evmlr_commit_clear(proof->W);

    evmlr_bin_proof_clear(proof->proof_D);
    evmlr_bin_proof_clear(proof->proof_P);
    evmlr_bin_proof_clear(proof->proof_W);
    evmlr_lin_proof_clear(proof->proof_u);
}

void evmlr_shuffle_sp_clear(evmlr_shuffle_sp_t sp, const evmlr_shuffle_ctx_t ctx) {
    free(sp->pi);
    nmod_poly_mat_clear(sp->r_D);
    for (size_t i = 0; i < ctx->N; i++) {
        nmod_poly_mat_clear(sp->d_dagger[i]);
    }
    free(sp->d_dagger);
}

void evmlr_shuffle_pp_clear(evmlr_shuffle_pp_t pp, const evmlr_shuffle_ctx_t ctx) {
    evmlr_commit_clear(pp->D);
    for (size_t i = 0; i < ctx->N; i++) {
        nmod_poly_mat_clear(pp->c_hat[i]);
        evmlr_otse_ciphertext_clear(pp->c_star[i]);
    }
    free(pp->c_hat);
    free(pp->c_star);
}

static void get_challenges_1(nmod_poly_t alpha, nmod_poly_t beta, nmod_poly_t lambda,
                             const evmlr_shuffle_pp_t pp, const evmlr_commit_t P, const evmlr_shuffle_ctx_t ctx, uint8_t hash_out[SHA256HashSize]) {
    evmlr_challenge_t chal;
    evmlr_challenge_init(chal);
    /* The public parameters the relation is stated over come first: without
     * them the challenges are the same for any commitment key and any OTSE
     * matrices, so a prover free to choose those chooses them after seeing
     * alpha, beta and lambda. */
    evmlr_challenge_add_matrix(chal, ctx->com_ctx->A_1);
    evmlr_challenge_add_matrix(chal, ctx->com_ctx->A_2);
    evmlr_challenge_add_matrix(chal, ctx->hpke_ctx->otse_ctx->H);
    evmlr_challenge_add_matrix(chal, ctx->hpke_ctx->otse_ctx->H_prime);
    evmlr_challenge_add_matrix(chal, pp->D->c);
    for (slong i = 0; i < ctx->N; i++) {
        evmlr_challenge_add_matrix(chal, pp->c_hat[i]);
        evmlr_challenge_add_matrix(chal, pp->c_star[i]->c);
    }
    evmlr_challenge_add_matrix(chal, P->c);

    int degree = DEGREE_N >> 1;
    evmlr_challenge_get_poly(alpha, degree, chal);
    evmlr_challenge_get_poly(beta, degree, chal);
    evmlr_challenge_get_poly(lambda, degree, chal);

    evmlr_challenge_get_hash(hash_out, chal);
}

static void get_challenge_2(nmod_poly_t gamma, const uint8_t hash_in[SHA256HashSize], const evmlr_commit_t W) {
    evmlr_challenge_t chal;
    evmlr_challenge_init(chal);
    evmlr_challenge_add_bytes(chal, hash_in, SHA256HashSize);
    evmlr_challenge_add_matrix(chal, W->c);

    evmlr_challenge_get_poly(gamma, DEGREE_N >> 1, chal);
}

static void prove_commit(evmlr_bin_proof_t proof, const evmlr_commit_ctx_t com_ctx, const nmod_poly_mat_t m, const nmod_poly_mat_t r, const nmod_poly_mat_t c, flint_rand_t state) {
    evmlr_bin_proof_ctx_t ctx;
    evmlr_bin_proof_ctx_init(ctx, K_SIS, 2 * K_SIS, com_ctx->N);
    evmlr_bin_proof_ctx_set_gaussian(ctx);

    evmlr_bin_prove(proof, com_ctx->A_1, com_ctx->A_2, m, r, c, ctx, state);

    evmlr_bin_proof_ctx_clear(ctx);
}

static int verify_commit(const evmlr_bin_proof_t proof, const evmlr_commit_ctx_t com_ctx, const nmod_poly_mat_t c) {
    evmlr_bin_proof_ctx_t ctx;
    evmlr_bin_proof_ctx_init(ctx, K_SIS, 2 * K_SIS, com_ctx->N);
    evmlr_bin_proof_ctx_set_gaussian(ctx);

    int valid = evmlr_bin_verify(proof, com_ctx->A_1, com_ctx->A_2, c, ctx);

    evmlr_bin_proof_ctx_clear(ctx);
    return valid;
}

static void setup_A_t_u(nmod_poly_mat_t A_u, nmod_poly_mat_t t_u, const nmod_poly_mat_t u, const nmod_poly_t alpha, const nmod_poly_t beta, const nmod_poly_t lambda, const nmod_poly_t gamma, const evmlr_shuffle_ctx_t ctx, const evmlr_shuffle_pp_t pp) {
    int N = ctx->N;
    int L = ctx->L;
    int Cw = LOG_Q_CEIL;
    int Cd = 2 * ETA * (K_LWE + L);
    int cols_per_i = Cw + 1 + Cd;

    nmod_poly_mat_t Lambda;
    lambda_setup(Lambda, lambda, ctx->com_ctx->cyclo_poly, L);

    nmod_poly_mat_t h_pub, h_hat_pub;
    nmod_poly_mat_init(h_pub, N, 1, MOD_Q);
    nmod_poly_mat_init(h_hat_pub, N, 1, MOD_Q);
    
    nmod_poly_t tmp, tmp2, tmp_bin;
    nmod_poly_init(tmp, MOD_Q);
    nmod_poly_init(tmp2, MOD_Q);
    nmod_poly_init(tmp_bin, MOD_Q);
    for (int i = 0; i < N; i++) {
        nmod_poly_struct* h_pub_i = nmod_poly_mat_entry(h_pub, i, 0);
        nmod_poly_zero(h_pub_i);
        for (int j = 0; j < L; j++) {
            evmlr_crt_mulmod(tmp, nmod_poly_mat_entry(pp->c_star[i]->c, j, 0), nmod_poly_mat_entry(Lambda, j, 0), ctx->com_ctx->cyclo_poly);
            nmod_poly_add(h_pub_i, h_pub_i, tmp);
        }
        nmod_poly_zero(tmp_bin);
        evmlr_utils_int_to_bin(tmp_bin, i);
        evmlr_crt_mulmod(tmp_bin, tmp_bin, beta, ctx->com_ctx->cyclo_poly);
        nmod_poly_add(h_pub_i, h_pub_i, tmp_bin);
        nmod_poly_sub(h_pub_i, h_pub_i, alpha);

        nmod_poly_struct* h_hat_pub_i = nmod_poly_mat_entry(h_hat_pub, i, 0);
        nmod_poly_zero(h_hat_pub_i);
        for (int j = 0; j < L; j++) {
            evmlr_crt_mulmod(tmp, nmod_poly_mat_entry(pp->c_hat[i], j, 0), nmod_poly_mat_entry(Lambda, j, 0), ctx->com_ctx->cyclo_poly);
            nmod_poly_add(h_hat_pub_i, h_hat_pub_i, tmp);
        }
        nmod_poly_sub(h_hat_pub_i, h_hat_pub_i, alpha);
    }

    nmod_poly_mat_t V;
    nmod_poly_mat_init(V, 1, K_LWE + L, MOD_Q);
    nmod_poly_mat_zero(V);
    for (int j = 0; j < K_LWE + L; j++) {
        nmod_poly_struct* V_j = nmod_poly_mat_entry(V, 0, j);
        for (int k = 0; k < L; k++) {
            evmlr_crt_mulmod(tmp, nmod_poly_mat_entry(Lambda, k, 0), nmod_poly_mat_entry(ctx->hpke_ctx->otse_ctx->H_prime, k, j), ctx->com_ctx->cyclo_poly);
            nmod_poly_add(V_j, V_j, tmp);
        }
    }

    nmod_poly_mat_t M_d;
    nmod_poly_mat_init(M_d, 1, Cd, MOD_Q);
    for (int b = 0; b < 2 * ETA; b++) {
        for (int j = 0; j < K_LWE + L; j++) {
            nmod_poly_struct* Md_entry = nmod_poly_mat_entry(M_d, 0, b * (K_LWE + L) + j);
            if (b < ETA) {
                nmod_poly_set(Md_entry, nmod_poly_mat_entry(V, 0, j));
            } else {
                nmod_poly_neg(Md_entry, nmod_poly_mat_entry(V, 0, j));
            }
        }
    }

    nmod_poly_mat_t G;
    nmod_poly_mat_init(G, 1, Cw, MOD_Q);
    evmlr_utils_gadget_matrix(G, 1, Cw, MOD_Q);

    for (int i = 0; i < N; i++) {
        for (int j = 0; j < Cw; j++) {
            nmod_poly_set(nmod_poly_mat_entry(A_u, i, i * cols_per_i + j), nmod_poly_mat_entry(G, 0, j));
        }

        nmod_poly_struct* sig_coeff = nmod_poly_mat_entry(A_u, i, i * cols_per_i + Cw);
        if (i == 0) {
            evmlr_crt_mulmod(sig_coeff, gamma, beta, ctx->com_ctx->cyclo_poly);
            nmod_poly_neg(sig_coeff, sig_coeff);
        } else if (i < N - 1) {
            evmlr_crt_mulmod(sig_coeff, nmod_poly_mat_entry(u, i-1, 0), beta, ctx->com_ctx->cyclo_poly);
            nmod_poly_neg(sig_coeff, sig_coeff);
        } else {
            evmlr_crt_mulmod(sig_coeff, nmod_poly_mat_entry(u, N-2, 0), beta, ctx->com_ctx->cyclo_poly);
            nmod_poly_neg(sig_coeff, sig_coeff);
        }

        nmod_poly_t factor;
        nmod_poly_init(factor, MOD_Q);
        if (i == 0) {
            nmod_poly_set(factor, nmod_poly_mat_entry(u, 0, 0));
        } else if (i < N - 1) {
            nmod_poly_set(factor, nmod_poly_mat_entry(u, i, 0));
        } else {
            nmod_poly_set(factor, gamma);
            if (N % 2 != 0) nmod_poly_neg(factor, factor);
        }

        for (int j = 0; j < Cd; j++) {
            evmlr_crt_mulmod(nmod_poly_mat_entry(A_u, i, i * cols_per_i + Cw + 1 + j), factor, nmod_poly_mat_entry(M_d, 0, j), ctx->com_ctx->cyclo_poly);
        }
        nmod_poly_clear(factor);

        nmod_poly_struct* t_u_i = nmod_poly_mat_entry(t_u, i, 0);
        nmod_poly_struct* h_pub_i = nmod_poly_mat_entry(h_pub, i, 0);
        nmod_poly_struct* h_hat_pub_i = nmod_poly_mat_entry(h_hat_pub, i, 0);
        
        if (i == 0) {
            evmlr_crt_mulmod(tmp, gamma, h_hat_pub_i, ctx->com_ctx->cyclo_poly);
            evmlr_crt_mulmod(tmp2, nmod_poly_mat_entry(u, 0, 0), h_pub_i, ctx->com_ctx->cyclo_poly);
            nmod_poly_add(t_u_i, tmp, tmp2);
        } else if (i < N - 1) {
            evmlr_crt_mulmod(tmp, nmod_poly_mat_entry(u, i-1, 0), h_hat_pub_i, ctx->com_ctx->cyclo_poly);
            evmlr_crt_mulmod(tmp2, nmod_poly_mat_entry(u, i, 0), h_pub_i, ctx->com_ctx->cyclo_poly);
            nmod_poly_add(t_u_i, tmp, tmp2);
        } else {
            evmlr_crt_mulmod(tmp, nmod_poly_mat_entry(u, N-2, 0), h_hat_pub_i, ctx->com_ctx->cyclo_poly);
            evmlr_crt_mulmod(tmp2, gamma, h_pub_i, ctx->com_ctx->cyclo_poly);
            if (N % 2 != 0) nmod_poly_neg(tmp2, tmp2);
            nmod_poly_add(t_u_i, tmp, tmp2);
        }
    }

    nmod_poly_mat_clear(Lambda);
    nmod_poly_mat_clear(h_pub); nmod_poly_mat_clear(h_hat_pub);
    nmod_poly_clear(tmp); nmod_poly_clear(tmp2); nmod_poly_clear(tmp_bin);
    nmod_poly_mat_clear(V); nmod_poly_mat_clear(M_d);
    nmod_poly_mat_clear(G);
}

static void prove_u(evmlr_lin_proof_t lin_proof, const nmod_poly_mat_t w_dagger[], const nmod_poly_mat_t sigma, const evmlr_shuffle_sp_t sp, const nmod_poly_mat_t u, const nmod_poly_t alpha, const nmod_poly_t beta, const nmod_poly_t lambda, const nmod_poly_t gamma, const evmlr_shuffle_ctx_t ctx, const evmlr_shuffle_pp_t pp) {
    int N = ctx->N;
    int Cw = LOG_Q_CEIL;
    int Cd = 2 * ETA * (K_LWE + ctx->L);
    int cols_per_i = Cw + 1 + Cd;

    evmlr_lin_proof_ctx_t ctx_u;
    evmlr_lin_proof_ctx_init(ctx_u, N, N * cols_per_i);
    evmlr_lin_proof_ctx_set_gaussian(ctx_u, ETA);

    nmod_poly_mat_t A_u, t_u;
    nmod_poly_mat_init(A_u, N, N * cols_per_i, MOD_Q);
    nmod_poly_mat_zero(A_u);
    nmod_poly_mat_init(t_u, N, 1, MOD_Q);

    setup_A_t_u(A_u, t_u, u, alpha, beta, lambda, gamma, ctx, pp);

    nmod_poly_mat_t s1_u, s2_u;
    nmod_poly_mat_init(s1_u, N * cols_per_i, 1, MOD_Q);
    for(int i=0; i<N; i++) {
        int offset = i * cols_per_i;
        for(int j=0; j<Cw; j++) nmod_poly_set(nmod_poly_mat_entry(s1_u, offset + j, 0), nmod_poly_vec_entry(w_dagger[i], j));
        nmod_poly_set(nmod_poly_mat_entry(s1_u, offset + Cw, 0), nmod_poly_mat_entry(sigma, i, 0));
        for(int j=0; j<Cd; j++) nmod_poly_set(nmod_poly_mat_entry(s1_u, offset + Cw + 1 + j, 0), nmod_poly_mat_entry(sp->d_dagger[i], j, 0));
    }
    
    nmod_poly_mat_init(s2_u, N, 1, MOD_Q);
    nmod_poly_mat_zero(s2_u);

    evmlr_lin_prove(lin_proof, A_u, s1_u, s2_u, t_u, ctx_u);

    nmod_poly_mat_clear(A_u); nmod_poly_mat_clear(s1_u); nmod_poly_mat_clear(s2_u); nmod_poly_mat_clear(t_u);
    evmlr_lin_proof_ctx_clear(ctx_u);
}

static int verify_u(const evmlr_lin_proof_t lin_proof, const nmod_poly_mat_t u, const nmod_poly_t alpha, const nmod_poly_t beta, const nmod_poly_t lambda, const nmod_poly_t gamma, const evmlr_shuffle_ctx_t ctx, const evmlr_shuffle_pp_t pp) {
    int N = ctx->N;
    int cols_per_i = LOG_Q_CEIL + 1 + 2 * ETA * (K_LWE + ctx->L);
    evmlr_lin_proof_ctx_t ctx_u;
    evmlr_lin_proof_ctx_init(ctx_u, N, N * cols_per_i);
    evmlr_lin_proof_ctx_set_gaussian(ctx_u, 1.0);

    nmod_poly_mat_t A_u, t_u;
    nmod_poly_mat_init(A_u, N, N * cols_per_i, MOD_Q);
    nmod_poly_mat_zero(A_u);
    nmod_poly_mat_init(t_u, N, 1, MOD_Q);

    setup_A_t_u(A_u, t_u, u, alpha, beta, lambda, gamma, ctx, pp);

    int valid = evmlr_lin_verify(lin_proof, A_u, t_u, ctx_u);

    nmod_poly_mat_clear(A_u); nmod_poly_mat_clear(t_u);
    evmlr_lin_proof_ctx_clear(ctx_u);
    return valid;
}

void evmlr_shuffle_phase_1(nmod_poly_mat_t sigma, evmlr_commit_t com, nmod_poly_mat_t r, const evmlr_shuffle_ctx_t ctx, const evmlr_shuffle_sp_t sp) {
    // Sample r from B^{2K_SIS} (r and com are owned by the caller)
    nmod_poly_mat_init(r, 2 * K_SIS, 1, MOD_Q);
    evmlr_commit_sample_r(r);
    evmlr_commit_init(com);
    nmod_poly_mat_init(sigma, ctx->com_ctx->N, 1, MOD_Q);
    nmod_poly_mat_zero(sigma);
    for (slong i = 0; i < ctx->N; i++) {
        evmlr_utils_int_to_bin(nmod_poly_mat_entry(sigma, i, 0), sp->pi[i]);
    }
    evmlr_commit(com, sigma, r, ctx->com_ctx);
}

void lambda_setup(nmod_poly_mat_t Lambda, const nmod_poly_t lambda, const nmod_poly_t cyclo_poly, slong L);

void calc_z(nmod_poly_t z, const evmlr_otse_ciphertext_t cipher, const nmod_poly_mat_t d_dagger,
            const nmod_poly_mat_t Lambda, const evmlr_shuffle_ctx_t ctx);

void calc_z_hat(nmod_poly_t z_hat, const nmod_poly_mat_t c_hat, const nmod_poly_mat_t Lambda, const evmlr_shuffle_ctx_t ctx);

void calc_h(nmod_poly_t h, const nmod_poly_t z, const nmod_poly_t bin_poly, const nmod_poly_t alpha, const nmod_poly_t beta, const nmod_poly_t cyclo_poly);

void evmlr_shuffle_phase_2(nmod_poly_mat_t h, nmod_poly_mat_t h_hat, evmlr_shuffle_proof_t proof, nmod_poly_mat_t r_W,
                           nmod_poly_mat_t Theta, nmod_poly_mat_t w_dagger[],
                           const nmod_poly_mat_t sigma, const nmod_poly_t alpha, const nmod_poly_t beta, const nmod_poly_t lambda, const evmlr_shuffle_ctx_t ctx, const evmlr_shuffle_sp_t sp,
                           const evmlr_shuffle_pp_t pp, flint_rand_t state) {
    slong L = ctx->L;
    slong N = ctx->N;

    nmod_poly_mat_init(h, N, 1, MOD_Q);
    nmod_poly_mat_init(h_hat, N, 1, MOD_Q);

    nmod_poly_mat_t Lambda;
    lambda_setup(Lambda, lambda, ctx->com_ctx->cyclo_poly, L);

    nmod_poly_mat_t z, z_hat;
    nmod_poly_mat_init(z, N, 1, MOD_Q);
    nmod_poly_mat_init(z_hat, N, 1, MOD_Q);
    nmod_poly_mat_zero(z);
    nmod_poly_mat_zero(z_hat);

    nmod_poly_t tmp;
    nmod_poly_init(tmp, MOD_Q);
    for (slong i = 0; i < N; i++) {
        calc_z(nmod_poly_mat_entry(z, i, 0), pp->c_star[i], sp->d_dagger[i], Lambda, ctx); // z_i = ⟨c^⋆_i − H'B(η)d^dagger_i , Λ⟩
        calc_z_hat(nmod_poly_mat_entry(z_hat, i, 0), pp->c_hat[i], Lambda, ctx); // ẑ_i = ⟨c^hat_i, Λ⟩
        evmlr_utils_int_to_bin(tmp, i);
        calc_h(nmod_poly_mat_entry(h, i, 0), nmod_poly_mat_entry(z, i, 0), tmp, alpha, beta, ctx->com_ctx->cyclo_poly); // h_i = z_i + int_to_bin(i) * beta - alpha
        calc_h(nmod_poly_mat_entry(h_hat, i, 0), nmod_poly_mat_entry(z_hat, i, 0), nmod_poly_mat_entry(sigma, i, 0), alpha, beta, ctx->com_ctx->cyclo_poly); // ĥ_i = ẑ_i + sigma_i * beta - alpha
    }

    nmod_poly_mat_init(Theta, N - 1, 1, MOD_Q);
    evmlr_utils_uniform_mat(Theta);

    nmod_poly_mat_t w;
    nmod_poly_mat_init(w, N, 1, MOD_Q);

    evmlr_crt_mulmod(nmod_poly_vec_entry(w, 0), nmod_poly_vec_entry(Theta, 0), nmod_poly_vec_entry(h, 0), ctx->com_ctx->cyclo_poly);
    for (slong i = 1; i < N - 1; i++) {
        // w_i = Θ_{i-1} * h^hat_i + Θ_i * h_i
        evmlr_crt_mulmod(nmod_poly_vec_entry(w, i), nmod_poly_vec_entry(Theta, i-1), nmod_poly_vec_entry(h_hat, i), ctx->com_ctx->cyclo_poly);
        evmlr_crt_mulmod(tmp, nmod_poly_vec_entry(Theta, i), nmod_poly_vec_entry(h, i), ctx->com_ctx->cyclo_poly);
        nmod_poly_add(nmod_poly_vec_entry(w, i), nmod_poly_vec_entry(w, i), tmp);
    }
    evmlr_crt_mulmod(nmod_poly_vec_entry(w, N-1), nmod_poly_vec_entry(Theta, N-2),
                     nmod_poly_vec_entry(h_hat, N-1), ctx->com_ctx->cyclo_poly);

    // TODO see coefficient range
    // w_i = G^{LOG_Q_CEIL} w_dagger_i
    nmod_poly_mat_t tmp_mat;
    nmod_poly_mat_init(tmp_mat, 1, 1, MOD_Q);
    for (int i = 0; i < N; i++) {
        nmod_poly_set(nmod_poly_vec_entry(tmp_mat, 0), nmod_poly_vec_entry(w, i));
        nmod_poly_mat_init(w_dagger[i], LOG_Q_CEIL, nmod_poly_mat_nrows(tmp_mat), 2);
        evmlr_utils_ring_to_bin(w_dagger[i], tmp_mat, LOG_Q_CEIL);
    }
    nmod_poly_mat_clear(tmp_mat);

    nmod_poly_mat_t w_flat;
    nmod_poly_mat_init(w_flat, ctx->com_ctx->N, 1, MOD_Q);
    nmod_poly_mat_zero(w_flat);
    for (int i = 0; i < N; i++) {
        for (int j = 0; j < LOG_Q_CEIL; j++) {
            nmod_poly_struct* w_poly = nmod_poly_vec_entry(w_dagger[i], j);
            nmod_poly_set(nmod_poly_vec_entry(w_flat, i * LOG_Q_CEIL + j), w_poly);
        }
    }

    nmod_poly_mat_init(r_W, 2 * K_SIS, 1, MOD_Q);
    evmlr_commit_sample_r(r_W);
    evmlr_commit_init(proof->W);
    evmlr_commit(proof->W, w_flat, r_W, ctx->com_ctx);

    // cleanup
    nmod_poly_clear(tmp);
    nmod_poly_mat_clear(Lambda);
    nmod_poly_mat_clear(z);
    nmod_poly_mat_clear(z_hat);
    nmod_poly_mat_clear(w);
    nmod_poly_mat_clear(w_flat);
}

void evmlr_shuffle_phase_3(evmlr_shuffle_proof_t proof, const nmod_poly_mat_t h, const nmod_poly_mat_t h_hat,
                           const nmod_poly_mat_t Theta, const nmod_poly_t gamma, const evmlr_shuffle_ctx_t ctx) {
    slong N = ctx->N;

    // Temporary polynomials for calculations
    nmod_poly_t running_prod, tmp;
    nmod_poly_init(running_prod, MOD_Q);
    nmod_poly_init(tmp, MOD_Q);

    // Initialize the running product with gamma
    nmod_poly_set(running_prod, gamma);

    // Loop to calculate u_1 through u_{N-1} (indexed 0 to N-2 in code)
    for (slong i = 0; i < N - 1; i++) {
        // h_hat[i] / h[i]
        nmod_poly_invmod(tmp, nmod_poly_vec_entry(h, i), ctx->com_ctx->cyclo_poly);
        evmlr_crt_mulmod(tmp, nmod_poly_vec_entry(h_hat, i), tmp, ctx->com_ctx->cyclo_poly);

        // update gamma * \prod_{j=1}^{i} (h_hat[j] / h[j])
        evmlr_crt_mulmod(running_prod, running_prod, tmp, ctx->com_ctx->cyclo_poly);

        // 3. (-1)^(i+1). If i is even, negate the running product
        if (i % 2 == 0) nmod_poly_neg(tmp, running_prod);
        else            nmod_poly_set(tmp, running_prod);

        // +- gamma * prod + Θ_i
        nmod_poly_add(nmod_poly_vec_entry(proof->u, i), tmp, nmod_poly_vec_entry(Theta, i));
    }

    // Cleanup
    nmod_poly_clear(running_prod);
    nmod_poly_clear(tmp);
}

// check if everything is correct using linear proofs
int evmlr_shuffle_verify(const evmlr_shuffle_proof_t proof, const evmlr_shuffle_ctx_t ctx, const evmlr_shuffle_pp_t pp) {
    
    // Recompute alphas, beta, lambda, gamma
    uint8_t hash1[SHA256HashSize];
    nmod_poly_t alpha, beta, lambda, gamma;
    nmod_poly_init(alpha, MOD_Q);
    nmod_poly_init(beta, MOD_Q);
    nmod_poly_init(lambda, MOD_Q);
    nmod_poly_init(gamma, MOD_Q);

    get_challenges_1(alpha, beta, lambda, pp, proof->P, ctx, hash1);
    get_challenge_2(gamma, hash1, proof->W);

    int valid = 1;
    valid &= verify_commit(proof->proof_D, ctx->com_ctx, pp->D->c);
    valid &= verify_commit(proof->proof_P, ctx->com_ctx, proof->P->c);
    valid &= verify_commit(proof->proof_W, ctx->com_ctx, proof->W->c);

    valid &= verify_u(proof->proof_u, proof->u, alpha, beta, lambda, gamma, ctx, pp);

    nmod_poly_clear(alpha); nmod_poly_clear(beta); nmod_poly_clear(lambda); nmod_poly_clear(gamma);
    return valid;
}

void evmlr_shuffle_clear_sp(evmlr_shuffle_sp_t sp, const evmlr_shuffle_ctx_t ctx) {
    free(sp->pi);
    for (size_t i = 0; i < ctx->N; i++) {
        nmod_poly_mat_clear(sp->d_dagger[i]);
    }
    free(sp->d_dagger);
    nmod_poly_mat_clear(sp->r_D);
}

void evmlr_shuffle_clear_pp(evmlr_shuffle_pp_t pp, const evmlr_shuffle_ctx_t ctx) {
    evmlr_commit_clear(pp->D);
    for (size_t i = 0; i < ctx->N; i++) {
        nmod_poly_mat_clear(pp->c_hat[i]);
        evmlr_otse_ciphertext_clear(pp->c_star[i]);
    }
    free(pp->c_hat);
    free(pp->c_star);
}

void lambda_setup(nmod_poly_mat_t Lambda, const nmod_poly_t lambda, const nmod_poly_t cyclo_poly, slong L) {
    nmod_poly_mat_init(Lambda, L, 1, MOD_Q);
    for (int i = 0; i < L; i++) {
        nmod_poly_struct* Lambda_i = nmod_poly_mat_entry(Lambda, i, 0);
        switch (i) {
            case 0: nmod_poly_one(Lambda_i);           break;
            case 1: nmod_poly_set(Lambda_i, lambda); break;
            default:
                evmlr_crt_mulmod(Lambda_i, nmod_poly_mat_entry(Lambda, i-1, 0), lambda, cyclo_poly);
                break;
        }
    }
}

void calc_z(nmod_poly_t z, const evmlr_otse_ciphertext_t cipher, const nmod_poly_mat_t d_dagger,
            const nmod_poly_mat_t Lambda, const evmlr_shuffle_ctx_t ctx) {
    slong L = ctx->L;
    nmod_poly_mat_t a;
    nmod_poly_mat_init(a, L, 1, MOD_Q);
    evmlr_calc_a(a, d_dagger, ctx->hpke_ctx->otse_ctx);

    for (int j = 0; j < L; j++) {
        nmod_poly_struct* a_j = nmod_poly_mat_entry(a, j, 0);
        nmod_poly_sub(a_j, nmod_poly_mat_entry(cipher->c, j, 0), a_j);
        evmlr_crt_mulmod(a_j, a_j, nmod_poly_mat_entry(Lambda, j, 0), ctx->com_ctx->cyclo_poly);
        nmod_poly_add(z, z, a_j);
    }

    nmod_poly_mat_clear(a);
}

void calc_z_hat(nmod_poly_t z_hat, const nmod_poly_mat_t c_hat, const nmod_poly_mat_t Lambda, const evmlr_shuffle_ctx_t ctx) {
    slong L = ctx->L;
    nmod_poly_t tmp;
    nmod_poly_init(tmp, MOD_Q);

    for (int j = 0; j < L; j++) {
        nmod_poly_struct* c_hat_j = nmod_poly_mat_entry(c_hat, j, 0);
        nmod_poly_struct* Lambda_j = nmod_poly_mat_entry(Lambda, j, 0);
        evmlr_crt_mulmod(tmp, c_hat_j, Lambda_j, ctx->com_ctx->cyclo_poly);
        nmod_poly_add(z_hat, z_hat, tmp);
    }
    nmod_poly_clear(tmp);
}

void calc_h(nmod_poly_t h, const nmod_poly_t z, const nmod_poly_t bin_poly, const nmod_poly_t alpha,
            const nmod_poly_t beta, const nmod_poly_t cyclo_poly) {
    nmod_poly_set(h, bin_poly);
    evmlr_crt_mulmod(h, h, beta, cyclo_poly);
    nmod_poly_add(h, z, h);
    nmod_poly_sub(h, h, alpha);
}

void evmlr_shuffle_prove(evmlr_shuffle_proof_t proof, const evmlr_shuffle_sp_t sp, const evmlr_shuffle_pp_t pp, const evmlr_shuffle_ctx_t ctx, flint_rand_t state) {
    size_t N = ctx->N;
    nmod_poly_mat_t sigma;
    nmod_poly_mat_t r_P;
    // Prover computes P, sigma, r_P
    evmlr_shuffle_phase_1(sigma, proof->P, r_P, ctx, sp);

    nmod_poly_t alpha, beta, lambda, gamma;
    nmod_poly_init(alpha, MOD_Q);
    nmod_poly_init(beta, MOD_Q);
    nmod_poly_init(lambda, MOD_Q);
    nmod_poly_init(gamma, MOD_Q);

    uint8_t hash1[SHA256HashSize];
    get_challenges_1(alpha, beta, lambda, pp, proof->P, ctx, hash1);

    nmod_poly_mat_t h, h_hat;
    nmod_poly_mat_t r_W;
    nmod_poly_mat_t Theta;
    nmod_poly_mat_t w_dagger[N];

    // Prover computes W, h, h_hat, Theta, w_dagger, r_W
    evmlr_shuffle_phase_2(h, h_hat, proof, r_W, Theta, w_dagger, sigma, alpha, beta, lambda, ctx, sp, pp, state);

    // Verifier samples gamma
    get_challenge_2(gamma, hash1, proof->W);

    // Prover computes u
    evmlr_shuffle_phase_3(proof, h, h_hat, Theta, gamma, ctx);

    // Prover compute proofs D, P, W
    nmod_poly_mat_t d_flat;
    nmod_poly_mat_init(d_flat, ctx->com_ctx->N, 1, MOD_Q);
    nmod_poly_mat_zero(d_flat);
    slong row_len = (2*ETA) * (K_LWE + ctx->L);
    for (slong i = 0; i < N; i++) {
        for (slong j = 0; j < row_len; j++) {
            nmod_poly_struct* d_dag_ij = nmod_poly_mat_entry(sp->d_dagger[i], j, 0);
            nmod_poly_struct* poly = nmod_poly_mat_entry(d_flat, i * row_len + j, 0);
            nmod_poly_set(poly, d_dag_ij);
        }
    }
    prove_commit(proof->proof_D, ctx->com_ctx, d_flat, sp->r_D, pp->D->c, state);
    nmod_poly_mat_clear(d_flat);

    prove_commit(proof->proof_P, ctx->com_ctx, sigma, r_P, proof->P->c, state);

    nmod_poly_mat_t w_flat;
    nmod_poly_mat_init(w_flat, ctx->com_ctx->N, 1, MOD_Q);
    nmod_poly_mat_zero(w_flat);
    for (int i = 0; i < N; i++) {
        for (int j = 0; j < LOG_Q_CEIL; j++) {
            nmod_poly_struct* w_poly = nmod_poly_vec_entry(w_dagger[i], j);
            nmod_poly_set(nmod_poly_vec_entry(w_flat, i * LOG_Q_CEIL + j), w_poly);
        }
    }
    prove_commit(proof->proof_W, ctx->com_ctx, w_flat, r_W, proof->W->c, state);
    nmod_poly_mat_clear(w_flat);

    // Prover compute proof u
    prove_u(proof->proof_u, w_dagger, sigma, sp, proof->u, alpha, beta, lambda, gamma, ctx, pp);

    // cleanup
    nmod_poly_clear(alpha);
    nmod_poly_clear(beta);
    nmod_poly_clear(lambda);
    nmod_poly_clear(gamma);
    nmod_poly_mat_clear(sigma);
    nmod_poly_mat_clear(r_P);

    nmod_poly_mat_clear(h);
    nmod_poly_mat_clear(h_hat);
    nmod_poly_mat_clear(r_W);
    nmod_poly_mat_clear(Theta);
    for (size_t i = 0; i < N; i++) {
        nmod_poly_mat_clear(w_dagger[i]);
    }
}

int evmlr_shuffle_run(evmlr_shuffle_sp_t sp, evmlr_shuffle_pp_t pp, const evmlr_shuffle_ctx_t ctx, flint_rand_t state) {
    evmlr_shuffle_proof_t proof;
    evmlr_proof_init(proof, ctx);

    evmlr_shuffle_prove(proof, sp, pp, ctx, state);

    int valid = evmlr_shuffle_verify(proof, ctx, pp);

    evmlr_proof_clear(proof, ctx);
    return valid;
}

#ifdef MAIN
#include "evmlr_main.h"
void setup(evmlr_shuffle_sp_t sp, evmlr_shuffle_pp_t pp, const evmlr_shuffle_ctx_t ctx, flint_rand_t state) {
    slong N = ctx->N;
    slong L = ctx->L;
    evmlr_hpke_keypair_t keypair;
    evmlr_hpke_keypair_gen(keypair, state, ctx->hpke_ctx);

    nmod_poly_mat_t m[N];
    for (size_t i = 0; i < N; i++) {
        nmod_poly_mat_init(m[i], L, 1, MOD_Q);
        nmod_poly_mat_randtest(m[i], state, DEGREE_N);
    }

    sp->pi = (size_t *) malloc(N * sizeof(size_t));
    evmlr_utils_new_perm(sp->pi, N);

    // shuffle messages
    pp->c_hat = (nmod_poly_mat_t *) malloc(N * sizeof(nmod_poly_mat_t));
    for (size_t i = 0; i < N; i++) {
        nmod_poly_mat_init(pp->c_hat[i], L, 1, MOD_Q);
        nmod_poly_mat_set(pp->c_hat[i], m[sp->pi[i]]);
    }

    pp->c_star = (evmlr_otse_ciphertext_t *) malloc(N * sizeof(evmlr_otse_ciphertext_t));
    sp->d_dagger = (nmod_poly_mat_t *) malloc(N * sizeof(nmod_poly_mat_t));
    for (slong i = 0; i < N; i++) {
        evmlr_hpke_cipher_t cipher;
        evmlr_hpke_cipher_init(cipher, ctx->hpke_ctx->otse_ctx->L);
        // d_dagger is owned by the caller; HPKE encryption only fills it in.
        nmod_poly_mat_init(sp->d_dagger[i], (2*ETA) * (K_LWE + L), 1, MOD_Q);
        nmod_poly_mat_struct* d_dagger_i = sp->d_dagger[i];
        evmlr_hpke_encrypt(cipher, d_dagger_i, m[i], keypair->enc_keypair->pk, ctx->hpke_ctx, state);
        nmod_poly_mat_init(pp->c_star[i]->c, L, 1, MOD_Q);
        nmod_poly_mat_set(pp->c_star[i]->c, cipher->otse_cipher->c);
        evmlr_hpke_cipher_clear(cipher);
    }

    nmod_poly_mat_init(sp->r_D, 2 * K_SIS, 1, MOD_Q);
    evmlr_commit_sample_r(sp->r_D);

    nmod_poly_mat_t d_flat;
    nmod_poly_mat_init(d_flat, ctx->com_ctx->N, 1, MOD_Q);
    nmod_poly_mat_zero(d_flat);
    slong row_len = (2*ETA) * (K_LWE + L);
    for (slong i = 0; i < N; i++) {
        for (slong j = 0; j < row_len; j++) {
            nmod_poly_struct* d_dag_ij = nmod_poly_mat_entry(sp->d_dagger[i], j, 0);
            nmod_poly_struct* poly = nmod_poly_mat_entry(d_flat, i * row_len + j, 0);
            nmod_poly_set(poly, d_dag_ij);
        }
    }
    evmlr_commit_init(pp->D);
    evmlr_commit(pp->D, d_flat, sp->r_D, ctx->com_ctx);

    nmod_poly_mat_clear(d_flat);
    evmlr_hpke_keypair_clear(keypair);
    for (int i = 0; i < N; ++i) {
        nmod_poly_mat_clear(m[i]);
    }
}

void test(evmlr_shuffle_ctx_t ctx, flint_rand_t state) {
    evmlr_shuffle_sp_t sp;
    evmlr_shuffle_pp_t pp;
    setup(sp, pp, ctx, state);

    TEST_ONCE("shuffle proof works") {
        TEST_ASSERT(evmlr_shuffle_run(sp, pp, ctx, state) == 1, end)
    } TEST_END;

    end:
        evmlr_shuffle_clear_sp(sp, ctx);
        evmlr_shuffle_clear_pp(pp, ctx);
}

void bench(evmlr_shuffle_ctx_t ctx, flint_rand_t state) {
    evmlr_shuffle_sp_t sp;
    evmlr_shuffle_pp_t pp;
    setup(sp, pp, ctx, state);

    BENCH_BEGIN("evmlr_shuffle_run") {
        BENCH_ADD(evmlr_shuffle_run(sp, pp, ctx, state))
    } BENCH_END;

    evmlr_shuffle_clear_sp(sp, ctx);
    evmlr_shuffle_clear_pp(pp, ctx);
}

int main(int argc, char *argv[]) {
    slong n_messages = SHUFFLE_N_MSGS;

    evmlr_mode_t mode = evmlr_mode(argc, argv);

    flint_rand_t state;
    evmlr_rand_init(state);

    evmlr_shuffle_ctx_t ctx;
    evmlr_shuffle_ctx_init(ctx, n_messages, M_LEN, state);

    if (evmlr_runs_tests(mode))   test(ctx, state);
    if (evmlr_runs_benches(mode)) bench(ctx, state);

    evmlr_shuffle_ctx_clear(ctx);
    flint_rand_clear(state);
    return test_status();
}
#endif