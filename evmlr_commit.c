#include "evmlr_crt.h"
#include "evmlr_commit.h"
#include "evmlr_utils.h"
#ifdef MAIN
#include "test.h"
#include "bench.h"
#endif

// B^2 := nL + n 2 K_SIS ETA^2
ulong compute_b(ulong L) {
    return (DEGREE_N * L) + (DEGREE_N * 2 * K_SIS * ETA * ETA);
}

void evmlr_commit_ctx_init(evmlr_commit_ctx_t ctx, slong N, flint_rand_t state) {
    ctx->b_sqr = compute_b(N);
    ctx->N = N;

    // A_1 \sample R_q^{K_SIS x N}
    nmod_poly_mat_init(ctx->A_1, K_SIS, N, MOD_Q);
    nmod_poly_mat_randtest(ctx->A_1, state, DEGREE_N);

    // A_2 \sample R_q^{K_SIS x 2K_SIS}
    nmod_poly_mat_init(ctx->A_2, K_SIS, 2 * K_SIS, MOD_Q);
    nmod_poly_mat_randtest(ctx->A_2, state, DEGREE_N);

    nmod_poly_init(ctx->cyclo_poly, MOD_Q);
    nmod_poly_set_coeff_ui(ctx->cyclo_poly, DEGREE_N, 1);
    nmod_poly_set_coeff_ui(ctx->cyclo_poly, 0, 1);
}

void evmlr_commit_ctx_clear(evmlr_commit_ctx_t ctx) {
    nmod_poly_mat_clear(ctx->A_1);
    nmod_poly_mat_clear(ctx->A_2);
    nmod_poly_clear(ctx->cyclo_poly);
}

void evmlr_commit_init(evmlr_commit_t com) {
    nmod_poly_mat_init(com->c, K_SIS, 1, MOD_Q);
}

void evmlr_commit_sample_r(nmod_poly_mat_t r) {
    evmlr_utils_binom_sample_mat_ring(r, ETA); // r is owned by the caller
}

void evmlr_commit(evmlr_commit_t com, const nmod_poly_mat_t msg, const nmod_poly_mat_t r, const evmlr_commit_ctx_t ctx) {
    // com is owned by the caller; this only fills it in.

    nmod_poly_mat_t tmp;
    nmod_poly_mat_init(tmp, K_SIS, 1, MOD_Q);
    nmod_poly_t one;
    nmod_poly_init(one, MOD_Q);
    nmod_poly_one(one);

    // Compute c = A_1 * msg + A_2 * r
    nmod_poly_mat_mul(com->c, ctx->A_1, msg);
    for (slong i = 0; i < K_SIS; i++) {
        nmod_poly_struct* c_i = nmod_poly_mat_entry(com->c, i, 0);
        evmlr_crt_mulmod(c_i, c_i, one, ctx->cyclo_poly);
    }

    nmod_poly_mat_mul(tmp, ctx->A_2, r);
    for (slong i = 0; i < K_SIS; i++) {
        nmod_poly_struct* tmp_i = nmod_poly_mat_entry(tmp, i, 0);
        evmlr_crt_mulmod(tmp_i, tmp_i, one, ctx->cyclo_poly);
    }

    nmod_poly_mat_add(com->c, com->c, tmp);

    nmod_poly_mat_clear(tmp);
    nmod_poly_clear(one);
}

void evmlr_commit_clear(evmlr_commit_t com) {
    nmod_poly_mat_clear(com->c);
}

slong nmod_poly_norm_sqr(const nmod_poly_t poly) {
   slong norm = 0;
   for (slong i = 0; i < nmod_poly_length(poly); i++) {
         slong coeff = nmod_poly_get_coeff_ui(poly, i);
         if (coeff > MOD_Q / 2) {
            coeff -= MOD_Q;
         }
         norm += coeff * coeff;
   }
   return norm;
}

int verify_norm(const ulong L, const nmod_poly_mat_t msg, const nmod_poly_mat_t r, ulong b_sqr) {
    ulong total_norm = 0;
    for (slong i = 0; i < L; i++) {
        total_norm += nmod_poly_hamming_weight(nmod_poly_mat_entry(msg, i, 0));
    }
    for (slong i = 0; i < 2 * K_SIS; i++) {
        total_norm += nmod_poly_norm_sqr(nmod_poly_mat_entry(r, i, 0));
    }
    return total_norm <= b_sqr;
}

int evmlr_commit_verify(const evmlr_commit_t com, const nmod_poly_mat_t msg, const nmod_poly_mat_t r, const evmlr_commit_ctx_t ctx) {
    // ||\binom{m}{r}|| <= B
    int valid = verify_norm(ctx->N, msg, r, ctx->b_sqr);
    if (!valid) {
        return 0;
    }
    // c = A_1 * msg + A_2 * r
    evmlr_commit_t recomputed_com;
    evmlr_commit_init(recomputed_com);
    evmlr_commit(recomputed_com, msg, r, ctx);
    valid = nmod_poly_mat_equal(com->c, recomputed_com->c);

    evmlr_commit_clear(recomputed_com);
    return valid;
}

#ifdef MAIN
#include "evmlr_main.h"

void test(evmlr_commit_ctx_t ctx) {
    ulong msg_value[ctx->N];
    nmod_poly_mat_t msg, r;
    evmlr_commit_t com;
    // Sample message
    evmlr_utils_random(msg_value, sizeof(ulong) * ctx->N);
    nmod_poly_mat_init(msg, ctx->N, 1, MOD_Q);
    for (slong i = 0; i < ctx->N; i++) {
        evmlr_utils_int_to_bin(nmod_poly_mat_entry(msg, i, 0), msg_value[i]);
    }
    // Sample r
    nmod_poly_mat_init(r, 2 * K_SIS, 1, MOD_Q);
    evmlr_commit_sample_r(r);

    evmlr_commit_init(com);
    TEST_BEGIN("commitments can be created and verified") {
        evmlr_commit(com, msg, r, ctx);
        int valid = evmlr_commit_verify(com, msg, r, ctx);
        TEST_ASSERT(valid == 1, end)
    } TEST_END;

    end:
        nmod_poly_mat_clear(msg);
        nmod_poly_mat_clear(r);
        evmlr_commit_clear(com);
}

void bench(evmlr_commit_ctx_t ctx) {
    ulong msg_value[ctx->N];
    nmod_poly_mat_t msg, r;
    evmlr_commit_t com;
    // Sample message
    evmlr_utils_random(msg_value, sizeof(ulong) * ctx->N);
    nmod_poly_mat_init(msg, ctx->N, 1, MOD_Q);
    for (slong i = 0; i < ctx->N; i++) {
        evmlr_utils_int_to_bin(nmod_poly_mat_entry(msg, i, 0), msg_value[i]);
    }
    // Sample r
    nmod_poly_mat_init(r, 2 * K_SIS, 1, MOD_Q);
    evmlr_commit_sample_r(r);

    evmlr_commit_init(com);
    BENCH_BEGIN("evmlr_commit") {
        BENCH_ADD(evmlr_commit(com, msg, r, ctx))
    } BENCH_END;

    BENCH_BEGIN("evmlr_commit_verify") {
        evmlr_commit(com, msg, r, ctx);
        BENCH_ADD(evmlr_commit_verify(com,msg, r, ctx))
    } BENCH_END;

    nmod_poly_mat_clear(msg);
    nmod_poly_mat_clear(r);
    evmlr_commit_clear(com);
}

int main(int argc, char *argv[]) {
    evmlr_mode_t mode = evmlr_mode(argc, argv);

    flint_rand_t state;
    evmlr_rand_init(state);

    evmlr_commit_ctx_t ctx;
    evmlr_commit_ctx_init(ctx, M_LEN, state);

    if (evmlr_runs_tests(mode))   test(ctx);
    if (evmlr_runs_benches(mode)) bench(ctx);

    evmlr_commit_ctx_clear(ctx);
    flint_rand_clear(state);
    return test_status();
}
#endif