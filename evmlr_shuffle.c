#include "evmlr_crt.h"
#include "evmlr_shuffle.h"
#include "evmlr_challenge.h"
#include "evmlr_utils.h"
#include "evmlr_zk_proof.h"
#include "sha.h"
#include <math.h>

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

/* Length of ZK⋆'s binary witness: d†, σ and w† per message, and the bits of
 * the three Com⋆ randomness vectors. */
static slong zk_witness_len(const evmlr_shuffle_ctx_t ctx) {
    return ctx->N * (2 * ETA * (K_LWE + ctx->L) + 1 + LOG_Q_CEIL) + 3 * 2 * K_SIS * 2 * ETA;
}

void evmlr_proof_init(evmlr_shuffle_proof_t proof, const evmlr_shuffle_ctx_t ctx) {
    nmod_poly_mat_init(proof->u, ctx->N - 1, 1, MOD_Q);
    evmlr_zk_proof_init(proof->zk, zk_witness_len(ctx), 1 + 3 * K_SIS);
}

void evmlr_proof_clear(evmlr_shuffle_proof_t proof, const evmlr_shuffle_ctx_t ctx) {
    nmod_poly_mat_clear(proof->u);
    evmlr_commit_clear(proof->P);
    evmlr_commit_clear(proof->W);
    evmlr_zk_proof_clear(proof->zk);
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

/*============================================================================*/
/* ZK⋆: the statement Protocol 1 leaves to prove (SHUFFLE-ZK.md)              */
/*============================================================================*/

/* Equation i of Protocol 1, (1) to (3), involves only message i:
 *
 *     G w†_i + sig_i σ_i + fac_i M_d d†_i = tu_i,
 *
 * with G the gadget row, M_d = (B(eta) applied to Λ H') the row that turns d†_i
 * into its contribution to h_i, and sig_i, fac_i, tu_i built from the public
 * u, α, β, γ and the ciphertexts. This computes those per message, so that
 * the statement is never held as a matrix. */
typedef struct {
    slong N, Cd, Cw;
    nmod_poly_struct *sig, *fac, *tu; // N each, mod q
    nmod_poly_struct *Md;             // Cd, mod q
    nmod_poly_struct *G;              // Cw, mod q
} u_relation_t;

static void u_relation(u_relation_t *ur, const nmod_poly_mat_t u, const nmod_poly_t alpha,
                       const nmod_poly_t beta, const nmod_poly_t lambda, const nmod_poly_t gamma,
                       const evmlr_shuffle_ctx_t ctx, const evmlr_shuffle_pp_t pp) {
    const slong N = ctx->N, L = ctx->L;
    const nmod_poly_struct *cyclo = ctx->com_ctx->cyclo_poly;
    nmod_poly_mat_t Lambda, V, Gm;
    nmod_poly_t tmp, tmp2, h_pub, h_hat_pub;

    ur->N = N;
    ur->Cw = LOG_Q_CEIL;
    ur->Cd = 2 * ETA * (K_LWE + L);
    ur->sig = flint_malloc(N * sizeof(nmod_poly_struct));
    ur->fac = flint_malloc(N * sizeof(nmod_poly_struct));
    ur->tu = flint_malloc(N * sizeof(nmod_poly_struct));
    ur->Md = flint_malloc(ur->Cd * sizeof(nmod_poly_struct));
    ur->G = flint_malloc(ur->Cw * sizeof(nmod_poly_struct));

    lambda_setup(Lambda, lambda, cyclo, L);
    nmod_poly_init(tmp, MOD_Q);
    nmod_poly_init(tmp2, MOD_Q);
    nmod_poly_init(h_pub, MOD_Q);
    nmod_poly_init(h_hat_pub, MOD_Q);

    // V = Λ^T H', and M_d = (V, ..., V, -V, ..., -V), eta copies of each.
    nmod_poly_mat_init(V, 1, K_LWE + L, MOD_Q);
    nmod_poly_mat_zero(V);
    for (slong j = 0; j < K_LWE + L; j++) {
        for (slong k = 0; k < L; k++) {
            evmlr_crt_mulmod(tmp, nmod_poly_mat_entry(Lambda, k, 0),
                             nmod_poly_mat_entry(ctx->hpke_ctx->otse_ctx->H_prime, k, j), cyclo);
            nmod_poly_add(nmod_poly_mat_entry(V, 0, j), nmod_poly_mat_entry(V, 0, j), tmp);
        }
    }
    for (slong b = 0; b < 2 * ETA; b++) {
        for (slong j = 0; j < K_LWE + L; j++) {
            nmod_poly_struct *md = ur->Md + b * (K_LWE + L) + j;

            nmod_poly_init(md, MOD_Q);
            if (b < ETA) nmod_poly_set(md, nmod_poly_mat_entry(V, 0, j));
            else         nmod_poly_neg(md, nmod_poly_mat_entry(V, 0, j));
        }
    }
    nmod_poly_mat_init(Gm, 1, ur->Cw, MOD_Q);
    evmlr_utils_gadget_matrix(Gm, 1, ur->Cw, MOD_Q);
    for (slong j = 0; j < ur->Cw; j++) {
        nmod_poly_init(ur->G + j, MOD_Q);
        nmod_poly_set(ur->G + j, nmod_poly_mat_entry(Gm, 0, j));
    }

    for (slong i = 0; i < N; i++) {
        // h_pub = <c*_i, Λ> + int_to_bin(i) β - α and h_hat_pub = <ĉ_i, Λ> - α:
        // h_i and ĥ_i without their witness terms.
        nmod_poly_zero(h_pub);
        nmod_poly_zero(h_hat_pub);
        for (slong j = 0; j < L; j++) {
            evmlr_crt_mulmod(tmp, nmod_poly_mat_entry(pp->c_star[i]->c, j, 0),
                             nmod_poly_mat_entry(Lambda, j, 0), cyclo);
            nmod_poly_add(h_pub, h_pub, tmp);
            evmlr_crt_mulmod(tmp, nmod_poly_mat_entry(pp->c_hat[i], j, 0),
                             nmod_poly_mat_entry(Lambda, j, 0), cyclo);
            nmod_poly_add(h_hat_pub, h_hat_pub, tmp);
        }
        nmod_poly_zero(tmp);
        evmlr_utils_int_to_bin(tmp, i);
        evmlr_crt_mulmod(tmp, tmp, beta, cyclo);
        nmod_poly_add(h_pub, h_pub, tmp);
        nmod_poly_sub(h_pub, h_pub, alpha);
        nmod_poly_sub(h_hat_pub, h_hat_pub, alpha);

        // The weight of ĥ_i (which carries σ_i) and of h_i (which carries d†_i).
        const nmod_poly_struct *w_hat = (i == 0) ? gamma : nmod_poly_mat_entry(u, (i < N - 1) ? i - 1 : N - 2, 0);
        nmod_poly_init(ur->sig + i, MOD_Q);
        evmlr_crt_mulmod(ur->sig + i, w_hat, beta, cyclo);
        nmod_poly_neg(ur->sig + i, ur->sig + i);
        nmod_poly_init(ur->fac + i, MOD_Q);
        if (i < N - 1) {
            nmod_poly_set(ur->fac + i, nmod_poly_mat_entry(u, i, 0));
        } else {
            nmod_poly_set(ur->fac + i, gamma);
            if (N % 2 != 0) nmod_poly_neg(ur->fac + i, ur->fac + i);
        }
        nmod_poly_init(ur->tu + i, MOD_Q);
        evmlr_crt_mulmod(tmp, w_hat, h_hat_pub, cyclo);
        evmlr_crt_mulmod(tmp2, ur->fac + i, h_pub, cyclo);
        nmod_poly_add(ur->tu + i, tmp, tmp2);
    }

    nmod_poly_mat_clear(Lambda);
    nmod_poly_mat_clear(V);
    nmod_poly_mat_clear(Gm);
    nmod_poly_clear(tmp);
    nmod_poly_clear(tmp2);
    nmod_poly_clear(h_pub);
    nmod_poly_clear(h_hat_pub);
}

static void u_relation_clear(u_relation_t *ur) {
    for (slong i = 0; i < ur->N; i++) {
        nmod_poly_clear(ur->sig + i);
        nmod_poly_clear(ur->fac + i);
        nmod_poly_clear(ur->tu + i);
    }
    for (slong j = 0; j < ur->Cd; j++) nmod_poly_clear(ur->Md + j);
    for (slong j = 0; j < ur->Cw; j++) nmod_poly_clear(ur->G + j);
    flint_free(ur->sig);
    flint_free(ur->fac);
    flint_free(ur->tu);
    flint_free(ur->Md);
    flint_free(ur->G);
}

/* Bits per coefficient of the Com⋆ randomness: CBD(ETA) is a sum of ETA bits
 * minus ETA bits, so r = B bits with B = (1, ..., 1, -1, ..., -1). */
#define R_BITS (2 * ETA)
/* Ring elements of the binary witness that one Com⋆ randomness takes. */
#define R_ELEMS (2 * K_SIS * R_BITS)
/* Rows of the statement: the batched equations, then the openings of D, P
 * and W, K_SIS rows each. */
#define ZK_ROWS (1 + 3 * K_SIS)

/* The statement E s = t (mod q) of ZK⋆ for one shuffle. The witness is
 *     s = (d†_1..N, σ_1..N, w†_1..N, bits(r_D), bits(r_P), bits(r_W)),
 * all binary, and the rows are
 *     0:   sum_i rho_i (equation i)                (batched)
 *     1-2: A_1 d† + A_2 B bits(r_D) = D
 *     3-4: A_1 σ  + A_2 B bits(r_P) = P
 *     5-6: A_1 w† + A_2 B bits(r_W) = W.
 * Equation i is weighted by rho_i, uniform in R_q and hashed from the whole
 * statement: every variable in it is bound by D, P or W before rho is drawn,
 * so a false equation survives the combination with probability q^(-n/2). */
typedef struct {
    u_relation_t ur;
    nmod_poly_struct *rho;              // N, mod q
    const evmlr_commit_ctx_struct *com; // A_1, A_2
    slong off_d, off_s, off_w, off_r;
} shuffle_stmt_t;

/* Column j of the statement: its entries in rows 0..ZK_ROWS-1, lifted to
 * R_p. Each column belongs to one message's d†, σ or w†, or to one bit of
 * one randomness element, and touches at most three rows: the batched
 * equation and its commitment's two opening rows. */
static uint32_t shuffle_column(nmod_poly_struct *out, slong j, const evmlr_zk_stmt_struct *st) {
    const shuffle_stmt_t *ss = (const shuffle_stmt_t *) st->data;
    const u_relation_t *ur = &ss->ur;
    const evmlr_commit_ctx_struct *com = ss->com;
    nmod_poly_t e;
    uint32_t mask = 0;
    slong c = 0, col = 0;     // which opening (0 D, 1 P, 2 W) and its A_1 column

    nmod_poly_init(e, MOD_Q);
    if (j < ss->off_s) {
        slong i = j / ur->Cd, jj = j % ur->Cd;

        evmlr_crt_mulmod(e, ss->rho + i, ur->fac + i, com->cyclo_poly);
        evmlr_crt_mulmod(e, e, ur->Md + jj, com->cyclo_poly);
        c = 0;
        col = i * ur->Cd + jj;
    } else if (j < ss->off_w) {
        slong i = j - ss->off_s;

        evmlr_crt_mulmod(e, ss->rho + i, ur->sig + i, com->cyclo_poly);
        c = 1;
        col = i;
    } else if (j < ss->off_r) {
        slong i = (j - ss->off_w) / ur->Cw, jj = (j - ss->off_w) % ur->Cw;

        evmlr_crt_mulmod(e, ss->rho + i, ur->G + jj, com->cyclo_poly);
        c = 2;
        col = i * ur->Cw + jj;
    }
    if (j < ss->off_r) {
        // The batched equation, and the commitment's message part.
        evmlr_zk_lift(out + 0, e);
        mask |= 1;
        for (slong a = 0; a < K_SIS; a++) {
            evmlr_zk_lift(out + 1 + c * K_SIS + a, nmod_poly_mat_entry(com->A_1, a, col));
            mask |= 1u << (1 + c * K_SIS + a);
        }
    } else {
        // A bit of a randomness element: +-A_2's column, + for the first ETA.
        slong o = j - ss->off_r, k = (o % R_ELEMS) / R_BITS, b = o % R_BITS;

        c = o / R_ELEMS;
        for (slong a = 0; a < K_SIS; a++) {
            nmod_poly_struct *x = out + 1 + c * K_SIS + a;

            evmlr_zk_lift(x, nmod_poly_mat_entry(com->A_2, a, k));
            if (b >= ETA) nmod_poly_neg(x, x);
            mask |= 1u << (1 + c * K_SIS + a);
        }
    }
    nmod_poly_clear(e);
    return mask;
}

/* Sum of the squared centred coefficients of e mod q. */
static double l2sq_q(const nmod_poly_t e) {
    double s = 0;

    for (slong k = 0; k < nmod_poly_length(e); k++) {
        ulong c = nmod_poly_get_coeff_ui(e, k);
        double v = (c > MOD_Q / 2) ? (double) (MOD_Q - c) : (double) c;
        s += v * v;
    }
    return s;
}

/* A public bound on the carry k = (E s - t) / q of an honest witness.
 *
 * It only has to hold for an honest prover, who refuses past it: it sets the
 * widths that hide k, not anything the verifier relies on, since a cheating
 * prover's carry is bounded by the projection whatever this says. So it is a
 * statistical bound rather than a worst case, which would be some 400 times
 * larger and would cost binding some ten bits. Coefficient i of E_r s is a sum
 * of products of E's coefficients, which are uniform-looking mod q, with the
 * witness's bits, so its square averages at most sum_col ||s_col||^2 times the
 * mean square of E_r,col's coefficients; with ||s_col||^2 <= n, summing over
 * the n coefficients gives E||E_r s||^2 <= n sum_col ||E_r,col||^2. The bound
 * is 1.25 times the root of that over all rows, divided by q, plus the carry
 * of t, at most 1/2 a coefficient. Over thousands of coefficients ||k||
 * concentrates within a few per cent of its mean, and the actual witness has
 * about half its bits set, so the honest carry sits well inside; the shuffle's
 * test measures by how much. */
static double shuffle_k_bound(const shuffle_stmt_t *ss) {
    const u_relation_t *ur = &ss->ur;
    const evmlr_commit_ctx_struct *com = ss->com;
    double l2 = 0;
    nmod_poly_t e;

    nmod_poly_init(e, MOD_Q);
    for (slong i = 0; i < ur->N; i++) {
        for (slong j = 0; j < ur->Cw; j++) {
            evmlr_crt_mulmod(e, ss->rho + i, ur->G + j, com->cyclo_poly);
            l2 += l2sq_q(e);
        }
        evmlr_crt_mulmod(e, ss->rho + i, ur->sig + i, com->cyclo_poly);
        l2 += l2sq_q(e);
        for (slong j = 0; j < ur->Cd; j++) {
            evmlr_crt_mulmod(e, ss->rho + i, ur->fac + i, com->cyclo_poly);
            evmlr_crt_mulmod(e, e, ur->Md + j, com->cyclo_poly);
            l2 += l2sq_q(e);
        }
        for (slong a = 0; a < K_SIS; a++) {
            for (slong j = 0; j < ur->Cd; j++) l2 += l2sq_q(nmod_poly_mat_entry(com->A_1, a, i * ur->Cd + j));
            l2 += l2sq_q(nmod_poly_mat_entry(com->A_1, a, i));
            for (slong j = 0; j < ur->Cw; j++) l2 += l2sq_q(nmod_poly_mat_entry(com->A_1, a, i * ur->Cw + j));
        }
    }
    for (slong c = 0; c < 3; c++) {
        for (slong k = 0; k < 2 * K_SIS; k++) {
            for (slong a = 0; a < K_SIS; a++) {
                l2 += R_BITS * l2sq_q(nmod_poly_mat_entry(com->A_2, a, k));
            }
        }
    }
    nmod_poly_clear(e);
    return 1.25 * sqrt(DEGREE_N * l2) / MOD_Q + 0.5 * sqrt((double) ZK_ROWS * DEGREE_N);
}

#ifdef MAIN
/* Tests only: the honest carry's norm against its bound, from the last proof. */
static double zk_carry_ratio = 0;
#endif

/* ZK⋆'s public parameters: a seed fixed by hashing a label, so that nobody
 * chose it. */
static void zk_public_seed(uint8_t pp[32]) {
    SHA256Context sha;

    SHA256Reset(&sha);
    SHA256Input(&sha, (const uint8_t *) "evmlr-shuffle-zk-pp", 19);
    SHA256Result(&sha, pp);
}

/* Builds the statement from Protocol 1's public data: everything hashed into
 * the challenges so far (hash1 covers the keys, D, the ciphertexts and P),
 * then W and u. rho and the statement digest both come from that. */
static void shuffle_stmt(evmlr_zk_stmt_struct *st, shuffle_stmt_t *ss,
                         const evmlr_shuffle_proof_t proof, const uint8_t hash1[SHA256HashSize],
                         const nmod_poly_t alpha, const nmod_poly_t beta, const nmod_poly_t lambda,
                         const nmod_poly_t gamma, const evmlr_shuffle_ctx_t ctx,
                         const evmlr_shuffle_pp_t pp) {
    const slong N = ctx->N;
    evmlr_challenge_t chal;

    u_relation(&ss->ur, proof->u, alpha, beta, lambda, gamma, ctx, pp);
    ss->com = ctx->com_ctx;
    ss->off_d = 0;
    ss->off_s = N * ss->ur.Cd;
    ss->off_w = ss->off_s + N;
    ss->off_r = ss->off_w + N * ss->ur.Cw;

    evmlr_challenge_init(chal);
    evmlr_challenge_add_bytes(chal, (const uint8_t *) "evmlr-shuffle-zk-stmt", 21);
    evmlr_challenge_add_bytes(chal, hash1, SHA256HashSize);
    evmlr_challenge_add_matrix(chal, proof->W->c);
    evmlr_challenge_add_matrix(chal, proof->u);
    ss->rho = flint_malloc(N * sizeof(nmod_poly_struct));
    for (slong i = 0; i < N; i++) {
        nmod_poly_init(ss->rho + i, MOD_Q);
        evmlr_challenge_get_poly(ss->rho + i, DEGREE_N, chal);
    }
    evmlr_challenge_get_hash(st->digest, chal);

    st->m = ss->off_r + 3 * R_ELEMS;
    st->rows = ZK_ROWS;
    st->t = flint_malloc(ZK_ROWS * sizeof(nmod_poly_struct));
    for (slong r = 0; r < ZK_ROWS; r++) nmod_poly_init(st->t + r, MOD_Q);
    for (slong i = 0; i < N; i++) {
        nmod_poly_t e;
        nmod_poly_init(e, MOD_Q);
        evmlr_crt_mulmod(e, ss->rho + i, ss->ur.tu + i, ctx->com_ctx->cyclo_poly);
        nmod_poly_add(st->t + 0, st->t + 0, e);
        nmod_poly_clear(e);
    }
    for (slong a = 0; a < K_SIS; a++) {
        nmod_poly_set(st->t + 1 + a, nmod_poly_mat_entry(pp->D->c, a, 0));
        nmod_poly_set(st->t + 1 + K_SIS + a, nmod_poly_mat_entry(proof->P->c, a, 0));
        nmod_poly_set(st->t + 1 + 2 * K_SIS + a, nmod_poly_mat_entry(proof->W->c, a, 0));
    }
    st->column = shuffle_column;
    st->data = ss;
    st->k_bound = shuffle_k_bound(ss);
}

static void shuffle_stmt_clear(evmlr_zk_stmt_struct *st, shuffle_stmt_t *ss) {
    for (slong i = 0; i < ss->ur.N; i++) nmod_poly_clear(ss->rho + i);
    flint_free(ss->rho);
    for (slong r = 0; r < ZK_ROWS; r++) nmod_poly_clear(st->t + r);
    flint_free(st->t);
    u_relation_clear(&ss->ur);
}

/* The bits of a Com⋆ randomness r, R_BITS binary elements per element of r:
 * a coefficient v in [-ETA, ETA] becomes max(v, 0) ones among the first ETA
 * bits and max(-v, 0) among the last ETA. */
static void r_to_bits(nmod_poly_struct *bits, const nmod_poly_mat_t r) {
    for (slong k = 0; k < 2 * K_SIS; k++) {
        const nmod_poly_struct *rk = nmod_poly_mat_entry(r, k, 0);

        for (slong b = 0; b < R_BITS; b++) nmod_poly_zero(bits + k * R_BITS + b);
        for (slong c = 0; c < DEGREE_N; c++) {
            ulong x = nmod_poly_get_coeff_ui(rk, c);
            slong v = (x > MOD_Q / 2) ? (slong) x - MOD_Q : (slong) x;

            for (slong b = 0; b < ETA; b++) {
                if (v > b)  nmod_poly_set_coeff_ui(bits + k * R_BITS + b, c, 1);
                if (-v > b) nmod_poly_set_coeff_ui(bits + k * R_BITS + ETA + b, c, 1);
            }
        }
    }
}

/* The binary witness, in the order shuffle_column expects. */
static nmod_poly_struct *shuffle_witness(const evmlr_zk_stmt_struct *st, const shuffle_stmt_t *ss,
                                         const nmod_poly_mat_t w_dagger[], const nmod_poly_mat_t sigma,
                                         const nmod_poly_mat_t r_P, const nmod_poly_mat_t r_W,
                                         const evmlr_shuffle_sp_t sp) {
    const slong N = ss->ur.N;
    nmod_poly_struct *s = flint_malloc(st->m * sizeof(nmod_poly_struct));

    for (slong j = 0; j < st->m; j++) nmod_poly_init(s + j, MOD_Q);
    for (slong i = 0; i < N; i++) {
        for (slong j = 0; j < ss->ur.Cd; j++) {
            nmod_poly_set(s + ss->off_d + i * ss->ur.Cd + j, nmod_poly_mat_entry(sp->d_dagger[i], j, 0));
        }
        nmod_poly_set(s + ss->off_s + i, nmod_poly_mat_entry(sigma, i, 0));
        for (slong j = 0; j < ss->ur.Cw; j++) {
            nmod_poly_set(s + ss->off_w + i * ss->ur.Cw + j, nmod_poly_vec_entry(w_dagger[i], j));
        }
    }
    r_to_bits(s + ss->off_r, sp->r_D);
    r_to_bits(s + ss->off_r + R_ELEMS, r_P);
    r_to_bits(s + ss->off_r + 2 * R_ELEMS, r_W);
    return s;
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

    // ZK⋆ for what remains: equations (1)-(3), the openings of D, P and W,
    // and the binary witness.
    evmlr_zk_stmt_struct st;
    shuffle_stmt_t ss;
    uint8_t zk_pp[32];
    shuffle_stmt(&st, &ss, proof, hash1, alpha, beta, lambda, gamma, ctx, pp);
    zk_public_seed(zk_pp);
    int valid = evmlr_zk_verify(proof->zk, &st, zk_pp);
    shuffle_stmt_clear(&st, &ss);

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

    // ZK⋆ for what remains: equations (1)-(3), the openings of D, P and W,
    // and the binary witness.
    evmlr_zk_stmt_struct st;
    shuffle_stmt_t ss;
    uint8_t zk_pp[32];
    shuffle_stmt(&st, &ss, proof, hash1, alpha, beta, lambda, gamma, ctx, pp);
    zk_public_seed(zk_pp);
    nmod_poly_struct *s = shuffle_witness(&st, &ss, (const nmod_poly_mat_struct (*)[1]) w_dagger,
                                          sigma, r_P, r_W, sp);
    // ZK⋆ refuses when the statement does not hold for this witness, e.g.
    // when the outputs are not a shuffle of the inputs; the proof is then left
    // incomplete and does not verify, which is all this void function can say.
    evmlr_zk_prove(proof->zk, s, &st, zk_pp);
#ifdef MAIN
    zk_carry_ratio = evmlr_zk_carry_norm(s, &st) / st.k_bound;
#endif
    for (slong j = 0; j < st.m; j++) nmod_poly_clear(s + j);
    flint_free(s);
    shuffle_stmt_clear(&st, &ss);

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

    /* The carry bound is statistical; an honest carry past it would make the
     * prover refuse. Check, and report, how much room it leaves. */
    TEST_ONCE("the honest carry sits inside its statistical bound") {
        evmlr_shuffle_proof_t proof;
        evmlr_proof_init(proof, ctx);
        evmlr_shuffle_prove(proof, sp, pp, ctx, state);
        evmlr_proof_clear(proof, ctx);
        printf("\n    ||k|| / k_bound = %.3f\n", zk_carry_ratio);
        TEST_ASSERT(zk_carry_ratio > 0 && zk_carry_ratio < 0.9, end);
    } TEST_END;

    TEST_ONCE("a proof does not verify once a value it is bound to changes") {
        evmlr_shuffle_proof_t proof;
        evmlr_proof_init(proof, ctx);
        evmlr_shuffle_prove(proof, sp, pp, ctx, state);
        int honest = evmlr_shuffle_verify(proof, ctx, pp);
        nmod_poly_struct *u0 = nmod_poly_mat_entry(proof->u, 0, 0);
        nmod_poly_set_coeff_ui(u0, 1, n_addmod(nmod_poly_get_coeff_ui(u0, 1), 1, MOD_Q));
        int altered = evmlr_shuffle_verify(proof, ctx, pp);
        evmlr_proof_clear(proof, ctx);
        TEST_ASSERT(honest == 1 && altered == 0, end);
    } TEST_END;

    /* An output that is not a re-ordering of the decrypted inputs has no
     * witness: the prover cannot make equations (1)-(3) hold, and whatever it
     * publishes does not verify. */
    TEST_ONCE("outputs that are not a shuffle of the inputs are not accepted") {
        nmod_poly_struct *c0 = nmod_poly_mat_entry(pp->c_hat[0], 0, 0);
        ulong old = nmod_poly_get_coeff_ui(c0, 0);
        nmod_poly_set_coeff_ui(c0, 0, n_addmod(old, 1, MOD_Q));
        int accepted = evmlr_shuffle_run(sp, pp, ctx, state);
        nmod_poly_set_coeff_ui(c0, 0, old);
        TEST_ASSERT(accepted == 0, end);
    } TEST_END;

    end:
        evmlr_shuffle_clear_sp(sp, ctx);
        evmlr_shuffle_clear_pp(pp, ctx);
}

void bench(evmlr_shuffle_ctx_t ctx, flint_rand_t state) {
    evmlr_shuffle_sp_t sp;
    evmlr_shuffle_pp_t pp;
    setup(sp, pp, ctx, state);

    evmlr_shuffle_proof_t proof;
    evmlr_proof_init(proof, ctx);
    BENCH_BEGIN("evmlr_shuffle_prove") {
        BENCH_ADD(evmlr_shuffle_prove(proof, sp, pp, ctx, state))
    } BENCH_END;
    BENCH_BEGIN("evmlr_shuffle_verify") {
        BENCH_ADD(evmlr_shuffle_verify(proof, ctx, pp))
    } BENCH_END;
    evmlr_proof_clear(proof, ctx);

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