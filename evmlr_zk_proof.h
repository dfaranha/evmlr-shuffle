#ifndef EVMLR_SHUFFLE_EVMLR_ZK_PROOF_H
#define EVMLR_SHUFFLE_EVMLR_ZK_PROOF_H

/**
 * @file
 *
 * ZK⋆: a proof that a binary vector s satisfies E s = t (mod q), run in R_p
 * (SHUFFLE-ZK.md). The statement is lifted to E s - q k = t over the
 * integers, with the carry k committed beside s in the Ajtai part of one
 * ABDLOP commitment; every claim is reduced to constant coefficients being
 * zero, aggregated into ZK_LAMBDA published values h_l, and tied to the
 * commitment by challenge-free first messages that are hashed rather than
 * sent.
 *
 * The statement is given by a callback that produces one column of E at a
 * time, so E is never stored: the shuffle builds each column from its
 * message's data, which keeps memory linear in the number of messages.
 */

#include "evmlr_zk.h"
#include "sha.h"

/** Rows of the Ajtai part of the commitment. */
#define ZK_KAPPA 4
/** Number of aggregated constant-coefficient checks; error p^-ZK_LAMBDA. */
#define ZK_LAMBDA 4
/** Rows of each Johnson-Lindenstrauss projection. There are two, one bounding
 * the binary witness s and one the carry k, so that the carry's much larger
 * bound does not loosen the one on s, which the binary claim depends on. */
#define ZK_PROJ 256
/** Message slots of the BDLOP part committed with the witness: the masks
 * g_1..g_LAMBDA; the projection masks of s and of k, one slot each in their
 * first ZK_PROJ coefficients, so that each projection is redrawn on its own
 * when its rejection test fails; and F = sum_j sigma(s_j)(s_j - 1). */
#define ZK_SLOT_YS ZK_LAMBDA
#define ZK_SLOT_YK (ZK_LAMBDA + 1)
#define ZK_SLOT_F (ZK_LAMBDA + 2)
#define ZK_SLOTS (ZK_LAMBDA + 3)
/** The garbage term of the binary claim, committed with each first message
 * under the same randomness, in one more BDLOP row. */
#define ZK_SLOT_G ZK_SLOTS
/** Extra randomness rank for hiding: the commitment hides (s, k) under MLWE of
 * this rank over R_p with ternary secrets, 133 bits core-SVP at rank 5 and
 * p = 2^52 (98 at rank 4; it was 2, about 35 bits). */
#define ZK_HIDE 5
/** The largest MSIS bound, 2 ||c - c'||_1 ||z - z'|| <= 4 ||c - c'||_1 B_z,
 * that binding is estimated for: ZK_KAPPA = 4 rows over R_p give at least 173
 * bits core-SVP up to it. The shuffle reaches 2^42.9 at N = 1000 messages,
 * 174 bits. */
#define ZK_BETA_MAX 0x1p43
/** Length of the commitment randomness s_2. */
#define ZK_M2 (ZK_KAPPA + ZK_SLOTS + 1 + ZK_HIDE)

typedef struct evmlr_zk_stmt_struct evmlr_zk_stmt_struct;

/**
 * A statement E s = t (mod q) over R_q, with E of size rows x m.
 */
struct evmlr_zk_stmt_struct {
    slong m;        /**< witness length, in ring elements */
    slong rows;     /**< number of ring equations */
    nmod_poly_struct *t; /**< the right-hand side, rows elements mod q */
    double k_bound; /**< a public bound on the l2 norm of the carry k */
    uint8_t digest[SHA256HashSize]; /**< hash of E and t, for Fiat-Shamir */
    /**
     * Column j < m of E, lifted to R_p through centred representatives: sets
     * out[r] = E[r][j] for every row r (out has rows elements, initialised mod
     * p) and returns a mask with bit r set where it is nonzero. The proof
     * streams over the columns, so E is never held whole.
     */
    uint32_t (*column)(nmod_poly_struct *out, slong j, const evmlr_zk_stmt_struct *st);
    void *data;     /**< for column */
};

/** A proof. Every vector is in R_p. */
typedef struct {
    slong m, rows;
    nmod_poly_struct *tA;  /**< ZK_KAPPA: Ajtai part */
    nmod_poly_struct *tB;  /**< ZK_SLOTS: BDLOP part */
    nmod_poly_t tG;        /**< BDLOP row ZK_SLOT_G: the garbage term */
    nmod_poly_struct *h;   /**< ZK_LAMBDA: aggregated values, ct(h_l) = 0 */
    nmod_poly_struct *z1;  /**< m + rows: masked opening of (s, k) */
    nmod_poly_struct *z2;  /**< ZK_M2: masked opening of s_2 */
    slong z3[2 * ZK_PROJ]; /**< the projections R_s s + y_s and R_k k + y_k */
    uint8_t hash[SHA256HashSize]; /**< the hash the challenge came from */
} evmlr_zk_proof_struct;
typedef evmlr_zk_proof_struct evmlr_zk_proof_t[1];

void evmlr_zk_proof_init(evmlr_zk_proof_t pi, slong m, slong rows);
void evmlr_zk_proof_clear(evmlr_zk_proof_t pi);

/**
 * Proves that the binary vector @p s (m elements mod q with 0/1
 * coefficients) satisfies the statement @p st, under the public parameters
 * expanded from @p pp. Returns 0 if the statement does not hold for s.
 */
int evmlr_zk_prove(evmlr_zk_proof_t pi, const nmod_poly_struct *s,
                   const evmlr_zk_stmt_struct *st, const uint8_t pp[32]);

/** Verifies @p pi against @p st and @p pp. */
int evmlr_zk_verify(const evmlr_zk_proof_t pi, const evmlr_zk_stmt_struct *st,
                    const uint8_t pp[32]);

/**
 * The Gaussian widths of the masked openings of s, of k and of s_2, and of
 * the projection masks of s and of k, for a
 * witness of @p m elements and a carry bound @p k_bound. Exposed for tests and
 * size estimates.
 */
void evmlr_zk_sigmas(double sigma[5], slong m, double k_bound);

/**
 * The bounds on ||s|| and ||k|| that a verified proof certifies, through the
 * projections: for R drawn after a vector v and the mask y are committed,
 * ||R v + y|| >= ||v|| / 2 except with probability 2^-128 (the projection
 * lemma of LNP22; the constant is to be checked), so ||v|| <= 2 ||z||, and
 * the verifier bounds ||z||.
 */
void evmlr_zk_certified(double bound[2], slong m, double k_bound);

/** The MSIS bound binding rests on for a statement of this shape. */
double evmlr_zk_msis_bound(slong m, slong rows, double k_bound);

/**
 * Whether these parameters cover a statement of this shape: the certified
 * bounds leave neither the lifted linear claim nor the binary claim room to
 * wrap mod p, and the MSIS bound is one binding was estimated for. Prover and
 * verifier both refuse a statement for which this fails.
 */
int evmlr_zk_supported(slong m, slong rows, double k_bound);

/**
 * ||k|| for the carry of the binary witness @p s, or -1 if E s != t (mod q).
 * For checking that a statement's k_bound has room, in tests.
 */
double evmlr_zk_carry_norm(const nmod_poly_struct *s, const evmlr_zk_stmt_struct *st);

#endif // EVMLR_SHUFFLE_EVMLR_ZK_PROOF_H
