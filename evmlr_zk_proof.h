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
 * The statement is given by a callback that applies E to a vector, so E is
 * never stored: the shuffle builds it block by block, which keeps time and
 * memory linear in the number of messages.
 */

#include "evmlr_zk.h"
#include "sha.h"

/** Rows of the Ajtai part of the commitment. */
#define ZK_KAPPA 4
/** Number of aggregated constant-coefficient checks; error p^-ZK_LAMBDA. */
#define ZK_LAMBDA 4
/** Message slots of the BDLOP part: the masks g_1..g_LAMBDA. */
#define ZK_SLOTS ZK_LAMBDA
/** Extra randomness rank for hiding. */
#define ZK_HIDE 2
/** Length of the commitment randomness s_2. */
#define ZK_M2 (ZK_KAPPA + ZK_SLOTS + ZK_HIDE)

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
     * out[r] = sum_j E[r][j] v[j] in R_p, for every row r, with E lifted
     * through its centred representatives. out has rows elements, already
     * initialised mod p; v has m elements mod p.
     */
    void (*apply)(nmod_poly_struct *out, const nmod_poly_struct *v,
                  const evmlr_zk_stmt_struct *st);
    void *data;     /**< for apply */
};

/** A proof. Every vector is in R_p. */
typedef struct {
    slong m, rows;
    nmod_poly_struct *tA;  /**< ZK_KAPPA: Ajtai part */
    nmod_poly_struct *tB;  /**< ZK_SLOTS: BDLOP part */
    nmod_poly_struct *h;   /**< ZK_LAMBDA: aggregated values, ct(h_l) = 0 */
    nmod_poly_struct *z1;  /**< m + rows: masked opening of (s, k) */
    nmod_poly_struct *z2;  /**< ZK_M2: masked opening of s_2 */
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
 * The Gaussian widths of the masked openings: of s, of k and of s_2, for a
 * witness of @p m elements and a carry bound @p k_bound. Exposed for tests and
 * size estimates.
 */
void evmlr_zk_sigmas(double sigma[3], slong m, double k_bound);

#endif // EVMLR_SHUFFLE_EVMLR_ZK_PROOF_H
