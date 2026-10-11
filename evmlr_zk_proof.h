#ifndef EVMLR_SHUFFLE_EVMLR_ZK_PROOF_H
#define EVMLR_SHUFFLE_EVMLR_ZK_PROOF_H

/**
 * @file
 *
 * ZK⋆: a proof that a binary vector s satisfies E s = t, each row modulo its
 * own modulus Q_r (q, or 2^ZETA for the rounding relation), run in R_p
 * (SHUFFLE-ZK.md). The statement is lifted to E s - Q k = t over the
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

/** Rows of the Ajtai part of the commitment: 5 since the shuffle's statement
 * took in the proof of correct decryption, whose carries raised the MSIS
 * bound past what 4 rows hold (ZK_BETA_MAX). */
#define ZK_KAPPA 5
/** Number of aggregated constant-coefficient checks; error p^-ZK_LAMBDA. */
#define ZK_LAMBDA 4
/** Rows of each Johnson-Lindenstrauss projection. */
#define ZK_PROJ 256
/** Number of projections, one per block of the witness: the binary s (with
 * the projections' signs), the carries of the first rows1 rows, and those of
 * the rest. Each block's bound is certified by its own projection, so that a
 * block's large bound does not loosen another's: s's bound is what the binary
 * claim depends on, and the shuffle's few large carries would loosen the
 * bound on the decryption's many small ones. */
#define ZK_NPROJ 3
/** Message slots of the BDLOP part committed with the witness: the masks
 * g_1..g_LAMBDA; the projection masks, one slot each in their first ZK_PROJ
 * coefficients; and F = sum_j sigma(s_j)(s_j - 1). */
#define ZK_SLOT_Y(i) (ZK_LAMBDA + (i))
#define ZK_SLOT_F (ZK_LAMBDA + ZK_NPROJ)
#define ZK_SLOTS (ZK_LAMBDA + ZK_NPROJ + 1)
/** The garbage term of the binary claim, committed with each first message
 * under the same randomness, in one more BDLOP row. */
#define ZK_SLOT_G ZK_SLOTS
/** Extra randomness rank for hiding: the commitment hides (s, k) under MLWE of
 * this rank over R_p with ternary secrets, 133 bits core-SVP at rank 5 and
 * p = 2^52 (98 at rank 4; it was 2, about 35 bits). */
#define ZK_HIDE 5
/** The largest MSIS bound, 2 ||c - c'||_1 ||z - z'|| <= 4 ||c - c'||_1 B_z,
 * that binding is estimated for: ZK_KAPPA = 5 rows over R_p give at least 164
 * bits core-SVP up to it (lattice-estimator, 207 at 2^45, 184 at 2^47). The
 * shuffle with decryption reaches about 2^47.1 at N = 1000 messages of
 * L = 7 (three servers). */
#define ZK_BETA_MAX 0x1p49
/** Length of the commitment randomness s_2. */
#define ZK_M2 (ZK_KAPPA + ZK_SLOTS + 1 + ZK_HIDE)

typedef struct evmlr_zk_stmt_struct evmlr_zk_stmt_struct;

/**
 * A statement E s = t over R, with E of size rows x m, each row modulo its own
 * modulus: that of t[r], MOD_Q or 2^ZETA (the rounding relation (3)).
 */
struct evmlr_zk_stmt_struct {
    slong m;        /**< witness length, in ring elements */
    slong rows;     /**< number of ring equations */
    nmod_poly_struct *t; /**< the right-hand side, rows elements, each mod its row's modulus */
    slong rows1;    /**< rows [0, rows1) have carries bounded by k_bound, the others by k_bound2 */
    double k_bound; /**< a public bound on the l2 norm of the carries of rows [0, rows1) */
    double k_bound2; /**< and of rows [rows1, rows) */
    uint8_t digest[SHA256HashSize]; /**< hash of E and t, for Fiat-Shamir */
    slong col_max;  /**< the most nonzero entries a column of E has */
    /**
     * Column j < m of E, lifted to R_p through centred representatives: sets
     * out[i] = E[rows_out[i]][j] for each nonzero entry, at most col_max of
     * them (out initialised mod p), and returns how many. The proof streams
     * over the columns, so E is never held whole.
     */
    slong (*column)(nmod_poly_struct *out, slong *rows_out, slong j, const evmlr_zk_stmt_struct *st);
    void *data;     /**< for column */
};

/** A proof. Every vector is in R_p. */
typedef struct {
    slong m, rows;
    nmod_poly_struct *tA;  /**< ZK_KAPPA: Ajtai part */
    nmod_poly_struct *tB;  /**< ZK_SLOTS: BDLOP part */
    nmod_poly_t tG;        /**< BDLOP row ZK_SLOT_G: the garbage term */
    nmod_poly_struct *h;   /**< ZK_LAMBDA: aggregated values, ct(h_l) = 0 */
    nmod_poly_struct *z1;  /**< m + 1 + rows: masked opening of (s, signs, k) */
    nmod_poly_struct *z2;  /**< ZK_M2: masked opening of s_2 */
    slong z3[ZK_NPROJ * ZK_PROJ]; /**< the projections b_i R_i v_i + y_i of the blocks */
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

/**
 * The encoding of @p pi for the statement @p st, whose shape and carry bound
 * fix the widths the Gaussian parts are coded for: its length in bytes, and
 * the encoding itself into @p buf, which must hold that many.
 */
size_t evmlr_zk_proof_size(const evmlr_zk_proof_t pi, const evmlr_zk_stmt_struct *st);
size_t evmlr_zk_proof_encode(uint8_t *buf, const evmlr_zk_proof_t pi,
                             const evmlr_zk_stmt_struct *st);

/**
 * Decodes @p len bytes into @p pi, initialised for the shape of @p st.
 * Returns 1 only for a canonical encoding: every coefficient in range, no
 * byte left over and zero padding, so that a proof has exactly one encoding.
 */
int evmlr_zk_proof_decode(evmlr_zk_proof_t pi, const uint8_t *buf, size_t len,
                          const evmlr_zk_stmt_struct *st);

/** Verifies @p pi against @p st and @p pp. */
int evmlr_zk_verify(const evmlr_zk_proof_t pi, const evmlr_zk_stmt_struct *st,
                    const uint8_t pp[32]);

/** Indices into the widths: the masked openings of (s, signs), of the two
 * carry blocks and of s_2; and the projection masks of the three blocks. */
enum { ZK_SG_S, ZK_SG_K1, ZK_SG_K2, ZK_SG_2, ZK_SG_P0, ZK_SG_P1, ZK_SG_P2, ZK_SIGMAS };

/**
 * The Gaussian widths for a statement of @p st's shape (m, rows, rows1) and
 * carry bounds. Exposed for tests and size estimates.
 */
void evmlr_zk_sigmas(double sigma[ZK_SIGMAS], const evmlr_zk_stmt_struct *st);

/**
 * The bounds on the blocks' norms that a verified proof certifies, through
 * the projections: for R drawn after a vector v and the mask y are committed,
 * ||R v + y mod p|| >= ||v|| sqrt(26) / 2 except with probability 2^-128
 * (LNP22, Lemma 2.9, for ||v|| at most p / 41 over v's dimension, which
 * evmlr_zk_supported checks), so ||v|| < 2 ||z|| / sqrt(26), and the verifier
 * bounds ||z||.
 */
void evmlr_zk_certified(double bound[ZK_NPROJ], const evmlr_zk_stmt_struct *st);

/** The MSIS bound binding rests on for a statement of this shape. */
double evmlr_zk_msis_bound(const evmlr_zk_stmt_struct *st);

/**
 * Whether these parameters cover a statement of this shape: the certified
 * bounds leave neither the lifted linear claim nor the binary claim room to
 * wrap mod p, they meet the projection lemma's condition, and the MSIS bound
 * is one binding was estimated for. Prover and verifier both refuse a
 * statement for which this fails.
 */
int evmlr_zk_supported(const evmlr_zk_stmt_struct *st);

/**
 * The larger of ||k_1|| / k_bound and ||k_2|| / k_bound2 for the carries of
 * the binary witness @p s, or -1 if E s != t. For checking that a statement's
 * carry bounds have room, in tests.
 */
double evmlr_zk_carry_ratio(const nmod_poly_struct *s, const evmlr_zk_stmt_struct *st);

#endif // EVMLR_SHUFFLE_EVMLR_ZK_PROOF_H
