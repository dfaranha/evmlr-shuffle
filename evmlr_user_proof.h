#ifndef EVMLR_SHUFFLE_EVMLR_USER_PROOF_H
#define EVMLR_SHUFFLE_EVMLR_USER_PROOF_H

/**
 * @file
 *
 * The user's proof of correct layered encryption (Section 3.3 of the paper,
 * "Proof of correct encryption"), in LaZer (option A' of PROOF-SYSTEM.md).
 *
 * A ballot for k servers is the outermost of k HPKE layers: layer i encrypts,
 * under server i's key, the serialisation of layer i + 1, and the innermost
 * layer encrypts the vote. Only the outermost layer is public. The proof is
 * one LaZer linear statement across all layers, mod 64 q, with witness, per
 * layer i:
 *
 *   - r, e2, e3: the MLPKE randomness, CBD(ETA), l2-bounded;
 *   - sbar: the OTSE seed, binary;
 *   - the bits of d = round(H sbar) and of the rounding error, for the
 *     K_LWE + L_i positions of the pad that the next layer's ciphertext and
 *     the vote depend on, binary;
 *
 * and the vote m, binary, with a copy u of l2 norm at most 1.
 *
 * The rows are layer 0's MLPKE encryption, and for each inner layer its MLPKE
 * encryption expressed through the outer layers' OTSE pads (an inner
 * ciphertext is the outer one minus the pads), mod q and scaled by 64; and
 * the rounding relation (3) for each pad position used, mod 2^ZETA and
 * scaled by q; the vote's position of the outermost ciphertext as m plus every
 * layer's pad there; and m - u = 0. A binary m equal to a u of norm at most 1
 * is X^j or 0: the ballot is a vote for one candidate, or for none. Which j is
 * a candidate is left to the tally.
 *
 * LaZer is optional at build time (make LAZER_DIR=...). Without it,
 * evmlr_user_proof_available() is 0 and the prover and verifier refuse.
 */

#include "evmlr_ballot.h"
#include <stdint.h>

typedef struct {
    uint8_t *data;
    size_t len;
} evmlr_user_proof_struct;
typedef evmlr_user_proof_struct evmlr_user_proof_t[1];

/** Whether LaZer was built in, and has parameters for k servers. */
int evmlr_user_proof_available(slong k);

void evmlr_user_proof_init(evmlr_user_proof_t pi);
void evmlr_user_proof_clear(evmlr_user_proof_t pi);

/**
 * Proves that @p ballot is a correct k-layer encryption of @p vote (M_LEN x
 * 1), and that the vote is X^j or 0, with the secrets in @p layers. Returns 0,
 * leaving no proof, when the vote is not of that form, the secrets do not
 * satisfy the statement, or LaZer is not available.
 */
int evmlr_user_proof_prove(evmlr_user_proof_t pi, const evmlr_ballot_struct *ballot,
                           const evmlr_ballot_layer_struct *layers, const nmod_poly_mat_t vote,
                           slong k, const evmlr_mlpke_pk_t *pks, const evmlr_otse_ctx_t otse);

/** Verifies @p pi for @p ballot. */
int evmlr_user_proof_verify(const evmlr_user_proof_t pi, const evmlr_ballot_struct *ballot,
                            slong k, const evmlr_mlpke_pk_t *pks, const evmlr_otse_ctx_t otse);

#endif // EVMLR_SHUFFLE_EVMLR_USER_PROOF_H
