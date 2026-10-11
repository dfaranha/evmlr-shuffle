#ifndef EVMLR_SHUFFLE_EVMLR_BALLOT_H
#define EVMLR_SHUFFLE_EVMLR_BALLOT_H

/**
 * @file
 *
 * A voter's ballot: the vote encrypted in k HPKE layers, layer i under
 * server i's key and encrypting the serialisation of layer i + 1, outermost
 * first; only the outermost layer is public. The encryption keeps each
 * layer's secrets, which a proof of correct encryption needs.
 */

#include "evmlr_params.h"
#include "evmlr_mlpke.h"
#include "evmlr_otse.h"
#include "evmlr_hpke.h"

/** The secrets of one layer that the proof needs, as the encryption made them. */
typedef struct {
    nmod_poly_mat_t r, e2;    /**< 1 x K_LWE, CBD(ETA) mod q */
    nmod_poly_t e3;           /**< CBD(ETA) mod q */
    nmod_poly_mat_t sbar;     /**< K_LWR x 1, binary */
    nmod_poly_mat_t d_dagger; /**< 2 ETA (K_LWE + L_max) x 1, the stacked bits of d */
} evmlr_ballot_layer_struct;

/** The outermost layer of a ballot, which is public. */
typedef struct {
    evmlr_mlpke_cipher_t enc[K_LWR];
    nmod_poly_mat_t cstar;    /**< L_0 x 1, L_0 = (k - 1) K_LWR (K_LWE + 1) + 1 */
} evmlr_ballot_struct;

/** The length of the OTSE plaintext of layer i out of k, L_i. */
slong evmlr_ballot_layer_len(slong k, slong i);

void evmlr_ballot_layers_init(evmlr_ballot_layer_struct *layers, slong k, slong L_max);
void evmlr_ballot_layers_clear(evmlr_ballot_layer_struct *layers, slong k);
void evmlr_ballot_init(evmlr_ballot_struct *ballot, slong k);
void evmlr_ballot_clear(evmlr_ballot_struct *ballot);

/**
 * Encrypts @p vote (M_LEN x 1) in k layers under @p pks[0..k-1], outermost
 * first, keeping each layer's secrets in @p layers. The OTSE context of
 * @p hpke has L = L_max = (k - 1) K_LWR (K_LWE + 1) + 1, as in evmlr_voting.
 */
void evmlr_ballot_encrypt(evmlr_ballot_struct *ballot, evmlr_ballot_layer_struct *layers,
                        const nmod_poly_mat_t vote, slong k, const evmlr_mlpke_pk_t *pks,
                        const evmlr_hpke_ctx_t hpke);

#endif // EVMLR_SHUFFLE_EVMLR_BALLOT_H
