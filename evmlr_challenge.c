#include "evmlr_challenge.h"
#include "fastrandombytes.h"
#include <string.h>

void evmlr_challenge_init(evmlr_challenge_t chal) {
    SHA256Reset(&chal->sha);
    chal->finalized = 0;
}

void evmlr_challenge_add_matrix(evmlr_challenge_t chal, const nmod_poly_mat_t mat) {
    if (chal->finalized) return;
    for (slong i = 0; i < nmod_poly_mat_nrows(mat); i++) {
        for (slong j = 0; j < nmod_poly_mat_ncols(mat); j++) {
            nmod_poly_struct *poly = nmod_poly_mat_entry(mat, i, j);
            for (slong c = 0; c < nmod_poly_length(poly); c++) {
                ulong coeff = nmod_poly_get_coeff_ui(poly, c);
                SHA256Input(&chal->sha, (const uint8_t *)&coeff, sizeof(ulong));
            }
        }
    }
}

void evmlr_challenge_add_poly(evmlr_challenge_t chal, const nmod_poly_t poly) {
    if (chal->finalized) return;
    for (slong c = 0; c < nmod_poly_length(poly); c++) {
        ulong coeff = nmod_poly_get_coeff_ui(poly, c);
        SHA256Input(&chal->sha, (const uint8_t *)&coeff, sizeof(ulong));
    }
}

void evmlr_challenge_add_bytes(evmlr_challenge_t chal, const uint8_t* bytes, size_t len) {
    if (chal->finalized) return;
    SHA256Input(&chal->sha, bytes, len);
}

static void ensure_seeded(evmlr_challenge_t chal) {
    if (!chal->finalized) {
        SHA256Result(&(chal->sha), chal->hash);
        prg_setseed(&chal->prg, chal->hash);
        chal->finalized = 1;
    }
}

void evmlr_challenge_get_poly(nmod_poly_t out, int degree, evmlr_challenge_t chal) {
    ensure_seeded(chal);
    if (out) nmod_poly_zero(out);
    ulong buf;
    for (int i = 0; i < degree; i++) {
        prg_bytes(&chal->prg, (unsigned char *)&buf, sizeof(buf));
        if (out) nmod_poly_set_coeff_ui(out, i, buf % MOD_Q);
    }
}

void evmlr_challenge_get_poly_one_ternary(nmod_poly_t out, evmlr_challenge_t chal) {
    ensure_seeded(chal);
    if (out) nmod_poly_zero(out);
    int count = 0;
    while (count < 1) {
        ulong idx;
        prg_bytes(&chal->prg, (unsigned char *)&idx, sizeof(ulong));
        idx %= DEGREE_N;
        if (!out || nmod_poly_get_coeff_ui(out, idx) == 0) {
            ulong sign;
            prg_bytes(&chal->prg, (unsigned char *)&sign, 1);
            if (out) nmod_poly_set_coeff_ui(out, idx, (sign & 1) ? 1 : MOD_Q - 1);
            count++;
        }
    }
}

void evmlr_challenge_get_poly_symmetric(nmod_poly_t out, evmlr_challenge_t chal) {
    ensure_seeded(chal);
    if (out) nmod_poly_zero(out);
    ulong buf;
    // Sample c_0
    prg_bytes(&chal->prg, (unsigned char *)&buf, sizeof(buf));
    if (out) nmod_poly_set_coeff_ui(out, 0, buf % MOD_Q);
    // Sample c_i and set c_i, -c_i
    for (int i = 1; i < (DEGREE_N >> 1); i++) {
        prg_bytes(&chal->prg, (unsigned char *)&buf, sizeof(buf));
        ulong val = buf % MOD_Q;
        if (out) {
            nmod_poly_set_coeff_ui(out, i, val);
            if (val > 0) {
                nmod_poly_set_coeff_ui(out, DEGREE_N - i, MOD_Q - val);
            } else {
                nmod_poly_set_coeff_ui(out, DEGREE_N - i, 0);
            }
        }
    }
}

void evmlr_challenge_get_val(ulong* val, evmlr_challenge_t chal) {
    ensure_seeded(chal);
    ulong buf;
    prg_bytes(&chal->prg, (unsigned char *)&buf, sizeof(buf));
    *val = buf % MOD_Q;
}

void evmlr_challenge_get_vector(ulong* vec, slong len, evmlr_challenge_t chal) {
    ensure_seeded(chal);
    ulong buf;
    for (slong i = 0; i < len; i++) {
        prg_bytes(&chal->prg, (unsigned char *)&buf, sizeof(buf));
        vec[i] = buf % MOD_Q;
    }
}

void evmlr_challenge_get_hash(uint8_t hash[SHA256HashSize], evmlr_challenge_t chal) {
    ensure_seeded(chal);
    memcpy(hash, chal->hash, SHA256HashSize);
}
