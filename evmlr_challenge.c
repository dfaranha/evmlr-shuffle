#include "evmlr_challenge.h"
#include "fastrandombytes.h"
#include <string.h>

void evmlr_challenge_init(evmlr_challenge_t chal) {
    SHA256Reset(&chal->sha);
    chal->finalized = 0;
}

/* Coefficients are absorbed in two little-endian bytes, the fewest that hold
 * a residue, and every polynomial and matrix is preceded by its dimensions,
 * so that two different transcripts cannot absorb the same bytes. Each
 * coefficient used to take the eight bytes of a ulong, six of them zero, and
 * polynomials were absorbed back to back with nothing to mark where one ended:
 * moving a trailing coefficient from one into the next left the hash
 * unchanged. */
_Static_assert(MOD_Q <= 65536, "challenge coefficients are absorbed in two bytes");

static void absorb_word(evmlr_challenge_t chal, uint64_t v) {
    uint8_t buf[8];

    for (int b = 0; b < 8; b++) {
        buf[b] = (uint8_t) (v >> (8 * b));
    }
    SHA256Input(&chal->sha, buf, sizeof(buf));
}

static void absorb_poly(evmlr_challenge_t chal, const nmod_poly_struct *poly) {
    slong len = nmod_poly_length(poly);
    uint8_t buf[2 * DEGREE_N];
    slong done = 0;

    absorb_word(chal, (uint64_t) len);
    while (done < len) {
        slong n = (len - done < DEGREE_N) ? len - done : DEGREE_N;

        for (slong c = 0; c < n; c++) {
            ulong coeff = poly->coeffs[done + c];

            buf[2 * c] = (uint8_t) coeff;
            buf[2 * c + 1] = (uint8_t) (coeff >> 8);
        }
        SHA256Input(&chal->sha, buf, 2 * n);
        done += n;
    }
}

void evmlr_challenge_add_matrix(evmlr_challenge_t chal, const nmod_poly_mat_t mat) {
    if (chal->finalized) return;
    absorb_word(chal, (uint64_t) nmod_poly_mat_nrows(mat));
    absorb_word(chal, (uint64_t) nmod_poly_mat_ncols(mat));
    for (slong i = 0; i < nmod_poly_mat_nrows(mat); i++) {
        for (slong j = 0; j < nmod_poly_mat_ncols(mat); j++) {
            absorb_poly(chal, nmod_poly_mat_entry(mat, i, j));
        }
    }
}

void evmlr_challenge_add_poly(evmlr_challenge_t chal, const nmod_poly_t poly) {
    if (chal->finalized) return;
    absorb_poly(chal, poly);
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
