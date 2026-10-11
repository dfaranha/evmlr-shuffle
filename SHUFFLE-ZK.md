# ZK⋆ for the proof of shuffle

The proof system that Protocol 1 of ePrint 2025/658 calls `ZK⋆`, specialised to
the shuffle. It replaces `evmlr_lin_proof` and `evmlr_bin_proof` in
`evmlr_shuffle.c`, which cannot be sound at `q = 3109` (`PROOF-SYSTEM.md`,
section 1). It follows Lyubashevsky, Nguyen and Plançon (CRYPTO 2022, "LNP22"),
the construction behind LaZer, but is written for this one statement so that
time and memory stay linear in the number of messages `N`; LaZer's general
prover does not (`PROOF-SYSTEM.md`, section 2).

## 1. The statement

Protocol 1 is unchanged. Before `ZK⋆` runs, the prover has published the
Com⋆ commitments `D`, `P`, `W` mod `q`, and both sides know the challenges
`α, β, λ, γ` and the `u_1, ..., u_{N-1}`. What remains to prove, with every
equation mod `q` over `R_q = Z_q[x]/(x^n + 1)`, `n = 512`:

1. equations (1)–(3) of Protocol 1, `N` ring equations, each involving only
   message `i`'s variables: `h_i` is linear in `d†_i`, `ĥ_i` in `σ_i`, and the
   right-hand side is `G w†_i`;
2. `Verify⋆(D, d†, r_D)`, `Verify⋆(P, σ, r_P)`, `Verify⋆(W, w†, r_W)`: three
   pairs of ring equations `A_1 m + A_2 r = c`, and the norm bound;
3. `is_bin(d†_i)`, `is_bin(σ_i)`, `is_bin(w†_i)`.

**Batching the `N` equations.** Every variable in them is already bound by
`D`, `P` or `W`, and the `u_i` are fixed, before `ZK⋆` starts. So they are
replaced by one random combination `Σ_i ρ_i · eq_i = 0`, with `ρ_i ∈ R_q`
derived by hashing the whole statement. If some `eq_i ≠ 0` for the committed
witness, the combination vanishes with probability at most `q^{-n/2}` per
`R_q`-component, since `R_q` is a product of two fields of size `q^{n/2}`
(`q ≡ 5 mod 8`). This leaves `R = 1 + 3 · 2 = 7` ring equations.

**Making the witness binary.** The Com⋆ randomness `r` is CBD(η = 2): each
coefficient is `a_1 + a_2 - b_1 - b_2` for bits. The prover decomposes each of
the 3 × 4 polynomials of randomness into 4 binary polynomials, so the opening
equations read `A_2 (B r^bits) = ...` with `B` the fixed map
`(a_1, a_2, b_1, b_2) ↦ a_1 + a_2 - b_1 - b_2`. Shortness of `r` then follows
from binariness, and Com⋆'s norm bound holds exactly, which an approximate
norm proof could not give: Com⋆ binds only for openings of norm well below
`q`.

So the witness is one binary vector

```
s = (d†_1..N, σ_1..N, w†_1..N, bits(r_D), bits(r_P), bits(r_W))
    ∈ {0,1}^{m n},   m = 25 N + 48   (at L = 1)
```

and the statement is `E s = t (mod q)` with `E ∈ R_q^{7 × m}`, `t ∈ R_q^7`.
`E` is built block by block from the protocol's data, never densely.

## 2. Lifting to the proof modulus

Proofs run over `R_p = Z_p[x]/(x^n + 1)` for a prime `p ≫ q` with
`p ≡ 5 mod 8`, so that `R_p` is also a product of two fields (Lemma 1), and
challenge differences are invertible. Over the integers, with the centred
representatives of `E` and `t`,

```
E s - t = q k        for a carry k ∈ Z[x]^7,
```

and the prover commits `k` alongside `s`. Proving `E s - q k = t (mod p)`
plus bounds on `s` and `k` that rule out wraparound,
`‖E s - q k - t‖_∞ < p / 2`, gives the equation over the integers and hence
mod `q`. This is the lifting LaZer does (`lin-codegen.sage`, `Bprime`).

## 3. Commitment (ABDLOP)

```
Ajtai part:  t_A = A_1 s_1 + A_2 s_2            s_1 = (s, k), s_2 ternary
BDLOP part:  t_B,j = <b_j, s_2> + m_j           one row per message slot
```

with `A_1 ∈ R_p^{κ × (m + 7)}`, `A_2 ∈ R_p^{κ × m_2}`, `b_j ∈ R_p^{m_2}`, all
expanded from a public seed on demand, so that `A_1` is never held in full.
The BDLOP slots:

| slot | holds | when |
| --- | --- | --- |
| `F` | `Σ_j σ(s_j)(s_j - 𝟙)` | with `t_A` |
| `Y` | the projection mask, packed into 256 coefficients | with `t_A` |
| `g_1..g_λ` | masks with `ct(g_l) = 0` | with `t_A` |
| `G` | the garbage term of the binary proof | with the first message, per attempt |

`σ` is the automorphism `x ↦ x^{-1}`, `𝟙` the all-ones polynomial, and `ct` the
constant coefficient. The identity everything uses: `ct(σ(a) b) = <a, b>`.

## 4. Challenges

`c` is drawn from `C = { c : σ(c) = c, ‖c‖_∞ ≤ 1, ν' pairs of nonzero
coefficients }`: `c_0 = 0`, and for `ν'` indices `0 < i < n/2`, `c_i = ±1` and
`c_{n-i} = -c_i`. `σ(c) = c` makes the binary proof's identity a polynomial in
`c` alone, which three transcripts determine, as in LNP22; general challenges
would bring in `σ(c)` and an extraction we have not worked out. `ν' = 23`
gives `|C| = 2^23 C(255, 23) ≈ 2^130.9` (22 would give `2^126.6`), and
`‖c‖_1 = 46`. Differences of
challenges have `‖·‖_∞ ≤ 2`, invertible in `R_p` by Lemma 1.

## 5. The claims, and how each is checked

All are reduced to "a constant coefficient is zero" and aggregated, as in the
`lnp` branch of `lattice-voting-ctrsa21` (`LNP.md`, section 5).

**Binary.** `s` is binary iff `Σ_j <s_j, s_j - 𝟙> = 0` over the integers, each
term being non-negative. That is `ct(F) = 0`, provided `F` is the committed
slot and nothing wraps mod `p`.

*F is what it should be.* With `z = y + c s` and `σ(c) = c`,

```
Σ_j σ(z_j)(z_j - c 𝟙) = c² F + c G_0 + G_1,
G_0 = Σ_j σ(y_j)(s_j - 𝟙) + σ(s_j) y_j,     G_1 = Σ_j σ(y_j) y_j .
```

The prover commits `G = G_0 + v_F` in slot `G`, where `v_F = <b_F, y_2>` is
`F`'s mask. With `u_X = <b_X, z_2> - c t_B,X = v_X - c X` for any slot `X`,
the verifier checks

```
τ := Σ_j σ(z_j)(z_j - c 𝟙) + c u_F + u_G      is the prover's τ = v_G + G_1,
```

a challenge-free value that is hashed into `c` rather than sent.

**Linear.** `e_r = E_r s - q k_r - t_r = 0` for `r = 1..7`. For random
`α_{l,r} ∈ R_p`, `Σ_r ct(σ(α_{l,r}) e_r) = Σ_r <α_{l,r}, e_r>` vanishes for a
nonzero `e` with probability `1/p`.

**Short.** Two Johnson-Lindenstrauss projections, one for `s` and one for `k`,
so that the carry's much larger bound does not loosen the one on `s`, which the
binary claim needs below `sqrt(p/2)`. Each has 256 rows with entries `±1` with
probability `1/4` each, streamed per element from a seed hashed after the
commitment, one byte per four rows at one coefficient (so that `Σ_i μ_{l,i} R_i`
is a table lookup per pair of rows); both masks are packed into one slot `Y`. The prover publishes
`z_3 = (R_s s + y_s, R_k k + y_k)`, the masks of width
`9 · sqrt(337) · ‖·‖` and rejection-sampled (3.8 tries each, the ratio the
`lnp` branch used, which certifies 2.4 times tighter than the openings'
21.485), and only slot `Y` is redrawn on rejection. The verifier checks
`‖z_3‖ ≤ 1.7 σ sqrt(256)` per half. The code assumes that for `R` drawn after
`v` and `y` are committed, `‖R v + y‖ ≥ ‖v‖ / 2` except with probability
`2^-128`, so that `‖v‖ ≤ 2 ‖z‖` is certified (`evmlr_zk_certified`). **That
constant is to be checked against the projection lemma of LNP22**, which is not
to hand; the `lnp` branch of `lattice-voting-ctrsa21` used it with the same
caveat. The certified bounds rule out wraparound in the linear claim,
`(q/2) sqrt(m n) B_s + q B_k + q/2 < p/2`, and in the binary claim,
`B_s^2 + sqrt(m n) B_s < p`.
Consistency with the commitment:
`Σ_i μ_{l,i} (<R_i, s_1> + y_{3,i} - z_{3,i}) = 0`.

**Merged.** For `l = 1..λ`, published:

```
h_l = g_l + ν_l F + Σ_r σ(α_{l,r}) e_r + σ(P_l) · s_1 + σ(M_l) Y - Z_l
```

with `P_l = Σ_i μ_{l,i} R_i` (as ring elements), `M_l = Σ_i μ_{l,i} x^i`,
`Z_l = Σ_i μ_{l,i} z_{3,i}`, and the verifier checks `ct(h_l) = 0`. Each `h_l`
is linear in the committed values, so its consistency is a challenge-free
first message `w_l` recomputed from the openings and hashed, like `τ`. With
`λ = 4` and `p ≈ 2^44`, the aggregation error is `2^-176`.

## 6. Order of the transcript

1. Hash the statement; derive `ρ` and so `E`, `t`.
2. Commit `t_A` (from `s_1, s_2`) and slots `F`, `Y`, `g_1..g_λ`.
3. Hash; derive the projection `R`. Publish `z_3`; if its rejection test fails,
   go back to 2 with fresh `y_3` and randomness.
4. Hash with `z_3`; derive `μ`, `ν`, `α`. Compute `h_l`.
5. Sample `y_1, y_2`; commit slot `G`; compute the first messages `w`
   (Ajtai), `τ`, `w_l`. Hash everything into `c`.
6. `z_1 = y_1 + c s_1`, `z_2 = y_2 + c s_2`. One rejection test for all of
   `(z_1, z_2)`, each block scaled by its own width; on rejection go back to 5.

The prover draws two candidates `(y_1, y_2)` at a time and computes their
linear first messages in the same pass over the columns of `A_1`, `E` and
`P`, which the first time also gives `h`. Generating the columns is most of a
pass, and two candidates take 1.23 passes on average against 1.75 for one.
Candidates are tried in order, the first accepted is used and rejected ones
are never published, so the proof is distributed as with one at a time.

The proof is `(t_A, t_B, z_3, h, c, z_1, z_2)`. The verifier checks the norms
of `z_1` (per block), `z_2`, `z_3`; `ct(h_l) = 0`; recomputes `w`, `τ`, `w_l`
from the openings; and recomputes the hashes, accepting if `c` matches.

## 7. Parameters

Chosen to cover the shuffle up to `N = 1000` messages, estimated with the
lattice-estimator (commit `53da598`, core-SVP); `evmlr_zk_supported` checks
every statement against them, and prover and verifier refuse one they do not
cover.

| | | |
| --- | --- | --- |
| `n` | 512 | as the statement |
| `p` | `2^52 - 395` | the binary claim needs `B_s^2 + sqrt(m n) B_s < p`, `2^49.9` at `N = 1000`; the linear claim needs less |
| `κ` | 4 | MSIS binding at `2 ‖c - c'‖_1 ‖z - z'‖`, with `z - z'` the difference of two accepted openings: 232 bits at `N = 10`, 174 at `N = 1000` (`κ = 3` falls below 128 there) |
| hiding rank | 5 | MLWE over `R_p`, ternary: 133 bits (rank 4: 98; the first version had 2, about 35) |
| `λ` | 4 | aggregation error `p^-4 = 2^-208` |
| `ν'` | 23 | `|C| ≈ 2^130.9`, `‖c‖_1 = 46` |
| widths | `α_b · 46 · B_b` for block `b`, with `α = 23.583` for `s`, `2.5 · 21.485` for `k` and `10 · 21.485` for `s_2`; projections `9 · sqrt(337) · B` at `M = 3.8` | `B_b` the block's public honest bound. One joint rejection test at `M = 1.75` needs `(Σ_b α_b^-2)^-1/2 ≥ 21.485`; three tests at 21.485 each would repeat `1.75^3 = 5.4` times. `k` and `s_2` are a few elements, so widening them costs little in size, and 2.5 for `k` keeps the MSIS bound at `N = 1000` lowest |
| `ZK_BETA_MAX` | `2^43` | the MSIS bound at which `κ = 4` still gives 173 bits; `N = 1000` reaches `2^42.9` |

**The carry bound is statistical.** The widths that hide `k` need a public
bound on an honest carry. The worst case is some 400 times what an honest
carry reaches, and through `σ_k` it would dominate `‖z‖` and cost binding about
nine bits of MSIS bound (`2^51.5` instead of `2^42.6` at `N = 1000`, with
three separate rejection tests, against
`p = 2^52`). Since the bound has to hold only for an honest prover, who refuses
past it, and a cheating prover's carry is bounded by the projection whatever it
says, `shuffle_k_bound` uses `1.25 sqrt(n Σ_r Σ_col ‖E_r,col‖^2) / q`: the
root of the expected squared norm for coefficients of `E` that look uniform
mod `q`, with a margin. The shuffle's test measures an honest carry at 0.52
of it.

| N | MSIS bound | binding | `p` needed |
| --- | --- | --- | --- |
| 10 | `2^38.6` | 232 | `2^43.5` |
| 100 | `2^40.4` | 205 | `2^46.6` |
| 1000 | `2^42.9` | 174 | `2^49.9` |

## 8. Size and speed

**Encoding** (`evmlr_zk_proof_encode`, `_decode`). `t_A`, `t_B`, `t_G` and `h`
take 52 bits a coefficient, with `h`'s constant coefficients left out since
they must be zero; then the 32-byte hash; then `z_3`, `z_1` and `z_2`
Rice-coded per block, with the parameter from the block's public width:
`log2 σ + 2.6` bits a coefficient against an entropy of `log2 σ + 2.05`.
Decoding accepts only canonical encodings, so each proof has exactly one.

Measured on an i7-10510U, one core, CPU time:

| N | ZK⋆ | P, W, u | per message | prove | verify | peak memory |
| --- | --- | --- | --- | --- | --- | --- |
| 10 | 476 KiB | 10 KiB | 48.6 KiB | 0.43 s | 0.13 s | 19 MB |
| 100 | 3658 KiB | 77 KiB | 37.4 KiB | about 3 s | 1.1 s | |
| 1000 | 37683 KiB | 752 KiB | 38.4 KiB | 30–47 s | 10.5 s | 830 MB |

Proving times vary with the number of projection tries. For the same
statement, LaZer's generated parameters give 393 KiB at `N = 10`, and its
prover needs 2.5 GB at `N = 4` and more than 5.7 GB at `N = 10`
(PROOF-SYSTEM.md).

ZK⋆ is about a fifth larger at `N = 10`. The parts are:
- the commitments and `h`, a fixed 53 KiB;
- `z_1`, at `log2 σ_s = 18.7` bits plus coding, most of the rest.

What would shrink it:
- **Operator-norm challenges.** The widths use `‖c v‖ ≤ ‖c‖_1 ‖v‖ = 46 ‖v‖`.
  Keeping only challenges with `max_ζ |c(ζ)| ≤ 24` keeps 93.6% of them
  (`|C|` from `2^130.9` to `2^130.8`) and gives `‖c v‖ ≤ 24 ‖v‖`. That is
  0.94 bits a coefficient, about 4.5%, and a smaller MSIS bound
  (`‖c - c'‖ ≤ 48` against 92).
- **A statistical bound on `‖s‖`.** The honest witness is 43–47% ones, against
  the `sqrt(m n)` the widths assume. A public bound at 52% would save 0.47
  bits a coefficient, about 2.3%, with the honest prover refusing past it as
  for the carry.
- **Entropy coding** in place of Rice: about 0.5 bits a coefficient, 2.5%.

## 9. Milestones

1. `R_p` arithmetic: CRT multiplication mod `p`, `σ`, `ct`, the challenge
   sampler, seeded key expansion. Tests against coefficient-form references.
2. ABDLOP commitment and the linear claim on its own, with rejection sampling:
   completeness, and rejection of a wrong `t`.
3. Lifting with the carry `k`, and the projection: a mod-`q` statement with a
   non-binary witness or an oversized carry is rejected.
4. The binary claim: a witness with a coefficient of 2 or -1 is rejected by
   the binary check and not incidentally.
5. The shuffle: build `E` from Protocol 1's data, replace the current proofs,
   keep the existing shuffle tests passing, and add one per claim.
6. Parameters from the lattice-estimator, sizes and timings against LaZer, and
   a soundness write-up.
