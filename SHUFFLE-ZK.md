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
3. `is_bin(d†_i)`, `is_bin(σ_i)`, `is_bin(w†_i)`;
4. the server's proof of correct decryption (Section 3.3 of the paper,
   section 1.1 below).

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
`E` is built block by block from the protocol's data, never densely. The
decryption (1.1) adds to both.

### 1.1 The proof of correct decryption

The paper has each server prove, besides the shuffle, that it decrypted the
layer it removes:

- knowledge of its key, `A s + e = t`;
- for each message, the decryption of the seed:
  `e'_i = v_i - u_i^T s - ⌈q/2⌋ s̄_i` with `‖e'_i‖_∞ < q/4`;
- the rounding relation (3), `2^{ζ-2η} d_i + r_i = H s̄_i (mod 2^ζ)`, with
  `r_i` in `[-2^{ζ-2η}/2, 2^{ζ-2η}/2)`, on the same `d†_i` the shuffle
  commits in `D`.

The paper reports the size of one "shuffle & decryption proof" per server, so
here these relations join the shuffle's statement, and `d†_i` is the same
witness variable in both. LaZer, which option A′ of `PROOF-SYSTEM.md` had
for this, cannot share `d†_i` with the shuffle. `D` commits every message's
`d†` at once, so a LaZer proof that opens `D` is a single statement over all
`N` messages, and LaZer's prover runs out of memory at about ten messages.

| added | per message | once |
| --- | --- | --- |
| witness, binary | `s̄_i`; 10 bits of `e'_i + 511`; 2 bits of `r_i + 2` at each of the `K_LWE + L` positions | the CBD bits of `s` and `e`, 16 elements |
| rows mod `q` | `u_i^T s + ⌈q/2⌋ s̄_i + (e'_i + 511) = v_i + 511` | `A s + e = t`, `K_LWE` rows |
| rows mod `2^ζ` | `H[p] s̄_i - 4 d_{i,p} - (r_{i,p} + 2) = -2`, `K_LWE + L` of them | |

Ten bits put `e'_i` in `[-511, 512]`, inside the `q/4 = 777` that decryption
needs. An honest `e'_i = r^T e + e_3 - e_2^T s` has a standard deviation of
about 45, so 511 leaves more than 11 of them. The rows are not batched: the
variables they hold are not bound by a commitment before the statement is
fixed, and rows mod `2^ζ` could not be batched anyway, since `Z_{2^ζ}` has zero
divisors. Each row is instead lifted with its own carry, which section 5's
aggregation by columns makes affordable. The server's key and the seed
ciphertexts go into the statement's digest. At `L = 1` the witness grows from
25 to 42 binary elements a message, and the rows from 7 to `9 + 4 N`.

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
gives `2^23 C(255, 23) ≈ 2^130.94` candidates (22 would give `2^126.6`).

Of those, `C` keeps the ones with operator norm `max_ζ |c(ζ)| ≤ 24`, over
the primitive `2n`-th roots of unity `ζ`. The canonical embedding of
`x^n + 1` is a scaled isometry, so `‖c v‖ ≤ 24 ‖v‖`, where `‖c‖_1 = 46` would
give `46 ‖v‖`. `σ(c) = c` makes every `c(ζ) = 2 Σ_i c_i cos(π(2t+1)i/n)`
real. The sampler draws candidates from the hash's stream until one passes,
checking all `n/2` values in integer arithmetic against a cosine table from
an exact integer recurrence, so that prover and verifier agree on every
platform. 93.5% pass, so `|C| ≈ 2^130.85`. Differences of challenges have
`‖·‖_∞ ≤ 2`, invertible in `R_p` by Lemma 1, and operator norm at most 48.

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

**Linear.** `e_r = E_r s - Q_r k_r - t_r = 0` for every row `r`, with `Q_r`
the row's modulus: `q`, or `2^ζ` for the rounding relation (3) of the
decryption proof. For each `l`, with `α_l` uniform in `R_p` and scalars `a_{l,r}`
uniform mod `p`, `ct(σ(α_l) Σ_r a_{l,r} e_r) = <α_l, Σ_r a_{l,r} e_r>`. For a
nonzero `e`, the sum `Σ_r a_{l,r} e_r` is nonzero except with probability
`1/p`, and then its inner product with `α_l` is nonzero except with
probability `1/p`, so the check fails to notice with probability at most
`2/p`. Each column `j` of `E` then enters `h_l` as one aggregated element
`Σ_r a_{l,r} E_{r,j}`, so the number of rows costs scalar work only. (Uniform
`α_{l,r}` for every row would cost `λ` ring products per row and column, and
per-row accumulators, which do not scale to a row per message.)

**Short.** Three Johnson-Lindenstrauss projections, one per block of the
witness: `s`; the carries of Protocol 1's 7 rows (the batched equation and the
openings of `D`, `P` and `W`); and the carries of the decryption's rows. Each
block's bound is certified by its own projection, so that a large bound does
not loosen a small one: `s`'s bound is what the binary claim needs below
`sqrt(p/2)`, and Protocol 1's few large carries would loosen the bound on the
decryption's many small ones. Each has 256 rows with entries `±1` with
probability `1/4` each, streamed per element from a seed hashed after the
commitment, one byte per four rows at one coefficient (so that `Σ_i μ_{l,i} R_i`
is a table lookup per pair of rows). The projection of `s` also covers one
more witness element holding the projections' signs (below).

The projections are bimodal, as in LNP22's Figure 9:
- **Signs.** The prover draws a secret sign `b_i ∈ {±1}` per projection,
  kept as bits `β_i` with `b_i = 1 - 2β_i` in coefficients 0, 1 and 2 of the
  signs' element.
- **Masks.** It commits `b_i y_i` in slot `Y_i` (`y_i` of width
  `γ · sqrt(337) · ‖·‖`, `γ = 2`).
- **Publication.** It publishes `z_3 = b R v + y` for each projection, after
  LNP22's `Rej0` test at `M = exp(1/(2γ^2)) = 1.13`, which makes `z_3`
  exactly Gaussian whatever its width.

`b z_3 = R v + b y` with `z_3` public is linear in `(v, β, b y)`, so it joins
the other aggregated claims, and the binary claim makes `β` bits. That
replaces LNP22's committed sign and its quadratic proof that `b^2 = 1`.

The ratio 2 in place of 9 (the plain rejection sampling used before, at
`M = 3.8`) certifies a bound 4.5 times tighter. As in LNP22, a projection that
fails its test restarts the proof from fresh signs and commitment. The verifier checks
`‖z_3‖ ≤ 1.7 σ sqrt(256)` per half. By LNP22's Lemma 2.9, for `R` with
entries from `Bin_1` drawn after `v` and `y` are committed, and `v` of
dimension `d` with `‖v‖ ≥ b` for some `b ≤ p / (41 d)`,
`‖R v + y mod p‖ ≥ b sqrt(26) / 2` except with probability `2^-128`. So a
verified `z_3` certifies `‖v‖ < 2 ‖z_3‖ / sqrt(26)` (`evmlr_zk_certified`), as
in LNP22's Proposition 5.1, whose `γ`, `sqrt(337)` and `t ≥ 1.64` are the
width ratio (2 here), stretch and tail used here. The lemma rests on LNP22's Lemma 2.8, which
substitutes the normal distribution for `Bin_1` heuristically. Its condition
`41 d B ≤ p` is checked for both projections: `d = (m + 1) n` for `s` with
the signs, and `rows · n` for `k`. At `N = 1000` it needs `p ≥ 2^49.4`, and
`p = 2^52` meets it up to about 3500 messages. The certified bounds rule out
wraparound in the linear claim, `(q/2) sqrt(m n) B_s + q B_k + q/2 < p/2`, and
in the binary claim, `B_s^2 + sqrt((m + 1) n) B_s < p`.
Consistency with the commitment, row by row:
`<R_i, s_1> + (b y)_i - z_{3,i} + 2 β z_{3,i} = 0`, aggregated as
`Σ_i μ_{l,i} (...)`.

**Merged.** For `l = 1..λ`, published:

```
h_l = g_l + ν_l F + σ(α_l) Σ_r a_{l,r} e_r + σ(P_l) · s_1 + σ(M_l) Y - Z_l
```

with `P_l = Σ_i μ_{l,i} R_i` (as ring elements, plus `2 Z_{s,l} + 2 Z_{k,l} x`
in the signs' column, from `2 β z_3`), `M_l = Σ_i μ_{l,i} x^i`,
`Z_l = Σ_i μ_{l,i} z_{3,i}`, and the verifier checks `ct(h_l) = 0`. Each `h_l`
is linear in the committed values, so its consistency is a challenge-free
first message `w_l` recomputed from the openings and hashed, like `τ`. With
`λ = 3` and `p ≈ 2^52`, the aggregation error is `(2/p)^3 = 2^-153`, LNP22's
`λ = ⌈128 / log p⌉`.

## 6. Order of the transcript

1. Hash the statement; derive `ρ` and so `E`, `t`.
2. Draw the signs; commit `t_A` (from `s_1, s_2`) and slots `F`, `g_1..g_λ`.
3. For each projection: commit `b y` in its slot `Y`, hash, derive `R`, and
   publish `z_3 = b R v + y`. If its `Rej0` test fails, go back to 2.
4. Hash with `z_3`; derive `μ`, `ν`, `α`. Compute `h_l`.
5. Sample `y_1, y_2`; commit slot `G`; compute the first messages `w`
   (Ajtai), `τ`, `w_l`. Hash everything into `c`.
6. `z_1 = y_1 + c s_1`, `z_2 = y_2 + c s_2`. One rejection test for all of
   `(z_1, z_2)`, each block scaled by its own width; on rejection go back to 5.

The prover draws two candidates `(y_1, y_2)` at a time and computes their
linear first messages in the same pass over the columns of `A_1`, `E` and
`P`, which the first time also gives `h`. Generating the columns is most of a
pass, and two candidates take 1.37 passes on average against 1.92 for one.
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
| `p` | `2^52 - 395` | the projection lemma needs `41 (m + 1) n B_s ≤ p`, `2^49.4` at `N = 1000`; the binary claim (`2^40.8`) and the linear claim (`2^43.8`) need less |
| `κ` | 5 | MSIS binding at `2 ‖c - c'‖_1 ‖z - z'‖`, with `z - z'` the difference of two accepted openings. It was 4 before the decryption's carries raised the MSIS bound past `2^43` (table below) |
| hiding rank | 5 | MLWE over `R_p`, ternary: 133 bits (rank 4: 98; the first version had 2, about 35) |
| `λ` | 3 | aggregation error `(2/p)^3 = 2^-153` |
| `ν'` | 23 | `|C| ≈ 2^130.85` after the operator-norm test, `max_ζ |c(ζ)| ≤ 24` |
| widths | `α_b · 24 · B_b` for block `b` (`B_s = sqrt(0.52 m n + 3)`, section 7), with `α = 23.583` for `s`, `2.5 · 21.485` for `k` and `10 · 21.485` for `s_2`; projections `2 · sqrt(337) · B`, bimodal at `M = 1.13` | `B_b` the block's public honest bound. One joint rejection test needs `(Σ_b α_b^-2)^-1/2 ≥ 21.485`, at `M = exp(14/21.485 + 1/(2 · 21.485^2)) = 1.92` for statistical distance `2^-128` (LNP22, Lemma 2.14); four tests would repeat `1.92^4` times. A block's part of the MSIS bound is `α_b` times its honest norm times the root of its dimension; the ratios, 24 for `s`, 186 for Protocol 1's carries, 51.5 for the decryption's and 214.85 for `s_2`, keep `s`'s near its minimum, since `s` is most of the proof, and spread the rest to keep the MSIS bound lowest at `N = 1000` with three servers |
| `ZK_BETA_MAX` | `2^49` | the MSIS bound at which `κ = 5` still gives 164 bits (lattice-estimator: 207 at `2^45`, 184 at `2^47`); `N = 1000` reaches `2^43.3` at `L = 1` and `2^44.2` at `L = 7` |

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

**So is the bound on `‖s‖`.** `s` is binary, and the widths assumed every
bit could be one, `‖s‖^2 ≤ m n`. An honest witness is under half ones:
44.8% at `N = 10`, 48.4% at `N = 100`, 48.8% and 49.2% at `N = 100` with
`L = 4` and `10`, rising with `L` as the decryption's `e' + 511` bits, mostly
ones, take a larger share. Over millions of bits the fraction varies by a few
hundredths of a per cent, so the shuffle states `s_weight = 0.52`, the widths
use `sqrt(0.52 m n + 3)`, and the prover refuses a heavier witness, as for the
carry. The same argument covers it: a cheating prover's `s` is bounded by the
projection whatever the statement says. It narrows `σ_s` by `sqrt(0.52)`,
0.47 bits a coefficient, and ZK⋆ by 1.8%. A statement that gives no
`s_weight` keeps the worst case.

With the proof of correct decryption, `κ = 5`. The MSIS bounds are measured
on the statements (`evmlr_zk_msis_bound`), with binding in bits core-SVP from
the lattice-estimator; the `p` needed at `N = 100` and `1000` is extrapolated
from measured statements at `N = 10, 20`, and does not depend on the
challenges:

| N | L | MSIS bound | binding | `p` needed, projection of `s` | Protocol 1's carries | decryption's carries |
| --- | --- | --- | --- | --- | --- | --- |
| 10 | 1 | `2^38.6` | 313 | `2^40.9` | `2^38.2` | `2^39.4` |
| 100 | 1 | `2^40.5` | 275 | `2^45.7` | | |
| 1000 | 1 | `2^43.3` | 230 | `2^50.7` | `2^41.5` | `2^49.3` |
| 1000 | 7 | `2^44.2` | 217 | `2^51.9` | `2^41.9` | `2^50.9` |

With `‖c‖_1` in place of the operator norm, the MSIS bounds were 1.9 bits
higher (`2^45.2` and `2^46.1` at `N = 1000`): the challenge difference goes
from 92 to 48 and the widths from `46 B` to `24 B`.

The `p` needed is the projection lemma's `41 d B`, for each projection. It is
larger than what the linear and binary claims need at every `N` here, and
grows as `N^1.5`, so the projection of `s` is what limits `p = 2^52` to about
1000 messages with three servers. With all the carries in one block, their
projection exceeded `p` from about 790 messages with three servers, and the
MSIS bound was `2^47.7`.

## 8. Security argument

This section maps ZK⋆ onto the results of LNP22 (ePrint 2022/284) that it
instantiates. It argues that each step applies with our parameters and names
what is assumed rather than proven. It is not a new proof.

### 8.1 Knowledge soundness

Take a prover that makes the verifier accept with probability `ε`. Rewinding
it at the challenge `c` (LNP22, Lemma 3.1 and Theorem 4.5) gives two accepting
transcripts with the same first messages and `c ≠ c'`. Subtracting the
verification equations of the Ajtai part gives
`A_1 z̄_1 + A_2 z̄_2 = c̄ t_A` with `c̄ = c - c'`. That is either an MSIS
solution for `[A_1 | A_2]` of norm at most `8 · 24 · B_z` (LNP22's
`B = 8η sqrt(...)`, with `η` the challenges' operator norm, 24 here, which
bounds `‖c̄ z‖ ≤ 48 ‖z‖`), or a relaxed opening
`(s̄_1, s̄_2, c̄)` with `c̄ s̄_i` short, unique, and such that `z_i - c s̄_i` is
the same in every accepting transcript (Lemma 3.1, items 4–5).

- **The MSIS bound** is `evmlr_zk_msis_bound`, which `evmlr_zk_supported`
  keeps under `ZK_BETA_MAX = 2^49`. At `N = 1000` it reaches `2^43.3` at
  `L = 1` and `2^44.2` at `L = 7`, 230 and 217 bits core-SVP (section 7).
- **`c̄` is invertible.** `‖c̄‖_∞ ≤ 2` and `σ(c̄) = c̄`, so `c̄` is invertible
  in `R_p` for `p ≡ 5 mod 8` (LNP22, Lemma 2.6; Lemma 1 of the paper; tested).

With `s̄_1 = (s̄, k̄)` and the BDLOP messages fixed by the opening, the hashed
first messages give, as in LNP22's Theorem 4.5, three properties of
`(s̄, k̄)`. Each holds except with the probability noted.

1. **Every aggregated constant coefficient is zero.** `h_l` has
   `ct(h_l) = 0` and is consistent with the commitment, and the `μ`, `α`, `ν`
   it aggregates with are hashed after `t_A`, `t_B` and `z_3`. So each
   aggregated claim holds, except with probability `(2/p)^λ = 2^-153`. The
   claims are the linear rows, the 512 projection rows and `ct(F)`.
2. **`F` is `Σ_j σ(s̄_j)(s̄_j - 𝟙)`.** The verifier's `τ` is a polynomial of
   degree 2 in `c` (section 5). Agreeing on more than two challenges forces
   its coefficients to agree, so it fails only with probability `2/|C|`, plus
   `p^-n/2` for the ring being a product of two fields.
3. **The projections are honest.** `b_i z_{3,i} ≡ R_i v̄_i + b_i y_i (mod p)`
   for each block `v̄_i` of `(s̄, k̄_1, k̄_2)`, where `b_i y_i` is the opening of
   slot `Y_i`, committed before `R_i` was derived.

LNP22's extractor for this six-round Fiat-Shamir transcript (Theorem B.7, via
[AFK21]) has knowledge error

```
2/|C| + p^-n/2 + (2/p)^λ + 2^-128
```

with `|C| ≈ 2^130.85`, so `2/|C| ≈ 2^-129.85`, and the sum, dominated by
the `2^-128` term, is about `2^-127.65`. It makes `O(Q)` expected oracle queries, so the reduction
loses a factor of the prover's query count `Q`, as in LNP22. Our transcript
hashes in this order:
- the statement and commitment (`h_0`);
- the seed of `R_0`, after slot `Y_0`;
- the seed of `R_i`, after `z_{3,i-1}` and slot `Y_i`, for `i = 1, 2`;
- `μ`, `α`, `ν`, after `z_3`;
- `c`, after `h`, `t_G` and the first messages.

Each challenge is drawn after everything it must not be chosen around.
LNP22's has two rounds fewer, because it projects once.

### 8.2 From the extracted witness to the statement

- **Shortness.** Lemma 2.9 of LNP22, applied to each projection with
  `P = p` and `d = m n` or `rows · n`, gives `‖s̄‖ < B_s` and `‖k̄‖ < B_k`,
  except with probability `2^-128` each. `B = 2 ‖z_3‖_max / sqrt(26)` is
  `evmlr_zk_certified`. The lemma's condition `41 d B ≤ p` is checked in
  `evmlr_zk_supported`. **Assumed:** Lemma 2.9 rests on Lemma 2.8, which
  replaces `Bin_1` by the normal distribution of the same variance
  heuristically, as LNP22 and LaZer do.
- **Binary.** `ct(F) = Σ_i s̄_i (s̄_i - 1) = 0 (mod p)` with
  `|Σ_i s̄_i (s̄_i - 1)| ≤ B_s^2 + sqrt(m n) B_s < p`. So the sum is zero over the
  integers, and since each term is non-negative, every `s̄_i ∈ {0, 1}`
  (LNP22, Lemma 5.2).
- **Linear.** For each row, `E_r s̄ - Q_r k̄_r - t_r ≡ 0 (mod p)` with every
  coefficient below `(Q_r/2) sqrt(m n) B_s + Q_r B_k + Q_r/2 < p/2`, which the
  check for `Q_r = q` covers for `Q_r = 2^ζ` too. So it holds over the
  integers, and `E_r s̄ ≡ t_r (mod Q_r)` (section 2). The shuffle's equations
  (1)–(3) and the openings of `D`, `P` and `W` follow, as `E` and `t` encode
  them (`shuffle_stmt`).
- **Decryption** (section 1.1). The extracted bits give:
  - a key `(s, e)`, CBD by construction, with `A s + e = t`;
  - for each message, a binary seed `s̄_i` with
    `v_i - u_i^T s - ⌈q/2⌋ s̄_i = e'_i` and `e'_i ∈ [-511, 512]`. Since
    `|e'_i| < q/4`, decrypting `c'_i` with `s` gives `s̄_i`;
  - for each position, `d_{i,p} = ⌈H s̄_i⌋` exactly, as the rounding error is
    bits for `[-2, 2)`, and these are the `d†_i` that the shuffle's equations
    use.

  So the server's output is the decryption of its input under the key that
  matches its public key, permuted. Two short keys for the same public key
  would give a short solution to `[A | I] x = 0 (mod q)`. The argument takes
  the key to be the one the server generated, with `t = A s + e`, as LWE does.

### 8.3 Zero knowledge

- **Openings.** The simulator draws `z_1`, `z_2` and `z_3` from their target
  Gaussians.
  - Rejection sampling makes the honest openings statistically close,
    within `2^-128` (LNP22, Lemma 2.14, Rej1). They pass one test at
    `M = 1.92` over four blocks, each scaled by its own width (section 7).
  - Each projection passes Rej0 at `M = 1.13`, which makes `z_3` exactly
    Gaussian (Lemma 2.14, item 3), since its sign is uniform and secret.
    The sign is committed only inside `t_A` and the slots, which hide it.
  - Rejected tries are never published. The prover tries two candidate masks
    per pass and uses the first accepted, so the transcript is distributed as
    with one at a time.
  - The simulator draws `h_l` uniformly with `ct(h_l) = 0`, as LNP22's proof of
    Theorem 4.5 does. That matches the real `h_l`, which the masks `g_l`
    make uniform among such elements.
- **Commitments.** `t_A`, `t_B` and `t_G` are indistinguishable from uniform
  under Extended-MLWE with secrets `s_2` ternary of rank `ZK_HIDE = 5` beyond
  what the commitment rows use. That is LNP22's assumption: the plain MLWE
  instance is estimated at 133 bits, and Extended-MLWE, which also reveals
  `c s_2 + y_2`, is assumed comparably hard, as in [LNS21a].
- **Completeness.**
  - The carry bounds are statistical (section 7). An honest prover whose
    carries exceed them refuses rather than produce a proof that would leak
    them. The shuffle's tests measure the honest carries at about half of
    them.
  - The limit of 80 attempts at the commitment and projections fails an
    honest prover with probability below `2^-128` (`0.313^80 = 2^-134`).

### 8.4 What this does not cover

- **The quantum random oracle model.** Like LNP22's, the analysis is in the
  ROM.
- **Tightness.** The rewinding loses a factor of `Q`. The bit-security figures
  in section 7 are those of the underlying MSIS and MLWE instances, with no
  allowance for that loss.
- **The heuristic projection lemma.** See section 8.2.
- **The rest of the shuffle.** That the statement `E s = t` captures
  Protocol 1's relations (`shuffle_stmt`) is checked by the shuffle's tests,
  including outputs that are not a shuffle being rejected, not by an argument
  here. The encryption and decryption proofs are outside ZK⋆ (option A′ in
  PROOF-SYSTEM.md).

## 9. Size and speed

**Encoding** (`evmlr_zk_proof_encode`, `_decode`). `t_A`, `t_B`, `t_G` and `h`
take 52 bits a coefficient, with `h`'s constant coefficients left out since
they must be zero; then the 32-byte hash; then `z_3`, `z_1` and `z_2`
Rice-coded per block, with the parameter from the block's public width.
Measured on a proof at `N = 10`, `s`'s block takes 19.80 bits a coefficient
against an entropy of `log2(σ sqrt(2 π e)) = log2 σ + 2.05 = 19.71`, and the
carries' blocks 0.15 and 0.17 bits more than theirs: Rice is within a tenth
of a bit of the entropy where most of the proof is, so an entropy coder
would save about 0.5%. (This said `log2 σ + 2.6` and 2.5%, which was not
measured.)
Decoding accepts only canonical encodings, so each proof has exactly one.

Measured on an i7-10510U, one core, in cycles of its 1.8 GHz time-stamp
counter, over 100 proofs: the mean, with the median in brackets, since a
proof restarts whenever a rejection test fails. With the proof of correct
decryption (section 1.1), at `L = 1`, `κ = 5`, `λ = 3`:

| N | ZK⋆ | P, W, u | per message | prove | verify |
| --- | --- | --- | --- | --- | --- |
| 10 | 751 KiB | 10 KiB | 76 KiB | 0.42 s (0.37 s) | 0.12 s |
| 100 | 6423 KiB | 77 KiB | 65 KiB | 3.2 s (2.9 s) | 1.0 s |

The sizes are with operator-norm challenges (section 4) and the bound on
`‖s‖` (section 7), which took 4% and 1.8% off ZK⋆ (from 798 and 6818 KiB);
the times were measured before both, which cost the prover and verifier a
few thousand cycles a challenge and one pass over `s`.

The paper estimates 110 KB a user per server for the shuffle and decryption
proof with LaZer, averaged over four layers (`L` from 1 to 10). The
decryption adds 17 binary elements and 4 carry rows a message at `L = 1`.
Over `L`, at `N = 100`:

| L | `m` | rows | proof | per message | MSIS bound | prove | verify |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | 4264 | 409 | 6500 KiB | 65.0 KiB | `2^40.5` | 4.3 s (3.9 s) | 1.5 s |
| 4 | 6064 | 709 | 9486 KiB | 94.9 KiB | `2^40.9` | 6.2 s (5.8 s) | 2.1 s |
| 7 | 7864 | 1009 | 12480 KiB | 124.8 KiB | `2^41.2` | 10.0 s (9.0 s) | 2.9 s |
| 10 | 9664 | 1309 | 15504 KiB | 155.0 KiB | `2^41.5` | 12.3 s (10.3 s) | 3.9 s |

Taking the four layers as `L = 1, 4, 7, 10`, ZK⋆ averages 110 KiB (112.5 KB) a
message, within 2.3% of the paper's estimate. Each layer adds 600 witness
elements and 100 rows at `N = 100`, about 30 KiB a message. The sizes are with
the bound on `‖s‖`; the times were measured before it. The times are
means of 16 proofs (medians in brackets), taken while another process
loaded the machine: `L = 1` took 4.3 s against the 3.2 s above, so they are
about a third high, but they rise with `L` like the witness does.

The arithmetic behind these numbers (`evmlr_zk.c`): products in `R_p` are
exact over the integers in a negacyclic NTT over four 31-bit primes, eight
residues to an AVX2 vector, and summed in the NTT domain, where `σ` is a
permutation of the slots. Constant columns skip the transform. Every pass
over the witness regenerates `A_1`'s columns, `E`'s aggregated columns and
the projections' from their seeds, so memory stays linear in the witness.
At `N = 100` a pass costs about 160k cycles a column and vector, the
NTT about 10k cycles a transform.

The shuffle alone, before the decryption was added (`κ = 4`, `λ = 4`),
which is the statement the LaZer comparison below is about. These were
measured as CPU time before the arithmetic above, and not re-run:

| N | ZK⋆ | P, W, u | per message | prove | verify | peak memory |
| --- | --- | --- | --- | --- | --- | --- |
| 10 | 477 KiB | 10 KiB | 48.7 KiB | 0.34 s | 0.13 s | 19 MB |
| 100 | 3660 KiB | 77 KiB | 37.4 KiB | 2.7 s | 1.1 s | |
| 1000 | 37684 KiB | 752 KiB | 38.4 KiB | 29–36 s | 9.7–11.5 s | 830 MB |

Proving times vary with the number of rejections. For the same
statement, LaZer's generated parameters give 393 KiB at `N = 10`, and its
prover needs 2.5 GB at `N = 4` and more than 5.7 GB at `N = 10`
(PROOF-SYSTEM.md).

ZK⋆ is about a fifth larger at `N = 10`. The parts are:
- the commitments and `h`, a fixed 53 KiB;
- `z_1`, at `log2 σ_s = 18.7` bits plus coding, most of the rest.

## 10. Milestones

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
