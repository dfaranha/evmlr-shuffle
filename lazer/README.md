# LaZer parameters for the user's proof

`evmlr_user_proof.c` proves a ballot's correct layered encryption with
LaZer's linear proof (option A′ in `PROOF-SYSTEM.md`). LaZer's proof
parameters depend on the statement's shape, which depends on the number of
servers `k`, so there is one header per `k`:

| `k` | statement | proof | prove / verify | prover memory |
| --- | --- | --- | --- | --- |
| 2 | 11 × 42 | 68.5 KiB | ~2 s / ~1.5 s | 0.55 GB |
| 3 | 22 × 96 | | | about 2 GB (estimated) |
| 4 | 36 × 168 | | | about 4.5 GB (estimated) |

The `user<k>.py` files describe the statements and are written by
`user_params.py <k>`. The `user<k>.h` headers are generated from them and
checked in, so building needs LaZer's library but not Sage.

## Building

LaZer is the submodule `third_party/lazer`: branch `tbox-fixes` of
[this fork](https://github.com/dfaranha/lazer), which drops an unused matrix
allocation that roughly doubled the prover's peak memory, fixes the toolbox
prover's proofs without the approximate infinity-norm part, and speeds it up.
Fetch it with `git submodule update --init third_party/lazer`; `make` here
builds it, HEXL included, through LaZer's own Makefile, and links its
`liblazer.a`, HEXL and MPFR. `make LAZER_DIR=/path/to/lazer` uses a checkout
elsewhere. Without LaZer, the user proof refuses and its tests are skipped.

LaZer's prover recurses over the binary coefficients. From three servers on,
it overflows a default 8 MB stack, so `evmlr_user_proof.c` runs LaZer on a
thread of its own with a 1 GB stack.

## Regenerating a header

From the top of this repository:

```
cd third_party/lazer/scripts
python3 ../../../lazer/user_params.py 3
sage lin-codegen.sage user3.py > user3.h
```

`lin-codegen.sage` needs one change. The statement holds mod `64 q`: rows mod
`q` are scaled by 64, and the rounding rows mod `2^ζ = 64` are scaled by `q`.
The script takes the centred bound on the statement's coefficients to be
`P = (mod-1)/2`, which is not an integer for an even modulus. The bound it
means is `floor(mod/2)`, which is the same for odd moduli:

```
-P = (mod-1)/2
+P = floor(mod/2)
```

The headers here were generated that way, from LaZer commit `415967c`.
