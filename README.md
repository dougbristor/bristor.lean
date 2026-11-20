# bristor.lean

The Bristorian product of rank 3 (B3), checked in [Lean 4](https://lean-lang.org/).

Bristorian algebra is Doug Bristor's number system behind the [Bristorbrot](https://bristorbrot.org). Its numbers are **imordials**
(imaginary + ordinal: ranked imaginary units). It is not the quaternions: the units share the letters i, j, k and nothing else.
The whole multiplication is one line:

```
e_a · e_b = sgn(b − a) · e_b   (a ≠ b)        e_a · e_a = −1        1 is the identity
```

so `i·j = +j` and `j·i = −i`. The right-hand unit always survives; its sign records which rank came first.

**The rule is a choice; what follows from it is not.** This repository checks the second part.

## What is proved

For B3 = 1 + three imaginary units (i, j, k), over any commutative ring:

| theorem | statement |
|---|---|
| `table` | the product on all 16 unit pairs is the one-line rule |
| `mul_add_left/right`, `mul_smul_left/right` | the product is bilinear, so with `table` it **is** the rule's product, not a formula that happens to agree |
| `commutator` | `x·y − y·x = Σ_{p<q} (x_p y_q − x_q y_p)(e_p + e_q)`, real part 0; for units, `[e_p, e_q] = e_p + e_q` |
| `square_closed` | `z·z = (z0² − Σ z_a², z_b·(2·z0 + Σ_{a<b} z_a − Σ_{a>b} z_a))` |
| `jroll_is_reversal` | the other sign convention (the "j-roll", `i·j = −j`) is this product with the rank order reversed: one algebra, relabelled |

And by computed example: not associative (`(i·j)·i = −i`, `i·(j·i) = +1`), not alternative (associator `(i,i,j) = −2j`), sizes do not
multiply (`|(1+i)(1+j)|² = 6`, `|1+i|²·|1+j|² = 4`), and `i·j ≠ k`.

## Does the check bite?

`check.sh` passes only if all three hold:

1. `Bristor.lean` checks with no `sorry`, using only Lean's standard axioms (`propext`, `Quot.sound`, `Classical.choice`).
2. The Lean product reproduces all 19 B3 cases (12 products, 7 squares) in `vectors/vectors.json`: the exact test vectors every
   implementation of the product answers to. They were computed from the one-line rule alone. This is a copy of
   [bristorbrot](https://github.com/dougbristor/bristorbrot)'s `core/bristor_product/vectors.json` (v1, frozen); both have
   md5 `5c55af657c1cfdd019600084a7ab8ead`.
3. Every false claim in `plants/` fails, inside the plant: associativity, `|xy| = |x||y|`, the other convention's commutator sign,
   `i·j = k`, the two conventions equal without the reversal, a `sorry`, and the product matching the vectors' j-roll column.

```
ok   13 theorems; axioms used: Classical.choice propext Quot.sound
ok   vectors: 19 B3 cases match canon
plants fired 7/7
PASS
```

## Run it

Core Lean only: no Mathlib and no Lake project. The built-in `grind` tactic's ring solver proves the identities.

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh    # Lean's installer; the toolchain is pinned in lean-toolchain
./check.sh                                                 # about 6 seconds; needs python3
```

## Where the vectors come from

`vectors/vectors.json` is byte-for-byte the file shipped as `core/bristor_product/vectors.json` (v1, frozen) in
[dougbristor/bristorbrot](https://github.com/dougbristor/bristorbrot): sha256 `83be4ccef07176a43eafcade2fafb5ff44e9bb24f0841af552d2353698822d23`. The two copies are kept on purpose, so this
repository stands alone; compare the hashes to confirm they still agree.

## What it does not show

Lean checks the statement it is given. It says nothing about pictures, fields or statistics, and it cannot tell whether a question
was the right one to ask. This covers B3 only. The rule extends to any number of units, which is not yet formalised here.

## Licence

MIT for the code (`LICENSE`); `vectors/vectors.json` is CC0 1.0, because test vectors are data anyone may drop into their own test
suite. Attribution requested, not required. Which file is under which licence is stated in `REUSE.toml` ([REUSE](https://reuse.software)
convention), and both full texts are in `LICENSES/`. © 2026 Doug Bristor, bristorbrot.org.
