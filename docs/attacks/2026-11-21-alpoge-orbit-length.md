<!-- doc-kind: finding
date: 2026-11-21
Provenance: 3fec7e4
Theorems: `TowerOrderLawQED.v : orbit_length`, `TowerOrderLawQED.v : orbit_longer_than`
-->
# Orbit-length bound in the ℤ₂-tower: the division step, compiled

Closes a review point on `2026-11-20-alpoge-grh-lean-audit.md`, slice 9
(Cursor review at `290d863`). `ord_large_J` proves only the **divisibility
law**. The audit's sentence "every prime `l ≤ x` has orbit length
`≳ x^(1+8ε)`" also needs (a) the division `J ≥ 2^N/(l+1)` and (b) a size for
`2^N`, which the Lean development's `PageN` supplies
(`2^s ≈ x^(2+8ε)`, `…/CharacterBoxes/ExistsPageN.lean`). The audit finding is
merged and immutable, so the correction lives here.

| Rocq theorem | statement | OUTCOME |
|---|---|---|
| `TowerOrderLawQED.v : orbit_length` | For odd `l` with `2 ≤ l ≤ x` and `k ≥ 1` with `l^k ≡ ±1 (mod 2^N)`: `2^N ≤ k·(x+1)` | **QED, zero axioms** (from `ord_large_J`) |
| `TowerOrderLawQED.v : orbit_longer_than` | If moreover `J·(x+1) < 2^N`, then `J < k` | **QED, zero axioms** |

**Reading.**
- The Frobenius order of every odd `l ≤ x` in `(ℤ/2^N)ˣ/±1` is at least
  `2^N/(x+1)`.
- With `PageN`'s `2^(s+2) ≥ 4·x^(2+8ε)`, that is about `x^(1+8ε)`. This is the
  long-orbit statement, now with **only `PageN`'s size** as an explicit
  input.
- The group translation is unchanged: order of `frob` ≤ `J` iff some
  `1 ≤ k ≤ J` has `l^k ≡ ±1`.

**OUTCOME.** **CLOSED, modulo `PageN`.** The division step is now a theorem.
`PageN`'s size choice is an input, as in the Lean development.

**SUMMARY ok 2 / warn 0 / bug 0.**
