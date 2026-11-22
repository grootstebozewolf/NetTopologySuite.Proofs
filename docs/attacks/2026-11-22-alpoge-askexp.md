<!-- doc-kind: finding
date: 2026-11-22
Provenance: 0c81eb62
Theorems: `AlpogeAskExp.v : cutoff_uniform`, `AlpogeAskExp.v : cutoff_needs_hN`, `AlpogeAskExp.v : ramified_weights_zero`, `AlpogeAskExp.v : askExp_split_r`, `AlpogeAskExp.v : hA_swap`, `AlpogeSkeleton.v : counts`
-->
# Alpöge main line: askExp refined, cutoff checked for a NACK

Requested: `CharacterBalance.askExp`, and a NACK hunt on its critical step.
#1046 left `askExp` (`ChBalance.lean`, the lemma above `ch_balance`) as an
inventory hypothesis of `ch_balance_r`. This finding replays it.

The work is in `docs/h1-vacuity/AlpogeAskExp.v`. It is within the
three-axiom allowlist, with no `Admitted`.

External subject: mirror `CocoSgt/riemann-hypothesis-lean` @ `7cbf7a0`, read
from source; nothing was built. This does not verify RH. The verdict on the
external development is unchanged: **PASS-STATIC / PENDING**.

## NACK hunt

The step that could have hidden a Masullo-style gap is `max(a/n − w, 0) = 0`
for `n > N`, used by `ramifiedPrimeTerm_eq_zero` and by the support
obligation of `sum_vonMangoldt_primePow`.

`cutoff_uniform` proves it from `0 < w` and `a/w ≤ INR N` alone:
`a/n = (a/w)·(w/n) ≤ N·(w/n) < w`. The bound does not depend on the group
element, on `t`, or on a scale `x`. `N` is the parameter of `ASK` itself,
not a constant pulled out of a tail.

`cutoff_needs_hN` is a control, not a NACK. With `a = 3`, `w = 1`, `N = 1`,
`n = 2`, `a/w = 3 ≰ 1` and `max(3/2 − 1, 0) = 1/2`. Dropping `hN` makes the
support step false. The Lean proof assumes `hN`.

The prime case split was replayed. `p = D.d` is not inert (the last field of
`IsInert` is `p ≠ D.d`). `p ∈ S0` contributes 0 and is not inert. An
unramified prime that is not inert has `askP p = 0` by `inPhi_nsmul`. No
step is circular: `askExp` does not call `ch_balance`.

**No candidate NACK.**

## What is rebuilt

| Lean | Rocq | proved here |
|---|---|---|
| cutoff `max_zero_of_gt` | `cutoff_uniform` | The inequality, with no hypothesis. |
| `D.d ≤ D.d^i` | `nat_pow_ge_base`, `ramified_base_exceeds` | For `i ≥ 1`. |
| `ramifiedPrimeTerm_eq_zero` | `ramified_weights_zero`, `askD_zero_of_lt` | The sum of cut-off weights is 0. `unfold askD` is a named reading. |
| `hC` and the sum over `P` | `primeSum_eq`, `askExp_split_r` | The three cases, then the sum. |
| the three-sum swap in `hA` | `hA_swap` | `ksum_swap` twice. |

## QEX (named hypotheses, statements not weakened)

- `ld`, `lsplit`, `lunram` (the character-sum evaluations `ounram` / `cardI` sit inside them).
- `askP p = 0` from `inPhi (frob p)` and `inPhi_nsmul`.
- The reading of `unfold askD` as a sum of `max(a/D.d^i − w, 0)`.
- `sum_vonMangoldt_primePow` as an identity of prime powers. Its support obligation is the proved cutoff; the identity itself is not opened.
- The ring step that names `Kc * Fc` is not separated from `hA_swap`: the swaps are proved for an arbitrary summand.

## Ledger

`AlpogeSkeleton.v` cites the refinement on the `ch_balance` row and `Check`s the theorems. Counts unchanged: 53/53 refined, 46 proved over R. `askExp` is a sub-lemma of `ch_balance`, not a new row.

## Ranking the twelve QEX calls from #1049

Readings of the Lean sources named in `docs/attacks/2026-11-22-alpoge-topshape.md`. Not proofs, and not NACK verdicts. Ordered by how much a uniformity or quantifier-order gap could hide.

1. **`theoremS_transport_link_zero`.** Counting constants `c30` (`n0`, `A`, `C`) are applied across a whole family. A constant that is really per-`x` would be a Masullo gap. Highest risk; the body was not opened.
2. **`sizesRec_at`.** Many `x^(…ε)` comparisons. The proof that was read uses `x ≥ 4` and `ε < 1/52` pointwise, so a single `C` pulled outside `x` is the thing to watch.
3. **`bRest_all`.** The whole of `LinkBrest.lean`. Row bounds can hide a uniform length. Opaque, so the risk is the opacity.
4. **`divinN_of_hypV`.** `LinkN` supplies one `C` and then a tail `x ≥ x3`. The order is the safe one if `C` does not depend on `x`. Worth checking the `obtain`.
5. **`rank_zero_of_row_conditions`.** Level-projection surjectivity is `∃ xr`, then `x ≥ xr`. Risk is an `xr` that was treated as uniform in the family.
6. **`linkIRR_of_join_ex`.** The threshold `max(x0, (3/2)^(1/ez))` is per family. Lower risk if that `∃ x0` is kept inside the family.
7. **`dGamSize_of_dvd`.** The factor 12 comes from `log 2 ≤ log(f·N)` and is absolute in the calc that was read. Lower risk than the counting-constant lemmas.
8. **`muRank`.** `ChosenE → NuFull ∧ MuRank` at a fixed level. Less obviously `x`-dependent.
9. **`link8`.** `LinkGLOBAL` at the fixed parameters `(2, 3, 2, 0)`. Same remark.
10. **`linkMu_of_linkDIV`.** Packaging of already-built links. Algebraic if the Lean term is only the application seen in `DesWin.lean`.
11. **`muTu_of_tuSize`.** One direction from `TuSize`. Thin.
12. **`muDGam_of_fact`.** One direction from `DGamSize`. Thin.

## OUTCOME

**QED (refined)** for the cutoff, the power comparison, the weight sum, the prime case split, and the sum swap. **No candidate NACK.** **QEX** for the inventory calls above. The Alpöge verdict is unchanged: **PASS-STATIC / PENDING**.

**SUMMARY ok 6 / warn 0 / bug 0.**
