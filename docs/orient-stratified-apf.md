<!-- doc-kind: guide -->
# Stratified Adaptive Precision Filter (APF) for orient2d

*Companion to `theories-flocq/OrientStratifiedAPF.v`.*

This note describes the stratified adaptive-precision orientation filter, the
three proof tracks it delivers (X / Y / Z), and the extraction + benchmark
protocol against NetTopologySuite that track Z targets.

## 1. What it is

`orient2d(P0, P1, Q)` — the sign of the 2×2 cross-product determinant

```
det = (P1.x - P0.x)(Q.y - P0.y) - (Q.x - P0.x)(P1.y - P0.y)
```

— is the primitive on which almost every robust-geometry decision in JTS /
NetTopologySuite rests (`RobustDeterminant.SignOfDet2x2`,
`Algorithm.Orientation.Index`, and everything that consumes them: RelateNG's
edge-side tests, noding, convex-hull, `IsCCW`). A rounded binary64 evaluation
is fast but can return the wrong sign near collinearity; an exact evaluation is
always right but slow.

The **stratified APF** is the standard adaptive answer, expressed as two strata:

| Stratum | Function | Cost | Guarantee |
|---|---|---|---|
| **A** — ulp-bounded fast filter | `b64_orient_sign_filtered` | one rounded det + Shewchuk Stage-A error bound `(3 + 16·eps)·eps` | commits to Pos/Neg/Zero only when `|det|` strictly clears the bound; otherwise declines (`Uncertain`/`Nan`) |
| **D** — certified expansion switch | `b64_orient2d_expansion_sign` | Shewchuk fast-expansion-sum determinant | exact sign; fires **only** when Stratum A declines |

The composed decoder is `b64_orient_apf = b64_orient_sign_stage_d` (filter
first, exact fallback on decline). This file's value is not the composition
(that already ships in `Orient_b64_stage_d.v`) but the three tracks below.

## 2. Track X — filter + switch lemmas

The shipped `b64_orient_sign_stage_d_sound` (`Orient_b64_stage_d.v`) is stated
**under** the hypothesis `fast_expansion_sum_strong_nonoverlap_headline` — the
general Shewchuk Theorem-13 property, which is *false as stated* and therefore
carried as an explicit assumption there (never `Admitted`, but present).

`OrientStratifiedAPF.v` re-derives soundness of the **same** decoder in the
integer regime with that hypothesis **discharged**, by routing the exact
fallback through the unconditional `b64_orient2d_expansion_int_sign_correct_coords`
(`Orient_b64_int_safe_coords.v`) instead of the headline-dependent
`b64_orient2d_expansion_sign_correct`.

| Lemma | Statement |
|---|---|
| `b64_orient_apf_fast_path` | when Stratum A commits, the switch is not consulted; decoder = filter verdict |
| `b64_orient_apf_decisive` | **unconditional**: the decoder always returns Pos/Neg/Zero (never Nan/Uncertain) |
| `b64_orient_apf_never_nan` / `_never_uncertain` | corollaries |
| `b64_orient_sign_exact_sound_int` | Stratum D sound vs `cross_R_BP` under `int_safe ∧ expansion_safe`, **no headline** |
| `b64_orient_apf_sound_int` | **headline**: whole decoder sound vs `cross_R_BP` under `int_safe ∧ expansion_safe`, **no headline** |
| `b64_orient_apf_decides_int` | sharp form: each verdict ⇔ the matching sign of `cross_R_BP` |

`b64_orient_apf_decisive` is the hypothesis-free strengthening of the shipped
stack's *conditional* `tiny_regime_decisive`: because the exact fallback always
commits, the two indefinite verdicts are structurally unreachable.

## 3. Track Y — the witness algebra

A provenance-carrying certificate records which stratum decided each call and
supports an algebra whose involution is the geometric orientation flip.

- `apf_witness` = `AWFilter s | AWExpansion e` — the deciding stratum plus its
  raw verdict; `apf_stratum_of` is the coarse tag (`APF_FilterA` / `APF_ExpansionD`).
- `apf_run` produces the certificate; `apf_decode` recovers the verdict.
- `apf_decode_run` : `apf_decode (apf_run …) = b64_orient_apf …` (coherence).
- `apf_stratum_filter_iff_committed` / `apf_stratum_switch_iff_indefinite` :
  decidable provenance — Stratum A is the decider **exactly** when the filter
  committed; the switch fires **exactly** on `Uncertain`/`Nan`.
- `apf_run_sound_int` : the decoded certificate meets the exact spec.

The algebra:

- `sign_robust_neg`, `expansion_sign_neg`, `apf_witness_neg` — sign involutions
  (`*_involutive` laws), with `apf_stratum_of_neg` (negation preserves provenance).
- `apf_decode_neg` : `apf_decode` is a **homomorphism** — it intertwines the
  witness-level and verdict-level negations.
- `cross_R_BP_swap01` : `cross_R_BP P1 P0 Q = − cross_R_BP P0 P1 Q` (a `ring`
  identity — the exact spec is antisymmetric).
- `b64_orient_apf_antisym_int` : the payoff — swapping the first two arguments
  negates the decoded verdict, realising the witness-algebra involution as the
  geometric orientation flip (under `int_safe` and `expansion_safe` for both
  orderings; `orient2d_inputs_int_safe_swap01` supplies the swapped int-safety).

## 4. Track Z — extraction + NTS benchmark

### 4.1 What already extracts

Stratum A (`b64_orient_sign_filtered`) is **already** extracted to native
binary64 in the shipped oracle: `Validate_binary64_extract.v` overrides
`Binary.Bplus/Bminus/Bmult/Bcompare/Babs` with native `+. -. *. compare
abs_float` and the Stage-A constants (`b64_three/sixteen/eps`) with float
literals, emitting `oracle/extracted.ml`. So the fast path of the APF is
benchmark-ready today.

### 4.2 What the exact-fallback native harness needs

`b64_orient2d_expansion_sign` bottoms out in `sign_of_expansion`
(`B64_Expansion.v`), whose Coq body inspects `Rcompare (B2R x) 0`. That is a
*mathematical* definition, not a computation: extracting it drags in Flocq's
entire real-number model (`f2R`, `bpow`, `RbaseSymbolsImpl.coq_R`), which does
not run. This is exactly why the shipped oracle extracts only the leaf
expansion primitives (`b64_TwoSum`, `b64_grow_expansion_aux`).

The one required override — semantics-preserving, mirroring the existing
`b64_snap_coord` override — is a native head-first component scan (the
expansion is stored most-significant-first, so the sign is that of the first
nonzero component):

```coq
Extract Constant B64_Expansion.sign_of_expansion =>
  "(let rec go = function
      | [] -> ExpZero
      | x :: xs -> if x < 0.0 then ExpNeg else if x > 0.0 then ExpPos else go xs
    in go)".
```

With that in place, `b64_orient_apf` / `apf_run` (pure binary64 recursion over
the filter and the native-float expansion) extract into an `apf` module
alongside the existing oracle functions. `apf_run`'s `apf_stratum_of` result is
what the harness reads to measure the Stratum-A hit rate.

### 4.3 Benchmark protocol against NetTopologySuite

Reference implementation: `NetTopologySuite.Algorithm`
- `RobustDeterminant.SignOfDet2x2(x1,y1,x2,y2)` and
- `Orientation.Index(p1, p2, q)` (which calls the CGAL-style
  `CGAlgorithmsDD` DD filter).

Protocol (driven through `oracle/driver.ml`, `ORIENT` mode):

1. **Agreement (correctness).** For each triple, compare the APF verdict with
   NTS `Orientation.Index`. On the integer regime the APF verdict is
   *proved* equal to the exact sign (`b64_orient_apf_decides_int`), so any
   disagreement localises a bug in the reference DD filter, not the APF.
2. **Stratum-A hit rate (the APF payoff).** Read `apf_stratum_of (apf_run …)`;
   report the fraction decided by Stratum A alone. Sample families:
   - *bulk random* doubles (filter should decide ≈100%);
   - *near-collinear* triples generated by perturbing a point on the line
     `P0P1` by `k·ulp` for `k = 0,1,2,…` (the hit rate should climb from 0 to 1
     as `k` grows past the Stage-A bound);
   - *exactly collinear* integer triples (Stratum A returns `Zero` directly).
3. **Throughput.** Wall-clock the APF vs. NTS `Orientation.Index` on the bulk
   family; the APF should track the plain rounded det on the fast path and pay
   the expansion cost only on the near-collinear tail.

The correctness guarantee for the fast path in the integer regime is the
machine-checked `b64_orient_apf_sound_int` / `b64_orient_apf_decides_int`; the
benchmark measures *cost*, not correctness.

## 5. Assumption footprint

All 20 lemmas/theorems are `Qed`-closed with no `Admitted` / `Axiom` /
`Parameter`. The file inherits `Classical_Prop.classic` transitively through
the shared binary-op lineage (`B64_bridge` `Bplus/Bminus/Bmult`) under the
`Orient_b64_*` / expansion stack it composes, together with the standard
classical-reals trio and functional extensionality — the same footprint as the
rest of that stack, recorded in `docs/audit-exceptions.txt`. It introduces no
axioms of its own.
