# Phase 0 completion: robust orientation predicate

**Status.** Written 2026-05-25 retroactively.  Phase 0's deliverable —
a Qed-closed `b64_orient_sign_filtered` with integer-regime soundness
and a bit-equal C# port — landed on main around 2026-05-15 and was
the foundation Phase 1 built on top of (Phase 1's first slice
`Intersect_b64.v` calls `b64_orient_sign_filtered` four times in its
five-valued dispatch).  No completion doc was written at the time;
this artifact closes the documentation gap so the
Phase 0 → Phase 1 → Phase 2 retro chain is intact before Phase 2
opens.

The discipline observed for Slice A
([`docs/slice-a-retro.md`](slice-a-retro.md)), Stage D
([`docs/stage-d-retro.md`](stage-d-retro.md)), and Phase 1
([`docs/phase1-completion.md`](phase1-completion.md)) is mirrored
here.  Same structure: current state, what stays open, why this is
"Phase 0 complete," future paths.

## Current state (2026-05-15, completion point)

**Shipped, Qed-closed.**

R-side foundation ([`theories/Orientation.v`](../theories/Orientation.v),
[`theories/Distance.v`](../theories/Distance.v),
[`theories/Vec.v`](../theories/Vec.v)):

- `cross` / `dot` / `orient2d` over `R` — the predicate-layer
  reference under exact real arithmetic.
- Antisymmetry, cyclic permutation, translation invariance —
  arithmetic identities that the binary64 predicate must respect
  (vacuously in the integer regime; via Stage A's filter elsewhere).
- All three vertex degeneracies (`P0 = P1`, `P0 = Q`, `P1 = Q`)
  forcing `cross = 0`.

Binary64 layer ([`theories-flocq/Orientation_b64.v`](../theories-flocq/Orientation_b64.v)):

- `b64_orient2d` — naive determinant evaluation on `binary64` via
  `b64_minus` / `b64_mult` from `Validate_binary64.v`.
- `b64_orient_sign_naive` — four-valued sign decoder (`OrientPos` /
  `OrientNeg` / `OrientZero` / `OrientNan`) over `b64_orient2d`'s
  output.
- **Stage A filter** —
  `b64_errbound_A_coeff = (3 + 16·eps)·eps`,
  `b64_orient2d_detsum`,
  `b64_orient2d_errbound`,
  five-valued `Inductive orient_sign_robust` (adding
  `OrientRUncertain`),
  `b64_orient_sign_filtered` (the Stage A decoder).
- Structural lemmas: decidability of equality, totality,
  five-constructor pairwise distinctness, NaN-iff-`b64_compare`-`None`.

R-bridge + integer-regime soundness
([`theories-flocq/Orient_b64_R.v`](../theories-flocq/Orient_b64_R.v),
[`theories-flocq/Orient_b64_sound.v`](../theories-flocq/Orient_b64_sound.v),
[`theories-flocq/Orient_b64_exact.v`](../theories-flocq/Orient_b64_exact.v)):

- `b64_orient2d_safe` — no-overflow premise discharged for inputs in
  the integer regime (`|coord| ≤ 2^25`, integer-valued).
- `b64_orient_sign_filtered_consistent_with_b64` — the filter's
  five-valued output is consistent with `b64_orient2d`'s rounded
  determinant.
- `b64_orient2d_exact_for_small_int` — bit-exact integer cross_R
  under the integer regime: `B2R (b64_orient2d P0 P1 Q) = cross_R_BP
  P0 P1 Q`.
- **`b64_orient_sign_filtered_sound_small_int`** — HEADLINE.
  Match-on-five soundness in the integer regime:

```coq
Theorem b64_orient_sign_filtered_sound_small_int :
  forall P0 P1 Q : BPoint,
    orient2d_inputs_int_safe P0 P1 Q ->
    match b64_orient_sign_filtered P0 P1 Q with
    | OrientRPos       => 0 < cross_R_BP P0 P1 Q
    | OrientRNeg       => cross_R_BP P0 P1 Q < 0
    | OrientRZero      => cross_R_BP P0 P1 Q = 0
    | OrientRNan       => True
    | OrientRUncertain => True
    end.
```

- Antisymmetry, all three vertex degeneracies, both cyclic
  permutations — Qed-closed in the integer regime via the same
  exactness lift.

Shewchuk expansion arithmetic
([`theories-flocq/B64_Expansion.v`](../theories-flocq/B64_Expansion.v),
[`theories-flocq/B64_FastExpansionSum.v`](../theories-flocq/B64_FastExpansionSum.v),
[`theories-flocq/B64_FastExpansionSum_Shewchuk.v`](../theories-flocq/B64_FastExpansionSum_Shewchuk.v),
[`theories-flocq/Orient_b64_expansion.v`](../theories-flocq/Orient_b64_expansion.v)):

- TwoSum / Dekker building blocks (no-overlap, sign-preservation).
- `fast_expansion_sum` over binary64 lists with nonoverlap invariant
  preservation (Shewchuk Theorem 13).
- `orient2d` via fast-expansion-sum — the expansion-based decoder
  feeding Stage D.
- Slice A documented separately in [`docs/slice-a-retro.md`](slice-a-retro.md);
  the 17-session Slice A engagement closed Shewchuk's
  `fast_expansion_sum_nonoverlap` in
  [`B64_FastExpansionSum_Shewchuk.v`](../theories-flocq/B64_FastExpansionSum_Shewchuk.v).

Stage D decoder
([`theories-flocq/Orient_b64_stage_d.v`](../theories-flocq/Orient_b64_stage_d.v)):

- `b64_orient_sign_exact` — expansion-based decoder with
  `orient_sign_robust` output.
- `b64_orient_sign_stage_d` — Stage A → expansion fallback dispatch.
- `b64_orient_sign_stage_d_tiny_regime_decisive` — in the tiny
  regime (`|coord| ≤ 2^25` integer), Stage D never returns
  `Uncertain`.

C# consumer ([`NetTopologySuite.Curve`](https://github.com/NetTopologySuite/NetTopologySuite.Curve)):

- `Robust.Orientation.RobustOrientation` — `Orient2d` (raw
  determinant), `Sign` (4-valued, naive), `SignFiltered` (5-valued
  `OrientSignRobust`) — bit-exact against RocqRefRunner `ORIENT` /
  `ORIENT_FILTERED` modes.
- Differential corpus: deterministic fixtures + random fuzz + NaN /
  huge-magnitude / integer-regime adversarial families, all
  bit-equal between C# `double` and OCaml-extracted Coq.

## Open

Two pieces remain, both parallel to deferrals carried into Phase 1's
own completion doc:

### Stages B / C / D expansion refinement for general bounded-magnitude inputs

The integer-regime soundness covers `|coord| ≤ 2^25` integer-valued
inputs.  Outside that regime, Stage A may legitimately return
`OrientRUncertain` for ill-conditioned configurations, and the
expansion fallback (Stage D) is what would commit a sign decisively.
The fallback is in place
([`Orient_b64_stage_d.v`](../theories-flocq/Orient_b64_stage_d.v)),
but its cross_R soundness on the general bounded-magnitude regime —
the conjunction of Stages B (renormalization), C (sign-of-expansion
extraction), and D (chain composition) — is documented as open in
[`docs/soundness-strategy.md`](soundness-strategy.md) and
[`docs/stage-d-feasibility.md`](stage-d-feasibility.md).

The work is qualitatively harder than what shipped: the integer
regime achieves complete-soundness via exactness (rounding errors
structurally vanish), whereas the general regime needs the actual
Shewchuk forward-error chain (Stage A coefficient + Stages B/C
intermediate bounds + Stage D renormalization).
[`docs/soundness-strategy.md`](soundness-strategy.md)'s
consolidation discussion concludes there is no middle ground
between "the integer regime as shipped" and "full Stages B/C/D" that
buys meaningful intermediate value.

### `OrientRUncertain` semantics

The predicate returns `OrientRUncertain` when Stage A's filter
declines to commit a sign — the determinant's sign cannot be
guaranteed from the rounded-arithmetic bound alone.  The soundness
theorem's `OrientRUncertain` branch is `True` by design: the
predicate honestly declines to commit.

This is exactly the shape Phase 1's `IntersectCollinear` and
Scope C.2-tight's K-condition-number-dependence inherit.  Phase 1's
completion doc records the parallel
([`docs/phase1-completion.md`](phase1-completion.md), section
"`IntersectCollinear` sub-cases").

## Why this is "Phase 0 complete"

Phase 0's chokepoint deliverable is a **verified orientation
predicate**: decide whether three coordinates are oriented
positively, negatively, or degenerately, with honest reporting of
NaN / Uncertain inputs.  That deliverable shipped end-to-end:

- **Coq-side**: integer-regime cross_R soundness for the headline
  `b64_orient_sign_filtered_sound_small_int`, plus the R-side
  identities (antisymmetry, cyclic permutations, vertex
  degeneracies) that downstream callers compose with.
- **C#-side**: `Robust.Orientation.RobustOrientation` ported with
  three call shapes; bit-equal against RocqRefRunner across the
  differential corpus.

What's open — general bounded-magnitude soundness via Stages B/C/D —
is parallel to Phase 1's open Stage D in the same way Phase 1's
deferrals parallel Phase 0's: substantial separate engagements, not
chokepoint work.  Mirroring
[`docs/soundness-strategy.md`](soundness-strategy.md)'s consolidation
discussion: the integer regime *is* the scoped-down complete-soundness
an abbreviated Stages B/C/D would otherwise have to deliver.

## Future paths

In rough order of payoff vs. cost:

1. **Full Stages B/C/D expansion-arithmetic chain composition** —
   large slice, the natural follow-up to Slice A's
   `fast_expansion_sum_nonoverlap`.  Reading-unblocked: Shewchuk
   1997 + 1999, Jeannerod–Rump 2014.  See
   [`docs/audit-shewchuk-stages.md`](audit-shewchuk-stages.md) and
   [`docs/stage-d-chain-composition-approach.md`](stage-d-chain-composition-approach.md)
   for the inventory and approach.
2. **General bounded-magnitude cross_R soundness for
   `b64_orient_sign_filtered`** — composes (1) with the existing
   integer-regime exactness path.  Unlocks the general-regime
   headline parallel to
   `b64_orient_sign_filtered_sound_small_int`.
3. **Phase 2 onward** — snap rounding noder (Hobby 1999 +
   Halperin-Packer 2002), planar overlay, etc.  See the
   Phase 0–7 chokepoint table in
   [`README.md`](../README.md).  Phase 2 builds on Phase 0's
   predicate (overlay needs robust orientation) but does NOT
   depend on closing (1) or (2) — Phase 2 can land using the
   integer-regime soundness alone, just as Phase 1 did.

## Audit summary

- **No `Admitted`, `Axiom`, `Parameter`** anywhere in
  `theories/` or `theories-flocq/` reachable from Phase 0's
  proof obligations.  Same four-axiom corpus baseline carried
  forward to Phase 1 and Scope C.2-tight.
- **No `Admitted` placeholder for the deferred pieces.**  Stages
  B/C/D refinement is *absent* from the corpus, not stubbed.
- **No silent narrowing of contracts.**  `OrientRUncertain` is
  `True` in the soundness theorem, mirroring the same treatment
  Phase 1 gives `IntersectCollinear` and `IntersectUncertain`.

## Why this doc lands now

Phase 0 worked.  The work shipped to the corpus, the C# port went
live, and Phase 1 composed on top of it without friction.  The
missed ceremony was a `docs/phase0-completion.md` to mirror the
ones written for Slice A, Stage D, and Phase 1.  This doc closes
that gap before Phase 2 opens, so the retrospective chain
(Phase 0 → Phase 1 → Phase 1 Scope C.2-tight → Phase 2) reads
linearly when future contributors trace the history.

---

**AI assistance disclosure:** AI-drafted, human-reviewed.
  Assisted-by: Claude
