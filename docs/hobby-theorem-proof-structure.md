# Hobby Theorem 4.1 — proof structure

> **Status (Phase 2, this session).** Section 4 definitions land, two
> supporting lemmas Admitted with registered deferred-proof entries,
> the conditional theorem Qed-closed.  Mirrors the
> `docs/shewchuk-theorem-13-proof-structure.md` treatment for Shewchuk
> Theorem 13: a single document captures what the corpus has, what the
> precise gap is, and what a future contributor needs to resume the work.
>
> The conditional theorem's exact Coq form:
>
> ```coq
> Theorem hobby_theorem_4_1_conditional :
>   forall (A : list (Point * Point)),
>     fully_intersected A ->
>     (forall s1 s2 : Point * Point,
>        segments_intersect_only_at_endpoints s1 s2 ->
>        forall sigma1 sigma2 : Point * Point,
>          In sigma1 (snap_round_segments [s1]) ->
>          In sigma2 (snap_round_segments [s2]) ->
>          sigma1 <> sigma2 ->
>          segments_intersect_only_at_endpoints sigma1 sigma2) ->
>     fully_intersected (snap_round_segments A).
> ```
>
> File: `theories-flocq/HobbyTheorem_b64.v` (in the Flocq layer because
> `snap_round_segments` consumes Flocq-pinned `snap_round`; this is the
> same placement constraint as Slices 11-13).
>
> **Provenance.** The paper-specific numbering ("Theorem 4.1 / Lemma 4.2 /
> Lemma 4.3"), the page reference to the R⁻ convention (p.210-211), and the
> proof sketches are taken from the user's verification of Hobby 1999
> against the paper.  No author of this document has been able to read the
> PDF (every reachable host returned 403); the Coq statements are correct
> mathematically regardless of paper-specific numbering, but the
> attributions stand on the user-verified reading.

## §1 — The theorem

**Paper.** J. D. Hobby, "Practical segment intersection with finite
precision output," Computational Geometry: Theory and Applications
13(4):199-214, 1999. Section 4.

**Result.** Hobby's snap-rounding discretisation operator `D_T` preserves
the "fully intersected" property of an arrangement: distinct input segments
that meet only at endpoints stay that way after snap-rounding.  In the
corpus:

  - `D_T` is `snap_round_segments` — apply `snap_round (·) 1` to every
    segment endpoint.
  - "Fully intersected" is `fully_intersected` — for all distinct pairs in
    the arrangement, `segments_intersect_only_at_endpoints` holds.

The theorem reads: `fully_intersected A → fully_intersected (snap_round_segments A)`.

**Why this matters.** This is the heart of snap-rounding's combinatorial
correctness.  Together with bounded displacement (Phase 2 audit doc §2.5),
it gives the algorithm's two foundational guarantees: the output is close
to the input *and* its arrangement structure is well-formed.  Downstream
arrangement algorithms (overlay, planar subdivision) consume this property.

## §2 — The proof structure

Hobby's Section 4 establishes the theorem via two lemmas:

  1. **Lemma 4.2 (monotone coordinate)** — §3 below.  A geometric fact:
     for any segment, there is a 45° diagonal direction in which the
     snap-rounded integer points along the segment are strictly ordered.
     Foundation for the rotated-coordinate argument in Lemma 4.3.

  2. **Lemma 4.3 (piecewise-linear ordering)** — §4 below.  The core
     argument: snap-rounding two endpoint-only-intersecting segments
     produces two snap-rounded chains that still meet only at endpoints.
     Uses Lemma 4.2's diagonal coordinate, the tolerance-square half-width
     bound, and a piecewise-linear ordering of the snap chains.

Once Lemma 4.3 holds, the arrangement-level Theorem 4.1 is a pairwise lift:
every distinct pair in `snap_round_segments A` comes from a distinct pair
in `A`, which is endpoint-only by `fully_intersected A`, which by Lemma 4.3
gives endpoint-only after snapping.  That lift IS
`hobby_theorem_4_1_conditional` in the corpus; it is **Qed-closed** modulo
Lemma 4.3 as an explicit hypothesis.

## §3 — Lemma 4.2 (monotone coordinate)

**Statement (corpus form).**

```coq
Lemma hobby_lemma_4_2 :
  forall (P0 P1 : Point),
    P0 <> P1 ->
    exists alpha_y : R,
      (alpha_y = 1 \/ alpha_y = -1) /\
      forall p q : Point,
        in_snap_region P0 P1 p ->
        in_snap_region P0 P1 q ->
        p <> q ->
        px p + alpha_y * py p <> px q + alpha_y * py q.
```

`in_snap_region P0 P1 p` is the Coq rendering of Hobby's R⁻(segment):
integer-grid points lying weakly lower-left of some point on the segment.

**Proof sketch (Hobby §4).** Take `alpha_y = sign(slope of the segment)`.
For two distinct integer points `(x_1, y_1), (x_2, y_2)` in R⁻(segment),
the projection `x_i + alpha_y · y_i` is the linear functional whose level
lines are perpendicular to the segment-aligned diagonal.  Because the
segment's slope sign is `alpha_y`, no two distinct lattice points in
R⁻(segment) lie on the same diagonal level: their integer coordinates
would force them to coincide on the segment, contradicting
`(x_1, y_1) ≠ (x_2, y_2)`.

**Coq tools required.**
  - `IZR : Z → R`, `Z.le`, `Z.lt`, `Z.add`, `Z.mul`.
  - Ceiling and floor functions (`Zfloor`, `Zceil` — already available via
    Flocq or `up`); ceiling monotonicity over Z.
  - Pure real arithmetic via `lra` / `nra`.
  - **No Flocq specifically** — this lemma's statement and proof are
    Flocq-independent; it lives in the Flocq layer only because the
    surrounding infrastructure does.

**Scope estimate.** 2-3 sessions.  Genuine geometric work but bounded.

**First refinement on resumption.** The exact half-open boundary
convention of `in_snap_region` (Hobby p.210-211 specifies a convention
opposite to R's; see §4 below) must be aligned with the paper before
attempting the proof, since the boundary case is where lattice-point
monotonicity could fail at the segment endpoints.  See §7.

## §4 — Lemma 4.3 (piecewise-linear ordering)

**Statement (corpus form).**

```coq
Lemma hobby_lemma_4_3 :
  forall (P0 P1 Q0 Q1 : Point),
    segments_intersect_only_at_endpoints (P0, P1) (Q0, Q1) ->
    forall sigma1 sigma2 : Point * Point,
      In sigma1 (snap_round_segments [(P0, P1)]) ->
      In sigma2 (snap_round_segments [(Q0, Q1)]) ->
      sigma1 <> sigma2 ->
      segments_intersect_only_at_endpoints sigma1 sigma2.
```

**Proof sketch (Hobby §4).**

1. Apply Lemma 4.2 to one of the two segments to obtain a diagonal
   direction `α = (1, ±1)`.  Use `α` as the new "ξ" axis; let `η` be the
   perpendicular axis.  In (ξ, η) coordinates the snap-rounded chains
   `D_T(s_1)` and `D_T(s_2)` become piecewise-linear functions `F_1(ξ)`
   and `F_2(ξ)` (single-valued in ξ because Lemma 4.2 gave us monotonicity
   in ξ).

2. Each `F_j(ξ)` approximates the linear function `β_j + γ_j · ξ` (the
   original segment in (ξ, η)) with the tolerance-square bound:

   `|F_j(ξ) − β_j − γ_j · ξ| < 1/2`.

3. The endpoint-only-intersect hypothesis on the originals gives an
   ordering of the two linear functions on the relevant ξ-range:
   `β_1 + γ_1 · ξ ≤ β_2 + γ_2 · ξ` (or the symmetric inequality), with
   equality only at the (at most one) endpoint they share.

4. Composing (2) and (3) with appropriate slack from the tolerance bound
   shows `F_1(ξ) ≤ F_2(ξ)` strictly except possibly at the snap-rounded
   endpoints — exactly the condition for the snapped chains to meet only
   at endpoints.

**Key subtlety — the R⁻ half-open convention (Hobby p.210-211).**
Hobby uses a half-open convention for R⁻ that is the **opposite** of R's
standard convention.  This is load-bearing for step (4): the boundary
strictness in `|F_j(ξ) − β_j − γ_j · ξ| < 1/2` versus `≤ 1/2` decides
whether a snap-rounded endpoint that lands exactly on the boundary is
attributed to the segment containing it (and therefore counted as a shared
endpoint) or excluded (and the segments are non-incident).  The conditional
theorem is robust to either choice; the standalone Lemma 4.3 is not.

**Coq tools required.**
  - A representation of piecewise-linear functions over R (a `list` of
    breakpoints + per-segment linear forms is sufficient).
  - The (ξ, η) coordinate rotation as a linear change of variables
    (provable in pure R).
  - The tolerance-square half-width bound: from `snap_round_coord`'s
    definition (round-to-nearest-even on the unit grid),
    `|B2R (snap_round_coord x 1) - x| ≤ 1/2` — already implicit in
    Slice 12's analysis, needs to be stated as a standalone lemma.
  - `Rle`/`Rlt` chaining; `lra` for the final composition.
  - Possibly Coquelicot for cleaner piecewise-linear analysis (optional;
    everything is doable in pure R + `lra` at the cost of more bookkeeping).

**Scope estimate.** 4-6 weeks of focused work.  Thesis-shaped — comparable
to the Shewchuk-Theorem-13 effort in audit weight: the algorithm-level
correctness rests on this single combinatorial-geometric lemma.

## §5 — What the corpus already has

Phase 2 Slices 10-13 supplied the local infrastructure that the proof of
Lemma 4.3 will eventually consume:

  - **Slice 10** — `b64_liang_barsky_touches`: tolerance-square
    intersection detection.  Establishes the form of the half-open
    intersection predicate used in §4 above.
  - **Slice 11** — `b64_passes_through_hot_pixel`: passes-through
    relation; the sound+complete bracket against the closed/half-open
    R-side relation.  Pinned `b64_snap` to Flocq's `Bnearbyint` with the
    exact `b64_snap_coord_B2R` bridge.
  - **Slice 12** — `b64_snap_round_preserves_passes_through`: the local
    kernel of Lemma 4.3 at the per-pixel level.  Says snap-rounding does
    not eject a segment from a hot pixel it passes through.  Unconditional
    (the relation's definition already carries the snapped touch).
  - **Slice 13** — `b64_snap_round_preserves_shared_hot_pixel` and
    `b64_snap_round_preserves_pixel_cover`: per-pair and per-arrangement
    consequences of Slice 12, again at the hot-pixel level (not yet at
    the piecewise-linear-ordering level Lemma 4.3 needs).
  - **This session** — `hobby_theorem_4_1_conditional` (Qed-closed); the
    arrangement-level lift conditional on Lemma 4.3 as an explicit
    pair-preservation hypothesis.

The corpus is therefore in the same position for Hobby as it is for
Shewchuk: the headline is conditional-closed, the gap is named, the
infrastructure that the proof will sit on is in place.

## §6 — The precise gap

Two Admitteds, both registered in `docs/admitted-deferred-proofs.txt`:

| Lemma                | Scope      | Tools                                              |
|----------------------|------------|----------------------------------------------------|
| `hobby_lemma_4_2`    | 2-3 sessions | IZR, ceiling-over-Z, pure R arithmetic           |
| `hobby_lemma_4_3`    | 4-6 weeks  | Piecewise-linear functions, (ξ, η) rotation, bound |

Lemma 4.2 is the accessible warm-up.  Lemma 4.3 is the thesis-shaped
piece.  Closing both clears Hobby Theorem 4.1 from `hobby_theorem_4_1_
conditional` to the unconditional `hobby_theorem_4_1` (by discharging
the `Hlemma43` premise via `hobby_lemma_4_3` plus a small wrapper that
specialises `snap_round_segments [s1]` / `snap_round_segments [s2]` to
the explicit `(snap_round (fst s_i) 1, snap_round (snd s_i) 1)` pair).

The conditional theorem itself is **already Qed-closed**.  No proof work
is needed on the headline — only the two supporting lemmas remain.

## §7 — Resumption checklist

In order:

  - [ ] **Redefine `in_snap_region` against Hobby's p.210-211 R⁻** —
        not merely a boundary flip.  Lemma 4.2 Session 1
        (`docs/hobby-lemma-4-2-session-1-outcome.md`) exhibits a
        concrete three-point counterexample under the current
        closed-staircase rendering: the predicate as written is an
        entire lower-left quadrant, not a near-segment strip, so the
        monotone-coordinate lemma is **false** as stated.  Proposed
        fix: replace the closed-staircase form with
        `segment_touches_hot_pixel P0 P1 p 1`, which is
        strip-shaped and matches Hobby's R⁻.  Fix before any further
        attempt at Lemma 4.2.
  - [ ] **Prove `hobby_lemma_4_2`** via IZR plus ceiling monotonicity
        over Z.  Choose `alpha_y` based on the sign of the segment's
        slope; reduce to a Z-level monotonicity argument.  2-3 sessions
        — but only after the predicate is corrected; the §3 sketch is
        valid against the corrected predicate, not the current one.
  - [ ] **Define a piecewise-linear function representation** suitable
        for §4's `F_j(ξ)`.  A list of breakpoints with per-segment linear
        coefficients suffices; provide an evaluation function and
        ordering lemmas.
  - [ ] **Formalise the (ξ, η) coordinate rotation** as a linear change
        of variables; show that `snap_round` composed with the rotation
        gives the piecewise-linear `F_j(ξ)` of §4 step (1).
  - [ ] **Extract the tolerance-square bound** from Slice 12's
        `snap_round_coord` infrastructure as a standalone lemma:
        `Rabs (snap_round_coord x 1 - x) <= 1/2` (or the corresponding
        strict bound, per the chosen boundary convention).
  - [ ] **Prove `hobby_lemma_4_3`** by composing steps (1)-(4) of §4
        above: rotated coordinates → piecewise-linear functions →
        tolerance bound → ordering composition.  4-6 weeks.
  - [ ] **Close the unconditional Hobby Theorem 4.1** as a small wrapper
        over `hobby_theorem_4_1_conditional` discharging `Hlemma43` via
        the now-proved `hobby_lemma_4_3`.  Remove both registry entries.

The conditional theorem is the corpus's commitment that the rest of the
proof composes correctly once these pieces land.  The deferred-proof
registry is the corpus's commitment that the pieces are tractable, with
named tools and scope estimates rather than "TODO: hard."
