# Hobby Lemma 4.2 Session 1 — outcome

**Session.** First attempt at closing `hobby_lemma_4_2` (monotone
coordinate) — Hobby (1999) §4 Lemma 4.2.  Branch
`claude/hobby-lemma-4-2-Wbpn8`.

**Outcome.** TANGENT STOP — the lemma as currently stated is **false**
under the corpus's current `in_snap_region` definition.  A concrete
three-point counterexample is given below.  No proof was attempted.
No registry change.  This is the §7 "first refinement" item from
`docs/hobby-theorem-proof-structure.md` materialising as a hard
counterexample rather than a soft boundary nit — the snap-region
definition needs more than a boundary tweak before the lemma can be
proved.

## The statement under review

`theories-flocq/HobbyTheorem_b64.v:108-118`:

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

`theories-flocq/HobbyTheorem_b64.v:92-96`:

```coq
Definition in_snap_region (P0 P1 p : Point) : Prop :=
  (exists nx ny : Z, px p = IZR nx /\ py p = IZR ny) /\
  exists t : R, 0 <= t <= 1 /\
    px p <= px (segment_point P0 P1 t) /\
    py p <= py (segment_point P0 P1 t).
```

`segment_point` (from `theories/HotPixel.v:106-108`) is the standard
parametric form `(1-t)·P0 + t·P1`.

## The counterexample

Take the segment `P0 = mkPoint 0 0`, `P1 = mkPoint 2 2`.  Positive
slope; `P0 <> P1` holds.  For every `t ∈ [0,1]`, `segment_point t =
(2t, 2t)`.

For ANY integer point `(a, b)` with `a ≤ 2 ∧ b ≤ 2`, pick `t = 1`:
`segment_point 1 = (2, 2)`, satisfying `a ≤ 2` and `b ≤ 2`.  So

```
in_snap_region P0 P1 (mkPoint a b)   ⟺   a ≤ 2 ∧ b ≤ 2     (for a,b ∈ ℤ)
```

i.e. `in_snap_region` is the entire integer lower-left quadrant `{(a,b)
∈ ℤ² : a ≤ 2 ∧ b ≤ 2}`.  No proximity-to-segment constraint at all.

Pick three distinct integer points in that quadrant:

| name | `(a, b)` | `a + b` (`α_y = +1`) | `a − b` (`α_y = −1`) |
|------|----------|----------------------|-----------------------|
| `p`  | `(0, 0)` | `0`                  | `0`                   |
| `q`  | `(1, 1)` | `2`                  | `0`                   |
| `r`  | `(1, −1)`| `0`                  | `2`                   |

* `α_y = +1` collides on `(p, r)` — both give `0`.
* `α_y = −1` collides on `(p, q)` — both give `0`.

There is no `α_y ∈ {+1, −1}` separating all three pairs, but the lemma
asks for a single `α_y` good for every distinct pair.  The existential
cannot be witnessed for this segment — the universal `forall p q` would
have to fail for the witness chosen.  **The lemma is false as written.**

## Why this is a definition mismatch, not a proof gap

Hobby's R⁻(s) (Hobby 1999 p.210-211) is the set of integer points whose
**hot pixel intersects the segment** — a strip of width ≈√2/2 around
the segment, not a half-plane.  Hobby's monotonicity argument relies on
that strip being thin: two distinct integer points whose hot pixels both
meet the segment cannot project to the same diagonal coordinate, because
that would force their hot pixels to lie on the same diagonal **and**
both touch the segment, which (since the diagonal is perpendicular to
the chosen `α`-axis when `α = sign(slope)`) forces the two pixels to
coincide.

The corpus's `in_snap_region` is missing the upper bound entirely.  It
says "p is integer **and** weakly lower-left of some segment point" —
which any integer point in the open quadrant `(-∞, x_max] × (-∞, y_max]`
satisfies, where `x_max = max(px P0, px P1)` and likewise for `y_max`.
This is dramatically more permissive than Hobby's R⁻.  In the
counterexample above, `r = (1, −1)` is on the opposite side of the
segment from `q = (1, 1)`; both are far from the diagonal containing
the segment, but both are in the lower-left quadrant of `(2, 2)`.

The file comment on lines 88-91 already hints at this:

> "Hobby's exact R^- has a specific half-open boundary convention
> OPPOSITE to R's; the form here is the closed-staircase rendering and
> the boundary refinement is the first resumption item."

But this understates the problem.  A "boundary refinement" would mean
flipping `≤` to `<` on one side or the other.  The actual gap is
structural: a missing upper bound coupling `p` to the **same** segment
point `(px p, py p) ≤ segment_point t` only on the lower side.  The
correct rendering needs **two-sided** containment in a hot-pixel-wide
neighbourhood of the segment.

## Proposed fix (for a follow-up design session)

The corpus already has a half-open hot-pixel predicate that captures
the right strip:

`theories/HotPixel.v:75-77`:

```coq
Definition in_hot_pixel (P C : Point) (scale : R) : Prop :=
  px C - hot_pixel_radius scale <= px P < px C + hot_pixel_radius scale /\
  py C - hot_pixel_radius scale <= py P < py C + hot_pixel_radius scale.
```

`theories/HotPixel.v:110-112`:

```coq
Definition segment_touches_hot_pixel
  (P0 P1 C : Point) (scale : R) : Prop :=
  exists t : R, 0 <= t <= 1 /\ in_hot_pixel (segment_point P0 P1 t) C scale.
```

A faithful R⁻ would be roughly:

```coq
Definition in_snap_region (P0 P1 p : Point) : Prop :=
  (exists nx ny : Z, px p = IZR nx /\ py p = IZR ny) /\
  segment_touches_hot_pixel P0 P1 p 1.
```

i.e. "p is an integer point whose unit hot pixel meets the segment."
That predicate is strip-shaped, not quadrant-shaped, and the
counterexample above evaporates: for the segment `(0,0)–(2,2)`, the
only integer points whose unit hot pixel meets the segment are `(0,0),
(1,1), (2,2)` (and possibly the half-open-boundary neighbours of those
along the diagonal).  `(1, −1)` and `(−1, 1)` are excluded — their unit
hot pixels lie entirely off the diagonal.

The lemma would then be plausibly provable along the lines of §3's
sketch: with `α_y = sign(slope)`, the projection `x + α_y·y` is
strictly monotone along the segment in the chosen diagonal, and the
hot-pixel-width bound prevents two distinct integer points in the strip
from projecting to the same value.

This change requires re-verifying that `hobby_theorem_4_1_conditional`
and `hobby_lemma_4_3` still compose against the new `in_snap_region`.
The conditional theorem (lines 159-183) doesn't unfold `in_snap_region`
directly — it only references `snap_round_segments` and
`segments_intersect_only_at_endpoints` — so it should be unaffected.
`hobby_lemma_4_3`'s proof (still Admitted) will eventually consume
`in_snap_region` through Lemma 4.2's conclusion, so the redefinition
must precede serious work on 4.3 anyway.

## What was NOT done, and why

* **No proof attempt.** Proving a false statement is impossible; closing
  it with `Admitted` would be regressive (it's already `Admitted`).
* **No registry update.** The registry entry stays at 3.  The deferred
  count drops to 2 only when the lemma is actually proved (against a
  fixed definition).
* **No edit to `in_snap_region`.** Changing the definition has
  downstream implications for `hobby_lemma_4_3` and the proof structure
  doc, and should be done in a focused design session with the
  Hobby p.210-211 paper text open.  This session's mandate was to prove
  Lemma 4.2 against the **registered** statement, not to redesign it.
* **Build verification skipped.** The remote execution environment for
  this session does not have Rocq/opam installed — `which opam`,
  `which rocq`, `which coqc` all return nothing — so the standard
  gauntlet (`make -f Makefile.gen`, `check_admitted.sh`,
  `audit_axioms.sh`) could not be run.  No source files were modified
  so this is moot for the on-disk state.

## Recommended next session

A short design session (≤1 session) that:

1. Reads Hobby (1999) p.210-211 directly to fix the exact R⁻
   convention.
2. Replaces `in_snap_region`'s closed-staircase rendering with the
   `segment_touches_hot_pixel` form (or whatever exactly matches the
   paper).
3. Re-verifies `hobby_theorem_4_1_conditional` still compiles
   unchanged (expected: yes, no unfolding involved).
4. Notes the consequent change in `hobby_lemma_4_3`'s eventual proof
   plan in `docs/hobby-theorem-proof-structure.md` §4.

After that design session, a fresh "Hobby Lemma 4.2 Session 2" attempt
can pick up the proof against the corrected definition.  The proof
sketch in §3 of the proof-structure doc remains valid — only the
predicate it's quantifying over needs to change.

## Stopping condition

This stop matches the **first** listed stopping condition in the
session prompt:

> *Tangent stop — in_snap_region uses closed box: the definition
> doesn't match the R⁻ half-open convention from Hobby p.210.  The
> monotonicity argument requires strict inequality which a closed
> box doesn't provide.  Document the definition mismatch.  This is a
> §7 refinement item from docs/hobby-theorem-proof-structure.md —
> the corpus's in_snap_region may need adjustment before the proof
> can close.  Stop.  Open a follow-up design session.*

with the strengthening that the closed-box rendering is not merely
strictness-deficient but **structurally** wrong (a quadrant rather
than a strip), so the fix is a redefinition rather than a boundary
flip.
