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

## Design session outcome — predicate fixed

**Session.** Follow-up design session, branch
`claude/hobby-in-snap-region-fix`.

**Outcome.** `in_snap_region` replaced with the strip-shaped Minkowski
sum per Hobby (1999) p.210.  The counterexample evaporates as
predicted, and `hobby_theorem_4_1_conditional` continues to compile
unchanged.  No proof attempted; that is Session 2's work.

### The corrected definition

`theories-flocq/HobbyTheorem_b64.v` (replacing the closed-staircase
form):

```coq
Definition in_snap_region (P0 P1 p : Point) : Prop :=
  (exists nx ny : Z, px p = IZR nx /\ py p = IZR ny) /\
  exists t : R, 0 <= t <= 1 /\
    let q := segment_point P0 P1 t in
    - (1/2) < px p - px q <= 1/2 /\
    - (1/2) < py p - py q <= 1/2.
```

Equivalent to `p in ℤ² ∩ (segment(P0,P1) + R⁻)` for Hobby's

    R⁻ = {(x, y) | -1/2 < x ≤ 1/2, -1/2 < y ≤ 1/2}

— the half-open unit square with bottom/left OPEN, top/right CLOSED.
Opposite half-open convention to `in_hot_pixel` (which uses
`[-1/2, 1/2) × [-1/2, 1/2)`); Session 1's proposed
`segment_touches_hot_pixel P0 P1 p 1` form would have inherited the
wrong convention.

### Choice of formulation vs. session 1's recommendation

Session 1 above proposed `segment_touches_hot_pixel P0 P1 p 1` (an
existing predicate in `theories/HotPixel.v`).  That predicate uses
`in_hot_pixel`'s `R` convention `[-1/2, 1/2) × [-1/2, 1/2)`, which is
the OPPOSITE half-open convention to Hobby's `R⁻`.  The original
file comment on the pre-fix definition (lines 88-91) already flagged
this:

> "Hobby's exact R^- has a specific half-open boundary convention
> OPPOSITE to R's; the form here is the closed-staircase rendering
> and the boundary refinement is the first resumption item."

The Minkowski-sum form used in the fix preserves Hobby's exact
convention without going through `in_hot_pixel`.  This matters for
Lemma 4.3's piecewise-linear argument, which exploits the
complementary boundary inclusion (Hobby p.211-212).

### Counterexample evaporation, verified in Coq

Three sanity lemmas (out-of-tree check, not committed to the
corpus):

  - `counterexample_evaporates`: `~ in_snap_region (mkPoint 0 0)
    (mkPoint 2 2) (mkPoint 1 (-1))`.  Proof by `lra` after
    unfolding: the y-condition `-1/2 < -1 - 2t` forces `t < -1/4`,
    contradicting `t >= 0`.
  - `origin_still_in_region`: `in_snap_region (mkPoint 0 0)
    (mkPoint 2 2) (mkPoint 0 0)` with witness `t = 0`.
  - `midpoint_still_in_region`: `in_snap_region (mkPoint 0 0)
    (mkPoint 2 2) (mkPoint 1 1)` with witness `t = 1/2`.

All three close with `lra` against `unfold in_snap_region;
unfold segment_point; simpl`.  This validates that the corrected
predicate excludes the off-diagonal counterexample point while
keeping the on-segment integer points.

### Downstream impact

  - `hobby_theorem_4_1_conditional`: unchanged.  Does not reference
    `in_snap_region` (only `snap_round_segments` and
    `segments_intersect_only_at_endpoints`).  Verified by grep and
    by re-compiling `HobbyTheorem_b64.vo` clean.
  - `hobby_lemma_4_3`: unchanged statement (does not reference
    `in_snap_region` directly), but its eventual proof plan in
    `docs/hobby-theorem-proof-structure.md` §4 is now stated
    against the correct snap region.
  - `hobby_lemma_4_2`: statement unchanged (uses `alpha_y : R` and
    the `R`-form linear projection `px p + alpha_y * py p`; the
    integer-point condition inside `in_snap_region` is what carries
    the discretisation).  Proof now plausibly closable along the
    §3 sketch in the proof-structure doc.

### Registry

`docs/admitted-deferred-proofs.txt`: no entry change.  The
`hobby_lemma_4_2` entry stays present because the lemma remains
Admitted; the deferred-proof status changes from "predicate
defective" (informal) to "predicate fixed, proof ready" (this
session).  The registry format does not capture this transition —
it is recorded here in the design doc.

### Build verification

  - `make -f Makefile.gen -j2 theories-flocq/HobbyTheorem_b64.vo`
    -> clean compile, 9.2 KB `.vo`.
  - The four standard axioms appear in the per-theorem `Print
    Assumptions` block (the three README-allowlisted plus
    `Classical_Prop.classic` -- the file is in
    `audit-exceptions.txt` for the Flocq-binary lineage; unchanged
    by this fix).
  - Counterexample-evaporation sanity check (`/tmp/counterexample_
    check.v`, out-of-tree): three lemmas, all `Qed`-closed.

### Next session

"Hobby Lemma 4.2 Session 2": attempt the proof against the
corrected predicate.  Proof structure: `docs/hobby-theorem-proof-
structure.md` §3 (unchanged -- the sketch was always against the
strip-shaped snap region, the corpus's earlier rendering was the
mismatch).

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

## Session 2 — proof closed

**Session.** Lemma 4.2 proof attempt against the corrected predicate,
follow-up branch `claude/hobby-lemma-4-2-session-2`.

**Outcome.** `hobby_lemma_4_2` is now **Qed-closed** in
`theories-flocq/HobbyTheorem_b64.v`.  Deferred-proof registry: 3 → 2
entries.

### Proof structure (matches `docs/hobby-theorem-proof-structure.md` §3)

Case split on `(px P1 - px P0) * (py P1 - py P0)` (the slope-product
sign), via `Rle_or_lt`:

  - **Product ≥ 0** (non-negative slope, horizontal, or vertical):
    choose `alpha_y = +1`.
  - **Product < 0** (negative slope): choose `alpha_y = -1`.

In each case, suppose `f(p) = f(q)` with `p ≠ q` and both in
`in_snap_region`.  Then:

  1. Destructure both `in_snap_region` witnesses (integer points
     `(np, mp)`, `(nq, mq)` and segment parameters `tp`, `tq`).
  2. From `f(p) = f(q)` and the IZR-encoded coordinates: derive a
     Z-equation via `eq_IZR_R0` plus `plus_IZR` / `minus_IZR`.  For
     `alpha_y = +1`: `(np - nq) + (mp - mq) = 0`.  For `alpha_y = -1`:
     `(np - nq) - (mp - mq) = 0`.
  3. Case split on `Z.eq_dec np nq`:
       - `np = nq`: forces `mp = mq` (from the Z-equation), so `p = q`,
         contradicting `p ≠ q`.
       - `np ≠ nq`: trichotomy on `Ztrichotomy_inf np nq` reduces to
         `np > nq` (the `np < nq` branch is symmetric).
  4. With `np - nq ≥ 1`: integer arithmetic via `IZR_le` gives
     `px p ≥ px q + 1` (and analogously for `py` from the Z-equation).
  5. R⁻ strip bounds (half-open: strict lower `-1/2 <`, closed upper
     `≤ 1/2`) combine with the integer differences to force strict
     inequalities `(1-tp)*px P0 + tp*px P1 > (1-tq)*px P0 + tq*px P1`
     etc., closed by `lra`.
  6. These rearrange (`nra`) to `(tp - tq) * (px P1 - px P0) > 0` and
     a corresponding `py` inequality.
  7. Final case split on `Rtotal_order tp tq`:
       - `tp = tq`: contradicts step 6's strict inequality (`lra`).
       - `tp < tq` or `tp > tq`: assert the sign of each segment
         difference (`px P1 - px P0`, `py P1 - py P0`) via `nra`, then
         conclude the slope product has the OPPOSITE sign of the case
         assumption (`nra` against `Hprod`).

The explicit sign-assertion step (`Hpx_neg`/`Hpx_pos`,
`Hpy_pos`/`Hpy_neg`) is the deliberate hint that lets the final `nra`
close — `nra` cannot find the witness in one step from the raw
hypothesis set, but the two-line assertion breaks the nonlinear
inference into pieces it can handle.

### Why the half-open boundary convention is load-bearing

The R⁻ strict-lower / closed-upper boundary is what gives **strict**
inequalities `(1-tp)*px P0 + tp*px P1 > (1-tq)*px P0 + tq*px P1` in
step 5.  A closed boundary on both sides would give only `≥`, which
doesn't yield contradiction at the trichotomy step 7.

This justifies the Session 1 design choice (Minkowski sum with R⁻
rather than `segment_touches_hot_pixel`, which uses the opposite
convention).

### Boundary cases handled implicitly

  - **Vertical segment** (`px P1 = px P0`): step 6 derives
    `(tp - tq) * (px P1 - px P0) > 0` with `px P1 - px P0 = 0`, giving
    `0 > 0` -- immediate contradiction.  Handled by `nra`.
  - **Horizontal segment** (`py P1 = py P0`): symmetric.
  - **Slope = ±1**: handled by the product-sign case split.  For slope
    = +1, product > 0 (Case 1, `alpha_y = +1` works).  For slope = -1,
    product < 0 (Case 2, `alpha_y = -1`).  No special-case needed.

### Build verification

  - `make -f Makefile.gen -j2 theories-flocq/HobbyTheorem_b64.vo`
    -> clean compile, 47.6 KB `.vo`.
  - `Print Assumptions hobby_lemma_4_2`:
    * `ClassicalDedekindReals.sig_forall_dec`
    * `FunctionalExtensionality.functional_extensionality_dep`
    Both on the README allowlist.  Notably, the per-theorem footprint
    does NOT include `Classical_Prop.classic` -- the proof avoids the
    Flocq-binary content that pulls `classic` elsewhere in this file.
  - `scripts/check_admitted.sh` -> 5 entries (3 counterexample, 2
    deferred-proof, down from 3).

### Imports added

  - `From Stdlib Require Import Lra.` -- for `lra`.
  - `From Stdlib Require Import Lia.` -- for `lia`.

### Next session

Hobby Lemma 4.3 (piecewise-linear ordering).  This is the
thesis-shaped piece; estimated 4-6 weeks per
`docs/hobby-theorem-proof-structure.md` §4.  Lemma 4.2's proof above
provides one of the two building blocks; the tolerance-square
`|F_j(xi) - beta_j - gamma_j * xi| < 1/2` bound is the other.
