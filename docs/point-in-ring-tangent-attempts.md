# Seams 3 + 5 tangent attempts — green workflow outcomes

**Companion to** `theories/PointInRingTangents.v` and
`docs/point-in-ring-seams-3-5-7-red.md`.

**Status.**  Green-phase outcomes per tangent (4 Seam 5 + 5 Seam 3 =
9 tangents).  Per the discipline: every tangent attempted; Qed-closed
results land in `theories/PointInRingTangents.v`; stuck/deferred
results documented here.  No Admitteds added.

---

## Tangent 5A — `atan2` definition + trivial property

### Statement

```coq
Definition atan2 (y x : R) : R :=
  if Rgt_dec x 0 then atan (y / x)
  else if Rlt_dec x 0 then
    if Rge_dec y 0 then atan (y / x) + PI
    else atan (y / x) - PI
  else
    if Rgt_dec y 0 then PI / 2
    else if Rlt_dec y 0 then - (PI / 2)
    else 0.

Lemma atan2_pos_x :
  forall y x : R, x > 0 -> atan2 y x = atan (y / x).
```

### Outcome

**Qed**.  Definition + four sample properties (`atan2_pos_x`,
`atan2_neg_x_pos_y`, `atan2_zero_x_pos_y`, `atan2_origin`) — all 4-line
proofs by `unfold + destruct Rgt_dec`.

### Notes

Stdlib's `atan` (Ratan.v:549) is sufficient.  No Coquelicot needed.

---

## Tangent 5B — `atan2_bound`

### Statement

```coq
Lemma atan2_bound :
  forall y x : R, -PI < atan2 y x <= PI.
```

### Outcome

**Provable but skipped** (exceeds 20-min budget).  Path is mechanical:
6+ case branches (x > 0; x < 0 with y >= 0, y < 0; x = 0 with y > 0,
y < 0, y = 0).  Each closes via `atan_bound : -PI/2 < atan x < PI/2`
plus sign analysis of y/x.

For x < 0, y >= 0: atan2 = atan(y/x) + PI.  Since y >= 0 and x < 0,
y/x <= 0, so atan(y/x) <= 0, giving atan2 <= PI.  Lower bound from
atan(y/x) > -PI/2 gives atan2 > PI/2.

The prompt's predicted obstacle ("adding π gives (π/2, 3π/2) which
exceeds π") was wrong about the upper bound — the y-sign constraint
gives atan(y/x) <= 0 in this branch.

### Cost to close

50-80 lines; 1/2 session.

---

## Tangent 5C — `total_angle_telescopes`

### Statement

```coq
Lemma total_angle_telescopes :
  forall (P : Point) (r : Ring),
    ring_closed r ->
    total_angle P r = atan2 (...) - atan2 (...).
```

### Outcome

**STUCK** — the claim is FALSE in general.

`atan2` has a branch cut at the negative x-axis (the function jumps
from -PI to PI when crossing).  Summing angular differences naively
does NOT telescope; for a closed simple polygon the sum is
`2*PI*k` for some `k in {-1, 0, +1}` (the winding number), NOT zero
as the telescoping interpretation would predict.

The "telescoping" framing confuses signed angle differences with
arc lengths.  A correct approach needs either:
  - branch-cut-aware angular subtraction (subtract 2*PI when the
    naive difference jumps), or
  - the Cauchy/Stokes line integral form (`d theta` integral).

Both are research-grade.  Documented as motivation for Option C
(Tangent 5D below) — bypassing winding number is the right move.

### Cost to close

Thesis-scale (Jordan / winding number theory).

---

## Tangent 5D — Option C bypass theorem

### Statement

```coq
Section OptionCBypass.
  Variable topological_interior : Point -> Ring -> Prop.

  Theorem point_in_ring_correct_via_crossing :
    forall (p : Point) (r : Ring),
      ring_simple r -> ring_closed r -> no_horizontal_edge_at p r ->
      (forall q s, ring_simple s -> ring_closed s ->
                   no_horizontal_edge_at q s ->
                   point_in_ring q s <-> topological_interior q s) ->
      point_in_ring p r <-> topological_interior p r.
End OptionCBypass.
```

Plus a companion `count_crossings_correct_via_crossing` that bridges
through the bool-side parity via the existing `point_in_ring_eq_parity`.

### Outcome

**Qed**.  Both theorems close trivially (the iff is the hypothesis
applied to the goal).

### Significance

These two theorems are the formal Option C — the JCT-shaped
hypothesis fully spelt out, plus the corollary that connects the
bool-side `count_crossings_ray` directly to the topological interior.
Once a future session lands the JCT discharge of the hypothesis,
the full `point_in_ring_correct` theorem is one `apply HJCT` away.

This is strictly more useful than `point_in_ring_correct_conditional`
from the previous session because:
  - it carries the `no_horizontal_edge_at` precondition explicitly
    (matching the generic-position convention);
  - it bridges through the bool-side count via the fold-bridge
    corollary.

---

## Tangent 3A — fourcolor import gate

### Statement

```coq
From fourcolor Require Import real realplane.
Check @Real.structure.
Check @realplane.point.
Check @realplane.connected.
```

### Outcome

**GREEN** — confirmed via standalone test (not committed to the
corpus build).  fourcolor's `real.v` and `realplane.v` import
cleanly alongside Stdlib `Reals`.  No universe inconsistency, no
namespace conflict.  Both `Real.structure : Type` and
`realplane.point : Real.structure -> Type` are accessible.

### Critical finding adjusting the red workflow

The red-workflow doc rated this as "import alone surfaces the
Real.structure bridge gap" with the implication that conflicts might
appear.  Confirmed: no conflicts.  The two libraries coexist.

### Why this matters

This GATES Tangents 3B/3C/3D's feasibility.  Without it, all
Seam 3 fourcolor-based work would have been blocked.  With it, the
remaining tangents are all reachable.

### Why not committed to the corpus build

Adding `fourcolor` to the corpus's build dependencies costs ~10
minutes per CI run (mathcomp + ssreflect + elpi compile chain) and
pulls additional axioms (see Tangent 3B).  The current corpus build
stays Stdlib-only; the fourcolor bridge becomes a separate
investment when the user authorises the policy change.

---

## Tangent 3B — `Real.sup` from Stdlib `completeness`

### Statement

```coq
Definition R_sup (E : R -> Prop) : R :=
  match excluded_middle_informative (bound E /\ (exists x, E x)) with
  | left H => proj1_sig (completeness E (proj1 H) (proj2 H))
  | right _ => 0
  end.
```

### Outcome

**GREEN with COST**.  The construction typechecks and yields a total
`(R -> Prop) -> R` function suitable for `Real.sup`.

### Cost: README allowlist expansion

The `excluded_middle_informative` call pulls
**`constructive_definite_description`** into the axiom footprint.
This axiom is NOT currently on the README allowlist
(`docs/axiom-allowlist.txt`).  Landing the Real.structure instance
in the main corpus would require either:

  1. Adding `constructive_definite_description` to the allowlist
     (a policy-level decision), OR
  2. Listing the new file in `docs/audit-exceptions.txt` as a
     transitional Category C exemption.

Per the corpus's documented policy (audit-exceptions.txt:13-19),
adding to the exception list requires PR justification.

### Alternative paths investigated

  - **Using `classic` directly**: `Classical_Prop.classic` returns
    a `Prop`-level disjunction; cannot `match` on it to construct
    a TERM.  Would need a sumbool — same axiom pull as
    `excluded_middle_informative`.
  - **Partial Real.sup**: define `R_sup_partial` with `bound E`
    + `exists x, E x` as preconditions.  Avoids the axiom but
    doesn't match fourcolor's total `Real.sup` signature.

### Cost to close

Definition: zero — already done above.  Policy decision (axiom
allowlist expansion OR exception listing): user-level.

---

## Tangent 3C — `to_rplane` translation

### Statement

```coq
Definition to_rplane (p : Distance.Point) : realplane.point Stdlib_R_struct :=
  @realplane.Point Stdlib_R_struct (px p) (py p).
```

### Outcome

**GREEN** — once `Stdlib_R_struct` is built with `Real.val := R`
definitionally, the translation typechecks immediately.  No
coercion, no `eq_rect`, no universe gymnastics.

### Approach pivoted from the red workflow

The red-workflow doc suggested using `eq_rect` with an explicit
`R_val_is_R : Real.val Rmodel = R` proof.  That approach **fails**
with a universe inconsistency:

```
The term "real.Real.val Rmodel" has type "Type"
while it is expected to have type "Set"
(universe inconsistency: Cannot enforce
 real.Real.structure.u0 <= Set).
```

(Stdlib `R : Set`; fourcolor `Real.val : Type` at a higher universe.)

The pivot: build the structure with `Real.val := R` definitionally
(no equality proof needed).  Then `to_rplane` just constructs
`realplane.Point` with `px p` and `py p` directly — they have type
`R` which IS `Real.val Stdlib_R_struct` definitionally.

### Cost to close

Zero — done above.  Land in corpus once Tangent 3B's allowlist
issue is resolved.

---

## Tangent 3D — `geometric_interior` in Stdlib only

### Statement

```coq
Definition ring_image (r : Ring) (q : Point) : Prop := ...
Definition ring_complement (r : Ring) (q : Point) : Prop := ~ ring_image r q.
Definition connected_in_complement (r : Ring) (p q : Point) : Prop := ...
Definition in_bounded_component (r : Ring) (p : Point) : Prop := ...
Definition geometric_interior_stdlib (p : Point) (r : Ring) : Prop :=
  ring_complement r p /\ in_bounded_component r p.
```

### Outcome

**Qed**.  Definition + three basic properties:
  - `not_geometric_interior_on_edge` — points on ring edges are not
    in the interior.
  - `ring_image_nil` — empty ring has empty image.
  - `not_geometric_interior_empty_ring` — empty ring has no interior
    (no bounded component covers all of R^2).

### Critical finding

**Pure-Stdlib `geometric_interior` IS definable.**  The red-workflow
doc anticipated this might require fourcolor's `realplane.connected`
machinery, but the topological structure (connectedness via paths,
boundedness via diameter) is expressible directly in Stdlib `Reals`
with continuous functions `R -> Point`.

The corpus now has TWO `geometric_interior` candidates:
  1. **`geometric_interior_stdlib`** (this tangent, Stdlib only):
     pulls only README-allowlisted axioms; ready to use today.
  2. **fourcolor-based** (Tangent 3B+3C, not landed): would pull
     `constructive_definite_description` and pay the fourcolor
     build cost.

Option 1 is preferred for the corpus's epistemic invariants.  The
fourcolor route remains documented as a future option if the
combinatorial-Jordan piece becomes useful.

### Cost to close

Done.

---

## Tangent 3E — geometric_interior basic properties

### Statement

```coq
Lemma not_geometric_interior_on_edge : ...   (* Tangent 3D *)
Lemma connected_in_complement_refl : forall r p,
  ring_complement r p -> connected_in_complement r p p.
```

### Outcome

**Qed**.  Two basic properties — `not_geometric_interior_on_edge`
(under Tangent 3D) and `connected_in_complement_refl` (the path-
relation is reflexive on complement points; constant path witnesses).

### Notes

These are the building blocks for downstream development:
boundary exclusion + reflexivity of the connectedness relation.
Transitivity, symmetry, and connection to bounded components are
future tractable work (~1-2 sessions).

---

## Summary

| Tangent | Outcome | In corpus? |
|---------|---------|-----------|
| 5A: `atan2` def + `atan2_pos_x` | **Qed** | Yes (+ 3 bonus props) |
| 5B: `atan2_bound` | Provable, skipped (20-min budget) | No (doc only) |
| 5C: `total_angle_telescopes` | **STUCK** — false in general | No (claim is false) |
| 5D: Option C bypass | **Qed** | Yes (+ count_crossings corollary) |
| 3A: fourcolor import gate | **GREEN** | No (build-cost / policy) |
| 3B: `Real.sup` from completeness | GREEN, allowlist cost | No (allowlist expansion needed) |
| 3C: `to_rplane` translation | **GREEN** | No (depends on 3B in corpus) |
| 3D: Stdlib-only `geometric_interior` | **Qed** | **Yes** |
| 3E: geometric_interior properties | **Qed** | Yes (+ reflexivity) |

### Qed-closed in corpus (this session)

  - `atan2` (definition).
  - `atan2_pos_x`, `atan2_neg_x_pos_y`, `atan2_zero_x_pos_y`,
    `atan2_origin` (sample properties).
  - `point_in_ring_correct_via_crossing` (Option C bypass).
  - `count_crossings_correct_via_crossing` (bool-side dual).
  - `ring_image`, `ring_complement`, `connected_in_complement`,
    `in_bounded_component`, `geometric_interior_stdlib` (Stdlib
    topological-interior framework).
  - `not_geometric_interior_on_edge`, `ring_image_nil`,
    `not_geometric_interior_empty_ring`,
    `connected_in_complement_refl` (basic properties).

### Critical findings

**Finding 1 — Tangent 3D is the breakthrough.**  Pure-Stdlib
`geometric_interior_stdlib` is definable.  The JCT gap is now only
in the CORRECTNESS PROOF connecting `point_in_ring` to
`geometric_interior_stdlib`, not in the *definition* of the
topological interior.  This unblocks the corpus's
`overlay_ng_correct_conditional` to use a concrete `interior`
predicate instead of an opaque Section Variable.

**Finding 2 — Tangent 5C confirms Option C is the only viable path.**
The telescoping interpretation of winding number is structurally
wrong (`atan2` branch cuts).  A correct angular formulation would
need branch-cut-aware arithmetic; the combinatorial bypass (Option
C) sidesteps this entirely.

**Finding 3 — fourcolor coexists with Stdlib R cleanly.**  The
import gate (3A) was conjectural in the red workflow; confirmed
GREEN here.  The cost of the fourcolor route is now precisely
characterised: Tangent 3B's `constructive_definite_description`
axiom expansion is the only real obstacle, not a structural
incompatibility.

**Finding 4 — Tangent 3C's eq_rect approach was wrong.**  Universe
inconsistency between `Set` (Stdlib R) and `Type` (fourcolor
`Real.val`) defeats the equality-based coercion.  Pivoting to
`Real.val := R` definitionally avoids the issue entirely.  Records
this as the canonical pattern for any future Real.structure
construction over Stdlib `R`.

### Recommended next action

Use `geometric_interior_stdlib` from Tangent 3D to instantiate the
opaque `Variable geometric_interior` in
`theories-flocq/OverlayCorrectness.v` — strengthens the conditional
headline from "for any abstract interior predicate" to "for the
Stdlib-defined topological interior".  ~1 session.  No JCT
investment needed for the strengthening; the JCT piece would still
be needed to discharge the H1 hypothesis non-vacuously.

### Audit footprint

All Qed-closed results in `theories/PointInRingTangents.v` pull
only README-allowlisted axioms (`sig_forall_dec`,
`functional_extensionality_dep`).  No `Classical_Prop.classic`,
no `constructive_definite_description`, no axiom expansion.
