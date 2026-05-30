# `point_in_ring_correct` — seam attempts

**Companion to** `theories/PointInRingCorrect.v` and
`docs/point-in-ring-correct-seam-map.md`.

**Status.**  Green-phase outcomes per seam.  Every seam was attempted
at the simplest-possible level.  Some closed (Qed); some surfaced
precise stuck goals; some are deferred without a Coq surface
(library/ecosystem gating).  No Admitteds were registered — failed
attempts are documented here rather than left in the corpus.

---

## Seam 1 — `segment_crosses_ray` (bool) and correctness

### Statement

```coq
Definition segment_crosses_ray (P A B : Point) : bool :=
  if Rlt_b (py A) (py P) && Rlt_b (py P) (py B) then
    Rlt_b (px P) (px A + (px B - px A) * (py P - py A) / (py B - py A))
  else if Rlt_b (py B) (py P) && Rlt_b (py P) (py A) then
    Rlt_b (px P) (px B + (px A - px B) * (py P - py B) / (py A - py B))
  else false.

Theorem segment_crosses_ray_correct :
  forall (P A B : Point),
    py A <> py B ->
    segment_crosses_ray P A B = true <->
    exists t : R,
      0 < t < 1 /\
      py A + t * (py B - py A) = py P /\
      px A + t * (px B - px A) > px P.
```

### Outcome

**Qed** on three companion lemmas — `segment_crosses_ray_sound` (no
precondition), `segment_crosses_ray_complete` (with `py A <> py B`),
and `segment_crosses_ray_correct` (biconditional under `py A <>
py B`).

### Pivot from the prompt

The prompt suggested an xorb-on-y-straddle bool form.  That form
admits a parametric witness with `t = 1` (endpoint on the ray) but
the bool returns `true`, so soundness can't claim `0 < t < 1`
strictly.  Switched to a TWO-CASE strict-strict form mirroring the
corpus's existing `edge_crosses_ray : Prop`, which makes
`segment_crosses_ray_sound` precondition-free.

### Notes

  - Stdlib has no `Rlt_bool`; defined a local
    `Rlt_b : R -> R -> bool` via `Rlt_dec`.
  - Completeness REQUIRES `py A <> py B`.  A horizontal segment lying
    ON the ray admits a parametric witness while the bool returns
    false (strict-strict y-straddle fails).  Generic-position
    convention.

### Cost to close

Closed.  ~110 lines of routine algebra (case-split on `Rlt_dec (py A)
(py B)`; `field` + `nra` + `lra` for the rest).

---

## Seam 2 — `count_crossings_ray` and agreement with `point_in_ring`

### Statement

```coq
Definition count_crossings_ray (p : Point) (r : Ring) : nat :=
  fold_left
    (fun acc e => let '(A, B) := e in
                  if segment_crosses_ray p A B then S acc else acc)
    (ring_edges r) 0%nat.

Lemma point_in_ring_eq_parity :
  forall (p : Point) (r : Ring),
    point_in_ring p r <-> Nat.odd (count_crossings_ray p r) = true.
```

### Outcome

**Partial.**  Definition `count_crossings_ray` lands.
`segment_crosses_ray_matches_edge_crosses_ray` lemma closes (per-edge
agreement between bool and Prop forms under `py A <> py B`).

The list-level parity agreement (`point_in_ring p r <-> Nat.odd
(count_crossings_ray p r) = true`) does NOT close.

### Stuck at

The fold_left accumulator's parity does not align with the mutual
inductive `ray_parity_odd`/`ray_parity_even` directly.  The fold
seeds at 0 and toggles per crossing edge; `ray_parity_odd` /
`ray_parity_even` toggle in the same way over the edge list — but
the proof requires:

  1. A generalised induction lemma where the fold accumulator is
     left abstract (any starting nat, not just 0), and
  2. A bridge `forall acc l, Nat.odd (fold_left ... l acc) =
     xorb (Nat.odd acc) (Nat.odd (fold_left ... l 0))` or similar.

These exist in `Stdlib.NArith` / `Stdlib.Nat` but tying them to
the mutual inductive's structure requires careful destructuring of
both the `Forall (fun e => py (fst e) <> py (snd e))` precondition
(needed per-edge) AND the inductive's constructors.

### Missing piece

The fold-vs-mutual-inductive bridge.  Standard list-level induction
pattern, 2-3 hours of careful proof engineering.

### Cost to close

1 session (2-4 hours of routine list induction + Nat.odd
distributing over fold_left).

---

## Seam 3 — `geometric_interior` via fourcolor `realplane`

### Attempt

```coq
From fourcolor Require Import realplane.

Definition to_rplane (p : Point) : realplane.point R_structure :=
  Point (px p) (py p).
```

### Outcome

**Documented stuck** — no Coq definition lands.

### Stuck at

`realplane.point` is `Inductive point := Point (x y : Real.val R)`
parametric over a Section variable `R : Real.structure`.  Stdlib's
`R` is NOT a `Real.structure` instance.  Constructing one requires
defining all of `Real.structure`'s fields (a Tarski-style axiomatic
real-line interface: `add`, `mul`, `opp`, `lt`, `min`, `set` ...) and
proving each axiom over Stdlib `R`.

Per `docs/ecosystem-search-2026-05-29.md` §5: estimated 2-3 sessions
for the bridge work.

### Missing piece

The `Real.structure` instance for Stdlib `R` -- THE bridge artifact.
Once it exists, `geometric_interior` can be defined as:

```coq
Definition geometric_interior (p : Point) (r : Ring) : Prop :=
  let m : map R_stdlib := <map from ring r> in
  let z : point R_stdlib := to_rplane p in
  exists region_id : point R_stdlib,
    (m z) region_id /\ bounded (m z).
```

### Cost to close

`Real.structure` instance: 2-3 sessions.

`geometric_interior` definition: <1 session after the bridge.

---

## Seam 4 — `point_in_ring_correct_conditional`

### Statement

```coq
Section ConditionalPointInRingCorrect.
  Variable interior : Point -> Ring -> Prop.

  Theorem point_in_ring_correct_conditional :
    forall (p : Point) (r : Ring),
      ring_simple r -> ring_closed r -> ring_has_minimum_points r ->
      (point_in_ring p r <-> interior p r) ->
      point_in_ring p r <-> interior p r.
  Proof.
    intros p r _ _ _ Hiff. exact Hiff.
  Qed.
End ConditionalPointInRingCorrect.
```

### Outcome

**Qed (vacuously).**  The theorem is a tautology because the iff is
both hypothesis and conclusion.

### Honest reading

The Qed here records the SHAPE of the headline statement once an
`interior` predicate exists.  It does NOT close any actual gap.  Real
Seam 4 work — deriving the iff from a structural hypothesis like
"`interior` is the bounded component of `R² \ image(r)`" — requires
`interior` to be defined first (Seam 3's blocker).

### Missing piece

Same as Seam 3: `interior` defined.

### Cost to close

Already Qed.  The "real" Seam 4 (deriving the iff from a topology-
flavoured structural hypothesis) is gated by Seam 3.

---

## Seam 5 — `winding_number` for simple polygons

### Attempt

```coq
Definition winding_number (p : Point) (r : Ring) : R :=
  (* signed-angle sum over edges, divided by 2*pi *)
  ...
```

### Outcome

**Documented stuck** — no Coq definition lands.

### Stuck at

`winding_number` requires `atan2 : R -> R -> R` for the signed-angle
contribution per edge.  Stdlib's `Ratan : R -> R` (in `Stdlib.Reals.
Ratan`) is single-argument; it does NOT provide a quadrant-correct
two-argument variant.  `atan2` lives in Coquelicot or
`mathcomp-analysis`.

Per `docs/ecosystem-search-2026-05-29.md`:
  - Coquelicot is NOT in the installed package set.
  - `mathcomp-analysis` is installed but introduces
    `propositional_extensionality` + `constructive_indefinite_
    description` axioms — README allowlist expansion required.

### Alternative attempted

```coq
Definition winding_number (p : Point) (r : Ring) : Z :=
  (count_crossings_ray p r) / 2.
```

This combinatorial form works under generic-position
(no-vertex-on-ray) preconditions.  In effect it just reduces back to
the crossing-number parity, providing no genuine progress for the
crossing → topological-interior bridge.

### Missing piece

Either (a) Coquelicot or `mathcomp-analysis` import (axiom
allowlist expansion) for `atan2`, or (b) a hand-rolled `atan2` over
Stdlib via `Ratan` and quadrant case-splitting (~1 session).

### Cost to close

Definition only: 1-2 sessions for option (b).  Bridge to topology:
still gated by Seam 5/6 of the seam map (thesis-scale).

---

## Seam 6 — Ray-degenerate-safe characterisation

### Statement

```coq
Definition no_horizontal_edge_at (p : Point) (r : Ring) : Prop :=
  Forall (fun e : Edge => py (fst e) <> py (snd e)) (ring_edges r).

Lemma no_horizontal_edge_at_implies_bool_matches_prop :
  forall (p : Point) (e : Edge),
    py (fst e) <> py (snd e) ->
    let '(A, B) := e in
    segment_crosses_ray p A B = true <-> edge_crosses_ray p (A, B).
```

### Outcome

**Qed** on the per-edge agreement lemma.

`no_horizontal_edge_at` definition lands.  The simpler per-edge
bool/Prop agreement is a direct corollary of
`segment_crosses_ray_matches_edge_crosses_ray`.

### What does NOT close

The list-level lemma: `no_horizontal_edge_at p r -> point_in_ring p r
<-> Nat.odd (count_crossings_ray p r) = true`.  Same stuck point as
Seam 2 — fold_left accumulator parity vs mutual inductive.

### Missing piece

Same as Seam 2: fold-vs-mutual-inductive bridge.

### Cost to close

1 session (joint closure with Seam 2).

---

## Seam 7 — `segment_crosses_ray` agrees with `cross_R_pt`

### Statement

```coq
Lemma segment_crosses_ray_implies_cross_R_pt :
  forall (P A B : Point),
    segment_crosses_ray P A B = true ->
    ( (py A < py P < py B /\ 0 < cross_R_pt P A B) \/
      (py B < py P < py A /\ cross_R_pt P A B < 0) ).
```

### Outcome

**Qed** on the forward direction.

Companion lemma `segment_crosses_ray_non_horizontal` (bool firing
implies `py A <> py B`) closes in 8 lines via tactic-driven
destructuring.

### What does NOT close

The full biconditional (reverse direction: cross-product sign +
y-straddle implies bool fires).  Reverse direction requires
algebraic re-derivation via `field_simplify`; its denominator-
nonvanishing side conditions interact poorly with the bool case-
split.  Several attempts via `Rmult_lt_reg_r` + `field_simplify`
produced `Found no subterm matching` errors mid-tactic.

### Missing piece

The reverse-direction algebra.  Hand-rolled proof rearranging
`cross_R_pt P A B * sign(py B - py A) > 0` into `px A + t * (px B -
px A) > px P` with explicit denominator hypotheses, instead of
`field_simplify`.

### Cost to close

½ session (2-3 hours of careful algebra in two case branches).

---

## Summary

| Seam | Outcome | Cost-to-close (delta) |
|------|---------|----------------------|
| 1: `segment_crosses_ray_correct`        | **Qed** | — |
| 2: `count_crossings_ray` ↔ `point_in_ring` | Partial (defn + per-edge Qed; list-level stuck) | 1 session |
| 3: `geometric_interior` via fourcolor   | Stuck (Real.structure bridge) | 2-3 sessions |
| 4: `point_in_ring_correct_conditional`  | **Qed (vacuous)** | — (gated by Seam 3) |
| 5: `winding_number` definition          | Stuck (atan2 / Coquelicot) | 1-2 sessions |
| 6: `no_horizontal_edge_at` per-edge     | **Qed** (per-edge only) | 1 session (list-level, joint with Seam 2) |
| 7: cross_R_pt forward direction         | **Qed** (forward only) | ½ session (reverse direction) |

**Qed-closed Coq results landed:**

  - `Rlt_b` + iff lemmas (local infrastructure).
  - `segment_crosses_ray` (bool) + `segment_crosses_ray_sound` +
    `segment_crosses_ray_complete` + `segment_crosses_ray_correct`.
  - `segment_crosses_ray_matches_edge_crosses_ray` (bool ↔ Prop
    under non-horizontal precondition).
  - `count_crossings_ray` (definition).
  - `segment_crosses_ray_non_horizontal` (bool firing implies
    non-horizontal segment).
  - `point_in_ring_correct_conditional` (vacuous, records shape).
  - `no_horizontal_edge_at` (definition) +
    `no_horizontal_edge_at_implies_bool_matches_prop`.
  - `segment_crosses_ray_implies_right`.
  - `segment_crosses_ray_implies_cross_R_pt` (forward direction).

**Tractable next steps (Qed-able in 1-2 sessions each, no JCT
dependency):**

  - Seam 2/6 joint closure: fold ↔ mutual inductive bridge.
  - Seam 7 reverse direction: hand-rolled algebra.
  - Coquelicot import OR hand-rolled `atan2` for Seam 5.

**Library-gated next steps:**

  - Seam 3: `Real.structure` instance for Stdlib `R` (2-3 sessions).
  - Once that lands, Seam 4 becomes non-vacuous.

**Thesis-scale next steps (unchanged from `docs/point-in-ring-
correct-seam-map.md`):**

  - Jordan curve theorem for simple polygons.
  - Bounded-component identification once JCT delivers two
    components.

**Audit footprint.**  `theories/PointInRingCorrect.v` pulls only
README-allowlisted axioms (`sig_forall_dec`,
`functional_extensionality_dep`) -- importantly, NO
`Classical_Prop.classic` because none of the Qed-closed theorems
reference the snap layer.  File NOT listed in
`docs/audit-exceptions.txt`.  No Admitteds added.
