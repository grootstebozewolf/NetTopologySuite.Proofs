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

Theorem point_in_ring_eq_parity :
  forall (p : Point) (r : Ring),
    no_horizontal_edge_at p r ->
    point_in_ring p r <-> Nat.odd (count_crossings_ray p r) = true.
```

### Outcome

**Qed** under the `no_horizontal_edge_at` precondition.  Bridge lemma
`ray_parity_fold_bridge` closes; `point_in_ring_eq_parity` and
`point_outside_ring_eq_even_parity` follow as direct corollaries.

### How it landed

Three supporting lemmas:

  - `count_aux p l acc` — auxiliary `fold_left`-with-accumulator
    helper.
  - `count_aux_acc` — accumulator generalisation:
    `count_aux p l acc = (acc + count_aux p l 0)%nat`.
  - `count_aux_cons` — cons-form: `count_aux p ((A,B)::l) 0` is
    `S (count_aux p l 0)` or `count_aux p l 0` per bool firing.

Then the bridge:

```coq
Lemma ray_parity_fold_bridge :
  forall (p : Point) (edges : list Edge),
    Forall (fun e => py (fst e) <> py (snd e)) edges ->
    (ray_parity_odd  p edges <-> Nat.odd  (count_aux p edges 0%nat) = true) /\
    (ray_parity_even p edges <-> Nat.even (count_aux p edges 0%nat) = true).
```

Stated as a conjunction so the odd-half and even-half IHs are
simultaneously available at each induction step.  Proof uses
`Nat.odd_succ` + `Nat.even_succ` for the parity flip on the
crossing branch, and the §2 per-edge `segment_crosses_ray_matches_
edge_crosses_ray` to bridge between bool case-split and Prop
constructor application.

### Note on the precondition

The `no_horizontal_edge_at` (= `Forall ... py (fst e) <> py (snd e)`)
precondition is essential: the per-edge bool/Prop agreement
(`segment_crosses_ray_matches_edge_crosses_ray`) only holds under
non-horizontality.  This is the generic-position convention, also
required by Seam 6 — the two seams close as one bridge with this
precondition baked in.

### Cost to close

Closed.  ~80 lines including the helper lemmas and accumulator
generalisation.

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

Theorem point_outside_ring_eq_even_parity :
  forall (p : Point) (r : Ring),
    no_horizontal_edge_at p r ->
    ray_parity_even p (ring_edges r) <->
    Nat.even (count_crossings_ray p r) = true.
```

### Outcome

**Qed** — `no_horizontal_edge_at` definition lands AND the list-level
even-parity dual (outside-the-ring side) closes as a direct corollary
of `ray_parity_fold_bridge` (the same bridge that closes Seam 2).

### How it landed

Seam 6's list-level conclusion is the dual of Seam 2 — the same
bridge gives both the odd characterisation (`point_in_ring_eq_parity`)
and the even characterisation (`point_outside_ring_eq_even_parity`).
The `no_horizontal_edge_at` precondition is exactly the
`Forall (py (fst e) <> py (snd e)) (ring_edges r)` shape the
bridge requires.

### Cost to close

Closed jointly with Seam 2 — same bridge lemma serves both.

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
| 2: `count_crossings_ray` ↔ `point_in_ring` (list-level) | **Qed** (under `no_horizontal_edge_at`) | — |
| 3: `geometric_interior` via fourcolor   | Stuck (Real.structure bridge) | 2-3 sessions |
| 4: `point_in_ring_correct_conditional`  | **Qed (vacuous)** | — (gated by Seam 3) |
| 5: `winding_number` definition          | Stuck (atan2 / Coquelicot) | 1-2 sessions |
| 6: `no_horizontal_edge_at` (list-level) | **Qed** (joint with Seam 2) | — |
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
  - `no_horizontal_edge_at` (definition).
  - `count_aux` + `count_aux_acc` + `count_aux_cons` (fold-left
    accumulator helpers).
  - `ray_parity_fold_bridge` — the load-bearing fold ↔ mutual
    inductive bridge under `Forall (py (fst e) <> py (snd e))`.
  - `point_in_ring_eq_parity` — list-level Seam 2 corollary.
  - `point_outside_ring_eq_even_parity` — list-level Seam 6
    corollary (even-parity dual).
  - `segment_crosses_ray_implies_right`.
  - `segment_crosses_ray_implies_cross_R_pt` (forward direction).

**Tractable next steps (Qed-able in 1-2 sessions each, no JCT
dependency):**

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
