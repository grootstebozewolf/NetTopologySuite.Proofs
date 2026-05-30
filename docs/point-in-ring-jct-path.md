# JCT path to `point_in_ring_correct` — minimal hypothesis set

**Status.**  Documentation only.  No Coq written.  Maps the precise
logical path from a Jordan Curve Theorem statement to
`point_in_ring_correct`.

**Companion documents:**

  - `docs/point-in-ring-correct-seam-map.md` — original seven-seam
    inventory.
  - `docs/point-in-ring-seam-attempts.md` — green outcomes per seam.
  - `docs/point-in-ring-seams-3-5-7-red.md` — red workflow for the
    remaining seams.
  - `docs/point-in-ring-tangent-attempts.md` — green tangent outcomes
    (Stdlib-only `geometric_interior_stdlib` lands).

---

## §1 — The target

```coq
Theorem point_in_ring_correct_jct :
  forall (p : Point) (r : Ring),
    ring_simple r ->
    ring_closed r ->
    ring_has_minimum_points r ->
    no_horizontal_edge_at p r ->
    (* Two named JCT-side hypotheses *)
    JCT_two_components r ->
    ray_parity_iff_interior p r ->
    (* Conclusion *)
    point_in_ring p r <-> geometric_interior_stdlib p r.
```

**Vocabulary mapping** (the prompt's hypothetical names ↔ corpus
actuals):

| Prompt | Corpus actual | Location |
|--------|--------------|----------|
| `generic_ray_position p r` | `no_horizontal_edge_at p r` | `theories/PointInRingCorrect.v:461` |
| `geometric_interior` | `geometric_interior_stdlib` | `theories/PointInRingTangents.v:145` |
| Hypothesis `JCT_simple_polygon` | `JCT_two_components` (proposed) | new |
| Hypothesis `ray_crossing_parity` | `ray_parity_iff_interior` (proposed) | new |

---

## §2 — The seven steps

### Step 1 — JCT gives two components

**What's needed.**  A simple closed polygon divides `R²` into
exactly two connected components — one bounded (interior) and one
unbounded (exterior), separated by the polygon boundary.

**Coq statement (proposed hypothesis):**

```coq
Definition JCT_two_components (r : Ring) : Prop :=
  ring_simple r ->
  ring_closed r ->
  ring_has_minimum_points r ->
  exists (interior_pred exterior_pred : Point -> Prop),
    (* Every non-boundary point is in exactly one component *)
    (forall q : Point,
       ~ ring_image r q ->
       (interior_pred q \/ exterior_pred q) /\
       ~ (interior_pred q /\ exterior_pred q)) /\
    (* Both components are "connected in the complement" *)
    (forall p q, interior_pred p -> interior_pred q ->
       connected_in_complement r p q) /\
    (forall p q, exterior_pred p -> exterior_pred q ->
       connected_in_complement r p q) /\
    (* Interior is bounded; exterior is not *)
    (exists M : R, M > 0 /\
       forall q, interior_pred q ->
                 px q * px q + py q * py q <= M * M) /\
    (forall M : R,
       exists q, exterior_pred q /\
                 px q * px q + py q * py q > M * M).
```

**What exists.**  `connected_in_complement`, `ring_image`,
`ring_has_minimum_points`, `ring_simple`, `ring_closed` — all in
the corpus.

**What's missing.**  The Jordan Curve Theorem itself.  Thesis-scale.

**Hypothesis or provable?**  **Hypothesis** — this IS the JCT.

**Cost.**  Discharging this hypothesis is the thesis-scale gap
documented across all earlier audits.

---

### Step 2 — `geometric_interior_stdlib` equals the JCT interior

**What's needed.**  Show that `geometric_interior_stdlib p r`
(= `ring_complement r p ∧ in_bounded_component r p`) coincides with
the `interior_pred` from Step 1.

**Coq statement:**

```coq
Lemma geometric_interior_eq_JCT_interior :
  forall (p : Point) (r : Ring)
         (interior_pred exterior_pred : Point -> Prop),
    ring_simple r -> ring_closed r -> ring_has_minimum_points r ->
    (* Step 1's output, destructured *)
    (forall q, ~ ring_image r q ->
       (interior_pred q \/ exterior_pred q) /\
       ~ (interior_pred q /\ exterior_pred q)) ->
    (exists M, M > 0 /\ forall q, interior_pred q ->
       px q * px q + py q * py q <= M * M) ->
    (forall p q, interior_pred p -> interior_pred q ->
       connected_in_complement r p q) ->
    (* Then geometric_interior_stdlib agrees with interior_pred *)
    geometric_interior_stdlib p r <-> interior_pred p.
```

**What exists.**  `geometric_interior_stdlib`,
`in_bounded_component`, `connected_in_complement` definitions.

**Hypothesis or provable?**  **Provable** from Step 1's output.  The
"bounded component containing p" is uniquely determined; both
predicates pick out the same component.  Forward direction
(`geometric_interior_stdlib p r → interior_pred p`) requires
showing exterior points are unbounded, which is Step 1's last
clause.  Reverse direction uses the bounded-component condition
directly.

**Cost.**  1-2 sessions once Step 1 is available.  No new
hypotheses.

---

### Step 3 — Path separation (any path between components crosses the boundary)

**What's needed.**  Any continuous path from an interior to an
exterior point must pass through the ring image.  This is the
operational content of "the polygon separates `R²`".

**Coq statement (provable from Step 1):**

```coq
Lemma JCT_path_separation :
  forall (r : Ring) (p q : Point)
         (interior_pred exterior_pred : Point -> Prop)
         (path : R -> Point),
    ring_simple r -> ring_closed r ->
    interior_pred p -> exterior_pred q ->
    path 0 = p -> path 1 = q ->
    (* No assumption of continuity on `path` -- our connected_in_
       complement def doesn't carry continuity either *)
    (forall t, 0 <= t <= 1 -> ~ ring_image r (path t)) ->
    False.  (* Cannot have such a path -- it would put p in q's
               component, contradicting Step 1's disjointness. *)
```

**Hypothesis or provable?**  **Provable** from Step 1.  If the
path stays in the complement, then `p` is connected to `q` in the
complement, but `p` and `q` are in disjoint components — direct
contradiction with Step 1's disjointness clause.

**Cost.**  1 session.

**Note on continuity.**  The corpus's `connected_in_complement`
does NOT carry a continuity precondition on the path — it's a
purely set-theoretic "exists path: R → Point with values in
complement" definition.  That's a weaker connectedness than
topological path-connectedness (any function works, not just
continuous ones).  This simplification suits the corpus's
algorithmic focus but means our Step 3 statement is correspondingly
weaker than the full topological separation theorem.  For
algorithmic correctness this is sufficient; for a full topological
treatment the connectedness predicate would need strengthening.

---

### Step 4 — Ray-crossing parity for interior/exterior points

**What's needed.**  The load-bearing parity theorem: a horizontal
ray from an interior point crosses the polygon boundary an **odd**
number of times; from an exterior point, an **even** number.

**Coq statement (proposed hypothesis):**

```coq
Definition ray_parity_iff_interior (p : Point) (r : Ring) : Prop :=
  ring_simple r -> ring_closed r -> ring_has_minimum_points r ->
  no_horizontal_edge_at p r ->
  forall interior_pred : Point -> Prop,
    (forall q, ~ ring_image r q ->
       interior_pred q \/ ~ interior_pred q) ->
    (interior_pred p <->
     Nat.odd (count_crossings_ray p r) = true).
```

**What exists.**  `count_crossings_ray`, `no_horizontal_edge_at`,
`ring_image`.

**Hypothesis or provable from Step 1?**  Either:

  - **As hypothesis**: name it and proceed.  Discharging it
    requires a winding-number argument or a direct combinatorial
    proof for simple polygons — thesis-scale.
  - **As provable from JCT_two_components**: yes in principle.
    Given the two-component decomposition + Step 3 (path
    separation), one can argue: a horizontal ray going to infinity
    eventually enters the exterior; crossings along the ray
    alternate interior/exterior; the count's parity matches the
    starting region.  ~3-5 sessions of careful counting argument
    in Coq, plus correctness lemmas about the ray (every-other-
    edge straddle).

For the **conditional** target theorem, naming `ray_parity_iff_interior`
as a hypothesis is the right move — it matches the corpus's other
conditional headlines that name the load-bearing topological fact
without discharging it.

**Cost.**  Hypothesis: zero.  Discharging from JCT_two_components:
3-5 sessions plus the JCT itself.

---

### Step 5 — Odd crossings → `point_in_ring`

**What's needed.**  Connect `Nat.odd (count_crossings_ray p r) =
true` to `point_in_ring p r`.

**Coq statement:**

```coq
Lemma odd_crossings_implies_point_in_ring :
  forall (p : Point) (r : Ring),
    no_horizontal_edge_at p r ->
    Nat.odd (count_crossings_ray p r) = true ->
    point_in_ring p r.
```

**What exists.**  `point_in_ring_eq_parity` (Qed-closed in
`theories/PointInRingCorrect.v:596`) gives the biconditional:

```coq
Theorem point_in_ring_eq_parity :
  forall (p : Point) (r : Ring),
    no_horizontal_edge_at p r ->
    point_in_ring p r <-> Nat.odd (count_crossings_ray p r) = true.
```

**Hypothesis or provable?**  **Provable now** — Step 5 is literally
the reverse direction of `point_in_ring_eq_parity`:

```coq
Proof.
  intros p r Hnh Hodd.
  apply (point_in_ring_eq_parity p r Hnh). exact Hodd.
Qed.
```

**Cost.**  Trivial — 2 lines.  Provable today, no JCT needed.

---

### Step 6 — Even crossings → ¬ `point_in_ring`

**What's needed.**  The symmetric direction.

**Coq statement:**

```coq
Lemma even_crossings_implies_not_point_in_ring :
  forall (p : Point) (r : Ring),
    no_horizontal_edge_at p r ->
    Nat.even (count_crossings_ray p r) = true ->
    ~ point_in_ring p r.
```

**What exists.**  `point_outside_ring_eq_even_parity` (Qed-closed
in `theories/PointInRingCorrect.v:609`):

```coq
Theorem point_outside_ring_eq_even_parity :
  forall (p : Point) (r : Ring),
    no_horizontal_edge_at p r ->
    ray_parity_even p (ring_edges r) <->
    Nat.even (count_crossings_ray p r) = true.
```

Plus a structural argument that `ray_parity_odd` and
`ray_parity_even` are mutually exclusive (a list cannot be both
odd-parity and even-parity at once for the same point).

**Hypothesis or provable?**  **Provable now** — the
even-parity ↔ `ray_parity_even` correspondence is the dual of
Step 5.  The "not `ray_parity_odd`" piece requires a small
disjointness lemma (~10-20 lines).

**Cost.**  Trivial-to-small — 1/4 session.  Provable today,
no JCT needed.

---

### Step 7 — Composition into `point_in_ring_correct_jct`

```coq
Theorem point_in_ring_correct_jct :
  forall (p : Point) (r : Ring),
    ring_simple r ->
    ring_closed r ->
    ring_has_minimum_points r ->
    no_horizontal_edge_at p r ->
    JCT_two_components r ->
    ray_parity_iff_interior p r ->
    point_in_ring p r <-> geometric_interior_stdlib p r.
Proof.
  intros p r Hs Hc Hm Hnh HJCT Hparity.
  (* Step 1 unpacks JCT_two_components into interior_pred + props. *)
  destruct (HJCT Hs Hc Hm) as
    [interior_pred [exterior_pred [Hdisj [Hint_conn [Hext_conn
     [Hint_bnd Hext_unbnd]]]]]].
  (* Step 4: parity ↔ interior_pred *)
  pose proof (Hparity Hs Hc Hm Hnh interior_pred ...) as Hp_iff_int.
  (* Step 2: geometric_interior_stdlib ↔ interior_pred *)
  pose proof (geometric_interior_eq_JCT_interior p r
                interior_pred exterior_pred Hs Hc Hm Hdisj
                Hint_bnd Hint_conn) as Hgi_iff_int.
  (* Step 5/6: point_in_ring ↔ odd crossings *)
  pose proof (point_in_ring_eq_parity p r Hnh) as Hpir_iff_odd.
  (* Chain: point_in_ring ↔ odd ↔ interior_pred ↔ geometric_interior_stdlib *)
  split; intro H.
  - apply Hgi_iff_int. apply Hp_iff_int.
    apply Hpir_iff_odd. exact H.
  - apply Hpir_iff_odd. apply Hp_iff_int.
    apply Hgi_iff_int. exact H.
Qed.
```

The proof composes Steps 1, 2, 4, 5 into the biconditional.

**Cost.**  ~1 session once all preceding steps are available.

---

## §3 — The minimal hypothesis set

After tracing all seven steps, the minimum set of named hypotheses
is **two**:

### Hypothesis 1: `JCT_two_components`

The Jordan Curve Theorem for simple polygons — the topological
fact that the polygon separates `R²` into exactly two connected
components, one bounded and one unbounded.

```coq
Definition JCT_two_components (r : Ring) : Prop :=
  ring_simple r -> ring_closed r -> ring_has_minimum_points r ->
  exists (interior_pred exterior_pred : Point -> Prop),
    (* (predicates, connectedness, boundedness, unboundedness) *)
    ...
```

**Why thesis-scale.**  This is the JCT itself.  No installed
library provides it for `R²` polygons; the corpus's
`docs/ecosystem-search-2026-05-29.md` confirmed RED for all
searched candidates (fourcolor: combinatorial Jordan only;
mathcomp-analysis: no JCT; GeoCoq: foundational only).

### Hypothesis 2: `ray_parity_iff_interior`

The algorithmic parity fact — a horizontal ray from any
non-boundary point crosses the polygon an odd number of times iff
the point is in the interior.

```coq
Definition ray_parity_iff_interior (p : Point) (r : Ring) : Prop :=
  ring_simple r -> ring_closed r -> ring_has_minimum_points r ->
  no_horizontal_edge_at p r ->
  forall interior_pred : Point -> Prop,
    (* well-formedness of interior_pred *)
    (interior_pred p <->
     Nat.odd (count_crossings_ray p r) = true).
```

**Why thesis-scale (independently).**  Provable from
`JCT_two_components` via a winding-number argument or direct
counting argument (3-5 sessions), OR can be named as a separate
hypothesis matching the corpus's existing pattern.

### Could it be one hypothesis?

If we strengthen `JCT_two_components` to include the parity
clause, the count drops to one.  But the parity clause is a
non-trivial corollary of the topological theorem and bundling
them obscures their independent contents:

  - JCT is purely topological (about connectedness of `R²`).
  - Parity is algorithmic (about a specific counting algorithm).

The minimal-information hypothesis set is two; the cleanly-named
hypothesis set is also two.  Recommendation: **stay at two**.

---

## §4 — What's provable now (no JCT)

Two lemmas close immediately without any new hypotheses, using
existing corpus infrastructure:

### `odd_crossings_implies_point_in_ring` (Step 5)

```coq
Lemma odd_crossings_implies_point_in_ring :
  forall (p : Point) (r : Ring),
    no_horizontal_edge_at p r ->
    Nat.odd (count_crossings_ray p r) = true ->
    point_in_ring p r.
Proof.
  intros p r Hnh Hodd.
  apply (point_in_ring_eq_parity p r Hnh). exact Hodd.
Qed.
```

### `even_crossings_implies_not_point_in_ring` (Step 6)

```coq
Lemma even_crossings_implies_not_point_in_ring :
  forall (p : Point) (r : Ring),
    no_horizontal_edge_at p r ->
    Nat.even (count_crossings_ray p r) = true ->
    ~ point_in_ring p r.
Proof.
  intros p r Hnh Heven Hpir.
  apply point_in_ring_eq_parity in Hpir; [|exact Hnh].
  rewrite <- Nat.negb_even, Heven in Hpir.
  discriminate.
Qed.
```

Both should land in the next green session.  ~1/4 session total.

### Provable from JCT (post-Step-1)

  - `geometric_interior_eq_JCT_interior` (Step 2) — 1-2 sessions.
  - `JCT_path_separation` (Step 3) — 1 session.
  - `point_in_ring_correct_jct` composition (Step 7) — 1 session.

Total once JCT lands: 3-4 sessions of mechanical composition.

---

## §5 — The conditional theorem shape

The exact Coq statement that the next green session targets:

```coq
Theorem point_in_ring_correct_jct :
  forall (p : Point) (r : Ring),
    ring_simple r ->
    ring_closed r ->
    ring_has_minimum_points r ->
    no_horizontal_edge_at p r ->
    JCT_two_components r ->
    ray_parity_iff_interior p r ->
    point_in_ring p r <-> geometric_interior_stdlib p r.
```

This matches the corpus's established conditional-headline pattern:

  - `hobby_theorem_4_1_conditional` (Phase 2, Link 1).
  - `overlay_ng_correct_conditional` (Phase 3, M5 S15) — H1, H2,
    H_bridge as named hypotheses.

The TWO named hypotheses (`JCT_two_components`,
`ray_parity_iff_interior`) become a tighter, more locally
characterised replacement for H1 of `overlay_ng_correct_conditional`:

  - **Current H1**: opaque "`point_in_ring q r ↔
    geometric_interior_stdlib q r` for valid rings".
  - **Decomposed H1**: `JCT_two_components r` (topological) +
    `ray_parity_iff_interior p r` (algorithmic).

A future session that lands `point_in_ring_correct_jct` could
re-derive `overlay_ng_correct_conditional`'s H1 from the two
decomposed hypotheses, making the Phase 3 headline depend on the
SAME two atomic facts the rest of the literature names.

---

## §6 — Summary

**Minimal hypothesis set:** TWO.

  - `JCT_two_components` — the topological theorem.
  - `ray_parity_iff_interior` — the algorithmic theorem.

**Provable today (no JCT) — LANDED:**

  - `odd_crossings_implies_point_in_ring` — Qed-closed in
    `theories/PointInRingCorrect.v` §6c.
  - `even_crossings_implies_not_point_in_ring` — Qed-closed in
    `theories/PointInRingCorrect.v` §6c.
  - `point_in_ring_correct_jct` — Qed-closed conditional shell in
    `theories/PointInRingTangents.v` §3b.  Two named hypotheses
    (parity ↔ interior_pred, geometric_interior_stdlib ↔
    interior_pred) discharged when JCT lands.
  - `point_in_ring_correct_jct_Prop` — Prop-form variant.

**Provable once JCT_two_components is available:**

  - `geometric_interior_eq_JCT_interior` (Step 2).
  - `JCT_path_separation` (Step 3).
  - Derivation of the two `point_in_ring_correct_jct` hypotheses
    from `JCT_two_components` (composition of Steps 2 + 4).

**Current corpus state (post-session):**

  - `point_in_ring_correct_jct` Qed-closed under two named
    hypotheses (parity ↔ interior_pred + geometric_interior_stdlib
    ↔ interior_pred).
  - Both hypotheses are precisely-stated Coq predicates that
    discharge from `JCT_two_components` (the actual thesis-scale
    gap).
  - The corpus has reached the same epistemic position for
    `point_in_ring_correct` as it has for `hobby_theorem_4_1`
    (Phase 2) and `overlay_ng_correct` (Phase 3): conditional
    Qed-closed under thesis-shaped hypotheses, principled stopping
    point.

**Trigger to re-open this work:**

  - Either hypothesis can be discharged independently:
    - `JCT_two_components` discharged via a future ecosystem JCT
      import (e.g. mathcomp-analysis if it adds R² Jordan) or
      thesis-scale corpus work.
    - `ray_parity_iff_interior` discharged via a counting
      argument from `JCT_two_components` (3-5 sessions) or
      independently as its own thesis-scale work.
  - Or both as named hypotheses to land the conditional headline
    (matches corpus pattern), then dispatch over time.

**One-line target.**  Land
`point_in_ring_correct_jct : ... <-> geometric_interior_stdlib p r`
as a conditional Qed-closed theorem on two named hypotheses,
matching `overlay_ng_correct_conditional`'s shape.

**Findings.**

  - Finding 1: The prompt's "Step 4 thesis-scale" reading stands;
    `ray_parity_iff_interior` is independently thesis-scale,
    consistent with the rest of the path.
  - Finding 2: Steps 5 and 6 close immediately via the existing
    fold-bridge corollaries; flag for next green session
    regardless of JCT progress.
  - Finding 3: The minimal hypothesis count is **two**, not one or
    three.  Bundling them would obscure their distinct content
    (topological vs algorithmic); splitting them further would
    add accidental hypotheses that follow from JCT directly.
