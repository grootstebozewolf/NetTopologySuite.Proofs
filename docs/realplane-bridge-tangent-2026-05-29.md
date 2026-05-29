# realplane bridge — tangent stop

**Session goal.**  Internalise the H1 (JCT) hypothesis in
`overlay_ng_correct_conditional` (Phase 3 M5 S15) using fourcolor's
`realplane.region` machinery.  Replace the opaque Section-scoped
`Variable geometric_interior : Point -> Ring -> Prop` with a concrete
topological definition.

**Outcome.**  **TANGENT STOP** — two structural problems compounded.
The prompt anticipated one (real-number framework mismatch); the
other (`realplane.region` is not the right shape) surfaced during the
grep audit.  No `.v` files modified; no Admitteds introduced.

This document records the structural mismatch so a future session
can resume with the correct architecture.

---

## §1 — What was expected

The session prompt's target was a thin bridge:

```coq
(* PROMPT'S TARGET *)
From fourcolor Require Import realplane.

Definition point_to_rplane (p : Point) : realplane.point := ...
Definition ring_to_realplane_curve (r : Ring) : realplane.curve := ...
Definition geometric_interior (p : Point) (r : Ring) : Prop :=
  realplane.region
    (ring_to_realplane_curve r)
    (point_to_rplane p).
```

The assumption: `realplane.region : curve -> point -> Prop`, a
predicate that says "point p is inside the region bounded by curve c."

---

## §2 — What realplane actually provides

From `~/.opam/nts-flocq/lib/coq/user-contrib/fourcolor/proof/realplane.v`:

```coq
Section Definitions.
Variable R : Real.structure.   (* ← fourcolor's abstract reals *)

Inductive point : Type := Point (x y : Real.val R).
Definition region : Type := point -> Prop.    (* ← unary indicator *)
Definition map : Type := point -> region.     (* binary -- maps, not curves *)

Definition open (r : region) : Prop := ...
Definition closure (r : region) : region := ...
Definition connected (r : region) : Prop := ...
Definition subregion (r1 r2 : region) : Prop := ...
Definition meet (r1 r2 : region) : Prop := ...

Record simple_map (m : map) : Prop := SimpleMap { ... }.
Definition border (m : map) (z1 z2 : point) : region := ...
Definition adjacent (m : map) (z1 z2 : point) : Prop := ...

End Definitions.
```

Two structural surprises:

  1. **`region` is unary**: `point -> Prop`.  Not a relation between
     a curve and a point.  There is no `region : curve -> point ->
     Prop` form anywhere in realplane.v.

  2. **No curve type**: realplane.v has `point`, `region`, `map`
     (relations on points), `interval`, `rectangle`, and `simple_map`
     (PERs on points), but NO simple closed curve, NO polygon, and
     NO "interior of a closed curve" predicate.

The realplane API is a **topology vocabulary** for stating coloring
problems on planar maps, not a Jordan-curve-theorem library.

---

## §3 — The real-number framework gate (the prompt anticipated this)

```coq
From fourcolor Require Import real.      (* not Stdlib Reals *)

Module Real.
  Record structure : Type := Structure {
    val : Type;
    le : rel; sup : set -> val;
    add : val -> val -> val; zero : val; opp : val -> val;
    mul : val -> val -> val; one : val; inv : val -> val
  }.
  Record axioms R : Prop := Axioms { ... 11 axioms ... }.
  Record model : Type := Model { ... }.
End Real.
```

realplane operates over `Real.val R` for an abstract `R :
Real.structure`.  The corpus operates over Stdlib `Reals.R`.

**Bridging requires**:

  1. Construct a `Real.structure` with `val := R` (the corpus's R).
  2. Provide the 11 fields (`le := Rle`, `sup := Rsup`, `add := Rplus`,
     etc.).
  3. Prove `Real.axioms` (Dedekind completeness via Stdlib's
     `Rcomplete`, sup_upper_bound, sup_total, the arithmetic axioms).
  4. Upgrade to `Real.model` if any consumer requires it.

Step 3 is the load-bearing piece.  Stdlib R *has* Dedekind
completeness (`completeness : forall E : R -> Prop, bound E ->
(exists x, E x) -> { m : R | is_lub E m }`) but threading it through
fourcolor's `Real.axioms` record requires reformulating each axiom.

Estimated scope: 2-3 sessions for a complete bridge, ~150 lines of
Coq.  Not feasible inline with H1 internalisation.

---

## §4 — Why "internalise H1" needs more than these two bridges

Even with both problems solved (Stdlib R bridged to `Real.structure`,
type translations defined), realplane's API does NOT provide the
predicate we need.

The target H1 statement is:

> Given a closed simple ring `r` (a polygon), `point_in_ring p r =
> true` iff `p` is in the bounded interior of the region enclosed
> by `r`.

realplane gives us `open`, `closure`, `connected`, `simple_map`,
`border`.  To construct "bounded interior of the region enclosed by
ring r", you'd need to:

  1. Define a `region` `boundary_of(r) : point -> Prop` for the
     polygonal boundary (union of line-segment indicators).
  2. Define `complement_of(boundary_of(r)) : region`.
  3. Establish that the complement decomposes into connected
     components (this needs JCT-flavored reasoning itself).
  4. Pick the bounded component.
  5. Define `geometric_interior p r := <bounded component> p`.

Steps 3-4 are JCT-shaped reasoning, not just topology vocabulary.
realplane.v's `connected` predicate is a definition, not a theorem
about polygon complements.

The fundamental issue: **realplane is plumbing for stating the four
color theorem, not infrastructure for proving JCT for polygons**.

---

## §5 — Three fallback paths

### Option F1 — Stdlib-R internalisation (skip fourcolor)

Define `geometric_interior` directly in Stdlib R + corpus's `Point`,
expressing "bounded component of R² \ |∂r|" via Stdlib primitives.

  - Builds planar topology (open balls, connectedness, complement)
    in Stdlib R from scratch.
  - All in the corpus's existing framework; no foreign-library
    interaction.
  - Cost: ~3-5 sessions.

### Option F2 — Two-stage bridge (use fourcolor)

  - Session A (~2-3 sessions): "Stdlib R → fourcolor `Real.structure`"
    bridge.  Construct the instance + axiom proofs.
  - Session B (~1-2 sessions): Build polygon-interior predicate from
    realplane's topology primitives.
  - Session C (the original H1 session, ~1 session): wire
    `geometric_interior` to the constructed predicate.
  - Total: ~4-6 sessions.

  Buys: a reusable Stdlib-R-to-fourcolor bridge that future DCEL work
  can also leverage.

### Option F3 — Ship S15 as originally designed (no internalisation)

  - The Phase 3 conditional theorem (PR #41) uses a Section-scoped
    `Variable geometric_interior`.  This is epistemically honest:
    the gap is named, the conditional theorem is Qed-closed, no
    axiom pollution.
  - The "concrete topology, stronger statement" benefit is real but
    incremental; it doesn't change the deferred-proof status of
    `point_in_ring_correct`.
  - Cost: 0 additional sessions.

---

## §6 — Recommendation

**Option F3** (ship S15 as designed) is the right move for this
phase.  Rationale:

  - The conditional theorem with an opaque Variable is structurally
    equivalent to one with a concrete predicate, from the corpus's
    epistemic standpoint.  Both leave `point_in_ring_correct`
    deferred.

  - Options F1 and F2 are 3-6 sessions of topology infrastructure
    work.  If we're investing that much, the better target is
    **Option F2's session B applied to JCT itself** — define the
    predicate AND prove the JCT for simple polygons.  But that's the
    full thesis-scale piece the audit doc anticipated.

  - The fourcolor install + this audit IS a valuable side-result.
    The reproducible network workaround (PR #42, §0) opens the
    ecosystem.  The internalisation can be revisited as part of the
    eventual JCT session (whenever the budget appears).

If a future session wants F1 or F2 anyway, the design here is the
checkpoint: **the load-bearing work is not the bridge but the JCT
itself**.  Don't budget less than 5 sessions for a full closure.

---

## §7 — What this session produced

  - This document (`docs/realplane-bridge-tangent-2026-05-29.md`).
  - No `.v` changes.
  - No Admitteds added.
  - The branch `ecosystem/realplane-bridge` records the structural
    finding.

`ecosystem/library-search` (PR #42) remains the primary ecosystem
audit doc; this file complements it with the specific H1
internalisation analysis.
