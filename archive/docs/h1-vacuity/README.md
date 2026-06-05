# H1 vacuity finding — the OverlayNG/buffer headline's JCT hypothesis is uninstantiable

**Status:** confirmed (mechanically, in Rocq 9.1.1).
**Scope:** `overlay_ng_correct_conditional` (`theories-flocq/OverlayCorrectness.v:86`)
and its buffer analogue target `buffer_correct_conditional`
(`docs/buffer-noder-pipeline.md:328`).
**Verification:** [`VacuityCheck.v`](VacuityCheck.v) + [`WitnessCheck.v`](WitnessCheck.v),
both `Qed`-closed; `Print Assumptions` shows only the Stdlib-Reals axioms
(`sig_forall_dec`, `functional_extensionality`) — **not** `Classical_Prop.classic`.

---

## The claim under review

> The OverlayNG/buffer headline's H1 hypothesis
> (`buffer-noder-pipeline.md:289`, `:342`) is stated as
> `point_in_ring q r <-> geometric_interior_stdlib q r` — so by
> `geometric_interior_stdlib_vacuous` that H1 forces `~ point_in_ring q r`
> for all rings, making `overlay_ng_correct_conditional` vacuous.

## Verdict: conclusion correct, mechanism misattributed

**The conclusion holds, and is in fact stronger than stated.** But the cited
mechanism is wrong on two counts, and the real reason is more interesting.

### 1. There is no `geometric_interior_stdlib_vacuous` lemma

No such lemma exists anywhere in the corpus (`grep -r vacuous` confirms). The
two genuine "not-in-interior" lemmas in `theories/PointInRingTangents.v` are:

| Lemma | What it actually says |
|---|---|
| `not_geometric_interior_on_edge` (`:151`) | a point **on a ring edge** is not in the interior |
| `not_geometric_interior_empty_ring` (`:174`) | the **empty** ring `[]` has no interior |

The second is presumably what the claim is reaching for — but it is restricted
to `r = []`, not "all rings." So as stated, the claim's load-bearing premise
does not exist.

### 2. …but `geometric_interior_stdlib` *is* provably false for **every** point and ring

The right general statement is true, and we proved it
([`VacuityCheck.v`](VacuityCheck.v)):

```coq
Theorem geometric_interior_stdlib_universally_false :
  forall (p : Point) (r : Ring), ~ geometric_interior_stdlib p r.
```

**Root cause — a modelling defect in `connected_in_complement`.**
`theories/PointInRingTangents.v:125-131`:

```coq
(* A continuous path between two points stays in the complement. ... *)
Definition connected_in_complement (r : Ring) (p q : Point) : Prop :=
  exists path : R -> Point,
    path 0 = p /\ path 1 = q /\
    forall t : R, 0 <= t <= 1 -> ring_complement r (path t).
```

The comment says *"a continuous path,"* but the definition imposes **no
continuity** on `path : R -> Point`. A discontinuous step path
`fun t => if t =? 1 then q else p` therefore links **any** off-ring `p` to
**any** off-ring `q`. So `connected_in_complement` collapses to "both points
are off the ring," and the notion of a *bounded connected component* degenerates:
the entire off-ring set becomes one "component."

Since a ring's edge skeleton is a finite union of bounded segments, the off-ring
set is unbounded — it contains points arbitrarily far from the origin. Hence the
`in_bounded_component` bound `M` can never hold, and
`geometric_interior_stdlib p r = ring_complement r p /\ in_bounded_component r p`
is satisfied by **no** point of **any** ring. (The corpus's own
`not_geometric_interior_empty_ring` is exactly the `r = []` special case of
this, proved with the same far-point technique.)

### 3. Therefore H1 forces `~ point_in_ring`, and is in fact *contradictory*

H1 (`OverlayCorrectness.v:95`, instantiated with the concrete predicate at S15):

```coq
forall q r, ring_closed r -> ring_simple r ->
  point_in_ring q r <-> geometric_interior_stdlib q r
```

Because the right side is universally `False`, H1 is logically equivalent to
"`~ point_in_ring q r` for every closed, simple ring"
([`VacuityCheck.v`], `H1_forces_not_point_in_ring`).

But `point_in_ring` is genuinely **inhabited** on closed, simple rings. We
exhibit a witness — the unit square with its centre
([`WitnessCheck.v`](WitnessCheck.v)):

```coq
Theorem point_in_ring_inhabited_on_closed_simple :
  exists (q : Point) (r : Ring),
    ring_closed r /\ ring_simple r /\ point_in_ring q r.
```

So H1 is not merely trivialising — it is **contradictory**. No caller can ever
supply a *true* H1. `overlay_ng_correct_conditional` is `Qed`-closed only
because its conclusion is reachable from a hypothesis that can never be
discharged: it is **vacuous / uninstantiable**, proving nothing about the actual
overlay algorithm.

The buffer target `buffer_correct_conditional`
(`docs/buffer-noder-pipeline.md:343`) carries the identical H1 shape ("shared
with overlay") and inherits the same defect verbatim.

## Why this slipped in

`OverlayCorrectness.v:63-69` records the S15 change: the *opaque* Section
Variable `geometric_interior : Point -> Ring -> Prop` was replaced by the
*concrete* `geometric_interior_stdlib`, on the reasoning that "the JCT gap
remains in the H1 biconditional's content (not in the definition itself)." That
is precisely the misstep: the concrete predicate is not an under-specified
stand-in for the topological interior — it is a predicate that happens to be
*identically false*, so instantiating H1 with it silently converted a faithful
conditional headline into a vacuous one.

## Resolution (applied)

The fix combines option 1 (continuity) at the definition level with a
re-pointing of the consuming headlines:

1. **Continuity-carrying definitions** landed in `theories/JordanCurveSeam.v`
   (PR #81): `connected_in_complement_cont` / `in_bounded_component_cont` /
   `geometric_interior_cont` require the connecting `path` to be continuous
   (`path_continuous`, via Stdlib `Ranalysis.continuity`).
   `far_points_connected_cont` shows the corrected relation is non-degenerate.
2. **The deferred JCT hypothesis was strengthened.** `JCT_two_components_cont`
   now carries a **separation clause** ("no continuous complement path links an
   interior point to an exterior one") — the trapped-interior half of the JCT.
   `jct_cont_interior_is_geometric` proves that *under* this hypothesis every
   interior point is a `geometric_interior_cont` point, i.e. the hypothesis is
   strong enough to discharge the seam. (This does **not** prove the JCT;
   `JCT_two_components_cont` remains an unproved `Prop`.)
3. **The OverlayNG/buffer headline H1 was re-pointed** off the (vacuous)
   `geometric_interior_stdlib` onto `geometric_interior_cont`, at all 6 sites in
   `theories-flocq/OverlayCorrectness.v` (the `overlay_ng_correct_conditional`
   headline + its forward/backward corollaries) and at the buffer target in
   `docs/buffer-noder-pipeline.md`. H1 is now a genuine, satisfiable —
   still-undischarged — JCT obligation rather than a contradiction. The
   headline's axiom footprint is unchanged (README allowlist + the snap layer's
   `Classical_Prop.classic`).

Verified under Rocq 9.1.1 + Flocq 4.2.2: `theories/JordanCurveSeam.v` and
`theories-flocq/OverlayCorrectness.vo` both build clean; the new
`jct_cont_interior_is_geometric` is axiom-clean (no `classic`).

## Reproduce

Build the Stdlib dependency chain and the two probe files (host fallback per
[`docs/development-environment.md`](../development-environment.md)):

```sh
eval $(opam env --switch=nts-flocq)
rocq c -Q theories NTS.Proofs docs/h1-vacuity/VacuityCheck.v
rocq c -Q theories NTS.Proofs docs/h1-vacuity/WitnessCheck.v
```

Both end in `Print Assumptions` output listing only the Stdlib-Reals axioms.
