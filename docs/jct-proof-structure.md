# JCT proof structure — the continuous-component spine

**Date:** 2026-06-04.
**Status:** Qed-closed (`theories/JCT.v`), axiom-clean.
**Builds on:** `theories/JordanCurveSeam.v` (#81/#82) — the vacuity finding
and the continuity-carrying definitions.
**Bearing:** the Jordan-curve seam of `point_in_ring_correct` (Phase 3 H1)
and the conditional headlines `overlay_ng_correct_conditional` /
`buffer_correct_conditional`.

---

## TL;DR

The issue proposed a 6–8 lemma structure for the genuine polygonal JCT, with
one lemma (`no_path_from_interior_to_exterior`) graded "the genuine
topological content (thesis-scale)" and the rest "easy". We implemented the
structure on the corrected continuity-carrying definitions and found the
grading is **inverted at that lemma**:

> Once "interior" is *defined* as "lies in a bounded connected component of
> the complement" (which `geometric_interior_cont` already does),
> `no_path_from_interior_to_exterior` is **free** — a one-line corollary of
> component invariance. It is NOT the thesis-scale content.

`theories/JCT.v` proves, all `Qed`, with the corpus-standard axiom footprint
(classical reals + `functional_extensionality`):

| § | Result | Note |
|---|--------|------|
| §0 | `continuity_glue` | the one real analysis obligation: glue two ℝ-continuous functions agreeing at a point |
| §1 | `connected_in_complement_cont_{refl,sym,trans,left,right}` | continuous complement-connectivity is an equivalence relation |
| §2 | `in_bounded_component_cont_{invariant,iff}`, `not_in_bounded_component_cont_intro` | boundedness is a component invariant |
| §3 | `no_path_from_interior_to_exterior`, `interior_component_bounded` | **the interior is trapped relative to the exterior — for free** |
| §4 | `far_point_not_interior`, `exterior_inhabited_and_connected` | the honest, non-vacuous analogue of the vacuity witness |
| §5 | `parity_characterises_interior_cont` (Prop), `point_in_ring_correct_jct_cont` | the genuine remaining seam, isolated; a non-vacuous headline |

These mirror `theories/BoundedComponent.v`, which proves exactly the same
component algebra for the *discontinuous* relation. The novelty here is that
everything goes through for the **continuous** relation — the one that makes
`geometric_interior_cont` inhabitable (`JordanCurveSeam.far_points_connected_cont`).

---

## Why the sketch's "hard core" is free

The sketch's target was

```coq
forall p q, geometric_interior_cont p r -> ~ geometric_interior_cont q r ->
            ~ connected_in_complement_cont r p q.
```

Unfold `geometric_interior_cont p r = ring_complement r p /\
in_bounded_component_cont r p`. Suppose a continuous complement path joins `p`
to `q`. Then:

1. `q` is the path's right endpoint, so `ring_complement r q`
   (`connected_in_complement_cont_right`).
2. `q` is connected to the bounded point `p`, so `q` is itself in a bounded
   component (`in_bounded_component_cont_invariant`) — *the same radius works*.

Hence `geometric_interior_cont q r`, contradicting `~ geometric_interior_cont
q r`. The whole content is component invariance (§2), whose only non-trivial
input is transitivity (§1) — whose only non-trivial input is the gluing of two
continuous half-paths at their join (§0, `continuity_glue`). No geometry, no
winding number, no Jordan Curve Theorem.

The genuine topological difficulty was never "interior can't reach exterior".
It is "an *odd-ray-parity* off-ring point actually **is** interior" — i.e. is
trapped in a bounded component, with no continuous escape to infinity. That is
the load-bearing half of the polygonal JCT, and it is exactly what
`far_point_not_interior` settles **only** for the far field (points already
past the bounding box), no further.

## The honest replacement for the vacuous witness

`JordanCurveSeam.geometric_interior_stdlib_vacuous` proves the *old* interior
predicate empty, using a discontinuous jump path. Its continuous counterpart
here, `far_point_not_interior`, uses a genuine straight-line ray and proves
only the true statement: a point far to the right of the ring is exterior.
Crucially it does **not** prove the interior empty — `geometric_interior_cont`
remains inhabitable, which is the whole point of the #81 repair.

## The remaining seam, isolated

```coq
Definition parity_characterises_interior_cont (p : Point) (r : Ring) : Prop :=
  ring_simple r -> ring_closed r -> ring_has_minimum_points r ->
  no_horizontal_edge_at p r ->
  (geometric_interior_cont p r <-> point_in_ring p r).
```

This single named `Prop` (never axiomatised, never `Admitted`) bundles the two
thesis-scale directions: a bounded-component point has odd parity
(winding/counting), and an odd-parity point is trapped (no continuous escape).
`point_in_ring_correct_jct_cont` discharges `point_in_ring p r <->
geometric_interior_cont p r` from it — the non-vacuous, continuous replacement
for `PointInRingTangents.point_in_ring_correct_jct`, which is `Qed`-closed only
over the identically-false `geometric_interior_stdlib`.

## Relation to the corpus `JCT_two_components_cont` Prop (post-#82)

An earlier draft of this file flagged a gap: the documented "Step 3"
path-separation (`docs/point-in-ring-jct-path.md`) was not derivable from
`JordanCurveSeam.JCT_two_components_cont` as then written, because its clauses
asserted connectivity *within* each component but never that connectivity
*implies* same-component. **PR #82 closed that gap**: `JCT_two_components_cont`
now carries an explicit inter-component **separation clause** (interior and
exterior points are never complement-connected), and
`JordanCurveSeam.jct_cont_interior_is_geometric` uses it to place every interior
point into `geometric_interior_cont`.

§3's `no_path_from_interior_to_exterior` is the gap-free **Qed counterpart** of
that clause for the `geometric_interior_cont` definition itself: there
separation is not *assumed* (as a hypothesis clause) but *proved*, because
boundedness is baked into the interior predicate and the rest is component
invariance (§2). The two are complementary — `jct_cont_interior_is_geometric`
shows `JCT_two_components_cont` (with its separation hypothesis) ⟹ interior
points are bounded-component; §3 shows that for bounded-component points,
separation is free. Neither proves the JCT.


## Verification

`rocq makefile -f _CoqProject.full` + `make theories/JCT.vo` under Rocq 9.1.1
builds clean (no warnings). `Print Assumptions` on every headline shows only
`ClassicalDedekindReals.sig_forall_dec` and
`FunctionalExtensionality.functional_extensionality_dep` (both allowlisted).
`scripts/check_admitted.sh`, `scripts/check_readme_axioms.sh`, and
`scripts/validate-claims.sh` are green. `theories/JCT.v` is pure-ℝ with no
`Admitted` / `Axiom` / `Parameter`.
