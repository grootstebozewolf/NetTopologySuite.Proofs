# JCT seam — the corpus interior predicate is vacuous

**Date:** 2026-06-04.
**Status:** Qed-closed finding (`theories/JordanCurveSeam.v`).
**Bearing:** Directly on the Jordan-curve seam of `point_in_ring_correct`
(Phase 3 H1) and on the conditional headline `point_in_ring_correct_jct`
(`theories/PointInRingTangents.v:235`).

---

## TL;DR

Asked to "prove JCT", we examined the *actual* corpus definitions rather
than the doc's proposed forms — and found that the seam is currently
**degenerate**. The corpus's interior predicate
`geometric_interior_stdlib` is **identically false**, so the genuine
Jordan Curve Theorem cannot even be stated correctly against it. The fix
is definitional (continuous paths), and the genuine theorem behind it
remains thesis-scale, exactly as `docs/jct-scout-2026-05-29.md` graded.

We did **not** prove the polygonal JCT. We proved the seam as written is
vacuous, supplied the corrected definitions, and showed the discontinuity
(not the geometry) is the cause — all `Qed`, all axiom-clean.

---

## The defect

`theories/PointInRingTangents.v:127`:

```coq
Definition connected_in_complement (r : Ring) (p q : Point) : Prop :=
  exists path : R -> Point,
    path 0 = p /\ path 1 = q /\
    forall t : R, 0 <= t <= 1 -> ring_complement r (path t).
```

There is **no continuity requirement** on `path`. So for any two off-ring
points `p`, `q`, the discontinuous *jump*

```coq
fun t => if Rlt_dec t 1 then p else q
```

satisfies all three conjuncts (`path 0 = p`, `path 1 = q`, every value is
`p` or `q`, both off-ring). Hence

> `connected_in_complement r p q` ⟺ `ring_complement r p ∧ ring_complement r q`

— the relation is the *total* relation on the complement, not topological
connectedness at all.

`in_bounded_component r p` (ibid:136) then requires a single radius `M`
bounding **every** complement point reachable from `p` — i.e. the whole
complement. But a ring is a finite edge list; its image is bounded, so the
complement is unbounded. The requirement is unsatisfiable.

## The theorem

`theories/JordanCurveSeam.v`:

```coq
Theorem geometric_interior_stdlib_vacuous :
  forall (p : Point) (r : Ring), ~ geometric_interior_stdlib p r.
```

Proof sketch: from a claimed bound `M`, take `q = (max(B, M) + 1, 0)` where
`B = edges_maxX (ring_edges r)` bounds the image's x-extent
(`ring_image_px_bound`). Then `q` is off-ring (its x exceeds `B`) and
jump-connected to `p`, so the bound forces `|q|² ≤ M²` — yet `|q|² > M²`.
Contradiction.

## Consequence for the headline

`point_in_ring_correct_jct` carries the hypothesis
`geometric_interior_stdlib p r <-> interior_pred p`. Since the left side is
always false:

```coq
Corollary jct_hypotheses_force_empty_interior :
  forall p r interior_pred,
    (geometric_interior_stdlib p r <-> interior_pred p) -> ~ interior_pred p.
```

So the abstract `interior_pred` is forced empty too. For a genuine interior
point — where `point_in_ring` / ray-parity is *true* — the headline's
hypotheses **cannot jointly hold**. The theorem is `Qed`-closed but only
*vacuously* instantiable: it never witnesses a real interior point. It is
not wrong, but it is not the JCT either.

---

## The fix and what is now provable

`theories/JordanCurveSeam.v` adds the continuity-carrying definitions:

```coq
Definition path_continuous (path : R -> Point) : Prop :=
  continuity (fun t => px (path t)) /\ continuity (fun t => py (path t)).

Definition connected_in_complement_cont (r : Ring) (p q : Point) : Prop :=
  exists path, path_continuous path /\ path 0 = p /\ path 1 = q /\
    forall t, 0 <= t <= 1 -> ring_complement r (path t).

Definition in_bounded_component_cont ...
Definition geometric_interior_cont ...
Definition JCT_two_components_cont (r : Ring) : Prop := ...   (* Prop, not proved *)
```

and proves the discontinuity — not the geometry — caused the collapse:

```coq
Lemma far_points_connected_cont :
  forall r x0 x1,
    x0 > edges_maxX (ring_edges r) -> x1 > edges_maxX (ring_edges r) ->
    connected_in_complement_cont r (mkPoint x0 0) (mkPoint x1 0).
```

A genuine straight-line (hence `continuity`-provable, via the `reg` tactic)
path joins two points right of the bounding box without meeting the ring.
The corrected relation is therefore non-trivial exactly where the old one
was vacuous.

## What remains thesis-scale (unchanged)

The load-bearing half of the polygonal JCT — that an **interior** point is
*trapped*, i.e. `in_bounded_component_cont` holds because no continuous
complement path escapes to infinity — is **not** discharged here and
remains the thesis-scale gap (`docs/jct-scout-2026-05-29.md`). What this
session establishes is the precise, machine-checked reason the previous
seam could not carry it: it was vacuous, and the genuine statement requires
`JCT_two_components_cont` over continuous paths.

## Recommended follow-ups

1. Re-state `point_in_ring_correct_jct`'s H3 against
   `geometric_interior_cont` (continuous) rather than
   `geometric_interior_stdlib` (vacuous), so the conditional headline can
   witness genuine interior points once `JCT_two_components_cont` lands.
2. Treat `JCT_two_components_cont` as the canonical Phase 3 H1 Prop; derive
   the old `geometric_interior_stdlib` clauses only after the definition is
   repaired.
3. Keep `geometric_interior_stdlib_vacuous` as a standing regression guard:
   any future "interior" predicate that re-collapses to it is back to
   square one.

## Verification

Full sequential `_CoqProject.full` build (exit 0) under Rocq 9.1.1 +
Flocq 4.2.2; `check_admitted.sh`, `audit_axioms.sh`,
`check_readme_axioms.sh` all green. `theories/JordanCurveSeam.v` is
pure-ℝ with no `Admitted` / `Axiom` / `Parameter`; its only axiom footprint
is the corpus-standard `ClassicalDedekindReals.sig_forall_dec` +
`FunctionalExtensionality.functional_extensionality_dep`.
