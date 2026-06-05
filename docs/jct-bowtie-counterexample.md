# The bowtie counterexample: `ring_simple` is not enough for the JCT

**Coq artifact:** [`theories/JCT_Counterexample.v`](../theories/JCT_Counterexample.v)
(Qed-closed; no `Admitted` / `Axiom` / `Parameter`; axiom footprint =
the standard classical-reals pair on the allowlist).

**Seam touched:** the polygonal Jordan Curve Theorem hypothesis
`JCT_two_components_cont` in
[`theories/JordanCurveSeam.v`](../theories/JordanCurveSeam.v) §3.

---

## TL;DR

`JordanCurveSeam.v` states the honest, continuity-carrying JCT hypothesis

```coq
Definition JCT_two_components_cont (r : Ring) : Prop :=
  ring_simple r -> ring_closed r -> ring_has_minimum_points r ->
  exists interior_pred exterior_pred : Point -> Prop, ...
```

The long-term goal of the seam is to *discharge* this for genuine simple
polygons. This file shows that the **three structural premises as written are
not sufficient**: there is a ring that satisfies all three yet whose complement
has **three** connected components, not two. Therefore

> `forall r, JCT_two_components_cont r` is **false as stated** — the premise
> set must be strengthened from "no proper crossing" to genuine curve
> *injectivity* (every vertex degree 2 / no self-touch).

This is **not** a defect in the implication `jct_cont_interior_is_geometric`
(which remains correct: it merely *uses* `JCT_two_components_cont` as a
hypothesis). It is a scope finding about what that hypothesis can ever be
proved for.

## The witness

A figure-8 made of two triangles that meet **only** at the shared origin
vertex:

```
        (1,1)                 (-1,1)
          *                     *
         /|                     |\
        / |    right     left   | \
 (0,0) *--+----- * -------*------+--* (0,0)   <- the pinch is a single point
        \ |                     | /
         \|                     |/
          *                     *
        (1,-1)                (-1,-1)
```

As a `Ring` (vertex list):

```coq
Definition bowtie : Ring :=
  mkPoint 0 0
    :: mkPoint 1 1     :: mkPoint 1 (-1)
    :: mkPoint 0 0
    :: mkPoint (-1) 1  :: mkPoint (-1) (-1)
    :: mkPoint 0 0 :: nil.
```

## Why it slips past `ring_simple`

`ring_simple` (Overlay.v) forbids only **proper** crossings — two distinct
edges sharing an *interior* point (parameters `t, s` strictly inside `(0,1)`):

```coq
Definition ring_simple (r : Ring) : Prop :=
  forall e1 e2, In e1 (ring_edges r) -> In e2 (ring_edges r) -> e1 <> e2 ->
    ~ segments_intersect_properly (fst e1) (snd e1) (fst e2) (snd e2).
```

The two triangles meet only at the origin, which is an **endpoint** (`t` or `s`
= 0 or 1) of every edge incident to it — never an interior point. So no pair of
edges crosses properly, and the bowtie **is** `ring_simple`
(`bowtie_ring_simple`). It is also `ring_closed` and has 7 ≥ 4 vertices.

What `ring_simple` *fails* to capture is that the origin is a **degree-4**
vertex (`bowtie_origin_degree_four`): four edges are incident to it. A genuine
simple closed curve is injective, so every vertex has degree exactly 2. The
degree-4 pinch is the self-touch, and it is exactly what splits the complement
into three pieces.

## The parity trap

The ray-casting predicate `point_in_ring` (rightward horizontal ray, odd
crossing count) is fooled by the pinch. Only the two **vertical** edges (`x=1`
and `x=-1`) straddle the `y=0` ray; the four origin-incident edges merely touch
`y=0` at an endpoint and are not counted. Hence (`bowtie_parity_*`):

| point                 | crossings of `y=0` ray to the right | `point_in_ring` |
|-----------------------|-------------------------------------|-----------------|
| `p_left  = (-1/2, 0)` | 1 (the `x=1` edge)                  | **true** (inside) |
| `p_right = ( 1/2, 0)` | 1 (the `x=1` edge)                  | **true** (inside) |
| `p_exterior = (10,0)` | 0                                   | false (outside) |

Both bounded lobes are classified "inside", but they live in **different**
bounded components — there is no continuous complement path between them
(every such path must pass through the pinch, which is on the ring).

## The refutation (and what is taken on faith)

```coq
Theorem bowtie_refutes_two_components_modulo_separation :
  ~ connected_in_complement_cont bowtie p_left  p_right    ->
  ~ connected_in_complement_cont bowtie p_left  p_exterior ->
  ~ connected_in_complement_cont bowtie p_right p_exterior ->
  ~ JCT_two_components_cont bowtie.
```

The three hypotheses are the **pairwise separation** facts: the left lobe,
right lobe and exterior are mutually unreachable by a *continuous* complement
path. These are geometrically true but are the **trapped-interior, thesis-scale
half of the JCT** — so they are taken as explicit hypotheses, **not proved and
not axiomatised**. This mirrors precisely how `JordanCurveSeam.v` treats
`JCT_two_components_cont` itself: a named, unproved `Prop`.

Given the separations, the contradiction is pure pigeonhole: a JCT partition
offers only **two** classes (interior / exterior), each internally connected by
continuous complement paths. With three representatives in three distinct
components, two must share a class — forcing a continuous complement path
between two separated components, contradicting a separation hypothesis. All
eight `(interior/exterior)^3` cases are discharged explicitly.

## Recommendation — now a proven GREEN (§7)

Strengthen the premise set of `JCT_two_components_cont` (and any downstream
H1 stated against it) with a curve-injectivity / no-self-touch condition.
`ring_simple` (no *proper* crossing) alone is provably insufficient, and the
bowtie's degree-4 origin is the concrete obstruction.

§7 of the Coq file makes this concrete and machine-checks the fix — the
**GREEN** half of the Red–Green–Refactor cycle:

```coq
(* the OGC "simple ring" half that ring_simple omits *)
Definition ring_vertices_distinct (r : Ring) : Prop := NoDup (removelast r).

Lemma  bowtie_violates_vertex_distinctness : ~ ring_vertices_distinct bowtie.

(* JCT_two_components_cont's body, additionally guarded by the new premise *)
Definition JCT_two_components_cont_simple (r : Ring) : Prop :=
  ring_simple r -> ring_closed r -> ring_has_minimum_points r ->
  ring_vertices_distinct r -> exists interior_pred exterior_pred, ...

Theorem bowtie_excluded_by_rescoped_JCT : JCT_two_components_cont_simple bowtie.
```

The bowtie now satisfies the re-scoped hypothesis (vacuously: its added
premise is unsatisfiable), whereas it refuted the un-strengthened one.
`rescoping_resolves_the_bowtie` states both halves together — the single
added premise `ring_vertices_distinct` is the whole difference.

### RGR status

| phase | content | status |
|---|---|---|
| **RED**   | bowtie passes `ring_simple`+closed+min-points yet refutes two-components (`bowtie_refutes_two_components_modulo_separation`) | Qed |
| **GREEN** | adding `ring_vertices_distinct` excludes the bowtie (`bowtie_excluded_by_rescoped_JCT`) | Qed |
| **REFACTOR** | done: `ring_vertices_distinct` lives in `Overlay.v`, `JCT_two_components_cont_simple` in `JordanCurveSeam.v`, and the headline `jct_cont_interior_is_geometric` is re-pointed onto it | Qed |

## Registry note

This file contains **no `Admitted`**, so it gets **no entry** in
`docs/admitted-counterexamples.txt` (that registry's semantics are "this
*Admitted theorem* cannot be proved as stated"). `JCT_two_components_cont` is a
`Prop` *hypothesis*, never an `Admitted` theorem; the bowtie is a scope finding
about it, fully Qed-closed here.
