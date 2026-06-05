(* ============================================================================
   NetTopologySuite.Proofs.Overlay
   ----------------------------------------------------------------------------
   Phase 3 Milestone 1: foundational definitions for the overlay correctness
   theorem.  Two concepts the Phase 3 headline rests on:

     - `valid_geometry`: the structural validity conditions on a geometry,
                         capturing the OGC 06-103r4 §6 polygon invariants
                         (closed rings, simple rings, holes inside outer
                         ring, minimum vertex count).

     - `boolean_op`:     the point-set semantics of the four boolean
                         overlay operations -- Union, Intersection,
                         Difference, SymDiff.  Stated against a
                         `point_set : Geometry -> Point -> Prop` bridge
                         so the eventual correctness theorem
                         `point_set (extract op g) = boolean_op op A B`
                         can be written cleanly in Milestone 5.

   ----------------------------------------------------------------------------
   Representation choice (Shape C -- hybrid structural + point-set bridge).

   Three candidate shapes were considered:

     A. List of rings (concrete, computational).  Pros: decidable
        membership composes with `List.Forall` for validity.  Cons:
        point-set membership needs a point_in_polygon function, which
        bundles winding-number / crossing-number arithmetic.

     B. Predicate over points (abstract, mathematical).  Pros: boolean_op
        is trivial set algebra.  Cons: valid_geometry on a raw `Point ->
        Prop` cannot easily express "this geometry has these rings with
        these holes"; extraction to OCaml is awkward.

     C. Hybrid: structural `Geometry := list Polygon` for validity,
        bridged to `point_set : Geometry -> Point -> Prop` for the
        correctness theorem.  Pros: both `valid_geometry` and the
        correctness theorem are simultaneously tractable.  Cons: the
        bridge needs `point_in_polygon`, here defined concretely via
        crossing-number parity.

   Shape C is the one used in standard computational-geometry
   formalisations.  It also matches docs/audit-phase4-curves.md's
   "chord-first concrete" directive: rings are concrete lists of
   `Point`, so an arc-bearing future extension specialises the carrier
   rather than the algorithm.

   ----------------------------------------------------------------------------
   OGC 06-103r4 reference.  This corpus does not yet carry a Phase 3
   audit document with per-clause attribution (the structural counterpart
   to docs/audit-phase2-snap-rounding.md / docs/audit-phase4-curves.md).
   The validity conditions below are formulated against the published
   OGC 06-103r4 §6 polygon rules; pinning each conjunct to its precise
   sub-clause is registered as a documentation gap for the Phase 3
   completion writeup, not a proof obligation.

   ----------------------------------------------------------------------------
   Audit footprint.  This file imports only `From Stdlib Require Import
   Reals` (and Lra / List), and the corpus's `Distance` module.  It
   does NOT pull `Classical_Prop.classic`; it is not listed in
   docs/audit-exceptions.txt.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import List.
From NTS.Proofs Require Import Distance.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Geometry representation.                                               *)
(* -------------------------------------------------------------------------- *)

(* A ring is a list of vertices.  Validity (closure, simplicity, minimum
   vertex count) is layered on top via the `valid_polygon` predicate
   below -- the bare `Ring` type does not pre-enforce it. *)
Definition Ring : Type := list Point.

(* A polygon is one outer ring and a list of hole rings (each a Ring). *)
Record Polygon : Type := mkPolygon {
  outer_ring : Ring;
  hole_rings : list Ring
}.

(* A geometry is a list of polygons (a "multi-polygon" in OGC terms). *)
Definition Geometry : Type := list Polygon.

(* -------------------------------------------------------------------------- *)
(* §2  Edges and proper intersection.                                         *)
(* -------------------------------------------------------------------------- *)

(* An edge is an ordered pair of points.  Used for the per-edge crossing
   tests below; ring-edge orientation is inherited from the ring's vertex
   order. *)
Definition Edge : Type := (Point * Point)%type.

(* Convert a ring to its consecutive-pair edge list.  For a properly
   closed ring [v0; v1; ...; vn; v0], the result is
   [(v0,v1); (v1,v2); ...; (vn,v0)].  The recursion stops on lists of
   length < 2, returning []; the trailing single-vertex tail (which
   carries the closing vertex) is consumed but produces no edge, as the
   prior step already emitted (vn, v0). *)
Fixpoint ring_edges (r : Ring) : list Edge :=
  match r with
  | a :: r' =>
      match r' with
      | b :: _ => (a, b) :: ring_edges r'
      | nil    => nil
      end
  | nil => nil
  end.

(* Two segments [P0,P1] and [Q0,Q1] intersect PROPERLY when they cross at
   an interior point: parameters t and s both strictly in (0,1) yield
   the same point.  Mirrors the definition in
   theories-flocq/HobbyTheorem_b64.v -- copied here to keep Overlay.v
   independent of the Flocq layer. *)
Definition segments_intersect_properly (P0 P1 Q0 Q1 : Point) : Prop :=
  exists t s : R,
    0 < t < 1 /\ 0 < s < 1 /\
    (1 - t) * px P0 + t * px P1 =
    (1 - s) * px Q0 + s * px Q1 /\
    (1 - t) * py P0 + t * py P1 =
    (1 - s) * py Q0 + s * py Q1.

(* -------------------------------------------------------------------------- *)
(* §3  Point-in-ring via crossing-number parity.                              *)
(* -------------------------------------------------------------------------- *)

(* A horizontal rightward ray from p crosses edge (a,b) iff the edge's
   endpoints strictly straddle the y-coordinate of p, and the
   x-intersection at height `py p` lies strictly to the right of p.

   Two cases (a below ray and b above, or a above and b below) keep the
   denominator strictly nonzero in the linear-interpolation formula.

   This is the standard generic-position crossing predicate.  Boundary
   cases (p on a vertex, p on an edge) are excluded by the strict
   inequalities -- the standard convention for the crossing-number
   algorithm, valid for a generic ray direction.  Robust handling of
   on-edge cases is a follow-up refinement, not a Milestone 1 blocker. *)
Definition edge_crosses_ray (p : Point) (e : Edge) : Prop :=
  let (a, b) := e in
  (py a < py p < py b /\
     px p < px a + (px b - px a) * (py p - py a) / (py b - py a))
  \/
  (py b < py p < py a /\
     px p < px b + (px a - px b) * (py p - py b) / (py a - py b)).

(* Parity-of-crossings as a Prop, defined inductively without a bool
   detour or decidability assumption.  Two mutually inductive predicates:
   "the number of edges in this list crossed by the ray from p is odd"
   and "...is even".  Each cons-step toggles between the two. *)
Inductive ray_parity_odd (p : Point) : list Edge -> Prop :=
| rpo_cross : forall e es,
    edge_crosses_ray p e ->
    ray_parity_even p es ->
    ray_parity_odd p (e :: es)
| rpo_skip : forall e es,
    ~ edge_crosses_ray p e ->
    ray_parity_odd p es ->
    ray_parity_odd p (e :: es)
with ray_parity_even (p : Point) : list Edge -> Prop :=
| rpe_nil : ray_parity_even p []
| rpe_cross : forall e es,
    edge_crosses_ray p e ->
    ray_parity_odd p es ->
    ray_parity_even p (e :: es)
| rpe_skip : forall e es,
    ~ edge_crosses_ray p e ->
    ray_parity_even p es ->
    ray_parity_even p (e :: es).

(* Point-in-ring: the horizontal rightward ray from p crosses an odd
   number of edges of r.  Standard crossing-number characterisation. *)
Definition point_in_ring (p : Point) (r : Ring) : Prop :=
  ray_parity_odd p (ring_edges r).

(* -------------------------------------------------------------------------- *)
(* §4  Point-in-polygon and the geometry point-set bridge.                    *)
(* -------------------------------------------------------------------------- *)

(* p is inside polygon `poly` iff it is inside the outer ring and outside
   every hole.  This is the standard OGC interior characterisation; the
   polygon's boundary is the union of its rings, treated here as not
   contributing to the interior point-set. *)
Definition point_in_polygon (p : Point) (poly : Polygon) : Prop :=
  point_in_ring p (outer_ring poly) /\
  forall h, In h (hole_rings poly) -> ~ point_in_ring p h.

(* The point-set of a geometry: the union of its polygons' interiors.
   Bridge from the structural representation to the mathematical
   semantics that boolean_op and the eventual correctness theorem are
   stated against. *)
Definition point_set (g : Geometry) (p : Point) : Prop :=
  exists poly, In poly g /\ point_in_polygon p poly.

(* -------------------------------------------------------------------------- *)
(* §5  Boolean operations.                                                    *)
(* -------------------------------------------------------------------------- *)

(* The four OGC overlay operations, as a tag enum.  Used as the first
   argument of `boolean_op` to dispatch the four point-set
   constructions. *)
Inductive BooleanOp : Type :=
| Union        : BooleanOp
| Intersection : BooleanOp
| Difference   : BooleanOp
| SymDiff      : BooleanOp.

(* Point-set semantics of the boolean operations.  Each case is the
   standard set-theoretic construction over the operand point-sets. *)
Definition boolean_op (op : BooleanOp) (A B : Geometry) (p : Point) : Prop :=
  match op with
  | Union        => point_set A p \/ point_set B p
  | Intersection => point_set A p /\ point_set B p
  | Difference   => point_set A p /\ ~ point_set B p
  | SymDiff      => (point_set A p /\ ~ point_set B p) \/
                    (point_set B p /\ ~ point_set A p)
  end.

(* -------------------------------------------------------------------------- *)
(* §6  Validity (OGC 06-103r4 §6 polygon invariants).                         *)
(* -------------------------------------------------------------------------- *)

(* Condition 1.  A ring is closed: its first and last vertices coincide.
   Expressed as: there exist p and ps such that r = p :: ps ++ [p]. *)
Definition ring_closed (r : Ring) : Prop :=
  exists (p : Point) (ps : list Point), r = p :: (ps ++ [p]).

(* Condition 2.  A ring is simple: distinct edges do not intersect
   properly (i.e., do not cross at an interior point of either edge).
   Adjacent edges share an endpoint but do not cross at an interior
   point, so the `~ segments_intersect_properly` form is correct for
   adjacent pairs as well as non-adjacent pairs.  Distinctness `e1 <>
   e2` excludes only the trivial self-equal case. *)
Definition ring_simple (r : Ring) : Prop :=
  forall e1 e2 : Edge,
    In e1 (ring_edges r) ->
    In e2 (ring_edges r) ->
    e1 <> e2 ->
    ~ segments_intersect_properly (fst e1) (snd e1) (fst e2) (snd e2).

(* Condition 3.  Each hole sits inside the outer ring.  We adopt the
   "some vertex of the hole is in the outer ring" form here; the
   stronger "every point of the hole is in the outer ring" follows
   under simple + non-intersecting outer + simple hole (a Jordan-curve
   consequence) and is not Milestone 1 work. *)
Definition hole_inside_outer (outer hole : Ring) : Prop :=
  exists p, In p hole /\ point_in_ring p outer.

(* Condition 4.  A ring has at least four vertices: three distinct
   geometric vertices plus the repeated closing vertex.  This is the
   minimum a non-degenerate closed simple polygon admits (a triangle). *)
Definition ring_has_minimum_points (r : Ring) : Prop :=
  (4 <= length r)%nat.

(* A polygon is valid iff: the outer ring is closed, simple, and has
   the minimum vertex count; and each hole ring satisfies the same
   three conditions and lies inside the outer ring. *)
Definition valid_polygon (poly : Polygon) : Prop :=
  ring_closed (outer_ring poly) /\
  ring_simple (outer_ring poly) /\
  ring_has_minimum_points (outer_ring poly) /\
  (forall h, In h (hole_rings poly) ->
     ring_closed h /\
     ring_simple h /\
     ring_has_minimum_points h /\
     hole_inside_outer (outer_ring poly) h).

(* A geometry is valid iff every polygon in it is valid. *)
Definition valid_geometry (g : Geometry) : Prop :=
  forall poly, In poly g -> valid_polygon poly.

(* -------------------------------------------------------------------------- *)
(* §7  Structural lemmas.                                                     *)
(*                                                                            *)
(* Five warmup theorems exercising the definitions and confirming they       *)
(* compose.  Each closes by elementary list / set-theoretic reasoning; no    *)
(* unfolding of point_in_ring is required.                                    *)
(* -------------------------------------------------------------------------- *)

(* The empty geometry is vacuously valid. *)
Lemma valid_geometry_nil : valid_geometry [].
Proof.
  intros poly Hin. simpl in Hin. contradiction.
Qed.

(* Prepending a valid polygon to a valid geometry yields a valid geometry. *)
Lemma valid_geometry_cons :
  forall poly g,
    valid_polygon poly ->
    valid_geometry g ->
    valid_geometry (poly :: g).
Proof.
  intros poly g Hpoly Hg poly' Hin. simpl in Hin.
  destruct Hin as [Heq | Hin'].
  - subst poly'. exact Hpoly.
  - apply Hg. exact Hin'.
Qed.

(* The point-set of the empty geometry is empty. *)
Lemma point_set_nil : forall p, ~ point_set [] p.
Proof.
  intros p [poly [Hin _]]. simpl in Hin. contradiction.
Qed.

(* Union is symmetric (point-set commutativity of \/). *)
Lemma boolean_op_union_comm :
  forall A B p,
    boolean_op Union A B p <-> boolean_op Union B A p.
Proof.
  intros A B p. unfold boolean_op. tauto.
Qed.

(* Intersection is symmetric (point-set commutativity of /\). *)
Lemma boolean_op_intersection_comm :
  forall A B p,
    boolean_op Intersection A B p <-> boolean_op Intersection B A p.
Proof.
  intros A B p. unfold boolean_op. tauto.
Qed.

(* Symmetric difference is symmetric (point-set commutativity of the
   xor-style disjunction). *)
Lemma boolean_op_symdiff_comm :
  forall A B p,
    boolean_op SymDiff A B p <-> boolean_op SymDiff B A p.
Proof.
  intros A B p. unfold boolean_op. tauto.
Qed.
