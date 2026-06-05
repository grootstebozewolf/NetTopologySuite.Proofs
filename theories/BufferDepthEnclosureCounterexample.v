(* ============================================================================
   NetTopologySuite.Proofs.BufferDepthEnclosureCounterexample
   ----------------------------------------------------------------------------
   Why `depth_region` (BufferDepth.v) needs a CLOSED-BOUNDARY guard: the open
   "spur" counterexample (RED + GREEN).

   `BufferDepth.v` defines the buffer interior as the crossing-number interior
   of the kept boundary edges:

       depth_region G p := ray_parity_odd p (edges_of (kept_edges G)).

   `kept_edges G` is `filter (xor in_left in_right) (tg_edges G)` -- an arbitrary
   sublist of the graph's edges.  Nothing constrains those edges to form a
   CLOSED boundary (each vertex incident to an even number of kept edges).  But
   ray-crossing parity is only a meaningful enclosure test for a closed
   boundary: for an OPEN edge set it is not even constant on a connected
   component of the complement, so it cannot equal any region.

   The witness is the smallest open boundary -- a single kept edge ("spur")
   from (0,0) to (0,2):

       G = spur :     kept boundary = the segment x = 0, 0 <= y <= 2  (open!)

   Its kept-edge list is exactly `ring_edges` of the degenerate two-vertex
   "ring" `spur_ring = [(0,0); (0,2)]`, which is NOT `ring_closed` and has only
   two vertices.  The complement of a single segment is path-connected, yet the
   rightward-ray parity differs across it:

       p1 = (-1, 1)   ray crosses the segment   -> depth_region true  ("inside")
       p2 = (-1, 3)   ray misses the segment    -> depth_region false ("outside")

   and p1, p2 are joined by the off-boundary vertical path x = -1.  So
   `depth_region spur` is NOT a complement-component invariant -- it classifies
   two points of the same component differently -- hence it is not a sound
   enclosure predicate without a closure guard.

   WHAT IS PROVED HERE (all Qed-closed, no `Admitted`/`Axiom`/`Parameter`):

     - `spur_kept_is_open_ring`: `edges_of (kept_edges spur) = ring_edges
       spur_ring` (the kept boundary is the degenerate open ring).
     - `spur_depth_p1` / `spur_not_depth_p2`: the parity verdicts differ.
     - `spur_p1_p2_connected`: p1 and p2 share a complement component.
     - `spur_depth_not_component_invariant` (RED): `depth_region spur` is not
       constant on a complement component -- so it is not a valid enclosure.
     - `spur_ring_not_closed` / `_not_min_points` + `spur_excluded_by_closure_guard`
       (GREEN): the kept boundary is not a closed ring; a `depth_region` guarded
       by closure of its kept boundary excludes the witness vacuously.

   The proper general guard is "every vertex is incident to an even number of
   kept edges" (the boundary decomposes into closed cycles); for the single-edge
   witness this collapses to "the kept boundary is a closed ring", which is what
   we formalise.  Mirrors the JCT parity-seam guard findings (#84-#87): the
   ray-parity primitive is shared (BufferDepth.v reuses `ray_parity_odd`), and
   so is the missing-precondition pattern.

   Pure-R; no atan / Flocq / `Classical_Prop.classic`.  No `Admitted`,
   no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import List.

From NTS.Proofs Require Import Distance.
From NTS.Proofs Require Import Overlay.
From NTS.Proofs Require Import OverlayGraph.
From NTS.Proofs Require Import BufferCorrectness.
From NTS.Proofs Require Import BufferDepth.
From NTS.Proofs Require Import PointInRingTangents.
From NTS.Proofs Require Import JordanCurveSeam.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The open "spur" graph and its kept boundary.                            *)
(* -------------------------------------------------------------------------- *)

(* A graph with a single edge whose label is kept by the depth rule
   (xor in_left in_right = xor true false = true). *)
Definition spur : TopologyGraph :=
  {| tg_vertices := [mkPoint 0 0; mkPoint 0 2];
     tg_edges    := [ (mkPoint 0 0, mkPoint 0 2,
                       {| in_left := true; in_right := false |}) ] |}.

(* The degenerate two-vertex "ring" whose edge list is the kept boundary.
   Open: a single segment, not a closed loop. *)
Definition spur_ring : Ring := [mkPoint 0 0; mkPoint 0 2].

Definition p1 : Point := mkPoint (-1) 1.   (* ray crosses the segment *)
Definition p2 : Point := mkPoint (-1) 3.   (* ray misses the segment  *)

(* The kept boundary of `spur` is exactly the edge list of `spur_ring`. *)
Lemma spur_kept_is_open_ring :
  edges_of (kept_edges spur) = ring_edges spur_ring.
Proof. reflexivity. Qed.

Lemma spur_depth_is_ring_parity :
  forall p, depth_region spur p <-> point_in_ring p spur_ring.
Proof.
  intro p. unfold depth_region, point_in_ring.
  rewrite spur_kept_is_open_ring. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The two parity verdicts differ.                                         *)
(* -------------------------------------------------------------------------- *)

Ltac no_cross :=
  let H := fresh "H" in
  intro H; unfold edge_crosses_ray in H; simpl in H;
  destruct H as [ [[? ?] ?] | [[? ?] ?] ]; lra.

Ltac yes_cross :=
  unfold edge_crosses_ray; simpl;
  ((left; repeat split; lra) || (right; repeat split; lra)).

Lemma ray_parity_even_not_odd :
  forall (p : Point) (es : list Edge),
    ray_parity_even p es -> ~ ray_parity_odd p es.
Proof.
  intros p es; induction es as [|e es' IH]; intros Heven Hodd.
  - inversion Hodd.
  - inversion Heven; subst; inversion Hodd; subst;
      try (eapply IH; eassumption);
      try contradiction.
Qed.

(* p1 = (-1,1): the ray at height 1 crosses the segment (0,0)->(0,2). *)
Lemma spur_depth_p1 : depth_region spur p1.
Proof.
  apply spur_depth_is_ring_parity.
  unfold point_in_ring, spur_ring, p1. cbn [ring_edges].
  apply rpo_cross; [ yes_cross | ].
  apply rpe_nil.
Qed.

(* p2 = (-1,3): the ray at height 3 misses the segment (y in [0,2]). *)
Lemma spur_not_depth_p2 : ~ depth_region spur p2.
Proof.
  rewrite spur_depth_is_ring_parity.
  unfold point_in_ring, spur_ring, p2. cbn [ring_edges].
  apply ray_parity_even_not_odd.
  apply rpe_skip; [ no_cross | ].
  apply rpe_nil.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  p1 and p2 share a complement component.                                 *)
(* -------------------------------------------------------------------------- *)

(* The vertical path x = -1 from p1 to p2 never meets the kept boundary (which
   lies on x = 0). *)
Lemma spur_p1_p2_connected : connected_in_complement_cont spur_ring p1 p2.
Proof.
  unfold connected_in_complement_cont.
  exists (fun t => mkPoint ((1 - t) * (-1) + t * (-1)) ((1 - t) * 1 + t * 3)).
  split; [ apply straight_path_continuous | ].
  split; [ unfold p1; cbn; f_equal; lra | ].
  split; [ unfold p2; cbn; f_equal; lra | ].
  intros t [Ht0 Ht1] Himg.
  unfold ring_image in Himg.
  destruct Himg as [e [u [Hin [[Hu0 Hu1] [Hx Hy]]]]].
  unfold spur_ring in Hin. cbn [ring_edges] in Hin.
  destruct Hin as [E|[]]; subst e; simpl in Hx, Hy; nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  RED: depth_region is not a complement-component invariant.              *)
(* -------------------------------------------------------------------------- *)

(* A sound enclosure predicate is constant on each connected component of the
   complement (as `geometric_interior_cont` is, JCT.v).  `depth_region spur` is
   not: p1 and p2 are complement-connected yet get opposite verdicts. *)
Theorem spur_depth_not_component_invariant :
  ~ (forall a b, connected_in_complement_cont spur_ring a b ->
       (depth_region spur a <-> depth_region spur b)).
Proof.
  intro Hinv.
  apply spur_not_depth_p2.
  apply (proj1 (Hinv p1 p2 spur_p1_p2_connected)).
  exact spur_depth_p1.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  GREEN: the kept boundary is not closed; a closure guard excludes it.    *)
(* -------------------------------------------------------------------------- *)

Lemma spur_ring_not_closed : ~ ring_closed spur_ring.
Proof.
  unfold ring_closed, spur_ring. intros [q [ps Heq]].
  destruct ps as [|a ps'].
  - (* ps = [] : (0,0)::(0,2)::nil = q :: q :: nil forces (0,2) = (0,0) *)
    simpl in Heq. injection Heq as Hq Htl.
    rewrite <- Hq in Htl. apply (f_equal py) in Htl. simpl in Htl. lra.
  - (* ps = a::ps' : tail length forces nil = ps' ++ [q], impossible *)
    simpl in Heq. injection Heq as _ _ Hnil.
    symmetry in Hnil. apply app_eq_nil in Hnil. destruct Hnil as [_ Hbad].
    discriminate.
Qed.

Lemma spur_ring_not_min_points : ~ ring_has_minimum_points spur_ring.
Proof. unfold ring_has_minimum_points, spur_ring. simpl. lia. Qed.

(* A depth predicate guarded by closure of its kept boundary: it only fires
   when the kept edges are the edge list of a closed ring with the minimum
   vertex count.  (The proper general guard is even kept-degree at every
   vertex; for a single-edge boundary this is the cleanest specialisation.) *)
Definition depth_region_closed_guarded
    (G : TopologyGraph) (r : Ring) (p : Point) : Prop :=
  edges_of (kept_edges G) = ring_edges r ->
  ring_closed r ->
  ring_has_minimum_points r ->
  depth_region G p.

(* GREEN.  The spur is excluded by the closure guard: its kept boundary IS the
   ring `spur_ring` (so the guard applies), but `spur_ring` is not closed -- so
   the obligation is vacuously dischargeable.  The closure guard -- and nothing
   else -- is what rules out the open-boundary witness. *)
Theorem spur_excluded_by_closure_guard :
  forall p, depth_region_closed_guarded spur spur_ring p.
Proof.
  intros p _ Hclosed _. exfalso. exact (spur_ring_not_closed Hclosed).
Qed.

(* RED and GREEN in one statement: ray-parity over the kept edges is not a
   component invariant for the open spur, but a closure-guarded depth predicate
   excludes it. *)
Theorem closure_guard_resolves_the_spur :
  (~ (forall a b, connected_in_complement_cont spur_ring a b ->
        (depth_region spur a <-> depth_region spur b)))     (* RED   *)
  /\ (forall p, depth_region_closed_guarded spur spur_ring p). (* GREEN *)
Proof.
  split.
  - exact spur_depth_not_component_invariant.
  - exact spur_excluded_by_closure_guard.
Qed.
