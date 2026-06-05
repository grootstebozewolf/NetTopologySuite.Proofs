(* ============================================================================
   NetTopologySuite.Proofs.BufferDepthVertexGrazeCounterexample
   ----------------------------------------------------------------------------
   Completing `depth_region`'s guard set: the vertex-graze case (RED + GREEN).

   `BufferDepthEnclosureCounterexample.v` (#91) showed `depth_region` needs a
   CLOSED kept boundary; `BufferDepthHorizontalEdgeCounterexample.v` (#93) showed
   closure is not sufficient -- it also needs `no_horizontal_edge_at`.  This file
   adds the third and final guard, `ray_avoids_vertices`, exactly mirroring the
   JCT parity seam (#85): a closed kept boundary with NO horizontal edge is still
   misclassified when the rightward ray grazes a vertex.

   The witness reuses the merged #85 convex "diamond" (vertices (0,1),(1,0),
   (0,-1),(-1,0)) as the kept boundary of a graph `G_diamond`.  Because
   `edges_of (kept_edges G_diamond) = ring_edges diamond`, `depth_region
   G_diamond` coincides with `point_in_ring ( ) diamond`, so the #85 verdicts
   transfer verbatim:

     - A = (0, 1/2): ray crosses one edge  -> depth_region true  ("inside")
     - B = (0, 0)  : ray grazes vertex (1,0) -> depth_region false ("outside")

   and A, B are joined by the off-boundary vertical segment x = 0
   (`diamond_segment_off_ring`).  The diamond has no horizontal edge, so the #93
   guard does NOT exclude this; only `ray_avoids_vertices` does.

   WHAT IS PROVED HERE (all Qed-closed, no `Admitted`/`Axiom`/`Parameter`):

     - `Gdiamond_kept_is_diamond`: the kept boundary is `ring_edges diamond`.
     - `Gdiamond_depth_is_point_in_ring`: `depth_region G_diamond` = `point_in_ring`.
     - `depth_region_vertex_not_invariant` (RED): `depth_region G_diamond` is not
       constant on a complement component (A and B differ).
     - `depth_region_vertex_guarded` + `Gdiamond_excluded_by_ray_avoids_guard`
       (GREEN): a `depth_region` additionally guarded by `ray_avoids_vertices`
       on its kept boundary excludes the witness vacuously.

   With #91 and #93 this completes `depth_region`'s required guard set --
   identical to `point_in_ring`'s: a CLOSED kept boundary, plus the
   generic-position guards `no_horizontal_edge_at` and `ray_avoids_vertices`.

   Pure-R; no atan / Flocq / `Classical_Prop.classic`.  No `Admitted`,
   no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import List.

From NTS.Proofs Require Import Distance.
From NTS.Proofs Require Import Overlay.
From NTS.Proofs Require Import OverlayGraph.
From NTS.Proofs Require Import BufferCorrectness.
From NTS.Proofs Require Import BufferDepth.
From NTS.Proofs Require Import PointInRingCorrect.
From NTS.Proofs Require Import PointInRingTangents.
From NTS.Proofs Require Import JordanCurveSeam.
From NTS.Proofs Require Import JCT_VertexGrazingCounterexample.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  A graph whose closed kept boundary is the #85 diamond.                  *)
(* -------------------------------------------------------------------------- *)

Definition keep_lbl : EdgeLabel := {| in_left := true; in_right := false |}.

Definition G_diamond : TopologyGraph :=
  {| tg_vertices :=
       [mkPoint 0 1; mkPoint 1 0; mkPoint 0 (-1); mkPoint (-1) 0];
     tg_edges :=
       [ (mkPoint 0 1,    mkPoint 1 0,    keep_lbl);
         (mkPoint 1 0,    mkPoint 0 (-1), keep_lbl);
         (mkPoint 0 (-1), mkPoint (-1) 0, keep_lbl);
         (mkPoint (-1) 0, mkPoint 0 1,    keep_lbl) ] |}.

Lemma Gdiamond_kept_is_diamond :
  edges_of (kept_edges G_diamond) = ring_edges diamond.
Proof. reflexivity. Qed.

Lemma Gdiamond_depth_is_point_in_ring :
  forall p, depth_region G_diamond p <-> point_in_ring p diamond.
Proof.
  intro p. unfold depth_region, point_in_ring.
  rewrite Gdiamond_kept_is_diamond. reflexivity.
Qed.

Lemma Gdiamond_depth_A : depth_region G_diamond A.
Proof. apply Gdiamond_depth_is_point_in_ring. exact diamond_point_in_ring_A. Qed.

Lemma Gdiamond_not_depth_B : ~ depth_region G_diamond B.
Proof.
  rewrite Gdiamond_depth_is_point_in_ring. exact diamond_not_point_in_ring_B.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  RED: a closed, horizontal-edge-free kept boundary still misclassifies.  *)
(* -------------------------------------------------------------------------- *)

(* A and B are complement-connected (`diamond_segment_off_ring`) yet get
   opposite `depth_region` verdicts -- so `depth_region G_diamond` is not a
   complement-component invariant, hence not a sound enclosure predicate, even
   though its kept boundary is closed and has no horizontal edge. *)
Theorem depth_region_vertex_not_invariant :
  ~ (forall a b, connected_in_complement_cont diamond a b ->
       (depth_region G_diamond a <-> depth_region G_diamond b)).
Proof.
  intro Hinv.
  apply Gdiamond_not_depth_B.
  apply (proj2 (Hinv B A diamond_segment_off_ring)).
  exact Gdiamond_depth_A.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  GREEN: a ray-avoids-vertices guard on the kept boundary excludes it.     *)
(* -------------------------------------------------------------------------- *)

Definition depth_region_vertex_guarded
    (G : TopologyGraph) (r : Ring) (p : Point) : Prop :=
  edges_of (kept_edges G) = ring_edges r ->
  ray_avoids_vertices p r ->
  depth_region G p.

(* GREEN.  B's rightward ray grazes the kept vertex (1,0), so
   `ray_avoids_vertices B diamond` is false and the guarded predicate excludes
   the witness vacuously. *)
Theorem Gdiamond_excluded_by_ray_avoids_guard :
  depth_region_vertex_guarded G_diamond diamond B.
Proof.
  intros _ Hrav. exfalso. exact (diamond_B_ray_hits_vertex Hrav).
Qed.

(* RED and GREEN in one statement. *)
Theorem ray_avoids_guard_is_necessary_for_depth_region :
  (~ (forall a b, connected_in_complement_cont diamond a b ->
        (depth_region G_diamond a <-> depth_region G_diamond b)))   (* RED   *)
  /\ depth_region_vertex_guarded G_diamond diamond B.               (* GREEN *)
Proof.
  split.
  - exact depth_region_vertex_not_invariant.
  - exact Gdiamond_excluded_by_ray_avoids_guard.
Qed.
