(* ============================================================================
   NetTopologySuite.Proofs.BufferDepthGuarded
   ----------------------------------------------------------------------------
   REFACTOR: the guarded depth-region predicate, and the depth/interior bridge.

   The BufferDepth enclosure counterexamples pinned the guards `depth_region`
   needs to be a sound enclosure test (each a Qed-closed RED/GREEN):

     - a CLOSED kept boundary
         (BufferDepthEnclosureCounterexample.v -- open spur, #91);
     - `no_horizontal_edge_at` on the kept boundary
         (BufferDepthHorizontalEdgeCounterexample.v -- horizontal edge, #93);
     - `ray_avoids_vertices` on the kept boundary
         (BufferDepthVertexGrazeCounterexample.v -- vertex graze, #95).

   This file folds those into one predicate (`kept_boundary_wellformed`) and
   re-points the depth seams onto it, WITHOUT mutating the existing `BufferDepth`
   theorems (additive).  The headline `depth_region_is_geometric_interior_guarded`
   is the depth-labelling analogue of `JCT.point_in_ring_correct_jct_cont`: for a
   well-formed kept boundary, `depth_region` equals the continuous geometric
   interior -- CONDITIONAL on the same named JCT seam
   `parity_characterises_interior_cont_strict` (the genuine remaining content;
   not proved, not axiomatised).

   SCOPE NOTE.  The proposed `depth_region_guarded_component_invariant`
   (ray-parity is constant on a complement component for a closed ring) is NOT
   provable here: it IS the winding-number / JCT theorem -- the same thesis-scale
   gap `parity_characterises_interior_cont_strict` names.  We therefore route the
   bridge THROUGH that named seam rather than re-proving it.

   Pure-R; no atan / Flocq.  No `Admitted` / `Axiom` / `Parameter`.  Axiom
   footprint: the corpus-standard classical-reals pair.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import List.

From NTS.Proofs Require Import Distance.
From NTS.Proofs Require Import Overlay.
From NTS.Proofs Require Import OverlayGraph.
From NTS.Proofs Require Import BufferCorrectness.
From NTS.Proofs Require Import BufferDepth.
From NTS.Proofs Require Import PointInRingCorrect.
From NTS.Proofs Require Import PointInRingTangents.
From NTS.Proofs Require Import JordanCurveSeam.
From NTS.Proofs Require Import JCT.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The combined kept-boundary well-formedness guard.                       *)
(* -------------------------------------------------------------------------- *)

(* The kept boundary of G is (the edge list of) a ring r that is a valid simple
   closed boundary, with the generic-position guards for the rightward ray from
   p.  This is exactly the guard set the #91/#93/#95 counterexamples force. *)
Definition kept_boundary_wellformed
    (G : TopologyGraph) (r : Ring) (p : Point) : Prop :=
  edges_of (kept_edges G) = ring_edges r /\
  ring_simple r /\
  ring_closed r /\
  ring_has_minimum_points r /\
  no_horizontal_edge_at p r /\
  ray_avoids_vertices p r.

(* When the kept boundary is the edge list of r, `depth_region` is exactly
   `point_in_ring` of r -- the bridge from the graph predicate to the ring one. *)
Lemma depth_region_eq_point_in_ring :
  forall (G : TopologyGraph) (r : Ring) (p : Point),
    edges_of (kept_edges G) = ring_edges r ->
    (depth_region G p <-> point_in_ring p r).
Proof.
  intros G r p Hedges. unfold depth_region, point_in_ring.
  rewrite Hedges. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The depth / geometric-interior bridge (conditional on the JCT seam).    *)
(* -------------------------------------------------------------------------- *)

(* The depth-labelling analogue of `point_in_ring_correct_jct_cont`: for a
   well-formed kept boundary, `depth_region` coincides with the continuous
   geometric interior -- under the named JCT seam
   `parity_characterises_interior_cont_strict` (JCT.v).  This does NOT prove the
   JCT; it shows depth labelling reduces to the SAME single remaining seam. *)
Theorem depth_region_is_geometric_interior_guarded :
  forall (G : TopologyGraph) (r : Ring) (p : Point),
    kept_boundary_wellformed G r p ->
    parity_characterises_interior_cont_strict p r ->
    (depth_region G p <-> geometric_interior_cont p r).
Proof.
  intros G r p [Hedges [Hs [Hc [Hm [Hnh Hrav]]]]] Hseam.
  rewrite (depth_region_eq_point_in_ring G r p Hedges).
  symmetry. exact (Hseam Hs Hc Hm Hnh Hrav).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Re-pointing the H_bridge factorisation onto the guarded seam.           *)
(* -------------------------------------------------------------------------- *)

(* The guarded depth seam: depth equals the buffer only at well-formed kept
   boundaries / generic-position points.  This is the dischargeable scope of
   `depth_region_is_buffer` -- the unguarded form is refuted by the #91/#93/#95
   witnesses, so any correctness use should carry the guard. *)
Definition depth_region_is_buffer_guarded
    (G : TopologyGraph) (g : Geometry) (d : R) (r : Ring) : Prop :=
  forall p, kept_boundary_wellformed G r p ->
            (depth_region G p <-> buffer_spec g d p).

(* Re-pointed H_bridge factor: compose the extractor seam with the GUARDED depth
   seam, carrying the well-formedness guard.  Mirrors `buffer_H_bridge_factor`
   but over the dischargeable seam. *)
Theorem buffer_H_bridge_factor_guarded :
  forall (extract_buffer : TopologyGraph -> Geometry)
         (G : TopologyGraph) (g : Geometry) (d : R) (r : Ring),
    extract_realizes_depth extract_buffer G ->
    depth_region_is_buffer_guarded G g d r ->
    forall p, kept_boundary_wellformed G r p ->
      point_set (extract_buffer G) p <-> buffer_spec g d p.
Proof.
  intros extract_buffer G g d r Hreal Hbuf p Hwf.
  rewrite (Hreal p). exact (Hbuf p Hwf).
Qed.

(* End-to-end capstone over the guarded seam (the guarded analogue of
   `buffer_correct_via_depth`). *)
Theorem buffer_correct_via_depth_guarded :
  forall (node : list (Point * Point) -> list (Point * Point))
         (extract_buffer : TopologyGraph -> Geometry)
         (g : Geometry) (d : R) (r : Ring) (p : Point),
    extract_realizes_depth extract_buffer (build_graph (node (offset_curve g d))) ->
    depth_region_is_buffer_guarded (build_graph (node (offset_curve g d))) g d r ->
    kept_boundary_wellformed (build_graph (node (offset_curve g d))) r p ->
    point_set (extract_buffer (build_graph (node (offset_curve g d)))) p
      <-> buffer_spec g d p.
Proof.
  intros node extract_buffer g d r p Hreal Hbuf Hwf.
  apply (buffer_H_bridge_factor_guarded extract_buffer
           (build_graph (node (offset_curve g d))) g d r Hreal Hbuf p Hwf).
Qed.
