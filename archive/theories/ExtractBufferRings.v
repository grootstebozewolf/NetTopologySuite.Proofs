(* ============================================================================
   NetTopologySuite.Proofs.ExtractBufferRings
   ----------------------------------------------------------------------------
   extract_rings_valid, slice R6 (see docs/extract-rings-proof-structure.md):
   compose the combinatorial core (R2 = RingExtract) and the noded-ring
   simplicity (RingSimple) into `valid_polygon`, and DISCHARGE the `H_valid`
   hypothesis of `BufferCorrectness.buffer_correct_conditional`.

   Headline finding.  For the HOLE-FREE regime `valid_polygon` reduces to its
   three outer-ring conditions -- `ring_closed`, `ring_simple`,
   `ring_has_minimum_points` -- all of which are now Qed-closed:

     - `ring_closed` + `ring_has_minimum_points` from RingExtract.face_walk_core
       (a closed chain of >= 3 segments yields a closed, min-vertex ring whose
       edges are exactly the chain);
     - `ring_simple` from RingSimple.ring_simple_of_subset (a ring drawn from a
       NODED, pairwise-non-crossing arrangement is simple).

   So a hole-free buffer polygon whose outer ring is a closed chain from the
   noded set is `valid_polygon` UNCONDITIONALLY -- no Jordan-curve residual
   (`valid_polygon_of_noded_chain`).  Hence `H_valid` of
   `buffer_correct_conditional` is dischargeable for any extractor that emits
   such polygons (`H_valid_of_chain_extractor`), and the buffer headline
   reduces to just the semantic `H_bridge` (`buffer_correct_hole_free`).

   The only place the H1/JCT gap re-enters is `hole_inside_outer` for polygons
   WITH holes; that path is the thin conditional `valid_polygon_with_holes`
   (the hole clause taken as a hypothesis), unchanged from R3's residual.

   Pure-R; no atan / Flocq.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.8)
   ========================================================================== *)

From Stdlib Require Import Reals List.
From NTS.Proofs Require Import Distance Overlay OverlayGraph
                               BufferAssembly RingExtract RingSimple
                               BufferCorrectness.
Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  A hole-free polygon from a noded closed chain is valid (no JCT).       *)
(* -------------------------------------------------------------------------- *)

Theorem valid_polygon_of_noded_chain :
  forall (S : list Edge) (poly : Polygon) (segs : list (Point * Point)),
    pairwise_no_proper_cross S ->
    closed_chain segs ->
    (3 <= length segs)%nat ->
    (forall e, In e segs -> In e S) ->
    outer_ring poly = ring_of_chain segs ->
    hole_rings poly = [] ->
    valid_polygon poly.
Proof.
  intros S poly segs Hpw Hcc Hlen Hsub Houter Hholes.
  destruct (face_walk_core segs Hcc Hlen) as [Hclosed [Hmin Hedges]].
  unfold valid_polygon. rewrite Houter, Hholes.
  split; [ exact Hclosed | ].
  split; [ apply (ring_simple_of_subset S);
           [ exact Hpw
           | intros e He; rewrite Hedges in He; apply Hsub; exact He ] | ].
  split; [ exact Hmin | ].
  intros hr Hhr. destruct Hhr.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  With holes: the hole clause is the named residual (= H1/JCT).          *)
(* -------------------------------------------------------------------------- *)

Theorem valid_polygon_with_holes :
  forall (S : list Edge) (poly : Polygon) (segs : list (Point * Point)),
    pairwise_no_proper_cross S ->
    closed_chain segs ->
    (3 <= length segs)%nat ->
    (forall e, In e segs -> In e S) ->
    outer_ring poly = ring_of_chain segs ->
    (forall h, In h (hole_rings poly) ->
       ring_closed h /\ ring_simple h /\ ring_has_minimum_points h /\
       hole_inside_outer (outer_ring poly) h) ->
    valid_polygon poly.
Proof.
  intros S poly segs Hpw Hcc Hlen Hsub Houter Hholes.
  destruct (face_walk_core segs Hcc Hlen) as [Hclosed [Hmin Hedges]].
  unfold valid_polygon. rewrite Houter.
  split; [ exact Hclosed | ].
  split; [ apply (ring_simple_of_subset S);
           [ exact Hpw
           | intros e He; rewrite Hedges in He; apply Hsub; exact He ] | ].
  split; [ exact Hmin | ].
  rewrite <- Houter. exact Hholes.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Discharging H_valid of buffer_correct_conditional.                     *)
(* -------------------------------------------------------------------------- *)

(* The structural spec on a face extractor: every emitted polygon is
   hole-free with outer ring a closed chain (>= 3 segments) drawn from the
   noded set S.  This is what a correct hole-free ring extractor satisfies. *)
Definition chain_extractor_spec
    (extract_buffer : TopologyGraph -> Geometry) (S : list Edge) : Prop :=
  forall (G : TopologyGraph) (poly : Polygon),
    valid_topology_graph G ->
    In poly (extract_buffer G) ->
    hole_rings poly = [] /\
    exists segs, outer_ring poly = ring_of_chain segs /\
                 closed_chain segs /\
                 (3 <= length segs)%nat /\
                 (forall e, In e segs -> In e S).

(* Any extractor meeting the spec satisfies H_valid -- no JCT residual. *)
Theorem H_valid_of_chain_extractor :
  forall (extract_buffer : TopologyGraph -> Geometry) (S : list Edge),
    pairwise_no_proper_cross S ->
    chain_extractor_spec extract_buffer S ->
    forall G : TopologyGraph,
      valid_topology_graph G -> valid_geometry (extract_buffer G).
Proof.
  intros extract_buffer S Hpw Hspec G HG poly Hin.
  destruct (Hspec G poly HG Hin) as [Hholes [segs [Houter [Hcc [Hlen Hsub]]]]].
  apply (valid_polygon_of_noded_chain S poly segs); assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Capstone: buffer_correct_conditional with H_valid discharged.          *)
(*     Only the semantic H_bridge remains a hypothesis.                       *)
(* -------------------------------------------------------------------------- *)

Theorem buffer_correct_hole_free :
  forall (node : list (Point * Point) -> list (Point * Point))
         (extract_buffer : TopologyGraph -> Geometry)
         (S : list Edge) (g : Geometry) (d : R) (p : Point),
    valid_geometry g ->
    0 <= d ->
    pairwise_no_proper_cross S ->
    chain_extractor_spec extract_buffer S ->
    (forall G : TopologyGraph,
       valid_topology_graph G ->
       valid_geometry (extract_buffer G) ->
       (point_set (extract_buffer G) p <-> buffer_spec g d p)) ->
    point_set (extract_buffer (build_graph (node (offset_curve g d)))) p
      <-> buffer_spec g d p.
Proof.
  intros node extract_buffer S g d p Hg Hd Hpw Hspec H_bridge.
  apply (buffer_correct_conditional node extract_buffer g d p Hg Hd).
  - apply (H_valid_of_chain_extractor extract_buffer S); assumption.
  - exact H_bridge.
Qed.
