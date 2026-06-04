(* ============================================================================
   NetTopologySuite.Proofs.ExtractRingsShell
   ----------------------------------------------------------------------------
   Completing the analytic shell of `extract_rings_valid`
   (docs/extract-rings-proof-structure.md §4, §7 R7).

   `ExtractBufferRings.valid_polygon_with_holes` left the ENTIRE per-hole
   conjunction -- `ring_closed h /\ ring_simple h /\ ring_has_minimum_points h
   /\ hole_inside_outer (outer) h` -- as a single opaque hypothesis.  But the
   first three of those are the SAME combinatorial + noder facts already
   discharged for the outer ring: a hole that is itself a closed chain drawn
   from the noded arrangement is automatically `ring_closed`, `ring_simple`,
   and `ring_has_minimum_points`.

   This file discharges those for holes too, shrinking the residual of the
   WITH-HOLES case to EXACTLY ONE analytic clause: `hole_inside_outer`, the
   point-set nesting bridge (= the H1/JCT gap of `overlay_ng_correct_conditional`
   and R3 of the proof-structure doc).  That is the completed analytic shell:

       valid_polygon  =  [combinatorial core + ring_simple, ALL Qed here]
                         ⊕  hole_inside_outer        (the single named JCT seam)

   - `valid_polygon_noded_shell`: outer + holes are noded closed chains
     (everything but nesting discharged); the only remaining hypothesis is the
     per-hole `hole_inside_outer`.
   - `H_valid_of_chain_extractor_holes`: the extractor-level `H_valid` of
     `buffer_correct_conditional` for the with-holes regime, conditional on
     exactly that one nesting hypothesis -- a strict shrink of the deferred
     `extract_rings_valid`.

   Pure-R; no atan / Flocq.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals List.
From NTS.Proofs Require Import Distance Overlay OverlayGraph
                               BufferAssembly RingExtract RingSimple
                               BufferCorrectness ExtractBufferRings.
Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  A hole that is a noded closed chain has its combinatorial + simplicity *)
(*     conditions for free; only nesting (hole_inside_outer) is analytic.     *)
(* -------------------------------------------------------------------------- *)

(* The combinatorial structure of a hole: it is a closed chain of >= 3
   segments drawn from the noded edge set S.  (The same shape as the outer
   ring's chain -- this is what an assembled face boundary is.) *)
Definition hole_noded_chain (S : list Edge) (h : Ring) : Prop :=
  exists segs : list (Point * Point),
    h = ring_of_chain segs /\
    closed_chain segs /\
    (3 <= length segs)%nat /\
    (forall e, In e segs -> In e S).

(* From the combinatorial structure alone, three of the four hole conditions
   follow -- with NO Jordan-curve content. *)
Lemma hole_noded_chain_conditions :
  forall (S : list Edge) (h : Ring),
    pairwise_no_proper_cross S ->
    hole_noded_chain S h ->
    ring_closed h /\ ring_simple h /\ ring_has_minimum_points h.
Proof.
  intros S h Hpw [segs [Hh [Hcc [Hlen Hsub]]]].
  destruct (face_walk_core segs Hcc Hlen) as [Hclosed [Hmin Hedges]].
  subst h. split; [ exact Hclosed | ].
  split; [ apply (ring_simple_of_subset S);
           [ exact Hpw
           | intros e He; rewrite Hedges in He; apply Hsub; exact He ]
         | exact Hmin ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The completed shell: valid_polygon with the single JCT residual.       *)
(* -------------------------------------------------------------------------- *)

(* A polygon whose outer ring AND every hole are noded closed chains is valid
   as soon as each hole is nested in the outer ring.  Everything except that
   nesting (the combinatorial core + ring_simple, for outer and holes alike)
   is discharged here. *)
Theorem valid_polygon_noded_shell :
  forall (S : list Edge) (poly : Polygon) (segs : list (Point * Point)),
    pairwise_no_proper_cross S ->
    closed_chain segs ->
    (3 <= length segs)%nat ->
    (forall e, In e segs -> In e S) ->
    outer_ring poly = ring_of_chain segs ->
    (forall h, In h (hole_rings poly) -> hole_noded_chain S h) ->
    (* the SINGLE analytic residual: each hole is nested in the outer ring *)
    (forall h, In h (hole_rings poly) -> hole_inside_outer (outer_ring poly) h) ->
    valid_polygon poly.
Proof.
  intros S poly segs Hpw Hcc Hlen Hsub Houter Hholes Hnest.
  destruct (face_walk_core segs Hcc Hlen) as [Hclosed [Hmin Hedges]].
  unfold valid_polygon. rewrite Houter.
  split; [ exact Hclosed | ].
  split; [ apply (ring_simple_of_subset S);
           [ exact Hpw
           | intros e He; rewrite Hedges in He; apply Hsub; exact He ] | ].
  split; [ exact Hmin | ].
  (* The hole clause: combinatorial + simplicity from §1, nesting from Hnest. *)
  intros h Hh.
  destruct (hole_noded_chain_conditions S h Hpw (Hholes h Hh))
    as [Hhc [Hhs Hhm]].
  rewrite <- Houter.
  split; [ exact Hhc | ].
  split; [ exact Hhs | ].
  split; [ exact Hhm | ].
  exact (Hnest h Hh).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Extractor-level H_valid for the with-holes regime.                     *)
(* -------------------------------------------------------------------------- *)

(* The with-holes analogue of chain_extractor_spec: every emitted polygon has
   outer ring and holes all noded closed chains, AND its holes are nested.
   The nesting conjunct is the only piece carrying JCT content. *)
Definition chain_extractor_holes_spec
    (extract_buffer : TopologyGraph -> Geometry) (S : list Edge) : Prop :=
  forall (G : TopologyGraph) (poly : Polygon),
    valid_topology_graph G ->
    In poly (extract_buffer G) ->
    (exists segs, outer_ring poly = ring_of_chain segs /\
                  closed_chain segs /\ (3 <= length segs)%nat /\
                  (forall e, In e segs -> In e S)) /\
    (forall h, In h (hole_rings poly) -> hole_noded_chain S h) /\
    (forall h, In h (hole_rings poly) ->
       hole_inside_outer (outer_ring poly) h).

(* H_valid holds for a with-holes extractor meeting the spec: the proof needs
   no JCT beyond what the spec's nesting conjunct already supplies. *)
Theorem H_valid_of_chain_extractor_holes :
  forall (extract_buffer : TopologyGraph -> Geometry) (S : list Edge),
    pairwise_no_proper_cross S ->
    chain_extractor_holes_spec extract_buffer S ->
    forall G : TopologyGraph,
      valid_topology_graph G -> valid_geometry (extract_buffer G).
Proof.
  intros extract_buffer S Hpw Hspec G HG poly Hin.
  destruct (Hspec G poly HG Hin)
    as [[segs [Houter [Hcc [Hlen Hsub]]]] [Hholes Hnest]].
  apply (valid_polygon_noded_shell S poly segs); assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Capstone: buffer_correct_conditional, holes allowed, H_valid           *)
(*     discharged modulo ONLY the per-hole nesting (JCT) carried in the spec. *)
(* -------------------------------------------------------------------------- *)

Theorem buffer_correct_with_holes :
  forall (node : list (Point * Point) -> list (Point * Point))
         (extract_buffer : TopologyGraph -> Geometry)
         (S : list Edge) (g : Geometry) (d : R) (p : Point),
    valid_geometry g ->
    0 <= d ->
    pairwise_no_proper_cross S ->
    chain_extractor_holes_spec extract_buffer S ->
    (forall G : TopologyGraph,
       valid_topology_graph G ->
       valid_geometry (extract_buffer G) ->
       (point_set (extract_buffer G) p <-> buffer_spec g d p)) ->
    point_set (extract_buffer (build_graph (node (offset_curve g d)))) p
      <-> buffer_spec g d p.
Proof.
  intros node extract_buffer S g d p Hg Hd Hpw Hspec H_bridge.
  apply (buffer_correct_conditional node extract_buffer g d p Hg Hd).
  - apply (H_valid_of_chain_extractor_holes extract_buffer S); assumption.
  - exact H_bridge.
Qed.

Print Assumptions valid_polygon_noded_shell.
Print Assumptions H_valid_of_chain_extractor_holes.
