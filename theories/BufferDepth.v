(* ============================================================================
   NetTopologySuite.Proofs.BufferDepth
   ----------------------------------------------------------------------------
   Seam map: docs/buffer-noder-pipeline.md §2.4 (Stage 4b depth labelling) and
   §6 (the H_bridge factorisation through the depth region).
   Stage 4b (depth labelling) + a factorisation of the full buffer H_bridge.

   The buffer pipeline reuses the OverlayNG graph spine but labels edges by
   DEPTH (which side is interior to the d-region) instead of by SOURCE
   (in_left / in_right of two input geometries).  This file:

   (1) DEPTH LABELLING.  Reusing `EdgeLabel` with `in_left` / `in_right` read
       as "the left/right side of the offset edge is interior to the buffer",
       the result-boundary rule "keep an edge iff exactly one side is
       interior" is exactly the SymDiff edge rule
       (`buffer_edge_in_result = edge_in_result SymDiff`,
       `buffer_edge_in_result_symdiff`).  `kept_edges` is the result boundary;
       it inherits graph validity (`kept_edges_in_vertices`).

   (2) THE DEPTH REGION.  The buffer interior is the crossing-number interior
       of the kept boundary edges (`depth_region`, reusing Overlay's
       `ray_parity_odd`).  Concrete -- no parameter.  The empty graph encloses
       nothing (`depth_region_empty`).

   (3) H_BRIDGE FACTORISATION.  The monolithic semantic bridge
         point_set (extract_buffer G) p  <->  buffer_spec g d p
       factors through the depth boundary into two CONCRETE seams:
         - `extract_realizes_depth`: the extractor's point-set is the depth
           region of the kept edges (the DCEL ring-assembly / extract content);
         - `depth_region_is_buffer`: the depth region equals the
           d-neighbourhood (the offset-soundness + depth-correctness + JCT
           analytic content -- pinned at the corner level in
           BufferBridge{Sound,Complete,Round}).
       `buffer_H_bridge_factor` composes them (Qed); `buffer_correct_via_depth`
       threads them through the end-to-end pipeline graph.  The full bridge is
       NOT manufactured -- the two seams remain the precise, named residual,
       and the base case (empty geometry) is discharged unconditionally
       (`depth_region_is_buffer_empty`).

   Pure-R; reuses only Overlay / OverlayGraph / BufferCorrectness (classic-
   free).  Three-axiom footprint.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals List.
From NTS.Proofs Require Import Distance Overlay OverlayGraph BufferCorrectness.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Depth labelling: the result-boundary rule is the SymDiff edge rule.    *)
(* -------------------------------------------------------------------------- *)

(* Reusing EdgeLabel: in_left / in_right now mean "the left / right side of
   this offset edge lies interior to the buffer region".  An edge is on the
   result boundary iff exactly one of its sides is interior. *)
Definition buffer_edge_in_result (l : EdgeLabel) : bool :=
  xorb (in_left l) (in_right l).

(* The depth (keep-the-boundary) rule is literally the SymDiff overlay rule. *)
Lemma buffer_edge_in_result_symdiff :
  forall l : EdgeLabel, buffer_edge_in_result l = edge_in_result SymDiff l.
Proof. intro l. reflexivity. Qed.

(* The result boundary: the edges the depth rule keeps. *)
Definition kept_edges (G : TopologyGraph) : list (Point * Point * EdgeLabel) :=
  filter (fun e => buffer_edge_in_result (snd e)) (tg_edges G).

(* The boundary edges inherit the graph's well-formedness. *)
Lemma kept_edges_in_vertices :
  forall (G : TopologyGraph),
    valid_topology_graph G ->
    forall p q l, In (p, q, l) (kept_edges G) ->
      In p (tg_vertices G) /\ In q (tg_vertices G).
Proof.
  intros G HG p q l Hin. unfold kept_edges in Hin.
  apply filter_In in Hin. destruct Hin as [Hin _].
  exact (HG p q l Hin).
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The depth region (crossing-number interior of the kept boundary).      *)
(* -------------------------------------------------------------------------- *)

(* Strip labels from a labelled-edge list to a plain edge list. *)
Definition edges_of (E : list (Point * Point * EdgeLabel)) : list Edge :=
  map fst E.

(* A point is in the buffer interior iff a rightward ray crosses an odd
   number of result-boundary edges -- the crossing-number rule of
   Overlay.point_in_ring, applied to the kept edges. *)
Definition depth_region (G : TopologyGraph) (p : Point) : Prop :=
  ray_parity_odd p (edges_of (kept_edges G)).

(* SCOPE CAVEAT (see theories/BufferDepthEnclosureCounterexample.v +
   docs/buffer-depth-enclosure-counterexample.md).  `depth_region` runs ray
   parity over `kept_edges` with NO guard that they form a CLOSED boundary.
   Crossing parity is a sound enclosure test only for a closed boundary: for an
   open kept-edge set (e.g. a single "spur" edge) `depth_region` is not even
   constant on a complement component (`spur_depth_not_component_invariant`).
   A `depth_region`/`depth_region_is_buffer` used for correctness should carry a
   closed-boundary premise -- the general form being "even kept-degree at every
   vertex" (the boundary decomposes into closed cycles).  Closure is necessary
   but NOT sufficient: even a closed kept boundary is misclassified when a kept
   edge is horizontal at the ray height (theories/BufferDepthHorizontalEdge-
   Counterexample.v) -- so `depth_region` also needs the generic-position guards
   of the parity seam, `no_horizontal_edge_at` and `ray_avoids_vertices`
   (PointInRingCorrect.v), on the kept boundary, exactly as `point_in_ring`
   does (JCT.v). *)

(* The empty graph has no boundary, hence encloses nothing. *)
Lemma depth_region_empty : forall p, ~ depth_region empty_graph p.
Proof.
  intros p H. unfold depth_region, edges_of, kept_edges, empty_graph in H.
  simpl in H. inversion H.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Factorising the full H_bridge through the depth boundary.              *)
(* -------------------------------------------------------------------------- *)

(* Seam (a): the extractor realises the depth region -- its point-set is the
   crossing-number interior of the kept boundary edges.  This is the
   DCEL / ring-assembly content (the realisation half of extract_rings_valid),
   relating the extracted polygons to the labelled boundary. *)
Definition extract_realizes_depth
    (extract_buffer : TopologyGraph -> Geometry) (G : TopologyGraph) : Prop :=
  forall p, point_set (extract_buffer G) p <-> depth_region G p.

(* Seam (b): the depth region equals the d-neighbourhood.  This is the
   offset-soundness + depth-labelling + JCT analytic content, pinned at the
   corner-distance level in BufferBridge{Sound,Complete,Round}
   (chord d^2/2 < arc d^2 < miter 2 d^2). *)
Definition depth_region_is_buffer
    (G : TopologyGraph) (g : Geometry) (d : R) : Prop :=
  forall p, depth_region G p <-> buffer_spec g d p.

(* The full semantic H_bridge is exactly the conjunction of the two seams. *)
Theorem buffer_H_bridge_factor :
  forall (extract_buffer : TopologyGraph -> Geometry)
         (G : TopologyGraph) (g : Geometry) (d : R),
    extract_realizes_depth extract_buffer G ->
    depth_region_is_buffer G g d ->
    forall p, point_set (extract_buffer G) p <-> buffer_spec g d p.
Proof.
  intros extract_buffer G g d Hreal Hbuf p.
  rewrite (Hreal p). apply Hbuf.
Qed.

(* End-to-end capstone: with the two depth seams holding on the pipeline
   graph, the buffer is exactly the d-neighbourhood -- the depth-labelled
   instantiation of buffer_correct_conditional's H_bridge. *)
Theorem buffer_correct_via_depth :
  forall (node : list (Point * Point) -> list (Point * Point))
         (extract_buffer : TopologyGraph -> Geometry)
         (g : Geometry) (d : R) (p : Point),
    extract_realizes_depth extract_buffer (build_graph (node (offset_curve g d))) ->
    depth_region_is_buffer (build_graph (node (offset_curve g d))) g d ->
    point_set (extract_buffer (build_graph (node (offset_curve g d)))) p
      <-> buffer_spec g d p.
Proof.
  intros node extract_buffer g d p Hreal Hbuf.
  apply (buffer_H_bridge_factor extract_buffer
           (build_graph (node (offset_curve g d))) g d Hreal Hbuf).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Base case: the empty buffer closes both seams unconditionally.         *)
(* -------------------------------------------------------------------------- *)

Lemma buffer_spec_empty : forall d p, ~ buffer_spec [] d p.
Proof. intros d p [q [[poly [Hin _]] _]]. exact Hin. Qed.

(* For the empty geometry / empty graph, depth_region_is_buffer holds
   unconditionally: both sides are everywhere false. *)
Lemma depth_region_is_buffer_empty :
  forall d, depth_region_is_buffer empty_graph [] d.
Proof.
  intros d p. split.
  - intro H. exfalso. exact (depth_region_empty p H).
  - intro H. exfalso. exact (buffer_spec_empty d p H).
Qed.

Print Assumptions buffer_H_bridge_factor.
Print Assumptions buffer_correct_via_depth.
Print Assumptions depth_region_is_buffer_empty.
