(* ============================================================================
   NetTopologySuite.Proofs.SheetRingPipStmt
   ----------------------------------------------------------------------------
   STATEMENTS ONLY (no Lemma / Theorem / Proof here).  The statement half of
   claimId `sheet-pip-transport` (statement C of the shear plan, point
   location); the proof half is SheetRingPip.v, which must prove exactly
   `claim`, `supporting` and `witness` below.  The code of this file
   (comments excluded) is pinned by sha256 in docs/claim-statements.json and
   checked by scripts/check_claim_statements.py.

   The canonical point-in-ring test is the half-open east-ray parity
   `JCTHalfOpenParity.point_in_ring_ho`.  Its ray and its half-open y test
   are tied to the axes of the sheet, so after a change of sheet
   S -> S' = (f O; L e1, L e2) the test on S' casts its ray in the pulled-back
   direction L^-1 e1, not along e1.  Agreement of the two tests is the
   direction-independence of parity, i.e. Jordan-curve content.  It is
   stated here for the rings on which the corpus closes the polygonal Jordan
   seam (JCTEscapeDescentHolds.parity_seam_offring_taut): taut, vertex-proper
   (ring_core_nodup), at least four points and without horizontal edges.
   Tautness, properness and the point count are affine invariants (proved,
   supporting); horizontality is not, so "no horizontal edge" is assumed on
   both sheets.  No guard on the point: any point off the ring.

   Objects.  Rings `Overlay.Ring` (vertex lists, closing vertex repeated),
   the off-ring predicate `PointInRingTangents.ring_complement`, the
   topological interior `JordanCurveSeam.geometric_interior_cont` (off the
   ring and in a bounded complement component), affine maps `Aff2` of
   ClothoidAffineStmt acting on rings vertex-wise.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending
   (review.status in docs/claim-statements.json).
   ========================================================================== *)

From Stdlib Require Import Reals List.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam
  JCTHalfOpenParity JCTTautClearance JCTRingCycle JCTHugStep ConvexChainSplit
  ClothoidPlacement ClothoidAffineStmt.
Import ListNotations.

Local Open Scope R_scope.

Definition ring_act (f : Aff2) (r : Ring) : Ring := map (aff_ap f) r.

(* The rings on which the corpus closes the polygonal Jordan seam. *)
Definition seam_ring (r : Ring) : Prop :=
  ring_taut r /\ ring_core_nodup r /\ ring_has_minimum_points r /\
  no_horizontal_edges r.

(* The vertical shear (x, y) |-> (x, y + x / 2): not a similarity, and it
   turns the east ray of S' into the direction (1, -1/2) on S. *)
Definition vshear_half : Aff2 := mkAff2 (mkPoint 0 0) (mkLin2 1 0 (1 / 2) 1).

(* main: for an invertible affine map and a ring that is a seam ring on both
   sheets, the canonical half-open east-ray test at any off-ring point gives
   the same answer on S and on S'. *)
Definition claim : Prop :=
  forall f r p,
    lin_det (af_L f) <> 0 ->
    seam_ring r -> no_horizontal_edges (ring_act f r) ->
    ring_complement r p ->
    (point_in_ring_ho p r <-> point_in_ring_ho (aff_ap f p) (ring_act f r)).

(* supporting: the topological side transports for every ring (off-ring and
   bounded-component interior), and so do the seam conditions other than
   horizontality. *)
Definition supporting : Prop :=
  (forall f r q, lin_det (af_L f) <> 0 ->
     (ring_complement r q <-> ring_complement (ring_act f r) (aff_ap f q)))
  /\ (forall f r p, lin_det (af_L f) <> 0 ->
        (geometric_interior_cont p r
         <-> geometric_interior_cont (aff_ap f p) (ring_act f r)))
  /\ (forall f r, lin_det (af_L f) <> 0 ->
        (ring_taut r -> ring_taut (ring_act f r)) /\
        (ring_core_nodup r -> ring_core_nodup (ring_act f r)) /\
        (ring_has_minimum_points r -> ring_has_minimum_points (ring_act f r))).

(* witness: the corpus diamond (vertices (0,-2), (2,0), (0,2), (-2,0)) and its
   image under the non-similarity vshear_half are seam rings on their sheets;
   the origin is off the ring and inside by the canonical test on both
   sheets. *)
Definition witness : Prop :=
  seam_ring diamond_ring /\ no_horizontal_edges (ring_act vshear_half diamond_ring) /\
  l11 (af_L vshear_half) * l11 (af_L vshear_half)
    + l21 (af_L vshear_half) * l21 (af_L vshear_half)
    <> l12 (af_L vshear_half) * l12 (af_L vshear_half)
       + l22 (af_L vshear_half) * l22 (af_L vshear_half) /\
  ring_complement diamond_ring (mkPoint 0 0) /\
  point_in_ring_ho (mkPoint 0 0) diamond_ring /\
  point_in_ring_ho (aff_ap vshear_half (mkPoint 0 0)) (ring_act vshear_half diamond_ring).
