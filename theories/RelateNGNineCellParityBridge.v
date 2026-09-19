(* ============================================================================
   NetTopologySuite.Proofs.RelateNGNineCellParityBridge
   ----------------------------------------------------------------------------
   ADR-0003 letter after Accept: nine-cell parity→spec bridge
   (claimId 0003-nine-cell-parity-bridge).

   Two-tier (law, Accepted 2026-08-22):
     Spec    = OGC open interior (0 < gtri / strict box)
     Compute = half-open ray parity (point_in_ring / edge_crosses_ray)
     Bridge  = guarded parity→spec only
   Unguarded form is already Qed-false:
     RelateNGTouchRED.v : touch_triangle_ii_separation_not_unconditional

   Already QED — do not remint (triangle-local ceiling):
     RelateNGTouchCells.v : gtri_point_in_ring_imp_pos
     RelateNGTouchCells.v : tri_interior_iff_point_set_generic
   under ring_complement / ray_avoids_vertices.

   Missing ctor: GeomDe9imPointsetNineCell
   LEFT only if that ctor inhabits for a general ring
     (not the triangle-local pin, not a vacuous interior,
      not unguarded parity = OGC).
   RIGHT if that ctor is missing. This tip: RIGHT.

   Honesty fences:
     Do not bless parity as OGC interior.
     Do not re-base point_set on 0 < gtri.
     Do not drop bridge guards.
     Do not claim ADR-0003 “now has a Qed bridge”.
     ADR-0003 Status stays Accepted (two-tier spec).
     This letter stops the bridge. QEX ≠ owner accept.
     Do not remint ticket_522_* / ticket_523_*.
     Do not mint leftover Ⅹ. Do not flip nine-cell discharged.
     Do not steal 508-e/g/h. Do not Accept ADR-0008.
     Do not flip LoopDischarged. Do not silent NURBS/geodesic
     / ellipsoid = MkChord. CircGamma stays MkCirc.

   WITNESS topic: relate · claimId: 0003-nine-cell-parity-bridge
   witness: 0003-nine-cell-parity-bridge
   board: ADR-0003
   3-axiom host. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay Segment RectangleJCT.
From NTS.Proofs Require Import PointInRingTangents PointInRingCorrect.
From NTS.Proofs Require Import RelateAreaPoint RelateCurveMatrix.
From NTS.Proofs Require Import GeneralTriangleSeparation.
From NTS.Proofs Require Import RelateNGCore RelateNGTouch RelateNGTouchCells RelateNGTouchRED.
Import ListNotations.
Local Open Scope R_scope.

(* WITNESS: campaign=relate rung=adr-0003-bridge claim=0003-nine-cell-parity-bridge
   file=theories/RelateNGNineCellParityBridge.v
   kind=QEX-named-missing-ctor
   missing=GeomDe9imPointsetNineCell
   ceiling=gtri_point_in_ring_imp_pos,tri_interior_iff_point_set_generic
   cex=touch_triangle_ii_separation_not_unconditional
   not=parity-as-OGC,point_set-rebased-gtri,unguarded-bridge,vacuous-interior
   not=ticket_522,ticket_523,leftover-X,nine-cell-discharged
   not=ADR-0008-Accept,LoopDischarged,508-e,508-g,508-h
   not=CircGamma-reopen,NURBS-as-MkChord,geodesic-as-MkChord
   note=letter-stops-bridge-not-ADR-status *)

(* -------------------------------------------------------------------------- *)
(* Named missing constructor. Inhabitance is general-ring nine-cell           *)
(* BI / side-E* → hand-specified F via the guarded ADR-0003 bridge.           *)
(* That constructor is NONE on this tip.                                      *)
(* -------------------------------------------------------------------------- *)

Inductive NineCellParityBridgeCtor : Type :=
| GeomDe9imPointsetNineCell.

(* General-ring inhabitance — not triangle-local, not vacuous, not
   unguarded parity=OGC. Missing on this tip. *)
Definition general_ring_nine_cell_via_bridge : Prop := False.

Definition nine_cell_parity_bridge_ctor_inhabits
  (c : NineCellParityBridgeCtor) : Prop :=
  match c with
  | GeomDe9imPointsetNineCell => general_ring_nine_cell_via_bridge
  end.

Lemma geom_de9im_pointset_nine_cell_missing :
  ~ nine_cell_parity_bridge_ctor_inhabits GeomDe9imPointsetNineCell.
Proof.
  intro H. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* Triangle-local pin is the ceiling already reached. Do not remint.          *)
(* -------------------------------------------------------------------------- *)

Lemma triangle_local_bridge_ceiling :
  forall ax ay bx by_ cx cy p,
    0 < gdbl ax ay bx by_ cx cy ->
    ring_complement (gtri_ring ax ay bx by_ cx cy) p ->
    ray_avoids_vertices p (gtri_ring ax ay bx by_ cx cy) ->
    point_in_ring p (gtri_ring ax ay bx by_ cx cy) ->
    0 < gtri ax ay bx by_ cx cy p.
Proof.
  exact gtri_point_in_ring_imp_pos.
Qed.

Lemma triangle_local_interior_iff_ceiling :
  forall ax ay bx by_ cx cy p,
    0 < gdbl ax ay bx by_ cx cy ->
    ring_complement (gtri_ring ax ay bx by_ cx cy) p ->
    ray_avoids_vertices p (gtri_ring ax ay bx by_ cx cy) ->
    (tri_interior ax ay bx by_ cx cy p
       <-> point_set (triangle_geometry ax ay bx by_ cx cy) p).
Proof.
  exact tri_interior_iff_point_set_generic.
Qed.

Lemma triangle_local_pin_is_not_general_ring_ctor :
  (forall ax ay bx by_ cx cy p,
     0 < gdbl ax ay bx by_ cx cy ->
     ring_complement (gtri_ring ax ay bx by_ cx cy) p ->
     ray_avoids_vertices p (gtri_ring ax ay bx by_ cx cy) ->
     point_in_ring p (gtri_ring ax ay bx by_ cx cy) ->
     0 < gtri ax ay bx by_ cx cy p)
  /\ (forall ax ay bx by_ cx cy p,
        0 < gdbl ax ay bx by_ cx cy ->
        ring_complement (gtri_ring ax ay bx by_ cx cy) p ->
        ray_avoids_vertices p (gtri_ring ax ay bx by_ cx cy) ->
        (tri_interior ax ay bx by_ cx cy p
           <-> point_set (triangle_geometry ax ay bx by_ cx cy) p))
  /\ ~ nine_cell_parity_bridge_ctor_inhabits GeomDe9imPointsetNineCell.
Proof.
  split; [exact triangle_local_bridge_ceiling|].
  split; [exact triangle_local_interior_iff_ceiling|].
  exact geom_de9im_pointset_nine_cell_missing.
Qed.

Lemma bridge_guards_not_dropped :
  forall ax ay bx by_ cx cy p,
    0 < gdbl ax ay bx by_ cx cy ->
    ring_complement (gtri_ring ax ay bx by_ cx cy) p ->
    ray_avoids_vertices p (gtri_ring ax ay bx by_ cx cy) ->
    point_in_ring p (gtri_ring ax ay bx by_ cx cy) ->
    0 < gtri ax ay bx by_ cx cy p.
Proof.
  exact gtri_point_in_ring_imp_pos.
Qed.

(* -------------------------------------------------------------------------- *)
(* Unguarded cex: parity SInt overlap is not OGC II. Cite, do not remint.     *)
(* -------------------------------------------------------------------------- *)

Lemma unguarded_parity_ii_cex :
  triangles_touch_on_shared_edge
    (mkPoint 0 0) (mkPoint 4 1) (mkPoint 0 2)
    (mkPoint 0 0) (mkPoint 0 2) (mkPoint (-4) 1)
  /\ 0 < gdbl 0 0 4 1 0 2
  /\ 0 < gdbl 0 0 0 2 (-4) 1
  /\ (exists p,
        RelateCurveMatrix.in_stratum RelateCurveMatrix.SInt
          (triangle_geometry 0 0 4 1 0 2) p /\
        RelateCurveMatrix.in_stratum RelateCurveMatrix.SInt
          (triangle_geometry 0 0 0 2 (-4) 1) p).
Proof.
  exact touch_triangle_ii_separation_not_unconditional.
Qed.

(* Parity SInt is not the specified interior: ttc_p is SInt of A
   and algebraically exterior (gtri A < 0). Do not bless parity as OGC. *)
Lemma unguarded_parity_is_not_ogc_interior :
  exists p,
    RelateCurveMatrix.in_stratum RelateCurveMatrix.SInt
      (triangle_geometry 0 0 4 1 0 2) p
    /\ gtri 0 0 4 1 0 2 p < 0.
Proof.
  exists ttc_p.
  split; [exact ttc_in_A | exact ttc_gtri_A_neg].
Qed.

Lemma point_set_not_rebased_on_gtri :
  exists p,
    RelateCurveMatrix.in_stratum RelateCurveMatrix.SInt
      (triangle_geometry 0 0 4 1 0 2) p
    /\ gtri 0 0 4 1 0 2 p < 0.
Proof.
  exact unguarded_parity_is_not_ogc_interior.
Qed.

(* -------------------------------------------------------------------------- *)
(* Half-open compute tier: SInt and SBnd overlap on the unit-square left      *)
(* edge. Unguarded BI = F over point_set is therefore false.                  *)
(* -------------------------------------------------------------------------- *)

Definition unit_sq_left_mid : Point := mkPoint 0 (1 / 2).

Lemma unit_sq_left_mid_sint :
  RelateCurveMatrix.in_stratum RelateCurveMatrix.SInt
    (rect_geometry 0 0 1 1) unit_sq_left_mid.
Proof.
  unfold RelateCurveMatrix.in_stratum, point_set, rect_geometry.
  exists (rect_polygon 0 0 1 1).
  split; [left; reflexivity|].
  apply left_boundary_in_rect_polygon; try lra.
  unfold point_on_rect_left_boundary, unit_sq_left_mid.
  cbn [px py].
  split; [reflexivity|].
  split; lra.
Qed.

Lemma unit_sq_left_mid_on_left_edge :
  RelateCurveMatrix.on_edge unit_sq_left_mid
    (mkPoint 0 1, mkPoint 0 0).
Proof.
  unfold RelateCurveMatrix.on_edge, between, unit_sq_left_mid.
  exists (1 / 2).
  cbn [px py fst snd].
  split; [lra|].
  split; [lra|].
  split; [field|].
  field.
Qed.

Lemma unit_sq_left_mid_sbnd :
  RelateCurveMatrix.in_stratum RelateCurveMatrix.SBnd
    (rect_geometry 0 0 1 1) unit_sq_left_mid.
Proof.
  unfold RelateCurveMatrix.in_stratum, RelateCurveMatrix.geom_boundary,
         rect_geometry.
  exists (rect_polygon 0 0 1 1).
  split; [left; reflexivity|].
  exists (mkPoint 0 1, mkPoint 0 0).
  split.
  - unfold RelateCurveMatrix.poly_edges, rect_polygon, outer_ring, hole_rings.
    simpl.
    rewrite ring_edges_rect.
    simpl.
    right; right; right; left; reflexivity.
  - exact unit_sq_left_mid_on_left_edge.
Qed.

Lemma sint_sbnd_overlap_unit_square :
  exists p,
    RelateCurveMatrix.in_stratum RelateCurveMatrix.SInt
      (rect_geometry 0 0 1 1) p /\
    RelateCurveMatrix.in_stratum RelateCurveMatrix.SBnd
      (rect_geometry 0 0 1 1) p.
Proof.
  exists unit_sq_left_mid.
  split; [exact unit_sq_left_mid_sint | exact unit_sq_left_mid_sbnd].
Qed.

(* Unguarded hand-specified F on BI (SBnd × SInt) fails on this ring:
   the compute-tier strata overlap. Not a general-ring bridge. *)
Lemma unguarded_bi_f_false_on_unit_square :
  ~ RelateCurveMatrix.cell_ok None
      RelateCurveMatrix.SBnd RelateCurveMatrix.SInt
      (rect_geometry 0 0 1 1) (rect_geometry 0 0 1 1).
Proof.
  intros [Hok [Hfwd Hback]].
  apply Hback.
  destruct sint_sbnd_overlap_unit_square as [p [Hint Hbnd]].
  exists p. split; [exact Hbnd | exact Hint].
Qed.

(* -------------------------------------------------------------------------- *)
(* ADR-0003 Status stays Accepted. This letter does not flip it.              *)
(* -------------------------------------------------------------------------- *)

Inductive Adr0003LetterStatus : Type :=
| Adr0003Accepted
| Adr0003StatusFlipped
| Adr0003QedBridgeClaimed.

Definition adr0003_letter_status : Adr0003LetterStatus := Adr0003Accepted.

Lemma adr0003_stays_accepted :
  adr0003_letter_status = Adr0003Accepted.
Proof.
  reflexivity.
Qed.

Lemma adr0003_not_flipped :
  adr0003_letter_status <> Adr0003StatusFlipped.
Proof.
  discriminate.
Qed.

Lemma adr0003_bridge_not_claimed_qed :
  adr0003_letter_status <> Adr0003QedBridgeClaimed.
Proof.
  discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stop.                                               *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0003-nine-cell-parity-bridge","topic":"relate","lemma":"ticket_0003_nine_cell_parity_bridge_qed_or_qex","title":"ADR-0003 nine-cell parity bridge: GeomDe9imPointsetNineCell inhabits for a general ring via the guarded parity-to-spec bridge (QED) or that ctor stays missing while the triangle-local pin is the ceiling and the unguarded cex stands (QEX); discharged QEX; do not bless parity as OGC; do not rebase point_set on 0<gtri; ADR-0003 stays Accepted","file":"theories/RelateNGNineCellParityBridge.v","witness":"0003-nine-cell-parity-bridge","board":"ADR-0003"} *)
Theorem ticket_0003_nine_cell_parity_bridge_qed_or_qex :
  (nine_cell_parity_bridge_ctor_inhabits GeomDe9imPointsetNineCell
   /\ general_ring_nine_cell_via_bridge)
  \/
  (~ nine_cell_parity_bridge_ctor_inhabits GeomDe9imPointsetNineCell
   /\ general_ring_nine_cell_via_bridge = False
   /\ (forall ax ay bx by_ cx cy p,
         0 < gdbl ax ay bx by_ cx cy ->
         ring_complement (gtri_ring ax ay bx by_ cx cy) p ->
         ray_avoids_vertices p (gtri_ring ax ay bx by_ cx cy) ->
         point_in_ring p (gtri_ring ax ay bx by_ cx cy) ->
         0 < gtri ax ay bx by_ cx cy p)
   /\ (forall ax ay bx by_ cx cy p,
         0 < gdbl ax ay bx by_ cx cy ->
         ring_complement (gtri_ring ax ay bx by_ cx cy) p ->
         ray_avoids_vertices p (gtri_ring ax ay bx by_ cx cy) ->
         (tri_interior ax ay bx by_ cx cy p
            <-> point_set (triangle_geometry ax ay bx by_ cx cy) p))
   /\ triangles_touch_on_shared_edge
        (mkPoint 0 0) (mkPoint 4 1) (mkPoint 0 2)
        (mkPoint 0 0) (mkPoint 0 2) (mkPoint (-4) 1)
   /\ (exists p,
         RelateCurveMatrix.in_stratum RelateCurveMatrix.SInt
           (triangle_geometry 0 0 4 1 0 2) p /\
         RelateCurveMatrix.in_stratum RelateCurveMatrix.SInt
           (triangle_geometry 0 0 0 2 (-4) 1) p)
   /\ (exists p,
         RelateCurveMatrix.in_stratum RelateCurveMatrix.SInt
           (triangle_geometry 0 0 4 1 0 2) p
         /\ gtri 0 0 4 1 0 2 p < 0)
   /\ ~ RelateCurveMatrix.cell_ok None
          RelateCurveMatrix.SBnd RelateCurveMatrix.SInt
          (rect_geometry 0 0 1 1) (rect_geometry 0 0 1 1)
   /\ adr0003_letter_status = Adr0003Accepted
   /\ adr0003_letter_status <> Adr0003QedBridgeClaimed).
Proof.
  right.
  split; [exact geom_de9im_pointset_nine_cell_missing|].
  split; [reflexivity|].
  split; [exact triangle_local_bridge_ceiling|].
  split; [exact triangle_local_interior_iff_ceiling|].
  destruct unguarded_parity_ii_cex as [Htouch [_ [_ Hex]]].
  split; [exact Htouch|].
  split; [exact Hex|].
  split; [exact unguarded_parity_is_not_ogc_interior|].
  split; [exact unguarded_bi_f_false_on_unit_square|].
  split; [reflexivity|].
  exact adr0003_bridge_not_claimed_qed.
Qed.

Print Assumptions geom_de9im_pointset_nine_cell_missing.
Print Assumptions triangle_local_bridge_ceiling.
Print Assumptions triangle_local_interior_iff_ceiling.
Print Assumptions triangle_local_pin_is_not_general_ring_ctor.
Print Assumptions bridge_guards_not_dropped.
Print Assumptions unguarded_parity_ii_cex.
Print Assumptions unguarded_parity_is_not_ogc_interior.
Print Assumptions point_set_not_rebased_on_gtri.
Print Assumptions sint_sbnd_overlap_unit_square.
Print Assumptions unguarded_bi_f_false_on_unit_square.
Print Assumptions adr0003_stays_accepted.
Print Assumptions adr0003_bridge_not_claimed_qed.
Print Assumptions ticket_0003_nine_cell_parity_bridge_qed_or_qex.
