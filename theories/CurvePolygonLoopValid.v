(* ============================================================================
   NetTopologySuite.Proofs.CurvePolygonLoopValid
   ----------------------------------------------------------------------------
   Multi rung 5, M2. claimId: 0007-cp-loop-rings.
   witness: curve_polygon_from_loop.
   Ring validity from the loop fixpoint plus no coincident pieces:
   closed, simple per ring via SheetHenSimple.cscc_issimple, and noded
   (bag_noded_ov).
   theories/CurvePolygonValid.v is the earlier holes-inside-shell slice.
   This file does not edit it and does not import CurveRingWinding.
   holes_nest_in_outer is the lane-D nesting hypothesis.
   hole_polygon_fixtures is one polygon with a hole. claimId: none.
   3-axiom host. No Admitted.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List.
From NTS.Proofs Require Import
  Distance CurveGeometry SheetHenCook SheetHenCookCore SheetHenBag
  SheetHenCircEgg SheetHenRho SheetHenNodedOv SheetHenPickSpec
  SheetHenRhoLoop SheetHenBagRunFix SheetHenSimple.
Import ListNotations.
Local Open Scope R_scope.

Definition segment_on_piece (s : CurveSegment) (pc : BagPiece) : Prop :=
  curve_segment_start s =
    support_at (bp_support pc) (win_lo (bp_window pc)) /\
  curve_segment_end s =
    support_at (bp_support pc) (win_hi (bp_window pc)) /\
  match s, bp_support pc with
  | CSChord _ _, SuppChord _ => True
  | CSArc _, SuppCircle _ => True
  | _, _ => False
  end.

Fixpoint ring_on_pieces (r : CurveRing) (pcs : list BagPiece) : Prop :=
  match r, pcs with
  | nil, nil => True
  | s :: rs, pc :: ps => segment_on_piece s pc /\ ring_on_pieces rs ps
  | _, _ => False
  end.

Definition ring_realized (r : CurveRing) (b : SheetBag) : Prop :=
  match b with
  | BagLive _ pcs => ring_on_pieces r pcs
  | BagDeclined _ => False
  end.

Definition loop_ring_from_fixpoint (r : CurveRing) (b : SheetBag) : Prop :=
  curve_ring_closed r /\
  ring_realized r b /\
  loop_carrier b /\
  cscc_IsSimple b /\
  match b with
  | BagLive _ _ => bag_noded_ov b
  | BagDeclined _ => False
  end.

Lemma loop_ring_of_fixpoint : forall r b,
  curve_ring_closed r ->
  ring_realized r b ->
  loop_carrier b ->
  loop_fixpoint_adds_no_interior b ->
  no_coincident_pieces b ->
  loop_ring_from_fixpoint r b.
Proof.
  intros r b Hc Hr Hcar Hfix Hnc.
  assert (Hs : cscc_IsSimple b).
  { apply (proj2 (cscc_issimple b Hcar)). split; [exact Hfix| exact Hnc]. }
  split; [exact Hc|]. split; [exact Hr|]. split; [exact Hcar|].
  split; [exact Hs|].
  destruct b as [sh pcs|sh].
  - apply meets_at_vertices_noded_ov. exact (proj1 Hs).
  - exact Hcar.
Qed.

(* Premises the fixpoint supplies for each hole ring. Nesting is not one. *)
Fixpoint hole_fixpoint_premises (rs : list CurveRing) (bs : list SheetBag)
  : Prop :=
  match rs, bs with
  | nil, nil => True
  | r :: rt, b :: bt =>
      curve_ring_closed r /\ ring_realized r b /\
      loop_carrier b /\ loop_fixpoint_adds_no_interior b /\
      no_coincident_pieces b /\ hole_fixpoint_premises rt bt
  | _, _ => False
  end.

Fixpoint rings_from_fixpoint (rs : list CurveRing) (bs : list SheetBag)
  : Prop :=
  match rs, bs with
  | nil, nil => True
  | r :: rt, b :: bt =>
      loop_ring_from_fixpoint r b /\ rings_from_fixpoint rt bt
  | _, _ => False
  end.

Lemma holes_from_fixpoint : forall rs bs,
  hole_fixpoint_premises rs bs -> rings_from_fixpoint rs bs.
Proof.
  induction rs as [|r rt IH]; intros bs H.
  - destruct bs as [|b bt]; [exact H| exact H].
  - destruct bs as [|b bt]; [exact H|].
    simpl in H. destruct H as [Hc [Hr [Hcar [Hfix [Hnc Ht]]]]].
    split.
    + apply loop_ring_of_fixpoint; assumption.
    + apply IH. exact Ht.
Qed.

Definition curve_polygon_loop_valid (cp : CurvePolygon) (ou : SheetBag)
    (hs : list SheetBag) (holes_nest_in_outer : Prop) : Prop :=
  loop_ring_from_fixpoint (curve_outer cp) ou /\
  rings_from_fixpoint (curve_holes cp) hs /\
  holes_nest_in_outer.

(* WITNESS {"claimId":"0007-cp-loop-rings","topic":"overlay","lemma":"curve_polygon_from_loop","title":"CurvePolygon rings are closed, simple, and noded from the loop fixpoint with no coincident pieces","file":"theories/CurvePolygonLoopValid.v","witness":"curve_polygon_from_loop","board":"ADR-0007"} *)
Theorem curve_polygon_from_loop : forall cp ou hs (holes_nest_in_outer : Prop),
  curve_ring_closed (curve_outer cp) ->
  ring_realized (curve_outer cp) ou ->
  loop_carrier ou ->
  loop_fixpoint_adds_no_interior ou ->
  no_coincident_pieces ou ->
  hole_fixpoint_premises (curve_holes cp) hs ->
  holes_nest_in_outer ->
  curve_polygon_loop_valid cp ou hs holes_nest_in_outer.
Proof.
  intros cp ou hs holes_nest_in_outer Hc Hr Hcar Hfix Hnc Hh Hnest.
  split.
  - apply loop_ring_of_fixpoint; assumption.
  - split.
    + apply holes_from_fixpoint. exact Hh.
    + exact Hnest.
Qed.

(* -------------------------------------------------------------------------- *)
(* Fixture. Outer ring is the two half-turns. The hole is a closed point     *)
(* chord. Nesting is not claimed.                                             *)
(* -------------------------------------------------------------------------- *)

Definition poly_outer_ring : CurveRing :=
  [CSArc (mkCircularArc (circ_eval iso_half_fst 0)
                        (circ_eval iso_half_fst (1 / 2))
                        (circ_eval iso_half_fst 1));
   CSArc (mkCircularArc (circ_eval iso_half_snd 0)
                        (circ_eval iso_half_snd (1 / 2))
                        (circ_eval iso_half_snd 1))].

Definition poly_hole_pt : Point := mkPoint 1 0.
Definition poly_hole_chord : ChordEgg :=
  mkChordEgg poly_hole_pt poly_hole_pt.
Definition poly_hole_pc : BagPiece :=
  mkBagPiece
    (mkChicken 0%nat 1%nat
       (MkChord (window_chord poly_hole_chord (mkWindow 0 1))))
    (SuppChord poly_hole_chord) (mkWindow 0 1) nil.
Definition poly_hole_pcs : list BagPiece := [poly_hole_pc].
Definition poly_hole_bag : SheetBag := BagLive default_sheet poly_hole_pcs.
Definition poly_hole_ring : CurveRing :=
  [CSChord poly_hole_pt poly_hole_pt].
Definition poly_with_hole : CurvePolygon :=
  mkCurvePolygon poly_outer_ring [poly_hole_ring].

Lemma half_joint : circ_eval iso_half_fst 1 = circ_eval iso_half_snd 0.
Proof.
  unfold circ_eval, iso_half_fst, iso_half_snd.
  cbn [circ_o circ_r circ_theta0 circ_sweep px py].
  replace (0 + 1 * PI) with (PI + 0 * PI) by ring.
  reflexivity.
Qed.

Lemma half_close : circ_eval iso_half_snd 1 = circ_eval iso_half_fst 0.
Proof.
  unfold circ_eval, iso_half_snd, iso_half_fst.
  cbn [circ_o circ_r circ_theta0 circ_sweep px py].
  apply (f_equal2 mkPoint).
  - replace (PI + 1 * PI) with (2 * PI) by ring.
    replace (0 + 0 * PI) with 0 by ring.
    rewrite cos_2PI, cos_0. ring.
  - replace (PI + 1 * PI) with (2 * PI) by ring.
    replace (0 + 0 * PI) with 0 by ring.
    rewrite sin_2PI, sin_0. ring.
Qed.

Lemma outer_closed : curve_ring_closed poly_outer_ring.
Proof.
  unfold curve_ring_closed, poly_outer_ring, curve_segment_end,
    curve_segment_start. simpl.
  unfold arc_end, arc_start. exact half_close.
Qed.

Lemma outer_realized : ring_realized poly_outer_ring iso_half_bag.
Proof.
  unfold ring_realized, iso_half_bag, poly_outer_ring, iso_half_pcs,
    ring_on_pieces, segment_on_piece, curve_segment_start, curve_segment_end,
    arc_start, arc_end, iso_half_pc, support_at, win_lo, win_hi.
  repeat split; reflexivity.
Qed.

Lemma hole_closed : curve_ring_closed poly_hole_ring.
Proof.
  unfold curve_ring_closed, poly_hole_ring, curve_segment_end,
    curve_segment_start. simpl. reflexivity.
Qed.

Lemma hole_piece_wf : piece_wf poly_hole_pc.
Proof.
  split.
  - unfold piece_realizes, poly_hole_pc. simpl. reflexivity.
  - unfold window_ordered, poly_hole_pc. simpl. lra.
Qed.

Lemma hole_carrier : loop_carrier poly_hole_bag.
Proof.
  unfold loop_carrier, poly_hole_bag. split.
  - intros pc Hin. unfold poly_hole_pcs in Hin.
    destruct Hin as [<-|[]]. apply hole_piece_wf.
  - intros a c Ha Hc Hneq _.
    unfold poly_hole_pcs in Ha, Hc.
    destruct Ha as [<-|[]]. destruct Hc as [<-|[]].
    contradict Hneq. reflexivity.
Qed.

Lemma hole_rho : rho_pcs poly_hole_pcs = 0%nat.
Proof.
  unfold rho_pcs, poly_hole_pcs, supports_of. simpl. reflexivity.
Qed.

Lemma hole_no_interior : loop_fixpoint_adds_no_interior poly_hole_bag.
Proof.
  unfold loop_fixpoint_adds_no_interior, poly_hole_bag, rho.
  rewrite hole_rho.
  assert (E : bag_run_arm 1%nat (BagLive default_sheet poly_hole_pcs) =
              BagLive default_sheet poly_hole_pcs).
  { apply (rho_zero_arm_fix 1%nat default_sheet poly_hole_pcs).
    - exact (proj1 hole_carrier).
    - exact (proj2 hole_carrier).
    - exact hole_rho. }
  rewrite E. intros s p Hv. exact Hv.
Qed.

Lemma hole_no_coincident : no_coincident_pieces poly_hole_bag.
Proof.
  unfold no_coincident_pieces, poly_hole_bag, poly_hole_pcs.
  intros i j a c Hi Hj Hij.
  destruct i as [|i]; destruct j as [|j].
  - exfalso. apply Hij. reflexivity.
  - destruct j; discriminate Hj.
  - destruct i; discriminate Hi.
  - destruct i; discriminate Hi.
Qed.

Lemma hole_realized : ring_realized poly_hole_ring poly_hole_bag.
Proof.
  unfold ring_realized, poly_hole_bag, poly_hole_ring, poly_hole_pcs,
    ring_on_pieces, segment_on_piece, curve_segment_start, curve_segment_end,
    poly_hole_pc, support_at, win_lo, win_hi, chord_eval, window_chord,
    poly_hole_chord, poly_hole_pt.
  simpl. repeat split; apply (f_equal2 mkPoint); ring.
Qed.

Lemma hole_polygon_fixtures :
  loop_ring_from_fixpoint poly_outer_ring iso_half_bag /\
  loop_ring_from_fixpoint poly_hole_ring poly_hole_bag /\
  curve_holes poly_with_hole = [poly_hole_ring].
Proof.
  split.
  - apply loop_ring_of_fixpoint.
    + exact outer_closed.
    + exact outer_realized.
    + exact (proj1 simple_cscc_egg_fixtures).
    + exact (proj1 (proj2 (proj2 simple_cscc_egg_fixtures))).
    + exact (proj2 (proj2 (proj2 simple_cscc_egg_fixtures))).
  - split.
    + apply loop_ring_of_fixpoint.
      * exact hole_closed.
      * exact hole_realized.
      * exact hole_carrier.
      * exact hole_no_interior.
      * exact hole_no_coincident.
    + reflexivity.
Qed.

Print Assumptions loop_ring_of_fixpoint.
Print Assumptions holes_from_fixpoint.
Print Assumptions curve_polygon_from_loop.
Print Assumptions half_joint.
Print Assumptions half_close.
Print Assumptions outer_closed.
Print Assumptions outer_realized.
Print Assumptions hole_closed.
Print Assumptions hole_piece_wf.
Print Assumptions hole_carrier.
Print Assumptions hole_rho.
Print Assumptions hole_no_interior.
Print Assumptions hole_no_coincident.
Print Assumptions hole_realized.
Print Assumptions hole_polygon_fixtures.
