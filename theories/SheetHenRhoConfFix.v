(* ============================================================================
   NetTopologySuite.Proofs.SheetHenRhoConfFix
   ----------------------------------------------------------------------------
   Letter 6a-iii fixture. claimId: none.
   Three crossing chords. pick_bag hits AB first; pick_rev hits BC first.
   x3_selectors_agree is run_vset_determined on that bag.
   3-axiom host. No Admitted.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List PeanoNat Bool.
From NTS.Proofs Require Import
  Distance SheetHenCook SheetHenCookCore SheetHenBag
  SheetHenRho SheetHenRhoCount SheetHenRhoEnds
  SheetHenBagRun SheetHenLoop3 SheetHenPickSpec
  SheetHenNodedOv SheetHenRhoLoop SheetHenRhoConf HostCircChordOracle.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Three crossing chords. pick_bag hits AB first; pick_rev hits BC first.     *)
(* -------------------------------------------------------------------------- *)

Definition x3_A : ChordEgg := mkChordEgg (mkPoint 0 0) (mkPoint 4 0).
Definition x3_B : ChordEgg := mkChordEgg (mkPoint 0 2) (mkPoint 4 (-2)).
Definition x3_C : ChordEgg := mkChordEgg (mkPoint 1 2) (mkPoint 1 (-2)).
Definition x3_pAB : Point := mkPoint 2 0.
Definition x3_pBC : Point := mkPoint 1 1.

Definition x3_pcA : BagPiece :=
  mkBagPiece (mkChicken 0%nat 1%nat (MkChord x3_A)) (SuppChord x3_A) unit_win [].
Definition x3_pcB : BagPiece :=
  mkBagPiece (mkChicken 2%nat 3%nat (MkChord x3_B)) (SuppChord x3_B) unit_win [].
Definition x3_pcC : BagPiece :=
  mkBagPiece (mkChicken 4%nat 5%nat (MkChord x3_C)) (SuppChord x3_C) unit_win [].
Definition x3_pcs : list BagPiece := [x3_pcA; x3_pcB; x3_pcC].
Definition x3_bag : SheetBag := BagLive default_sheet x3_pcs.

Lemma x3_wf : forall n m c,
  piece_wf (mkBagPiece (mkChicken n m (MkChord c)) (SuppChord c) unit_win []).
Proof.
  intros n m c. unfold piece_wf, piece_realizes. cbn.
  split; [| unfold window_ordered, unit_win; cbn; lra].
  symmetry. apply window_chord_unit.
Qed.

Lemma x3_wfb : forall n m c,
  piece_wf_b (mkBagPiece (mkChicken n m (MkChord c)) (SuppChord c) unit_win [])
  = true.
Proof.
  intros n m c. unfold piece_wf_b. cbn.
  rewrite window_chord_unit. unfold chord_eqb.
  apply andb_true_intro. split.
  - apply andb_true_intro. split; apply pt_eqb_true; reflexivity.
  - unfold unit_win. cbn. apply rle_b_true. lra.
Qed.

Lemma x3_cross_AB :
  req_b (cross2 (chord_dx x3_A) (chord_dy x3_A)
                (chord_dx x3_B) (chord_dy x3_B)) 0 = false.
Proof.
  unfold cross2, chord_dx, chord_dy, x3_A, x3_B. cbn.
  apply req_b_false. lra.
Qed.

Lemma x3_cross_BC :
  req_b (cross2 (chord_dx x3_B) (chord_dy x3_B)
                (chord_dx x3_C) (chord_dy x3_C)) 0 = false.
Proof.
  unfold cross2, chord_dx, chord_dy, x3_B, x3_C. cbn.
  apply req_b_false. lra.
Qed.

Lemma x3_not_same_AB : same_line_b x3_A x3_B = false.
Proof.
  unfold same_line_b, cross2, chord_dx, chord_dy, x3_A, x3_B. cbn.
  assert (Ex : req_b (4 - 0) 0 = false) by (apply req_b_false; lra).
  assert (Ey : req_b (0 - 0) 0 = true) by (apply req_b_true; ring).
  rewrite Ex, Ey. cbn.
  assert (Ec : req_b ((4 - 0) * (-2 - 2) - (0 - 0) * (4 - 0)) 0 = false)
    by (apply req_b_false; lra).
  rewrite Ec. reflexivity.
Qed.

Lemma x3_not_same_BC : same_line_b x3_B x3_C = false.
Proof.
  unfold same_line_b, cross2, chord_dx, chord_dy, x3_B, x3_C. cbn.
  assert (Ex : req_b (4 - 0) 0 = false) by (apply req_b_false; lra).
  assert (Ey : req_b (-2 - 2) 0 = false) by (apply req_b_false; lra).
  rewrite Ex, Ey. cbn.
  assert (Ec : req_b ((4 - 0) * (-2 - 2) - (-2 - 2) * (1 - 1)) 0 = false)
    by (apply req_b_false; lra).
  rewrite Ec. reflexivity.
Qed.

Lemma x3_canon_AB :
  canon2 (SuppChord x3_A) (SuppChord x3_B) =
  (SuppChord x3_A, SuppChord x3_B).
Proof.
  unfold canon2, support_reals, x3_A, x3_B. cbn [px py ce_p0 ce_p1].
  unfold rlex_le.
  destruct (Req_EM_T 0 0) as [_|N0]; [| congruence].
  destruct (Req_EM_T 0 0) as [_|N1]; [| congruence].
  destruct (Req_EM_T 0 2) as [Bad|N2]; [lra|].
  destruct (Rle_dec 0 2) as [_|H]; [| lra]. reflexivity.
Qed.

Lemma x3_canon_BC :
  canon2 (SuppChord x3_B) (SuppChord x3_C) =
  (SuppChord x3_B, SuppChord x3_C).
Proof.
  unfold canon2, support_reals, x3_B, x3_C. cbn [px py ce_p0 ce_p1].
  unfold rlex_le.
  destruct (Req_EM_T 0 0) as [_|N0]; [| congruence].
  destruct (Req_EM_T 0 1) as [Bad|N1]; [lra|].
  destruct (Rle_dec 0 1) as [_|H]; [| lra]. reflexivity.
Qed.

Lemma x3_ll_AB : line_line_pts x3_A x3_B = [x3_pAB].
Proof.
  unfold line_line_pts. rewrite x3_cross_AB.
  assert (Et : cramer_t x3_A x3_B = 1 / 2).
  { unfold cramer_t, cross2, chord_dx, chord_dy, x3_A, x3_B. cbn. field. }
  rewrite Et. unfold chord_eval, x3_A, x3_pAB. cbn.
  apply (f_equal (fun p => [p])). apply (f_equal2 mkPoint); field.
Qed.

Lemma x3_ll_BC : line_line_pts x3_B x3_C = [x3_pBC].
Proof.
  unfold line_line_pts. rewrite x3_cross_BC.
  assert (Et : cramer_t x3_B x3_C = 1 / 4).
  { unfold cramer_t, cross2, chord_dx, chord_dy, x3_B, x3_C. cbn. field. }
  rewrite Et. unfold chord_eval, x3_B, x3_pBC. cbn.
  apply (f_equal (fun p => [p])). apply (f_equal2 mkPoint); field.
Qed.

Lemma x3_img_A_AB : in_image_b x3_pcs (SuppChord x3_A) x3_pAB = true.
Proof.
  apply in_image_spec. exists x3_pcA.
  split; [unfold x3_pcs; left; reflexivity|]. split; [reflexivity|].
  exists (1 / 2). split; [unfold x3_pcA, unit_win; cbn; lra|].
  unfold support_at, x3_pcA, chord_eval, x3_A, x3_pAB. cbn.
  apply (f_equal2 mkPoint); field.
Qed.

Lemma x3_img_B_AB : in_image_b x3_pcs (SuppChord x3_B) x3_pAB = true.
Proof.
  apply in_image_spec. exists x3_pcB.
  split; [unfold x3_pcs; right; left; reflexivity|]. split; [reflexivity|].
  exists (1 / 2). split; [unfold x3_pcB, unit_win; cbn; lra|].
  unfold support_at, x3_pcB, chord_eval, x3_B, x3_pAB. cbn.
  apply (f_equal2 mkPoint); field.
Qed.

Lemma x3_img_B_BC : in_image_b x3_pcs (SuppChord x3_B) x3_pBC = true.
Proof.
  apply in_image_spec. exists x3_pcB.
  split; [unfold x3_pcs; right; left; reflexivity|]. split; [reflexivity|].
  exists (1 / 4). split; [unfold x3_pcB, unit_win; cbn; lra|].
  unfold support_at, x3_pcB, chord_eval, x3_B, x3_pBC. cbn.
  apply (f_equal2 mkPoint); field.
Qed.

Lemma x3_img_C_BC : in_image_b x3_pcs (SuppChord x3_C) x3_pBC = true.
Proof.
  apply in_image_spec. exists x3_pcC.
  split; [unfold x3_pcs; right; right; left; reflexivity|].
  split; [reflexivity|].
  exists (1 / 4). split; [unfold x3_pcC, unit_win; cbn; lra|].
  unfold support_at, x3_pcC, chord_eval, x3_C, x3_pBC. cbn.
  apply (f_equal2 mkPoint); field.
Qed.

Lemma x3_not_vert_A_AB : ~ family_vertex x3_pcs (SuppChord x3_A) x3_pAB.
Proof.
  intros [pc [Hin [Hs Hep]]]. unfold x3_pcs in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]].
  - unfold piece_endpoint, support_at, x3_pcA, unit_win, chord_eval,
      x3_A, x3_pAB in Hep. cbn in Hep.
    destruct Hep as [Hep|Hep]; apply (f_equal px) in Hep; cbn in Hep; lra.
  - unfold x3_pcB in Hs. cbn in Hs. inversion Hs.
    unfold x3_A, x3_B in H0. inversion H0. lra.
  - unfold x3_pcC in Hs. cbn in Hs. inversion Hs.
    unfold x3_A, x3_C in H0. inversion H0. lra.
Qed.

Lemma x3_not_vert_B_BC : ~ family_vertex x3_pcs (SuppChord x3_B) x3_pBC.
Proof.
  intros [pc [Hin [Hs Hep]]]. unfold x3_pcs in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]].
  - unfold x3_pcA in Hs. cbn in Hs. inversion Hs.
    unfold x3_B, x3_A in H0. inversion H0. lra.
  - unfold piece_endpoint, support_at, x3_pcB, unit_win, chord_eval,
      x3_B, x3_pBC in Hep. cbn in Hep.
    destruct Hep as [Hep|Hep]; apply (f_equal px) in Hep; cbn in Hep; lra.
  - unfold x3_pcC in Hs. cbn in Hs. inversion Hs.
    unfold x3_B, x3_C in H0. inversion H0. lra.
Qed.

Lemma x3_ov_AB : overlap_b (SuppChord x3_A) (SuppChord x3_B) = false.
Proof. unfold overlap_b. rewrite x3_canon_AB. exact x3_not_same_AB. Qed.

Lemma x3_ov_BC : overlap_b (SuppChord x3_B) (SuppChord x3_C) = false.
Proof. unfold overlap_b. rewrite x3_canon_BC. exact x3_not_same_BC. Qed.

Lemma x3_keep_AB : keep_b x3_pcs (SuppChord x3_A) (SuppChord x3_B) x3_pAB = true.
Proof.
  unfold keep_b. rewrite x3_img_A_AB, x3_img_B_AB.
  assert (Hv : vertex_b x3_pcs (SuppChord x3_A) x3_pAB = false).
  { destruct (vertex_b x3_pcs (SuppChord x3_A) x3_pAB) eqn:Ev; [| reflexivity].
    apply vertex_spec in Ev. exfalso. exact (x3_not_vert_A_AB Ev). }
  rewrite Hv. reflexivity.
Qed.

Lemma x3_keep_BC : keep_b x3_pcs (SuppChord x3_B) (SuppChord x3_C) x3_pBC = true.
Proof.
  unfold keep_b. rewrite x3_img_B_BC, x3_img_C_BC.
  assert (Hv : vertex_b x3_pcs (SuppChord x3_B) x3_pBC = false).
  { destruct (vertex_b x3_pcs (SuppChord x3_B) x3_pBC) eqn:Ev; [| reflexivity].
    apply vertex_spec in Ev. exfalso. exact (x3_not_vert_B_BC Ev). }
  rewrite Hv. reflexivity.
Qed.

Opaque keep_b.

Lemma x3_counted_AB :
  counted x3_pcs (SuppChord x3_A) (SuppChord x3_B) = [x3_pAB].
Proof.
  unfold counted, counted_raw, raw_pts.
  rewrite x3_canon_AB. cbn -[keep_b].
  rewrite x3_not_same_AB, x3_ll_AB. cbn -[keep_b].
  rewrite x3_keep_AB. cbn -[keep_b]. reflexivity.
Qed.

Lemma x3_counted_BC :
  counted x3_pcs (SuppChord x3_B) (SuppChord x3_C) = [x3_pBC].
Proof.
  unfold counted, counted_raw, raw_pts.
  rewrite x3_canon_BC. cbn -[keep_b].
  rewrite x3_not_same_BC, x3_ll_BC. cbn -[keep_b].
  rewrite x3_keep_BC. cbn -[keep_b]. reflexivity.
Qed.

Transparent keep_b.

Lemma x3_dd_A : req_b (chord_dd x3_A) 0 = false.
Proof.
  unfold chord_dd, chord_dx, chord_dy, x3_A. cbn. apply req_b_false. lra.
Qed.

Lemma x3_dd_B : req_b (chord_dd x3_B) 0 = false.
Proof.
  unfold chord_dd, chord_dx, chord_dy, x3_B. cbn. apply req_b_false. lra.
Qed.

Lemma x3_dd_C : req_b (chord_dd x3_C) 0 = false.
Proof.
  unfold chord_dd, chord_dx, chord_dy, x3_C. cbn. apply req_b_false. lra.
Qed.

Lemma x3_cook_A_AB : cook_t_chord x3_A x3_pAB = 1 / 2.
Proof.
  unfold cook_t_chord. rewrite x3_dd_A.
  unfold chord_param, chord_dd, chord_dx, chord_dy, x3_A, x3_pAB. cbn. field.
Qed.

Lemma x3_cook_B_AB : cook_t_chord x3_B x3_pAB = 1 / 2.
Proof.
  unfold cook_t_chord. rewrite x3_dd_B.
  unfold chord_param, chord_dd, chord_dx, chord_dy, x3_B, x3_pAB. cbn. field.
Qed.

Lemma x3_cook_B_BC : cook_t_chord x3_B x3_pBC = 1 / 4.
Proof.
  unfold cook_t_chord. rewrite x3_dd_B.
  unfold chord_param, chord_dd, chord_dx, chord_dy, x3_B, x3_pBC. cbn. field.
Qed.

Lemma x3_cook_C_BC : cook_t_chord x3_C x3_pBC = 1 / 4.
Proof.
  unfold cook_t_chord. rewrite x3_dd_C.
  unfold chord_param, chord_dd, chord_dx, chord_dy, x3_C, x3_pBC. cbn. field.
Qed.

Lemma x3_hit_AB :
  admissible_hit_b x3_pcs x3_pcA x3_pcB x3_pAB (1 / 2) (1 / 2) = true.
Proof.
  apply admissible_hit_spec. split; [| split].
  - unfold x3_pcA, x3_pcB. cbn. split.
    + split; [lra|]. unfold chord_eval, x3_A, x3_pAB. cbn.
      apply (f_equal2 mkPoint); field.
    + split; [lra|]. unfold chord_eval, x3_B, x3_pAB. cbn.
      apply (f_equal2 mkPoint); field.
  - intro Hv. apply x3_not_vert_A_AB. exact (proj1 Hv).
  - intro Ho. unfold overlap, x3_pcA, x3_pcB in Ho. cbn in Ho.
    rewrite x3_ov_AB in Ho. discriminate.
Qed.

Lemma x3_hit_BC :
  admissible_hit_b x3_pcs x3_pcB x3_pcC x3_pBC (1 / 4) (1 / 4) = true.
Proof.
  apply admissible_hit_spec. split; [| split].
  - unfold x3_pcB, x3_pcC. cbn. split.
    + split; [lra|]. unfold chord_eval, x3_B, x3_pBC. cbn.
      apply (f_equal2 mkPoint); field.
    + split; [lra|]. unfold chord_eval, x3_C, x3_pBC. cbn.
      apply (f_equal2 mkPoint); field.
  - intro Hv. apply x3_not_vert_B_BC. exact (proj1 Hv).
  - intro Ho. unfold overlap, x3_pcB, x3_pcC in Ho. cbn in Ho.
    rewrite x3_ov_BC in Ho. discriminate.
Qed.

Lemma x3_least_AB :
  least_ti (adm_list x3_pcs x3_pcA x3_pcB) =
  Some (mkHitCand x3_pAB (1 / 2) (1 / 2)).
Proof.
  unfold adm_list.
  replace (bp_support x3_pcA) with (SuppChord x3_A) by reflexivity.
  replace (bp_support x3_pcB) with (SuppChord x3_B) by reflexivity.
  rewrite x3_counted_AB. unfold cands_of, cook_t_egg.
  replace (ck_egg (bp_ck x3_pcA)) with (MkChord x3_A) by reflexivity.
  replace (ck_egg (bp_ck x3_pcB)) with (MkChord x3_B) by reflexivity.
  cbn -[cook_t_chord admissible_hit_b least_ti].
  rewrite x3_cook_A_AB, x3_cook_B_AB, x3_hit_AB.
  cbn [least_ti]. reflexivity.
Qed.

Lemma x3_least_BC :
  least_ti (adm_list x3_pcs x3_pcB x3_pcC) =
  Some (mkHitCand x3_pBC (1 / 4) (1 / 4)).
Proof.
  unfold adm_list.
  replace (bp_support x3_pcB) with (SuppChord x3_B) by reflexivity.
  replace (bp_support x3_pcC) with (SuppChord x3_C) by reflexivity.
  rewrite x3_counted_BC. unfold cands_of, cook_t_egg.
  replace (ck_egg (bp_ck x3_pcB)) with (MkChord x3_B) by reflexivity.
  replace (ck_egg (bp_ck x3_pcC)) with (MkChord x3_C) by reflexivity.
  cbn -[cook_t_chord admissible_hit_b least_ti].
  rewrite x3_cook_B_BC, x3_cook_C_BC, x3_hit_BC.
  cbn [least_ti]. reflexivity.
Qed.

Lemma x3_sup_AB : support_eqb (SuppChord x3_A) (SuppChord x3_B) = false.
Proof.
  unfold support_eqb, chord_eqb, pt_eqb, x3_A, x3_B. cbn.
  assert (Ex : req_b 0 0 = true) by (apply req_b_true; ring).
  assert (Ey : req_b 0 2 = false) by (apply req_b_false; lra).
  rewrite Ex, Ey. cbn. reflexivity.
Qed.

Lemma x3_sup_BC : support_eqb (SuppChord x3_B) (SuppChord x3_C) = false.
Proof.
  unfold support_eqb, chord_eqb, pt_eqb, x3_B, x3_C. cbn.
  assert (Ex : req_b 0 1 = false) by (apply req_b_false; lra).
  rewrite Ex. cbn. reflexivity.
Qed.

Lemma x3_pok_AB : pair_ok x3_pcA x3_pcB = true.
Proof.
  unfold pair_ok, x3_pcA, x3_pcB. cbn [bp_support].
  rewrite x3_wfb, x3_wfb, x3_sup_AB. reflexivity.
Qed.

Lemma x3_pok_BC : pair_ok x3_pcB x3_pcC = true.
Proof.
  unfold pair_ok, x3_pcB, x3_pcC. cbn [bp_support].
  rewrite x3_wfb, x3_wfb, x3_sup_BC. reflexivity.
Qed.

Opaque pair_ok adm_list least_ti.

Lemma x3_pick_bag_first :
  pick_bag x3_bag = Some (mkHitPick 0%nat 1%nat x3_pAB (1 / 2) (1 / 2)).
Proof.
  unfold pick_bag, x3_bag, pick.
  cbn [scan_i scan_j length nth_error x3_pcs].
  rewrite x3_pok_AB, x3_least_AB. cbn [hc_p hc_ti hc_tj]. reflexivity.
Qed.

Lemma x3_rev_first :
  pick_rev x3_bag = Some (mkHitPick 1%nat 2%nat x3_pBC (1 / 4) (1 / 4)).
Proof.
  unfold pick_rev, x3_bag.
  cbn [scan_i_down scan_j_down length Nat.leb nth_error x3_pcs].
  rewrite x3_pok_BC, x3_least_BC. cbn [hc_p hc_ti hc_tj]. reflexivity.
Qed.

Transparent pair_ok adm_list least_ti.

Lemma x3_inv : bag_inv x3_bag.
Proof.
  intros pc Hin. unfold x3_bag, x3_pcs in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]].
  - apply x3_wf.
  - apply x3_wf.
  - apply x3_wf.
Qed.

Lemma x3_no_decline : no_decline_pair x3_pcs.
Proof.
  intros a c Ha Hc Hneq Hd.
  unfold x3_pcs in Ha, Hc.
  destruct Ha as [<-|[<-|[<-|[]]]];
    destruct Hc as [<-|[<-|[<-|[]]]];
    try (contradict Hneq; reflexivity);
    exact Hd.
Qed.

Theorem x3_selectors_agree :
  vset_eq (run_pcs pick_bag x3_bag) (run_pcs pick_rev x3_bag).
Proof.
  apply (run_vset_determined pick_bag pick_rev default_sheet x3_pcs
          pick_bag_lawful pick_rev_lawful x3_inv x3_no_decline).
Qed.

Print Assumptions x3_wf.
Print Assumptions x3_wfb.
Print Assumptions x3_cross_AB.
Print Assumptions x3_cross_BC.
Print Assumptions x3_not_same_AB.
Print Assumptions x3_not_same_BC.
Print Assumptions x3_canon_AB.
Print Assumptions x3_canon_BC.
Print Assumptions x3_ll_AB.
Print Assumptions x3_ll_BC.
Print Assumptions x3_img_A_AB.
Print Assumptions x3_img_B_AB.
Print Assumptions x3_img_B_BC.
Print Assumptions x3_img_C_BC.
Print Assumptions x3_not_vert_A_AB.
Print Assumptions x3_not_vert_B_BC.
Print Assumptions x3_ov_AB.
Print Assumptions x3_ov_BC.
Print Assumptions x3_keep_AB.
Print Assumptions x3_keep_BC.
Print Assumptions x3_counted_AB.
Print Assumptions x3_counted_BC.
Print Assumptions x3_dd_A.
Print Assumptions x3_dd_B.
Print Assumptions x3_dd_C.
Print Assumptions x3_cook_A_AB.
Print Assumptions x3_cook_B_AB.
Print Assumptions x3_cook_B_BC.
Print Assumptions x3_cook_C_BC.
Print Assumptions x3_hit_AB.
Print Assumptions x3_hit_BC.
Print Assumptions x3_least_AB.
Print Assumptions x3_least_BC.
Print Assumptions x3_sup_AB.
Print Assumptions x3_sup_BC.
Print Assumptions x3_pok_AB.
Print Assumptions x3_pok_BC.
Print Assumptions x3_pick_bag_first.
Print Assumptions x3_rev_first.
Print Assumptions x3_inv.
Print Assumptions x3_no_decline.
Print Assumptions x3_selectors_agree.
