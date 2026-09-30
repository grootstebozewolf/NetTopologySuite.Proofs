(* ============================================================================
   NetTopologySuite.Proofs.SheetHenNodedOvGap
   ----------------------------------------------------------------------------
   Letter 6a-i counterexample. claimId: none.
   Headline: rho_zero_not_ov. Consumer: SheetHenNodedOv.
   Two co-circular arcs. Canon frame S counts only a double vertex, so
   rho_pcs is 0. Piece order (L, S) has a progress hit at (5, 0) that is
   an overlap endpoint in that frame and not a vertex of L, so
   bag_noded_ov fails. Refutes rho = 0 -> bag_noded_ov.
   3-axiom host. No Admitted.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List PeanoNat Bool.
From NTS.Proofs Require Import Distance SheetHenCook SheetHenBag SheetHenRho
  SheetHenBagRun SheetHenLoop3 SheetHenBagRunFix HostCircChordOracle
  SheetHenNodedOv.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Converse fails. Two co-circular arcs. Canon frame S sees only a double    *)
(* vertex, so rho is 0. Piece order (L, S) has a progress hit at (5, 0),     *)
(* which is an overlap endpoint in that frame and not a vertex of L.         *)
(* -------------------------------------------------------------------------- *)

Definition gap_s : CircularEgg := mkCircularEgg (mkPoint 0 0) 5 0 PI.
Definition gap_l : CircularEgg := mkCircularEgg (mkPoint 0 0) 5 PI (3 * PI / 2).
Definition gap_p : Point := mkPoint 5 0.
Definition gap_pc (src dst : nat) (c : CircularEgg) : BagPiece :=
  mkBagPiece (mkChicken src dst (MkCirc (window_circ c (mkWindow 0 1))))
             (SuppCircle c) (mkWindow 0 1) nil.
Definition gap_pcs : list BagPiece :=
  [gap_pc 0%nat 1%nat gap_l; gap_pc 1%nat 0%nat gap_s].

Lemma gap_wf : forall n m c, piece_wf (gap_pc n m c).
Proof.
  intros n m c. unfold piece_wf, piece_realizes, gap_pc. cbn.
  split; [reflexivity| unfold window_ordered; cbn; lra].
Qed.

Lemma gap_distinct : gap_l <> gap_s.
Proof.
  intro H. inversion H. pose proof PI_RGT_0. lra.
Qed.

Lemma gap_circ_ls : circ_eqb gap_l gap_s = false.
Proof.
  unfold circ_eqb, gap_l, gap_s. cbn.
  assert (E : req_b PI 0 = false).
  { destruct (req_b PI 0) eqn:Eb; [| reflexivity].
    apply req_b_true in Eb. pose proof PI_RGT_0. lra. }
  rewrite E.
  destruct (pt_eqb (mkPoint 0 0) (mkPoint 0 0));
    destruct (req_b 5 5); destruct (req_b 0 PI);
    destruct (req_b (3 * PI / 2) PI); reflexivity.
Qed.

Lemma gap_circ_sl : circ_eqb gap_s gap_l = false.
Proof.
  unfold circ_eqb, gap_s, gap_l. cbn.
  assert (E : req_b 0 PI = false).
  { destruct (req_b 0 PI) eqn:Eb; [| reflexivity].
    apply req_b_true in Eb. pose proof PI_RGT_0. lra. }
  rewrite E.
  destruct (pt_eqb (mkPoint 0 0) (mkPoint 0 0));
    destruct (req_b 5 5); destruct (req_b PI 0);
    destruct (req_b PI (3 * PI / 2)); reflexivity.
Qed.

Lemma gap_same : same_circle_b gap_s gap_l = true.
Proof.
  unfold same_circle_b, gap_s, gap_l. cbn.
  apply andb_true_intro. split; [apply pt_eqb_true; reflexivity| apply req_b_true; ring].
Qed.

Lemma gap_same_swap : same_circle_b gap_l gap_s = true.
Proof.
  unfold same_circle_b, gap_l, gap_s. cbn.
  apply andb_true_intro. split; [apply pt_eqb_true; reflexivity| apply req_b_true; ring].
Qed.

Lemma gap_canon :
  canon2 (SuppCircle gap_l) (SuppCircle gap_s) =
  (SuppCircle gap_s, SuppCircle gap_l).
Proof.
  unfold canon2, support_reals, gap_l, gap_s.
  cbn [px py circ_o circ_r circ_theta0 circ_sweep].
  unfold rlex_le.
  destruct (Req_EM_T 1 1) as [_|N]; [| congruence].
  destruct (Req_EM_T 0 0) as [_|N0]; [| congruence].
  destruct (Req_EM_T 0 0) as [_|N0b]; [| congruence].
  destruct (Req_EM_T 5 5) as [_|N5]; [| congruence].
  destruct (Req_EM_T PI 0) as [Bad|Npi]; [pose proof PI_RGT_0; lra|].
  destruct (Rle_dec PI 0) as [Hle|Hle]; [pose proof PI_RGT_0; lra|].
  reflexivity.
Qed.

Lemma gap_key_ss : forall t,
  key_param (SuppCircle gap_s) (SuppCircle gap_s) t = t * PI.
Proof.
  intro t. unfold key_param, gap_s. cbn.
  assert (Eb : rle_b 0 (5 * 5) = true) by (apply rle_b_true; lra).
  rewrite Eb. cbv beta iota zeta. replace (0 + 0) with 0 by ring.
  rewrite align_k_same. replace (IZR 0) with 0 by reflexivity. ring.
Qed.

Lemma gap_key_sl : forall t,
  key_param (SuppCircle gap_s) (SuppCircle gap_l) t = PI + t * (3 * PI / 2).
Proof.
  intro t. unfold key_param, gap_s, gap_l. cbn.
  assert (Eb : rle_b 0 (5 * 5) = true) by (apply rle_b_true; lra).
  rewrite Eb. cbv beta iota zeta. replace (PI + 0) with PI by ring.
  rewrite align_k_zero_pi. replace (IZR 0) with 0 by reflexivity. ring.
Qed.

Lemma gap_key_ll : forall t,
  key_param (SuppCircle gap_l) (SuppCircle gap_l) t = PI + t * (3 * PI / 2).
Proof.
  intro t. unfold key_param, gap_l. cbn.
  assert (Eb : rle_b 0 (5 * 5) = true) by (apply rle_b_true; lra).
  rewrite Eb. cbv beta iota zeta. replace (PI + 0) with PI by ring.
  rewrite align_k_same. replace (IZR 0) with 0 by reflexivity. ring.
Qed.

Lemma gap_key_ls : forall t,
  key_param (SuppCircle gap_l) (SuppCircle gap_s) t = t * PI + 2 * PI.
Proof.
  intro t. unfold key_param, gap_l, gap_s. cbn.
  assert (Eb : rle_b 0 (5 * 5) = true) by (apply rle_b_true; lra).
  rewrite Eb. cbv beta iota zeta. replace (0 + 0) with 0 by ring.
  rewrite align_k_pi_zero. change (IZR 1) with 1. ring.
Qed.

Lemma gap_keys_ss :
  all_keys (SuppCircle gap_s) (SuppCircle gap_s) gap_pcs = [0; PI].
Proof.
  Opaque key_param.
  unfold all_keys, gap_pcs, piece_keys, gap_pc. cbn.
  rewrite gap_circ_ls. rewrite circ_eqb_refl. cbn.
  rewrite gap_key_ss, gap_key_ss.
  replace (0 * PI) with 0 by ring. replace (1 * PI) with PI by ring. reflexivity.
  Transparent key_param.
Qed.

Lemma gap_keys_sl :
  all_keys (SuppCircle gap_s) (SuppCircle gap_l) gap_pcs = [PI; 5 * PI / 2].
Proof.
  Opaque key_param.
  unfold all_keys, gap_pcs, piece_keys, gap_pc. cbn.
  rewrite circ_eqb_refl. rewrite gap_circ_sl. cbn.
  rewrite gap_key_sl, gap_key_sl.
  replace (PI + 0 * (3 * PI / 2)) with PI by ring.
  replace (PI + 1 * (3 * PI / 2)) with (5 * PI / 2) by field. reflexivity.
  Transparent key_param.
Qed.

Lemma gap_keys_ll :
  all_keys (SuppCircle gap_l) (SuppCircle gap_l) gap_pcs = [PI; 5 * PI / 2].
Proof.
  Opaque key_param.
  unfold all_keys, gap_pcs, piece_keys, gap_pc. cbn.
  rewrite circ_eqb_refl. rewrite gap_circ_sl. cbn.
  rewrite gap_key_ll, gap_key_ll.
  replace (PI + 0 * (3 * PI / 2)) with PI by ring.
  replace (PI + 1 * (3 * PI / 2)) with (5 * PI / 2) by field. reflexivity.
  Transparent key_param.
Qed.

Lemma gap_keys_ls :
  all_keys (SuppCircle gap_l) (SuppCircle gap_s) gap_pcs = [2 * PI; 3 * PI].
Proof.
  Opaque key_param.
  unfold all_keys, gap_pcs, piece_keys, gap_pc. cbn.
  rewrite gap_circ_ls. rewrite circ_eqb_refl. cbn.
  rewrite gap_key_ls, gap_key_ls.
  replace (0 * PI + 2 * PI) with (2 * PI) by ring.
  replace (1 * PI + 2 * PI) with (3 * PI) by ring. reflexivity.
  Transparent key_param.
Qed.

Lemma gap_west : point_of_key (SuppCircle gap_s) PI = mkPoint (-5) 0.
Proof.
  unfold point_of_key, gap_s. cbn [circ_sweep circ_theta0 circ_o circ_r].
  destruct (req_b PI 0) eqn:E.
  - apply req_b_true in E. pose proof PI_RGT_0. lra.
  - unfold circ_eval. cbn [circ_o circ_r circ_theta0 circ_sweep px py].
    assert (Hp : PI <> 0). { pose proof PI_RGT_0. lra. }
    replace (0 + ((PI - 0) / PI) * PI) with PI by (field; exact Hp).
    rewrite cos_PI, sin_PI. apply (f_equal2 mkPoint); ring.
Qed.

Lemma gap_overlap_sl :
  overlap_pts gap_pcs (SuppCircle gap_s) (SuppCircle gap_l) = [mkPoint (-5) 0].
Proof.
  unfold overlap_pts. rewrite gap_keys_ss, gap_keys_sl. cbn [rmin_list rmax_list].
  assert (A0 : Rmin 0 PI = 0). { apply Rmin_left. pose proof PI_RGT_0. lra. }
  assert (A1 : Rmax 0 PI = PI). { apply Rmax_right. pose proof PI_RGT_0. lra. }
  assert (B0 : Rmin PI (5 * PI / 2) = PI). { apply Rmin_left. pose proof PI_RGT_0. lra. }
  assert (B1 : Rmax PI (5 * PI / 2) = 5 * PI / 2). { apply Rmax_right. pose proof PI_RGT_0. lra. }
  rewrite A0, A1, B0, B1.
  assert (Lo : Rmax 0 PI = PI). { apply Rmax_right. pose proof PI_RGT_0. lra. }
  assert (Hi : Rmin PI (5 * PI / 2) = PI). { apply Rmin_left. pose proof PI_RGT_0. lra. }
  rewrite Lo, Hi.
  assert (Er : rle_b PI PI = true) by (apply rle_b_true; lra).
  rewrite Er. rewrite gap_west. apply dedup_dup.
Qed.

Lemma gap_east : point_of_key (SuppCircle gap_l) (2 * PI) = gap_p.
Proof.
  unfold point_of_key, gap_l, gap_p. cbn [circ_sweep circ_theta0 circ_o circ_r px py].
  destruct (req_b (3 * PI / 2) 0) eqn:E.
  - apply req_b_true in E. pose proof PI_RGT_0. lra.
  - unfold circ_eval. cbn [circ_o circ_r circ_theta0 circ_sweep px py].
    replace (PI + ((2 * PI - PI) / (3 * PI / 2)) * (3 * PI / 2)) with (2 * PI)
      by (field; pose proof PI_RGT_0; lra).
    rewrite cos_2PI, sin_2PI. apply (f_equal2 mkPoint); ring.
Qed.

Lemma gap_overlap_ls_in : In gap_p (overlap_pts gap_pcs (SuppCircle gap_l) (SuppCircle gap_s)).
Proof.
  unfold overlap_pts. rewrite gap_keys_ll, gap_keys_ls. cbn [rmin_list rmax_list].
  assert (A0 : Rmin PI (5 * PI / 2) = PI). { apply Rmin_left. pose proof PI_RGT_0. lra. }
  assert (A1 : Rmax PI (5 * PI / 2) = 5 * PI / 2). { apply Rmax_right. pose proof PI_RGT_0. lra. }
  assert (B0 : Rmin (2 * PI) (3 * PI) = 2 * PI). { apply Rmin_left. pose proof PI_RGT_0. lra. }
  assert (B1 : Rmax (2 * PI) (3 * PI) = 3 * PI). { apply Rmax_right. pose proof PI_RGT_0. lra. }
  rewrite A0, A1, B0, B1.
  assert (Lo : Rmax PI (2 * PI) = 2 * PI). { apply Rmax_right. pose proof PI_RGT_0. lra. }
  assert (Hi : Rmin (5 * PI / 2) (3 * PI) = 5 * PI / 2).
  { apply Rmin_left. pose proof PI_RGT_0. lra. }
  rewrite Lo, Hi.
  assert (Er : rle_b (2 * PI) (5 * PI / 2) = true).
  { apply rle_b_true. pose proof PI_RGT_0. lra. }
  rewrite Er. rewrite dedup_In. left. apply gap_east.
Qed.

Lemma gap_l_start : support_at (SuppCircle gap_l) 0 = mkPoint (-5) 0.
Proof.
  unfold support_at, circ_eval, gap_l. cbn.
  replace (PI + 0 * (3 * PI / 2)) with PI by ring.
  rewrite cos_PI, sin_PI. apply (f_equal2 mkPoint); ring.
Qed.

Lemma gap_l_end_px : px (support_at (SuppCircle gap_l) 1) = 0.
Proof.
  unfold support_at, circ_eval, gap_l. cbn.
  replace (PI + 1 * (3 * PI / 2)) with (PI / 2 + 2 * PI) by field.
  rewrite cos_plus, cos_PI2, sin_PI2, cos_2PI, sin_2PI. ring.
Qed.

Lemma gap_s_end : support_at (SuppCircle gap_s) 1 = mkPoint (-5) 0.
Proof.
  unfold support_at, circ_eval, gap_s. cbn.
  replace (0 + 1 * PI) with PI by ring.
  rewrite cos_PI, sin_PI. apply (f_equal2 mkPoint); ring.
Qed.

Lemma gap_s_start : support_at (SuppCircle gap_s) 0 = gap_p.
Proof.
  unfold support_at, circ_eval, gap_s, gap_p. cbn.
  replace (0 + 0 * PI) with 0 by ring.
  rewrite cos_0, sin_0. apply (f_equal2 mkPoint); ring.
Qed.

Lemma gap_west_vertices :
  family_vertex gap_pcs (SuppCircle gap_s) (mkPoint (-5) 0) /\
  family_vertex gap_pcs (SuppCircle gap_l) (mkPoint (-5) 0).
Proof.
  split.
  - exists (gap_pc 1%nat 0%nat gap_s). split; [simpl; auto|]. split; [reflexivity|].
    unfold piece_endpoint, gap_pc. cbn. right. symmetry. apply gap_s_end.
  - exists (gap_pc 0%nat 1%nat gap_l). split; [simpl; auto|]. split; [reflexivity|].
    unfold piece_endpoint, gap_pc. cbn. left. symmetry. apply gap_l_start.
Qed.

Lemma gap_not_vertex_l : ~ family_vertex gap_pcs (SuppCircle gap_l) gap_p.
Proof.
  intros [pc [Hin [Hs Hep]]].
  destruct Hin as [E|[E|[]]]; subst pc.
  - unfold piece_endpoint, gap_pc in Hep.
    cbn [bp_support bp_window win_lo win_hi] in Hep.
    destruct Hep as [Hep|Hep].
    + rewrite gap_l_start in Hep. unfold gap_p in Hep.
      apply (f_equal px) in Hep. cbn in Hep. lra.
    + apply (f_equal px) in Hep. rewrite gap_l_end_px in Hep.
      unfold gap_p in Hep. cbn in Hep. lra.
  - unfold gap_pc in Hs. cbn in Hs. inversion Hs. pose proof PI_RGT_0. lra.
Qed.

Lemma gap_overlap_b :
  overlap_b (SuppCircle gap_l) (SuppCircle gap_s) = true.
Proof.
  unfold overlap_b. rewrite gap_canon. apply gap_same.
Qed.

Lemma gap_hit :
  I_ok (ck_egg (bp_ck (gap_pc 0%nat 1%nat gap_l)))
       (ck_egg (bp_ck (gap_pc 1%nat 0%nat gap_s)))
       (IHit gap_p (2 / 3) 0).
Proof.
  simpl. split; unfold on_circ; split; try lra.
  - unfold gap_pc, window_circ, circ_eval, gap_l, gap_p. cbn.
    replace (PI + 0 * (3 * PI / 2)) with PI by ring.
    replace ((1 - 0) * (3 * PI / 2)) with (3 * PI / 2) by ring.
    replace (PI + (2 / 3) * (3 * PI / 2)) with (2 * PI) by field.
    rewrite cos_2PI, sin_2PI. apply (f_equal2 mkPoint); ring.
  - unfold gap_pc, window_circ, circ_eval, gap_s, gap_p. cbn.
    replace (0 + 0 * PI) with 0 by ring.
    replace ((1 - 0) * PI) with PI by ring.
    replace (0 + 0 * PI) with 0 by ring.
    rewrite cos_0, sin_0. apply (f_equal2 mkPoint); ring.
Qed.

Lemma gap_supports :
  supports_of gap_pcs = [SuppCircle gap_l; SuppCircle gap_s].
Proof.
  unfold gap_pcs, supports_of, gap_pc. cbn. rewrite gap_circ_ls. reflexivity.
Qed.

Lemma gap_keep_west :
  keep_b gap_pcs (SuppCircle gap_s) (SuppCircle gap_l) (mkPoint (-5) 0) = false.
Proof.
  unfold keep_b.
  destruct gap_west_vertices as [Vs Vl].
  assert (V : vertex_b gap_pcs (SuppCircle gap_s) (mkPoint (-5) 0) &&
              vertex_b gap_pcs (SuppCircle gap_l) (mkPoint (-5) 0) = true).
  { apply andb_true_intro. split; apply vertex_spec; assumption. }
  rewrite V.
  destruct (in_image_b gap_pcs (SuppCircle gap_s) (mkPoint (-5) 0) &&
            in_image_b gap_pcs (SuppCircle gap_l) (mkPoint (-5) 0)); reflexivity.
Qed.

Lemma gap_counted_nil :
  counted gap_pcs (SuppCircle gap_l) (SuppCircle gap_s) = [].
Proof.
  unfold counted. rewrite gap_canon. cbn [fst snd].
  unfold raw_pts. rewrite gap_same. rewrite gap_overlap_sl. cbn.
  rewrite gap_keep_west. reflexivity.
Qed.

Lemma gap_rho : rho_pcs gap_pcs = 0%nat.
Proof.
  unfold rho_pcs. rewrite gap_supports. cbn. rewrite gap_counted_nil. reflexivity.
Qed.

Lemma gap_not_ov : ~ bag_noded_ov (BagLive default_sheet gap_pcs).
Proof.
  simpl. intro Hov.
  pose (a := gap_pc 0%nat 1%nat gap_l).
  pose (c := gap_pc 1%nat 0%nat gap_s).
  assert (Ha : nth_error gap_pcs 0%nat = Some a) by reflexivity.
  assert (Hc : nth_error gap_pcs 1%nat = Some c) by reflexivity.
  assert (Hprog : progress_hit gap_pcs a c (IHit gap_p (2 / 3) 0)).
  { unfold progress_hit. cbn [bp_support gap_pc]. intro Hv.
    destruct Hv as [Hl _]. exact (gap_not_vertex_l Hl). }
  assert (Hnp : ~ progress_hit gap_pcs a c (IHit gap_p (2 / 3) 0)).
  { apply (Hov 0%nat 1%nat a c gap_p (2 / 3) 0 Ha Hc).
    - discriminate.
    - apply gap_hit.
    - intro Hoverlap. exact gap_overlap_ls_in. }
  exact (Hnp Hprog).
Qed.

Theorem rho_zero_not_ov :
  exists pcs,
    bag_inv (BagLive default_sheet pcs) /\
    rho_pcs pcs = 0%nat /\
    ~ bag_noded_ov (BagLive default_sheet pcs).
Proof.
  exists gap_pcs. split; [| split].
  - unfold bag_inv. intros pc Hin. destruct Hin as [<-|[<-|[]]]; apply gap_wf.
  - exact gap_rho.
  - exact gap_not_ov.
Qed.

Print Assumptions gap_wf.
Print Assumptions gap_distinct.
Print Assumptions gap_circ_ls.
Print Assumptions gap_circ_sl.
Print Assumptions gap_same.
Print Assumptions gap_same_swap.
Print Assumptions gap_canon.
Print Assumptions gap_key_ss.
Print Assumptions gap_key_sl.
Print Assumptions gap_key_ll.
Print Assumptions gap_key_ls.
Print Assumptions gap_keys_ss.
Print Assumptions gap_keys_sl.
Print Assumptions gap_keys_ll.
Print Assumptions gap_keys_ls.
Print Assumptions gap_west.
Print Assumptions gap_overlap_sl.
Print Assumptions gap_east.
Print Assumptions gap_overlap_ls_in.
Print Assumptions gap_l_start.
Print Assumptions gap_l_end_px.
Print Assumptions gap_s_end.
Print Assumptions gap_s_start.
Print Assumptions gap_west_vertices.
Print Assumptions gap_not_vertex_l.
Print Assumptions gap_overlap_b.
Print Assumptions gap_hit.
Print Assumptions gap_supports.
Print Assumptions gap_keep_west.
Print Assumptions gap_counted_nil.
Print Assumptions gap_rho.
Print Assumptions gap_not_ov.
Print Assumptions rho_zero_not_ov.
