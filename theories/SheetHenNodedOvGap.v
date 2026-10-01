(* ============================================================================
   NetTopologySuite.Proofs.SheetHenNodedOvGap
   ----------------------------------------------------------------------------
   Letter 6a-i gap bag. claimId: none.
   Headline: gap_not_ov. Consumer: SheetHenNodedOv.
   Regression: gap_counted, gap_rho_pos. Same consumer. No claimId.
   (5, 0) is a symmetric overlap endpoint, so the gap bag is counted
   and rho_pcs > 0. bag_noded_ov fails. Does not claim the iff.
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
(* Gap bag. (5, 0) is a symmetric overlap endpoint and a progress hit, so     *)
(* bag_noded_ov fails. The parameter hull of frame S still misses it.        *)
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

Lemma gap_p_on_l : support_at (SuppCircle gap_l) (2 / 3) = gap_p.
Proof.
  unfold support_at, circ_eval, gap_l, gap_p. cbn.
  replace (PI + (2 / 3) * (3 * PI / 2)) with (2 * PI) by field.
  rewrite cos_2PI, sin_2PI. apply (f_equal2 mkPoint); ring.
Qed.

Lemma gap_p_count_s : count_ends gap_pcs (SuppCircle gap_s) gap_p = 1%nat.
Proof.
  unfold gap_pcs.
  rewrite (count_ends_cons_bit (gap_pc 0%nat 1%nat gap_l)). unfold endbit.
  replace (support_eqb (bp_support (gap_pc 0%nat 1%nat gap_l)) (SuppCircle gap_s))
    with false by (unfold gap_pc; simpl; symmetry; exact gap_circ_ls).
  rewrite andb_false_l. change (if false then 1%nat else 0%nat) with 0%nat.
  rewrite Nat.add_0_l.
  rewrite (count_ends_cons_bit (gap_pc 1%nat 0%nat gap_s)). unfold endbit.
  replace (support_eqb (bp_support (gap_pc 1%nat 0%nat gap_s)) (SuppCircle gap_s))
    with true by (unfold gap_pc; simpl; symmetry; apply circ_eqb_refl).
  rewrite andb_true_l.
  replace (endpoint_b (gap_pc 1%nat 0%nat gap_s) gap_p) with true.
  - change (if true then 1%nat else 0%nat) with 1%nat. simpl. reflexivity.
  - symmetry. apply endpoint_spec. left.
    unfold gap_pc. simpl. symmetry. exact gap_s_start.
Qed.

Lemma gap_p_in_l : in_image_b gap_pcs (SuppCircle gap_l) gap_p = true.
Proof.
  apply in_image_spec. exists (gap_pc 0%nat 1%nat gap_l).
  split; [apply in_eq|]. split; [reflexivity|].
  exists (2 / 3). split.
  - unfold gap_pc. simpl. split; lra.
  - unfold gap_pc. simpl. symmetry. exact gap_p_on_l.
Qed.

Lemma gap_p_in_ends :
  In gap_p (circ_overlap_pts gap_pcs gap_s gap_l).
Proof.
  unfold circ_overlap_pts. rewrite dedup_In. apply filter_In. split.
  - apply in_or_app. left. unfold ends_of, gap_pcs. simpl.
    unfold gap_pc. simpl. rewrite gap_circ_ls. simpl.
    rewrite circ_eqb_refl. simpl. refine (or_introl gap_s_start).
  - unfold circ_end_in_other_b. apply orb_true_intro. left.
    apply andb_true_intro. split.
    + unfold boundary_end_b. apply andb_true_intro. split.
      * apply vertex_spec. exists (gap_pc 1%nat 0%nat gap_s).
        split; [unfold gap_pcs; right; left; reflexivity|].
        split; [reflexivity|]. left. unfold gap_pc. simpl. symmetry. exact gap_s_start.
      * apply negb_true_iff. unfold joint_b. rewrite gap_p_count_s. reflexivity.
    + exact gap_p_in_l.
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
    - intros _. unfold a, c, overlap_endpoints.
      cbn [bp_support gap_pc]. rewrite gap_canon. simpl.
      exact gap_p_in_ends. }
  exact (Hnp Hprog).
Qed.

(* Regression. Consumer: SheetHenNodedOv. claimId: none. *)
Lemma gap_admissible :
  admissible_hit gap_pcs (gap_pc 0%nat 1%nat gap_l) (gap_pc 1%nat 0%nat gap_s)
    gap_p (2 / 3) 0.
Proof.
  split; [| split].
  - exact gap_hit.
  - intro Hv. apply gap_not_vertex_l. exact (proj1 Hv).
  - intros _. unfold overlap_endpoints, gap_pc.
    cbn [bp_support]. rewrite gap_canon. simpl. exact gap_p_in_ends.
Qed.

Lemma gap_counted :
  In gap_p (counted gap_pcs (SuppCircle gap_s) (SuppCircle gap_l)).
Proof.
  rewrite counted_sym.
  apply (admissible_in_counted gap_pcs
      (gap_pc 0%nat 1%nat gap_l) (gap_pc 1%nat 0%nat gap_s)
      gap_p (2 / 3) 0).
  - apply in_eq.
  - right. apply in_eq.
  - apply gap_wf.
  - apply gap_wf.
  - intro H. inversion H. pose proof PI_RGT_0. lra.
  - exact gap_admissible.
Qed.

Lemma gap_rho_pos : (rho_pcs gap_pcs > 0)%nat.
Proof.
  unfold rho_pcs. rewrite gap_supports. simpl pair_sum. simpl map. simpl fold_right.
  assert (Hin : In gap_p (counted gap_pcs (SuppCircle gap_l) (SuppCircle gap_s))).
  { rewrite counted_sym. exact gap_counted. }
  destruct (counted gap_pcs (SuppCircle gap_l) (SuppCircle gap_s)) as [|q tl].
  - contradiction.
  - simpl. lia.
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
Print Assumptions gap_p_on_l.
Print Assumptions gap_p_count_s.
Print Assumptions gap_p_in_l.
Print Assumptions gap_p_in_ends.
Print Assumptions gap_not_ov.
Print Assumptions gap_admissible.
Print Assumptions gap_counted.
Print Assumptions gap_rho_pos.
