(* ============================================================================
   NetTopologySuite.Proofs.SheetHenNodedOv
   ----------------------------------------------------------------------------
   Letter 6a-i. claimId: 0007-loop-letter6.
   Headline: noded_ov_rho_zero.
   Consumer: col_fixture_ov_not_noded.
   bag_noded_ov is bag_noded weakened by the piece-order overlap antecedent.
   That direction (ov + no declining pair -> rho = 0) is proved.
   The converse is false: rho_zero_not_ov. Circle overlap_pts is not
   symmetric, so a progress hit can sit in the piece-order endpoint list
   while the canon frame that rho counts is empty.
   Does not remint 0007-loop-letter3-strict. Does not redefine bag_noded.
   Does not define CookLoopRho. cook_loop_status unchanged.
   LeftoverBagTermArm stays refuted. 3-axiom host. No Admitted.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List PeanoNat Bool.
From NTS.Proofs Require Import Distance SheetHenCook SheetHenBag SheetHenRho
  SheetHenBagRun SheetHenLoop3 SheetHenBagRunFix HostCircChordOracle.
Import ListNotations.
Local Open Scope R_scope.

Lemma nth_length : forall (A : Type) (l : list A) n (x : A),
  nth_error l n = Some x -> (n < length l)%nat.
Proof.
  intros A l n x. revert l.
  induction n as [|n IH]; intros [|h t] H; simpl in *; try discriminate.
  - lia.
  - apply IH in H. lia.
Qed.

Lemma ov_fold_zero : forall (A : Type) (g : A -> nat) xs,
  (forall y, In y xs -> g y = 0%nat) ->
  fold_right Nat.add 0%nat (map g xs) = 0%nat.
Proof.
  intros A g xs Hg. induction xs as [|y tl IH]; simpl; [reflexivity|].
  rewrite (Hg y (or_introl eq_refl)).
  rewrite IH; [reflexivity|].
  intros z Hz. apply Hg. right. exact Hz.
Qed.

Lemma ov_pair_sum_zero : forall ss f,
  NoDup ss ->
  (forall a b, In a ss -> In b ss -> a <> b -> f a b = 0%nat) ->
  pair_sum ss f = 0%nat.
Proof.
  induction ss as [|s tl IH]; intros f Hnd Hz; simpl; [reflexivity|].
  inversion Hnd as [|s0 tl0 Hnin Hnd']; subst.
  rewrite ov_fold_zero.
  - rewrite IH; [reflexivity| exact Hnd'|].
    intros a b Ha Hb Hneq. apply Hz; [right| right|]; assumption.
  - intros y Hy. apply Hz; [left; reflexivity| right; exact Hy|].
    intro E. subst y. exact (Hnin Hy).
Qed.

Lemma ov_counted_images : forall pcs s1 s2 p,
  In p (counted pcs s1 s2) ->
  support_image pcs s1 p /\ support_image pcs s2 p.
Proof.
  intros pcs s1 s2 p Hin.
  unfold counted in Hin.
  destruct (canon2 s1 s2) as [u v] eqn:Ec.
  rewrite dedup_In in Hin. apply filter_In in Hin. destruct Hin as [_ Hk].
  unfold keep_b in Hk. apply andb_prop in Hk. destruct Hk as [Hi _].
  apply andb_prop in Hi. destruct Hi as [Hu Hv].
  apply in_image_spec in Hu. apply in_image_spec in Hv.
  destruct (canon_orient s1 s2 u v Ec) as [[-> ->]|[-> ->]]; split; assumption.
Qed.

Lemma ov_counted_end : forall pcs s1 s2 p,
  In p (counted pcs s1 s2) ->
  overlap_b s1 s2 = true ->
  In p (overlap_endpoints pcs s1 s2).
Proof.
  intros pcs s1 s2 p Hin Ho.
  unfold counted in Hin. unfold overlap_endpoints.
  destruct (canon2 s1 s2) as [u v] eqn:Ec.
  rewrite dedup_In in Hin. apply filter_In in Hin. destruct Hin as [Hraw _].
  unfold overlap_b in Ho. rewrite Ec in Ho.
  destruct u as [cu|cu]; destruct v as [cv|cv]; simpl in Ho; try discriminate.
  - unfold raw_pts in Hraw. rewrite Ho in Hraw. exact Hraw.
  - unfold raw_pts in Hraw. rewrite Ho in Hraw. exact Hraw.
Qed.

Lemma overlap_b_sym : forall s1 s2, overlap_b s1 s2 = overlap_b s2 s1.
Proof.
  intros s1 s2. unfold overlap_b. rewrite (canon_swap s1 s2). reflexivity.
Qed.

Lemma canon_fixed : forall s1 s2 u v,
  canon2 s1 s2 = (u, v) -> canon2 u v = (u, v).
Proof.
  intros s1 s2 u v H.
  destruct (canon_orient s1 s2 u v H) as [[-> ->]|[-> ->]].
  - exact H.
  - rewrite canon_swap. exact H.
Qed.

Lemma canon_overlap_eq : forall s1 s2 u v,
  canon2 s1 s2 = (u, v) -> overlap_b s1 s2 = overlap_b u v.
Proof.
  intros s1 s2 u v H. unfold overlap_b. rewrite H. rewrite (canon_fixed s1 s2 u v H).
  reflexivity.
Qed.

Lemma same_line_refl : forall c, same_line_b c c = true.
Proof.
  intro c. unfold same_line_b, cross2.
  destruct (req_b (chord_dx c) 0) eqn:Ex;
  destruct (req_b (chord_dy c) 0) eqn:Ey; simpl.
  - apply pt_eqb_true. reflexivity.
  - apply andb_true_intro. split; apply req_b_true; ring.
  - apply andb_true_intro. split; apply req_b_true; ring.
  - apply andb_true_intro. split; apply req_b_true; ring.
Qed.

Lemma overlap_b_same_chord : forall c,
  overlap_b (SuppChord c) (SuppChord c) = true.
Proof.
  intro c. unfold overlap_b, canon2. rewrite rlex_refl. apply same_line_refl.
Qed.

Lemma chord_self_key : forall c t,
  chord_dd c <> 0 -> key_param (SuppChord c) (SuppChord c) t = t.
Proof.
  intros c t Hd. unfold key_param.
  destruct (req_b (chord_dd c) 0) eqn:Eb.
  - apply req_b_true in Eb. contradiction.
  - apply chord_param_eval. exact Hd.
Qed.

Lemma chord_self_point : forall c k,
  chord_dd c <> 0 -> point_of_key (SuppChord c) k = chord_eval c k.
Proof.
  intros c k Hd. unfold point_of_key.
  destruct (req_b (chord_dd c) 0) eqn:Eb.
  - apply req_b_true in Eb. contradiction.
  - reflexivity.
Qed.

Lemma key_in_vertex : forall pcs c k,
  chord_dd c <> 0 ->
  In k (all_keys (SuppChord c) (SuppChord c) pcs) ->
  family_vertex pcs (SuppChord c) (point_of_key (SuppChord c) k).
Proof.
  intros pcs c k Hd Hin.
  apply in_flat_map in Hin. destruct Hin as [pc [Hpc Hk]].
  unfold piece_keys in Hk.
  destruct (support_eqb (bp_support pc) (SuppChord c)) eqn:Heq.
  - apply support_eqb_true in Heq.
    Opaque key_param. simpl in Hk. Transparent key_param.
    destruct Hk as [Hk|[Hk|[]]].
    + rewrite (chord_self_key c (win_lo (bp_window pc)) Hd) in Hk.
      rewrite (chord_self_point c k Hd). rewrite <- Hk.
      exists pc. split; [exact Hpc|]. split; [exact Heq|].
      left. unfold support_at. rewrite Heq. reflexivity.
    + rewrite (chord_self_key c (win_hi (bp_window pc)) Hd) in Hk.
      rewrite (chord_self_point c k Hd). rewrite <- Hk.
      exists pc. split; [exact Hpc|]. split; [exact Heq|].
      right. unfold support_at. rewrite Heq. reflexivity.
  - simpl in Hk. contradiction.
Qed.

Lemma chord_self_overlap_vertex : forall pcs c p,
  chord_dd c <> 0 ->
  In p (overlap_pts pcs (SuppChord c) (SuppChord c)) ->
  family_vertex pcs (SuppChord c) p.
Proof.
  intros pcs c p Hd Hin.
  unfold overlap_pts in Hin.
  remember (all_keys (SuppChord c) (SuppChord c) pcs) as ks eqn:Eks.
  destruct ks as [|x xs].
  - contradiction.
  -     replace (Rmax (rmin_list (x :: xs)) (rmin_list (x :: xs)))
      with (rmin_list (x :: xs)) in Hin by (symmetry; apply Rmax_left; lra).
    replace (Rmin (rmax_list (x :: xs)) (rmax_list (x :: xs)))
      with (rmax_list (x :: xs)) in Hin by (symmetry; apply Rmin_left; lra).
    cbn zeta in Hin.
    destruct (rle_b (rmin_list (x :: xs)) (rmax_list (x :: xs))).
    + rewrite dedup_In in Hin. destruct Hin as [<-|[<-|[]]].
      * apply key_in_vertex; [exact Hd|]. rewrite <- Eks.
        apply rmin_in. discriminate.
      * apply key_in_vertex; [exact Hd|]. rewrite <- Eks.
        apply rmax_in. discriminate.
    + contradiction.
Qed.

(* -------------------------------------------------------------------------- *)
(* The weakened node predicate. overlap_pair is letter 5's overlap_b.        *)
(* -------------------------------------------------------------------------- *)

Definition bag_noded_ov (b : SheetBag) : Prop :=
  match b with
  | BagDeclined _ => True
  | BagLive _ pcs =>
      forall i j a c p ti tj,
        nth_error pcs i = Some a ->
        nth_error pcs j = Some c ->
        i <> j ->
        I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck c)) (IHit p ti tj) ->
        (overlap_pair (bp_support a) (bp_support c) = true ->
           In p (overlap_pts pcs (bp_support a) (bp_support c))) ->
        ~ progress_hit pcs a c (IHit p ti tj)
  end.

Definition no_decline_pair (pcs : list BagPiece) : Prop :=
  forall a c, In a pcs -> In c pcs -> a <> c ->
    ~ I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck c)) IDecline.

Lemma bag_noded_implies_ov : forall b, bag_noded b -> bag_noded_ov b.
Proof.
  intros b Hb. destruct b as [sh pcs|sh].
  - intros i j a c p ti tj Hi Hj Hij Hok _.
    exact (Hb i j a c (IHit p ti tj) Hi Hj Hij Hok).
  - exact Hb.
Qed.

Lemma pieces_hit : forall a c p,
  piece_wf a -> piece_wf c ->
  window_pts (bp_support a) (bp_window a) p ->
  window_pts (bp_support c) (bp_window c) p ->
  ~ I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck c)) IDecline ->
  exists ti tj, I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck c)) (IHit p ti tj).
Proof.
  intros a c p Ha Hc Wa Wc Hnd.
  assert (Ha0 := Ha). assert (Hc0 := Hc).
  destruct Ha as [Hra Hoa]. destruct Hc as [Hrc Hoc].
  destruct (bp_support a) as [sa|sa] eqn:Ea;
  destruct (bp_support c) as [sc|sc] eqn:Ec.
  - rewrite <- Ea in Wa. rewrite <- Ec in Wc.
    apply hit_param_line_line.
    + exact Ha0.
    + exact Hc0.
    + exact Wa.
    + exact Wc.
    + exists sa. exact Ea.
    + exists sc. exact Ec.
  - unfold piece_realizes in Hra, Hrc. rewrite Ea in Hra. rewrite Ec in Hrc.
    destruct (ck_egg (bp_ck a)) as [ea|ea|ea|ea|ea] eqn:Ega; try contradiction.
    destruct (ck_egg (bp_ck c)) as [ec|ec|ec|ec|ec] eqn:Egc; try contradiction.
    destruct (circ_open_span_b ec && chord_nondeg_b ea) eqn:Es.
    + pose proof hit_param_line_circle as Htmp.
      rewrite <- Ega. rewrite <- Egc. rewrite <- Ea in Wa. rewrite <- Ec in Wc.
      apply Htmp.
      * exact Ha0.
      * exact Hc0.
      * exact Wa.
      * exact Wc.
      * rewrite Ega. rewrite Egc. apply scope_spec. exact Es.
    + exfalso. apply Hnd. simpl. intro Hs.
      apply scope_spec in Hs. congruence.
  - unfold piece_realizes in Hra, Hrc. rewrite Ea in Hra. rewrite Ec in Hrc.
    destruct (ck_egg (bp_ck a)) as [ea|ea|ea|ea|ea] eqn:Ega; try contradiction.
    destruct (ck_egg (bp_ck c)) as [ec|ec|ec|ec|ec] eqn:Egc; try contradiction.
    destruct (circ_open_span_b ea && chord_nondeg_b ec) eqn:Es.
    + rewrite <- Ega. rewrite <- Egc. rewrite <- Ea in Wa. rewrite <- Ec in Wc.
      apply hit_param_line_circle.
      * exact Ha0.
      * exact Hc0.
      * exact Wa.
      * exact Wc.
      * rewrite Ega. rewrite Egc. apply scope_spec. exact Es.
    + exfalso. apply Hnd. simpl. intro Hs.
      apply scope_spec in Hs. congruence.
  - destruct (hit_param_circle_circle a c p sa sc
               Ha0 Hc0 Ea Ec Wa Wc)
      as [ti [tj [Hok _]]].
    exists ti, tj. exact Hok.
Qed.

Theorem noded_ov_rho_zero : forall sh pcs,
  bag_inv (BagLive sh pcs) ->
  no_decline_pair pcs ->
  bag_noded_ov (BagLive sh pcs) ->
  rho_pcs pcs = 0%nat.
Proof.
  intros sh pcs Hinv Hnd Hov.
  unfold rho_pcs. apply ov_pair_sum_zero; [apply supports_NoDup|].
  intros s1 s2 Hs1 Hs2 Hneq.
  destruct (counted pcs s1 s2) as [|p tl] eqn:Ecnt.
  - reflexivity.
  - exfalso.
    assert (Hin : In p (counted pcs s1 s2)).
    { rewrite Ecnt. left. reflexivity. }
    destruct (ov_counted_images pcs s1 s2 p Hin) as [I1 I2].
    destruct (canon2 s1 s2) as [u v] eqn:Ecan.
    assert (Huv : (u = s1 /\ v = s2) \/ (u = s2 /\ v = s1)).
    { apply canon_orient. exact Ecan. }
    assert (Iu : support_image pcs u p).
    { destruct Huv as [[-> ->]|[-> ->]]; assumption. }
    assert (Iv : support_image pcs v p).
    { destruct Huv as [[-> ->]|[-> ->]]; assumption. }
    destruct Iu as [a [HaIn [HaS HaW]]].
    destruct Iv as [c [HcIn [HcS HcW]]].
    assert (Hac : a <> c).
    { intro Eac. subst c. rewrite HaS in HcS.
      destruct Huv as [[Eu Ev]|[Eu Ev]].
      - rewrite Eu, Ev in HcS. exact (Hneq HcS).
      - rewrite Eu, Ev in HcS. exact (Hneq (eq_sym HcS)). }
    destruct (In_nth_error _ _ HaIn) as [i Hi].
    destruct (In_nth_error _ _ HcIn) as [j Hj].
    assert (Hij : i <> j).
    { intro E. subst j. rewrite Hi in Hj. inversion Hj. subst c. contradiction. }
    assert (Hwa : piece_wf a) by (apply Hinv, HaIn).
    assert (Hwc : piece_wf c) by (apply Hinv, HcIn).
    assert (Hdec : ~ I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck c)) IDecline).
    { apply Hnd; assumption. }
    rewrite <- HaS in HaW. rewrite <- HcS in HcW.
    destruct (pieces_hit a c p Hwa Hwc HaW HcW Hdec) as [ti [tj Hok]].
    assert (Hcnt2 : In p (counted pcs (bp_support a) (bp_support c))).
    { rewrite HaS, HcS. destruct Huv as [[-> ->]|[-> ->]].
      - exact Hin.
      - rewrite counted_sym. exact Hin. }
    assert (Hprog : progress_hit pcs a c (IHit p ti tj)).
    { unfold progress_hit, vertex_of_both.
      exact (counted_not_vertex pcs (bp_support a) (bp_support c) p Hcnt2). }
    apply (Hov i j a c p ti tj Hi Hj Hij Hok).
    + intro Ho.
      assert (Ho2 : overlap_b s1 s2 = true).
      { rewrite (canon_overlap_eq s1 s2 u v Ecan). rewrite <- HaS, <- HcS. exact Ho. }
      assert (He : In p (overlap_endpoints pcs s1 s2)).
      { apply ov_counted_end; assumption. }
      unfold overlap_endpoints in He. rewrite Ecan in He.
      rewrite HaS, HcS. exact He.
    + exact Hprog.
Qed.

(* -------------------------------------------------------------------------- *)
(* #903 collinear bag: ov holds, bag_noded fails at the interior point 3/2.  *)
(* -------------------------------------------------------------------------- *)

Definition col_final : SheetBag := col_bag2.
Definition col_mid : Point := mkPoint (3 / 2) 0.

Lemma col_dd_A : chord_dd col_A <> 0.
Proof. unfold chord_dd, chord_dx, chord_dy, col_A. cbn. lra. Qed.

Lemma col_dd_B : chord_dd col_B <> 0.
Proof. unfold chord_dd, chord_dx, chord_dy, col_B. cbn. lra. Qed.

Lemma col_A_px : forall t, px (support_at (SuppChord col_A) t) = 2 * t.
Proof. intro t. unfold support_at, chord_eval, col_A. cbn. ring. Qed.

Lemma col_B_pt : forall t,
  support_at (SuppChord col_B) t = mkPoint (1 + 2 * t) 0.
Proof.
  intro t. unfold support_at, chord_eval, col_B. cbn.
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma split_parent_support : forall pc u h,
  piece_realizes pc ->
  bp_support (fst (split_piece pc u h)) = bp_support pc /\
  bp_support (snd (split_piece pc u h)) = bp_support pc.
Proof.
  intros pc u h Hr.
  destruct (split_windows_sub pc u h Hr) as [H1 [H2 _]]. split; assumption.
Qed.

Lemma col_e1_support : bp_support col_e1 = SuppChord col_A.
Proof.
  destruct (split_parent_support col_pcA (1 / 2) col_h1 (proj1 col_wf_A)) as [_ H].
  unfold col_e1. rewrite H. reflexivity.
Qed.

Lemma col_e2_support : bp_support col_e2 = SuppChord col_B.
Proof.
  destruct (split_parent_support col_pcB 0 col_h1 (proj1 col_wf_B)) as [_ H].
  unfold col_e2. rewrite H. reflexivity.
Qed.

Lemma col_e1_win : bp_window col_e1 = mkWindow (1 / 2) 1.
Proof.
  destruct (split_windows_sub col_pcA (1 / 2) col_h1 (proj1 col_wf_A))
    as [_ [_ [_ Hw]]].
  unfold col_e1. rewrite Hw. unfold sub_hi, win_abs, col_pcA, unit_win. cbn.
  replace (0 + (1 / 2) * (1 - 0)) with (1 / 2) by field. reflexivity.
Qed.

Lemma col_e2_win : bp_window col_e2 = mkWindow 0 1.
Proof.
  destruct (split_windows_sub col_pcB 0 col_h1 (proj1 col_wf_B))
    as [_ [_ [_ Hw]]].
  unfold col_e2. rewrite Hw. unfold sub_hi, win_abs, col_pcB, unit_win. cbn.
  replace (0 + 0 * (1 - 0)) with 0 by ring. reflexivity.
Qed.

Lemma col_a_lo_win :
  bp_window (fst (split_piece col_e1 1 col_h2)) = mkWindow (1 / 2) 1.
Proof.
  destruct (split_windows_sub col_e1 1 col_h2 (proj1 (col_child_wf_hiA col_h1)))
    as [_ [_ [Hw _]]].
  rewrite Hw, col_e1_win. unfold sub_lo, win_abs. cbn.
  replace ((1 / 2) + 1 * (1 - (1 / 2))) with 1 by field. reflexivity.
Qed.

Lemma col_a_hi_win :
  bp_window (snd (split_piece col_e1 1 col_h2)) = mkWindow 1 1.
Proof.
  destruct (split_windows_sub col_e1 1 col_h2 (proj1 (col_child_wf_hiA col_h1)))
    as [_ [_ [_ Hw]]].
  rewrite Hw, col_e1_win. unfold sub_hi, win_abs. cbn.
  replace ((1 / 2) + 1 * (1 - (1 / 2))) with 1 by field. reflexivity.
Qed.

Lemma col_b_lo_win :
  bp_window (fst (split_piece col_e2 (1 / 2) col_h2)) = mkWindow 0 (1 / 2).
Proof.
  destruct (split_windows_sub col_e2 (1 / 2) col_h2 (proj1 (col_child_wf_hiB col_h1)))
    as [_ [_ [Hw _]]].
  rewrite Hw, col_e2_win. unfold sub_lo, win_abs. cbn.
  replace (0 + (1 / 2) * (1 - 0)) with (1 / 2) by field. reflexivity.
Qed.

Lemma col_a0_win :
  bp_window (fst (split_piece col_pcA (1 / 2) col_h1)) = mkWindow 0 (1 / 2).
Proof.
  destruct (split_windows_sub col_pcA (1 / 2) col_h1 (proj1 col_wf_A))
    as [_ [_ [Hw _]]].
  rewrite Hw. unfold sub_lo, win_abs, col_pcA, unit_win. cbn.
  replace (0 + (1 / 2) * (1 - 0)) with (1 / 2) by field. reflexivity.
Qed.

Lemma col_pcs2_form :
  col_pcs2 =
  [fst (split_piece col_e1 1 col_h2);
   snd (split_piece col_e1 1 col_h2);
   fst (split_piece col_e2 (1 / 2) col_h2);
   snd (split_piece col_e2 (1 / 2) col_h2);
   fst (split_piece col_pcA (1 / 2) col_h1);
   fst (split_piece col_pcB 0 col_h1)].
Proof.
  unfold col_pcs2, progress_pieces, col_pcs1, cooked_four, drop_pair,
    keep_other_idx, filter_idx.
  simpl. reflexivity.
Qed.

Lemma col_support_kind : forall pc,
  In pc col_pcs2 ->
  bp_support pc = SuppChord col_A \/ bp_support pc = SuppChord col_B.
Proof.
  intros pc Hin. rewrite col_pcs2_form in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
  - left. destruct (split_parent_support col_e1 1 col_h2
                    (proj1 (col_child_wf_hiA col_h1))) as [H _].
    rewrite H. apply col_e1_support.
  - left. destruct (split_parent_support col_e1 1 col_h2
                    (proj1 (col_child_wf_hiA col_h1))) as [_ H].
    rewrite H. apply col_e1_support.
  - right. destruct (split_parent_support col_e2 (1 / 2) col_h2
                     (proj1 (col_child_wf_hiB col_h1))) as [H _].
    rewrite H. apply col_e2_support.
  - right. destruct (split_parent_support col_e2 (1 / 2) col_h2
                     (proj1 (col_child_wf_hiB col_h1))) as [_ H].
    rewrite H. apply col_e2_support.
  - left. destruct (split_parent_support col_pcA (1 / 2) col_h1 (proj1 col_wf_A))
      as [H _]. rewrite H. reflexivity.
  - right. destruct (split_parent_support col_pcB 0 col_h1 (proj1 col_wf_B))
      as [H _]. rewrite H. reflexivity.
Qed.

Lemma col_key_BB : forall t,
  key_param (SuppChord col_B) (SuppChord col_B) t = t.
Proof.
  intro t. unfold key_param, chord_dd, chord_dx, chord_dy, col_B. cbn.
  assert (E : req_b ((3 - 1) * (3 - 1) + (0 - 0) * (0 - 0)) 0 = false)
    by (apply req_b_false; lra).
  rewrite E. unfold chord_eval. cbn. field.
Qed.

Lemma col_key_BA : forall t,
  key_param (SuppChord col_B) (SuppChord col_A) t = t - 1 / 2.
Proof.
  intro t. unfold key_param, chord_dd, chord_dx, chord_dy, col_A, col_B. cbn.
  assert (E : req_b ((3 - 1) * (3 - 1) + (0 - 0) * (0 - 0)) 0 = false)
    by (apply req_b_false; lra).
  rewrite E. unfold chord_eval. cbn. field.
Qed.

Lemma col_pok_B : forall k,
  point_of_key (SuppChord col_B) k = mkPoint (1 + 2 * k) 0.
Proof.
  intro k. unfold point_of_key, chord_dd, chord_dx, chord_dy, col_B. cbn.
  assert (E : req_b ((3 - 1) * (3 - 1) + (0 - 0) * (0 - 0)) 0 = false)
    by (apply req_b_false; lra).
  rewrite E. unfold chord_eval. cbn. apply (f_equal2 mkPoint); ring.
Qed.

Lemma col_keys_BB :
  all_keys (SuppChord col_B) (SuppChord col_B) col_pcs0 = [0; 1].
Proof.
  Opaque key_param.
  unfold all_keys, col_pcs0, piece_keys, col_pcA, col_pcB. cbn.
  rewrite col_chord_neq. rewrite chord_eqb_refl. cbn.
  rewrite col_key_BB, col_key_BB. unfold unit_win. cbn. reflexivity.
  Transparent key_param.
Qed.

Lemma col_keys_BA :
  all_keys (SuppChord col_B) (SuppChord col_A) col_pcs0 = [- (1 / 2); 1 / 2].
Proof.
  Opaque key_param.
  unfold all_keys, col_pcs0, piece_keys, col_pcA, col_pcB. cbn.
  rewrite chord_eqb_refl. rewrite col_chord_neq_swap. cbn.
  rewrite col_key_BA, col_key_BA. unfold unit_win. cbn.
  replace (0 - 1 / 2) with (- (1 / 2)) by field.
  replace (1 - 1 / 2) with (1 / 2) by field. reflexivity.
  Transparent key_param.
Qed.

Lemma col_overlap_BA :
  overlap_pts col_pcs0 (SuppChord col_B) (SuppChord col_A) = [col_P1; col_P2].
Proof.
  unfold overlap_pts. rewrite col_keys_BB, col_keys_BA. cbn [rmin_list rmax_list].
  assert (A0 : Rmin 0 1 = 0) by (apply Rmin_left; lra).
  assert (A1 : Rmax 0 1 = 1) by (apply Rmax_right; lra).
  assert (B0 : Rmin (- (1 / 2)) (1 / 2) = - (1 / 2)) by (apply Rmin_left; lra).
  assert (B1 : Rmax (- (1 / 2)) (1 / 2) = 1 / 2) by (apply Rmax_right; lra).
  rewrite A0, A1, B0, B1.
  assert (Lo : Rmax 0 (- (1 / 2)) = 0) by (apply Rmax_left; lra).
  assert (Hi : Rmin 1 (1 / 2) = 1 / 2) by (apply Rmin_right; lra).
  rewrite Lo, Hi.
  assert (Er : rle_b 0 (1 / 2) = true) by (apply rle_b_true; lra).
  rewrite Er. rewrite !col_pok_B.
  replace (1 + 2 * 0) with 1 by ring.
  replace (1 + 2 * (1 / 2)) with 2 by field.
  unfold col_P1, col_P2. apply dedup_two_neq.
  intro H. apply (f_equal px) in H. cbn in H. lra.
Qed.

Lemma col_overlap_BA_pcs1 : forall h,
  overlap_pts (progress_pieces col_pcs0 0%nat 1%nat col_pcA col_pcB (1 / 2) 0 h)
    (SuppChord col_B) (SuppChord col_A) = [col_P1; col_P2].
Proof.
  intro h. rewrite overlap_stable with (i := 0%nat) (j := 1%nat)
      (a := col_pcA) (b := col_pcB) (ti := 1 / 2) (tj := 0) (h := h).
  - exact col_overlap_BA.
  - reflexivity.
  - reflexivity.
  - discriminate.
  - exact (proj1 col_wf_A).
  - exact (proj1 col_wf_B).
  - lra.
  - lra.
Qed.

Lemma col_overlap_BA_pcs2 :
  overlap_pts col_pcs2 (SuppChord col_B) (SuppChord col_A) = [col_P1; col_P2].
Proof.
  unfold col_pcs2.
  destruct col_nths as [N1 N2].
  rewrite overlap_stable with (i := 1%nat) (j := 3%nat)
      (a := col_e1) (b := col_e2) (ti := 1) (tj := 1 / 2) (h := col_h2).
  - unfold col_pcs1. rewrite <- (col_pcs1_eq col_h1). apply col_overlap_BA_pcs1.
  - exact N1.
  - exact N2.
  - discriminate.
  - exact (proj1 (col_child_wf_hiA col_h1)).
  - exact (proj1 (col_child_wf_hiB col_h1)).
  - lra.
  - lra.
Qed.

Lemma col_end_not_mid : forall pc,
  bp_support pc = SuppChord col_A ->
  (bp_window pc = mkWindow (1 / 2) 1 \/
   bp_window pc = mkWindow 1 1 \/
   bp_window pc = mkWindow 0 (1 / 2)) ->
  ~ piece_endpoint pc col_mid.
Proof.
  intros pc Hs Hw Hep. unfold piece_endpoint in Hep.
  destruct Hep as [Hep|Hep]; rewrite Hs in Hep; apply (f_equal px) in Hep;
    rewrite col_A_px in Hep; destruct Hw as [Hw|[Hw|Hw]]; rewrite Hw in Hep;
    cbn in Hep; lra.
Qed.

Lemma col_mid_not_A : ~ family_vertex col_pcs2 (SuppChord col_A) col_mid.
Proof.
  intros [pc [Hin [Hs Hep]]].
  rewrite col_pcs2_form in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
  - exact (col_end_not_mid _ Hs (or_introl col_a_lo_win) Hep).
  - exact (col_end_not_mid _ Hs (or_intror (or_introl col_a_hi_win)) Hep).
  - destruct (split_parent_support col_e2 (1 / 2) col_h2
              (proj1 (col_child_wf_hiB col_h1))) as [Hsup _].
    rewrite Hsup, col_e2_support in Hs. exact (col_supports_distinct (eq_sym Hs)).
  - destruct (split_parent_support col_e2 (1 / 2) col_h2
              (proj1 (col_child_wf_hiB col_h1))) as [_ Hsup].
    rewrite Hsup, col_e2_support in Hs. exact (col_supports_distinct (eq_sym Hs)).
  - exact (col_end_not_mid _ Hs (or_intror (or_intror col_a0_win)) Hep).
  - destruct (split_parent_support col_pcB 0 col_h1 (proj1 col_wf_B)) as [Hsup _].
    rewrite Hsup in Hs. exact (col_supports_distinct (eq_sym Hs)).
Qed.

Lemma col_mid_on_a :
  window_pts (bp_support (fst (split_piece col_e1 1 col_h2)))
             (bp_window (fst (split_piece col_e1 1 col_h2))) col_mid.
Proof.
  destruct (split_parent_support col_e1 1 col_h2 (proj1 (col_child_wf_hiA col_h1)))
    as [Hs _].
  rewrite Hs, col_e1_support, col_a_lo_win. unfold window_pts, support_at.
  refine (ex_intro _ (3 / 4) _). cbn [win_lo win_hi].
  split; [split; lra|].
  unfold col_mid, chord_eval, col_A. cbn.
  apply (f_equal2 mkPoint); field.
Qed.

Lemma col_mid_on_b :
  window_pts (bp_support (fst (split_piece col_e2 (1 / 2) col_h2)))
             (bp_window (fst (split_piece col_e2 (1 / 2) col_h2))) col_mid.
Proof.
  destruct (split_parent_support col_e2 (1 / 2) col_h2
            (proj1 (col_child_wf_hiB col_h1))) as [Hs _].
  rewrite Hs, col_e2_support, col_b_lo_win. unfold window_pts.
  refine (ex_intro _ (1 / 4) _). cbn [win_lo win_hi].
  split; [split; lra|].
  rewrite col_B_pt. unfold col_mid. apply (f_equal2 mkPoint); field.
Qed.

Lemma col_nth_mid :
  nth_error col_pcs2 0%nat = Some (fst (split_piece col_e1 1 col_h2)) /\
  nth_error col_pcs2 2%nat = Some (fst (split_piece col_e2 (1 / 2) col_h2)).
Proof.
  rewrite col_pcs2_form. split; reflexivity.
Qed.

Lemma col_not_noded : ~ bag_noded col_final.
Proof.
  unfold col_final. rewrite col_bag2_eq. simpl. intro Hn.
  destruct col_nth_mid as [Ha Hc].
  set (a := fst (split_piece col_e1 1 col_h2)).
  set (c := fst (split_piece col_e2 (1 / 2) col_h2)).
  assert (Hwa : piece_wf a).
  { apply (split_piece_wf col_e1 1 col_h2 (col_child_wf_hiA col_h1)). lra. }
  assert (Hwc : piece_wf c).
  { apply (split_piece_wf col_e2 (1 / 2) col_h2 (col_child_wf_hiB col_h1)). lra. }
  destruct (hit_param_line_line a c col_mid Hwa Hwc col_mid_on_a col_mid_on_b)
      as [ti [tj Hok]].
  - exists col_A.
    destruct (split_parent_support col_e1 1 col_h2 (proj1 (col_child_wf_hiA col_h1)))
      as [Hs _]. unfold a. rewrite Hs. apply col_e1_support.
  - exists col_B.
    destruct (split_parent_support col_e2 (1 / 2) col_h2
              (proj1 (col_child_wf_hiB col_h1))) as [Hs _].
    unfold c. rewrite Hs. apply col_e2_support.
  - apply (Hn 0%nat 2%nat a c (IHit col_mid ti tj) Ha Hc).
    + discriminate.
    + exact Hok.
    + unfold progress_hit. intro Hv. destruct Hv as [VA _].
      exact (col_mid_not_A VA).
Qed.

Lemma col_ov_point : forall p s1 s2,
  (s1 = SuppChord col_A /\ s2 = SuppChord col_B) \/
  (s1 = SuppChord col_B /\ s2 = SuppChord col_A) ->
  In p (overlap_pts col_pcs2 s1 s2) ->
  (family_vertex col_pcs2 (SuppChord col_A) p /\
   family_vertex col_pcs2 (SuppChord col_B) p).
Proof.
  intros p s1 s2 Hor Hin.
  destruct Hor as [[-> ->]|[-> ->]].
  - rewrite col_overlap_pcs2 in Hin. destruct Hin as [<-|[<-|[]]].
    + apply col_P1_vertices.
    + apply col_P2_vertices.
  - rewrite col_overlap_BA_pcs2 in Hin. destruct Hin as [<-|[<-|[]]].
    + apply col_P1_vertices.
    + apply col_P2_vertices.
Qed.

Lemma col_final_ov : bag_noded_ov col_final.
Proof.
  unfold col_final. rewrite col_bag2_eq. simpl.
  intros i j a c p ti tj Hi Hj Hij Hok Hante.
  assert (Ha : In a col_pcs2) by (eapply nth_error_In; exact Hi).
  assert (Hc : In c col_pcs2) by (eapply nth_error_In; exact Hj).
  destruct (col_support_kind a Ha) as [Ea|Ea];
  destruct (col_support_kind c Hc) as [Ec|Ec]; rewrite Ea, Ec in *.
  - assert (Hv : family_vertex col_pcs2 (SuppChord col_A) p).
    { apply chord_self_overlap_vertex; [apply col_dd_A|].
      apply Hante. apply overlap_b_same_chord. }
    unfold progress_hit. intro Hp. apply Hp. split; assumption.
  - assert (Hv : family_vertex col_pcs2 (SuppChord col_A) p /\
                 family_vertex col_pcs2 (SuppChord col_B) p).
    { apply (col_ov_point p (SuppChord col_A) (SuppChord col_B));
        [left; split; reflexivity|].
      apply Hante. unfold overlap_pair, overlap_b. rewrite col_canon.
      apply col_same_line. }
    unfold progress_hit. intro Hp. apply Hp. exact Hv.
  - assert (Hv : family_vertex col_pcs2 (SuppChord col_A) p /\
                 family_vertex col_pcs2 (SuppChord col_B) p).
    { apply (col_ov_point p (SuppChord col_B) (SuppChord col_A));
        [right; split; reflexivity|].
      apply Hante. unfold overlap_pair. rewrite overlap_b_sym.
      unfold overlap_b. rewrite col_canon. apply col_same_line. }
    unfold progress_hit. intro Hp. apply Hp.
    destruct Hv as [VA VB]. split; assumption.
  - assert (Hv : family_vertex col_pcs2 (SuppChord col_B) p).
    { apply chord_self_overlap_vertex; [apply col_dd_B|].
      apply Hante. apply overlap_b_same_chord. }
    unfold progress_hit. intro Hp. apply Hp. split; assumption.
Qed.

Lemma col_fixture_ov_not_noded :
  bag_noded_ov col_final /\ ~ bag_noded col_final.
Proof.
  split; [apply col_final_ov| apply col_not_noded].
Qed.

(* -------------------------------------------------------------------------- *)
(* #892 halves: zero steps, and bag_noded_ov. Both key frames' overlap        *)
(* points are vertices of both families.                                      *)
(* -------------------------------------------------------------------------- *)

Lemma iso_overlap_b :
  overlap_b (SuppCircle iso_half_fst) (SuppCircle iso_half_snd) = true.
Proof.
  unfold overlap_b. rewrite iso_canon. apply iso_same_circle.
Qed.

Lemma int_part_one : Int_part 1 = 1%Z.
Proof.
  destruct (base_Int_part 1) as [Hle Hlt].
  pose (n := Int_part 1). fold n in Hle, Hlt.
  assert (Hn_le : (n <= 1)%Z).
  { apply le_IZR. change (IZR 1) with 1. exact Hle. }
  assert (Hn_pos : (0 < n)%Z).
  { apply lt_IZR. change (IZR 0) with 0. lra. }
  lia.
Qed.

Lemma align_k_pi_zero : align_k PI 0 = 1%Z.
Proof.
  unfold align_k.
  pose proof PI_RGT_0 as Hpi.
  assert (Hp : PI <> 0) by lra.
  assert (H2 : 2 * PI <> 0) by nra.
  assert (E : (PI - 0) / (2 * PI) + / 2 = 1).
  { apply (Rmult_eq_reg_l (2 * PI)); [| exact H2].
    replace (2 * PI * ((PI - 0) / (2 * PI) + / 2)) with (PI + PI)
      by (field; exact Hp).
    replace (2 * PI * 1) with (PI + PI) by field.
    ring. }
  rewrite E. apply int_part_one.
Qed.

Lemma iso_key_snd_self : forall t,
  key_param (SuppCircle iso_half_snd) (SuppCircle iso_half_snd) t = PI + t * PI.
Proof.
  intro t. unfold key_param, iso_half_snd. cbn.
  assert (Eb : rle_b 0 (5 * 5) = true) by (apply rle_b_true; lra).
  rewrite Eb. cbv beta iota zeta.
  replace (PI + 0) with PI by ring.
  rewrite align_k_same. replace (IZR 0) with 0 by reflexivity. ring.
Qed.

Lemma iso_key_snd_fst : forall t,
  key_param (SuppCircle iso_half_snd) (SuppCircle iso_half_fst) t = t * PI + 2 * PI.
Proof.
  intro t. unfold key_param, iso_half_snd, iso_half_fst. cbn.
  assert (Eb : rle_b 0 (5 * 5) = true) by (apply rle_b_true; lra).
  rewrite Eb. cbv beta iota zeta.
  replace (0 + 0) with 0 by ring.
  rewrite align_k_pi_zero. change (IZR 1) with 1. ring.
Qed.

Lemma iso_keys_snd_self :
  all_keys (SuppCircle iso_half_snd) (SuppCircle iso_half_snd) iso_half_pcs =
  [PI; 2 * PI].
Proof.
  Opaque key_param.
  unfold all_keys, iso_half_pcs, piece_keys, iso_half_pc. cbn.
  rewrite iso_circ_ord_false. rewrite circ_eqb_refl. cbn.
  rewrite iso_key_snd_self, iso_key_snd_self.
  replace (PI + 0 * PI) with PI by ring.
  replace (PI + 1 * PI) with (2 * PI) by ring. reflexivity.
  Transparent key_param.
Qed.

Lemma iso_keys_snd_fst :
  all_keys (SuppCircle iso_half_snd) (SuppCircle iso_half_fst) iso_half_pcs =
  [2 * PI; 3 * PI].
Proof.
  Opaque key_param.
  unfold all_keys, iso_half_pcs, piece_keys, iso_half_pc. cbn.
  rewrite circ_eqb_refl. rewrite iso_circ_swap_false. cbn.
  rewrite iso_key_snd_fst, iso_key_snd_fst.
  replace (0 * PI + 2 * PI) with (2 * PI) by ring.
  replace (1 * PI + 2 * PI) with (3 * PI) by ring. reflexivity.
  Transparent key_param.
Qed.

Lemma iso_east : point_of_key (SuppCircle iso_half_snd) (2 * PI) = mkPoint 5 0.
Proof.
  unfold point_of_key, iso_half_snd. cbn [circ_sweep circ_theta0 circ_o circ_r].
  destruct (req_b PI 0) eqn:E.
  - apply req_b_true in E. pose proof PI_RGT_0. lra.
  - unfold circ_eval. cbn [circ_o circ_r circ_theta0 circ_sweep px py].
    assert (Hp : PI <> 0). { pose proof PI_RGT_0. lra. }
    replace (PI + ((2 * PI - PI) / PI) * PI) with (2 * PI) by (field; exact Hp).
    rewrite cos_2PI, sin_2PI. apply (f_equal2 mkPoint); ring.
Qed.

Lemma iso_swap_overlap :
  overlap_pts iso_half_pcs (SuppCircle iso_half_snd) (SuppCircle iso_half_fst) =
  [mkPoint 5 0].
Proof.
  unfold overlap_pts. rewrite iso_keys_snd_self, iso_keys_snd_fst.
  cbn [rmin_list rmax_list].
  assert (A0 : Rmin PI (2 * PI) = PI). { apply Rmin_left. pose proof PI_RGT_0. lra. }
  assert (A1 : Rmax PI (2 * PI) = 2 * PI). { apply Rmax_right. pose proof PI_RGT_0. lra. }
  assert (B0 : Rmin (2 * PI) (3 * PI) = 2 * PI). { apply Rmin_left. pose proof PI_RGT_0. lra. }
  assert (B1 : Rmax (2 * PI) (3 * PI) = 3 * PI). { apply Rmax_right. pose proof PI_RGT_0. lra. }
  rewrite A0, A1, B0, B1.
  assert (Lo : Rmax PI (2 * PI) = 2 * PI). { apply Rmax_right. pose proof PI_RGT_0. lra. }
  assert (Hi : Rmin (2 * PI) (3 * PI) = 2 * PI). { apply Rmin_left. pose proof PI_RGT_0. lra. }
  rewrite Lo, Hi.
  assert (Er : rle_b (2 * PI) (2 * PI) = true) by (apply rle_b_true; lra).
  rewrite Er. rewrite iso_east. apply dedup_dup.
Qed.

Lemma iso_east_fst :
  support_at (SuppCircle iso_half_fst) 0 = mkPoint 5 0.
Proof.
  unfold support_at, circ_eval, iso_half_fst. cbn.
  replace (0 + 0 * PI) with 0 by ring.
  rewrite cos_0, sin_0. apply (f_equal2 mkPoint); ring.
Qed.

Lemma iso_east_snd :
  support_at (SuppCircle iso_half_snd) 1 = mkPoint 5 0.
Proof.
  unfold support_at, circ_eval, iso_half_snd. cbn.
  replace (PI + 1 * PI) with (2 * PI) by ring.
  rewrite cos_2PI, sin_2PI. apply (f_equal2 mkPoint); ring.
Qed.

Lemma iso_swap_hens : forall p,
  In p (overlap_pts iso_half_pcs (SuppCircle iso_half_snd)
           (SuppCircle iso_half_fst)) ->
  family_vertex iso_half_pcs (SuppCircle iso_half_fst) p /\
  family_vertex iso_half_pcs (SuppCircle iso_half_snd) p.
Proof.
  intros p Hin.
  assert (Hin' : In p [mkPoint 5 0]).
  { exact (eq_rect _ (fun l => In p l) Hin _ iso_swap_overlap). }
  destruct Hin' as [<-|[]]. split.
  - exists (iso_half_pc 0 1 iso_half_fst). split; [simpl; auto|]. split; [reflexivity|].
    unfold piece_endpoint, iso_half_pc. cbn. left. symmetry. apply iso_east_fst.
  - exists (iso_half_pc 1 0 iso_half_snd). split; [simpl; auto|]. split; [reflexivity|].
    unfold piece_endpoint, iso_half_pc. cbn. right. symmetry. apply iso_east_snd.
Qed.

Lemma none_pick_spec : forall b, pick_spec (fun _ => None) b.
Proof.
  intros b. unfold pick_spec. destruct b; simpl; exact I.
Qed.

Lemma halves_bag_ov : bag_noded_ov iso_half_bag.
Proof.
  unfold iso_half_bag. simpl.
  intros i j a c p ti tj Hi Hj Hij Hok Hante.
  assert (Hi2 : (i < 2)%nat) by (apply (nth_length _ _ _ _ Hi)).
  assert (Hj2 : (j < 2)%nat) by (apply (nth_length _ _ _ _ Hj)).
  destruct i as [|i]; destruct j as [|j].
  - exfalso. apply Hij. reflexivity.
  - destruct j as [|j]; [| lia].
    simpl in Hi, Hj. inversion Hi. inversion Hj. subst a c.
    assert (Hv : family_vertex iso_half_pcs (SuppCircle iso_half_fst) p /\
                 family_vertex iso_half_pcs (SuppCircle iso_half_snd) p).
    { apply iso_half_overlap_are_hens. apply Hante. unfold overlap_pair.
      apply iso_overlap_b. }
    unfold progress_hit. intro Hp. apply Hp. exact Hv.
  - destruct i as [|i]; [| lia].
    simpl in Hi, Hj. inversion Hi. inversion Hj. subst a c.
    assert (Hv : family_vertex iso_half_pcs (SuppCircle iso_half_fst) p /\
                 family_vertex iso_half_pcs (SuppCircle iso_half_snd) p).
    { apply iso_swap_hens. apply Hante. unfold overlap_pair.
      rewrite overlap_b_sym. apply iso_overlap_b. }
    unfold progress_hit. cbn [bp_support iso_half_pc]. intro Hp.
    destruct Hv as [Vf Vs]. apply Hp. split; [exact Vs| exact Vf].
  - destruct i as [|i]; [| lia]. destruct j as [|j]; [| lia].
    exfalso. apply Hij. reflexivity.
Qed.

Lemma halves_zero_ov :
  bag_noded_ov iso_half_bag /\
  bag_run_steps (fun _ => None) (S (rho iso_half_bag)) iso_half_bag = 0%nat.
Proof.
  split.
  - apply halves_bag_ov.
  - destruct (halves_zero_steps (fun _ => None)
               (fun b => none_pick_spec b)) as [Hs _].
    exact Hs.
Qed.

(* The converse rho = 0 -> bag_noded_ov is refuted in
   SheetHenNodedOvGap.v : rho_zero_not_ov. *)

Print Assumptions nth_length.
Print Assumptions ov_fold_zero.
Print Assumptions ov_pair_sum_zero.
Print Assumptions ov_counted_images.
Print Assumptions ov_counted_end.
Print Assumptions overlap_b_sym.
Print Assumptions canon_fixed.
Print Assumptions canon_overlap_eq.
Print Assumptions same_line_refl.
Print Assumptions overlap_b_same_chord.
Print Assumptions chord_self_key.
Print Assumptions chord_self_point.
Print Assumptions key_in_vertex.
Print Assumptions chord_self_overlap_vertex.
Print Assumptions bag_noded_implies_ov.
Print Assumptions pieces_hit.
Print Assumptions noded_ov_rho_zero.
Print Assumptions col_dd_A.
Print Assumptions col_dd_B.
Print Assumptions col_A_px.
Print Assumptions col_B_pt.
Print Assumptions split_parent_support.
Print Assumptions col_e1_support.
Print Assumptions col_e2_support.
Print Assumptions col_e1_win.
Print Assumptions col_e2_win.
Print Assumptions col_a_lo_win.
Print Assumptions col_a_hi_win.
Print Assumptions col_b_lo_win.
Print Assumptions col_a0_win.
Print Assumptions col_pcs2_form.
Print Assumptions col_support_kind.
Print Assumptions col_key_BB.
Print Assumptions col_key_BA.
Print Assumptions col_pok_B.
Print Assumptions col_keys_BB.
Print Assumptions col_keys_BA.
Print Assumptions col_overlap_BA.
Print Assumptions col_overlap_BA_pcs1.
Print Assumptions col_overlap_BA_pcs2.
Print Assumptions col_end_not_mid.
Print Assumptions col_mid_not_A.
Print Assumptions col_mid_on_a.
Print Assumptions col_mid_on_b.
Print Assumptions col_nth_mid.
Print Assumptions col_not_noded.
Print Assumptions col_ov_point.
Print Assumptions col_final_ov.
Print Assumptions col_fixture_ov_not_noded.
Print Assumptions iso_overlap_b.
Print Assumptions int_part_one.
Print Assumptions align_k_pi_zero.
Print Assumptions iso_key_snd_self.
Print Assumptions iso_key_snd_fst.
Print Assumptions iso_keys_snd_self.
Print Assumptions iso_keys_snd_fst.
Print Assumptions iso_east.
Print Assumptions iso_swap_overlap.
Print Assumptions iso_east_fst.
Print Assumptions iso_east_snd.
Print Assumptions iso_swap_hens.
Print Assumptions none_pick_spec.
Print Assumptions halves_bag_ov.
Print Assumptions halves_zero_ov.
