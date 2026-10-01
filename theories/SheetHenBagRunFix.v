(* SheetHenBagRunFix — letter 3 fixtures.
   Steps: locked quarter 1, #892 halves 0, collinear 2 (then ρ = 0),
   tangency 1 at the double root, partial co-circular overlap 1.
   3-axiom host. No Admitted / Axiom / Parameter.
   AI-drafted, human-reviewed. Assisted-by: Cursor Grok 4.7.
   License: BSD-3-Clause (see LICENSE). *)

From Stdlib Require Import Reals Lra Lia List PeanoNat Bool Permutation.
From NTS.Proofs Require Import Distance SheetHenCook SheetHenBag SheetHenRho
  ZetaHostHit SheetHenBagRun HostCircChordOracle.
Import ListNotations.
Local Open Scope R_scope.

Lemma steps_none : forall pick fuel b,
  match b with
  | BagDeclined _ => True
  | BagLive _ _ => pick b = None
  end ->
  bag_run_steps pick fuel b = 0%nat.
Proof.
  intros pick fuel. induction fuel as [|fuel IH]; intros b Hs; simpl; [reflexivity|].
  destruct b as [sh pcs|sh]; [|reflexivity]. rewrite Hs. reflexivity.
Qed.

Lemma run_none : forall pick fuel b,
  match b with
  | BagDeclined _ => True
  | BagLive _ _ => pick b = None
  end ->
  bag_run pick fuel b = b.
Proof.
  intros pick fuel. induction fuel as [|fuel IH]; intros b Hs; simpl; [reflexivity|].
  destruct b as [sh pcs|sh]; [|reflexivity]. rewrite Hs. reflexivity.
Qed.

Lemma rho_two : forall pcs s1 s2,
  supports_of pcs = [s1; s2] ->
  rho_pcs pcs = length (counted pcs s1 s2).
Proof.
  intros pcs s1 s2 Hs. unfold rho_pcs. rewrite Hs. simpl. lia.
Qed.

Lemma overlap_stable : forall pcs i j a b ti tj h s1 s2,
  nth_error pcs i = Some a ->
  nth_error pcs j = Some b ->
  i <> j ->
  piece_realizes a ->
  piece_realizes b ->
  0 <= ti <= 1 ->
  0 <= tj <= 1 ->
  overlap_pts (progress_pieces pcs i j a b ti tj h) s1 s2 =
  overlap_pts pcs s1 s2.
Proof.
  intros pcs i j a b ti tj h s1 s2 Hi Hj Hij Hra Hrb Hti Htj.
  destruct (hull_progress s1 s1 pcs i j a b ti tj h Hi Hj Hij Hra Hrb Hti Htj)
    as [M1 [X1 N1]].
  destruct (hull_progress s1 s2 pcs i j a b ti tj h Hi Hj Hij Hra Hrb Hti Htj)
    as [M2 [X2 N2]].
  symmetry.
  apply (overlap_eq pcs (progress_pieces pcs i j a b ti tj h) s1 s2
           M1 X1 N1 M2 X2 N2).
Qed.

Lemma drop_pair_01_two : forall a b, drop_pair 0%nat 1%nat [a; b] = [].
Proof.
  intros a b. unfold drop_pair, keep_other_idx, filter_idx. simpl. reflexivity.
Qed.

Lemma drop_pair_13_four : forall a b c d,
  drop_pair 1%nat 3%nat [a; b; c; d] = [a; c].
Proof.
  intros a b c d. unfold drop_pair, keep_other_idx, filter_idx. simpl. reflexivity.
Qed.

Lemma dedup_two_neq : forall p q, p <> q -> dedup [p; q] = [p; q].
Proof.
  intros p q H.
  assert (E : pt_eqb p q = false).
  { destruct (pt_eqb p q) eqn:Eb; [|reflexivity].
    apply pt_eqb_true in Eb. contradiction. }
  unfold dedup. cbn [existsb]. simpl. rewrite E. simpl. reflexivity.
Qed.

Definition pick_two (P : Point) (ti tj : R) (b : SheetBag) : option HitPick :=
  match b with
  | BagDeclined _ => None
  | BagLive _ pcs =>
      match pcs with
      | [e1; e2] =>
          if andb (admissible_hit_b pcs e1 e2 P ti tj)
                  (negb (support_eqb (bp_support e1) (bp_support e2)))
          then Some (mkHitPick 0%nat 1%nat P ti tj)
          else None
      | _ => None
      end
  end.

Lemma pick_two_some : forall sh e1 e2 P ti tj,
  admissible_hit [e1; e2] e1 e2 P ti tj ->
  bp_support e1 <> bp_support e2 ->
  pick_two P ti tj (BagLive sh [e1; e2]) = Some (mkHitPick 0%nat 1%nat P ti tj).
Proof.
  intros sh e1 e2 P ti tj Hadm Hne. unfold pick_two. simpl.
  assert (Ha : admissible_hit_b [e1; e2] e1 e2 P ti tj = true).
  { apply admissible_hit_spec. exact Hadm. }
  assert (Hs : support_eqb (bp_support e1) (bp_support e2) = false).
  { destruct (support_eqb (bp_support e1) (bp_support e2)) eqn:E; [|reflexivity].
    apply support_eqb_true in E. contradiction. }
  rewrite Ha, Hs. simpl. reflexivity.
Qed.

Lemma pick_two_after : forall sh e1 e2 P ti tj,
  pick_two P ti tj
    (step_hit (BagLive sh [e1; e2]) (mkHitPick 0%nat 1%nat P ti tj)) = None.
Proof.
  intros sh e1 e2 P ti tj.
  Opaque mint_or_share.
  unfold step_hit. simpl hp_i. simpl hp_j. simpl hp_P. simpl hp_ti. simpl hp_tj.
  simpl nth_error. unfold progress_pieces.
  rewrite drop_pair_01_two. rewrite app_nil_r.
  unfold pick_two, cooked_four. simpl. reflexivity.
  Transparent mint_or_share.
Qed.

Lemma one_step_report : forall pick (b : SheetBag) (w : HitPick),
  pick b = Some w ->
  (match step_hit b w with
   | BagDeclined _ => False
   | BagLive _ _ => pick (step_hit b w) = None
   end) ->
  (1 <= rho b)%nat ->
  bag_run_steps pick (S (rho b)) b = 1%nat /\
  bag_run pick (S (rho b)) b = step_hit b w /\
  run_stopped pick (bag_run pick (S (rho b)) b).
Proof.
  intros pick b w Hsome Hnone Hpos.
  destruct b as [sh pcs|sh]; [ | simpl in Hnone; contradiction ].
  destruct (rho (BagLive sh pcs)) as [|k] eqn:Hr; [ exfalso; lia | ].
  destruct (step_hit (BagLive sh pcs) w) as [sh2 pcs2|sh2] eqn:Es.
  - cbn [bag_run_steps bag_run]. rewrite Hsome.
    cbn [bag_run_steps bag_run]. rewrite Es.
    cbn [bag_run_steps bag_run]. rewrite Hnone.
    cbn [bag_run_steps bag_run].
    split; [ reflexivity | split; [ reflexivity | ] ].
    unfold run_stopped. exact Hnone.
  - contradiction.
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked quarter × chord. One interior hit, then the selector declines.      *)
(* -------------------------------------------------------------------------- *)

Lemma f1_admissible :
  admissible_hit [f1_circ_pc; f1_chord_pc] f1_circ_pc f1_chord_pc
    f1_hit_pt f1_ti f1_tj.
Proof.
  split; [|split].
  - unfold f1_circ_pc, f1_chord_pc. simpl. exact f1_I_ok.
  - intro Hv. apply f1_not_circ_vertex. exact (proj1 Hv).
  - intro Ho. unfold overlap, f1_circ_pc, f1_chord_pc in Ho. simpl in Ho.
    rewrite overlap_b_circ_chord in Ho. discriminate.
Qed.

Lemma f1_supports :
  supports_of [f1_circ_pc; f1_chord_pc] =
  [SuppCircle F1_egg; SuppChord F1_chord].
Proof.
  unfold supports_of, f1_circ_pc, f1_chord_pc. simpl. reflexivity.
Qed.

Lemma f1_rho_pos :
  (1 <= rho (BagLive default_sheet [f1_circ_pc; f1_chord_pc]))%nat.
Proof.
  simpl. rewrite (rho_two _ _ _ f1_supports).
  assert (Hin : In f1_hit_pt
      (counted [f1_circ_pc; f1_chord_pc]
         (bp_support f1_circ_pc) (bp_support f1_chord_pc))).
  { exact (admissible_in_counted _ _ _ _ _ _
      (in_eq _ _) (in_cons _ _ _ (in_eq _ _))
      f1_circ_wf f1_chord_wf ltac:(discriminate) f1_admissible). }
  replace (counted [f1_circ_pc; f1_chord_pc] (SuppCircle F1_egg) (SuppChord F1_chord))
    with (counted [f1_circ_pc; f1_chord_pc]
            (bp_support f1_circ_pc) (bp_support f1_chord_pc))
    by (unfold f1_circ_pc, f1_chord_pc; simpl; reflexivity).
  destruct (counted [f1_circ_pc; f1_chord_pc]
              (bp_support f1_circ_pc) (bp_support f1_chord_pc))
    as [|p tl].
  - destruct Hin.
  - simpl. apply le_n_S. apply Nat.le_0_l.
Qed.

Definition f1_bag : SheetBag :=
  BagLive default_sheet [f1_circ_pc; f1_chord_pc].

Definition f1_pick : SheetBag -> option HitPick :=
  pick_two f1_hit_pt f1_ti f1_tj.

Theorem fix_locked_steps :
  bag_run_steps f1_pick (S (rho f1_bag)) f1_bag = 1%nat /\
  run_stopped f1_pick (bag_run f1_pick (S (rho f1_bag)) f1_bag).
Proof.
  assert (Hs : f1_pick f1_bag = Some (mkHitPick 0%nat 1%nat f1_hit_pt f1_ti f1_tj)).
  { unfold f1_pick, f1_bag. apply pick_two_some.
    - exact f1_admissible.
    - discriminate. }
  destruct (one_step_report f1_pick f1_bag
              (mkHitPick 0%nat 1%nat f1_hit_pt f1_ti f1_tj) Hs)
    as [Hc [_ Hstop]].
  - unfold f1_pick, f1_bag.
    exact (pick_two_after default_sheet f1_circ_pc f1_chord_pc
             f1_hit_pt f1_ti f1_tj).
  - exact f1_rho_pos.
  - split; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* #892 halves. ρ is already 0, so every sound selector takes zero steps.     *)
(* -------------------------------------------------------------------------- *)

Definition iso_half_bag : SheetBag := BagLive default_sheet iso_half_pcs.

Theorem halves_zero_steps : forall pick,
  (forall b0, pick_spec pick b0) ->
  bag_run_steps pick (S (rho iso_half_bag)) iso_half_bag = 0%nat /\
  run_stopped pick (bag_run pick (S (rho iso_half_bag)) iso_half_bag).
Proof.
  intros pick Hspec.
  assert (Hr : rho iso_half_bag = 0%nat).
  { unfold iso_half_bag, rho. exact iso_half_pair_rho_zero. }
  rewrite Hr. simpl.
  destruct (pick iso_half_bag) as [w|] eqn:Ep.
  - exfalso.
    assert (Hlt : (rho (step_hit iso_half_bag w) < rho iso_half_bag)%nat).
    { apply step_hit_rho_lt.
      specialize (Hspec iso_half_bag).
      unfold pick_spec, iso_half_bag in Hspec, Ep.
      rewrite Ep in Hspec. exact Hspec. }
    rewrite Hr in Hlt. exact (Nat.nlt_0_r _ Hlt).
  - split; [reflexivity|]. unfold run_stopped, iso_half_bag. exact Ep.
Qed.

(* -------------------------------------------------------------------------- *)
(* Collinear overlap [0,2] × [1,3]. Two admissible endpoints, then ρ = 0.     *)
(* -------------------------------------------------------------------------- *)

Definition col_A : ChordEgg := mkChordEgg (mkPoint 0 0) (mkPoint 2 0).
Definition col_B : ChordEgg := mkChordEgg (mkPoint 1 0) (mkPoint 3 0).
Definition col_P1 : Point := mkPoint 1 0.
Definition col_P2 : Point := mkPoint 2 0.

Definition col_pcA : BagPiece :=
  mkBagPiece (mkChicken 0%nat 1%nat (MkChord col_A)) (SuppChord col_A) unit_win [].
Definition col_pcB : BagPiece :=
  mkBagPiece (mkChicken 2%nat 3%nat (MkChord col_B)) (SuppChord col_B) unit_win [].
Definition col_pcs0 : list BagPiece := [col_pcA; col_pcB].
Definition col_bag : SheetBag := BagLive default_sheet col_pcs0.

Lemma col_wf_A : piece_wf col_pcA.
Proof.
  unfold piece_wf, piece_realizes, col_pcA. cbn.
  split; [|unfold window_ordered, unit_win; cbn; lra].
  symmetry. apply window_chord_unit.
Qed.

Lemma col_wf_B : piece_wf col_pcB.
Proof.
  unfold piece_wf, piece_realizes, col_pcB. cbn.
  split; [|unfold window_ordered, unit_win; cbn; lra].
  symmetry. apply window_chord_unit.
Qed.

Lemma col_supports_distinct : SuppChord col_A <> SuppChord col_B.
Proof.
  intro H. inversion H. unfold col_A, col_B in H1. inversion H1. lra.
Qed.

Lemma col_same_line : same_line_b col_A col_B = true.
Proof.
  unfold same_line_b, cross2, chord_dx, chord_dy, col_A, col_B. cbn.
  assert (E2 : req_b (2 - 0) 0 = false) by (apply req_b_false; lra).
  assert (E0 : req_b (0 - 0) 0 = true) by (apply req_b_true; ring).
  rewrite E2, E0. cbn.
  apply andb_true_intro. split; apply req_b_true; ring.
Qed.

Lemma col_canon :
  canon2 (SuppChord col_A) (SuppChord col_B) =
  (SuppChord col_A, SuppChord col_B).
Proof.
  unfold canon2, support_reals, col_A, col_B. cbn [px py ce_p0 ce_p1].
  unfold rlex_le.
  destruct (Req_EM_T 0 0) as [_|N0]; [|congruence].
  destruct (Req_EM_T 0 1) as [Bad|N01]; [lra|].
  destruct (Rle_dec 0 1) as [_|H]; [|lra]. reflexivity.
Qed.

Lemma col_key_AA : forall t,
  key_param (SuppChord col_A) (SuppChord col_A) t = t.
Proof.
  intro t. unfold key_param, chord_dd, chord_dx, chord_dy, col_A. cbn.
  assert (E : req_b ((2 - 0) * (2 - 0) + (0 - 0) * (0 - 0)) 0 = false)
    by (apply req_b_false; lra).
  rewrite E. unfold chord_eval. cbn. field.
Qed.

Lemma col_key_AB : forall t,
  key_param (SuppChord col_A) (SuppChord col_B) t = t + 1 / 2.
Proof.
  intro t. unfold key_param, chord_dd, chord_dx, chord_dy, col_A, col_B. cbn.
  assert (E : req_b ((2 - 0) * (2 - 0) + (0 - 0) * (0 - 0)) 0 = false)
    by (apply req_b_false; lra).
  rewrite E. unfold chord_eval. cbn. field.
Qed.

Lemma chord_eqb_refl : forall c, chord_eqb c c = true.
Proof.
  intro c. unfold chord_eqb. apply andb_true_intro.
  split; apply pt_eqb_true; reflexivity.
Qed.

Lemma col_chord_neq : chord_eqb col_A col_B = false.
Proof.
  unfold chord_eqb, pt_eqb, col_A, col_B. cbn.
  assert (E : req_b 0 1 = false) by (apply req_b_false; lra).
  rewrite E. reflexivity.
Qed.

Lemma col_chord_neq_swap : chord_eqb col_B col_A = false.
Proof.
  unfold chord_eqb, pt_eqb, col_A, col_B. cbn.
  assert (E : req_b 1 0 = false) by (apply req_b_false; lra).
  rewrite E. reflexivity.
Qed.

Lemma col_keys_AA :
  all_keys (SuppChord col_A) (SuppChord col_A) col_pcs0 = [0; 1].
Proof.
  Opaque key_param.
  unfold all_keys, col_pcs0, piece_keys, col_pcA, col_pcB. cbn.
  rewrite chord_eqb_refl. rewrite col_chord_neq_swap. cbn.
  rewrite col_key_AA, col_key_AA.
  unfold unit_win. cbn. reflexivity.
  Transparent key_param.
Qed.

Lemma col_keys_AB :
  all_keys (SuppChord col_A) (SuppChord col_B) col_pcs0 = [1 / 2; 3 / 2].
Proof.
  Opaque key_param.
  unfold all_keys, col_pcs0, piece_keys, col_pcA, col_pcB. cbn.
  rewrite col_chord_neq. rewrite chord_eqb_refl. cbn.
  rewrite col_key_AB, col_key_AB.
  unfold unit_win. cbn.
  replace (0 + 1 / 2) with (1 / 2) by ring.
  replace (1 + 1 / 2) with (3 / 2) by field.
  reflexivity.
  Transparent key_param.
Qed.

Lemma col_pok : forall k,
  point_of_key (SuppChord col_A) k = mkPoint (2 * k) 0.
Proof.
  intro k. unfold point_of_key, chord_dd, chord_dx, chord_dy, col_A. cbn.
  assert (E : req_b ((2 - 0) * (2 - 0) + (0 - 0) * (0 - 0)) 0 = false)
    by (apply req_b_false; lra).
  rewrite E. unfold chord_eval. cbn. apply (f_equal2 mkPoint); ring.
Qed.

Lemma col_overlap :
  overlap_pts col_pcs0 (SuppChord col_A) (SuppChord col_B) = [col_P1; col_P2].
Proof.
  unfold overlap_pts. rewrite col_keys_AA, col_keys_AB. cbn [rmin_list rmax_list].
  assert (A0 : Rmin 0 1 = 0) by (apply Rmin_left; lra).
  assert (A1 : Rmax 0 1 = 1) by (apply Rmax_right; lra).
  assert (B0 : Rmin (1 / 2) (3 / 2) = 1 / 2) by (apply Rmin_left; lra).
  assert (B1 : Rmax (1 / 2) (3 / 2) = 3 / 2) by (apply Rmax_right; lra).
  rewrite A0, A1, B0, B1.
  assert (Lo : Rmax 0 (1 / 2) = 1 / 2) by (apply Rmax_right; lra).
  assert (Hi : Rmin 1 (3 / 2) = 1) by (apply Rmin_left; lra).
  rewrite Lo, Hi.
  assert (Er : rle_b (1 / 2) 1 = true) by (apply rle_b_true; lra).
  rewrite Er. rewrite !col_pok.
  replace (2 * (1 / 2)) with 1 by field.
  replace (2 * 1) with 2 by ring.
  apply dedup_two_neq. intro H. apply (f_equal px) in H. cbn in H. lra.
Qed.

Lemma col_I_ok_1 :
  I_ok (MkChord col_A) (MkChord col_B) (IHit col_P1 (1 / 2) 0).
Proof.
  simpl. split; unfold on_chord, chord_eval, col_A, col_B, col_P1; cbn; split;
    try lra; apply (f_equal2 mkPoint); field.
Qed.

Lemma col_P1_not_A :
  ~ family_vertex col_pcs0 (SuppChord col_A) col_P1.
Proof.
  intros [pc [Hin [Hs Hep]]].
  destruct Hin as [<-|[<-|[]]].
  - unfold piece_endpoint, col_pcA, support_at, chord_eval, col_A, col_P1 in Hep.
    cbn in Hep. destruct Hep as [Hep|Hep]; apply (f_equal px) in Hep; cbn in Hep; lra.
  - unfold col_pcB in Hs. cbn in Hs. exact (col_supports_distinct (eq_sym Hs)).
Qed.

Lemma col_admissible_1 :
  admissible_hit col_pcs0 col_pcA col_pcB col_P1 (1 / 2) 0.
Proof.
  split; [|split].
  - unfold col_pcA, col_pcB. simpl. exact col_I_ok_1.
  - intro Hv. apply col_P1_not_A. exact (proj1 Hv).
  - intro Ho. unfold overlap_endpoints, col_pcA, col_pcB. simpl.
    rewrite col_canon. simpl. rewrite col_overlap. left. reflexivity.
Qed.

Lemma col_supports : supports_of col_pcs0 = [SuppChord col_A; SuppChord col_B].
Proof.
  unfold col_pcs0, supports_of, col_pcA, col_pcB. simpl.
  unfold support_eqb. rewrite col_chord_neq. reflexivity.
Qed.

Lemma col_rho_pos : (1 <= rho col_bag)%nat.
Proof.
  unfold col_bag, rho. rewrite (rho_two _ _ _ col_supports).
  assert (Hin : In col_P1 (counted col_pcs0 (SuppChord col_A) (SuppChord col_B))).
  { exact (admissible_in_counted _ _ _ _ _ _
      (in_eq _ _) (in_cons _ _ _ (in_eq _ _))
      col_wf_A col_wf_B col_supports_distinct col_admissible_1). }
  destruct (counted col_pcs0 (SuppChord col_A) (SuppChord col_B)) as [|p tl] eqn:E.
  - destruct Hin.
  - simpl. lia.
Qed.

Lemma col_step2_I_ok : forall h,
  I_ok (ck_egg (bp_ck (snd (split_piece col_pcA (1 / 2) h))))
       (ck_egg (bp_ck (snd (split_piece col_pcB 0 h))))
       (IHit col_P2 1 (1 / 2)).
Proof.
  intro h. unfold col_pcA, col_pcB.
  destruct (split_piece_chord_cook 0%nat 1%nat col_A (SuppChord col_A)
              unit_win [] (1 / 2) h) as [_ [_ [_ [Ha _]]]].
  destruct (split_piece_chord_cook 2%nat 3%nat col_B (SuppChord col_B)
              unit_win [] 0 h) as [_ [_ [_ [Hb _]]]].
  rewrite Ha, Hb. simpl. split; unfold on_chord; split; try lra;
  unfold chord_eval, col_A, col_B, col_P2; cbn;
  apply (f_equal2 mkPoint); field.
Qed.

Lemma col_P2_not_B_child : forall h pc,
  pc = fst (split_piece col_pcB 0 h) \/ pc = snd (split_piece col_pcB 0 h) ->
  ~ piece_endpoint pc col_P2.
Proof.
  intros h pc [->| ->] Hep.
  - destruct (split_windows_sub col_pcB 0 h (proj1 col_wf_B)) as [Hs1 [_ [Hw1 _]]].
    unfold piece_endpoint in Hep. rewrite Hs1, Hw1 in Hep.
    unfold piece_endpoint, sub_lo, win_abs, unit_win, support_at, chord_eval,
      col_pcB, col_B, col_P2 in Hep.
    cbn in Hep. destruct Hep as [Hep|Hep]; apply (f_equal px) in Hep; cbn in Hep; lra.
  - destruct (split_windows_sub col_pcB 0 h (proj1 col_wf_B)) as [_ [Hs2 [_ Hw2]]].
    unfold piece_endpoint in Hep. rewrite Hs2, Hw2 in Hep.
    unfold piece_endpoint, sub_hi, win_abs, unit_win, support_at, chord_eval,
      col_pcB, col_B, col_P2 in Hep.
    cbn in Hep. destruct Hep as [Hep|Hep]; apply (f_equal px) in Hep; cbn in Hep; lra.
Qed.

Lemma col_P2_not_B_four : forall h,
  ~ family_vertex (cooked_four col_pcA col_pcB (1 / 2) 0 h) (SuppChord col_B) col_P2.
Proof.
  intros h [pc [Hin [Hs Hep]]].
  unfold cooked_four in Hin. simpl in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]].
  - simpl in Hs. exact (col_supports_distinct Hs).
  - simpl in Hs. exact (col_supports_distinct Hs).
  - exact (col_P2_not_B_child h _ (or_introl eq_refl) Hep).
  - exact (col_P2_not_B_child h _ (or_intror eq_refl) Hep).
Qed.

Lemma col_child_wf_hiA : forall h, piece_wf (snd (split_piece col_pcA (1 / 2) h)).
Proof.
  intro h. exact (proj2 (split_piece_wf col_pcA (1 / 2) h col_wf_A ltac:(lra))).
Qed.

Lemma col_child_wf_hiB : forall h, piece_wf (snd (split_piece col_pcB 0 h)).
Proof.
  intro h. exact (proj2 (split_piece_wf col_pcB 0 h col_wf_B ltac:(lra))).
Qed.

Lemma col_pcs1_eq : forall h,
  progress_pieces col_pcs0 0%nat 1%nat col_pcA col_pcB (1 / 2) 0 h =
  cooked_four col_pcA col_pcB (1 / 2) 0 h.
Proof.
  intro h. unfold progress_pieces, col_pcs0. rewrite drop_pair_01_two.
  apply app_nil_r.
Qed.

Lemma col_overlap_pcs1 : forall h,
  overlap_pts (progress_pieces col_pcs0 0%nat 1%nat col_pcA col_pcB (1 / 2) 0 h)
    (SuppChord col_A) (SuppChord col_B) =
  [col_P1; col_P2].
Proof.
  intro h. rewrite overlap_stable with (i := 0%nat) (j := 1%nat)
      (a := col_pcA) (b := col_pcB) (ti := 1 / 2) (tj := 0) (h := h).
  - exact col_overlap.
  - reflexivity.
  - reflexivity.
  - discriminate.
  - exact (proj1 col_wf_A).
  - exact (proj1 col_wf_B).
  - lra.
  - lra.
Qed.

Lemma col_admissible_2 : forall h,
  let pcs := progress_pieces col_pcs0 0%nat 1%nat col_pcA col_pcB (1 / 2) 0 h in
  let e1 := snd (split_piece col_pcA (1 / 2) h) in
  let e2 := snd (split_piece col_pcB 0 h) in
  admissible_hit pcs e1 e2 col_P2 1 (1 / 2).
Proof.
  intros h pcs e1 e2. split; [|split].
  - subst e1 e2. exact (col_step2_I_ok h).
  - intro Hv. apply (col_P2_not_B_four h).
    rewrite <- (col_pcs1_eq h). exact (proj2 Hv).
  - intros _. subst e1 e2 pcs.
    destruct (split_windows_sub col_pcA (1 / 2) h (proj1 col_wf_A)) as [_ [HA _]].
    destruct (split_windows_sub col_pcB 0 h (proj1 col_wf_B)) as [_ [HB _]].
    unfold overlap_endpoints. rewrite HA, HB. unfold col_pcA, col_pcB. simpl.
    rewrite col_canon. simpl. rewrite col_overlap_pcs1. right. left. reflexivity.
Qed.

Definition pick_at (n i j : nat) (P : Point) (ti tj : R) (b : SheetBag)
  : option HitPick :=
  match b with
  | BagDeclined _ => None
  | BagLive _ pcs =>
      if Nat.eqb (length pcs) n then
        match nth_error pcs i, nth_error pcs j with
        | Some e1, Some e2 =>
            if andb (andb (admissible_hit_b pcs e1 e2 P ti tj)
                          (negb (support_eqb (bp_support e1) (bp_support e2))))
                    (negb (Nat.eqb i j))
            then Some (mkHitPick i j P ti tj)
            else None
        | _, _ => None
        end
      else None
  end.

Definition col_pick (b : SheetBag) : option HitPick :=
  match pick_at 2%nat 0%nat 1%nat col_P1 (1 / 2) 0 b with
  | Some w => Some w
  | None => pick_at 4%nat 1%nat 3%nat col_P2 1 (1 / 2) b
  end.

Lemma col_pick_0 :
  col_pick col_bag = Some (mkHitPick 0%nat 1%nat col_P1 (1 / 2) 0).
Proof.
  Opaque admissible_hit_b support_eqb col_pcA col_pcB.
  unfold col_pick, col_bag, pick_at, col_pcs0. cbn.
  assert (Ha : admissible_hit_b [col_pcA; col_pcB] col_pcA col_pcB
                 col_P1 (1 / 2) 0 = true).
  { Transparent admissible_hit_b. unfold col_pcs0.
    apply admissible_hit_spec. exact col_admissible_1. }
  assert (Hs : support_eqb (bp_support col_pcA) (bp_support col_pcB) = false).
  { Transparent support_eqb col_pcA col_pcB.
    unfold col_pcA, col_pcB. cbn. exact col_chord_neq. }
  rewrite Ha, Hs. cbn. reflexivity.
  Transparent admissible_hit_b support_eqb col_pcA col_pcB.
Qed.

Definition col_h1 : Hen := mint_or_share col_pcs0 col_P1.
Definition col_bag1 : SheetBag :=
  step_hit col_bag (mkHitPick 0%nat 1%nat col_P1 (1 / 2) 0).
Definition col_e1 : BagPiece := snd (split_piece col_pcA (1 / 2) col_h1).
Definition col_e2 : BagPiece := snd (split_piece col_pcB 0 col_h1).
Definition col_w2 : HitPick := mkHitPick 1%nat 3%nat col_P2 1 (1 / 2).
Definition col_bag2 : SheetBag := step_hit col_bag1 col_w2.

Lemma col_bag1_pieces :
  col_bag1 = BagLive default_sheet (cooked_four col_pcA col_pcB (1 / 2) 0 col_h1).
Proof.
  Opaque mint_or_share.
  unfold col_bag1, col_bag, step_hit, col_pcs0, col_h1. simpl. reflexivity.
  Transparent mint_or_share.
Qed.

Lemma col_pick_1 : col_pick col_bag1 = Some col_w2.
Proof.
  Opaque admissible_hit_b support_eqb split_piece.
  rewrite col_bag1_pieces. unfold col_pick, pick_at, col_w2, cooked_four. cbn.
  assert (Ha : admissible_hit_b
            [fst (split_piece col_pcA (1 / 2) col_h1);
             snd (split_piece col_pcA (1 / 2) col_h1);
             fst (split_piece col_pcB 0 col_h1);
             snd (split_piece col_pcB 0 col_h1)]
            (snd (split_piece col_pcA (1 / 2) col_h1))
            (snd (split_piece col_pcB 0 col_h1)) col_P2 1 (1 / 2) = true).
  { Transparent admissible_hit_b split_piece. unfold cooked_four, col_e1, col_e2.
    apply admissible_hit_spec.
    assert (Hadm := col_admissible_2 col_h1).
    rewrite col_pcs1_eq in Hadm. exact Hadm. }
  assert (Hs : support_eqb (bp_support (snd (split_piece col_pcA (1 / 2) col_h1)))
                           (bp_support (snd (split_piece col_pcB 0 col_h1))) = false).
  { Transparent support_eqb split_piece.
    destruct (split_windows_sub col_pcA (1 / 2) col_h1 (proj1 col_wf_A)) as [_ [HA _]].
    destruct (split_windows_sub col_pcB 0 col_h1 (proj1 col_wf_B)) as [_ [HB _]].
    rewrite HA, HB. unfold col_pcA, col_pcB. cbn. exact col_chord_neq. }
  rewrite Ha, Hs. cbn. reflexivity.
  Transparent admissible_hit_b support_eqb split_piece.
Qed.

Lemma col_bag2_len : exists a b c d e f,
  col_bag2 = BagLive default_sheet [a; b; c; d; e; f].
Proof.
  Opaque mint_or_share.
  unfold col_bag2, col_w2, step_hit. rewrite col_bag1_pieces. simpl.
  unfold progress_pieces, cooked_four. rewrite drop_pair_13_four. simpl.
  do 6 eexists. reflexivity.
  Transparent mint_or_share.
Qed.

Lemma col_pick_2 : col_pick col_bag2 = None.
Proof.
  destruct col_bag2_len as [a [b [c [d [e [f Heq]]]]]].
  rewrite Heq. unfold col_pick, pick_at. simpl. reflexivity.
Qed.

Lemma col_P1_vertex_pcs1 : forall h,
  family_vertex (progress_pieces col_pcs0 0%nat 1%nat col_pcA col_pcB (1 / 2) 0 h)
    (SuppChord col_A) col_P1 /\
  family_vertex (progress_pieces col_pcs0 0%nat 1%nat col_pcA col_pcB (1 / 2) 0 h)
    (SuppChord col_B) col_P1.
Proof.
  intro h.
  apply (hit_becomes_vertex col_pcs0 0%nat 1%nat col_pcA col_pcB col_P1 (1 / 2) 0 h);
    try reflexivity; try exact col_wf_A; try exact col_wf_B.
  unfold col_pcA, col_pcB. simpl. exact col_I_ok_1.
Qed.

Definition col_pcs1 : list BagPiece :=
  cooked_four col_pcA col_pcB (1 / 2) 0 col_h1.
Definition col_h2 : Hen := mint_or_share col_pcs1 col_P2.
Definition col_pcs2 : list BagPiece :=
  progress_pieces col_pcs1 1%nat 3%nat col_e1 col_e2 1 (1 / 2) col_h2.

Lemma col_bag2_eq : col_bag2 = BagLive default_sheet col_pcs2.
Proof.
  Opaque mint_or_share.
  unfold col_bag2, col_pcs2, col_h2, col_w2, step_hit, col_pcs1.
  rewrite col_bag1_pieces. simpl. reflexivity.
  Transparent mint_or_share.
Qed.

Lemma col_nths :
  nth_error col_pcs1 1%nat = Some col_e1 /\
  nth_error col_pcs1 3%nat = Some col_e2.
Proof.
  unfold col_pcs1, col_e1, col_e2, cooked_four. split; reflexivity.
Qed.

Lemma col_P2_vertices :
  family_vertex col_pcs2 (SuppChord col_A) col_P2 /\
  family_vertex col_pcs2 (SuppChord col_B) col_P2.
Proof.
  destruct col_nths as [N1 N2].
  apply (hit_becomes_vertex col_pcs1 1%nat 3%nat col_e1 col_e2 col_P2 1 (1 / 2) col_h2);
    try exact N1; try exact N2.
  - apply col_child_wf_hiA.
  - apply col_child_wf_hiB.
  - unfold col_e1, col_e2. exact (col_step2_I_ok col_h1).
Qed.

Lemma col_P1_vertices :
  family_vertex col_pcs2 (SuppChord col_A) col_P1 /\
  family_vertex col_pcs2 (SuppChord col_B) col_P1.
Proof.
  destruct col_nths as [N1 N2].
  destruct (col_P1_vertex_pcs1 col_h1) as [VA VB].
  rewrite col_pcs1_eq in VA, VB. unfold col_pcs1 in VA, VB.
  split.
  - eapply progress_vertices_mono; [exact N1| exact N2| discriminate| exact VA].
  - eapply progress_vertices_mono; [exact N1| exact N2| discriminate| exact VB].
Qed.

Lemma col_overlap_pcs2 :
  overlap_pts col_pcs2 (SuppChord col_A) (SuppChord col_B) = [col_P1; col_P2].
Proof.
  unfold col_pcs2.
  destruct col_nths as [N1 N2].
  rewrite overlap_stable with (i := 1%nat) (j := 3%nat)
      (a := col_e1) (b := col_e2) (ti := 1) (tj := 1 / 2) (h := col_h2).
  - unfold col_pcs1. rewrite <- (col_pcs1_eq col_h1). apply col_overlap_pcs1.
  - exact N1.
  - exact N2.
  - discriminate.
  - exact (proj1 (col_child_wf_hiA col_h1)).
  - exact (proj1 (col_child_wf_hiB col_h1)).
  - lra.
  - lra.
Qed.

Lemma col_keep_false : forall p,
  family_vertex col_pcs2 (SuppChord col_A) p ->
  family_vertex col_pcs2 (SuppChord col_B) p ->
  keep_b col_pcs2 (SuppChord col_A) (SuppChord col_B) p = false.
Proof.
  intros p VA VB. unfold keep_b.
  assert (V : vertex_b col_pcs2 (SuppChord col_A) p &&
              vertex_b col_pcs2 (SuppChord col_B) p = true).
  { apply andb_true_intro. split; apply vertex_spec; assumption. }
  rewrite V.
  destruct (in_image_b col_pcs2 (SuppChord col_A) p &&
            in_image_b col_pcs2 (SuppChord col_B) p); reflexivity.
Qed.

Lemma col_counted_nil :
  counted col_pcs2 (SuppChord col_A) (SuppChord col_B) = [].
Proof.
  unfold counted. rewrite col_canon. simpl.
  unfold raw_pts. rewrite col_same_line. rewrite col_overlap_pcs2.
  assert (K1 : keep_b col_pcs2 (SuppChord col_A) (SuppChord col_B) col_P1 = false).
  { apply col_keep_false; apply col_P1_vertices. }
  assert (K2 : keep_b col_pcs2 (SuppChord col_A) (SuppChord col_B) col_P2 = false).
  { apply col_keep_false; apply col_P2_vertices. }
  simpl. rewrite K1, K2. reflexivity.
Qed.

Lemma col_supports_pcs2 :
  Permutation (supports_of col_pcs2) [SuppChord col_A; SuppChord col_B].
Proof.
  destruct col_nths as [N1 N2].
  assert (H1 : Permutation (supports_of col_pcs1) (supports_of col_pcs0)).
  { unfold col_pcs1.
    apply (supports_progress_perm col_pcs0 0%nat 1%nat col_pcA col_pcB (1 / 2) 0 col_h1);
      try reflexivity; try discriminate.
    - exact (proj1 col_wf_A).
    - exact (proj1 col_wf_B). }
  assert (H2 : Permutation (supports_of col_pcs2) (supports_of col_pcs1)).
  { unfold col_pcs2.
    apply (supports_progress_perm col_pcs1 1%nat 3%nat col_e1 col_e2 1 (1 / 2) col_h2);
      try exact N1; try exact N2; try discriminate.
    - exact (proj1 (col_child_wf_hiA col_h1)).
    - exact (proj1 (col_child_wf_hiB col_h1)). }
  rewrite col_supports in H1. eapply Permutation_trans; eassumption.
Qed.

Lemma col_rho_pcs2 : rho_pcs col_pcs2 = 0%nat.
Proof.
  assert (Hsym : forall x y,
            length (counted col_pcs2 x y) = length (counted col_pcs2 y x)).
  { intros x y. f_equal. apply counted_sym. }
  unfold rho_pcs.
  rewrite (pair_sum_perm (supports_of col_pcs2)
            [SuppChord col_A; SuppChord col_B]
            (fun x y => length (counted col_pcs2 x y))
            col_supports_pcs2 Hsym).
  simpl. rewrite col_counted_nil. reflexivity.
Qed.

Theorem col_two_steps :
  bag_run_steps col_pick (S (rho col_bag)) col_bag = 2%nat /\
  run_stopped col_pick (bag_run col_pick (S (rho col_bag)) col_bag) /\
  rho (bag_run col_pick (S (rho col_bag)) col_bag) = 0%nat.
Proof.
  Opaque col_pick.
  destruct (rho col_bag) as [|k] eqn:Hr.
  - pose proof col_rho_pos as Hpos; rewrite Hr in Hpos; exfalso;
      exact (Nat.nle_succ_0 0 Hpos).
  - assert (Hs0 : bag_run_steps col_pick k col_bag2 = 0%nat).
    { apply steps_none. rewrite col_pick_2. rewrite col_bag2_eq.
      simpl. reflexivity. }
    assert (Hr0 : bag_run col_pick k col_bag2 = col_bag2).
    { apply run_none. rewrite col_pick_2. rewrite col_bag2_eq.
      simpl. reflexivity. }
    cbn [bag_run_steps bag_run]. rewrite col_pick_0.
    cbn [bag_run_steps bag_run].
    replace (step_hit col_bag (mkHitPick 0%nat 1%nat col_P1 (1 / 2) 0))
      with col_bag1 by reflexivity.
    cbn [bag_run_steps bag_run]. rewrite col_pick_1.
    cbn [bag_run_steps bag_run].
    replace (step_hit col_bag1 col_w2) with col_bag2 by reflexivity.
    rewrite Hs0, Hr0. split; [reflexivity|]. split.
    + unfold run_stopped. rewrite col_bag2_eq. simpl. exact col_pick_2.
    + rewrite col_bag2_eq. simpl. exact col_rho_pcs2.
  Transparent col_pick.
Qed.

(* -------------------------------------------------------------------------- *)
(* Tangency of the locked quarter. One step, at the double root.              *)
(* -------------------------------------------------------------------------- *)

Definition tan_pc : BagPiece :=
  mkBagPiece (mkChicken 2%nat 3%nat (MkChord tan_chord))
    (SuppChord tan_chord) unit_win [].
Definition tan_pcs : list BagPiece := [f1_circ_pc; tan_pc].
Definition tan_bag : SheetBag := BagLive default_sheet tan_pcs.

Lemma tan_wf : piece_wf tan_pc.
Proof.
  unfold piece_wf, piece_realizes, tan_pc. cbn.
  split; [|unfold window_ordered, unit_win; cbn; lra].
  symmetry. apply window_chord_unit.
Qed.

Lemma tan_not_circ_vertex :
  ~ family_vertex tan_pcs (SuppCircle F1_egg) tan_pt.
Proof.
  intros [pc [Hin [Hs Hep]]].
  destruct Hin as [<-|[<-|[]]].
  - unfold piece_endpoint, f1_circ_pc in Hep. simpl in Hep.
    assert (E : tan_pt = circ_eval F1_egg (/ 2)).
    { exact (proj2 tan_on_circ_mid). }
    destruct Hep as [Hep|Hep].
    + apply (proj1 f1_mid_not_ends). rewrite <- E. exact Hep.
    + apply (proj2 f1_mid_not_ends). rewrite <- E. exact Hep.
  - discriminate Hs.
Qed.

Lemma tan_admissible :
  admissible_hit tan_pcs f1_circ_pc tan_pc tan_pt (/ 2) (/ 2).
Proof.
  split; [|split].
  - unfold f1_circ_pc, tan_pc. simpl. exact tan_I_ok.
  - intro Hv. apply tan_not_circ_vertex. exact (proj1 Hv).
  - intro Ho. unfold overlap, f1_circ_pc, tan_pc in Ho. simpl in Ho.
    rewrite overlap_b_circ_chord in Ho. discriminate.
Qed.

Lemma tan_supports :
  supports_of tan_pcs = [SuppCircle F1_egg; SuppChord tan_chord].
Proof.
  unfold tan_pcs, supports_of, f1_circ_pc, tan_pc. simpl. reflexivity.
Qed.

Lemma tan_rho_pos : (1 <= rho tan_bag)%nat.
Proof.
  unfold tan_bag, rho. rewrite (rho_two _ _ _ tan_supports).
  assert (Hin : In tan_pt
      (counted tan_pcs (bp_support f1_circ_pc) (bp_support tan_pc))).
  { exact (admissible_in_counted _ _ _ _ _ _
      (in_eq _ _) (in_cons _ _ _ (in_eq _ _))
      f1_circ_wf tan_wf ltac:(discriminate) tan_admissible). }
  replace (counted tan_pcs (SuppCircle F1_egg) (SuppChord tan_chord))
    with (counted tan_pcs (bp_support f1_circ_pc) (bp_support tan_pc))
    by (unfold f1_circ_pc, tan_pc; simpl; reflexivity).
  destruct (counted tan_pcs (bp_support f1_circ_pc) (bp_support tan_pc))
    as [|p tl].
  - destruct Hin.
  - simpl. apply le_n_S. apply Nat.le_0_l.
Qed.

Definition tan_pick : SheetBag -> option HitPick := pick_two tan_pt (/ 2) (/ 2).

Theorem tan_one_step :
  bag_run_steps tan_pick (S (rho tan_bag)) tan_bag = 1%nat /\
  run_stopped tan_pick (bag_run tan_pick (S (rho tan_bag)) tan_bag).
Proof.
  assert (Hs : tan_pick tan_bag = Some (mkHitPick 0%nat 1%nat tan_pt (/ 2) (/ 2))).
  { unfold tan_pick, tan_bag, tan_pcs. apply pick_two_some.
    - exact tan_admissible.
    - discriminate. }
  destruct (one_step_report tan_pick tan_bag
              (mkHitPick 0%nat 1%nat tan_pt (/ 2) (/ 2)) Hs)
    as [Hc [_ Hstop]].
  - unfold tan_pick, tan_bag, tan_pcs.
    exact (pick_two_after default_sheet f1_circ_pc tan_pc tan_pt (/ 2) (/ 2)).
  - exact tan_rho_pos.
  - split; assumption.
Qed.

Theorem tan_step_at_double_root :
  forall t p,
    on_chord tan_chord t p ->
    px p * px p + py p * py p = 25 ->
    t = / 2 /\ p = tan_pt.
Proof.
  exact tan_chord_double_root.
Qed.

(* -------------------------------------------------------------------------- *)
(* Partial co-circular overlap: semicircle and a quarter on the same circle.  *)
(* The shared start is already a vertex. The quarter's end is one step.       *)
(* -------------------------------------------------------------------------- *)

Definition arc_q : CircularEgg := mkCircularEgg (mkPoint 0 0) 5 0 (PI / 2).
Definition arc_P : Point := mkPoint 0 5.
Definition arc_pcS : BagPiece :=
  mkBagPiece (mkChicken 0%nat 1%nat (MkCirc iso_half_fst))
    (SuppCircle iso_half_fst) unit_win [].
Definition arc_pcQ : BagPiece :=
  mkBagPiece (mkChicken 2%nat 3%nat (MkCirc arc_q))
    (SuppCircle arc_q) unit_win [].
Definition arc_pcs : list BagPiece := [arc_pcS; arc_pcQ].
Definition arc_bag : SheetBag := BagLive default_sheet arc_pcs.

Lemma arc_wf_S : piece_wf arc_pcS.
Proof.
  unfold piece_wf, piece_realizes, arc_pcS. cbn.
  split; [|unfold window_ordered, unit_win; cbn; lra].
  symmetry. apply window_circ_unit.
Qed.

Lemma arc_wf_Q : piece_wf arc_pcQ.
Proof.
  unfold piece_wf, piece_realizes, arc_pcQ. cbn.
  split; [|unfold window_ordered, unit_win; cbn; lra].
  symmetry. apply window_circ_unit.
Qed.

Lemma arc_distinct : SuppCircle iso_half_fst <> SuppCircle arc_q.
Proof.
  intro H. inversion H. unfold iso_half_fst, arc_q in H1. inversion H1.
  pose proof PI_RGT_0. lra.
Qed.

Lemma arc_same : same_circle_b iso_half_fst arc_q = true.
Proof.
  unfold same_circle_b, iso_half_fst, arc_q. cbn.
  apply andb_true_intro. split; [apply pt_eqb_true; reflexivity|].
  apply req_b_true. ring.
Qed.

Lemma arc_canon :
  canon2 (SuppCircle iso_half_fst) (SuppCircle arc_q) =
  (SuppCircle arc_q, SuppCircle iso_half_fst).
Proof.
  unfold canon2, support_reals, iso_half_fst, arc_q.
  cbn [px py circ_o circ_r circ_theta0 circ_sweep].
  unfold rlex_le.
  destruct (Req_EM_T 1 1) as [_|N1]; [|congruence].
  destruct (Req_EM_T 0 0) as [_|N0]; [|congruence].
  destruct (Req_EM_T 0 0) as [_|N0b]; [|congruence].
  destruct (Req_EM_T 5 5) as [_|N5]; [|congruence].
  destruct (Req_EM_T 0 0) as [_|N0c]; [|congruence].
  destruct (Req_EM_T PI (PI / 2)) as [Bad|Npi].
  - pose proof PI_RGT_0. lra.
  - destruct (Rle_dec PI (PI / 2)) as [Hle|Hle]; [pose proof PI_RGT_0; lra|].
    reflexivity.
Qed.

Lemma arc_circ_sq : circ_eqb iso_half_fst arc_q = false.
Proof.
  unfold circ_eqb, iso_half_fst, arc_q. cbn.
  rewrite (proj2 (pt_eqb_true _ _) eq_refl).
  assert (E5 : req_b 5 5 = true) by (apply req_b_true; lra).
  assert (E0 : req_b 0 0 = true) by (apply req_b_true; lra).
  assert (Ep : req_b PI (PI / 2) = false)
    by (destruct (req_b PI (PI / 2)) eqn:Eb; [|reflexivity];
        apply req_b_true in Eb; pose proof PI_RGT_0; lra).
  rewrite E5, E0, Ep. reflexivity.
Qed.

Lemma arc_end_S0 : support_at (SuppCircle iso_half_fst) 0 = mkPoint 5 0.
Proof.
  unfold support_at, circ_eval, iso_half_fst. cbn.
  replace (0 + 0 * PI) with 0 by ring.
  rewrite cos_0, sin_0. apply (f_equal2 mkPoint); ring.
Qed.

Lemma arc_end_S1 : support_at (SuppCircle iso_half_fst) 1 = mkPoint (-5) 0.
Proof.
  unfold support_at, circ_eval, iso_half_fst. cbn.
  replace (0 + 1 * PI) with PI by ring.
  rewrite cos_PI, sin_PI. apply (f_equal2 mkPoint); ring.
Qed.

Lemma arc_P_not_S : ~ family_vertex arc_pcs (SuppCircle iso_half_fst) arc_P.
Proof.
  intros [pc [Hin [Hs Hep]]].
  destruct Hin as [<-|[<-|[]]].
  - unfold piece_endpoint, arc_pcS, unit_win in Hep.
    cbn [bp_support bp_window win_lo win_hi] in Hep.
    destruct Hep as [Hep|Hep].
    + rewrite arc_end_S0 in Hep. unfold arc_P in Hep.
      apply (f_equal py) in Hep. cbn in Hep. lra.
    + rewrite arc_end_S1 in Hep. unfold arc_P in Hep.
      apply (f_equal py) in Hep. cbn in Hep. lra.
  - exact (arc_distinct (eq_sym Hs)).
Qed.

Lemma arc_I_ok :
  I_ok (MkCirc iso_half_fst) (MkCirc arc_q) (IHit arc_P (1 / 2) 1).
Proof.
  simpl. split; unfold on_circ; split; try lra.
  - unfold circ_eval, iso_half_fst, arc_P. cbn.
    replace (0 + (1 / 2) * PI) with (PI / 2) by field.
    rewrite cos_PI2, sin_PI2. apply (f_equal2 mkPoint); ring.
  - unfold circ_eval, arc_q, arc_P. cbn.
    replace (0 + 1 * (PI / 2)) with (PI / 2) by field.
    rewrite cos_PI2, sin_PI2. apply (f_equal2 mkPoint); ring.
Qed.

Lemma arc_Q_hi : support_at (SuppCircle arc_q) 1 = arc_P.
Proof.
  unfold support_at, circ_eval, arc_q, arc_P. cbn.
  replace (0 + 1 * (PI / 2)) with (PI / 2) by field.
  rewrite cos_PI2, sin_PI2. apply (f_equal2 mkPoint); ring.
Qed.

Lemma arc_S_mid : support_at (SuppCircle iso_half_fst) (1 / 2) = arc_P.
Proof.
  unfold support_at, circ_eval, iso_half_fst, arc_P. cbn.
  replace (0 + (1 / 2) * PI) with (PI / 2) by field.
  rewrite cos_PI2, sin_PI2. apply (f_equal2 mkPoint); ring.
Qed.

Lemma arc_P_count_Q : count_ends arc_pcs (SuppCircle arc_q) arc_P = 1%nat.
Proof.
  unfold arc_pcs, count_ends. simpl.
  unfold arc_pcS, arc_pcQ. simpl. rewrite arc_circ_sq. simpl.
  rewrite circ_eqb_refl. simpl.
  assert (Eb : endpoint_b
      (mkBagPiece (mkChicken 2%nat 3%nat (MkCirc arc_q))
         (SuppCircle arc_q) unit_win []) arc_P = true).
  { apply endpoint_spec. right. unfold unit_win. cbn [win_hi].
    symmetry. exact arc_Q_hi. }
  rewrite Eb. reflexivity.
Qed.

Lemma arc_P_in_circ :
  In arc_P (circ_overlap_pts arc_pcs iso_half_fst arc_q).
Proof.
  unfold circ_overlap_pts. rewrite dedup_In. apply filter_In. split.
  - apply in_or_app. right. unfold ends_of, arc_pcs. simpl.
    unfold arc_pcS, arc_pcQ. simpl. rewrite arc_circ_sq. simpl.
    rewrite circ_eqb_refl. simpl.
    pose proof arc_Q_hi as Ehi. unfold support_at in Ehi.
    right. left. exact Ehi.
  - unfold circ_end_in_other_b. apply orb_true_intro. right.
    apply andb_true_intro. split.
    + unfold boundary_end_b. apply andb_true_intro. split.
      * apply vertex_spec. exists arc_pcQ. split.
        -- unfold arc_pcs. right. left. reflexivity.
        -- split; [reflexivity|]. right. unfold arc_pcQ, unit_win. cbn [win_hi bp_support bp_window].
           symmetry. exact arc_Q_hi.
      * apply negb_true_iff. unfold joint_b. rewrite arc_P_count_Q. reflexivity.
    + apply in_image_spec. exists arc_pcS. split; [apply in_eq|].
      split; [reflexivity|]. exists (1 / 2). split.
      * unfold arc_pcS, unit_win. simpl. split; lra.
      * unfold arc_pcS, support_at. cbn. symmetry. exact arc_S_mid.
Qed.

Lemma arc_admissible :
  admissible_hit arc_pcs arc_pcS arc_pcQ arc_P (1 / 2) 1.
Proof.
  split; [|split].
  - unfold arc_pcS, arc_pcQ. simpl. exact arc_I_ok.
  - intro Hv. apply arc_P_not_S. exact (proj1 Hv).
  - intros _. unfold overlap_endpoints, arc_pcS, arc_pcQ. simpl.
    rewrite arc_canon. simpl.
    apply (proj2 (circ_overlap_in_sym arc_pcs arc_q iso_half_fst arc_P)).
    exact arc_P_in_circ.
Qed.

Lemma arc_supports :
  supports_of arc_pcs = [SuppCircle iso_half_fst; SuppCircle arc_q].
Proof.
  unfold arc_pcs, supports_of, arc_pcS, arc_pcQ. simpl.
  unfold support_eqb. rewrite arc_circ_sq. reflexivity.
Qed.

Lemma arc_rho_pos : (1 <= rho arc_bag)%nat.
Proof.
  unfold arc_bag, rho. rewrite (rho_two _ _ _ arc_supports).
  assert (Hin : In arc_P
      (counted arc_pcs (bp_support arc_pcS) (bp_support arc_pcQ))).
  { exact (admissible_in_counted _ _ _ _ _ _
      (in_eq _ _) (in_cons _ _ _ (in_eq _ _))
      arc_wf_S arc_wf_Q arc_distinct arc_admissible). }
  replace (counted arc_pcs (SuppCircle iso_half_fst) (SuppCircle arc_q))
    with (counted arc_pcs (bp_support arc_pcS) (bp_support arc_pcQ))
    by (unfold arc_pcS, arc_pcQ; simpl; reflexivity).
  destruct (counted arc_pcs (bp_support arc_pcS) (bp_support arc_pcQ))
    as [|p tl].
  - destruct Hin.
  - simpl. apply le_n_S. apply Nat.le_0_l.
Qed.

Definition arc_pick : SheetBag -> option HitPick := pick_two arc_P (1 / 2) 1.

Theorem arc_partial_steps :
  bag_run_steps arc_pick (S (rho arc_bag)) arc_bag = 1%nat /\
  run_stopped arc_pick (bag_run arc_pick (S (rho arc_bag)) arc_bag).
Proof.
  assert (Hs : arc_pick arc_bag = Some (mkHitPick 0%nat 1%nat arc_P (1 / 2) 1)).
  { unfold arc_pick, arc_bag, arc_pcs. apply pick_two_some.
    - exact arc_admissible.
    - exact arc_distinct. }
  destruct (one_step_report arc_pick arc_bag
              (mkHitPick 0%nat 1%nat arc_P (1 / 2) 1) Hs)
    as [Hc [_ Hstop]].
  - unfold arc_pick, arc_bag, arc_pcs.
    exact (pick_two_after default_sheet arc_pcS arc_pcQ arc_P (1 / 2) 1).
  - exact arc_rho_pos.
  - split; assumption.
Qed.

Print Assumptions steps_none.
Print Assumptions run_none.
Print Assumptions rho_two.
Print Assumptions overlap_stable.
Print Assumptions drop_pair_01_two.
Print Assumptions drop_pair_13_four.
Print Assumptions dedup_two_neq.
Print Assumptions pick_two_some.
Print Assumptions pick_two_after.
Print Assumptions one_step_report.
Print Assumptions f1_admissible.
Print Assumptions f1_supports.
Print Assumptions f1_rho_pos.
Print Assumptions fix_locked_steps.
Print Assumptions halves_zero_steps.
Print Assumptions col_wf_A.
Print Assumptions col_wf_B.
Print Assumptions col_supports_distinct.
Print Assumptions col_same_line.
Print Assumptions col_canon.
Print Assumptions col_key_AA.
Print Assumptions col_key_AB.
Print Assumptions chord_eqb_refl.
Print Assumptions col_chord_neq.
Print Assumptions col_chord_neq_swap.
Print Assumptions col_keys_AA.
Print Assumptions col_keys_AB.
Print Assumptions col_pok.
Print Assumptions col_overlap.
Print Assumptions col_I_ok_1.
Print Assumptions col_P1_not_A.
Print Assumptions col_admissible_1.
Print Assumptions col_supports.
Print Assumptions col_rho_pos.
Print Assumptions col_step2_I_ok.
Print Assumptions col_P2_not_B_child.
Print Assumptions col_P2_not_B_four.
Print Assumptions col_child_wf_hiA.
Print Assumptions col_child_wf_hiB.
Print Assumptions col_pcs1_eq.
Print Assumptions col_overlap_pcs1.
Print Assumptions col_admissible_2.
Print Assumptions col_pick_0.
Print Assumptions col_bag1_pieces.
Print Assumptions col_pick_1.
Print Assumptions col_bag2_len.
Print Assumptions col_pick_2.
Print Assumptions col_P1_vertex_pcs1.
Print Assumptions col_bag2_eq.
Print Assumptions col_nths.
Print Assumptions col_P2_vertices.
Print Assumptions col_P1_vertices.
Print Assumptions col_overlap_pcs2.
Print Assumptions col_keep_false.
Print Assumptions col_counted_nil.
Print Assumptions col_supports_pcs2.
Print Assumptions col_rho_pcs2.
Print Assumptions col_two_steps.
Print Assumptions tan_wf.
Print Assumptions tan_not_circ_vertex.
Print Assumptions tan_admissible.
Print Assumptions tan_supports.
Print Assumptions tan_rho_pos.
Print Assumptions tan_one_step.
Print Assumptions tan_step_at_double_root.
Print Assumptions arc_wf_S.
Print Assumptions arc_wf_Q.
Print Assumptions arc_distinct.
Print Assumptions arc_same.
Print Assumptions arc_canon.
Print Assumptions arc_circ_sq.
Print Assumptions arc_end_S0.
Print Assumptions arc_end_S1.
Print Assumptions arc_P_not_S.
Print Assumptions arc_I_ok.
Print Assumptions arc_Q_hi.
Print Assumptions arc_S_mid.
Print Assumptions arc_P_count_Q.
Print Assumptions arc_P_in_circ.
Print Assumptions arc_admissible.
Print Assumptions arc_supports.
Print Assumptions arc_rho_pos.
Print Assumptions arc_partial_steps.
