(* ============================================================================
   NetTopologySuite.Proofs.SheetHenLoop3
   ----------------------------------------------------------------------------
   ∀-bag letter 5. Concrete pick (least cook ti on the first i<j
   pair) and the three hit-parameter lemmas. Stacked on letter 3.
   letter5_obligation and rho_adm_step_strict stay in SheetHenBagRun.
   Does not remint 0007-loop-letter3-strict.
   Hen is nat: hen_pt walks piece endpoints. hens_injective is
   "same endpoint point implies same hen".
   3-axiom host. No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List PeanoNat Bool ZArith.
From NTS.Proofs Require Import Distance Atan2 SheetHenCook SheetHenBag SheetHenRho
  SheetHenBagRun.
Import ListNotations.
Local Open Scope R_scope.
Local Open Scope list_scope.

Definition overlap_pair (s1 s2 : BagSupport) : bool := overlap_b s1 s2.

Definition hen_at (pcs : list BagPiece) (p : Point) : option Hen :=
  lookup_hen_at pcs p.

Definition admissible (pcs : list BagPiece) (a b : BagPiece) (p : Point)
    (ti tj : R) : Prop :=
  I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck b)) (IHit p ti tj) /\
  progress_hit pcs a b (IHit p ti tj) /\
  (overlap_pair (bp_support a) (bp_support b) = true ->
     In p (overlap_endpoints pcs (bp_support a) (bp_support b))).

Definition adm_step (pcs : list BagPiece) (i j : nat) (a b : BagPiece)
    (p : Point) (ti tj : R) : list BagPiece :=
  progress_pieces pcs i j a b ti tj (mint_or_share pcs p).

Lemma progress_hit_vertex : forall pcs a b p ti tj,
  progress_hit pcs a b (IHit p ti tj) <->
  ~ vertex_of_both pcs (bp_support a) (bp_support b) p.
Proof. intros. unfold progress_hit, vertex_of_both. tauto. Qed.

Lemma admissible_alt : forall pcs a b p ti tj,
  admissible pcs a b p ti tj <-> admissible_hit pcs a b p ti tj.
Proof.
  intros pcs a b p ti tj.
  unfold admissible, admissible_hit, overlap_pair, overlap.
  rewrite progress_hit_vertex. tauto.
Qed.

Lemma admissible_counted : forall pcs a b p ti tj,
  In a pcs -> In b pcs ->
  bp_support a <> bp_support b ->
  piece_wf a -> piece_wf b ->
  admissible pcs a b p ti tj ->
  In p (counted pcs (bp_support a) (bp_support b)).
Proof.
  intros pcs a b p ti tj Ia Ib Hd Ha Hb Hadm.
  exact (admissible_in_counted pcs a b p ti tj Ia Ib Ha Hb Hd
           (proj1 (admissible_alt pcs a b p ti tj) Hadm)).
Qed.

Lemma adm_step_is_bag_step : forall sh pcs i j a b p ti tj,
  nth_error pcs i = Some a ->
  nth_error pcs j = Some b ->
  i <> j ->
  piece_wf a -> piece_wf b ->
  admissible pcs a b p ti tj ->
  bag_step (BagLive sh pcs) (BagLive sh (adm_step pcs i j a b p ti tj)).
Proof.
  intros sh pcs i j a b p ti tj Hi Hj Hij Ha Hb Hadm.
  left. unfold adm_step.
  apply StepProgress with (p := p); try assumption.
  - exact (proj1 Hadm).
  - exact (proj1 (proj2 Hadm)).
Qed.

Lemma adm_step_vertex_both : forall pcs i j a b p ti tj,
  nth_error pcs i = Some a ->
  nth_error pcs j = Some b ->
  piece_wf a -> piece_wf b ->
  admissible pcs a b p ti tj ->
  family_vertex (adm_step pcs i j a b p ti tj) (bp_support a) p /\
  family_vertex (adm_step pcs i j a b p ti tj) (bp_support b) p.
Proof.
  intros pcs i j a b p ti tj Hi Hj Ha Hb Hadm.
  unfold adm_step. apply hit_becomes_vertex; try assumption.
  exact (proj1 Hadm).
Qed.

(* -------------------------------------------------------------------------- *)
(* hen_pt walks endpoints. Hen itself is a nat and has no point field.        *)
(* -------------------------------------------------------------------------- *)

Fixpoint hen_pt (pcs : list BagPiece) (h : Hen) : option Point :=
  match pcs with
  | nil => None
  | pc :: tl =>
      if Nat.eqb (ck_src (bp_ck pc)) h
      then Some (support_at (bp_support pc) (win_lo (bp_window pc)))
      else if Nat.eqb (ck_dst (bp_ck pc)) h
      then Some (support_at (bp_support pc) (win_hi (bp_window pc)))
      else hen_pt tl h
  end.

Definition hens_injective (pcs : list BagPiece) : Prop :=
  forall h1 h2 p,
    (exists pc, In pc pcs /\ hen_sits pc h1 p) ->
    (exists pc, In pc pcs /\ hen_sits pc h2 p) ->
    h1 = h2.

Lemma hens_injective_unique : forall pcs,
  hens_injective pcs <-> hens_unique_by_point pcs.
Proof.
  intros pcs. unfold hens_injective, hens_unique_by_point. split.
  - intros H pc1 pc2 h1 h2 p I1 I2 S1 S2.
    apply (H h1 h2 p); [exists pc1| exists pc2]; split; assumption.
  - intros H h1 h2 p [pc1 [I1 S1]] [pc2 [I2 S2]].
    apply (H pc1 pc2 h1 h2 p); assumption.
Qed.

Lemma hen_pt_sits : forall pcs h p,
  hen_pt pcs h = Some p -> exists pc, In pc pcs /\ hen_sits pc h p.
Proof.
  induction pcs as [|pc tl IH]; intros h p H; simpl in H; [discriminate|].
  destruct (Nat.eqb (ck_src (bp_ck pc)) h) eqn:Hs.
  - apply Nat.eqb_eq in Hs. inversion H. subst p.
    exists pc. split; [left; reflexivity|]. left. split; [exact Hs| reflexivity].
  - destruct (Nat.eqb (ck_dst (bp_ck pc)) h) eqn:Hd.
    + apply Nat.eqb_eq in Hd. inversion H. subst p.
      exists pc. split; [left; reflexivity|]. right. split; [exact Hd| reflexivity].
    + destruct (IH h p H) as [pc' [Hin Hs']].
      exists pc'. split; [right; exact Hin| exact Hs'].
Qed.

Lemma hen_pt_injective : forall pcs h1 h2 p,
  hens_injective pcs ->
  hen_pt pcs h1 = Some p -> hen_pt pcs h2 = Some p -> h1 = h2.
Proof.
  intros pcs h1 h2 p Hi H1 H2.
  apply (Hi h1 h2 p); [apply hen_pt_sits; exact H1| apply hen_pt_sits; exact H2].
Qed.

Lemma adm_step_hens_injective : forall pcs i j a b p ti tj,
  hens_injective pcs ->
  nth_error pcs i = Some a ->
  nth_error pcs j = Some b ->
  piece_wf a -> piece_wf b ->
  admissible pcs a b p ti tj ->
  hens_injective (adm_step pcs i j a b p ti tj).
Proof.
  intros pcs i j a b p ti tj Hi Hni Hnj Ha Hb Hadm.
  apply hens_injective_unique.
  apply hens_injective_unique in Hi.
  unfold adm_step.
  apply mint_or_share_preserves_unique; try assumption.
  exact (proj1 Hadm).
Qed.

(* -------------------------------------------------------------------------- *)
(* Cook parameters. Chords use chord_param. Circles use atan2, folded onto    *)
(* the least nonnegative turn so the value is <= any on-curve parameter.      *)
(* -------------------------------------------------------------------------- *)

Definition cook_t_chord (c : ChordEgg) (p : Point) : R :=
  if req_b (chord_dd c) 0 then 0 else chord_param c p.

Definition circ_ang (c : CircularEgg) (p : Point) : R :=
  let dx := px p - px (circ_o c) in
  let dy := py p - py (circ_o c) in
  if rle_b 0 (circ_r c) then atan2 dy dx else atan2 (- dy) (- dx).

Definition fold_lattice (base ap : R) : R :=
  base + IZR (ceil_Z (- base / ap)) * ap.

Definition cook_t_circ (c : CircularEgg) (p : Point) : R :=
  if orb (req_b (circ_r c) 0) (req_b (circ_sweep c) 0) then 0
  else fold_lattice ((circ_ang c p - circ_theta0 c) / circ_sweep c)
                     (Rabs (2 * PI / circ_sweep c)).

Definition cook_t_egg (e : Egg) (p : Point) : R :=
  match e with
  | MkChord c => cook_t_chord c p
  | MkCirc c => cook_t_circ c p
  | _ => 0
  end.

Lemma cook_chord_le : forall c t p,
  on_chord c t p ->
  cook_t_chord c p <= t /\ on_chord c (cook_t_chord c p) p.
Proof.
  intros c t p [Ht Hp]. unfold cook_t_chord.
  destruct (req_b (chord_dd c) 0) eqn:Hd.
  - apply req_b_true in Hd. split; [apply Ht|].
    split; [split; lra|].
    rewrite (chord_eval_deg c 0 Hd).
    rewrite (chord_eval_deg c t Hd) in Hp. exact Hp.
  - assert (Hnz : chord_dd c <> 0).
    { intro Z. apply req_b_true in Z. rewrite Z in Hd. discriminate. }
    assert (Et : chord_param c p = t).
    { rewrite Hp. apply chord_param_eval. exact Hnz. }
    rewrite Et. split; [lra| split; [exact Ht| exact Hp]].
Qed.

Lemma circ_ang_eval : forall c t,
  circ_r c <> 0 ->
  circ_ang c (circ_eval c t) = reduce_angle (circ_theta0 c + t * circ_sweep c).
Proof.
  intros c t Hr. unfold circ_ang, circ_eval. cbn.
  set (a := circ_theta0 c + t * circ_sweep c).
  replace (py (circ_o c) + circ_r c * sin a - py (circ_o c))
    with (circ_r c * sin a) by ring.
  replace (px (circ_o c) + circ_r c * cos a - px (circ_o c))
    with (circ_r c * cos a) by ring.
  assert (E : (if rle_b 0 (circ_r c)
               then atan2 (circ_r c * sin a) (circ_r c * cos a)
               else atan2 (- (circ_r c * sin a)) (- (circ_r c * cos a)))
              = reduce_angle a).
  { apply atan_reduce. exact Hr. }
  fold a. destruct (rle_b 0 (circ_r c)); exact E.
Qed.

Lemma fold_lattice_spec : forall base ap k,
  ap > 0 ->
  k = ceil_Z (- base / ap) ->
  0 <= base + IZR k * ap < ap.
Proof.
  intros base ap k Hap Hk. subst k.
  destruct (ceil_bounds (- base / ap)) as [Hle Hlt].
  split.
  - apply (Rmult_le_compat_l ap) in Hle; [| lra].
    replace (ap * (- base / ap)) with (- base) in Hle by (field; lra).
    lra.
  - apply (Rmult_lt_compat_l ap) in Hlt; [| lra].
    replace (ap * (- base / ap)) with (- base) in Hlt by (field; lra).
    replace (ap * (- base / ap + 1)) with (- base + ap) in Hlt by (field; lra).
    lra.
Qed.

Lemma fold_lattice_le : forall base ap t m,
  ap > 0 -> 0 <= t ->
  t = base + IZR m * ap ->
  fold_lattice base ap <= t.
Proof.
  intros base ap t m Hap Ht Heq.
  set (k := ceil_Z (- base / ap)).
  pose proof (fold_lattice_spec base ap k Hap eq_refl) as [H0 Hap2].
  unfold fold_lattice. fold k.
  destruct (Rle_or_lt (base + IZR k * ap) t) as [Hle|Hlt]; [exact Hle|].
  exfalso.
  assert (Hd : t - (base + IZR k * ap) = IZR (m - k) * ap).
  { rewrite Heq, minus_IZR. ring. }
  assert (Hneg : t - (base + IZR k * ap) < 0) by lra.
  assert (Hm : IZR (m - k) < 0).
  { apply (Rmult_lt_reg_r ap); [exact Hap|]. rewrite Rmult_0_l. rewrite <- Hd. exact Hneg. }
  assert (Hmz : (m - k < 0)%Z) by (apply lt_IZR; exact Hm).
  assert (HleZ : (m - k <= -1)%Z) by lia.
  assert (Hiz : IZR (m - k) <= -1).
  { apply IZR_le. exact HleZ. }
  assert (Hgap : t - (base + IZR k * ap) <= - ap).
  { rewrite Hd. replace (- ap) with ((-1) * ap) by ring.
    apply Rmult_le_compat_r; lra. }
  assert (Ht0 : t <= (base + IZR k * ap) - ap) by lra.
  assert (Hcook : (base + IZR k * ap) - ap < 0) by lra.
  lra.
Qed.

Lemma cook_circ_le : forall c t p,
  on_circ c t p ->
  cook_t_circ c p <= t /\ on_circ c (cook_t_circ c p) p.
Proof.
  intros c t p [Ht Hp]. unfold cook_t_circ.
  destruct (orb (req_b (circ_r c) 0) (req_b (circ_sweep c) 0)) eqn:Ez.
  - apply orb_true_iff in Ez. split; [apply Ht|].
    destruct Ez as [Er|Es].
    + apply req_b_true in Er. split; [split; lra|].
      rewrite Hp. unfold circ_eval. rewrite Er. apply pt_eq_coords; cbn; ring.
    + apply req_b_true in Es. split; [split; lra|].
      rewrite Hp. unfold circ_eval. rewrite Es.
      replace (t * 0) with 0 by ring. replace (0 * 0) with 0 by ring.
      apply pt_eq_coords; cbn; ring.
  - apply orb_false_iff in Ez. destruct Ez as [Er Es].
    assert (Hr : circ_r c <> 0).
    { intro Z. apply req_b_true in Z. rewrite Z in Er. discriminate. }
    assert (Hs : circ_sweep c <> 0).
    { intro Z. apply req_b_true in Z. rewrite Z in Es. discriminate. }
    set (ap := Rabs (2 * PI / circ_sweep c)).
    assert (Hap : ap > 0).
    { unfold ap. apply Rabs_pos_lt.
      intro Z. apply (Rmult_eq_compat_r (circ_sweep c)) in Z.
      replace ((2 * PI / circ_sweep c) * circ_sweep c) with (2 * PI) in Z
        by (field; exact Hs).
      rewrite Rmult_0_l in Z. pose proof PI_RGT_0. lra. }
    set (base := (circ_ang c p - circ_theta0 c) / circ_sweep c).
    assert (Hang : circ_ang c p = reduce_angle (circ_theta0 c + t * circ_sweep c)).
    { rewrite Hp. apply circ_ang_eval. exact Hr. }
    destruct (reduce_angle_period (circ_theta0 c + t * circ_sweep c)) as [n Hn].
    assert (Htbase : t = base + IZR n * (2 * PI / circ_sweep c)).
    { unfold base. rewrite Hang.
      assert (Hsw : t * circ_sweep c =
                    reduce_angle (circ_theta0 c + t * circ_sweep c) - circ_theta0 c
                    + 2 * PI * IZR n).
      { assert (E : circ_theta0 c + t * circ_sweep c =
                    reduce_angle (circ_theta0 c + t * circ_sweep c) + 2 * PI * IZR n)
          by exact Hn.
        lra. }
      apply (Rmult_eq_reg_r (circ_sweep c)); [| exact Hs].
      replace (((reduce_angle (circ_theta0 c + t * circ_sweep c) - circ_theta0 c)
                / circ_sweep c + IZR n * (2 * PI / circ_sweep c)) * circ_sweep c)
        with (reduce_angle (circ_theta0 c + t * circ_sweep c) - circ_theta0 c
              + 2 * PI * IZR n) by (field; exact Hs).
      exact Hsw. }
    assert (Hlat : exists m, t = base + IZR m * ap).
    { destruct (Rle_dec 0 (circ_sweep c)) as [Hpos|Hneg].
      - assert (Hswp : 0 < circ_sweep c) by lra.
        assert (Eap : ap = 2 * PI / circ_sweep c).
        { unfold ap. rewrite Rabs_pos_eq; [reflexivity|].
          apply Rmult_le_pos; [| apply Rlt_le; apply Rinv_0_lt_compat; exact Hswp].
          pose proof PI_RGT_0. lra. }
        exists n. rewrite <- Eap in Htbase. exact Htbase.
      - assert (Hswm : circ_sweep c < 0) by (apply Rnot_le_lt; exact Hneg).
        assert (Eap : ap = - (2 * PI / circ_sweep c)).
        { unfold ap. rewrite Rabs_left; [reflexivity|].
          assert (2 * PI / circ_sweep c < 0).
          { pose proof PI_RGT_0 as Hpi.
            assert (Hpos : 0 < 2 * PI) by lra.
            unfold Rdiv.
            replace (/ circ_sweep c) with (- / - circ_sweep c) by (field; lra).
            replace (2 * PI * (- / - circ_sweep c))
              with (- (2 * PI * / - circ_sweep c)) by ring.
            apply Ropp_0_lt_gt_contravar.
            apply Rmult_lt_0_compat; [exact Hpos|].
            apply Rinv_0_lt_compat. lra. }
          exact H. }
        exists (- n)%Z. rewrite opp_IZR, Eap. rewrite Htbase. ring. }
    destruct Hlat as [m Hm].
    assert (Hle : fold_lattice base ap <= t).
    { apply (fold_lattice_le base ap t m Hap (proj1 Ht) Hm). }
    split.
    + exact Hle.
    + split.
      * pose proof (fold_lattice_spec base ap (ceil_Z (- base / ap)) Hap eq_refl) as [Hz _].
        split; [exact Hz|].
        apply Rle_trans with t; [exact Hle| exact (proj2 Ht)].
      * rewrite Hp.
        assert (Hdiff : t = fold_lattice base ap + IZR (m - ceil_Z (- base / ap)) * ap).
        { rewrite Hm. unfold fold_lattice. rewrite minus_IZR. ring. }
        rewrite Hdiff.
        replace (IZR (m - ceil_Z (- base / ap)) * ap)
          with (IZR (m - ceil_Z (- base / ap)) * (2 * PI / Rabs (circ_sweep c))).
        { apply circ_eval_abs_shift. exact Hs. }
        unfold ap, Rdiv. rewrite Rabs_mult, Rabs_inv.
        rewrite (Rabs_pos_eq (2 * PI)); [| pose proof PI_RGT_0; lra].
        reflexivity.
Qed.

Lemma I_ok_at_cook : forall e1 e2 p ti tj,
  match e1, e2 with
  | MkChord _, MkChord _ | MkChord _, MkCirc _
  | MkCirc _, MkChord _ | MkCirc _, MkCirc _ => True
  | _, _ => False
  end ->
  I_ok e1 e2 (IHit p ti tj) ->
  I_ok e1 e2 (IHit p (cook_t_egg e1 p) (cook_t_egg e2 p)).
Proof.
  intros e1 e2 p ti tj Hcl H.
  destruct e1 as [c1|c1|c1|cl|nu]; destruct e2 as [c2|c2|c2|cl2|nu2];
    simpl in Hcl, H; try contradiction; simpl.
  - destruct (cook_chord_le c1 ti p (proj1 H)) as [_ H1].
    destruct (cook_chord_le c2 tj p (proj2 H)) as [_ H2].
    split; assumption.
  - destruct H as [Hs [H1 H2]].
    destruct (cook_chord_le c1 ti p H1) as [_ G1].
    destruct (cook_circ_le c2 tj p H2) as [_ G2].
    split; [exact Hs| split; assumption].
  - destruct H as [Hs [H1 H2]].
    destruct (cook_circ_le c1 ti p H1) as [_ G1].
    destruct (cook_chord_le c2 tj p H2) as [_ G2].
    split; [exact Hs| split; assumption].
  - destruct (cook_circ_le c1 ti p (proj1 H)) as [_ H1].
    destruct (cook_circ_le c2 tj p (proj2 H)) as [_ H2].
    split; assumption.
Qed.

Lemma admissible_at_cook : forall pcs a b p ti tj,
  match ck_egg (bp_ck a), ck_egg (bp_ck b) with
  | MkChord _, MkChord _ | MkChord _, MkCirc _
  | MkCirc _, MkChord _ | MkCirc _, MkCirc _ => True
  | _, _ => False
  end ->
  admissible pcs a b p ti tj ->
  admissible pcs a b p (cook_t_egg (ck_egg (bp_ck a)) p)
                         (cook_t_egg (ck_egg (bp_ck b)) p) /\
  cook_t_egg (ck_egg (bp_ck a)) p <= ti.
Proof.
  intros pcs a b p ti tj Hcl [Hok [Hpr Hov]].
  assert (Hon : match ck_egg (bp_ck a) with
                | MkChord c => on_chord c ti p
                | MkCirc c => on_circ c ti p
                | _ => False
                end).
  { destruct (ck_egg (bp_ck a)) as [c|c|c|cl|nu];
      destruct (ck_egg (bp_ck b)) as [c2|c2|c2|cl2|nu2];
      simpl in Hok, Hcl; try contradiction.
    - exact (proj1 Hok).
    - exact (proj1 (proj2 Hok)).
    - exact (proj1 (proj2 Hok)).
    - exact (proj1 Hok). }
  assert (Hle : cook_t_egg (ck_egg (bp_ck a)) p <= ti).
  { destruct (ck_egg (bp_ck a)) as [c|c|c|cl|nu]; simpl in Hon; try contradiction; simpl.
    - exact (proj1 (cook_chord_le c ti p Hon)).
    - exact (proj1 (cook_circ_le c ti p Hon)). }
  split; [| exact Hle].
  split; [| split].
  - apply (I_ok_at_cook _ _ p ti tj); assumption.
  - unfold progress_hit in Hpr. exact Hpr.
  - exact Hov.
Qed.

(* -------------------------------------------------------------------------- *)
(* Per-class hit parameters. Existence from the window; circle×circle also    *)
(* lands on the radical line when the centres differ.                         *)
(* -------------------------------------------------------------------------- *)

Definition unit_param (w : Window) (t : R) : R :=
  if req_b (win_hi w) (win_lo w) then 0 else (t - win_lo w) / (win_hi w - win_lo w).

Lemma unit_param_spec : forall w t,
  window_ordered w -> win_lo w <= t <= win_hi w ->
  0 <= unit_param w t <= 1 /\ win_abs w (unit_param w t) = t.
Proof.
  intros w t Ho Ht. unfold unit_param, win_abs.
  destruct (req_b (win_hi w) (win_lo w)) eqn:E.
  - apply req_b_true in E. destruct Ht as [H1 H2]. split; [lra|].
    rewrite E. ring_simplify. lra.
  - assert (Hne : win_hi w <> win_lo w).
    { intro Z. apply req_b_true in Z. rewrite Z in E. discriminate. }
    assert (Hd : win_hi w - win_lo w <> 0) by lra.
    split.
    + split.
      * apply (Rmult_le_reg_r (win_hi w - win_lo w)); [lra|].
        unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_0_l; [| exact Hd].
        lra.
      * apply (Rmult_le_reg_r (win_hi w - win_lo w)); [lra|].
        unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_1_l; [| exact Hd].
        lra.
    + unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r; [| exact Hd]. ring.
Qed.

Lemma piece_param_on : forall pc p u,
  piece_realizes pc -> 0 <= u <= 1 ->
  p = support_at (bp_support pc) (win_abs (bp_window pc) u) ->
  match ck_egg (bp_ck pc) with
  | MkChord e => on_chord e u p
  | MkCirc e => on_circ e u p
  | _ => False
  end.
Proof.
  intros pc p u Hr Hu Hp.
  destruct pc as [[src dst egg] sup w prov].
  unfold piece_realizes in Hr. simpl in Hr.
  destruct sup as [c|c]; destruct egg as [e|e|e|e|e]; simpl in Hr; try contradiction.
  - rewrite Hr. simpl in Hp. simpl. split; [exact Hu|].
    rewrite Hp. rewrite <- (chord_window_eval c w u). reflexivity.
  - rewrite Hr. simpl in Hp. simpl. split; [exact Hu|].
    rewrite Hp. rewrite <- (circ_window_eval c w u). reflexivity.
Qed.

Lemma hit_param_line_line : forall a b p,
  piece_wf a -> piece_wf b ->
  window_pts (bp_support a) (bp_window a) p ->
  window_pts (bp_support b) (bp_window b) p ->
  (exists ca, bp_support a = SuppChord ca) ->
  (exists cb, bp_support b = SuppChord cb) ->
  exists ti tj, I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck b)) (IHit p ti tj).
Proof.
  intros a b p [Hra Hoa] [Hrb Hob] [ta [Ha1 Ha2]] [tb [Hb1 Hb2]] [ca Ea] [cb Eb].
  destruct (unit_param_spec (bp_window a) ta Hoa Ha1) as [Hua Ea2].
  destruct (unit_param_spec (bp_window b) tb Hob Hb1) as [Hub Eb2].
  exists (unit_param (bp_window a) ta), (unit_param (bp_window b) tb).
  assert (Pa : match ck_egg (bp_ck a) with
               | MkChord e => on_chord e (unit_param (bp_window a) ta) p
               | MkCirc e => on_circ e (unit_param (bp_window a) ta) p
               | _ => False end).
  { apply piece_param_on; [exact Hra| exact Hua|]. rewrite Ea2. exact Ha2. }
  assert (Pb : match ck_egg (bp_ck b) with
               | MkChord e => on_chord e (unit_param (bp_window b) tb) p
               | MkCirc e => on_circ e (unit_param (bp_window b) tb) p
               | _ => False end).
  { apply piece_param_on; [exact Hrb| exact Hub|]. rewrite Eb2. exact Hb2. }
  destruct a as [[sa da ea] supa wa pa].
  destruct b as [[sb db eb] supb wb pb].
  simpl in Pa, Pb, Ea, Eb. destruct supa as [ca'|ca']; [| discriminate].
  destruct supb as [cb'|cb']; [| discriminate].
  destruct ea as [ea|ea|ea|ea|ea]; try contradiction.
  destruct eb as [eb|eb|eb|eb|eb]; try contradiction.
  simpl. split; assumption.
Qed.

Lemma hit_param_line_circle : forall a b p,
  piece_wf a -> piece_wf b ->
  window_pts (bp_support a) (bp_window a) p ->
  window_pts (bp_support b) (bp_window b) p ->
  match ck_egg (bp_ck a), ck_egg (bp_ck b) with
  | MkCirc c, MkChord s => circ_chord_host_scope c s
  | MkChord s, MkCirc c => circ_chord_host_scope c s
  | _, _ => False
  end ->
  exists ti tj, I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck b)) (IHit p ti tj).
Proof.
  intros a b p [Hra Hoa] [Hrb Hob] [ta [Ha1 Ha2]] [tb [Hb1 Hb2]] Hscope.
  destruct (unit_param_spec _ ta Hoa Ha1) as [Hua Ea].
  destruct (unit_param_spec _ tb Hob Hb1) as [Hub Eb].
  exists (unit_param (bp_window a) ta), (unit_param (bp_window b) tb).
  assert (Pa : match ck_egg (bp_ck a) with
               | MkChord e => on_chord e (unit_param (bp_window a) ta) p
               | MkCirc e => on_circ e (unit_param (bp_window a) ta) p
               | _ => False end).
  { apply piece_param_on; [exact Hra| exact Hua|]. rewrite Ea. exact Ha2. }
  assert (Pb : match ck_egg (bp_ck b) with
               | MkChord e => on_chord e (unit_param (bp_window b) tb) p
               | MkCirc e => on_circ e (unit_param (bp_window b) tb) p
               | _ => False end).
  { apply piece_param_on; [exact Hrb| exact Hub|]. rewrite Eb. exact Hb2. }
  destruct (ck_egg (bp_ck a)) as [ca|ca|ca|cla|na];
    destruct (ck_egg (bp_ck b)) as [cb|cb|cb|clb|nb];
    simpl in Pa, Pb, Hscope; try contradiction.
  - split; [exact Hscope| split; assumption].
  - split; [exact Hscope| split; assumption].
Qed.

Lemma hit_param_circle_circle : forall a b p ca cb,
  piece_wf a -> piece_wf b ->
  bp_support a = SuppCircle ca ->
  bp_support b = SuppCircle cb ->
  window_pts (SuppCircle ca) (bp_window a) p ->
  window_pts (SuppCircle cb) (bp_window b) p ->
  exists ti tj,
    I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck b)) (IHit p ti tj) /\
    (0 < dist (circ_o ca) (circ_o cb) ->
       p = radical_point_plus (circ_o ca) (circ_o cb) (circ_r ca) (circ_r cb) \/
       p = radical_point_minus (circ_o ca) (circ_o cb) (circ_r ca) (circ_r cb)).
Proof.
  intros a b p ca cb [Hra Hoa] [Hrb Hob] Ea Eb [ta [Ha1 Ha2]] [tb [Hb1 Hb2]].
  destruct (unit_param_spec _ ta Hoa Ha1) as [Hua Eua].
  destruct (unit_param_spec _ tb Hob Hb1) as [Hub Eub].
  exists (unit_param (bp_window a) ta), (unit_param (bp_window b) tb).
  assert (Pa : match ck_egg (bp_ck a) with
               | MkChord e => on_chord e (unit_param (bp_window a) ta) p
               | MkCirc e => on_circ e (unit_param (bp_window a) ta) p
               | _ => False end).
  { apply piece_param_on; [exact Hra| exact Hua|].
    rewrite Eua, Ea. exact Ha2. }
  assert (Pb : match ck_egg (bp_ck b) with
               | MkChord e => on_chord e (unit_param (bp_window b) tb) p
               | MkCirc e => on_circ e (unit_param (bp_window b) tb) p
               | _ => False end).
  { apply piece_param_on; [exact Hrb| exact Hub|].
    rewrite Eub, Eb. exact Hb2. }
  assert (Hega : exists ea, ck_egg (bp_ck a) = MkCirc ea /\
                          on_circ ea (unit_param (bp_window a) ta) p).
  { unfold piece_realizes in Hra. rewrite Ea in Hra. simpl in Hra.
    destruct (ck_egg (bp_ck a)) as [e|e|e|e|e] eqn:Eg;
      try (solve [destruct Hra]).
    exists e. split; [reflexivity|]. exact Pa. }
  assert (Hegb : exists eb, ck_egg (bp_ck b) = MkCirc eb /\
                          on_circ eb (unit_param (bp_window b) tb) p).
  { unfold piece_realizes in Hrb. rewrite Eb in Hrb. simpl in Hrb.
    destruct (ck_egg (bp_ck b)) as [e|e|e|e|e] eqn:Eg;
      try (solve [destruct Hrb]).
    exists e. split; [reflexivity|]. exact Pb. }
  destruct Hega as [ea [Ega Haok]].
  destruct Hegb as [eb [Egb Hbok]].
  split.
  - rewrite Ega, Egb. simpl. split; assumption.
  - intro Hd.
    assert (Ca : on_circle_carrier ca p).
    { rewrite Ha2. apply circ_eval_carrier. }
    assert (Cb : on_circle_carrier cb p).
    { rewrite Hb2. apply circ_eval_carrier. }
    unfold on_circle_carrier in Ca, Cb.
    apply two_circles_radical_point_unique; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* adm_list, least ti, and the index-order pick. Same-support pairs are       *)
(* skipped: ρ sums distinct supports, so a same-support step is not the       *)
(* strict measure this fuel uses.                                              *)
(* -------------------------------------------------------------------------- *)

Record HitCand : Type := mkHitCand { hc_p : Point; hc_ti : R; hc_tj : R }.

Fixpoint cands_of (pcs : list BagPiece) (a b : BagPiece) (ps : list Point)
  : list HitCand :=
  match ps with
  | nil => nil
  | q :: tl =>
      let ti := cook_t_egg (ck_egg (bp_ck a)) q in
      let tj := cook_t_egg (ck_egg (bp_ck b)) q in
      if admissible_hit_b pcs a b q ti tj
      then mkHitCand q ti tj :: cands_of pcs a b tl
      else cands_of pcs a b tl
  end.

Definition adm_list (pcs : list BagPiece) (a b : BagPiece) : list HitCand :=
  cands_of pcs a b (counted pcs (bp_support a) (bp_support b)).

Fixpoint least_ti (cs : list HitCand) : option HitCand :=
  match cs with
  | nil => None
  | c :: tl =>
      match least_ti tl with
      | None => Some c
      | Some d => if rle_b (hc_ti c) (hc_ti d) then Some c else Some d
      end
  end.

Lemma cands_cook : forall pcs a b ps c,
  In c (cands_of pcs a b ps) ->
  hc_ti c = cook_t_egg (ck_egg (bp_ck a)) (hc_p c) /\
  hc_tj c = cook_t_egg (ck_egg (bp_ck b)) (hc_p c).
Proof.
  intros pcs a b ps. induction ps as [|q tl IH]; intros c Hin; simpl in Hin.
  - contradiction.
  - destruct (admissible_hit_b pcs a b q
               (cook_t_egg (ck_egg (bp_ck a)) q)
               (cook_t_egg (ck_egg (bp_ck b)) q)) eqn:Eb.
    + destruct Hin as [<-|Hin]; [simpl; split; reflexivity| apply IH; exact Hin].
    + apply IH. exact Hin.
Qed.

Lemma cands_admissible : forall pcs a b ps c,
  In c (cands_of pcs a b ps) ->
  admissible_hit pcs a b (hc_p c) (hc_ti c) (hc_tj c).
Proof.
  intros pcs a b ps. induction ps as [|q tl IH]; intros c Hin; simpl in Hin.
  - contradiction.
  - destruct (admissible_hit_b pcs a b q
               (cook_t_egg (ck_egg (bp_ck a)) q)
               (cook_t_egg (ck_egg (bp_ck b)) q)) eqn:Eb.
    + destruct Hin as [<-|Hin].
      * apply admissible_hit_spec. simpl. exact Eb.
      * apply IH. exact Hin.
    + apply IH. exact Hin.
Qed.

Lemma adm_list_admissible : forall pcs a b c,
  In c (adm_list pcs a b) ->
  admissible_hit pcs a b (hc_p c) (hc_ti c) (hc_tj c).
Proof.
  intros pcs a b c H. unfold adm_list in H.
  exact (cands_admissible pcs a b
           (counted pcs (bp_support a) (bp_support b)) c H).
Qed.

Lemma cands_in : forall pcs a b ps p,
  In p ps ->
  admissible_hit_b pcs a b p (cook_t_egg (ck_egg (bp_ck a)) p)
                              (cook_t_egg (ck_egg (bp_ck b)) p) = true ->
  In (mkHitCand p (cook_t_egg (ck_egg (bp_ck a)) p)
                 (cook_t_egg (ck_egg (bp_ck b)) p)) (cands_of pcs a b ps).
Proof.
  intros pcs a b ps p. induction ps as [|q tl IH]; intros Hin Hb; simpl in Hin.
  - contradiction.
  - simpl. destruct Hin as [->|Hin].
    + rewrite Hb. left. reflexivity.
    + destruct (admissible_hit_b pcs a b q _ _) eqn:Eb; [right|]; apply IH; assumption.
Qed.

Lemma least_in : forall cs c, least_ti cs = Some c -> In c cs.
Proof.
  induction cs as [|d tl IH]; intros c H; simpl in H; [discriminate|].
  destruct (least_ti tl) as [e|] eqn:El.
  - destruct (rle_b (hc_ti d) (hc_ti e)) eqn:Er; inversion H; subst.
    + left. reflexivity.
    + right. apply IH. reflexivity.
  - inversion H. left. reflexivity.
Qed.

Lemma rle_b_false_iff : forall x y, rle_b x y = false <-> ~ x <= y.
Proof.
  intros x y. unfold rle_b. destruct (Rle_dec x y) as [E|N]; simpl; split; intro H.
  - discriminate.
  - contradiction.
  - exact N.
  - reflexivity.
Qed.

Lemma least_le : forall cs c d,
  least_ti cs = Some c -> In d cs -> hc_ti c <= hc_ti d.
Proof.
  induction cs as [|e tl IH]; intros c d H Hin; simpl in Hin; [contradiction|].
  simpl in H. destruct (least_ti tl) as [f|] eqn:El.
  - destruct (rle_b (hc_ti e) (hc_ti f)) eqn:Er; inversion H; subst.
    + destruct Hin as [->|Hin]; [lra|].
      apply rle_b_true in Er.
      apply Rle_trans with (hc_ti f); [exact Er|].
      apply IH; [reflexivity| exact Hin].
    + destruct Hin as [->|Hin].
      * apply rle_b_false_iff in Er. lra.
      * apply IH; [reflexivity| exact Hin].
  - inversion H; subst. destruct Hin as [->|Hin]; [lra|].
    destruct tl as [|q qs]; [contradiction|].
    assert (He : exists r, least_ti (q :: qs) = Some r).
    { simpl. destruct (least_ti qs) as [r|].
      - destruct (rle_b (hc_ti q) (hc_ti r)); [exists q| exists r]; reflexivity.
      - exists q. reflexivity. }
    destruct He as [r Hr]. rewrite Hr in El. discriminate El.
Qed.

Lemma chord_eqb_spec_ok : forall a b, chord_eqb a b = true <-> a = b.
Proof.
  destruct a as [p0 p1], b as [q0 q1]. unfold chord_eqb. simpl.
  rewrite andb_true_iff, !pt_eqb_true. split.
  - intros [-> ->]. reflexivity.
  - intro E. inversion E. split; reflexivity.
Qed.

Lemma circ_eqb_spec_ok : forall a b, circ_eqb a b = true <-> a = b.
Proof.
  destruct a as [o1 r1 t1 s1], b as [o2 r2 t2 s2]. unfold circ_eqb. simpl.
  rewrite !andb_true_iff, pt_eqb_true, !req_b_true. split.
  - intros [[[-> ->] ->] ->]. reflexivity.
  - intro E. inversion E. repeat split; reflexivity.
Qed.

Definition piece_wf_b (pc : BagPiece) : bool :=
  match bp_support pc, ck_egg (bp_ck pc) with
  | SuppChord c, MkChord e =>
      chord_eqb e (window_chord c (bp_window pc)) &&
      rle_b (win_lo (bp_window pc)) (win_hi (bp_window pc))
  | SuppCircle c, MkCirc e =>
      circ_eqb e (window_circ c (bp_window pc)) &&
      rle_b (win_lo (bp_window pc)) (win_hi (bp_window pc))
  | _, _ => false
  end.

Lemma piece_wf_b_spec : forall pc, piece_wf_b pc = true <-> piece_wf pc.
Proof.
  intros [[src dst egg] sup w prov].
  unfold piece_wf_b, piece_wf, piece_realizes. simpl.
  destruct sup as [c|c]; destruct egg as [e|e|e|e|e]; simpl; split; intro H.
  all: try discriminate.
  all: try (solve [destruct H as [F _]; destruct F]).
  - apply andb_prop in H. destruct H as [He Ho].
    apply chord_eqb_spec_ok in He. apply rle_b_true in Ho. split; assumption.
  - destruct H as [Hr Ho]. apply andb_true_intro. split.
    + apply chord_eqb_spec_ok. exact Hr.
    + apply rle_b_true. exact Ho.
  - apply andb_prop in H. destruct H as [He Ho].
    apply circ_eqb_spec_ok in He. apply rle_b_true in Ho. split; assumption.
  - destruct H as [Hr Ho]. apply andb_true_intro. split.
    + apply circ_eqb_spec_ok. exact Hr.
    + apply rle_b_true. exact Ho.
Qed.

Definition pair_ok (a b : BagPiece) : bool :=
  piece_wf_b a && piece_wf_b b &&
  negb (support_eqb (bp_support a) (bp_support b)).

Lemma pair_ok_spec : forall a b, pair_ok a b = true ->
  piece_wf a /\ piece_wf b /\ bp_support a <> bp_support b.
Proof.
  intros a b H. unfold pair_ok in H.
  apply andb_prop in H. destruct H as [Hw Hs].
  apply andb_prop in Hw. destruct Hw as [Ha Hb].
  apply negb_true_iff in Hs.
  split; [| split].
  - apply piece_wf_b_spec. exact Ha.
  - apply piece_wf_b_spec. exact Hb.
  - intro E. apply support_eqb_true in E. rewrite E in Hs. discriminate.
Qed.

Fixpoint scan_j (pcs : list BagPiece) (i j fuel : nat)
  : option (nat * nat * (Point * R * R)) :=
  match fuel with
  | O => None
  | S fuel' =>
      match nth_error pcs i, nth_error pcs j with
      | Some a, Some b =>
          if pair_ok a b then
            match least_ti (adm_list pcs a b) with
            | Some c => Some (i, j, (hc_p c, hc_ti c, hc_tj c))
            | None => scan_j pcs i (S j) fuel'
            end
          else scan_j pcs i (S j) fuel'
      | _, _ => None
      end
  end.

Fixpoint scan_i (pcs : list BagPiece) (i fuel : nat)
  : option (nat * nat * (Point * R * R)) :=
  match fuel with
  | O => None
  | S fuel' =>
      match scan_j pcs i (S i) (S (length pcs)) with
      | Some ans => Some ans
      | None => scan_i pcs (S i) fuel'
      end
  end.

Definition pick (pcs : list BagPiece) : option (nat * nat * (Point * R * R)) :=
  scan_i pcs 0%nat (S (length pcs)).

Lemma scan_j_sound : forall fuel pcs i j,
  (i < j)%nat ->
  forall i' j' p ti tj,
    scan_j pcs i j fuel = Some (i', j', (p, ti, tj)) ->
    i' = i /\ (i < j')%nat /\
    exists a b,
      nth_error pcs i = Some a /\
      nth_error pcs j' = Some b /\
      piece_wf a /\ piece_wf b /\
      bp_support a <> bp_support b /\
      least_ti (adm_list pcs a b) = Some (mkHitCand p ti tj) /\
      admissible pcs a b p ti tj.
Proof.
  induction fuel as [|fuel IH]; intros pcs i j Hij i' j' p ti tj H; simpl in H.
  - discriminate.
  - destruct (nth_error pcs i) as [a|] eqn:Hi; [| discriminate].
    destruct (nth_error pcs j) as [b|] eqn:Hj; [| discriminate].
    destruct (pair_ok a b) eqn:Eok.
    + destruct (least_ti (adm_list pcs a b)) as [[cp cti ctj]|] eqn:El.
      * simpl in H. inversion H; subst i' j' p ti tj. clear H.
        destruct (pair_ok_spec a b Eok) as [Ha [Hb Hd]].
        split; [reflexivity|]. split; [exact Hij|].
        exists a, b. split; [reflexivity|]. split; [exact Hj|].
        split; [exact Ha|]. split; [exact Hb|]. split; [exact Hd|].
        split; [exact El|].
        apply admissible_alt.
        pose proof (adm_list_admissible pcs a b (mkHitCand cp cti ctj)) as Had.
        simpl in Had. apply Had. apply least_in. exact El.
      * destruct (IH pcs i (S j) (Nat.lt_lt_succ_r _ _ Hij) i' j' p ti tj H)
          as [Ei [Hj' Hex]].
        split; [exact Ei|]. split; [exact Hj'|]. rewrite <- Hi. exact Hex.
    + destruct (IH pcs i (S j) (Nat.lt_lt_succ_r _ _ Hij) i' j' p ti tj H)
        as [Ei [Hj' Hex]].
      split; [exact Ei|]. split; [exact Hj'|]. rewrite <- Hi. exact Hex.
Qed.

Lemma scan_i_sound : forall fuel pcs i i' j p ti tj,
  scan_i pcs i fuel = Some (i', j, (p, ti, tj)) ->
  exists a b,
    nth_error pcs i' = Some a /\
    nth_error pcs j = Some b /\
    (i' < j)%nat /\
    piece_wf a /\ piece_wf b /\
    bp_support a <> bp_support b /\
    least_ti (adm_list pcs a b) = Some (mkHitCand p ti tj) /\
    admissible pcs a b p ti tj.
Proof.
  induction fuel as [|fuel IH]; intros pcs i i' j p ti tj H; cbn [scan_i] in H.
  - discriminate.
  - destruct (scan_j pcs i (S i) (S (length pcs)))
      as [[[i0 j0] [[q u] v]]|] eqn:Ej.
    + injection H as E. inversion E. subst.
      destruct (scan_j_sound (S (length pcs)) pcs i (S i) (Nat.lt_succ_diag_r i)
                  i' j p ti tj Ej) as [Ei [Hij Hex]].
      destruct Hex as [a [b [Ha [Hb [Hwf1 [Hwf2 [Hd [Hel Hadm]]]]]]]].
      rewrite Ei.
      exists a, b. split; [exact Ha|]. split; [exact Hb|]. split; [exact Hij|].
      split; [exact Hwf1|]. split; [exact Hwf2|]. split; [exact Hd|].
      split; [exact Hel|]. exact Hadm.
    + apply (IH pcs (S i) i' j p ti tj H).
Qed.

Lemma pick_sound : forall pcs i j p ti tj,
  pick pcs = Some (i, j, (p, ti, tj)) ->
  exists a b,
    nth_error pcs i = Some a /\
    nth_error pcs j = Some b /\
    i <> j /\
    piece_wf a /\ piece_wf b /\
    bp_support a <> bp_support b /\
    least_ti (adm_list pcs a b) = Some (mkHitCand p ti tj) /\
    admissible pcs a b p ti tj.
Proof.
  intros pcs i j p ti tj H.
  unfold pick in H.
  destruct (scan_i_sound _ _ _ _ _ _ _ _ H) as [a [b [Hi [Hj [Hij rest]]]]].
  destruct rest as [Ha [Hb [Hd [Hel Hadm]]]].
  exists a, b. split; [exact Hi|]. split; [exact Hj|].
  split; [intro E; subst j; exact (Nat.lt_irrefl i Hij)|].
  split; [exact Ha|]. split; [exact Hb|]. split; [exact Hd|].
  split; [exact Hel|]. exact Hadm.
Qed.

Lemma pick_admissible : forall pcs i j p ti tj,
  pick pcs = Some (i, j, (p, ti, tj)) ->
  exists a b, admissible pcs a b p ti tj.
Proof.
  intros pcs i j p ti tj H.
  destruct (pick_sound pcs i j p ti tj H) as [a [b [_ [_ [_ [_ [_ [_ [_ Hadm]]]]]]]]].
  exists a, b. exact Hadm.
Qed.

Lemma pick_least : forall pcs i j a b p ti tj p' ti' tj',
  pick pcs = Some (i, j, (p, ti, tj)) ->
  nth_error pcs i = Some a ->
  nth_error pcs j = Some b ->
  admissible pcs a b p' ti' tj' ->
  ti <= ti'.
Proof.
  intros pcs i j a b p ti tj p' ti' tj' H Hi Hj Hadm.
  destruct (pick_sound pcs i j p ti tj H)
    as [a0 [b0 [Hi0 [Hj0 [_ [Hwa [Hwb [Hd [Hel _]]]]]]]]].
  rewrite Hi in Hi0. inversion Hi0. subst a0.
  rewrite Hj in Hj0. inversion Hj0. subst b0.
  assert (Hgeom : match ck_egg (bp_ck a), ck_egg (bp_ck b) with
                  | MkChord _, MkChord _ | MkChord _, MkCirc _
                  | MkCirc _, MkChord _ | MkCirc _, MkCirc _ => True
                  | _, _ => False
                  end -> ti <= ti').
  { intro Hcl.
    destruct (admissible_at_cook pcs a b p' ti' tj' Hcl Hadm) as [Hcook Hle].
    assert (Hin : In p' (counted pcs (bp_support a) (bp_support b))).
    { exact (admissible_counted pcs a b p' ti' tj'
               (nth_error_In _ _ Hi) (nth_error_In _ _ Hj) Hd Hwa Hwb Hadm). }
    assert (Hb : admissible_hit_b pcs a b p'
              (cook_t_egg (ck_egg (bp_ck a)) p')
              (cook_t_egg (ck_egg (bp_ck b)) p') = true).
    { apply admissible_hit_spec. apply admissible_alt. exact Hcook. }
    assert (Ic : In (mkHitCand p' (cook_t_egg (ck_egg (bp_ck a)) p')
                                (cook_t_egg (ck_egg (bp_ck b)) p'))
                     (adm_list pcs a b)).
    { unfold adm_list. apply cands_in; assumption. }
    apply Rle_trans with (cook_t_egg (ck_egg (bp_ck a)) p'); [| exact Hle].
    apply (least_le (adm_list pcs a b) (mkHitCand p ti tj)
            (mkHitCand p' (cook_t_egg (ck_egg (bp_ck a)) p')
                       (cook_t_egg (ck_egg (bp_ck b)) p')) Hel Ic). }
  destruct Hadm as [Hok _].
  destruct (ck_egg (bp_ck a)) as [ea|ea|ea|cla|na] eqn:Ea;
    destruct (ck_egg (bp_ck b)) as [eb|eb|eb|clb|nb] eqn:Eb;
    simpl in Hok; try contradiction.
  - apply Hgeom. exact I.
  - apply Hgeom. exact I.
  - apply Hgeom. exact I.
  - apply Hgeom. exact I.
  - assert (Eti : ti = 0).
    { destruct (cands_cook pcs a b _ (mkHitCand p ti tj) (least_in _ _ Hel)) as [Et _].
      simpl in Et. rewrite Ea in Et. simpl in Et. exact Et. }
    rewrite Eti. exact (proj1 (proj1 (proj1 Hok))).
Qed.

Lemma adm_list_covers : forall pcs a b p,
  piece_wf a -> piece_wf b ->
  window_pts (bp_support a) (bp_window a) p ->
  window_pts (bp_support b) (bp_window b) p ->
  In p (counted pcs (bp_support a) (bp_support b)) ->
  ~ vertex_of_both pcs (bp_support a) (bp_support b) p ->
  (overlap_pair (bp_support a) (bp_support b) = true ->
     In p (overlap_endpoints pcs (bp_support a) (bp_support b))) ->
  match ck_egg (bp_ck a), ck_egg (bp_ck b) with
  | MkChord _, MkChord _ => True
  | MkCirc _, MkCirc _ => True
  | MkCirc c, MkChord s => circ_chord_host_scope c s
  | MkChord s, MkCirc c => circ_chord_host_scope c s
  | _, _ => False
  end ->
  exists ti tj,
    In (mkHitCand p ti tj) (adm_list pcs a b) /\ admissible pcs a b p ti tj.
Proof.
  intros pcs a b p Ha Hb Hwa Hwb Hin Hv Hov Hclass.
  assert (Hhit : exists ti tj,
            I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck b)) (IHit p ti tj)).
  { destruct (ck_egg (bp_ck a)) as [ca|ca|ca|cla|na] eqn:Ega;
      destruct (ck_egg (bp_ck b)) as [cb|cb|cb|clb|nb] eqn:Egb;
      simpl in Hclass; try contradiction.
    - destruct (bp_support a) as [sa|sa] eqn:Ea;
        destruct (bp_support b) as [sb|sb] eqn:Eb.
      + rewrite <- Ea in Hwa. rewrite <- Eb in Hwb.
        destruct (hit_param_line_line a b p Ha Hb Hwa Hwb
                    (ex_intro _ sa Ea) (ex_intro _ sb Eb)) as [ti [tj Hok]].
        rewrite Ega, Egb in Hok. exists ti, tj. exact Hok.
      + destruct Hb as [Hr _]. unfold piece_realizes in Hr.
        rewrite Eb, Egb in Hr. destruct Hr.
      + destruct Ha as [Hr _]. unfold piece_realizes in Hr.
        rewrite Ea, Ega in Hr. destruct Hr.
      + destruct Hb as [Hr _]. unfold piece_realizes in Hr.
        rewrite Eb, Egb in Hr. destruct Hr.
    - assert (Hs : match ck_egg (bp_ck a), ck_egg (bp_ck b) with
                   | MkCirc c, MkChord s => circ_chord_host_scope c s
                   | MkChord s, MkCirc c => circ_chord_host_scope c s
                   | _, _ => False end).
      { rewrite Ega, Egb. exact Hclass. }
      destruct (hit_param_line_circle a b p Ha Hb Hwa Hwb Hs) as [ti [tj Hok]].
      rewrite Ega, Egb in Hok. exists ti, tj. exact Hok.
    - assert (Hs : match ck_egg (bp_ck a), ck_egg (bp_ck b) with
                   | MkCirc c, MkChord s => circ_chord_host_scope c s
                   | MkChord s, MkCirc c => circ_chord_host_scope c s
                   | _, _ => False end).
      { rewrite Ega, Egb. exact Hclass. }
      destruct (hit_param_line_circle a b p Ha Hb Hwa Hwb Hs) as [ti [tj Hok]].
      rewrite Ega, Egb in Hok. exists ti, tj. exact Hok.
    - destruct (bp_support a) as [sa|sa] eqn:Ea;
        destruct (bp_support b) as [sb|sb] eqn:Eb.
      + destruct Ha as [Hr _]. unfold piece_realizes in Hr.
        rewrite Ea, Ega in Hr. destruct Hr.
      + destruct Ha as [Hr _]. unfold piece_realizes in Hr.
        rewrite Ea, Ega in Hr. destruct Hr.
      + destruct Hb as [Hr _]. unfold piece_realizes in Hr.
        rewrite Eb, Egb in Hr. destruct Hr.
      + destruct (hit_param_circle_circle a b p sa sb Ha Hb Ea Eb Hwa Hwb)
          as [ti [tj [Hok _]]].
        rewrite Ega, Egb in Hok. exists ti, tj. exact Hok. }
  destruct Hhit as [ti [tj Hok]].
  assert (Hadm : admissible pcs a b p ti tj).
  { split; [exact Hok| split; [unfold progress_hit; exact Hv| exact Hov]]. }
  assert (Hcl : match ck_egg (bp_ck a), ck_egg (bp_ck b) with
                | MkChord _, MkChord _ | MkChord _, MkCirc _
                | MkCirc _, MkChord _ | MkCirc _, MkCirc _ => True
                | _, _ => False
                end).
  { destruct (ck_egg (bp_ck a)); destruct (ck_egg (bp_ck b));
      simpl in Hclass; try contradiction; exact I. }
  destruct (admissible_at_cook pcs a b p ti tj Hcl Hadm) as [Hcook _].
  exists (cook_t_egg (ck_egg (bp_ck a)) p), (cook_t_egg (ck_egg (bp_ck b)) p).
  split; [| exact Hcook].
  unfold adm_list. apply cands_in; [exact Hin|].
  apply admissible_hit_spec. apply admissible_alt. exact Hcook.
Qed.

(* -------------------------------------------------------------------------- *)
(* run on fuel S (rho_pcs). Declined absorbs. pick None stops.                *)
(* -------------------------------------------------------------------------- *)

Definition pick_bag (b : SheetBag) : option HitPick :=
  match b with
  | BagDeclined _ => None
  | BagLive _ pcs =>
      match pick pcs with
      | None => None
      | Some (i, j, (p, ti, tj)) => Some (mkHitPick i j p ti tj)
      end
  end.

Fixpoint run (fuel : nat) (b : SheetBag) : SheetBag :=
  match fuel with
  | O => b
  | S n =>
      match b with
      | BagDeclined _ => b
      | BagLive sh pcs =>
          match pick pcs with
          | None => b
          | Some (i, j, (p, ti, tj)) =>
              match nth_error pcs i, nth_error pcs j with
              | Some a, Some bb =>
                  run n (BagLive sh (adm_step pcs i j a bb p ti tj))
              | _, _ => b
              end
          end
      end
  end.

Lemma pick_bag_spec : forall b, pick_spec pick_bag b.
Proof.
  intros [sh pcs|sh]; unfold pick_spec, pick_bag.
  - destruct (pick pcs) as [[[i j] [[p ti] tj]]|] eqn:Ep; [simpl| exact I].
    destruct (pick_sound pcs i j p ti tj Ep)
      as [a [b [Hi [Hj [Hij [Ha [Hb [Hd [_ Hadm]]]]]]]]].
    exists a, b. split; [exact Hi|]. split; [exact Hj|]. split; [exact Hij|].
    split; [exact Ha|]. split; [exact Hb|]. split; [exact Hd|].
    apply admissible_alt. exact Hadm.
  - exact I.
Qed.

Lemma run_eq : forall fuel b, run fuel b = bag_run pick_bag fuel b.
Proof.
  induction fuel as [|fuel IH]; intros b; [reflexivity|].
  cbn [run bag_run].
  destruct b as [sh pcs|sh]; [| reflexivity].
  destruct (pick pcs) as [[[i j] [[p ti] tj]]|] eqn:Ep.
  2: { unfold pick_bag. rewrite Ep. reflexivity. }
  destruct (pick_sound pcs i j p ti tj Ep) as [a [bb [Hi [Hj _]]]].
  rewrite Hi, Hj.
  unfold pick_bag. rewrite Ep.
  assert (Es : step_hit (BagLive sh pcs) (mkHitPick i j p ti tj) =
               BagLive sh (adm_step pcs i j a bb p ti tj)).
  { unfold step_hit, adm_step. simpl. rewrite Hi, Hj. reflexivity. }
  rewrite <- Es. apply IH.
Qed.

Lemma run_step_or_stop : forall n b,
  run (S n) b = b \/ bag_step b (run 1%nat b).
Proof.
  intros n [sh pcs|sh].
  - simpl. destruct (pick pcs) as [[[i j] [[p ti] tj]]|] eqn:Ep.
    + destruct (nth_error pcs i) as [a|] eqn:Hi;
        destruct (nth_error pcs j) as [bb|] eqn:Hj.
      * right.
        destruct (pick_sound pcs i j p ti tj Ep)
          as [a0 [b0 [Hi0 [Hj0 [Hij [Ha [Hb [_ [_ Hadm]]]]]]]]].
        rewrite Hi in Hi0. inversion Hi0. subst a0.
        rewrite Hj in Hj0. inversion Hj0. subst b0.
        replace (run 1%nat (BagLive sh pcs))
          with (BagLive sh (adm_step pcs i j a bb p ti tj)).
        -- apply adm_step_is_bag_step; assumption.
        -- simpl. rewrite Ep, Hi, Hj. reflexivity.
      * left. reflexivity.
      * left. reflexivity.
      * left. reflexivity.
    + left. reflexivity.
  - left. simpl. reflexivity.
Qed.

Lemma run_terminates : forall sh pcs,
  bag_inv (BagLive sh pcs) ->
  match run (S (rho_pcs pcs)) (BagLive sh pcs) with
  | BagDeclined _ => True
  | BagLive _ pcs' => pick pcs' = None
  end.
Proof.
  intros sh pcs _.
  assert (Hs : run_stopped pick_bag (run (S (rho_pcs pcs)) (BagLive sh pcs))).
  { rewrite run_eq.
    change (S (rho_pcs pcs)) with (S (rho (BagLive sh pcs))).
    apply bag_run_fixpoint. exact pick_bag_spec. }
  destruct (run (S (rho_pcs pcs)) (BagLive sh pcs)) as [sh' pcs'|sh']; simpl in Hs.
  - unfold pick_bag in Hs.
    destruct (pick pcs') as [[[i j] [[p ti] tj]]|] eqn:Ep.
    + discriminate.
    + reflexivity.
  - exact I.
Qed.

Print Assumptions progress_hit_vertex.
Print Assumptions admissible_alt.
Print Assumptions admissible_counted.
Print Assumptions adm_step_is_bag_step.
Print Assumptions adm_step_vertex_both.
Print Assumptions hens_injective_unique.
Print Assumptions hen_pt_sits.
Print Assumptions hen_pt_injective.
Print Assumptions adm_step_hens_injective.
Print Assumptions cook_chord_le.
Print Assumptions circ_ang_eval.
Print Assumptions fold_lattice_spec.
Print Assumptions fold_lattice_le.
Print Assumptions cook_circ_le.
Print Assumptions I_ok_at_cook.
Print Assumptions admissible_at_cook.
Print Assumptions unit_param_spec.
Print Assumptions piece_param_on.
Print Assumptions hit_param_line_line.
Print Assumptions hit_param_line_circle.
Print Assumptions hit_param_circle_circle.
Print Assumptions cands_cook.
Print Assumptions cands_admissible.
Print Assumptions adm_list_admissible.
Print Assumptions cands_in.
Print Assumptions least_in.
Print Assumptions rle_b_false_iff.
Print Assumptions least_le.
Print Assumptions chord_eqb_spec_ok.
Print Assumptions circ_eqb_spec_ok.
Print Assumptions piece_wf_b_spec.
Print Assumptions pair_ok_spec.
Print Assumptions scan_j_sound.
Print Assumptions scan_i_sound.
Print Assumptions pick_sound.
Print Assumptions pick_admissible.
Print Assumptions pick_least.
Print Assumptions adm_list_covers.
Print Assumptions pick_bag_spec.
Print Assumptions run_eq.
Print Assumptions run_step_or_stop.
Print Assumptions run_terminates.

