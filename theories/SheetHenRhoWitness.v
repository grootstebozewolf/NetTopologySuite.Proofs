(* ============================================================================
   NetTopologySuite.Proofs.SheetHenRhoWitness
   ----------------------------------------------------------------------------
   Letter 2 slice: completeness, #892 halves, concentric radii.
   SheetHenRho.v is the Require Export umbrella. claimId: none.
   Does not remint 0007-forall-bag. 3-axiom host.
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From NTS.Proofs Require Export SheetHenRhoCount.
From Stdlib Require Import Reals Lra Lia List PeanoNat Bool Permutation ZArith.
From NTS.Proofs Require Import
  Distance Polynomial CircleChart SheetHenCookCore SheetHenCircEgg
  SheetHenBag ChartLineQuadratic HostCircChordOracle Atan2.
Import ListNotations.
Local Open Scope R_scope.
Local Open Scope list_scope.

(* -------------------------------------------------------------------------- *)
(* Completeness: a common window point is a candidate, by class.              *)
(* Equal carriers list overlap endpoints only, not the open interval.        *)
(* -------------------------------------------------------------------------- *)
Lemma image_on_line : forall pcs c p,
  support_image pcs (SuppChord c) p -> on_line c p.
Proof.
  intros pcs c p [pc [_ [_ [t [_ Hp]]]]].
  unfold support_at in Hp. exists t. exact Hp.
Qed.
Lemma image_on_circle : forall pcs c p,
  support_image pcs (SuppCircle c) p -> on_circle_carrier c p.
Proof.
  intros pcs c p [pc [_ [_ [t [_ Hp]]]]].
  unfold support_at in Hp. rewrite Hp. apply circ_eval_carrier.
Qed.
Lemma cross_zero_same_line : forall a b p,
  on_line a p -> on_line b p ->
  cross2 (chord_dx a) (chord_dy a) (chord_dx b) (chord_dy b) = 0 ->
  same_line_b a b = true.
Proof.
  intros a b p [ta Ha] [tb Hb] Hcr.
  destruct (chord_eval_lin a ta) as [Ax Ay]. rewrite <- Ha in Ax, Ay.
  destruct (chord_eval_lin b tb) as [Bx By]. rewrite <- Hb in Bx, By.
  assert (Dx : px (ce_p0 b) - px (ce_p0 a) = ta * chord_dx a - tb * chord_dx b) by lra.
  assert (Dy : py (ce_p0 b) - py (ce_p0 a) = ta * chord_dy a - tb * chord_dy b) by lra.
  assert (Hcda : cross2 (chord_dx a) (chord_dy a)
                        (px (ce_p0 b) - px (ce_p0 a))
                        (py (ce_p0 b) - py (ce_p0 a)) = 0).
  { unfold cross2. rewrite Dx, Dy.
    replace (chord_dx a * (ta * chord_dy a - tb * chord_dy b)
             - chord_dy a * (ta * chord_dx a - tb * chord_dx b))
      with (- tb * (chord_dx a * chord_dy b - chord_dy a * chord_dx b)) by ring.
    unfold cross2 in Hcr. rewrite Hcr. ring. }
  assert (Hcdv : cross2 (chord_dx b) (chord_dy b)
                        (px (ce_p0 b) - px (ce_p0 a))
                        (py (ce_p0 b) - py (ce_p0 a)) = 0).
  { unfold cross2. rewrite Dx, Dy.
    replace (chord_dx b * (ta * chord_dy a - tb * chord_dy b)
             - chord_dy b * (ta * chord_dx a - tb * chord_dx b))
      with (- ta * (chord_dx a * chord_dy b - chord_dy a * chord_dx b)) by ring.
    unfold cross2 in Hcr. rewrite Hcr. ring. }
  unfold same_line_b. cbn zeta.
  destruct (req_b (chord_dx a) 0 && req_b (chord_dy a) 0) eqn:Eda; simpl.
  - destruct (req_b (chord_dx b) 0 && req_b (chord_dy b) 0) eqn:Edb; simpl.
    + apply andb_prop in Eda. destruct Eda as [Eax Eay].
      apply req_b_true in Eax. apply req_b_true in Eay.
      apply andb_prop in Edb. destruct Edb as [Ebx Eby].
      apply req_b_true in Ebx. apply req_b_true in Eby.
      assert (Hdda : chord_dd a = 0) by (unfold chord_dd; rewrite Eax, Eay; ring).
      assert (Hddb : chord_dd b = 0) by (unfold chord_dd; rewrite Ebx, Eby; ring).
      apply pt_eqb_true.
      rewrite <- (chord_eval_deg a ta Hdda).
      rewrite <- (chord_eval_deg b tb Hddb).
      rewrite <- Ha, <- Hb. reflexivity.
    + apply req_b_true. exact Hcdv.
  - apply andb_true_intro. split; apply req_b_true; [exact Hcr| exact Hcda].
Qed.
Lemma not_same_cross : forall a b p,
  on_line a p -> on_line b p -> same_line_b a b = false ->
  cross2 (chord_dx a) (chord_dy a) (chord_dx b) (chord_dy b) <> 0.
Proof.
  intros a b p Ha Hb Hs Hz.
  assert (E : same_line_b a b = true) by (apply (cross_zero_same_line a b p); assumption).
  congruence.
Qed.
Lemma cramer_param : forall a b t s,
  cross2 (chord_dx a) (chord_dy a) (chord_dx b) (chord_dy b) <> 0 ->
  chord_eval a t = chord_eval b s ->
  t = cramer_t a b.
Proof.
  intros a b t s Hcr Heq.
  destruct (chord_eval_lin a t) as [Ax Ay].
  destruct (chord_eval_lin b s) as [Bx By].
  assert (Ex : px (chord_eval a t) = px (chord_eval b s)) by (rewrite Heq; reflexivity).
  assert (Ey : py (chord_eval a t) = py (chord_eval b s)) by (rewrite Heq; reflexivity).
  rewrite Ax, Bx in Ex. rewrite Ay, By in Ey.
  assert (Dx : t * chord_dx a - s * chord_dx b = px (ce_p0 b) - px (ce_p0 a)) by lra.
  assert (Dy : t * chord_dy a - s * chord_dy b = py (ce_p0 b) - py (ce_p0 a)) by lra.
  assert (Hc : t * cross2 (chord_dx a) (chord_dy a) (chord_dx b) (chord_dy b)
               = cross2 (px (ce_p0 b) - px (ce_p0 a)) (py (ce_p0 b) - py (ce_p0 a))
                        (chord_dx b) (chord_dy b)).
  { unfold cross2. rewrite <- Dx, <- Dy. ring. }
  unfold cramer_t.
  apply (Rmult_eq_reg_l (cross2 (chord_dx a) (chord_dy a) (chord_dx b) (chord_dy b)));
    [| exact Hcr].
  replace (cross2 (chord_dx a) (chord_dy a) (chord_dx b) (chord_dy b) *
           (cross2 (px (ce_p0 b) - px (ce_p0 a)) (py (ce_p0 b) - py (ce_p0 a))
                   (chord_dx b) (chord_dy b)
            / cross2 (chord_dx a) (chord_dy a) (chord_dx b) (chord_dy b)))
    with (cross2 (px (ce_p0 b) - px (ce_p0 a)) (py (ce_p0 b) - py (ce_p0 a))
                 (chord_dx b) (chord_dy b)) by (field; exact Hcr).
  rewrite <- Hc. ring.
Qed.
Lemma line_line_in_raw : forall a b p,
  on_line a p -> on_line b p -> same_line_b a b = false ->
  In p (line_line_pts a b).
Proof.
  intros a b p Ha Hb Hs.
  pose proof (not_same_cross a b p Ha Hb Hs) as Hcr.
  unfold line_line_pts.
  destruct (req_b (cross2 (chord_dx a) (chord_dy a) (chord_dx b) (chord_dy b)) 0) eqn:Ec.
  - apply req_b_true in Ec. contradiction.
  - destruct Ha as [t Ht]. destruct Hb as [s Hs2].
    assert (Et : t = cramer_t a b).
    { apply (cramer_param a b t s); [exact Hcr| rewrite <- Ht, <- Hs2; reflexivity]. }
    simpl. left. rewrite Ht, Et. reflexivity.
Qed.
Lemma quad_root_in : forall a b c x,
  a <> 0 -> quadratic a b c x = 0 -> In x (quad_roots a b c).
Proof.
  intros a b c x Ha Hx. unfold quad_roots.
  destruct (req_b a 0) eqn:Ea.
  - apply req_b_true in Ea. contradiction.
  - set (d := discriminant a b c).
    assert (Hnn : 0 <= d).
    { unfold d. apply (discriminant_real_root_implies_nonneg a b c x Ha Hx). }
    destruct (Rlt_dec d 0) as [Hlt|Hge]; [exfalso; lra|].
    pose proof (quad_formula a b c x Ha Hx) as Hf. cbv zeta in Hf. fold d in Hf.
    destruct (req_b d 0) eqn:Ed.
    + apply req_b_true in Ed.
      destruct Hf as [Hx1|Hx2].
      * simpl. left. rewrite Hx1, Ed, sqrt_0.
        replace (- b + 0) with (- b) by ring. reflexivity.
      * simpl. left. rewrite Hx2, Ed, sqrt_0.
        replace (- b - 0) with (- b) by ring. reflexivity.
    + destruct Hf as [Hx1|Hx2].
      * rewrite Hx1. simpl. left. reflexivity.
      * rewrite Hx2. simpl. right. left. reflexivity.
Qed.
Lemma line_circle_in_pts : forall s c p,
  on_line s p -> on_circle_carrier c p -> In p (line_circle_pts s c).
Proof.
  intros s c p [t Ht] Hc. unfold line_circle_pts.
  destruct (req_b (lc_qa s) 0) eqn:Eqa.
  - apply req_b_true in Eqa.
    destruct (sum_of_squares_zero _ _ Eqa) as [Dx Dy].
    assert (Hdd : chord_dd s = 0) by (unfold chord_dd; rewrite Dx, Dy; ring).
    assert (Hp0 : p = ce_p0 s) by (rewrite Ht; apply chord_eval_deg; exact Hdd).
    assert (Hqc0 : lc_qc s c = dist_sq (circ_o c) (ce_p0 s) - circ_r c * circ_r c).
    { unfold lc_qc, dist_sq. cbn zeta. ring. }
    assert (Hqc : lc_qc s c = 0).
    { rewrite Hp0 in Hc. unfold on_circle_carrier in Hc. rewrite Hqc0. lra. }
    destruct (req_b (lc_qc s c) 0) eqn:Eqc.
    + simpl. left. symmetry. exact Hp0.
    + assert (Et : req_b (lc_qc s c) 0 = true) by (apply req_b_true; exact Hqc).
      congruence.
  - assert (Hqa : lc_qa s <> 0).
    { intro Hz. assert (Eb : req_b (lc_qa s) 0 = true) by (apply req_b_true; exact Hz).
      congruence. }
    assert (Hq : quadratic (lc_qa s) (lc_qb s c) (lc_qc s c) t = 0).
    { rewrite lc_param_root. rewrite <- Ht. unfold on_circle_carrier in Hc. lra. }
    rewrite Ht. apply in_map. apply quad_root_in; assumption.
Qed.
Lemma same_circle_carriers : forall a b,
  same_circle_b a b = true ->
  circ_o a = circ_o b /\ circ_r a * circ_r a = circ_r b * circ_r b.
Proof.
  intros a b H. unfold same_circle_b in H. apply andb_prop in H. destruct H as [Ho Hr].
  split; [apply pt_eqb_true; exact Ho| apply req_b_true; exact Hr].
Qed.
Lemma circle_circle_le_2_excludes_same : forall a b,
  same_circle_b a b = true -> ~ (0 < dist (circ_o a) (circ_o b)).
Proof.
  intros a b H Hd. destruct (same_circle_carriers a b H) as [Ho _].
  rewrite Ho, dist_refl in Hd. lra.
Qed.
Lemma distinct_circles_positive : forall a b p,
  same_circle_b a b = false ->
  on_circle_carrier a p -> on_circle_carrier b p ->
  0 < dist (circ_o a) (circ_o b).
Proof.
  intros a b p Hs Ha Hb.
  destruct (Rle_dec (dist (circ_o a) (circ_o b)) 0) as [Hle|Hgt].
  - assert (Hz : dist (circ_o a) (circ_o b) = 0).
    { pose proof (dist_nonneg (circ_o a) (circ_o b)). lra. }
    apply dist_eq_zero_iff in Hz. destruct Hz as [Hx Hy].
    assert (Eo : circ_o a = circ_o b) by (apply pt_eq_coords; assumption).
    assert (Er : circ_r a * circ_r a = circ_r b * circ_r b).
    { unfold on_circle_carrier in Ha, Hb. rewrite Eo in Ha. lra. }
    assert (Es : same_circle_b a b = true).
    { unfold same_circle_b. apply andb_true_intro. split.
      - apply pt_eqb_true. exact Eo.
      - apply req_b_true. exact Er. }
    congruence.
  - pose proof (dist_nonneg (circ_o a) (circ_o b)). lra.
Qed.
Lemma circle_circle_in_pts : forall a b p,
  same_circle_b a b = false ->
  on_circle_carrier a p -> on_circle_carrier b p ->
  In p (circle_circle_pts a b).
Proof.
  intros a b p Hs Ha Hb.
  pose proof (distinct_circles_positive a b p Hs Ha Hb) as Hd.
  unfold circle_circle_pts.
  destruct (rle_b (dist (circ_o a) (circ_o b)) 0) eqn:Eb.
  - apply rle_b_true in Eb. lra.
  - apply filter_In. split.
    + destruct (two_circles_radical_point_unique (circ_o a) (circ_o b)
                 (circ_r a) (circ_r b) p Hd Ha Hb) as [Hp|Hp].
      * left. symmetry. exact Hp.
      * right. left. symmetry. exact Hp.
    + unfold on_both_b. apply andb_true_intro. split; apply req_b_true; assumption.
Qed.
Lemma keep_of_images : forall pcs s1 s2 p,
  support_image pcs s1 p -> support_image pcs s2 p ->
  ~ (family_vertex pcs s1 p /\ family_vertex pcs s2 p) ->
  keep_b pcs s1 s2 p = true.
Proof.
  intros pcs s1 s2 p I1 I2 Nv. unfold keep_b.
  apply andb_true_intro. split.
  - apply andb_true_intro. split; apply in_image_spec; assumption.
  - apply negb_true_iff.
    destruct (vertex_b pcs s1 p && vertex_b pcs s2 p) eqn:Ev; [| reflexivity].
    exfalso. apply andb_prop in Ev. destruct Ev as [A B].
    apply Nv. split; apply vertex_spec; assumption.
Qed.
Lemma raw_in_of_class : forall pcs u v p,
  support_image pcs u p -> support_image pcs v p ->
  match u, v with
  | SuppChord a, SuppChord b =>
      same_line_b a b = false \/ In p (overlap_pts pcs (SuppChord a) (SuppChord b))
  | SuppCircle a, SuppCircle b =>
      same_circle_b a b = false \/ In p (overlap_pts pcs (SuppCircle a) (SuppCircle b))
  | _, _ => True
  end ->
  In p (raw_pts pcs u v).
Proof.
  intros pcs u v p Iu Iv Hclass.
  destruct u as [a|a]; destruct v as [b|b]; simpl in Hclass; unfold raw_pts.
  - destruct (same_line_b a b) eqn:Esl.
    + destruct Hclass as [Hs|Hover]; [congruence| exact Hover].
    + apply line_line_in_raw.
      * apply (image_on_line pcs a). exact Iu.
      * apply (image_on_line pcs b). exact Iv.
      * exact Esl.
  - apply line_circle_in_pts.
    + apply (image_on_line pcs a). exact Iu.
    + apply (image_on_circle pcs b). exact Iv.
  - apply line_circle_in_pts.
    + apply (image_on_line pcs b). exact Iv.
    + apply (image_on_circle pcs a). exact Iu.
  - destruct (same_circle_b a b) eqn:Esc.
    + destruct Hclass as [Hs|Hover]; [congruence| exact Hover].
    + apply circle_circle_in_pts.
      * exact Esc.
      * apply (image_on_circle pcs a). exact Iu.
      * apply (image_on_circle pcs b). exact Iv.
Qed.
(* Letter 3 first obligation, flagged on #816 as overlap_hits_are_endpoints.
   An overlap has infinitely many common points, so this theorem counts p
   only when it is an overlap endpoint. A progress hit strictly inside the
   overlap interval is not in counted, and cooking there does not decrease ρ.
   For overlapping supports, 𝓘 or the step may take progress hits only at
   those endpoints. Once both endpoints are shared vertices, the coincident
   pieces go to the merge step. *)
Theorem rho_candidates_complete : forall pcs s1 s2 p,
  s1 <> s2 ->
  support_image pcs s1 p ->
  support_image pcs s2 p ->
  ~ (family_vertex pcs s1 p /\ family_vertex pcs s2 p) ->
  (forall a b, canon2 s1 s2 = (SuppChord a, SuppChord b) ->
     same_line_b a b = false \/ In p (overlap_pts pcs (SuppChord a) (SuppChord b))) ->
  (forall a b, canon2 s1 s2 = (SuppCircle a, SuppCircle b) ->
     same_circle_b a b = false \/ In p (overlap_pts pcs (SuppCircle a) (SuppCircle b))) ->
  In p (counted pcs s1 s2).
Proof.
  intros pcs s1 s2 p _ I1 I2 Nv Hline Hcirc.
  unfold counted.
  destruct (canon2 s1 s2) as [u v] eqn:Ec.
  assert (Huv : (u = s1 /\ v = s2) \/ (u = s2 /\ v = s1)).
  { unfold canon2 in Ec.
    destruct (rlex_le (support_reals s1) (support_reals s2)); inversion Ec; auto. }
  assert (Iu : support_image pcs u p).
  { destruct Huv as [[-> ->]|[-> ->]]; assumption. }
  assert (Iv : support_image pcs v p).
  { destruct Huv as [[-> ->]|[-> ->]]; assumption. }
  assert (Hk : keep_b pcs u v p = true).
  { apply keep_of_images; [exact Iu| exact Iv|].
    intros [A B]. apply Nv. destruct Huv as [[-> ->]|[-> ->]]; split; assumption. }
  assert (Hin : In p (raw_pts pcs u v)).
  { apply raw_in_of_class; [exact Iu| exact Iv|].
    destruct u as [a|a]; destruct v as [b|b]; simpl.
    - apply Hline. reflexivity.
    - exact I.
    - exact I.
    - apply Hcirc. reflexivity. }
  rewrite dedup_In. apply filter_In. split; assumption.
Qed.
(* -------------------------------------------------------------------------- *)
(* #892 CCW full-circle halves: two +π turns, Leibniz-distinct supports on    *)
(* one circle. Overlap is the shared antipode, a hen of both families, so ρ   *)
(* of the pair is 0. circle_circle_le_2's 0 < dist excludes this pair.        *)
(* -------------------------------------------------------------------------- *)
Lemma int_part_on_unit : forall x, 0 <= x < 1 -> Int_part x = 0%Z.
Proof.
  intros x Hx. destruct (base_Int_part x) as [Hle Hlt].
  assert (Hlt1 : IZR (Int_part x) < IZR 1) by lra.
  apply lt_IZR in Hlt1.
  assert (Hgt : IZR (-1) < IZR (Int_part x)) by lra.
  apply lt_IZR in Hgt. lia.
Qed.
Lemma align_k_same : forall a, align_k a a = 0%Z.
Proof.
  intro a. unfold align_k.
  pose proof PI_RGT_0 as Hpi.
  assert (Hp : PI <> 0) by lra.
  assert (H2 : 2 * PI <> 0) by nra.
  assert (E : (a - a) / (2 * PI) + / 2 = / 2).
  { apply (Rmult_eq_reg_l (2 * PI)); [| exact H2].
    replace (2 * PI * ((a - a) / (2 * PI) + / 2)) with ((a - a) + PI) by (field; exact Hp).
    replace (2 * PI * (/ 2)) with PI by field.
    ring. }
  rewrite E. apply int_part_on_unit. split.
  - apply Rlt_le. apply Rinv_0_lt_compat. lra.
  - apply (Rmult_lt_reg_l 2); [lra|]. replace (2 * (/ 2)) with 1 by field. lra.
Qed.
Lemma align_k_zero_pi : align_k 0 PI = 0%Z.
Proof.
  unfold align_k.
  pose proof PI_RGT_0 as Hpi.
  assert (Hp : PI <> 0) by lra.
  assert (H2 : 2 * PI <> 0) by nra.
  assert (E : (0 - PI) / (2 * PI) + / 2 = 0).
  { apply (Rmult_eq_reg_l (2 * PI)); [| exact H2].
    replace (2 * PI * ((0 - PI) / (2 * PI) + / 2)) with ((0 - PI) + PI) by (field; exact Hp).
    replace (2 * PI * 0) with 0 by ring.
    ring. }
  rewrite E. apply int_part_on_unit. lra.
Qed.
Definition iso_half_fst : CircularEgg := mkCircularEgg (mkPoint 0 0) 5 0 PI.
Definition iso_half_snd : CircularEgg := mkCircularEgg (mkPoint 0 0) 5 PI PI.
Lemma iso_halves_leibniz_distinct : iso_half_fst <> iso_half_snd.
Proof.
  intro H. unfold iso_half_fst, iso_half_snd in H. inversion H.
  pose proof PI_RGT_0. lra.
Qed.
Lemma iso_supports_distinct :
  SuppCircle iso_half_fst <> SuppCircle iso_half_snd.
Proof.
  intro H. inversion H. pose proof PI_RGT_0. lra.
Qed.
Lemma iso_same_circle : same_circle_b iso_half_fst iso_half_snd = true.
Proof.
  unfold same_circle_b, iso_half_fst, iso_half_snd. cbn.
  apply andb_true_intro. split; [apply pt_eqb_true; reflexivity| apply req_b_true; ring].
Qed.
Lemma iso_halves_not_transverse :
  ~ (0 < dist (circ_o iso_half_fst) (circ_o iso_half_snd)).
Proof. apply circle_circle_le_2_excludes_same. apply iso_same_circle. Qed.
Definition iso_half_pc (src dst : nat) (c : CircularEgg) : BagPiece :=
  mkBagPiece (mkChicken src dst (MkCirc (window_circ c (mkWindow 0 1))))
             (SuppCircle c) (mkWindow 0 1) nil.
Definition iso_half_pcs : list BagPiece :=
  [iso_half_pc 0 1 iso_half_fst; iso_half_pc 1 0 iso_half_snd].
Lemma iso_key_fst : forall t,
  key_param (SuppCircle iso_half_fst) (SuppCircle iso_half_fst) t = t * PI.
Proof.
  intro t. unfold key_param, iso_half_fst. cbn.
  assert (Eb : rle_b 0 (5 * 5) = true) by (apply rle_b_true; lra).
  rewrite Eb. cbv beta iota zeta.
  replace (0 + 0) with 0 by ring.
  rewrite align_k_same. replace (IZR 0) with 0 by reflexivity. ring.
Qed.
Lemma iso_key_snd : forall t,
  key_param (SuppCircle iso_half_fst) (SuppCircle iso_half_snd) t = PI + t * PI.
Proof.
  intro t. unfold key_param, iso_half_fst, iso_half_snd. cbn.
  assert (Eb : rle_b 0 (5 * 5) = true) by (apply rle_b_true; lra).
  rewrite Eb. cbv beta iota zeta.
  replace (PI + 0) with PI by ring.
  rewrite align_k_zero_pi. replace (IZR 0) with 0 by reflexivity. ring.
Qed.
Lemma circ_eqb_refl : forall c, circ_eqb c c = true.
Proof.
  intro c. unfold circ_eqb, pt_eqb.
  repeat (apply andb_true_intro; split); apply req_b_true; reflexivity.
Qed.
Lemma iso_circ_swap_false : circ_eqb iso_half_snd iso_half_fst = false.
Proof.
  unfold circ_eqb, iso_half_snd, iso_half_fst. cbn.
  assert (E : req_b PI 0 = false).
  { destruct (req_b PI 0) eqn:Eb; [| reflexivity].
    apply req_b_true in Eb. pose proof PI_RGT_0. lra. }
  rewrite E.
  destruct (pt_eqb (mkPoint 0 0) (mkPoint 0 0));
    destruct (req_b 5 5); destruct (req_b PI PI); reflexivity.
Qed.
Lemma iso_circ_ord_false : circ_eqb iso_half_fst iso_half_snd = false.
Proof.
  unfold circ_eqb, iso_half_fst, iso_half_snd. cbn.
  assert (E : req_b 0 PI = false).
  { destruct (req_b 0 PI) eqn:Eb; [| reflexivity].
    apply req_b_true in Eb. pose proof PI_RGT_0. lra. }
  rewrite E.
  destruct (pt_eqb (mkPoint 0 0) (mkPoint 0 0));
    destruct (req_b 5 5); destruct (req_b PI PI); reflexivity.
Qed.
Lemma iso_keys_fst :
  all_keys (SuppCircle iso_half_fst) (SuppCircle iso_half_fst) iso_half_pcs = [0; PI].
Proof.
  Opaque key_param.
  unfold all_keys, iso_half_pcs, piece_keys, iso_half_pc. cbn.
  rewrite circ_eqb_refl. rewrite iso_circ_swap_false. cbn.
  rewrite iso_key_fst, iso_key_fst.
  replace (0 * PI) with 0 by ring. replace (1 * PI) with PI by ring. reflexivity.
  Transparent key_param.
Qed.
Lemma iso_keys_snd :
  all_keys (SuppCircle iso_half_fst) (SuppCircle iso_half_snd) iso_half_pcs = [PI; 2 * PI].
Proof.
  Opaque key_param.
  unfold all_keys, iso_half_pcs, piece_keys, iso_half_pc. cbn.
  rewrite iso_circ_ord_false. rewrite circ_eqb_refl. cbn.
  rewrite iso_key_snd, iso_key_snd.
  replace (PI + 0 * PI) with PI by ring.
  replace (PI + 1 * PI) with (2 * PI) by ring. reflexivity.
  Transparent key_param.
Qed.
Lemma iso_antipode : point_of_key (SuppCircle iso_half_fst) PI = mkPoint (-5) 0.
Proof.
  unfold point_of_key, iso_half_fst. cbn [circ_sweep circ_theta0 circ_o circ_r px py].
  destruct (req_b PI 0) eqn:E.
  - apply req_b_true in E. pose proof PI_RGT_0. lra.
  - unfold circ_eval. cbn [circ_o circ_r circ_theta0 circ_sweep px py].
    assert (Hp : PI <> 0). { pose proof PI_RGT_0. lra. }
    replace (0 + ((PI - 0) / PI) * PI) with PI by (field; exact Hp).
    rewrite cos_PI, sin_PI. apply (f_equal2 mkPoint); ring.
Qed.
Lemma dedup_dup : forall p, dedup [p; p] = [p].
Proof.
  intro p.
  assert (E : pt_eqb p p = true) by (apply pt_eqb_true; reflexivity).
  simpl. rewrite E. reflexivity.
Qed.
Lemma iso_overlap_pts :
  overlap_pts iso_half_pcs (SuppCircle iso_half_fst) (SuppCircle iso_half_snd) =
  [mkPoint (-5) 0].
Proof.
  unfold overlap_pts. rewrite iso_keys_fst, iso_keys_snd. cbn [rmin_list rmax_list].
  assert (A : Rmin 0 PI = 0). { apply Rmin_left. pose proof PI_RGT_0. lra. }
  assert (B : Rmax 0 PI = PI). { apply Rmax_right. pose proof PI_RGT_0. lra. }
  assert (C : Rmin PI (2 * PI) = PI). { apply Rmin_left. pose proof PI_RGT_0. lra. }
  assert (D : Rmax PI (2 * PI) = 2 * PI). { apply Rmax_right. pose proof PI_RGT_0. lra. }
  rewrite A, B, C, D. rewrite B, C.
  assert (E : rle_b PI PI = true) by (apply rle_b_true; lra).
  rewrite E. rewrite iso_antipode. apply dedup_dup.
Qed.
Lemma iso_antipode_end_fst :
  support_at (SuppCircle iso_half_fst) 1 = mkPoint (-5) 0.
Proof.
  unfold support_at, circ_eval, iso_half_fst. cbn.
  replace (0 + 1 * PI) with PI by ring.
  rewrite cos_PI, sin_PI. apply (f_equal2 mkPoint); ring.
Qed.
Lemma iso_antipode_start_snd :
  support_at (SuppCircle iso_half_snd) 0 = mkPoint (-5) 0.
Proof.
  unfold support_at, circ_eval, iso_half_snd. cbn.
  replace (PI + 0 * PI) with PI by ring.
  rewrite cos_PI, sin_PI. apply (f_equal2 mkPoint); ring.
Qed.
Lemma iso_half_overlap_are_hens : forall p,
  In p (overlap_pts iso_half_pcs (SuppCircle iso_half_fst) (SuppCircle iso_half_snd)) ->
  family_vertex iso_half_pcs (SuppCircle iso_half_fst) p /\
  family_vertex iso_half_pcs (SuppCircle iso_half_snd) p.
Proof.
  intros p Hin.
  assert (Hin' : In p [mkPoint (-5) 0]).
  { exact (eq_rect _ (fun l => In p l) Hin _ iso_overlap_pts). }
  destruct Hin' as [<-|[]]. split.
  - exists (iso_half_pc 0 1 iso_half_fst). split; [simpl; auto|]. split; [reflexivity|].
    unfold piece_endpoint, iso_half_pc. cbn. right. symmetry. apply iso_antipode_end_fst.
  - exists (iso_half_pc 1 0 iso_half_snd). split; [simpl; auto|]. split; [reflexivity|].
    unfold piece_endpoint, iso_half_pc. cbn. left. symmetry. apply iso_antipode_start_snd.
Qed.
Lemma iso_keep_antipode :
  keep_b iso_half_pcs (SuppCircle iso_half_fst) (SuppCircle iso_half_snd)
         (mkPoint (-5) 0) = false.
Proof.
  unfold keep_b.
  assert (Hin : In (mkPoint (-5) 0)
      (overlap_pts iso_half_pcs (SuppCircle iso_half_fst) (SuppCircle iso_half_snd))).
  { assert (Hin0 : In (mkPoint (-5) 0) [mkPoint (-5) 0]).
    { unfold In. left. reflexivity. }
    apply (eq_rect _ (fun l => In (mkPoint (-5) 0) l) Hin0 _ (eq_sym iso_overlap_pts)). }
  assert (V : vertex_b iso_half_pcs (SuppCircle iso_half_fst) (mkPoint (-5) 0) &&
              vertex_b iso_half_pcs (SuppCircle iso_half_snd) (mkPoint (-5) 0) = true).
  { apply andb_true_intro. split; apply vertex_spec; apply iso_half_overlap_are_hens; exact Hin. }
  rewrite V. destruct (in_image_b iso_half_pcs (SuppCircle iso_half_fst) (mkPoint (-5) 0) &&
                       in_image_b iso_half_pcs (SuppCircle iso_half_snd) (mkPoint (-5) 0));
    reflexivity.
Qed.
Lemma iso_halves_raw_overlap :
  raw_pts iso_half_pcs (SuppCircle iso_half_fst) (SuppCircle iso_half_snd) =
  overlap_pts iso_half_pcs (SuppCircle iso_half_fst) (SuppCircle iso_half_snd).
Proof. unfold raw_pts. rewrite iso_same_circle. reflexivity. Qed.
Lemma iso_canon :
  canon2 (SuppCircle iso_half_fst) (SuppCircle iso_half_snd) =
  (SuppCircle iso_half_fst, SuppCircle iso_half_snd).
Proof.
  unfold canon2. unfold support_reals, iso_half_fst, iso_half_snd. cbn [px py circ_o circ_r circ_theta0 circ_sweep].
  unfold rlex_le.
  destruct (Req_EM_T 1 1) as [_|N1]; [| congruence].
  destruct (Req_EM_T 0 0) as [_|N0]; [| congruence].
  destruct (Req_EM_T 0 0) as [_|N0b]; [| congruence].
  destruct (Req_EM_T 5 5) as [_|N5]; [| congruence].
  destruct (Req_EM_T 0 PI) as [Bad|Npi].
  - pose proof PI_RGT_0. lra.
  - destruct (Rle_dec 0 PI) as [_|Hle]; [| pose proof PI_RGT_0; lra]. reflexivity.
Qed.
Lemma iso_half_counted_nil :
  counted iso_half_pcs (SuppCircle iso_half_fst) (SuppCircle iso_half_snd) = [].
Proof.
  unfold counted. rewrite iso_canon. cbn [fst snd].
  rewrite iso_halves_raw_overlap, iso_overlap_pts.
  cbn. rewrite iso_keep_antipode. reflexivity.
Qed.
Lemma iso_supports :
  supports_of iso_half_pcs = [SuppCircle iso_half_fst; SuppCircle iso_half_snd].
Proof.
  unfold iso_half_pcs, supports_of, iso_half_pc. cbn.
  rewrite iso_circ_ord_false. reflexivity.
Qed.
Lemma iso_half_pair_rho_zero : rho_pcs iso_half_pcs = 0%nat.
Proof.
  unfold rho_pcs. rewrite iso_supports. cbn.
  rewrite iso_half_counted_nil. reflexivity.
Qed.
(* Concentric, distinct radii: not separated (circle_circle_le_2 does not
   apply) and not the same circle (the overlap route does not apply).
   circle_circle_pts returns nil because dist of the centres is 0. *)
Definition conc_r5 : CircularEgg := mkCircularEgg (mkPoint 0 0) 5 0 PI.
Definition conc_r3 : CircularEgg := mkCircularEgg (mkPoint 0 0) 3 0 PI.
Lemma concentric_distinct_radii_empty : forall pcs,
  same_circle_b conc_r5 conc_r3 = false /\
  ~ (0 < dist (circ_o conc_r5) (circ_o conc_r3)) /\
  circle_circle_pts conc_r5 conc_r3 = [] /\
  raw_pts pcs (SuppCircle conc_r5) (SuppCircle conc_r3) = [].
Proof.
  intro pcs.
  assert (Hs : same_circle_b conc_r5 conc_r3 = false).
  { unfold same_circle_b, conc_r5, conc_r3. cbn.
    assert (E : req_b (5 * 5) (3 * 3) = false).
    { destruct (req_b (5 * 5) (3 * 3)) eqn:Eb; [| reflexivity].
      apply req_b_true in Eb. lra. }
    rewrite E. destruct (pt_eqb (mkPoint 0 0) (mkPoint 0 0)); reflexivity. }
  assert (Hd : dist (circ_o conc_r5) (circ_o conc_r3) = 0).
  { unfold conc_r5, conc_r3. cbn. apply dist_refl. }
  assert (Hsep : ~ (0 < dist (circ_o conc_r5) (circ_o conc_r3))) by lra.
  assert (Hc : circle_circle_pts conc_r5 conc_r3 = []).
  { unfold circle_circle_pts. rewrite Hd.
    assert (Eb : rle_b 0 0 = true) by (apply rle_b_true; lra).
    rewrite Eb. reflexivity. }
  assert (Hr : raw_pts pcs (SuppCircle conc_r5) (SuppCircle conc_r3) = []).
  { unfold raw_pts. rewrite Hs. exact Hc. }
  repeat split; assumption.
Qed.
Print Assumptions image_on_line.
Print Assumptions image_on_circle.
Print Assumptions cross_zero_same_line.
Print Assumptions not_same_cross.
Print Assumptions cramer_param.
Print Assumptions line_line_in_raw.
Print Assumptions quad_root_in.
Print Assumptions line_circle_in_pts.
Print Assumptions same_circle_carriers.
Print Assumptions circle_circle_le_2_excludes_same.
Print Assumptions distinct_circles_positive.
Print Assumptions circle_circle_in_pts.
Print Assumptions keep_of_images.
Print Assumptions raw_in_of_class.
Print Assumptions rho_candidates_complete.
Print Assumptions int_part_on_unit.
Print Assumptions align_k_same.
Print Assumptions align_k_zero_pi.
Print Assumptions iso_halves_leibniz_distinct.
Print Assumptions iso_supports_distinct.
Print Assumptions iso_same_circle.
Print Assumptions iso_halves_not_transverse.
Print Assumptions iso_key_fst.
Print Assumptions iso_key_snd.
Print Assumptions circ_eqb_refl.
Print Assumptions iso_circ_swap_false.
Print Assumptions iso_circ_ord_false.
Print Assumptions iso_keys_fst.
Print Assumptions iso_keys_snd.
Print Assumptions iso_antipode.
Print Assumptions dedup_dup.
Print Assumptions iso_overlap_pts.
Print Assumptions iso_antipode_end_fst.
Print Assumptions iso_antipode_start_snd.
Print Assumptions iso_half_overlap_are_hens.
Print Assumptions iso_keep_antipode.
Print Assumptions iso_halves_raw_overlap.
Print Assumptions iso_canon.
Print Assumptions iso_half_counted_nil.
Print Assumptions iso_supports.
Print Assumptions iso_half_pair_rho_zero.
Print Assumptions concentric_distinct_radii_empty.
