(* ============================================================================
   NetTopologySuite.Proofs.AtanIvt
   ----------------------------------------------------------------------------
   R1 / issue #559 (508-a golden quarter, and the 508-g half-circle instance).

   3-axiom atan on (-PI/2, PI/2): the IVT root of sin t - u * cos t.
   Drop-in for the Stdlib Ratan lemmas used by NurbsConicExact /
   AtanDoubleAngle.  No atan2 (that swap stays off this file).

   Scope.  CurveLength.is_curve_length_reparam asks for an explicit
   preimage in the surjectivity proof.  golden_phi_surj already exhibits
   golden_pre_u (tan (v/2)); tan is 3-axiom.  Defining
   golden_phi t := 2 * atan3 (golden_u t) puts IVT inside phi only.
   The headline nurbs2_golden_quarter_length does not mention atan.

   Not a MkNurbs remint.  Not an egg change.  Not host noding.

   No Admitted, no Axiom, no Parameter.  Print Assumptions should show
   the allowlist trio only (no classic).  Re-run on the corpus Rocq
   before peeling audit-exceptions.txt.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Grok
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
Local Open Scope R_scope.

(* ---------- atan3 : IVT root of sin t - u * cos t on [-PI/2, PI/2] ----- *)

Definition atan3_g (u t : R) : R := sin t - u * cos t.

Lemma atan3_g_cont (u : R) : continuity (atan3_g u).
Proof.
  unfold atan3_g. apply continuity_minus; [apply continuity_sin|].
  apply continuity_mult; [apply continuity_const; intros ? ?; reflexivity | apply continuity_cos].
Qed.

Lemma atan3_g_lo (u : R) : atan3_g u (- (PI / 2)) < 0.
Proof. unfold atan3_g. rewrite sin_neg, cos_neg, sin_PI2, cos_PI2. lra. Qed.

Lemma atan3_g_hi (u : R) : 0 < atan3_g u (PI / 2).
Proof. unfold atan3_g. rewrite sin_PI2, cos_PI2. lra. Qed.

Lemma atan3_half_pi_lt : - (PI / 2) < PI / 2.
Proof. pose proof PI2_RGT_0. lra. Qed.

Definition atan3 (u : R) : R :=
  proj1_sig (IVT (atan3_g u) (- (PI / 2)) (PI / 2)
                 (atan3_g_cont u) atan3_half_pi_lt (atan3_g_lo u) (atan3_g_hi u)).

Lemma atan3_spec (u : R) :
  - (PI / 2) < atan3 u < PI / 2 /\ sin (atan3 u) = u * cos (atan3 u).
Proof.
  unfold atan3. destruct (IVT _ _ _ _ _ _ _) as [z [Hz Hg]]; cbn.
  unfold atan3_g in Hg.
  assert (z <> - (PI / 2)).
  { intro E. subst. pose proof (atan3_g_lo u). unfold atan3_g in H. lra. }
  assert (z <> PI / 2).
  { intro E. subst. pose proof (atan3_g_hi u). unfold atan3_g in H0. lra. }
  repeat split; lra.
Qed.

Local Lemma atan3_sin_zero_unique (d : R) : - PI < d < PI -> sin d = 0 -> d = 0.
Proof.
  intros [Hl Hh] Hs.
  destruct (Rtotal_order d 0) as [Hn|[Hz|Hp]]; [|exact Hz|].
  - pose proof (sin_gt_0 (- d) ltac:(lra) ltac:(lra)). rewrite sin_neg in H. lra.
  - pose proof (sin_gt_0 d Hp Hh). lra.
Qed.

Lemma atan3_unique (u a : R) :
  - (PI / 2) < a < PI / 2 -> sin a = u * cos a -> a = atan3 u.
Proof.
  intros Ha Hs. destruct (atan3_spec u) as [Hb Hs'].
  set (b := atan3 u) in *.
  assert (sin (a - b) = 0) by (rewrite sin_minus, Hs, Hs'; ring).
  apply (Rplus_eq_reg_r (- b)). ring_simplify.
  replace (a - b) with (a + - b) in H by ring.
  apply atan3_sin_zero_unique; [lra | exact H].
Qed.

(* ---------- drop-ins for NurbsConicExact / AtanDoubleAngle ---------------- *)

Lemma atan3_0 : atan3 0 = 0.
Proof.
  symmetry. apply (atan3_unique 0 0).
  - pose proof PI2_RGT_0. lra.
  - rewrite sin_0. lra.
Qed.

Lemma atan3_1 : atan3 1 = PI / 4.
Proof.
  symmetry. apply (atan3_unique 1 (PI / 4)).
  - pose proof PI_RGT_0. lra.
  - rewrite sin_PI4, cos_PI4. lra.
Qed.

Lemma atan3_cos_pos (u : R) : 0 < cos (atan3 u).
Proof.
  destruct (atan3_spec u) as [Hb _]. apply cos_gt_0. exact Hb.
Qed.

Lemma atan3_le : forall x y, x <= y -> atan3 x <= atan3 y.
Proof.
  intros x y Hxy.
  set (a := atan3 x). set (b := atan3 y).
  destruct (atan3_spec x) as [Ha Hsx]. fold a in Ha, Hsx.
  destruct (atan3_spec y) as [Hb Hsy]. fold b in Hb, Hsy.
  assert (Hca : 0 < cos a) by (apply cos_gt_0; exact Ha).
  assert (Hcb : 0 < cos b) by (apply cos_gt_0; exact Hb).
  assert (Hsin : sin (a - b) = cos a * cos b * (x - y)).
  { rewrite sin_minus, Hsx, Hsy. ring. }
  destruct (Rle_lt_dec a b) as [Hle|Hgt].
  - exact Hle.
  - exfalso.
    assert (Hpos : 0 < a - b) by lra.
    assert (Hltpi : a - b < PI).
    { pose proof PI_RGT_0. lra. }
    pose proof (sin_gt_0 (a - b) Hpos Hltpi) as Hp.
    assert (0 < x - y).
    { assert (0 < cos a * cos b * (x - y)) by (rewrite <- Hsin; exact Hp). nra. }
    lra.
Qed.

Lemma atan3_tan : forall a,
  - (PI / 2) < a < PI / 2 -> atan3 (tan a) = a.
Proof.
  intros a Ha.
  symmetry. apply (atan3_unique (tan a) a Ha).
  unfold tan. field. apply Rgt_not_eq, cos_gt_0. exact Ha.
Qed.

Lemma cos_2_atan3 : forall x,
  cos (2 * atan3 x) = (1 - x * x) / (1 + x * x).
Proof.
  intro x.
  set (a := atan3 x).
  destruct (atan3_spec x) as [_ Hs]. fold a in Hs.
  assert (Hden : 1 + x * x <> 0) by nra.
  assert (Hpy : sin a * sin a + cos a * cos a = 1).
  { pose proof (sin2_cos2 a) as K. unfold Rsqr in K. exact K. }
  assert (Hcos2 : cos a * cos a * (1 + x * x) = 1).
  { replace (cos a * cos a * (1 + x * x))
      with (x * cos a * (x * cos a) + cos a * cos a) by ring.
    rewrite <- Hs. exact Hpy. }
  rewrite cos_2a.
  assert (E : cos a * cos a - sin a * sin a
              = cos a * cos a * (1 - x * x)) by (rewrite Hs; ring).
  rewrite E. unfold Rdiv.
  apply (Rmult_eq_reg_r (1 + x * x)); [| exact Hden].
  replace ((1 - x * x) * / (1 + x * x) * (1 + x * x))
    with (1 - x * x) by (field; exact Hden).
  replace (cos a * cos a * (1 - x * x) * (1 + x * x))
    with ((cos a * cos a * (1 + x * x)) * (1 - x * x)) by ring.
  rewrite Hcos2. ring.
Qed.

Lemma sin_2_atan3 : forall x,
  sin (2 * atan3 x) = (2 * x) / (1 + x * x).
Proof.
  intro x.
  set (a := atan3 x).
  destruct (atan3_spec x) as [_ Hs]. fold a in Hs.
  assert (Hden : 1 + x * x <> 0) by nra.
  assert (Hpy : sin a * sin a + cos a * cos a = 1).
  { pose proof (sin2_cos2 a) as K. unfold Rsqr in K. exact K. }
  assert (Hcos2 : cos a * cos a * (1 + x * x) = 1).
  { replace (cos a * cos a * (1 + x * x))
      with (x * cos a * (x * cos a) + cos a * cos a) by ring.
    rewrite <- Hs. exact Hpy. }
  rewrite sin_2a.
  replace (2 * sin a * cos a) with (2 * x * (cos a * cos a)) by (rewrite Hs; ring).
  unfold Rdiv.
  apply (Rmult_eq_reg_r (1 + x * x)); [| exact Hden].
  replace ((2 * x) * / (1 + x * x) * (1 + x * x))
    with (2 * x) by (field; exact Hden).
  replace (2 * x * (cos a * cos a) * (1 + x * x))
    with (2 * x * (cos a * cos a * (1 + x * x))) by ring.
  rewrite Hcos2. ring.
Qed.

Print Assumptions atan3_unique.
Print Assumptions atan3_0.
Print Assumptions atan3_1.
Print Assumptions atan3_le.
Print Assumptions atan3_tan.
Print Assumptions cos_2_atan3.
Print Assumptions sin_2_atan3.
