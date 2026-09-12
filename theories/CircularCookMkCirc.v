(* ============================================================================
   NetTopologySuite.Proofs.CircularCookMkCirc
   ----------------------------------------------------------------------------
   ADR-0007 Γ letter: host MkCirc / CircGamma (claimId 0007-gamma-mkcirc).

   Host CircularEgg interpolant γ(t) = O + r·(cos(θ₀ + t·Δθ), sin(θ₀ + t·Δθ)).
   Angles are egg data — atan2-free, 3-axiom. Sidecar arc_gamma / circ_gamma
   (atan2 retract) is not this interpolant.

   Locked fixture: two minor quarter-circles that properly cross.
     A: O=(0,0) r=5 θ₀=0   Δθ=π/2   (5,0) → (0,5)
     B: O=(5,0) r=5 θ₀=π/2 Δθ=π/2   (5,5) → (0,0)
   Hit at (5/2, 5√3/2) with (tᵢ, tⱼ) = (2/3, 1/3). try_cook_hit mints.

   MkOutOfScope EggCircularArc stays Decline. Mixed stays sidecar.
   Not CircularString / CompoundCurve / Circle-as-own-type. Not nlerp.

   WITNESS topic: overlay / core · claimId: 0007-gamma-mkcirc
   witness: 0007-gamma-mkcirc
   board: ADR-0007
   3-axiom. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra Rtrigo_calc Rtrigo_facts.
From NTS.Proofs Require Import Distance SheetHenCook.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Angle arithmetic for the locked quarter-circle pair.                       *)
(* -------------------------------------------------------------------------- *)

Lemma two_thirds_half_pi : (2 / 3) * (PI / 2) = PI / 3.
Proof.
  pose proof PI_RGT_0. field; lra.
Qed.

Lemma one_third_half_pi : (1 / 3) * (PI / 2) = PI / 6.
Proof.
  pose proof PI_RGT_0. field; lra.
Qed.

Lemma half_pi_plus_pi6 : PI / 2 + PI / 6 = 2 * PI / 3.
Proof.
  pose proof PI_RGT_0. field; lra.
Qed.

Lemma two_pi_over_three : 2 * PI / 3 = PI - PI / 3.
Proof.
  pose proof PI_RGT_0. field; lra.
Qed.

Lemma cos_2PI3 : cos (2 * PI / 3) = - (1 / 2).
Proof.
  rewrite two_pi_over_three, cos_pi_minus, cos_PI3. reflexivity.
Qed.

Lemma sin_2PI3 : sin (2 * PI / 3) = sqrt 3 / 2.
Proof.
  rewrite two_pi_over_three, sin_pi_minus, sin_PI3. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked MkCirc eggs.                                                        *)
(* -------------------------------------------------------------------------- *)

Definition locked_circ_A : CircularEgg :=
  mkCircularEgg (mkPoint 0 0) 5 0 (PI / 2).

Definition locked_circ_B : CircularEgg :=
  mkCircularEgg (mkPoint 5 0) 5 (PI / 2) (PI / 2).

Definition locked_circ_hit_pt : Point :=
  mkPoint (5 / 2) (5 * sqrt 3 / 2).

Definition locked_circ_ti : R := 2 / 3.
Definition locked_circ_tj : R := 1 / 3.

Definition locked_mkcirc_ck1 : Chicken :=
  mkChicken 0%nat 1%nat (MkCirc locked_circ_A).

Definition locked_mkcirc_ck2 : Chicken :=
  mkChicken 2%nat 3%nat (MkCirc locked_circ_B).

(* -------------------------------------------------------------------------- *)
(* 3 interpolant axioms on the locked eggs: γ(0), γ(1), on-circle.            *)
(* -------------------------------------------------------------------------- *)

Lemma circ_eval_on_circle :
  forall c t,
    dist_sq (circ_o c) (circ_eval c t) = (circ_r c) * (circ_r c).
Proof.
  intros [o r th0 sw] t.
  unfold dist_sq, circ_eval. cbn [px py circ_o circ_r circ_theta0 circ_sweep].
  set (th := th0 + t * sw).
  pose proof (sin2_cos2 th) as Hsc.
  unfold Rsqr in Hsc.
  replace (px o - (px o + r * cos th)) with (- (r * cos th)) by ring.
  replace (py o - (py o + r * sin th)) with (- (r * sin th)) by ring.
  replace ((- (r * cos th)) * (- (r * cos th))
           + (- (r * sin th)) * (- (r * sin th)))
    with (r * r * (sin th * sin th + cos th * cos th)) by ring.
  rewrite Hsc. ring.
Qed.

Lemma locked_circ_A_at_0 :
  circ_eval locked_circ_A 0 = mkPoint 5 0.
Proof.
  unfold circ_eval, locked_circ_A. cbn [px py circ_o circ_r circ_theta0 circ_sweep].
  rewrite Rmult_0_l, Rplus_0_r, cos_0, sin_0.
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma locked_circ_A_at_1 :
  circ_eval locked_circ_A 1 = mkPoint 0 5.
Proof.
  unfold circ_eval, locked_circ_A. cbn [px py circ_o circ_r circ_theta0 circ_sweep].
  replace (0 + 1 * (PI / 2)) with (PI / 2) by field.
  rewrite cos_PI2, sin_PI2.
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma locked_circ_B_at_0 :
  circ_eval locked_circ_B 0 = mkPoint 5 5.
Proof.
  unfold circ_eval, locked_circ_B. cbn [px py circ_o circ_r circ_theta0 circ_sweep].
  replace (PI / 2 + 0 * (PI / 2)) with (PI / 2) by field.
  rewrite cos_PI2, sin_PI2.
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma locked_circ_B_at_1 :
  circ_eval locked_circ_B 1 = mkPoint 0 0.
Proof.
  unfold circ_eval, locked_circ_B. cbn [px py circ_o circ_r circ_theta0 circ_sweep].
  rewrite Rmult_1_l.
  replace (PI / 2 + PI / 2) with PI by field.
  rewrite cos_PI, sin_PI.
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma locked_circ_A_at_ti :
  circ_eval locked_circ_A locked_circ_ti = locked_circ_hit_pt.
Proof.
  unfold circ_eval, locked_circ_A, locked_circ_ti, locked_circ_hit_pt.
  cbn [px py circ_o circ_r circ_theta0 circ_sweep].
  replace (0 + (2 / 3) * (PI / 2)) with (PI / 3) by (pose proof PI_RGT_0; field; lra).
  rewrite cos_PI3, sin_PI3.
  apply (f_equal2 mkPoint); field.
Qed.

Lemma locked_circ_B_at_tj :
  circ_eval locked_circ_B locked_circ_tj = locked_circ_hit_pt.
Proof.
  unfold circ_eval, locked_circ_B, locked_circ_tj, locked_circ_hit_pt.
  cbn [px py circ_o circ_r circ_theta0 circ_sweep].
  rewrite one_third_half_pi, half_pi_plus_pi6, cos_2PI3, sin_2PI3.
  apply (f_equal2 mkPoint); field.
Qed.

Lemma locked_circ_ti_in_01 : 0 <= locked_circ_ti <= 1.
Proof.
  unfold locked_circ_ti. lra.
Qed.

Lemma locked_circ_tj_in_01 : 0 <= locked_circ_tj <= 1.
Proof.
  unfold locked_circ_tj. lra.
Qed.

Lemma locked_on_circ_A :
  on_circ locked_circ_A locked_circ_ti locked_circ_hit_pt.
Proof.
  unfold on_circ. split; [exact locked_circ_ti_in_01|].
  symmetry. exact locked_circ_A_at_ti.
Qed.

Lemma locked_on_circ_B :
  on_circ locked_circ_B locked_circ_tj locked_circ_hit_pt.
Proof.
  unfold on_circ. split; [exact locked_circ_tj_in_01|].
  symmetry. exact locked_circ_B_at_tj.
Qed.

(* -------------------------------------------------------------------------- *)
(* Host I_ok Hit and try_cook_hit mint on the locked MkCirc pair.             *)
(* -------------------------------------------------------------------------- *)

Lemma locked_mkcirc_I_ok :
  I_ok (MkCirc locked_circ_A) (MkCirc locked_circ_B)
       (IHit locked_circ_hit_pt locked_circ_ti locked_circ_tj).
Proof.
  unfold I_ok.
  split; [exact locked_on_circ_A | exact locked_on_circ_B].
Qed.

Definition locked_mkcirc_hit : IResult :=
  IHit locked_circ_hit_pt locked_circ_ti locked_circ_tj.

Definition cooked_mkcirc : CookedPair :=
  cook_hit_circs locked_mkcirc_ck1 locked_mkcirc_ck2
    locked_circ_A locked_circ_B locked_circ_ti locked_circ_tj crossing_hen.

Lemma cook_hit_circs_shares_hen :
  forall c1 c2 e1 e2 ti tj h,
    cooked_shares_hen (cook_hit_circs c1 c2 e1 e2 ti tj h).
Proof.
  intros. repeat split; reflexivity.
Qed.

Lemma cooked_mkcirc_shares :
  cooked_shares_hen cooked_mkcirc.
Proof.
  apply cook_hit_circs_shares_hen.
Qed.

Lemma cooked_mkcirc_try :
  try_cook_hit locked_mkcirc_ck1 locked_mkcirc_ck2
    locked_mkcirc_hit crossing_hen = Some cooked_mkcirc.
Proof.
  reflexivity.
Qed.

(* Fixture honesty: arc eval ≠ endpoint-chord lerp; chords meet at
   (5/2, 5/2); Hit is not that crossing. Fail if γ is endpoint lerp. *)

Lemma locked_circ_eval_neq_endpoint_chord :
  circ_eval locked_circ_A locked_circ_ti <>
  chord_eval
    (mkChordEgg (circ_eval locked_circ_A 0) (circ_eval locked_circ_A 1))
    locked_circ_ti.
Proof.
  rewrite locked_circ_A_at_0, locked_circ_A_at_1, locked_circ_A_at_ti.
  unfold chord_eval, locked_circ_ti, locked_circ_hit_pt.
  cbn [ce_p0 ce_p1 px py].
  intros H. injection H as Hx _.
  lra.
Qed.

Lemma locked_mkcirc_endpoint_chords_hit :
  chord_eval
    (mkChordEgg (circ_eval locked_circ_A 0) (circ_eval locked_circ_A 1))
    (1 / 2)
  = mkPoint (5 / 2) (5 / 2) /\
  chord_eval
    (mkChordEgg (circ_eval locked_circ_B 0) (circ_eval locked_circ_B 1))
    (1 / 2)
  = mkPoint (5 / 2) (5 / 2).
Proof.
  rewrite locked_circ_A_at_0, locked_circ_A_at_1,
          locked_circ_B_at_0, locked_circ_B_at_1.
  unfold chord_eval. cbn [ce_p0 ce_p1 px py].
  split; apply (f_equal2 mkPoint); field.
Qed.

Lemma locked_mkcirc_hit_neq_endpoint_chord_x :
  locked_circ_hit_pt <> mkPoint (5 / 2) (5 / 2).
Proof.
  unfold locked_circ_hit_pt. intros H. injection H as _ Hy.
  apply (f_equal (fun z => z * 2 / 5)) in Hy.
  replace ((5 * sqrt 3 / 2) * 2 / 5) with (sqrt 3) in Hy by field.
  replace ((5 / 2) * 2 / 5) with 1 in Hy by field.
  pose proof (sqrt_sqrt 3 ltac:(lra)) as Hsq.
  rewrite Hy in Hsq. lra.
Qed.

Lemma mkcirc_tag_still_decline :
  I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc) IDecline.
Proof.
  exact circular_decline_I_ok.
Qed.

Lemma mkcirc_tag_hit_false :
  forall p ti tj,
    ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
         (IHit p ti tj).
Proof.
  exact circular_hit_not_I_ok.
Qed.

Lemma mkcirc_mixed_still_decline :
  I_ok (MkChord hor_bot) (MkCirc locked_circ_A) IDecline.
Proof.
  unfold I_ok, interpolant_pair. intro H. exact H.
Qed.

Lemma circular_egg_mkcirc_or_tag :
  forall e : Egg,
    egg_class e = EggCircularArc ->
    (exists c, e = MkCirc c) \/ e = MkOutOfScope EggCircularArc.
Proof.
  intros e He.
  destruct e as [c | circ | clth | cl].
  - unfold egg_class in He. discriminate.
  - left. exists circ. reflexivity.
  - unfold egg_class in He. discriminate.
  - unfold egg_class in He. subst cl. right. reflexivity.
Qed.

(* WITNESS {"claimId":"0007-gamma-mkcirc","topic":"overlay","lemma":"locked_mkcirc_I_ok","title":"Host I_ok Hits two MkCirc circular chickens on the locked quarter-circle pair","file":"theories/CircularCookMkCirc.v","witness":"0007-gamma-mkcirc","board":"ADR-0007"} *)

(* WITNESS {"claimId":"0007-gamma-mkcirc","topic":"core","lemma":"cooked_mkcirc_try","title":"try_cook_hit mints a hen on the locked MkCirc Hit","file":"theories/CircularCookMkCirc.v","witness":"0007-gamma-mkcirc","board":"ADR-0007"} *)

Print Assumptions two_thirds_half_pi.
Print Assumptions cos_2PI3.
Print Assumptions sin_2PI3.
Print Assumptions circ_eval_on_circle.
Print Assumptions locked_circ_A_at_0.
Print Assumptions locked_circ_A_at_1.
Print Assumptions locked_circ_A_at_ti.
Print Assumptions locked_circ_B_at_tj.
Print Assumptions locked_mkcirc_I_ok.
Print Assumptions cooked_mkcirc_try.
Print Assumptions locked_circ_eval_neq_endpoint_chord.
Print Assumptions locked_mkcirc_endpoint_chords_hit.
Print Assumptions locked_mkcirc_hit_neq_endpoint_chord_x.
Print Assumptions cook_hit_circs_shares_hen.
Print Assumptions cooked_mkcirc_shares.
Print Assumptions circular_egg_mkcirc_or_tag.
Print Assumptions mkcirc_mixed_still_decline.
