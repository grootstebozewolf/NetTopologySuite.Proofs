(* ============================================================================
   NetTopologySuite.Proofs.EllipseCookMkEllipse
   ----------------------------------------------------------------------------
   ADR-0007 letter: ellipse×ellipse first-cook / Hit arm
   (claimId 0007-ellipse-first-cook; owner decision #1031). NTS has no
   elliptic arc type;
   this is the ADR-0007 EggEllipse (SQL/MM-style EllipticalCurve) pair.

   Host gamma is the eccentric-anomaly ellipse in SheetHenEllipseEgg.
   The parameterisation is OUR choice (egg header). Endpoints are
   gamma(0) and gamma(1).

   Fixture: two 2×1 half-ellipses, the second rotated a quarter turn.
     A: centre (0,0), a = 2, b = 1, phi = 0,    theta in [0, pi].
        gamma_A(t) = (2 cos(pi t), sin(pi t))
     B: centre (1,1), a = 2, b = 1, phi = pi/2, theta in [0, pi].
        gamma_B(u) = (1 - sin(pi u), 1 + 2 cos(pi u))
   Both images meet at (0,1) with ti = tj = 1/2, interior on both.
   A runs along its minor vertex there (direction (-1,0)); B runs
   along its major vertex (direction (0,-1)). The Hit is not on the
   endpoint chord of A (that chord is y = 0), so an endpoint-lerp
   reading of gamma fails locked_ell_eval_neq_endpoint_chord.
     C: A translated to centre (0,5). A × C is Empty: y_A <= 1 < 4 <= y_C.

   MkOutOfScope EggEllipse stays Decline. Mixed ellipse×chord and
   ellipse×circular stay Decline. SIN / spiral / geodesic stay out
   of first cook. This is a locked pair plus the Hit / Empty / mint
   arms, not a general ellipse×ellipse root finder (that is a
   quartic; no constructed_hit for ellipses here), not a kiss
   procedure, and not EllipseLength / EllipseSpeedIntegral.

   WITNESS topic: overlay · claimId: 0007-ellipse-first-cook
   witness: 0007-ellipse-first-cook
   board: ADR-0007
   3-axiom host. No Admitted, no stub declaration.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance SheetHenCook.
Local Open Scope R_scope.

Definition locked_ell_A : EllipticEgg :=
  mkEllipticEgg (mkPoint 0 0) 2 1 0 0 PI.

Definition locked_ell_B : EllipticEgg :=
  mkEllipticEgg (mkPoint 1 1) 2 1 (PI / 2) 0 PI.

Definition locked_ell_C : EllipticEgg :=
  mkEllipticEgg (mkPoint 0 5) 2 1 0 0 PI.

Definition locked_ell_hit_pt : Point := mkPoint 0 1.
Definition locked_ell_ti : R := 1 / 2.
Definition locked_ell_tj : R := 1 / 2.

Definition locked_ell_ck1 : Chicken :=
  mkChicken 0%nat 1%nat (MkEllipse locked_ell_A).

Definition locked_ell_ck2 : Chicken :=
  mkChicken 2%nat 3%nat (MkEllipse locked_ell_B).

(* Closed forms of the three locked interpolants. *)
Lemma locked_ell_A_eval :
  forall t, ell_eval locked_ell_A t = mkPoint (2 * cos (t * PI)) (sin (t * PI)).
Proof.
  intros t. unfold ell_eval, ell_u, ell_v, locked_ell_A.
  cbn [ell_o ell_a ell_b ell_phi ell_theta0 ell_sweep px py].
  rewrite cos_0, sin_0.
  replace (0 + t * PI) with (t * PI) by ring.
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma locked_ell_B_eval :
  forall u,
    ell_eval locked_ell_B u =
    mkPoint (1 - sin (u * PI)) (1 + 2 * cos (u * PI)).
Proof.
  intros u. unfold ell_eval, ell_u, ell_v, locked_ell_B.
  cbn [ell_o ell_a ell_b ell_phi ell_theta0 ell_sweep px py].
  rewrite cos_PI2, sin_PI2.
  replace (0 + u * PI) with (u * PI) by ring.
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma locked_ell_C_eval :
  forall t,
    ell_eval locked_ell_C t = mkPoint (2 * cos (t * PI)) (5 + sin (t * PI)).
Proof.
  intros t. unfold ell_eval, ell_u, ell_v, locked_ell_C.
  cbn [ell_o ell_a ell_b ell_phi ell_theta0 ell_sweep px py].
  rewrite cos_0, sin_0.
  replace (0 + t * PI) with (t * PI) by ring.
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma half_PI_is_PI2 : 1 / 2 * PI = PI / 2.
Proof. field. Qed.

Lemma locked_ell_A_at_ti :
  ell_eval locked_ell_A locked_ell_ti = locked_ell_hit_pt.
Proof.
  rewrite locked_ell_A_eval. unfold locked_ell_ti, locked_ell_hit_pt.
  rewrite half_PI_is_PI2, cos_PI2, sin_PI2.
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma locked_ell_B_at_tj :
  ell_eval locked_ell_B locked_ell_tj = locked_ell_hit_pt.
Proof.
  rewrite locked_ell_B_eval. unfold locked_ell_tj, locked_ell_hit_pt.
  rewrite half_PI_is_PI2, cos_PI2, sin_PI2.
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma locked_on_ell_A :
  on_ell locked_ell_A locked_ell_ti locked_ell_hit_pt.
Proof.
  unfold on_ell. split; [unfold locked_ell_ti; lra|].
  symmetry. exact locked_ell_A_at_ti.
Qed.

Lemma locked_on_ell_B :
  on_ell locked_ell_B locked_ell_tj locked_ell_hit_pt.
Proof.
  unfold on_ell. split; [unfold locked_ell_tj; lra|].
  symmetry. exact locked_ell_B_at_tj.
Qed.

Lemma locked_mkellipse_I_ok :
  I_ok (MkEllipse locked_ell_A) (MkEllipse locked_ell_B)
       (IHit locked_ell_hit_pt locked_ell_ti locked_ell_tj).
Proof.
  unfold I_ok.
  split; [exact locked_on_ell_A | exact locked_on_ell_B].
Qed.

(* The Hit is interior on both eggs: not a shared endpoint. *)
Lemma locked_ell_hit_interior :
  0 < locked_ell_ti < 1 /\ 0 < locked_ell_tj < 1.
Proof.
  unfold locked_ell_ti, locked_ell_tj. lra.
Qed.

Lemma locked_ell_A_at_0 : ell_eval locked_ell_A 0 = mkPoint 2 0.
Proof.
  rewrite locked_ell_A_eval.
  replace (0 * PI) with 0 by ring. rewrite cos_0, sin_0.
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma locked_ell_A_at_1 : ell_eval locked_ell_A 1 = mkPoint (-2) 0.
Proof.
  rewrite locked_ell_A_eval.
  replace (1 * PI) with PI by ring. rewrite cos_PI, sin_PI.
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma locked_ell_B_at_0 : ell_eval locked_ell_B 0 = mkPoint 1 3.
Proof.
  rewrite locked_ell_B_eval.
  replace (0 * PI) with 0 by ring. rewrite cos_0, sin_0.
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma locked_ell_B_at_1 : ell_eval locked_ell_B 1 = mkPoint 1 (-1).
Proof.
  rewrite locked_ell_B_eval.
  replace (1 * PI) with PI by ring. rewrite cos_PI, sin_PI.
  apply (f_equal2 mkPoint); ring.
Qed.

(* gamma(ti) is not the endpoint chord at the same parameter. An
   endpoint lerp would make this an equality, so the obligation
   fails under that reading of eval. *)
Lemma locked_ell_eval_neq_endpoint_chord :
  ell_eval locked_ell_A locked_ell_ti
    <> chord_eval
         (mkChordEgg (ell_eval locked_ell_A 0) (ell_eval locked_ell_A 1))
         locked_ell_ti.
Proof.
  intros Heq.
  rewrite locked_ell_A_at_ti, locked_ell_A_at_0, locked_ell_A_at_1 in Heq.
  apply (f_equal py) in Heq.
  unfold chord_eval, locked_ell_hit_pt, locked_ell_ti in Heq.
  cbn [ce_p0 ce_p1 px py] in Heq.
  lra.
Qed.

(* The locked eggs are ellipses, not circles: a <> b. The Hit is on
   the minor vertex of A and the major vertex of B, at different
   distances from the two centres. *)
Lemma locked_ell_not_circle :
  ell_a locked_ell_A <> ell_b locked_ell_A /\
  ell_a locked_ell_B <> ell_b locked_ell_B.
Proof.
  unfold locked_ell_A, locked_ell_B. cbn [ell_a ell_b]. split; lra.
Qed.

(* Empty: A sits in y <= 1, C in y >= 4. *)
Lemma locked_ell_A_C_disjoint :
  ~ exists X t1 t2,
      on_ell locked_ell_A t1 X /\ on_ell locked_ell_C t2 X.
Proof.
  intros [X [t1 [t2 [[_ HA] [_ HC]]]]].
  rewrite locked_ell_A_eval in HA. rewrite locked_ell_C_eval in HC.
  rewrite HA in HC. apply (f_equal py) in HC. cbn [py] in HC.
  pose proof (SIN_bound (t1 * PI)) as [_ H1].
  pose proof (SIN_bound (t2 * PI)) as [H2 _].
  lra.
Qed.

Lemma locked_mkellipse_empty_I_ok :
  I_ok (MkEllipse locked_ell_A) (MkEllipse locked_ell_C) IEmpty.
Proof.
  unfold I_ok. exact locked_ell_A_C_disjoint.
Qed.

(* A Hit pair is never Empty and an Empty pair never Hits. *)
Lemma locked_mkellipse_hit_not_empty :
  ~ I_ok (MkEllipse locked_ell_A) (MkEllipse locked_ell_B) IEmpty.
Proof.
  unfold I_ok. intros H. apply H.
  exists locked_ell_hit_pt, locked_ell_ti, locked_ell_tj.
  split; [exact locked_on_ell_A | exact locked_on_ell_B].
Qed.

Lemma locked_mkellipse_empty_not_hit :
  forall p ti tj,
    ~ I_ok (MkEllipse locked_ell_A) (MkEllipse locked_ell_C) (IHit p ti tj).
Proof.
  intros p ti tj [HA HC].
  apply locked_ell_A_C_disjoint. exists p, ti, tj. split; assumption.
Qed.

Lemma mkellipse_pair_not_decline :
  forall e1 e2, ~ I_ok (MkEllipse e1) (MkEllipse e2) IDecline.
Proof.
  intros e1 e2 H. exact H.
Qed.

Definition locked_mkellipse_hit : IResult :=
  IHit locked_ell_hit_pt locked_ell_ti locked_ell_tj.

Definition cooked_mkellipse : CookedPair :=
  cook_hit_ellipses locked_ell_ck1 locked_ell_ck2
    locked_ell_A locked_ell_B locked_ell_ti locked_ell_tj
    crossing_hen.

Lemma cook_hit_ellipses_shares_hen :
  forall c1 c2 e1 e2 ti tj h,
    cooked_shares_hen (cook_hit_ellipses c1 c2 e1 e2 ti tj h).
Proof.
  intros. repeat split; reflexivity.
Qed.

Lemma cooked_mkellipse_shares :
  cooked_shares_hen cooked_mkellipse.
Proof.
  apply cook_hit_ellipses_shares_hen.
Qed.

Lemma cooked_mkellipse_try :
  try_cook_hit locked_ell_ck1 locked_ell_ck2
    locked_mkellipse_hit crossing_hen = Some cooked_mkellipse.
Proof.
  reflexivity.
Qed.

Lemma cooked_mkellipse_children_are_ellipse :
  egg_class (ck_egg (cp_left1 cooked_mkellipse)) = EggEllipse /\
  egg_class (ck_egg (cp_right1 cooked_mkellipse)) = EggEllipse /\
  egg_class (ck_egg (cp_left2 cooked_mkellipse)) = EggEllipse /\
  egg_class (ck_egg (cp_right2 cooked_mkellipse)) = EggEllipse.
Proof.
  repeat split; reflexivity.
Qed.

(* The four minted children all meet at the Hit point. *)
Lemma cooked_mkellipse_join :
  ell_eval (fst (ell_split locked_ell_A locked_ell_ti)) 1 = locked_ell_hit_pt /\
  ell_eval (snd (ell_split locked_ell_A locked_ell_ti)) 0 = locked_ell_hit_pt /\
  ell_eval (fst (ell_split locked_ell_B locked_ell_tj)) 1 = locked_ell_hit_pt /\
  ell_eval (snd (ell_split locked_ell_B locked_ell_tj)) 0 = locked_ell_hit_pt.
Proof.
  destruct (ell_split_join locked_ell_A locked_ell_ti) as [Ha1 Ha2].
  destruct (ell_split_join locked_ell_B locked_ell_tj) as [Hb1 Hb2].
  rewrite Ha1, Ha2, Hb1, Hb2, locked_ell_A_at_ti, locked_ell_B_at_tj.
  repeat split; reflexivity.
Qed.

Lemma interpolant_pair_mkellipse :
  interpolant_pair (MkEllipse locked_ell_A) (MkEllipse locked_ell_B).
Proof.
  exact I.
Qed.

Lemma mkellipse_tag_still_decline :
  I_ok (MkOutOfScope EggEllipse) (MkOutOfScope EggEllipse) IDecline.
Proof.
  unfold I_ok, interpolant_pair. intro H. exact H.
Qed.

Lemma mkellipse_tag_hit_false :
  forall p ti tj,
    ~ I_ok (MkOutOfScope EggEllipse) (MkOutOfScope EggEllipse)
         (IHit p ti tj).
Proof.
  intros p ti tj H. exact H.
Qed.

Lemma mkellipse_chord_still_decline :
  I_ok (MkChord hor_bot) (MkEllipse locked_ell_A) IDecline.
Proof.
  unfold I_ok, interpolant_pair. intro H. exact H.
Qed.

Lemma mkellipse_circ_still_decline :
  forall c, I_ok (MkEllipse locked_ell_A) (MkCirc c) IDecline.
Proof.
  intros c. unfold I_ok, interpolant_pair. intro H. exact H.
Qed.

Lemma mkellipse_mixed_try_none :
  forall c o h,
    try_cook_hit locked_ell_ck1 (mkChicken 2%nat 3%nat (MkChord c)) o h = None.
Proof.
  intros c o h. destruct o; reflexivity.
Qed.

Lemma ellipse_chord_not_first_cook_scope :
  ~ first_cook_scope EggEllipse EggChord.
Proof.
  intro H. exact H.
Qed.

Lemma ellipse_circular_not_first_cook_scope :
  ~ first_cook_scope EggEllipse EggCircularArc.
Proof.
  intro H. exact H.
Qed.

Lemma mkellipse_neq_tag : forall e, MkEllipse e <> MkOutOfScope EggEllipse.
Proof.
  intros e. discriminate.
Qed.

(* Sinusoid×sinusoid is the next documented out-of-scope pair. *)
Lemma sinusoid_not_first_cook_after_ellipse :
  ~ first_cook_scope EggSinusoid EggSinusoid.
Proof.
  intro H. exact H.
Qed.

(* WITNESS {"claimId":"0007-ellipse-first-cook","topic":"overlay","lemma":"locked_mkellipse_I_ok","title":"Host I_ok Hits two MkEllipse chickens on the locked crossing half-ellipse pair at an interior parameter of both","file":"theories/EllipseCookMkEllipse.v","witness":"0007-ellipse-first-cook","board":"ADR-0007"} *)

(* WITNESS {"claimId":"0007-ellipse-first-cook","topic":"overlay","lemma":"cooked_mkellipse_try","title":"try_cook_hit mints MkEllipse hens on the locked ellipse Hit","file":"theories/EllipseCookMkEllipse.v","witness":"0007-ellipse-first-cook","board":"ADR-0007"} *)

(* WITNESS {"claimId":"0007-ellipse-first-cook","topic":"overlay","lemma":"ticket_0007_ellipse_first_cook_qed_or_qex","title":"Ellipse times ellipse is first cook with a locked MkEllipse IHit that try_cook_hit mints and a locked Empty pair (QED) or ellipse times ellipse stays QEX (QEX); discharged QED; eccentric-anomaly interpolant not endpoint chord; tags and mixed stay Decline; locked pair, not a general ellipse root finder","file":"theories/EllipseCookMkEllipse.v","witness":"0007-ellipse-first-cook","board":"ADR-0007"} *)
Theorem ticket_0007_ellipse_first_cook_qed_or_qex :
  (first_cook_scope EggEllipse EggEllipse /\
   interpolant_pair (MkEllipse locked_ell_A) (MkEllipse locked_ell_B) /\
   I_ok (MkEllipse locked_ell_A) (MkEllipse locked_ell_B)
        (IHit locked_ell_hit_pt locked_ell_ti locked_ell_tj) /\
   I_ok (MkEllipse locked_ell_A) (MkEllipse locked_ell_C) IEmpty /\
   try_cook_hit locked_ell_ck1 locked_ell_ck2
     locked_mkellipse_hit crossing_hen = Some cooked_mkellipse /\
   cooked_shares_hen cooked_mkellipse /\
   egg_class (ck_egg (cp_left1 cooked_mkellipse)) = EggEllipse /\
   I_ok (MkOutOfScope EggEllipse) (MkOutOfScope EggEllipse) IDecline /\
   I_ok (MkChord hor_bot) (MkEllipse locked_ell_A) IDecline /\
   ~ first_cook_scope EggEllipse EggChord /\
   ~ first_cook_scope EggSinusoid EggSinusoid /\
   cook_loop_status = LoopDischarged)
  \/
  (~ first_cook_scope EggEllipse EggEllipse /\
   forall p ti tj,
     ~ I_ok (MkEllipse locked_ell_A) (MkEllipse locked_ell_B)
          (IHit p ti tj)).
Proof.
  left.
  split; [exact ellipse_ellipse_first_cook_scope|].
  split; [exact interpolant_pair_mkellipse|].
  split; [exact locked_mkellipse_I_ok|].
  split; [exact locked_mkellipse_empty_I_ok|].
  split; [exact cooked_mkellipse_try|].
  split; [exact cooked_mkellipse_shares|].
  split; [reflexivity|].
  split; [exact mkellipse_tag_still_decline|].
  split; [exact mkellipse_chord_still_decline|].
  split; [exact ellipse_chord_not_first_cook_scope|].
  split; [exact sinusoid_not_first_cook_after_ellipse|].
  exact cook_loop_is_discharged.
Qed.

Print Assumptions locked_ell_A_eval.
Print Assumptions locked_ell_B_eval.
Print Assumptions locked_ell_C_eval.
Print Assumptions locked_mkellipse_I_ok.
Print Assumptions locked_ell_hit_interior.
Print Assumptions locked_ell_eval_neq_endpoint_chord.
Print Assumptions locked_ell_not_circle.
Print Assumptions locked_ell_A_C_disjoint.
Print Assumptions locked_mkellipse_empty_I_ok.
Print Assumptions locked_mkellipse_hit_not_empty.
Print Assumptions locked_mkellipse_empty_not_hit.
Print Assumptions mkellipse_pair_not_decline.
Print Assumptions cook_hit_ellipses_shares_hen.
Print Assumptions cooked_mkellipse_shares.
Print Assumptions cooked_mkellipse_try.
Print Assumptions cooked_mkellipse_children_are_ellipse.
Print Assumptions cooked_mkellipse_join.
Print Assumptions interpolant_pair_mkellipse.
Print Assumptions mkellipse_tag_still_decline.
Print Assumptions mkellipse_tag_hit_false.
Print Assumptions mkellipse_chord_still_decline.
Print Assumptions mkellipse_circ_still_decline.
Print Assumptions mkellipse_mixed_try_none.
Print Assumptions ellipse_chord_not_first_cook_scope.
Print Assumptions ellipse_circular_not_first_cook_scope.
Print Assumptions mkellipse_neq_tag.
Print Assumptions sinusoid_not_first_cook_after_ellipse.
Print Assumptions ticket_0007_ellipse_first_cook_qed_or_qex.
