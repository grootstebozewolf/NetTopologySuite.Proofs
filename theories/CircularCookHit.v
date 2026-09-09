(* ============================================================================
   NetTopologySuite.Proofs.CircularCookHit
   ----------------------------------------------------------------------------
   Core-slice rung after CircularCook's p* attach: full-circle interpolant
   γ : [0,1] → S and Hit (h*, p*, tᵢ, tⱼ) on the integer seam.

   γ(t) = O + r · (cos(2πt), sin(2πt)).  t is the wrapped atan2 polar
   angle of p* about O.  Hens stay the named radical-root certificates.

   QED: locked (0,0)/(7,0) r=5 Hit carries constructed (h*, p*, tᵢ, tⱼ)
   with γᵢ(tᵢ) = γⱼ(tⱼ) = p* and t ∈ [0,1].  Kiss Touch carries t too.
   I.2: ∀ Hit soundness off that lock — I_circles_gamma = Hit iff
   proper discriminant and on_full_circle on both radical roots
   (γ_full, not CircularArc span). R3 is the locked witness.
   QEX: CircularArc still has no γ / (tᵢ, tⱼ) — CircGamma stays QEX;
   do not fake Discharge.  first_cook_scope stays chord–chord.

   Not glossary 𝓘 for CircularArc eggs.  Not a noder.  Not OverlayNGCurve
   / #857 / fully_intersected / ticket 523.  Not chord-lane constructed 𝓘.
   Not I.3 / I.8–I.10 / Campaign II / H⊥ / a CRV-TOUCH kiss procedure.

   WITNESS topic: core · claimId: 64-circ-hit-params / 0007
   witness: 64-i-circular-locked / 0007-I.2-hit-sound
   board: ADR-0007
   4-axiom (atan2 / Classical_Prop.classic). No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   ========================================================================== *)

From Stdlib Require Import ZArith Reals Lra Lia.
From NTS.Proofs Require Import Distance SheetHenCook ArcArcCircles
  Atan2 AngleBetween CircularCookZ CircularCook.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Full-circle interpolant γ : [0,1] → S and its polar parameter.             *)
(* -------------------------------------------------------------------------- *)

Definition circ_gamma (O : Point) (r t : R) : Point :=
  mkPoint (px O + r * cos (2 * PI * t))
          (py O + r * sin (2 * PI * t)).

Definition circ_angle (O P : Point) : R :=
  atan2 (py P - py O) (px P - px O).

Definition circ_t (O P : Point) : R :=
  let th := circ_angle O P in
  if Rle_dec 0 th then th / (2 * PI) else (th + 2 * PI) / (2 * PI).

Definition on_full_circle (O : Point) (r t : R) (p : Point) : Prop :=
  0 <= t <= 1 /\ p = circ_gamma O r t.

Lemma two_PI_pos : 0 < 2 * PI.
Proof.
  pose proof PI_RGT_0. lra.
Qed.

Lemma cos_plus_2PI : forall t, cos (t + 2 * PI) = cos t.
Proof.
  intros t. rewrite cos_plus, cos_2PI, sin_2PI. ring.
Qed.

Lemma sin_plus_2PI : forall t, sin (t + 2 * PI) = sin t.
Proof.
  intros t. rewrite sin_plus, cos_2PI, sin_2PI. ring.
Qed.

Lemma circ_delta_sq : forall O P,
  (px P - px O) * (px P - px O) + (py P - py O) * (py P - py O)
  = dist_sq O P.
Proof.
  intros O P. unfold dist_sq. ring.
Qed.

Lemma circ_point_ne_of_on_circle : forall O P r,
  0 < r ->
  dist_sq O P = r * r ->
  ~ (px P - px O = 0 /\ py P - py O = 0).
Proof.
  intros O P r Hr Heq [Hx Hy].
  assert (H0 : dist_sq O P = 0).
  { unfold dist_sq.
    replace (px O - px P) with (- (px P - px O)) by ring.
    replace (py O - py P) with (- (py P - py O)) by ring.
    rewrite Hx, Hy. ring. }
  rewrite H0 in Heq.
  symmetry in Heq.
  apply sqr_eq_zero in Heq. lra.
Qed.

Lemma circ_radius_sqrt : forall O P r,
  0 < r ->
  dist_sq O P = r * r ->
  sqrt ((px P - px O) * (px P - px O) + (py P - py O) * (py P - py O)) = r.
Proof.
  intros O P r Hr Heq.
  rewrite circ_delta_sq, Heq.
  change (r * r) with (Rsqr r).
  apply sqrt_Rsqr. lra.
Qed.

(* Polar retract: a point on the circle is γ(circ_t O P). *)
Lemma circ_gamma_retract : forall O P r,
  0 < r ->
  dist_sq O P = r * r ->
  circ_gamma O r (circ_t O P) = P.
Proof.
  intros O P r Hr Heq.
  set (x := px P - px O).
  set (y := py P - py O).
  assert (Hxy : ~ (x = 0 /\ y = 0))
    by (apply (circ_point_ne_of_on_circle O P r Hr Heq)).
  pose proof (atan2_on_circle x y Hxy) as [Hc Hs].
  pose proof (circ_radius_sqrt O P r Hr Heq) as Hsr.
  fold x y in Hsr. rewrite Hsr in Hc, Hs.
  unfold circ_gamma, circ_t, circ_angle. fold x y.
  pose proof PI_RGT_0 as HPI.
  destruct (Rle_dec 0 (atan2 y x)) as [_|Hth].
  - replace (2 * PI * (atan2 y x / (2 * PI))) with (atan2 y x)
      by (field; lra).
    apply point_eq_of_coords; cbn [px py].
    + rewrite Hc. unfold x. ring.
    + rewrite Hs. unfold y. ring.
  - replace (2 * PI * ((atan2 y x + 2 * PI) / (2 * PI)))
      with (atan2 y x + 2 * PI)
      by (field; lra).
    rewrite cos_plus_2PI, sin_plus_2PI.
    apply point_eq_of_coords; cbn [px py].
    + rewrite Hc. unfold x. ring.
    + rewrite Hs. unfold y. ring.
Qed.

Lemma circ_t_range : forall O P,
  ~ (px P - px O = 0 /\ py P - py O = 0) ->
  0 <= circ_t O P < 1.
Proof.
  intros O P Hne.
  set (x := px P - px O) in *.
  set (y := py P - py O) in *.
  pose proof (atan2_range x y Hne) as Hrng.
  pose proof two_PI_pos as H2.
  pose proof PI_RGT_0 as HPI.
  assert (Hinv : 0 < / (2 * PI)) by (apply Rinv_0_lt_compat; exact H2).
  unfold circ_t, circ_angle, Rdiv. fold x y.
  set (th := atan2 y x) in *.
  destruct (Rle_dec 0 th) as [Hth|Hth].
  - split.
    + apply Rmult_le_pos; [exact Hth | apply Rlt_le, Hinv].
    + apply (Rmult_lt_reg_r (2 * PI)); [exact H2|].
      replace (th * / (2 * PI) * (2 * PI)) with th by (field; lra).
      lra.
  - split.
    + apply Rmult_le_pos; [lra | apply Rlt_le, Hinv].
    + apply (Rmult_lt_reg_r (2 * PI)); [exact H2|].
      replace ((th + 2 * PI) * / (2 * PI) * (2 * PI))
        with (th + 2 * PI) by (field; lra).
      lra.
Qed.

Lemma circ_t_in_unit : forall O P r,
  0 < r ->
  dist_sq O P = r * r ->
  0 <= circ_t O P <= 1.
Proof.
  intros O P r Hr Heq.
  pose proof (circ_t_range O P (circ_point_ne_of_on_circle O P r Hr Heq))
    as [Hlo Hhi].
  lra.
Qed.

Lemma on_full_circle_of_retract : forall O P r,
  0 < r ->
  dist_sq O P = r * r ->
  on_full_circle O r (circ_t O P) P.
Proof.
  intros O P r Hr Heq.
  split.
  - exact (circ_t_in_unit O P r Hr Heq).
  - symmetry. exact (circ_gamma_retract O P r Hr Heq).
Qed.

(* -------------------------------------------------------------------------- *)
(* Full-circle Hit with constructed (h*, p*, tᵢ, tⱼ). CircGamma / CircularArc *)
(* interpolant stays QEX — this is not glossary 𝓘 for arc eggs.               *)
(* -------------------------------------------------------------------------- *)

Inductive ICircG : Type :=
| ICircGHit (h_plus : Hen) (p_plus : Point) (ti_plus tj_plus : R)
            (h_minus : Hen) (p_minus : Point) (ti_minus tj_minus : R)
| ICircGEmpty
| ICircGTouch (h : Hen) (p : Point) (ti tj : R)
| ICircGDecline.

Definition I_circles_gamma (o1x o1y r1 o2x o2y r2 : Z) : ICircG :=
  let O1 := zpt o1x o1y in
  let O2 := zpt o2x o2y in
  match I_circles_on_z_sheet o1x o1y r1 o2x o2y r2 with
  | ICircHit hp pp hm pm =>
      ICircGHit hp pp (circ_t O1 pp) (circ_t O2 pp)
                hm pm (circ_t O1 pm) (circ_t O2 pm)
  | ICircEmpty => ICircGEmpty
  | ICircTouch h p =>
      ICircGTouch h p (circ_t O1 p) (circ_t O2 p)
  | ICircDecline => ICircGDecline
  end.

Lemma ICircGEmpty_neq_ICircGDecline : ICircGEmpty <> ICircGDecline.
Proof.
  discriminate.
Qed.

Lemma ICircGTouch_neq_ICircGHit :
  forall h p ti tj hp pp tip tjp hm pm tim tjm,
    ICircGTouch h p ti tj <>
    ICircGHit hp pp tip tjp hm pm tim tjm.
Proof.
  intros. discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked fixture (0,0)/(7,0) r=5 — same witness as 64-i-circular-locked.     *)
(* -------------------------------------------------------------------------- *)

Definition locked_O1 : Point := mkPoint 0 0.
Definition locked_O2 : Point := mkPoint 7 0.
Definition locked_r : R := 5.
Definition locked_p_plus : Point :=
  radical_point_plus locked_O1 locked_O2 locked_r locked_r.
Definition locked_p_minus : Point :=
  radical_point_minus locked_O1 locked_O2 locked_r locked_r.

Lemma locked_centers_dist : dist locked_O1 locked_O2 = 7.
Proof.
  unfold locked_O1, locked_O2, dist, dist_sq. cbn [px py].
  replace ((0 - 7) * (0 - 7) + (0 - 0) * (0 - 0)) with (Rsqr 7)
    by (unfold Rsqr; ring).
  apply sqrt_Rsqr. lra.
Qed.

Lemma locked_circles_proper :
  0 < locked_r /\
  0 < dist locked_O1 locked_O2 /\
  Rabs (locked_r - locked_r) < dist locked_O1 locked_O2 /\
  dist locked_O1 locked_O2 < locked_r + locked_r.
Proof.
  rewrite locked_centers_dist. unfold locked_r.
  replace (5 - 5) with 0 by ring. rewrite Rabs_R0. lra.
Qed.

Lemma locked_radical_on_circles :
  dist_sq locked_O1 locked_p_plus = locked_r * locked_r /\
  dist_sq locked_O2 locked_p_plus = locked_r * locked_r /\
  dist_sq locked_O1 locked_p_minus = locked_r * locked_r /\
  dist_sq locked_O2 locked_p_minus = locked_r * locked_r.
Proof.
  unfold locked_p_plus, locked_p_minus.
  destruct locked_circles_proper as [Hr [Hd [Habs Hlt]]].
  pose proof (radical_points_on_circles locked_O1 locked_O2
                locked_r locked_r Hr Hr Hd Habs Hlt)
    as [[Hp1 Hp2] [Hm1 Hm2]].
  repeat split; assumption.
Qed.

(* WITNESS {"claimId":"64-circ-hit-params","topic":"core","lemma":"locked_I_circles_gamma_hit","title":"Locked (0,0)/(7,0) r=5 Hit carries hens and constructed (t_i, t_j)","file":"theories/CircularCookHit.v","witness":"64-i-circular-locked","board":"ADR-0007"} *)

Lemma locked_I_circles_gamma_hit :
  I_circles_gamma 0 0 5 7 0 5 =
  ICircGHit hen_plus locked_p_plus
    (circ_t locked_O1 locked_p_plus) (circ_t locked_O2 locked_p_plus)
    hen_minus locked_p_minus
    (circ_t locked_O1 locked_p_minus) (circ_t locked_O2 locked_p_minus).
Proof.
  unfold I_circles_gamma, locked_p_plus, locked_p_minus, locked_O1, locked_O2,
         locked_r.
  rewrite locked_I_circles_on_z_sheet_hit.
  rewrite zpt_00, zpt_70.
  reflexivity.
Qed.

Lemma locked_hit_plus_on_gamma :
  on_full_circle locked_O1 locked_r
    (circ_t locked_O1 locked_p_plus) locked_p_plus /\
  on_full_circle locked_O2 locked_r
    (circ_t locked_O2 locked_p_plus) locked_p_plus.
Proof.
  destruct locked_radical_on_circles as [H1 [H2 _]].
  split.
  - apply on_full_circle_of_retract; [unfold locked_r; lra|exact H1].
  - apply on_full_circle_of_retract; [unfold locked_r; lra|exact H2].
Qed.

Lemma locked_hit_minus_on_gamma :
  on_full_circle locked_O1 locked_r
    (circ_t locked_O1 locked_p_minus) locked_p_minus /\
  on_full_circle locked_O2 locked_r
    (circ_t locked_O2 locked_p_minus) locked_p_minus.
Proof.
  destruct locked_radical_on_circles as [_ [_ [H1 H2]]].
  split.
  - apply on_full_circle_of_retract; [unfold locked_r; lra|exact H1].
  - apply on_full_circle_of_retract; [unfold locked_r; lra|exact H2].
Qed.

Lemma locked_I_circles_gamma_empty :
  I_circles_gamma 0 0 5 20 0 5 = ICircGEmpty.
Proof.
  unfold I_circles_gamma. rewrite locked_I_circles_empty. reflexivity.
Qed.

Lemma locked_I_circles_gamma_decline :
  I_circles_gamma 0 0 5 0 0 5 = ICircGDecline.
Proof.
  unfold I_circles_gamma. rewrite locked_I_circles_decline. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked external kiss (0,0)/(10,0) r=5: Touch with constructed t.           *)
(* -------------------------------------------------------------------------- *)

Definition kiss_O2 : Point := mkPoint 10 0.
Definition kiss_p : Point :=
  radical_point_plus locked_O1 kiss_O2 locked_r locked_r.

Lemma kiss_centers_dist : dist locked_O1 kiss_O2 = 10.
Proof.
  unfold locked_O1, kiss_O2, dist, dist_sq. cbn [px py].
  replace ((0 - 10) * (0 - 10) + (0 - 0) * (0 - 0)) with (Rsqr 10)
    by (unfold Rsqr; ring).
  apply sqrt_Rsqr. lra.
Qed.

Lemma kiss_radical_a :
  radical_axis_a locked_O1 kiss_O2 locked_r locked_r = 5.
Proof.
  unfold radical_axis_a, locked_r.
  rewrite kiss_centers_dist. field.
Qed.

Lemma kiss_radical_ux : radical_axis_ux locked_O1 kiss_O2 = 1.
Proof.
  unfold radical_axis_ux. rewrite kiss_centers_dist.
  unfold locked_O1, kiss_O2. cbn [px py]. field.
Qed.

Lemma kiss_radical_uy : radical_axis_uy locked_O1 kiss_O2 = 0.
Proof.
  unfold radical_axis_uy. rewrite kiss_centers_dist.
  unfold locked_O1, kiss_O2. cbn [px py]. field.
Qed.

Lemma kiss_radical_h : radical_axis_h locked_O1 kiss_O2 locked_r locked_r = 0.
Proof.
  unfold radical_axis_h. rewrite kiss_radical_a. unfold locked_r.
  replace (5 * 5 - 5 * 5) with 0 by ring. apply sqrt_0.
Qed.

Lemma kiss_p_eq_50 : kiss_p = mkPoint 5 0.
Proof.
  unfold kiss_p, radical_point_plus.
  rewrite kiss_radical_a, kiss_radical_h, kiss_radical_ux, kiss_radical_uy.
  unfold locked_O1. cbn [px py].
  apply point_eq_of_coords; cbn [px py]; ring.
Qed.

Lemma kiss_p_on_circles :
  dist_sq locked_O1 kiss_p = locked_r * locked_r /\
  dist_sq kiss_O2 kiss_p = locked_r * locked_r.
Proof.
  rewrite kiss_p_eq_50. unfold locked_O1, kiss_O2, locked_r, dist_sq.
  cbn [px py]. split; field.
Qed.

Lemma locked_I_circles_gamma_touch :
  I_circles_gamma 0 0 5 10 0 5 =
  ICircGTouch hen_plus kiss_p
    (circ_t locked_O1 kiss_p) (circ_t kiss_O2 kiss_p).
Proof.
  unfold I_circles_gamma, kiss_p, locked_O1, kiss_O2, locked_r.
  rewrite locked_I_circles_touch.
  rewrite zpt_00.
  unfold zpt. reflexivity.
Qed.

Lemma locked_touch_on_gamma :
  on_full_circle locked_O1 locked_r (circ_t locked_O1 kiss_p) kiss_p /\
  on_full_circle kiss_O2 locked_r (circ_t kiss_O2 kiss_p) kiss_p.
Proof.
  destruct kiss_p_on_circles as [H1 H2].
  split.
  - apply on_full_circle_of_retract; [unfold locked_r; lra|exact H1].
  - apply on_full_circle_of_retract; [unfold locked_r; lra|exact H2].
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked internal kiss (0,0) r=5 vs (3,0) r=2: Touch with constructed t.     *)
(* Mirrors CircularCook.locked_I_circles_internal_kiss.                       *)
(* -------------------------------------------------------------------------- *)

Definition ikiss_O2 : Point := mkPoint 3 0.
Definition ikiss_r2 : R := 2.
Definition ikiss_p : Point :=
  radical_point_plus locked_O1 ikiss_O2 locked_r ikiss_r2.

Lemma ikiss_centers_dist : dist locked_O1 ikiss_O2 = 3.
Proof.
  unfold locked_O1, ikiss_O2, dist, dist_sq. cbn [px py].
  replace ((0 - 3) * (0 - 3) + (0 - 0) * (0 - 0)) with (Rsqr 3)
    by (unfold Rsqr; ring).
  apply sqrt_Rsqr. lra.
Qed.

Lemma ikiss_radical_a :
  radical_axis_a locked_O1 ikiss_O2 locked_r ikiss_r2 = 5.
Proof.
  unfold radical_axis_a, locked_r, ikiss_r2.
  rewrite ikiss_centers_dist. field.
Qed.

Lemma ikiss_radical_ux : radical_axis_ux locked_O1 ikiss_O2 = 1.
Proof.
  unfold radical_axis_ux. rewrite ikiss_centers_dist.
  unfold locked_O1, ikiss_O2. cbn [px py]. field.
Qed.

Lemma ikiss_radical_uy : radical_axis_uy locked_O1 ikiss_O2 = 0.
Proof.
  unfold radical_axis_uy. rewrite ikiss_centers_dist.
  unfold locked_O1, ikiss_O2. cbn [px py]. field.
Qed.

Lemma ikiss_radical_h :
  radical_axis_h locked_O1 ikiss_O2 locked_r ikiss_r2 = 0.
Proof.
  unfold radical_axis_h. rewrite ikiss_radical_a.
  unfold locked_r. replace (5 * 5 - 5 * 5) with 0 by ring. apply sqrt_0.
Qed.

Lemma ikiss_p_eq_50 : ikiss_p = mkPoint 5 0.
Proof.
  unfold ikiss_p, radical_point_plus.
  rewrite ikiss_radical_a, ikiss_radical_h, ikiss_radical_ux, ikiss_radical_uy.
  unfold locked_O1. cbn [px py].
  apply point_eq_of_coords; cbn [px py]; ring.
Qed.

Lemma ikiss_p_on_circles :
  dist_sq locked_O1 ikiss_p = locked_r * locked_r /\
  dist_sq ikiss_O2 ikiss_p = ikiss_r2 * ikiss_r2.
Proof.
  rewrite ikiss_p_eq_50. unfold locked_O1, ikiss_O2, locked_r, ikiss_r2, dist_sq.
  cbn [px py]. split; field.
Qed.

Lemma locked_I_circles_gamma_internal_kiss :
  I_circles_gamma 0 0 5 3 0 2 =
  ICircGTouch hen_plus ikiss_p
    (circ_t locked_O1 ikiss_p) (circ_t ikiss_O2 ikiss_p).
Proof.
  unfold I_circles_gamma, ikiss_p, locked_O1, ikiss_O2, locked_r, ikiss_r2.
  rewrite locked_I_circles_internal_kiss.
  rewrite zpt_00.
  unfold zpt. reflexivity.
Qed.

Lemma locked_internal_kiss_on_gamma :
  on_full_circle locked_O1 locked_r (circ_t locked_O1 ikiss_p) ikiss_p /\
  on_full_circle ikiss_O2 ikiss_r2 (circ_t ikiss_O2 ikiss_p) ikiss_p.
Proof.
  destruct ikiss_p_on_circles as [H1 H2].
  split.
  - apply on_full_circle_of_retract; [unfold locked_r; lra|exact H1].
  - apply on_full_circle_of_retract; [unfold ikiss_r2; lra|exact H2].
Qed.

(* -------------------------------------------------------------------------- *)
(* CircGamma stays QEX — CircularArc still has no γ. Honest; not Discharge.   *)
(* -------------------------------------------------------------------------- *)

Lemma circular_gamma_still_qex :
  circular_gamma_status = CircGammaQEX.
Proof.
  exact circular_gamma_is_qex.
Qed.

Lemma circular_still_not_first_cook_scope :
  ~ first_cook_scope EggCircularArc EggCircularArc.
Proof.
  exact circular_not_first_cook_scope.
Qed.

(* CircGamma QEX ticket lives in CircularCook.v (3-axiom stamp).
   This module owns the QED Hit-params ticket only. *)

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"64-circ-hit-params","topic":"core","lemma":"ticket_64_circ_hit_params_qed_or_qex","title":"Locked full-circle Hit carries (h*, p*, t_i, t_j) with gamma(t)=p* (QED) or the attach fails (QEX); discharged QED","file":"theories/CircularCookHit.v","witness":"64-i-circular-locked","board":"ADR-0007"} *)

Theorem ticket_64_circ_hit_params_qed_or_qex :
  (I_circles_gamma 0 0 5 7 0 5 =
     ICircGHit hen_plus locked_p_plus
       (circ_t locked_O1 locked_p_plus) (circ_t locked_O2 locked_p_plus)
       hen_minus locked_p_minus
       (circ_t locked_O1 locked_p_minus) (circ_t locked_O2 locked_p_minus)
   /\ on_full_circle locked_O1 locked_r
        (circ_t locked_O1 locked_p_plus) locked_p_plus
   /\ on_full_circle locked_O2 locked_r
        (circ_t locked_O2 locked_p_plus) locked_p_plus
   /\ on_full_circle locked_O1 locked_r
        (circ_t locked_O1 locked_p_minus) locked_p_minus
   /\ on_full_circle locked_O2 locked_r
        (circ_t locked_O2 locked_p_minus) locked_p_minus)
  \/
  I_circles_gamma 0 0 5 7 0 5 = ICircGDecline.
Proof.
  left.
  split; [exact locked_I_circles_gamma_hit|].
  destruct locked_hit_plus_on_gamma as [Hp1 Hp2].
  destruct locked_hit_minus_on_gamma as [Hm1 Hm2].
  refine (conj Hp1 (conj Hp2 (conj Hm1 Hm2))).
Qed.

Print Assumptions circ_gamma_retract.
Print Assumptions locked_I_circles_gamma_hit.
Print Assumptions locked_hit_plus_on_gamma.
Print Assumptions locked_touch_on_gamma.
Print Assumptions locked_I_circles_gamma_internal_kiss.
Print Assumptions locked_internal_kiss_on_gamma.
Print Assumptions ticket_64_circ_hit_params_qed_or_qex.
Print Assumptions ICircGEmpty_neq_ICircGDecline.
Print Assumptions ICircGTouch_neq_ICircGHit.

(* -------------------------------------------------------------------------- *)
(* I.2 ∀ Hit soundness. Drop the lock; keep γ_full. Both radical roots.       *)
(* Not CircularArc span membership. CircGamma stays QEX. R3 is the locked     *)
(* (0,0)/(7,0) r=5 witness above.                                             *)
(* -------------------------------------------------------------------------- *)

Definition proper_circ_disc (o1x o1y r1 o2x o2y r2 : Z) : Prop :=
  (0 < r1)%Z /\ (0 < r2)%Z /\
  (circ_diff2 r1 r2 < circ_d2 o1x o1y o2x o2y)%Z /\
  (circ_d2 o1x o1y o2x o2y < circ_sum2 r1 r2)%Z.

Definition gamma_p_plus (o1x o1y r1 o2x o2y r2 : Z) : Point :=
  radical_point_plus (zpt o1x o1y) (zpt o2x o2y) (IZR r1) (IZR r2).

Definition gamma_p_minus (o1x o1y r1 o2x o2y r2 : Z) : Point :=
  radical_point_minus (zpt o1x o1y) (zpt o2x o2y) (IZR r1) (IZR r2).

Definition I_circles_gamma_hit_val (o1x o1y r1 o2x o2y r2 : Z) : ICircG :=
  let O1 := zpt o1x o1y in
  let O2 := zpt o2x o2y in
  let pp := gamma_p_plus o1x o1y r1 o2x o2y r2 in
  let pm := gamma_p_minus o1x o1y r1 o2x o2y r2 in
  ICircGHit hen_plus pp (circ_t O1 pp) (circ_t O2 pp)
            hen_minus pm (circ_t O1 pm) (circ_t O2 pm).

Definition on_full_circle_both_roots
  (o1x o1y r1 o2x o2y r2 : Z) : Prop :=
  let O1 := zpt o1x o1y in
  let O2 := zpt o2x o2y in
  let R1 := IZR r1 in
  let R2 := IZR r2 in
  let pp := gamma_p_plus o1x o1y r1 o2x o2y r2 in
  let pm := gamma_p_minus o1x o1y r1 o2x o2y r2 in
  on_full_circle O1 R1 (circ_t O1 pp) pp /\
  on_full_circle O2 R2 (circ_t O2 pp) pp /\
  on_full_circle O1 R1 (circ_t O1 pm) pm /\
  on_full_circle O2 R2 (circ_t O2 pm) pm.

Lemma I_circles_gamma_eq_hit_val :
  forall o1x o1y r1 o2x o2y r2,
    I_circles_gamma o1x o1y r1 o2x o2y r2 =
      I_circles_gamma_hit_val o1x o1y r1 o2x o2y r2
    <->
    I_circles_z o1x o1y r1 o2x o2y r2 = IZHit hen_plus hen_minus.
Proof.
  intros o1x o1y r1 o2x o2y r2.
  unfold I_circles_gamma, I_circles_gamma_hit_val, I_circles_on_z_sheet,
         gamma_p_plus, gamma_p_minus.
  destruct (I_circles_z o1x o1y r1 o2x o2y r2) as [hp hm | | h | ] eqn:Hz.
  - split.
    + intros Heq. inversion Heq. subst. reflexivity.
    + intros Heq. inversion Heq. subst. reflexivity.
  - split; discriminate.
  - split; discriminate.
  - split; discriminate.
Qed.

Lemma sq_monotone_nonneg_lt : forall x y,
  0 <= x -> 0 <= y -> (x < y <-> x * x < y * y).
Proof.
  intros x y Hx Hy.
  split; intros H.
  - apply Rmult_le_0_lt_compat; lra.
  - destruct (Rle_or_lt y x) as [Hle | Hlt].
    + exfalso.
      assert (y * y <= x * x) by (apply Rmult_le_compat; lra).
      lra.
    + exact Hlt.
Qed.

Lemma zpt_dist_sq :
  forall o1x o1y o2x o2y,
    dist_sq (zpt o1x o1y) (zpt o2x o2y) = IZR (circ_d2 o1x o1y o2x o2y).
Proof.
  intros o1x o1y o2x o2y.
  unfold dist_sq, zpt, circ_d2. cbn [px py].
  rewrite <- !minus_IZR, <- !mult_IZR, <- plus_IZR.
  apply f_equal.
  lia.
Qed.

Lemma IZR_circ_sum2 :
  forall r1 r2,
    IZR (circ_sum2 r1 r2) = (IZR r1 + IZR r2) * (IZR r1 + IZR r2).
Proof.
  intros r1 r2.
  unfold circ_sum2.
  rewrite mult_IZR, plus_IZR.
  reflexivity.
Qed.

Lemma IZR_circ_diff2 :
  forall r1 r2,
    IZR (circ_diff2 r1 r2) = (IZR r1 - IZR r2) * (IZR r1 - IZR r2).
Proof.
  intros r1 r2.
  unfold circ_diff2.
  rewrite mult_IZR, minus_IZR.
  reflexivity.
Qed.

Lemma proper_circ_disc_lifts :
  forall o1x o1y r1 o2x o2y r2,
    proper_circ_disc o1x o1y r1 o2x o2y r2 ->
    0 < IZR r1 /\
    0 < IZR r2 /\
    0 < dist (zpt o1x o1y) (zpt o2x o2y) /\
    Rabs (IZR r1 - IZR r2) < dist (zpt o1x o1y) (zpt o2x o2y) /\
    dist (zpt o1x o1y) (zpt o2x o2y) < IZR r1 + IZR r2.
Proof.
  intros o1x o1y r1 o2x o2y r2 [Hr1 [Hr2 [Hdiff Hsum]]].
  assert (Hr1R : 0 < IZR r1) by (apply IZR_lt; exact Hr1).
  assert (Hr2R : 0 < IZR r2) by (apply IZR_lt; exact Hr2).
  assert (Hd2pos : (0 < circ_d2 o1x o1y o2x o2y)%Z).
  { pose proof (Z.square_nonneg (r1 - r2)) as Hnn.
    unfold circ_diff2 in Hdiff. lia.
  }
  assert (Hdsq : dist_sq (zpt o1x o1y) (zpt o2x o2y) =
                   IZR (circ_d2 o1x o1y o2x o2y))
    by apply zpt_dist_sq.
  assert (Hdsq_pos : 0 < dist_sq (zpt o1x o1y) (zpt o2x o2y)).
  { rewrite Hdsq. apply IZR_lt. exact Hd2pos. }
  assert (Hdpos : 0 < dist (zpt o1x o1y) (zpt o2x o2y)).
  { unfold dist. apply sqrt_lt_R0. exact Hdsq_pos. }
  assert (HsumR : 0 < IZR r1 + IZR r2) by lra.
  assert (Habsnn : 0 <= Rabs (IZR r1 - IZR r2)) by apply Rabs_pos.
  assert (Hdnn : 0 <= dist (zpt o1x o1y) (zpt o2x o2y)) by apply dist_nonneg.
  split; [exact Hr1R|].
  split; [exact Hr2R|].
  split; [exact Hdpos|].
  split.
  - apply (sq_monotone_nonneg_lt _ _ Habsnn Hdnn).
    pose proof (Rsqr_abs (IZR r1 - IZR r2)) as Habs2.
    unfold Rsqr in Habs2. rewrite Habs2.
    unfold dist. rewrite sqrt_sqrt by apply dist_sq_nonneg.
    rewrite Hdsq, <- IZR_circ_diff2.
    apply IZR_lt. exact Hdiff.
  - apply (sq_monotone_nonneg_lt _ _ Hdnn (Rlt_le _ _ HsumR)).
    unfold dist. rewrite sqrt_sqrt by apply dist_sq_nonneg.
    rewrite Hdsq, <- IZR_circ_sum2.
    apply IZR_lt. exact Hsum.
Qed.

Lemma on_full_circle_both_of_proper :
  forall o1x o1y r1 o2x o2y r2,
    proper_circ_disc o1x o1y r1 o2x o2y r2 ->
    on_full_circle_both_roots o1x o1y r1 o2x o2y r2.
Proof.
  intros o1x o1y r1 o2x o2y r2 Hdisc.
  destruct (proper_circ_disc_lifts o1x o1y r1 o2x o2y r2 Hdisc)
    as [Hr1 [Hr2 [Hdpos [Habs Hsum]]]].
  unfold on_full_circle_both_roots, gamma_p_plus, gamma_p_minus.
  pose proof (radical_points_on_circles
                (zpt o1x o1y) (zpt o2x o2y) (IZR r1) (IZR r2)
                Hr1 Hr2 Hdpos Habs Hsum)
    as [[Hp1 Hp2] [Hm1 Hm2]].
  repeat split.
  - apply on_full_circle_of_retract; [exact Hr1|exact Hp1].
  - apply on_full_circle_of_retract; [exact Hr2|exact Hp2].
  - apply on_full_circle_of_retract; [exact Hr1|exact Hm1].
  - apply on_full_circle_of_retract; [exact Hr2|exact Hm2].
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"I_circles_gamma_hit_iff","title":"I.2 forall Hit soundness: I_circles_gamma is Hit iff proper discriminant and on_full_circle on both radical roots (gamma_full)","file":"theories/CircularCookHit.v","witness":"0007-I.2-hit-sound","board":"ADR-0007"} *)

Theorem I_circles_gamma_hit_iff :
  forall o1x o1y r1 o2x o2y r2,
    I_circles_gamma o1x o1y r1 o2x o2y r2 =
      I_circles_gamma_hit_val o1x o1y r1 o2x o2y r2
    <->
    proper_circ_disc o1x o1y r1 o2x o2y r2 /\
    on_full_circle_both_roots o1x o1y r1 o2x o2y r2.
Proof.
  intros o1x o1y r1 o2x o2y r2.
  split.
  - intros Hhit.
    apply I_circles_gamma_eq_hit_val in Hhit.
    apply I_circles_z_hit_iff in Hhit.
    split; [exact Hhit|].
    apply on_full_circle_both_of_proper. exact Hhit.
  - intros [Hdisc _].
    apply I_circles_gamma_eq_hit_val.
    apply I_circles_z_hit_iff. exact Hdisc.
Qed.

(* R3: the locked witness inhabits the forall. *)
Lemma i2_recovers_locked_r3 :
  I_circles_gamma 0 0 5 7 0 5 =
    I_circles_gamma_hit_val 0 0 5 7 0 5
  <->
  proper_circ_disc 0 0 5 7 0 5 /\
  on_full_circle_both_roots 0 0 5 7 0 5.
Proof.
  apply I_circles_gamma_hit_iff.
Qed.

Lemma locked_is_gamma_hit_val :
  I_circles_gamma_hit_val 0 0 5 7 0 5 =
  ICircGHit hen_plus locked_p_plus
    (circ_t locked_O1 locked_p_plus) (circ_t locked_O2 locked_p_plus)
    hen_minus locked_p_minus
    (circ_t locked_O1 locked_p_minus) (circ_t locked_O2 locked_p_minus).
Proof.
  unfold I_circles_gamma_hit_val, gamma_p_plus, gamma_p_minus,
         locked_p_plus, locked_p_minus, locked_O1, locked_O2, locked_r.
  rewrite zpt_00, zpt_70.
  reflexivity.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_i2_hit_sound_qed_or_qex","title":"I.2 forall Hit soundness off the lock (QED) or the locked R3 witness declines (QEX); discharged QED; both roots on gamma_full","file":"theories/CircularCookHit.v","witness":"0007-I.2-hit-sound","board":"ADR-0007"} *)

Theorem ticket_0007_i2_hit_sound_qed_or_qex :
  (forall o1x o1y r1 o2x o2y r2,
     I_circles_gamma o1x o1y r1 o2x o2y r2 =
       I_circles_gamma_hit_val o1x o1y r1 o2x o2y r2
     <->
     proper_circ_disc o1x o1y r1 o2x o2y r2 /\
     on_full_circle_both_roots o1x o1y r1 o2x o2y r2)
  \/
  I_circles_gamma 0 0 5 7 0 5 = ICircGDecline.
Proof.
  left.
  exact I_circles_gamma_hit_iff.
Qed.

(* I.2 is γ_full, not CircularArc span membership. CircGamma stays QEX. *)
(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_i2_arc_scope_qed_or_qex","title":"I.2 is arc-span membership (QED) or gamma_full only while CircGamma stays QEX (QEX); discharged QEX; not CircularArc membership","file":"theories/CircularCookHit.v","witness":"0007-I.2-hit-sound","board":"ADR-0007"} *)

Theorem ticket_0007_i2_arc_scope_qed_or_qex :
  (circular_gamma_status = CircGammaDischarged
   /\ first_cook_scope EggCircularArc EggCircularArc)
  \/
  (circular_gamma_status = CircGammaQEX
   /\ ~ first_cook_scope EggCircularArc EggCircularArc).
Proof.
  right.
  split; [exact circular_gamma_is_qex|exact circular_not_first_cook_scope].
Qed.

Print Assumptions I_circles_gamma_hit_iff.
Print Assumptions proper_circ_disc_lifts.
Print Assumptions on_full_circle_both_of_proper.
Print Assumptions i2_recovers_locked_r3.
Print Assumptions ticket_0007_i2_hit_sound_qed_or_qex.
Print Assumptions ticket_0007_i2_arc_scope_qed_or_qex.
