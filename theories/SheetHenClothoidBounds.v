(* ============================================================================
   NetTopologySuite.Proofs.SheetHenClothoidBounds
   ----------------------------------------------------------------------------
   Fresnel integral bounds for the host clothoid. The parameterisation
   is OUR choice, not an ISO formula (stated in SheetHenClothoidCore):
     phi(s) = phi0 + sigma * s^2 / (2 * A^2)
     P(s)   = LOCATION + integral_0^s (cos phi(u), sin phi(u)) du
     gamma(t) = P(sd + t * (ed - sd))
   Normalised form (sigma = +1):
     P = LOCATION + R(phi0) * A * sqrt(pi)
           * (C(s / (A * sqrt(pi))), S(s / (A * sqrt(pi)))).
   This file is Cx, Cy, and the Taylor bounds the fixture uses.
   No Admitted / Axiom / Parameter.
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals RiemannInt Ranalysis1 Rtrigo1 Rtrigo_alt
  Ratan Lra Arith.Factorial.
From Stdlib Require Import Ranalysis_reg.
From NTS.Proofs Require Import SheetHenClothoidCore.
Local Open Scope R_scope.

Definition p1 (t : R) := t.
Definition p2 (t : R) := p1 t * t.
Definition p3 (t : R) := p2 t * t.
Definition p4 (t : R) := p3 t * t.
Definition p5 (t : R) := p4 t * t.
Definition p6 (t : R) := p5 t * t.
Definition p7 (t : R) := p6 t * t.

Lemma d_p1 : forall x, derivable_pt_lim p1 x 1.
Proof. intros x. unfold p1. apply derivable_pt_lim_id. Qed.

Lemma d_p2 : forall x, derivable_pt_lim p2 x (2 * x).
Proof.
  intros x. unfold p2, p1.
  apply derivable_pt_lim_ext with ((id * id)%F).
  - intros z. unfold mult_fct, id. ring.
  - replace (2 * x) with (1 * id x + id x * 1) by (unfold id; ring).
    apply (derivable_pt_lim_mult id id x 1 1); apply derivable_pt_lim_id.
Qed.

Lemma d_p3 : forall x, derivable_pt_lim p3 x (3 * x * x).
Proof.
  intros x. unfold p3.
  apply derivable_pt_lim_ext with ((p2 * id)%F).
  - intros z. unfold mult_fct, id. reflexivity.
  - replace (3 * x * x) with ((2 * x) * id x + p2 x * 1)
      by (unfold id, p2, p1; ring).
    apply (derivable_pt_lim_mult p2 id x (2 * x) 1);
      [apply d_p2 | apply derivable_pt_lim_id].
Qed.

Lemma d_p4 : forall x, derivable_pt_lim p4 x (4 * x * x * x).
Proof.
  intros x. unfold p4.
  apply derivable_pt_lim_ext with ((p3 * id)%F).
  - intros z. unfold mult_fct, id. reflexivity.
  - replace (4 * x * x * x) with ((3 * x * x) * id x + p3 x * 1)
      by (unfold id, p3, p2, p1; ring).
    apply (derivable_pt_lim_mult p3 id x (3 * x * x) 1);
      [apply d_p3 | apply derivable_pt_lim_id].
Qed.

Lemma d_p5 : forall x, derivable_pt_lim p5 x (5 * x * x * x * x).
Proof.
  intros x. unfold p5.
  apply derivable_pt_lim_ext with ((p4 * id)%F).
  - intros z. unfold mult_fct, id. reflexivity.
  - replace (5 * x * x * x * x) with ((4 * x * x * x) * id x + p4 x * 1)
      by (unfold id, p4, p3, p2, p1; ring).
    apply (derivable_pt_lim_mult p4 id x (4 * x * x * x) 1);
      [apply d_p4 | apply derivable_pt_lim_id].
Qed.

Lemma d_p6 : forall x, derivable_pt_lim p6 x (6 * x * x * x * x * x).
Proof.
  intros x. unfold p6.
  apply derivable_pt_lim_ext with ((p5 * id)%F).
  - intros z. unfold mult_fct, id. reflexivity.
  - replace (6 * x * x * x * x * x)
      with ((5 * x * x * x * x) * id x + p5 x * 1)
      by (unfold id, p5, p4, p3, p2, p1; ring).
    apply (derivable_pt_lim_mult p5 id x (5 * x * x * x * x) 1);
      [apply d_p5 | apply derivable_pt_lim_id].
Qed.

Lemma d_p7 : forall x, derivable_pt_lim p7 x (7 * x * x * x * x * x * x).
Proof.
  intros x. unfold p7.
  apply derivable_pt_lim_ext with ((p6 * id)%F).
  - intros z. unfold mult_fct, id. reflexivity.
  - replace (7 * x * x * x * x * x * x)
      with ((6 * x * x * x * x * x) * id x + p6 x * 1)
      by (unfold id, p6, p5, p4, p3, p2, p1; ring).
    apply (derivable_pt_lim_mult p6 id x (6 * x * x * x * x * x) 1);
      [apply d_p6 | apply derivable_pt_lim_id].
Qed.

Lemma d_half_ant : forall x, derivable_pt_lim (fun t => p3 t / 6) x (x * x / 2).
Proof.
  intros x.
  apply derivable_pt_lim_ext with (fun t => p3 t * / 6).
  - intros z. unfold Rdiv. ring.
  - replace (x * x / 2) with ((3 * x * x) * / 6) by field.
    apply derivable_pt_lim_scal_right. apply d_p3.
Qed.

Lemma d_sixth_ant : forall x, derivable_pt_lim (fun t => p7 t / 336) x (p6 x / 48).
Proof.
  intros x.
  apply derivable_pt_lim_ext with (fun t => p7 t * / 336).
  - intros z. unfold Rdiv. ring.
  - replace (p6 x / 48) with ((7 * x * x * x * x * x * x) * / 336).
    + apply derivable_pt_lim_scal_right. apply d_p7.
    + unfold p6, p5, p4, p3, p2, p1. field.
Qed.

Section ClothFTC.
  Variable F d : R -> R.
  Hypothesis Hd : forall x, derivable_pt_lim F x (d x).
  Hypothesis Hcd : forall x, continuity_pt d x.

  Definition cloth_F_pr : derivable F := fun x => exist _ (d x) (Hd x).

  Lemma cloth_F_cont : continuity (derive F cloth_F_pr).
  Proof.
    intro x. unfold derive, derive_pt, cloth_F_pr. simpl. apply Hcd.
  Qed.

  Definition cloth_F_c1 : C1_fun :=
    {| c1 := F; diff0 := cloth_F_pr; cont1 := cloth_F_cont |}.

  Lemma cloth_F_int : forall s, 0 <= s ->
    RInt_cont d Hcd 0 s = F s - F 0.
  Proof.
    intros s Hs.
    pose (prD := RiemannInt_P32 cloth_F_c1 0 s).
    assert (Heq : RInt_cont d Hcd 0 s = RiemannInt prD).
    { unfold RInt_cont.
      destruct (Rle_dec 0 s) as [Hle|Hn]; [|exfalso; apply Hn; exact Hs].
      apply RiemannInt_P18; [exact Hle|].
      intros x _.
      unfold derive, derive_pt, proj1_sig, cloth_F_c1, diff0, cloth_F_pr.
      cbn. exact (eq_refl (d x)). }
    rewrite Heq.
    rewrite (@FTC_Riemann cloth_F_c1 0 s prD).
    unfold cloth_F_c1, c1. reflexivity.
  Qed.
End ClothFTC.

Definition fresnel_angle (u : R) : R := u * u / 2.
Definition sixth_p6 (u : R) : R := p6 u / 48.

Lemma fresnel_angle_cont : forall x, continuity_pt fresnel_angle x.
Proof.
  intro x. unfold fresnel_angle, Rdiv.
  apply continuity_pt_mult.
  - apply continuity_pt_mult; apply cont_id.
  - apply continuity_pt_const. intros a b. reflexivity.
Qed.

Lemma sixth_p6_cont : forall x, continuity_pt sixth_p6 x.
Proof.
  intro x. unfold sixth_p6, Rdiv.
  apply continuity_pt_mult.
  - unfold p6, p5, p4, p3, p2, p1.
    repeat apply continuity_pt_mult; apply cont_id.
  - apply continuity_pt_const. intros a b. reflexivity.
Qed.

Lemma int_fresnel_angle : forall s, 0 <= s ->
  RInt_cont fresnel_angle fresnel_angle_cont 0 s = s * s * s / 6.
Proof.
  intros s Hs.
  rewrite (cloth_F_int (fun t => p3 t / 6) fresnel_angle d_half_ant
             fresnel_angle_cont s Hs).
  unfold p3, p2, p1, fresnel_angle, Rdiv. cbn. ring.
Qed.

Lemma int_sixth_p6 : forall s, 0 <= s ->
  RInt_cont sixth_p6 sixth_p6_cont 0 s = p7 s / 336.
Proof.
  intros s Hs.
  rewrite (cloth_F_int (fun t => p7 t / 336) sixth_p6 d_sixth_ant
             sixth_p6_cont s Hs).
  unfold p7, p6, p5, p4, p3, p2, p1, Rdiv. cbn. ring.
Qed.

Lemma RInt_cont_mono_fun :
  forall f g Hf Hg a b, a <= b ->
    (forall x, a < x < b -> f x <= g x) ->
    RInt_cont f Hf a b <= RInt_cont g Hg a b.
Proof.
  intros f g Hf Hg a b Hab Hle.
  pose (prf := @continuity_implies_RiemannInt f a b Hab (fun x _ => Hf x)).
  pose (prg := @continuity_implies_RiemannInt g a b Hab (fun x _ => Hg x)).
  rewrite (RInt_cont_le f Hf a b Hab prf).
  rewrite (RInt_cont_le g Hg a b Hab prg).
  apply RiemannInt_P19; [exact Hab | exact Hle].
Qed.

Lemma RInt_cont_minus :
  forall f g Hf Hg Hm a b, a <= b ->
    RInt_cont (fun x => f x - g x) Hm a b
      = RInt_cont f Hf a b - RInt_cont g Hg a b.
Proof.
  intros f g Hf Hg Hm a b Hab.
  pose (prf := @continuity_implies_RiemannInt f a b Hab (fun x _ => Hf x)).
  pose (prg := @continuity_implies_RiemannInt g a b Hab (fun x _ => Hg x)).
  pose (prm := @continuity_implies_RiemannInt (fun x => f x - g x) a b Hab
                 (fun x _ => Hm x)).
  rewrite (RInt_cont_le _ Hm a b Hab prm).
  rewrite (RInt_cont_le _ Hf a b Hab prf).
  rewrite (RInt_cont_le _ Hg a b Hab prg).
  pose (prs := @RiemannInt_P10 f g a b (-1) prf prg).
  assert (He : RiemannInt prm = RiemannInt prs).
  { apply RiemannInt_P18; [exact Hab|]. intros x _. unfold fct_cte. ring. }
  rewrite He.
  rewrite (@RiemannInt_P12 f g a b (-1) prf prg prs Hab).
  ring.
Qed.

Lemma three_lt_PI : 3 < PI.
Proof.
  apply (Rmult_lt_reg_r (/ 2)).
  - apply Rinv_0_lt_compat. lra.
  - replace (3 * / 2) with (3 / 2) by field.
    replace (PI * / 2) with (PI / 2) by field.
    exact PI2_3_2.
Qed.

Lemma sin_approx_1 : forall a, sin_approx a 1 = a - a * a * a / 6.
Proof.
  intro a. unfold sin_approx, sin_term. simpl. field.
Qed.

Lemma cos_approx_1 : forall a, cos_approx a 1 = 1 - a * a / 2.
Proof.
  intro a. unfold cos_approx, cos_term. simpl. field.
Qed.

Lemma cos_approx_2 : forall a,
  cos_approx a 2 = 1 - a * a / 2 + a * a * a * a / 24.
Proof.
  intro a. unfold cos_approx, cos_term. simpl. field.
Qed.

Lemma sin_ge_cubic : forall z, 0 <= z <= PI -> z - z * z * z / 6 <= sin z.
Proof.
  intros z Hz.
  destruct (sin_bound z 0 (proj1 Hz) (proj2 Hz)) as [Hb _].
  rewrite sin_approx_1 in Hb. exact Hb.
Qed.

Lemma cos_ge_quad : forall z, - PI / 2 <= z -> z <= PI / 2 ->
  1 - z * z / 2 <= cos z.
Proof.
  intros z Hlo Hhi.
  destruct (cos_bound z 0 Hlo Hhi) as [Hb _].
  rewrite cos_approx_1 in Hb. exact Hb.
Qed.

Lemma cos_le_quart : forall z, - PI / 2 <= z -> z <= PI / 2 ->
  cos z <= 1 - z * z / 2 + z * z * z * z / 24.
Proof.
  intros z Hlo Hhi.
  destruct (cos_bound z 0 Hlo Hhi) as [_ Hb].
  rewrite cos_approx_2 in Hb. exact Hb.
Qed.

Lemma sin_le_arg : forall z, 0 <= z -> sin z <= z.
Proof.
  intros z Hz.
  destruct (Req_dec z 0) as [->|Hne].
  - rewrite sin_0. lra.
  - apply Rlt_le. apply sin_lt_x. lra.
Qed.

Definition fresnel_cx_integrand (u : R) : R := cos (fresnel_angle u).
Definition fresnel_cy_integrand (u : R) : R := sin (fresnel_angle u).
Definition fresnel_low (u : R) : R := fresnel_angle u - sixth_p6 u.

Lemma fresnel_cx_cont : forall x, continuity_pt fresnel_cx_integrand x.
Proof.
  intro x. unfold fresnel_cx_integrand.
  change (continuity_pt (comp cos fresnel_angle) x).
  apply continuity_pt_comp; [apply fresnel_angle_cont | apply continuity_cos].
Qed.

Lemma fresnel_cy_cont : forall x, continuity_pt fresnel_cy_integrand x.
Proof.
  intro x. unfold fresnel_cy_integrand.
  change (continuity_pt (comp sin fresnel_angle) x).
  apply continuity_pt_comp; [apply fresnel_angle_cont | apply continuity_sin].
Qed.

Lemma fresnel_cx_neg_cont :
  forall x, continuity_pt (fun u => - fresnel_cx_integrand u) x.
Proof.
  intro x.
  change (continuity_pt (- fresnel_cx_integrand)%F x).
  apply continuity_pt_opp. apply fresnel_cx_cont.
Qed.

Lemma fresnel_low_cont : forall x, continuity_pt fresnel_low x.
Proof.
  intro x. unfold fresnel_low.
  apply continuity_pt_minus; [apply fresnel_angle_cont | apply sixth_p6_cont].
Qed.

Definition cloth_Cx (s : R) : R :=
  RInt_cont fresnel_cx_integrand fresnel_cx_cont 0 s.

Definition cloth_Cy (s : R) : R :=
  RInt_cont fresnel_cy_integrand fresnel_cy_cont 0 s.

Lemma angle_in_01 : forall u, 0 <= u <= 1 ->
  0 <= fresnel_angle u <= 1 / 2.
Proof.
  intros u Hu. unfold fresnel_angle. nra.
Qed.

Lemma angle_nonneg : forall u, 0 <= u -> 0 <= fresnel_angle u.
Proof.
  intros u Hu. unfold fresnel_angle, Rdiv.
  apply Rmult_le_pos.
  - apply Rmult_le_pos; exact Hu.
  - apply Rlt_le. apply Rinv_0_lt_compat. lra.
Qed.

Lemma angle_le_half_arg : forall u, 0 <= u -> u <= 1 ->
  fresnel_angle u <= 1 / 2.
Proof.
  intros u H0 H1. apply (proj2 (angle_in_01 u (conj H0 H1))).
Qed.

Lemma PI_pos : 0 < PI.
Proof.
  apply Rlt_trans with 3; [lra | exact three_lt_PI].
Qed.

Lemma neg_PI2_eq : - PI / 2 = - (PI / 2).
Proof. field. Qed.

Lemma angle_ge_neg_PI2 : forall u, 0 <= u -> - PI / 2 <= fresnel_angle u.
Proof.
  intros u Hu. apply Rle_trans with 0.
  - pose proof PI_pos. lra.
  - apply angle_nonneg. exact Hu.
Qed.

Lemma sq_le : forall a b, 0 <= a -> a <= b -> a * a <= b * b.
Proof.
  intros a b Ha Hab. apply Rmult_le_compat; assumption.
Qed.

Lemma one_minus_sq_7_8 : forall z, 0 <= z -> z <= 1 / 2 ->
  7 / 8 <= 1 - z * z / 2.
Proof.
  intros z Hz0 Hz.
  assert (Hz2 : z * z <= (1 / 2) * (1 / 2)).
  { apply sq_le; assumption. }
  assert (Hz3 : z * z / 2 <= ((1 / 2) * (1 / 2)) / 2).
  { unfold Rdiv. apply Rmult_le_compat_r; [apply Rlt_le; apply Rinv_0_lt_compat; lra | exact Hz2]. }
  assert (((1 / 2) * (1 / 2)) / 2 = 1 / 8) by field.
  lra.
Qed.

Lemma one_minus_sq_4919 : forall z, 0 <= z -> z <= 9 / 50 ->
  4919 / 5000 <= 1 - z * z / 2.
Proof.
  intros z Hz0 Hz.
  assert (Hz2 : z * z <= (9 / 50) * (9 / 50)).
  { apply sq_le; assumption. }
  assert (Hz3 : z * z / 2 <= ((9 / 50) * (9 / 50)) / 2).
  { unfold Rdiv. apply Rmult_le_compat_r; [apply Rlt_le; apply Rinv_0_lt_compat; lra | exact Hz2]. }
  assert (((9 / 50) * (9 / 50)) / 2 = 81 / 5000) by field.
  lra.
Qed.

Lemma angle_le_9_50 : forall u, 0 <= u -> u <= 3 / 5 ->
  fresnel_angle u <= 9 / 50.
Proof.
  intros u H0 H1.
  unfold fresnel_angle.
  assert (u * u <= (3 / 5) * (3 / 5)).
  { apply sq_le; assumption. }
  assert (u * u / 2 <= ((3 / 5) * (3 / 5)) / 2).
  { unfold Rdiv. apply Rmult_le_compat_r; [apply Rlt_le; apply Rinv_0_lt_compat; lra | exact H]. }
  assert (((3 / 5) * (3 / 5)) / 2 = 9 / 50) by field.
  lra.
Qed.

Lemma half_lt_PI : 1 / 2 < PI.
Proof.
  apply Rlt_trans with 3; [lra | exact three_lt_PI].
Qed.

Lemma half_le_PI2 : 1 / 2 <= PI / 2.
Proof.
  apply Rlt_le. apply Rlt_trans with (3 / 2); [lra | exact PI2_3_2].
Qed.

Lemma cloth_Cx_mono_01 : forall a b, 0 <= a -> a <= b -> b <= 1 ->
  cloth_Cx a <= cloth_Cx b.
Proof.
  intros a b Ha Hab Hb.
  unfold cloth_Cx.
  rewrite (RInt_cont_split0 fresnel_cx_integrand fresnel_cx_cont a b Ha Hab).
  assert (0 <= RInt_cont fresnel_cx_integrand fresnel_cx_cont a b).
  { apply RInt_cont_ge0; [exact Hab|].
    intros x Hx.
    assert (Hx01 : 0 <= x <= 1).
    { destruct Hx as [Hax Hxb]. lra. }
    apply cos_ge_0.
    - rewrite <- neg_PI2_eq. apply angle_ge_neg_PI2. apply (proj1 Hx01).
    - apply Rle_trans with (1 / 2);
        [apply (proj2 (angle_in_01 x Hx01)) | apply half_le_PI2]. }
  lra.
Qed.

Lemma cloth_Cy_mono_01 : forall a b, 0 <= a -> a <= b -> b <= 1 ->
  cloth_Cy a <= cloth_Cy b.
Proof.
  intros a b Ha Hab Hb.
  unfold cloth_Cy.
  rewrite (RInt_cont_split0 fresnel_cy_integrand fresnel_cy_cont a b Ha Hab).
  assert (0 <= RInt_cont fresnel_cy_integrand fresnel_cy_cont a b).
  { apply RInt_cont_ge0; [exact Hab|].
    intros x Hx.
    assert (Hx01 : 0 <= x <= 1).
    { destruct Hx as [Hax Hxb]. lra. }
    apply sin_ge_0.
    - apply (proj1 (angle_in_01 x Hx01)).
    - apply Rle_trans with (1 / 2); [apply (proj2 (angle_in_01 x Hx01)) |].
      apply Rlt_le. apply Rlt_trans with 1; [lra |].
      apply Rlt_trans with 3; [lra | exact three_lt_PI]. }
  lra.
Qed.

Lemma cloth_Cx_le_1 : cloth_Cx 1 <= 1.
Proof.
  unfold cloth_Cx.
  destruct (RInt_cont_bound fresnel_cx_integrand fresnel_cx_cont 0 1 (-1) 1)
    as [_ Hhi].
  - lra.
  - intros x _. destruct (COS_bound (fresnel_angle x)) as [Hlo Hup].
    split; assumption.
  - nra.
Qed.

Lemma cloth_Cx_ge_7_8 : 7 / 8 <= cloth_Cx 1.
Proof.
  unfold cloth_Cx.
  destruct (RInt_cont_bound fresnel_cx_integrand fresnel_cx_cont 0 1 (7 / 8) 1)
    as [Hlo _].
  - lra.
  - intros u Hu.
    assert (Hu01 : 0 <= u <= 1) by (destruct Hu; lra).
    split; [| apply (proj2 (COS_bound (fresnel_angle u)))].
    apply Rle_trans with (1 - fresnel_angle u * fresnel_angle u / 2).
    + apply one_minus_sq_7_8.
      * apply angle_nonneg. apply (proj1 Hu01).
      * apply angle_le_half_arg; [apply (proj1 Hu01) | apply (proj2 Hu01)].
    + apply cos_ge_quad.
      * apply angle_ge_neg_PI2. apply (proj1 Hu01).
      * apply Rle_trans with (1 / 2);
          [apply angle_le_half_arg; [apply (proj1 Hu01) | apply (proj2 Hu01)]
           | apply half_le_PI2].
  - assert (7 / 8 * (1 - 0) = 7 / 8) by field. lra.
Qed.

Lemma cloth_Cy_le_cube : forall s, 0 <= s -> s <= 1 ->
  cloth_Cy s <= s * s * s / 6.
Proof.
  intros s Hs0 Hs1.
  unfold cloth_Cy.
  assert (Hle : RInt_cont fresnel_cy_integrand fresnel_cy_cont 0 s
              <= RInt_cont fresnel_angle fresnel_angle_cont 0 s).
  { apply RInt_cont_mono_fun; [exact Hs0|].
    intros u Hu. unfold fresnel_cy_integrand.
    apply sin_le_arg. apply angle_nonneg. destruct Hu; lra. }
  rewrite int_fresnel_angle in Hle; [|exact Hs0].
  exact Hle.
Qed.

Lemma cloth_Cy_le_sixth : cloth_Cy 1 <= 1 / 6.
Proof.
  replace (1 / 6) with (1 * 1 * 1 / 6) by field.
  apply cloth_Cy_le_cube; lra.
Qed.

Lemma cloth_Cy_three_fifth_le : cloth_Cy (3 / 5) <= 27 / 750.
Proof.
  apply Rle_trans with ((3 / 5) * (3 / 5) * (3 / 5) / 6).
  - apply cloth_Cy_le_cube; lra.
  - nra.
Qed.

Lemma taylor_gap : forall u, fresnel_low u =
  fresnel_angle u - fresnel_angle u * fresnel_angle u * fresnel_angle u / 6.
Proof.
  intro u.
  unfold fresnel_low, fresnel_angle, sixth_p6, p6, p5, p4, p3, p2, p1, Rdiv.
  field.
Qed.

Lemma int_low_1 : RInt_cont fresnel_low fresnel_low_cont 0 1 = 55 / 336.
Proof.
  unfold fresnel_low.
  rewrite (RInt_cont_minus fresnel_angle sixth_p6 fresnel_angle_cont
             sixth_p6_cont fresnel_low_cont 0 1); [|lra].
  rewrite int_fresnel_angle; [|lra].
  rewrite int_sixth_p6; [|lra].
  unfold p7, p6, p5, p4, p3, p2, p1. field.
Qed.

Lemma cloth_Cy_ge_55_336 : 55 / 336 <= cloth_Cy 1.
Proof.
  unfold cloth_Cy.
  assert (Hle : RInt_cont fresnel_low fresnel_low_cont 0 1
              <= RInt_cont fresnel_cy_integrand fresnel_cy_cont 0 1).
  { apply RInt_cont_mono_fun; [lra|].
    intros u Hu.
    rewrite taylor_gap.
    unfold fresnel_cy_integrand.
    apply sin_ge_cubic.
    assert (Hu01 : 0 <= u <= 1) by (destruct Hu; lra).
    split.
    - apply angle_nonneg. apply (proj1 Hu01).
    - apply Rle_trans with (1 / 2);
        [apply angle_le_half_arg; [apply (proj1 Hu01) | apply (proj2 Hu01)]
         | apply Rlt_le; exact half_lt_PI]. }
  rewrite int_low_1 in Hle. exact Hle.
Qed.

Lemma cloth_Cx_three_fifth_gt : 1 / 2 < cloth_Cx (3 / 5).
Proof.
  unfold cloth_Cx.
  destruct (RInt_cont_bound fresnel_cx_integrand fresnel_cx_cont 0 (3 / 5)
             (4919 / 5000) 1) as [Hge _].
  - lra.
  - intros u Hu.
    assert (Hu35 : 0 <= u <= 3 / 5) by (destruct Hu; lra).
    split.
    + apply Rle_trans with (1 - fresnel_angle u * fresnel_angle u / 2).
      * apply one_minus_sq_4919.
        -- apply angle_nonneg. apply (proj1 Hu35).
        -- apply angle_le_9_50; [apply (proj1 Hu35) | apply (proj2 Hu35)].
      * apply cos_ge_quad.
        -- apply angle_ge_neg_PI2. apply (proj1 Hu35).
        -- apply Rle_trans with (1 / 2).
           ++ apply angle_le_half_arg; [apply (proj1 Hu35)|].
              apply Rle_trans with (3 / 5); [apply (proj2 Hu35)|lra].
           ++ apply half_le_PI2.
    + apply (proj2 (COS_bound (fresnel_angle u))).
  - assert (1 / 2 < (4919 / 5000) * (3 / 5 - 0)).
    { assert ((4919 / 5000) * (3 / 5 - 0) = 14757 / 25000) by field.
      assert (1 / 2 = 12500 / 25000) by field. lra. }
    lra.
Qed.

Lemma cloth_Cx_half_lt : cloth_Cx (1 / 2) < 1 / 2.
Proof.
  assert (Hadd : cloth_Cx (1 / 2) =
            cloth_Cx (1 / 4) +
            RInt_cont fresnel_cx_integrand fresnel_cx_cont (1 / 4) (1 / 2)).
  { unfold cloth_Cx.
    apply RInt_cont_split0; lra. }
  assert (H1 : cloth_Cx (1 / 4) <= 1 / 4).
  { unfold cloth_Cx.
    destruct (RInt_cont_bound fresnel_cx_integrand fresnel_cx_cont 0 (1 / 4) (-1) 1)
      as [_ Hhi].
    - lra.
    - intros x _. destruct (COS_bound (fresnel_angle x)) as [Ha Hb]. split; assumption.
    - nra. }
  assert (Hcos : cos (1 / 32) <= 1 - 1 / 2048 + 1 / 25165824).
  { apply Rle_trans with (1 - (1 / 32) * (1 / 32) / 2
                          + (1 / 32) * (1 / 32) * (1 / 32) * (1 / 32) / 24).
    - apply cos_le_quart.
      + pose proof PI_pos. lra.
      + apply Rle_trans with (1 / 2); [lra | apply half_le_PI2].
    - assert ((1 / 32) * (1 / 32) / 2 = 1 / 2048) by field.
      assert ((1 / 32) * (1 / 32) * (1 / 32) * (1 / 32) / 24 = 1 / 25165824) by field.
      lra. }
  assert (H2 : RInt_cont fresnel_cx_integrand fresnel_cx_cont (1 / 4) (1 / 2)
              <= (1 / 4) * cos (1 / 32)).
  { destruct (RInt_cont_bound fresnel_cx_integrand fresnel_cx_cont (1 / 4) (1 / 2)
                (-1) (cos (1 / 32))) as [_ Hhi].
    - lra.
    - intros u Hu.
      assert (Huq : 1 / 4 <= u <= 1 / 2) by (destruct Hu; lra).
      split.
      + apply (proj1 (COS_bound (fresnel_angle u))).
      + unfold fresnel_cx_integrand.
        apply cos_decr_1.
        * lra.
        * apply Rle_trans with (1 / 2); [lra|]. apply Rlt_le. exact half_lt_PI.
        * apply angle_nonneg. lra.
        * apply Rle_trans with (1 / 2).
          -- apply angle_le_half_arg; lra.
          -- apply Rlt_le. exact half_lt_PI.
        * apply Rle_trans with (fresnel_angle (1 / 4)).
          -- assert (fresnel_angle (1 / 4) = 1 / 32).
             { unfold fresnel_angle. field. }
             lra.
          -- unfold fresnel_angle.
             assert (Huu : (1 / 4) * (1 / 4) <= u * u).
             { apply sq_le; lra. }
             unfold Rdiv. apply Rmult_le_compat_r;
               [apply Rlt_le; apply Rinv_0_lt_compat; lra | exact Huu].
  - replace ((1 / 2) - (1 / 4)) with (1 / 4) in Hhi by field.
    rewrite (Rmult_comm (cos (1 / 32)) (1 / 4)) in Hhi.
    exact Hhi. }
  rewrite Hadd.
  assert (cloth_Cx (1 / 4) +
          RInt_cont fresnel_cx_integrand fresnel_cx_cont (1 / 4) (1 / 2)
          <= 1 / 4 + (1 / 4) * (1 - 1 / 2048 + 1 / 25165824)).
  { apply Rplus_le_compat; [exact H1|].
    apply Rle_trans with ((1 / 4) * cos (1 / 32)); [exact H2|].
    apply Rmult_le_compat_l; [lra | exact Hcos]. }
  assert (1 / 4 + (1 / 4) * (1 - 1 / 2048 + 1 / 25165824)
          = 50319361 / 100663296) by field.
  assert (1 / 2 = 50331648 / 100663296) by field.
  lra.
Qed.

Definition fresnel_cx_C0 :
  forall x : R, 0 <= x <= 1 -> continuity_pt fresnel_cx_integrand x :=
  fun x _ => fresnel_cx_cont x.

Definition fresnel_cx_prim_pr :
  forall x : R, 0 <= x -> x <= 1 ->
    Riemann_integrable fresnel_cx_integrand 0 x :=
  FTC_P1 Rle_0_1 fresnel_cx_C0.

Definition fresnel_cx_prim : R -> R :=
  primitive Rle_0_1 fresnel_cx_prim_pr.

Lemma cloth_Cx_as_prim : forall s, 0 <= s <= 1 ->
  cloth_Cx s = fresnel_cx_prim s.
Proof.
  intros s Hs. unfold cloth_Cx, fresnel_cx_prim, primitive.
  destruct (Rle_dec 0 s) as [Hs0|Hn0]; [|exfalso; lra].
  destruct (Rle_dec s 1) as [Hs1|Hn1]; [|exfalso; lra].
  apply RInt_cont_le. exact Hs0.
Qed.

Lemma cloth_Cx_cont_on : forall x, 1 / 2 <= x <= 3 / 5 ->
  continuity_pt cloth_Cx x.
Proof.
  intros x Hx.
  apply continuity_pt_locally_ext with (f := fresnel_cx_prim) (a := 1 / 4).
  - lra.
  - intros y Hy.
    apply Rabs_def2 in Hy.
    assert (Hy01 : 0 <= y <= 1) by lra.
    symmetry. apply cloth_Cx_as_prim. exact Hy01.
  - apply derivable_continuous_pt.
    exists (fresnel_cx_integrand x).
    apply RiemannInt_P27. lra.
Qed.

Lemma cloth_axis_gap_cont : forall a, 1 / 2 <= a <= 3 / 5 ->
  continuity_pt (fun t => cloth_Cx t - 1 / 2) a.
Proof.
  intros a Ha.
  unfold Rminus.
  apply continuity_pt_plus.
  - apply cloth_Cx_cont_on. exact Ha.
  - apply continuity_pt_opp. apply continuity_pt_const.
    intros u v. reflexivity.
Qed.

Lemma cloth_Cx_0 : cloth_Cx 0 = 0.
Proof. unfold cloth_Cx. apply RInt_cont_point. Qed.

Lemma cloth_Cy_0 : cloth_Cy 0 = 0.
Proof. unfold cloth_Cy. apply RInt_cont_point. Qed.
