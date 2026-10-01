(* ============================================================================
   NetTopologySuite.Proofs.ClothoidAxis
   ----------------------------------------------------------------------------
   Stations where a host clothoid's world heading α + ψ(s) is an integer
   multiple of π/2. ψ(s) = σ s² / (2 A²) is quadratic, so each such
   heading is the explicit pair of stations ±√(2 σ A² (k·π/2 − α))
   when the disc is non-negative. Odd k are the horizontal tangents
   (vx = 0); even k are the vertical tangents (vy = 0).

   claimId: none. The envelope letter is ClothoidEnvelope.clothoid_envelope.
   3-axiom host. No Admitted / Axiom / Parameter. No Rolle.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List ZArith Bool.
From Stdlib Require Import Ranalysis1.
From NTS.Proofs Require Import Distance SheetHenClothoidCore ClothoidTangent Atan2.
Import ListNotations.
Local Open Scope R_scope.

Lemma env_sigma_sq : forall c, cloth_sigma c * cloth_sigma c = 1.
Proof.
  intro c. unfold cloth_sigma. destruct (Rle_dec 0 (cloth_cross c)); ring.
Qed.

Lemma env_A_pos : forall c, cloth_wf c -> 0 < cloth_A c.
Proof. intros c [HA _]. exact HA. Qed.

Lemma env_h2 : forall c, cloth_wf c -> cloth_h2 c <> 0.
Proof. intros c [_ [Hh _]]. exact Hh. Qed.

Definition cloth_heading0 (c : ClothoidEgg) : R :=
  atan2 (cloth_sin0 c) (cloth_cos0 c).

Definition cloth_heading (c : ClothoidEgg) (s : R) : R :=
  cloth_heading0 c + cloth_psi c s.

Lemma heading_frame : forall c,
  cloth_h2 c <> 0 ->
  cos (cloth_heading0 c) = cloth_cos0 c /\
  sin (cloth_heading0 c) = cloth_sin0 c.
Proof.
  intros c Hh.
  assert (Hs := cloth_frame_sumsq c Hh).
  assert (Hne : ~ (cloth_cos0 c = 0 /\ cloth_sin0 c = 0)).
  { intros [Hc Hsn]. nra. }
  assert (Hr : sqrt (cloth_cos0 c * cloth_cos0 c + cloth_sin0 c * cloth_sin0 c) = 1).
  { rewrite Hs. apply sqrt_1. }
  unfold cloth_heading0. split.
  - rewrite cos_atan2 by exact Hne. rewrite Hr. field.
  - rewrite sin_atan2 by exact Hne. rewrite Hr. field.
Qed.

Lemma vx_heading : forall c s,
  cloth_h2 c <> 0 -> cloth_vx c s = cos (cloth_heading c s).
Proof.
  intros c s Hh. unfold cloth_heading, cloth_vx.
  destruct (heading_frame c Hh) as [Hc Hs].
  rewrite cos_plus, Hc, Hs. ring.
Qed.

Lemma vy_heading : forall c s,
  cloth_h2 c <> 0 -> cloth_vy c s = sin (cloth_heading c s).
Proof.
  intros c s Hh. unfold cloth_heading, cloth_vy.
  destruct (heading_frame c Hh) as [Hc Hs].
  rewrite sin_plus, Hc, Hs. ring.
Qed.

Lemma heading0_range : forall c,
  cloth_h2 c <> 0 -> - PI < cloth_heading0 c <= PI.
Proof.
  intros c Hh. unfold cloth_heading0. apply atan2_range.
  destruct (heading_frame c Hh) as [Hc Hs].
  intros [Hx Hy]. assert (Hsum := cloth_frame_sumsq c Hh). nra.
Qed.

Lemma IZR_pos_INR : forall p, IZR (Z.pos p) = INR (Pos.to_nat p).
Proof. intro p. apply eq_sym, INR_IPR. Qed.

Lemma cos_period_Z : forall x (k : Z), cos (x + 2 * IZR k * PI) = cos x.
Proof.
  intros x k. destruct k as [|p|p].
  - replace (IZR Z0) with 0 by reflexivity.
    replace (x + 2 * 0 * PI) with x by ring. reflexivity.
  - rewrite (IZR_pos_INR p). apply cos_period.
  - rewrite IZR_NEG, (IZR_pos_INR p).
    set (n := Pos.to_nat p).
    assert (E : (x + 2 * (- INR n) * PI) + 2 * INR n * PI = x) by ring.
    pose proof (cos_period (x + 2 * (- INR n) * PI) n) as Hc.
    rewrite E in Hc. symmetry. exact Hc.
Qed.

Lemma sin_period_Z : forall x (k : Z), sin (x + 2 * IZR k * PI) = sin x.
Proof.
  intros x k. destruct k as [|p|p].
  - replace (IZR Z0) with 0 by reflexivity.
    replace (x + 2 * 0 * PI) with x by ring. reflexivity.
  - rewrite (IZR_pos_INR p). apply sin_period.
  - rewrite IZR_NEG, (IZR_pos_INR p).
    set (n := Pos.to_nat p).
    assert (E : (x + 2 * (- INR n) * PI) + 2 * INR n * PI = x) by ring.
    pose proof (sin_period (x + 2 * (- INR n) * PI) n) as Hs.
    rewrite E in Hs. symmetry. exact Hs.
Qed.

Definition reduce_angle (alpha : R) : R :=
  let n := Int_part ((alpha + PI) / (2 * PI)) in
  let s := alpha - 2 * PI * IZR n in
  if Req_EM_T s (- PI) then PI else s.

Lemma reduce_angle_spec : forall alpha,
  - PI < reduce_angle alpha <= PI /\
  cos (reduce_angle alpha) = cos alpha /\
  sin (reduce_angle alpha) = sin alpha.
Proof.
  intro alpha. unfold reduce_angle.
  set (x := (alpha + PI) / (2 * PI)).
  set (n := Int_part x).
  set (s := alpha - 2 * PI * IZR n).
  pose proof PI_RGT_0 as Hp.
  pose proof (base_Int_part x) as [Hle Hgt]. fold n in Hle, Hgt.
  assert (Hs : s = PI * (2 * (x - IZR n) - 1)).
  { unfold s, x. field. lra. }
  assert (Hslo : - PI <= s).
  { rewrite Hs. assert (0 <= 2 * (x - IZR n)) by lra. nra. }
  assert (Hshi : s < PI).
  { rewrite Hs. assert (2 * (x - IZR n) - 1 < 1) by lra. nra. }
  assert (Hcos : cos s = cos alpha).
  { unfold s. rewrite <- (cos_period_Z alpha (- n)%Z).
    replace (alpha + 2 * IZR (- n)%Z * PI) with (alpha - 2 * PI * IZR n).
    - reflexivity.
    - rewrite opp_IZR. ring. }
  assert (Hsin : sin s = sin alpha).
  { unfold s. rewrite <- (sin_period_Z alpha (- n)%Z).
    replace (alpha + 2 * IZR (- n)%Z * PI) with (alpha - 2 * PI * IZR n).
    - reflexivity.
    - rewrite opp_IZR. ring. }
  destruct (Req_EM_T s (- PI)) as [Heq|Hne].
  - split; [lra|]. rewrite Heq in Hcos, Hsin.
    rewrite cos_neg, cos_PI in Hcos. rewrite sin_neg, sin_PI in Hsin.
    split; [rewrite cos_PI; exact Hcos | rewrite sin_PI; rewrite <- Hsin; ring].
  - split; [lra | split; [exact Hcos | exact Hsin]].
Qed.

Lemma reduce_angle_period : forall alpha, exists k : Z,
  alpha = reduce_angle alpha + 2 * PI * IZR k.
Proof.
  intro alpha. unfold reduce_angle.
  set (x := (alpha + PI) / (2 * PI)).
  set (n := Int_part x).
  set (s := alpha - 2 * PI * IZR n).
  destruct (Req_EM_T s (- PI)) as [Heq|Hne].
  - exists (n - 1)%Z.
    assert (E : IZR (n - 1) = IZR n - 1).
    { replace (n - 1)%Z with (n + Z.opp 1)%Z by lia.
      rewrite plus_IZR, opp_IZR. ring. }
    rewrite E. unfold s in Heq. lra.
  - exists n. unfold s. ring.
Qed.

Lemma cos_pos_open_quarter : forall a, Rabs a < PI / 2 -> 0 < cos a.
Proof.
  intros a Ha.
  pose proof PI_RGT_0 as Hp.
  assert (He : cos a = cos (Rabs a)).
  { destruct (Rle_dec 0 a) as [H|H].
    - rewrite Rabs_right by lra. reflexivity.
    - apply Rnot_le_lt in H. rewrite (Rabs_left a H). rewrite cos_neg. reflexivity. }
  rewrite He.
  assert (Hdec : cos (PI / 2) < cos (Rabs a)).
  { apply cos_decreasing_1.
    - apply Rabs_pos.
    - apply Rle_trans with (PI / 2); [apply Rlt_le; exact Ha | lra].
    - lra.
    - lra.
    - exact Ha. }
  rewrite cos_PI2 in Hdec. exact Hdec.
Qed.

Lemma cos_neg_past_quarter : forall a, PI / 2 < a < PI -> cos a < 0.
Proof.
  intros a Ha.
  pose proof PI_RGT_0 as Hp.
  assert (Hs : sin (a - PI / 2) = - cos a).
  { rewrite sin_minus, cos_PI2, sin_PI2. ring. }
  assert (0 < sin (a - PI / 2)) by (apply sin_gt_0; lra).
  lra.
Qed.

Lemma cos_zero_principal : forall a,
  - PI < a <= PI -> cos a = 0 -> a = PI / 2 \/ a = - PI / 2.
Proof.
  intros a Ha Hz.
  pose proof PI_RGT_0 as Hp.
  destruct (Rle_lt_dec 0 a) as [Hp0|Hn0].
  - destruct (Rle_lt_dec (PI / 2) a) as [Hge|Hlt].
    + destruct (Req_dec_T a (PI / 2)) as [->|Hne]; [left; reflexivity|].
      destruct (Req_dec_T a PI) as [->|Hpi].
      * rewrite cos_PI in Hz. lra.
      * assert (cos a < 0) by (apply cos_neg_past_quarter; lra). lra.
    + assert (0 < cos a).
      { apply cos_pos_open_quarter. rewrite Rabs_right by lra. lra. }
      lra.
  - assert (Hc : cos (- a) = 0) by (rewrite cos_neg; exact Hz).
    assert (Hr : 0 <= - a <= PI) by lra.
    destruct (Rle_lt_dec (PI / 2) (- a)) as [Hge|Hlt].
    + destruct (Req_dec_T (- a) (PI / 2)) as [Heq|Hne].
      * right. lra.
      * destruct (Req_dec_T (- a) PI) as [Hpi|Hpi].
        -- rewrite Hpi in Hc. rewrite cos_PI in Hc. lra.
        -- assert (cos (- a) < 0) by (apply cos_neg_past_quarter; lra). lra.
    + assert (0 < cos (- a)).
      { apply cos_pos_open_quarter. rewrite Rabs_right by lra. lra. }
      lra.
Qed.

Lemma sin_zero_principal : forall a,
  - PI < a <= PI -> sin a = 0 -> a = 0 \/ a = PI.
Proof.
  intros a Ha Hz.
  pose proof PI_RGT_0 as Hp.
  destruct (Rle_lt_dec 0 a) as [H0|Hn].
  - destruct (Req_dec_T a 0) as [->|Hne0]; [left; reflexivity|].
    destruct (Req_dec_T a PI) as [->|Hnepi]; [right; reflexivity|].
    assert (0 < sin a) by (apply sin_gt_0; lra). lra.
  - assert (0 < sin (- a)) by (apply sin_gt_0; lra).
    rewrite sin_neg in H. lra.
Qed.

Lemma cos_zero_shift : forall a,
  cos a = 0 -> exists k : Z, a = IZR k * PI / 2 /\ Z.odd k = true.
Proof.
  intros a Hz.
  destruct (reduce_angle_period a) as [m Hm].
  destruct (reduce_angle_spec a) as [Hr [Hc _]].
  assert (Hcz : cos (reduce_angle a) = 0) by (rewrite Hc; exact Hz).
  destruct (cos_zero_principal (reduce_angle a) Hr Hcz) as [Hp|Hn].
  - exists (4 * m + 1)%Z. split.
    + rewrite Hm, Hp.
      replace (IZR (4 * m + 1)) with (4 * IZR m + 1).
      * field.
      * rewrite plus_IZR, mult_IZR.
        replace (IZR 4) with 4 by reflexivity.
        replace (IZR 1) with 1 by reflexivity. ring.
    + apply Z.odd_spec. exists (2 * m)%Z. lia.
  - exists (4 * m - 1)%Z. split.
    + rewrite Hm, Hn.
      replace (IZR (4 * m - 1)) with (4 * IZR m - 1).
      * field.
      * replace (4 * m - 1)%Z with (4 * m + Z.opp 1)%Z by lia.
        rewrite plus_IZR, mult_IZR, opp_IZR.
        replace (IZR 4) with 4 by reflexivity.
        replace (IZR 1) with 1 by reflexivity. ring.
    + apply Z.odd_spec. exists (2 * m - 1)%Z. lia.
Qed.

Lemma sin_zero_shift : forall a,
  sin a = 0 -> exists k : Z, a = IZR k * PI / 2 /\ Z.even k = true.
Proof.
  intros a Hz.
  destruct (reduce_angle_period a) as [m Hm].
  destruct (reduce_angle_spec a) as [Hr [_ Hs]].
  assert (Hsz : sin (reduce_angle a) = 0) by (rewrite Hs; exact Hz).
  destruct (sin_zero_principal (reduce_angle a) Hr Hsz) as [H0|Hpi].
  - exists (4 * m)%Z. split.
    + rewrite Hm, H0.
      replace (IZR (4 * m)) with (4 * IZR m).
      * field.
      * rewrite mult_IZR. replace (IZR 4) with 4 by reflexivity. ring.
    + apply Z.even_spec. exists (2 * m)%Z. lia.
  - exists (4 * m + 2)%Z. split.
    + rewrite Hm, Hpi.
      replace (IZR (4 * m + 2)) with (4 * IZR m + 2).
      * field.
      * rewrite plus_IZR, mult_IZR.
        replace (IZR 4) with 4 by reflexivity.
        replace (IZR 2) with 2 by reflexivity. ring.
    + apply Z.even_spec. exists (2 * m + 1)%Z. lia.
Qed.

Lemma sin_INR_PI : forall n, sin (INR n * PI) = 0.
Proof.
  induction n.
  - simpl. rewrite Rmult_0_l. apply sin_0.
  - rewrite S_INR. rewrite Rmult_plus_distr_r, Rmult_1_l.
    rewrite sin_plus, IHn, cos_PI, sin_PI. ring.
Qed.

Lemma sin_Z_PI : forall k, sin (IZR k * PI) = 0.
Proof.
  intro k. destruct k as [|p|p].
  - simpl. rewrite Rmult_0_l. apply sin_0.
  - rewrite IZR_pos_INR. apply sin_INR_PI.
  - rewrite IZR_NEG, IZR_pos_INR.
    replace ((- INR (Pos.to_nat p)) * PI) with (- (INR (Pos.to_nat p) * PI)) by ring.
    rewrite sin_neg, sin_INR_PI. ring.
Qed.

Lemma cos_k_half_odd : forall k, Z.odd k = true -> cos (IZR k * PI / 2) = 0.
Proof.
  intros k Ho. destruct (proj1 (Z.odd_spec k) Ho) as [m Hm].
  rewrite Hm. rewrite plus_IZR, mult_IZR.
  replace (IZR 2) with 2 by reflexivity. replace (IZR 1) with 1 by reflexivity.
  replace ((2 * IZR m + 1) * PI / 2) with (PI / 2 + IZR m * PI) by field.
  rewrite cos_plus, cos_PI2, sin_PI2, sin_Z_PI. ring.
Qed.

Lemma sin_k_half_even : forall k, Z.even k = true -> sin (IZR k * PI / 2) = 0.
Proof.
  intros k He. destruct (proj1 (Z.even_spec k) He) as [m Hm].
  rewrite Hm, mult_IZR. replace (IZR 2) with 2 by reflexivity.
  replace (2 * IZR m * PI / 2) with (IZR m * PI) by field.
  apply sin_Z_PI.
Qed.

Lemma odd_even_compl : forall k : Z, Z.odd k = negb (Z.even k).
Proof.
  intro k. destruct k as [|p|p]; try reflexivity; destruct p; reflexivity.
Qed.

Lemma odd_false_even : forall k, Z.odd k = false -> Z.even k = true.
Proof.
  intros k H. rewrite odd_even_compl in H.
  destruct (Z.even k); simpl in H; [reflexivity | discriminate].
Qed.

Lemma even_odd_false : forall k, Z.even k = true -> Z.odd k = false.
Proof.
  intros k H. rewrite odd_even_compl, H. reflexivity.
Qed.

Definition cloth_lo (c : ClothoidEgg) : R := Rmin (cloth_sd c) (cloth_ed c).
Definition cloth_hi (c : ClothoidEgg) : R := Rmax (cloth_sd c) (cloth_ed c).

Definition cloth_disc (c : ClothoidEgg) (theta : R) : R :=
  2 * cloth_sigma c * (cloth_A c * cloth_A c) * theta.

Definition cloth_theta (c : ClothoidEgg) (k : Z) : R :=
  IZR k * PI / 2 - cloth_heading0 c.

Lemma psi_solve : forall c s th,
  0 < cloth_A c ->
  cloth_psi c s = th ->
  s * s = cloth_disc c th.
Proof.
  intros c s th HA Heq.
  unfold cloth_psi, Rdiv in Heq. unfold cloth_disc.
  set (sig := cloth_sigma c) in *. set (A := cloth_A c) in *.
  assert (Hsig : sig * sig = 1) by (unfold sig; apply env_sigma_sq).
  assert (Hd : 2 * A * A <> 0) by (unfold A in *; nra).
  apply (Rmult_eq_compat_l sig) in Heq.
  assert (E1 : sig * (((sig * s) * s) * / (2 * A * A)) =
               ((sig * sig) * (s * s)) * / (2 * A * A)) by ring.
  rewrite E1, Hsig, Rmult_1_l in Heq.
  apply (Rmult_eq_compat_l (2 * A * A)) in Heq.
  assert (E2 : (2 * A * A) * ((s * s) * / (2 * A * A)) = s * s).
  { replace ((2 * A * A) * ((s * s) * / (2 * A * A)))
      with ((s * s) * ((2 * A * A) * / (2 * A * A))) by ring.
    rewrite Rinv_r by exact Hd. ring. }
  rewrite E2 in Heq.
  replace ((2 * A * A) * (sig * th)) with (2 * sig * (A * A) * th) in Heq by ring.
  exact Heq.
Qed.

Lemma psi_of_disc : forall c s th,
  0 < cloth_A c ->
  s * s = cloth_disc c th ->
  cloth_psi c s = th.
Proof.
  intros c s th HA Heq.
  unfold cloth_disc in Heq.
  set (sig := cloth_sigma c) in *. set (A := cloth_A c) in *.
  assert (Hsig : sig * sig = 1) by (unfold sig; apply env_sigma_sq).
  assert (Hd : 2 * A * A <> 0) by (unfold A in *; nra).
  assert (E : cloth_psi c s = sig * (s * s) * / (2 * A * A)).
  { unfold cloth_psi, sig, A, Rdiv. ring. }
  rewrite E, Heq.
  replace (sig * (2 * sig * (A * A) * th) * / (2 * A * A))
    with (sig * sig * th * ((2 * A * A) * / (2 * A * A))) by ring.
  rewrite Hsig, Rinv_r by exact Hd. ring.
Qed.

Lemma heading_of_disc : forall c s k,
  0 < cloth_A c ->
  s * s = cloth_disc c (cloth_theta c k) ->
  cloth_heading c s = IZR k * PI / 2.
Proof.
  intros c s k HA Heq. unfold cloth_heading.
  rewrite (psi_of_disc c s _ HA Heq). unfold cloth_theta. ring.
Qed.

Lemma disc_of_heading : forall c s k,
  cloth_wf c ->
  cloth_heading c s = IZR k * PI / 2 ->
  s * s = cloth_disc c (cloth_theta c k).
Proof.
  intros c s k Hwf Heq.
  apply psi_solve; [apply env_A_pos; exact Hwf|].
  unfold cloth_heading in Heq. unfold cloth_theta. lra.
Qed.

Lemma cand_square : forall s d, 0 <= d ->
  s = sqrt d \/ s = - sqrt d -> s * s = d.
Proof.
  intros s d Hd [-> | ->].
  - apply sqrt_sqrt. exact Hd.
  - replace ((- sqrt d) * (- sqrt d)) with (sqrt d * sqrt d) by ring.
    apply sqrt_sqrt. exact Hd.
Qed.

Lemma sqrt_pm : forall s d, 0 <= d -> s * s = d ->
  s = sqrt d \/ s = - sqrt d.
Proof.
  intros s d Hd Heq.
  destruct (Rle_dec 0 s) as [Hp|Hn].
  - left. rewrite <- (sqrt_square s Hp). rewrite Heq. reflexivity.
  - right. apply Rnot_le_lt in Hn.
    assert (E : sqrt d = - s).
    { rewrite <- Heq. replace (s * s) with ((- s) * (- s)) by ring.
      apply sqrt_square. lra. }
    lra.
Qed.

Lemma sqr_abs_eq : forall x, x * x = Rabs x * Rabs x.
Proof.
  intro x. destruct (Rle_dec 0 x) as [H|H].
  - rewrite (Rabs_right x (Rle_ge _ _ H)). reflexivity.
  - apply Rnot_le_lt in H. rewrite (Rabs_left x H). ring.
Qed.

Definition psi_span (c : ClothoidEgg) : R :=
  Rmax (Rabs (cloth_psi c (cloth_sd c))) (Rabs (cloth_psi c (cloth_ed c))).

Lemma psi_abs_window : forall c s,
  cloth_wf c -> cloth_lo c <= s <= cloth_hi c ->
  Rabs (cloth_psi c s) <= psi_span c.
Proof.
  intros c s Hwf Hs.
  pose proof (env_A_pos c Hwf) as HA.
  assert (Hden : 0 < 2 * cloth_A c * cloth_A c) by nra.
  assert (Hinv : 0 < / (2 * cloth_A c * cloth_A c)) by (apply Rinv_0_lt_compat; exact Hden).
  assert (Hsig : Rabs (cloth_sigma c) = 1) by apply cloth_sigma_abs.
  set (rad := Rmax (Rabs (cloth_sd c)) (Rabs (cloth_ed c))).
  assert (Hneg_sd : - rad <= cloth_sd c).
  { apply Rle_trans with (- Rabs (cloth_sd c)).
    - apply Ropp_le_contravar. unfold rad. apply Rmax_l.
    - destruct (Rle_dec 0 (cloth_sd c)) as [P|N].
      + rewrite (Rabs_right (cloth_sd c) (Rle_ge _ _ P)). lra.
      + apply Rnot_le_lt in N. rewrite (Rabs_left (cloth_sd c) N). lra. }
  assert (Hneg_ed : - rad <= cloth_ed c).
  { apply Rle_trans with (- Rabs (cloth_ed c)).
    - apply Ropp_le_contravar. unfold rad. apply Rmax_r.
    - destruct (Rle_dec 0 (cloth_ed c)) as [P|N].
      + rewrite (Rabs_right (cloth_ed c) (Rle_ge _ _ P)). lra.
      + apply Rnot_le_lt in N. rewrite (Rabs_left (cloth_ed c) N). lra. }
  assert (Hlo : - rad <= cloth_lo c).
  { unfold cloth_lo. apply Rmin_glb; assumption. }
  assert (Hhi : cloth_hi c <= rad).
  { unfold cloth_hi. apply Rmax_lub.
    - eapply Rle_trans; [apply Rle_abs | unfold rad; apply Rmax_l].
    - eapply Rle_trans; [apply Rle_abs | unfold rad; apply Rmax_r]. }
  assert (Hsrad : Rabs s <= rad).
  { apply Rabs_le. split.
    - eapply Rle_trans; [exact Hlo | exact (proj1 Hs)].
    - eapply Rle_trans; [exact (proj2 Hs) | exact Hhi]. }
  assert (Hrad_nn : 0 <= rad).
  { unfold rad. eapply Rle_trans; [apply Rabs_pos | apply Rmax_l]. }
  assert (Hsq : s * s <= rad * rad).
  { rewrite sqr_abs_eq. apply Rmult_le_compat; try apply Rabs_pos; exact Hsrad. }
  assert (Hpsi_u : forall u,
      Rabs (cloth_psi c u) = (u * u) * / (2 * cloth_A c * cloth_A c)).
  { intro u. unfold cloth_psi, Rdiv. rewrite !Rabs_mult, Hsig, Rmult_1_l.
    rewrite <- (sqr_abs_eq u).
    rewrite (Rabs_pos_eq (/ (2 * cloth_A c * cloth_A c)) (Rlt_le _ _ Hinv)).
    ring. }
  assert (Hspan : psi_span c =
      Rmax (cloth_sd c * cloth_sd c) (cloth_ed c * cloth_ed c) *
      / (2 * cloth_A c * cloth_A c)).
  { unfold psi_span. rewrite !Hpsi_u.
    set (inv := / (2 * cloth_A c * cloth_A c)).
    set (xs := cloth_sd c * cloth_sd c). set (ys := cloth_ed c * cloth_ed c).
    destruct (Rle_dec xs ys) as [Hxy|Hyx].
    - rewrite (Rmax_right xs ys Hxy).
      rewrite (Rmax_right (xs * inv) (ys * inv)).
      + ring.
      + apply Rmult_le_compat_r; [apply Rlt_le; exact Hinv | exact Hxy].
    - apply Rnot_le_lt in Hyx.
      rewrite (Rmax_left xs ys (Rlt_le _ _ Hyx)).
      rewrite (Rmax_left (xs * inv) (ys * inv)).
      + ring.
      + apply Rmult_le_compat_r; [apply Rlt_le; exact Hinv | apply Rlt_le; exact Hyx]. }
  assert (Erad : rad * rad =
      Rmax (cloth_sd c * cloth_sd c) (cloth_ed c * cloth_ed c)).
  { unfold rad.
    rewrite (sqr_abs_eq (cloth_sd c)), (sqr_abs_eq (cloth_ed c)).
    destruct (Rle_dec (Rabs (cloth_sd c)) (Rabs (cloth_ed c))) as [Hle|Hlt].
    - rewrite (Rmax_right _ _ Hle).
      rewrite (Rmax_right (Rabs (cloth_sd c) * Rabs (cloth_sd c))
                          (Rabs (cloth_ed c) * Rabs (cloth_ed c))).
      + reflexivity.
      + apply Rmult_le_compat; try apply Rabs_pos; exact Hle.
    - apply Rnot_le_lt in Hlt.
      rewrite (Rmax_left _ _ (Rlt_le _ _ Hlt)).
      rewrite (Rmax_left (Rabs (cloth_sd c) * Rabs (cloth_sd c))
                         (Rabs (cloth_ed c) * Rabs (cloth_ed c))).
      + reflexivity.
      + apply Rmult_le_compat; try apply Rabs_pos; apply Rlt_le; exact Hlt. }
  rewrite (Hpsi_u s).
  apply Rle_trans with ((rad * rad) * / (2 * cloth_A c * cloth_A c)).
  - apply Rmult_le_compat_r; [apply Rlt_le; exact Hinv | exact Hsq].
  - rewrite Erad, <- Hspan. apply Rle_refl.
Qed.

Lemma heading_abs_window : forall c s,
  cloth_wf c -> cloth_lo c <= s <= cloth_hi c ->
  Rabs (cloth_heading c s) <= PI + psi_span c.
Proof.
  intros c s Hwf Hs. unfold cloth_heading.
  eapply Rle_trans; [apply Rabs_triang|].
  assert (Ha : Rabs (cloth_heading0 c) <= PI).
  { apply Rabs_le. destruct (heading0_range c (env_h2 c Hwf)) as [H1 H2]. split; lra. }
  assert (Hp : Rabs (cloth_psi c s) <= psi_span c) by (apply psi_abs_window; assumption).
  lra.
Qed.

Definition k_span (c : ClothoidEgg) : R := 2 + 2 * psi_span c / PI.

Definition k_bound (c : ClothoidEgg) : nat := Z.to_nat (up (k_span c + 1)).

Lemma heading_k_bound : forall c s k,
  cloth_wf c -> cloth_lo c <= s <= cloth_hi c ->
  cloth_heading c s = IZR k * PI / 2 ->
  (Z.abs k <= Z.of_nat (k_bound c))%Z.
Proof.
  intros c s k Hwf Hs Heq.
  pose proof PI_RGT_0 as Hp.
  assert (Hh : Rabs (cloth_heading c s) <= PI + psi_span c)
    by (apply heading_abs_window; assumption).
  rewrite Heq in Hh.
  assert (E : Rabs (IZR k * PI / 2) = IZR (Z.abs k) * PI / 2).
  { unfold Rdiv. rewrite !Rabs_mult. rewrite <- abs_IZR.
    rewrite (Rabs_right PI) by lra.
    rewrite (Rabs_right (/ 2)) by (apply Rle_ge, Rlt_le, Rinv_0_lt_compat; lra).
    ring. }
  assert (Hk : IZR (Z.abs k) <= k_span c).
  { apply (Rmult_le_reg_r (PI / 2)).
    - apply Rdiv_lt_0_compat; lra.
    - replace (IZR (Z.abs k) * (PI / 2)) with (Rabs (IZR k * PI / 2)).
      + assert (Er : k_span c * (PI / 2) = PI + psi_span c).
        { unfold k_span. field. lra. }
        rewrite Er. exact Hh.
      + rewrite E. field. }
  destruct (archimed (k_span c + 1)) as [Hg _].
  apply Rgt_lt in Hg.
  assert (Hlt : (Z.abs k < up (k_span c + 1))%Z).
  { apply lt_IZR. eapply Rle_lt_trans; [exact Hk|].
    eapply Rlt_trans; [ | exact Hg]. lra. }
  assert (Hpos : 0 < k_span c + 1).
  { unfold k_span, Rdiv.
    assert (Hnn : 0 <= psi_span c).
    { unfold psi_span. eapply Rle_trans; [apply Rabs_pos | apply Rmax_l]. }
    assert (Hinv : 0 < / PI) by (apply Rinv_0_lt_compat; exact Hp).
    assert (0 <= 2 * psi_span c * / PI).
    { apply Rmult_le_pos; [apply Rmult_le_pos; [lra | exact Hnn] | apply Rlt_le; exact Hinv]. }
    lra. }
  assert (Hup : (0 <= up (k_span c + 1))%Z).
  { apply Z.lt_le_incl. apply lt_IZR.
    apply Rlt_trans with (k_span c + 1); [exact Hpos | exact Hg]. }
  apply Z.lt_le_incl in Hlt.
  unfold k_bound. rewrite Z2Nat.id by exact Hup. exact Hlt.
Qed.

Definition k_range (n : nat) : list Z :=
  map (fun i => (Z.of_nat i - Z.of_nat n)%Z) (seq 0 (2 * n + 1)).

Lemma k_range_spec : forall n (k : Z),
  In k (k_range n) <-> (- Z.of_nat n <= k <= Z.of_nat n)%Z.
Proof.
  intros n k. unfold k_range. rewrite in_map_iff. split.
  - intros [i [Hk Hin]]. subst k. rewrite in_seq in Hin. split; lia.
  - intros [Hlo Hhi].
    exists (Z.to_nat (k + Z.of_nat n)). split.
    + rewrite Z2Nat.id by lia. lia.
    + rewrite in_seq. split; [lia|].
      rewrite <- (Nat2Z.id (2 * n + 1)).
      apply Z2Nat.inj_lt; lia.
Qed.

Print Assumptions env_sigma_sq.
Print Assumptions env_A_pos.
Print Assumptions env_h2.
Print Assumptions heading_frame.
Print Assumptions vx_heading.
Print Assumptions vy_heading.
Print Assumptions heading0_range.
Print Assumptions IZR_pos_INR.
Print Assumptions cos_period_Z.
Print Assumptions sin_period_Z.
Print Assumptions reduce_angle_spec.
Print Assumptions reduce_angle_period.
Print Assumptions cos_pos_open_quarter.
Print Assumptions cos_neg_past_quarter.
Print Assumptions cos_zero_principal.
Print Assumptions sin_zero_principal.
Print Assumptions cos_zero_shift.
Print Assumptions sin_zero_shift.
Print Assumptions sin_INR_PI.
Print Assumptions sin_Z_PI.
Print Assumptions cos_k_half_odd.
Print Assumptions sin_k_half_even.
Print Assumptions odd_even_compl.
Print Assumptions odd_false_even.
Print Assumptions even_odd_false.
Print Assumptions psi_solve.
Print Assumptions psi_of_disc.
Print Assumptions heading_of_disc.
Print Assumptions disc_of_heading.
Print Assumptions cand_square.
Print Assumptions sqrt_pm.
Print Assumptions sqr_abs_eq.
Print Assumptions psi_abs_window.
Print Assumptions heading_abs_window.
Print Assumptions heading_k_bound.
Print Assumptions k_range_spec.
