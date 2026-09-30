(* ============================================================================
   NetTopologySuite.Proofs.ClothoidNorm2
   ----------------------------------------------------------------------------
   Normalizer 2, letter N2a. Start state plus spiral law (k0, k1, L)
   builds the host ClothoidEgg of SheetHenClothoidCore. Closed form,
   no atan2. sigma = sign(k1-k0), A^2 = L/|k1-k0|,
   sd = sigma*k0*A^2, ed = sigma*k1*A^2. psi0 = sigma*sd^2/(2 A^2).
   With (c,s) = st_dir,
     cos0 = c cos psi0 + s sin psi0,
     sin0 = s cos psi0 - c sin psi0.
   ref1 = (cos0, sin0). Unit dir => cloth_h2 = 1.
   ref2 = sigma * rot90(ref1), so cloth_cross = sigma. ref2 encodes
   sigma only. LOC = P0 - R0*(Icos sd, Isin sd). Icos depends on
   sigma and A, not on LOCATION (cloth_Icos_same_place is the
   window half of that; the probe egg below changes only aff_loc).
   sd < 0 uses the existing int_seg window from 0 to s. No oriented
   primitive. World curvature kappa(s) = sigma*s/A^2. Tangent is
   (cloth_vx s, cloth_vy s). cloth_unit_speed is the host fact that
   this tangent is unit when cloth_h2 <> 0; this letter does not
   re-prove it.

   norm2_length is both halves: ed - sd = L, and is_curve_length of
   cloth_eval on [0,1] equals L. The second half is
   lip_speed_is_curve_length. cloth_eval_speed_sq makes the speed the
   constant L once cloth_h2 = 1. The Lipschitz constant is read off
   cloth_phi_K on the station ball, with A > 0, so no excluded middle.

   clothoid_state_unique pins sigma, A, sd, ed, R0, LOC from the
   start state and the law. Ref-vector scale is already gone in
   cloth_cos0 / cloth_sin0 (division by cloth_hypot);
   cloth_cos0_same / cloth_sin0_same drop the window and the measures.
   No ODE uniqueness. No MVT, Rolle, or RiemannInt.
   claimId: 0006-norm2-state
   witness: clothoid_state_unique
   consumer: norm2_is_the_state
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra Ranalysis1.
From NTS.Proofs Require Import Distance LipInt SheetHenClothoidCore
  ClothoidTangent MetricSpeed CurveLength.
Local Open Scope R_scope.

Record StartState : Type := mkStart {
  st_pos : Point;
  st_dir : Point;
  st_curv : R
}.

Record SpiralLaw : Type := mkLaw {
  sl_k0 : R;
  sl_k1 : R;
  sl_len : R
}.

Definition pt_h2 (p : Point) : R :=
  px p * px p + py p * py p.

Definition rot90 (p : Point) : Point :=
  mkPoint (- py p) (px p).

(* sign(k1-k0). k1 = k0 is not a normalizer input; Rle maps it to +1. *)
Definition law_sigma (law : SpiralLaw) : R :=
  if Rle_dec (sl_k0 law) (sl_k1 law) then 1 else -1.

Definition law_A2 (law : SpiralLaw) : R :=
  sl_len law / Rabs (sl_k1 law - sl_k0 law).

Definition law_A (law : SpiralLaw) : R := sqrt (law_A2 law).

Definition law_sd (law : SpiralLaw) : R :=
  law_sigma law * sl_k0 law * law_A2 law.

Definition law_ed (law : SpiralLaw) : R :=
  law_sigma law * sl_k1 law * law_A2 law.

Definition law_psi0 (law : SpiralLaw) : R :=
  law_sigma law * law_sd law * law_sd law / (2 * law_A2 law).

Definition norm2_cos0 (st : StartState) (law : SpiralLaw) : R :=
  px (st_dir st) * cos (law_psi0 law) + py (st_dir st) * sin (law_psi0 law).

Definition norm2_sin0 (st : StartState) (law : SpiralLaw) : R :=
  py (st_dir st) * cos (law_psi0 law) - px (st_dir st) * sin (law_psi0 law).

Definition norm2_ref1 (st : StartState) (law : SpiralLaw) : Point :=
  mkPoint (norm2_cos0 st law) (norm2_sin0 st law).

Definition norm2_ref2 (st : StartState) (law : SpiralLaw) : Point :=
  pt_scale (law_sigma law) (rot90 (norm2_ref1 st law)).

(* Same refs and A as the result, LOCATION at the origin, so Icos(sd)
   is available before LOC is stored. *)
Definition norm2_probe (st : StartState) (law : SpiralLaw) : ClothoidEgg :=
  mk_cloth (mkAffPlace (mkPoint 0 0) (norm2_ref1 st law) (norm2_ref2 st law))
    (law_A law) (law_sd law) (law_ed law) None None.

Definition norm2_loc (st : StartState) (law : SpiralLaw) : Point :=
  let c0 := norm2_cos0 st law in
  let s0 := norm2_sin0 st law in
  let ix := cloth_Icos (norm2_probe st law) (law_sd law) in
  let iy := cloth_Isin (norm2_probe st law) (law_sd law) in
  mkPoint (px (st_pos st) - (c0 * ix - s0 * iy))
          (py (st_pos st) - (s0 * ix + c0 * iy)).

Definition norm2 (st : StartState) (law : SpiralLaw) (m0 m1 : option R)
  : ClothoidEgg :=
  mk_cloth (mkAffPlace (norm2_loc st law) (norm2_ref1 st law) (norm2_ref2 st law))
    (law_A law) (law_sd law) (law_ed law) m0 m1.

Definition cloth_kappa (c : ClothoidEgg) (s : R) : R :=
  cloth_sigma c * s / (cloth_A c * cloth_A c).

Definition cloth_tangent (c : ClothoidEgg) (t : R) : Point :=
  mkPoint (cloth_vx c (cloth_s c t)) (cloth_vy c (cloth_s c t)).

Definition cloth_curv (c : ClothoidEgg) (t : R) : R :=
  cloth_kappa c (cloth_s c t).

Definition cloth_exit (c : ClothoidEgg) : StartState :=
  mkStart (cloth_eval c 1)
    (mkPoint (cloth_vx c (cloth_ed c)) (cloth_vy c (cloth_ed c)))
    (cloth_kappa c (cloth_ed c)).

Lemma point_eq : forall p q : Point, px p = px q -> py p = py q -> p = q.
Proof.
  intros [x1 y1] [x2 y2] Hx Hy. cbn in Hx, Hy. subst. reflexivity.
Qed.

Lemma law_sigma_sq : forall law, law_sigma law * law_sigma law = 1.
Proof.
  intro law. unfold law_sigma.
  destruct (Rle_dec (sl_k0 law) (sl_k1 law)); ring.
Qed.

Lemma law_dk_nz : forall law,
  sl_k0 law <> sl_k1 law -> sl_k1 law - sl_k0 law <> 0.
Proof.
  intros law Hne E. apply Hne. lra.
Qed.

Lemma law_A2_pos : forall law,
  0 < sl_len law -> sl_k0 law <> sl_k1 law -> 0 < law_A2 law.
Proof.
  intros law HL Hne.
  unfold law_A2, Rdiv.
  apply Rmult_lt_0_compat; [exact HL|].
  apply Rinv_0_lt_compat, Rabs_pos_lt, law_dk_nz. exact Hne.
Qed.

Lemma law_A_pos : forall law,
  0 < sl_len law -> sl_k0 law <> sl_k1 law -> 0 < law_A law.
Proof.
  intros law HL Hne. unfold law_A. apply sqrt_lt_R0, law_A2_pos; assumption.
Qed.

Lemma law_A_sq : forall law,
  0 < sl_len law -> sl_k0 law <> sl_k1 law ->
  law_A law * law_A law = law_A2 law.
Proof.
  intros law HL Hne. unfold law_A. apply sqrt_sqrt.
  apply Rlt_le, law_A2_pos; assumption.
Qed.

Lemma law_sigma_dk : forall law,
  sl_k0 law <> sl_k1 law ->
  law_sigma law * (sl_k1 law - sl_k0 law) = Rabs (sl_k1 law - sl_k0 law).
Proof.
  intros law Hne.
  unfold law_sigma.
  destruct (Rle_dec (sl_k0 law) (sl_k1 law)) as [Hle|Hlt].
  - rewrite Rabs_right by lra. ring.
  - assert (Hneg : sl_k1 law - sl_k0 law < 0) by lra.
    rewrite Rabs_left by exact Hneg. ring.
Qed.

Lemma law_ed_sd : forall law,
  sl_k0 law <> sl_k1 law -> law_ed law - law_sd law = sl_len law.
Proof.
  intros law Hne.
  unfold law_ed, law_sd, law_A2, Rdiv.
  set (dk := sl_k1 law - sl_k0 law).
  assert (Hdk : dk <> 0) by (unfold dk; apply law_dk_nz; exact Hne).
  assert (Habs : 0 < Rabs dk) by (apply Rabs_pos_lt; exact Hdk).
  assert (Hsig : law_sigma law * dk = Rabs dk).
  { unfold dk. apply law_sigma_dk. exact Hne. }
  replace (law_sigma law * sl_k1 law * (sl_len law * / Rabs dk) -
           law_sigma law * sl_k0 law * (sl_len law * / Rabs dk))
    with ((law_sigma law * dk) * (sl_len law * / Rabs dk)).
  - rewrite Hsig. field. apply Rgt_not_eq. exact Habs.
  - unfold dk. ring.
Qed.

Lemma norm2_ref_sumsq : forall st law,
  pt_h2 (norm2_ref1 st law) = pt_h2 (st_dir st).
Proof.
  intros st law.
  unfold pt_h2, norm2_ref1, norm2_cos0, norm2_sin0. cbn.
  set (c := px (st_dir st)). set (s := py (st_dir st)).
  set (u := cos (law_psi0 law)). set (v := sin (law_psi0 law)).
  assert (E : u * u + v * v = 1).
  { unfold u, v. pose proof (sin2_cos2 (law_psi0 law)) as H.
    unfold Rsqr in H. rewrite Rplus_comm in H. exact H. }
  replace ((c * u + s * v) * (c * u + s * v) +
           (s * u - c * v) * (s * u - c * v))
    with ((c * c + s * s) * (u * u + v * v)) by ring.
  rewrite E. unfold c, s, pt_h2. ring.
Qed.

Lemma norm2_cross_raw : forall st law,
  aff_cross (mkAffPlace (norm2_loc st law) (norm2_ref1 st law) (norm2_ref2 st law))
    = law_sigma law * pt_h2 (norm2_ref1 st law).
Proof.
  intros st law.
  unfold aff_cross, norm2_ref2, rot90, pt_scale, norm2_ref1, pt_h2. cbn.
  ring.
Qed.

Lemma norm2_h2 : forall st law m0 m1,
  pt_h2 (st_dir st) = 1 -> cloth_h2 (norm2 st law m0 m1) = 1.
Proof.
  intros st law m0 m1 Hu.
  unfold cloth_h2, aff_h2, norm2. cbn.
  assert (E := norm2_ref_sumsq st law).
  unfold pt_h2, norm2_ref1 in E. cbn in E.
  exact (eq_trans E Hu).
Qed.

Lemma norm2_cross : forall st law m0 m1,
  pt_h2 (st_dir st) = 1 ->
  cloth_cross (norm2 st law m0 m1) = law_sigma law.
Proof.
  intros st law m0 m1 Hu.
  unfold cloth_cross, norm2. cbn.
  rewrite norm2_cross_raw, norm2_ref_sumsq, Hu. ring.
Qed.

Lemma norm2_sigma : forall st law m0 m1,
  pt_h2 (st_dir st) = 1 ->
  cloth_sigma (norm2 st law m0 m1) = law_sigma law.
Proof.
  intros st law m0 m1 Hu.
  unfold cloth_sigma. rewrite (norm2_cross st law m0 m1 Hu).
  unfold law_sigma.
  destruct (Rle_dec (sl_k0 law) (sl_k1 law)) as [Hle|Hlt].
  - destruct (Rle_dec 0 1) as [_|Hn]; [reflexivity|]. exfalso. lra.
  - destruct (Rle_dec 0 (-1)) as [Hp|Hn]; [exfalso; lra|]. reflexivity.
Qed.

Lemma norm2_hypot : forall st law m0 m1,
  pt_h2 (st_dir st) = 1 -> cloth_hypot (norm2 st law m0 m1) = 1.
Proof.
  intros st law m0 m1 Hu.
  unfold cloth_hypot. rewrite (norm2_h2 st law m0 m1 Hu). apply sqrt_1.
Qed.

Lemma norm2_cos0_eq : forall st law m0 m1,
  pt_h2 (st_dir st) = 1 ->
  cloth_cos0 (norm2 st law m0 m1) = norm2_cos0 st law.
Proof.
  intros st law m0 m1 Hu.
  unfold cloth_cos0, Rdiv. rewrite (norm2_hypot st law m0 m1 Hu).
  rewrite Rinv_1, Rmult_1_r.
  unfold norm2, norm2_ref1. cbn. reflexivity.
Qed.

Lemma norm2_sin0_eq : forall st law m0 m1,
  pt_h2 (st_dir st) = 1 ->
  cloth_sin0 (norm2 st law m0 m1) = norm2_sin0 st law.
Proof.
  intros st law m0 m1 Hu.
  unfold cloth_sin0, Rdiv. rewrite (norm2_hypot st law m0 m1 Hu).
  rewrite Rinv_1, Rmult_1_r.
  unfold norm2, norm2_ref1. cbn. reflexivity.
Qed.

Lemma norm2_Icos_probe : forall st law m0 m1 s,
  cloth_Icos (norm2 st law m0 m1) s = cloth_Icos (norm2_probe st law) s.
Proof.
  intros st law m0 m1 s. unfold cloth_Icos. apply int_seg_pi.
Qed.

Lemma norm2_Isin_probe : forall st law m0 m1 s,
  cloth_Isin (norm2 st law m0 m1) s = cloth_Isin (norm2_probe st law) s.
Proof.
  intros st law m0 m1 s. unfold cloth_Isin. apply int_seg_pi.
Qed.

Lemma norm2_wf : forall st law m0 m1,
  0 < sl_len law ->
  sl_k0 law <> sl_k1 law ->
  pt_h2 (st_dir st) = 1 ->
  (m0 = None /\ m1 = None) \/ (exists a b, m0 = Some a /\ m1 = Some b) ->
  cloth_wf (norm2 st law m0 m1).
Proof.
  intros st law m0 m1 HL Hne Hu Hm.
  apply cloth_wf_mk.
  - apply law_A_pos; assumption.
  - change (cloth_h2 (norm2 st law m0 m1) <> 0).
    rewrite (norm2_h2 st law m0 m1 Hu). lra.
  - change (cloth_cross (norm2 st law m0 m1) <> 0).
    rewrite (norm2_cross st law m0 m1 Hu).
    unfold law_sigma.
    destruct (Rle_dec (sl_k0 law) (sl_k1 law)); lra.
  - exact Hm.
Qed.

Lemma norm2_start : forall st law m0 m1,
  pt_h2 (st_dir st) = 1 ->
  cloth_eval (norm2 st law m0 m1) 0 = st_pos st.
Proof.
  intros st law m0 m1 Hu.
  set (c := norm2 st law m0 m1).
  assert (Hs : cloth_s c 0 = law_sd law).
  { unfold cloth_s, c, norm2, mk_cloth. cbn. ring. }
  unfold cloth_eval. rewrite Hs. unfold c.
  apply point_eq.
  - unfold cloth_P, cloth_Px.
    rewrite (norm2_cos0_eq st law m0 m1 Hu).
    rewrite (norm2_sin0_eq st law m0 m1 Hu).
    rewrite (norm2_Icos_probe st law m0 m1 (law_sd law)).
    rewrite (norm2_Isin_probe st law m0 m1 (law_sd law)).
    unfold norm2, norm2_loc, mk_cloth. cbn [cloth_place aff_loc px py].
    set (ix := cloth_Icos (norm2_probe st law) (law_sd law)).
    set (iy := cloth_Isin (norm2_probe st law) (law_sd law)).
    set (c0 := norm2_cos0 st law). set (s0 := norm2_sin0 st law).
    ring.
  - unfold cloth_P, cloth_Py.
    rewrite (norm2_cos0_eq st law m0 m1 Hu).
    rewrite (norm2_sin0_eq st law m0 m1 Hu).
    rewrite (norm2_Icos_probe st law m0 m1 (law_sd law)).
    rewrite (norm2_Isin_probe st law m0 m1 (law_sd law)).
    unfold norm2, norm2_loc, mk_cloth. cbn [cloth_place aff_loc px py].
    set (ix := cloth_Icos (norm2_probe st law) (law_sd law)).
    set (iy := cloth_Isin (norm2_probe st law) (law_sd law)).
    set (c0 := norm2_cos0 st law). set (s0 := norm2_sin0 st law).
    ring.
Qed.

Lemma rotate_out : forall c0 s0 psi,
  (c0 * cos psi + s0 * sin psi) * cos psi
    - (s0 * cos psi - c0 * sin psi) * sin psi = c0 /\
  (s0 * cos psi - c0 * sin psi) * cos psi
    + (c0 * cos psi + s0 * sin psi) * sin psi = s0.
Proof.
  intros c0 s0 psi.
  pose proof (sin2_cos2 psi) as H. unfold Rsqr in H.
  assert (E : cos psi * cos psi + sin psi * sin psi = 1).
  { rewrite Rplus_comm. exact H. }
  split.
  - replace ((c0 * cos psi + s0 * sin psi) * cos psi
        - (s0 * cos psi - c0 * sin psi) * sin psi)
      with (c0 * (cos psi * cos psi + sin psi * sin psi)) by ring.
    rewrite E. ring.
  - replace ((s0 * cos psi - c0 * sin psi) * cos psi
        + (c0 * cos psi + s0 * sin psi) * sin psi)
      with (s0 * (cos psi * cos psi + sin psi * sin psi)) by ring.
    rewrite E. ring.
Qed.

Lemma norm2_psi_sd : forall st law m0 m1,
  0 < sl_len law -> sl_k0 law <> sl_k1 law -> pt_h2 (st_dir st) = 1 ->
  cloth_psi (norm2 st law m0 m1) (law_sd law) = law_psi0 law.
Proof.
  intros st law m0 m1 HL Hne Hu.
  unfold cloth_psi, law_psi0.
  rewrite (norm2_sigma st law m0 m1 Hu).
  unfold norm2, mk_cloth. cbn [cloth_A].
  replace (2 * law_A law * law_A law) with (2 * (law_A law * law_A law)) by ring.
  rewrite (law_A_sq law HL Hne).
  reflexivity.
Qed.

Lemma norm2_psi_ed : forall st law m0 m1,
  0 < sl_len law -> sl_k0 law <> sl_k1 law -> pt_h2 (st_dir st) = 1 ->
  cloth_psi (norm2 st law m0 m1) (law_ed law)
    = law_sigma law * law_ed law * law_ed law / (2 * law_A2 law).
Proof.
  intros st law m0 m1 HL Hne Hu.
  unfold cloth_psi.
  rewrite (norm2_sigma st law m0 m1 Hu).
  unfold norm2, mk_cloth. cbn [cloth_A].
  replace (2 * law_A law * law_A law) with (2 * (law_A law * law_A law)) by ring.
  rewrite (law_A_sq law HL Hne). reflexivity.
Qed.

Lemma norm2_start_dir : forall st law m0 m1,
  0 < sl_len law -> sl_k0 law <> sl_k1 law -> pt_h2 (st_dir st) = 1 ->
  cloth_tangent (norm2 st law m0 m1) 0 = st_dir st.
Proof.
  intros st law m0 m1 HL Hne Hu.
  set (c := norm2 st law m0 m1).
  assert (Hs : cloth_s c 0 = law_sd law).
  { unfold cloth_s, c, norm2, mk_cloth. cbn. ring. }
  apply point_eq.
  - unfold cloth_tangent, cloth_vx. cbn. rewrite Hs. unfold c.
    rewrite (norm2_cos0_eq st law m0 m1 Hu).
    rewrite (norm2_sin0_eq st law m0 m1 Hu).
    rewrite (norm2_psi_sd st law m0 m1 HL Hne Hu).
    unfold norm2_cos0, norm2_sin0.
    apply (proj1 (rotate_out (px (st_dir st)) (py (st_dir st)) (law_psi0 law))).
  - unfold cloth_tangent, cloth_vy. cbn. rewrite Hs. unfold c.
    rewrite (norm2_cos0_eq st law m0 m1 Hu).
    rewrite (norm2_sin0_eq st law m0 m1 Hu).
    rewrite (norm2_psi_sd st law m0 m1 HL Hne Hu).
    unfold norm2_cos0, norm2_sin0.
    apply (proj2 (rotate_out (px (st_dir st)) (py (st_dir st)) (law_psi0 law))).
Qed.

Lemma norm2_kappa_sd : forall st law m0 m1,
  0 < sl_len law -> sl_k0 law <> sl_k1 law -> pt_h2 (st_dir st) = 1 ->
  cloth_kappa (norm2 st law m0 m1) (law_sd law) = sl_k0 law.
Proof.
  intros st law m0 m1 HL Hne Hu.
  unfold cloth_kappa, law_sd, Rdiv.
  rewrite (norm2_sigma st law m0 m1 Hu).
  unfold norm2, mk_cloth. cbn [cloth_A].
  rewrite (law_A_sq law HL Hne).
  assert (HA : law_A2 law <> 0).
  { apply Rgt_not_eq, law_A2_pos; assumption. }
  replace (law_sigma law * (law_sigma law * sl_k0 law * law_A2 law) * / law_A2 law)
    with (law_sigma law * law_sigma law * sl_k0 law) by (field; exact HA).
  rewrite law_sigma_sq. ring.
Qed.

Lemma norm2_kappa_ed : forall st law m0 m1,
  0 < sl_len law -> sl_k0 law <> sl_k1 law -> pt_h2 (st_dir st) = 1 ->
  cloth_kappa (norm2 st law m0 m1) (law_ed law) = sl_k1 law.
Proof.
  intros st law m0 m1 HL Hne Hu.
  unfold cloth_kappa, law_ed, Rdiv.
  rewrite (norm2_sigma st law m0 m1 Hu).
  unfold norm2, mk_cloth. cbn [cloth_A].
  rewrite (law_A_sq law HL Hne).
  assert (HA : law_A2 law <> 0).
  { apply Rgt_not_eq, law_A2_pos; assumption. }
  replace (law_sigma law * (law_sigma law * sl_k1 law * law_A2 law) * / law_A2 law)
    with (law_sigma law * law_sigma law * sl_k1 law) by (field; exact HA).
  rewrite law_sigma_sq. ring.
Qed.

Lemma norm2_curv : forall st law m0 m1,
  0 < sl_len law -> sl_k0 law <> sl_k1 law -> pt_h2 (st_dir st) = 1 ->
  cloth_curv (norm2 st law m0 m1) 0 = sl_k0 law /\
  cloth_curv (norm2 st law m0 m1) 1 = sl_k1 law.
Proof.
  intros st law m0 m1 HL Hne Hu.
  set (c := norm2 st law m0 m1).
  assert (H0 : cloth_s c 0 = law_sd law).
  { unfold cloth_s, c, norm2, mk_cloth. cbn. ring. }
  assert (H1 : cloth_s c 1 = law_ed law).
  { unfold cloth_s, c, norm2, mk_cloth. cbn. ring. }
  split.
  - unfold cloth_curv. rewrite H0. apply norm2_kappa_sd; assumption.
  - unfold cloth_curv. rewrite H1. apply norm2_kappa_ed; assumption.
Qed.

(* ed - sd = L, and that difference is the metric length of cloth_eval
   on [0,1]. Speed is the constant L (cloth_eval_speed_sq). *)
Section Norm2Speed.
Variable st : StartState.
Variable law : SpiralLaw.
Variables m0 m1 : option R.
Hypothesis HL : 0 < sl_len law.
Hypothesis Hne : sl_k0 law <> sl_k1 law.
Hypothesis Hu : pt_h2 (st_dir st) = 1.

Let c : ClothoidEgg := norm2 st law m0 m1.
Let d : R := cloth_ed c - cloth_sd c.
Let rad : R := Rmax (Rabs (cloth_sd c)) (Rabs (cloth_ed c)).
Let Kphi : R := cloth_phi_K c rad.
Let Lv : R := 2 * d * d * Kphi.

Let nvx (t : R) : R := d * cloth_vx c (cloth_s c t).
Let nvy (t : R) : R := d * cloth_vy c (cloth_s c t).
Let ngx (t : R) : R := px (cloth_eval c t).
Let ngy (t : R) : R := py (cloth_eval c t).

Lemma norm2_d_eq : d = sl_len law.
Proof.
  unfold d, c, norm2, mk_cloth. cbn. apply law_ed_sd. exact Hne.
Qed.

Lemma norm2_d_pos : 0 < d.
Proof. rewrite norm2_d_eq. exact HL. Qed.

Lemma norm2_h2_nz : cloth_h2 c <> 0.
Proof. unfold c. rewrite (norm2_h2 st law m0 m1 Hu). lra. Qed.

Lemma norm2_rad_nn : 0 <= rad.
Proof.
  unfold rad. apply Rle_trans with (Rabs (cloth_sd c));
    [apply Rabs_pos | apply Rmax_l].
Qed.

Lemma norm2_Lv_nn : 0 <= Lv.
Proof.
  unfold Lv. replace (2 * d * d * Kphi) with (2 * (d * d) * Kphi) by ring.
  apply Rmult_le_pos; [apply Rmult_le_pos; [lra | apply Rle_0_sqr] |].
  unfold Kphi. apply cloth_phi_K_nonneg.
Qed.

Lemma norm2_frame_abs :
  Rabs (cloth_cos0 c) <= 1 /\ Rabs (cloth_sin0 c) <= 1.
Proof.
  assert (Hs := cloth_frame_sumsq c norm2_h2_nz).
  assert (one : forall x y, x * x + y * y = 1 -> -1 <= x <= 1).
  { intros x y H. nra. }
  split; apply Rabs_le.
  - apply (one (cloth_cos0 c) (cloth_sin0 c) Hs).
  - apply (one (cloth_sin0 c) (cloth_cos0 c)).
    rewrite Rplus_comm. exact Hs.
Qed.

Lemma norm2_s_in_rad : forall t, 0 <= t <= 1 -> - rad <= cloth_s c t <= rad.
Proof.
  intros t [Ht0 Ht1].
  unfold cloth_s.
  assert (Es : cloth_sd c + t * (cloth_ed c - cloth_sd c)
               = (1 - t) * cloth_sd c + t * cloth_ed c) by ring.
  rewrite Es.
  set (s := (1 - t) * cloth_sd c + t * cloth_ed c).
  assert (H1t : 0 <= 1 - t) by lra.
  assert (Hs : Rabs s <= rad).
  { unfold s. eapply Rle_trans; [apply Rabs_triang |].
    rewrite !Rabs_mult.
    rewrite (Rabs_pos_eq (1 - t) H1t), (Rabs_pos_eq t Ht0).
    apply Rle_trans with ((1 - t) * rad + t * rad).
    - apply Rplus_le_compat.
      + apply Rmult_le_compat_l; [exact H1t | unfold rad; apply Rmax_l].
      + apply Rmult_le_compat_l; [exact Ht0 | unfold rad; apply Rmax_r].
    - right. ring. }
  split.
  - apply Rle_trans with (- Rabs s).
    + apply Ropp_le_contravar. exact Hs.
    + apply Ropp_le_cancel. rewrite Ropp_involutive.
      rewrite <- (Rabs_Ropp s). apply Rle_abs.
  - apply Rle_trans with (Rabs s); [apply Rle_abs | exact Hs].
Qed.

Lemma norm2_psi_lip : forall x y,
  - rad <= x <= rad -> - rad <= y <= rad ->
  Rabs (cloth_psi c x - cloth_psi c y) <= Kphi * Rabs (x - y).
Proof.
  intros x y Hx Hy.
  set (AA := cloth_A c * cloth_A c).
  assert (HA0 : 0 < cloth_A c).
  { unfold c. apply law_A_pos; assumption. }
  assert (Hpos : 0 < AA) by (unfold AA; nra).
  assert (HA : cloth_A c <> 0) by lra.
  assert (Hinv : 0 < / (2 * AA)) by (apply Rinv_0_lt_compat; lra).
  unfold cloth_psi, Kphi, cloth_phi_K, Rdiv.
  assert (E :
    (cloth_sigma c * x * x) * / (2 * cloth_A c * cloth_A c) -
    (cloth_sigma c * y * y) * / (2 * cloth_A c * cloth_A c)
    = cloth_sigma c * ((x - y) * (x + y)) * / (2 * AA)).
  { unfold AA. field. exact HA. }
  rewrite E. clear E.
  rewrite !Rabs_mult. rewrite cloth_sigma_abs.
  assert (Habs : Rabs (/ (2 * AA)) = / (2 * AA)).
  { apply Rabs_pos_eq. apply Rlt_le. exact Hinv. }
  rewrite Habs. clear Habs.
  assert (Hxy : Rabs (x + y) <= 2 * rad).
  { eapply Rle_trans; [apply Rabs_triang |].
    assert (Hxabs : Rabs x <= rad) by (apply Rabs_le; exact Hx).
    assert (Hyabs : Rabs y <= rad) by (apply Rabs_le; exact Hy).
    apply Rle_trans with (rad + rad); [apply Rplus_le_compat; assumption |].
    right. ring. }
  rewrite (Rabs_pos_eq rad norm2_rad_nn).
  apply Rle_trans with ((1 * (Rabs (x - y) * (2 * rad))) * / (2 * AA)).
  - apply Rmult_le_compat_r; [apply Rlt_le; exact Hinv |].
    apply Rmult_le_compat_l; [lra |].
    apply Rmult_le_compat_l; [apply Rabs_pos | exact Hxy].
  - unfold AA. right. field. exact HA.
Qed.

Lemma norm2_comb_lip : forall a0 b0 s1 s2,
  Rabs a0 <= 1 -> Rabs b0 <= 1 ->
  - rad <= s1 <= rad -> - rad <= s2 <= rad ->
  Rabs (a0 * (cos (cloth_psi c s1) - cos (cloth_psi c s2))
      + b0 * (sin (cloth_psi c s1) - sin (cloth_psi c s2)))
    <= 2 * Kphi * Rabs (s1 - s2).
Proof.
  intros a0 b0 s1 s2 Ha Hb Hs1 Hs2.
  eapply Rle_trans; [apply Rabs_triang |].
  rewrite !Rabs_mult.
  assert (Hc : Rabs (cos (cloth_psi c s1) - cos (cloth_psi c s2))
               <= Kphi * Rabs (s1 - s2)).
  { eapply Rle_trans; [apply cos_lip | apply norm2_psi_lip; assumption]. }
  assert (Hs : Rabs (sin (cloth_psi c s1) - sin (cloth_psi c s2))
               <= Kphi * Rabs (s1 - s2)).
  { eapply Rle_trans; [apply sin_lip | apply norm2_psi_lip; assumption]. }
  apply Rle_trans with
    (1 * (Kphi * Rabs (s1 - s2)) + 1 * (Kphi * Rabs (s1 - s2))).
  - apply Rplus_le_compat; apply Rmult_le_compat; try apply Rabs_pos; assumption.
  - right. ring.
Qed.

Lemma norm2_scaled_lip : forall (f : R -> R),
  (forall s1 s2, - rad <= s1 <= rad -> - rad <= s2 <= rad ->
     Rabs (f s1 - f s2) <= 2 * Kphi * Rabs (s1 - s2)) ->
  forall x y, 0 <= x <= 1 -> 0 <= y <= 1 ->
  Rabs (d * f (cloth_s c x) - d * f (cloth_s c y)) <= Lv * Rabs (x - y).
Proof.
  intros f Hf x y Hx Hy.
  replace (d * f (cloth_s c x) - d * f (cloth_s c y))
    with (d * (f (cloth_s c x) - f (cloth_s c y))) by ring.
  rewrite Rabs_mult. rewrite (Rabs_pos_eq d (Rlt_le _ _ norm2_d_pos)).
  apply Rle_trans with (d * (2 * Kphi * Rabs (cloth_s c x - cloth_s c y))).
  - apply Rmult_le_compat_l; [apply Rlt_le, norm2_d_pos |].
    apply Hf; apply norm2_s_in_rad; assumption.
  - assert (Es : cloth_s c x - cloth_s c y = d * (x - y)).
    { unfold cloth_s, d. ring. }
    rewrite Es, Rabs_mult. rewrite (Rabs_pos_eq d (Rlt_le _ _ norm2_d_pos)).
    unfold Lv. right. ring.
Qed.

Lemma norm2_nvx_lip : forall x y, 0 <= x <= 1 -> 0 <= y <= 1 ->
  Rabs (nvx x - nvx y) <= Lv * Rabs (x - y).
Proof.
  intros x y Hx Hy. unfold nvx. apply norm2_scaled_lip; [| exact Hx | exact Hy].
  intros s1 s2 Hs1 Hs2.
  replace (cloth_vx c s1 - cloth_vx c s2) with
    (cloth_cos0 c * (cos (cloth_psi c s1) - cos (cloth_psi c s2))
     + (- cloth_sin0 c) * (sin (cloth_psi c s1) - sin (cloth_psi c s2)))
    by (unfold cloth_vx; ring).
  apply norm2_comb_lip; try assumption.
  - exact (proj1 norm2_frame_abs).
  - rewrite Rabs_Ropp. exact (proj2 norm2_frame_abs).
Qed.

Lemma norm2_nvy_lip : forall x y, 0 <= x <= 1 -> 0 <= y <= 1 ->
  Rabs (nvy x - nvy y) <= Lv * Rabs (x - y).
Proof.
  intros x y Hx Hy. unfold nvy. apply norm2_scaled_lip; [| exact Hx | exact Hy].
  intros s1 s2 Hs1 Hs2.
  replace (cloth_vy c s1 - cloth_vy c s2) with
    (cloth_sin0 c * (cos (cloth_psi c s1) - cos (cloth_psi c s2))
     + cloth_cos0 c * (sin (cloth_psi c s1) - sin (cloth_psi c s2)))
    by (unfold cloth_vy; ring).
  apply norm2_comb_lip; try assumption; apply norm2_frame_abs.
Qed.

Lemma norm2_ngx_deriv : forall t, 0 <= t <= 1 ->
  derivable_pt_lim ngx t (nvx t).
Proof. intros t _. unfold ngx, nvx. apply cloth_eval_px_deriv. Qed.

Lemma norm2_ngy_deriv : forall t, 0 <= t <= 1 ->
  derivable_pt_lim ngy t (nvy t).
Proof. intros t _. unfold ngy, nvy. apply cloth_eval_py_deriv. Qed.

Lemma norm2_speed_const : forall t, speed nvx nvy t = d.
Proof.
  intro t. unfold speed.
  assert (E : nvx t * nvx t + nvy t * nvy t = d * d).
  { unfold nvx, nvy.
    pose proof (cloth_eval_speed_sq c t norm2_h2_nz) as Hq.
    cbv zeta in Hq. unfold d. exact Hq. }
  rewrite E. apply sqrt_square. apply Rlt_le, norm2_d_pos.
Qed.

Lemma norm2_speed_lip : forall x y,
  Rmin 0 1 <= x <= Rmax 0 1 -> Rmin 0 1 <= y <= Rmax 0 1 ->
  Rabs (speed nvx nvy x - speed nvx nvy y) <= (Lv + Lv) * Rabs (x - y).
Proof.
  intros x y _ _. rewrite !norm2_speed_const.
  rewrite Rminus_diag, Rabs_R0.
  apply Rmult_le_pos; [apply Rplus_le_le_0_compat; exact norm2_Lv_nn | apply Rabs_pos].
Qed.

Lemma norm2_length :
  cloth_ed c - cloth_sd c = sl_len law /\
  is_curve_length (cloth_eval c) 0 1 (sl_len law).
Proof.
  split.
  - exact norm2_d_eq.
  - rewrite <- norm2_d_eq.
    set (SF := speedF nvx nvy 0 1 Lv Lv norm2_Lv_nn norm2_Lv_nn
                 norm2_nvx_lip norm2_nvy_lip).
    destruct (lip_speed_is_curve_length ngx ngy nvx nvy 0 1 Lv Lv
                Rle_0_1 norm2_Lv_nn norm2_Lv_nn
                norm2_nvx_lip norm2_nvy_lip
                norm2_ngx_deriv norm2_ngy_deriv) as [Hint Hlen].
    assert (Hsum : 0 <= Lv + Lv).
    { apply Rplus_le_le_0_compat; exact norm2_Lv_nn. }
    assert (Hdiff : SF 1 - SF 0 = d).
    { unfold SF. rewrite Hint.
      transitivity (int_seg (speed nvx nvy) (Lv + Lv) 0 1 Hsum norm2_speed_lip).
      - apply int_seg_pi.
      - transitivity (int_seg (fun _ : R => d) (Lv + Lv) 0 1 Hsum
                       (const_lip d (Lv + Lv) 0 1 Hsum)).
        + apply int_seg_ext. intros x _. apply norm2_speed_const.
        + rewrite (int_seg_const d (Lv + Lv) 0 1 Hsum
                    (const_lip d (Lv + Lv) 0 1 Hsum) Rle_0_1).
          ring. }
    apply is_curve_length_ext with (g1 := gamma ngx ngy).
    + intro t. apply point_eq; reflexivity.
    + rewrite <- Hdiff. unfold SF. exact Hlen.
Qed.

End Norm2Speed.

Lemma norm2_exit : forall st law m0 m1,
  0 < sl_len law -> sl_k0 law <> sl_k1 law -> pt_h2 (st_dir st) = 1 ->
  let c := norm2 st law m0 m1 in
  st_pos (cloth_exit c) = cloth_eval c 1 /\
  st_dir (cloth_exit c) =
    mkPoint (cloth_vx c (cloth_ed c)) (cloth_vy c (cloth_ed c)) /\
  st_curv (cloth_exit c) = sl_k1 law.
Proof.
  intros st law m0 m1 HL Hne Hu c.
  unfold cloth_exit. cbn [st_pos st_dir st_curv].
  split; [|split]; [reflexivity|reflexivity|].
  unfold c. rewrite <- (norm2_kappa_ed st law m0 m1 HL Hne Hu).
  unfold norm2, mk_cloth. cbn [cloth_ed]. reflexivity.
Qed.

Lemma cloth_sigma_pm : forall c, cloth_sigma c = 1 \/ cloth_sigma c = -1.
Proof.
  intro c. unfold cloth_sigma.
  destruct (Rle_dec 0 (cloth_cross c)); [left|right]; reflexivity.
Qed.

Lemma cloth_sigma_sq : forall c, cloth_sigma c * cloth_sigma c = 1.
Proof.
  intro c. destruct (cloth_sigma_pm c) as [H|H]; rewrite H; ring.
Qed.

Lemma cloth_A_nz : forall c, cloth_wf c -> cloth_A c <> 0.
Proof.
  intros c [HA _]. lra.
Qed.

Lemma cloth_AA_pos : forall c, cloth_wf c -> 0 < cloth_A c * cloth_A c.
Proof.
  intros c [HA _]. nra.
Qed.

Lemma kappa_diff : forall c,
  cloth_A c <> 0 ->
  cloth_kappa c (cloth_ed c) - cloth_kappa c (cloth_sd c)
    = cloth_sigma c * (cloth_ed c - cloth_sd c) / (cloth_A c * cloth_A c).
Proof.
  intros c HA. unfold cloth_kappa, Rdiv. field. exact HA.
Qed.

Lemma rotate_in : forall a b u v vx vy,
  u * u + v * v = 1 ->
  vx = a * u - b * v ->
  vy = b * u + a * v ->
  a = vx * u + vy * v /\ b = vy * u - vx * v.
Proof.
  intros a b u v vx vy Huv Hvx Hvy.
  subst vx vy. split.
  - replace ((a * u - b * v) * u + (b * u + a * v) * v)
      with (a * (u * u + v * v)) by ring.
    rewrite Huv. ring.
  - replace ((b * u + a * v) * u - (a * u - b * v) * v)
      with (b * (u * u + v * v)) by ring.
    rewrite Huv. ring.
Qed.

Lemma int_seg_cast : forall (g : R -> R) L1 L2 a b
  (HL1 : 0 <= L1)
  (Hlip1 : forall x y,
      Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
      Rabs (g x - g y) <= L1 * Rabs (x - y))
  (HL2 : 0 <= L2)
  (Hlip2 : forall x y,
      Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
      Rabs (g x - g y) <= L2 * Rabs (x - y)),
  L1 = L2 ->
  int_seg g L1 a b HL1 Hlip1 = int_seg g L2 a b HL2 Hlip2.
Proof.
  intros g L1 L2 a b HL1 Hlip1 HL2 Hlip2 Heq.
  revert HL1 Hlip1 HL2 Hlip2. rewrite <- Heq.
  intros HL1 Hlip1 HL2 Hlip2. apply int_seg_pi.
Qed.

Lemma cloth_Icos_sigma_A : forall c1 c2 s,
  cloth_sigma c1 = cloth_sigma c2 ->
  cloth_A c1 = cloth_A c2 ->
  cloth_Icos c1 s = cloth_Icos c2 s.
Proof.
  intros c1 c2 s Hs HA.
  unfold cloth_Icos.
  assert (HK : cloth_phi_K c1 s = cloth_phi_K c2 s).
  { unfold cloth_phi_K. rewrite HA. reflexivity. }
  assert (Hp : forall u, cloth_psi c1 u = cloth_psi c2 u).
  { intro u. unfold cloth_psi. rewrite Hs, HA. reflexivity. }
  assert (Hlip : forall x y,
      Rmin 0 s <= x <= Rmax 0 s -> Rmin 0 s <= y <= Rmax 0 s ->
      Rabs (cos (cloth_psi c1 x) - cos (cloth_psi c1 y))
        <= cloth_phi_K c2 s * Rabs (x - y)).
  { intros x y Hx Hy. rewrite <- HK. apply cloth_cos_psi_lip; assumption. }
  transitivity (int_seg (fun u => cos (cloth_psi c1 u)) (cloth_phi_K c2 s) 0 s
                  (cloth_phi_K_nonneg c2 s) Hlip).
  - apply int_seg_cast. exact HK.
  - apply int_seg_ext. intros u _. f_equal. apply Hp.
Qed.

Lemma cloth_Isin_sigma_A : forall c1 c2 s,
  cloth_sigma c1 = cloth_sigma c2 ->
  cloth_A c1 = cloth_A c2 ->
  cloth_Isin c1 s = cloth_Isin c2 s.
Proof.
  intros c1 c2 s Hs HA.
  unfold cloth_Isin.
  assert (HK : cloth_phi_K c1 s = cloth_phi_K c2 s).
  { unfold cloth_phi_K. rewrite HA. reflexivity. }
  assert (Hp : forall u, cloth_psi c1 u = cloth_psi c2 u).
  { intro u. unfold cloth_psi. rewrite Hs, HA. reflexivity. }
  assert (Hlip : forall x y,
      Rmin 0 s <= x <= Rmax 0 s -> Rmin 0 s <= y <= Rmax 0 s ->
      Rabs (sin (cloth_psi c1 x) - sin (cloth_psi c1 y))
        <= cloth_phi_K c2 s * Rabs (x - y)).
  { intros x y Hx Hy. rewrite <- HK. apply cloth_sin_psi_lip; assumption. }
  transitivity (int_seg (fun u => sin (cloth_psi c1 u)) (cloth_phi_K c2 s) 0 s
                  (cloth_phi_K_nonneg c2 s) Hlip).
  - apply int_seg_cast. exact HK.
  - apply int_seg_ext. intros u _. f_equal. apply Hp.
Qed.

Lemma cloth_eval_window0 : forall c t,
  cloth_ed c - cloth_sd c = 0 ->
  cloth_eval c t = cloth_eval c 0.
Proof.
  intros c t HL.
  unfold cloth_eval, cloth_s.
  replace (cloth_sd c + t * (cloth_ed c - cloth_sd c))
    with (cloth_sd c + 0 * (cloth_ed c - cloth_sd c)) by (rewrite HL; ring).
  replace (cloth_sd c + 0 * (cloth_ed c - cloth_sd c)) with (cloth_sd c) by ring.
  replace (cloth_sd c + 0 * (cloth_ed c - cloth_sd c)) with (cloth_sd c) by ring.
  reflexivity.
Qed.

Theorem clothoid_state_unique : forall e1 e2,
  cloth_wf e1 -> cloth_wf e2 ->
  cloth_eval e1 0 = cloth_eval e2 0 ->
  cloth_tangent e1 0 = cloth_tangent e2 0 ->
  cloth_curv e1 0 = cloth_curv e2 0 ->
  cloth_curv e1 1 = cloth_curv e2 1 ->
  cloth_ed e1 - cloth_sd e1 = cloth_ed e2 - cloth_sd e2 ->
  forall t, cloth_eval e1 t = cloth_eval e2 t.
Proof.
  intros e1 e2 Hw1 Hw2 Hp0 Ht0 Hk0 Hk1 HL t.
  set (L := cloth_ed e1 - cloth_sd e1).
  assert (HL2 : cloth_ed e2 - cloth_sd e2 = L).
  { unfold L. symmetry. exact HL. }
  destruct (Req_EM_T L 0) as [HZ|Hnz].
  - rewrite (cloth_eval_window0 e1 t) by (unfold L in HZ; exact HZ).
    rewrite (cloth_eval_window0 e2 t) by (rewrite HL2; exact HZ).
    exact Hp0.
  - set (k0 := cloth_curv e1 0).
    set (k1 := cloth_curv e1 1).
    assert (Hk0b : cloth_curv e2 0 = k0) by (symmetry; exact Hk0).
    assert (Hk1b : cloth_curv e2 1 = k1) by (symmetry; exact Hk1).
    assert (Hdk1 : cloth_kappa e1 (cloth_ed e1) - cloth_kappa e1 (cloth_sd e1)
                   = cloth_sigma e1 * L / (cloth_A e1 * cloth_A e1)).
    { unfold L. apply kappa_diff, cloth_A_nz, Hw1. }
    assert (Hdk2 : cloth_kappa e2 (cloth_ed e2) - cloth_kappa e2 (cloth_sd e2)
                   = cloth_sigma e2 * L / (cloth_A e2 * cloth_A e2)).
    { rewrite <- HL2. apply kappa_diff, cloth_A_nz, Hw2. }
    assert (Hs0 : cloth_s e1 0 = cloth_sd e1) by (unfold cloth_s; ring).
    assert (Hs1 : cloth_s e1 1 = cloth_ed e1) by (unfold cloth_s; ring).
    assert (Ht0b : cloth_s e2 0 = cloth_sd e2) by (unfold cloth_s; ring).
    assert (Ht1b : cloth_s e2 1 = cloth_ed e2) by (unfold cloth_s; ring).
    assert (Ek0 : k0 = cloth_kappa e1 (cloth_sd e1)).
    { unfold k0, cloth_curv. rewrite Hs0. reflexivity. }
    assert (Ek1 : k1 = cloth_kappa e1 (cloth_ed e1)).
    { unfold k1, cloth_curv. rewrite Hs1. reflexivity. }
    assert (Fk0 : k0 = cloth_kappa e2 (cloth_sd e2)).
    { rewrite <- Hk0b. unfold cloth_curv. rewrite Ht0b. reflexivity. }
    assert (Fk1 : k1 = cloth_kappa e2 (cloth_ed e2)).
    { rewrite <- Hk1b. unfold cloth_curv. rewrite Ht1b. reflexivity. }
    set (dk := k1 - k0).
    assert (Edk1 : dk = cloth_sigma e1 * L / (cloth_A e1 * cloth_A e1)).
    { unfold dk. rewrite Ek0, Ek1. exact Hdk1. }
    assert (Edk2 : dk = cloth_sigma e2 * L / (cloth_A e2 * cloth_A e2)).
    { unfold dk. rewrite Fk0, Fk1. exact Hdk2. }
    assert (HA1 : 0 < cloth_A e1 * cloth_A e1) by (apply cloth_AA_pos, Hw1).
    assert (HA2 : 0 < cloth_A e2 * cloth_A e2) by (apply cloth_AA_pos, Hw2).
    assert (Hdk : dk <> 0).
    { intro Z. apply Hnz.
      assert (Q : 0 = cloth_sigma e1 * L / (cloth_A e1 * cloth_A e1)).
      { rewrite <- Edk1. symmetry. exact Z. }
      assert (E : cloth_sigma e1 * L = 0).
      { apply (Rmult_eq_reg_r (/ (cloth_A e1 * cloth_A e1))).
        - rewrite Rmult_0_l. symmetry. exact Q.
        - apply Rinv_neq_0_compat, Rgt_not_eq. exact HA1. }
      destruct (cloth_sigma_pm e1) as [S|S]; rewrite S in E; nra. }
    assert (S1 : cloth_sigma e1 * dk = L / (cloth_A e1 * cloth_A e1)).
    { rewrite Edk1. unfold Rdiv.
      replace (cloth_sigma e1 * (cloth_sigma e1 * L * / (cloth_A e1 * cloth_A e1)))
        with ((cloth_sigma e1 * cloth_sigma e1) * L * / (cloth_A e1 * cloth_A e1))
        by ring.
      rewrite cloth_sigma_sq. field. nra. }
    assert (S2 : cloth_sigma e2 * dk = L / (cloth_A e2 * cloth_A e2)).
    { rewrite Edk2. unfold Rdiv.
      replace (cloth_sigma e2 * (cloth_sigma e2 * L * / (cloth_A e2 * cloth_A e2)))
        with ((cloth_sigma e2 * cloth_sigma e2) * L * / (cloth_A e2 * cloth_A e2))
        by ring.
      rewrite cloth_sigma_sq. field. nra. }
    assert (Hpin : cloth_sigma e1 = cloth_sigma e2).
    { assert (P1 : 0 < cloth_sigma e1 * (L * dk)).
      { replace (cloth_sigma e1 * (L * dk)) with (L * (cloth_sigma e1 * dk)) by ring.
        rewrite S1. unfold Rdiv.
        replace (L * (L * / (cloth_A e1 * cloth_A e1)))
          with (L * L * / (cloth_A e1 * cloth_A e1)) by ring.
        apply Rmult_lt_0_compat; [nra|].
        apply Rinv_0_lt_compat. exact HA1. }
      assert (P2 : 0 < cloth_sigma e2 * (L * dk)).
      { replace (cloth_sigma e2 * (L * dk)) with (L * (cloth_sigma e2 * dk)) by ring.
        rewrite S2. unfold Rdiv.
        replace (L * (L * / (cloth_A e2 * cloth_A e2)))
          with (L * L * / (cloth_A e2 * cloth_A e2)) by ring.
        apply Rmult_lt_0_compat; [nra|].
        apply Rinv_0_lt_compat. exact HA2. }
      destruct (cloth_sigma_pm e1) as [E1|E1];
      destruct (cloth_sigma_pm e2) as [E2|E2];
      rewrite ?E1, ?E2; try reflexivity;
      exfalso; rewrite ?E1 in P1; rewrite ?E2 in P2; lra. }
    assert (HAA : cloth_A e1 * cloth_A e1 = cloth_A e2 * cloth_A e2).
    { assert (Nz : cloth_sigma e1 * dk <> 0).
      { intro Z. apply Hnz.
        assert (E : L / (cloth_A e1 * cloth_A e1) = 0) by (rewrite <- S1; exact Z).
        apply (Rmult_eq_reg_r (/ (cloth_A e1 * cloth_A e1))).
        - rewrite Rmult_0_l. unfold Rdiv in E. exact E.
        - apply Rinv_neq_0_compat, Rgt_not_eq. exact HA1. }
      apply Rmult_eq_reg_l with (r := cloth_sigma e1 * dk); [|exact Nz].
      replace (cloth_sigma e1 * dk * (cloth_A e1 * cloth_A e1))
        with L.
      - rewrite Hpin.
        replace (cloth_sigma e2 * dk * (cloth_A e2 * cloth_A e2)) with L.
        + reflexivity.
        + rewrite S2. unfold Rdiv. field. nra.
      - rewrite S1. unfold Rdiv. field. nra. }
    assert (HA : cloth_A e1 = cloth_A e2).
    { apply Rsqr_inj.
      - apply Rlt_le. exact (proj1 Hw1).
      - apply Rlt_le. exact (proj1 Hw2).
      - unfold Rsqr. exact HAA. }
    assert (Hsd : cloth_sd e1 = cloth_sd e2).
    {       assert (E1 : cloth_sd e1 = cloth_sigma e1 * k0 * (cloth_A e1 * cloth_A e1)).
      { assert (Q : k0 * (cloth_A e1 * cloth_A e1) = cloth_sigma e1 * cloth_sd e1).
        { rewrite Ek0. unfold cloth_kappa, Rdiv. field. apply cloth_A_nz, Hw1. }
        transitivity (cloth_sigma e1 * (k0 * (cloth_A e1 * cloth_A e1))).
        - rewrite Q.
          replace (cloth_sigma e1 * (cloth_sigma e1 * cloth_sd e1))
            with ((cloth_sigma e1 * cloth_sigma e1) * cloth_sd e1) by ring.
          rewrite cloth_sigma_sq. ring.
        - ring. }
      assert (E2 : cloth_sd e2 = cloth_sigma e2 * k0 * (cloth_A e2 * cloth_A e2)).
      { assert (Q : k0 * (cloth_A e2 * cloth_A e2) = cloth_sigma e2 * cloth_sd e2).
        { rewrite Fk0. unfold cloth_kappa, Rdiv. field. apply cloth_A_nz, Hw2. }
        transitivity (cloth_sigma e2 * (k0 * (cloth_A e2 * cloth_A e2))).
        - rewrite Q.
          replace (cloth_sigma e2 * (cloth_sigma e2 * cloth_sd e2))
            with ((cloth_sigma e2 * cloth_sigma e2) * cloth_sd e2) by ring.
          rewrite cloth_sigma_sq. ring.
        - ring. }
      rewrite E1, E2, Hpin, HAA. reflexivity. }
    assert (Hed : cloth_ed e1 = cloth_ed e2).
    { assert (E : cloth_ed e1 = cloth_sd e1 + L) by (unfold L; ring).
      assert (F : cloth_ed e2 = cloth_sd e2 + L).
      { rewrite <- HL2. ring. }
      rewrite E, F, Hsd. reflexivity. }
    assert (Hpsi : forall s, cloth_psi e1 s = cloth_psi e2 s).
    { intro s. unfold cloth_psi. rewrite Hpin, HA. reflexivity. }
    assert (Hcos : cloth_cos0 e1 = cloth_cos0 e2 /\ cloth_sin0 e1 = cloth_sin0 e2).
    { set (psi := cloth_psi e1 (cloth_sd e1)).
      assert (Hpsi0 : cloth_psi e2 (cloth_sd e2) = psi).
      { unfold psi. rewrite <- Hsd. symmetry. apply Hpsi. }
      assert (Huv : cos psi * cos psi + sin psi * sin psi = 1).
      { pose proof (sin2_cos2 psi) as Hs. unfold Rsqr in Hs.
        rewrite Rplus_comm. exact Hs. }
      assert (T1 : cloth_tangent e1 0
                   = mkPoint (cloth_vx e1 (cloth_sd e1)) (cloth_vy e1 (cloth_sd e1))).
      { unfold cloth_tangent. rewrite Hs0. reflexivity. }
      assert (T2 : cloth_tangent e2 0
                   = mkPoint (cloth_vx e2 (cloth_sd e2)) (cloth_vy e2 (cloth_sd e2))).
      { unfold cloth_tangent. rewrite Ht0b. reflexivity. }
      assert (Hvt : cloth_vx e1 (cloth_sd e1) = cloth_vx e2 (cloth_sd e2) /\
                    cloth_vy e1 (cloth_sd e1) = cloth_vy e2 (cloth_sd e2)).
      { rewrite Ht0 in T1. rewrite T2 in T1. injection T1. intros Ey Ex.
        split; [symmetry; exact Ex|symmetry; exact Ey]. }
      destruct Hvt as [Hvx Hvy].
      assert (R1 := rotate_in (cloth_cos0 e1) (cloth_sin0 e1)
                     (cos psi) (sin psi)
                     (cloth_vx e1 (cloth_sd e1)) (cloth_vy e1 (cloth_sd e1))
                     Huv).
      assert (R1a : cloth_vx e1 (cloth_sd e1)
                    = cloth_cos0 e1 * cos psi - cloth_sin0 e1 * sin psi).
      { unfold cloth_vx, psi. reflexivity. }
      assert (R1b : cloth_vy e1 (cloth_sd e1)
                    = cloth_sin0 e1 * cos psi + cloth_cos0 e1 * sin psi).
      { unfold cloth_vy, psi. reflexivity. }
      specialize (R1 R1a R1b).
      assert (R2 := rotate_in (cloth_cos0 e2) (cloth_sin0 e2)
                     (cos (cloth_psi e2 (cloth_sd e2)))
                     (sin (cloth_psi e2 (cloth_sd e2)))
                     (cloth_vx e2 (cloth_sd e2)) (cloth_vy e2 (cloth_sd e2))
                     ).
      assert (Huv2 : cos (cloth_psi e2 (cloth_sd e2)) * cos (cloth_psi e2 (cloth_sd e2))
                     + sin (cloth_psi e2 (cloth_sd e2)) * sin (cloth_psi e2 (cloth_sd e2))
                     = 1).
      { rewrite Hpsi0. exact Huv. }
      assert (R2a : cloth_vx e2 (cloth_sd e2)
                    = cloth_cos0 e2 * cos (cloth_psi e2 (cloth_sd e2))
                      - cloth_sin0 e2 * sin (cloth_psi e2 (cloth_sd e2))).
      { unfold cloth_vx. reflexivity. }
      assert (R2b : cloth_vy e2 (cloth_sd e2)
                    = cloth_sin0 e2 * cos (cloth_psi e2 (cloth_sd e2))
                      + cloth_cos0 e2 * sin (cloth_psi e2 (cloth_sd e2))).
      { unfold cloth_vy. reflexivity. }
      specialize (R2 Huv2 R2a R2b).
      rewrite Hpsi0 in R2. rewrite <- Hvx, <- Hvy in R2.
      split; [rewrite (proj1 R1), (proj1 R2); reflexivity
             | rewrite (proj2 R1), (proj2 R2); reflexivity]. }
    destruct Hcos as [Hc0 Hs0e].
    assert (HIx : forall s, cloth_Icos e1 s = cloth_Icos e2 s).
    { intro s. apply cloth_Icos_sigma_A; [exact Hpin|exact HA]. }
    assert (HIy : forall s, cloth_Isin e1 s = cloth_Isin e2 s).
    { intro s. apply cloth_Isin_sigma_A; [exact Hpin|exact HA]. }
    assert (Hloc : aff_loc (cloth_place e1) = aff_loc (cloth_place e2)).
    { apply point_eq.
      - assert (P1 : px (cloth_eval e1 0)
                     = px (aff_loc (cloth_place e1))
                       + cloth_cos0 e1 * cloth_Icos e1 (cloth_sd e1)
                       - cloth_sin0 e1 * cloth_Isin e1 (cloth_sd e1)).
        { unfold cloth_eval, cloth_P, cloth_Px. rewrite Hs0. reflexivity. }
        assert (P2 : px (cloth_eval e2 0)
                     = px (aff_loc (cloth_place e2))
                       + cloth_cos0 e2 * cloth_Icos e2 (cloth_sd e2)
                       - cloth_sin0 e2 * cloth_Isin e2 (cloth_sd e2)).
        { unfold cloth_eval, cloth_P, cloth_Px. rewrite Ht0b. reflexivity. }
        rewrite Hp0 in P1. rewrite P2 in P1.
        rewrite <- Hsd, Hc0, Hs0e, (HIx (cloth_sd e1)), (HIy (cloth_sd e1)) in P1.
        lra.
      - assert (P1 : py (cloth_eval e1 0)
                     = py (aff_loc (cloth_place e1))
                       + cloth_sin0 e1 * cloth_Icos e1 (cloth_sd e1)
                       + cloth_cos0 e1 * cloth_Isin e1 (cloth_sd e1)).
        { unfold cloth_eval, cloth_P, cloth_Py. rewrite Hs0. reflexivity. }
        assert (P2 : py (cloth_eval e2 0)
                     = py (aff_loc (cloth_place e2))
                       + cloth_sin0 e2 * cloth_Icos e2 (cloth_sd e2)
                       + cloth_cos0 e2 * cloth_Isin e2 (cloth_sd e2)).
        { unfold cloth_eval, cloth_P, cloth_Py. rewrite Ht0b. reflexivity. }
        rewrite Hp0 in P1. rewrite P2 in P1.
        rewrite <- Hsd, Hc0, Hs0e, (HIx (cloth_sd e1)), (HIy (cloth_sd e1)) in P1.
        lra. }
    assert (Hst : cloth_s e1 t = cloth_s e2 t).
    { unfold cloth_s. rewrite Hsd, Hed. reflexivity. }
    apply point_eq.
    + unfold cloth_eval, cloth_P, cloth_Px. rewrite Hst.
      rewrite Hloc, Hc0, Hs0e, HIx, HIy. reflexivity.
    + unfold cloth_eval, cloth_P, cloth_Py. rewrite Hst.
      rewrite Hloc, Hc0, Hs0e, HIx, HIy. reflexivity.
Qed.

Lemma norm2_is_the_state : forall st law m0 m1 e,
  0 < sl_len law ->
  sl_k0 law <> sl_k1 law ->
  pt_h2 (st_dir st) = 1 ->
  (m0 = None /\ m1 = None) \/ (exists a b, m0 = Some a /\ m1 = Some b) ->
  cloth_wf e ->
  cloth_eval e 0 = st_pos st ->
  cloth_tangent e 0 = st_dir st ->
  cloth_curv e 0 = sl_k0 law ->
  cloth_curv e 1 = sl_k1 law ->
  cloth_ed e - cloth_sd e = sl_len law ->
  forall t, cloth_eval e t = cloth_eval (norm2 st law m0 m1) t.
Proof.
  intros st law m0 m1 e HL Hne Hu Hm Hw Hp Ht Hc0 Hc1 Hlen t.
  apply (clothoid_state_unique e (norm2 st law m0 m1)).
  - exact Hw.
  - apply norm2_wf; assumption.
  - rewrite Hp. symmetry. apply norm2_start. exact Hu.
  - rewrite Ht. symmetry. apply norm2_start_dir; assumption.
  - rewrite Hc0. symmetry. apply (proj1 (norm2_curv st law m0 m1 HL Hne Hu)).
  - rewrite Hc1. symmetry. apply (proj2 (norm2_curv st law m0 m1 HL Hne Hu)).
  - rewrite Hlen. symmetry.
    apply (proj1 (norm2_length st law m0 m1 HL Hne Hu)).
Qed.

Print Assumptions point_eq.
Print Assumptions law_sigma_sq.
Print Assumptions law_dk_nz.
Print Assumptions law_A2_pos.
Print Assumptions law_A_pos.
Print Assumptions law_A_sq.
Print Assumptions law_sigma_dk.
Print Assumptions law_ed_sd.
Print Assumptions norm2_ref_sumsq.
Print Assumptions norm2_cross_raw.
Print Assumptions norm2_h2.
Print Assumptions norm2_cross.
Print Assumptions norm2_sigma.
Print Assumptions norm2_hypot.
Print Assumptions norm2_cos0_eq.
Print Assumptions norm2_sin0_eq.
Print Assumptions norm2_Icos_probe.
Print Assumptions norm2_Isin_probe.
Print Assumptions norm2_wf.
Print Assumptions norm2_start.
Print Assumptions rotate_out.
Print Assumptions norm2_psi_sd.
Print Assumptions norm2_psi_ed.
Print Assumptions norm2_start_dir.
Print Assumptions norm2_kappa_sd.
Print Assumptions norm2_kappa_ed.
Print Assumptions norm2_curv.
Print Assumptions norm2_d_eq.
Print Assumptions norm2_d_pos.
Print Assumptions norm2_h2_nz.
Print Assumptions norm2_rad_nn.
Print Assumptions norm2_Lv_nn.
Print Assumptions norm2_frame_abs.
Print Assumptions norm2_s_in_rad.
Print Assumptions norm2_psi_lip.
Print Assumptions norm2_comb_lip.
Print Assumptions norm2_scaled_lip.
Print Assumptions norm2_nvx_lip.
Print Assumptions norm2_nvy_lip.
Print Assumptions norm2_ngx_deriv.
Print Assumptions norm2_ngy_deriv.
Print Assumptions norm2_speed_const.
Print Assumptions norm2_speed_lip.
Print Assumptions norm2_length.
Print Assumptions norm2_exit.
Print Assumptions cloth_sigma_pm.
Print Assumptions cloth_sigma_sq.
Print Assumptions cloth_A_nz.
Print Assumptions cloth_AA_pos.
Print Assumptions kappa_diff.
Print Assumptions rotate_in.
Print Assumptions int_seg_cast.
Print Assumptions cloth_Icos_sigma_A.
Print Assumptions cloth_Isin_sigma_A.
Print Assumptions cloth_eval_window0.
Print Assumptions clothoid_state_unique.
Print Assumptions norm2_is_the_state.
