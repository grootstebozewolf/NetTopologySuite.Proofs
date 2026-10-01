(* ============================================================================
   NetTopologySuite.Proofs.ClothoidFresnelInc
   ----------------------------------------------------------------------------
   Ordered Fresnel increments: Icos(b)-Icos(a) and Isin(b)-Isin(a) equal
   int_seg of cos(psi) and sin(psi) on [a,b], with no lip_ftc.
   claimId: none. 3-axiom host. No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia ZArith.
From Stdlib Require Import Ranalysis1.
From NTS.Proofs Require Import Distance LipInt SheetHenClothoidCore Atan2.
Local Open Scope R_scope.
Lemma rho_h2 : forall c, cloth_wf c -> cloth_h2 c <> 0.
Proof. intros c [_ [Hh _]]. exact Hh. Qed.
Lemma rho_A : forall c, cloth_wf c -> 0 < cloth_A c.
Proof. intros c [HA _]. exact HA. Qed.
Lemma cloth_frame_sumsq :
  forall c, cloth_h2 c <> 0 ->
    cloth_cos0 c * cloth_cos0 c + cloth_sin0 c * cloth_sin0 c = 1.
Proof.
  intros c Hnz.
  assert (Hpos : 0 < cloth_h2 c).
  { assert (Hnn : 0 <= cloth_h2 c).
    { unfold cloth_h2, aff_h2.
      apply Rplus_le_le_0_compat; apply Rle_0_sqr. }
    destruct (Req_EM_T (cloth_h2 c) 0) as [Hz|Hne]; [| lra].
    lra. }
  set (h := sqrt (cloth_h2 c)).
  assert (Hh : h <> 0).
  { unfold h. intro Hz.
    apply (Rlt_irrefl 0). rewrite <- Hz at 2. apply sqrt_lt_R0. exact Hpos. }
  assert (Eh : h * h = cloth_h2 c).
  { unfold h. apply sqrt_sqrt. apply Rlt_le. exact Hpos. }
  unfold cloth_cos0, cloth_sin0, cloth_hypot, Rdiv. fold h.
  replace (px (aff_ref1 (cloth_place c)) * / h *
           (px (aff_ref1 (cloth_place c)) * / h) +
           py (aff_ref1 (cloth_place c)) * / h *
           (py (aff_ref1 (cloth_place c)) * / h))
    with ((px (aff_ref1 (cloth_place c)) * px (aff_ref1 (cloth_place c)) +
           py (aff_ref1 (cloth_place c)) * py (aff_ref1 (cloth_place c))) *
          / (h * h)) by (field; exact Hh).
  rewrite Eh.
  unfold cloth_h2, aff_h2. field. exact Hnz.
Qed.
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
Definition line_offset (Q : Point) (phi : R) (P : Point) : R :=
  (- sin phi) * (px P - px Q) + (cos phi) * (py P - py Q).
Definition rho_L (c : ClothoidEgg) (a b : R) : R :=
  cloth_phi_K c (Rmax (Rabs a) (Rabs b)).
Lemma rho_L_nn : forall c a b, 0 <= rho_L c a b.
Proof. intros. unfold rho_L. apply cloth_phi_K_nonneg. Qed.
Lemma rho_rad_nn : forall a b, 0 <= Rmax (Rabs a) (Rabs b).
Proof.
  intros. apply Rle_trans with (Rabs a); [apply Rabs_pos | apply Rmax_l].
Qed.
Lemma abs_seg : forall a b x,
  Rmin a b <= x <= Rmax a b -> Rabs x <= Rmax (Rabs a) (Rabs b).
Proof.
  intros a b x Hx.
  set (rad := Rmax (Rabs a) (Rabs b)).
  apply Rabs_le. split.
  - apply Rle_trans with (Rmin a b); [| exact (proj1 Hx)].
    apply Rmin_glb.
    + apply Rle_trans with (- Rabs a).
      * apply Ropp_le_contravar. unfold rad. apply Rmax_l.
      * destruct (Rle_dec 0 a) as [P|N].
        -- rewrite (Rabs_right a (Rle_ge _ _ P)). lra.
        -- apply Rnot_le_lt in N. rewrite (Rabs_left a N). lra.
    + apply Rle_trans with (- Rabs b).
      * apply Ropp_le_contravar. unfold rad. apply Rmax_r.
      * destruct (Rle_dec 0 b) as [P|N].
        -- rewrite (Rabs_right b (Rle_ge _ _ P)). lra.
        -- apply Rnot_le_lt in N. rewrite (Rabs_left b N). lra.
  - apply Rle_trans with (Rmax a b); [exact (proj2 Hx)|].
    apply Rmax_lub.
    + apply Rle_trans with (Rabs a); [apply Rle_abs | unfold rad; apply Rmax_l].
    + apply Rle_trans with (Rabs b); [apply Rle_abs | unfold rad; apply Rmax_r].
Qed.
Lemma psi_lip_ball : forall c rad x y,
  0 < cloth_A c -> 0 <= rad ->
  Rabs x <= rad -> Rabs y <= rad ->
  Rabs (cloth_psi c x - cloth_psi c y) <= cloth_phi_K c rad * Rabs (x - y).
Proof.
  intros c rad x y HA Hrad Hx Hy.
  set (AA := cloth_A c * cloth_A c).
  assert (Hpos : 0 < AA) by (unfold AA; nra).
  assert (HA0 : cloth_A c <> 0) by lra.
  assert (Hinv : 0 < / (2 * AA)) by (apply Rinv_0_lt_compat; lra).
  unfold cloth_psi, cloth_phi_K, Rdiv.
  assert (E :
    (cloth_sigma c * x * x) * / (2 * cloth_A c * cloth_A c) -
    (cloth_sigma c * y * y) * / (2 * cloth_A c * cloth_A c)
    = cloth_sigma c * ((x - y) * (x + y)) * / (2 * AA)).
  { unfold AA. field. exact HA0. }
  rewrite E. clear E.
  rewrite !Rabs_mult, cloth_sigma_abs.
  assert (Habs : Rabs (/ (2 * AA)) = / (2 * AA)).
  { apply Rabs_pos_eq. apply Rlt_le. exact Hinv. }
  rewrite Habs. clear Habs.
  assert (Hxy : Rabs (x + y) <= 2 * rad).
  { eapply Rle_trans; [apply Rabs_triang|]. lra. }
  apply Rle_trans with ((1 * (Rabs (x - y) * (2 * rad))) * / (2 * AA)).
  - apply Rmult_le_compat_r; [apply Rlt_le; exact Hinv|].
    apply Rmult_le_compat_l; [lra|].
    apply Rmult_le_compat_l; [apply Rabs_pos| exact Hxy].
  - rewrite (Rabs_right rad (Rle_ge _ _ Hrad)). unfold AA. right. field. exact HA0.
Qed.
Lemma cos_psi_ball : forall c a b x y,
  0 < cloth_A c ->
  Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
  Rabs (cos (cloth_psi c x) - cos (cloth_psi c y))
    <= rho_L c a b * Rabs (x - y).
Proof.
  intros c a b x y HA Hx Hy.
  eapply Rle_trans; [apply cos_lip|].
  unfold rho_L. apply psi_lip_ball; [exact HA | apply rho_rad_nn | |].
  - apply abs_seg. exact Hx.
  - apply abs_seg. exact Hy.
Qed.
Lemma sin_psi_ball : forall c a b x y,
  0 < cloth_A c ->
  Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
  Rabs (sin (cloth_psi c x) - sin (cloth_psi c y))
    <= rho_L c a b * Rabs (x - y).
Proof.
  intros c a b x y HA Hx Hy.
  eapply Rle_trans; [apply sin_lip|].
  unfold rho_L. apply psi_lip_ball; [exact HA | apply rho_rad_nn | |].
  - apply abs_seg. exact Hx.
  - apply abs_seg. exact Hy.
Qed.
Lemma sin_head_lip : forall c phi a b x y,
  cloth_wf c ->
  Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
  Rabs (sin (cloth_heading c x - phi) - sin (cloth_heading c y - phi))
    <= rho_L c a b * Rabs (x - y).
Proof.
  intros c phi a b x y Hwf Hx Hy.
  eapply Rle_trans; [apply sin_lip|].
  unfold cloth_heading.
  replace ((cloth_heading0 c + cloth_psi c x - phi) -
           (cloth_heading0 c + cloth_psi c y - phi))
    with (cloth_psi c x - cloth_psi c y) by ring.
  unfold rho_L. apply psi_lip_ball; [apply rho_A; exact Hwf | apply rho_rad_nn | |].
  - apply abs_seg. exact Hx.
  - apply abs_seg. exact Hy.
Qed.
Lemma cos_lip_prefix : forall c s0 s,
  cloth_wf c -> 0 <= s0 -> s0 <= s ->
  forall x y,
    Rmin 0 s0 <= x <= Rmax 0 s0 ->
    Rmin 0 s0 <= y <= Rmax 0 s0 ->
    Rabs (cos (cloth_psi c x) - cos (cloth_psi c y))
      <= cloth_phi_K c s * Rabs (x - y).
Proof.
  intros c s0 s Hwf Hs0 Hle x y Hx Hy.
  eapply Rle_trans; [apply (cloth_cos_psi_lip c s0 x y Hx Hy)|].
  apply Rmult_le_compat_r; [apply Rabs_pos|].
  unfold cloth_phi_K, Rdiv.
  assert (HA : 0 < cloth_A c) by (apply rho_A; exact Hwf).
  assert (Hinv : 0 <= / (cloth_A c * cloth_A c)).
  { apply Rlt_le, Rinv_0_lt_compat. nra. }
  apply Rmult_le_compat_r; [exact Hinv|].
  rewrite (Rabs_right s0 (Rle_ge _ _ Hs0)).
  rewrite (Rabs_right s) by lra. lra.
Qed.
Lemma cos_lip_tail : forall c a b,
  cloth_wf c -> 0 <= a -> a <= b ->
  forall x y,
    Rmin a b <= x <= Rmax a b ->
    Rmin a b <= y <= Rmax a b ->
    Rabs (cos (cloth_psi c x) - cos (cloth_psi c y))
      <= cloth_phi_K c b * Rabs (x - y).
Proof.
  intros c a b Hwf Ha Hab x y Hx Hy.
  rewrite (Rmin_left a b Hab) in Hx, Hy.
  rewrite (Rmax_right a b Hab) in Hx, Hy.
  apply (cloth_cos_psi_lip c b).
  - rewrite (Rmin_left 0 b) by lra. rewrite (Rmax_right 0 b) by lra. lra.
  - rewrite (Rmin_left 0 b) by lra. rewrite (Rmax_right 0 b) by lra. lra.
Qed.
Lemma icos_nonneg : forall c a b (Hwf : cloth_wf c),
  0 <= a -> a <= b ->
  cloth_Icos c b - cloth_Icos c a =
  int_seg (fun u => cos (cloth_psi c u)) (rho_L c a b) a b
    (rho_L_nn c a b)
    (fun x y Hx Hy => cos_psi_ball c a b x y (rho_A c Hwf) Hx Hy).
Proof.
  intros c a b Hwf Ha Hab.
  assert (Erad : rho_L c a b = cloth_phi_K c b).
  { unfold rho_L.
    rewrite (Rabs_right a (Rle_ge _ _ Ha)).
    rewrite (Rabs_right b) by lra.
    rewrite (Rmax_right a b Hab). reflexivity. }
  set (g := fun u : R => cos (cloth_psi c u)).
  assert (Hadd := int_seg_add g (cloth_phi_K c b) 0 a b
    (cloth_phi_K_nonneg c b)
    (cloth_cos_psi_lip c b)
    (cos_lip_prefix c a b Hwf Ha Hab)
    (cos_lip_tail c a b Hwf Ha Hab)
    Ha Hab).
  assert (Hb0 : cloth_Icos c b =
    int_seg g (cloth_phi_K c b) 0 b (cloth_phi_K_nonneg c b)
      (cloth_cos_psi_lip c b)).
  { unfold cloth_Icos, g. apply int_seg_pi. }
  assert (Ha0 : cloth_Icos c a =
    int_seg g (cloth_phi_K c b) 0 a (cloth_phi_K_nonneg c b)
      (cos_lip_prefix c a b Hwf Ha Hab)).
  { unfold cloth_Icos, g.
    etransitivity.
    - apply int_seg_pi.
    - apply (int_seg_L g (cloth_phi_K c a) (cloth_phi_K c b) 0 a
        (cloth_phi_K_nonneg c a) (cloth_phi_K_nonneg c b)
        (cloth_cos_psi_lip c a) (cos_lip_prefix c a b Hwf Ha Hab)). }
  rewrite Hb0, Ha0, Hadd.
  replace (int_seg g (cloth_phi_K c b) 0 a (cloth_phi_K_nonneg c b)
             (cos_lip_prefix c a b Hwf Ha Hab) +
           int_seg g (cloth_phi_K c b) a b (cloth_phi_K_nonneg c b)
             (cos_lip_tail c a b Hwf Ha Hab) -
           int_seg g (cloth_phi_K c b) 0 a (cloth_phi_K_nonneg c b)
             (cos_lip_prefix c a b Hwf Ha Hab))
    with (int_seg g (cloth_phi_K c b) a b (cloth_phi_K_nonneg c b)
            (cos_lip_tail c a b Hwf Ha Hab)) by ring.
  apply (int_seg_L g (cloth_phi_K c b) (rho_L c a b) a b
    (cloth_phi_K_nonneg c b) (rho_L_nn c a b)
    (cos_lip_tail c a b Hwf Ha Hab)
    (fun x y Hx Hy => cos_psi_ball c a b x y (rho_A c Hwf) Hx Hy)).
Qed.
Lemma seg_in_rad : forall a b p q z,
  Rabs p <= Rmax (Rabs a) (Rabs b) ->
  Rabs q <= Rmax (Rabs a) (Rabs b) ->
  Rmin p q <= z <= Rmax p q ->
  Rabs z <= Rmax (Rabs a) (Rabs b).
Proof.
  intros a b p q z Hp Hq Hz.
  apply Rle_trans with (Rmax (Rabs p) (Rabs q)).
  - apply abs_seg. exact Hz.
  - apply Rmax_lub; assumption.
Qed.
Lemma cos_on_rad : forall c a b p q,
  cloth_wf c ->
  Rabs p <= Rmax (Rabs a) (Rabs b) ->
  Rabs q <= Rmax (Rabs a) (Rabs b) ->
  forall x y,
    Rmin p q <= x <= Rmax p q ->
    Rmin p q <= y <= Rmax p q ->
    Rabs (cos (cloth_psi c x) - cos (cloth_psi c y))
      <= rho_L c a b * Rabs (x - y).
Proof.
  intros c a b p q Hwf Hp Hq x y Hx Hy.
  eapply Rle_trans; [apply cos_lip|].
  unfold rho_L. apply psi_lip_ball.
  - apply rho_A. exact Hwf.
  - apply rho_rad_nn.
  - apply (seg_in_rad a b p q x Hp Hq Hx).
  - apply (seg_in_rad a b p q y Hp Hq Hy).
Qed.
Lemma cos_lip_flip : forall c s x y,
  Rmin s 0 <= x <= Rmax s 0 ->
  Rmin s 0 <= y <= Rmax s 0 ->
  Rabs (cos (cloth_psi c x) - cos (cloth_psi c y))
    <= cloth_phi_K c s * Rabs (x - y).
Proof.
  intros c s x y Hx Hy. apply cloth_cos_psi_lip.
  - rewrite Rmin_comm, Rmax_comm. exact Hx.
  - rewrite Rmin_comm, Rmax_comm. exact Hy.
Qed.
Lemma icos_straddle : forall c a b (Hwf : cloth_wf c),
  a <= 0 -> 0 <= b ->
  cloth_Icos c b - cloth_Icos c a =
  int_seg (fun u => cos (cloth_psi c u)) (rho_L c a b) a b
    (rho_L_nn c a b)
    (fun x y Hx Hy => cos_psi_ball c a b x y (rho_A c Hwf) Hx Hy).
Proof.
  intros c a b Hwf Ha Hb.
  set (rad := Rmax (Rabs a) (Rabs b)).
  assert (H0 : Rabs 0 <= rad) by (unfold rad; rewrite Rabs_R0; apply rho_rad_nn).
  assert (HaR : Rabs a <= rad) by (unfold rad; apply Rmax_l).
  assert (HbR : Rabs b <= rad) by (unfold rad; apply Rmax_r).
  set (g := fun u : R => cos (cloth_psi c u)).
  assert (Hadd := int_seg_add g (rho_L c a b) a 0 b (rho_L_nn c a b)
    (fun x y Hx Hy => cos_psi_ball c a b x y (rho_A c Hwf) Hx Hy)
    (cos_on_rad c a b a 0 Hwf HaR H0)
    (cos_on_rad c a b 0 b Hwf H0 HbR)
    Ha Hb).
  assert (Eb : cloth_Icos c b =
      int_seg g (rho_L c a b) 0 b (rho_L_nn c a b)
        (cos_on_rad c a b 0 b Hwf H0 HbR)).
  { unfold cloth_Icos. fold g.
    apply (int_seg_L g (cloth_phi_K c b) (rho_L c a b) 0 b
      (cloth_phi_K_nonneg c b) (rho_L_nn c a b)
      (cloth_cos_psi_lip c b)
      (cos_on_rad c a b 0 b Hwf H0 HbR)). }
  assert (Ea : cloth_Icos c a =
      - int_seg g (rho_L c a b) a 0 (rho_L_nn c a b)
          (cos_on_rad c a b a 0 Hwf HaR H0)).
  { unfold cloth_Icos. fold g.
    rewrite (int_seg_swap g (cloth_phi_K c a) 0 a
      (cloth_phi_K_nonneg c a) (cloth_cos_psi_lip c a)
      (cos_lip_flip c a)).
    apply f_equal.
    apply (int_seg_L g (cloth_phi_K c a) (rho_L c a b) a 0
      (cloth_phi_K_nonneg c a) (rho_L_nn c a b)
      (cos_lip_flip c a)
      (cos_on_rad c a b a 0 Hwf HaR H0)). }
  rewrite Hadd, Eb, Ea. ring.
Qed.
Lemma icos_nonpos : forall c a b (Hwf : cloth_wf c),
  a <= b -> b <= 0 ->
  cloth_Icos c b - cloth_Icos c a =
  int_seg (fun u => cos (cloth_psi c u)) (rho_L c a b) a b
    (rho_L_nn c a b)
    (fun x y Hx Hy => cos_psi_ball c a b x y (rho_A c Hwf) Hx Hy).
Proof.
  intros c a b Hwf Hab Hbn.
  set (rad := Rmax (Rabs a) (Rabs b)).
  assert (H0 : Rabs 0 <= rad) by (unfold rad; rewrite Rabs_R0; apply rho_rad_nn).
  assert (HaR : Rabs a <= rad) by (unfold rad; apply Rmax_l).
  assert (HbR : Rabs b <= rad) by (unfold rad; apply Rmax_r).
  set (g := fun u : R => cos (cloth_psi c u)).
  assert (Hadd : int_seg g (rho_L c a b) a 0 (rho_L_nn c a b)
              (cos_on_rad c a b a 0 Hwf HaR H0) =
            int_seg g (rho_L c a b) a b (rho_L_nn c a b)
              (fun x y Hx Hy => cos_psi_ball c a b x y (rho_A c Hwf) Hx Hy) +
            int_seg g (rho_L c a b) b 0 (rho_L_nn c a b)
              (cos_on_rad c a b b 0 Hwf HbR H0)).
  { apply (int_seg_add g (rho_L c a b) a b 0 (rho_L_nn c a b)
      (cos_on_rad c a b a 0 Hwf HaR H0)
      (fun x y Hx Hy => cos_psi_ball c a b x y (rho_A c Hwf) Hx Hy)
      (cos_on_rad c a b b 0 Hwf HbR H0) Hab Hbn). }
  assert (Ea : int_seg g (rho_L c a b) a 0 (rho_L_nn c a b)
            (cos_on_rad c a b a 0 Hwf HaR H0) = - cloth_Icos c a).
  { unfold cloth_Icos. fold g.
    rewrite (int_seg_swap g (cloth_phi_K c a) 0 a
      (cloth_phi_K_nonneg c a) (cloth_cos_psi_lip c a) (cos_lip_flip c a)).
    rewrite Ropp_involutive.
    apply (int_seg_L g (rho_L c a b) (cloth_phi_K c a) a 0
      (rho_L_nn c a b) (cloth_phi_K_nonneg c a)
      (cos_on_rad c a b a 0 Hwf HaR H0)
      (cos_lip_flip c a)). }
  assert (Eb : int_seg g (rho_L c a b) b 0 (rho_L_nn c a b)
            (cos_on_rad c a b b 0 Hwf HbR H0) = - cloth_Icos c b).
  { unfold cloth_Icos. fold g.
    rewrite (int_seg_swap g (cloth_phi_K c b) 0 b
      (cloth_phi_K_nonneg c b) (cloth_cos_psi_lip c b) (cos_lip_flip c b)).
    rewrite Ropp_involutive.
    apply (int_seg_L g (rho_L c a b) (cloth_phi_K c b) b 0
      (rho_L_nn c a b) (cloth_phi_K_nonneg c b)
      (cos_on_rad c a b b 0 Hwf HbR H0)
      (cos_lip_flip c b)). }
  assert (Eab : int_seg g (rho_L c a b) a b (rho_L_nn c a b)
            (fun x y Hx Hy => cos_psi_ball c a b x y (rho_A c Hwf) Hx Hy)
          = int_seg g (rho_L c a b) a 0 (rho_L_nn c a b)
              (cos_on_rad c a b a 0 Hwf HaR H0) -
            int_seg g (rho_L c a b) b 0 (rho_L_nn c a b)
              (cos_on_rad c a b b 0 Hwf HbR H0)).
  { rewrite Hadd. ring. }
  rewrite Eab, Ea, Eb. ring.
Qed.
Lemma icos_ordered : forall c a b (Hwf : cloth_wf c),
  a <= b ->
  cloth_Icos c b - cloth_Icos c a =
  int_seg (fun u => cos (cloth_psi c u)) (rho_L c a b) a b
    (rho_L_nn c a b)
    (fun x y Hx Hy => cos_psi_ball c a b x y (rho_A c Hwf) Hx Hy).
Proof.
  intros c a b Hwf Hab.
  destruct (Rle_dec 0 a) as [Ha|Ha].
  - apply icos_nonneg; assumption.
  - apply Rnot_le_lt in Ha.
    destruct (Rle_dec b 0) as [Hb|Hb].
    + apply icos_nonpos; assumption.
    + apply Rnot_le_lt in Hb. apply icos_straddle; lra.
Qed.
Lemma sin_lip_prefix : forall c s0 s,
  cloth_wf c -> 0 <= s0 -> s0 <= s ->
  forall x y,
    Rmin 0 s0 <= x <= Rmax 0 s0 ->
    Rmin 0 s0 <= y <= Rmax 0 s0 ->
    Rabs (sin (cloth_psi c x) - sin (cloth_psi c y))
      <= cloth_phi_K c s * Rabs (x - y).
Proof.
  intros c s0 s Hwf Hs0 Hle x y Hx Hy.
  eapply Rle_trans; [apply (cloth_sin_psi_lip c s0 x y Hx Hy)|].
  apply Rmult_le_compat_r; [apply Rabs_pos|].
  unfold cloth_phi_K, Rdiv.
  assert (HA : 0 < cloth_A c) by (apply rho_A; exact Hwf).
  assert (Hinv : 0 <= / (cloth_A c * cloth_A c)).
  { apply Rlt_le, Rinv_0_lt_compat. nra. }
  apply Rmult_le_compat_r; [exact Hinv|].
  rewrite (Rabs_right s0 (Rle_ge _ _ Hs0)).
  rewrite (Rabs_right s) by lra. lra.
Qed.
Lemma sin_lip_tail : forall c a b,
  cloth_wf c -> 0 <= a -> a <= b ->
  forall x y,
    Rmin a b <= x <= Rmax a b ->
    Rmin a b <= y <= Rmax a b ->
    Rabs (sin (cloth_psi c x) - sin (cloth_psi c y))
      <= cloth_phi_K c b * Rabs (x - y).
Proof.
  intros c a b Hwf Ha Hab x y Hx Hy.
  rewrite (Rmin_left a b Hab) in Hx, Hy.
  rewrite (Rmax_right a b Hab) in Hx, Hy.
  apply (cloth_sin_psi_lip c b).
  - rewrite (Rmin_left 0 b) by lra. rewrite (Rmax_right 0 b) by lra. lra.
  - rewrite (Rmin_left 0 b) by lra. rewrite (Rmax_right 0 b) by lra. lra.
Qed.
Lemma isin_nonneg : forall c a b (Hwf : cloth_wf c),
  0 <= a -> a <= b ->
  cloth_Isin c b - cloth_Isin c a =
  int_seg (fun u => sin (cloth_psi c u)) (rho_L c a b) a b
    (rho_L_nn c a b)
    (fun x y Hx Hy => sin_psi_ball c a b x y (rho_A c Hwf) Hx Hy).
Proof.
  intros c a b Hwf Ha Hab.
  assert (Erad : rho_L c a b = cloth_phi_K c b).
  { unfold rho_L.
    rewrite (Rabs_right a (Rle_ge _ _ Ha)).
    rewrite (Rabs_right b) by lra.
    rewrite (Rmax_right a b Hab). reflexivity. }
  set (g := fun u : R => sin (cloth_psi c u)).
  assert (Hadd := int_seg_add g (cloth_phi_K c b) 0 a b
    (cloth_phi_K_nonneg c b)
    (cloth_sin_psi_lip c b)
    (sin_lip_prefix c a b Hwf Ha Hab)
    (sin_lip_tail c a b Hwf Ha Hab)
    Ha Hab).
  assert (Hb0 : cloth_Isin c b =
    int_seg g (cloth_phi_K c b) 0 b (cloth_phi_K_nonneg c b)
      (cloth_sin_psi_lip c b)).
  { unfold cloth_Isin, g. apply int_seg_pi. }
  assert (Ha0 : cloth_Isin c a =
    int_seg g (cloth_phi_K c b) 0 a (cloth_phi_K_nonneg c b)
      (sin_lip_prefix c a b Hwf Ha Hab)).
  { unfold cloth_Isin, g.
    etransitivity.
    - apply int_seg_pi.
    - apply (int_seg_L g (cloth_phi_K c a) (cloth_phi_K c b) 0 a
        (cloth_phi_K_nonneg c a) (cloth_phi_K_nonneg c b)
        (cloth_sin_psi_lip c a) (sin_lip_prefix c a b Hwf Ha Hab)). }
  rewrite Hb0, Ha0, Hadd.
  replace (int_seg g (cloth_phi_K c b) 0 a (cloth_phi_K_nonneg c b)
             (sin_lip_prefix c a b Hwf Ha Hab) +
           int_seg g (cloth_phi_K c b) a b (cloth_phi_K_nonneg c b)
             (sin_lip_tail c a b Hwf Ha Hab) -
           int_seg g (cloth_phi_K c b) 0 a (cloth_phi_K_nonneg c b)
             (sin_lip_prefix c a b Hwf Ha Hab))
    with (int_seg g (cloth_phi_K c b) a b (cloth_phi_K_nonneg c b)
            (sin_lip_tail c a b Hwf Ha Hab)) by ring.
  apply (int_seg_L g (cloth_phi_K c b) (rho_L c a b) a b
    (cloth_phi_K_nonneg c b) (rho_L_nn c a b)
    (sin_lip_tail c a b Hwf Ha Hab)
    (fun x y Hx Hy => sin_psi_ball c a b x y (rho_A c Hwf) Hx Hy)).
Qed.
Lemma sin_on_rad : forall c a b p q,
  cloth_wf c ->
  Rabs p <= Rmax (Rabs a) (Rabs b) ->
  Rabs q <= Rmax (Rabs a) (Rabs b) ->
  forall x y,
    Rmin p q <= x <= Rmax p q ->
    Rmin p q <= y <= Rmax p q ->
    Rabs (sin (cloth_psi c x) - sin (cloth_psi c y))
      <= rho_L c a b * Rabs (x - y).
Proof.
  intros c a b p q Hwf Hp Hq x y Hx Hy.
  eapply Rle_trans; [apply sin_lip|].
  unfold rho_L. apply psi_lip_ball.
  - apply rho_A. exact Hwf.
  - apply rho_rad_nn.
  - apply (seg_in_rad a b p q x Hp Hq Hx).
  - apply (seg_in_rad a b p q y Hp Hq Hy).
Qed.
Lemma sin_lip_flip : forall c s x y,
  Rmin s 0 <= x <= Rmax s 0 ->
  Rmin s 0 <= y <= Rmax s 0 ->
  Rabs (sin (cloth_psi c x) - sin (cloth_psi c y))
    <= cloth_phi_K c s * Rabs (x - y).
Proof.
  intros c s x y Hx Hy. apply cloth_sin_psi_lip.
  - rewrite Rmin_comm, Rmax_comm. exact Hx.
  - rewrite Rmin_comm, Rmax_comm. exact Hy.
Qed.
Lemma isin_straddle : forall c a b (Hwf : cloth_wf c),
  a <= 0 -> 0 <= b ->
  cloth_Isin c b - cloth_Isin c a =
  int_seg (fun u => sin (cloth_psi c u)) (rho_L c a b) a b
    (rho_L_nn c a b)
    (fun x y Hx Hy => sin_psi_ball c a b x y (rho_A c Hwf) Hx Hy).
Proof.
  intros c a b Hwf Ha Hb.
  set (rad := Rmax (Rabs a) (Rabs b)).
  assert (H0 : Rabs 0 <= rad) by (unfold rad; rewrite Rabs_R0; apply rho_rad_nn).
  assert (HaR : Rabs a <= rad) by (unfold rad; apply Rmax_l).
  assert (HbR : Rabs b <= rad) by (unfold rad; apply Rmax_r).
  set (g := fun u : R => sin (cloth_psi c u)).
  assert (Hadd := int_seg_add g (rho_L c a b) a 0 b (rho_L_nn c a b)
    (fun x y Hx Hy => sin_psi_ball c a b x y (rho_A c Hwf) Hx Hy)
    (sin_on_rad c a b a 0 Hwf HaR H0)
    (sin_on_rad c a b 0 b Hwf H0 HbR)
    Ha Hb).
  assert (Eb : cloth_Isin c b =
      int_seg g (rho_L c a b) 0 b (rho_L_nn c a b)
        (sin_on_rad c a b 0 b Hwf H0 HbR)).
  { unfold cloth_Isin. fold g.
    apply (int_seg_L g (cloth_phi_K c b) (rho_L c a b) 0 b
      (cloth_phi_K_nonneg c b) (rho_L_nn c a b)
      (cloth_sin_psi_lip c b)
      (sin_on_rad c a b 0 b Hwf H0 HbR)). }
  assert (Ea : cloth_Isin c a =
      - int_seg g (rho_L c a b) a 0 (rho_L_nn c a b)
          (sin_on_rad c a b a 0 Hwf HaR H0)).
  { unfold cloth_Isin. fold g.
    rewrite (int_seg_swap g (cloth_phi_K c a) 0 a
      (cloth_phi_K_nonneg c a) (cloth_sin_psi_lip c a)
      (sin_lip_flip c a)).
    apply f_equal.
    apply (int_seg_L g (cloth_phi_K c a) (rho_L c a b) a 0
      (cloth_phi_K_nonneg c a) (rho_L_nn c a b)
      (sin_lip_flip c a)
      (sin_on_rad c a b a 0 Hwf HaR H0)). }
  rewrite Hadd, Eb, Ea. ring.
Qed.
Lemma isin_nonpos : forall c a b (Hwf : cloth_wf c),
  a <= b -> b <= 0 ->
  cloth_Isin c b - cloth_Isin c a =
  int_seg (fun u => sin (cloth_psi c u)) (rho_L c a b) a b
    (rho_L_nn c a b)
    (fun x y Hx Hy => sin_psi_ball c a b x y (rho_A c Hwf) Hx Hy).
Proof.
  intros c a b Hwf Hab Hbn.
  set (rad := Rmax (Rabs a) (Rabs b)).
  assert (H0 : Rabs 0 <= rad) by (unfold rad; rewrite Rabs_R0; apply rho_rad_nn).
  assert (HaR : Rabs a <= rad) by (unfold rad; apply Rmax_l).
  assert (HbR : Rabs b <= rad) by (unfold rad; apply Rmax_r).
  set (g := fun u : R => sin (cloth_psi c u)).
  assert (Hadd : int_seg g (rho_L c a b) a 0 (rho_L_nn c a b)
              (sin_on_rad c a b a 0 Hwf HaR H0) =
            int_seg g (rho_L c a b) a b (rho_L_nn c a b)
              (fun x y Hx Hy => sin_psi_ball c a b x y (rho_A c Hwf) Hx Hy) +
            int_seg g (rho_L c a b) b 0 (rho_L_nn c a b)
              (sin_on_rad c a b b 0 Hwf HbR H0)).
  { apply (int_seg_add g (rho_L c a b) a b 0 (rho_L_nn c a b)
      (sin_on_rad c a b a 0 Hwf HaR H0)
      (fun x y Hx Hy => sin_psi_ball c a b x y (rho_A c Hwf) Hx Hy)
      (sin_on_rad c a b b 0 Hwf HbR H0) Hab Hbn). }
  assert (Ea : int_seg g (rho_L c a b) a 0 (rho_L_nn c a b)
            (sin_on_rad c a b a 0 Hwf HaR H0) = - cloth_Isin c a).
  { unfold cloth_Isin. fold g.
    rewrite (int_seg_swap g (cloth_phi_K c a) 0 a
      (cloth_phi_K_nonneg c a) (cloth_sin_psi_lip c a) (sin_lip_flip c a)).
    rewrite Ropp_involutive.
    apply (int_seg_L g (rho_L c a b) (cloth_phi_K c a) a 0
      (rho_L_nn c a b) (cloth_phi_K_nonneg c a)
      (sin_on_rad c a b a 0 Hwf HaR H0)
      (sin_lip_flip c a)). }
  assert (Eb : int_seg g (rho_L c a b) b 0 (rho_L_nn c a b)
            (sin_on_rad c a b b 0 Hwf HbR H0) = - cloth_Isin c b).
  { unfold cloth_Isin. fold g.
    rewrite (int_seg_swap g (cloth_phi_K c b) 0 b
      (cloth_phi_K_nonneg c b) (cloth_sin_psi_lip c b) (sin_lip_flip c b)).
    rewrite Ropp_involutive.
    apply (int_seg_L g (rho_L c a b) (cloth_phi_K c b) b 0
      (rho_L_nn c a b) (cloth_phi_K_nonneg c b)
      (sin_on_rad c a b b 0 Hwf HbR H0)
      (sin_lip_flip c b)). }
  assert (Eab : int_seg g (rho_L c a b) a b (rho_L_nn c a b)
            (fun x y Hx Hy => sin_psi_ball c a b x y (rho_A c Hwf) Hx Hy)
          = int_seg g (rho_L c a b) a 0 (rho_L_nn c a b)
              (sin_on_rad c a b a 0 Hwf HaR H0) -
            int_seg g (rho_L c a b) b 0 (rho_L_nn c a b)
              (sin_on_rad c a b b 0 Hwf HbR H0)).
  { rewrite Hadd. ring. }
  rewrite Eab, Ea, Eb. ring.
Qed.
Lemma isin_ordered : forall c a b (Hwf : cloth_wf c),
  a <= b ->
  cloth_Isin c b - cloth_Isin c a =
  int_seg (fun u => sin (cloth_psi c u)) (rho_L c a b) a b
    (rho_L_nn c a b)
    (fun x y Hx Hy => sin_psi_ball c a b x y (rho_A c Hwf) Hx Hy).
Proof.
  intros c a b Hwf Hab.
  destruct (Rle_dec 0 a) as [Ha|Ha].
  - apply isin_nonneg; assumption.
  - apply Rnot_le_lt in Ha.
    destruct (Rle_dec b 0) as [Hb|Hb].
    + apply isin_nonpos; assumption.
    + apply Rnot_le_lt in Hb. apply isin_straddle; lra.
Qed.
Lemma pow2_neq0 : forall k, 2 ^ k <> 0.
Proof. intro k. apply pow_nonzero. lra. Qed.
Lemma dyadic_ramp : forall p k a b,
  a <= b ->
  dyadic (fun u => p - u) k a b =
    (b - a) * (p - a) - (b - a) * (b - a) * (1 - / (2 ^ k)) / 2.
Proof.
  intros p k. induction k as [|k IH]; intros a b Hab.
  - simpl. replace (2 ^ 0) with 1 by (simpl; reflexivity). field.
  - simpl dyadic. set (m := (a + b) / 2).
    assert (Ham : a <= m) by (unfold m; lra).
    assert (Hmb : m <= b) by (unfold m; lra).
    rewrite (IH a m Ham), (IH m b Hmb).
    unfold m. rewrite <- (tech_pow_Rmult 2 k). field. apply pow2_neq0.
Qed.
Lemma ramp_lim : forall h pa,
  Un_cv (fun k => h * pa - h * h * (1 - / (2 ^ k)) / 2)
        (h * pa - h * h / 2).
Proof.
  intros h pa.
  remember (h * h / 2) as a eqn:Ea.
  remember (h * pa - a) as c eqn:Ec.
  assert (Hc0 : c = c + 0) by (rewrite Rplus_0_r; reflexivity).
  rewrite Hc0.
  apply seq_ext with (u := fun k => c + a / (2 ^ k)).
  - intro k. rewrite Ec, Ea. field. apply pow2_neq0.
  - apply CV_plus; [apply seq_const | apply cv_pow_half].
Qed.
Lemma ramp_lip : forall p a b x y,
  Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
  Rabs ((p - x) - (p - y)) <= 1 * Rabs (x - y).
Proof.
  intros p a b x y _ _.
  replace ((p - x) - (p - y)) with (y - x) by ring.
  rewrite Rabs_minus_sym, Rmult_1_l. apply Rle_refl.
Qed.
Lemma int_ramp : forall p a b,
  a <= b ->
  int_seg (fun u => p - u) 1 a b Rle_0_1 (ramp_lip p a b) =
    (b - a) * (p - a) - (b - a) * (b - a) / 2.
Proof.
  intros p a b Hab.
  unfold int_seg.
  destruct (Rle_dec a b) as [Hab'|Hbad]; [|exfalso; apply Hbad; exact Hab].
  apply UL_sequence with (fun k => dyadic (fun u => p - u) k a b).
  - apply lint_cv_dyadic.
  - apply seq_ext with
      (u := fun k => (b - a) * (p - a) -
                     (b - a) * (b - a) * (1 - / (2 ^ k)) / 2).
    + intro k. symmetry. apply dyadic_ramp. exact Hab.
    + apply ramp_lim.
Qed.
Lemma opp_ramp_lip : forall p a b x y,
  Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
  Rabs ((- (p - x)) - (- (p - y))) <= 1 * Rabs (x - y).
Proof.
  intros p a b x y Hx Hy.
  replace ((- (p - x)) - (- (p - y))) with ((p - y) - (p - x)) by ring.
  rewrite Rmult_1_l, Rabs_minus_sym.
  replace ((p - x) - (p - y)) with (y - x) by ring.
  rewrite Rabs_minus_sym. apply Rle_refl.
Qed.
Lemma fwd_lip : forall s b x y,
  Rmin s b <= x <= Rmax s b -> Rmin s b <= y <= Rmax s b ->
  Rabs ((x - s) - (y - s)) <= 1 * Rabs (x - y).
Proof.
  intros s b x y _ _.
  replace ((x - s) - (y - s)) with (x - y) by ring.
  rewrite Rmult_1_l. apply Rle_refl.
Qed.
Lemma int_forward : forall s b,
  s <= b ->
  int_seg (fun u => u - s) 1 s b Rle_0_1 (fwd_lip s b) =
    (b - s) * (b - s) / 2.
Proof.
  intros s b Hsb.
  rewrite (int_seg_ext (fun u => u - s) (fun u => - (s - u)) 1 s b
             Rle_0_1 (fwd_lip s b) (opp_ramp_lip s s b))
    by (intros u _; ring).
  rewrite (int_seg_opp (fun u => s - u) 1 s b Rle_0_1
             (ramp_lip s s b) (opp_ramp_lip s s b)).
  rewrite int_ramp by exact Hsb. ring.
Qed.

Print Assumptions rho_h2.
Print Assumptions rho_A.
Print Assumptions cloth_frame_sumsq.
Print Assumptions heading_frame.
Print Assumptions vx_heading.
Print Assumptions vy_heading.
Print Assumptions rho_L_nn.
Print Assumptions rho_rad_nn.
Print Assumptions abs_seg.
Print Assumptions psi_lip_ball.
Print Assumptions cos_psi_ball.
Print Assumptions sin_psi_ball.
Print Assumptions sin_head_lip.
Print Assumptions cos_lip_prefix.
Print Assumptions cos_lip_tail.
Print Assumptions icos_nonneg.
Print Assumptions seg_in_rad.
Print Assumptions cos_on_rad.
Print Assumptions cos_lip_flip.
Print Assumptions icos_straddle.
Print Assumptions icos_nonpos.
Print Assumptions icos_ordered.
Print Assumptions sin_lip_prefix.
Print Assumptions sin_lip_tail.
Print Assumptions isin_nonneg.
Print Assumptions sin_on_rad.
Print Assumptions sin_lip_flip.
Print Assumptions isin_straddle.
Print Assumptions isin_nonpos.
Print Assumptions isin_ordered.
Print Assumptions pow2_neq0.
Print Assumptions dyadic_ramp.
Print Assumptions ramp_lim.
Print Assumptions ramp_lip.
Print Assumptions int_ramp.
Print Assumptions opp_ramp_lip.
Print Assumptions fwd_lip.
Print Assumptions int_forward.
