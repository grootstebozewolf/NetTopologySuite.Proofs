(* ============================================================================
   NetTopologySuite.Proofs.ClothoidChordRho
   ----------------------------------------------------------------------------
   Signed distance from a host clothoid to a directed chord line.
   d(s) = d(s0) + ∫ sin(α + ψ(u) − φ) du, built from int_seg linearity
   of the Fresnel increments. No lip_ftc. On each open interval that
   contains no root of sin(α + ψ − φ) = 0, the integrand keeps its
   sign (IVT) and the integral is strictly signed (lint_mono / int_seg
   add / a positive middle piece), so d has at most one zero there.
   Those roots are the explicit stations s² = 2 σ A² (φ + kπ − α).

   The pair stays host Decline. This letter does not touch counted
   or bag_run_arm.

   claimId: 0007-clothoid-chord-rho
   witness: clothoid_chord_rho
   3-axiom host. No Admitted / Axiom / Parameter. No FTC.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia ZArith.
From Stdlib Require Import Ranalysis1.
From NTS.Proofs Require Import Distance LipInt SheetHenClothoidCore Atan2
  SheetHenClothoidBounds SheetHenCookCore.
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
Definition off_A (c : ClothoidEgg) (phi : R) : R :=
  (- sin phi) * cloth_cos0 c + (cos phi) * cloth_sin0 c.
Definition off_B (c : ClothoidEgg) (phi : R) : R :=
  (sin phi) * cloth_sin0 c + (cos phi) * cloth_cos0 c.
Lemma off_ab_sumsq : forall c phi,
  cloth_h2 c <> 0 ->
  off_A c phi * off_A c phi + off_B c phi * off_B c phi = 1.
Proof.
  intros c phi Hh.
  unfold off_A, off_B.
  assert (Hs := cloth_frame_sumsq c Hh).
  pose proof (sin2_cos2 phi) as Ht. unfold Rsqr in Ht.
  nra.
Qed.
Lemma off_A_abs : forall c phi,
  cloth_h2 c <> 0 -> Rabs (off_A c phi) <= 1.
Proof.
  intros c phi Hh.
  assert (Hsum := off_ab_sumsq c phi Hh).
  assert (Hsq : Rsqr (off_A c phi) <= Rsqr 1).
  { unfold Rsqr. assert (0 <= off_B c phi * off_B c phi) by apply Rle_0_sqr. lra. }
  apply Rsqr_le_abs_0 in Hsq. rewrite Rabs_R1 in Hsq. exact Hsq.
Qed.
Lemma off_B_abs : forall c phi,
  cloth_h2 c <> 0 -> Rabs (off_B c phi) <= 1.
Proof.
  intros c phi Hh.
  assert (Hsum := off_ab_sumsq c phi Hh).
  assert (Hsq : Rsqr (off_B c phi) <= Rsqr 1).
  { unfold Rsqr. assert (0 <= off_A c phi * off_A c phi) by apply Rle_0_sqr. lra. }
  apply Rsqr_le_abs_0 in Hsq. rewrite Rabs_R1 in Hsq. exact Hsq.
Qed.
Lemma off_angle : forall c phi u,
  cloth_h2 c <> 0 ->
  off_A c phi * cos (cloth_psi c u) + off_B c phi * sin (cloth_psi c u)
    = sin (cloth_heading c u - phi).
Proof.
  intros c phi u Hh.
  destruct (heading_frame c Hh) as [Hc Hsn].
  unfold off_A, off_B, cloth_heading.
  rewrite sin_minus, sin_plus, cos_plus, Hc, Hsn. ring.
Qed.
Lemma scal_cos_lip : forall c phi a b (Hwf : cloth_wf c),
  forall x y,
    Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
    Rabs (off_A c phi * cos (cloth_psi c x) - off_A c phi * cos (cloth_psi c y))
      <= rho_L c a b * Rabs (x - y).
Proof.
  intros c phi a b Hwf x y Hx Hy.
  replace (off_A c phi * cos (cloth_psi c x) - off_A c phi * cos (cloth_psi c y))
    with (off_A c phi * (cos (cloth_psi c x) - cos (cloth_psi c y))) by ring.
  rewrite Rabs_mult.
  apply Rle_trans with (1 * (rho_L c a b * Rabs (x - y))).
  - apply Rmult_le_compat; try apply Rabs_pos.
    + apply off_A_abs. apply rho_h2. exact Hwf.
    + apply cos_psi_ball; [apply rho_A; exact Hwf | exact Hx | exact Hy].
  - rewrite Rmult_1_l. lra.
Qed.
Lemma scal_sin_lip : forall c phi a b (Hwf : cloth_wf c),
  forall x y,
    Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
    Rabs (off_B c phi * sin (cloth_psi c x) - off_B c phi * sin (cloth_psi c y))
      <= rho_L c a b * Rabs (x - y).
Proof.
  intros c phi a b Hwf x y Hx Hy.
  replace (off_B c phi * sin (cloth_psi c x) - off_B c phi * sin (cloth_psi c y))
    with (off_B c phi * (sin (cloth_psi c x) - sin (cloth_psi c y))) by ring.
  rewrite Rabs_mult.
  apply Rle_trans with (1 * (rho_L c a b * Rabs (x - y))).
  - apply Rmult_le_compat; try apply Rabs_pos.
    + apply off_B_abs. apply rho_h2. exact Hwf.
    + apply sin_psi_ball; [apply rho_A; exact Hwf | exact Hx | exact Hy].
  - rewrite Rmult_1_l. lra.
Qed.
Lemma sum_head_lip : forall c phi a b (Hwf : cloth_wf c),
  forall x y,
    Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
    Rabs ((off_A c phi * cos (cloth_psi c x) + off_B c phi * sin (cloth_psi c x)) -
          (off_A c phi * cos (cloth_psi c y) + off_B c phi * sin (cloth_psi c y)))
      <= rho_L c a b * Rabs (x - y).
Proof.
  intros c phi a b Hwf x y Hx Hy.
  replace (off_A c phi * cos (cloth_psi c x) + off_B c phi * sin (cloth_psi c x))
    with (sin (cloth_heading c x - phi))
    by (symmetry; apply off_angle; apply rho_h2; exact Hwf).
  replace (off_A c phi * cos (cloth_psi c y) + off_B c phi * sin (cloth_psi c y))
    with (sin (cloth_heading c y - phi))
    by (symmetry; apply off_angle; apply rho_h2; exact Hwf).
  apply sin_head_lip; assumption.
Qed.
Lemma offset_alg : forall c phi Q a b,
  line_offset Q phi (cloth_P c b) - line_offset Q phi (cloth_P c a) =
  off_A c phi * (cloth_Icos c b - cloth_Icos c a) +
  off_B c phi * (cloth_Isin c b - cloth_Isin c a).
Proof.
  intros c phi Q a b.
  unfold line_offset, cloth_P, cloth_Px, cloth_Py, off_A, off_B. simpl. ring.
Qed.
Lemma offset_delta_ordered : forall c phi Q a b (Hwf : cloth_wf c),
  a <= b ->
  line_offset Q phi (cloth_P c b) - line_offset Q phi (cloth_P c a) =
  int_seg (fun u => sin (cloth_heading c u - phi)) (rho_L c a b) a b
    (rho_L_nn c a b)
    (fun x y Hx Hy => sin_head_lip c phi a b x y Hwf Hx Hy).
Proof.
  intros c phi Q a b Hwf Hab.
  rewrite (offset_alg c phi Q a b).
  rewrite (icos_ordered c a b Hwf Hab).
  rewrite (isin_ordered c a b Hwf Hab).
  set (gc := fun u : R => cos (cloth_psi c u)) in *.
  set (gs := fun u : R => sin (cloth_psi c u)) in *.
  set (Ac := off_A c phi) in *.
  set (Bc := off_B c phi) in *.
  assert (EscA :=
    int_seg_scal gc Ac (rho_L c a b) (rho_L c a b) a b
      (rho_L_nn c a b) (rho_L_nn c a b)
      (fun x y Hx Hy => cos_psi_ball c a b x y (rho_A c Hwf) Hx Hy)
      (scal_cos_lip c phi a b Hwf)).
  assert (EscB :=
    int_seg_scal gs Bc (rho_L c a b) (rho_L c a b) a b
      (rho_L_nn c a b) (rho_L_nn c a b)
      (fun x y Hx Hy => sin_psi_ball c a b x y (rho_A c Hwf) Hx Hy)
      (scal_sin_lip c phi a b Hwf)).
  assert (Eplus :=
    int_seg_plus (fun x => Ac * gc x) (fun x => Bc * gs x)
      (rho_L c a b) (rho_L c a b) (rho_L c a b) a b
      (rho_L_nn c a b) (scal_cos_lip c phi a b Hwf)
      (rho_L_nn c a b) (scal_sin_lip c phi a b Hwf)
      (rho_L_nn c a b) (sum_head_lip c phi a b Hwf)).
  assert (Eext :
    int_seg (fun u => sin (cloth_heading c u - phi)) (rho_L c a b) a b
      (rho_L_nn c a b)
      (fun x y Hx Hy => sin_head_lip c phi a b x y Hwf Hx Hy) =
    int_seg (fun x => Ac * gc x + Bc * gs x) (rho_L c a b) a b
      (rho_L_nn c a b) (sum_head_lip c phi a b Hwf)).
  { apply int_seg_ext. intros u Hu.
    unfold gc, gs, Ac, Bc. symmetry. apply off_angle. apply rho_h2. exact Hwf. }
  rewrite <- EscA, <- EscB, <- Eplus, <- Eext. reflexivity.
Qed.
Lemma offset_integral : forall c phi Q s0 s (Hwf : cloth_wf c),
  line_offset Q phi (cloth_P c s) =
  line_offset Q phi (cloth_P c s0) +
  int_seg (fun u => sin (cloth_heading c u - phi)) (rho_L c s0 s) s0 s
    (rho_L_nn c s0 s)
    (fun x y Hx Hy => sin_head_lip c phi s0 s x y Hwf Hx Hy).
Proof.
  intros c phi Q s0 s Hwf.
  destruct (Rle_dec s0 s) as [Hle|Hlt].
  - assert (E := offset_delta_ordered c phi Q s0 s Hwf Hle). lra.
  - apply Rnot_le_lt in Hlt.
    assert (Hle : s <= s0) by lra.
    assert (E := offset_delta_ordered c phi Q s s0 Hwf Hle).
    assert (EL : rho_L c s0 s = rho_L c s s0).
    { unfold rho_L. rewrite Rmax_comm. reflexivity. }
    assert (Hrev : forall x y,
        Rmin s0 s <= x <= Rmax s0 s -> Rmin s0 s <= y <= Rmax s0 s ->
        Rabs (sin (cloth_heading c x - phi) - sin (cloth_heading c y - phi))
          <= rho_L c s s0 * Rabs (x - y)).
    { intros x y Hx Hy. rewrite <- EL.
      apply (sin_head_lip c phi s0 s x y Hwf Hx Hy). }
    assert (Esw :
      int_seg (fun u => sin (cloth_heading c u - phi)) (rho_L c s s0) s s0
        (rho_L_nn c s s0)
        (fun x y Hx Hy => sin_head_lip c phi s s0 x y Hwf Hx Hy) =
      - int_seg (fun u => sin (cloth_heading c u - phi)) (rho_L c s s0) s0 s
          (rho_L_nn c s s0) Hrev).
    { apply int_seg_swap. }
    assert (Efwd :
      int_seg (fun u => sin (cloth_heading c u - phi)) (rho_L c s0 s) s0 s
        (rho_L_nn c s0 s)
        (fun x y Hx Hy => sin_head_lip c phi s0 s x y Hwf Hx Hy) =
      int_seg (fun u => sin (cloth_heading c u - phi)) (rho_L c s s0) s0 s
        (rho_L_nn c s s0) Hrev).
    { apply int_seg_L. }
    lra.
Qed.
Lemma chord_dir_nz : forall ch, chord_nondeg ch ->
  chord_dx ch <> 0 \/ chord_dy ch <> 0.
Proof.
  intros ch H.
  destruct (Req_dec_T (chord_dx ch) 0) as [Hx|Hx];
  destruct (Req_dec_T (chord_dy ch) 0) as [Hy|Hy].
  - exfalso. apply H. rewrite Hx, Hy. reflexivity.
  - right. exact Hy.
  - left. exact Hx.
  - left. exact Hx.
Qed.
Lemma sigma_sq : forall c, cloth_sigma c * cloth_sigma c = 1.
Proof.
  intro c. unfold cloth_sigma. destruct (Rle_dec 0 (cloth_cross c)); ring.
Qed.
Lemma psi_square : forall c s th,
  cloth_wf c -> cloth_psi c s = th ->
  s * s = 2 * cloth_sigma c * (cloth_A c * cloth_A c) * th.
Proof.
  intros c s th Hwf Heq.
  set (sig := cloth_sigma c). set (A := cloth_A c).
  assert (Hsig : sig * sig = 1) by (unfold sig; apply sigma_sq).
  assert (HA0 : 0 < A) by (unfold A; apply rho_A; exact Hwf).
  assert (Hd : 2 * A * A <> 0) by nra.
  unfold cloth_psi, Rdiv in Heq. fold sig in Heq. fold A in Heq.
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
Lemma heading_station : forall c phi s,
  cloth_wf c -> sin (cloth_heading c s - phi) = 0 ->
  exists k : Z,
    cloth_heading c s = phi + IZR k * PI /\
    s * s = 2 * cloth_sigma c * (cloth_A c * cloth_A c) *
              (phi + IZR k * PI - cloth_heading0 c).
Proof.
  intros c phi s Hwf Hz.
  destruct (sin_eq_0_0 _ Hz) as [k Hk]. exists k. split.
  - rewrite <- Hk. ring.
  - apply (psi_square c s (phi + IZR k * PI - cloth_heading0 c) Hwf).
    unfold cloth_heading in Hk. lra.
Qed.
Lemma cont_ext : forall f g, (forall x, f x = g x) ->
  continuity g -> continuity f.
Proof.
  intros f g Heq Hg x.
  unfold continuity_pt, continue_in, limit1_in, limit_in, R_dist in *.
  intros eps Heps.
  destruct (Hg x eps Heps) as [alp [Halp Hlim]].
  exists alp. split; [exact Halp|].
  intros y Hy. rewrite !Heq. apply Hlim. exact Hy.
Qed.
Lemma continuity_psi : forall c, continuity (cloth_psi c).
Proof.
  intro c.
  apply cont_ext with (g := fun s =>
    (cloth_sigma c * / (2 * cloth_A c * cloth_A c)) * (s * s)).
  - intro s. unfold cloth_psi, Rdiv. ring.
  - apply continuity_mult.
    + apply continuity_const. unfold constant. intros. reflexivity.
    + apply continuity_mult; apply derivable_continuous, derivable_id.
Qed.
Lemma continuity_sin_head : forall c phi,
  continuity (fun s => sin (cloth_heading c s - phi)).
Proof.
  intros c phi.
  apply cont_ext with
    (fun s => sin ((cloth_heading0 c - phi) + cloth_psi c s)).
  - intro s. f_equal. unfold cloth_heading. ring.
  - change (continuity (comp sin
      (fun s => (cloth_heading0 c - phi) + cloth_psi c s))).
    apply continuity_comp.
    + apply continuity_plus.
      * apply continuity_const. unfold constant. intros. reflexivity.
      * apply continuity_psi.
    + apply continuity_sin.
Qed.
Lemma ivt_cross : forall f x y,
  continuity f -> x < y -> f x < 0 -> 0 < f y ->
  exists z, x < z < y /\ f z = 0.
Proof.
  intros f x y Hc Hxy Hx Hy.
  destruct (IVT f x y Hc Hxy Hx Hy) as [z [Hz Ez]].
  exists z. split; [| exact Ez].
  destruct Hz as [Hxz Hzy]. split.
  - destruct Hxz as [Hlt|Heq]; [exact Hlt| subst z; exfalso; lra].
  - destruct Hzy as [Hlt|Heq]; [exact Hlt| subst z; exfalso; lra].
Qed.
Lemma sign_holds : forall f a b,
  a < b -> continuity f ->
  (forall t, a < t < b -> f t <> 0) ->
  forall t, a <= t <= b -> 0 < f ((a + b) / 2) -> 0 <= f t.
Proof.
  intros f a b Hab Hc Hnz t Ht Hm.
  destruct (Rle_lt_dec 0 (f t)) as [Hnn|Hneg]; [exact Hnn|].
  set (m := (a + b) / 2) in *.
  assert (Hmab : a < m < b) by (unfold m; lra).
  destruct (Rtotal_order t m) as [Hlt|[Heq|Hgt]].
  - destruct (ivt_cross f t m Hc Hlt Hneg Hm) as [z [Hz Ez]].
    exfalso. apply (Hnz z); [| exact Ez]. split; lra.
  - subst t. lra.
  - assert (Hc' : continuity (fun z => - f z)) by (apply continuity_opp; exact Hc).
    destruct (ivt_cross (fun z => - f z) m t Hc' Hgt) as [z [Hz Ez]].
    + lra.
    + lra.
    + exfalso. apply (Hnz z); [| lra]. split; lra.
Qed.
Lemma sin_head_between : forall c phi a b (Hwf : cloth_wf c) p q,
  Rmin a b <= p <= Rmax a b -> Rmin a b <= q <= Rmax a b ->
  forall x y,
    Rmin p q <= x <= Rmax p q -> Rmin p q <= y <= Rmax p q ->
    Rabs (sin (cloth_heading c x - phi) - sin (cloth_heading c y - phi))
      <= rho_L c a b * Rabs (x - y).
Proof.
  intros c phi a b Hwf p q Hp Hq x y Hx Hy.
  apply (sin_head_lip c phi a b x y Hwf).
  - split.
    + apply Rle_trans with (Rmin p q); [| exact (proj1 Hx)].
      apply Rmin_glb; [exact (proj1 Hp) | exact (proj1 Hq)].
    + apply Rle_trans with (Rmax p q); [exact (proj2 Hx)|].
      apply Rmax_lub; [exact (proj2 Hp) | exact (proj2 Hq)].
  - split.
    + apply Rle_trans with (Rmin p q); [| exact (proj1 Hy)].
      apply Rmin_glb; [exact (proj1 Hp) | exact (proj1 Hq)].
    + apply Rle_trans with (Rmax p q); [exact (proj2 Hy)|].
      apply Rmax_lub; [exact (proj2 Hp) | exact (proj2 Hq)].
Qed.
Lemma lip_gap_half : forall rho gap fm,
  0 <= rho -> gap <= Rabs fm / (2 * (rho + 1)) ->
  rho * gap <= Rabs fm / 2.
Proof.
  intros rho gap fm Hrho Hg.
  apply Rle_trans with (rho * (Rabs fm / (2 * (rho + 1)))).
  - apply Rmult_le_compat_l; assumption.
  - unfold Rdiv.
    assert (E : rho * (Rabs fm * / (2 * (rho + 1))) =
                (rho * / (rho + 1)) * (Rabs fm * / 2)) by (field; lra).
    rewrite E. apply Rle_trans with (1 * (Rabs fm * / 2)).
    + apply Rmult_le_compat_r.
      * apply Rmult_le_pos; [apply Rabs_pos|].
        apply Rlt_le, Rinv_0_lt_compat. lra.
      * apply Rmult_le_reg_r with (rho + 1); [lra|].
        rewrite Rmult_assoc, Rinv_l by lra. rewrite Rmult_1_r, Rmult_1_l. lra.
    + rewrite Rmult_1_l. apply Rle_refl.
Qed.
Lemma integrand_nonzero : forall c phi a b (Hwf : cloth_wf c),
  a < b ->
  (forall t, a < t < b -> sin (cloth_heading c t - phi) <> 0) ->
  forall s1 s2, a <= s1 -> s1 < s2 -> s2 <= b ->
  int_seg (fun u => sin (cloth_heading c u - phi)) (rho_L c s1 s2) s1 s2
    (rho_L_nn c s1 s2)
    (fun x y Hx Hy => sin_head_lip c phi s1 s2 x y Hwf Hx Hy) <> 0.
Proof.
  intros c phi a b Hwf Hab Hnz s1 s2 Hs1 H12 Hs2.
  set (f := fun u => sin (cloth_heading c u - phi)).
  set (rho := rho_L c s1 s2).
  set (mid := (a + b) / 2).
  assert (Hc : continuity f) by (unfold f; apply continuity_sin_head).
  assert (Hmidb : a < mid < b) by (unfold mid; lra).
  assert (Hmidz : f mid <> 0) by (unfold f; apply Hnz; exact Hmidb).
  set (m := (s1 + s2) / 2).
  assert (Hmm : a < m < b) by (unfold m; lra).
  assert (Hmz : f m <> 0) by (unfold f; apply Hnz; exact Hmm).
  set (gap := Rmin ((s2 - s1) / 4) (Rabs (f m) / (2 * (rho + 1)))).
  assert (Hgap : 0 < gap).
  { assert (0 < (s2 - s1) / 4) by lra.
    assert (0 < Rabs (f m)) by (apply Rabs_pos_lt; exact Hmz).
    assert (0 <= rho) by (unfold rho; apply rho_L_nn).
    assert (0 < Rabs (f m) / (2 * (rho + 1))) by (apply Rdiv_lt_0_compat; lra).
    unfold gap.
    destruct (Rle_dec ((s2 - s1) / 4) (Rabs (f m) / (2 * (rho + 1)))) as [Hd|Hd].
    - rewrite (Rmin_left _ _ Hd). lra.
    - apply Rnot_le_lt in Hd. rewrite (Rmin_right _ _ (Rlt_le _ _ Hd)). lra. }
  set (lo := m - gap). set (hi := m + gap).
  assert (Hgs : gap <= (s2 - s1) / 4) by (unfold gap; apply Rmin_l).
  assert (Hslo : s1 <= lo) by (unfold lo, m; lra).
  assert (Hhis : hi <= s2) by (unfold hi, m; lra).
  assert (Hlh : lo <= hi) by (unfold lo, hi; lra).
  assert (Hball : forall x, lo <= x <= hi -> Rabs (f x - f m) <= Rabs (f m) / 2).
  { intros x Hx.
    assert (Rabs (x - m) <= gap) by (apply Rabs_le; unfold lo, hi in Hx; lra).
    assert (Hxw : Rmin s1 s2 <= x <= Rmax s1 s2).
    { rewrite (Rmin_left s1 s2) by lra. rewrite (Rmax_right s1 s2) by lra.
      split.
      - apply Rle_trans with lo; [exact Hslo | exact (proj1 Hx)].
      - apply Rle_trans with hi; [exact (proj2 Hx) | exact Hhis]. }
    assert (Hmw : Rmin s1 s2 <= m <= Rmax s1 s2).
    { rewrite (Rmin_left s1 s2) by lra. rewrite (Rmax_right s1 s2) by lra.
      split.
      - apply Rle_trans with lo; [exact Hslo | unfold lo; lra].
      - apply Rle_trans with hi; [unfold hi; lra | exact Hhis]. }
    apply Rle_trans with (rho * Rabs (x - m)).
    - unfold f, rho. apply sin_head_lip; assumption.
    - apply Rle_trans with (rho * gap).
      + apply Rmult_le_compat_l; [unfold rho; apply rho_L_nn | assumption].
      + apply lip_gap_half; [unfold rho; apply rho_L_nn | unfold gap; apply Rmin_r]. }
  assert (Hin1 : Rmin s1 s2 <= s1 <= Rmax s1 s2).
  { rewrite (Rmin_left s1 s2) by lra. rewrite (Rmax_right s1 s2) by lra. lra. }
  assert (Hinlo : Rmin s1 s2 <= lo <= Rmax s1 s2).
  { rewrite (Rmin_left s1 s2) by lra. rewrite (Rmax_right s1 s2) by lra. lra. }
  assert (Hinhi : Rmin s1 s2 <= hi <= Rmax s1 s2).
  { rewrite (Rmin_left s1 s2) by lra. rewrite (Rmax_right s1 s2) by lra. lra. }
  assert (Hin2 : Rmin s1 s2 <= s2 <= Rmax s1 s2).
  { rewrite (Rmin_left s1 s2) by lra. rewrite (Rmax_right s1 s2) by lra. lra. }
  assert (Hlos2 : lo <= s2) by lra.
  assert (E1 := int_seg_add f rho s1 lo s2 (rho_L_nn c s1 s2)
    (fun x y Hx Hy => sin_head_lip c phi s1 s2 x y Hwf Hx Hy)
    (sin_head_between c phi s1 s2 Hwf s1 lo Hin1 Hinlo)
    (sin_head_between c phi s1 s2 Hwf lo s2 Hinlo Hin2)
    Hslo Hlos2).
  assert (E2 := int_seg_add f rho lo hi s2 (rho_L_nn c s1 s2)
    (sin_head_between c phi s1 s2 Hwf lo s2 Hinlo Hin2)
    (sin_head_between c phi s1 s2 Hwf lo hi Hinlo Hinhi)
    (sin_head_between c phi s1 s2 Hwf hi s2 Hinhi Hin2)
    Hlh Hhis).
  assert (Esum : int_seg f rho s1 s2 (rho_L_nn c s1 s2)
            (fun x y Hx Hy => sin_head_lip c phi s1 s2 x y Hwf Hx Hy)
          = int_seg f rho s1 lo (rho_L_nn c s1 s2)
              (sin_head_between c phi s1 s2 Hwf s1 lo Hin1 Hinlo)
          + int_seg f rho lo hi (rho_L_nn c s1 s2)
              (sin_head_between c phi s1 s2 Hwf lo hi Hinlo Hinhi)
          + int_seg f rho hi s2 (rho_L_nn c s1 s2)
              (sin_head_between c phi s1 s2 Hwf hi s2 Hinhi Hin2)).
  { rewrite E1, E2. ring. }
  rewrite Esum.
  destruct (Rle_lt_dec 0 (f mid)) as [Hnn0|Hneg0].
  - assert (Hgt : 0 < f mid) by lra.
    assert (Hnn : forall t, a <= t <= b -> 0 <= f t).
    { intros t Ht. apply (sign_holds f a b Hab Hc Hnz t Ht Hgt). }
    assert (Hfm : 0 < f m).
    { assert (0 <= f m) by (apply Hnn; unfold m; lra). lra. }
    assert (Hlow : forall x, lo <= x <= hi -> f m / 2 <= f x).
    { intros x Hx. assert (Hbnd := Hball x Hx).
      assert (Rabs (f m) = f m) by (apply Rabs_right; lra).
      pose proof (Rle_abs (f m - f x)) as Habs.
      rewrite (Rabs_minus_sym (f m) (f x)) in Habs. lra. }
    assert (HA : 0 <= int_seg f rho s1 lo (rho_L_nn c s1 s2)
              (sin_head_between c phi s1 s2 Hwf s1 lo Hin1 Hinlo)).
    { assert (Hge := int_seg_ge_const f rho s1 lo (rho_L_nn c s1 s2)
        (sin_head_between c phi s1 s2 Hwf s1 lo Hin1 Hinlo) 0 Hslo).
      assert (0 * (lo - s1) <= int_seg f rho s1 lo (rho_L_nn c s1 s2)
        (sin_head_between c phi s1 s2 Hwf s1 lo Hin1 Hinlo)).
      { apply Hge. intros x Hx. apply Hnn. lra. }
      replace 0 with (0 * (lo - s1)) by ring. exact H. }
    assert (HC : 0 <= int_seg f rho hi s2 (rho_L_nn c s1 s2)
              (sin_head_between c phi s1 s2 Hwf hi s2 Hinhi Hin2)).
    { assert (0 * (s2 - hi) <= int_seg f rho hi s2 (rho_L_nn c s1 s2)
        (sin_head_between c phi s1 s2 Hwf hi s2 Hinhi Hin2)).
      { apply int_seg_ge_const; [lra|]. intros x Hx. apply Hnn. lra. }
      replace 0 with (0 * (s2 - hi)) by ring. exact H. }
    assert (HB : f m / 2 * (hi - lo) <= int_seg f rho lo hi (rho_L_nn c s1 s2)
              (sin_head_between c phi s1 s2 Hwf lo hi Hinlo Hinhi)).
    { apply int_seg_ge_const; [exact Hlh|]. intros x Hx. apply Hlow. exact Hx. }
    assert (0 < f m / 2 * (hi - lo)).
    { apply Rmult_lt_0_compat; unfold lo, hi; lra. }
    lra.
  - assert (Hop : continuity (fun z => - f z)) by (apply continuity_opp; exact Hc).
    assert (Hpos : 0 < - f mid) by lra.
    assert (Hnz' : forall t, a < t < b -> (fun z => - f z) t <> 0).
    { intros t Ht Heq. unfold f in Heq. apply (Hnz t Ht). lra. }
    assert (Hnp : forall t, a <= t <= b -> f t <= 0).
    { intros t Ht.
      assert (0 <= - f t).
      { apply (sign_holds (fun z => - f z) a b Hab Hop Hnz' t Ht Hpos). }
      lra. }
    assert (Hfm : f m < 0).
    { assert (f m <= 0) by (apply Hnp; unfold m; lra). lra. }
    assert (Hup : forall x, lo <= x <= hi -> f x <= f m / 2).
    { intros x Hx. assert (Hbnd := Hball x Hx).
      assert (Rabs (f m) = - f m) by (apply Rabs_left; exact Hfm).
      pose proof (Rle_abs (f x - f m)) as Habs. lra. }
    assert (HA : int_seg f rho s1 lo (rho_L_nn c s1 s2)
              (sin_head_between c phi s1 s2 Hwf s1 lo Hin1 Hinlo) <= 0).
    { assert (int_seg f rho s1 lo (rho_L_nn c s1 s2)
        (sin_head_between c phi s1 s2 Hwf s1 lo Hin1 Hinlo) <= 0 * (lo - s1)).
      { apply int_seg_le_const; [exact Hslo|]. intros x Hx. apply Hnp. lra. }
      replace (0 * (lo - s1)) with 0 in H by ring. exact H. }
    assert (HC : int_seg f rho hi s2 (rho_L_nn c s1 s2)
              (sin_head_between c phi s1 s2 Hwf hi s2 Hinhi Hin2) <= 0).
    { assert (int_seg f rho hi s2 (rho_L_nn c s1 s2)
        (sin_head_between c phi s1 s2 Hwf hi s2 Hinhi Hin2) <= 0 * (s2 - hi)).
      { apply int_seg_le_const; [lra|]. intros x Hx. apply Hnp. lra. }
      replace (0 * (s2 - hi)) with 0 in H by ring. exact H. }
    assert (HB : int_seg f rho lo hi (rho_L_nn c s1 s2)
              (sin_head_between c phi s1 s2 Hwf lo hi Hinlo Hinhi)
            <= f m / 2 * (hi - lo)).
    { apply int_seg_le_const; [exact Hlh|]. intros x Hx. apply Hup. exact Hx. }
    assert (f m / 2 * (hi - lo) < 0).
    { assert (f m / 2 < 0) by lra. assert (0 < hi - lo) by (unfold lo, hi; lra).
      nra. }
    lra.
Qed.
Lemma offset_at_most_one : forall c phi Q a b (Hwf : cloth_wf c),
  a < b ->
  (forall t, a < t < b -> sin (cloth_heading c t - phi) <> 0) ->
  forall s1 s2, a <= s1 -> s1 < s2 -> s2 <= b ->
    line_offset Q phi (cloth_P c s1) = 0 ->
    line_offset Q phi (cloth_P c s2) = 0 -> False.
Proof.
  intros c phi Q a b Hwf Hab Hnz s1 s2 Ha Hlt Hb Hz1 Hz2.
  assert (E := offset_integral c phi Q s1 s2 Hwf).
  rewrite Hz1, Hz2 in E.
  assert (int_seg (fun u => sin (cloth_heading c u - phi)) (rho_L c s1 s2) s1 s2
            (rho_L_nn c s1 s2)
            (fun x y Hx Hy => sin_head_lip c phi s1 s2 x y Hwf Hx Hy) = 0) by lra.
  apply (integrand_nonzero c phi a b Hwf Hab Hnz s1 s2 Ha Hlt Hb). exact H.
Qed.
(* WITNESS {"claimId":"0007-clothoid-chord-rho","topic":"curves","lemma":"clothoid_chord_rho","title":"Clothoid versus chord signed distance is an integral of sin(heading-phi); explicit stations where the heading meets the chord mod pi; at most one zero on each sign-constant interval","file":"theories/ClothoidChordRho.v","witness":"clothoid_chord_rho"} *)
Theorem clothoid_chord_rho :
  forall (c : ClothoidEgg) (ch : ChordEgg) (Hwf : cloth_wf c),
    chord_nondeg ch ->
    let phi := atan2 (chord_dy ch) (chord_dx ch) in
    let Q := ce_p0 ch in
    (forall s0 s,
       line_offset Q phi (cloth_P c s) =
       line_offset Q phi (cloth_P c s0) +
       int_seg (fun u => sin (cloth_heading c u - phi))
         (rho_L c s0 s) s0 s (rho_L_nn c s0 s)
         (fun x y Hx Hy => sin_head_lip c phi s0 s x y Hwf Hx Hy)) /\
    (forall s, sin (cloth_heading c s - phi) = 0 ->
       exists k : Z,
         cloth_heading c s = phi + IZR k * PI /\
         s * s = 2 * cloth_sigma c * (cloth_A c * cloth_A c) *
                   (phi + IZR k * PI - cloth_heading0 c)) /\
    (forall a b, a < b ->
       (forall t, a < t < b -> sin (cloth_heading c t - phi) <> 0) ->
       forall s1 s2, a <= s1 -> s1 < s2 -> s2 <= b ->
         line_offset Q phi (cloth_P c s1) = 0 ->
         line_offset Q phi (cloth_P c s2) = 0 -> False).
Proof.
  intros c ch Hwf Hnd. cbn zeta.
  assert (Hdir := chord_dir_nz ch Hnd).
  split; [| split].
  - intros s0 s. apply offset_integral.
  - intros s Hz. apply heading_station; assumption.
  - intros a b Hab Hopen s1 s2 Ha Hlt Hb Hz1 Hz2.
    apply (offset_at_most_one c (atan2 (chord_dy ch) (chord_dx ch)) (ce_p0 ch)
      a b Hwf Hab Hopen s1 s2 Ha Hlt Hb Hz1 Hz2).
Qed.
Lemma clothoid_chord_I_decline : forall c ch,
  I_ok (MkClothoid c) (MkChord ch) IDecline.
Proof.
  intros c ch. simpl. intro H. exact H.
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
Print Assumptions off_ab_sumsq.
Print Assumptions off_A_abs.
Print Assumptions off_B_abs.
Print Assumptions off_angle.
Print Assumptions scal_cos_lip.
Print Assumptions scal_sin_lip.
Print Assumptions sum_head_lip.
Print Assumptions offset_alg.
Print Assumptions offset_delta_ordered.
Print Assumptions offset_integral.
Print Assumptions chord_dir_nz.
Print Assumptions sigma_sq.
Print Assumptions psi_square.
Print Assumptions heading_station.
Print Assumptions cont_ext.
Print Assumptions continuity_psi.
Print Assumptions continuity_sin_head.
Print Assumptions ivt_cross.
Print Assumptions sign_holds.
Print Assumptions sin_head_between.
Print Assumptions lip_gap_half.
Print Assumptions integrand_nonzero.
Print Assumptions offset_at_most_one.
Print Assumptions clothoid_chord_rho.
Print Assumptions clothoid_chord_I_decline.
