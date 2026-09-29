(* ============================================================================
   NetTopologySuite.Proofs.ClothoidTangent
   ----------------------------------------------------------------------------
   Derivative of the host clothoid from SheetHenClothoidCore.

   P(s) = LOCATION + int_0^s R(phi0) (cos psi, sin psi),
   psi(s) = sigma * s^2 / (2 A^2),
   so each coordinate is an affine image of cloth_Icos / cloth_Isin.
   LipIntFTC gives d/ds of that primitive: the integrand. The rotated
   integrand is cloth_vx / cloth_vy, the unit tangent when the first
   reference vector is nonzero (cloth_h2 <> 0). The windowed eval
   gamma(t) = P(sd + t (ed - sd)) picks up the chain-rule factor
   (ed - sd).

   This is not Halley d/dL. ClothoidResidual.H_deriv differentiates
   the length parameter under the integral (moments P, Q, R, T), and
   H_fprime_pos is the sign of that derivative. Stdlib MVT prints
   Classical_Prop.classic, so H_mvt is not discharged here either.
   claimId: none. The tangent is an instance of
   LipIntFTC.lipint_ftc (claimId 0001-lint-ftc) on cos and sin of psi,
   plus the rigid frame and the chain rule. It does not mint a second
   claim, and it does not take 0007-clothoid-first-cook.
   No Admitted / Axiom / Parameter. No Coquelicot. No RiemannInt.
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From Stdlib Require Import Ranalysis1.
From NTS.Proofs Require Import Distance LipInt LipIntFTC SheetHenClothoidCore.
Local Open Scope R_scope.

(* psi is Lipschitz on [-R, R] with constant cloth_phi_K c R = |R| / A^2.
   The core lemma cloth_psi_lip only covers the segment from 0 to one
   station, which does not contain a two-sided neighbourhood. *)
Lemma cloth_psi_ball_lip :
  forall c R x y,
    0 <= R ->
    - R <= x <= R -> - R <= y <= R ->
    Rabs (cloth_psi c x - cloth_psi c y)
      <= cloth_phi_K c R * Rabs (x - y).
Proof.
  intros c R x y HR Hx Hy.
  set (AA := cloth_A c * cloth_A c).
  destruct (Req_EM_T AA 0) as [Hz|Hnz].
  - assert (H0 : forall t, cloth_psi c t = 0).
    { intro t. unfold cloth_psi, Rdiv.
      assert (E : 2 * cloth_A c * cloth_A c = 0).
      { unfold AA in Hz.
        replace (2 * cloth_A c * cloth_A c)
          with (2 * (cloth_A c * cloth_A c)) by ring.
        rewrite Hz. ring. }
      rewrite E, Rinv_0. ring. }
    rewrite !H0. unfold cloth_phi_K, Rdiv. unfold AA in Hz.
    rewrite Hz, Rinv_0, Rminus_diag, Rabs_R0. lra.
  - assert (Hpos : 0 < AA).
    { assert (0 <= AA) by (unfold AA; apply Rle_0_sqr). lra. }
    assert (HA : cloth_A c <> 0).
    { intro HzA. apply Hnz. unfold AA. rewrite HzA. ring. }
    assert (Hinv : 0 < / (2 * AA)).
    { apply Rinv_0_lt_compat. lra. }
    unfold cloth_psi, cloth_phi_K, Rdiv.
    assert (E :
      (cloth_sigma c * x * x) * / (2 * cloth_A c * cloth_A c) -
      (cloth_sigma c * y * y) * / (2 * cloth_A c * cloth_A c)
      = cloth_sigma c * ((x - y) * (x + y)) * / (2 * AA)).
    { unfold AA. field. exact HA. }
    rewrite E. clear E.
    rewrite !Rabs_mult.
    rewrite cloth_sigma_abs.
    assert (Habs : Rabs (/ (2 * AA)) = / (2 * AA)).
    { apply Rabs_pos_eq. apply Rlt_le. exact Hinv. }
    rewrite Habs. clear Habs.
    assert (Hxy : Rabs (x + y) <= 2 * R).
    { eapply Rle_trans; [apply Rabs_triang |].
      assert (Hxabs : Rabs x <= R) by (apply Rabs_le; exact Hx).
      assert (Hyabs : Rabs y <= R) by (apply Rabs_le; exact Hy).
      apply Rle_trans with (R + R).
      - apply Rplus_le_compat; assumption.
      - right. ring. }
    rewrite (Rabs_pos_eq R HR).
    apply Rle_trans with
      ((1 * (Rabs (x - y) * (2 * R))) * / (2 * AA)).
    + apply Rmult_le_compat_r; [apply Rlt_le; exact Hinv |].
      apply Rmult_le_compat_l; [lra |].
      apply Rmult_le_compat_l; [apply Rabs_pos | exact Hxy].
    + unfold AA. right. field. exact HA.
Qed.

Lemma cloth_cos_ball_lip :
  forall c R x y,
    0 <= R ->
    - R <= x <= R -> - R <= y <= R ->
    Rabs (cos (cloth_psi c x) - cos (cloth_psi c y))
      <= cloth_phi_K c R * Rabs (x - y).
Proof.
  intros c R x y HR Hx Hy.
  eapply Rle_trans; [apply cos_lip |].
  apply cloth_psi_ball_lip; assumption.
Qed.

Lemma cloth_sin_ball_lip :
  forall c R x y,
    0 <= R ->
    - R <= x <= R -> - R <= y <= R ->
    Rabs (sin (cloth_psi c x) - sin (cloth_psi c y))
      <= cloth_phi_K c R * Rabs (x - y).
Proof.
  intros c R x y HR Hx Hy.
  eapply Rle_trans; [apply sin_lip |].
  apply cloth_psi_ball_lip; assumption.
Qed.

Lemma cloth_Icos_as_prim :
  forall c R (HR : 0 <= R) z,
    - R <= z <= R ->
    lipPrim (fun u => cos (cloth_psi c u)) (- R) R
      (cloth_phi_K c R) (cloth_phi_K_nonneg c R)
      (fun x y Hx Hy => cloth_cos_ball_lip c R x y HR Hx Hy)
      0 z = cloth_Icos c z.
Proof.
  intros c R HR z Hz.
  assert (Ha : - R <= 0 <= R).
  { split; [| exact HR].
    assert (HR' := HR).
    apply Ropp_le_contravar in HR'.
    rewrite Ropp_0 in HR'. exact HR'. }
  rewrite (lipPrim_as_seg (fun u => cos (cloth_psi c u)) (- R) R
            (cloth_phi_K c R) (cloth_phi_K_nonneg c R)
            (fun x y Hx Hy => cloth_cos_ball_lip c R x y HR Hx Hy)
            0 z Ha Hz).
  unfold cloth_Icos.
  apply int_seg_L.
Qed.

Lemma cloth_Isin_as_prim :
  forall c R (HR : 0 <= R) z,
    - R <= z <= R ->
    lipPrim (fun u => sin (cloth_psi c u)) (- R) R
      (cloth_phi_K c R) (cloth_phi_K_nonneg c R)
      (fun x y Hx Hy => cloth_sin_ball_lip c R x y HR Hx Hy)
      0 z = cloth_Isin c z.
Proof.
  intros c R HR z Hz.
  assert (Ha : - R <= 0 <= R).
  { split; [| exact HR].
    assert (HR' := HR).
    apply Ropp_le_contravar in HR'.
    rewrite Ropp_0 in HR'. exact HR'. }
  rewrite (lipPrim_as_seg (fun u => sin (cloth_psi c u)) (- R) R
            (cloth_phi_K c R) (cloth_phi_K_nonneg c R)
            (fun x y Hx Hy => cloth_sin_ball_lip c R x y HR Hx Hy)
            0 z Ha Hz).
  unfold cloth_Isin.
  apply int_seg_L.
Qed.

Lemma cloth_Icos_deriv :
  forall c s,
    derivable_pt_lim (cloth_Icos c) s (cos (cloth_psi c s)).
Proof.
  intros c s.
  set (R0 := Rabs s + 1).
  assert (HR : 0 <= R0).
  { unfold R0. apply Rplus_le_le_0_compat; [apply Rabs_pos | apply Rlt_le, Rlt_0_1]. }
  assert (Hs : - R0 < s < R0).
  { assert (Habs : Rabs s < R0).
    { unfold R0. rewrite <- (Rplus_0_r (Rabs s)) at 1.
      apply Rplus_lt_compat_l. exact Rlt_0_1. }
    destruct (Rabs_def2 _ _ Habs) as [Hhi Hlo].
    split; [exact Hlo | exact Hhi]. }
  apply derivable_pt_lim_locally_ext with
    (f := lipPrim (fun u => cos (cloth_psi c u)) (- R0) R0
            (cloth_phi_K c R0) (cloth_phi_K_nonneg c R0)
            (fun x y Hx Hy => cloth_cos_ball_lip c R0 x y HR Hx Hy) 0)
    (a := - R0) (b := R0).
  - exact Hs.
  - intros z Hz.
    apply cloth_Icos_as_prim.
    destruct Hz as [Hz1 Hz2]. split; apply Rlt_le; assumption.
  - apply (lipPrim_ftc (fun u => cos (cloth_psi c u)) (- R0) R0
           (cloth_phi_K c R0) (cloth_phi_K_nonneg c R0)
           (fun x y Hx Hy => cloth_cos_ball_lip c R0 x y HR Hx Hy) 0 s).
    + split; [| exact HR].
      assert (HR' := HR).
      apply Ropp_le_contravar in HR'.
      rewrite Ropp_0 in HR'. exact HR'.
    + exact Hs.
Qed.

Lemma cloth_Isin_deriv :
  forall c s,
    derivable_pt_lim (cloth_Isin c) s (sin (cloth_psi c s)).
Proof.
  intros c s.
  set (R0 := Rabs s + 1).
  assert (HR : 0 <= R0).
  { unfold R0. apply Rplus_le_le_0_compat; [apply Rabs_pos | apply Rlt_le, Rlt_0_1]. }
  assert (Hs : - R0 < s < R0).
  { assert (Habs : Rabs s < R0).
    { unfold R0. rewrite <- (Rplus_0_r (Rabs s)) at 1.
      apply Rplus_lt_compat_l. exact Rlt_0_1. }
    destruct (Rabs_def2 _ _ Habs) as [Hhi Hlo].
    split; [exact Hlo | exact Hhi]. }
  apply derivable_pt_lim_locally_ext with
    (f := lipPrim (fun u => sin (cloth_psi c u)) (- R0) R0
            (cloth_phi_K c R0) (cloth_phi_K_nonneg c R0)
            (fun x y Hx Hy => cloth_sin_ball_lip c R0 x y HR Hx Hy) 0)
    (a := - R0) (b := R0).
  - exact Hs.
  - intros z Hz.
    apply cloth_Isin_as_prim.
    destruct Hz as [Hz1 Hz2]. split; apply Rlt_le; assumption.
  - apply (lipPrim_ftc (fun u => sin (cloth_psi c u)) (- R0) R0
           (cloth_phi_K c R0) (cloth_phi_K_nonneg c R0)
           (fun x y Hx Hy => cloth_sin_ball_lip c R0 x y HR Hx Hy) 0 s).
    + split; [| exact HR].
      assert (HR' := HR).
      apply Ropp_le_contravar in HR'.
      rewrite Ropp_0 in HR'. exact HR'.
    + exact Hs.
Qed.

Lemma cloth_Px_deriv :
  forall c s, derivable_pt_lim (cloth_Px c) s (cloth_vx c s).
Proof.
  intros c s.
  set (Ix := cloth_Icos c).
  set (Iy := cloth_Isin c).
  set (a := cloth_cos0 c).
  set (b := cloth_sin0 c).
  set (loc := px (aff_loc (cloth_place c))).
  assert (Ha : derivable_pt_lim (mult_real_fct a Ix) s (a * cos (cloth_psi c s))).
  { apply derivable_pt_lim_scal. unfold Ix. apply cloth_Icos_deriv. }
  assert (Hb : derivable_pt_lim (mult_real_fct b Iy) s (b * sin (cloth_psi c s))).
  { apply derivable_pt_lim_scal. unfold Iy. apply cloth_Isin_deriv. }
  assert (Hsub : derivable_pt_lim
           (minus_fct (mult_real_fct a Ix) (mult_real_fct b Iy)) s
           (a * cos (cloth_psi c s) - b * sin (cloth_psi c s))).
  { apply derivable_pt_lim_minus; assumption. }
  assert (Hplus : derivable_pt_lim
           (plus_fct (fct_cte loc)
              (minus_fct (mult_real_fct a Ix) (mult_real_fct b Iy))) s
           (0 + (a * cos (cloth_psi c s) - b * sin (cloth_psi c s)))).
  { apply derivable_pt_lim_plus; [apply derivable_pt_lim_const | exact Hsub]. }
  replace (cloth_vx c s)
    with (0 + (a * cos (cloth_psi c s) - b * sin (cloth_psi c s))).
  - apply derivable_pt_lim_ext with
      (f := plus_fct (fct_cte loc)
              (minus_fct (mult_real_fct a Ix) (mult_real_fct b Iy))).
    + intro z. unfold cloth_Px, plus_fct, minus_fct, mult_real_fct, fct_cte.
      unfold Ix, Iy, a, b, loc. ring.
    + exact Hplus.
  - unfold cloth_vx, a, b. ring.
Qed.

Lemma cloth_Py_deriv :
  forall c s, derivable_pt_lim (cloth_Py c) s (cloth_vy c s).
Proof.
  intros c s.
  set (Ix := cloth_Icos c).
  set (Iy := cloth_Isin c).
  set (a := cloth_cos0 c).
  set (b := cloth_sin0 c).
  set (loc := py (aff_loc (cloth_place c))).
  assert (Ha : derivable_pt_lim (mult_real_fct b Ix) s (b * cos (cloth_psi c s))).
  { apply derivable_pt_lim_scal. unfold Ix. apply cloth_Icos_deriv. }
  assert (Hb : derivable_pt_lim (mult_real_fct a Iy) s (a * sin (cloth_psi c s))).
  { apply derivable_pt_lim_scal. unfold Iy. apply cloth_Isin_deriv. }
  assert (Hadd : derivable_pt_lim
           (plus_fct (mult_real_fct b Ix) (mult_real_fct a Iy)) s
           (b * cos (cloth_psi c s) + a * sin (cloth_psi c s))).
  { apply derivable_pt_lim_plus; assumption. }
  assert (Hplus : derivable_pt_lim
           (plus_fct (fct_cte loc)
              (plus_fct (mult_real_fct b Ix) (mult_real_fct a Iy))) s
           (0 + (b * cos (cloth_psi c s) + a * sin (cloth_psi c s)))).
  { apply derivable_pt_lim_plus; [apply derivable_pt_lim_const | exact Hadd]. }
  replace (cloth_vy c s)
    with (0 + (b * cos (cloth_psi c s) + a * sin (cloth_psi c s))).
  - apply derivable_pt_lim_ext with
      (f := plus_fct (fct_cte loc)
              (plus_fct (mult_real_fct b Ix) (mult_real_fct a Iy))).
    + intro z. unfold cloth_Py, plus_fct, mult_real_fct, fct_cte.
      unfold Ix, Iy, a, b, loc. ring.
    + exact Hplus.
  - unfold cloth_vy, a, b. ring.
Qed.

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

Lemma cloth_tangent_sumsq :
  forall c s, cloth_h2 c <> 0 ->
    cloth_vx c s * cloth_vx c s + cloth_vy c s * cloth_vy c s = 1.
Proof.
  intros c s Hh.
  unfold cloth_vx, cloth_vy.
  set (a := cloth_cos0 c). set (b := cloth_sin0 c).
  set (u := cos (cloth_psi c s)). set (v := sin (cloth_psi c s)).
  replace ((a * u - b * v) * (a * u - b * v) +
           (b * u + a * v) * (b * u + a * v))
    with ((a * a + b * b) * (u * u + v * v)) by ring.
  assert (Hf : a * a + b * b = 1).
  { unfold a, b. apply cloth_frame_sumsq. exact Hh. }
  assert (Ht : u * u + v * v = 1).
  { unfold u, v. pose proof (sin2_cos2 (cloth_psi c s)) as Hs.
    unfold Rsqr in Hs. rewrite Rplus_comm in Hs. exact Hs. }
  rewrite Hf, Ht. ring.
Qed.

Lemma cloth_unit_speed :
  forall c s, cloth_h2 c <> 0 ->
    sqrt (cloth_vx c s * cloth_vx c s + cloth_vy c s * cloth_vy c s) = 1.
Proof.
  intros c s Hh.
  rewrite (cloth_tangent_sumsq c s Hh).
  apply sqrt_1.
Qed.

Lemma cloth_s_deriv :
  forall c t,
    derivable_pt_lim (cloth_s c) t (cloth_ed c - cloth_sd c).
Proof.
  intros c t.
  set (sd := cloth_sd c).
  set (delta := cloth_ed c - sd).
  assert (E : delta = 0 + delta * 1) by ring.
  apply derivable_pt_lim_ext with
    (f := plus_fct (fct_cte sd) (mult_real_fct delta id)).
  - intro z.
    unfold cloth_s, plus_fct, fct_cte, mult_real_fct, id, sd, delta.
    cbn. rewrite Rmult_comm. reflexivity.
  - rewrite E at 2.
    apply derivable_pt_lim_plus.
    + apply derivable_pt_lim_const.
    + apply derivable_pt_lim_scal. apply derivable_pt_lim_id.
Qed.

Lemma cloth_eval_px_deriv :
  forall c t,
    derivable_pt_lim (fun u => px (cloth_eval c u)) t
      ((cloth_ed c - cloth_sd c) * cloth_vx c (cloth_s c t)).
Proof.
  intros c t.
  replace ((cloth_ed c - cloth_sd c) * cloth_vx c (cloth_s c t))
    with (cloth_vx c (cloth_s c t) * (cloth_ed c - cloth_sd c)) by ring.
  apply derivable_pt_lim_ext with (f := comp (cloth_Px c) (cloth_s c)).
  - intro z. unfold comp, cloth_eval, cloth_P. reflexivity.
  - apply derivable_pt_lim_comp.
    + apply cloth_s_deriv.
    + apply cloth_Px_deriv.
Qed.

Lemma cloth_eval_py_deriv :
  forall c t,
    derivable_pt_lim (fun u => py (cloth_eval c u)) t
      ((cloth_ed c - cloth_sd c) * cloth_vy c (cloth_s c t)).
Proof.
  intros c t.
  replace ((cloth_ed c - cloth_sd c) * cloth_vy c (cloth_s c t))
    with (cloth_vy c (cloth_s c t) * (cloth_ed c - cloth_sd c)) by ring.
  apply derivable_pt_lim_ext with (f := comp (cloth_Py c) (cloth_s c)).
  - intro z. unfold comp, cloth_eval, cloth_P. reflexivity.
  - apply derivable_pt_lim_comp.
    + apply cloth_s_deriv.
    + apply cloth_Py_deriv.
Qed.

Lemma cloth_eval_speed_sq :
  forall c t, cloth_h2 c <> 0 ->
    let d := cloth_ed c - cloth_sd c in
    (d * cloth_vx c (cloth_s c t)) * (d * cloth_vx c (cloth_s c t)) +
    (d * cloth_vy c (cloth_s c t)) * (d * cloth_vy c (cloth_s c t))
      = d * d.
Proof.
  intros c t Hh d.
  set (vx := cloth_vx c (cloth_s c t)).
  set (vy := cloth_vy c (cloth_s c t)).
  assert (H : vx * vx + vy * vy = 1).
  { unfold vx, vy. apply cloth_tangent_sumsq. exact Hh. }
  replace ((d * vx) * (d * vx) + (d * vy) * (d * vy))
    with (d * d * (vx * vx + vy * vy)) by ring.
  rewrite H. ring.
Qed.

Print Assumptions cloth_psi_ball_lip.
Print Assumptions cloth_cos_ball_lip.
Print Assumptions cloth_sin_ball_lip.
Print Assumptions cloth_Icos_as_prim.
Print Assumptions cloth_Isin_as_prim.
Print Assumptions cloth_Icos_deriv.
Print Assumptions cloth_Isin_deriv.
Print Assumptions cloth_Px_deriv.
Print Assumptions cloth_Py_deriv.
Print Assumptions cloth_frame_sumsq.
Print Assumptions cloth_tangent_sumsq.
Print Assumptions cloth_unit_speed.
Print Assumptions cloth_s_deriv.
Print Assumptions cloth_eval_px_deriv.
Print Assumptions cloth_eval_py_deriv.
Print Assumptions cloth_eval_speed_sq.
