(* ============================================================================
   NetTopologySuite.Proofs.ClothoidTraversal
   ----------------------------------------------------------------------------
   Mode A chips on the host clothoid of SheetHenClothoidCore. The host
   eval is already the Fresnel integral (#883). This file does not
   replace it. It proves that eval has the window-start Fresnel form,
   that its arc-length traversal has unit speed and curvature linear in
   arc length, and how reverse and split act on that law.

   Window. d = ed - sd (signed). dir = +1 when d >= 0, else -1.
   L = |d|. Station of arc length s: sd + dir * s.
   kappa(u) = sigma * u / A^2 is the host station curvature.
   Traversal law: k0 = dir * kappa(sd), k1 = dir * kappa(ed), L.

   Fresnel form (cloth_eval_fresnel_form, A <> 0):
     gamma(t) = gamma(0) + R(phi0) * int_0^{t d} (cos th(u), sin th(u)) du
     th(u)    = psi(sd) + kappa(sd) u + (kappa(ed) - kappa(sd)) u^2 / (2 d)
   with R(phi0) the rotation by (cloth_cos0, cloth_sin0), the first
   reference vector over its length: a unit vector when h2 <> 0 (for
   h2 = 0 both entries are 0). The heading is therefore phi0 + th(u);
   phi0 is carried as that vector, not as an angle (Stdlib acos prints
   Classical_Prop.classic). Non-axis fixture: locked_cloth_tilted_heading
   ((cos0, sin0) = (3/5, 4/5), start tangent (3/5, 4/5)).
   For d = 0 the window is a point and both integrals are over [0, 0].
   Endpoints stay derived: cloth_p0 / cloth_p1 are gamma(0) / gamma(1),
   and cloth_arc_ends reads them back from the traversal.

   Headline (cloth_arc_unit_speed_linear_curvature): A <> 0, the first
   reference vector nonzero, d <> 0. The derivatives of
   s |-> P(sd + dir s) are computed (not assumed); the speed is 1 and
   cross(v, a) / |v|^3 = k0 + (k1 - k0) s / L.

   Reverse: cloth_rev of ClothoidLinearize (sd and ed swapped on the
   same placement and A; measures kept). Law (-k1, -k0, L), same image
   read as t -> 1 - t (cloth_rev_reparam), arc of the reverse is the arc
   read from the other end (cloth_rev_arc). Placed reverse under any
   linear map: ClothoidPlacement.cloth_placed_rev_law.
   Split: cloth_split of the core. The split rule lemmas already live
   there (cloth_split_eval_left / _right / _join / _left_start /
   _right_end). Here: the children carry the parent law, cut at
   k0 + (k1 - k0) t (cloth_split_traversal_law).
   Fixture: the locked pair of ClothoidCookMkClothoid (interior Hit,
   ti <> tj, named chord crossing) read as laws (0, 1, 1) and (1, 0, 1).

   claimId: none new. The clothoid letters keep 0007-clothoid-first-cook
   / 0007-intake-mkclothoid; this file adds no claim row and no WITNESS.
   3-axiom host. No Admitted / Axiom / Parameter. No RiemannInt. No MVT.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
   ========================================================================== *)

From Stdlib Require Import Reals Lra Ranalysis1.
From NTS.Proofs Require Import Distance LipInt LipIntFTC SheetHenClothoidCore
  ClothoidTangent ClothoidNorm2 SignedCurvature SheetHenClothoidFrames
  ClothoidLinearize ClothoidLinearizeContract ClothoidCookMkClothoid.
Local Open Scope R_scope.

Lemma cloth_sq_deriv : forall s, derivable_pt_lim (fun u => u * u) s (2 * s).
Proof.
  intro s.
  apply derivable_pt_lim_ext with (f := mult_fct id id).
  - intro x. reflexivity.
  - replace (2 * s) with (1 * id s + id s * 1) by (unfold id; ring).
    apply derivable_pt_lim_mult; apply derivable_pt_lim_id.
Qed.

Lemma cloth_lin2_deriv : forall f g a b x lf lg,
  derivable_pt_lim f x lf -> derivable_pt_lim g x lg ->
  derivable_pt_lim (fun u => a * f u + b * g u) x (a * lf + b * lg).
Proof.
  intros f g a b x lf lg Hf Hg.
  apply derivable_pt_lim_ext with
    (f := plus_fct (mult_real_fct a f) (mult_real_fct b g)).
  - intro u. reflexivity.
  - apply derivable_pt_lim_plus; apply derivable_pt_lim_scal; assumption.
Qed.

Lemma cloth_psi_deriv : forall c s, cloth_A c <> 0 ->
  derivable_pt_lim (cloth_psi c) s (cloth_kappa c s).
Proof.
  intros c s HA.
  set (k := cloth_sigma c / (2 * cloth_A c * cloth_A c)).
  apply derivable_pt_lim_ext with (f := fun u => k * (u * u) + 0 * u).
  - intro u. unfold cloth_psi, k. field. exact HA.
  - replace (cloth_kappa c s) with (k * (2 * s) + 0 * 1).
    + apply cloth_lin2_deriv; [apply cloth_sq_deriv | apply derivable_pt_lim_id].
    + unfold k, cloth_kappa. field. exact HA.
Qed.

Lemma cloth_cos_psi_deriv : forall c s, cloth_A c <> 0 ->
  derivable_pt_lim (fun u => cos (cloth_psi c u)) s
    (- sin (cloth_psi c s) * cloth_kappa c s).
Proof.
  intros c s HA.
  apply derivable_pt_lim_ext with (f := comp cos (cloth_psi c)).
  - intro u. reflexivity.
  - apply derivable_pt_lim_comp; [apply cloth_psi_deriv; exact HA|].
    apply derivable_pt_lim_cos.
Qed.

Lemma cloth_sin_psi_deriv : forall c s, cloth_A c <> 0 ->
  derivable_pt_lim (fun u => sin (cloth_psi c u)) s
    (cos (cloth_psi c s) * cloth_kappa c s).
Proof.
  intros c s HA.
  apply derivable_pt_lim_ext with (f := comp sin (cloth_psi c)).
  - intro u. reflexivity.
  - apply derivable_pt_lim_comp; [apply cloth_psi_deriv; exact HA|].
    apply derivable_pt_lim_sin.
Qed.

Lemma cloth_vx_deriv : forall c s, cloth_A c <> 0 ->
  derivable_pt_lim (cloth_vx c) s (- cloth_kappa c s * cloth_vy c s).
Proof.
  intros c s HA.
  apply derivable_pt_lim_ext with
    (f := fun u => cloth_cos0 c * cos (cloth_psi c u)
                   + (- cloth_sin0 c) * sin (cloth_psi c u)).
  - intro u. unfold cloth_vx. ring.
  - replace (- cloth_kappa c s * cloth_vy c s) with
      (cloth_cos0 c * (- sin (cloth_psi c s) * cloth_kappa c s)
       + (- cloth_sin0 c) * (cos (cloth_psi c s) * cloth_kappa c s))
      by (unfold cloth_vy; ring).
    apply cloth_lin2_deriv;
      [apply cloth_cos_psi_deriv | apply cloth_sin_psi_deriv]; exact HA.
Qed.

Lemma cloth_vy_deriv : forall c s, cloth_A c <> 0 ->
  derivable_pt_lim (cloth_vy c) s (cloth_kappa c s * cloth_vx c s).
Proof.
  intros c s HA.
  apply derivable_pt_lim_ext with
    (f := fun u => cloth_sin0 c * cos (cloth_psi c u)
                   + cloth_cos0 c * sin (cloth_psi c u)).
  - intro u. unfold cloth_vy. ring.
  - replace (cloth_kappa c s * cloth_vx c s) with
      (cloth_sin0 c * (- sin (cloth_psi c s) * cloth_kappa c s)
       + cloth_cos0 c * (cos (cloth_psi c s) * cloth_kappa c s))
      by (unfold cloth_vx; ring).
    apply cloth_lin2_deriv;
      [apply cloth_cos_psi_deriv | apply cloth_sin_psi_deriv]; exact HA.
Qed.

(* Traversal by arc length. *)
Definition cloth_d (c : ClothoidEgg) : R := cloth_ed c - cloth_sd c.

Definition cloth_dir (c : ClothoidEgg) : R :=
  if Rle_dec 0 (cloth_d c) then 1 else -1.

Definition cloth_tlen (c : ClothoidEgg) : R := Rabs (cloth_d c).

Definition cloth_tk0 (c : ClothoidEgg) : R :=
  cloth_dir c * cloth_kappa c (cloth_sd c).

Definition cloth_tk1 (c : ClothoidEgg) : R :=
  cloth_dir c * cloth_kappa c (cloth_ed c).

Definition cloth_station (c : ClothoidEgg) (s : R) : R :=
  cloth_sd c + cloth_dir c * s.

Definition cloth_arc (c : ClothoidEgg) (s : R) : Point :=
  cloth_P c (cloth_station c s).

Definition cloth_arc_v (c : ClothoidEgg) (s : R) : Point :=
  mkPoint (cloth_dir c * cloth_vx c (cloth_station c s))
          (cloth_dir c * cloth_vy c (cloth_station c s)).

Definition cloth_arc_a (c : ClothoidEgg) (s : R) : Point :=
  mkPoint (- cloth_kappa c (cloth_station c s) * cloth_vy c (cloth_station c s))
          (cloth_kappa c (cloth_station c s) * cloth_vx c (cloth_station c s)).

Lemma cloth_dir_sq : forall c, cloth_dir c * cloth_dir c = 1.
Proof.
  intro c. unfold cloth_dir. destruct (Rle_dec 0 (cloth_d c)); ring.
Qed.

Lemma cloth_dir_abs : forall c, cloth_dir c * cloth_d c = cloth_tlen c.
Proof.
  intro c. unfold cloth_dir, cloth_tlen.
  destruct (Rle_dec 0 (cloth_d c)) as [H|H].
  - rewrite Rabs_right by lra. ring.
  - rewrite Rabs_left by lra. ring.
Qed.

Lemma cloth_tlen_pos : forall c, cloth_d c <> 0 -> 0 < cloth_tlen c.
Proof. intros c H. unfold cloth_tlen. apply Rabs_pos_lt. exact H. Qed.

Lemma cloth_station_deriv : forall c s,
  derivable_pt_lim (cloth_station c) s (cloth_dir c).
Proof.
  intros c s.
  apply derivable_pt_lim_ext with
    (f := fun u => cloth_sd c * 1 + cloth_dir c * id u).
  - intro u. unfold cloth_station, id. ring.
  - pose proof (cloth_lin2_deriv (fun _ => 1) id (cloth_sd c) (cloth_dir c) s 0 1
      (derivable_pt_lim_const 1 s) (derivable_pt_lim_id s)) as H.
    replace (cloth_sd c * 0 + cloth_dir c * 1) with (cloth_dir c) in H by ring.
    exact H.
Qed.

Lemma cloth_comp_station_deriv : forall c f s l,
  derivable_pt_lim f (cloth_station c s) l ->
  derivable_pt_lim (fun u => f (cloth_station c u)) s (cloth_dir c * l).
Proof.
  intros c f s l Hf.
  apply derivable_pt_lim_ext with (f := comp f (cloth_station c)).
  - intro u. reflexivity.
  - replace (cloth_dir c * l) with (l * cloth_dir c) by ring.
    apply derivable_pt_lim_comp; [apply cloth_station_deriv | exact Hf].
Qed.

Lemma cloth_arc_px_deriv : forall c s,
  derivable_pt_lim (fun u => px (cloth_arc c u)) s (px (cloth_arc_v c s)).
Proof.
  intros c s. unfold cloth_arc, cloth_arc_v. cbn [px].
  apply (cloth_comp_station_deriv c (cloth_Px c)). apply cloth_Px_deriv.
Qed.

Lemma cloth_arc_py_deriv : forall c s,
  derivable_pt_lim (fun u => py (cloth_arc c u)) s (py (cloth_arc_v c s)).
Proof.
  intros c s. unfold cloth_arc, cloth_arc_v. cbn [py].
  apply (cloth_comp_station_deriv c (cloth_Py c)). apply cloth_Py_deriv.
Qed.

Lemma cloth_arc_vx_deriv : forall c s, cloth_A c <> 0 ->
  derivable_pt_lim (fun u => px (cloth_arc_v c u)) s (px (cloth_arc_a c s)).
Proof.
  intros c s HA. unfold cloth_arc_v, cloth_arc_a. cbn [px].
  set (st := cloth_station c s).
  apply derivable_pt_lim_ext with
    (f := fun u => cloth_dir c * cloth_vx c (cloth_station c u) + 0 * u).
  - intro u. ring.
  - replace (- cloth_kappa c st * cloth_vy c st) with
      (cloth_dir c * (cloth_dir c * (- cloth_kappa c st * cloth_vy c st)) + 0 * 1).
    + apply cloth_lin2_deriv; [|apply derivable_pt_lim_id].
      apply cloth_comp_station_deriv. apply cloth_vx_deriv. exact HA.
    + rewrite <- Rmult_assoc, cloth_dir_sq. ring.
Qed.

Lemma cloth_arc_vy_deriv : forall c s, cloth_A c <> 0 ->
  derivable_pt_lim (fun u => py (cloth_arc_v c u)) s (py (cloth_arc_a c s)).
Proof.
  intros c s HA. unfold cloth_arc_v, cloth_arc_a. cbn [py].
  set (st := cloth_station c s).
  apply derivable_pt_lim_ext with
    (f := fun u => cloth_dir c * cloth_vy c (cloth_station c u) + 0 * u).
  - intro u. ring.
  - replace (cloth_kappa c st * cloth_vx c st) with
      (cloth_dir c * (cloth_dir c * (cloth_kappa c st * cloth_vx c st)) + 0 * 1).
    + apply cloth_lin2_deriv; [|apply derivable_pt_lim_id].
      apply cloth_comp_station_deriv. apply cloth_vy_deriv. exact HA.
    + rewrite <- Rmult_assoc, cloth_dir_sq. ring.
Qed.

Lemma cloth_arc_speed2 : forall c s, cloth_h2 c <> 0 ->
  curv_speed2 (cloth_arc_v c s) = 1.
Proof.
  intros c s Hh. unfold curv_speed2, cloth_arc_v. cbn [px py].
  set (st := cloth_station c s).
  replace (cloth_dir c * cloth_vx c st * (cloth_dir c * cloth_vx c st) +
           cloth_dir c * cloth_vy c st * (cloth_dir c * cloth_vy c st))
    with ((cloth_dir c * cloth_dir c) *
          (cloth_vx c st * cloth_vx c st + cloth_vy c st * cloth_vy c st)) by ring.
  rewrite cloth_dir_sq, cloth_tangent_sumsq by exact Hh. ring.
Qed.

Lemma cloth_arc_signed_curv : forall c s, cloth_h2 c <> 0 ->
  signed_curv (cloth_arc_v c s) (cloth_arc_a c s)
    = cloth_dir c * cloth_kappa c (cloth_station c s).
Proof.
  intros c s Hh. unfold signed_curv. rewrite cloth_arc_speed2 by exact Hh.
  rewrite sqrt_1.
  unfold curv_cross, cloth_arc_v, cloth_arc_a. cbn [px py].
  set (st := cloth_station c s).
  pose proof (cloth_tangent_sumsq c st Hh) as H1.
  replace (cloth_dir c * cloth_vx c st * (cloth_kappa c st * cloth_vx c st) -
           cloth_dir c * cloth_vy c st * (- cloth_kappa c st * cloth_vy c st))
    with (cloth_dir c * cloth_kappa c st *
          (cloth_vx c st * cloth_vx c st + cloth_vy c st * cloth_vy c st)) by ring.
  rewrite H1. field.
Qed.

Lemma cloth_kappa_traversal_linear : forall c s,
  cloth_d c <> 0 ->
  cloth_dir c * cloth_kappa c (cloth_station c s)
    = cloth_tk0 c + (cloth_tk1 c - cloth_tk0 c) * s / cloth_tlen c.
Proof.
  intros c s Hd.
  assert (Hl : cloth_tlen c <> 0) by (apply Rgt_not_eq, cloth_tlen_pos; exact Hd).
  rewrite <- (cloth_dir_abs c) in *.
  unfold cloth_tk0, cloth_tk1, cloth_kappa, cloth_station.
  unfold cloth_d in *.
  set (D := cloth_dir c) in *.
  set (k := cloth_sigma c / (cloth_A c * cloth_A c)).
  replace (cloth_sigma c * (cloth_sd c + D * s) / (cloth_A c * cloth_A c))
    with (k * (cloth_sd c + D * s)) by (unfold k, Rdiv; ring).
  replace (cloth_sigma c * cloth_sd c / (cloth_A c * cloth_A c))
    with (k * cloth_sd c) by (unfold k, Rdiv; ring).
  replace (cloth_sigma c * cloth_ed c / (cloth_A c * cloth_A c))
    with (k * cloth_ed c) by (unfold k, Rdiv; ring).
  assert (HD : D * D = 1) by apply cloth_dir_sq.
  assert (HDn : D <> 0) by (intro Hz; rewrite Hz in HD; lra).
  replace ((D * (k * cloth_ed c) - D * (k * cloth_sd c)) * s /
           (D * (cloth_ed c - cloth_sd c))) with (k * s)
    by (field; split; assumption).
  replace (D * (k * (cloth_sd c + D * s))) with
    (D * (k * cloth_sd c) + (D * D) * k * s) by ring.
  rewrite HD. ring.
Qed.

Theorem cloth_arc_unit_speed_linear_curvature : forall c s,
  cloth_A c <> 0 -> cloth_h2 c <> 0 -> cloth_d c <> 0 ->
  derivable_pt_lim (fun u => px (cloth_arc c u)) s (px (cloth_arc_v c s)) /\
  derivable_pt_lim (fun u => py (cloth_arc c u)) s (py (cloth_arc_v c s)) /\
  derivable_pt_lim (fun u => px (cloth_arc_v c u)) s (px (cloth_arc_a c s)) /\
  derivable_pt_lim (fun u => py (cloth_arc_v c u)) s (py (cloth_arc_a c s)) /\
  sqrt (curv_speed2 (cloth_arc_v c s)) = 1 /\
  signed_curv (cloth_arc_v c s) (cloth_arc_a c s)
    = cloth_tk0 c + (cloth_tk1 c - cloth_tk0 c) * s / cloth_tlen c.
Proof.
  intros c s HA Hh Hd.
  split; [apply cloth_arc_px_deriv|].
  split; [apply cloth_arc_py_deriv|].
  split; [apply cloth_arc_vx_deriv; exact HA|].
  split; [apply cloth_arc_vy_deriv; exact HA|].
  split.
  - rewrite cloth_arc_speed2 by exact Hh. apply sqrt_1.
  - rewrite cloth_arc_signed_curv by exact Hh.
    apply cloth_kappa_traversal_linear. exact Hd.
Qed.

Lemma cloth_dir_nz : forall c, cloth_dir c <> 0.
Proof. intro c. unfold cloth_dir. destruct (Rle_dec 0 (cloth_d c)); lra. Qed.

Lemma cloth_arc_eval : forall c s, cloth_d c <> 0 ->
  cloth_arc c s = cloth_eval c (s / cloth_tlen c).
Proof.
  intros c s Hd. unfold cloth_arc, cloth_eval, cloth_s, cloth_station.
  f_equal.
  rewrite <- (cloth_dir_abs c).
  unfold cloth_d in *. unfold cloth_dir, cloth_d.
  destruct (Rle_dec 0 (cloth_ed c - cloth_sd c)); field; exact Hd.
Qed.

Lemma cloth_arc_ends : forall c, cloth_d c <> 0 ->
  cloth_arc c 0 = cloth_eval c 0 /\ cloth_arc c (cloth_tlen c) = cloth_eval c 1.
Proof.
  intros c Hd. split; rewrite cloth_arc_eval by exact Hd; f_equal.
  - unfold Rdiv. ring.
  - field. apply Rgt_not_eq, cloth_tlen_pos. exact Hd.
Qed.

(* Fresnel form from the window start. *)
Definition cloth_q (c : ClothoidEgg) : R :=
  (cloth_kappa c (cloth_ed c) - cloth_kappa c (cloth_sd c)) / cloth_d c.

Definition cloth_wtheta (c : ClothoidEgg) (u : R) : R :=
  cloth_psi c (cloth_sd c) + cloth_kappa c (cloth_sd c) * u
    + cloth_q c * u * u / 2.

Lemma cloth_psi_station_law : forall c u,
  cloth_A c <> 0 -> cloth_d c <> 0 ->
  cloth_psi c (cloth_sd c + u) = cloth_wtheta c u.
Proof.
  intros c u HA Hd. unfold cloth_wtheta, cloth_q, cloth_psi, cloth_kappa.
  unfold cloth_d in *. field. split; assumption.
Qed.

Lemma cloth_kappa_station_law : forall c u,
  cloth_d c <> 0 ->
  cloth_kappa c (cloth_sd c + u)
    = cloth_kappa c (cloth_sd c)
      + (cloth_kappa c (cloth_ed c) - cloth_kappa c (cloth_sd c)) * u / cloth_d c.
Proof.
  intros c u Hd. unfold cloth_kappa, cloth_d in *.
  unfold Rdiv. set (k := / (cloth_A c * cloth_A c)). field. exact Hd.
Qed.

Definition cloth_wtheta_K (c : ClothoidEgg) (sg : R) : R :=
  Rabs (cloth_kappa c (cloth_sd c)) + Rabs (cloth_q c) * Rabs sg.

Lemma cloth_wtheta_K_nonneg : forall c sg, 0 <= cloth_wtheta_K c sg.
Proof.
  intros c sg. unfold cloth_wtheta_K.
  apply Rplus_le_le_0_compat; [apply Rabs_pos|].
  apply Rmult_le_pos; apply Rabs_pos.
Qed.

Lemma cloth_wtheta_lip : forall c sg x y,
  Rmin 0 sg <= x <= Rmax 0 sg -> Rmin 0 sg <= y <= Rmax 0 sg ->
  Rabs (cloth_wtheta c x - cloth_wtheta c y) <= cloth_wtheta_K c sg * Rabs (x - y).
Proof.
  intros c sg x y Hx Hy.
  pose proof (cloth_window_abs sg x Hx) as Ax.
  pose proof (cloth_window_abs sg y Hy) as Ay.
  set (k0 := cloth_kappa c (cloth_sd c)). set (q := cloth_q c).
  replace (cloth_wtheta c x - cloth_wtheta c y)
    with ((x - y) * (k0 + q * ((x + y) / 2)))
    by (unfold cloth_wtheta, k0, q; field).
  rewrite Rabs_mult, Rmult_comm.
  apply Rmult_le_compat_r; [apply Rabs_pos|].
  unfold cloth_wtheta_K. fold k0 q.
  eapply Rle_trans; [apply Rabs_triang|].
  apply Rplus_le_compat_l. rewrite Rabs_mult.
  apply Rmult_le_compat_l; [apply Rabs_pos|].
  unfold Rdiv. rewrite Rabs_mult.
  assert (Hxy : Rabs (x + y) <= 2 * Rabs sg).
  { eapply Rle_trans; [apply Rabs_triang|]. lra. }
  rewrite (Rabs_right (/ 2)) by lra. lra.
Qed.

Lemma cloth_cos_theta_lip : forall c sg x y,
  Rmin 0 sg <= x <= Rmax 0 sg -> Rmin 0 sg <= y <= Rmax 0 sg ->
  Rabs (cos (cloth_wtheta c x) - cos (cloth_wtheta c y))
    <= cloth_wtheta_K c sg * Rabs (x - y).
Proof.
  intros. eapply Rle_trans; [apply cos_lip | apply cloth_wtheta_lip; assumption].
Qed.

Lemma cloth_sin_theta_lip : forall c sg x y,
  Rmin 0 sg <= x <= Rmax 0 sg -> Rmin 0 sg <= y <= Rmax 0 sg ->
  Rabs (sin (cloth_wtheta c x) - sin (cloth_wtheta c y))
    <= cloth_wtheta_K c sg * Rabs (x - y).
Proof.
  intros. eapply Rle_trans; [apply sin_lip | apply cloth_wtheta_lip; assumption].
Qed.

(* int_0^sg cos theta(u) du and int_0^sg sin theta(u) du. *)
Definition cloth_fresnel_C (c : ClothoidEgg) (sg : R) : R :=
  int_seg (fun u => cos (cloth_wtheta c u)) (cloth_wtheta_K c sg) 0 sg
    (cloth_wtheta_K_nonneg c sg) (cloth_cos_theta_lip c sg).

Definition cloth_fresnel_S (c : ClothoidEgg) (sg : R) : R :=
  int_seg (fun u => sin (cloth_wtheta c u)) (cloth_wtheta_K c sg) 0 sg
    (cloth_wtheta_K_nonneg c sg) (cloth_sin_theta_lip c sg).

Lemma dyadic_shift : forall g h k a b,
  dyadic g k (a + h) (b + h) = dyadic (fun u => g (u + h)) k a b.
Proof.
  intros g h k. induction k as [|k IH]; intros a b; simpl.
  - replace (b + h - (a + h)) with (b - a) by ring. reflexivity.
  - replace ((a + h + (b + h)) / 2) with ((a + b) / 2 + h) by field.
    rewrite IH, IH. reflexivity.
Qed.

Lemma int_seg_shift : forall g h K a b a' b' HK Hlip Hlip',
  a' = a + h -> b' = b + h ->
  int_seg g K a' b' HK Hlip = int_seg (fun u => g (u + h)) K a b HK Hlip'.
Proof.
  intros g h K a b a' b' HK Hlip Hlip' Ea Eb. subst a' b'.
  unfold int_seg.
  destruct (Rle_dec (a + h) (b + h)) as [H1|H1];
  destruct (Rle_dec a b) as [H2|H2]; try (exfalso; lra).
  - apply UL_sequence with (fun n => dyadic g n (a + h) (b + h)).
    + apply lint_cv_dyadic.
    + apply seq_ext with (u := fun n => dyadic (fun u => g (u + h)) n a b).
      * intro n. symmetry. apply dyadic_shift.
      * apply lint_cv_dyadic.
  - f_equal.
    apply UL_sequence with (fun n => dyadic g n (b + h) (a + h)).
    + apply lint_cv_dyadic.
    + apply seq_ext with (u := fun n => dyadic (fun u => g (u + h)) n b a).
      * intro n. symmetry. apply dyadic_shift.
      * apply lint_cv_dyadic.
Qed.

Lemma cloth_ball_of_abs : forall z R, Rabs z <= R -> - R <= z <= R.
Proof. intros z R H. unfold Rabs in H. destruct (Rcase_abs z); split; lra. Qed.

Lemma cloth_window_ball : forall sd sg x,
  Rmin 0 sg <= x <= Rmax 0 sg ->
  - (Rabs sd + Rabs sg + 1) <= x + sd <= Rabs sd + Rabs sg + 1.
Proof.
  intros sd sg x Hx. apply cloth_ball_of_abs.
  pose proof (cloth_window_abs sg x Hx).
  eapply Rle_trans; [apply Rabs_triang|]. lra.
Qed.

Lemma cloth_Icos_window : forall c sg,
  cloth_A c <> 0 -> cloth_d c <> 0 ->
  cloth_Icos c (cloth_sd c + sg) - cloth_Icos c (cloth_sd c)
    = cloth_fresnel_C c sg.
Proof.
  intros c sg HA Hd.
  set (sd := cloth_sd c).
  set (R0 := Rabs sd + Rabs sg + 1).
  assert (HR : 0 <= R0).
  { unfold R0. pose proof (Rabs_pos sd). pose proof (Rabs_pos sg). lra. }
  assert (H0 : - R0 <= 0 <= R0) by lra.
  assert (Hsd : - R0 <= sd <= R0).
  { apply cloth_ball_of_abs. unfold R0. pose proof (Rabs_pos sg). lra. }
  assert (Hz : - R0 <= sd + sg <= R0).
  { apply cloth_ball_of_abs. unfold R0.
    eapply Rle_trans; [apply Rabs_triang|]. lra. }
  rewrite <- (cloth_Icos_as_prim c R0 HR (sd + sg) Hz).
  rewrite <- (cloth_Icos_as_prim c R0 HR sd Hsd).
  set (g := fun u => cos (cloth_psi c u)).
  set (Hb := fun x y Hx Hy => cloth_cos_ball_lip c R0 x y HR Hx Hy).
  rewrite (lipPrim_chasles g (- R0) R0 _ (cloth_phi_K_nonneg c R0) Hb 0 (sd + sg) H0 Hz).
  rewrite (lipPrim_chasles g (- R0) R0 _ (cloth_phi_K_nonneg c R0) Hb 0 sd H0 Hsd).
  replace (lipF g (- R0) R0 (cloth_phi_K c R0) (cloth_phi_K_nonneg c R0) Hb (sd + sg) -
           lipF g (- R0) R0 (cloth_phi_K c R0) (cloth_phi_K_nonneg c R0) Hb 0 -
           (lipF g (- R0) R0 (cloth_phi_K c R0) (cloth_phi_K_nonneg c R0) Hb sd -
            lipF g (- R0) R0 (cloth_phi_K c R0) (cloth_phi_K_nonneg c R0) Hb 0))
    with (lipF g (- R0) R0 (cloth_phi_K c R0) (cloth_phi_K_nonneg c R0) Hb (sd + sg) -
          lipF g (- R0) R0 (cloth_phi_K c R0) (cloth_phi_K_nonneg c R0) Hb sd) by ring.
  rewrite <- (lipPrim_chasles g (- R0) R0 _ (cloth_phi_K_nonneg c R0) Hb sd (sd + sg) Hsd Hz).
  rewrite (lipPrim_as_seg g (- R0) R0 _ (cloth_phi_K_nonneg c R0) Hb sd (sd + sg) Hsd Hz).
  assert (Hsh : forall x y,
    Rmin 0 sg <= x <= Rmax 0 sg -> Rmin 0 sg <= y <= Rmax 0 sg ->
    Rabs (g (x + sd) - g (y + sd)) <= cloth_phi_K c R0 * Rabs (x - y)).
  { intros x y Hx Hy. unfold g.
    replace (x - y) with ((x + sd) - (y + sd)) by ring.
    apply cloth_cos_ball_lip; [exact HR | apply cloth_window_ball; exact Hx
                                        | apply cloth_window_ball; exact Hy]. }
  rewrite (int_seg_shift g sd _ 0 sg sd (sd + sg) _ _ Hsh) by ring.
  assert (Hth : forall u, g (u + sd) = cos (cloth_wtheta c u)).
  { intro u. unfold g, sd. rewrite Rplus_comm.
    rewrite cloth_psi_station_law by assumption. reflexivity. }
  assert (Hsh2 : forall x y,
    Rmin 0 sg <= x <= Rmax 0 sg -> Rmin 0 sg <= y <= Rmax 0 sg ->
    Rabs (g (x + sd) - g (y + sd)) <= cloth_wtheta_K c sg * Rabs (x - y)).
  { intros x y Hx Hy. rewrite !Hth. apply cloth_cos_theta_lip; assumption. }
  rewrite (int_seg_L (fun u => g (u + sd)) _ (cloth_wtheta_K c sg) 0 sg _
             (cloth_wtheta_K_nonneg c sg) Hsh Hsh2).
  unfold cloth_fresnel_C.
  apply int_seg_ext. intros u _. apply Hth.
Qed.

Lemma cloth_Isin_window : forall c sg,
  cloth_A c <> 0 -> cloth_d c <> 0 ->
  cloth_Isin c (cloth_sd c + sg) - cloth_Isin c (cloth_sd c)
    = cloth_fresnel_S c sg.
Proof.
  intros c sg HA Hd.
  set (sd := cloth_sd c).
  set (R0 := Rabs sd + Rabs sg + 1).
  assert (HR : 0 <= R0).
  { unfold R0. pose proof (Rabs_pos sd). pose proof (Rabs_pos sg). lra. }
  assert (H0 : - R0 <= 0 <= R0) by lra.
  assert (Hsd : - R0 <= sd <= R0).
  { apply cloth_ball_of_abs. unfold R0. pose proof (Rabs_pos sg). lra. }
  assert (Hz : - R0 <= sd + sg <= R0).
  { apply cloth_ball_of_abs. unfold R0.
    eapply Rle_trans; [apply Rabs_triang|]. lra. }
  rewrite <- (cloth_Isin_as_prim c R0 HR (sd + sg) Hz).
  rewrite <- (cloth_Isin_as_prim c R0 HR sd Hsd).
  set (g := fun u => sin (cloth_psi c u)).
  set (Hb := fun x y Hx Hy => cloth_sin_ball_lip c R0 x y HR Hx Hy).
  rewrite (lipPrim_chasles g (- R0) R0 _ (cloth_phi_K_nonneg c R0) Hb 0 (sd + sg) H0 Hz).
  rewrite (lipPrim_chasles g (- R0) R0 _ (cloth_phi_K_nonneg c R0) Hb 0 sd H0 Hsd).
  replace (lipF g (- R0) R0 (cloth_phi_K c R0) (cloth_phi_K_nonneg c R0) Hb (sd + sg) -
           lipF g (- R0) R0 (cloth_phi_K c R0) (cloth_phi_K_nonneg c R0) Hb 0 -
           (lipF g (- R0) R0 (cloth_phi_K c R0) (cloth_phi_K_nonneg c R0) Hb sd -
            lipF g (- R0) R0 (cloth_phi_K c R0) (cloth_phi_K_nonneg c R0) Hb 0))
    with (lipF g (- R0) R0 (cloth_phi_K c R0) (cloth_phi_K_nonneg c R0) Hb (sd + sg) -
          lipF g (- R0) R0 (cloth_phi_K c R0) (cloth_phi_K_nonneg c R0) Hb sd) by ring.
  rewrite <- (lipPrim_chasles g (- R0) R0 _ (cloth_phi_K_nonneg c R0) Hb sd (sd + sg) Hsd Hz).
  rewrite (lipPrim_as_seg g (- R0) R0 _ (cloth_phi_K_nonneg c R0) Hb sd (sd + sg) Hsd Hz).
  assert (Hsh : forall x y,
    Rmin 0 sg <= x <= Rmax 0 sg -> Rmin 0 sg <= y <= Rmax 0 sg ->
    Rabs (g (x + sd) - g (y + sd)) <= cloth_phi_K c R0 * Rabs (x - y)).
  { intros x y Hx Hy. unfold g.
    replace (x - y) with ((x + sd) - (y + sd)) by ring.
    apply cloth_sin_ball_lip; [exact HR | apply cloth_window_ball; exact Hx
                                        | apply cloth_window_ball; exact Hy]. }
  rewrite (int_seg_shift g sd _ 0 sg sd (sd + sg) _ _ Hsh) by ring.
  assert (Hth : forall u, g (u + sd) = sin (cloth_wtheta c u)).
  { intro u. unfold g, sd. rewrite Rplus_comm.
    rewrite cloth_psi_station_law by assumption. reflexivity. }
  assert (Hsh2 : forall x y,
    Rmin 0 sg <= x <= Rmax 0 sg -> Rmin 0 sg <= y <= Rmax 0 sg ->
    Rabs (g (x + sd) - g (y + sd)) <= cloth_wtheta_K c sg * Rabs (x - y)).
  { intros x y Hx Hy. rewrite !Hth. apply cloth_sin_theta_lip; assumption. }
  rewrite (int_seg_L (fun u => g (u + sd)) _ (cloth_wtheta_K c sg) 0 sg _
             (cloth_wtheta_K_nonneg c sg) Hsh Hsh2).
  unfold cloth_fresnel_S.
  apply int_seg_ext. intros u _. apply Hth.
Qed.

Theorem cloth_eval_fresnel_form : forall c t,
  cloth_A c <> 0 ->
  cloth_eval c t =
    mkPoint
      (px (cloth_eval c 0) + cloth_cos0 c * cloth_fresnel_C c (t * cloth_d c)
                           - cloth_sin0 c * cloth_fresnel_S c (t * cloth_d c))
      (py (cloth_eval c 0) + cloth_sin0 c * cloth_fresnel_C c (t * cloth_d c)
                           + cloth_cos0 c * cloth_fresnel_S c (t * cloth_d c)).
Proof.
  intros c t HA.
  assert (E0 : cloth_s c 0 = cloth_sd c) by (unfold cloth_s; ring).
  assert (Et : cloth_s c t = cloth_sd c + t * cloth_d c) by (unfold cloth_s, cloth_d; ring).
  destruct (Req_EM_T (cloth_d c) 0) as [Hz|Hd].
  - rewrite Hz, Rmult_0_r.
    unfold cloth_fresnel_C, cloth_fresnel_S. rewrite !int_seg_point.
    unfold cloth_eval. rewrite E0, Et, Hz, Rmult_0_r, Rplus_0_r.
    destruct (cloth_P c (cloth_sd c)) as [x y]. cbn [px py].
    f_equal; ring.
  - rewrite <- (cloth_Icos_window c _ HA Hd), <- (cloth_Isin_window c _ HA Hd).
    unfold cloth_eval, cloth_P, cloth_Px, cloth_Py. cbn [px py].
    rewrite E0, Et. f_equal; ring.
Qed.

(* Reverse: the ClothoidLinearize cloth_rev swaps sd and ed on the same
   placement and A. *)
Lemma cloth_rev_d : forall c, cloth_d (cloth_rev c) = - cloth_d c.
Proof. intro c. unfold cloth_rev, cloth_d, mk_cloth. cbn. ring. Qed.

Lemma cloth_rev_kappa : forall c s, cloth_kappa (cloth_rev c) s = cloth_kappa c s.
Proof. intros [pl A sd ed m0 m1] s. reflexivity. Qed.

Lemma cloth_rev_dir : forall c, cloth_d c <> 0 ->
  cloth_dir (cloth_rev c) = - cloth_dir c.
Proof.
  intros c Hd. unfold cloth_dir. rewrite cloth_rev_d.
  destruct (Rle_dec 0 (- cloth_d c)); destruct (Rle_dec 0 (cloth_d c)); lra.
Qed.

Theorem cloth_rev_traversal_law : forall c, cloth_d c <> 0 ->
  cloth_tk0 (cloth_rev c) = - cloth_tk1 c /\
  cloth_tk1 (cloth_rev c) = - cloth_tk0 c /\
  cloth_tlen (cloth_rev c) = cloth_tlen c.
Proof.
  intros c Hd. unfold cloth_tk0, cloth_tk1, cloth_tlen.
  rewrite cloth_rev_dir, !cloth_rev_kappa, cloth_rev_d by exact Hd.
  unfold cloth_rev, mk_cloth. cbn [cloth_sd cloth_ed].
  split; [ring|]. split; [ring|]. apply Rabs_Ropp.
Qed.

Theorem cloth_rev_reparam : forall c t p,
  on_cloth (cloth_rev c) t p <-> on_cloth c (1 - t) p.
Proof.
  intros c t p. unfold on_cloth. rewrite cloth_eval_rev.
  split; intros [Ht Hp]; split; try exact Hp; lra.
Qed.

Lemma cloth_rev_arc : forall c s, cloth_d c <> 0 ->
  cloth_arc (cloth_rev c) s = cloth_arc c (cloth_tlen c - s).
Proof.
  intros c s Hd. unfold cloth_arc. rewrite cloth_P_rev. f_equal.
  unfold cloth_station. rewrite cloth_rev_dir by exact Hd.
  rewrite <- (cloth_dir_abs c).
  pose proof (cloth_dir_sq c) as HD.
  unfold cloth_rev, mk_cloth, cloth_d. cbn [cloth_sd cloth_ed].
  replace (cloth_sd c + cloth_dir c * (cloth_dir c * (cloth_ed c - cloth_sd c) - s))
    with (cloth_sd c + (cloth_dir c * cloth_dir c) * (cloth_ed c - cloth_sd c)
          - cloth_dir c * s) by ring.
  rewrite HD. ring.
Qed.

Lemma cloth_rev_wf : forall c, cloth_wf c -> cloth_wf (cloth_rev c).
Proof. intros [pl A sd ed m0 m1] H. exact H. Qed.

Theorem cloth_rev_curvature_law : forall c s,
  cloth_A c <> 0 -> cloth_h2 c <> 0 -> cloth_d c <> 0 ->
  signed_curv (cloth_arc_v (cloth_rev c) s) (cloth_arc_a (cloth_rev c) s)
    = - cloth_tk1 c + (- cloth_tk0 c - - cloth_tk1 c) * s / cloth_tlen c.
Proof.
  intros c s HA Hh Hd.
  assert (HA' : cloth_A (cloth_rev c) <> 0) by (destruct c; exact HA).
  assert (Hh' : cloth_h2 (cloth_rev c) <> 0) by (destruct c; exact Hh).
  assert (Hd' : cloth_d (cloth_rev c) <> 0).
  { rewrite cloth_rev_d. intro Hz. apply Hd. lra. }
  destruct (cloth_arc_unit_speed_linear_curvature (cloth_rev c) s HA' Hh' Hd')
    as (_ & _ & _ & _ & _ & Hk).
  rewrite Hk.
  destruct (cloth_rev_traversal_law c Hd) as (E0 & E1 & El).
  rewrite E0, E1, El. reflexivity.
Qed.

(* Split keeps the parent law: the children are the two sub-windows. *)
Lemma cloth_split_kappa : forall c t s,
  cloth_kappa (fst (cloth_split c t)) s = cloth_kappa c s /\
  cloth_kappa (snd (cloth_split c t)) s = cloth_kappa c s.
Proof. intros [pl A sd ed m0 m1] t s. split; reflexivity. Qed.

Theorem cloth_split_traversal_law : forall c t,
  0 < t < 1 -> cloth_d c <> 0 ->
  let km := cloth_tk0 c + (cloth_tk1 c - cloth_tk0 c) * t in
  cloth_tk0 (fst (cloth_split c t)) = cloth_tk0 c /\
  cloth_tk1 (fst (cloth_split c t)) = km /\
  cloth_tlen (fst (cloth_split c t)) = t * cloth_tlen c /\
  cloth_tk0 (snd (cloth_split c t)) = km /\
  cloth_tk1 (snd (cloth_split c t)) = cloth_tk1 c /\
  cloth_tlen (snd (cloth_split c t)) = (1 - t) * cloth_tlen c.
Proof.
  intros c t Ht Hd km.
  assert (EdL : cloth_d (fst (cloth_split c t)) = t * cloth_d c).
  { unfold cloth_split, cloth_d, mk_cloth. cbn. ring. }
  assert (EdR : cloth_d (snd (cloth_split c t)) = (1 - t) * cloth_d c).
  { unfold cloth_split, cloth_d, mk_cloth. cbn. ring. }
  assert (DL : cloth_dir (fst (cloth_split c t)) = cloth_dir c).
  { unfold cloth_dir. rewrite EdL.
    destruct (Rle_dec 0 (t * cloth_d c)) as [H1|H1];
    destruct (Rle_dec 0 (cloth_d c)) as [H2|H2]; try reflexivity; exfalso.
    - apply H2. destruct (Rle_dec 0 (cloth_d c)) as [|H3]; [assumption|].
      assert (cloth_d c < 0) by lra. nra.
    - apply H1. apply Rmult_le_pos; lra. }
  assert (DR : cloth_dir (snd (cloth_split c t)) = cloth_dir c).
  { unfold cloth_dir. rewrite EdR.
    destruct (Rle_dec 0 ((1 - t) * cloth_d c)) as [H1|H1];
    destruct (Rle_dec 0 (cloth_d c)) as [H2|H2]; try reflexivity; exfalso.
    - assert (cloth_d c < 0) by lra. nra.
    - apply H1. apply Rmult_le_pos; lra. }
  destruct (cloth_split_kappa c t (cloth_sd c)) as [KL0 KR0].
  unfold km, cloth_tk0, cloth_tk1, cloth_tlen.
  rewrite DL, DR, EdL, EdR.
  rewrite !(proj1 (cloth_split_kappa c t _)), !(proj2 (cloth_split_kappa c t _)).
  unfold cloth_split, mk_cloth. cbn [fst snd cloth_sd cloth_ed].
  rewrite !Rabs_mult, (Rabs_right t) by lra.
  rewrite (Rabs_right (1 - t)) by lra.
  unfold cloth_kappa, Rdiv.
  repeat split; ring.
Qed.

(* Locked pair of ClothoidCookMkClothoid, read as traversal laws.
   A runs (0, 1, 1). B, the west mirror, runs (1, 0, 1). The reverse
   of A runs (-1, 0, 1): the mirror flips the curvature sign. *)
Lemma locked_cloth_traversal_laws :
  (cloth_tk0 locked_cloth_A = 0 /\ cloth_tk1 locked_cloth_A = 1 /\
   cloth_tlen locked_cloth_A = 1) /\
  (cloth_tk0 locked_cloth_B = 1 /\ cloth_tk1 locked_cloth_B = 0 /\
   cloth_tlen locked_cloth_B = 1) /\
  (cloth_tk0 (cloth_rev locked_cloth_A) = -1 /\
   cloth_tk1 (cloth_rev locked_cloth_A) = 0 /\
   cloth_tlen (cloth_rev locked_cloth_A) = 1).
Proof.
  assert (SA : cloth_sigma locked_cloth_A = 1) by apply east_sigma.
  assert (SB : cloth_sigma locked_cloth_B = -1) by apply west_sigma.
  assert (DA : cloth_d locked_cloth_A = 1)
    by (unfold cloth_d, locked_cloth_A, mk_cloth; cbn; ring).
  assert (DB : cloth_d locked_cloth_B = -1)
    by (unfold cloth_d, locked_cloth_B, mk_cloth; cbn; ring).
  assert (dA : cloth_dir locked_cloth_A = 1).
  { unfold cloth_dir. rewrite DA. destruct (Rle_dec 0 1); [reflexivity | lra]. }
  assert (dB : cloth_dir locked_cloth_B = -1).
  { unfold cloth_dir. rewrite DB. destruct (Rle_dec 0 (-1)); [lra | reflexivity]. }
  assert (HdA : cloth_d locked_cloth_A <> 0) by (rewrite DA; lra).
  destruct (cloth_rev_traversal_law locked_cloth_A HdA) as (R0 & R1 & Rl).
  rewrite R0, R1, Rl.
  unfold cloth_tk0, cloth_tk1, cloth_tlen. rewrite dA, dB, DA, DB.
  unfold cloth_kappa. rewrite SA, SB.
  unfold locked_cloth_A, locked_cloth_B, mk_cloth. cbn [cloth_sd cloth_ed cloth_A].
  replace (Rabs 1) with 1 by (symmetry; apply Rabs_R1).
  replace (Rabs (-1)) with 1 by (rewrite Rabs_left; lra).
  repeat split; field.
Qed.

(* Non-axis heading: ref1 = (3, 4), ref2 = (-4, 3), so (cos0, sin0) =
   (3/5, 4/5) with sin0 <> 0. The Fresnel form rotates by that vector,
   the start tangent of the traversal is (3/5, 4/5), and the law is
   (0, 1, 1). *)
Definition tilted_cloth : ClothoidEgg :=
  mk_cloth (mkAffPlace (mkPoint 0 0) (mkPoint 3 4) (mkPoint (-4) 3)) 1 0 1 None None.

Lemma locked_cloth_tilted_heading :
  cloth_cos0 tilted_cloth = 3 / 5 /\ cloth_sin0 tilted_cloth = 4 / 5 /\
  cloth_arc_v tilted_cloth 0 = mkPoint (3 / 5) (4 / 5) /\
  (forall t, cloth_eval tilted_cloth t =
     mkPoint (px (cloth_eval tilted_cloth 0)
                + 3 / 5 * cloth_fresnel_C tilted_cloth t
                - 4 / 5 * cloth_fresnel_S tilted_cloth t)
             (py (cloth_eval tilted_cloth 0)
                + 4 / 5 * cloth_fresnel_C tilted_cloth t
                + 3 / 5 * cloth_fresnel_S tilted_cloth t)) /\
  cloth_tk0 tilted_cloth = 0 /\ cloth_tk1 tilted_cloth = 1 /\
  cloth_tlen tilted_cloth = 1.
Proof.
  assert (Hy : cloth_hypot tilted_cloth = 5).
  { unfold cloth_hypot, cloth_h2, aff_h2, tilted_cloth, mk_cloth. cbn.
    replace (3 * 3 + 4 * 4) with (5 * 5) by ring. apply sqrt_square. lra. }
  assert (Hc : cloth_cos0 tilted_cloth = 3 / 5).
  { unfold cloth_cos0. rewrite Hy. unfold tilted_cloth, mk_cloth. cbn. reflexivity. }
  assert (Hs : cloth_sin0 tilted_cloth = 4 / 5).
  { unfold cloth_sin0. rewrite Hy. unfold tilted_cloth, mk_cloth. cbn. reflexivity. }
  assert (Sg : cloth_sigma tilted_cloth = 1).
  { unfold cloth_sigma, cloth_cross, aff_cross, tilted_cloth, mk_cloth. cbn.
    destruct (Rle_dec 0 (3 * 3 - 4 * -4)); [reflexivity | lra]. }
  assert (D : cloth_d tilted_cloth = 1)
    by (unfold cloth_d, tilted_cloth, mk_cloth; cbn; ring).
  assert (Dir : cloth_dir tilted_cloth = 1).
  { unfold cloth_dir. rewrite D. destruct (Rle_dec 0 1); [reflexivity | lra]. }
  assert (HA : cloth_A tilted_cloth <> 0)
    by (unfold tilted_cloth, mk_cloth; cbn; lra).
  split; [exact Hc|]. split; [exact Hs|].
  split.
  - assert (St : cloth_station tilted_cloth 0 = 0).
    { unfold cloth_station. rewrite Dir. unfold tilted_cloth, mk_cloth. cbn. ring. }
    assert (Ps : cloth_psi tilted_cloth 0 = 0)
      by (unfold cloth_psi; rewrite Sg; unfold tilted_cloth, mk_cloth; cbn; field).
    unfold cloth_arc_v, cloth_vx, cloth_vy. rewrite Dir, St, Ps, Hc, Hs, cos_0, sin_0.
    f_equal; field.
  - split.
    + intro t. rewrite (cloth_eval_fresnel_form tilted_cloth t HA).
      rewrite D, Rmult_1_r, Hc, Hs. reflexivity.
    + unfold cloth_tk0, cloth_tk1, cloth_tlen, cloth_kappa.
      rewrite Dir, D, Sg. unfold tilted_cloth, mk_cloth. cbn [cloth_sd cloth_ed cloth_A].
      replace (Rabs 1) with 1 by (symmetry; apply Rabs_R1).
      repeat split; field.
Qed.

Print Assumptions cloth_sq_deriv.
Print Assumptions cloth_lin2_deriv.
Print Assumptions cloth_psi_deriv.
Print Assumptions cloth_cos_psi_deriv.
Print Assumptions cloth_sin_psi_deriv.
Print Assumptions cloth_vx_deriv.
Print Assumptions cloth_vy_deriv.
Print Assumptions cloth_dir_sq.
Print Assumptions cloth_dir_abs.
Print Assumptions cloth_tlen_pos.
Print Assumptions cloth_station_deriv.
Print Assumptions cloth_comp_station_deriv.
Print Assumptions cloth_arc_px_deriv.
Print Assumptions cloth_arc_py_deriv.
Print Assumptions cloth_arc_vx_deriv.
Print Assumptions cloth_arc_vy_deriv.
Print Assumptions cloth_arc_speed2.
Print Assumptions cloth_arc_signed_curv.
Print Assumptions cloth_kappa_traversal_linear.
Print Assumptions cloth_arc_unit_speed_linear_curvature.
Print Assumptions cloth_dir_nz.
Print Assumptions cloth_arc_eval.
Print Assumptions cloth_arc_ends.
Print Assumptions cloth_psi_station_law.
Print Assumptions cloth_kappa_station_law.
Print Assumptions cloth_wtheta_K_nonneg.
Print Assumptions cloth_wtheta_lip.
Print Assumptions cloth_cos_theta_lip.
Print Assumptions cloth_sin_theta_lip.
Print Assumptions dyadic_shift.
Print Assumptions int_seg_shift.
Print Assumptions cloth_ball_of_abs.
Print Assumptions cloth_window_ball.
Print Assumptions cloth_Icos_window.
Print Assumptions cloth_Isin_window.
Print Assumptions cloth_eval_fresnel_form.
Print Assumptions cloth_rev_d.
Print Assumptions cloth_rev_kappa.
Print Assumptions cloth_rev_dir.
Print Assumptions cloth_rev_traversal_law.
Print Assumptions cloth_rev_reparam.
Print Assumptions cloth_rev_arc.
Print Assumptions cloth_rev_wf.
Print Assumptions cloth_rev_curvature_law.
Print Assumptions cloth_split_kappa.
Print Assumptions cloth_split_traversal_law.
Print Assumptions locked_cloth_traversal_laws.
Print Assumptions locked_cloth_tilted_heading.
