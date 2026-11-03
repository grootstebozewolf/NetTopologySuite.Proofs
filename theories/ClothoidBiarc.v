(* ============================================================================
   NetTopologySuite.Proofs.ClothoidBiarc
   ----------------------------------------------------------------------------
   Biarc (and arc-spline) approximation of a host clothoid window, with a
   machine-checked tolerance.  The arc-spline analogue of the chord contract
   `ClothoidLinearizeContract.v : clothoid_linearizes` (tol kappa_max h^2/8).

   Construction.  On the station window [a, b], cut N equal pieces of length
   h = (b - a) / N at nodes x_k = a + k h.  Piece k is the unit-speed
   circular arc (a straight segment when its curvature is 0) that
     - starts where piece k-1 ends (piece 0 starts at the clothoid point
       P(a)),
     - starts with the clothoid tangent T(x_k),
     - has the clothoid curvature at the piece midpoint,
       kappa_k = sigma (x_k + h/2) / A^2.
   Its heading is the linear interpolant of the clothoid heading psi at
   x_k and x_{k+1}, so the pieces join G1 and each node tangent is the
   clothoid tangent exactly (`cbi_spline_g1`).  N = 2 is the biarc.

   Contract.
     |P(u) - spline(u)| <= (u - a) h^2 / (8 A^2) <= (b - a)^3 / (8 A^2 N^2)
   for every u in [a, b], at equal arc length, so both Hausdorff
   directions hold.  The biarc (N = 2) is within (b - a)^3 / (32 A^2):
   `cbi_biarc_within_eps`.  The ε-gate `(b - a)^3 <= 8 A^2 N^2 ε` is a
   contract, not a heuristic; its binary64 evaluation is
   `theories-flocq/ClothoidBiarc_b64.v`.

   Proof.  The heading error of piece k is
     psi(u) - beta_k(u) = sigma (u - x_k)(u - x_{k+1}) / (2 A^2),
   at most h^2 / (8 A^2).  Unit tangents at heading distance d differ by at
   most |d|.  A vector mean-value inequality (`cbi_vec_mvi`, from
   RealMonotone.deriv_nonneg_incr: no MVT, no classic) adds the piece's
   contribution to the start offset it inherits.  The tangent of the
   clothoid is ClothoidTangent.cloth_Px_deriv / cloth_Py_deriv (LipInt FTC).

   claimId: 0007-clothoid-biarc.  witness: cbi_biarc_within_eps.
   3-axiom host. No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia.
From Stdlib Require Import Ranalysis1.
From NTS.Proofs Require Import Distance LipInt SheetHenClothoidCore
  ClothoidTangent RealMonotone ClothoidLinearize ClothoidLinearizeContract.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Circular arcs.                                                             *)
(* -------------------------------------------------------------------------- *)

(* Rotation of the unit vector (tx, ty) by theta. *)
Definition cbi_rot_x (tx ty th : R) : R := tx * cos th - ty * sin th.
Definition cbi_rot_y (tx ty th : R) : R := ty * cos th + tx * sin th.

(* Local coordinates of the unit-speed arc of curvature k after arc
   length x, in the frame (tangent, left normal).  k = 0 is the segment. *)
Definition cbi_arc_X (k x : R) : R :=
  if Req_EM_T k 0 then x else sin (k * x) / k.
Definition cbi_arc_Y (k x : R) : R :=
  if Req_EM_T k 0 then 0 else (1 - cos (k * x)) / k.

(* The arc from Q with unit tangent (tx, ty) and curvature k, at arc
   length x. *)
Definition cbi_arc_pt (Q : Point) (tx ty k x : R) : Point :=
  mkPoint (px Q + tx * cbi_arc_X k x - ty * cbi_arc_Y k x)
          (py Q + ty * cbi_arc_X k x + tx * cbi_arc_Y k x).

Lemma cbi_arc_pt_0 : forall Q tx ty k, cbi_arc_pt Q tx ty k 0 = Q.
Proof.
  intros Q tx ty k. destruct Q as [qx qy].
  unfold cbi_arc_pt, cbi_arc_X, cbi_arc_Y. cbn.
  destruct (Req_EM_T k 0) as [_|Hk].
  - f_equal; ring.
  - rewrite Rmult_0_r, sin_0, cos_0. f_equal; field; exact Hk.
Qed.

(* A piece with k <> 0 lies on the circle of radius 1/|k| centred at
   Q + (-ty, tx)/k: it is a circular arc. *)
Lemma cbi_arc_on_circle : forall Q tx ty k x,
  k <> 0 -> tx * tx + ty * ty = 1 ->
  dist_sq (cbi_arc_pt Q tx ty k x)
          (mkPoint (px Q - ty / k) (py Q + tx / k)) = / (k * k).
Proof.
  intros Q tx ty k x Hk Hu.
  unfold dist_sq, cbi_arc_pt, cbi_arc_X, cbi_arc_Y. cbn.
  destruct (Req_EM_T k 0) as [E|_]; [exfalso; exact (Hk E)|].
  pose proof (sin2_cos2 (k * x)) as Hsc. unfold Rsqr in Hsc.
  replace ((px Q + tx * (sin (k * x) / k) - ty * ((1 - cos (k * x)) / k) -
            (px Q - ty / k)) *
           (px Q + tx * (sin (k * x) / k) - ty * ((1 - cos (k * x)) / k) -
            (px Q - ty / k)) +
           (py Q + ty * (sin (k * x) / k) + tx * ((1 - cos (k * x)) / k) -
            (py Q + tx / k)) *
           (py Q + ty * (sin (k * x) / k) + tx * ((1 - cos (k * x)) / k) -
            (py Q + tx / k)))
    with ((tx * tx + ty * ty) *
          (sin (k * x) * sin (k * x) + cos (k * x) * cos (k * x)) / (k * k))
    by (field; exact Hk).
  rewrite Hu, Hsc. field. exact Hk.
Qed.

(* A piece with k = 0 is the segment from Q along (tx, ty). *)
Lemma cbi_arc_segment : forall Q tx ty x,
  cbi_arc_pt Q tx ty 0 x = mkPoint (px Q + tx * x) (py Q + ty * x).
Proof.
  intros. unfold cbi_arc_pt, cbi_arc_X, cbi_arc_Y.
  destruct (Req_EM_T 0 0) as [_|H]; [|exfalso; apply H; reflexivity].
  f_equal; ring.
Qed.

Lemma cbi_d_scal : forall (f : R -> R) a x l,
  derivable_pt_lim f x l -> derivable_pt_lim (fun u => a * f u) x (a * l).
Proof.
  intros f a x l H.
  apply derivable_pt_lim_ext with (f := mult_real_fct a f).
  - intro u. reflexivity.
  - apply derivable_pt_lim_scal. exact H.
Qed.

Lemma cbi_d_plus : forall (f g : R -> R) x l m,
  derivable_pt_lim f x l -> derivable_pt_lim g x m ->
  derivable_pt_lim (fun u => f u + g u) x (l + m).
Proof.
  intros f g x l m Hf Hg.
  apply derivable_pt_lim_ext with (f := plus_fct f g).
  - intro u. reflexivity.
  - apply derivable_pt_lim_plus; assumption.
Qed.

Lemma cbi_d_minus : forall (f g : R -> R) x l m,
  derivable_pt_lim f x l -> derivable_pt_lim g x m ->
  derivable_pt_lim (fun u => f u - g u) x (l - m).
Proof.
  intros f g x l m Hf Hg.
  apply derivable_pt_lim_ext with (f := minus_fct f g).
  - intro u. reflexivity.
  - apply derivable_pt_lim_minus; assumption.
Qed.

Lemma cbi_shift_deriv : forall k p x,
  derivable_pt_lim (fun u => k * (u - p)) x k.
Proof.
  intros k p x.
  assert (H : derivable_pt_lim (fun u => k * (u - p)) x (k * (1 - 0))).
  { apply (cbi_d_scal (fun u => u - p)).
    apply (cbi_d_minus id (fun _ => p)); [apply derivable_pt_lim_id|].
    apply derivable_pt_lim_const. }
  replace (k * (1 - 0)) with k in H by ring. exact H.
Qed.

Lemma cbi_arc_X_deriv : forall k p x,
  derivable_pt_lim (fun u => cbi_arc_X k (u - p)) x (cos (k * (x - p))).
Proof.
  intros k p x. unfold cbi_arc_X.
  destruct (Req_EM_T k 0) as [->|Hk].
  - rewrite Rmult_0_l, cos_0.
    replace 1 with (1 - 0) by ring.
    apply (cbi_d_minus id (fun _ => p)); [apply derivable_pt_lim_id|].
    apply derivable_pt_lim_const.
  - apply derivable_pt_lim_ext with
      (f := fun u => / k * comp sin (fun v => k * (v - p)) u).
    + intro u. unfold comp, Rdiv. ring.
    + replace (cos (k * (x - p))) with (/ k * (cos (k * (x - p)) * k))
        by (field; exact Hk).
      apply cbi_d_scal.
      apply derivable_pt_lim_comp; [apply cbi_shift_deriv|].
      apply derivable_pt_lim_sin.
Qed.

Lemma cbi_arc_Y_deriv : forall k p x,
  derivable_pt_lim (fun u => cbi_arc_Y k (u - p)) x (sin (k * (x - p))).
Proof.
  intros k p x. unfold cbi_arc_Y.
  destruct (Req_EM_T k 0) as [->|Hk].
  - rewrite Rmult_0_l, sin_0. apply derivable_pt_lim_const.
  - apply derivable_pt_lim_ext with
      (f := fun u => / k * (1 - comp cos (fun v => k * (v - p)) u)).
    + intro u. unfold comp, Rdiv. ring.
    + replace (sin (k * (x - p)))
        with (/ k * (0 - (- sin (k * (x - p)) * k)))
        by (field; exact Hk).
      apply cbi_d_scal.
      apply (cbi_d_minus (fun _ => 1)); [apply derivable_pt_lim_const|].
      apply derivable_pt_lim_comp; [apply cbi_shift_deriv|].
      apply derivable_pt_lim_cos.
Qed.

(* The tangent of a piece at arc length x - p is its start tangent rotated
   by k (x - p). *)
Lemma cbi_arc_px_deriv : forall Q tx ty k p x,
  derivable_pt_lim (fun u => px (cbi_arc_pt Q tx ty k (u - p))) x
    (cbi_rot_x tx ty (k * (x - p))).
Proof.
  intros Q tx ty k p x. unfold cbi_arc_pt, cbi_rot_x. cbn.
  replace (tx * cos (k * (x - p)) - ty * sin (k * (x - p)))
    with (0 + tx * cos (k * (x - p)) - ty * sin (k * (x - p))) by ring.
  apply cbi_d_minus.
  - apply (cbi_d_plus (fun _ => px Q)); [apply derivable_pt_lim_const|].
    apply cbi_d_scal. apply cbi_arc_X_deriv.
  - apply cbi_d_scal. apply cbi_arc_Y_deriv.
Qed.

Lemma cbi_arc_py_deriv : forall Q tx ty k p x,
  derivable_pt_lim (fun u => py (cbi_arc_pt Q tx ty k (u - p))) x
    (cbi_rot_y tx ty (k * (x - p))).
Proof.
  intros Q tx ty k p x. unfold cbi_arc_pt, cbi_rot_y. cbn.
  replace (ty * cos (k * (x - p)) + tx * sin (k * (x - p)))
    with (0 + ty * cos (k * (x - p)) + tx * sin (k * (x - p))) by ring.
  apply cbi_d_plus.
  - apply (cbi_d_plus (fun _ => py Q)); [apply derivable_pt_lim_const|].
    apply cbi_d_scal. apply cbi_arc_X_deriv.
  - apply cbi_d_scal. apply cbi_arc_Y_deriv.
Qed.

Lemma cbi_rot_compose_x : forall tx ty a b,
  cbi_rot_x (cbi_rot_x tx ty a) (cbi_rot_y tx ty a) b = cbi_rot_x tx ty (a + b).
Proof.
  intros. unfold cbi_rot_x, cbi_rot_y. rewrite cos_plus, sin_plus. ring.
Qed.

Lemma cbi_rot_compose_y : forall tx ty a b,
  cbi_rot_y (cbi_rot_x tx ty a) (cbi_rot_y tx ty a) b = cbi_rot_y tx ty (a + b).
Proof.
  intros. unfold cbi_rot_x, cbi_rot_y. rewrite cos_plus, sin_plus. ring.
Qed.

(* Unit tangents at headings a and b differ by at most |a - b|. *)
Lemma cbi_rot_diff_sq : forall tx ty a b,
  tx * tx + ty * ty = 1 ->
  (cbi_rot_x tx ty a - cbi_rot_x tx ty b) *
  (cbi_rot_x tx ty a - cbi_rot_x tx ty b) +
  (cbi_rot_y tx ty a - cbi_rot_y tx ty b) *
  (cbi_rot_y tx ty a - cbi_rot_y tx ty b) <= (a - b) * (a - b).
Proof.
  intros tx ty a b Hu.
  unfold cbi_rot_x, cbi_rot_y.
  pose proof (sin2_cos2 a) as Ha. pose proof (sin2_cos2 b) as Hb.
  unfold Rsqr in Ha, Hb.
  set (z := (a - b) / 2).
  assert (Hc : cos (a - b) = 1 - 2 * sin z * sin z).
  { rewrite <- cos_2a_sin. unfold z. f_equal. field. }
  rewrite cos_minus in Hc.
  assert (Hs : sin z * sin z <= z * z).
  { pose proof (abs_sin_le z) as Habs.
    pose proof (Rsqr_le_abs_1 _ _ Habs) as Hsq. unfold Rsqr in Hsq. exact Hsq. }
  replace ((tx * cos a - ty * sin a - (tx * cos b - ty * sin b)) *
           (tx * cos a - ty * sin a - (tx * cos b - ty * sin b)) +
           (ty * cos a + tx * sin a - (ty * cos b + tx * sin b)) *
           (ty * cos a + tx * sin a - (ty * cos b + tx * sin b)))
    with ((tx * tx + ty * ty) *
          ((sin a * sin a + cos a * cos a) + (sin b * sin b + cos b * cos b)
           - 2 * (cos a * cos b + sin a * sin b))) by ring.
  rewrite Hu, Ha, Hb, Hc.
  replace ((a - b) * (a - b)) with (4 * (z * z)) by (unfold z; field).
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Vector mean-value inequality, from deriv_nonneg_incr (no MVT, no classic). *)
(* -------------------------------------------------------------------------- *)

Lemma cbi_dot_le_norm : forall wx wy x y,
  wx * wx + wy * wy = 1 ->
  wx * x + wy * y <= sqrt (x * x + y * y).
Proof.
  intros wx wy x y Hw.
  set (z := wx * x + wy * y).
  destruct (Rle_lt_dec z 0) as [Hz|Hz].
  - apply Rle_trans with 0; [exact Hz | apply sqrt_pos].
  - rewrite <- (sqrt_square z) by lra.
    apply sqrt_le_1_alt.
    assert (E : (x * x + y * y) - z * z = (wx * y - wy * x) * (wx * y - wy * x)).
    { unfold z.
      replace (x * x + y * y) with ((wx * wx + wy * wy) * (x * x + y * y))
        by (rewrite Hw; ring).
      ring. }
    pose proof (Rle_0_sqr (wx * y - wy * x)) as H0. unfold Rsqr in H0. lra.
Qed.

Lemma cbi_vec_mvi : forall (fx fy gx gy : R -> R) p q d,
  p <= q -> 0 <= d ->
  (forall t, p <= t <= q -> derivable_pt_lim fx t (gx t)) ->
  (forall t, p <= t <= q -> derivable_pt_lim fy t (gy t)) ->
  (forall t, p <= t <= q -> gx t * gx t + gy t * gy t <= d * d) ->
  sqrt (fx q * fx q + fy q * fy q)
    <= sqrt (fx p * fx p + fy p * fy p) + d * (q - p).
Proof.
  intros fx fy gx gy p q d Hpq Hd Hdx Hdy Hg.
  set (S := fx q * fx q + fy q * fy q).
  assert (HS : 0 <= S) by (unfold S; nra).
  set (Nq := sqrt S).
  destruct (Req_EM_T Nq 0) as [Hz|Hnz].
  - rewrite Hz. pose proof (sqrt_pos (fx p * fx p + fy p * fy p)). nra.
  - assert (HN0 : 0 <= Nq) by apply sqrt_pos.
    assert (HN : 0 < Nq) by lra.
    assert (HNN : Nq * Nq = S) by (unfold Nq; apply sqrt_sqrt; exact HS).
    set (wx := fx q / Nq). set (wy := fy q / Nq).
    assert (Hw : wx * wx + wy * wy = 1).
    { unfold wx, wy.
      replace (fx q / Nq * (fx q / Nq) + fy q / Nq * (fy q / Nq))
        with (S / (Nq * Nq)) by (unfold S; field; exact Hnz).
      rewrite HNN. unfold Rdiv. apply Rinv_r.
      rewrite <- HNN. apply Rgt_not_eq. nra. }
    set (g := fun t => d * t - (wx * fx t + wy * fy t)).
    set (g' := fun t => d - (wx * gx t + wy * gy t)).
    assert (Hgd : forall t, p <= t <= q -> derivable_pt_lim g t (g' t)).
    { intros t Ht. unfold g, g'.
      replace (d - (wx * gx t + wy * gy t))
        with (d * 1 - (wx * gx t + wy * gy t)) by ring.
      apply (cbi_d_minus (fun t => d * t)).
      - apply cbi_d_scal. apply derivable_pt_lim_id.
      - apply (cbi_d_plus (fun t => wx * fx t) (fun t => wy * fy t));
          apply cbi_d_scal.
        + apply Hdx. exact Ht.
        + apply Hdy. exact Ht. }
    assert (Hgn : forall t, p <= t <= q -> 0 <= g' t).
    { intros t Ht. unfold g'.
      pose proof (cbi_dot_le_norm wx wy (gx t) (gy t) Hw) as Hc.
      assert (Hsq : sqrt (gx t * gx t + gy t * gy t) <= d).
      { rewrite <- (sqrt_square d) by exact Hd.
        apply sqrt_le_1_alt. apply Hg. exact Ht. }
      lra. }
    pose proof (deriv_nonneg_incr g g' p q p q Hgd Hgn
                  (Rle_refl p) Hpq (Rle_refl q)) as Hinc.
    unfold g in Hinc.
    assert (Hq : wx * fx q + wy * fy q = Nq).
    { unfold wx, wy.
      replace (fx q / Nq * fx q + fy q / Nq * fy q) with (S / Nq)
        by (unfold S; field; exact Hnz).
      rewrite <- HNN. field. exact Hnz. }
    pose proof (cbi_dot_le_norm wx wy (fx p) (fy p) Hw) as Hp.
    fold S Nq. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Clothoid heading against a linear interpolant.                             *)
(* -------------------------------------------------------------------------- *)

(* Clothoid curvature at the midpoint of [x, x + h]. *)
Definition cbi_kap (c : ClothoidEgg) (x h : R) : R :=
  cloth_sigma c * (x + h / 2) / (cloth_A c * cloth_A c).

(* Heading tolerance of one piece of length h. *)
Definition cbi_delta (c : ClothoidEgg) (h : R) : R :=
  h * h / (8 * (cloth_A c * cloth_A c)).

Lemma cbi_sigma_sq : forall c, cloth_sigma c * cloth_sigma c = 1.
Proof. intro c. unfold cloth_sigma. destruct (Rle_dec 0 (cloth_cross c)); ring. Qed.

Lemma cbi_delta_nonneg : forall c h, cloth_A c <> 0 -> 0 <= cbi_delta c h.
Proof.
  intros c h HA. unfold cbi_delta.
  assert (0 < cloth_A c * cloth_A c) by (apply Rsqr_pos_lt; exact HA).
  apply Rmult_le_pos; [nra|]. apply Rlt_le, Rinv_0_lt_compat. lra.
Qed.

(* The interpolant hits the clothoid heading at the far node. *)
Lemma cbi_psi_node : forall c x h, cloth_A c <> 0 ->
  cloth_psi c x + cbi_kap c x h * h = cloth_psi c (x + h).
Proof.
  intros c x h HA. unfold cloth_psi, cbi_kap. field. exact HA.
Qed.

Lemma cbi_heading_err : forall c x h u, cloth_A c <> 0 ->
  cloth_psi c u - (cloth_psi c x + cbi_kap c x h * (u - x)) =
  cloth_sigma c * ((u - x) * (u - x - h)) / (2 * (cloth_A c * cloth_A c)).
Proof.
  intros c x h u HA. unfold cloth_psi, cbi_kap. field. exact HA.
Qed.

Lemma cbi_heading_err_sq : forall c x h u, cloth_A c <> 0 ->
  0 <= h -> x <= u <= x + h ->
  (cloth_psi c u - (cloth_psi c x + cbi_kap c x h * (u - x))) *
  (cloth_psi c u - (cloth_psi c x + cbi_kap c x h * (u - x)))
    <= cbi_delta c h * cbi_delta c h.
Proof.
  intros c x h u HA Hh Hu.
  rewrite (cbi_heading_err c x h u HA).
  set (w := (u - x) * (u - x - h)).
  set (AA := cloth_A c * cloth_A c).
  assert (HAA : 0 < AA) by (unfold AA; apply Rsqr_pos_lt; exact HA).
  assert (Hw : w * w <= (h * h / 4) * (h * h / 4)).
  { assert (H1 : 0 <= - w) by (unfold w; nra).
    assert (H2 : - w <= h * h / 4).
    { pose proof (Rle_0_sqr (u - x - h / 2)) as Hq. unfold Rsqr in Hq.
      unfold w. nra. }
    nra. }
  pose proof (cbi_sigma_sq c) as Hs.
  replace (cloth_sigma c * w / (2 * AA) * (cloth_sigma c * w / (2 * AA)))
    with ((cloth_sigma c * cloth_sigma c) * (w * w) / (4 * (AA * AA)))
    by (field; lra).
  rewrite Hs. unfold cbi_delta. fold AA.
  replace (h * h / (8 * AA) * (h * h / (8 * AA)))
    with ((h * h / 4) * (h * h / 4) / (4 * (AA * AA))) by (field; lra).
  apply Rmult_le_compat_r; [|lra].
  apply Rlt_le, Rinv_0_lt_compat. nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* The arc spline.                                                            *)
(* -------------------------------------------------------------------------- *)

Definition cbi_node (a h : R) (k : nat) : R := a + INR k * h.

Lemma cbi_node_S : forall a h k, cbi_node a h (S k) = cbi_node a h k + h.
Proof. intros. unfold cbi_node. rewrite S_INR. ring. Qed.

Lemma cbi_node_0 : forall a h, cbi_node a h 0 = a.
Proof. intros. unfold cbi_node. cbn. ring. Qed.

(* Start point of piece k: the clothoid point P(a) for k = 0, else the end
   of piece k - 1. *)
Fixpoint cbi_start (c : ClothoidEgg) (a h : R) (k : nat) : Point :=
  match k with
  | O => cloth_P c a
  | S j =>
      cbi_arc_pt (cbi_start c a h j)
        (cloth_vx c (cbi_node a h j)) (cloth_vy c (cbi_node a h j))
        (cbi_kap c (cbi_node a h j) h) h
  end.

(* Piece k, evaluated at station u in [x_k, x_k + h]. *)
Definition cbi_piece (c : ClothoidEgg) (a h : R) (k : nat) (u : R) : Point :=
  cbi_arc_pt (cbi_start c a h k)
    (cloth_vx c (cbi_node a h k)) (cloth_vy c (cbi_node a h k))
    (cbi_kap c (cbi_node a h k) h) (u - cbi_node a h k).

Lemma cbi_piece_end : forall c a h k,
  cbi_piece c a h k (cbi_node a h (S k)) = cbi_start c a h (S k).
Proof.
  intros. unfold cbi_piece. cbn [cbi_start]. f_equal.
  rewrite cbi_node_S. ring.
Qed.

(* Position continuity: piece k ends where piece k + 1 starts. *)
Lemma cbi_spline_c0 : forall c a h k,
  cbi_piece c a h k (cbi_node a h (S k)) =
  cbi_piece c a h (S k) (cbi_node a h (S k)).
Proof.
  intros. rewrite cbi_piece_end. unfold cbi_piece.
  rewrite Rminus_diag. rewrite cbi_arc_pt_0. reflexivity.
Qed.

Lemma cbi_spline_start : forall c a h, cbi_piece c a h 0 a = cloth_P c a.
Proof.
  intros. unfold cbi_piece. rewrite cbi_node_0, Rminus_diag, cbi_arc_pt_0.
  reflexivity.
Qed.

Lemma cbi_vx_rot : forall c s, cloth_vx c s =
  cbi_rot_x (cloth_cos0 c) (cloth_sin0 c) (cloth_psi c s).
Proof. reflexivity. Qed.

Lemma cbi_vy_rot : forall c s, cloth_vy c s =
  cbi_rot_y (cloth_cos0 c) (cloth_sin0 c) (cloth_psi c s).
Proof. reflexivity. Qed.

(* Tangent of piece k at station u. *)
Lemma cbi_piece_tangent : forall c a h k u,
  derivable_pt_lim (fun v => px (cbi_piece c a h k v)) u
    (cbi_rot_x (cloth_cos0 c) (cloth_sin0 c)
       (cloth_psi c (cbi_node a h k)
        + cbi_kap c (cbi_node a h k) h * (u - cbi_node a h k))) /\
  derivable_pt_lim (fun v => py (cbi_piece c a h k v)) u
    (cbi_rot_y (cloth_cos0 c) (cloth_sin0 c)
       (cloth_psi c (cbi_node a h k)
        + cbi_kap c (cbi_node a h k) h * (u - cbi_node a h k))).
Proof.
  intros. unfold cbi_piece. split.
  - rewrite <- cbi_rot_compose_x, <- cbi_vx_rot, <- cbi_vy_rot.
    apply cbi_arc_px_deriv.
  - rewrite <- cbi_rot_compose_y, <- cbi_vx_rot, <- cbi_vy_rot.
    apply cbi_arc_py_deriv.
Qed.

(* G1: the tangent of piece k at its far node is the clothoid tangent there,
   which is the start tangent of piece k + 1. *)
Theorem cbi_spline_g1 : forall c a h k, cloth_A c <> 0 ->
  cbi_rot_x (cloth_vx c (cbi_node a h k)) (cloth_vy c (cbi_node a h k))
    (cbi_kap c (cbi_node a h k) h * h) = cloth_vx c (cbi_node a h (S k)) /\
  cbi_rot_y (cloth_vx c (cbi_node a h k)) (cloth_vy c (cbi_node a h k))
    (cbi_kap c (cbi_node a h k) h * h) = cloth_vy c (cbi_node a h (S k)).
Proof.
  intros c a h k HA.
  rewrite cbi_vx_rot, cbi_vy_rot, cbi_rot_compose_x, cbi_rot_compose_y.
  rewrite cbi_psi_node by exact HA. rewrite <- cbi_node_S.
  split; reflexivity.
Qed.

(* One piece: error = inherited start offset + delta * arc length so far. *)
Lemma cbi_piece_err : forall c a h k u, cloth_wf c -> 0 <= h ->
  cbi_node a h k <= u <= cbi_node a h k + h ->
  dist (cloth_P c u) (cbi_piece c a h k u)
    <= dist (cloth_P c (cbi_node a h k)) (cbi_start c a h k)
       + cbi_delta c h * (u - cbi_node a h k).
Proof.
  intros c a h k u Hwf Hh Hu.
  destruct Hwf as [HA [Hh2 _]].
  assert (HA0 : cloth_A c <> 0) by lra.
  set (x := cbi_node a h k).
  fold x in Hu.
  set (fx := fun v => cloth_Px c v - px (cbi_piece c a h k v)).
  set (fy := fun v => cloth_Py c v - py (cbi_piece c a h k v)).
  set (bet := fun v => cloth_psi c x + cbi_kap c x h * (v - x)).
  set (gx := fun v => cloth_vx c v
               - cbi_rot_x (cloth_cos0 c) (cloth_sin0 c) (bet v)).
  set (gy := fun v => cloth_vy c v
               - cbi_rot_y (cloth_cos0 c) (cloth_sin0 c) (bet v)).
  assert (Hpx : forall v, x <= v <= u -> derivable_pt_lim fx v (gx v)).
  { intros v _. unfold fx, gx, bet.
    apply cbi_d_minus; [apply cloth_Px_deriv|].
    apply (cbi_piece_tangent c a h k v). }
  assert (Hpy : forall v, x <= v <= u -> derivable_pt_lim fy v (gy v)).
  { intros v _. unfold fy, gy, bet.
    apply cbi_d_minus; [apply cloth_Py_deriv|].
    apply (cbi_piece_tangent c a h k v). }
  assert (Hg : forall v, x <= v <= u ->
            gx v * gx v + gy v * gy v <= cbi_delta c h * cbi_delta c h).
  { intros v Hv. unfold gx, gy.
    rewrite cbi_vx_rot, cbi_vy_rot.
    eapply Rle_trans.
    - apply cbi_rot_diff_sq. apply cloth_frame_sumsq. exact Hh2.
    - unfold bet. apply cbi_heading_err_sq; [exact HA0 | exact Hh | lra]. }
  pose proof (cbi_vec_mvi fx fy gx gy x u (cbi_delta c h) (proj1 Hu)
                (cbi_delta_nonneg c h HA0) Hpx Hpy Hg) as H.
  unfold dist, dist_sq. cbn [px py cloth_P]. unfold fx, fy in H.
  replace (cbi_piece c a h k x) with (cbi_start c a h k) in H.
  - exact H.
  - unfold cbi_piece. fold x. rewrite Rminus_diag, cbi_arc_pt_0. reflexivity.
Qed.

(* Node offsets accumulate linearly: no heading drift at the nodes. *)
Lemma cbi_start_err : forall c a h k, cloth_wf c -> 0 <= h ->
  dist (cloth_P c (cbi_node a h k)) (cbi_start c a h k)
    <= cbi_delta c h * (INR k * h).
Proof.
  intros c a h k Hwf Hh. induction k as [|k IH].
  - rewrite cbi_node_0. cbn [cbi_start INR].
    rewrite dist_refl. right. ring.
  - rewrite <- cbi_piece_end.
    eapply Rle_trans.
    + apply cbi_piece_err; [exact Hwf | exact Hh |].
      rewrite cbi_node_S. lra.
    + rewrite cbi_node_S, S_INR.
      replace (cbi_node a h k + h - cbi_node a h k) with h by ring.
      lra.
Qed.

Theorem cbi_spline_err : forall c a h k u, cloth_wf c -> 0 <= h ->
  cbi_node a h k <= u <= cbi_node a h (S k) ->
  dist (cloth_P c u) (cbi_piece c a h k u) <= cbi_delta c h * (u - a).
Proof.
  intros c a h k u Hwf Hh Hu.
  rewrite cbi_node_S in Hu.
  eapply Rle_trans; [apply cbi_piece_err; assumption|].
  pose proof (cbi_start_err c a h k Hwf Hh) as Hs.
  replace (u - a) with (INR k * h + (u - cbi_node a h k))
    by (unfold cbi_node; ring).
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Window form and the ε contract.                                            *)
(* -------------------------------------------------------------------------- *)

Definition cbi_step (a b : R) (N : nat) : R := (b - a) / INR N.

Lemma cbi_node_N : forall a b N, (N <> 0)%nat ->
  cbi_node a (cbi_step a b N) N = b.
Proof.
  intros a b N HN. unfold cbi_node, cbi_step. field. apply not_0_INR. exact HN.
Qed.

(* Every station of the window lies in some piece. *)
Lemma cbi_slot : forall a b N u, a < b -> (2 <= N)%nat -> a <= u <= b ->
  exists k, (k < N)%nat /\
    cbi_node a (cbi_step a b N) k <= u <= cbi_node a (cbi_step a b N) (S k).
Proof.
  intros a b N u Hab HN Hu.
  set (t := (u - a) / (b - a)).
  assert (Ht : 0 <= t <= 1).
  { unfold t. split.
    - apply Rmult_le_pos; [lra|]. apply Rlt_le, Rinv_0_lt_compat. lra.
    - apply Rmult_le_reg_r with (b - a); [lra|].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
  destruct (param_slot N t HN Ht) as [k [Hk Hkt]].
  exists k. split; [exact Hk|].
  assert (Hnode : forall j, cbi_node a (cbi_step a b N) j
                            = a + (b - a) * cloth_ts N j).
  { intro j. unfold cbi_node, cbi_step, cloth_ts. field.
    apply not_0_INR. lia. }
  rewrite !Hnode.
  assert (Hu' : u = a + (b - a) * t) by (unfold t; field; lra).
  rewrite Hu'. nra.
Qed.

(* The N-arc spline on [a, b], in both Hausdorff directions at equal arc
   length: every piece point is near the clothoid and every clothoid point
   is near a piece. *)
Theorem cbi_arc_spline_within : forall c a b N, cloth_wf c -> a <= b ->
  (N <> 0)%nat ->
  (forall k u, (k < N)%nat ->
     cbi_node a (cbi_step a b N) k <= u <= cbi_node a (cbi_step a b N) (S k) ->
     dist (cloth_P c u) (cbi_piece c a (cbi_step a b N) k u)
       <= (b - a) * (b - a) * (b - a)
          / (8 * (cloth_A c * cloth_A c) * (INR N * INR N))).
Proof.
  intros c a b N Hwf Hab HN k u Hk Hu.
  assert (HNp : 0 < INR N) by (apply lt_0_INR; lia).
  set (h := cbi_step a b N).
  assert (Hh : 0 <= h).
  { unfold h, cbi_step. apply Rmult_le_pos; [lra|].
    apply Rlt_le, Rinv_0_lt_compat. exact HNp. }
  eapply Rle_trans; [apply cbi_spline_err; [exact Hwf | exact Hh | exact Hu]|].
  assert (Hub : u <= b).
  { apply Rle_trans with (cbi_node a h (S k)); [exact (proj2 Hu)|].
    rewrite <- (cbi_node_N a b N HN). fold h. unfold cbi_node.
    apply Rplus_le_compat_l, Rmult_le_compat_r; [exact Hh|].
    apply le_INR. lia. }
  assert (Hua : a <= u).
  { apply Rle_trans with (cbi_node a h k); [|exact (proj1 Hu)].
    unfold cbi_node. pose proof (pos_INR k). nra. }
  destruct Hwf as [HA _].
  assert (HAA : 0 < cloth_A c * cloth_A c) by nra.
  pose proof (cbi_delta_nonneg c h ltac:(lra)) as Hd.
  apply Rle_trans with (cbi_delta c h * (b - a)); [nra|].
  right. unfold cbi_delta, h, cbi_step. field. lra.
Qed.

(* The ε contract for the N-arc spline. *)
Theorem cbi_arc_spline_within_eps : forall c a b N eps,
  cloth_wf c -> a <= b -> (N <> 0)%nat ->
  (b - a) * (b - a) * (b - a)
    <= 8 * (cloth_A c * cloth_A c) * (INR N * INR N) * eps ->
  forall k u, (k < N)%nat ->
    cbi_node a (cbi_step a b N) k <= u <= cbi_node a (cbi_step a b N) (S k) ->
    dist (cloth_P c u) (cbi_piece c a (cbi_step a b N) k u) <= eps.
Proof.
  intros c a b N eps Hwf Hab HN Hgate k u Hk Hu.
  eapply Rle_trans; [apply cbi_arc_spline_within; eassumption|].
  destruct Hwf as [HA _].
  assert (HNp : 0 < INR N) by (apply lt_0_INR; lia).
  assert (Hden : 0 < 8 * (cloth_A c * cloth_A c) * (INR N * INR N)).
  { apply Rmult_lt_0_compat; [nra | nra]. }
  apply Rmult_le_reg_r with (8 * (cloth_A c * cloth_A c) * (INR N * INR N));
    [exact Hden|].
  unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra.
Qed.

(* WITNESS {"claimId":"0007-clothoid-biarc","topic":"curves","lemma":"cbi_biarc_within_eps","title":"Biarc approximation of a host clothoid window [a, b]: two G1-joined circular arcs from P(a) with the clothoid tangents at a, (a+b)/2, b and the midpoint curvatures; every point within (b-a)^3/(32 A^2) at equal arc length, so (b-a)^3 <= 32 A^2 eps is a contract","file":"theories/ClothoidBiarc.v","witness":"cbi_biarc_within_eps","board":"ADR-0007"} *)
Theorem cbi_biarc_within_eps : forall c a b eps,
  cloth_wf c -> a <= b ->
  (b - a) * (b - a) * (b - a) <= 32 * (cloth_A c * cloth_A c) * eps ->
  (* every biarc point is within eps of the clothoid point at its station *)
  (forall k u, (k < 2)%nat ->
     cbi_node a (cbi_step a b 2) k <= u <= cbi_node a (cbi_step a b 2) (S k) ->
     dist (cloth_P c u) (cbi_piece c a (cbi_step a b 2) k u) <= eps) /\
  (* every clothoid point of the window is within eps of a biarc point *)
  (forall u, a <= u <= b -> exists k, (k < 2)%nat /\
     dist (cloth_P c u) (cbi_piece c a (cbi_step a b 2) k u) <= eps) /\
  (* G1 at the junction and at b: node tangents are the clothoid tangents *)
  (forall k, (k < 2)%nat ->
     cbi_rot_x (cloth_vx c (cbi_node a (cbi_step a b 2) k))
               (cloth_vy c (cbi_node a (cbi_step a b 2) k))
       (cbi_kap c (cbi_node a (cbi_step a b 2) k) (cbi_step a b 2)
        * cbi_step a b 2)
       = cloth_vx c (cbi_node a (cbi_step a b 2) (S k)) /\
     cbi_rot_y (cloth_vx c (cbi_node a (cbi_step a b 2) k))
               (cloth_vy c (cbi_node a (cbi_step a b 2) k))
       (cbi_kap c (cbi_node a (cbi_step a b 2) k) (cbi_step a b 2)
        * cbi_step a b 2)
       = cloth_vy c (cbi_node a (cbi_step a b 2) (S k))) /\
  (* the biarc starts at P(a) and is continuous at the junction *)
  cbi_piece c a (cbi_step a b 2) 0 a = cloth_P c a /\
  cbi_piece c a (cbi_step a b 2) 0 (cbi_node a (cbi_step a b 2) 1) =
  cbi_piece c a (cbi_step a b 2) 1 (cbi_node a (cbi_step a b 2) 1).
Proof.
  intros c a b eps Hwf Hab Hgate.
  assert (H2 : (2 <> 0)%nat) by lia.
  assert (Hgate2 : (b - a) * (b - a) * (b - a)
            <= 8 * (cloth_A c * cloth_A c) * (INR 2 * INR 2) * eps).
  { replace (INR 2) with 2 by (cbn; ring). lra. }
  pose proof (cbi_arc_spline_within_eps c a b 2 eps Hwf Hab H2 Hgate2) as Hin.
  split; [exact Hin|]. split; [|split; [|split]].
  - intros u Hu.
    destruct (Rle_lt_dec b a) as [Hba|Hlt].
    + exists 0%nat. split; [lia|]. apply Hin; [lia|].
      rewrite cbi_node_S, cbi_node_0. unfold cbi_step.
      assert (u = a) by lra. assert (b = a) by lra. subst. lra.
    + destruct (cbi_slot a b 2 u Hlt (le_n 2) Hu) as [k [Hk Hku]].
      exists k. split; [exact Hk|]. apply Hin; assumption.
  - intros k _. apply cbi_spline_g1. destruct Hwf as [HA _]. lra.
  - apply cbi_spline_start.
  - apply cbi_spline_c0.
Qed.

Print Assumptions cbi_arc_on_circle.
Print Assumptions cbi_vec_mvi.
Print Assumptions cbi_spline_g1.
Print Assumptions cbi_spline_err.
Print Assumptions cbi_arc_spline_within.
Print Assumptions cbi_arc_spline_within_eps.
Print Assumptions cbi_biarc_within_eps.
