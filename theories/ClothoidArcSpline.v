(* ============================================================================
   NetTopologySuite.Proofs.ClothoidArcSpline
   ----------------------------------------------------------------------------
   Heading-interpolating arc spline of a host clothoid window, with a
   machine-checked tolerance.  The arc analogue of the chord contract
   `ClothoidLinearizeContract.v : clothoid_linearizes` (tol kappa_max h^2/8).

   Construction.  On the station window [a, b], cut N equal pieces of length
   h = (b - a) / N at nodes x_k = a + k h.  Piece k is the unit-speed
   circular arc (a straight segment when its curvature is 0) that
     - starts where piece k-1 ends (piece 0 starts at the clothoid point
       P(a)),
     - starts with the clothoid tangent T(x_k),
     - has the clothoid curvature at the piece midpoint,
       kappa_k = sigma (x_k + h/2) / A^2.
   Its heading is the linear interpolant of the clothoid heading psi at the
   nodes: pieces join C0 and G1 and every node TANGENT is the clothoid
   tangent (`cas_spline_g1`).  Node POSITIONS are not interpolated: the
   spline is shot forward from P(a), the heading error keeps one sign on
   every piece, and the end of the spline misses P(b) by up to
   (b - a) h^2 / (8 A^2) (`cas_end_gap`).  N = 2 is a two-arc spline, not
   the endpoint-interpolating (Hermite) biarc; windows chained end to end
   inherit that gap at their boundaries.

   Contract.
     |P(u) - spline(u)| <= (u - a) h^2 / (8 A^2) <= (b - a)^3 / (8 A^2 N^2)
   at equal arc length: piece -> clothoid (`cas_arc_spline_within_eps`)
   and clothoid -> piece (`cas_arc_spline_cover`), for every N >= 1.  The
   bound depends on A only (kappa' = 1/A^2 is constant), not on the station
   or the curvature size.  The gate `(b - a)^3 <= 8 A^2 N^2 eps` is a
   contract; its binary64 evaluation is
   `theories-flocq/ClothoidArcSpline_b64.v`.  The sup-norm step loses a
   factor 3/2 against integrating |psi - beta| (12 instead of 8).

   Proof.  The heading error of piece k is
     psi(u) - beta_k(u) = sigma (u - x_k)(u - x_{k+1}) / (2 A^2),
   at most h^2 / (8 A^2).  Unit tangents at heading distance d differ by at
   most |d|.  The vector mean-value inequality `VecMVI.vec_mvi` (from
   RealMonotone.deriv_nonneg_incr: no MVT, no classic) adds the piece's
   contribution to the start offset it inherits.  The tangent of the
   clothoid is ClothoidTangent.cloth_Px_deriv / cloth_Py_deriv (LipInt FTC).

   claimId: 0007-clothoid-arc-spline.  witness: cas_two_arc_within_eps.
   3-axiom host. No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia.
From Stdlib Require Import Ranalysis1.
From NTS.Proofs Require Import Distance LipInt SheetHenClothoidCore
  ClothoidTangent DerivAlgebra VecMVI ClothoidLinearize ClothoidLinearizeContract.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Circular arcs.                                                             *)
(* -------------------------------------------------------------------------- *)

(* Rotation of the unit vector (tx, ty) by theta. *)
Definition cas_rot_x (tx ty th : R) : R := tx * cos th - ty * sin th.
Definition cas_rot_y (tx ty th : R) : R := ty * cos th + tx * sin th.

(* Local coordinates of the unit-speed arc of curvature k after arc
   length x, in the frame (tangent, left normal).  k = 0 is the segment. *)
Definition cas_arc_X (k x : R) : R :=
  if Req_EM_T k 0 then x else sin (k * x) / k.
Definition cas_arc_Y (k x : R) : R :=
  if Req_EM_T k 0 then 0 else (1 - cos (k * x)) / k.

(* The arc from Q with unit tangent (tx, ty) and curvature k, at arc
   length x. *)
Definition cas_arc_pt (Q : Point) (tx ty k x : R) : Point :=
  mkPoint (px Q + tx * cas_arc_X k x - ty * cas_arc_Y k x)
          (py Q + ty * cas_arc_X k x + tx * cas_arc_Y k x).

Lemma cas_arc_pt_0 : forall Q tx ty k, cas_arc_pt Q tx ty k 0 = Q.
Proof.
  intros Q tx ty k. destruct Q as [qx qy].
  unfold cas_arc_pt, cas_arc_X, cas_arc_Y. cbn.
  destruct (Req_EM_T k 0) as [_|Hk].
  - f_equal; ring.
  - rewrite Rmult_0_r, sin_0, cos_0. f_equal; field; exact Hk.
Qed.

(* A piece with k <> 0 lies on the circle of radius 1/|k| centred at
   Q + (-ty, tx)/k: it is a circular arc. *)
Lemma cas_arc_on_circle : forall Q tx ty k x,
  k <> 0 -> tx * tx + ty * ty = 1 ->
  dist_sq (cas_arc_pt Q tx ty k x)
          (mkPoint (px Q - ty / k) (py Q + tx / k)) = / (k * k).
Proof.
  intros Q tx ty k x Hk Hu.
  unfold dist_sq, cas_arc_pt, cas_arc_X, cas_arc_Y. cbn.
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
Lemma cas_arc_segment : forall Q tx ty x,
  cas_arc_pt Q tx ty 0 x = mkPoint (px Q + tx * x) (py Q + ty * x).
Proof.
  intros. unfold cas_arc_pt, cas_arc_X, cas_arc_Y.
  destruct (Req_EM_T 0 0) as [_|H]; [|exfalso; apply H; reflexivity].
  f_equal; ring.
Qed.

Lemma cas_shift_deriv : forall k p x,
  derivable_pt_lim (fun u => k * (u - p)) x k.
Proof.
  intros k p x.
  assert (H : derivable_pt_lim (fun u => k * (u - p)) x (k * (1 - 0))).
  { apply (d_scal k (fun u => u - p)).
    apply (d_minus id (fun _ => p)); [apply derivable_pt_lim_id|].
    apply derivable_pt_lim_const. }
  replace (k * (1 - 0)) with k in H by ring. exact H.
Qed.

Lemma cas_arc_X_deriv : forall k p x,
  derivable_pt_lim (fun u => cas_arc_X k (u - p)) x (cos (k * (x - p))).
Proof.
  intros k p x. unfold cas_arc_X.
  destruct (Req_EM_T k 0) as [->|Hk].
  - rewrite Rmult_0_l, cos_0.
    replace 1 with (1 - 0) by ring.
    apply (d_minus id (fun _ => p)); [apply derivable_pt_lim_id|].
    apply derivable_pt_lim_const.
  - apply derivable_pt_lim_ext with
      (f := fun u => / k * comp sin (fun v => k * (v - p)) u).
    + intro u. unfold comp, Rdiv. ring.
    + replace (cos (k * (x - p))) with (/ k * (cos (k * (x - p)) * k))
        by (field; exact Hk).
      apply d_scal.
      apply derivable_pt_lim_comp; [apply cas_shift_deriv|].
      apply derivable_pt_lim_sin.
Qed.

Lemma cas_arc_Y_deriv : forall k p x,
  derivable_pt_lim (fun u => cas_arc_Y k (u - p)) x (sin (k * (x - p))).
Proof.
  intros k p x. unfold cas_arc_Y.
  destruct (Req_EM_T k 0) as [->|Hk].
  - rewrite Rmult_0_l, sin_0. apply derivable_pt_lim_const.
  - apply derivable_pt_lim_ext with
      (f := fun u => / k * (1 - comp cos (fun v => k * (v - p)) u)).
    + intro u. unfold comp, Rdiv. ring.
    + replace (sin (k * (x - p)))
        with (/ k * (0 - (- sin (k * (x - p)) * k)))
        by (field; exact Hk).
      apply d_scal.
      apply (d_minus (fun _ => 1)); [apply derivable_pt_lim_const|].
      apply derivable_pt_lim_comp; [apply cas_shift_deriv|].
      apply derivable_pt_lim_cos.
Qed.

(* The tangent of a piece at arc length x - p is its start tangent rotated
   by k (x - p). *)
Lemma cas_arc_px_deriv : forall Q tx ty k p x,
  derivable_pt_lim (fun u => px (cas_arc_pt Q tx ty k (u - p))) x
    (cas_rot_x tx ty (k * (x - p))).
Proof.
  intros Q tx ty k p x. unfold cas_arc_pt, cas_rot_x. cbn.
  replace (tx * cos (k * (x - p)) - ty * sin (k * (x - p)))
    with (0 + tx * cos (k * (x - p)) - ty * sin (k * (x - p))) by ring.
  apply d_minus.
  - apply (d_plus (fun _ => px Q)); [apply derivable_pt_lim_const|].
    apply d_scal. apply cas_arc_X_deriv.
  - apply d_scal. apply cas_arc_Y_deriv.
Qed.

Lemma cas_arc_py_deriv : forall Q tx ty k p x,
  derivable_pt_lim (fun u => py (cas_arc_pt Q tx ty k (u - p))) x
    (cas_rot_y tx ty (k * (x - p))).
Proof.
  intros Q tx ty k p x. unfold cas_arc_pt, cas_rot_y. cbn.
  replace (ty * cos (k * (x - p)) + tx * sin (k * (x - p)))
    with (0 + ty * cos (k * (x - p)) + tx * sin (k * (x - p))) by ring.
  apply d_plus.
  - apply (d_plus (fun _ => py Q)); [apply derivable_pt_lim_const|].
    apply d_scal. apply cas_arc_X_deriv.
  - apply d_scal. apply cas_arc_Y_deriv.
Qed.

Lemma cas_rot_compose_x : forall tx ty a b,
  cas_rot_x (cas_rot_x tx ty a) (cas_rot_y tx ty a) b = cas_rot_x tx ty (a + b).
Proof.
  intros. unfold cas_rot_x, cas_rot_y. rewrite cos_plus, sin_plus. ring.
Qed.

Lemma cas_rot_compose_y : forall tx ty a b,
  cas_rot_y (cas_rot_x tx ty a) (cas_rot_y tx ty a) b = cas_rot_y tx ty (a + b).
Proof.
  intros. unfold cas_rot_x, cas_rot_y. rewrite cos_plus, sin_plus. ring.
Qed.

(* Unit tangents at headings a and b differ by at most |a - b|. *)
Lemma cas_rot_diff_sq : forall tx ty a b,
  tx * tx + ty * ty = 1 ->
  (cas_rot_x tx ty a - cas_rot_x tx ty b) *
  (cas_rot_x tx ty a - cas_rot_x tx ty b) +
  (cas_rot_y tx ty a - cas_rot_y tx ty b) *
  (cas_rot_y tx ty a - cas_rot_y tx ty b) <= (a - b) * (a - b).
Proof.
  intros tx ty a b Hu.
  unfold cas_rot_x, cas_rot_y.
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
(* Clothoid heading against a linear interpolant.                             *)
(* -------------------------------------------------------------------------- *)

(* Clothoid curvature at the midpoint of [x, x + h]. *)
Definition cas_kap (c : ClothoidEgg) (x h : R) : R :=
  cloth_sigma c * (x + h / 2) / (cloth_A c * cloth_A c).

(* Heading tolerance of one piece of length h. *)
Definition cas_delta (c : ClothoidEgg) (h : R) : R :=
  h * h / (8 * (cloth_A c * cloth_A c)).

Lemma cas_sigma_sq : forall c, cloth_sigma c * cloth_sigma c = 1.
Proof. intro c. unfold cloth_sigma. destruct (Rle_dec 0 (cloth_cross c)); ring. Qed.

Lemma cas_delta_nonneg : forall c h, cloth_A c <> 0 -> 0 <= cas_delta c h.
Proof.
  intros c h HA. unfold cas_delta.
  assert (0 < cloth_A c * cloth_A c) by (apply Rsqr_pos_lt; exact HA).
  apply Rmult_le_pos; [nra|]. apply Rlt_le, Rinv_0_lt_compat. lra.
Qed.

(* The interpolant hits the clothoid heading at the far node. *)
Lemma cas_psi_node : forall c x h, cloth_A c <> 0 ->
  cloth_psi c x + cas_kap c x h * h = cloth_psi c (x + h).
Proof.
  intros c x h HA. unfold cloth_psi, cas_kap. field. exact HA.
Qed.

Lemma cas_heading_err : forall c x h u, cloth_A c <> 0 ->
  cloth_psi c u - (cloth_psi c x + cas_kap c x h * (u - x)) =
  cloth_sigma c * ((u - x) * (u - x - h)) / (2 * (cloth_A c * cloth_A c)).
Proof.
  intros c x h u HA. unfold cloth_psi, cas_kap. field. exact HA.
Qed.

Lemma cas_heading_err_sq : forall c x h u, cloth_A c <> 0 ->
  0 <= h -> x <= u <= x + h ->
  (cloth_psi c u - (cloth_psi c x + cas_kap c x h * (u - x))) *
  (cloth_psi c u - (cloth_psi c x + cas_kap c x h * (u - x)))
    <= cas_delta c h * cas_delta c h.
Proof.
  intros c x h u HA Hh Hu.
  rewrite (cas_heading_err c x h u HA).
  set (w := (u - x) * (u - x - h)).
  set (AA := cloth_A c * cloth_A c).
  assert (HAA : 0 < AA) by (unfold AA; apply Rsqr_pos_lt; exact HA).
  assert (Hw : w * w <= (h * h / 4) * (h * h / 4)).
  { assert (H1 : 0 <= - w) by (unfold w; nra).
    assert (H2 : - w <= h * h / 4).
    { pose proof (Rle_0_sqr (u - x - h / 2)) as Hq. unfold Rsqr in Hq.
      unfold w. nra. }
    nra. }
  pose proof (cas_sigma_sq c) as Hs.
  replace (cloth_sigma c * w / (2 * AA) * (cloth_sigma c * w / (2 * AA)))
    with ((cloth_sigma c * cloth_sigma c) * (w * w) / (4 * (AA * AA)))
    by (field; lra).
  rewrite Hs. unfold cas_delta. fold AA.
  replace (h * h / (8 * AA) * (h * h / (8 * AA)))
    with ((h * h / 4) * (h * h / 4) / (4 * (AA * AA))) by (field; lra).
  apply Rmult_le_compat_r; [|lra].
  apply Rlt_le, Rinv_0_lt_compat. nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* The arc spline.                                                            *)
(* -------------------------------------------------------------------------- *)

Definition cas_node (a h : R) (k : nat) : R := a + INR k * h.

Lemma cas_node_S : forall a h k, cas_node a h (S k) = cas_node a h k + h.
Proof. intros. unfold cas_node. rewrite S_INR. ring. Qed.

Lemma cas_node_0 : forall a h, cas_node a h 0 = a.
Proof. intros. unfold cas_node. cbn. ring. Qed.

(* Start point of piece k: the clothoid point P(a) for k = 0, else the end
   of piece k - 1. *)
Fixpoint cas_start (c : ClothoidEgg) (a h : R) (k : nat) : Point :=
  match k with
  | O => cloth_P c a
  | S j =>
      cas_arc_pt (cas_start c a h j)
        (cloth_vx c (cas_node a h j)) (cloth_vy c (cas_node a h j))
        (cas_kap c (cas_node a h j) h) h
  end.

(* Piece k, evaluated at station u in [x_k, x_k + h]. *)
Definition cas_piece (c : ClothoidEgg) (a h : R) (k : nat) (u : R) : Point :=
  cas_arc_pt (cas_start c a h k)
    (cloth_vx c (cas_node a h k)) (cloth_vy c (cas_node a h k))
    (cas_kap c (cas_node a h k) h) (u - cas_node a h k).

Lemma cas_piece_end : forall c a h k,
  cas_piece c a h k (cas_node a h (S k)) = cas_start c a h (S k).
Proof.
  intros. unfold cas_piece. cbn [cas_start]. f_equal.
  rewrite cas_node_S. ring.
Qed.

(* Position continuity: piece k ends where piece k + 1 starts. *)
Lemma cas_spline_c0 : forall c a h k,
  cas_piece c a h k (cas_node a h (S k)) =
  cas_piece c a h (S k) (cas_node a h (S k)).
Proof.
  intros. rewrite cas_piece_end. unfold cas_piece.
  rewrite Rminus_diag. rewrite cas_arc_pt_0. reflexivity.
Qed.

Lemma cas_spline_start : forall c a h, cas_piece c a h 0 a = cloth_P c a.
Proof.
  intros. unfold cas_piece. rewrite cas_node_0, Rminus_diag, cas_arc_pt_0.
  reflexivity.
Qed.

Lemma cas_vx_rot : forall c s, cloth_vx c s =
  cas_rot_x (cloth_cos0 c) (cloth_sin0 c) (cloth_psi c s).
Proof. reflexivity. Qed.

Lemma cas_vy_rot : forall c s, cloth_vy c s =
  cas_rot_y (cloth_cos0 c) (cloth_sin0 c) (cloth_psi c s).
Proof. reflexivity. Qed.

(* Tangent of piece k at station u. *)
Lemma cas_piece_tangent : forall c a h k u,
  derivable_pt_lim (fun v => px (cas_piece c a h k v)) u
    (cas_rot_x (cloth_cos0 c) (cloth_sin0 c)
       (cloth_psi c (cas_node a h k)
        + cas_kap c (cas_node a h k) h * (u - cas_node a h k))) /\
  derivable_pt_lim (fun v => py (cas_piece c a h k v)) u
    (cas_rot_y (cloth_cos0 c) (cloth_sin0 c)
       (cloth_psi c (cas_node a h k)
        + cas_kap c (cas_node a h k) h * (u - cas_node a h k))).
Proof.
  intros. unfold cas_piece. split.
  - rewrite <- cas_rot_compose_x, <- cas_vx_rot, <- cas_vy_rot.
    apply cas_arc_px_deriv.
  - rewrite <- cas_rot_compose_y, <- cas_vx_rot, <- cas_vy_rot.
    apply cas_arc_py_deriv.
Qed.

(* G1: the tangent of piece k at its far node is the clothoid tangent there,
   which is the start tangent of piece k + 1. *)
Theorem cas_spline_g1 : forall c a h k, cloth_A c <> 0 ->
  cas_rot_x (cloth_vx c (cas_node a h k)) (cloth_vy c (cas_node a h k))
    (cas_kap c (cas_node a h k) h * h) = cloth_vx c (cas_node a h (S k)) /\
  cas_rot_y (cloth_vx c (cas_node a h k)) (cloth_vy c (cas_node a h k))
    (cas_kap c (cas_node a h k) h * h) = cloth_vy c (cas_node a h (S k)).
Proof.
  intros c a h k HA.
  rewrite cas_vx_rot, cas_vy_rot, cas_rot_compose_x, cas_rot_compose_y.
  rewrite cas_psi_node by exact HA. rewrite <- cas_node_S.
  split; reflexivity.
Qed.

(* One piece: error = inherited start offset + delta * arc length so far. *)
Lemma cas_piece_err : forall c a h k u, cloth_wf c -> 0 <= h ->
  cas_node a h k <= u <= cas_node a h k + h ->
  dist (cloth_P c u) (cas_piece c a h k u)
    <= dist (cloth_P c (cas_node a h k)) (cas_start c a h k)
       + cas_delta c h * (u - cas_node a h k).
Proof.
  intros c a h k u Hwf Hh Hu.
  destruct Hwf as [HA [Hh2 _]].
  assert (HA0 : cloth_A c <> 0) by lra.
  set (x := cas_node a h k).
  fold x in Hu.
  set (fx := fun v => cloth_Px c v - px (cas_piece c a h k v)).
  set (fy := fun v => cloth_Py c v - py (cas_piece c a h k v)).
  set (bet := fun v => cloth_psi c x + cas_kap c x h * (v - x)).
  set (gx := fun v => cloth_vx c v
               - cas_rot_x (cloth_cos0 c) (cloth_sin0 c) (bet v)).
  set (gy := fun v => cloth_vy c v
               - cas_rot_y (cloth_cos0 c) (cloth_sin0 c) (bet v)).
  assert (Hpx : forall v, x <= v <= u -> derivable_pt_lim fx v (gx v)).
  { intros v _. unfold fx, gx, bet.
    apply d_minus; [apply cloth_Px_deriv|].
    apply (cas_piece_tangent c a h k v). }
  assert (Hpy : forall v, x <= v <= u -> derivable_pt_lim fy v (gy v)).
  { intros v _. unfold fy, gy, bet.
    apply d_minus; [apply cloth_Py_deriv|].
    apply (cas_piece_tangent c a h k v). }
  assert (Hg : forall v, x <= v <= u ->
            gx v * gx v + gy v * gy v <= cas_delta c h * cas_delta c h).
  { intros v Hv. unfold gx, gy.
    rewrite cas_vx_rot, cas_vy_rot.
    eapply Rle_trans.
    - apply cas_rot_diff_sq. apply cloth_frame_sumsq. exact Hh2.
    - unfold bet. apply cas_heading_err_sq; [exact HA0 | exact Hh | lra]. }
  pose proof (vec_mvi fx fy gx gy x u (cas_delta c h) (proj1 Hu)
                (cas_delta_nonneg c h HA0) Hpx Hpy Hg) as H.
  unfold dist, dist_sq. cbn [px py cloth_P]. unfold fx, fy in H.
  replace (cas_piece c a h k x) with (cas_start c a h k) in H.
  - exact H.
  - unfold cas_piece. fold x. rewrite Rminus_diag, cas_arc_pt_0. reflexivity.
Qed.

(* Node offsets accumulate linearly: no heading drift at the nodes. *)
Lemma cas_start_err : forall c a h k, cloth_wf c -> 0 <= h ->
  dist (cloth_P c (cas_node a h k)) (cas_start c a h k)
    <= cas_delta c h * (INR k * h).
Proof.
  intros c a h k Hwf Hh. induction k as [|k IH].
  - rewrite cas_node_0. cbn [cas_start INR].
    rewrite dist_refl. right. ring.
  - rewrite <- cas_piece_end.
    eapply Rle_trans.
    + apply cas_piece_err; [exact Hwf | exact Hh |].
      rewrite cas_node_S. lra.
    + rewrite cas_node_S, S_INR.
      replace (cas_node a h k + h - cas_node a h k) with h by ring.
      lra.
Qed.

Theorem cas_spline_err : forall c a h k u, cloth_wf c -> 0 <= h ->
  cas_node a h k <= u <= cas_node a h (S k) ->
  dist (cloth_P c u) (cas_piece c a h k u) <= cas_delta c h * (u - a).
Proof.
  intros c a h k u Hwf Hh Hu.
  rewrite cas_node_S in Hu.
  eapply Rle_trans; [apply cas_piece_err; assumption|].
  pose proof (cas_start_err c a h k Hwf Hh) as Hs.
  replace (u - a) with (INR k * h + (u - cas_node a h k))
    by (unfold cas_node; ring).
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Window form and the ε contract.                                            *)
(* -------------------------------------------------------------------------- *)

Definition cas_step (a b : R) (N : nat) : R := (b - a) / INR N.

Lemma cas_node_N : forall a b N, (N <> 0)%nat ->
  cas_node a (cas_step a b N) N = b.
Proof.
  intros a b N HN. unfold cas_node, cas_step. field. apply not_0_INR. exact HN.
Qed.

(* Every station of the window lies in some piece. *)
Lemma cas_slot : forall a b N u, a < b -> (2 <= N)%nat -> a <= u <= b ->
  exists k, (k < N)%nat /\
    cas_node a (cas_step a b N) k <= u <= cas_node a (cas_step a b N) (S k).
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
  assert (Hnode : forall j, cas_node a (cas_step a b N) j
                            = a + (b - a) * cloth_ts N j).
  { intro j. unfold cas_node, cas_step, cloth_ts. field.
    apply not_0_INR. lia. }
  rewrite !Hnode.
  assert (Hu' : u = a + (b - a) * t) by (unfold t; field; lra).
  rewrite Hu'. nra.
Qed.

Lemma cas_slot_any : forall a b N u, a <= b -> (N <> 0)%nat -> a <= u <= b ->
  exists k, (k < N)%nat /\
    cas_node a (cas_step a b N) k <= u <= cas_node a (cas_step a b N) (S k).
Proof.
  intros a b N u Hab HN Hu.
  destruct (Rle_lt_dec b a) as [Hba|Hlt].
  - exists 0%nat. split; [lia|].
    rewrite cas_node_S, cas_node_0. unfold cas_step.
    assert (E : b - a = 0) by lra. rewrite E. unfold Rdiv. lra.
  - destruct (Nat.eq_dec N 1) as [->|HN1].
    + exists 0%nat. split; [lia|].
      rewrite cas_node_S, cas_node_0. unfold cas_step.
      replace (INR 1) with 1 by reflexivity. unfold Rdiv. rewrite Rinv_1. lra.
    + apply cas_slot; [exact Hlt | lia | exact Hu].
Qed.

(* Piece -> clothoid: every point of piece k is near the clothoid point at
   its station. *)
Theorem cas_arc_spline_within : forall c a b N, cloth_wf c -> a <= b ->
  (N <> 0)%nat ->
  (forall k u, (k < N)%nat ->
     cas_node a (cas_step a b N) k <= u <= cas_node a (cas_step a b N) (S k) ->
     dist (cloth_P c u) (cas_piece c a (cas_step a b N) k u)
       <= (b - a) * (b - a) * (b - a)
          / (8 * (cloth_A c * cloth_A c) * (INR N * INR N))).
Proof.
  intros c a b N Hwf Hab HN k u Hk Hu.
  assert (HNp : 0 < INR N) by (apply lt_0_INR; lia).
  set (h := cas_step a b N).
  assert (Hh : 0 <= h).
  { unfold h, cas_step. apply Rmult_le_pos; [lra|].
    apply Rlt_le, Rinv_0_lt_compat. exact HNp. }
  eapply Rle_trans; [apply cas_spline_err; [exact Hwf | exact Hh | exact Hu]|].
  assert (Hub : u <= b).
  { apply Rle_trans with (cas_node a h (S k)); [exact (proj2 Hu)|].
    rewrite <- (cas_node_N a b N HN). fold h. unfold cas_node.
    apply Rplus_le_compat_l, Rmult_le_compat_r; [exact Hh|].
    apply le_INR. lia. }
  assert (Hua : a <= u).
  { apply Rle_trans with (cas_node a h k); [|exact (proj1 Hu)].
    unfold cas_node. pose proof (pos_INR k). nra. }
  destruct Hwf as [HA _].
  assert (HAA : 0 < cloth_A c * cloth_A c) by nra.
  pose proof (cas_delta_nonneg c h ltac:(lra)) as Hd.
  apply Rle_trans with (cas_delta c h * (b - a)); [nra|].
  right. unfold cas_delta, h, cas_step. field. lra.
Qed.

(* The ε contract for the N-arc spline. *)
Theorem cas_arc_spline_within_eps : forall c a b N eps,
  cloth_wf c -> a <= b -> (N <> 0)%nat ->
  (b - a) * (b - a) * (b - a)
    <= 8 * (cloth_A c * cloth_A c) * (INR N * INR N) * eps ->
  forall k u, (k < N)%nat ->
    cas_node a (cas_step a b N) k <= u <= cas_node a (cas_step a b N) (S k) ->
    dist (cloth_P c u) (cas_piece c a (cas_step a b N) k u) <= eps.
Proof.
  intros c a b N eps Hwf Hab HN Hgate k u Hk Hu.
  eapply Rle_trans; [apply cas_arc_spline_within; eassumption|].
  destruct Hwf as [HA _].
  assert (HNp : 0 < INR N) by (apply lt_0_INR; lia).
  assert (Hden : 0 < 8 * (cloth_A c * cloth_A c) * (INR N * INR N)).
  { apply Rmult_lt_0_compat; [nra | nra]. }
  apply Rmult_le_reg_r with (8 * (cloth_A c * cloth_A c) * (INR N * INR N));
    [exact Hden|].
  unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra.
Qed.

(* Clothoid -> piece: every clothoid point of the window is near the piece
   point at its station, for every N >= 1. *)
Theorem cas_arc_spline_cover : forall c a b N eps,
  cloth_wf c -> a <= b -> (N <> 0)%nat ->
  (b - a) * (b - a) * (b - a)
    <= 8 * (cloth_A c * cloth_A c) * (INR N * INR N) * eps ->
  forall u, a <= u <= b -> exists k, (k < N)%nat /\
    cas_node a (cas_step a b N) k <= u <= cas_node a (cas_step a b N) (S k) /\
    dist (cloth_P c u) (cas_piece c a (cas_step a b N) k u) <= eps.
Proof.
  intros c a b N eps Hwf Hab HN Hgate u Hu.
  destruct (cas_slot_any a b N u Hab HN Hu) as [k [Hk Hku]].
  exists k. split; [exact Hk|]. split; [exact Hku|].
  apply (cas_arc_spline_within_eps c a b N eps); assumption.
Qed.

(* The window end is NOT interpolated: the spline ends at cas_start N, at
   most (b - a)^3 / (8 A^2 N^2) from P(b). *)
Theorem cas_end_gap : forall c a b N, cloth_wf c -> a <= b -> (N <> 0)%nat ->
  dist (cloth_P c b) (cas_start c a (cas_step a b N) N)
    <= (b - a) * (b - a) * (b - a)
       / (8 * (cloth_A c * cloth_A c) * (INR N * INR N)).
Proof.
  intros c a b N Hwf Hab HN.
  assert (HNp : 0 < INR N) by (apply lt_0_INR; lia).
  assert (Hh : 0 <= cas_step a b N).
  { unfold cas_step. apply Rmult_le_pos; [lra|].
    apply Rlt_le, Rinv_0_lt_compat. exact HNp. }
  pose proof (cas_start_err c a (cas_step a b N) N Hwf Hh) as H.
  rewrite (cas_node_N a b N HN) in H.
  eapply Rle_trans; [exact H|].
  destruct Hwf as [HA _].
  right. unfold cas_delta, cas_step. field. split; lra.
Qed.

(* WITNESS {"claimId":"0007-clothoid-arc-spline","topic":"curves","lemma":"cas_two_arc_within_eps","title":"Two-arc heading-interpolating spline of a host clothoid window [a, b] (not the endpoint-interpolating biarc): two C0/G1-joined circular arcs shot from P(a) with the clothoid tangents at a, (a+b)/2, b and the midpoint curvatures; both directions within (b-a)^3/(32 A^2) at equal arc length, and the end misses P(b) by at most the same bound","file":"theories/ClothoidArcSpline.v","witness":"cas_two_arc_within_eps","board":"ADR-0007"} *)
Theorem cas_two_arc_within_eps : forall c a b eps,
  cloth_wf c -> a <= b ->
  (b - a) * (b - a) * (b - a) <= 32 * (cloth_A c * cloth_A c) * eps ->
  (* every spline point is within eps of the clothoid point at its station *)
  (forall k u, (k < 2)%nat ->
     cas_node a (cas_step a b 2) k <= u <= cas_node a (cas_step a b 2) (S k) ->
     dist (cloth_P c u) (cas_piece c a (cas_step a b 2) k u) <= eps) /\
  (* every clothoid point of the window is within eps of a spline point *)
  (forall u, a <= u <= b -> exists k, (k < 2)%nat /\
     dist (cloth_P c u) (cas_piece c a (cas_step a b 2) k u) <= eps) /\
  (* node tangents (a, the junction, b) are the clothoid tangents *)
  (forall k, (k < 2)%nat ->
     cas_rot_x (cloth_vx c (cas_node a (cas_step a b 2) k))
               (cloth_vy c (cas_node a (cas_step a b 2) k))
       (cas_kap c (cas_node a (cas_step a b 2) k) (cas_step a b 2)
        * cas_step a b 2)
       = cloth_vx c (cas_node a (cas_step a b 2) (S k)) /\
     cas_rot_y (cloth_vx c (cas_node a (cas_step a b 2) k))
               (cloth_vy c (cas_node a (cas_step a b 2) k))
       (cas_kap c (cas_node a (cas_step a b 2) k) (cas_step a b 2)
        * cas_step a b 2)
       = cloth_vy c (cas_node a (cas_step a b 2) (S k))) /\
  (* positions: starts at P(a), continuous at the junction, and the end is
     only within eps of P(b) -- not interpolated *)
  cas_piece c a (cas_step a b 2) 0 a = cloth_P c a /\
  cas_piece c a (cas_step a b 2) 0 (cas_node a (cas_step a b 2) 1) =
  cas_piece c a (cas_step a b 2) 1 (cas_node a (cas_step a b 2) 1) /\
  dist (cloth_P c b) (cas_start c a (cas_step a b 2) 2) <= eps.
Proof.
  intros c a b eps Hwf Hab Hgate.
  assert (H2 : (2 <> 0)%nat) by lia.
  assert (Hgate2 : (b - a) * (b - a) * (b - a)
            <= 8 * (cloth_A c * cloth_A c) * (INR 2 * INR 2) * eps).
  { replace (INR 2) with 2 by (cbn; ring). lra. }
  pose proof (cas_arc_spline_within_eps c a b 2 eps Hwf Hab H2 Hgate2) as Hin.
  split; [exact Hin|]. split; [|split; [|split; [|split]]].
  - intros u Hu.
    destruct (cas_arc_spline_cover c a b 2 eps Hwf Hab H2 Hgate2 u Hu)
      as [k [Hk [_ Hd]]].
    exists k. split; assumption.
  - intros k _. apply cas_spline_g1. destruct Hwf as [HA _]. lra.
  - apply cas_spline_start.
  - apply cas_spline_c0.
  - eapply Rle_trans; [apply (cas_end_gap c a b 2 Hwf Hab H2)|].
    destruct Hwf as [HA _].
    assert (Hden : 0 < 8 * (cloth_A c * cloth_A c) * (INR 2 * INR 2)).
    { replace (INR 2) with 2 by (cbn; ring). nra. }
    apply Rmult_le_reg_r with (8 * (cloth_A c * cloth_A c) * (INR 2 * INR 2));
      [exact Hden|].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Stability of one frame step (consumed by the binary64 point theorem).      *)
(* -------------------------------------------------------------------------- *)

(* S + (tx, ty) * (X + i Y): the step that places local arc coordinates. *)
Definition cas_frame (S : Point) (tx ty X Y : R) : Point :=
  mkPoint (px S + tx * X - ty * Y) (py S + ty * X + tx * Y).

Lemma cas_arc_pt_frame : forall Q tx ty k x,
  cas_arc_pt Q tx ty k x = cas_frame Q tx ty (cas_arc_X k x) (cas_arc_Y k x).
Proof. reflexivity. Qed.

(* The chord of an arc is no longer than the arc. *)
Lemma cas_arc_chord : forall k x,
  cas_arc_X k x * cas_arc_X k x + cas_arc_Y k x * cas_arc_Y k x <= x * x.
Proof.
  intros k x. unfold cas_arc_X, cas_arc_Y.
  destruct (Req_EM_T k 0) as [_|Hk]; [lra|].
  set (z := k * x / 2).
  assert (Hc : cos (k * x) = 1 - 2 * sin z * sin z).
  { rewrite <- cos_2a_sin. unfold z. f_equal. field. }
  pose proof (sin2_cos2 (k * x)) as Hsc. unfold Rsqr in Hsc.
  assert (Hs : sin z * sin z <= z * z).
  { pose proof (Rsqr_le_abs_1 _ _ (abs_sin_le z)) as H. unfold Rsqr in H. exact H. }
  assert (Hkk : 0 < k * k) by (apply Rsqr_pos_lt; exact Hk).
  replace (sin (k * x) / k * (sin (k * x) / k) +
           (1 - cos (k * x)) / k * ((1 - cos (k * x)) / k))
    with ((sin (k * x) * sin (k * x) + cos (k * x) * cos (k * x)
           + 1 - 2 * cos (k * x)) / (k * k)) by (field; exact Hk).
  rewrite Hsc, Hc.
  replace (x * x) with (4 * (z * z) / (k * k)) by (unfold z; field; exact Hk).
  unfold Rdiv. apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; lra|].
  lra.
Qed.

(* Moving the start, the frame and the local coordinates moves the step by
   at most the sum of the three effects. *)
Lemma cas_frame_perturb : forall S S' tx ty tx' ty' X Y X' Y',
  dist (cas_frame S' tx' ty' X' Y') (cas_frame S tx ty X Y)
    <= dist S' S
       + dist (mkPoint tx' ty') (mkPoint tx ty) * sqrt (X * X + Y * Y)
       + sqrt (tx' * tx' + ty' * ty') * dist (mkPoint X' Y') (mkPoint X Y).
Proof.
  intros.
  assert (E1 : dist (cas_frame S' tx' ty' X' Y') (cas_frame S' tx' ty' X Y)
               = sqrt (tx' * tx' + ty' * ty') * dist (mkPoint X' Y') (mkPoint X Y)).
  { unfold dist, dist_sq, cas_frame. cbn.
    rewrite <- sqrt_mult by (apply Rplus_le_le_0_compat; apply Rle_0_sqr).
    f_equal. ring. }
  assert (E2 : dist (cas_frame S' tx' ty' X Y) (cas_frame S' tx ty X Y)
               = dist (mkPoint tx' ty') (mkPoint tx ty) * sqrt (X * X + Y * Y)).
  { unfold dist, dist_sq, cas_frame. cbn.
    rewrite <- sqrt_mult by (apply Rplus_le_le_0_compat; apply Rle_0_sqr).
    f_equal. ring. }
  assert (E3 : dist (cas_frame S' tx ty X Y) (cas_frame S tx ty X Y) = dist S' S).
  { unfold dist, dist_sq, cas_frame. cbn. f_equal. ring. }
  pose proof (dist_triangle (cas_frame S' tx' ty' X' Y') (cas_frame S' tx' ty' X Y)
                (cas_frame S tx ty X Y)) as T1.
  pose proof (dist_triangle (cas_frame S' tx' ty' X Y) (cas_frame S' tx ty X Y)
                (cas_frame S tx ty X Y)) as T2.
  lra.
Qed.

Print Assumptions cas_arc_on_circle.
Print Assumptions cas_arc_chord.
Print Assumptions cas_frame_perturb.
Print Assumptions cas_spline_g1.
Print Assumptions cas_spline_err.
Print Assumptions cas_arc_spline_within.
Print Assumptions cas_arc_spline_within_eps.
Print Assumptions cas_arc_spline_cover.
Print Assumptions cas_end_gap.
Print Assumptions cas_two_arc_within_eps.
