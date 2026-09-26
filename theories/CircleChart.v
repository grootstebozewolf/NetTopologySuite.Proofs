(* ============================================================================
   NetTopologySuite.Proofs.CircleChart
   ----------------------------------------------------------------------------
   Stereographic / half-angle chart on a circle.  τ = tan(φ/2), pole Q the
   second intersection of the line through arc-mid M and the chord midpoint
   N of AB (rational by Vieta; no square root).

   Chart core (field operations on R), carried from the owner's exhibit:
     chart_on_circle, chart_left_inv, chart_right_inv, pole_on_circle.
   Corpus points are O + v; orient is translation-invariant, so the
   offset identity chart_orient3_offset lifts to chart_orient3.

   C0 (freeze-neutral; not a CircularEgg reparameterisation):
     pole_opposite_M
       Q is strictly on the opposite side of chord AB from M.
     tau_monotone_off_pole
       a < b < c ⇒ τ increases and orient(P(a),P(b),P(c)) > 0
       on the oriented circle minus Q.
     arc_member_iff_tau_interval
       on-circle P ≠ Q lies on the arc A‥B determined by M
       iff τ(P) lies in the bounded chart interval with ends τ(A), τ(B).
     arc_span_contains_iff_tau
       that membership is ArcIntersect.arc_span_contains on a valid_arc
       (Option S / chord-sign).  Angle-free third proof beside
       ArcSpanAtan2.arc_span_contains_atan2_iff_chord_sign.
       This file does not import Atan2 / Ratan.

   The projective full-circle case A = B with Q = A is outside valid_arc
   (the chord collapses).  chart_right_inv is the statement that every
   non-pole point is hit.  It is not a separate Admitted.

   Does not remint CircGamma, leftover Ⅹ, LoopDischarged, I_ok_mixed as
   host, MkNurbs, or 0007-intake-angles.  Does not inhabit
   HostMixedHitSpan.  Carry-and-check on CircularEgg (#771) stands.
   Refs #771 / #767.  Related, not discharged here: #770, #866.
   claimId: none.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra Field.
From NTS.Proofs Require Import Distance Segment CurveGeometry ArcOrient
  ArcIntersect ArcChordApprox.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Chart core (offset vectors).  u = O - Q, v = P - O.                   *)
(* -------------------------------------------------------------------------- *)

Definition dot (ax ay bx by_ : R) : R := ax * bx + ay * by_.
Definition crs (ax ay bx by_ : R) : R := ax * by_ - ay * bx.

Definition tau (ux uy vx vy : R) : R :=
  crs ux uy vx vy / (dot ux uy ux uy + dot ux uy vx vy).

Definition vx_of (ux uy t : R) : R :=
  ((1 - t * t) * ux + 2 * t * (- uy)) / (1 + t * t).
Definition vy_of (ux uy t : R) : R :=
  ((1 - t * t) * uy + 2 * t * ux) / (1 + t * t).

Lemma one_t2 : forall t, 0 < 1 + t * t.
Proof. intro t. nra. Qed.

Lemma sumsq_pos : forall x y : R, (x, y) <> (0, 0) -> 0 < x * x + y * y.
Proof.
  intros x y H.
  destruct (Req_dec x 0) as [->|Hx].
  - destruct (Req_dec y 0) as [->|Hy].
    + exfalso. apply H. reflexivity.
    + nra.
  - nra.
Qed.

Lemma Point_eq_of_coords : forall P Q : Point,
  px P = px Q -> py P = py Q -> P = Q.
Proof.
  intros P Q Hx Hy. destruct P as [pxP pyP], Q as [pxQ pyQ].
  cbn in Hx, Hy. subst. reflexivity.
Qed.

Theorem chart_on_circle : forall ux uy t,
  dot (vx_of ux uy t) (vy_of ux uy t) (vx_of ux uy t) (vy_of ux uy t)
    = dot ux uy ux uy.
Proof.
  intros ux uy t. pose proof (one_t2 t) as Ht.
  unfold dot, vx_of, vy_of. field. lra.
Qed.

Theorem chart_left_inv : forall ux uy t, (ux, uy) <> (0, 0) ->
  tau ux uy (vx_of ux uy t) (vy_of ux uy t) = t.
Proof.
  intros ux uy t Hu. pose proof (one_t2 t) as Ht.
  assert (Hr : 0 < ux * ux + uy * uy) by (apply sumsq_pos; exact Hu).
  unfold tau, dot, crs, vx_of, vy_of. field. split; nra.
Qed.

Theorem chart_right_inv : forall ux uy vx vy,
  vx * vx + vy * vy = ux * ux + uy * uy ->
  ux * ux + uy * uy + (ux * vx + uy * vy) <> 0 ->
  vx_of ux uy (tau ux uy vx vy) = vx /\
  vy_of ux uy (tau ux uy vx vy) = vy.
Proof.
  intros ux uy vx vy Hc Hd.
  set (s := ux * ux + uy * uy) in *.
  set (D := s + (ux * vx + uy * vy)) in *.
  set (C := ux * vy - uy * vx).
  assert (Hs : s <> 0).
  { intro E. apply Hd. unfold D.
    assert (ux = 0) by (unfold s in E; nra).
    assert (uy = 0) by (unfold s in E; nra).
    unfold s. subst. ring. }
  assert (Hh : vx * vx + vy * vy - s = 0) by lra.
  assert (K : C * C + D * D = 2 * s * D).
  { assert (E : C * C + D * D - 2 * s * D = s * (vx * vx + vy * vy - s))
      by (unfold C, D, s; ring).
    rewrite Hh in E. lra. }
  assert (Kx : (D * D - C * C) * ux - 2 * C * D * uy = 2 * s * D * vx).
  { assert (E : (D * D - C * C) * ux - 2 * C * D * uy - 2 * s * D * vx
              = - ux * s * (vx * vx + vy * vy - s)) by (unfold C, D, s; ring).
    rewrite Hh in E. lra. }
  assert (Ky : (D * D - C * C) * uy + 2 * C * D * ux = 2 * s * D * vy).
  { assert (E : (D * D - C * C) * uy + 2 * C * D * ux - 2 * s * D * vy
              = - uy * s * (vx * vx + vy * vy - s)) by (unfold C, D, s; ring).
    rewrite Hh in E. lra. }
  assert (Ht : tau ux uy vx vy = C / D) by (unfold tau, dot, crs; fold s; reflexivity).
  rewrite Ht. unfold vx_of, vy_of. split.
  - replace ((1 - C / D * (C / D)) * ux + 2 * (C / D) * - uy) with
      (((D * D - C * C) * ux - 2 * C * D * uy) / (D * D)) by (field; exact Hd).
    replace (1 + C / D * (C / D)) with ((C * C + D * D) / (D * D)) by (field; exact Hd).
    rewrite Kx, K. field. split; [exact Hd | exact Hs].
  - replace ((1 - C / D * (C / D)) * uy + 2 * (C / D) * ux) with
      (((D * D - C * C) * uy + 2 * C * D * ux) / (D * D)) by (field; exact Hd).
    replace (1 + C / D * (C / D)) with ((C * C + D * D) / (D * D)) by (field; exact Hd).
    rewrite Ky, K. field. split; [exact Hd | exact Hs].
Qed.

(* Twice signed area of triangle (A,B,C).  Same polynomial as
   ArcOrient.cross_R_pt A B C. *)
Definition orient3 (ax ay bx by_ cx cy : R) : R :=
  crs (bx - ax) (by_ - ay) (cx - ax) (cy - ay).

Definition orient_pts (A B C : Point) : R :=
  orient3 (px A) (py A) (px B) (py B) (px C) (py C).

Lemma orient3_translate : forall ox oy ax ay bx by_ cx cy,
  orient3 (ox + ax) (oy + ay) (ox + bx) (oy + by_) (ox + cx) (oy + cy)
    = orient3 ax ay bx by_ cx cy.
Proof. intros. unfold orient3, crs. ring. Qed.

Lemma orient_pts_offsets : forall O A B C,
  orient_pts A B C =
  orient3 (px A - px O) (py A - py O)
          (px B - px O) (py B - py O)
          (px C - px O) (py C - py O).
Proof. intros. unfold orient_pts, orient3, crs. ring. Qed.

Lemma orient_pts_first_zero : forall A B, orient_pts A B A = 0.
Proof. intros. unfold orient_pts, orient3, crs. ring. Qed.

Lemma orient_pts_second_zero : forall A B, orient_pts A B B = 0.
Proof. intros. unfold orient_pts, orient3, crs. ring. Qed.

Lemma arc_side_eq_orient : forall a P,
  arc_side_chord a P = orient_pts (arc_start a) (arc_end a) P.
Proof.
  intros. unfold arc_side_chord, cross_R_pt, orient_pts, orient3, crs. ring.
Qed.

(* Owner fact 1, on offsets.  One field; denominators are 1+t² > 0. *)
Lemma chart_orient3_offset : forall ux uy a b c,
  orient3 (vx_of ux uy a) (vy_of ux uy a)
          (vx_of ux uy b) (vy_of ux uy b)
          (vx_of ux uy c) (vy_of ux uy c)
  = 4 * (ux * ux + uy * uy) * (b - a) * (c - a) * (c - b)
      / ((1 + a * a) * (1 + b * b) * (1 + c * c)).
Proof.
  intros. unfold orient3, vx_of, vy_of, crs. field. repeat split; nra.
Qed.

Theorem chart_orient3 : forall ox oy ux uy a b c,
  orient3 (ox + vx_of ux uy a) (oy + vy_of ux uy a)
          (ox + vx_of ux uy b) (oy + vy_of ux uy b)
          (ox + vx_of ux uy c) (oy + vy_of ux uy c)
  = 4 * (ux * ux + uy * uy) * (b - a) * (c - a) * (c - b)
      / ((1 + a * a) * (1 + b * b) * (1 + c * c)).
Proof.
  intros. rewrite orient3_translate. apply chart_orient3_offset.
Qed.

(* The pole, as an offset, is -u.  Leading coefficient of the chart
   quadratic: orient(v(ta), v(tb), -u) = 4 |u|² (tb-ta) / ((1+ta²)(1+tb²)). *)
Lemma orient_at_pole_param : forall ux uy ta tb,
  orient3 (vx_of ux uy ta) (vy_of ux uy ta)
          (vx_of ux uy tb) (vy_of ux uy tb)
          (- ux) (- uy)
  = 4 * (ux * ux + uy * uy) * (tb - ta)
      / ((1 + ta * ta) * (1 + tb * tb)).
Proof.
  intros. unfold orient3, vx_of, vy_of, crs. field. repeat split; nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Rational pole.  m = M - O, w = N - M, k = -2 (m·w) / |w|².            *)
(* -------------------------------------------------------------------------- *)

Definition pole_k (mx my wx wy : R) : R :=
  - 2 * (mx * wx + my * wy) / (wx * wx + wy * wy).

Theorem pole_on_circle : forall mx my wx wy, (wx, wy) <> (0, 0) ->
  let k := pole_k mx my wx wy in
  (mx + k * wx) * (mx + k * wx) + (my + k * wy) * (my + k * wy)
    = mx * mx + my * my.
Proof.
  intros mx my wx wy Hw k.
  assert (Hr : 0 < wx * wx + wy * wy) by (apply sumsq_pos; exact Hw).
  unfold k, pole_k. field. lra.
Qed.

Definition pole_point (O M N : Point) : Point :=
  let mx := px M in
  let my := py M in
  let wx := px N - mx in
  let wy := py N - my in
  let k := pole_k (mx - px O) (my - py O) wx wy in
  mkPoint (mx + k * wx) (my + k * wy).

Definition tau_pt (O Q P : Point) : R :=
  tau (px O - px Q) (py O - py Q) (px P - px O) (py P - py O).

(* Bounded chart interval with endpoints ta, tb (order-independent).
   This is {τ(A), τ(B)}'s convex hull: the arc that does not contain the
   pole.  Equivalent to Rmin(ta,tb) ≤ tp ≤ Rmax(ta,tb). *)
Definition in_chart_interval (ta tb tp : R) : Prop :=
  (tp - ta) * (tp - tb) <= 0.

(* On-circle, same side of chord AB as M, or an endpoint.
   This is the formula of ArcIntersect.arc_span_contains. *)
Definition arc_member_AB_M (A B M P : Point) : Prop :=
  0 < orient_pts A B M * orient_pts A B P \/ P = A \/ P = B.

Lemma orient_along_mid : forall ax ay bx by_ mx my k,
  orient3 ax ay bx by_
    (mx + k * ((ax + bx) / 2 - mx))
    (my + k * ((ay + by_) / 2 - my))
  = (1 - k) * orient3 ax ay bx by_ mx my.
Proof.
  intros. unfold orient3, crs. field.
Qed.

(* Owner fact 2.  f(λ) = |m + λ w|² - |m|² = |w|² λ (λ - k), and
   f(1) = |N - O|² - |M - O|² = -|B - A|²/4 < 0 when A ≠ B, so 0 < 1 < k. *)
Lemma pole_k_gt_one : forall O A B M,
  dist_sq O A = dist_sq O M ->
  dist_sq O B = dist_sq O M ->
  A <> B ->
  let N := midpoint A B in
  (px N, py N) <> (px M, py M) /\
  1 < pole_k (px M - px O) (py M - py O) (px N - px M) (py N - py M).
Proof.
  intros O A B M HA HB HAB N.
  set (s := (px M - px O) * (px M - px O) + (py M - py O) * (py M - py O)).
  set (nx := (px A + px B) / 2).
  set (ny := (py A + py B) / 2).
  set (Mx := px M - px O). set (My := py M - py O).
  set (Nx := nx - px O). set (Ny := ny - py O).
  set (wx := px N - px M). set (wy := py N - py M).
  assert (Hnx : px N = nx).
  { unfold N, midpoint, nx. cbn. reflexivity. }
  assert (Hny : py N = ny).
  { unfold N, midpoint, ny. cbn. reflexivity. }
  assert (Hwx : wx = Nx - Mx) by (unfold wx, Nx, Mx; rewrite Hnx; ring).
  assert (Hwy : wy = Ny - My) by (unfold wy, Ny, My; rewrite Hny; ring).
  assert (HsM : s = Mx * Mx + My * My) by (unfold s, Mx, My; ring).
  assert (HsA : (px A - px O) * (px A - px O) + (py A - py O) * (py A - py O) = s).
  { unfold dist_sq in HA. unfold s.
    replace ((px O - px A) * (px O - px A)) with
      ((px A - px O) * (px A - px O)) in HA by ring.
    replace ((py O - py A) * (py O - py A)) with
      ((py A - py O) * (py A - py O)) in HA by ring.
    replace ((px O - px M) * (px O - px M)) with
      ((px M - px O) * (px M - px O)) in HA by ring.
    replace ((py O - py M) * (py O - py M)) with
      ((py M - py O) * (py M - py O)) in HA by ring.
    exact HA. }
  assert (HsB : (px B - px O) * (px B - px O) + (py B - py O) * (py B - py O) = s).
  { unfold dist_sq in HB. unfold s.
    replace ((px O - px B) * (px O - px B)) with
      ((px B - px O) * (px B - px O)) in HB by ring.
    replace ((py O - py B) * (py O - py B)) with
      ((py B - py O) * (py B - py O)) in HB by ring.
    replace ((px O - px M) * (px O - px M)) with
      ((px M - px O) * (px M - px O)) in HB by ring.
    replace ((py O - py M) * (py O - py M)) with
      ((py M - py O) * (py M - py O)) in HB by ring.
    exact HB. }
  assert (Hsep : 0 < (px A - px B) * (px A - px B) + (py A - py B) * (py A - py B)).
  { apply sumsq_pos. intros E. apply HAB. injection E as Ex Ey.
    apply Point_eq_of_coords; lra. }
  assert (Hmid :
    Nx * Nx + Ny * Ny
      = s - ((px A - px B) * (px A - px B) + (py A - py B) * (py A - py B)) / 4).
  { unfold Nx, Ny, nx, ny.
    assert (E :
      ((px A + px B) / 2 - px O) * ((px A + px B) / 2 - px O)
      + ((py A + py B) / 2 - py O) * ((py A + py B) / 2 - py O)
      - (((px A - px O) * (px A - px O) + (py A - py O) * (py A - py O))
         - ((px A - px B) * (px A - px B) + (py A - py B) * (py A - py B)) / 4)
      = (((px B - px O) * (px B - px O) + (py B - py O) * (py B - py O))
         - ((px A - px O) * (px A - px O) + (py A - py O) * (py A - py O))) / 2).
    { field. }
    rewrite HsA, HsB in E.
    assert (Z : (s - s) / 2 = 0) by field.
    lra. }
  assert (HNlt : Nx * Nx + Ny * Ny < s) by nra.
  assert (Hwpos : 0 < wx * wx + wy * wy).
  { rewrite Hwx, Hwy.
    destruct (Req_dec (Nx - Mx) 0) as [Hx0|Hx0].
    - destruct (Req_dec (Ny - My) 0) as [Hy0|Hy0].
      + exfalso.
        assert (Nx = Mx) by lra.
        assert (Ny = My) by lra.
        assert (Nx * Nx + Ny * Ny = s) by (rewrite H, H0; symmetry; exact HsM).
        lra.
      + apply sumsq_pos. intros E. injection E as Ex Ey. lra.
    - apply sumsq_pos. intros E. injection E as Ex Ey. lra. }
  assert (Hk :
    pole_k Mx My wx wy - 1
      = (s - (Nx * Nx + Ny * Ny)) / (wx * wx + wy * wy)).
  { rewrite Hwx, Hwy. rewrite HsM. unfold pole_k. field. nra. }
  assert (Hpos : 0 < s - (Nx * Nx + Ny * Ny)) by nra.
  assert (Hkg : 0 < pole_k Mx My wx wy - 1).
  { rewrite Hk. unfold Rdiv. apply Rmult_lt_0_compat.
    - exact Hpos.
    - apply Rinv_0_lt_compat. exact Hwpos. }
  split.
  - intros E.
    enough (wx * wx + wy * wy = 0) by lra.
    unfold wx, wy, N, midpoint in *.
    cbn [px py] in E |- *.
    injection E as Ex Ey. rewrite Ex, Ey. ring.
  - replace (pole_k (px M - px O) (py M - py O)
                    (px N - px M) (py N - py M))
      with (pole_k Mx My wx wy) by (unfold Mx, My, wx, wy; reflexivity).
    lra.
Qed.

Lemma orient_pole_scale : forall O A B M,
  orient_pts A B (pole_point O M (midpoint A B))
  = (1 - pole_k (px M - px O) (py M - py O)
                (px (midpoint A B) - px M)
                (py (midpoint A B) - py M))
    * orient_pts A B M.
Proof.
  intros O A B M.
  set (N := midpoint A B).
  set (k := pole_k (px M - px O) (py M - py O)
                   (px N - px M) (py N - py M)).
  unfold orient_pts.
  assert (Hx : px (pole_point O M N) = px M + k * (px N - px M)).
  { unfold pole_point, k. cbn. reflexivity. }
  assert (Hy : py (pole_point O M N) = py M + k * (py N - py M)).
  { unfold pole_point, k. cbn. reflexivity. }
  rewrite Hx, Hy. unfold N, midpoint, k. cbn [px py].
  apply orient_along_mid.
Qed.

Theorem pole_opposite_M : forall O A B M,
  dist_sq O A = dist_sq O M ->
  dist_sq O B = dist_sq O M ->
  A <> B ->
  orient_pts A B M <> 0 ->
  orient_pts A B M * orient_pts A B (pole_point O M (midpoint A B)) < 0.
Proof.
  intros O A B M HA HB HAB Horient.
  rewrite orient_pole_scale.
  destruct (pole_k_gt_one O A B M HA HB HAB) as [_ Hk].
  cbn zeta in Hk.
  set (om := orient_pts A B M) in *.
  set (k := pole_k (px M - px O) (py M - py O)
                   (px (midpoint A B) - px M)
                   (py (midpoint A B) - py M)) in *.
  replace (om * ((1 - k) * om))
    with (- ((k - 1) * (om * om))) by ring.
  apply Ropp_lt_gt_0_contravar.
  apply Rmult_lt_0_compat.
  - lra.
  - pose proof (Rsqr_pos_lt _ Horient) as Hs.
    unfold Rsqr in Hs. exact Hs.
Qed.

Lemma pole_ne_vertices : forall O A B M,
  dist_sq O A = dist_sq O M ->
  dist_sq O B = dist_sq O M ->
  A <> B ->
  orient_pts A B M <> 0 ->
  let Q := pole_point O M (midpoint A B) in
  Q <> A /\ Q <> B /\ Q <> M.
Proof.
  intros O A B M HA HB HAB Horient Q.
  set (N := midpoint A B).
  set (k := pole_k (px M - px O) (py M - py O)
                   (px N - px M) (py N - py M)).
  destruct (pole_k_gt_one O A B M HA HB HAB) as [HNM Hk].
  cbn zeta in HNM, Hk.
  fold N in HNM, Hk.
  assert (Hkgt : 1 < k) by (unfold k; exact Hk).
  assert (Hscale : orient_pts A B Q = (1 - k) * orient_pts A B M).
  { unfold Q. rewrite (orient_pole_scale O A B M). unfold N, k. reflexivity. }
  assert (Hnz : orient_pts A B Q <> 0).
  { rewrite Hscale. intros E.
    apply Rmult_integral in E. destruct E as [Ek | Eo]; lra. }
  split; [| split].
  - intros E. apply Hnz. rewrite E. apply orient_pts_first_zero.
  - intros E. apply Hnz. rewrite E. apply orient_pts_second_zero.
  - intros E.
    assert (Hx : px Q = px M + k * (px N - px M)).
    { unfold Q, pole_point, k, N. cbn. reflexivity. }
    assert (Hy : py Q = py M + k * (py N - py M)).
    { unfold Q, pole_point, k, N. cbn. reflexivity. }
    assert (Hk0 : k <> 0) by lra.
    assert (Hkx : k * (px N - px M) = 0) by (rewrite E in Hx; lra).
    assert (Hky : k * (py N - py M) = 0) by (rewrite E in Hy; lra).
    apply Rmult_integral in Hkx. apply Rmult_integral in Hky.
    destruct Hkx as [Ekx | Ex]; [contradiction |].
    destruct Hky as [Eky | Ey]; [contradiction |].
    apply HNM. f_equal; lra.
Qed.

Lemma pole_point_radius : forall O M N,
  (px N, py N) <> (px M, py M) ->
  dist_sq O (pole_point O M N) = dist_sq O M.
Proof.
  intros O M N Hne.
  set (mx := px M - px O). set (my := py M - py O).
  set (wx := px N - px M). set (wy := py N - py M).
  assert (Hw : (wx, wy) <> (0, 0)).
  { intros E. apply Hne. injection E as Ex Ey.
    unfold wx, wy in Ex, Ey. f_equal; lra. }
  pose proof (pole_on_circle mx my wx wy Hw) as Hc.
  cbn zeta in Hc.
  unfold dist_sq, pole_point. cbn [px py].
  fold mx my wx wy.
  replace (px O - (px M + pole_k mx my wx wy * wx))
    with (- (mx + pole_k mx my wx wy * wx)) by (unfold mx; ring).
  replace (py O - (py M + pole_k mx my wx wy * wy))
    with (- (my + pole_k mx my wx wy * wy)) by (unfold my; ring).
  replace ((px O - px M) * (px O - px M)) with (mx * mx) by (unfold mx; ring).
  replace ((py O - py M) * (py O - py M)) with (my * my) by (unfold my; ring).
  replace ((- (mx + pole_k mx my wx wy * wx))
           * (- (mx + pole_k mx my wx wy * wx))
         + (- (my + pole_k mx my wx wy * wy))
           * (- (my + pole_k mx my wx wy * wy)))
    with ((mx + pole_k mx my wx wy * wx)
          * (mx + pole_k mx my wx wy * wx)
        + (my + pole_k mx my wx wy * wy)
          * (my + pole_k mx my wx wy * wy)) by ring.
  exact Hc.
Qed.

(* On-circle P ≠ Q is the chart value of its offset, and the pole frame
   is non-degenerate. *)
Lemma chart_frame : forall O Q P,
  dist_sq O P = dist_sq O Q ->
  P <> Q ->
  0 < (px O - px Q) * (px O - px Q) + (py O - py Q) * (py O - py Q) /\
  px P = px O + vx_of (px O - px Q) (py O - py Q) (tau_pt O Q P) /\
  py P = py O + vy_of (px O - px Q) (py O - py Q) (tau_pt O Q P).
Proof.
  intros O Q P Hrad Hne.
  set (ux := px O - px Q). set (uy := py O - py Q).
  set (vx := px P - px O). set (vy := py P - py O).
  assert (Huv : (ux, uy) <> (0, 0)).
  { intros E. injection E as Ex Ey.
    assert (HQ : Q = O).
    { apply Point_eq_of_coords; unfold ux, uy in *; lra. }
    assert (H0 : dist_sq O Q = 0).
    { rewrite HQ. unfold dist_sq. ring. }
    assert (Hp0 : dist_sq O P = 0) by lra.
    apply dist_sq_zero_iff_eq in Hp0.
    destruct Hp0 as [Hpx Hpy].
    assert (PO : P = O).
    { apply Point_eq_of_coords; symmetry; assumption. }
    apply Hne. rewrite PO, HQ. reflexivity. }
  assert (Hr : 0 < ux * ux + uy * uy) by (apply sumsq_pos; exact Huv).
  assert (Hv : vx * vx + vy * vy = ux * ux + uy * uy).
  { unfold dist_sq in Hrad. unfold vx, vy, ux, uy.
    replace ((px P - px O) * (px P - px O))
      with ((px O - px P) * (px O - px P)) by ring.
    replace ((py P - py O) * (py P - py O))
      with ((py O - py P) * (py O - py P)) by ring.
    replace ((px O - px Q) * (px O - px Q))
      with ((px O - px Q) * (px O - px Q)) by ring.
    exact Hrad. }
  assert (Hd : ux * ux + uy * uy + (ux * vx + uy * vy) <> 0).
  { intros E.
    assert (Hpq : dist_sq P Q = 0).
    { unfold dist_sq.
      replace (px P - px Q) with (vx + ux) by (unfold vx, ux; ring).
      replace (py P - py Q) with (vy + uy) by (unfold vy, uy; ring).
      assert (R0 : (vx + ux) * (vx + ux) + (vy + uy) * (vy + uy)
                   = vx * vx + vy * vy + ux * ux + uy * uy
                     + 2 * (ux * vx + uy * vy)) by ring.
      rewrite R0, Hv.
      replace (ux * ux + uy * uy + ux * ux + uy * uy
               + 2 * (ux * vx + uy * vy))
        with (2 * (ux * ux + uy * uy + (ux * vx + uy * vy))) by ring.
      rewrite E. ring. }
    apply dist_sq_zero_iff_eq in Hpq.
    destruct Hpq as [Hx Hy].
    apply Hne. apply Point_eq_of_coords; assumption. }
  destruct (chart_right_inv ux uy vx vy Hv Hd) as [Hx Hy].
  split; [exact Hr | split].
  - replace (tau_pt O Q P) with (tau ux uy vx vy).
    + rewrite Hx. unfold vx. ring.
    + unfold tau_pt, tau, ux, uy, vx, vy. reflexivity.
  - replace (tau_pt O Q P) with (tau ux uy vx vy).
    + rewrite Hy. unfold vy. ring.
    + unfold tau_pt, tau, ux, uy, vx, vy. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  C0.                                                                    *)
(* -------------------------------------------------------------------------- *)

Theorem tau_monotone_off_pole : forall ox oy ux uy a b c,
  (ux, uy) <> (0, 0) ->
  a < b ->
  b < c ->
  tau ux uy (vx_of ux uy a) (vy_of ux uy a)
    < tau ux uy (vx_of ux uy b) (vy_of ux uy b) /\
  tau ux uy (vx_of ux uy b) (vy_of ux uy b)
    < tau ux uy (vx_of ux uy c) (vy_of ux uy c) /\
  0 < orient3 (ox + vx_of ux uy a) (oy + vy_of ux uy a)
              (ox + vx_of ux uy b) (oy + vy_of ux uy b)
              (ox + vx_of ux uy c) (oy + vy_of ux uy c).
Proof.
  intros ox oy ux uy a b c Hu Hab Hbc.
  assert (Hr : 0 < ux * ux + uy * uy) by (apply sumsq_pos; exact Hu).
  split; [| split].
  - rewrite !chart_left_inv by exact Hu. exact Hab.
  - rewrite !chart_left_inv by exact Hu. exact Hbc.
  - rewrite chart_orient3.
    assert (Hba : 0 < b - a) by lra.
    assert (Hca : 0 < c - a) by lra.
    assert (Hcb : 0 < c - b) by lra.
    pose proof (one_t2 a) as Ha1.
    pose proof (one_t2 b) as Hb1.
    pose proof (one_t2 c) as Hc1.
    assert (Hnum : 0 < 4 * (ux * ux + uy * uy) * (b - a) * (c - a) * (c - b)).
    { apply Rmult_lt_0_compat; [| exact Hcb].
      apply Rmult_lt_0_compat; [| exact Hca].
      apply Rmult_lt_0_compat; [| exact Hba].
      apply Rmult_lt_0_compat; [lra | exact Hr]. }
    assert (Hden : 0 < (1 + a * a) * (1 + b * b) * (1 + c * c)).
    { apply Rmult_lt_0_compat; [| exact Hc1].
      apply Rmult_lt_0_compat; assumption. }
    unfold Rdiv. apply Rmult_lt_0_compat.
    + exact Hnum.
    + apply Rinv_0_lt_compat. exact Hden.
Qed.

(* Full circle (A = B, Q = A) is not a valid_arc: the chord collapses.
   chart_right_inv already says every non-pole point is attained, which is
   the projective line.  No separate Admitted. *)

Theorem arc_member_iff_tau_interval : forall O A B M P,
  dist_sq O A = dist_sq O M ->
  dist_sq O B = dist_sq O M ->
  dist_sq O P = dist_sq O M ->
  A <> B ->
  orient_pts A B M <> 0 ->
  P <> pole_point O M (midpoint A B) ->
  arc_member_AB_M A B M P <->
  in_chart_interval
    (tau_pt O (pole_point O M (midpoint A B)) A)
    (tau_pt O (pole_point O M (midpoint A B)) B)
    (tau_pt O (pole_point O M (midpoint A B)) P).
Proof.
  intros O A B M P HA HB HP HAB Horient HPne.
  set (N := midpoint A B).
  set (Q := pole_point O M N).
  assert (HQA : dist_sq O A = dist_sq O Q).
  { destruct (pole_k_gt_one O A B M HA HB HAB) as [HNM _].
    cbn zeta in HNM. fold N in HNM.
    unfold Q. rewrite (pole_point_radius O M N HNM). exact HA. }
  assert (HQB : dist_sq O B = dist_sq O Q) by (rewrite HB, <- HA; exact HQA).
  assert (HQM : dist_sq O M = dist_sq O Q) by (rewrite <- HA; exact HQA).
  assert (HQP : dist_sq O P = dist_sq O Q) by (rewrite HP, <- HA; exact HQA).
  destruct (pole_ne_vertices O A B M HA HB HAB Horient) as [HnA [HnB HnM]].
  cbn zeta in HnA, HnB, HnM.
  fold N in HnA, HnB, HnM. fold Q in HnA, HnB, HnM.
  apply not_eq_sym in HnA. apply not_eq_sym in HnB. apply not_eq_sym in HnM.
  assert (HPneQ : P <> Q) by (unfold Q, N; exact HPne).
  destruct (chart_frame O Q A HQA HnA) as [Hr [HAx HAy]].
  destruct (chart_frame O Q B HQB HnB) as [_ [HBx HBy]].
  destruct (chart_frame O Q M HQM HnM) as [_ [HMx HMy]].
  destruct (chart_frame O Q P HQP HPneQ) as [_ [HPx HPy]].
  set (ux := px O - px Q). set (uy := py O - py Q).
  set (ta := tau_pt O Q A). set (tb := tau_pt O Q B).
  set (tm := tau_pt O Q M). set (tp := tau_pt O Q P).
  set (r2 := ux * ux + uy * uy).
  set (k := pole_k (px M - px O) (py M - py O)
                   (px N - px M) (py N - py M)).
  assert (Htab : ta <> tb).
  { intros E. apply HAB. apply Point_eq_of_coords.
    - rewrite HAx, HBx. unfold ta, tb in E. rewrite E. reflexivity.
    - rewrite HAy, HBy. unfold ta, tb in E. rewrite E. reflexivity. }
  assert (Hkgt : 1 < k).
  { unfold k. destruct (pole_k_gt_one O A B M HA HB HAB) as [_ Hk].
    unfold N in Hk. exact Hk. }
  assert (Hscale : orient_pts A B Q = (1 - k) * orient_pts A B M).
  { unfold Q, N. rewrite (orient_pole_scale O A B M). unfold k. reflexivity. }
  assert (HoA :
    orient_pts A B P
      = 4 * r2 * (tb - ta) * (tp - ta) * (tp - tb)
          / ((1 + ta * ta) * (1 + tb * tb) * (1 + tp * tp))).
  { rewrite (orient_pts_offsets O).
    replace (px A - px O) with (vx_of ux uy ta) by (rewrite HAx; unfold ux, uy, ta; ring).
    replace (py A - py O) with (vy_of ux uy ta) by (rewrite HAy; unfold ux, uy, ta; ring).
    replace (px B - px O) with (vx_of ux uy tb) by (rewrite HBx; unfold ux, uy, tb; ring).
    replace (py B - py O) with (vy_of ux uy tb) by (rewrite HBy; unfold ux, uy, tb; ring).
    replace (px P - px O) with (vx_of ux uy tp) by (rewrite HPx; unfold ux, uy, tp; ring).
    replace (py P - py O) with (vy_of ux uy tp) by (rewrite HPy; unfold ux, uy, tp; ring).
    unfold r2. apply chart_orient3_offset. }
  assert (HoM :
    orient_pts A B M
      = 4 * r2 * (tb - ta) * (tm - ta) * (tm - tb)
          / ((1 + ta * ta) * (1 + tb * tb) * (1 + tm * tm))).
  { rewrite (orient_pts_offsets O).
    replace (px A - px O) with (vx_of ux uy ta) by (rewrite HAx; unfold ux, uy, ta; ring).
    replace (py A - py O) with (vy_of ux uy ta) by (rewrite HAy; unfold ux, uy, ta; ring).
    replace (px B - px O) with (vx_of ux uy tb) by (rewrite HBx; unfold ux, uy, tb; ring).
    replace (py B - py O) with (vy_of ux uy tb) by (rewrite HBy; unfold ux, uy, tb; ring).
    replace (px M - px O) with (vx_of ux uy tm) by (rewrite HMx; unfold ux, uy, tm; ring).
    replace (py M - py O) with (vy_of ux uy tm) by (rewrite HMy; unfold ux, uy, tm; ring).
    unfold r2. apply chart_orient3_offset. }
  assert (HoQ :
    orient_pts A B Q
      = 4 * r2 * (tb - ta) / ((1 + ta * ta) * (1 + tb * tb))).
  { rewrite (orient_pts_offsets O).
    replace (px A - px O) with (vx_of ux uy ta) by (rewrite HAx; unfold ux, uy, ta; ring).
    replace (py A - py O) with (vy_of ux uy ta) by (rewrite HAy; unfold ux, uy, ta; ring).
    replace (px B - px O) with (vx_of ux uy tb) by (rewrite HBx; unfold ux, uy, tb; ring).
    replace (py B - py O) with (vy_of ux uy tb) by (rewrite HBy; unfold ux, uy, tb; ring).
    replace (px Q - px O) with (- ux) by (unfold ux; ring).
    replace (py Q - py O) with (- uy) by (unfold uy; ring).
    unfold r2. apply orient_at_pole_param. }
  set (C := 4 * r2 * (tb - ta) / ((1 + ta * ta) * (1 + tb * tb))).
  assert (Hr2 : 0 < r2) by (unfold r2, ux, uy; exact Hr).
  assert (HC0 : C <> 0).
  { pose proof (one_t2 ta) as Hta. pose proof (one_t2 tb) as Htb.
    assert (Hd : (1 + ta * ta) * (1 + tb * tb) <> 0) by nra.
    unfold C, Rdiv. intros E.
    assert (Hinv : / ((1 + ta * ta) * (1 + tb * tb)) <> 0)
      by (apply Rinv_neq_0_compat; exact Hd).
    apply Rmult_integral in E. destruct E as [En | Ei]; [| contradiction].
    apply Rmult_integral in En. destruct En as [E4 | Et].
    - apply Rmult_integral in E4. destruct E4 as [Efour | Er]; lra.
    - apply Htab. lra. }
  assert (HorientM : orient_pts A B M = C / (1 - k)).
  { assert (E : (1 - k) * orient_pts A B M = C).
    { rewrite <- Hscale. unfold C. exact HoQ. }
    apply (Rmult_eq_reg_l (1 - k)).
    - rewrite E. unfold Rdiv. field. lra.
    - lra. }
  assert (HoPz :
    orient_pts A B P = C * ((tp - ta) * (tp - tb)) / (1 + tp * tp)).
  { rewrite HoA. unfold C.
    pose proof (one_t2 ta) as Hta.
    pose proof (one_t2 tb) as Htb.
    pose proof (one_t2 tp) as Htp.
    field. repeat split; nra. }
  assert (Hprod :
    orient_pts A B M * orient_pts A B P
      = (C * C) / ((1 - k) * (1 + tp * tp)) * ((tp - ta) * (tp - tb))).
  { rewrite HorientM, HoPz.
    pose proof (one_t2 tp) as Htp.
    field. repeat split; nra. }
  assert (Hcoeff : (C * C) / ((1 - k) * (1 + tp * tp)) < 0).
  { pose proof (one_t2 tp) as Htp.
    assert (Hcc : 0 < C * C).
    { pose proof (Rsqr_pos_lt _ HC0) as Hs. unfold Rsqr in Hs. exact Hs. }
    assert (Hden : (1 - k) * (1 + tp * tp) < 0).
    { assert (Eq : (1 - k) * (1 + tp * tp)
                   = - ((k - 1) * (1 + tp * tp))) by ring.
      rewrite Eq. apply Ropp_lt_gt_0_contravar.
      apply Rmult_lt_0_compat; lra. }
    unfold Rdiv.
    assert (Hinv : / ((1 - k) * (1 + tp * tp)) < 0)
      by (apply Rinv_lt_0_compat; exact Hden).
    replace (C * C * / ((1 - k) * (1 + tp * tp)))
      with (- (C * C * - / ((1 - k) * (1 + tp * tp)))) by ring.
    apply Ropp_lt_gt_0_contravar.
    apply Rmult_lt_0_compat.
    - exact Hcc.
    - apply Ropp_gt_lt_0_contravar. exact Hinv. }
  assert (Hside : 0 < orient_pts A B M * orient_pts A B P
                  <-> (tp - ta) * (tp - tb) < 0).
  { rewrite Hprod.
    set (z := (tp - ta) * (tp - tb)).
    set (c := (C * C) / ((1 - k) * (1 + tp * tp))) in *.
    assert (Hcneg : 0 < - c) by lra.
    split; intros Hs.
    - assert (Hw : (- c) * z < 0).
      { replace ((- c) * z) with (- (c * z)) by ring.
        apply Ropp_lt_gt_0_contravar. exact Hs. }
      apply (Rmult_lt_reg_l (- c)).
      + exact Hcneg.
      + replace ((- c) * 0) with 0 by ring. exact Hw.
    - assert (Hw : (- c) * z < 0).
      { assert (0 < - z) by lra.
        assert (Hp : 0 < (- c) * (- z))
          by (apply Rmult_lt_0_compat; assumption).
        replace ((- c) * z) with (- ((- c) * (- z))) by ring.
        apply Ropp_lt_gt_0_contravar. exact Hp. }
      replace (c * z) with (- ((- c) * z)) by ring.
      apply Ropp_0_gt_lt_contravar. exact Hw. }
  assert (HendA : tp = ta <-> P = A).
  { split; intro E.
    - apply Point_eq_of_coords.
      + rewrite HPx, HAx. unfold tp, ta in E. rewrite E. reflexivity.
      + rewrite HPy, HAy. unfold tp, ta in E. rewrite E. reflexivity.
    - unfold tp, ta. rewrite E. reflexivity. }
  assert (HendB : tp = tb <-> P = B).
  { split; intro E.
    - apply Point_eq_of_coords.
      + rewrite HPx, HBx. unfold tp, tb in E. rewrite E. reflexivity.
      + rewrite HPy, HBy. unfold tp, tb in E. rewrite E. reflexivity.
    - unfold tp, tb. rewrite E. reflexivity. }
  unfold arc_member_AB_M, in_chart_interval.
  split.
  - intros [Hsame | [HEA | HEB]].
    + apply Rlt_le. apply (proj1 Hside). exact Hsame.
    + replace tp with ta by (symmetry; apply (proj2 HendA); exact HEA).
      replace ((ta - ta) * (ta - tb)) with 0 by ring. apply Rle_refl.
    + replace tp with tb by (symmetry; apply (proj2 HendB); exact HEB).
      replace ((tb - ta) * (tb - tb)) with 0 by ring. apply Rle_refl.
  - intro Hint.
    destruct (Rle_lt_or_eq _ _ Hint) as [Hlt | Heq].
    + left. apply (proj2 Hside). exact Hlt.
    + apply Rmult_integral in Heq. destruct Heq as [Ea | Eb].
      * right. left. apply (proj1 HendA). lra.
      * right. right. apply (proj1 HendB). lra.
Qed.

Definition arc_pole (a : CircularArc) : Point :=
  pole_point (arc_center a) (arc_mid a) (midpoint (arc_start a) (arc_end a)).

Definition arc_tau (a : CircularArc) (P : Point) : R :=
  tau_pt (arc_center a) (arc_pole a) P.

Lemma valid_arc_orient_ne : forall a,
  valid_arc a -> orient_pts (arc_start a) (arc_end a) (arc_mid a) <> 0.
Proof.
  intros a H.
  unfold valid_arc in H. cbn zeta in H.
  unfold orient_pts, orient3, crs.
  intro E. apply H. lra.
Qed.

Lemma valid_arc_ends_distinct : forall a,
  valid_arc a -> arc_start a <> arc_end a.
Proof.
  intros a H E.
  apply H. rewrite E. unfold valid_arc. cbn zeta. ring.
Qed.

Theorem arc_span_contains_iff_tau : forall (a : CircularArc) (P : Point),
  valid_arc a ->
  dist_sq (arc_center a) P = dist_sq (arc_center a) (arc_start a) ->
  P <> arc_pole a ->
  arc_span_contains a P <->
  in_chart_interval (arc_tau a (arc_start a))
                    (arc_tau a (arc_end a))
                    (arc_tau a P).
Proof.
  intros a P Hva Hcirc Hne.
  set (O := arc_center a).
  set (A := arc_start a).
  set (B := arc_end a).
  set (M := arc_mid a).
  destruct (arc_center_equidistant a Hva) as [Hsm Hse].
  assert (Hmem :=
    arc_member_iff_tau_interval O A B M P
      Hsm
      (eq_trans (eq_sym Hse) Hsm)
      (eq_trans Hcirc Hsm)
      (valid_arc_ends_distinct a Hva)
      (valid_arc_orient_ne a Hva)).
  assert (Hne' : P <> pole_point O M (midpoint A B)).
  { unfold arc_pole in Hne. unfold O, A, B, M. exact Hne. }
  specialize (Hmem Hne').
  assert (Hsp : arc_span_contains a P <-> arc_member_AB_M A B M P).
  { unfold arc_span_contains, arc_interior_side, arc_member_AB_M, A, B, M.
    rewrite !arc_side_eq_orient. reflexivity. }
  rewrite Hsp.
  unfold arc_tau, arc_pole, O, A, B, M in *.
  exact Hmem.
Qed.

Print Assumptions chart_on_circle.
Print Assumptions chart_left_inv.
Print Assumptions chart_right_inv.
Print Assumptions pole_on_circle.
Print Assumptions chart_orient3.
Print Assumptions pole_opposite_M.
Print Assumptions tau_monotone_off_pole.
Print Assumptions arc_member_iff_tau_interval.
Print Assumptions arc_span_contains_iff_tau.
