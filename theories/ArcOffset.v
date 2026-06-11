(* ============================================================================
   NetTopologySuite.Proofs.ArcOffset
   ----------------------------------------------------------------------------
   Buffer/noder pipeline, Stage 2a-CURVE seam: ARC OFFSET SOUNDNESS
   (parallel curve of a circular arc).

   Issue #65 (curve-aware buffer, BUF-* producing CurvePolygon output),
   first proof brick, unblocked by issue #64's arc-line closure.  The
   linear analogue is `BufferOffset.v` (offset segment = source edge
   translated along the unit normal); here the curved analogue: the
   offset of a circular arc at signed distance `d` is the CONCENTRIC arc
   of radius `r + d` (`d > 0` outward, `d < 0` inward), cf.
   `docs/buffer-noder-pipeline.md` §2.2.

   An arc is taken in center/radius/angle form: `circle_point C rho theta`
   is the point of the radius-`rho` circle about `C` at polar angle
   `theta`.  (The SQL/MM three-point `CurveGeometry.CircularArc` reduces
   to this form via `arc_center` / `arc_radius`; the bridge is left to
   the consumer, as the soundness facts below are statements about the
   circle itself.)

   Mirroring `BufferOffset.v`'s two soundness facts, plus the curve-only
   singularity phenomena a correct curve-aware buffer must respect:

     1. AT DISTANCE d.
        - `arc_offset_radial_dist`: the offset point at angle `theta` is
          at Euclidean distance `|d|` from the source point at the same
          angle.
        - `arc_offset_dist_exact` (headline): for `0 <= r`, `-r <= d`,
          `|d|` is moreover the distance from the offset point to the
          ENTIRE source circle -- every circle point is at distance
          `>= |d|` (reverse triangle inequality through the center) and
          the radial correspondent attains it.  This is the defining
          property of a parallel curve at distance `d`.

     2. PARALLEL (no kink).
        - `circle_point_{x,y}_deriv`: the parametrisation's tangent
          vector at angle `theta` is `circle_tangent rho theta
          = rho * (-sin theta, cos theta)` (genuine `derivable_pt_lim`
          derivatives, not a decreed definition).
        - `arc_offset_tangent_parallel` / `arc_offset_no_kink`: source
          and offset tangents are parallel (`vcross = 0`), and for
          `0 < r`, `0 < r + d` the offset tangent is a POSITIVE scalar
          multiple of the source tangent -- offsetting cannot rotate or
          reverse the direction of travel.  This is the curved version
          of `BufferOffset.offset_seg_dir`, whose failure produces the
          kinked linework of JTS#739 / JTS#180.

     3. SINGULARITY (inner offset past the center; the `r + d < 0`
        regime behind inverted negative buffers on arcs, issue #65).
        - `arc_offset_tangent_dot` / `arc_offset_tangent_reverses_past_singularity`:
          tangent dot product is exactly `r * (r + d)`, so past the
          singularity the direction of travel REVERSES (cusp + inversion).
        - `inner_offset_past_center_not_at_distance`: concrete witness
          (r = 1, d = -3) that for `d < -r` the "offset" point is NOT at
          distance `|d|` from the circle -- the parallel-curve property
          itself fails, so emitting `circle_point C (r+d)` as a buffer
          boundary there is unsound, not merely inverted.

     4. LENGTH (M-LEN bridge).
        - `arc_offset_length`: the offset arc's `ArcLength.arc_length`
          over the same sweep is `arc_length r theta + d * theta`.

   Pure-R; THREE-AXIOM THROUGHOUT (classical-reals trio) -- including
   the two derivative bridges via Stdlib `Rtrigo_reg`
   (`derivable_pt_lim_{sin,cos}`), which, unlike `atan`/`sin_lt_x`, do
   not pull `Classical_Prop.classic`.  See the `Print Assumptions`
   block at the foot of the file.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From Stdlib Require Import Ranalysis1 Rtrigo_reg.
From NTS.Proofs Require Import Distance Vec Linearise ArcLength.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Concentric parametrisation.                                            *)
(* -------------------------------------------------------------------------- *)

(* The point of the radius-`rho` circle about `C` at polar angle `theta`.    *)
Definition circle_point (C : Point) (rho theta : R) : Point :=
  mkPoint (px C + rho * cos theta) (py C + rho * sin theta).

(* The offset curve of the radius-`r` arc at signed distance `d` is the      *)
(* concentric radius-(r+d) parametrisation; this is definitional, and the    *)
(* theorems below are what make it the CORRECT definition.                   *)
Definition arc_offset_point (C : Point) (r d theta : R) : Point :=
  circle_point C (r + d) theta.

Lemma dist_sq_circle_point : forall C rho theta,
  dist_sq C (circle_point C rho theta) = rho * rho.
Proof.
  intros C rho theta. unfold dist_sq, circle_point. simpl.
  replace ((px C - (px C + rho * cos theta)) * (px C - (px C + rho * cos theta)) +
           (py C - (py C + rho * sin theta)) * (py C - (py C + rho * sin theta)))
    with (rho * rho * (Rsqr (sin theta) + Rsqr (cos theta)))
    by (unfold Rsqr; ring).
  rewrite sin2_cos2. ring.
Qed.

(* `circle_point` really lies on the circle: distance to center = |rho|.     *)
Lemma circle_point_center_dist : forall C rho theta,
  dist C (circle_point C rho theta) = Rabs rho.
Proof.
  intros C rho theta. unfold dist. rewrite dist_sq_circle_point.
  replace (rho * rho) with (Rsqr rho) by (unfold Rsqr; ring).
  apply sqrt_Rsqr_abs.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  AT DISTANCE d, pointwise: radial correspondents are |d| apart.        *)
(* -------------------------------------------------------------------------- *)

Lemma dist_sq_circle_point_radial : forall C rho1 rho2 theta,
  dist_sq (circle_point C rho1 theta) (circle_point C rho2 theta) =
  (rho2 - rho1) * (rho2 - rho1).
Proof.
  intros C rho1 rho2 theta. unfold dist_sq, circle_point. simpl.
  replace ((px C + rho1 * cos theta - (px C + rho2 * cos theta)) *
           (px C + rho1 * cos theta - (px C + rho2 * cos theta)) +
           (py C + rho1 * sin theta - (py C + rho2 * sin theta)) *
           (py C + rho1 * sin theta - (py C + rho2 * sin theta)))
    with ((rho2 - rho1) * (rho2 - rho1) * (Rsqr (sin theta) + Rsqr (cos theta)))
    by (unfold Rsqr; ring).
  rewrite sin2_cos2. ring.
Qed.

Theorem arc_offset_radial_dist : forall C r d theta,
  dist (circle_point C r theta) (arc_offset_point C r d theta) = Rabs d.
Proof.
  intros C r d theta. unfold arc_offset_point, dist.
  rewrite dist_sq_circle_point_radial.
  replace ((r + d - r) * (r + d - r)) with (Rsqr d) by (unfold Rsqr; ring).
  apply sqrt_Rsqr_abs.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  AT DISTANCE d, globally: |d| is the distance to the WHOLE circle.     *)
(*                                                                            *)
(* Lower bound: reverse triangle inequality through the center C.  For any   *)
(* X with dist C X = r and Q the offset point (dist C Q = r + d >= 0):       *)
(*    d <= dist Q X   (from  dist C Q <= dist C X + dist X Q)                *)
(*   -d <= dist Q X   (from  dist C X <= dist C Q + dist Q X)                *)
(* The radial correspondent (§2) attains |d|, so the infimum IS |d|: the     *)
(* offset curve is genuinely "at distance d" from the source circle.        *)
(* -------------------------------------------------------------------------- *)

Theorem arc_offset_dist_lower : forall C r d theta X,
  0 <= r -> - r <= d ->
  dist C X = r ->
  Rabs d <= dist (arc_offset_point C r d theta) X.
Proof.
  intros C r d theta X Hr Hd HX.
  set (Q := arc_offset_point C r d theta).
  assert (HQ : dist C Q = r + d).
  { unfold Q, arc_offset_point. rewrite circle_point_center_dist.
    apply Rabs_right. lra. }
  pose proof (dist_triangle C X Q) as T1.   (* dist C Q <= dist C X + dist X Q *)
  pose proof (dist_triangle C Q X) as T2.   (* dist C X <= dist C Q + dist Q X *)
  rewrite (dist_sym X Q) in T1.
  rewrite HQ, HX in T1, T2.
  apply Rabs_le. lra.
Qed.

(* Headline: the offset point's distance to the source circle is EXACTLY    *)
(* |d| -- lower-bounded over the whole circle, attained at the radial        *)
(* correspondent.  The defining property of a parallel curve at distance d, *)
(* valid up to (and including) the singularity d = -r.                       *)
Theorem arc_offset_dist_exact : forall C r d theta,
  0 <= r -> - r <= d ->
  (forall X, dist C X = r -> Rabs d <= dist (arc_offset_point C r d theta) X) /\
  (dist C (circle_point C r theta) = r /\
   dist (arc_offset_point C r d theta) (circle_point C r theta) = Rabs d).
Proof.
  intros C r d theta Hr Hd.
  split; [ | split ].
  - intros X HX. apply arc_offset_dist_lower; assumption.
  - rewrite circle_point_center_dist. apply Rabs_right. lra.
  - rewrite dist_sym. apply arc_offset_radial_dist.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  SINGULARITY: past the center (d < -r) the parallel-curve property     *)
(* FAILS -- concrete witness.  r = 1, d = -3, C = origin, theta = 0: the     *)
(* "offset" point is (-2,0); the circle point (-1,0) is at distance 1 < 3.   *)
(* A buffer emitting circle_point C (r+d) beyond the singularity does not    *)
(* produce linework at distance |d| (the inverted-negative-buffer artifact   *)
(* class of issue #65).                                                       *)
(* -------------------------------------------------------------------------- *)

Theorem inner_offset_past_center_not_at_distance :
  exists (C X : Point) (r d theta : R),
    0 <= r /\ d < - r /\ dist C X = r /\
    dist (arc_offset_point C r d theta) X < Rabs d.
Proof.
  exists (mkPoint 0 0), (mkPoint (-1) 0), 1, (-3), 0.
  repeat split.
  - lra.
  - lra.
  - (* dist (0,0) (-1,0) = 1 *)
    unfold dist, dist_sq. simpl.
    replace ((0 - -1) * (0 - -1) + (0 - 0) * (0 - 0)) with 1 by ring.
    apply sqrt_1.
  - (* offset point = (-2,0); dist to (-1,0) is 1 < |-3| = 3 *)
    unfold arc_offset_point, circle_point, dist, dist_sq. simpl.
    rewrite cos_0, sin_0.
    replace ((0 + (1 + -3) * 1 - -1) * (0 + (1 + -3) * 1 - -1) +
             (0 + (1 + -3) * 0 - 0) * (0 + (1 + -3) * 0 - 0)) with 1 by ring.
    rewrite sqrt_1.
    rewrite Rabs_left by lra. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  PARALLEL: tangent vectors.                                             *)
(*                                                                            *)
(* The tangent of theta |-> circle_point C rho theta, established as a real  *)
(* derivative of each coordinate (Stdlib derivable_pt_lim), not decreed.     *)
(* -------------------------------------------------------------------------- *)

Definition circle_tangent (rho theta : R) : Vec :=
  vscale rho (mkVec (- sin theta) (cos theta)).

Lemma circle_point_x_deriv : forall C rho theta,
  derivable_pt_lim (fun t => px (circle_point C rho t)) theta
                   (vx (circle_tangent rho theta)).
Proof.
  intros C rho theta.
  assert (D : derivable_pt_lim
                (plus_fct (fct_cte (px C)) (mult_real_fct rho cos))
                theta (0 + rho * (- sin theta))).
  { apply derivable_pt_lim_plus.
    - apply derivable_pt_lim_const.
    - apply derivable_pt_lim_scal. apply derivable_pt_lim_cos. }
  replace (vx (circle_tangent rho theta)) with (0 + rho * (- sin theta))
    by (unfold circle_tangent, vscale; simpl; ring).
  exact D.
Qed.

Lemma circle_point_y_deriv : forall C rho theta,
  derivable_pt_lim (fun t => py (circle_point C rho t)) theta
                   (vy (circle_tangent rho theta)).
Proof.
  intros C rho theta.
  assert (D : derivable_pt_lim
                (plus_fct (fct_cte (py C)) (mult_real_fct rho sin))
                theta (0 + rho * cos theta)).
  { apply derivable_pt_lim_plus.
    - apply derivable_pt_lim_const.
    - apply derivable_pt_lim_scal. apply derivable_pt_lim_sin. }
  replace (vy (circle_tangent rho theta)) with (0 + rho * cos theta)
    by (unfold circle_tangent, vscale; simpl; ring).
  exact D.
Qed.

(* Source and offset tangents are parallel at every angle.                   *)
Theorem arc_offset_tangent_parallel : forall r d theta,
  vcross (circle_tangent r theta) (circle_tangent (r + d) theta) = 0.
Proof.
  intros r d theta. unfold circle_tangent, vcross, vscale. simpl. ring.
Qed.

(* The tangent dot product is exactly r * (r + d): positive (same direction  *)
(* of travel) strictly before the singularity, zero at it, NEGATIVE past it. *)
Theorem arc_offset_tangent_dot : forall r d theta,
  vdot (circle_tangent r theta) (circle_tangent (r + d) theta) = r * (r + d).
Proof.
  intros r d theta. unfold circle_tangent, vdot, vscale. simpl.
  replace (r * - sin theta * ((r + d) * - sin theta) +
           r * cos theta * ((r + d) * cos theta))
    with (r * (r + d) * (Rsqr (sin theta) + Rsqr (cos theta)))
    by (unfold Rsqr; ring).
  rewrite sin2_cos2. ring.
Qed.

(* No kink, quantitatively: before the singularity the offset tangent is a   *)
(* POSITIVE scalar multiple of the source tangent.  Offsetting cannot rotate *)
(* or reverse the direction of travel (curved analogue of                    *)
(* BufferOffset.offset_seg_dir).                                              *)
Theorem arc_offset_no_kink : forall r d theta,
  0 < r -> 0 < r + d ->
  circle_tangent (r + d) theta = vscale ((r + d) / r) (circle_tangent r theta)
  /\ 0 < (r + d) / r.
Proof.
  intros r d theta Hr Hrd. split.
  - unfold circle_tangent, vscale. apply Vec_eq; simpl; field; lra.
  - apply Rdiv_lt_0_compat; lra.
Qed.

(* Past the singularity the direction of travel REVERSES (the cusp +         *)
(* inversion behind inside-out negative arc buffers).                         *)
Corollary arc_offset_tangent_reverses_past_singularity : forall r d theta,
  0 < r -> r + d < 0 ->
  vdot (circle_tangent r theta) (circle_tangent (r + d) theta) < 0.
Proof.
  intros r d theta Hr Hrd. rewrite arc_offset_tangent_dot. nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  LENGTH: the offset arc's length over the same sweep (M-LEN bridge).   *)
(* -------------------------------------------------------------------------- *)

Theorem arc_offset_length : forall r d theta,
  arc_length (r + d) theta = arc_length r theta + d * theta.
Proof.
  intros r d theta. unfold arc_length. ring.
Qed.

(* ========================================================================== *)
(* Axiom audit.  ALL headlines below are 3-axiom (classical-reals trio:      *)
(* sig_not_dec, sig_forall_dec, functional_extensionality_dep) -- including  *)
(* the derivative bridges, whose Rtrigo_reg dependencies stay classic-free.  *)
(* ========================================================================== *)

Print Assumptions arc_offset_radial_dist.
Print Assumptions arc_offset_dist_exact.
Print Assumptions inner_offset_past_center_not_at_distance.
Print Assumptions circle_point_x_deriv.
Print Assumptions circle_point_y_deriv.
Print Assumptions arc_offset_tangent_parallel.
Print Assumptions arc_offset_tangent_dot.
Print Assumptions arc_offset_no_kink.
Print Assumptions arc_offset_tangent_reverses_past_singularity.
Print Assumptions arc_offset_length.
