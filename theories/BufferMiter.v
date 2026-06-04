(* ============================================================================
   NetTopologySuite.Proofs.BufferMiter
   ----------------------------------------------------------------------------
   Buffer/noder pipeline, Stage 2b seam: MITER-JOIN APEX GEOMETRY.

   Continues the join work of theories/BufferJoin.v (round joins) with the
   *miter* join (see docs/buffer-noder-pipeline.md §2.2, slice S3;
   JTS#180 "Buffer with mitre join is incorrect due to short input
   segment").

   At a corner vertex V between two edges of direction `ein` and `eout`, the
   two parallel offset lines (each at perpendicular distance d from its
   edge) meet at the *miter apex*.  Solving the 2x2 system "perpendicular
   distance d from both edge lines" by Cramer's rule gives an explicit
   apex point `miter_apex V ein eout d`, well-defined whenever the edges are
   not parallel (`miter_det ein eout <> 0`).

   The soundness facts proven (the defining property of the miter apex):

     - `miter_apex_perp_dist_in` : the apex is at signed perpendicular
       distance exactly d from the FIRST edge's line.
     - `miter_apex_perp_dist_out` : ... and from the SECOND edge's line.

   So the apex lies on BOTH offset lines -- it is exactly their
   intersection.  The proofs are pure algebra: `vmag ein` and `vmag eout` stay
   opaque positive atoms (no square-root expansion), and the Cramer
   determinant cancels.  Pure-R, three-axiom footprint (no `atan`, no
   Flocq, no `Classical_Prop.classic`).  No `Admitted` / `Axiom` /
   `Parameter`.

   Also proven: `miter_length_sq` (the exact squared miter length, cleared
   of the determinant denominator) and `miter_within_limit_iff` (the
   division-free, square-root-free miter-limit decision: the apex is within
   cap L*d iff the determinant-scaled offset numerator is within
   L^2*det^2 -- the test JTS's BufferParameters miter limit makes).  The
   remaining link is the soundness of the cap value L against the corner
   half-angle (`Azimuth.miter_ratio_le_iff`), noted in the design doc.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.8)
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Real Vec Distance BufferOffset.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The miter apex (Cramer's-rule intersection of the two offset lines).   *)
(* -------------------------------------------------------------------------- *)

(* The 2x2 determinant of the offset-line system; equals vcross ein eout. *)
Definition miter_det (ein eout : Vec) : R := vx ein * vy eout - vy ein * vx eout.

(* The miter apex relative to the corner vertex V: the unique point at
   signed perpendicular distance d from both edge lines, obtained by
   Cramer's rule on
       vcross ein (M - V) = d * |ein|,
       vcross eout (M - V) = d * |eout|.
   Well-defined when miter_det ein eout <> 0 (edges not parallel). *)
Definition miter_apex (V : Point) (ein eout : Vec) (d : R) : Point :=
  mkPoint
    (px V + d * (vmag ein * vx eout - vmag eout * vx ein) / miter_det ein eout)
    (py V + d * (vmag ein * vy eout - vmag eout * vy ein) / miter_det ein eout).

(* -------------------------------------------------------------------------- *)
(* §2  Soundness: the apex is at perpendicular distance d from both lines.    *)
(* -------------------------------------------------------------------------- *)

Lemma miter_apex_perp_dist_in : forall V ein eout d,
  ein <> vzero ->
  miter_det ein eout <> 0 ->
  signed_perp_dist V ein (miter_apex V ein eout d) = d.
Proof.
  intros V ein eout d Hin Hdet.
  assert (Hmu : vmag ein <> 0)
    by (unfold vmag; apply Rgt_not_eq; apply sqrt_lt_R0; apply vmag_sq_pos; exact Hin).
  unfold miter_det in Hdet.
  unfold signed_perp_dist, miter_apex, miter_det, vcross. simpl.
  field_simplify_eq; try ring; try (split; assumption).
Qed.

Lemma miter_apex_perp_dist_out : forall V ein eout d,
  eout <> vzero ->
  miter_det ein eout <> 0 ->
  signed_perp_dist V eout (miter_apex V ein eout d) = d.
Proof.
  intros V ein eout d Hout Hdet.
  assert (Hmw : vmag eout <> 0)
    by (unfold vmag; apply Rgt_not_eq; apply sqrt_lt_R0; apply vmag_sq_pos; exact Hout).
  unfold miter_det in Hdet.
  unfold signed_perp_dist, miter_apex, miter_det, vcross. simpl.
  field_simplify_eq; try ring; try (split; assumption).
Qed.

(* -------------------------------------------------------------------------- *)
(* §2.5  Miter length and the miter-limit cap (JTS#180 decision).             *)
(* -------------------------------------------------------------------------- *)

(* Exact squared miter length, cleared of the determinant denominator:
   |V->apex|^2 * det^2 = d^2 * ((|ein| eout - |eout| ein) cross-free squared norm).
   Carrying det^2 on the left keeps this a pure polynomial identity in the
   opaque atoms vmag ein, vmag eout (no sqrt expansion needed). *)
Theorem miter_length_sq : forall V ein eout d,
  miter_det ein eout <> 0 ->
  dist_sq V (miter_apex V ein eout d) * (miter_det ein eout) ^ 2
  = d ^ 2 * ((vmag ein * vx eout - vmag eout * vx ein) ^ 2
             + (vmag ein * vy eout - vmag eout * vy ein) ^ 2).
Proof.
  intros V ein eout d Hdet.
  unfold dist_sq, miter_apex. simpl.
  field_simplify_eq; [ ring | exact Hdet ].
Qed.

(* The miter-limit decision, exactly.  For a positive buffer distance, the
   miter apex is within the cap L*d of the corner iff the determinant-scaled
   squared offset numerator is within L^2 * det^2.  This is the
   division-free, square-root-free form of "miter ratio <= L" that
   JTS's BufferParameters miter-limit test decides.  (Soundness of the cap
   value L vs the half-angle is the remaining link to
   Azimuth.miter_ratio_le_iff.) *)
Theorem miter_within_limit_iff : forall V ein eout d L,
  miter_det ein eout <> 0 ->
  0 < d ->
  dist_sq V (miter_apex V ein eout d) <= (L * d) ^ 2
  <-> (vmag ein * vx eout - vmag eout * vx ein) ^ 2 + (vmag ein * vy eout - vmag eout * vy ein) ^ 2
      <= L ^ 2 * (miter_det ein eout) ^ 2.
Proof.
  intros V ein eout d L Hdet Hd.
  pose proof (miter_length_sq V ein eout d Hdet) as Hlen.
  assert (Hd2 : 0 < d ^ 2) by nra.
  assert (Hdet2 : 0 < (miter_det ein eout) ^ 2).
  { assert (miter_det ein eout <> 0) by exact Hdet. nra. }
  set (N := (vmag ein * vx eout - vmag eout * vx ein) ^ 2
            + (vmag ein * vy eout - vmag eout * vy ein) ^ 2) in *.
  split.
  - intro Hle.
    (* dist_sq <= L^2 d^2  scaled by det^2:  d^2 * N <= L^2 d^2 det^2 *)
    apply Rmult_le_compat_r with (r := (miter_det ein eout) ^ 2) in Hle;
      [ | nra ].
    rewrite Hlen in Hle.
    (* d^2 * N <= (L*d)^2 * det^2 = L^2 det^2 * d^2 ; cancel d^2 > 0 *)
    apply Rmult_le_reg_l with (r := d ^ 2); [ exact Hd2 | nra ].
  - intro Hle.
    (* N <= L^2 det^2  scaled by d^2:  d^2 N <= L^2 d^2 det^2 = (L d)^2 det^2 *)
    apply Rmult_le_reg_r with (r := (miter_det ein eout) ^ 2); [ exact Hdet2 | ].
    rewrite Hlen. nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2.6  Law-of-cosines form (trig-free half-angle soundness).                *)
(*                                                                            *)
(* Rewriting the determinant and the offset numerator in terms of dot/cross  *)
(* products exposes the classical miter law:                                 *)
(*    |V->apex|^2 / d^2 = 2|ein||eout| / (|ein||eout| + <ein,eout>)                          *)
(* (i.e. sec^2 of the half-turn).  Both pieces below are pure-R, three-axiom; *)
(* the explicit trig (cos theta = <ein,eout>/(|ein||eout|)) is the Azimuth link, done   *)
(* separately so this file stays classic-free.                               *)
(* -------------------------------------------------------------------------- *)

(* |v|^2 = vmag_sq v (vmag squared is the squared magnitude).  Unconditional. *)
Lemma vmag_sq_eq : forall v, vmag v * vmag v = vmag_sq v.
Proof. intros v. unfold vmag. apply sqrt_sqrt. apply vmag_sq_nonneg. Qed.

(* The determinant is the cross product, so by Lagrange its square is
   |ein|^2|eout|^2 - <ein,eout>^2.  Pure ring identity. *)
Lemma miter_det_sq_lagrange : forall ein eout,
  (miter_det ein eout) ^ 2 = vmag_sq ein * vmag_sq eout - (vdot ein eout) ^ 2.
Proof.
  intros ein eout. unfold miter_det, vmag_sq, vdot. ring.
Qed.

(* The offset numerator in dot-product (law-of-cosines) form:
   N = 2|ein|^2|eout|^2 - 2|ein||eout|<ein,eout>. *)
Lemma miter_numerator_cos : forall ein eout,
  (vmag ein * vx eout - vmag eout * vx ein) ^ 2 + (vmag ein * vy eout - vmag eout * vy ein) ^ 2
  = 2 * vmag_sq ein * vmag_sq eout - 2 * (vmag ein * vmag eout) * vdot ein eout.
Proof.
  intros ein eout.
  pose proof (vmag_sq_eq ein) as HU. pose proof (vmag_sq_eq eout) as HW.
  unfold vmag_sq, vdot in *. nra.
Qed.

(* Combining: the law-of-cosines miter-length identity, fully in dot/cross
   products (cleared of denominators).  This is the geometric soundness of
   the miter ratio -- it is exactly |V->apex|^2 expressed via the corner's
   |ein|, |eout| and <ein,eout>. *)
Theorem miter_length_sq_cos : forall V ein eout d,
  miter_det ein eout <> 0 ->
  dist_sq V (miter_apex V ein eout d) * (vmag_sq ein * vmag_sq eout - (vdot ein eout) ^ 2)
  = d ^ 2 * (2 * vmag_sq ein * vmag_sq eout - 2 * (vmag ein * vmag eout) * vdot ein eout).
Proof.
  intros V ein eout d Hdet.
  rewrite <- miter_det_sq_lagrange, <- miter_numerator_cos.
  apply miter_length_sq. exact Hdet.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The apex lies on both offset lines simultaneously (restatement).       *)
(* -------------------------------------------------------------------------- *)

(* Packaging §2: the miter apex is the common point of the two offset
   lines -- exactly their intersection at offset distance d. *)
Theorem miter_apex_on_both_offsets : forall V ein eout d,
  ein <> vzero -> eout <> vzero -> miter_det ein eout <> 0 ->
  signed_perp_dist V ein (miter_apex V ein eout d) = d /\
  signed_perp_dist V eout (miter_apex V ein eout d) = d.
Proof.
  intros V ein eout d Hin Hout Hdet. split.
  - apply miter_apex_perp_dist_in; assumption.
  - apply miter_apex_perp_dist_out; assumption.
Qed.
