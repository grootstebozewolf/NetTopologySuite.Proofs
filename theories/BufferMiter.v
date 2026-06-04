(* ============================================================================
   NetTopologySuite.Proofs.BufferMiter
   ----------------------------------------------------------------------------
   Buffer/noder pipeline, Stage 2b seam: MITER-JOIN APEX GEOMETRY.

   Continues the join work of theories/BufferJoin.v (round joins) with the
   *miter* join (see docs/buffer-noder-pipeline.md §2.2, slice S3;
   JTS#180 "Buffer with mitre join is incorrect due to short input
   segment").

   At a corner vertex V between two edges of direction `u` and `w`, the
   two parallel offset lines (each at perpendicular distance d from its
   edge) meet at the *miter apex*.  Solving the 2x2 system "perpendicular
   distance d from both edge lines" by Cramer's rule gives an explicit
   apex point `miter_apex V u w d`, well-defined whenever the edges are
   not parallel (`miter_det u w <> 0`).

   The soundness facts proven (the defining property of the miter apex):

     - `miter_apex_perp_dist_u` : the apex is at signed perpendicular
       distance exactly d from the FIRST edge's line.
     - `miter_apex_perp_dist_w` : ... and from the SECOND edge's line.

   So the apex lies on BOTH offset lines -- it is exactly their
   intersection.  The proofs are pure algebra: `vmag u` and `vmag w` stay
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

(* The 2x2 determinant of the offset-line system; equals vcross u w. *)
Definition miter_det (u w : Vec) : R := vx u * vy w - vy u * vx w.

(* The miter apex relative to the corner vertex V: the unique point at
   signed perpendicular distance d from both edge lines, obtained by
   Cramer's rule on
       vcross u (M - V) = d * |u|,
       vcross w (M - V) = d * |w|.
   Well-defined when miter_det u w <> 0 (edges not parallel). *)
Definition miter_apex (V : Point) (u w : Vec) (d : R) : Point :=
  mkPoint
    (px V + d * (vmag u * vx w - vmag w * vx u) / miter_det u w)
    (py V + d * (vmag u * vy w - vmag w * vy u) / miter_det u w).

(* -------------------------------------------------------------------------- *)
(* §2  Soundness: the apex is at perpendicular distance d from both lines.    *)
(* -------------------------------------------------------------------------- *)

Lemma miter_apex_perp_dist_u : forall V u w d,
  u <> vzero ->
  miter_det u w <> 0 ->
  signed_perp_dist V u (miter_apex V u w d) = d.
Proof.
  intros V u w d Hu Hdet.
  assert (Hmu : vmag u <> 0)
    by (unfold vmag; apply Rgt_not_eq; apply sqrt_lt_R0; apply vmag_sq_pos; exact Hu).
  unfold miter_det in Hdet.
  unfold signed_perp_dist, miter_apex, miter_det, vcross. simpl.
  field_simplify_eq; try ring; try (split; assumption).
Qed.

Lemma miter_apex_perp_dist_w : forall V u w d,
  w <> vzero ->
  miter_det u w <> 0 ->
  signed_perp_dist V w (miter_apex V u w d) = d.
Proof.
  intros V u w d Hw Hdet.
  assert (Hmw : vmag w <> 0)
    by (unfold vmag; apply Rgt_not_eq; apply sqrt_lt_R0; apply vmag_sq_pos; exact Hw).
  unfold miter_det in Hdet.
  unfold signed_perp_dist, miter_apex, miter_det, vcross. simpl.
  field_simplify_eq; try ring; try (split; assumption).
Qed.

(* -------------------------------------------------------------------------- *)
(* §2.5  Miter length and the miter-limit cap (JTS#180 decision).             *)
(* -------------------------------------------------------------------------- *)

(* Exact squared miter length, cleared of the determinant denominator:
   |V->apex|^2 * det^2 = d^2 * ((|u| w - |w| u) cross-free squared norm).
   Carrying det^2 on the left keeps this a pure polynomial identity in the
   opaque atoms vmag u, vmag w (no sqrt expansion needed). *)
Theorem miter_length_sq : forall V u w d,
  miter_det u w <> 0 ->
  dist_sq V (miter_apex V u w d) * (miter_det u w) ^ 2
  = d ^ 2 * ((vmag u * vx w - vmag w * vx u) ^ 2
             + (vmag u * vy w - vmag w * vy u) ^ 2).
Proof.
  intros V u w d Hdet.
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
Theorem miter_within_limit_iff : forall V u w d L,
  miter_det u w <> 0 ->
  0 < d ->
  dist_sq V (miter_apex V u w d) <= (L * d) ^ 2
  <-> (vmag u * vx w - vmag w * vx u) ^ 2 + (vmag u * vy w - vmag w * vy u) ^ 2
      <= L ^ 2 * (miter_det u w) ^ 2.
Proof.
  intros V u w d L Hdet Hd.
  pose proof (miter_length_sq V u w d Hdet) as Hlen.
  assert (Hd2 : 0 < d ^ 2) by nra.
  assert (Hdet2 : 0 < (miter_det u w) ^ 2).
  { assert (miter_det u w <> 0) by exact Hdet. nra. }
  set (N := (vmag u * vx w - vmag w * vx u) ^ 2
            + (vmag u * vy w - vmag w * vy u) ^ 2) in *.
  split.
  - intro Hle.
    (* dist_sq <= L^2 d^2  scaled by det^2:  d^2 * N <= L^2 d^2 det^2 *)
    apply Rmult_le_compat_r with (r := (miter_det u w) ^ 2) in Hle;
      [ | nra ].
    rewrite Hlen in Hle.
    (* d^2 * N <= (L*d)^2 * det^2 = L^2 det^2 * d^2 ; cancel d^2 > 0 *)
    apply Rmult_le_reg_l with (r := d ^ 2); [ exact Hd2 | nra ].
  - intro Hle.
    (* N <= L^2 det^2  scaled by d^2:  d^2 N <= L^2 d^2 det^2 = (L d)^2 det^2 *)
    apply Rmult_le_reg_r with (r := (miter_det u w) ^ 2); [ exact Hdet2 | ].
    rewrite Hlen. nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The apex lies on both offset lines simultaneously (restatement).       *)
(* -------------------------------------------------------------------------- *)

(* Packaging §2: the miter apex is the common point of the two offset
   lines -- exactly their intersection at offset distance d. *)
Theorem miter_apex_on_both_offsets : forall V u w d,
  u <> vzero -> w <> vzero -> miter_det u w <> 0 ->
  signed_perp_dist V u (miter_apex V u w d) = d /\
  signed_perp_dist V w (miter_apex V u w d) = d.
Proof.
  intros V u w d Hu Hw Hdet. split.
  - apply miter_apex_perp_dist_u; assumption.
  - apply miter_apex_perp_dist_w; assumption.
Qed.
