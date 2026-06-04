(* ============================================================================
   NetTopologySuite.Proofs.BufferBevel
   ----------------------------------------------------------------------------
   Buffer/noder pipeline, Stage 2b seam: BEVEL-JOIN CHORD.
   (Seam map: docs/buffer-noder-pipeline.md §2.2 "2b joins" / §6 slice S3.)

   Completes the join trio of the buffer front-end (round join =
   theories/BufferJoin.v, miter join = theories/BufferMiter.v) with the
   *bevel* join: instead of an arc (round) or an apex (miter), the bevel
   simply connects the two offset-segment endpoints at the corner with a
   straight segment.

   At a corner vertex V between edges of direction u and w, those two
   endpoints are V offset by d along each edge's unit normal:
       P_u = V + d * unit_perp u,   P_w = V + d * unit_perp w.
   The bevel segment is (P_u, P_w).  This file proves its length is the
   chord subtended by the corner turn at radius d:

     - `bevel_length_sq_dot`: |P_u - P_w|^2 = 2 d^2 (1 - <u,w>/(|u||w|))
       (law-of-cosines form, three-axiom).
     - `bevel_length_sq_sin_half`: |P_u - P_w|^2 = (2 d * sin_half_turn u w)^2,
       i.e. the bevel chord = 2 d sin(theta/2) where theta is the turn --
       exactly the chord of the round-join arc (radius d, central angle the
       turn, cf. BufferJoin.corner_arc_sweep_eq_turn and
       ArcLength.chord_subtended r theta = 2 r sin(theta/2)).

   So round join (arc) and bevel join (chord) subtend the SAME angle at the
   same radius d -- the bevel is the round join's chord.  Three-axiom
   footprint (Azimuth.sin_half_turn is sqrt-only; no atan / Flocq /
   Classical_Prop.classic).  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.8)
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Real Vec Direction Distance BufferOffset Azimuth.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Bevel endpoints and segment.                                           *)
(* -------------------------------------------------------------------------- *)

(* The offset of the corner vertex V along edge direction u's unit normal. *)
Definition bevel_point (V : Point) (u : Vec) (d : R) : Point :=
  pt_translate V (d * vx (unit_perp u)) (d * vy (unit_perp u)).

Definition bevel_seg (V : Point) (u w : Vec) (d : R) : Point * Point :=
  (bevel_point V u d, bevel_point V w d).

(* -------------------------------------------------------------------------- *)
(* §2  Helper identities.                                                     *)
(* -------------------------------------------------------------------------- *)

(* Squared distance between two translates of the same base point. *)
Lemma dist_sq_translate2 : forall V a1 b1 a2 b2,
  dist_sq (pt_translate V a1 b1) (pt_translate V a2 b2)
  = (a1 - a2) * (a1 - a2) + (b1 - b2) * (b1 - b2).
Proof.
  intros V a1 b1 a2 b2. unfold dist_sq, pt_translate. cbn [px py]. ring.
Qed.

(* The dot product of two unit normals equals the cosine factor
   <u,w>/(|u||w|): vperp preserves the dot product and the normalisation
   contributes the 1/(|u||w|). *)
Lemma vdot_unit_perp : forall u w,
  u <> vzero -> w <> vzero ->
  vdot (unit_perp u) (unit_perp w)
  = vdot u w / (BufferOffset.vmag u * BufferOffset.vmag w).
Proof.
  intros u w Hu Hw.
  assert (HU : BufferOffset.vmag u <> 0)
    by (unfold BufferOffset.vmag; apply Rgt_not_eq; apply sqrt_lt_R0;
        apply vmag_sq_pos; exact Hu).
  assert (HW : BufferOffset.vmag w <> 0)
    by (unfold BufferOffset.vmag; apply Rgt_not_eq; apply sqrt_lt_R0;
        apply vmag_sq_pos; exact Hw).
  unfold unit_perp.
  rewrite vdot_scale_l, vdot_scale_r.
  (* vdot (vperp u) (vperp w) = vdot u w *)
  replace (vdot (vperp u) (vperp w)) with (vdot u w)
    by (unfold vdot, vperp; cbn; ring).
  field. split; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The bevel chord length.                                                *)
(* -------------------------------------------------------------------------- *)

(* Law-of-cosines form. *)
Theorem bevel_length_sq_dot : forall V u w d,
  u <> vzero -> w <> vzero ->
  dist_sq (bevel_point V u d) (bevel_point V w d)
  = 2 * d ^ 2 * (1 - vdot u w / (BufferOffset.vmag u * BufferOffset.vmag w)).
Proof.
  intros V u w d Hu Hw.
  unfold bevel_point.
  rewrite dist_sq_translate2.
  (* = d^2 * (vmag_sq nu + vmag_sq nw - 2 <nu,nw>) *)
  assert (Hraw :
    (d * vx (unit_perp u) - d * vx (unit_perp w)) *
    (d * vx (unit_perp u) - d * vx (unit_perp w)) +
    (d * vy (unit_perp u) - d * vy (unit_perp w)) *
    (d * vy (unit_perp u) - d * vy (unit_perp w))
    = d ^ 2 * (vmag_sq (unit_perp u) + vmag_sq (unit_perp w)
               - 2 * vdot (unit_perp u) (unit_perp w))).
  { unfold vmag_sq, vdot. ring. }
  rewrite Hraw.
  rewrite (vmag_sq_unit_perp u Hu), (vmag_sq_unit_perp w Hw).
  rewrite (vdot_unit_perp u w Hu Hw).
  ring.
Qed.

(* Half-angle (chord-subtended) form: the bevel chord is 2 d sin(theta/2),
   theta the turn between u and w.  This is the chord of the round-join arc. *)
Theorem bevel_length_sq_sin_half : forall V u w d,
  u <> vzero -> w <> vzero ->
  dist_sq (bevel_point V u d) (bevel_point V w d)
  = (2 * d * sin_half_turn u w) ^ 2.
Proof.
  intros V u w d Hu Hw.
  rewrite (bevel_length_sq_dot V u w d Hu Hw).
  replace ((2 * d * sin_half_turn u w) ^ 2)
    with (4 * d ^ 2 * (sin_half_turn u w) ^ 2) by ring.
  rewrite (sin_half_turn_sq u w Hu Hw).
  (* unify Azimuth.vmag with BufferOffset.vmag (both sqrt of vmag_sq) *)
  unfold Azimuth.vmag, BufferOffset.vmag.
  assert (HU : sqrt (vmag_sq u) <> 0)
    by (apply Rgt_not_eq; apply sqrt_lt_R0; apply vmag_sq_pos; exact Hu).
  assert (HW : sqrt (vmag_sq w) <> 0)
    by (apply Rgt_not_eq; apply sqrt_lt_R0; apply vmag_sq_pos; exact Hw).
  field. split; assumption.
Qed.
