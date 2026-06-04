(* ============================================================================
   NetTopologySuite.Proofs.BufferJoin
   ----------------------------------------------------------------------------
   Buffer/noder pipeline, Stage 2b seam: ROUND-JOIN CORNER-ARC RELATION.

   This is the second RGR seam of the buffer pipeline (see
   docs/buffer-noder-pipeline.md §2.2 / §6 slice S3) and closes the
   long-standing Roadmap "Original target 6":

     "for a positive buffer distance, the buffer of a convex corner
      consists of an arc whose central angle equals the exterior angle."

   At a corner between an incoming edge of direction `ein` and an outgoing
   edge of direction `eout`, the two parallel offset segments meet the
   corner along their respective offset normals `vperp ein` and
   `vperp eout`.  A round join fills the gap with a circular arc whose
   *central angle (sweep)* is the signed angle between those two normals.
   The corner's *turn / exterior angle* is the signed angle between the
   two edge directions.  This file proves they are EQUAL:

     angle_between_v (vperp ein) (vperp eout) = angle_between_v ein eout
       (`corner_arc_sweep_eq_turn`).

   The reason is structural: `vperp` is a rigid 90 degree rotation, and a
   rotation preserves both the cross product and the dot product of a
   pair of vectors (`vcross_vperp_vperp`, `vdot_vperp_vperp`); since
   `angle_between` is `atan2 (cross) (dot)`, the two angles coincide on
   the nose -- no orientation/wrap-around reasoning.

   We additionally prove `angle_between` is invariant under positive
   rescaling of either argument (`atan2_pos_scale`,
   `angle_between_v_pos_scale`), which lets the same sweep equality be
   read off the *unit* offset normals used by `theories/BufferOffset.v`
   (`corner_arc_sweep_eq_turn_unit`).

   Audit footprint.  Imports `theories/AngleBetween.v` (hence `atan2` /
   Stdlib `atan`), so inherits `Classical_Prop.classic`; listed in
   docs/audit-exceptions.txt under the same #64 atan lineage as Atan2.v /
   AngleBetween.v.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.8)
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Vec Direction Distance BufferOffset AngleBetween Atan2.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Vector-level wrapper for the signed angle.                             *)
(* -------------------------------------------------------------------------- *)

Definition angle_between_v (u w : Vec) : R :=
  angle_between (vx u) (vy u) (vx w) (vy w).

(* -------------------------------------------------------------------------- *)
(* §2  vperp preserves cross and dot (it is a rigid rotation).                *)
(* -------------------------------------------------------------------------- *)

Lemma vcross_vperp_vperp : forall u w, vcross (vperp u) (vperp w) = vcross u w.
Proof.
  intros u w. unfold vcross, vperp. simpl. ring.
Qed.

Lemma vdot_vperp_vperp : forall u w, vdot (vperp u) (vperp w) = vdot u w.
Proof.
  intros u w. unfold vdot, vperp. simpl. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Core: the sweep between the offset normals equals the turn between     *)
(*     the edges.  (Roadmap target 6, exact and unconditional.)               *)
(* -------------------------------------------------------------------------- *)

Theorem corner_arc_sweep_eq_turn : forall ein eout : Vec,
  angle_between_v (vperp ein) (vperp eout) = angle_between_v ein eout.
Proof.
  intros ein eout.
  unfold angle_between_v, angle_between.
  (* both sides are atan2 (cross) (dot); cross and dot are preserved by vperp *)
  f_equal.
  - (* the cross-product argument *)
    change (vx (vperp ein) * vy (vperp eout) - vy (vperp ein) * vx (vperp eout))
      with (vcross (vperp ein) (vperp eout)).
    change (vx ein * vy eout - vy ein * vx eout) with (vcross ein eout).
    apply vcross_vperp_vperp.
  - (* the dot-product argument *)
    change (vx (vperp ein) * vx (vperp eout) + vy (vperp ein) * vy (vperp eout))
      with (vdot (vperp ein) (vperp eout)).
    change (vx ein * vx eout + vy ein * vy eout) with (vdot ein eout).
    apply vdot_vperp_vperp.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  angle_between is invariant under positive rescaling of either arg.     *)
(* -------------------------------------------------------------------------- *)

(* atan2 is positively homogeneous: scaling both coordinates by k > 0 does
   not change the angle. *)
Lemma atan2_pos_scale : forall k y x, 0 < k -> atan2 (k * y) (k * x) = atan2 y x.
Proof.
  intros k y x Hk. unfold atan2.
  destruct (Req_dec x 0) as [Hx0|Hxn].
  - subst x. rewrite !Rmult_0_r.
    repeat match goal with
           | |- context[Rlt_dec ?a ?b] => destruct (Rlt_dec a b)
           end; try reflexivity; try (exfalso; nra).
  - assert (Hr : (k * y) / (k * x) = y / x) by (field; split; lra).
    rewrite !Hr.
    repeat match goal with
           | |- context[Rlt_dec ?a ?b] => destruct (Rlt_dec a b)
           | |- context[Rle_dec ?a ?b] => destruct (Rle_dec a b)
           end; try reflexivity; try (exfalso; nra).
Qed.

(* Hence the Vec-level angle is unchanged by a positive scalar on the left. *)
Lemma angle_between_v_scale_l : forall k u w,
  0 < k -> angle_between_v (vscale k u) w = angle_between_v u w.
Proof.
  intros k u w Hk. unfold angle_between_v, angle_between, vscale. simpl.
  (* cross = k*(ux*vy - uy*vx) and dot = k*(ux*vx+uy*vy) up to the k factor *)
  replace (k * vx u * vy w - k * vy u * vx w)
    with (k * (vx u * vy w - vy u * vx w)) by ring.
  replace (k * vx u * vx w + k * vy u * vy w)
    with (k * (vx u * vx w + vy u * vy w)) by ring.
  apply atan2_pos_scale; exact Hk.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Unit-normal corollary: the same sweep equality on BufferOffset's       *)
(*     unit offset normals.                                                    *)
(* -------------------------------------------------------------------------- *)

(* The unit normal is a strictly-positive rescale of vperp, so it carries
   the same angle.  Combined with §3 this reads the corner sweep off the
   exact unit normals BufferOffset.offset_normal uses. *)
Theorem corner_arc_sweep_eq_turn_unit : forall ein eout : Vec,
  ein <> vzero ->
  angle_between_v (unit_perp ein) (vperp eout) = angle_between_v ein eout.
Proof.
  intros ein eout Hne.
  unfold unit_perp.
  assert (Hpos : 0 < / vmag ein).
  { apply Rinv_0_lt_compat. unfold vmag. apply sqrt_lt_R0.
    apply vmag_sq_pos; exact Hne. }
  rewrite angle_between_v_scale_l by exact Hpos.
  apply corner_arc_sweep_eq_turn.
Qed.
