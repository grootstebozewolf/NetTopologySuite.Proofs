(* ============================================================================
   NetTopologySuite.Proofs.Direction
   ----------------------------------------------------------------------------
   Direction vectors:  Vec endowed with a "parallel" equivalence.
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Real Vec.
Open Scope R_scope.

(* Two vectors are parallel if one is a non-zero scalar multiple of the other.
   Equivalently: their cross product vanishes and they are not both zero. *)
Definition parallel (v w : Vec) : Prop :=
  vcross v w = 0.

(* Two vectors point in the same direction if w = c * v for some c > 0. *)
Definition same_direction (v w : Vec) : Prop :=
  exists c : R, c > 0 /\ w = vscale c v.

Definition opposite_direction (v w : Vec) : Prop :=
  exists c : R, c > 0 /\ w = vscale (- c) v.

Lemma parallel_refl : forall v, parallel v v.
Proof. intros v. unfold parallel, vcross. ring. Qed.

Lemma parallel_sym : forall v w, parallel v w -> parallel w v.
Proof.
  intros v w H. unfold parallel in *. rewrite vcross_antisym. lra.
Qed.

Lemma parallel_zero_r : forall v, parallel v vzero.
Proof. intros v. unfold parallel, vcross, vzero. simpl. ring. Qed.

Lemma parallel_zero_l : forall v, parallel vzero v.
Proof. intros v. apply parallel_sym. apply parallel_zero_r. Qed.

Lemma parallel_scale_r : forall v c, parallel v (vscale c v).
Proof.
  intros v c. unfold parallel, vcross, vscale. simpl. ring.
Qed.

Lemma parallel_scale_l : forall v c, parallel (vscale c v) v.
Proof. intros. apply parallel_sym. apply parallel_scale_r. Qed.

Lemma same_direction_refl : forall v, same_direction v v.
Proof.
  intros v. exists 1. split; [lra | rewrite vscale_1; reflexivity].
Qed.

Lemma same_direction_implies_parallel : forall v w,
  same_direction v w -> parallel v w.
Proof.
  intros v w [c [_ Hw]]. rewrite Hw. apply parallel_scale_r.
Qed.

Lemma opposite_direction_implies_parallel : forall v w,
  opposite_direction v w -> parallel v w.
Proof.
  intros v w [c [_ Hw]]. rewrite Hw. apply parallel_scale_r.
Qed.

Lemma same_direction_trans : forall u v w,
  same_direction u v -> same_direction v w -> same_direction u w.
Proof.
  intros u v w [c1 [Hc1 Hv]] [c2 [Hc2 Hw]].
  exists (c2 * c1). split.
  - apply Rmult_pos_pos; assumption.
  - rewrite Hw, Hv. rewrite vscale_assoc. reflexivity.
Qed.

Lemma same_direction_scale_pos : forall v c,
  c > 0 -> same_direction v (vscale c v).
Proof.
  intros v c Hc. exists c. split; [exact Hc | reflexivity].
Qed.

Lemma opposite_direction_scale_neg : forall v c,
  c > 0 -> opposite_direction v (vscale (- c) v).
Proof.
  intros v c Hc. exists c. split; [exact Hc | reflexivity].
Qed.

(* Perpendicularity: dot product is zero. *)
Definition perpendicular (v w : Vec) : Prop :=
  vdot v w = 0.

Lemma perpendicular_sym : forall v w, perpendicular v w -> perpendicular w v.
Proof.
  intros v w H. unfold perpendicular in *. rewrite vdot_comm. exact H.
Qed.

Lemma perpendicular_zero_r : forall v, perpendicular v vzero.
Proof.
  intros v. unfold perpendicular, vdot, vzero. simpl. ring.
Qed.

Lemma perpendicular_zero_l : forall v, perpendicular vzero v.
Proof. intros. apply perpendicular_sym. apply perpendicular_zero_r. Qed.

Lemma perpendicular_scale_r : forall v w c,
  perpendicular v w -> perpendicular v (vscale c w).
Proof.
  intros v w c H. unfold perpendicular in *.
  rewrite vdot_comm. rewrite vdot_scale_l. rewrite vdot_comm.
  rewrite H. ring.
Qed.

(* The unique perpendicular direction up to sign: (-y, x). *)
Definition vperp (v : Vec) : Vec := mkVec (- vy v) (vx v).

Lemma vperp_perpendicular : forall v, perpendicular v (vperp v).
Proof.
  intros v. unfold perpendicular, vdot, vperp. simpl. ring.
Qed.

Lemma vperp_perp_perp : forall v, vperp (vperp v) = vneg v.
Proof.
  intros v. unfold vperp, vneg. apply Vec_eq; simpl; ring.
Qed.

Lemma vperp_zero : vperp vzero = vzero.
Proof. unfold vperp, vzero. apply Vec_eq; simpl; ring. Qed.

Lemma vperp_mag_sq : forall v, vmag_sq (vperp v) = vmag_sq v.
Proof. intros v. unfold vmag_sq, vdot, vperp. simpl. ring. Qed.

Lemma parallel_iff_vcross_zero : forall v w, parallel v w <-> vcross v w = 0.
Proof. intros. unfold parallel. tauto. Qed.

Lemma perpendicular_iff_vdot_zero : forall v w, perpendicular v w <-> vdot v w = 0.
Proof. intros. unfold perpendicular. tauto. Qed.

Lemma parallel_neg_l : forall v w, parallel v w -> parallel (vneg v) w.
Proof. intros v w H. unfold parallel in *. rewrite vcross_neg_l. lra. Qed.

Lemma parallel_neg_r : forall v w, parallel v w -> parallel v (vneg w).
Proof. intros v w H. unfold parallel in *. rewrite vcross_neg_r. lra. Qed.

Lemma perpendicular_neg_l : forall v w, perpendicular v w -> perpendicular (vneg v) w.
Proof. intros v w H. unfold perpendicular in *. rewrite vdot_neg_l. lra. Qed.

Lemma perpendicular_neg_r : forall v w, perpendicular v w -> perpendicular v (vneg w).
Proof. intros v w H. unfold perpendicular in *. rewrite vdot_neg_r. lra. Qed.

Lemma vperp_unfold_x : forall v, vx (vperp v) = - vy v.
Proof. intros. reflexivity. Qed.

Lemma vperp_unfold_y : forall v, vy (vperp v) = vx v.
Proof. intros. reflexivity. Qed.

Lemma vperp_add : forall v w, vperp (vadd v w) = vadd (vperp v) (vperp w).
Proof. intros. unfold vperp, vadd. apply Vec_eq; simpl; ring. Qed.

Lemma vperp_scale : forall c v, vperp (vscale c v) = vscale c (vperp v).
Proof. intros. unfold vperp, vscale. apply Vec_eq; simpl; ring. Qed.

Lemma vperp_neg : forall v, vperp (vneg v) = vneg (vperp v).
Proof. intros. unfold vperp, vneg. apply Vec_eq; simpl; ring. Qed.

Lemma perpendicular_refl_iff_zero : forall v,
  perpendicular v v <-> v = vzero.
Proof.
  intros v. unfold perpendicular.
  rewrite vdot_self_eq_mag_sq. apply vmag_sq_zero_iff.
Qed.
