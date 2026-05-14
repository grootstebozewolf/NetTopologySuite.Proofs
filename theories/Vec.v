(* ============================================================================
   NetTopologySuite.Proofs.Vec
   ----------------------------------------------------------------------------
   Two-dimensional vector algebra: addition, negation, scalar multiplication,
   dot product, and squared magnitude.

   NetTopologySuite uses 2D vectors implicitly throughout — direction vectors
   for line segments, normals for buffer offsets, basis transformations in
   affine transforms.  Formalising the algebraic laws separately means every
   downstream theorem about a geometric operation that is a polynomial in
   vector components gets to cite a small named lemma rather than rebuild
   the ring reasoning each time.

   The module is independent of `Point` (which is shaped like a vector but
   plays the role of a position, not a free vector); the two records have
   the same field layout but different intended meanings.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From NTS.Proofs Require Import Distance.
Open Scope R_scope.

Record Vec : Type := mkVec { vx : R; vy : R }.

Definition vzero : Vec := mkVec 0 0.
Definition vadd (v w : Vec) : Vec := mkVec (vx v + vx w) (vy v + vy w).
Definition vneg (v : Vec) : Vec := mkVec (- vx v) (- vy v).
Definition vsub (v w : Vec) : Vec := vadd v (vneg w).
Definition vscale (c : R) (v : Vec) : Vec := mkVec (c * vx v) (c * vy v).
Definition vdot (v w : Vec) : R := vx v * vx w + vy v * vy w.
Definition vmag_sq (v : Vec) : R := vdot v v.

(* -------------------------------------------------------------------------- *)
(* Vector equality is component-wise: a small extensionality principle that   *)
(* lets the rest of the file prove identities by ring-style reasoning on the  *)
(* two scalar components separately.                                          *)
(* -------------------------------------------------------------------------- *)

Lemma Vec_eq : forall v w : Vec, vx v = vx w -> vy v = vy w -> v = w.
Proof.
  intros [a1 b1] [a2 b2] Hx Hy. cbn in Hx, Hy. subst. reflexivity.
Qed.

Ltac vec_eq := apply Vec_eq; cbn; ring.

(* -------------------------------------------------------------------------- *)
(* Abelian-group laws of vector addition.                                     *)
(* -------------------------------------------------------------------------- *)

Lemma vadd_comm : forall v w, vadd v w = vadd w v.
Proof. intros v w. vec_eq. Qed.

Lemma vadd_assoc : forall u v w, vadd (vadd u v) w = vadd u (vadd v w).
Proof. intros u v w. vec_eq. Qed.

Lemma vadd_zero_r : forall v, vadd v vzero = v.
Proof. intros v. vec_eq. Qed.

Lemma vadd_zero_l : forall v, vadd vzero v = v.
Proof. intros v. vec_eq. Qed.

Lemma vadd_neg_r : forall v, vadd v (vneg v) = vzero.
Proof. intros v. vec_eq. Qed.

(* -------------------------------------------------------------------------- *)
(* Scalar multiplication.                                                     *)
(* -------------------------------------------------------------------------- *)

Lemma vscale_distrib_add : forall c v w,
  vscale c (vadd v w) = vadd (vscale c v) (vscale c w).
Proof. intros c v w. vec_eq. Qed.

Lemma vscale_assoc : forall a b v, vscale a (vscale b v) = vscale (a * b) v.
Proof. intros a b v. vec_eq. Qed.

(* -------------------------------------------------------------------------- *)
(* Dot product.                                                               *)
(* -------------------------------------------------------------------------- *)

Lemma vdot_comm : forall v w, vdot v w = vdot w v.
Proof. intros v w. unfold vdot. ring. Qed.

Lemma vdot_distrib_l : forall u v w,
  vdot u (vadd v w) = vdot u v + vdot u w.
Proof. intros u v w. unfold vdot, vadd. simpl. ring. Qed.

(* -------------------------------------------------------------------------- *)
(* Squared magnitude is non-negative; it is zero exactly at the zero vector.  *)
(* The first is the algebraic kernel of any "buffer thickness is non-         *)
(* negative" reasoning downstream.                                            *)
(* -------------------------------------------------------------------------- *)

Lemma vmag_sq_nonneg : forall v, 0 <= vmag_sq v.
Proof.
  intros v. unfold vmag_sq, vdot.
  pose proof (sqr_nonneg (vx v)).
  pose proof (sqr_nonneg (vy v)).
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit.                                                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions vadd_assoc.
Print Assumptions vmag_sq_nonneg.
