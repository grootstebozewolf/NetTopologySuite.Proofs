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
(* More identity / inverse laws.                                              *)
(* -------------------------------------------------------------------------- *)

Lemma vneg_involutive : forall v, vneg (vneg v) = v.
Proof. intros v. vec_eq. Qed.

Lemma vscale_0 : forall v, vscale 0 v = vzero.
Proof. intros v. vec_eq. Qed.

Lemma vscale_1 : forall v, vscale 1 v = v.
Proof. intros v. vec_eq. Qed.

Lemma vsub_self : forall v, vsub v v = vzero.
Proof. intros v. unfold vsub. apply Vec_eq; cbn; ring. Qed.

(* -------------------------------------------------------------------------- *)
(* Additional dot-product properties.                                         *)
(* -------------------------------------------------------------------------- *)

Lemma vdot_distrib_r : forall u v w,
  vdot (vadd u v) w = vdot u w + vdot v w.
Proof. intros u v w. unfold vdot, vadd. cbn. ring. Qed.

Lemma vdot_scale_l : forall c v w,
  vdot (vscale c v) w = c * vdot v w.
Proof. intros c v w. unfold vdot, vscale. cbn. ring. Qed.

Lemma vdot_zero_l : forall v, vdot vzero v = 0.
Proof. intros v. unfold vdot, vzero. cbn. ring. Qed.

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

Lemma vmag_sq_scale : forall c v,
  vmag_sq (vscale c v) = c * c * vmag_sq v.
Proof. intros c v. unfold vmag_sq, vdot, vscale. cbn. ring. Qed.

Lemma vmag_sq_zero_iff : forall v, vmag_sq v = 0 <-> v = vzero.
Proof.
  intros v. split.
  - intros H. unfold vmag_sq, vdot in H.
    pose proof (sqr_nonneg (vx v)) as Hx.
    pose proof (sqr_nonneg (vy v)) as Hy.
    assert (Hxz : vx v * vx v = 0) by lra.
    assert (Hyz : vy v * vy v = 0) by lra.
    apply sqr_eq_zero in Hxz.
    apply sqr_eq_zero in Hyz.
    apply Vec_eq; cbn; assumption.
  - intros H. rewrite H. unfold vmag_sq, vdot, vzero. cbn. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Polarisation: expanding the squared magnitude of a sum.                    *)
(* -------------------------------------------------------------------------- *)

Theorem vmag_sq_expand : forall v w,
  vmag_sq (vadd v w) = vmag_sq v + 2 * vdot v w + vmag_sq w.
Proof. intros v w. unfold vmag_sq, vdot, vadd. cbn. ring. Qed.

(* -------------------------------------------------------------------------- *)
(* The 2D vector "cross product" — a scalar (the z-component of the           *)
(* corresponding 3D cross).  Distinct from `cross` in `Orientation.v`, which  *)
(* is the signed-area triple-argument predicate; this one is binary.          *)
(* -------------------------------------------------------------------------- *)

Definition vcross (v w : Vec) : R := vx v * vy w - vy v * vx w.

Lemma vcross_antisym : forall v w, vcross v w = - vcross w v.
Proof. intros v w. unfold vcross. ring. Qed.

(* -------------------------------------------------------------------------- *)
(* Lagrange's identity in 2D:                                                 *)
(*                                                                            *)
(*     |v|² · |w|²  =  (v · w)²  +  (v × w)²                                  *)
(*                                                                            *)
(* A clean algebraic statement provable by `ring`. The geometric content is   *)
(* "the squared area of the parallelogram spanned by v and w plus the         *)
(* squared dot product equals the product of squared magnitudes". The         *)
(* Cauchy-Schwarz inequality squared falls out of it directly.                *)
(* -------------------------------------------------------------------------- *)

Theorem lagrange_identity : forall v w,
  vmag_sq v * vmag_sq w =
  vdot v w * vdot v w + vcross v w * vcross v w.
Proof. intros v w. unfold vmag_sq, vdot, vcross. cbn. ring. Qed.

(* -------------------------------------------------------------------------- *)
(* The squared Cauchy-Schwarz inequality.  Falls out of Lagrange + the        *)
(* fact that a square is non-negative.                                        *)
(* -------------------------------------------------------------------------- *)

Theorem cauchy_schwarz_sq : forall v w,
  vdot v w * vdot v w <= vmag_sq v * vmag_sq w.
Proof.
  intros v w.
  rewrite (lagrange_identity v w).
  pose proof (sqr_nonneg (vcross v w)). lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit.                                                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions vadd_assoc.
Print Assumptions vmag_sq_nonneg.
Print Assumptions vmag_sq_zero_iff.
Print Assumptions cauchy_schwarz_sq.
