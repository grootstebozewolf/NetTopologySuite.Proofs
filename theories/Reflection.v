(* ============================================================================
   NetTopologySuite.Proofs.Reflection
   ----------------------------------------------------------------------------
   Reflections across the coordinate axes, across the origin, and across an
   arbitrary point.
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance Orientation Real.
Open Scope R_scope.

Definition reflect_x (p : Point) : Point := mkPoint (px p) (- py p).
Definition reflect_y (p : Point) : Point := mkPoint (- px p) (py p).
Definition reflect_origin (p : Point) : Point := mkPoint (- px p) (- py p).
Definition reflect_pt (c p : Point) : Point :=
  mkPoint (2 * px c - px p) (2 * py c - py p).

Lemma reflect_x_involutive : forall p, reflect_x (reflect_x p) = p.
Proof. intros [a b]. unfold reflect_x. simpl. f_equal; ring. Qed.

Lemma reflect_y_involutive : forall p, reflect_y (reflect_y p) = p.
Proof. intros [a b]. unfold reflect_y. simpl. f_equal; ring. Qed.

Lemma reflect_origin_involutive : forall p, reflect_origin (reflect_origin p) = p.
Proof. intros [a b]. unfold reflect_origin. simpl. f_equal; ring. Qed.

Lemma reflect_pt_involutive : forall c p,
  reflect_pt c (reflect_pt c p) = p.
Proof. intros c [a b]. unfold reflect_pt. simpl. f_equal; ring. Qed.

Lemma reflect_x_y_compose : forall p,
  reflect_x (reflect_y p) = reflect_origin p.
Proof. intros [a b]. unfold reflect_x, reflect_y, reflect_origin. simpl. f_equal; ring. Qed.

Lemma reflect_y_x_compose : forall p,
  reflect_y (reflect_x p) = reflect_origin p.
Proof. intros [a b]. unfold reflect_x, reflect_y, reflect_origin. simpl. f_equal; ring. Qed.

Lemma reflect_x_dist_sq : forall p q,
  dist_sq (reflect_x p) (reflect_x q) = dist_sq p q.
Proof. intros p q. unfold dist_sq, reflect_x. simpl. ring. Qed.

Lemma reflect_y_dist_sq : forall p q,
  dist_sq (reflect_y p) (reflect_y q) = dist_sq p q.
Proof. intros p q. unfold dist_sq, reflect_y. simpl. ring. Qed.

Lemma reflect_origin_dist_sq : forall p q,
  dist_sq (reflect_origin p) (reflect_origin q) = dist_sq p q.
Proof. intros p q. unfold dist_sq, reflect_origin. simpl. ring. Qed.

Lemma reflect_pt_dist_sq : forall c p q,
  dist_sq (reflect_pt c p) (reflect_pt c q) = dist_sq p q.
Proof. intros c p q. unfold dist_sq, reflect_pt. simpl. ring. Qed.

Lemma reflect_x_cross : forall A B Q,
  cross (reflect_x A) (reflect_x B) (reflect_x Q) = - cross A B Q.
Proof. intros A B Q. unfold cross, reflect_x. simpl. ring. Qed.

Lemma reflect_y_cross : forall A B Q,
  cross (reflect_y A) (reflect_y B) (reflect_y Q) = - cross A B Q.
Proof. intros A B Q. unfold cross, reflect_y. simpl. ring. Qed.

Lemma reflect_origin_cross : forall A B Q,
  cross (reflect_origin A) (reflect_origin B) (reflect_origin Q) = cross A B Q.
Proof. intros A B Q. unfold cross, reflect_origin. simpl. ring. Qed.

Lemma reflect_pt_cross : forall c A B Q,
  cross (reflect_pt c A) (reflect_pt c B) (reflect_pt c Q) = cross A B Q.
Proof. intros c A B Q. unfold cross, reflect_pt. simpl. ring. Qed.

Lemma reflect_x_fixed_when_y_zero : forall p,
  py p = 0 -> reflect_x p = p.
Proof.
  intros [a b]. unfold reflect_x. simpl. intros H. subst. f_equal; ring.
Qed.

Lemma reflect_y_fixed_when_x_zero : forall p,
  px p = 0 -> reflect_y p = p.
Proof.
  intros [a b]. unfold reflect_y. simpl. intros H. subst. f_equal; ring.
Qed.

Lemma reflect_origin_fixed_iff_origin : forall p,
  reflect_origin p = p <-> (px p = 0 /\ py p = 0).
Proof.
  intros [a b]. unfold reflect_origin. simpl. split.
  - intros H. inversion H. split; lra.
  - intros [Hx Hy]. subst. f_equal; ring.
Qed.

Lemma reflect_pt_fixed : forall c, reflect_pt c c = c.
Proof.
  intros [cx cy]. unfold reflect_pt. simpl. f_equal; ring.
Qed.

Lemma reflect_x_zero : reflect_x (mkPoint 0 0) = mkPoint 0 0.
Proof. unfold reflect_x. simpl. f_equal; ring. Qed.

Lemma reflect_origin_zero : reflect_origin (mkPoint 0 0) = mkPoint 0 0.
Proof. unfold reflect_origin. simpl. f_equal; ring. Qed.

(* -------------------------------------------------------------------------- *)
(* More reflection identities.                                                *)
(* -------------------------------------------------------------------------- *)

Lemma reflect_x_px : forall p, px (reflect_x p) = px p.
Proof. intros. reflexivity. Qed.

Lemma reflect_x_py : forall p, py (reflect_x p) = - py p.
Proof. intros. reflexivity. Qed.

Lemma reflect_y_px : forall p, px (reflect_y p) = - px p.
Proof. intros. reflexivity. Qed.

Lemma reflect_y_py : forall p, py (reflect_y p) = py p.
Proof. intros. reflexivity. Qed.

Lemma reflect_origin_px : forall p, px (reflect_origin p) = - px p.
Proof. intros. reflexivity. Qed.

Lemma reflect_origin_py : forall p, py (reflect_origin p) = - py p.
Proof. intros. reflexivity. Qed.

Lemma reflect_pt_px : forall c p, px (reflect_pt c p) = 2 * px c - px p.
Proof. intros. reflexivity. Qed.

Lemma reflect_pt_py : forall c p, py (reflect_pt c p) = 2 * py c - py p.
Proof. intros. reflexivity. Qed.

Lemma reflect_x_origin : reflect_x (mkPoint 0 0) = mkPoint 0 0.
Proof. unfold reflect_x. simpl. f_equal; ring. Qed.

Lemma reflect_y_zero : reflect_y (mkPoint 0 0) = mkPoint 0 0.
Proof. unfold reflect_y. simpl. f_equal; ring. Qed.

Lemma reflect_x_cancel_y_axis : forall a,
  reflect_x (mkPoint a 0) = mkPoint a 0.
Proof. intros. unfold reflect_x. simpl. f_equal; ring. Qed.

Lemma reflect_y_cancel_x_axis : forall b,
  reflect_y (mkPoint 0 b) = mkPoint 0 b.
Proof. intros. unfold reflect_y. simpl. f_equal; ring. Qed.

Lemma reflect_pt_swap : forall a b,
  reflect_pt a b = reflect_pt (mkPoint (px a) (py a)) b.
Proof. intros. destruct a. reflexivity. Qed.

Lemma reflect_pt_to_self_iff : forall c p,
  reflect_pt c p = p <-> p = c.
Proof.
  intros [cx cy] [px0 py0]. unfold reflect_pt. simpl. split.
  - intros H. inversion H. f_equal; lra.
  - intros H. inversion H. subst. f_equal; ring.
Qed.
