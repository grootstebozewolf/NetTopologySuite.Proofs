(* ============================================================================
   NetTopologySuite.Proofs.Lattice
   ----------------------------------------------------------------------------
   Rmin / Rmax as a lattice on the real numbers.  The named identities
   downstream code uses for bounding-box arithmetic, interval intersection
   and snap-rounding heuristics.
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
Open Scope R_scope.

Lemma Rmax_comm : forall a b, Rmax a b = Rmax b a.
Proof.
  intros a b. unfold Rmax. destruct (Rle_dec a b), (Rle_dec b a); try lra.
Qed.

Lemma Rmin_comm : forall a b, Rmin a b = Rmin b a.
Proof.
  intros a b. unfold Rmin. destruct (Rle_dec a b), (Rle_dec b a); try lra.
Qed.

Lemma Rmax_idempotent : forall a, Rmax a a = a.
Proof. intros a. unfold Rmax. destruct (Rle_dec a a); lra. Qed.

Lemma Rmin_idempotent : forall a, Rmin a a = a.
Proof. intros a. unfold Rmin. destruct (Rle_dec a a); lra. Qed.

Lemma Rmax_le_iff : forall a b c, Rmax a b <= c <-> a <= c /\ b <= c.
Proof.
  intros. split.
  - intros H. pose proof (Rmax_l a b). pose proof (Rmax_r a b). split; lra.
  - intros [Ha Hb]. unfold Rmax. destruct (Rle_dec a b); lra.
Qed.

Lemma Rmin_le_iff : forall a b c, c <= Rmin a b <-> c <= a /\ c <= b.
Proof.
  intros. split.
  - intros H. pose proof (Rmin_l a b). pose proof (Rmin_r a b). split; lra.
  - intros [Ha Hb]. unfold Rmin. destruct (Rle_dec a b); lra.
Qed.

Lemma Rmax_lub : forall a b c, a <= c -> b <= c -> Rmax a b <= c.
Proof. intros. apply Rmax_le_iff. tauto. Qed.

Lemma Rmin_glb : forall a b c, c <= a -> c <= b -> c <= Rmin a b.
Proof. intros. apply Rmin_le_iff. tauto. Qed.

Lemma Rmax_left_when_le : forall a b, b <= a -> Rmax a b = a.
Proof. intros. apply Rmax_left. lra. Qed.

Lemma Rmin_right_when_le : forall a b, b <= a -> Rmin a b = b.
Proof. intros. apply Rmin_right. lra. Qed.

Lemma Rmax_nonneg_of_nonneg_l : forall a b, 0 <= a -> 0 <= Rmax a b.
Proof. intros a b H. pose proof (Rmax_l a b). lra. Qed.

Lemma Rmax_nonneg_of_nonneg_r : forall a b, 0 <= b -> 0 <= Rmax a b.
Proof. intros a b H. pose proof (Rmax_r a b). lra. Qed.

Lemma Rmin_nonneg : forall a b, 0 <= a -> 0 <= b -> 0 <= Rmin a b.
Proof. intros a b Ha Hb. apply Rmin_glb; lra. Qed.

Lemma Rmax_add_distrib : forall a b c,
  Rmax (a + c) (b + c) = Rmax a b + c.
Proof.
  intros. unfold Rmax. destruct (Rle_dec (a+c) (b+c)), (Rle_dec a b); lra.
Qed.

Lemma Rmin_add_distrib : forall a b c,
  Rmin (a + c) (b + c) = Rmin a b + c.
Proof.
  intros. unfold Rmin. destruct (Rle_dec (a+c) (b+c)), (Rle_dec a b); lra.
Qed.

Lemma Rmax_neg : forall a b, Rmax (- a) (- b) = - Rmin a b.
Proof.
  intros. unfold Rmax, Rmin. destruct (Rle_dec (-a) (-b)), (Rle_dec a b); lra.
Qed.

Lemma Rmin_neg : forall a b, Rmin (- a) (- b) = - Rmax a b.
Proof.
  intros. unfold Rmax, Rmin. destruct (Rle_dec (-a) (-b)), (Rle_dec a b); lra.
Qed.

Lemma Rmax_eq_l : forall a b, a <= b -> Rmax a b = b.
Proof. intros. apply Rmax_right. exact H. Qed.

Lemma Rmin_eq_l : forall a b, a <= b -> Rmin a b = a.
Proof. intros. apply Rmin_left. exact H. Qed.
