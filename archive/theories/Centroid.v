(* ============================================================================
   NetTopologySuite.Proofs.Centroid
   ----------------------------------------------------------------------------
   Centroids of segments and triangles: the average of vertices.
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Real Distance Orientation Segment Triangle Convex.
Open Scope R_scope.

Definition centroid2 (P Q : Point) : Point :=
  mkPoint ((px P + px Q) / 2) ((py P + py Q) / 2).

Definition centroid3 (A B C : Point) : Point :=
  mkPoint ((px A + px B + px C) / 3) ((py A + py B + py C) / 3).

Lemma centroid2_eq_midpoint : forall P Q,
  centroid2 P Q = midpoint P Q.
Proof. intros. unfold centroid2, midpoint. simpl. f_equal; field. Qed.

Lemma centroid2_symmetric : forall P Q, centroid2 P Q = centroid2 Q P.
Proof. intros. unfold centroid2. simpl. f_equal; field. Qed.

Lemma centroid2_self : forall P, centroid2 P P = P.
Proof. intros [a b]. unfold centroid2. simpl. f_equal; field. Qed.

Lemma centroid2_between : forall P Q, between P Q (centroid2 P Q).
Proof.
  intros P Q. rewrite centroid2_eq_midpoint. apply midpoint_between.
Qed.

Lemma centroid3_symmetric_ABC_BAC : forall A B C,
  centroid3 A B C = centroid3 B A C.
Proof. intros. unfold centroid3. simpl. f_equal; field. Qed.

Lemma centroid3_symmetric_ABC_ACB : forall A B C,
  centroid3 A B C = centroid3 A C B.
Proof. intros. unfold centroid3. simpl. f_equal; field. Qed.

Lemma centroid3_symmetric_ABC_BCA : forall A B C,
  centroid3 A B C = centroid3 B C A.
Proof. intros. unfold centroid3. simpl. f_equal; field. Qed.

Lemma centroid3_symmetric_ABC_CAB : forall A B C,
  centroid3 A B C = centroid3 C A B.
Proof. intros. unfold centroid3. simpl. f_equal; field. Qed.

Lemma centroid3_self : forall P,
  centroid3 P P P = P.
Proof. intros [a b]. unfold centroid3. simpl. f_equal; field. Qed.

Lemma centroid3_collapse_two : forall P Q,
  centroid3 P P Q = mkPoint ((2 * px P + px Q) / 3) ((2 * py P + py Q) / 3).
Proof.
  intros. unfold centroid3. simpl. f_equal; field.
Qed.

Lemma centroid2_translation : forall P Q vx vy,
  centroid2 (mkPoint (px P + vx) (py P + vy))
            (mkPoint (px Q + vx) (py Q + vy)) =
  mkPoint (px (centroid2 P Q) + vx) (py (centroid2 P Q) + vy).
Proof. intros. unfold centroid2. simpl. f_equal; field. Qed.

Lemma centroid3_translation : forall A B C vx vy,
  centroid3 (mkPoint (px A + vx) (py A + vy))
            (mkPoint (px B + vx) (py B + vy))
            (mkPoint (px C + vx) (py C + vy)) =
  mkPoint (px (centroid3 A B C) + vx) (py (centroid3 A B C) + vy).
Proof. intros. unfold centroid3. simpl. f_equal; field. Qed.

Lemma centroid2_scale : forall c P Q,
  centroid2 (mkPoint (c * px P) (c * py P))
            (mkPoint (c * px Q) (c * py Q)) =
  mkPoint (c * px (centroid2 P Q)) (c * py (centroid2 P Q)).
Proof. intros. unfold centroid2. simpl. f_equal; field. Qed.

Lemma centroid3_scale : forall c A B C,
  centroid3 (mkPoint (c * px A) (c * py A))
            (mkPoint (c * px B) (c * py B))
            (mkPoint (c * px C) (c * py C)) =
  mkPoint (c * px (centroid3 A B C)) (c * py (centroid3 A B C)).
Proof. intros. unfold centroid3. simpl. f_equal; field. Qed.

Definition triangle_centroid (t : Triangle) : Point :=
  centroid3 (tA t) (tB t) (tC t).

Lemma triangle_centroid_translation_invariant : forall t vx vy,
  triangle_centroid (tri_translate t vx vy) =
  mkPoint (px (triangle_centroid t) + vx)
          (py (triangle_centroid t) + vy).
Proof.
  intros [A B C] vx vy. unfold triangle_centroid, tri_translate, translate.
  simpl. apply centroid3_translation.
Qed.

Lemma centroid2_x_in_range : forall P Q,
  Rmin (px P) (px Q) <= px (centroid2 P Q) <= Rmax (px P) (px Q).
Proof.
  intros P Q. unfold centroid2. simpl.
  pose proof (Rmin_l (px P) (px Q)). pose proof (Rmin_r (px P) (px Q)).
  pose proof (Rmax_l (px P) (px Q)). pose proof (Rmax_r (px P) (px Q)).
  split; nra.
Qed.

Lemma centroid2_y_in_range : forall P Q,
  Rmin (py P) (py Q) <= py (centroid2 P Q) <= Rmax (py P) (py Q).
Proof.
  intros P Q. unfold centroid2. simpl.
  pose proof (Rmin_l (py P) (py Q)). pose proof (Rmin_r (py P) (py Q)).
  pose proof (Rmax_l (py P) (py Q)). pose proof (Rmax_r (py P) (py Q)).
  split; nra.
Qed.

Lemma centroid3_x_lb : forall A B C,
  Rmin (px A) (Rmin (px B) (px C)) <= px (centroid3 A B C).
Proof.
  intros. unfold centroid3. simpl.
  pose proof (Rmin_l (px A) (Rmin (px B) (px C))).
  pose proof (Rmin_r (px A) (Rmin (px B) (px C))).
  pose proof (Rmin_l (px B) (px C)).
  pose proof (Rmin_r (px B) (px C)).
  nra.
Qed.

Lemma centroid3_x_ub : forall A B C,
  px (centroid3 A B C) <= Rmax (px A) (Rmax (px B) (px C)).
Proof.
  intros. unfold centroid3. simpl.
  pose proof (Rmax_l (px A) (Rmax (px B) (px C))).
  pose proof (Rmax_r (px A) (Rmax (px B) (px C))).
  pose proof (Rmax_l (px B) (px C)).
  pose proof (Rmax_r (px B) (px C)).
  nra.
Qed.

Lemma centroid3_y_lb : forall A B C,
  Rmin (py A) (Rmin (py B) (py C)) <= py (centroid3 A B C).
Proof.
  intros. unfold centroid3. simpl.
  pose proof (Rmin_l (py A) (Rmin (py B) (py C))).
  pose proof (Rmin_r (py A) (Rmin (py B) (py C))).
  pose proof (Rmin_l (py B) (py C)).
  pose proof (Rmin_r (py B) (py C)).
  nra.
Qed.

Lemma centroid3_y_ub : forall A B C,
  py (centroid3 A B C) <= Rmax (py A) (Rmax (py B) (py C)).
Proof.
  intros. unfold centroid3. simpl.
  pose proof (Rmax_l (py A) (Rmax (py B) (py C))).
  pose proof (Rmax_r (py A) (Rmax (py B) (py C))).
  pose proof (Rmax_l (py B) (py C)).
  pose proof (Rmax_r (py B) (py C)).
  nra.
Qed.

Lemma centroid2_translation_invariant_vec : forall P Q dx dy,
  centroid2 (mkPoint (px P + dx) (py P + dy))
            (mkPoint (px Q + dx) (py Q + dy)) =
  mkPoint (px (centroid2 P Q) + dx) (py (centroid2 P Q) + dy).
Proof. intros. apply centroid2_translation. Qed.

Lemma centroid3_eq_avg_x : forall A B C,
  px (centroid3 A B C) = (px A + px B + px C) / 3.
Proof. intros. reflexivity. Qed.

Lemma centroid3_eq_avg_y : forall A B C,
  py (centroid3 A B C) = (py A + py B + py C) / 3.
Proof. intros. reflexivity. Qed.
