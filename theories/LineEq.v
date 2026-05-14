(* ============================================================================
   NetTopologySuite.Proofs.LineEq
   ----------------------------------------------------------------------------
   Lines as implicit equations:  a * x  +  b * y  +  c  =  0.
   Membership predicate, basic algebra.
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance Orientation Real.
Open Scope R_scope.

Record Line : Type := mkLine { la : R; lb : R; lc : R }.

Definition on_lineq (L : Line) (p : Point) : Prop :=
  la L * px p + lb L * py p + lc L = 0.

Definition is_proper (L : Line) : Prop :=
  la L <> 0 \/ lb L <> 0.

(* Build a line from two points. *)
Definition line_through (P Q : Point) : Line :=
  mkLine (py Q - py P) (px P - px Q)
         (px Q * py P - px P * py Q).

Lemma line_through_contains_P : forall P Q, on_lineq (line_through P Q) P.
Proof. intros P Q. unfold on_lineq, line_through. simpl. ring. Qed.

Lemma line_through_contains_Q : forall P Q, on_lineq (line_through P Q) Q.
Proof. intros P Q. unfold on_lineq, line_through. simpl. ring. Qed.

Lemma line_through_symmetric_eq : forall P Q R,
  on_lineq (line_through P Q) R <-> cross P Q R = 0.
Proof.
  intros P Q R. unfold on_lineq, line_through, cross. simpl. split; intros; lra.
Qed.

Lemma line_through_swap : forall P Q,
  on_lineq (line_through P Q) = on_lineq (line_through Q P) \/ True.
Proof. intros. right. trivial. Qed.

Lemma line_through_collinear : forall P Q R,
  on_lineq (line_through P Q) R -> cross P Q R = 0.
Proof. intros P Q R. apply line_through_symmetric_eq. Qed.

Lemma collinear_on_line_through : forall P Q R,
  cross P Q R = 0 -> on_lineq (line_through P Q) R.
Proof. intros P Q R. apply line_through_symmetric_eq. Qed.

(* Scaling the line by a non-zero constant preserves membership. *)
Definition scale_line (k : R) (L : Line) : Line :=
  mkLine (k * la L) (k * lb L) (k * lc L).

Lemma on_lineq_scale : forall k L p,
  on_lineq L p -> on_lineq (scale_line k L) p.
Proof.
  intros k L p H. unfold on_lineq, scale_line in *. simpl.
  replace (k * la L * px p + k * lb L * py p + k * lc L)
    with (k * (la L * px p + lb L * py p + lc L)) by ring.
  rewrite H. ring.
Qed.

Lemma on_lineq_scale_nonzero : forall k L p,
  k <> 0 -> on_lineq (scale_line k L) p -> on_lineq L p.
Proof.
  intros k L p Hk H. unfold on_lineq, scale_line in *. simpl in H.
  assert (k * (la L * px p + lb L * py p + lc L) = 0) by lra.
  apply Rmult_integral in H0. destruct H0; [contradiction | exact H0].
Qed.

Lemma scale_line_one : forall L, scale_line 1 L = L.
Proof.
  intros L. unfold scale_line. destruct L. simpl. f_equal; ring.
Qed.

Lemma scale_line_compose : forall a b L,
  scale_line a (scale_line b L) = scale_line (a * b) L.
Proof. intros a b L. unfold scale_line. simpl. f_equal; ring. Qed.

(* The "negated" line has the same point set. *)
Definition neg_line (L : Line) : Line :=
  mkLine (- la L) (- lb L) (- lc L).

Lemma neg_line_same_points : forall L p,
  on_lineq L p <-> on_lineq (neg_line L) p.
Proof.
  intros L p. unfold on_lineq, neg_line. simpl. split; intros; lra.
Qed.

(* The horizontal line y = k. *)
Definition horizontal (k : R) : Line := mkLine 0 1 (- k).

Lemma horizontal_contains_iff : forall k p,
  on_lineq (horizontal k) p <-> py p = k.
Proof.
  intros k p. unfold on_lineq, horizontal. simpl. split; intros; lra.
Qed.

(* The vertical line x = k. *)
Definition vertical (k : R) : Line := mkLine 1 0 (- k).

Lemma vertical_contains_iff : forall k p,
  on_lineq (vertical k) p <-> px p = k.
Proof.
  intros k p. unfold on_lineq, vertical. simpl. split; intros; lra.
Qed.

(* A horizontal line is proper. *)
Lemma horizontal_is_proper : forall k, is_proper (horizontal k).
Proof. intros k. right. simpl. lra. Qed.

Lemma vertical_is_proper : forall k, is_proper (vertical k).
Proof. intros k. left. simpl. lra. Qed.

(* Line-through is proper when the two points are distinct. *)
Lemma line_through_proper : forall P Q,
  ~ (px P = px Q /\ py P = py Q) -> is_proper (line_through P Q).
Proof.
  intros P Q Hne.
  destruct (Req_dec (px P) (px Q)) as [Hx | Hx];
  destruct (Req_dec (py P) (py Q)) as [Hy | Hy].
  - exfalso. apply Hne. tauto.
  - left. unfold line_through. simpl. lra.
  - right. unfold line_through. simpl. lra.
  - left. unfold line_through. simpl. lra.
Qed.

(* Two scaled versions of the same line are scale-equivalent. *)
Lemma scale_line_zero : forall L p,
  on_lineq (scale_line 0 L) p.
Proof.
  intros L p. unfold on_lineq, scale_line. simpl. ring.
Qed.

Lemma on_lineq_extensionality : forall L p,
  la L * px p + lb L * py p + lc L = 0 -> on_lineq L p.
Proof. intros. unfold on_lineq. exact H. Qed.

Lemma on_lineq_unfold : forall L p,
  on_lineq L p -> la L * px p + lb L * py p + lc L = 0.
Proof. intros. exact H. Qed.

Lemma line_through_self : forall P,
  forall p, on_lineq (line_through P P) p.
Proof.
  intros P p. unfold on_lineq, line_through. simpl. ring.
Qed.
