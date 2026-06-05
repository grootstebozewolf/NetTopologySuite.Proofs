(* ============================================================================
   NetTopologySuite.Proofs.Parallel
   ----------------------------------------------------------------------------
   Parallelism and perpendicularity of line segments via the cross product
   and dot product of their direction vectors.
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance Orientation Vec Direction Segment.
Open Scope R_scope.

Definition seg_dir (s : Segment) : Vec :=
  mkVec (px (sp1 s) - px (sp0 s)) (py (sp1 s) - py (sp0 s)).

Definition seg_parallel (s1 s2 : Segment) : Prop :=
  parallel (seg_dir s1) (seg_dir s2).

Definition seg_perpendicular (s1 s2 : Segment) : Prop :=
  perpendicular (seg_dir s1) (seg_dir s2).

Lemma seg_parallel_refl : forall s, seg_parallel s s.
Proof. intros s. apply parallel_refl. Qed.

Lemma seg_parallel_sym : forall s1 s2, seg_parallel s1 s2 -> seg_parallel s2 s1.
Proof. intros s1 s2. apply parallel_sym. Qed.

Lemma seg_perpendicular_sym : forall s1 s2,
  seg_perpendicular s1 s2 -> seg_perpendicular s2 s1.
Proof. intros s1 s2. apply perpendicular_sym. Qed.

Lemma seg_dir_reverse : forall P0 P1,
  seg_dir (mkSegment P1 P0) = vneg (seg_dir (mkSegment P0 P1)).
Proof.
  intros P0 P1. unfold seg_dir, vneg. simpl. apply Vec_eq; simpl; ring.
Qed.

Lemma seg_parallel_reverse : forall P0 P1 P2 P3,
  seg_parallel (mkSegment P0 P1) (mkSegment P2 P3) <->
  seg_parallel (mkSegment P1 P0) (mkSegment P2 P3).
Proof.
  intros. unfold seg_parallel, parallel, vcross, seg_dir. simpl.
  split; intros; lra.
Qed.

Lemma seg_dir_zero_iff_degenerate : forall P0 P1,
  seg_dir (mkSegment P0 P1) = vzero <->
  (px P0 = px P1 /\ py P0 = py P1).
Proof.
  intros P0 P1. unfold seg_dir, vzero. simpl. split.
  - intros H. inversion H. split; lra.
  - intros [Hx Hy]. apply Vec_eq; simpl; lra.
Qed.

Lemma seg_parallel_cross_zero : forall P0 P1 Q0 Q1,
  seg_parallel (mkSegment P0 P1) (mkSegment Q0 Q1) <->
  (px P1 - px P0) * (py Q1 - py Q0) - (py P1 - py P0) * (px Q1 - px Q0) = 0.
Proof.
  intros. unfold seg_parallel, parallel, vcross, seg_dir. simpl.
  split; intros; lra.
Qed.

Lemma seg_perpendicular_dot_zero : forall P0 P1 Q0 Q1,
  seg_perpendicular (mkSegment P0 P1) (mkSegment Q0 Q1) <->
  (px P1 - px P0) * (px Q1 - px Q0) + (py P1 - py P0) * (py Q1 - py Q0) = 0.
Proof.
  intros. unfold seg_perpendicular, perpendicular, vdot, seg_dir. simpl.
  split; intros; lra.
Qed.

Lemma seg_dir_self_zero : forall P, seg_dir (mkSegment P P) = vzero.
Proof.
  intros P. apply seg_dir_zero_iff_degenerate. split; reflexivity.
Qed.

Lemma seg_parallel_to_degenerate_r : forall P0 P1 Q,
  seg_parallel (mkSegment P0 P1) (mkSegment Q Q).
Proof.
  intros P0 P1 Q. unfold seg_parallel.
  rewrite seg_dir_self_zero. apply parallel_zero_r.
Qed.

Lemma seg_parallel_to_degenerate_l : forall Q P0 P1,
  seg_parallel (mkSegment Q Q) (mkSegment P0 P1).
Proof.
  intros Q P0 P1. apply seg_parallel_sym. apply seg_parallel_to_degenerate_r.
Qed.

Lemma seg_perpendicular_to_degenerate_r : forall P0 P1 Q,
  seg_perpendicular (mkSegment P0 P1) (mkSegment Q Q).
Proof.
  intros P0 P1 Q. unfold seg_perpendicular.
  rewrite seg_dir_self_zero. apply perpendicular_zero_r.
Qed.

Lemma seg_dir_through_midpoint : forall P0 P1,
  seg_dir (mkSegment P0 (midpoint P0 P1)) =
  vscale (1/2) (seg_dir (mkSegment P0 P1)).
Proof.
  intros P0 P1. unfold seg_dir, midpoint, vscale. simpl.
  apply Vec_eq; simpl; field.
Qed.

Lemma seg_dir_to_midpoint_parallel : forall P0 P1,
  seg_parallel (mkSegment P0 (midpoint P0 P1)) (mkSegment P0 P1).
Proof.
  intros P0 P1. unfold seg_parallel.
  rewrite seg_dir_through_midpoint. apply parallel_scale_l.
Qed.

Lemma seg_perpendicular_seg_dir : forall s1 s2,
  seg_perpendicular s1 s2 <->
  vdot (seg_dir s1) (seg_dir s2) = 0.
Proof. intros. unfold seg_perpendicular. unfold perpendicular. tauto. Qed.

Lemma seg_parallel_seg_dir : forall s1 s2,
  seg_parallel s1 s2 <->
  vcross (seg_dir s1) (seg_dir s2) = 0.
Proof. intros. unfold seg_parallel. unfold parallel. tauto. Qed.

Lemma seg_dir_translate_l : forall P0 P1 vx vy,
  seg_dir (mkSegment (mkPoint (px P0 + vx) (py P0 + vy)) P1) =
  vadd (seg_dir (mkSegment P0 P1)) (vneg (mkVec vx vy)).
Proof.
  intros. unfold seg_dir, vadd, vneg. simpl. apply Vec_eq; simpl; ring.
Qed.

Lemma seg_perpendicular_irrelevant_translate_dir : forall P0 P1 Q0 Q1 dx dy,
  seg_perpendicular (mkSegment P0 P1) (mkSegment Q0 Q1) ->
  seg_perpendicular
    (mkSegment (mkPoint (px P0 + dx) (py P0 + dy))
               (mkPoint (px P1 + dx) (py P1 + dy)))
    (mkSegment Q0 Q1).
Proof.
  intros. unfold seg_perpendicular, perpendicular, vdot, seg_dir in *.
  simpl in *. lra.
Qed.
