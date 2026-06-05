(* ============================================================================
   NetTopologySuite.Proofs.Disk
   ----------------------------------------------------------------------------
   Closed disks (filled circles) in the plane.  Containment, monotonicity in
   radius, and the geometric fact that a point inside a disk is within the
   disk's radius of the centre.
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Real Distance.
Open Scope R_scope.

Record Disk : Type := mkDisk { dcentre : Point; dradius : R }.

Definition in_disk (D : Disk) (p : Point) : Prop :=
  dist_sq (dcentre D) p <= dradius D * dradius D.

Definition disk_is_valid (D : Disk) : Prop := 0 <= dradius D.

Lemma in_disk_centre : forall D,
  disk_is_valid D -> in_disk D (dcentre D).
Proof.
  intros D Hv. unfold in_disk.
  replace (dist_sq (dcentre D) (dcentre D)) with 0.
  - apply Rmult_nonneg_nonneg; exact Hv.
  - unfold dist_sq. ring.
Qed.

Lemma in_disk_monotone_radius : forall c r1 r2 p,
  0 <= r1 -> r1 <= r2 ->
  in_disk (mkDisk c r1) p -> in_disk (mkDisk c r2) p.
Proof.
  intros c r1 r2 p Hr1 Hle H. unfold in_disk in *. simpl in *.
  pose proof (dist_sq_nonneg c p).
  nra.
Qed.

Lemma in_disk_iff : forall c r p,
  0 <= r ->
  in_disk (mkDisk c r) p <-> dist c p <= r.
Proof.
  intros c r p Hr. unfold in_disk. simpl.
  rewrite (dist_le_iff_dist_sq_le c p r Hr). tauto.
Qed.

Lemma disk_zero_radius_singleton : forall c p,
  in_disk (mkDisk c 0) p -> (px p = px c /\ py p = py c).
Proof.
  intros c p H. unfold in_disk in H. simpl in H.
  assert (Hzero : dist_sq c p = 0).
  { pose proof (dist_sq_nonneg c p). nra. }
  apply dist_sq_zero_iff_eq in Hzero. destruct Hzero. split; symmetry; assumption.
Qed.

Lemma centre_zero_radius_disk : forall c,
  in_disk (mkDisk c 0) c.
Proof.
  intros c. unfold in_disk. simpl.
  replace (dist_sq c c) with 0. lra.
  unfold dist_sq. ring.
Qed.

Lemma in_disk_symmetric_centre : forall c r p,
  in_disk (mkDisk c r) p -> in_disk (mkDisk p r) c.
Proof.
  intros c r p H. unfold in_disk in *. simpl in *.
  rewrite dist_sq_sym. exact H.
Qed.

Lemma disk_contains_self : forall c r,
  0 <= r -> in_disk (mkDisk c r) c.
Proof.
  intros c r Hr. apply in_disk_centre. unfold disk_is_valid. simpl. exact Hr.
Qed.

Definition disk_concentric (D1 D2 : Disk) : Prop :=
  dcentre D1 = dcentre D2.

Lemma concentric_refl : forall D, disk_concentric D D.
Proof. intros D. unfold disk_concentric. reflexivity. Qed.

Lemma concentric_sym : forall D1 D2,
  disk_concentric D1 D2 -> disk_concentric D2 D1.
Proof. intros D1 D2 H. unfold disk_concentric in *. symmetry. exact H. Qed.

Lemma concentric_inclusion : forall c r1 r2 p,
  0 <= r1 -> r1 <= r2 ->
  in_disk (mkDisk c r1) p -> in_disk (mkDisk c r2) p.
Proof. apply in_disk_monotone_radius. Qed.

Lemma in_disk_intersection : forall c1 c2 r1 r2 p,
  in_disk (mkDisk c1 r1) p ->
  in_disk (mkDisk c2 r2) p ->
  dist_sq c1 p <= r1 * r1 /\ dist_sq c2 p <= r2 * r2.
Proof.
  intros c1 c2 r1 r2 p H1 H2. unfold in_disk in *. simpl in *. tauto.
Qed.

Lemma dist_sq_nonneg_simp : forall c p, 0 <= dist_sq c p.
Proof. apply dist_sq_nonneg. Qed.

Lemma radius_nonneg_when_centre_in_disk : forall D,
  in_disk D (dcentre D) -> 0 <= dradius D * dradius D.
Proof.
  intros D H. unfold in_disk in H.
  pose proof (dist_sq_nonneg (dcentre D) (dcentre D)). lra.
Qed.

Lemma in_disk_extensionality : forall c r p,
  dist_sq c p <= r * r -> in_disk (mkDisk c r) p.
Proof. intros. unfold in_disk. simpl. exact H. Qed.
