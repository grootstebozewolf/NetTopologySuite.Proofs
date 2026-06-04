(* ============================================================================
   NetTopologySuite.Proofs.BufferOffset
   ----------------------------------------------------------------------------
   Buffer/noder pipeline, Stage 2a seam: OFFSET-SEGMENT SOUNDNESS.

   This is the first RGR seam of the buffer pipeline (see
   docs/buffer-noder-pipeline.md §2.2 / §6 slice S2).  The buffer
   front-end's job is to emit, for each input edge, a *parallel curve at
   distance d* on the chosen side.  This file defines that offset segment
   and proves the two soundness facts a correct offset must satisfy:

     1. PARALLEL.  The offset segment has the *same* direction vector as
        its source edge (`offset_seg_dir`), hence is parallel to it
        (`offset_seg_parallel`).  Translating both endpoints by the same
        normal vector cannot rotate the edge -- this is the property
        whose failure produces the kinked / self-overlapping linework in
        flat-endcap and short-segment buffer artifacts (JTS#739, #180).

     2. AT DISTANCE d.  Each offset endpoint sits at Euclidean distance
        |d| from its source endpoint along the *unit* normal
        (`offset_point_dist`), and the offset endpoint's perpendicular
        distance to the source line is exactly |d|
        (`offset_perp_dist_to_line`).  This is the defining property of a
        distance-d offset.

   All pure-R (Stdlib only); no Flocq, no axioms beyond the corpus's
   classical-reals trio.  Builds in the host `_CoqProject`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.8)
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Real Vec Distance Direction.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Vector magnitude and the unit normal of a segment.                     *)
(* -------------------------------------------------------------------------- *)

(* Euclidean length of a vector.  (Defined locally to keep this module's
   import surface minimal; matches Azimuth.vmag.) *)
Definition vmag (v : Vec) : R := sqrt (vmag_sq v).

(* The perpendicular has the same length as the original vector:
   |(-y, x)| = |(x, y)|. *)
Lemma vmag_sq_vperp : forall v, vmag_sq (vperp v) = vmag_sq v.
Proof.
  intros v. unfold vmag_sq, vdot, vperp. simpl. ring.
Qed.

(* The unit normal of a vector: the perpendicular, normalised. *)
Definition unit_perp (v : Vec) : Vec := vscale (/ vmag v) (vperp v).

(* For a non-zero vector, vmag_sq is strictly positive. *)
Lemma vmag_sq_pos : forall v, v <> vzero -> 0 < vmag_sq v.
Proof.
  intros v Hv.
  pose proof (vmag_sq_nonneg v) as Hge.
  destruct (Rle_lt_or_eq_dec 0 (vmag_sq v) Hge) as [Hlt | Heq].
  - exact Hlt.
  - exfalso. apply Hv. apply (proj1 (vmag_sq_zero_iff v)). symmetry. exact Heq.
Qed.

(* The unit normal really has unit length:  vmag_sq (unit_perp v) = 1. *)
Lemma vmag_sq_unit_perp : forall v, v <> vzero -> vmag_sq (unit_perp v) = 1.
Proof.
  intros v Hv.
  pose proof (vmag_sq_pos v Hv) as Hpos.
  assert (Hmne : vmag v <> 0)
    by (unfold vmag; apply Rgt_not_eq; apply sqrt_lt_R0; exact Hpos).
  assert (Hss : vmag v * vmag v = vmag_sq v)
    by (unfold vmag; apply sqrt_sqrt; lra).
  assert (Hinv : / vmag v * vmag v = 1) by (apply Rinv_l; exact Hmne).
  assert (Hscale : forall c w, vmag_sq (vscale c w) = c * c * vmag_sq w)
    by (intros; unfold vmag_sq, vdot, vscale; simpl; ring).
  unfold unit_perp. rewrite Hscale, vmag_sq_vperp.
  rewrite <- Hss.
  replace (/ vmag v * / vmag v * (vmag v * vmag v))
    with ((/ vmag v * vmag v) * (/ vmag v * vmag v)) by ring.
  rewrite Hinv. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The offset of a segment by signed distance d.                          *)
(* -------------------------------------------------------------------------- *)

(* Direction vector of the edge A -> B. *)
Definition seg_vec (A B : Point) : Vec := mkVec (px B - px A) (py B - py A).

(* The offset normal of edge A->B: its unit perpendicular. *)
Definition offset_normal (A B : Point) : Vec := unit_perp (seg_vec A B).

(* Offset a point P by signed distance d along edge A->B's normal. *)
Definition offset_point (A B P : Point) (d : R) : Point :=
  pt_translate P (d * vx (offset_normal A B)) (d * vy (offset_normal A B)).

(* The offset segment: both endpoints translated by the same d * normal. *)
Definition offset_seg (A B : Point) (d : R) : Point * Point :=
  (offset_point A B A d, offset_point A B B d).

(* -------------------------------------------------------------------------- *)
(* §3  Soundness 1: the offset is parallel to its source.                     *)
(* -------------------------------------------------------------------------- *)

(* Translating both endpoints by the same vector preserves the direction
   vector exactly. *)
Theorem offset_seg_dir : forall A B d,
  seg_vec (fst (offset_seg A B d)) (snd (offset_seg A B d)) = seg_vec A B.
Proof.
  intros A B d.
  unfold offset_seg, offset_point, seg_vec, pt_translate. simpl.
  apply Vec_eq; simpl; ring.
Qed.

(* Hence the offset segment is parallel to the source segment. *)
Corollary offset_seg_parallel : forall A B d,
  parallel (seg_vec (fst (offset_seg A B d)) (snd (offset_seg A B d)))
           (seg_vec A B).
Proof.
  intros A B d. rewrite offset_seg_dir. apply parallel_refl.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Soundness 2: each offset endpoint is at distance |d| from its source.  *)
(* -------------------------------------------------------------------------- *)

(* A nondegenerate edge has a nonzero direction vector. *)
Lemma seg_vec_nonzero : forall A B, A <> B -> seg_vec A B <> vzero.
Proof.
  intros [ax ay] [bx by_] Hne Hz.
  unfold seg_vec, vzero in Hz. simpl in Hz.
  injection Hz as Hx Hy.
  apply Hne. f_equal; lra.
Qed.

(* Squared distance from a point to its translate is the squared length
   of the translation vector. *)
Lemma dist_sq_translate : forall P a b,
  dist_sq P (pt_translate P a b) = a * a + b * b.
Proof.
  intros P a b. unfold dist_sq, pt_translate. simpl. ring.
Qed.

(* The defining offset property: the offset endpoint sits at Euclidean
   distance |d| from the source endpoint.  (Holds for both endpoints;
   stated for a generic P since the normal does not depend on P.) *)
Theorem offset_point_dist : forall A B P d,
  A <> B ->
  dist P (offset_point A B P d) = Rabs d.
Proof.
  intros A B P d Hne.
  unfold dist, offset_point, offset_normal.
  rewrite dist_sq_translate.
  replace ((d * vx (unit_perp (seg_vec A B))) * (d * vx (unit_perp (seg_vec A B))) +
           (d * vy (unit_perp (seg_vec A B))) * (d * vy (unit_perp (seg_vec A B))))
    with (d * d * vmag_sq (unit_perp (seg_vec A B)))
    by (unfold vmag_sq, vdot; ring).
  rewrite (vmag_sq_unit_perp (seg_vec A B) (seg_vec_nonzero A B Hne)).
  rewrite Rmult_1_r.
  replace (d * d) with (Rsqr d) by (unfold Rsqr; ring).
  apply sqrt_Rsqr_abs.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Soundness 2': perpendicular distance to the SOURCE LINE is |d|.        *)
(*                                                                            *)
(* The perpendicular (signed) distance from a point Q to the line through    *)
(* A with direction u is  vcross u (A->Q) / |u|.  For Q the offset of A by    *)
(* d along the unit normal, this equals exactly d (so its magnitude is |d|), *)
(* which is the line-relative statement of "offset at distance d".           *)
(* -------------------------------------------------------------------------- *)

Definition signed_perp_dist (A : Point) (u : Vec) (Q : Point) : R :=
  vcross u (mkVec (px Q - px A) (py Q - py A)) / vmag u.

Theorem offset_perp_dist_to_line : forall A B d,
  A <> B ->
  signed_perp_dist A (seg_vec A B) (offset_point A B A d) = d.
Proof.
  intros A B d Hne.
  pose proof (seg_vec_nonzero A B Hne) as Hnz.
  pose proof (vmag_sq_pos (seg_vec A B) Hnz) as Hpos.
  unfold signed_perp_dist, offset_point, offset_normal, unit_perp,
         pt_translate, vcross, vscale, vperp.
  set (u := seg_vec A B) in *.
  assert (Hmne : vmag u <> 0)
    by (unfold vmag; apply Rgt_not_eq; apply sqrt_lt_R0; exact Hpos).
  assert (Hpow : vmag u ^ 2 =
                 (px B - px A) * (px B - px A) + (py B - py A) * (py B - py A)).
  { replace (vmag u ^ 2) with (vmag u * vmag u) by ring.
    unfold vmag. rewrite sqrt_sqrt by (apply vmag_sq_nonneg).
    unfold u, vmag_sq, vdot, seg_vec. simpl. ring. }
  simpl.
  field_simplify_eq; [ | exact Hmne ].
  rewrite Hpow. ring.
Qed.
