(* ============================================================================
   NetTopologySuite.Proofs.Bbox
   ----------------------------------------------------------------------------
   Axis-aligned bounding boxes (envelopes) and the soundness of envelope-
   based rejection in segment-intersection tests.

   Every `LineIntersector` implementation in NTS starts by computing the
   bounding box of each segment and rejecting pairs whose envelopes are
   disjoint.  The geometric fact justifying this short-circuit is small but
   essential: a point on a segment always lies within the segment's bounding
   box, so segments with disjoint bounding boxes cannot share a point.

   The headline theorem `disjoint_bboxes_imply_no_shared_point` is that
   fact, kernel-checked.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From NTS.Proofs Require Import Distance Segment.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* A bounding box is represented by its low / high coordinates on each axis.  *)
(* Well-formedness (lo <= hi) is not encoded in the type; it follows from     *)
(* how bounding boxes are constructed (via `bbox_of_seg`).                    *)
(* -------------------------------------------------------------------------- *)

Record Bbox : Type := mkBbox {
  xlo : R; xhi : R;
  ylo : R; yhi : R
}.

Definition in_bbox (b : Bbox) (p : Point) : Prop :=
  xlo b <= px p <= xhi b /\ ylo b <= py p <= yhi b.

Definition bbox_of_seg (s : Segment) : Bbox :=
  mkBbox (Rmin (px (sp0 s)) (px (sp1 s)))
         (Rmax (px (sp0 s)) (px (sp1 s)))
         (Rmin (py (sp0 s)) (py (sp1 s)))
         (Rmax (py (sp0 s)) (py (sp1 s))).

Definition bbox_disjoint (b1 b2 : Bbox) : Prop :=
  xhi b1 < xlo b2 \/ xhi b2 < xlo b1 \/
  yhi b1 < ylo b2 \/ yhi b2 < ylo b1.

(* -------------------------------------------------------------------------- *)
(* The bounding box of a segment contains both endpoints.                     *)
(* -------------------------------------------------------------------------- *)

Lemma bbox_of_seg_contains_sp0 : forall s, in_bbox (bbox_of_seg s) (sp0 s).
Proof.
  intros s. unfold in_bbox, bbox_of_seg. simpl.
  pose proof (Rmin_l (px (sp0 s)) (px (sp1 s))).
  pose proof (Rmax_l (px (sp0 s)) (px (sp1 s))).
  pose proof (Rmin_l (py (sp0 s)) (py (sp1 s))).
  pose proof (Rmax_l (py (sp0 s)) (py (sp1 s))).
  lra.
Qed.

Lemma bbox_of_seg_contains_sp1 : forall s, in_bbox (bbox_of_seg s) (sp1 s).
Proof.
  intros s. unfold in_bbox, bbox_of_seg. simpl.
  pose proof (Rmin_r (px (sp0 s)) (px (sp1 s))).
  pose proof (Rmax_r (px (sp0 s)) (px (sp1 s))).
  pose proof (Rmin_r (py (sp0 s)) (py (sp1 s))).
  pose proof (Rmax_r (py (sp0 s)) (py (sp1 s))).
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* The bounding box of a segment contains every point on the segment.         *)
(* This generalises `bbox_of_seg_contains_sp0/sp1` from the endpoints to the  *)
(* whole closed segment.                                                      *)
(* -------------------------------------------------------------------------- *)

Lemma bbox_of_seg_contains_between : forall s Q,
  between (sp0 s) (sp1 s) Q -> in_bbox (bbox_of_seg s) Q.
Proof.
  intros s Q HQ.
  pose proof (between_in_coord_range (sp0 s) (sp1 s) Q HQ) as [HXrange HYrange].
  unfold in_bbox, bbox_of_seg. simpl.
  split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Disjointness is symmetric.                                                 *)
(* -------------------------------------------------------------------------- *)

Lemma bbox_disjoint_sym : forall b1 b2,
  bbox_disjoint b1 b2 <-> bbox_disjoint b2 b1.
Proof.
  intros b1 b2. unfold bbox_disjoint. split; intros [H|[H|[H|H]]]; tauto.
Qed.

(* -------------------------------------------------------------------------- *)
(* If a point lies in two boxes simultaneously, those boxes are not disjoint. *)
(* -------------------------------------------------------------------------- *)

Lemma shared_point_implies_not_disjoint : forall b1 b2 p,
  in_bbox b1 p -> in_bbox b2 p -> ~ bbox_disjoint b1 b2.
Proof.
  intros b1 b2 p [[Hx1 Hx2] [Hy1 Hy2]] [[Hx3 Hx4] [Hy3 Hy4]] Hd.
  unfold bbox_disjoint in Hd.
  destruct Hd as [H | [H | [H | H]]]; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Headline theorem: if two segments have disjoint bounding boxes, they       *)
(* share no point.  This is the formal justification for envelope-based      *)
(* rejection in `LineIntersector` and friends.                                *)
(* -------------------------------------------------------------------------- *)

Theorem disjoint_bboxes_imply_no_shared_point : forall s1 s2,
  bbox_disjoint (bbox_of_seg s1) (bbox_of_seg s2) ->
  ~ exists X, between (sp0 s1) (sp1 s1) X /\ between (sp0 s2) (sp1 s2) X.
Proof.
  intros s1 s2 Hdisj [X [HX1 HX2]].
  apply (shared_point_implies_not_disjoint
           (bbox_of_seg s1) (bbox_of_seg s2) X).
  - apply bbox_of_seg_contains_between. exact HX1.
  - apply bbox_of_seg_contains_between. exact HX2.
  - exact Hdisj.
Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit.                                                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions bbox_of_seg_contains_between.
Print Assumptions disjoint_bboxes_imply_no_shared_point.
