(* ============================================================================
   NetTopologySuite.Proofs.RelateMatrixLineLine
   ----------------------------------------------------------------------------
   Issue #67 session 8 (S8): line×line regime→witness selection.

   A regime-indexed function `line_pair_fill` that SELECTS (does not compute
   from geometry) one of the S2 witness matrices from `RelateLineLine.v` per
   `LinePairRegime`.  This is a witness-selection API, not a DE-9IM matrix
   computation: deciding a regime from coordinates and proving the selected
   witness is the configuration's true DE-9IM is the deferred RelateNG-noding
   step (S13+).  Romanschek paper matrices are oracle pins (S3), not targets.

   Delivers:

     - `LinePairRegime` + `line_pair_fill` (regime → witness matrix)
     - `classify_line_pair` recording which S2 geometry guard names each regime
     - Fill = witness equalities
     - `*_fill_witness`: the selected witness satisfies the regime's predicate
       (constant facts; the regime hypothesis is NOT consumed)
     - Mutual-exclusion lemmas (genuine geometry) for rejection vs share /
       proper cross / overlap

   Honest scoping: closed segments; endpoint-only Touches witness lives in
   `RelateBoundary.v` (S4b).  Area-line fill is S9 (`RelateMatrixAreaLine.v`).

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import DE9IM Distance RelateLineLine.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Regime enum + matrix fill.                                                 *)
(* -------------------------------------------------------------------------- *)

Inductive LinePairRegime : Type :=
| LPR_Disjoint
| LPR_ProperCross
| LPR_Share
| LPR_CollinearOverlap.

Definition line_pair_fill (r : LinePairRegime) : IntersectionMatrix :=
  match r with
  | LPR_Disjoint         => ll_matrix_disjoint
  | LPR_ProperCross      => ll_matrix_point_ii
  | LPR_Share            => ll_matrix_point_ii
  | LPR_CollinearOverlap => ll_matrix_overlap_ii
  end.

Lemma line_pair_fill_disjoint_eq :
  line_pair_fill LPR_Disjoint = ll_matrix_disjoint.
Proof. reflexivity. Qed.

Lemma line_pair_fill_proper_cross_eq :
  line_pair_fill LPR_ProperCross = ll_matrix_point_ii.
Proof. reflexivity. Qed.

Lemma line_pair_fill_share_eq :
  line_pair_fill LPR_Share = ll_matrix_point_ii.
Proof. reflexivity. Qed.

Lemma line_pair_fill_collinear_overlap_eq :
  line_pair_fill LPR_CollinearOverlap = ll_matrix_overlap_ii.
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Classifier — mirrors S2 guards.                                            *)
(* -------------------------------------------------------------------------- *)

Definition classify_line_pair (A B C D : Point) (r : LinePairRegime) : Prop :=
  match r with
  | LPR_Disjoint         => segments_rejected A B C D
  | LPR_ProperCross      => segments_proper_cross A B C D
  | LPR_Share            => segments_share A B C D
  | LPR_CollinearOverlap =>
      segments_collinear A B C D /\
      segments_interior_collinear_overlap A B C D
  end.

Lemma proper_cross_not_rejected :
  forall A B C D : Point,
    segments_proper_cross A B C D ->
    ~ segments_rejected A B C D.
Proof.
  intros A B C D [Hab Hcd] Hrej.
  unfold segments_rejected in Hrej.
  destruct Hrej as [Habpos | Hcdpos].
  - lra.
  - lra.
Qed.

Lemma collinear_overlap_not_proper_cross :
  forall A B C D : Point,
    segments_collinear A B C D ->
    segments_interior_collinear_overlap A B C D ->
    ~ segments_proper_cross A B C D.
Proof.
  intros A B C D Hcol _ Hcross.
  destruct Hcol as [Hac [Had [_ _]]].
  destruct Hcross as [Hprod _].
  rewrite Hac, Had in Hprod. lra.
Qed.

Lemma rejection_not_share :
  forall A B C D : Point,
    segments_rejected A B C D ->
    ~ segments_share A B C D.
Proof.
  intros A B C D Hrej Hshare.
  exact (line_line_rejected_not_share A B C D Hrej Hshare).
Qed.

Lemma share_not_rejected :
  forall A B C D : Point,
    segments_share A B C D ->
    ~ segments_rejected A B C D.
Proof.
  intros A B C D Hshare Hrej.
  exact (rejection_not_share A B C D Hrej Hshare).
Qed.

Lemma collinear_overlap_not_rejected :
  forall A B C D : Point,
    segments_collinear A B C D ->
    segments_interior_collinear_overlap A B C D ->
    ~ segments_rejected A B C D.
Proof.
  intros A B C D Hcol Hov Hrej.
  pose proof (line_line_collinear_overlap_share A B C D Hcol Hov) as Hshare.
  exact (share_not_rejected A B C D Hshare Hrej).
Qed.

(* -------------------------------------------------------------------------- *)
(* Witness facts: the selected witness satisfies the regime's predicate.      *)
(*                                                                            *)
(* These are constant facts about `line_pair_fill` (a regime → matrix map);   *)
(* they take no geometry hypothesis and make no geometry→matrix claim.  That  *)
(* a given segment pair actually falls in a regime, and that the selected     *)
(* witness is then its true DE-9IM, is the deferred RelateNG-noding step.     *)
(* -------------------------------------------------------------------------- *)

Theorem line_fill_disjoint_witness :
  im_disjoint (line_pair_fill LPR_Disjoint).
Proof.
  rewrite line_pair_fill_disjoint_eq. exact ll_matrix_disjoint_witness.
Qed.

Theorem line_fill_proper_cross_witness :
  im_crosses (line_pair_fill LPR_ProperCross) /\
  im_intersects (line_pair_fill LPR_ProperCross).
Proof.
  rewrite line_pair_fill_proper_cross_eq.
  split; [exact ll_matrix_point_ii_crosses_ll | exact ll_matrix_point_ii_intersects].
Qed.

Theorem line_fill_share_witness :
  im_intersects (line_pair_fill LPR_Share).
Proof.
  rewrite line_pair_fill_share_eq. exact ll_matrix_point_ii_intersects.
Qed.

Theorem line_fill_collinear_overlap_witness :
  im_overlaps (line_pair_fill LPR_CollinearOverlap).
Proof.
  rewrite line_pair_fill_collinear_overlap_eq. exact ll_matrix_overlap_ii_overlaps.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions line_fill_disjoint_witness.
Print Assumptions line_fill_proper_cross_witness.
Print Assumptions line_fill_share_witness.
Print Assumptions line_fill_collinear_overlap_witness.