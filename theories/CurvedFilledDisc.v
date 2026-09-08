(* ============================================================================
   NetTopologySuite.Proofs.CurvedFilledDisc
   ----------------------------------------------------------------------------
   Shared curved-filled carrier and two-semicircle disc encoding.

   Cap / Op / Kiss (#679–#681) all need the same CurvedFilled record, the
   same disc-as-two-semicircle CurvePolygon, and the same radical-node
   noding hyp.  Those used to live in CurvedCapObligation, which then
   became the accidental commons.  This module is the single definition
   site; the obligation files Require it and keep only their own Records
   and headlines.

   No new overlay theorem.  No remint of DiscOverlay radical math —
   `disc_pair_exactly_noded_hold` is `lens_boundary_is_radical_node`.

   Full-only: imports DiscOverlay / CurveGeometry.  Classical-reals trio
   only (see Print Assumptions).  No new axioms.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Disk CurveGeometry
                               ArcArcCircles DiscOverlay.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Curved filled bodies.                                                   *)
(*                                                                            *)
(* A curved polygon is a point-set fill together with a finite list of        *)
(* curve segments (the boundary).  CurvePolygon and Disk both embed.          *)
(* -------------------------------------------------------------------------- *)

Record CurvedFilled : Type := mkCurvedFilled {
  cf_fill : Point -> Prop;
  cf_boundary : list CurveSegment
}.

(** Every boundary segment is a chord or a non-collinear circular arc.
    Finite by the list carrier. *)
Definition finite_curve_boundary (A : CurvedFilled) : Prop :=
  Forall (fun s => match s with
                   | CSChord _ _ => True
                   | CSArc a => valid_arc a
                   end) (cf_boundary A).

Definition curved_filled_domain (A B : CurvedFilled) : Prop :=
  finite_curve_boundary A /\ finite_curve_boundary B.

Definition curve_polygon_boundary (cp : CurvePolygon) : list CurveSegment :=
  curve_outer cp ++ concat (curve_holes cp).

Definition curve_polygon_filled (cp : CurvePolygon) (fill : Point -> Prop)
  : CurvedFilled :=
  {| cf_fill := fill; cf_boundary := curve_polygon_boundary cp |}.

(* -------------------------------------------------------------------------- *)
(* §2  Positive-radius discs as curved polygons.                              *)
(*                                                                            *)
(* Two semicircle arcs: west–north–east and east–south–west.  Fill is the     *)
(* closed metric disc — not [to_geometry] chord approximation.                *)
(* -------------------------------------------------------------------------- *)

Definition disc_west (D : Disk) : Point :=
  mkPoint (px (dcentre D) - dradius D) (py (dcentre D)).
Definition disc_east (D : Disk) : Point :=
  mkPoint (px (dcentre D) + dradius D) (py (dcentre D)).
Definition disc_north (D : Disk) : Point :=
  mkPoint (px (dcentre D)) (py (dcentre D) + dradius D).
Definition disc_south (D : Disk) : Point :=
  mkPoint (px (dcentre D)) (py (dcentre D) - dradius D).

Definition disc_upper_arc (D : Disk) : CircularArc :=
  mkCircularArc (disc_west D) (disc_north D) (disc_east D).
Definition disc_lower_arc (D : Disk) : CircularArc :=
  mkCircularArc (disc_east D) (disc_south D) (disc_west D).

Definition disc_boundary (D : Disk) : list CurveSegment :=
  [CSArc (disc_upper_arc D); CSArc (disc_lower_arc D)].

Definition disc_filled (D : Disk) : CurvedFilled :=
  {| cf_fill := in_disk D; cf_boundary := disc_boundary D |}.

Definition disc_as_curve_polygon (D : Disk) : CurvePolygon :=
  mkCurvePolygon (disc_boundary D) [].

Lemma disc_upper_arc_valid :
  forall D : Disk, 0 < dradius D -> valid_arc (disc_upper_arc D).
Proof.
  intros D Hr.
  unfold valid_arc, disc_upper_arc, disc_west, disc_north, disc_east.
  cbn [arc_start arc_mid arc_end px py].
  nra.
Qed.

Lemma disc_lower_arc_valid :
  forall D : Disk, 0 < dradius D -> valid_arc (disc_lower_arc D).
Proof.
  intros D Hr.
  unfold valid_arc, disc_lower_arc, disc_east, disc_south, disc_west.
  cbn [arc_start arc_mid arc_end px py].
  nra.
Qed.

Lemma disc_finite_boundary :
  forall D : Disk, 0 < dradius D -> finite_curve_boundary (disc_filled D).
Proof.
  intros D Hr.
  unfold finite_curve_boundary, disc_filled, disc_boundary. cbn.
  constructor.
  - exact (disc_upper_arc_valid D Hr).
  - constructor.
    + exact (disc_lower_arc_valid D Hr).
    + constructor.
Qed.

Lemma disc_pair_domain :
  forall A B : Disk,
    0 < dradius A -> 0 < dradius B ->
    curved_filled_domain (disc_filled A) (disc_filled B).
Proof.
  intros A B HrA HrB.
  split; apply disc_finite_boundary; assumption.
Qed.

Lemma disc_filled_as_curve_polygon :
  forall D : Disk,
    disc_filled D =
    curve_polygon_filled (disc_as_curve_polygon D) (in_disk D).
Proof.
  intros D.
  unfold disc_filled, curve_polygon_filled, disc_as_curve_polygon,
         curve_polygon_boundary. cbn [curve_outer curve_holes].
  rewrite concat_nil, app_nil_r. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Exact noding of two circle boundaries (reused, not reminted).          *)
(*                                                                            *)
(* Every point on both circles of a positive-distance pair is a radical       *)
(* node — [DiscOverlay.lens_boundary_is_radical_node].  Coincident centres    *)
(* make the premise false, so the implication holds.  This is the disc        *)
(* slice of "exact noding of ∂A ∪ ∂B".  No curved noder is constructed.       *)
(* -------------------------------------------------------------------------- *)

Definition disc_pair_exactly_noded (A B : Disk) : Prop :=
  forall X : Point,
    0 < dist (dcentre A) (dcentre B) ->
    dist_sq (dcentre A) X = dradius A * dradius A ->
    dist_sq (dcentre B) X = dradius B * dradius B ->
    X = radical_point_plus (dcentre A) (dcentre B) (dradius A) (dradius B) \/
    X = radical_point_minus (dcentre A) (dcentre B) (dradius A) (dradius B).

Lemma disc_pair_exactly_noded_hold :
  forall A B : Disk, disc_pair_exactly_noded A B.
Proof.
  intros A B X Hd HA HB.
  apply (lens_boundary_is_radical_node A B X Hd HA HB).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Valid CurvePolygon inhabits the domain.                                 *)
(* -------------------------------------------------------------------------- *)

Lemma curve_ring_arcs_valid_concat :
  forall hs : list CurveRing,
    Forall valid_curve_ring hs ->
    Forall (fun s => match s with
                     | CSChord _ _ => True
                     | CSArc a => valid_arc a
                     end) (concat hs).
Proof.
  intros hs Hhs.
  induction hs as [|h hs IH]; simpl.
  - constructor.
  - inversion Hhs; subst.
    apply (proj2 (Forall_app _ _ _)).
    split.
    + destruct H1 as [Ha _]. exact Ha.
    + apply IH. exact H2.
Qed.

Lemma valid_curve_polygon_inhabits_domain :
  forall (A B : CurvePolygon) (fillA fillB : Point -> Prop),
    valid_curve_polygon A ->
    valid_curve_polygon B ->
    curved_filled_domain (curve_polygon_filled A fillA)
                         (curve_polygon_filled B fillB).
Proof.
  intros A B fillA fillB [HAo HAh] [HBo HBh].
  unfold curved_filled_domain, finite_curve_boundary,
         curve_polygon_filled, curve_polygon_boundary. cbn.
  split.
  - apply (proj2 (Forall_app _ _ _)).
    split.
    + destruct HAo as [Ha _]. exact Ha.
    + apply curve_ring_arcs_valid_concat. exact HAh.
  - apply (proj2 (Forall_app _ _ _)).
    split.
    + destruct HBo as [Ha _]. exact Ha.
    + apply curve_ring_arcs_valid_concat. exact HBh.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Audit footprint.                                                        *)
(* -------------------------------------------------------------------------- *)

Print Assumptions disc_upper_arc_valid.
Print Assumptions disc_pair_exactly_noded_hold.
Print Assumptions valid_curve_polygon_inhabits_domain.
