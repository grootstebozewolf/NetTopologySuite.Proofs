(* ============================================================================
   NetTopologySuite.Proofs.CurvedCapObligation
   ----------------------------------------------------------------------------
   Named modulo-QEX for curved-polygon CAP after exact noding.

   Domain.  Pairs of curved polygons whose boundaries are finite unions of
   curve segments (chords and/or circular arcs), filled by the corpus
   Jordan/parity convention (Geometry / CurvePolygon as appropriate).
   Positive-radius closed discs inhabit the domain as two-semicircle
   CurvePolygons whose fill is Disk.in_disk.

   Conclusion (QEX until proved in general).  After exact noding of
   ∂A ∪ ∂B, the extracted overlay faces labelled CAP equal the point-set
   A ∩ B.

   This rung is ONLY that gap.  Separate sentences stay separate:

     * abstract boolean_op Intersection (CAP) is already QED
       (`Overlay.boolean_op`, `boolean_op_intersection_self`);
     * two-disc CAP = lens is already QED (`DiscOverlay`);
     * G1 is CAP self (A ∩ A = A), not this;
     * two-body kiss / TOUCH is `OverlayTouchRow` (#677), not this;
     * self-kiss is not this.

   Honest recording (CircGamma roast).  The obligation is a Prop/Record
   with domain hypotheses and the CAP = intersection conclusion — not a
   status flag, not `right; exact some_qex_bool`.  No new Axiom.  The
   general CurvePolygon statement is the named residual
   `curved_cap_on_curve_polygons`; we do not inhabit it.  What is Qed:

     * `curved_cap_obligation_specializes_to_disc_lens` — on discs the
       conclusion *is* `lens` / `disc_overlay Intersection`;
     * `two_disc_cap_discharges_curved_obligation` — the Record is
       inhabited when both bodies are positive-radius discs (noding =
       `DiscOverlay.lens_boundary_is_radical_node`);
     * `curved_cap_modulo_qex` — that inhabitant is equivalent to the
       already-Qed lens identity (the remaining stop, restricted to
       discs);
     * `touch_cap_faces_not_II` — if the obligation holds on a TOUCH
       pair, extracted CAP faces cannot be an II 2-cell
       (`T_cap_not_2cell` / `touch_no_II_2cell`).

   Not attempted: general curved noding, arrangement faces, or
   `arc_overlay_correct_chord_approx` (chord-approx lane, different
   claim).  OverlayCorrectness stays the linear OverlayNG headline.

   WITNESS topic: overlay · claimId: ov-curved-cap-qex
   witness: disc-cap-lens · board: OverlayNGCurve / G-family

   Full-only: imports DiscOverlay / OverlayTouchRow.
   Classical-reals trio only (see Print Assumptions).  No new axioms.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Disk Overlay CurveGeometry
                               DiscOverlay OverlayTouchRow.

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

Definition point_set_intersection (A B : CurvedFilled) (p : Point) : Prop :=
  cf_fill A p /\ cf_fill B p.

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
         curve_polygon_boundary. cbn.
  rewrite app_nil_r. reflexivity.
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
(* §4  The obligation — domain + noding + CAP = A ∩ B.                        *)
(*                                                                            *)
(* [extracted_cap_faces] is whatever a noder+extractor would emit for CAP.    *)
(* [H_exact_noding] is the noding hyp the consumer supplies.  On discs that   *)
(* hyp is [disc_pair_exactly_noded].  The Record is the remaining stop; it    *)
(* is not a status enum.                                                      *)
(* -------------------------------------------------------------------------- *)

Record CurvedCapExactNodingObligation
    (A B : CurvedFilled)
    (H_exact_noding : Prop)
    (extracted_cap_faces : Point -> Prop) : Prop :=
  mk_curved_cap_obligation {
    cco_domain : curved_filled_domain A B;
    cco_noding : H_exact_noding;
    cco_cap_eq_intersection :
      forall p, extracted_cap_faces p <-> point_set_intersection A B p
  }.

(** Named obligation Prop (Definition alias of the Record — the claims
    gate scans Definition/Theorem, not Record). *)
Definition curved_cap_exact_noding_obligation :=
  CurvedCapExactNodingObligation.

(** Residual QEX.  Same obligation on a CurvePolygon pair with an abstract
    Jordan/parity fill (not [to_geometry] chord approximation).  No
    inhabitant is constructed — general curved noding is not this rung. *)
Definition curved_cap_on_curve_polygons (A B : CurvePolygon)
    (fillA fillB : Point -> Prop)
    (H_exact_noding : Prop)
    (extracted_cap_faces : Point -> Prop) : Prop :=
  valid_curve_polygon A ->
  valid_curve_polygon B ->
  curved_cap_exact_noding_obligation
    (curve_polygon_filled A fillA)
    (curve_polygon_filled B fillB)
    H_exact_noding
    extracted_cap_faces.

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
(* §5  Disc slice — conclusion is lens / boolean_op Intersection.             *)
(* -------------------------------------------------------------------------- *)

Lemma disc_intersection_is_lens :
  forall (A B : Disk) (p : Point),
    point_set_intersection (disc_filled A) (disc_filled B) p <-> lens A B p.
Proof.
  intros A B p. unfold point_set_intersection, disc_filled, lens. cbn.
  reflexivity.
Qed.

Lemma disc_overlay_cap_is_lens :
  forall (A B : Disk) (p : Point),
    disc_overlay Intersection A B p <-> lens A B p.
Proof.
  intros A B p. apply disc_overlay_cap.
Qed.

(* WITNESS {"claimId":"ov-curved-cap-qex","topic":"overlay","lemma":"curved_cap_obligation_specializes_to_disc_lens","title":"On full discs the curved-CAP conclusion is lens / boolean_op Intersection","file":"theories/CurvedCapObligation.v","witness":"disc-cap-lens","board":"OverlayNGCurve / G-family"} *)

Theorem curved_cap_obligation_specializes_to_disc_lens :
  forall (A B : Disk) (p : Point),
    point_set_intersection (disc_filled A) (disc_filled B) p <->
    disc_overlay Intersection A B p.
Proof.
  intros A B p.
  rewrite disc_intersection_is_lens.
  symmetry. apply disc_overlay_cap_is_lens.
Qed.

Theorem two_disc_cap_discharges_curved_obligation :
  forall A B : Disk,
    0 < dradius A ->
    0 < dradius B ->
    curved_cap_exact_noding_obligation
      (disc_filled A) (disc_filled B)
      (disc_pair_exactly_noded A B)
      (disc_overlay Intersection A B).
Proof.
  intros A B HrA HrB.
  refine (mk_curved_cap_obligation _ _ _ _ _ _ _).
  - exact (disc_pair_domain A B HrA HrB).
  - exact (disc_pair_exactly_noded_hold A B).
  - intros p. apply curved_cap_obligation_specializes_to_disc_lens.
Qed.

(* WITNESS {"claimId":"ov-curved-cap-qex","topic":"overlay","lemma":"curved_cap_modulo_qex","title":"Disc-slice curved-CAP obligation is the Qed lens identity; CurvePolygon residual stays the named Prop","file":"theories/CurvedCapObligation.v","witness":"disc-cap-lens","board":"OverlayNGCurve / G-family"} *)

(** Named remaining stop.  On positive-radius discs the obligation is
    equivalent to CAP = lens = [disc_overlay Intersection] (already Qed
    in DiscOverlay).  The same Record at a general CurvePolygon pair
    ([curved_cap_on_curve_polygons]) is not constructed. *)
Theorem curved_cap_modulo_qex :
  forall A B : Disk,
    0 < dradius A ->
    0 < dradius B ->
    curved_cap_exact_noding_obligation
      (disc_filled A) (disc_filled B)
      (disc_pair_exactly_noded A B)
      (disc_overlay Intersection A B)
    <->
    (forall p, disc_overlay Intersection A B p <-> lens A B p).
Proof.
  intros A B HrA HrB. split.
  - intros [_ _ Hcap] p.
    rewrite (Hcap p).
    apply disc_intersection_is_lens.
  - intros _.
    exact (two_disc_cap_discharges_curved_obligation A B HrA HrB).
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  TOUCH: CAP faces cannot be II 2-cells (#677).                          *)
(*                                                                            *)
(* kiss ≠ CAP; not G1.  If the obligation holds on a TOUCH pair, extracted    *)
(* CAP equals the lens, which contains no open disc.                          *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"ov-curved-cap-qex","topic":"overlay","lemma":"touch_cap_faces_not_II","title":"On TOUCH, obligation CAP faces are not an II 2-cell","file":"theories/CurvedCapObligation.v","witness":"disc-cap-lens","board":"OverlayNGCurve / G-family"} *)

Theorem touch_cap_faces_not_II :
  forall (A B : Disk) (Hnod : Prop) (extracted_cap_faces : Point -> Prop),
    0 < dradius A ->
    0 < dradius B ->
    disks_touch A B ->
    curved_cap_exact_noding_obligation
      (disc_filled A) (disc_filled B) Hnod extracted_cap_faces ->
    region_not_2cell extracted_cap_faces /\
    (forall p, ~ (in_disk_int A p /\ in_disk_int B p)).
Proof.
  intros A B Hnod extract HrA HrB Ht [_ _ Hcap].
  split.
  - intros q rho Hrho.
    destruct (T_cap_not_2cell A B HrA HrB Ht q rho Hrho) as [p [Hin Hnlens]].
    exists p. split; [exact Hin|].
    intros Hex.
    apply Hnlens.
    apply disc_intersection_is_lens.
    apply Hcap.
    exact Hex.
  - apply touch_no_II_2cell. exact Ht.
Qed.

Corollary touch_disc_overlay_cap_not_II :
  forall A B : Disk,
    0 < dradius A ->
    0 < dradius B ->
    disks_touch A B ->
    region_not_2cell (disc_overlay Intersection A B) /\
    (forall p, ~ (in_disk_int A p /\ in_disk_int B p)).
Proof.
  intros A B HrA HrB Ht.
  apply (touch_cap_faces_not_II A B
           (disc_pair_exactly_noded A B)
           (disc_overlay Intersection A B) HrA HrB Ht).
  apply two_disc_cap_discharges_curved_obligation; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §7  Audit footprint.                                                        *)
(* -------------------------------------------------------------------------- *)

Print Assumptions disc_upper_arc_valid.
Print Assumptions disc_pair_exactly_noded_hold.
Print Assumptions valid_curve_polygon_inhabits_domain.
Print Assumptions curved_cap_obligation_specializes_to_disc_lens.
Print Assumptions two_disc_cap_discharges_curved_obligation.
Print Assumptions curved_cap_modulo_qex.
Print Assumptions touch_cap_faces_not_II.
Print Assumptions touch_disc_overlay_cap_not_II.
