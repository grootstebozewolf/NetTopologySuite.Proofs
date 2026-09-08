(* ============================================================================
   NetTopologySuite.Proofs.CurvedCapObligation
   ----------------------------------------------------------------------------
   Named modulo-QEX for curved-polygon CAP after exact noding.

   Domain.  Pairs of curved polygons whose boundaries are finite unions of
   curve segments (chords and/or circular arcs), filled by the corpus
   Jordan/parity convention (Geometry / CurvePolygon as appropriate).
   Positive-radius closed discs inhabit the domain as two-semicircle
   CurvePolygons whose fill is Disk.in_disk.

   Carrier / disc encoding / radical-node noding live in
   `CurvedFilledDisc` (Require Export, so importers of this module still
   see `CurvedFilled`, `disc_filled`, `disc_pair_exactly_noded`).  This
   file owns only the CAP Record and the CAP headlines.

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

   Full-only: imports CurvedFilledDisc / OverlayTouchRow.
   Classical-reals trio only (see Print Assumptions).  No new axioms.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Export CurvedFilledDisc.
From NTS.Proofs Require Import Distance Disk Overlay CurveGeometry
                               DiscOverlay OverlayTouchRow.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Point-set intersection on CurvedFilled.                                *)
(* -------------------------------------------------------------------------- *)

Definition point_set_intersection (A B : CurvedFilled) (p : Point) : Prop :=
  cf_fill A p /\ cf_fill B p.

(* -------------------------------------------------------------------------- *)
(* §2  The obligation — domain + noding + CAP = A ∩ B.                        *)
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

(* -------------------------------------------------------------------------- *)
(* §3  Disc slice — conclusion is lens / boolean_op Intersection.             *)
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
  unfold point_set_intersection, disc_filled, disc_overlay,
         overlayng_cap, lens. cbn.
  reflexivity.
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
(* §4  TOUCH: CAP faces cannot be II 2-cells (#677).                          *)
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
(* §5  Audit footprint.                                                        *)
(* -------------------------------------------------------------------------- *)

Print Assumptions curved_cap_obligation_specializes_to_disc_lens.
Print Assumptions two_disc_cap_discharges_curved_obligation.
Print Assumptions curved_cap_modulo_qex.
Print Assumptions touch_cap_faces_not_II.
Print Assumptions touch_disc_overlay_cap_not_II.
