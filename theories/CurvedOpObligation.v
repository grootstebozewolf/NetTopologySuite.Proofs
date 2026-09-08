(* ============================================================================
   NetTopologySuite.Proofs.CurvedOpObligation
   ----------------------------------------------------------------------------
   Named modulo-QEX for curved-polygon CUP / SUB / XOR after exact noding.

   Sibling of CurvedCapObligation (#679): same CurvedFilled carrier, same
   two-semicircle disc encoding, same radical-node noding hyp.  This file
   does not remint that scaffolding.  One Record is parameterized by
   Overlay.BooleanOp; CAP is the Intersection instance (Qed equivalence,
   no rewrite of the CAP module).

   Domain.  Pairs of curved polygons whose boundaries are finite unions of
   curve segments (chords and/or circular arcs), filled by the corpus
   Jordan/parity convention.  Positive-radius closed discs inhabit the
   domain as two-semicircle CurvePolygons whose fill is Disk.in_disk.

   Conclusion (QEX until proved in general).  After exact noding of
   ∂A ∪ ∂B, the extracted overlay faces labelled op equal the point-set
   boolean_op:

     CUP = A ∪ B    SUB = A ∖ B    XOR = A △ B    CAP = A ∩ B

   This rung is ONLY that gap.  Separate sentences stay separate:

     * abstract boolean_op is already QED (`Overlay.boolean_op`);
     * two-disc closed forms are already QED (`DiscOverlay`:
       blob / crescent / crescents / lens);
     * G1–G4 are the self-ops (A ⋆ A), not this;
     * two-body kiss / TOUCH is `OverlayTouchRow` (#677), not this;
     * self-kiss is not this.

   Honest recording (CircGamma roast).  The obligation is a Prop/Record
   with domain hypotheses and the faces = boolean_op conclusion — not a
   status flag, not a vacuous diploma.  No new Axiom.  The general
   CurvePolygon statement is the named residual
   `curved_op_on_curve_polygons`; we do not inhabit it.  What is Qed:

     * `curved_op_obligation_specializes_to_disc` — on discs the
       conclusion *is* `disc_overlay op` (blob / crescent / crescents /
       lens);
     * `two_disc_op_discharges_curved_obligation` — the Record is
       inhabited when both bodies are positive-radius discs (noding =
       `DiscOverlay.lens_boundary_is_radical_node`);
     * `curved_op_modulo_qex` — that inhabitant is equivalent to the
       already-Qed closed form (the remaining stop, restricted to discs);
     * named CUP/SUB/XOR corollaries pointing at blob / crescent /
       crescents;
     * `curved_cap_is_op_intersection` — #679 CAP Record ≡ this Record
       at Intersection;
     * `disc_cap_or_xor_iff_cup` — (A∩B)∪(A△B)=A∪B on discs
       (`lens_or_crescents_iff_blob`, already in DiscOverlay).

   Not attempted: general curved noding, arrangement faces, or
   `arc_overlay_correct_chord_approx` (chord-approx lane, different
   claim).  OverlayCorrectness stays the linear OverlayNG headline.

   WITNESS topic: overlay · claimId: ov-curved-ops-qex
   witness: disc-ops-closed-form · board: OverlayNGCurve / G-family

   Full-only: imports CurvedCapObligation (and thus DiscOverlay).
   Classical-reals trio only (see Print Assumptions).  No new axioms.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import Distance Disk Overlay CurveGeometry
                               DiscOverlay CurvedCapObligation.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Point-set boolean_op on CurvedFilled.                                  *)
(*                                                                            *)
(* Same four constructors as Overlay.boolean_op, over cf_fill.  CAP's         *)
(* point_set_intersection is the Intersection branch.                         *)
(* -------------------------------------------------------------------------- *)

Definition point_set_op (op : BooleanOp) (A B : CurvedFilled) (p : Point) : Prop :=
  match op with
  | Union        => cf_fill A p \/ cf_fill B p
  | Intersection => cf_fill A p /\ cf_fill B p
  | Difference   => cf_fill A p /\ ~ cf_fill B p
  | SymDiff      => (cf_fill A p /\ ~ cf_fill B p) \/
                    (cf_fill B p /\ ~ cf_fill A p)
  end.

Lemma point_set_op_intersection :
  forall (A B : CurvedFilled) (p : Point),
    point_set_op Intersection A B p <-> point_set_intersection A B p.
Proof. intros. reflexivity. Qed.

Lemma point_set_op_disc_overlay :
  forall (op : BooleanOp) (A B : Disk) (p : Point),
    point_set_op op (disc_filled A) (disc_filled B) p <->
    disc_overlay op A B p.
Proof. intros op A B p. destruct op; reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The obligation — domain + noding + faces = boolean_op.                 *)
(*                                                                            *)
(* Parameterized by BooleanOp.  Named CUP/SUB/XOR aliases are the same        *)
(* Record at Union / Difference / SymDiff.  [extracted_faces] is whatever     *)
(* a noder+extractor would emit for that op.  [H_exact_noding] is the         *)
(* noding hyp the consumer supplies.  On discs that hyp is                    *)
(* [disc_pair_exactly_noded] (reused from CurvedCapObligation).               *)
(* -------------------------------------------------------------------------- *)

Record CurvedOpExactNodingObligation
    (op : BooleanOp)
    (A B : CurvedFilled)
    (H_exact_noding : Prop)
    (extracted_faces : Point -> Prop) : Prop :=
  mk_curved_op_obligation {
    coo_domain : curved_filled_domain A B;
    coo_noding : H_exact_noding;
    coo_faces_eq_boolean :
      forall p, extracted_faces p <-> point_set_op op A B p
  }.

(** Named obligation Prop (Definition alias of the Record — the claims
    gate scans Definition/Theorem, not Record). *)
Definition curved_op_exact_noding_obligation :=
  CurvedOpExactNodingObligation.

Definition CurvedCupExactNodingObligation :=
  CurvedOpExactNodingObligation Union.
Definition CurvedSubExactNodingObligation :=
  CurvedOpExactNodingObligation Difference.
Definition CurvedXorExactNodingObligation :=
  CurvedOpExactNodingObligation SymDiff.

Definition curved_cup_exact_noding_obligation := CurvedCupExactNodingObligation.
Definition curved_sub_exact_noding_obligation := CurvedSubExactNodingObligation.
Definition curved_xor_exact_noding_obligation := CurvedXorExactNodingObligation.

(* -------------------------------------------------------------------------- *)
(* §3  Residual QEX on CurvePolygon.                                          *)
(*                                                                            *)
(* Same obligation on a CurvePolygon pair with an abstract Jordan/parity      *)
(* fill (not [to_geometry] chord approximation).  No inhabitant is            *)
(* constructed — general curved noding is not this rung.                      *)
(* -------------------------------------------------------------------------- *)

Definition curved_op_on_curve_polygons (op : BooleanOp)
    (A B : CurvePolygon)
    (fillA fillB : Point -> Prop)
    (H_exact_noding : Prop)
    (extracted_faces : Point -> Prop) : Prop :=
  valid_curve_polygon A ->
  valid_curve_polygon B ->
  curved_op_exact_noding_obligation op
    (curve_polygon_filled A fillA)
    (curve_polygon_filled B fillB)
    H_exact_noding
    extracted_faces.

Definition curved_cup_on_curve_polygons :=
  curved_op_on_curve_polygons Union.
Definition curved_sub_on_curve_polygons :=
  curved_op_on_curve_polygons Difference.
Definition curved_xor_on_curve_polygons :=
  curved_op_on_curve_polygons SymDiff.

(* -------------------------------------------------------------------------- *)
(* §4  CAP (#679) is the Intersection instance.                               *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"ov-curved-ops-qex","topic":"overlay","lemma":"curved_cap_is_op_intersection","title":"CAP Record is the Intersection instance of the parameterized curved-op obligation","file":"theories/CurvedOpObligation.v","witness":"disc-ops-closed-form","board":"OverlayNGCurve / G-family"} *)

Theorem curved_cap_is_op_intersection :
  forall (A B : CurvedFilled) (Hnod : Prop) (extract : Point -> Prop),
    curved_cap_exact_noding_obligation A B Hnod extract <->
    curved_op_exact_noding_obligation Intersection A B Hnod extract.
Proof.
  intros A B Hnod extract. split.
  - intros [Hd Hn Heq]. constructor; assumption.
  - intros [Hd Hn Heq]. constructor; assumption.
Qed.

Theorem curved_cap_on_curve_polygons_is_op_intersection :
  forall (A B : CurvePolygon) (fillA fillB : Point -> Prop)
         (Hnod : Prop) (extract : Point -> Prop),
    curved_cap_on_curve_polygons A B fillA fillB Hnod extract <->
    curved_op_on_curve_polygons Intersection A B fillA fillB Hnod extract.
Proof.
  intros A B fillA fillB Hnod extract. split;
    intros H va vb; apply curved_cap_is_op_intersection; exact (H va vb).
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Disc slice — conclusion is disc_overlay / blob / crescent / crescents. *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"ov-curved-ops-qex","topic":"overlay","lemma":"curved_op_obligation_specializes_to_disc","title":"On full discs the curved-op conclusion is disc_overlay (blob / crescent / crescents / lens)","file":"theories/CurvedOpObligation.v","witness":"disc-ops-closed-form","board":"OverlayNGCurve / G-family"} *)

Theorem curved_op_obligation_specializes_to_disc :
  forall (op : BooleanOp) (A B : Disk) (p : Point),
    point_set_op op (disc_filled A) (disc_filled B) p <->
    disc_overlay op A B p.
Proof.
  intros op A B p. apply point_set_op_disc_overlay.
Qed.

Corollary curved_cup_obligation_specializes_to_disc_blob :
  forall (A B : Disk) (p : Point),
    point_set_op Union (disc_filled A) (disc_filled B) p <-> blob A B p.
Proof. intros. reflexivity. Qed.

Corollary curved_sub_obligation_specializes_to_disc_crescent :
  forall (A B : Disk) (p : Point),
    point_set_op Difference (disc_filled A) (disc_filled B) p <-> crescent A B p.
Proof. intros. reflexivity. Qed.

Corollary curved_xor_obligation_specializes_to_disc_crescents :
  forall (A B : Disk) (p : Point),
    point_set_op SymDiff (disc_filled A) (disc_filled B) p <-> crescents A B p.
Proof. intros. reflexivity. Qed.

Theorem two_disc_op_discharges_curved_obligation :
  forall (op : BooleanOp) (A B : Disk),
    0 < dradius A ->
    0 < dradius B ->
    curved_op_exact_noding_obligation op
      (disc_filled A) (disc_filled B)
      (disc_pair_exactly_noded A B)
      (disc_overlay op A B).
Proof.
  intros op A B HrA HrB.
  constructor.
  - exact (disc_pair_domain A B HrA HrB).
  - exact (disc_pair_exactly_noded_hold A B).
  - intros p. apply point_set_op_disc_overlay.
Qed.

Corollary two_disc_cup_discharges_curved_obligation :
  forall A B : Disk,
    0 < dradius A ->
    0 < dradius B ->
    curved_cup_exact_noding_obligation
      (disc_filled A) (disc_filled B)
      (disc_pair_exactly_noded A B)
      (disc_overlay Union A B).
Proof.
  intros A B HrA HrB.
  exact (two_disc_op_discharges_curved_obligation Union A B HrA HrB).
Qed.

Corollary two_disc_sub_discharges_curved_obligation :
  forall A B : Disk,
    0 < dradius A ->
    0 < dradius B ->
    curved_sub_exact_noding_obligation
      (disc_filled A) (disc_filled B)
      (disc_pair_exactly_noded A B)
      (disc_overlay Difference A B).
Proof.
  intros A B HrA HrB.
  exact (two_disc_op_discharges_curved_obligation Difference A B HrA HrB).
Qed.

Corollary two_disc_xor_discharges_curved_obligation :
  forall A B : Disk,
    0 < dradius A ->
    0 < dradius B ->
    curved_xor_exact_noding_obligation
      (disc_filled A) (disc_filled B)
      (disc_pair_exactly_noded A B)
      (disc_overlay SymDiff A B).
Proof.
  intros A B HrA HrB.
  exact (two_disc_op_discharges_curved_obligation SymDiff A B HrA HrB).
Qed.

(* WITNESS {"claimId":"ov-curved-ops-qex","topic":"overlay","lemma":"curved_op_modulo_qex","title":"Disc-slice curved-op obligation is the Qed disc_overlay identity; CurvePolygon residual stays the named Prop","file":"theories/CurvedOpObligation.v","witness":"disc-ops-closed-form","board":"OverlayNGCurve / G-family"} *)

(** Named remaining stop.  On positive-radius discs the obligation is
    equivalent to faces = [disc_overlay op] (already Qed in DiscOverlay).
    The same Record at a general CurvePolygon pair
    ([curved_op_on_curve_polygons]) is not constructed. *)
Theorem curved_op_modulo_qex :
  forall (op : BooleanOp) (A B : Disk),
    0 < dradius A ->
    0 < dradius B ->
    curved_op_exact_noding_obligation op
      (disc_filled A) (disc_filled B)
      (disc_pair_exactly_noded A B)
      (disc_overlay op A B)
    <->
    (forall p, disc_overlay op A B p <->
               point_set_op op (disc_filled A) (disc_filled B) p).
Proof.
  intros op A B HrA HrB. split.
  - intros [_ _ Hfaces] p.
    rewrite (Hfaces p).
    reflexivity.
  - intros _.
    exact (two_disc_op_discharges_curved_obligation op A B HrA HrB).
Qed.

Theorem curved_cup_modulo_qex :
  forall A B : Disk,
    0 < dradius A ->
    0 < dradius B ->
    curved_cup_exact_noding_obligation
      (disc_filled A) (disc_filled B)
      (disc_pair_exactly_noded A B)
      (disc_overlay Union A B)
    <->
    (forall p, disc_overlay Union A B p <-> blob A B p).
Proof.
  intros A B HrA HrB. split.
  - intros [_ _ Hfaces] p.
    rewrite (Hfaces p).
    reflexivity.
  - intros _.
    exact (two_disc_cup_discharges_curved_obligation A B HrA HrB).
Qed.

Theorem curved_sub_modulo_qex :
  forall A B : Disk,
    0 < dradius A ->
    0 < dradius B ->
    curved_sub_exact_noding_obligation
      (disc_filled A) (disc_filled B)
      (disc_pair_exactly_noded A B)
      (disc_overlay Difference A B)
    <->
    (forall p, disc_overlay Difference A B p <-> crescent A B p).
Proof.
  intros A B HrA HrB. split.
  - intros [_ _ Hfaces] p.
    rewrite (Hfaces p).
    reflexivity.
  - intros _.
    exact (two_disc_sub_discharges_curved_obligation A B HrA HrB).
Qed.

Theorem curved_xor_modulo_qex :
  forall A B : Disk,
    0 < dradius A ->
    0 < dradius B ->
    curved_xor_exact_noding_obligation
      (disc_filled A) (disc_filled B)
      (disc_pair_exactly_noded A B)
      (disc_overlay SymDiff A B)
    <->
    (forall p, disc_overlay SymDiff A B p <-> crescents A B p).
Proof.
  intros A B HrA HrB. split.
  - intros [_ _ Hfaces] p.
    rewrite (Hfaces p).
    reflexivity.
  - intros _.
    exact (two_disc_xor_discharges_curved_obligation A B HrA HrB).
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  (A ∩ B) ∪ (A △ B) = A ∪ B on discs (already in DiscOverlay).           *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"ov-curved-ops-qex","topic":"overlay","lemma":"disc_cap_or_xor_iff_cup","title":"On discs, CAP ∪ XOR = CUP (lens ∨ crescents ↔ blob)","file":"theories/CurvedOpObligation.v","witness":"disc-ops-closed-form","board":"OverlayNGCurve / G-family"} *)

Theorem disc_cap_or_xor_iff_cup :
  forall (A B : Disk) (p : Point),
    disc_overlay Intersection A B p \/ disc_overlay SymDiff A B p <->
    disc_overlay Union A B p.
Proof.
  intros A B p.
  apply lens_or_crescents_iff_blob.
Qed.

(* -------------------------------------------------------------------------- *)
(* §7  Audit footprint.                                                        *)
(* -------------------------------------------------------------------------- *)

Print Assumptions point_set_op_disc_overlay.
Print Assumptions curved_cap_is_op_intersection.
Print Assumptions curved_cap_on_curve_polygons_is_op_intersection.
Print Assumptions curved_op_obligation_specializes_to_disc.
Print Assumptions curved_cup_obligation_specializes_to_disc_blob.
Print Assumptions curved_sub_obligation_specializes_to_disc_crescent.
Print Assumptions curved_xor_obligation_specializes_to_disc_crescents.
Print Assumptions two_disc_op_discharges_curved_obligation.
Print Assumptions two_disc_cup_discharges_curved_obligation.
Print Assumptions two_disc_sub_discharges_curved_obligation.
Print Assumptions two_disc_xor_discharges_curved_obligation.
Print Assumptions curved_op_modulo_qex.
Print Assumptions curved_cup_modulo_qex.
Print Assumptions curved_sub_modulo_qex.
Print Assumptions curved_xor_modulo_qex.
Print Assumptions disc_cap_or_xor_iff_cup.
