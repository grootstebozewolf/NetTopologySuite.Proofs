(* ============================================================================
   NetTopologySuite.Proofs.OverlayContactSound
   ----------------------------------------------------------------------------
   Proof companions for the three contact kernels of `run_overlay_unified`
   (oracle/driver.ml, Precision + Overlay trusted-kernel pass, Slice 7).

   The oracle computes the DE-9IM relationship between two segment-list
   geometries via three hand-rolled kernels:

     chord_chord_contact   -- Cramer's rule + collinear 1-D overlap
     arc_seg_contact        -- circumcentre_q + point_on_arc_sector (atan2)
     arc_arc_contact        -- circumcentre_q + point_on_arc_sector (atan2)

   This file names the Qed-closed Rocq theorems that back each kernel,
   following the interface-boundary convention of ArcChordSound.v and
   ArcArcSound.v: the atan2-based `point_on_arc_sector` float test stays a
   named hypothesis in §2 and §3b (it cannot be proven inside the 3-axiom
   host lane), while the circle-intersection and sign-algebra steps are
   machine-checked.

     §1  chord_chord_contact_crossing_sound
         chord_chord_contact_rejection_sound
         Proper crossing (strict opposite inCircle_R/cross signs) → shared
         point exists (Intersect.strict_completeness); same side → no shared
         point (Intersect.same_side_rejection_is_sound).

     §2  arc_chord_contact_sound
         Circle-crossing + span hypothesis → arc_chord_intersects is
         witnessed (ArcChordSound.chord_crosses_arc_circle_span_sound).

     §3a arc_arc_contact_shared_endpoint
         Shared arc endpoint (unconditional) → arc_arc_intersects
         (ArcArcSound.arc_arc_intersects_shared_vertex).

     §3b arc_arc_contact_circle_cross_cond
         a2's chord crosses a1's circumcircle + bundled span hypothesis →
         arc_arc_intersects (ArcArcSound.arc_arc_intersects_of_chord_cross_cond).

   Three-axiom policy: only Classical_Prop.classic / functional_extensionality
   / Raxioms enter via the transitive closure of the imported files.  No new
   Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import Distance Segment Orientation CurveGeometry
  ArcOrient ArcIntersect ArcIntersectIVT ArcChordSound ArcArcSound Intersect
  CircumcentreQSound.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Chord-chord contact soundness.                                         *)
(*                                                                            *)
(* The oracle kernel applies the Cramer's-rule / cross-product decision:     *)
(*   strict opposite signs on both lines  → proper crossing (§1a, sound)     *)
(*   either pair strictly same side       → no contact    (§1b, complete)    *)
(* -------------------------------------------------------------------------- *)

(** §1a  Proper crossing → a shared interior point exists. *)
Theorem chord_chord_contact_crossing_sound :
  forall A B C D : Point,
    cross A B C * cross A B D < 0 ->
    cross C D A * cross C D B < 0 ->
    exists X, between A B X /\ between C D X.
Proof. exact strict_completeness. Qed.

(** §1b  Same-side rejection is complete: when the oracle returns "no contact"
    via a strictly positive cross-product product, no shared point can exist. *)
Theorem chord_chord_contact_rejection_sound :
  forall A B C D : Point,
    (cross A B C * cross A B D > 0 \/ cross C D A * cross C D B > 0) ->
    ~ exists X, between A B X /\ between C D X.
Proof. exact same_side_rejection_is_sound. Qed.

(** §1c  Collinear 1D-overlap: when both cross-product products are zero
    (all four points collinear), a shared point exists iff at least one
    endpoint of one segment lies between the endpoints of the other.
    Backed by Intersect.segments_1d_overlap_share. *)
Theorem chord_chord_contact_collinear_sound :
  forall A B C D : Point,
    segments_1d_overlap A B C D ->
    exists X, between A B X /\ between C D X.
Proof. exact segments_1d_overlap_share. Qed.

(** §1d  Endpoint / T-junction contact: one endpoint of one segment lies on
    the other segment (cross-product product is zero, not strictly negative,
    so §1a does not apply; the collinear fallback may not trigger when the
    Cramer denominator is large).  The shared point is the endpoint itself.
    Backs the inclusive t/u ∈ [0,1] range in the OCaml chord_chord_contact
    Cramer branch. *)
Theorem chord_chord_contact_endpoint_sound :
  forall A B C D : Point,
    between C D A \/
    between C D B \/
    between A B C \/
    between A B D ->
    exists X, between A B X /\ between C D X.
Proof.
  intros A B C D [H | [H | [H | H]]].
  - exists A. split. apply between_P0. exact H.
  - exists B. split. apply between_P1. exact H.
  - exists C. split. exact H. apply between_P0.
  - exists D. split. exact H. apply between_P1.
Qed.

(** §1e  Shared-vertex contact: one endpoint of one segment equals one
    endpoint of the other (the "corner meets corner" case).  Backed by
    Intersect.shared_endpoint_share_point; no cross-product premise needed. *)
Theorem chord_chord_contact_shared_vertex :
  forall A B C D : Point,
    (A = C \/ A = D \/ B = C \/ B = D) ->
    exists X, between A B X /\ between C D X.
Proof. exact shared_endpoint_share_point. Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Arc-chord contact soundness.                                           *)
(*                                                                            *)
(* The oracle kernel checks:                                                  *)
(*   inCircle_R sign change across P,Q  (circle crossing, machine-checked)   *)
(*   point_on_arc_sector X              (atan2 span test, interface-boundary) *)
(*                                                                            *)
(* The Rocq counterpart names the span membership hypothesis explicitly;      *)
(* this is the same pattern as ArcChordSound.chord_crosses_arc_circle_span_  *)
(* sound, here restated in oracle-facing terminology.                         *)
(* -------------------------------------------------------------------------- *)

(** Arc-chord contact: circle crossing + span hypothesis → intersection. *)
Theorem arc_chord_contact_sound :
  forall (a : CircularArc) (P Q : Point),
    chord_crosses_arc_circle a P Q ->
    (forall X : Point,
       between P Q X ->
       inCircle_R (arc_start a) (arc_mid a) (arc_end a) X = 0 ->
       arc_span_contains a X) ->
    arc_chord_intersects a P Q.
Proof. exact chord_crosses_arc_circle_span_sound. Qed.

(** Arc-chord contact, direct-witness form: any point simultaneously on the
    circumcircle and in the arc span, that also lies on the chord segment,
    witnesses arc_chord_intersects.  Backs the h = 0 tangent branch of
    arc_seg_contact (where the foot of perpendicular is the unique candidate)
    and the endpoint-on-circle case.  The atan2 span test stays at the
    interface boundary; the caller supplies arc_span_contains as a hypothesis. *)
Theorem arc_chord_contact_witness_sound :
  forall (a : CircularArc) (P Q X : Point),
    between P Q X ->
    inCircle_R (arc_start a) (arc_mid a) (arc_end a) X = 0 ->
    arc_span_contains a X ->
    arc_chord_intersects a P Q.
Proof.
  intros a P Q X Hbet Hcirc Hspan.
  exists X. exact (conj Hbet (conj Hcirc Hspan)).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Arc-arc contact soundness.                                             *)
(* -------------------------------------------------------------------------- *)

(** §3a  Shared endpoint (unconditional): when the oracle detects that the
    end of one arc equals the start of the other, no span hypothesis is
    needed -- the shared point is on both circumcircles and in both spans by
    the boundary disjunct of arc_span_contains. *)
Theorem arc_arc_contact_shared_endpoint :
  forall a1 a2 : CircularArc,
    arc_end a1 = arc_start a2 ->
    arc_arc_intersects a1 a2.
Proof. exact arc_arc_intersects_shared_vertex. Qed.

(** §3a variant: start of a1 = end of a2. *)
Corollary arc_arc_contact_shared_endpoint_rev :
  forall a1 a2 : CircularArc,
    arc_start a1 = arc_end a2 ->
    arc_arc_intersects a1 a2.
Proof. exact arc_arc_intersects_shared_vertex_rev. Qed.

(** §3b  Circle-crossing (conditional floor): a2's chord crosses a1's
    circumcircle, and the bundled span/circle hypothesis holds for the IVT
    witness point.  The Rocq proof calls the IVT to produce a point on a1's
    circle, then the hypothesis promotes it to a full arc-arc intersection. *)
Theorem arc_arc_contact_circle_cross_cond :
  forall a1 a2 : CircularArc,
    chord_crosses_arc_circle a1 (arc_start a2) (arc_end a2) ->
    (forall X : Point,
       between (arc_start a2) (arc_end a2) X ->
       inCircle_R (arc_start a1) (arc_mid a1) (arc_end a1) X = 0 ->
       inCircle_R (arc_start a2) (arc_mid a2) (arc_end a2) X = 0
       /\ arc_span_contains a1 X
       /\ arc_span_contains a2 X) ->
    arc_arc_intersects a1 a2.
Proof. exact arc_arc_intersects_of_chord_cross_cond. Qed.

(** §3c  Direct-witness form: any point on both circumcircles and in both arc
    spans witnesses arc_arc_intersects.  Backs the concentric equal-radius
    branch of arc_arc_contact, where a control point of one arc serves as the
    witness (control points lie on their own circumcircle and are trivially in
    their own span via arc_span_contains_start / arc_span_contains_end; the
    atan2 span check for the other arc stays at the interface boundary). *)
Theorem arc_arc_contact_witness_sound :
  forall (a1 a2 : CircularArc) (X : Point),
    inCircle_R (arc_start a1) (arc_mid a1) (arc_end a1) X = 0 ->
    inCircle_R (arc_start a2) (arc_mid a2) (arc_end a2) X = 0 ->
    arc_span_contains a1 X ->
    arc_span_contains a2 X ->
    arc_arc_intersects a1 a2.
Proof.
  intros a1 a2 X H1 H2 Hsp1 Hsp2.
  exists X. exact (conj H1 (conj H2 (conj Hsp1 Hsp2))).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Circumcenter kernel soundness.                                         *)
(*                                                                            *)
(* The arc_seg_contact and arc_arc_contact kernels call circumcentre_q to    *)
(* get (ox, oy, r²), then test candidate intersection points by checking     *)
(* (x−ox)² + (y−oy)² = r².  The next two lemmas formally state the           *)
(* correctness of that test, backed by CircumcentreQSound.                   *)
(* -------------------------------------------------------------------------- *)

(** If (ox,oy) is the circumcenter of A,B,C with squared radius r2, then any
    point P at squared distance r2 from (ox,oy) lies on the circumcircle. *)
Theorem overlay_circumcenter_candidate_sound :
  forall ax ay bx by_ cx cy ox oy r2 px_ py_ : R,
    r2 = (ax - ox) * (ax - ox) + (ay - oy) * (ay - oy) ->
    (bx - ox) * (bx - ox) + (by_ - oy) * (by_ - oy) = r2 ->
    (cx - ox) * (cx - ox) + (cy - oy) * (cy - oy) = r2 ->
    (px_ - ox) * (px_ - ox) + (py_ - oy) * (py_ - oy) = r2 ->
    inCircle_R (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy) (mkPoint px_ py_) = 0.
Proof. exact circumcentre_formula_inCircle_R. Qed.

(** The circumcenter formula itself is equidistant from all three input points
    (equidistance is the defining property of circumcentre_q). *)
Theorem overlay_circumcenter_formula_sound :
  forall ax ay bx by_ cx cy ox oy r2 : R,
    ax * (by_ - cy) + bx * (cy - ay) + cx * (ay - by_) <> 0 ->
    ox = (  (ax*ax + ay*ay) * (by_ - cy)
          + (bx*bx + by_*by_) * (cy - ay)
          + (cx*cx + cy*cy) * (ay - by_))
         / (2 * (ax * (by_ - cy) + bx * (cy - ay) + cx * (ay - by_))) ->
    oy = (  (ax*ax + ay*ay) * (cx - bx)
          + (bx*bx + by_*by_) * (ax - cx)
          + (cx*cx + cy*cy) * (bx - ax))
         / (2 * (ax * (by_ - cy) + bx * (cy - ay) + cx * (ay - by_))) ->
    r2 = (ax - ox) * (ax - ox) + (ay - oy) * (ay - oy) ->
    (bx - ox) * (bx - ox) + (by_ - oy) * (by_ - oy) = r2 /\
    (cx - ox) * (cx - ox) + (cy - oy) * (cy - oy) = r2.
Proof. exact circumcentre_formula_equidistant. Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions chord_chord_contact_crossing_sound.
Print Assumptions chord_chord_contact_rejection_sound.
Print Assumptions chord_chord_contact_collinear_sound.
Print Assumptions chord_chord_contact_endpoint_sound.
Print Assumptions chord_chord_contact_shared_vertex.
Print Assumptions arc_chord_contact_sound.
Print Assumptions arc_chord_contact_witness_sound.
Print Assumptions arc_arc_contact_shared_endpoint.
Print Assumptions arc_arc_contact_circle_cross_cond.
Print Assumptions arc_arc_contact_witness_sound.
Print Assumptions overlay_circumcenter_candidate_sound.
Print Assumptions overlay_circumcenter_formula_sound.
