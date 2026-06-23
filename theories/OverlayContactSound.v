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
  ArcOrient ArcIntersect ArcIntersectIVT ArcChordSound ArcArcSound Intersect.

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

(* -------------------------------------------------------------------------- *)
(* §4  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions chord_chord_contact_crossing_sound.
Print Assumptions chord_chord_contact_rejection_sound.
Print Assumptions arc_chord_contact_sound.
Print Assumptions arc_arc_contact_shared_endpoint.
Print Assumptions arc_arc_contact_circle_cross_cond.
