(* ============================================================================
   NetTopologySuite.Proofs.RingContactSound
   ----------------------------------------------------------------------------
   Ring/Relate contact-soundness lift (Precision + Overlay trusted-kernel pass,
   Slice 7 follow-up).

   The oracle reuses the SAME three contact kernels certified by
   OverlayContactSound.v (chord_chord_contact / arc_seg_contact /
   arc_arc_contact) in two more composite modes:

     run_ring_simple   (RING_SIMPLE)    -- all-pairs non-adjacent segment test
     run_holes_disjoint (HOLES_DISJOINT) -- boundary meeting between two holes

   CurveRingSimple.v and CurvePolygonDisjoint.v already prove the WITNESS-shaped
   soundness of those modes -- but those theorems take the shared point X and its
   `on_curve_segment` membership facts as HYPOTHESES.  This file supplies the
   missing link: that a contact kernel firing PRODUCES such a witness.

   The link is pure existential repackaging, because the predicates line up
   definitionally (ArcIntersect.v vs. CurveRingSimple.v):

     on_curve_segment (CSChord p q) X  =  between p q X
     on_curve_segment (CSArc a)     X  =  inCircle_R .. X = 0 /\ arc_span_contains a X
     arc_chord_intersects a P Q         =  exists X, between P Q X /\ ...on_arc..
     arc_arc_intersects   a1 a2         =  exists X, ...on_arc a1.. /\ ...on_arc a2..

   So `arc_chord_intersects a P Q` IS `curve_segments_meet (CSArc a) (CSChord P Q)`
   up to reordering an existential conjunction -- no new geometric reasoning.

   Proved here (all reuse existing Qed theorems; the only float fact that ever
   enters is the SAME named atan2 span premise already carried by
   OverlayContactSound.arc_arc_contact_circle_cross_cond -- it stays a hypothesis,
   exactly as in ArcArcSound / ArcChordSound):

     §1  contact verdict  =>  curve_segments_meet  (six bridges, incl. the
         chord endpoint / T-junction case and the arc direct-witness forms)
     §2  RING_SIMPLE: a non-adjacent contact verdict  =>  ~ curve_ring_simple
         (crossing, collinear, chord-endpoint, arc-chord circle-cross + direct
          witness, arc-arc circle-cross + direct witness + shared endpoint)
     §3  HOLES_DISJOINT: a contact verdict between two distinct holes
         =>  ~ curve_polygon_holes_disjoint  (same kernel split as §2)

   NOT covered (honest scope): the CURVE_RELATE_MATRIX boundary-meet cells
   (RelateCurveMatrix.v) are stated over the LINEARISED `to_geometry` strata
   (point_set / geom_boundary), not `curve_segments_meet`; bridging a
   curve-segment witness to a `geom_boundary` witness needs an extra linearisation
   lemma and is left as a follow-up (alongside that file's deferred cell-dimension
   frontier).

   Three-axiom policy: only Classical_Prop.classic / functional_extensionality /
   Raxioms enter (transitively, via the imported files).  No new Admitted / Axiom
   / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List.
From NTS.Proofs Require Import Distance Segment Orientation CurveGeometry
  ArcOrient ArcIntersect Intersect OverlayContactSound CurveRingSimple
  CurvePolygonDisjoint.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Contact verdict  =>  curve_segments_meet.                               *)
(*                                                                            *)
(* Each bridge destructs the existence witness produced by the corresponding  *)
(* OverlayContactSound kernel theorem and repackages it into the              *)
(* `on_curve_segment` shape that CurveRingSimple.curve_segments_meet uses.     *)
(* All proofs are pure logic (destruct + exists); the conjunct reorderings     *)
(* close by conversion, since on_curve_segment / on_arc reduce definitionally. *)
(* -------------------------------------------------------------------------- *)

(** Proper crossing of two chords yields a shared point of the two chord
    segments. *)
Lemma chord_chord_meet_of_crossing :
  forall A B C D : Point,
    cross A B C * cross A B D < 0 ->
    cross C D A * cross C D B < 0 ->
    curve_segments_meet (CSChord A B) (CSChord C D).
Proof.
  intros A B C D H1 H2.
  destruct (chord_chord_contact_crossing_sound A B C D H1 H2) as [X [Hab Hcd]].
  exists X. split; [ exact Hab | exact Hcd ].
Qed.

(** Collinear 1-D overlap of two chords yields a shared point. *)
Lemma chord_chord_meet_of_collinear :
  forall A B C D : Point,
    segments_1d_overlap A B C D ->
    curve_segments_meet (CSChord A B) (CSChord C D).
Proof.
  intros A B C D H.
  destruct (chord_chord_contact_collinear_sound A B C D H) as [X [Hab Hcd]].
  exists X. split; [ exact Hab | exact Hcd ].
Qed.

(** Endpoint / T-junction contact of two chords yields a shared point (the
    endpoint itself).  Backs the inclusive t,u in [0,1] Cramer branch of the
    OCaml chord_chord_contact, where one segment's endpoint lies on the other
    even though the cross-product product is 0 (not strictly negative) and the
    directions are non-parallel (so neither §1a crossing nor the collinear
    overlap path fires). *)
Lemma chord_chord_meet_of_endpoint :
  forall A B C D : Point,
    between C D A \/ between C D B \/ between A B C \/ between A B D ->
    curve_segments_meet (CSChord A B) (CSChord C D).
Proof.
  intros A B C D H.
  destruct (chord_chord_contact_endpoint_sound A B C D H) as [X [Hab Hcd]].
  exists X. split; [ exact Hab | exact Hcd ].
Qed.

(** An arc-chord intersection witness is exactly a meeting of the arc segment
    and the chord segment. *)
Lemma arc_chord_meet_of_contact :
  forall (a : CircularArc) (P Q : Point),
    arc_chord_intersects a P Q ->
    curve_segments_meet (CSArc a) (CSChord P Q).
Proof.
  intros a P Q [X [Hbtw [Hcirc Hspan]]].
  exists X. split.
  - unfold on_curve_segment, on_arc. split; [ exact Hcirc | exact Hspan ].
  - exact Hbtw.
Qed.

(** An arc-arc intersection witness is exactly a meeting of the two arc
    segments. *)
Lemma arc_arc_meet_of_intersects :
  forall a1 a2 : CircularArc,
    arc_arc_intersects a1 a2 ->
    curve_segments_meet (CSArc a1) (CSArc a2).
Proof.
  intros a1 a2 [X [Hc1 [Hc2 [Hs1 Hs2]]]].
  exists X. split; unfold on_curve_segment, on_arc; split; assumption.
Qed.

(** A shared endpoint (end of a1 = start of a2) makes the two arc segments meet
    -- routed through the OverlayContactSound kernel theorem. *)
Lemma arc_arc_meet_of_shared_endpoint :
  forall a1 a2 : CircularArc,
    arc_end a1 = arc_start a2 ->
    curve_segments_meet (CSArc a1) (CSArc a2).
Proof.
  intros a1 a2 Hshare.
  apply arc_arc_meet_of_intersects.
  apply arc_arc_contact_shared_endpoint. exact Hshare.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  RING_SIMPLE end-to-end soundness.                                       *)
(*                                                                            *)
(* The oracle's NOT_SIMPLE verdict fires when one of the contact kernels       *)
(* reports a meeting between two NON-ADJACENT ring segments.  Composing each   *)
(* §1 bridge with CurveRingSimple.curve_ring_not_simple_of_witness gives the   *)
(* end-to-end fact: that verdict refutes curve_ring_simple.                    *)
(* -------------------------------------------------------------------------- *)

(** Generic step: a meeting of two non-adjacent ring segments refutes
    simplicity (the kernel-agnostic core; §1 bridges feed the last premise). *)
Lemma ring_not_simple_of_meet :
  forall (r : CurveRing) (i j : nat) (s1 s2 : CurveSegment),
    nth_error r i = Some s1 ->
    nth_error r j = Some s2 ->
    i <> j ->
    ~ ring_adjacent_positions (length r) i j ->
    curve_segments_meet s1 s2 ->
    ~ curve_ring_simple r.
Proof.
  intros r i j s1 s2 H1 H2 Hij Hnadj [X [Hon1 Hon2]].
  exact (curve_ring_not_simple_of_witness r i j s1 s2 X H1 H2 Hij Hnadj Hon1 Hon2).
Qed.

(** chord_chord_contact proper-crossing verdict on a non-adjacent pair. *)
Theorem ring_not_simple_of_chord_chord_crossing :
  forall (r : CurveRing) (i j : nat) (A B C D : Point),
    nth_error r i = Some (CSChord A B) ->
    nth_error r j = Some (CSChord C D) ->
    i <> j ->
    ~ ring_adjacent_positions (length r) i j ->
    cross A B C * cross A B D < 0 ->
    cross C D A * cross C D B < 0 ->
    ~ curve_ring_simple r.
Proof.
  intros r i j A B C D H1 H2 Hij Hnadj Hc1 Hc2.
  apply (ring_not_simple_of_meet r i j (CSChord A B) (CSChord C D) H1 H2 Hij Hnadj).
  apply chord_chord_meet_of_crossing; assumption.
Qed.

(** chord_chord_contact collinear-overlap verdict on a non-adjacent pair. *)
Theorem ring_not_simple_of_chord_chord_collinear :
  forall (r : CurveRing) (i j : nat) (A B C D : Point),
    nth_error r i = Some (CSChord A B) ->
    nth_error r j = Some (CSChord C D) ->
    i <> j ->
    ~ ring_adjacent_positions (length r) i j ->
    segments_1d_overlap A B C D ->
    ~ curve_ring_simple r.
Proof.
  intros r i j A B C D H1 H2 Hij Hnadj Hov.
  apply (ring_not_simple_of_meet r i j (CSChord A B) (CSChord C D) H1 H2 Hij Hnadj).
  apply chord_chord_meet_of_collinear; assumption.
Qed.

(** chord_chord_contact endpoint / T-junction verdict on a non-adjacent pair
    (inclusive t,u in [0,1] Cramer branch). *)
Theorem ring_not_simple_of_chord_chord_endpoint :
  forall (r : CurveRing) (i j : nat) (A B C D : Point),
    nth_error r i = Some (CSChord A B) ->
    nth_error r j = Some (CSChord C D) ->
    i <> j ->
    ~ ring_adjacent_positions (length r) i j ->
    between C D A \/ between C D B \/ between A B C \/ between A B D ->
    ~ curve_ring_simple r.
Proof.
  intros r i j A B C D H1 H2 Hij Hnadj Hend.
  apply (ring_not_simple_of_meet r i j (CSChord A B) (CSChord C D) H1 H2 Hij Hnadj).
  apply chord_chord_meet_of_endpoint; assumption.
Qed.

(** arc_seg_contact verdict (circle crossing + atan2 span premise) on a
    non-adjacent arc/chord pair. *)
Theorem ring_not_simple_of_arc_chord :
  forall (r : CurveRing) (i j : nat) (a : CircularArc) (P Q : Point),
    nth_error r i = Some (CSArc a) ->
    nth_error r j = Some (CSChord P Q) ->
    i <> j ->
    ~ ring_adjacent_positions (length r) i j ->
    chord_crosses_arc_circle a P Q ->
    (forall X : Point,
       between P Q X ->
       inCircle_R (arc_start a) (arc_mid a) (arc_end a) X = 0 ->
       arc_span_contains a X) ->
    ~ curve_ring_simple r.
Proof.
  intros r i j a P Q H1 H2 Hij Hnadj Hcross Hspan.
  apply (ring_not_simple_of_meet r i j (CSArc a) (CSChord P Q) H1 H2 Hij Hnadj).
  apply arc_chord_meet_of_contact.
  apply arc_chord_contact_sound; assumption.
Qed.

(** arc_seg_contact direct-witness verdict on a non-adjacent arc/chord pair:
    a point on the chord, on the arc circle, and in the arc span (the h = 0
    tangent foot or an endpoint-on-circle candidate that chord_crosses_arc_circle
    -- strict sP*sQ < 0 -- does NOT cover).  Routed through
    arc_chord_contact_witness_sound; the atan2 span fact stays a hypothesis. *)
Theorem ring_not_simple_of_arc_chord_witness :
  forall (r : CurveRing) (i j : nat) (a : CircularArc) (P Q X : Point),
    nth_error r i = Some (CSArc a) ->
    nth_error r j = Some (CSChord P Q) ->
    i <> j ->
    ~ ring_adjacent_positions (length r) i j ->
    between P Q X ->
    inCircle_R (arc_start a) (arc_mid a) (arc_end a) X = 0 ->
    arc_span_contains a X ->
    ~ curve_ring_simple r.
Proof.
  intros r i j a P Q X H1 H2 Hij Hnadj Hbtw Hcirc Hspan.
  apply (ring_not_simple_of_meet r i j (CSArc a) (CSChord P Q) H1 H2 Hij Hnadj).
  apply arc_chord_meet_of_contact.
  exact (arc_chord_contact_witness_sound a P Q X Hbtw Hcirc Hspan).
Qed.

(** arc_arc_contact circle-crossing verdict (+ bundled atan2 span premise) on a
    non-adjacent arc/arc pair. *)
Theorem ring_not_simple_of_arc_arc_circle_cross :
  forall (r : CurveRing) (i j : nat) (a1 a2 : CircularArc),
    nth_error r i = Some (CSArc a1) ->
    nth_error r j = Some (CSArc a2) ->
    i <> j ->
    ~ ring_adjacent_positions (length r) i j ->
    chord_crosses_arc_circle a1 (arc_start a2) (arc_end a2) ->
    (forall X : Point,
       between (arc_start a2) (arc_end a2) X ->
       inCircle_R (arc_start a1) (arc_mid a1) (arc_end a1) X = 0 ->
       inCircle_R (arc_start a2) (arc_mid a2) (arc_end a2) X = 0
       /\ arc_span_contains a1 X
       /\ arc_span_contains a2 X) ->
    ~ curve_ring_simple r.
Proof.
  intros r i j a1 a2 H1 H2 Hij Hnadj Hcross Hspan.
  apply (ring_not_simple_of_meet r i j (CSArc a1) (CSArc a2) H1 H2 Hij Hnadj).
  apply arc_arc_meet_of_intersects.
  apply arc_arc_contact_circle_cross_cond; assumption.
Qed.

(** arc_arc_contact direct-witness verdict on a non-adjacent arc/arc pair:
    a point on both circumcircles and in both spans (backs the concentric
    equal-radius branch, where a control point of one arc serves as witness).
    Routed through arc_arc_contact_witness_sound; both atan2 span facts stay
    hypotheses. *)
Theorem ring_not_simple_of_arc_arc_witness :
  forall (r : CurveRing) (i j : nat) (a1 a2 : CircularArc) (X : Point),
    nth_error r i = Some (CSArc a1) ->
    nth_error r j = Some (CSArc a2) ->
    i <> j ->
    ~ ring_adjacent_positions (length r) i j ->
    inCircle_R (arc_start a1) (arc_mid a1) (arc_end a1) X = 0 ->
    inCircle_R (arc_start a2) (arc_mid a2) (arc_end a2) X = 0 ->
    arc_span_contains a1 X ->
    arc_span_contains a2 X ->
    ~ curve_ring_simple r.
Proof.
  intros r i j a1 a2 X H1 H2 Hij Hnadj Hc1 Hc2 Hs1 Hs2.
  apply (ring_not_simple_of_meet r i j (CSArc a1) (CSArc a2) H1 H2 Hij Hnadj).
  apply arc_arc_meet_of_intersects.
  exact (arc_arc_contact_witness_sound a1 a2 X Hc1 Hc2 Hs1 Hs2).
Qed.

(** arc_arc_contact shared-endpoint verdict on a NON-ADJACENT arc/arc pair
    (when the same vertex is shared by non-consecutive arcs, simplicity fails;
    consecutive arcs are exempted by ring_adjacent_positions). *)
Theorem ring_not_simple_of_arc_arc_shared_endpoint :
  forall (r : CurveRing) (i j : nat) (a1 a2 : CircularArc),
    nth_error r i = Some (CSArc a1) ->
    nth_error r j = Some (CSArc a2) ->
    i <> j ->
    ~ ring_adjacent_positions (length r) i j ->
    arc_end a1 = arc_start a2 ->
    ~ curve_ring_simple r.
Proof.
  intros r i j a1 a2 H1 H2 Hij Hnadj Hshare.
  apply (ring_not_simple_of_meet r i j (CSArc a1) (CSArc a2) H1 H2 Hij Hnadj).
  apply arc_arc_meet_of_shared_endpoint. exact Hshare.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  HOLES_DISJOINT end-to-end soundness.                                    *)
(*                                                                            *)
(* The oracle's NOT_DISJOINT verdict (boundary-meeting branch) fires when a    *)
(* contact kernel reports a meeting between a segment of one hole and a        *)
(* segment of another, distinct hole.  Composing each §1 bridge with           *)
(* CurvePolygonDisjoint.holes_not_disjoint_of_meet gives the end-to-end fact.  *)
(* -------------------------------------------------------------------------- *)

(** Generic step: a meeting of a segment of hole A with a segment of a distinct
    hole B refutes holes-disjointness. *)
Lemma holes_not_disjoint_of_segments_meet :
  forall (cp : CurvePolygon) (n i j : nat) (A B : CurveRing) (sA sB : CurveSegment),
    nth_error (curve_holes cp) i = Some A ->
    nth_error (curve_holes cp) j = Some B ->
    i <> j ->
    In sA A -> In sB B ->
    curve_segments_meet sA sB ->
    ~ curve_polygon_holes_disjoint cp n.
Proof.
  intros cp n i j A B sA sB HA HB Hij HsA HsB [X [Hon1 Hon2]].
  exact (holes_not_disjoint_of_meet cp n i j A B sA sB X
           HA HB Hij HsA HsB Hon1 Hon2).
Qed.

(** chord_chord_contact proper-crossing verdict between two distinct holes. *)
Theorem holes_not_disjoint_of_chord_chord_crossing :
  forall (cp : CurvePolygon) (n i j : nat) (A B : CurveRing)
         (P0 P1 Q0 Q1 : Point),
    nth_error (curve_holes cp) i = Some A ->
    nth_error (curve_holes cp) j = Some B ->
    i <> j ->
    In (CSChord P0 P1) A -> In (CSChord Q0 Q1) B ->
    cross P0 P1 Q0 * cross P0 P1 Q1 < 0 ->
    cross Q0 Q1 P0 * cross Q0 Q1 P1 < 0 ->
    ~ curve_polygon_holes_disjoint cp n.
Proof.
  intros cp n i j A B P0 P1 Q0 Q1 HA HB Hij HinA HinB Hc1 Hc2.
  apply (holes_not_disjoint_of_segments_meet cp n i j A B
           (CSChord P0 P1) (CSChord Q0 Q1) HA HB Hij HinA HinB).
  apply chord_chord_meet_of_crossing; assumption.
Qed.

(** chord_chord_contact collinear-overlap verdict between two distinct holes. *)
Theorem holes_not_disjoint_of_chord_chord_collinear :
  forall (cp : CurvePolygon) (n i j : nat) (A B : CurveRing)
         (P0 P1 Q0 Q1 : Point),
    nth_error (curve_holes cp) i = Some A ->
    nth_error (curve_holes cp) j = Some B ->
    i <> j ->
    In (CSChord P0 P1) A -> In (CSChord Q0 Q1) B ->
    segments_1d_overlap P0 P1 Q0 Q1 ->
    ~ curve_polygon_holes_disjoint cp n.
Proof.
  intros cp n i j A B P0 P1 Q0 Q1 HA HB Hij HinA HinB Hov.
  apply (holes_not_disjoint_of_segments_meet cp n i j A B
           (CSChord P0 P1) (CSChord Q0 Q1) HA HB Hij HinA HinB).
  apply chord_chord_meet_of_collinear; assumption.
Qed.

(** chord_chord_contact endpoint / T-junction verdict between two distinct
    holes (inclusive t,u in [0,1] Cramer branch). *)
Theorem holes_not_disjoint_of_chord_chord_endpoint :
  forall (cp : CurvePolygon) (n i j : nat) (A B : CurveRing)
         (P0 P1 Q0 Q1 : Point),
    nth_error (curve_holes cp) i = Some A ->
    nth_error (curve_holes cp) j = Some B ->
    i <> j ->
    In (CSChord P0 P1) A -> In (CSChord Q0 Q1) B ->
    between Q0 Q1 P0 \/ between Q0 Q1 P1 \/ between P0 P1 Q0 \/ between P0 P1 Q1 ->
    ~ curve_polygon_holes_disjoint cp n.
Proof.
  intros cp n i j A B P0 P1 Q0 Q1 HA HB Hij HinA HinB Hend.
  apply (holes_not_disjoint_of_segments_meet cp n i j A B
           (CSChord P0 P1) (CSChord Q0 Q1) HA HB Hij HinA HinB).
  apply chord_chord_meet_of_endpoint; assumption.
Qed.

(** arc_seg_contact verdict (arc in hole A, chord in hole B). *)
Theorem holes_not_disjoint_of_arc_chord :
  forall (cp : CurvePolygon) (n i j : nat) (A B : CurveRing)
         (a : CircularArc) (P Q : Point),
    nth_error (curve_holes cp) i = Some A ->
    nth_error (curve_holes cp) j = Some B ->
    i <> j ->
    In (CSArc a) A -> In (CSChord P Q) B ->
    chord_crosses_arc_circle a P Q ->
    (forall X : Point,
       between P Q X ->
       inCircle_R (arc_start a) (arc_mid a) (arc_end a) X = 0 ->
       arc_span_contains a X) ->
    ~ curve_polygon_holes_disjoint cp n.
Proof.
  intros cp n i j A B a P Q HA HB Hij HinA HinB Hcross Hspan.
  apply (holes_not_disjoint_of_segments_meet cp n i j A B
           (CSArc a) (CSChord P Q) HA HB Hij HinA HinB).
  apply arc_chord_meet_of_contact.
  apply arc_chord_contact_sound; assumption.
Qed.

(** arc_seg_contact direct-witness verdict between two distinct holes (h = 0
    tangent / endpoint-on-circle candidate not covered by the strict
    chord_crosses_arc_circle filter).  Routed through
    arc_chord_contact_witness_sound. *)
Theorem holes_not_disjoint_of_arc_chord_witness :
  forall (cp : CurvePolygon) (n i j : nat) (A B : CurveRing)
         (a : CircularArc) (P Q X : Point),
    nth_error (curve_holes cp) i = Some A ->
    nth_error (curve_holes cp) j = Some B ->
    i <> j ->
    In (CSArc a) A -> In (CSChord P Q) B ->
    between P Q X ->
    inCircle_R (arc_start a) (arc_mid a) (arc_end a) X = 0 ->
    arc_span_contains a X ->
    ~ curve_polygon_holes_disjoint cp n.
Proof.
  intros cp n i j A B a P Q X HA HB Hij HinA HinB Hbtw Hcirc Hspan.
  apply (holes_not_disjoint_of_segments_meet cp n i j A B
           (CSArc a) (CSChord P Q) HA HB Hij HinA HinB).
  apply arc_chord_meet_of_contact.
  exact (arc_chord_contact_witness_sound a P Q X Hbtw Hcirc Hspan).
Qed.

(** arc_arc_contact circle-crossing verdict between two distinct holes. *)
Theorem holes_not_disjoint_of_arc_arc_circle_cross :
  forall (cp : CurvePolygon) (n i j : nat) (A B : CurveRing)
         (a1 a2 : CircularArc),
    nth_error (curve_holes cp) i = Some A ->
    nth_error (curve_holes cp) j = Some B ->
    i <> j ->
    In (CSArc a1) A -> In (CSArc a2) B ->
    chord_crosses_arc_circle a1 (arc_start a2) (arc_end a2) ->
    (forall X : Point,
       between (arc_start a2) (arc_end a2) X ->
       inCircle_R (arc_start a1) (arc_mid a1) (arc_end a1) X = 0 ->
       inCircle_R (arc_start a2) (arc_mid a2) (arc_end a2) X = 0
       /\ arc_span_contains a1 X
       /\ arc_span_contains a2 X) ->
    ~ curve_polygon_holes_disjoint cp n.
Proof.
  intros cp n i j A B a1 a2 HA HB Hij HinA HinB Hcross Hspan.
  apply (holes_not_disjoint_of_segments_meet cp n i j A B
           (CSArc a1) (CSArc a2) HA HB Hij HinA HinB).
  apply arc_arc_meet_of_intersects.
  apply arc_arc_contact_circle_cross_cond; assumption.
Qed.

(** arc_arc_contact direct-witness verdict between two distinct holes (backs the
    concentric equal-radius branch).  Routed through
    arc_arc_contact_witness_sound. *)
Theorem holes_not_disjoint_of_arc_arc_witness :
  forall (cp : CurvePolygon) (n i j : nat) (A B : CurveRing)
         (a1 a2 : CircularArc) (X : Point),
    nth_error (curve_holes cp) i = Some A ->
    nth_error (curve_holes cp) j = Some B ->
    i <> j ->
    In (CSArc a1) A -> In (CSArc a2) B ->
    inCircle_R (arc_start a1) (arc_mid a1) (arc_end a1) X = 0 ->
    inCircle_R (arc_start a2) (arc_mid a2) (arc_end a2) X = 0 ->
    arc_span_contains a1 X ->
    arc_span_contains a2 X ->
    ~ curve_polygon_holes_disjoint cp n.
Proof.
  intros cp n i j A B a1 a2 X HA HB Hij HinA HinB Hc1 Hc2 Hs1 Hs2.
  apply (holes_not_disjoint_of_segments_meet cp n i j A B
           (CSArc a1) (CSArc a2) HA HB Hij HinA HinB).
  apply arc_arc_meet_of_intersects.
  exact (arc_arc_contact_witness_sound a1 a2 X Hc1 Hc2 Hs1 Hs2).
Qed.

(** arc_arc_contact shared-endpoint verdict between two distinct holes. *)
Theorem holes_not_disjoint_of_arc_arc_shared_endpoint :
  forall (cp : CurvePolygon) (n i j : nat) (A B : CurveRing)
         (a1 a2 : CircularArc),
    nth_error (curve_holes cp) i = Some A ->
    nth_error (curve_holes cp) j = Some B ->
    i <> j ->
    In (CSArc a1) A -> In (CSArc a2) B ->
    arc_end a1 = arc_start a2 ->
    ~ curve_polygon_holes_disjoint cp n.
Proof.
  intros cp n i j A B a1 a2 HA HB Hij HinA HinB Hshare.
  apply (holes_not_disjoint_of_segments_meet cp n i j A B
           (CSArc a1) (CSArc a2) HA HB Hij HinA HinB).
  apply arc_arc_meet_of_shared_endpoint. exact Hshare.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions chord_chord_meet_of_crossing.
Print Assumptions chord_chord_meet_of_collinear.
Print Assumptions chord_chord_meet_of_endpoint.
Print Assumptions arc_chord_meet_of_contact.
Print Assumptions arc_arc_meet_of_intersects.
Print Assumptions arc_arc_meet_of_shared_endpoint.
Print Assumptions ring_not_simple_of_chord_chord_crossing.
Print Assumptions ring_not_simple_of_chord_chord_collinear.
Print Assumptions ring_not_simple_of_chord_chord_endpoint.
Print Assumptions ring_not_simple_of_arc_chord.
Print Assumptions ring_not_simple_of_arc_chord_witness.
Print Assumptions ring_not_simple_of_arc_arc_circle_cross.
Print Assumptions ring_not_simple_of_arc_arc_witness.
Print Assumptions ring_not_simple_of_arc_arc_shared_endpoint.
Print Assumptions holes_not_disjoint_of_chord_chord_crossing.
Print Assumptions holes_not_disjoint_of_chord_chord_collinear.
Print Assumptions holes_not_disjoint_of_chord_chord_endpoint.
Print Assumptions holes_not_disjoint_of_arc_chord.
Print Assumptions holes_not_disjoint_of_arc_chord_witness.
Print Assumptions holes_not_disjoint_of_arc_arc_circle_cross.
Print Assumptions holes_not_disjoint_of_arc_arc_witness.
Print Assumptions holes_not_disjoint_of_arc_arc_shared_endpoint.
