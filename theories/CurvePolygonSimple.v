(* ============================================================================
   NetTopologySuite.Proofs.CurvePolygonSimple
   ----------------------------------------------------------------------------
   Issue #64 / JTS #1195 §7 V-CP: the RING-SIMPLICITY component of CurvePolygon
   validity -- the first slice of V-CP, lifting the node-based ring simplicity
   of CurveRingSimple.v (the RING_SIMPLE oracle) over a polygon's shell and hole
   rings.

   `CurveGeometry.valid_curve_polygon` is structural ONLY (each ring's arcs valid
   + adjacent + closed).  This adds the SIMPLICITY layer:

     §1  `simple_curve_ring r` := structurally valid AND `curve_ring_simple`
         (no two non-adjacent segments meet -- the RING_SIMPLE pin).
         `simple_curve_polygon cp` := the outer ring and every hole ring are
         `simple_curve_ring`.

     §2  Projections (`*_outer_simple` / `*_holes_simple`): a simple polygon's
         every ring is `curve_ring_simple` -- the bridge that lets the oracle
         certify a CurvePolygon by running RING_SIMPLE on each ring.

     §3  SOUNDNESS (`curve_polygon_{outer,hole}_not_simple_of_witness`): a
         non-adjacent crossing witness in the OUTER ring or in ANY hole refutes
         `simple_curve_polygon` -- composing `curve_ring_not_simple_of_witness`,
         this certifies a per-ring NOT_SIMPLE verdict at the polygon level.

   All THREE-AXIOM (the classical-reals trio), no atan2/sin/Classic, no
   `Admitted`/`Axiom`.

   DEFERRED (the remaining V-CP obligations, to land with the full CP_VALID
   composition -- documented here, NOT stubbed as decreed definitions):
     - SECTOR ORIENTATION of each ring (curved ring winding / signed area;
       cf. theories/RingOrientation.v for the linear analogue).
     - HOLES INSIDE SHELL: each hole ring strictly within the outer ring
       (needs point-in-curve-polygon, the Phase-3 `Overlay.hole_inside_outer` /
       `point_in_ring` + the densification bridge).
     - HOLES MUTUALLY DISJOINT.
   Also (inherited from CurveRingSimple): the completeness direction
   (SIMPLE => no crossing = the oracle's all-pairs computation) and unconditional
   span membership for reflex arcs (sweep >= pi, atan2).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (claude-opus-4-8)
   ========================================================================== *)

From Stdlib Require Import List.
From NTS.Proofs Require Import Distance CurveGeometry CurveRingSimple.
Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  Simple rings and simple curve polygons.                                 *)
(* -------------------------------------------------------------------------- *)

Definition simple_curve_ring (r : CurveRing) : Prop :=
  valid_curve_ring r /\ curve_ring_simple r.

Definition simple_curve_polygon (cp : CurvePolygon) : Prop :=
  simple_curve_ring (curve_outer cp)
  /\ Forall simple_curve_ring (curve_holes cp).

(* -------------------------------------------------------------------------- *)
(* §2  Projections: every ring of a simple polygon is curve_ring_simple.       *)
(*     (The per-ring RING_SIMPLE checks compose to the polygon verdict.)       *)
(* -------------------------------------------------------------------------- *)

Lemma simple_curve_polygon_outer_simple :
  forall cp : CurvePolygon,
    simple_curve_polygon cp -> curve_ring_simple (curve_outer cp).
Proof. intros cp [[_ Houter] _]. exact Houter. Qed.

Lemma simple_curve_polygon_hole_simple :
  forall (cp : CurvePolygon) (h : CurveRing),
    simple_curve_polygon cp -> In h (curve_holes cp) -> curve_ring_simple h.
Proof.
  intros cp h [_ Hholes] Hin.
  rewrite Forall_forall in Hholes.
  destruct (Hholes h Hin) as [_ Hsimple]. exact Hsimple.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Soundness: a non-adjacent crossing in any ring refutes simplicity.      *)
(* -------------------------------------------------------------------------- *)

Theorem curve_polygon_outer_not_simple_of_witness :
  forall (cp : CurvePolygon) (i j : nat) (s1 s2 : CurveSegment) (X : Point),
    nth_error (curve_outer cp) i = Some s1 ->
    nth_error (curve_outer cp) j = Some s2 ->
    i <> j ->
    ~ ring_adjacent_positions (length (curve_outer cp)) i j ->
    on_curve_segment s1 X ->
    on_curve_segment s2 X ->
    ~ simple_curve_polygon cp.
Proof.
  intros cp i j s1 s2 X H1 H2 Hij Hnadj Hon1 Hon2 Hsimple.
  apply (curve_ring_not_simple_of_witness (curve_outer cp) i j s1 s2 X
           H1 H2 Hij Hnadj Hon1 Hon2).
  exact (simple_curve_polygon_outer_simple cp Hsimple).
Qed.

Theorem curve_polygon_hole_not_simple_of_witness :
  forall (cp : CurvePolygon) (h : CurveRing)
         (i j : nat) (s1 s2 : CurveSegment) (X : Point),
    In h (curve_holes cp) ->
    nth_error h i = Some s1 ->
    nth_error h j = Some s2 ->
    i <> j ->
    ~ ring_adjacent_positions (length h) i j ->
    on_curve_segment s1 X ->
    on_curve_segment s2 X ->
    ~ simple_curve_polygon cp.
Proof.
  intros cp h i j s1 s2 X Hin H1 H2 Hij Hnadj Hon1 Hon2 Hsimple.
  apply (curve_ring_not_simple_of_witness h i j s1 s2 X
           H1 H2 Hij Hnadj Hon1 Hon2).
  exact (simple_curve_polygon_hole_simple cp h Hsimple Hin).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions simple_curve_polygon_hole_simple.
Print Assumptions curve_polygon_outer_not_simple_of_witness.
Print Assumptions curve_polygon_hole_not_simple_of_witness.
