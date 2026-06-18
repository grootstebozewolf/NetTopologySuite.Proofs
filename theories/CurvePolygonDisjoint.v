(* ============================================================================
   NetTopologySuite.Proofs.CurvePolygonDisjoint
   ----------------------------------------------------------------------------
   Issue #64 / JTS #1195 §7 V-CP (CP_VALID): the HOLES-MUTUALLY-DISJOINT
   component of CurvePolygon validity -- the FINAL CP_VALID slice (after
   ring-simplicity, holes-inside-shell, and sector orientation).  The proof
   companion of the oracle HOLES_DISJOINT mode.

   Two hole rings are disjoint when their closed regions do not overlap.  For
   simple, valid holes this fails in exactly two ways: their BOUNDARIES meet, or
   one hole is NESTED inside the other.  So:

     curve_rings_disjoint A B := ~ boundaries meet  /\  ~ A nested in B
                                                    /\  ~ B nested in A.

   This file reuses the merged pieces -- `CurveRingSimple.curve_segments_meet`
   (two segments share a point) and `CurvePolygonValid.point_in_inscribed_ring`
   (the inscribed containment) -- and proves the SOUNDNESS the oracle relies on:
   a detected boundary meeting OR a nesting witness between two distinct holes
   refutes `curve_polygon_holes_disjoint`.  All THREE-AXIOM.

   The HOLES_DISJOINT oracle computes the TRUE version (true arc-aware boundary
   intersection + true point-in-curve-region containment); this file certifies
   the structural composition + the inscribed-containment floor.  The true-region
   (Jordan) containment soundness is the deferred frontier already noted for
   POINT_IN_CURVE_RING, pinned by the oracle test.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (claude-opus-4-8)
   ========================================================================== *)

From Stdlib Require Import List.
From NTS.Proofs Require Import Distance CurveGeometry CurveRingSimple
  CurvePolygonValid.
Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  Two rings meet / one nested in the other / disjoint.                    *)
(* -------------------------------------------------------------------------- *)

(* Some segment of A shares a point with some segment of B. *)
Definition curve_rings_meet (A B : CurveRing) : Prop :=
  exists (sA sB : CurveSegment),
    In sA A /\ In sB B /\ curve_segments_meet sA sB.

(* A vertex of A's densified ring lies inside B's (inscribed) region. *)
Definition curve_ring_nested_in (A B : CurveRing) (n : nat) : Prop :=
  exists p : Point,
    In p (chord_approx_ring A n) /\ point_in_inscribed_ring p B n.

Definition curve_rings_disjoint (A B : CurveRing) (n : nat) : Prop :=
  ~ curve_rings_meet A B
  /\ ~ curve_ring_nested_in A B n
  /\ ~ curve_ring_nested_in B A n.

Definition curve_polygon_holes_disjoint (cp : CurvePolygon) (n : nat) : Prop :=
  forall (i j : nat) (A B : CurveRing),
    nth_error (curve_holes cp) i = Some A ->
    nth_error (curve_holes cp) j = Some B ->
    i <> j ->
    curve_rings_disjoint A B n.

(* -------------------------------------------------------------------------- *)
(* §2  Soundness -- what a NOT_DISJOINT verdict witnesses.                     *)
(* -------------------------------------------------------------------------- *)

(* A boundary meeting between two distinct holes refutes disjointness. *)
Theorem holes_not_disjoint_of_meet :
  forall (cp : CurvePolygon) (n : nat) (i j : nat) (A B : CurveRing)
         (sA sB : CurveSegment) (X : Point),
    nth_error (curve_holes cp) i = Some A ->
    nth_error (curve_holes cp) j = Some B ->
    i <> j ->
    In sA A -> In sB B ->
    on_curve_segment sA X -> on_curve_segment sB X ->
    ~ curve_polygon_holes_disjoint cp n.
Proof.
  intros cp n i j A B sA sB X HA HB Hij HsA HsB Hon1 Hon2 Hdisj.
  destruct (Hdisj i j A B HA HB Hij) as [Hnm _].
  apply Hnm. exists sA, sB. split; [ exact HsA | split; [ exact HsB | ] ].
  exists X. split; [ exact Hon1 | exact Hon2 ].
Qed.

(* A nesting witness (a vertex of one hole inside the other) refutes it. *)
Theorem holes_not_disjoint_of_nested :
  forall (cp : CurvePolygon) (n : nat) (i j : nat) (A B : CurveRing) (p : Point),
    nth_error (curve_holes cp) i = Some A ->
    nth_error (curve_holes cp) j = Some B ->
    i <> j ->
    In p (chord_approx_ring A n) -> point_in_inscribed_ring p B n ->
    ~ curve_polygon_holes_disjoint cp n.
Proof.
  intros cp n i j A B p HA HB Hij Hp Hpin Hdisj.
  destruct (Hdisj i j A B HA HB Hij) as [_ [Hnest _]].
  apply Hnest. exists p. split; [ exact Hp | exact Hpin ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions holes_not_disjoint_of_meet.
Print Assumptions holes_not_disjoint_of_nested.
