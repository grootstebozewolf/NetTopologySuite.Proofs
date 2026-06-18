(* ============================================================================
   NetTopologySuite.Proofs.CurvePolygonOrientation
   ----------------------------------------------------------------------------
   Issue #64 / JTS #1195 §7 V-CP (CP_VALID): the SECTOR-ORIENTATION component of
   CurvePolygon validity -- outer ring CCW, hole rings CW.  The proof companion
   of the oracle RING_ORIENTATION mode.

   The TRUE twice-signed area of a curve ring is, by Green's theorem, the chord
   shoelace over the segment connection points (`RingOrientation.cross_pt`) PLUS
   each arc's signed circular-segment area `2 · segment_area` where
   `ArcArea.segment_area r θ = (r²/2)(θ − sin θ)` (the JTS curve-polygon
   area-per-arc), signed by the arc's sweep direction.  The oracle assembles this
   (interface-boundary float: the major-aware swept angle via acos, off the exact
   circumcentre); its sign is the orientation.

   This file certifies the clean ALGEBRA the orientation rests on (all
   THREE-AXIOM):

     §1  `segment_area_neg`: reversing an arc's sweep negates its signed
         segment-area contribution (`segment_area r (−θ) = − segment_area r θ`,
         via `sin` oddness) -- why traversal reversal flips a ring's orientation.
     §2  The signed-area orientation classifier on `R`: `area_ccw`/`area_cw`
         (sign), exclusivity, trichotomy, and `area_ccw_neg`
         (`area_ccw (−s) ↔ area_cw s`) -- the reversal law.
     §3  `curve_polygon_orientation_ok`: the V-CP convention (outer ring CCW,
         every hole CW) as a predicate over the rings' signed-area values.

   DEFERRED (the oracle/test layer): the assembled true signed area, the
   major-arc swept angle, and the topological "sign = inside orientation"
   (Jordan) -- pinned by oracle/gen_ring_orientation_tests.py (independent
   recompute + known-orientation rings).  `Overlay.valid_polygon` is itself
   orientation-lenient (as is JTS isValid); this is the canonical-form /
   `normalize` shell/hole convention.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (claude-opus-4-8)
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance RingOrientation ArcArea.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  An arc's signed segment-area contribution reverses with its sweep.      *)
(* -------------------------------------------------------------------------- *)

Lemma segment_area_neg :
  forall r theta, segment_area r (- theta) = - segment_area r theta.
Proof.
  intros r theta. unfold segment_area. rewrite sin_neg. field.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Signed-area orientation classifier and its laws.                        *)
(* -------------------------------------------------------------------------- *)

Definition area_ccw (s : R) : Prop := s > 0.
Definition area_cw  (s : R) : Prop := s < 0.

Lemma area_ccw_not_cw : forall s, area_ccw s -> ~ area_cw s.
Proof. unfold area_ccw, area_cw. intros s H Hc. lra. Qed.

Lemma area_orientation_trichotomy :
  forall s, area_ccw s \/ area_cw s \/ s = 0.
Proof.
  intro s. unfold area_ccw, area_cw.
  destruct (Rtotal_order s 0) as [H | [H | H]]; auto.
Qed.

(* Reversing the traversal negates the signed area, flipping orientation. *)
Lemma area_ccw_neg : forall s, area_ccw (- s) <-> area_cw s.
Proof. intro s. unfold area_ccw, area_cw. lra. Qed.

Lemma area_cw_neg : forall s, area_cw (- s) <-> area_ccw s.
Proof. intro s. unfold area_ccw, area_cw. lra. Qed.

(* -------------------------------------------------------------------------- *)
(* §3  CurvePolygon orientation convention: outer CCW, holes CW.               *)
(*     Stated over the rings' (oracle-computed) signed-area values.            *)
(* -------------------------------------------------------------------------- *)

Definition curve_polygon_orientation_ok
    (outer_area : R) (hole_areas : list R) : Prop :=
  area_ccw outer_area /\ Forall area_cw hole_areas.

Lemma curve_polygon_orientation_ok_outer :
  forall outer_area hole_areas,
    curve_polygon_orientation_ok outer_area hole_areas -> area_ccw outer_area.
Proof. intros oa ha [H _]. exact H. Qed.

Lemma curve_polygon_orientation_ok_hole :
  forall outer_area hole_areas a,
    curve_polygon_orientation_ok outer_area hole_areas ->
    In a hole_areas -> area_cw a.
Proof.
  intros oa ha a [_ Hf] Hin. rewrite Forall_forall in Hf. exact (Hf a Hin).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions segment_area_neg.
Print Assumptions area_orientation_trichotomy.
Print Assumptions curve_polygon_orientation_ok_hole.
