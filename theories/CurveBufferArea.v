(* ============================================================================
   NetTopologySuite.Proofs.CurveBufferArea
   ----------------------------------------------------------------------------
   Issue #65 / JTS #1195 §7 (BUF-1 / BUF-NEG): the buffer-region AREA companion
   of the `BUFFER_REGION` oracle mode, which ASSEMBLES the offset boundary of a
   closed curve ring at signed distance d and emits it + its TRUE signed area.

   The single-arc radial offset (`ArcOffsetThreePoint`) and the offset-boundary
   ASSEMBLY (`CurveRingOffset` .. `CurveOffsetAssemblyTotal`, round joins) are
   already proven valid-as-a-curve-ring (3-axiom).  What was NOT independently
   certifiable is the AREA / Minkowski semantics.  This file adds the AREA
   ALGEBRA the certificate rests on:

     - `buffer_arc_area r d theta := segment_area (r+d) theta` -- a buffered arc's
       circular-segment area (the arc offset to radius r+d), the per-arc summand
       the oracle's signed-area kernel accumulates.
     - `buffer_arc_area_zero` : d = 0 is the identity (no buffer => source area).
     - `buffer_arc_area_grows` : an OUTWARD buffer (0 <= d) only GROWS each arc's
       circular-segment area -- the per-arc monotonicity underlying BUF-1.
     - `buffer_arc_safe_iff_sq` (reuse) : the per-arc collapse / safety bound
       `-r < d` is the rational decision `0<=d \/ d*d<r*r` (no sqrt) -- ties the
       oracle's EMPTY verdict.
     - `buffer_boundary_arcs_valid` (reuse) : the assembled offset ring's arcs
       stay valid, so the emitted boundary is a genuine curve ring whose area is
       well-defined.

   Honesty posture (same as RING_ORIENTATION / POINT_IN_CURVE_RING): this
   certifies the boundary VALIDITY + the AREA ALGEBRA; the geometric "the emitted
   signed area equals the true Minkowski buffer(curve, d) area" is the deferred
   P2 / Jordan frontier (the offset boundary's point-set area = source (+) disk d),
   pinned by oracle/gen_buffer_region_tests.py (independent dense Minkowski
   sampling + the convex Steiner closed form + the proven parallel-distance
   property ArcOffset.arc_offset_dist_exact).

   Footprint: 4-axiom `[exact]` -- the area MAGNITUDE pulls
   `ArcArea.segment_area_nonneg` (the `sin_lt_x` / `Classical_Prop.classic`
   lineage), the documented exemption shared by `ArcArea` / `ArcLength`.
   (`RING_ORIENTATION`/`CurvePolygonOrientation` stayed 3-axiom only because they
   used the sign / sin-oddness, not the magnitude.)

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance ArcLength ArcArea CurveGeometry
  CurveRingOffset CurveJoinClassify ArcOffset.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Per-arc buffer segment area.                                           *)
(* -------------------------------------------------------------------------- *)

(* A buffered arc is the source arc offset to radius r+d (ArcOffsetThreePoint);
   its circular-segment area is segment_area (r+d) theta over the same sweep. *)
Definition buffer_arc_area (r d theta : R) : R := segment_area (r + d) theta.

(* d = 0: no buffer, the source segment area. *)
Lemma buffer_arc_area_zero :
  forall r theta, buffer_arc_area r 0 theta = segment_area r theta.
Proof.
  intros r theta. unfold buffer_arc_area. replace (r + 0) with r by ring.
  reflexivity.
Qed.

(* An outward buffer (0 <= d) only GROWS each arc's circular-segment area:
   (r+d)^2 >= r^2 and the sweep factor (theta - sin theta) >= 0. *)
Theorem buffer_arc_area_grows :
  forall r d theta,
    0 <= r -> 0 <= d -> 0 <= theta ->
    segment_area r theta <= buffer_arc_area r d theta.
Proof.
  intros r d theta Hr Hd Ht. unfold buffer_arc_area, segment_area.
  pose proof (sin_le_x theta Ht) as Hs.
  assert (Hg : 0 <= theta - sin theta) by lra.
  assert (Hsq : 0 <= (r + d) * (r + d) - r * r) by nra.
  nra.
Qed.

(* Both buffered segment areas are nonnegative for a forward sweep. *)
Lemma buffer_arc_area_nonneg :
  forall r d theta, 0 <= theta -> 0 <= buffer_arc_area r d theta.
Proof.
  intros r d theta Ht. unfold buffer_arc_area. apply segment_area_nonneg; exact Ht.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Safety / EMPTY decision (reuse) and boundary validity (reuse).         *)
(* -------------------------------------------------------------------------- *)

(* The per-arc collapse / safety bound -r < d (the oracle's EMPTY when r+sigma*d
   <= 0) is decidable in exact rational arithmetic without a square root. *)
Corollary buffer_arc_safe_iff_sq :
  forall r d : R, 0 < r -> (- r < d <-> 0 <= d \/ d * d < r * r).
Proof. exact offset_safe_iff_sq. Qed.

(* The assembled offset ring's arcs stay valid under the per-arc safety bound:
   the emitted boundary is a genuine curve ring, so its signed area is
   well-defined.  (The full round-join assembly's validity is
   CurveOffsetAssemblyTotal.curve_ring_offset_total_valid.) *)
Corollary buffer_boundary_arcs_valid :
  forall (r : CurveRing) (d : R),
    curve_ring_arcs_valid r -> ring_offset_safe r d ->
    curve_ring_arcs_valid (curve_ring_offset r d).
Proof. exact curve_ring_offset_arcs_valid. Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Parallel-curve distance (reuse): every offset boundary point is at      *)
(* distance |d| from the source -- the property the oracle test (I1) pins.     *)
(* -------------------------------------------------------------------------- *)

Corollary buffer_offset_point_dist :
  forall C r d theta,
    0 <= r -> - r <= d ->
    (forall X, dist C X = r ->
       Rabs d <= dist (arc_offset_point C r d theta) X)
    /\ dist (arc_offset_point C r d theta) (circle_point C r theta) = Rabs d.
Proof.
  intros C r d theta Hr Hd.
  destruct (arc_offset_dist_exact C r d theta Hr Hd) as [Hlow [_ Hattain]].
  split; [ exact Hlow | exact Hattain ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions buffer_arc_area_zero.
Print Assumptions buffer_arc_area_grows.
Print Assumptions buffer_arc_safe_iff_sq.
Print Assumptions buffer_boundary_arcs_valid.
Print Assumptions buffer_offset_point_dist.
