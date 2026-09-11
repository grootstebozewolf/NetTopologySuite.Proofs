(* ============================================================================
   NetTopologySuite.Proofs.ArcArcQuartic
   ----------------------------------------------------------------------------
   Issue #64 round-2 item ④ — N-AA quartic coordinate identity (Vieta).

   The two radical-line intersection candidate coordinates satisfy:
     px rp+ + px rp- = 2·(px O1 + a·ux)     (x Vieta sum)
     py rp+ + py rp- = 2·(py O1 + a·uy)     (y Vieta sum)
     px rp+ · px rp- = (px O1+a·ux)² − (h·uy)²   (x Vieta product)
     py rp+ · py rp- = (py O1+a·uy)² − (h·ux)²   (y Vieta product)
   These are the Vieta formulas for the degree-2 polynomial whose roots
   are the radical-line intersection x- (resp. y-) coordinates — the
   polynomial certificate that makes the "quartic" circle-circle system
   reducible to a quadratic after the radical-axis substitution.  Pure
   `ring` proofs; no geometric hypotheses.  3-axiom.

   Item ② (atan2 sector-membership discharge) and the headline
   `arc_arc_intersects_of_atan2_radical_span` live in ArcSpanAtan2.v
   (Category C via atan2).  This file does not Require that lane.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import Distance CurveGeometry ArcArcCircles.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Vieta coordinate identities (the quartic certificate).                     *)
(* -------------------------------------------------------------------------- *)

(* Sum of x-coordinates of the two radical-line intersection candidates.
   Proof: pure ring identity after unfolding the point constructors. *)
Lemma radical_point_x_sum :
  forall (O1 O2 : Point) (r1 r2 : R),
    px (radical_point_plus  O1 O2 r1 r2) +
    px (radical_point_minus O1 O2 r1 r2) =
    2 * (px O1 + radical_axis_a O1 O2 r1 r2 * radical_axis_ux O1 O2).
Proof.
  intros O1 O2 r1 r2.
  unfold radical_point_plus, radical_point_minus. cbn [px]. ring.
Qed.

(* Sum of y-coordinates. *)
Lemma radical_point_y_sum :
  forall (O1 O2 : Point) (r1 r2 : R),
    py (radical_point_plus  O1 O2 r1 r2) +
    py (radical_point_minus O1 O2 r1 r2) =
    2 * (py O1 + radical_axis_a O1 O2 r1 r2 * radical_axis_uy O1 O2).
Proof.
  intros O1 O2 r1 r2.
  unfold radical_point_plus, radical_point_minus. cbn [py]. ring.
Qed.

(* Product of x-coordinates: difference-of-squares identity. *)
Lemma radical_point_x_prod :
  forall (O1 O2 : Point) (r1 r2 : R),
    px (radical_point_plus  O1 O2 r1 r2) *
    px (radical_point_minus O1 O2 r1 r2) =
    (px O1 + radical_axis_a O1 O2 r1 r2 * radical_axis_ux O1 O2) *
    (px O1 + radical_axis_a O1 O2 r1 r2 * radical_axis_ux O1 O2) -
    (radical_axis_h O1 O2 r1 r2 * radical_axis_uy O1 O2) *
    (radical_axis_h O1 O2 r1 r2 * radical_axis_uy O1 O2).
Proof.
  intros O1 O2 r1 r2.
  unfold radical_point_plus, radical_point_minus. cbn [px]. ring.
Qed.

(* Product of y-coordinates: difference-of-squares identity. *)
Lemma radical_point_y_prod :
  forall (O1 O2 : Point) (r1 r2 : R),
    py (radical_point_plus  O1 O2 r1 r2) *
    py (radical_point_minus O1 O2 r1 r2) =
    (py O1 + radical_axis_a O1 O2 r1 r2 * radical_axis_uy O1 O2) *
    (py O1 + radical_axis_a O1 O2 r1 r2 * radical_axis_uy O1 O2) -
    (radical_axis_h O1 O2 r1 r2 * radical_axis_ux O1 O2) *
    (radical_axis_h O1 O2 r1 r2 * radical_axis_ux O1 O2).
Proof.
  intros O1 O2 r1 r2.
  unfold radical_point_plus, radical_point_minus. cbn [py]. ring.
Qed.

Print Assumptions radical_point_x_sum.
Print Assumptions radical_point_y_sum.
Print Assumptions radical_point_x_prod.
Print Assumptions radical_point_y_prod.
