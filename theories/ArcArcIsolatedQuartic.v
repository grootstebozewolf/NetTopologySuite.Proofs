(* ============================================================================
   NetTopologySuite.Proofs.ArcArcIsolatedQuartic
   ----------------------------------------------------------------------------
   Issue #64 ask #5b / JTS curve-awareness N-AA: ISOLATED QUARTIC IDENTITY
   for arc-arc intersection coordinates.

   Year-1 already names the radical-line candidates
   (`ArcArcCircles.radical_point_plus` / `_minus`) and proves they lie on
   both circumcircles (`radical_points_on_circles`).  `ArcArcQuartic.v`
   then records Vieta sum/product identities, but that file is 4-axiom
   (atan2 / Classic lineage).  TRIAGE still names "#5b coords" as the
   exactness frontier because the *named polynomial* whose roots those
   coordinates are had not been isolated at the 3-axiom floor.

   This file closes that gap, Classic-free:

     circle_poly O r x y  :=  (x − Ox)² + (y − Oy)² − r²

     isolated_quartic_x   :=  Sylvester Res_y of the two circle
                              polynomials (the isolated affine
                              polynomial of the pencil).

   Bézout counts four intersections of two conics in the projective
   plane.  For two circles the two circular points at infinity account
   for degree 2; the affine resultant is therefore degree ≤ 2.  The
   traditional name "quartic" is the Bézout count; the named polynomial
   here is the elimination resultant, derived from the two circle
   equations, not from the radical-line closed form.

   HEADLINE (one named Year-1 guard):
     `radical_points_satisfy_isolated_quartic`
     — both named radical-line x- and y-coordinates are roots of the
       corresponding isolated resultant.

   Supporting (hypothesis-free):
     `isolated_quartic_vanishes_on_common_zeros`
     — any common zero of the two circle polynomials has x-coordinate
       a root of `isolated_quartic_x`.

   Degenerate-pencil / missing-real-root boundary (not the headline;
   documented so the QEX constructor is not silently omitted):
     coincident centres (`dist = 0`) or a non-positive radius refuse
     `circles_properly_intersect`.  That is the Year-1 guard already
     used by `two_circles_radical_point`; no new primitive is missing.

   WITNESS topic: core · claimId: 64-naa-quartic · witness: locked-7-2
   lane: proofs
   issue: #64
   Eval (RED until the named resultant is shown to vanish):
     isolated_quartic_x (0,0) (7,0) 5 5 (7/2) = 0
     — the DiscOverlay / ARC_ARC_XY locked fixture, x-coordinate of
       both radical-line nodes.  Example
       `locked_fixture_isolated_quartic_x` is that Eval, Qed by field.

   No new oracle vectors: ARC_ARC_XY already exercises this fixture
   numerically (`oracle/arc_arc_tests.txt`, `oracle/gen_arc_arc_tests.py`).

   Proved here (THREE-AXIOM, no atan2, no Classic, no exemption).
   No `Admitted`, no `Axiom`, no `Parameter`.  Does not Require
   ArcArcQuartic / ArcSpanAtan2 / Atan2.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance ArcArcCircles.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Named polynomials.                                                     *)
(* -------------------------------------------------------------------------- *)

Definition circle_poly (O : Point) (r : R) (x y : R) : R :=
  (x - px O) * (x - px O) + (y - py O) * (y - py O) - r * r.

(* Circle as a monic quadratic in y: y² + By·y + Cy(x) = 0. *)
Definition circle_y_lin (O : Point) : R := - (2 * py O).

Definition circle_y_const (O : Point) (r x : R) : R :=
  (x - px O) * (x - px O) + py O * py O - r * r.

(* Circle as a monic quadratic in x: x² + Bx·x + Cx(y) = 0. *)
Definition circle_x_lin (O : Point) : R := - (2 * px O).

Definition circle_x_const (O : Point) (r y : R) : R :=
  (y - py O) * (y - py O) + px O * px O - r * r.

Lemma circle_poly_as_quad_y :
  forall O r x y,
    circle_poly O r x y =
    y * y + circle_y_lin O * y + circle_y_const O r x.
Proof.
  intros O r x y.
  unfold circle_poly, circle_y_lin, circle_y_const. ring.
Qed.

Lemma circle_poly_as_quad_x :
  forall O r x y,
    circle_poly O r x y =
    x * x + circle_x_lin O * x + circle_x_const O r y.
Proof.
  intros O r x y.
  unfold circle_poly, circle_x_lin, circle_x_const. ring.
Qed.

(* Sylvester resultant of two monic quadratics t² + b1 t + c1 and
   t² + b2 t + c2.  Expanded 4×4 determinant; vanishes whenever the
   quadratics share a root. *)
Definition sylvester_res_monic_quad (b1 c1 b2 c2 : R) : R :=
  let db := b1 - b2 in
  let dc := c1 - c2 in
  dc * dc - db * (c1 * b2 - c2 * b1).

Definition isolated_quartic_x (O1 O2 : Point) (r1 r2 x : R) : R :=
  sylvester_res_monic_quad
    (circle_y_lin O1) (circle_y_const O1 r1 x)
    (circle_y_lin O2) (circle_y_const O2 r2 x).

Definition isolated_quartic_y (O1 O2 : Point) (r1 r2 y : R) : R :=
  sylvester_res_monic_quad
    (circle_x_lin O1) (circle_x_const O1 r1 y)
    (circle_x_lin O2) (circle_x_const O2 r2 y).

(* -------------------------------------------------------------------------- *)
(* §2  WITNESS / Eval — locked fixture (RED surface).                         *)
(*                                                                            *)
(* DiscOverlay CIRCLE_5 ∩ CIRCLE_CROSSING: centres (0,0) and (7,0), r = 5.  *)
(* Both radical-line nodes have x = 7/2.  If the named resultant is wrong, *)
(* this Example does not close.                                               *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"64-naa-quartic","topic":"core","lemma":"radical_points_satisfy_isolated_quartic","title":"Radical-line intersection coordinates are roots of the isolated circle-circle resultant","file":"theories/ArcArcIsolatedQuartic.v","witness":"locked-7-2","board":"#64"} *)

Example locked_fixture_isolated_quartic_x :
  isolated_quartic_x (mkPoint 0 0) (mkPoint 7 0) 5 5 (7 / 2) = 0.
Proof.
  unfold isolated_quartic_x, sylvester_res_monic_quad,
         circle_y_lin, circle_y_const.
  cbn [px py].
  field.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Common zeros of the two circle equations are resultant roots.          *)
(*     Hypothesis-free; pure substitution + ring.                             *)
(* -------------------------------------------------------------------------- *)

Lemma sylvester_res_monic_quad_of_common_root :
  forall b1 c1 b2 c2 t,
    t * t + b1 * t + c1 = 0 ->
    t * t + b2 * t + c2 = 0 ->
    sylvester_res_monic_quad b1 c1 b2 c2 = 0.
Proof.
  intros b1 c1 b2 c2 t H1 H2.
  unfold sylvester_res_monic_quad.
  replace c1 with (- (t * t) - b1 * t) by lra.
  replace c2 with (- (t * t) - b2 * t) by lra.
  ring.
Qed.

Lemma circle_poly_of_dist_sq :
  forall O r (P : Point),
    dist_sq O P = r * r ->
    circle_poly O r (px P) (py P) = 0.
Proof.
  intros O r P H.
  unfold circle_poly. rewrite <- H. unfold dist_sq. ring.
Qed.

Lemma isolated_quartic_vanishes_on_common_zeros :
  forall (O1 O2 : Point) (r1 r2 : R) (P : Point),
    circle_poly O1 r1 (px P) (py P) = 0 ->
    circle_poly O2 r2 (px P) (py P) = 0 ->
    isolated_quartic_x O1 O2 r1 r2 (px P) = 0.
Proof.
  intros O1 O2 r1 r2 P H1 H2.
  unfold isolated_quartic_x.
  rewrite circle_poly_as_quad_y in H1, H2.
  apply sylvester_res_monic_quad_of_common_root with (t := py P);
    exact H1 || exact H2.
Qed.

Lemma isolated_quartic_y_vanishes_on_common_zeros :
  forall (O1 O2 : Point) (r1 r2 : R) (P : Point),
    circle_poly O1 r1 (px P) (py P) = 0 ->
    circle_poly O2 r2 (px P) (py P) = 0 ->
    isolated_quartic_y O1 O2 r1 r2 (py P) = 0.
Proof.
  intros O1 O2 r1 r2 P H1 H2.
  unfold isolated_quartic_y.
  rewrite circle_poly_as_quad_x in H1, H2.
  apply sylvester_res_monic_quad_of_common_root with (t := px P);
    exact H1 || exact H2.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Year-1 guard (one named hyp) and the coordinate-identity headline.     *)
(* -------------------------------------------------------------------------- *)

(* Bundles the guards already used by `two_circles_radical_point` /
   `radical_points_on_circles`: positive radii, distinct centres, and
   proper intersection (|r1−r2| < d < r1+r2). *)
Definition circles_properly_intersect (O1 O2 : Point) (r1 r2 : R) : Prop :=
  0 < r1 /\
  0 < r2 /\
  0 < dist O1 O2 /\
  Rabs (r1 - r2) < dist O1 O2 /\
  dist O1 O2 < r1 + r2.

(* Degenerate pencil: coincident centres.  The radical-axis construction
   divides by dist = 0; the pair is not `circles_properly_intersect`. *)
Lemma coincident_centres_not_proper :
  forall (O1 O2 : Point) (r1 r2 : R),
    dist O1 O2 = 0 ->
    ~ circles_properly_intersect O1 O2 r1 r2.
Proof.
  intros O1 O2 r1 r2 Hd [ _ [ _ [Hdpos _]]].
  lra.
Qed.

Theorem radical_points_satisfy_isolated_quartic :
  forall (O1 O2 : Point) (r1 r2 : R),
    circles_properly_intersect O1 O2 r1 r2 ->
    isolated_quartic_x O1 O2 r1 r2
      (px (radical_point_plus O1 O2 r1 r2)) = 0 /\
    isolated_quartic_x O1 O2 r1 r2
      (px (radical_point_minus O1 O2 r1 r2)) = 0 /\
    isolated_quartic_y O1 O2 r1 r2
      (py (radical_point_plus O1 O2 r1 r2)) = 0 /\
    isolated_quartic_y O1 O2 r1 r2
      (py (radical_point_minus O1 O2 r1 r2)) = 0.
Proof.
  intros O1 O2 r1 r2 [Hr1 [Hr2 [Hdpos [Hrabs Hdlt]]]].
  destruct (radical_points_on_circles O1 O2 r1 r2 Hr1 Hr2 Hdpos Hrabs Hdlt)
    as [[Hp1 Hp2] [Hm1 Hm2]].
  repeat split.
  - apply isolated_quartic_vanishes_on_common_zeros;
      apply circle_poly_of_dist_sq; assumption.
  - apply isolated_quartic_vanishes_on_common_zeros;
      apply circle_poly_of_dist_sq; assumption.
  - apply isolated_quartic_y_vanishes_on_common_zeros;
      apply circle_poly_of_dist_sq; assumption.
  - apply isolated_quartic_y_vanishes_on_common_zeros;
      apply circle_poly_of_dist_sq; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions locked_fixture_isolated_quartic_x.
Print Assumptions isolated_quartic_vanishes_on_common_zeros.
Print Assumptions coincident_centres_not_proper.
Print Assumptions radical_points_satisfy_isolated_quartic.
