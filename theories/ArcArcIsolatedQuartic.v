(* ============================================================================
   NetTopologySuite.Proofs.ArcArcIsolatedQuartic
   ----------------------------------------------------------------------------
   Issue #64 ask #5b / N-AA — first Year-1 𝓘 for two circular eggs on
   one sheet (ADR-0007 Accepted: sheet / hen / cook;
   𝓘 = Hit p*, ti, tj | empty | Decline).  Not a separate cathedral
   and not a remint of `SheetHenCook.v` (first cook scope stays
   chord–chord).

   ADR-0007 𝓘 on this slice:

     Hit    — under the Year-1 guard `circles_properly_intersect`,
              p* is `radical_point_plus` / `_minus`, and those
              coordinates are roots of the isolated quartic
              (`radical_points_satisfy_isolated_quartic`).
     empty  — disjoint circumcircles (d > r1+r2 or |r1−r2| > d) are
              𝓘 = empty; not this slice (the guard is proper intersection).
     Decline — legal 0007 answer.  Written in one paragraph below.

   Decline / missing constructor (not Empty, not a QEX-as-headline):
     `SheetHenCook` first cook scope is chord–chord; Year-1
     `CircularArc` is not an Egg interpolant γ:[0,1]→S there, and this
     file does not mint that constructor or widen first_cook_scope.
     The isolated quartic constructs p* (the Hit point on the sheet).
     The full triple p*, ti, tj would need that circular interpolant
     plus a sweep parameter — those constructors are not in this file.
     Coincident centres / zero radius refuse the Year-1 radical-axis
     guard (`coincident_centres_not_proper`): Decline of the cook, not ∅.

   Named polynomial (Classic-free, 3-axiom):

     circle_poly O r x y  :=  (x − Ox)² + (y − Oy)² − r²
     isolated_quartic_x   :=  Sylvester Res_y of the two circle
                              polynomials (affine elimination).

   Bézout counts four intersections of two conics.  The two circular
   points at infinity take degree 2; the affine resultant is degree ≤ 2.
   The traditional name "quartic" is the Bézout count.  `ArcArcQuartic.v`
   stays the 4-axiom atan2/Vieta discharge; this file does not Require it.

   HEADLINE (one named Year-1 guard):
     `radical_points_satisfy_isolated_quartic`
     — 𝓘 Hit coordinates: both named radical-line x- and y-coordinates
       are roots of the corresponding isolated resultant.

   Supporting (hypothesis-free):
     `isolated_quartic_vanishes_on_common_zeros`.

   WITNESS topic: core · claimId: 64-naa-quartic · witness: locked-7-2
   lane: proofs
   issue: #64
   ADR-0007: Year-1 circular–circular 𝓘 Hit p*; do not remint
   SheetHenCook / first cook scope / Egg constructors.
   Eval (RED until the named resultant is shown to vanish):
     isolated_quartic_x (0,0) (7,0) 5 5 (7/2) = 0
     — DiscOverlay / ARC_ARC_XY locked fixture.  Example
       `locked_fixture_isolated_quartic_x` is that Eval, Qed by field.

   No new oracle vectors: ARC_ARC_XY already exercises this fixture
   numerically (`oracle/arc_arc_tests.txt`, `oracle/gen_arc_arc_tests.py`).

   Proved here (THREE-AXIOM, no atan2, no Classic, no exemption).
   No `Admitted`, no `Axiom`, no `Parameter`.  Does not Require
   ArcArcQuartic / ArcSpanAtan2 / Atan2 / SheetHenCook.

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

(* WITNESS {"claimId":"64-naa-quartic","topic":"core","lemma":"radical_points_satisfy_isolated_quartic","title":"Year-1 circular-circular I Hit: radical-line p* are roots of the isolated quartic","file":"theories/ArcArcIsolatedQuartic.v","witness":"locked-7-2","board":"#64"} *)

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
(* §4  Year-1 𝓘 Hit p* under one named guard.                                 *)
(*                                                                            *)
(* ADR-0007: 𝓘 = Hit p*, ti, tj | empty | Decline.  This theorem is the      *)
(* Hit coordinate: p* = radical_point_plus/minus lies on the isolated        *)
(* quartic.  ti, tj are not minted here (no circular gamma Egg; see header   *)
(* Decline).                                                                 *)
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

(* Decline of the radical-axis cook (not 𝓘 = empty): coincident centres
   divide by dist = 0.  Legal ADR-0007 Decline, not a missing primitive. *)
Lemma coincident_centres_not_proper :
  forall (O1 O2 : Point) (r1 r2 : R),
    dist O1 O2 = 0 ->
    ~ circles_properly_intersect O1 O2 r1 r2.
Proof.
  intros O1 O2 r1 r2 Hd [ _ [ _ [Hdpos _]]].
  lra.
Qed.

(* Year-1 circular–circular 𝓘 Hit on one sheet: p* from the isolated
   quartic under the Year-1 proper-intersection guard. *)
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
