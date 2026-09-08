(* ============================================================================
   NetTopologySuite.Proofs.CircleCircleResultant
   ----------------------------------------------------------------------------
   Issue #64 ask #5b / N-AA — coordinate certificate: constructor ⇒
   resultant root.  Under `circles_properly_intersect`, the named
   radical-line points (`radical_point_plus` / `_minus`) are roots of
   the affine circle–circle resultants.  This is not the converse
   (resultant vanishing does not identify these radical coordinates),
   and not a formal degree / Bézout / homogenisation proof.

   Landscaping, not revolutionary: this names coordinates a later
   extracted 𝓘 / cook would write if it existed.  It does not
   implement 𝓘, mint hens, or execute ADR-0007.  Certificate on the
   existing radical-axis constructor
   (`ArcArcCircles.radical_point_plus` / `_minus`) only.

   QEX (explicit, not a headline): circular γ : [0,1] → S and the
   parameters (ti, tj) are not constructed; spans are not minted.
   `SheetHenCook` is not Required and is not reminted.

   Named polynomial (Classic-free, 3-axiom):

     circle_poly O r x y     :=  (x − Ox)² + (y − Oy)² − r²
     circle_circle_res_x     :=  Sylvester Res_y of the two circle
                                 polynomials (affine elimination).
     circle_circle_res_y     :=  Sylvester Res_x (symmetric).

   Informal Bézout remark (not proved here): two conics meet in 4
   points, 2 at the circular points at infinity; the affine
   certificate is degree ≤ 2.  `ArcArcQuartic.v` stays the 4-axiom
   atan2/Vieta discharge; this file does not Require it.

   HEADLINE (constructor ⇒ resultant root; one named Year-1 guard):
     `radical_points_satisfy_circle_circle_res`
     — both named radical-line x- and y-coordinates are roots of the
       corresponding affine resultant.

   Supporting (hypothesis-free):
     `circle_circle_res_vanishes_on_common_zeros` and
     `circle_circle_res_y_vanishes_on_common_zeros`.

   WITNESS topic: core · claimId: 64-naa-res · witness: locked-7-2
   lane: proofs
   issue: #64
   Eval (RED until both resultants vanish on the locked nodes):
     res_x (0,0) (7,0) 5 5 (7/2) = 0
     res_y (0,0) (7,0) 5 5 (±√(51/4)) = 0
     and the same on `radical_point_plus` / `_minus` of that fixture.
     If res_y were wrong, the x-only Example would still have closed —
     the y- and radical-point Examples stop that.

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

(* Affine Res_y of the two circle equations.  Informal Bézout remark
   (not a degree proof): counts 4 (2 at infinity); affine cert ≤ 2. *)
Definition circle_circle_res_x (O1 O2 : Point) (r1 r2 x : R) : R :=
  sylvester_res_monic_quad
    (circle_y_lin O1) (circle_y_const O1 r1 x)
    (circle_y_lin O2) (circle_y_const O2 r2 x).

(* Affine Res_x of the two circle equations.  Same informal remark. *)
Definition circle_circle_res_y (O1 O2 : Point) (r1 r2 y : R) : R :=
  sylvester_res_monic_quad
    (circle_x_lin O1) (circle_x_const O1 r1 y)
    (circle_x_lin O2) (circle_x_const O2 r2 y).

(* -------------------------------------------------------------------------- *)
(* §2  WITNESS / Eval — locked fixture (RED surface).                         *)
(*                                                                            *)
(* DiscOverlay CIRCLE_5 ∩ CIRCLE_CROSSING: centres (0,0) and (7,0), r = 5.  *)
(* Nodes (7/2, ±√(51/4)).  x-only was too thin: a wrong res_y still closed. *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"64-naa-res","topic":"core","lemma":"radical_points_satisfy_circle_circle_res","title":"Radical-line intersection coordinates are roots of the affine circle-circle resultant","file":"theories/CircleCircleResultant.v","witness":"locked-7-2","board":"#64"} *)

Example locked_fixture_res_x :
  circle_circle_res_x (mkPoint 0 0) (mkPoint 7 0) 5 5 (7 / 2) = 0.
Proof.
  unfold circle_circle_res_x, sylvester_res_monic_quad,
         circle_y_lin, circle_y_const.
  cbn [px py].
  field.
Qed.

Example locked_fixture_res_y_plus :
  circle_circle_res_y (mkPoint 0 0) (mkPoint 7 0) 5 5 (sqrt (51 / 4)) = 0.
Proof.
  unfold circle_circle_res_y, sylvester_res_monic_quad,
         circle_x_lin, circle_x_const.
  cbn [px py].
  assert (Hy2 : (sqrt (51 / 4) - 0) * (sqrt (51 / 4) - 0) = 51 / 4).
  { transitivity (sqrt (51 / 4) * sqrt (51 / 4));
      [ring | apply sqrt_sqrt; lra]. }
  rewrite Hy2.
  field.
Qed.

Example locked_fixture_res_y_minus :
  circle_circle_res_y (mkPoint 0 0) (mkPoint 7 0) 5 5 (- sqrt (51 / 4)) = 0.
Proof.
  unfold circle_circle_res_y, sylvester_res_monic_quad,
         circle_x_lin, circle_x_const.
  cbn [px py].
  assert (Hy2 : (- sqrt (51 / 4) - 0) * (- sqrt (51 / 4) - 0) = 51 / 4).
  { transitivity (sqrt (51 / 4) * sqrt (51 / 4));
      [ring | apply sqrt_sqrt; lra]. }
  rewrite Hy2.
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

Lemma circle_circle_res_vanishes_on_common_zeros :
  forall (O1 O2 : Point) (r1 r2 : R) (P : Point),
    circle_poly O1 r1 (px P) (py P) = 0 ->
    circle_poly O2 r2 (px P) (py P) = 0 ->
    circle_circle_res_x O1 O2 r1 r2 (px P) = 0.
Proof.
  intros O1 O2 r1 r2 P H1 H2.
  unfold circle_circle_res_x.
  rewrite circle_poly_as_quad_y in H1, H2.
  apply sylvester_res_monic_quad_of_common_root with (t := py P);
    exact H1 || exact H2.
Qed.

Lemma circle_circle_res_y_vanishes_on_common_zeros :
  forall (O1 O2 : Point) (r1 r2 : R) (P : Point),
    circle_poly O1 r1 (px P) (py P) = 0 ->
    circle_poly O2 r2 (px P) (py P) = 0 ->
    circle_circle_res_y O1 O2 r1 r2 (py P) = 0.
Proof.
  intros O1 O2 r1 r2 P H1 H2.
  unfold circle_circle_res_y.
  rewrite circle_poly_as_quad_x in H1, H2.
  apply sylvester_res_monic_quad_of_common_root with (t := px P);
    exact H1 || exact H2.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Coordinate certificate under one named Year-1 guard.                   *)
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

(* Year-1 guard, unused by headline: coincident centres are not a
   proper pair (dist = 0). *)
Lemma coincident_centres_not_proper :
  forall (O1 O2 : Point) (r1 r2 : R),
    dist O1 O2 = 0 ->
    ~ circles_properly_intersect O1 O2 r1 r2.
Proof.
  intros O1 O2 r1 r2 Hd [ _ [ _ [Hdpos _]]].
  lra.
Qed.

Theorem radical_points_satisfy_circle_circle_res :
  forall (O1 O2 : Point) (r1 r2 : R),
    circles_properly_intersect O1 O2 r1 r2 ->
    circle_circle_res_x O1 O2 r1 r2
      (px (radical_point_plus O1 O2 r1 r2)) = 0 /\
    circle_circle_res_x O1 O2 r1 r2
      (px (radical_point_minus O1 O2 r1 r2)) = 0 /\
    circle_circle_res_y O1 O2 r1 r2
      (py (radical_point_plus O1 O2 r1 r2)) = 0 /\
    circle_circle_res_y O1 O2 r1 r2
      (py (radical_point_minus O1 O2 r1 r2)) = 0.
Proof.
  intros O1 O2 r1 r2 [Hr1 [Hr2 [Hdpos [Hrabs Hdlt]]]].
  destruct (radical_points_on_circles O1 O2 r1 r2 Hr1 Hr2 Hdpos Hrabs Hdlt)
    as [[Hp1 Hp2] [Hm1 Hm2]].
  repeat split.
  - apply circle_circle_res_vanishes_on_common_zeros;
      apply circle_poly_of_dist_sq; assumption.
  - apply circle_circle_res_vanishes_on_common_zeros;
      apply circle_poly_of_dist_sq; assumption.
  - apply circle_circle_res_y_vanishes_on_common_zeros;
      apply circle_poly_of_dist_sq; assumption.
  - apply circle_circle_res_y_vanishes_on_common_zeros;
      apply circle_poly_of_dist_sq; assumption.
Qed.

(* Locked radical-line nodes themselves: both resultants vanish. *)
Example locked_fixture_res_on_radical_points :
  circle_circle_res_x (mkPoint 0 0) (mkPoint 7 0) 5 5
    (px (radical_point_plus (mkPoint 0 0) (mkPoint 7 0) 5 5)) = 0 /\
  circle_circle_res_x (mkPoint 0 0) (mkPoint 7 0) 5 5
    (px (radical_point_minus (mkPoint 0 0) (mkPoint 7 0) 5 5)) = 0 /\
  circle_circle_res_y (mkPoint 0 0) (mkPoint 7 0) 5 5
    (py (radical_point_plus (mkPoint 0 0) (mkPoint 7 0) 5 5)) = 0 /\
  circle_circle_res_y (mkPoint 0 0) (mkPoint 7 0) 5 5
    (py (radical_point_minus (mkPoint 0 0) (mkPoint 7 0) 5 5)) = 0.
Proof.
  apply radical_points_satisfy_circle_circle_res.
  unfold circles_properly_intersect.
  assert (Hd : dist (mkPoint 0 0) (mkPoint 7 0) = 7).
  { unfold dist, dist_sq. cbn [px py].
    replace ((0 - 7) * (0 - 7) + (0 - 0) * (0 - 0)) with 49 by ring.
    replace 49 with (Rsqr 7) by (unfold Rsqr; ring).
    apply sqrt_Rsqr. lra. }
  rewrite Hd.
  replace (Rabs (5 - 5)) with 0.
  2: { replace (5 - 5) with 0 by ring. rewrite Rabs_R0. reflexivity. }
  repeat split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions locked_fixture_res_x.
Print Assumptions locked_fixture_res_y_plus.
Print Assumptions locked_fixture_res_y_minus.
Print Assumptions locked_fixture_res_on_radical_points.
Print Assumptions circle_circle_res_vanishes_on_common_zeros.
Print Assumptions coincident_centres_not_proper.
Print Assumptions radical_points_satisfy_circle_circle_res.
