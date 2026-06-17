(* ============================================================================
   NetTopologySuite.Proofs.ArcArcCircles
   ----------------------------------------------------------------------------
   Issue #64 ask #5b / JTS curve-awareness N-AA: ARC-ARC CIRCLES INTERSECT,
   radical-line coordinate existence (Stage B).

   JTS issue #1195 describes the arc-arc intersection algorithm as "computes
   radical line between two circles; retains roots within both directed sweeps."
   The ARC_ARC_XY oracle mode (PR #220) implements this: for two circumcircles
   with centres O1, O2, radii r1, r2, inter-centre distance d:

       a  = (d² + r1² − r2²) / (2·d)     -- signed distance along O1 → O2
       M  = O1 + a·u                      -- foot of the radical axis
       h  = √(r1² − a²)                   -- half-chord height
       P± = M ± h·perp(u)                 -- the two candidate points

   ArcArcSound.v (merged PR #223, first slice) explicitly defers: "the
   UNCONDITIONAL both-circles existence for two arcs that cross at interior
   points (the radical-line / sqrt-discriminant coordinate story)."  This file
   closes that gap.

   Proved here (all THREE-AXIOM, no atan2/sin_lt_x, no Classic):

     §1  `inCircle_R_concyclic` — four points A,B,C,P at equal squared
         distance from a common centre O ⇒ the Shewchuk in-circle determinant
         inCircle_R A B C P = 0.  Proved by translating O to the origin
         (`inCircle_R_translation_invariant`), which removes the centre's
         coordinates, then `nsatz` on the resulting polynomial identity.
         `inCircle_R_zero_of_equidistant` — corollary: P equidistant from
         the circumcenter as the control points ⇒ inCircle_R = 0
         (arc_center_equidistant supplies OA=OB=OC, so all four concyclic).

     §3  `two_circles_radical_point` — HEADLINE unconditional existence: for
         properly-intersecting circles (|r1−r2| < d < r1+r2), the
         radical-line formula constructs an explicit point on BOTH circles.
         Pure algebra: ring + lra after asserting h·h = r1²−a² (sqrt) and
         ux²+uy² = 1 (unit vector).

     §4  `arc_arc_circles_intersect` — arc-level corollary: proper circle
         intersection ⇒ ∃ X with inCircle_R = 0 on both arcs' circumcircles.

   DEFERRED (honest scope in the header):
     - `arc_span_contains` for the radical-line points: angular sector
       membership needs atan2 and stays deferred.
     - `arc_arc_intersects` (requires both circles AND both spans).
     - Binary64 soundness of ARC_ARC_XY; sweep ≥ π / reflex arcs.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (claude-opus-4-8)
   ========================================================================== *)

From Stdlib Require Import Reals Lra Field Nsatz.
From NTS.Proofs Require Import Distance CurveGeometry ArcOrient ArcChordApprox
  ArcOffsetThreePoint.
Local Open Scope R_scope.

(* ========================================================================== *)
(* §1a  Four concyclic points ⇒ inCircle_R = 0                                *)
(*                                                                            *)
(* If A, B, C, P all lie at the same squared distance from a common centre O *)
(* (i.e. they are concyclic on the circle about O), the Shewchuk in-circle   *)
(* determinant vanishes.  We do NOT need the factored `D·(r²−||OP||²)` form  *)
(* -- the `= 0` conclusion is all the downstream proofs use, and it is the    *)
(* easiest possible shape for the Gröbner-basis tactic.                       *)
(*                                                                            *)
(* Proof: inCircle_R is translation-invariant, so shift O to the origin.      *)
(* This eliminates the centre's two coordinates (and the Ox²+Oy² cross terms *)
(* that otherwise blow up nsatz), leaving four points of equal squared norm. *)
(* ========================================================================== *)

Lemma inCircle_R_concyclic :
  forall (A B C P O : Point),
    dist_sq O A = dist_sq O B ->
    dist_sq O B = dist_sq O C ->
    dist_sq O C = dist_sq O P ->
    inCircle_R A B C P = 0.
Proof.
  intros A B C P O HAB HBC HCP.
  rewrite <- (inCircle_R_translation_invariant A B C P (- px O) (- py O)).
  unfold dist_sq, inCircle_R in *. cbn [px py] in *.
  nsatz.
Qed.

(* ========================================================================== *)
(* §1b  Equidistant from the circumcenter ⇒ on the circumcircle               *)
(*                                                                            *)
(* Immediate from §1a: arc_center_equidistant gives OA=OB=OC, and the         *)
(* hypothesis gives OP=OA, so all four control/test points are concyclic.     *)
(* ========================================================================== *)

Lemma inCircle_R_zero_of_equidistant :
  forall (a : CircularArc) (P : Point),
    valid_arc a ->
    dist_sq (arc_center a) P = dist_sq (arc_center a) (arc_start a) ->
    inCircle_R (arc_start a) (arc_mid a) (arc_end a) P = 0.
Proof.
  intros a P Hva Heq.
  pose proof (arc_center_equidistant a Hva) as [Hab Hbc].
  apply (inCircle_R_concyclic _ _ _ _ (arc_center a)); lra.
Qed.

(* ========================================================================== *)
(* §2  Radical-line point lies on both circles                                *)
(*                                                                            *)
(* HEADLINE THEOREM: for two properly-intersecting circles                    *)
(* (|r1−r2| < dist O1 O2 < r1+r2, both radii positive), the ARC_ARC_XY       *)
(* radical-line formula constructs a point P+ on BOTH circles.                *)
(*                                                                            *)
(* Proof steps:                                                               *)
(*   1.  d = dist O1 O2, d*d = dist_sq O1 O2.                                *)
(*   2.  ux = (o2x−o1x)/d, uy = (o2y−o1y)/d.  Prove ux²+uy²=1.             *)
(*   3.  a = (d²+r1²−r2²)/(2d).  Show |a| < r1 from the intersection         *)
(*       conditions (four-factor polynomial argument via nra).                *)
(*   4.  h = √(r1²−a²) > 0.  h·h = r1²−a² by sqrt_sqrt.                     *)
(*   5.  P+ = O1 + (a·ux − h·uy, a·uy + h·ux).                               *)
(*   6.  dist_sq O1 P+ = (a²+h²)(ux²+uy²) = a²+(r1²−a²) = r1².  ring.      *)
(*   7.  dist_sq O2 P+ = (a−d)²+h² = d²−2ad+r1².  With 2ad=d²+r1²−r2²:     *)
(*       = r2².  nra (via H2ad).                                              *)
(* ========================================================================== *)

Theorem two_circles_radical_point :
  forall (O1 O2 : Point) (r1 r2 : R),
    0 < r1 ->
    0 < r2 ->
    0 < dist O1 O2 ->
    Rabs (r1 - r2) < dist O1 O2 ->
    dist O1 O2 < r1 + r2 ->
    exists P : Point,
      dist_sq O1 P = r1 * r1 /\ dist_sq O2 P = r2 * r2.
Proof.
  intros O1 O2 r1 r2 Hr1 Hr2 Hdpos Hrabs Hdlt.

  (* -- Basic setup --------------------------------------------------------- *)
  set (d   := dist O1 O2) in *.
  set (o1x := px O1). set (o1y := py O1).
  set (o2x := px O2). set (o2y := py O2).

  assert (Hd_pos : 0 < d)   by exact Hdpos.
  assert (Hd_ne  : d <> 0)  by lra.

  (* d² = dist_sq O1 O2 *)
  assert (Hdd : d * d = dist_sq O1 O2).
  { unfold d, dist. rewrite sqrt_sqrt. reflexivity. apply dist_sq_nonneg. }
  assert (Hdd_decomp : d * d = (o2x - o1x) * (o2x - o1x)
                               + (o2y - o1y) * (o2y - o1y)).
  { rewrite Hdd. unfold dist_sq, o1x, o1y, o2x, o2y. ring. }

  (* Unpack Rabs condition into two linear bounds *)
  assert (Hr12a : r1 - r2 < d).
  { apply (Rle_lt_trans _ (Rabs (r1 - r2))); [apply Rle_abs | lra]. }
  assert (Hr12b : r2 - r1 < d).
  { apply (Rle_lt_trans _ (Rabs (r1 - r2)));
    [rewrite Rabs_minus_sym; apply Rle_abs | lra]. }

  (* -- Unit vector along O1 → O2 ------------------------------------------ *)
  set (ux := (o2x - o1x) / d).
  set (uy := (o2y - o1y) / d).

  (* Reconnect scaled unit vector to raw differences *)
  assert (Hdux : d * ux = o2x - o1x).
  { unfold ux. field. exact Hd_ne. }
  assert (Hduy : d * uy = o2y - o1y).
  { unfold uy. field. exact Hd_ne. }

  (* ux² + uy² = 1: multiply through by d² = (o2x-o1x)²+(o2y-o1y)², cancel. *)
  assert (Hunit : ux * ux + uy * uy = 1).
  { assert (Heq : d * d * (ux * ux + uy * uy) = d * d).
    { transitivity ((d * ux) * (d * ux) + (d * uy) * (d * uy)).
      - ring.
      - rewrite Hdux, Hduy. rewrite Hdd_decomp. ring. }
    assert (Hd2pos : 0 < d * d) by nra.
    assert (Hd2ne : d * d <> 0) by lra.
    apply (Rmult_eq_reg_l (d * d) _ _).
    - ring_simplify. lra.
    - lra. }

  (* -- Radical-axis parameter a -------------------------------------------- *)
  set (a := (d * d + r1 * r1 - r2 * r2) / (2 * d)).

  (* 2·a·d = d²+r1²−r2²  (key identity used in the O2 distance proof) *)
  assert (H2ad : 2 * a * d = d * d + r1 * r1 - r2 * r2).
  { unfold a. field. exact Hd_ne. }

  (* -- Positivity of discriminant: r1² − a² > 0 --------------------------- *)
  (*    (d+r1+r2)(d+r1−r2)(r2+d−r1)(r1+r2−d) = (2dr1)² − (d²+r1²−r2²)²    *)

  (* All four intersection factors are positive *)
  assert (Hf1 : 0 < d + r1 + r2)  by lra.
  assert (Hf2 : 0 < d + r1 - r2)  by lra.
  assert (Hf3 : 0 < r2 + d - r1)  by lra.
  assert (Hf4 : 0 < r1 + r2 - d)  by lra.

  (* Polynomial identity: product of factors = (2dr1)² − (d²+r1²−r2²)² *)
  assert (Hpoly :
    (d+r1+r2) * (d+r1-r2) * (r2+d-r1) * (r1+r2-d)
    = (2*d*r1) * (2*d*r1) - (d*d + r1*r1 - r2*r2) * (d*d + r1*r1 - r2*r2))
    by ring.

  assert (Hnum_pos :
    0 < (2*d*r1) * (2*d*r1) - (d*d + r1*r1 - r2*r2) * (d*d + r1*r1 - r2*r2)).
  { rewrite <- Hpoly. repeat apply Rmult_lt_0_compat; lra. }

  (* r1² − a² > 0: use the factored form via H2ad *)
  assert (Hh2_pos : 0 < r1 * r1 - a * a).
  { (* 4d²(r1²−a²) = (2dr1)² − (2ad)² = (2dr1)² − (d²+r1²−r2²)² > 0 *)
    assert (Hkey : 4 * d * d * (r1 * r1 - a * a)
              = (2*d*r1)*(2*d*r1) - (d*d+r1*r1-r2*r2)*(d*d+r1*r1-r2*r2)).
    { rewrite <- H2ad. ring. }
    apply (Rmult_lt_reg_l (4 * d * d)).
    - nra.
    - rewrite Rmult_0_r. rewrite Hkey. exact Hnum_pos. }

  (* -- Construct h = √(r1² − a²) ------------------------------------------ *)
  set (h2 := r1 * r1 - a * a).
  assert (Hh2_nn : 0 <= h2) by (unfold h2; lra).
  set (h := sqrt h2).
  assert (Hhh : h * h = h2).
  { unfold h. apply sqrt_sqrt. exact Hh2_nn. }

  (* -- Construct the radical-line intersection point P+ -------------------- *)
  set (mx := o1x + a * ux).
  set (my := o1y + a * uy).
  exists (mkPoint (mx - h * uy) (my + h * ux)).

  split.

  (* ---- dist_sq O1 P+ = r1² ---------------------------------------------- *)
  - unfold dist_sq.
    cbn [px py].
    unfold mx, my, o1x, o1y.
    unfold h2 in Hhh.
    (* P+ − O1 = (a·ux − h·uy, a·uy + h·ux);                              *)
    (* |P+−O1|² = (a²+h²)(ux²+uy²) = a²+h² = a²+(r1²−a²) = r1².           *)
    transitivity ((a * a + h * h) * (ux * ux + uy * uy)).
    + ring.
    + rewrite Hunit, Hhh. ring.

  (* ---- dist_sq O2 P+ = r2² ---------------------------------------------- *)
  - unfold dist_sq.
    cbn [px py].
    unfold mx, my, o1x, o1y.
    unfold o2x, o1x in Hdux. unfold o2y, o1y in Hduy.
    unfold h2 in Hhh.
    (* o2x − o1x = d·ux, o2y − o1y = d·uy (Hdux/Hduy): express O2.        *)
    assert (Ho2x : px O2 = px O1 + d * ux) by (rewrite Hdux; ring).
    assert (Ho2y : py O2 = py O1 + d * uy) by (rewrite Hduy; ring).
    rewrite Ho2x, Ho2y.
    (* |P+−O2|² = ((a−d)²+h²)(ux²+uy²) = d²−2ad+r1² = r2² via H2ad.        *)
    transitivity (((a - d) * (a - d) + h * h) * (ux * ux + uy * uy)).
    + ring.
    + rewrite Hunit, Hhh. nra.

Qed.

(* ========================================================================== *)
(* §3  Arc-level corollary: proper circle intersection ⇒ ∃ point on both     *)
(*                                                                            *)
(* Wraps §3 for valid arcs: converts between the `dist_sq O P = r²` and      *)
(* `inCircle_R = 0` representations via §2.                                   *)
(*                                                                            *)
(* DEFERRED (as stated): `arc_span_contains` for this point (angular sector   *)
(* membership, needs atan2); `arc_arc_intersects` (both circles + both spans).*)
(* ========================================================================== *)

Theorem arc_arc_circles_intersect :
  forall (a1 a2 : CircularArc),
    valid_arc a1 ->
    valid_arc a2 ->
    0 < dist (arc_center a1) (arc_center a2) ->
    Rabs (arc_radius a1 - arc_radius a2) < dist (arc_center a1) (arc_center a2) ->
    dist (arc_center a1) (arc_center a2) < arc_radius a1 + arc_radius a2 ->
    exists X : Point,
      inCircle_R (arc_start a1) (arc_mid a1) (arc_end a1) X = 0 /\
      inCircle_R (arc_start a2) (arc_mid a2) (arc_end a2) X = 0.
Proof.
  intros a1 a2 Hva1 Hva2 Hdpos Hrabs Hdlt.

  assert (Hr1 : 0 < arc_radius a1) by (apply arc_radius_pos; exact Hva1).
  assert (Hr2 : 0 < arc_radius a2) by (apply arc_radius_pos; exact Hva2).

  destruct (two_circles_radical_point
              (arc_center a1) (arc_center a2)
              (arc_radius a1) (arc_radius a2)
              Hr1 Hr2 Hdpos Hrabs Hdlt)
    as [P [Hp1 Hp2]].
  exists P.

  (* arc_radius² = dist_sq (arc_center a) (arc_start a) *)
  assert (Hr1sq : arc_radius a1 * arc_radius a1
                  = dist_sq (arc_center a1) (arc_start a1)).
  { rewrite arc_radius_eq_sqrt.
    rewrite sqrt_sqrt; [| apply arc_radius_sq_nonneg].
    unfold arc_radius_sq. reflexivity. }

  assert (Hr2sq : arc_radius a2 * arc_radius a2
                  = dist_sq (arc_center a2) (arc_start a2)).
  { rewrite arc_radius_eq_sqrt.
    rewrite sqrt_sqrt; [| apply arc_radius_sq_nonneg].
    unfold arc_radius_sq. reflexivity. }

  split.
  - apply inCircle_R_zero_of_equidistant; [exact Hva1 |]. lra.
  - apply inCircle_R_zero_of_equidistant; [exact Hva2 |]. lra.
Qed.

(* ========================================================================== *)
(* §4  Audit footprint.                                                       *)
(* ========================================================================== *)

Print Assumptions inCircle_R_zero_of_equidistant.
Print Assumptions two_circles_radical_point.
Print Assumptions arc_arc_circles_intersect.
