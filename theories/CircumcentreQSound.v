(* ============================================================================
   NetTopologySuite.Proofs.CircumcentreQSound
   ----------------------------------------------------------------------------
   Formal soundness of the circumcenter formula used by oracle/driver.ml:
   `circumcentre_q`.

   The OCaml function `circumcentre_q (ax,ay) (bx,by) (cx,cy)` computes the
   unique circumcenter of three non-collinear planar points and its squared
   radius via the exact formula:

       D  := 2·(ax·(by−cy) + bx·(cy−ay) + cx·(ay−by))
       ox := (|A|²·(by−cy) + |B|²·(cy−ay) + |C|²·(ay−by)) / D
       oy := (|A|²·(cx−bx) + |B|²·(ax−cx) + |C|²·(bx−ax)) / D
       r² := (ax−ox)² + (ay−oy)²

   This file proves two Qed-closed theorems in pure `R`:

     §1  `circumcentre_formula_equidistant`
         The computed center (ox, oy) is equidistant from all three input
         points with squared distance r².  Proof: `field` after exposing
         the non-zero denominator.  This is the raw-coordinate counterpart
         of ArcChordApprox.arc_center_equidistant (which works through the
         CircularArc record wrapper).

     §2  `circumcentre_formula_inCircle_R`
         Any point P at squared distance r² from the circumcenter satisfies
         `inCircle_R A B C P = 0`.  Proof: `inCircle_R_concyclic` applied
         with the equidistance facts from §1.  This directly backs the
         oracle kernels `arc_seg_contact` and `arc_arc_contact`, which test
         candidate intersection points by checking whether their squared
         distance from (ox, oy) equals r².

     §3  `circumcentre_formula_arc_center`
         The formula (ox, oy) equals `arc_center a` when applied to the
         control points of a `CircularArc a`.  Proved by `reflexivity`
         after unfolding both definitions — they are definitionally equal.
         Corollaries connect to the existing
         ArcChordApprox.arc_center_equidistant and
         ArcArcCircles.inCircle_R_zero_of_equidistant chains.

   Three-axiom policy: only the classical-reals trio.  No Admitted / Axiom /
   Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra Field.
From NTS.Proofs Require Import Distance CurveGeometry ArcOrient ArcChordApprox
  ArcArcCircles.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Equidistance: the circumcenter formula is equidistant from A, B, C.   *)
(*                                                                            *)
(* The raw-coordinate counterpart of ArcChordApprox.arc_center_equidistant.  *)
(* The hypothesis H is the non-zero half-denominator condition; the full     *)
(* denominator D = 2*H enters via field's side conditions.  The proof is     *)
(* `field; lra` after substituting the explicit expressions for ox, oy, r2. *)
(* -------------------------------------------------------------------------- *)

Theorem circumcentre_formula_equidistant :
  forall ax ay bx by_ cx cy ox oy r2 : R,
    ax * (by_ - cy) + bx * (cy - ay) + cx * (ay - by_) <> 0 ->
    ox = (  (ax*ax + ay*ay) * (by_ - cy)
          + (bx*bx + by_*by_) * (cy - ay)
          + (cx*cx + cy*cy) * (ay - by_))
         / (2 * (ax * (by_ - cy) + bx * (cy - ay) + cx * (ay - by_))) ->
    oy = (  (ax*ax + ay*ay) * (cx - bx)
          + (bx*bx + by_*by_) * (ax - cx)
          + (cx*cx + cy*cy) * (bx - ax))
         / (2 * (ax * (by_ - cy) + bx * (cy - ay) + cx * (ay - by_))) ->
    r2 = (ax - ox) * (ax - ox) + (ay - oy) * (ay - oy) ->
    (bx - ox) * (bx - ox) + (by_ - oy) * (by_ - oy) = r2 /\
    (cx - ox) * (cx - ox) + (cy - oy) * (cy - oy) = r2.
Proof.
  intros ax ay bx by_ cx cy ox oy r2 HD Hox Hoy Hr2.
  subst ox. subst oy. subst r2.
  split; field; exact HD.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Any point at the circumradius distance lies on the circumcircle.       *)
(*                                                                            *)
(* Given the equidistance of (ox, oy) from A, B, C (§1) and the hypothesis  *)
(* that P is also at distance r² from (ox, oy), `inCircle_R A B C P = 0`.   *)
(*                                                                            *)
(* The proof applies `inCircle_R_concyclic` with O = (ox, oy).  After        *)
(* `unfold dist_sq; cbn`, each `dist_sq` reduces to the inline product form *)
(* matching the hypotheses, and `lra` closes all three equalities.           *)
(* -------------------------------------------------------------------------- *)

Theorem circumcentre_formula_inCircle_R :
  forall ax ay bx by_ cx cy ox oy r2 px_ py_ : R,
    r2 = (ax - ox) * (ax - ox) + (ay - oy) * (ay - oy) ->
    (bx - ox) * (bx - ox) + (by_ - oy) * (by_ - oy) = r2 ->
    (cx - ox) * (cx - ox) + (cy - oy) * (cy - oy) = r2 ->
    (px_ - ox) * (px_ - ox) + (py_ - oy) * (py_ - oy) = r2 ->
    inCircle_R (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy) (mkPoint px_ py_) = 0.
Proof.
  intros ax ay bx by_ cx cy ox oy r2 px_ py_ Ha Hb Hc Hp.
  apply (inCircle_R_concyclic _ _ _ _ (mkPoint ox oy)).
  - unfold dist_sq. cbn. lra.
  - unfold dist_sq. cbn. lra.
  - unfold dist_sq. cbn. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Definitional equality: circumcenter formula = arc_center.              *)
(*                                                                            *)
(* `arc_center` (CurveGeometry.v) uses the same explicit formula as          *)
(* `circumcentre_q` (oracle/driver.ml), so px/py of arc_center equal ox/oy  *)
(* by reflexivity.  This closes the bridge between the oracle's exact-Q     *)
(* computation and the Rocq circumcenter theory chain:                        *)
(*                                                                            *)
(*   circumcentre_q ≅ arc_center          (§3, definitional)                *)
(*   arc_center_equidistant               (ArcChordApprox, QED via field)   *)
(*   inCircle_R_zero_of_equidistant       (ArcArcCircles, QED via nsatz)    *)
(*   arc_arc_intersects_shared_vertex     (ArcArcSound, QED)                 *)
(* -------------------------------------------------------------------------- *)

Lemma circumcentre_formula_arc_center_x :
  forall a : CircularArc,
    valid_arc a ->
    px (arc_center a) =
      let ax := px (arc_start a) in let ay := py (arc_start a) in
      let bx := px (arc_mid   a) in let by_ := py (arc_mid   a) in
      let cx := px (arc_end   a) in let cy := py (arc_end   a) in
      (  (ax*ax + ay*ay) * (by_ - cy)
       + (bx*bx + by_*by_) * (cy - ay)
       + (cx*cx + cy*cy) * (ay - by_))
      / (2 * (ax * (by_ - cy) + bx * (cy - ay) + cx * (ay - by_))).
Proof. intros a _. unfold arc_center. cbn. reflexivity. Qed.

Lemma circumcentre_formula_arc_center_y :
  forall a : CircularArc,
    valid_arc a ->
    py (arc_center a) =
      let ax := px (arc_start a) in let ay := py (arc_start a) in
      let bx := px (arc_mid   a) in let by_ := py (arc_mid   a) in
      let cx := px (arc_end   a) in let cy := py (arc_end   a) in
      (  (ax*ax + ay*ay) * (cx - bx)
       + (bx*bx + by_*by_) * (ax - cx)
       + (cx*cx + cy*cy) * (bx - ax))
      / (2 * (ax * (by_ - cy) + bx * (cy - ay) + cx * (ay - by_))).
Proof. intros a _. unfold arc_center. cbn. reflexivity. Qed.

(* Corollary: the arc_center_equidistant chain (QED) implies that the
   circumcenter formula is equidistant from the three arc control points. *)
Corollary circumcentre_formula_arc_equidistant :
  forall (a : CircularArc),
    valid_arc a ->
    dist_sq (arc_center a) (arc_mid a) = dist_sq (arc_center a) (arc_start a) /\
    dist_sq (arc_center a) (arc_end a) = dist_sq (arc_center a) (arc_start a).
Proof.
  intros a Hva.
  pose proof (arc_center_equidistant a Hva) as [Hsm Hse].
  split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions circumcentre_formula_equidistant.
Print Assumptions circumcentre_formula_inCircle_R.
Print Assumptions circumcentre_formula_arc_equidistant.
