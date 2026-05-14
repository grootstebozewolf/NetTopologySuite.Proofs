(* ============================================================================
   NetTopologySuite.Proofs.Intersect
   ----------------------------------------------------------------------------
   The forward (soundness) direction of the cross-product based segment
   intersection test used by `RobustLineIntersector` and the overlay
   machinery throughout NetTopologySuite.

   The geometric fact: if two segments AB and CD share any common point, then
   the line AB cannot strictly separate C and D, and the line CD cannot
   strictly separate A and B.  Stated in terms of the cross product:

       between A B X /\ between C D X
        -> cross A B C * cross A B D <= 0
        /\ cross C D A * cross C D B <= 0

   The intersection tests in NTS reject pairs of segments for which either
   product is strictly positive.  This theorem is the formal justification
   that those rejections never throw away a genuine intersection.

   The converse direction (sign conditions imply intersection -- the
   completeness of the test) requires constructing the intersection point
   and is tracked as the next roadmap item.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From NTS.Proofs Require Import Distance Orientation Segment.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Auxiliary: if a convex combination of two reals equals zero, the two       *)
(* reals cannot both be strictly the same sign.  Stated as a non-strict       *)
(* inequality on their product, which is the form the geometry theorem       *)
(* downstream actually needs.                                                 *)
(* -------------------------------------------------------------------------- *)

Lemma convex_combination_zero_opposite_signs : forall a b t,
  0 <= t -> t <= 1 -> (1 - t) * a + t * b = 0 -> a * b <= 0.
Proof.
  intros a b t Ht0 Ht1 Hsum.
  destruct (Rtotal_order a 0) as [Ha | [Ha | Ha]].
  - (* a < 0 *)
    destruct (Rtotal_order b 0) as [Hb | [Hb | Hb]].
    + exfalso. nra.
    + subst. nra.
    + nra.
  - subst. nra.
  - (* a > 0 *)
    destruct (Rtotal_order b 0) as [Hb | [Hb | Hb]].
    + nra.
    + subst. nra.
    + exfalso. nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* The cross product is affine in its third argument.  This is the algebraic *)
(* fact that powers everything downstream: a point parametrised as a convex  *)
(* combination of two others has its cross-product against any base line     *)
(* equal to the corresponding convex combination of the base line's cross    *)
(* products against those two points.                                        *)
(* -------------------------------------------------------------------------- *)

Lemma cross_affine_in_third : forall P0 P1 Q1 Q2 (t : R),
  cross P0 P1 (mkPoint ((1 - t) * px Q1 + t * px Q2)
                       ((1 - t) * py Q1 + t * py Q2))
  = (1 - t) * cross P0 P1 Q1 + t * cross P0 P1 Q2.
Proof.
  intros P0 P1 Q1 Q2 t.
  unfold cross. simpl. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Main theorem: shared interior point implies both cross-product products   *)
(* are non-positive.                                                          *)
(* -------------------------------------------------------------------------- *)

Theorem segments_share_point_implies_opposite_sides :
  forall A B C D X,
  between A B X ->
  between C D X ->
  cross A B C * cross A B D <= 0 /\
  cross C D A * cross C D B <= 0.
Proof.
  intros A B C D X HAB HCD.
  pose proof (between_implies_on_line A B X HAB) as HX_on_AB.
  pose proof (between_implies_on_line C D X HCD) as HX_on_CD.
  unfold on_line in HX_on_AB, HX_on_CD.
  split.
  - (* Show cross A B C * cross A B D <= 0.
       Use the parametrisation X = (1-s) * C + s * D from HCD,
       then cross A B X = (1-s) * cross A B C + s * cross A B D
       by bilinearity, and cross A B X = 0 by HX_on_AB. *)
    destruct HCD as [s [Hs0 [Hs1 [HXx HXy]]]].
    apply (convex_combination_zero_opposite_signs (cross A B C) (cross A B D) s);
      [exact Hs0 | exact Hs1 |].
    rewrite <- HX_on_AB.
    unfold cross. rewrite HXx, HXy. ring.
  - (* Symmetric: use parametrisation X = (1-t) * A + t * B from HAB. *)
    destruct HAB as [t [Ht0 [Ht1 [HXx HXy]]]].
    apply (convex_combination_zero_opposite_signs (cross C D A) (cross C D B) t);
      [exact Ht0 | exact Ht1 |].
    rewrite <- HX_on_CD.
    unfold cross. rewrite HXx, HXy. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Corollary: contrapositive form, matching the shape NTS's                   *)
(* intersection-rejection paths actually use.  If either cross-product       *)
(* product is strictly positive, the segments do not share any point.        *)
(* -------------------------------------------------------------------------- *)

Corollary same_side_rejection_is_sound :
  forall A B C D,
  (cross A B C * cross A B D > 0 \/ cross C D A * cross C D B > 0) ->
  ~ exists X, between A B X /\ between C D X.
Proof.
  intros A B C D Hreject [X [HAB HCD]].
  pose proof (segments_share_point_implies_opposite_sides A B C D X HAB HCD)
    as [H1 H2].
  destruct Hreject as [Hr | Hr]; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Symmetry: if AB and CD share a point, so do CD and AB.  Trivially true     *)
(* but states the relation symmetry explicitly so downstream proofs can use   *)
(* it as a rewrite.                                                           *)
(* -------------------------------------------------------------------------- *)

Lemma shared_point_symmetric : forall A B C D,
  (exists X, between A B X /\ between C D X) <->
  (exists X, between C D X /\ between A B X).
Proof.
  intros A B C D. split; intros [X [H1 H2]]; exists X; tauto.
Qed.

(* -------------------------------------------------------------------------- *)
(* Degenerate case: a segment with coincident endpoints (P = P) intersects   *)
(* a second segment iff that point lies on the second segment.                *)
(* -------------------------------------------------------------------------- *)

Lemma degenerate_segment_shares_iff : forall P C D,
  (exists X, between P P X /\ between C D X) <-> between C D P.
Proof.
  intros P C D. split.
  - intros [X [HPP HCD]].
    apply between_degenerate in HPP.
    destruct HPP as [Hpx Hpy].
    destruct C as [cx cy]. destruct D as [dx dy]. destruct P as [px0 py0].
    destruct X as [xx xy].
    simpl in *. subst. exact HCD.
  - intros HCD. exists P. split.
    + apply between_P0.
    + exact HCD.
Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit.                                                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions segments_share_point_implies_opposite_sides.
Print Assumptions same_side_rejection_is_sound.
