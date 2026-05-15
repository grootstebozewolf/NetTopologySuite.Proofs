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
(* Reformulation lemmas.                                                       *)
(* -------------------------------------------------------------------------- *)

Lemma shared_point_implies_AB_opposite_sides : forall A B C D X,
  between A B X -> between C D X ->
  cross A B C * cross A B D <= 0.
Proof.
  intros. apply (segments_share_point_implies_opposite_sides A B C D X);
                assumption.
Qed.

Lemma shared_point_implies_CD_opposite_sides : forall A B C D X,
  between A B X -> between C D X ->
  cross C D A * cross C D B <= 0.
Proof.
  intros. apply (segments_share_point_implies_opposite_sides A B C D X);
                assumption.
Qed.

Lemma cross_AB_positive_implies_no_shared : forall A B C D,
  cross A B C * cross A B D > 0 ->
  ~ exists X, between A B X /\ between C D X.
Proof.
  intros A B C D H. apply same_side_rejection_is_sound. left. exact H.
Qed.

Lemma cross_CD_positive_implies_no_shared : forall A B C D,
  cross C D A * cross C D B > 0 ->
  ~ exists X, between A B X /\ between C D X.
Proof.
  intros A B C D H. apply same_side_rejection_is_sound. right. exact H.
Qed.

Lemma trivial_self_intersection : forall A B,
  exists X, between A B X /\ between A B X.
Proof.
  intros A B. exists A. split; apply between_P0.
Qed.

(* -------------------------------------------------------------------------- *)
(* Strict completeness (the partial converse of                               *)
(* `segments_share_point_implies_opposite_sides`).                            *)
(*                                                                            *)
(* If BOTH cross-product products are strictly negative, the segments share   *)
(* an interior point.  This is the "proper crossing" case: all four signs    *)
(* are non-zero, with opposite signs in each pair.  Witness is constructed   *)
(* explicitly via Cramer's rule on the parametric form: the intersection     *)
(* point is `lerp t C D` where `t = cross A B C / (cross A B C - cross A B D)` *)
(* lies in `(0, 1)` under the premises.                                      *)
(*                                                                            *)
(* The FULL converse (with `<= 0` instead of `< 0` -- i.e., including the   *)
(* degenerate / collinear cases) is FALSE.  Counter-example:                  *)
(*   A=(0,0) B=(1,0) C=(2,0) D=(3,0)                                          *)
(* All four crosses are zero (so both products are 0 ≤ 0), but the segments  *)
(* are disjoint collinear segments on the x-axis sharing no point.  Handling *)
(* the `= 0` cases requires the algorithmic case analysis that NTS's         *)
(* `RobustLineIntersector` performs explicitly; that's `IntersectCollinear`  *)
(* in the Coq binary64 layer.                                                 *)
(* -------------------------------------------------------------------------- *)

(* Helper: under opposite-sign hypothesis on `a` and `b`, the ratio          *)
(* `a / (a - b)` lies in the unit interval.  Proved via `nra` after          *)
(* exposing the multiplicative identity `(a - b) * /(a - b) = 1` so the     *)
(* nonlinear-arithmetic decision procedure can clear the division.          *)
Lemma div_in_unit_interval :
  forall a b : R, a * b < 0 -> 0 <= a / (a - b) <= 1.
Proof.
  intros a b H.
  assert (Hd : a - b <> 0) by nra.
  unfold Rdiv.
  destruct (Rtotal_order (a - b) 0) as [Hd_neg | [Hd_zero | Hd_pos]];
    [| exfalso; apply Hd; exact Hd_zero |].
  - (* a - b < 0:  /(a-b) < 0; the multiplicative identity is still
       `(a-b) * /(a-b) = 1`, signs cooperate via `nra`. *)
    assert (Hkey : (a - b) * /(a - b) = 1) by (apply Rinv_r; exact Hd).
    assert (Hinv_neg : /(a - b) < 0) by (apply Rinv_lt_0_compat; exact Hd_neg).
    split; nra.
  - (* a - b > 0: standard positive denominator. *)
    assert (Hkey : (a - b) * /(a - b) = 1) by (apply Rinv_r; exact Hd).
    assert (Hinv_pos : 0 < /(a - b)) by (apply Rinv_pos; exact Hd_pos).
    split; nra.
Qed.

Theorem strict_completeness :
  forall A B C D,
    cross A B C * cross A B D < 0 ->
    cross C D A * cross C D B < 0 ->
    exists X, between A B X /\ between C D X.
Proof.
  intros A B C D HABCD HCDAB.
  assert (Hden_t : cross A B C - cross A B D <> 0) by nra.
  assert (Hden_s : cross C D A - cross C D B <> 0) by nra.
  set (t := cross A B C / (cross A B C - cross A B D)).
  set (s := cross C D A / (cross C D A - cross C D B)).
  pose proof (div_in_unit_interval _ _ HABCD) as [Ht_lo Ht_hi].
  fold t in Ht_lo, Ht_hi.
  pose proof (div_in_unit_interval _ _ HCDAB) as [Hs_lo Hs_hi].
  fold s in Hs_lo, Hs_hi.
  (* Witness X = lerp t C D.  Show simultaneously between A B X by giving s
     as the AB-parameter; the coordinate identity X = lerp s A B holds as a
     polynomial identity over R, closed by `field` once denominators are
     known nonzero.                                                          *)
  set (X := mkPoint
              ((1 - t) * px C + t * px D)
              ((1 - t) * py C + t * py D)).
  exists X.
  split.
  - exists s.
    repeat split; try assumption.
    + unfold X. simpl. unfold s, t, cross. field. split; assumption.
    + unfold X. simpl. unfold s, t, cross. field. split; assumption.
  - exists t. repeat split; try assumption; unfold X; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Collinear overlap completeness.                                            *)
(*                                                                            *)
(* Companion to `strict_completeness`: when all four cross-products are       *)
(* simultaneously zero (i.e., A, B, C, D are mutually collinear), the two    *)
(* segments AB and CD share a point iff at least one endpoint of one         *)
(* segment lies on the other.                                                 *)
(*                                                                            *)
(* The condition `segments_1d_overlap A B C D` packages the four-disjunct    *)
(* algorithmic check.  This is exactly how NTS's `RobustLineIntersector`     *)
(* probes the collinear-overlap case: it tests `between A B C`,              *)
(* `between A B D`, `between C D A`, `between C D B` and reports a shared    *)
(* point whenever any one is true.                                            *)
(*                                                                            *)
(* The "completeness" direction proved here is the existential one (overlap *)
(* witness ⇒ share-point witness).  Its proof is direct witness selection:   *)
(* each disjunct yields a vertex that lies on both segments.  The four       *)
(* cross-zero premises aren't needed for this direction -- they're carried   *)
(* through the statement so callers using the binary64 layer's               *)
(* `IntersectCollinear` branch can compose with the cross-product            *)
(* evidence they already have.                                                *)
(*                                                                            *)
(* The converse direction (collinear + share ⇒ overlap) is more subtle:      *)
(* it requires parametrising the shared point on segment AB (which needs    *)
(* A ≠ B in general) and case-splitting on which of t_C, t_D, t_X lies in   *)
(* [0, 1].  Documented as the natural follow-up; not in this slice.          *)
(* -------------------------------------------------------------------------- *)

Definition segments_1d_overlap (A B C D : Point) : Prop :=
  between C D A \/ between C D B \/ between A B C \/ between A B D.

Theorem collinear_overlap_completeness :
  forall A B C D,
    cross A B C = 0 -> cross A B D = 0 ->
    cross C D A = 0 -> cross C D B = 0 ->
    segments_1d_overlap A B C D ->
    exists P, between A B P /\ between C D P.
Proof.
  intros A B C D _ _ _ _ Hov.
  destruct Hov as [HA | [HB | [HC | HD]]].
  - exists A. split; [apply between_P0 | exact HA].
  - exists B. split; [apply between_P1 | exact HB].
  - exists C. split; [exact HC | apply between_P0].
  - exists D. split; [exact HD | apply between_P1].
Qed.

(* Symmetry: swapping the two segments leaves the 1D-overlap predicate     *)
(* unchanged.  Useful when downstream proofs want to canonicalise the      *)
(* argument order.                                                          *)
Lemma segments_1d_overlap_sym :
  forall A B C D, segments_1d_overlap A B C D <-> segments_1d_overlap C D A B.
Proof.
  intros A B C D. unfold segments_1d_overlap. tauto.
Qed.

(* Endpoint-coincidence sufficiency: if one segment's endpoint equals one  *)
(* of the other's, the overlap predicate holds trivially.  Captures the    *)
(* common "shared endpoint" sub-case of `IntersectCollinear`.               *)
Lemma segments_1d_overlap_shared_endpoint :
  forall A B C D,
    (A = C \/ A = D \/ B = C \/ B = D) ->
    segments_1d_overlap A B C D.
Proof.
  intros A B C D [HAC | [HAD | [HBC | HBD]]];
    unfold segments_1d_overlap.
  - left.  subst. apply between_P0.
  - left.  subst. apply between_P1.
  - right; left.  subst. apply between_P0.
  - right; left.  subst. apply between_P1.
Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit.                                                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions segments_share_point_implies_opposite_sides.
Print Assumptions same_side_rejection_is_sound.
Print Assumptions strict_completeness.
Print Assumptions collinear_overlap_completeness.
Print Assumptions segments_1d_overlap_sym.
Print Assumptions segments_1d_overlap_shared_endpoint.
