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
(* Proper-crossing uniqueness.                                                *)
(*                                                                            *)
(* Companion to `strict_completeness`: under the proper-crossing sign         *)
(* condition the shared point not only EXISTS but is UNIQUE.  This is what    *)
(* justifies speaking of *the* intersection point -- e.g. the binary64        *)
(* intersection-point forward-error bound bounds the error against a single   *)
(* well-defined target.                                                       *)
(*                                                                            *)
(* The two segment directions B - A and D - C are linearly independent in     *)
(* this regime: their 2x2 determinant equals `cross A B D - cross A B C`,     *)
(* which is nonzero because the two cross-products have strictly opposite     *)
(* signs.  Any point shared by both segments lies on both lines, so two       *)
(* shared points X, Y satisfy (t_X - t_Y)*(B - A) = (s_X - s_Y)*(D - C);      *)
(* independence forces t_X = t_Y, hence X = Y.  Only the AB-direction         *)
(* non-degeneracy is actually used; the second hypothesis is kept so the      *)
(* statement reads as the exact companion to `strict_completeness`.           *)
(* -------------------------------------------------------------------------- *)

Theorem strict_intersection_unique :
  forall A B C D X Y,
    cross A B C * cross A B D < 0 ->
    cross C D A * cross C D B < 0 ->
    between A B X -> between C D X ->
    between A B Y -> between C D Y ->
    X = Y.
Proof.
  intros A B C D X Y HAB _ HABX HCDX HABY HCDY.
  destruct HABX as [tx [_ [_ [HXx_ab HXy_ab]]]].
  destruct HCDX as [sx [_ [_ [HXx_cd HXy_cd]]]].
  destruct HABY as [ty [_ [_ [HYx_ab HYy_ab]]]].
  destruct HCDY as [sy [_ [_ [HYx_cd HYy_cd]]]].
  (* The direction determinant equals cross A B D - cross A B C, hence <> 0. *)
  assert (Hdet_id :
            (px B - px A) * (py D - py C) - (py B - py A) * (px D - px C)
            = cross A B D - cross A B C) by (unfold cross; ring).
  assert (Hdet :
            (px B - px A) * (py D - py C) - (py B - py A) * (px D - px C) <> 0).
  { rewrite Hdet_id. intro H. nra. }
  (* X - Y expressed on the AB axis equals its expression on the CD axis. *)
  assert (Heqx : (tx - ty) * (px B - px A) = (sx - sy) * (px D - px C)) by nra.
  assert (Heqy : (tx - ty) * (py B - py A) = (sx - sy) * (py D - py C)) by nra.
  (* (t_X - t_Y) * determinant = 0 by substituting the two identities. *)
  assert (Ha :
            (tx - ty)
            * ((px B - px A) * (py D - py C) - (py B - py A) * (px D - px C))
            = 0).
  { replace ((tx - ty)
             * ((px B - px A) * (py D - py C) - (py B - py A) * (px D - px C)))
      with (((tx - ty) * (px B - px A)) * (py D - py C)
            - ((tx - ty) * (py B - py A)) * (px D - px C)) by ring.
    rewrite Heqx, Heqy. ring. }
  assert (Etxy : tx = ty).
  { destruct (Rmult_integral _ _ Ha) as [H | H].
    - lra.
    - exfalso. apply Hdet. exact H. }
  destruct X as [Xx Xy]. destruct Y as [Yx Yy].
  simpl in HXx_ab, HXy_ab, HYx_ab, HYy_ab.
  f_equal.
  - rewrite HXx_ab, HYx_ab, Etxy. ring.
  - rewrite HXy_ab, HYy_ab, Etxy. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Closed form of the proper-crossing intersection point.                     *)
(*                                                                            *)
(* `strict_completeness` constructs the shared point as a convex combination  *)
(* of C and D with parameter t = cross A B C / (cross A B C - cross A B D).    *)
(* We name that point and, via `strict_intersection_unique`, show every       *)
(* shared point equals it -- so it is the closed-form coordinates of *the*    *)
(* intersection point.  This is the explicit target the binary64              *)
(* intersection-point forward-error analysis approximates.                    *)
(* -------------------------------------------------------------------------- *)

Definition strict_intersection_point (A B C D : Point) : Point :=
  mkPoint
    ((1 - cross A B C / (cross A B C - cross A B D)) * px C
       + cross A B C / (cross A B C - cross A B D) * px D)
    ((1 - cross A B C / (cross A B C - cross A B D)) * py C
       + cross A B C / (cross A B C - cross A B D) * py D).

(* The named point is genuinely shared by both segments -- the witness        *)
(* construction of `strict_completeness`, specialised to this point.          *)
Lemma strict_intersection_point_shared :
  forall A B C D,
    cross A B C * cross A B D < 0 ->
    cross C D A * cross C D B < 0 ->
    between A B (strict_intersection_point A B C D)
    /\ between C D (strict_intersection_point A B C D).
Proof.
  intros A B C D HABCD HCDAB.
  assert (Hden_t : cross A B C - cross A B D <> 0) by nra.
  assert (Hden_s : cross C D A - cross C D B <> 0) by nra.
  unfold strict_intersection_point.
  set (t := cross A B C / (cross A B C - cross A B D)).
  set (s := cross C D A / (cross C D A - cross C D B)).
  pose proof (div_in_unit_interval _ _ HABCD) as [Ht_lo Ht_hi]; fold t in Ht_lo, Ht_hi.
  pose proof (div_in_unit_interval _ _ HCDAB) as [Hs_lo Hs_hi]; fold s in Hs_lo, Hs_hi.
  split.
  - exists s. repeat split; try assumption.
    + simpl. unfold s, t, cross. field. split; assumption.
    + simpl. unfold s, t, cross. field. split; assumption.
  - exists t. repeat split; try assumption; reflexivity.
Qed.

(* Closed form: under the proper-crossing condition, any shared point IS      *)
(* `strict_intersection_point A B C D`.                                       *)
Theorem strict_intersection_eq_formula :
  forall A B C D X,
    cross A B C * cross A B D < 0 ->
    cross C D A * cross C D B < 0 ->
    between A B X -> between C D X ->
    X = strict_intersection_point A B C D.
Proof.
  intros A B C D X H1 H2 HABX HCDX.
  destruct (strict_intersection_point_shared A B C D H1 H2) as [HABP HCDP].
  apply (strict_intersection_unique A B C D X (strict_intersection_point A B C D)
           H1 H2 HABX HCDX HABP HCDP).
Qed.

(* -------------------------------------------------------------------------- *)
(* Canonical headline: under the proper-crossing condition the two segments   *)
(* cross in EXACTLY ONE point.  This packages existence                       *)
(* (`strict_completeness`, via the named witness) and uniqueness              *)
(* (`strict_intersection_unique`) as a single `exists!` statement.            *)
(* -------------------------------------------------------------------------- *)

Theorem strict_unique_shared_point :
  forall A B C D,
    cross A B C * cross A B D < 0 ->
    cross C D A * cross C D B < 0 ->
    exists! X, between A B X /\ between C D X.
Proof.
  intros A B C D H1 H2.
  destruct (strict_intersection_point_shared A B C D H1 H2) as [HAB HCD].
  exists (strict_intersection_point A B C D).
  split.
  - split; assumption.
  - intros Y [HABY HCDY].
    apply (strict_intersection_unique A B C D (strict_intersection_point A B C D) Y
             H1 H2 HAB HCD HABY HCDY).
Qed.

(* The proper-crossing point does not depend on which segment is listed       *)
(* first: both orderings name the same unique shared point.                   *)
Theorem strict_intersection_point_sym :
  forall A B C D,
    cross A B C * cross A B D < 0 ->
    cross C D A * cross C D B < 0 ->
    strict_intersection_point A B C D = strict_intersection_point C D A B.
Proof.
  intros A B C D H1 H2.
  destruct (strict_intersection_point_shared A B C D H1 H2) as [HAB1 HCD1].
  destruct (strict_intersection_point_shared C D A B H2 H1) as [HCD2 HAB2].
  apply (strict_intersection_unique A B C D
           (strict_intersection_point A B C D) (strict_intersection_point C D A B)
           H1 H2 HAB1 HCD1 HAB2 HCD2).
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

(* General version: the four cross-zero premises aren't actually needed   *)
(* -- the proof is pure witness selection.  Whenever the 1D overlap        *)
(* predicate holds (some endpoint of one segment is between the endpoints *)
(* of the other), the shared point is that endpoint itself.  This single  *)
(* theorem covers all three "positive claim" sub-cases of                  *)
(* `IntersectCollinear`:                                                    *)
(*                                                                          *)
(*   - Shared endpoint (e.g. A = C):                                        *)
(*       `between C D A` holds via `between_P0`.                            *)
(*   - T-junction (one endpoint strictly inside opposite segment):          *)
(*       e.g. A strictly between C and D, captured by `between C D A`      *)
(*       with the parameter in `(0, 1)`.                                    *)
(*   - Full collinear overlap:                                              *)
(*       At least one endpoint of one segment lies inside the other --      *)
(*       same disjunction.                                                  *)
(*                                                                          *)
(* The DETECTION of these cases from raw coordinates (i.e., recognising    *)
(* `between A B C` from cross-zero + coord-range checks) needs a converse  *)
(* of `between_in_coord_range`:                                             *)
(*                                                                          *)
(*   Lemma between_of_on_line_and_coord_range :                             *)
(*     cross P0 P1 Q = 0 ->                                                 *)
(*     Rmin (px P0) (px P1) <= px Q <= Rmax (px P0) (px P1) ->              *)
(*     Rmin (py P0) (py P1) <= py Q <= Rmax (py P0) (py P1) ->              *)
(*     between P0 P1 Q.                                                     *)
(*                                                                          *)
(* That converse is now LANDED as `between_of_on_line_and_coord_range` in   *)
(* theories/Segment.v (case split on degenerate-x / vertical / general,     *)
(* parameter taken from the non-degenerate axis, the other coordinate       *)
(* pinned via `cross = 0`).  Combined with `between_in_coord_range` it gives *)
(* the full detection bridge: callers recognise a `between` witness from     *)
(* raw `cross = 0` + coordinate-range checks, then feed it to               *)
(* `segments_1d_overlap_share` below.  This slice ships the general          *)
(* "premise carries a `between` witness" theorem -- callers with their      *)
(* own way of producing the witness use it directly.                        *)

Theorem segments_1d_overlap_share :
  forall A B C D : Point,
    segments_1d_overlap A B C D ->
    exists P, between A B P /\ between C D P.
Proof.
  intros A B C D Hov.
  destruct Hov as [HA | [HB | [HC | HD]]].
  - exists A. split; [apply between_P0 | exact HA].
  - exists B. split; [apply between_P1 | exact HB].
  - exists C. split; [exact HC | apply between_P0].
  - exists D. split; [exact HD | apply between_P1].
Qed.

(* Backward-compatible corollary with the cross-zero premises spelled out. *)
(* Useful when callers want to document that the geometric configuration   *)
(* is "all four points mutually collinear", even though the proof does     *)
(* not technically need that.                                              *)
Theorem collinear_overlap_completeness :
  forall A B C D,
    cross A B C = 0 -> cross A B D = 0 ->
    cross C D A = 0 -> cross C D B = 0 ->
    segments_1d_overlap A B C D ->
    exists P, between A B P /\ between C D P.
Proof.
  intros A B C D _ _ _ _ Hov.
  apply segments_1d_overlap_share. exact Hov.
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

(* Shared-endpoint completeness.  When one endpoint of one segment equals  *)
(* one endpoint of the other, the segments share that point trivially.    *)
(* No cross-product premise needed -- pure point-equality witness          *)
(* selection.  This is the "shared endpoint" sub-case of                  *)
(* `IntersectCollinear` that the predicate's algorithmic dispatch flags    *)
(* generically but cannot distinguish without coordinate-equality          *)
(* probing on the C# side.                                                  *)
Theorem shared_endpoint_share_point :
  forall A B C D : Point,
    (A = C \/ A = D \/ B = C \/ B = D) ->
    exists X, between A B X /\ between C D X.
Proof.
  intros A B C D [HAC | [HAD | [HBC | HBD]]].
  - subst. exists C. split; apply between_P0.
  - subst. exists D. split; [apply between_P0 | apply between_P1].
  - subst. exists C. split; [apply between_P1 | apply between_P0].
  - subst. exists D. split; [apply between_P1 | apply between_P1].
Qed.

(* -------------------------------------------------------------------------- *)
(* The converse: collinear + share => 1D overlap.                             *)
(*                                                                            *)
(* This closes the "more subtle" direction deferred in the comment above      *)
(* (collinear + share-a-point => some endpoint of one segment lies on the     *)
(* other).  Combined with `segments_1d_overlap_share` it yields the full      *)
(* biconditional characterisation of collinear-segment intersection, which    *)
(* is the complete R-side positive-claim story for `IntersectCollinear`.      *)
(* -------------------------------------------------------------------------- *)

(* Two collinear points with equal coordinates are equal. *)
Lemma points_eq_of_coords : forall R S : Point,
  px R = px S -> py R = py S -> R = S.
Proof. intros [rx ry] [sx sy] Hx Hy. cbn in *. subst. reflexivity. Qed.

(* A point on a collapsed (single-point) segment is that point. *)
Lemma between_collapse_to_endpoint : forall A B X,
  px A = px B -> py A = py B -> between A B X -> X = A.
Proof.
  intros A B X Hx Hy [t [_ [_ [Hbx Hby]]]].
  apply points_eq_of_coords.
  - rewrite Hbx. rewrite <- Hx. ring.
  - rewrite Hby. rewrite <- Hy. ring.
Qed.

(* On a non-vertical line, distinct x forces distinct points (contrapositive
   form): collinear R, S with equal x are equal. *)
Lemma collinear_nonvert_eq : forall P Q R S,
  px P <> px Q -> cross P Q R = 0 -> cross P Q S = 0 ->
  px R = px S -> R = S.
Proof.
  intros P Q R S Hpq HR HS Hxe.
  apply points_eq_of_coords; [exact Hxe |].
  assert (Hd : px Q - px P <> 0) by (intro H; apply Hpq; lra).
  assert (Hk : (px Q - px P) * (py R - py S) = 0).
  { unfold cross in HR, HS. rewrite Hxe in HR.
    replace ((px Q - px P) * (py R - py S))
      with (((px Q - px P) * (py R - py P) - (px S - px P) * (py Q - py P))
            - ((px Q - px P) * (py S - py P) - (px S - px P) * (py Q - py P)))
      by ring.
    rewrite HR, HS. ring. }
  apply Rmult_integral in Hk. destruct Hk as [H0 | H0].
  - exfalso. apply Hd. exact H0.
  - lra.
Qed.

(* On a vertical line (px P = px Q, py P <> py Q), every collinear point shares
   the common x-coordinate. *)
Lemma collinear_vertical_px : forall A B C,
  px A = px B -> py A <> py B -> cross A B C = 0 -> px C = px A.
Proof.
  intros A B C Hx Hy Hc.
  assert (Hd : py B - py A <> 0) by (intro H; apply Hy; lra).
  unfold cross in Hc. rewrite <- Hx in Hc.
  assert (Hk : (px C - px A) * (py B - py A) = 0).
  { replace ((px C - px A) * (py B - py A))
      with (- ((px A - px A) * (py C - py A) - (px C - px A) * (py B - py A)))
      by ring.
    rewrite Hc. ring. }
  apply Rmult_integral in Hk. destruct Hk as [H0 | H0].
  - lra.
  - exfalso. apply Hd. exact H0.
Qed.

(* Collinearity transfers an x-range bound to a y-range bound (non-vertical). *)
Lemma collinear_x_range_implies_y_range : forall P Q R,
  cross P Q R = 0 -> px P <> px Q ->
  Rmin (px P) (px Q) <= px R <= Rmax (px P) (px Q) ->
  Rmin (py P) (py Q) <= py R <= Rmax (py P) (py Q).
Proof.
  intros P Q R Hc Hpq Hx.
  assert (Hd : px Q - px P <> 0) by (intro H; apply Hpq; lra).
  pose (r := (px R - px P) / (px Q - px P)).
  assert (Hr := ratio_in_unit_interval (px P) (px Q) (px R) Hpq Hx).
  assert (Hrx : r * (px Q - px P) = px R - px P)
    by (unfold r, Rdiv; rewrite Rmult_assoc, (Rinv_l _ Hd); ring).
  assert (Hry : r * (py Q - py P) = py R - py P).
  { assert (Hk : (px Q - px P) * (r * (py Q - py P) - (py R - py P)) = 0).
    { replace ((px Q - px P) * (r * (py Q - py P) - (py R - py P)))
        with ((r * (px Q - px P)) * (py Q - py P)
              - (px Q - px P) * (py R - py P)) by ring.
      rewrite Hrx. unfold cross in Hc. lra. }
    apply Rmult_integral in Hk. destruct Hk as [H0 | H0].
    - exfalso. apply Hd. exact H0.
    - lra. }
  assert (Hbet : between P Q R).
  { exists r. repeat split; try (unfold r; lra).
    - replace ((1 - r) * px P + r * px Q) with (px P + r * (px Q - px P)) by ring.
      rewrite Hrx. lra.
    - replace ((1 - r) * py P + r * py Q) with (py P + r * (py Q - py P)) by ring.
      rewrite Hry. lra. }
  apply between_in_coord_range in Hbet. destruct Hbet as [_ Hyr]. exact Hyr.
Qed.

(* Symmetric transfer: y-range bound to x-range bound (non-horizontal). *)
Lemma collinear_y_range_implies_x_range : forall P Q R,
  cross P Q R = 0 -> py P <> py Q ->
  Rmin (py P) (py Q) <= py R <= Rmax (py P) (py Q) ->
  Rmin (px P) (px Q) <= px R <= Rmax (px P) (px Q).
Proof.
  intros P Q R Hc Hpq Hy.
  assert (Hd : py Q - py P <> 0) by (intro H; apply Hpq; lra).
  pose (r := (py R - py P) / (py Q - py P)).
  assert (Hr := ratio_in_unit_interval (py P) (py Q) (py R) Hpq Hy).
  assert (Hry : r * (py Q - py P) = py R - py P)
    by (unfold r, Rdiv; rewrite Rmult_assoc, (Rinv_l _ Hd); ring).
  assert (Hrx : r * (px Q - px P) = px R - px P).
  { assert (Hk : (py Q - py P) * (r * (px Q - px P) - (px R - px P)) = 0).
    { replace ((py Q - py P) * (r * (px Q - px P) - (px R - px P)))
        with ((px Q - px P) * (r * (py Q - py P))
              - (px R - px P) * (py Q - py P)) by ring.
      rewrite Hry. unfold cross in Hc. lra. }
    apply Rmult_integral in Hk. destruct Hk as [H0 | H0].
    - exfalso. apply Hd. exact H0.
    - lra. }
  assert (Hbet : between P Q R).
  { exists r. repeat split; try (unfold r; lra).
    - replace ((1 - r) * px P + r * px Q) with (px P + r * (px Q - px P)) by ring.
      rewrite Hrx. lra.
    - replace ((1 - r) * py P + r * py Q) with (py P + r * (py Q - py P)) by ring.
      rewrite Hry. lra. }
  apply between_in_coord_range in Hbet. destruct Hbet as [Hxr _]. exact Hxr.
Qed.

(* For a collinear point, an x-range bound alone (on a non-vertical segment)
   already gives betweenness. *)
Lemma between_of_collinear_x : forall P Q R,
  px P <> px Q -> cross P Q R = 0 ->
  Rmin (px P) (px Q) <= px R <= Rmax (px P) (px Q) ->
  between P Q R.
Proof.
  intros P Q R Hpq Hc Hx.
  apply between_of_on_line_and_coord_range.
  - exact Hc.
  - exact Hx.
  - apply collinear_x_range_implies_y_range; assumption.
Qed.

Lemma between_of_collinear_y : forall P Q R,
  py P <> py Q -> cross P Q R = 0 ->
  Rmin (py P) (py Q) <= py R <= Rmax (py P) (py Q) ->
  between P Q R.
Proof.
  intros P Q R Hpq Hc Hy.
  apply between_of_on_line_and_coord_range.
  - exact Hc.
  - apply collinear_y_range_implies_x_range; assumption.
  - exact Hy.
Qed.

(* 1D core: two closed real intervals that share a point have an endpoint of
   one inside the other. *)
Lemma range_overlap_endpoint_in : forall a b c d x : R,
  Rmin a b <= x <= Rmax a b ->
  Rmin c d <= x <= Rmax c d ->
  (Rmin c d <= a <= Rmax c d) \/ (Rmin c d <= b <= Rmax c d) \/
  (Rmin a b <= c <= Rmax a b) \/ (Rmin a b <= d <= Rmax a b).
Proof.
  intros a b c d x [Hax Hxb] [Hcx Hxd].
  unfold Rmin, Rmax in *.
  destruct (Rle_dec a b), (Rle_dec c d),
           (Rle_dec a c), (Rle_dec a d), (Rle_dec b c), (Rle_dec b d);
    solve [ left; split; lra
          | right; left; split; lra
          | right; right; left; split; lra
          | right; right; right; split; lra ].
Qed.

Theorem collinear_share_implies_1d_overlap : forall A B C D,
  cross A B C = 0 -> cross A B D = 0 ->
  cross C D A = 0 -> cross C D B = 0 ->
  (exists X, between A B X /\ between C D X) ->
  segments_1d_overlap A B C D.
Proof.
  intros A B C D HABC HABD HCDA HCDB [X [HabX HcdX]].
  unfold segments_1d_overlap.
  destruct (between_in_coord_range A B X HabX) as [HXabx HXaby].
  destruct (between_in_coord_range C D X HcdX) as [HXcdx HXcdy].
  destruct (Req_dec (px A) (px B)) as [HxAB | HxABne].
  - (* px A = px B *)
    destruct (Req_dec (py A) (py B)) as [HyAB | HyABne].
    + (* A = B : X = A, so A lies on [C,D] *)
      assert (HXA : X = A) by (apply (between_collapse_to_endpoint A B X); auto).
      left. rewrite <- HXA. exact HcdX.
    + (* AB is vertical and non-degenerate *)
      destruct (Req_dec (py C) (py D)) as [HyCD | HyCDne].
      * (* C, D share x (= px A) and y, hence C = D : X = C lies on [A,B] *)
        assert (HxCA : px C = px A) by (apply (collinear_vertical_px A B C); auto).
        assert (HxDA : px D = px A) by (apply (collinear_vertical_px A B D); auto).
        assert (HXC : X = C).
        { apply (between_collapse_to_endpoint C D X);
            [rewrite HxCA, HxDA; reflexivity | exact HyCD | exact HcdX]. }
        right; right; left. rewrite <- HXC. exact HabX.
      * (* y axis is faithful : run the 1D core on y *)
        destruct (range_overlap_endpoint_in (py A) (py B) (py C) (py D) (py X)
                    HXaby HXcdy) as [HA | [HB | [HC | HD]]].
        -- left.                apply between_of_collinear_y;
                                  [exact HyCDne | exact HCDA | exact HA].
        -- right; left.         apply between_of_collinear_y;
                                  [exact HyCDne | exact HCDB | exact HB].
        -- right; right; left.  apply between_of_collinear_y;
                                  [exact HyABne | exact HABC | exact HC].
        -- right; right; right. apply between_of_collinear_y;
                                  [exact HyABne | exact HABD | exact HD].
  - (* px A <> px B : the line is non-vertical, x axis is faithful *)
    destruct (Req_dec (px C) (px D)) as [HxCD | HxCDne].
    + (* C, D collinear with the non-vertical line and share x, hence C = D *)
      assert (HCD : C = D)
        by (apply (collinear_nonvert_eq A B C D);
            [exact HxABne | exact HABC | exact HABD | exact HxCD]).
      assert (HXC : X = C).
      { apply (between_collapse_to_endpoint C D X);
          [exact HxCD | rewrite HCD; reflexivity | exact HcdX]. }
      right; right; left. rewrite <- HXC. exact HabX.
    + destruct (range_overlap_endpoint_in (px A) (px B) (px C) (px D) (px X)
                  HXabx HXcdx) as [HA | [HB | [HC | HD]]].
      * left.                apply between_of_collinear_x;
                              [exact HxCDne | exact HCDA | exact HA].
      * right; left.         apply between_of_collinear_x;
                              [exact HxCDne | exact HCDB | exact HB].
      * right; right; left.  apply between_of_collinear_x;
                              [exact HxABne | exact HABC | exact HC].
      * right; right; right. apply between_of_collinear_x;
                              [exact HxABne | exact HABD | exact HD].
Qed.

(* The full biconditional: for collinear segments, sharing a point is
   equivalent to 1D overlap of their extents. *)
Theorem collinear_share_iff_1d_overlap : forall A B C D,
  cross A B C = 0 -> cross A B D = 0 ->
  cross C D A = 0 -> cross C D B = 0 ->
  ((exists X, between A B X /\ between C D X) <-> segments_1d_overlap A B C D).
Proof.
  intros A B C D HABC HABD HCDA HCDB. split.
  - intro H. exact (collinear_share_implies_1d_overlap A B C D HABC HABD HCDA HCDB H).
  - apply segments_1d_overlap_share.
Qed.

(* -------------------------------------------------------------------------- *)
(* Collinearity transfer.                                                     *)
(*                                                                            *)
(* If A <> B and two points C, D both lie on line AB (cross A B C = 0 and     *)
(* cross A B D = 0), then any further point X on line AB also lies on line    *)
(* CD: cross C D X = 0.  Geometrically, C and D pin down line AB, so line CD  *)
(* coincides with it (or, when C = D, cross C D X is degenerately zero).      *)
(*                                                                            *)
(* Non-vertical case: with u := px B - px A <> 0, the two collinearity        *)
(* equations give u*(py D - py C) = v*(px D - px C) and the analogue for X,   *)
(* whence u * cross C D X = 0; u <> 0 finishes.  Vertical case: all four      *)
(* x-coordinates coincide (via `collinear_vertical_px`), so cross C D X = 0   *)
(* outright.  Only A <> B is needed -- C = D is fine.                         *)
(* -------------------------------------------------------------------------- *)

Lemma cross_collinear_transfer : forall A B C D X,
  A <> B ->
  cross A B C = 0 -> cross A B D = 0 -> cross A B X = 0 ->
  cross C D X = 0.
Proof.
  intros A B C D X HAB HABC HABD HABX.
  destruct (Req_dec (px A) (px B)) as [HxAB | HxABne].
  - (* Vertical line AB: px A = px B, so py A <> py B. *)
    assert (Hpy : py A <> py B).
    { intro Hpy. apply HAB. apply points_eq_of_coords; assumption. }
    pose proof (collinear_vertical_px A B C HxAB Hpy HABC) as HpxC.
    pose proof (collinear_vertical_px A B D HxAB Hpy HABD) as HpxD.
    pose proof (collinear_vertical_px A B X HxAB Hpy HABX) as HpxX.
    unfold cross. rewrite HpxC, HpxD, HpxX. ring.
  - (* Non-vertical line AB: u := px B - px A <> 0. *)
    set (u := px B - px A). set (v := py B - py A).
    assert (Hu : u <> 0).
    { unfold u. intro Hz. apply HxABne. lra. }
    assert (Hi : u * (py D - py C) = v * (px D - px C)).
    { unfold u, v, cross in *. nra. }
    assert (Hii : u * (py X - py C) = v * (px X - px C)).
    { unfold u, v, cross in *. nra. }
    assert (H0 : u * cross C D X = 0).
    { unfold cross.
      replace (u * ((px D - px C) * (py X - py C)
                    - (px X - px C) * (py D - py C)))
        with ((px D - px C) * (u * (py X - py C))
              - (px X - px C) * (u * (py D - py C))) by ring.
      rewrite Hi, Hii. ring. }
    destruct (Rmult_integral _ _ H0) as [Hbad | Hgood].
    + exfalso. apply Hu. exact Hbad.
    + exact Hgood.
Qed.

(* The collinear share/overlap biconditional from just two cross-zero         *)
(* premises plus A <> B -- the form callers actually have (e.g. the binary64  *)
(* `IntersectCollinear` verdict establishes that C, D lie on line AB).  The   *)
(* other two cross-zeros are supplied by `cross_collinear_transfer`.          *)
Theorem collinear_share_iff_1d_overlap_2premise : forall A B C D,
  A <> B ->
  cross A B C = 0 -> cross A B D = 0 ->
  ((exists X, between A B X /\ between C D X) <-> segments_1d_overlap A B C D).
Proof.
  intros A B C D HAB HABC HABD.
  assert (HABA : cross A B A = 0) by (unfold cross; ring).
  assert (HABB : cross A B B = 0) by (unfold cross; ring).
  pose proof (cross_collinear_transfer A B C D A HAB HABC HABD HABA) as HCDA.
  pose proof (cross_collinear_transfer A B C D B HAB HABC HABD HABB) as HCDB.
  exact (collinear_share_iff_1d_overlap A B C D HABC HABD HCDA HCDB).
Qed.

(* -------------------------------------------------------------------------- *)
(* Phase-1 capstone: the complete segment-intersection decision.              *)
(*                                                                            *)
(* NTS's `RobustLineIntersector` dispatches on the four orientation tests     *)
(* cross A B C, cross A B D, cross C D A, cross C D B.  This theorem bundles  *)
(* the three regimes already proven above -- each an independently Qed-closed *)
(* result -- into the single decision the algorithm implements:               *)
(*                                                                            *)
(*   (1) PROPER CROSSING -- both endpoint pairs strictly opposite-signed:     *)
(*       the segments share a point (`strict_completeness`).                  *)
(*   (2) REJECTION -- either pair strictly same-signed: no shared point       *)
(*       (`same_side_rejection_is_sound`).                                    *)
(*   (3) COLLINEAR -- all four cross-products zero: the segments share a      *)
(*       point iff their 1D extents overlap (`collinear_share_iff_1d_overlap`).*)
(*                                                                            *)
(* The conjunction is the citable Phase-1 R-side statement behind the         *)
(* binary64 predicate `b64_intersect_sign_filtered`: its NaN/Uncertain        *)
(* paths aside, each verdict it returns is one of these three branches.  The  *)
(* mixed-boundary sign patterns (exactly one or two crosses zero -- an        *)
(* endpoint grazing the interior of the other segment) are not folded into    *)
(* this three-way headline; they are covered by the `between`-witness route   *)
(* of `segments_1d_overlap_share`.                                            *)
(* -------------------------------------------------------------------------- *)

Theorem segment_intersection_decision : forall A B C D : Point,
  (* (1) proper crossing *)
  (cross A B C * cross A B D < 0 ->
   cross C D A * cross C D B < 0 ->
   exists X, between A B X /\ between C D X)
  /\
  (* (2) rejection *)
  (cross A B C * cross A B D > 0 \/ cross C D A * cross C D B > 0 ->
   ~ exists X, between A B X /\ between C D X)
  /\
  (* (3) collinear regime *)
  (cross A B C = 0 -> cross A B D = 0 ->
   cross C D A = 0 -> cross C D B = 0 ->
   ((exists X, between A B X /\ between C D X) <-> segments_1d_overlap A B C D)).
Proof.
  intros A B C D. split; [| split].
  - intros H1 H2. exact (strict_completeness A B C D H1 H2).
  - intros H. exact (same_side_rejection_is_sound A B C D H).
  - intros HABC HABD HCDA HCDB.
    exact (collinear_share_iff_1d_overlap A B C D HABC HABD HCDA HCDB).
Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit.                                                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions segments_share_point_implies_opposite_sides.
Print Assumptions same_side_rejection_is_sound.
Print Assumptions strict_completeness.
Print Assumptions strict_intersection_unique.
Print Assumptions strict_intersection_point_shared.
Print Assumptions strict_intersection_eq_formula.
Print Assumptions strict_unique_shared_point.
Print Assumptions strict_intersection_point_sym.
Print Assumptions segments_1d_overlap_share.
Print Assumptions collinear_overlap_completeness.
Print Assumptions segments_1d_overlap_sym.
Print Assumptions segments_1d_overlap_shared_endpoint.
Print Assumptions shared_endpoint_share_point.
Print Assumptions range_overlap_endpoint_in.
Print Assumptions collinear_share_implies_1d_overlap.
Print Assumptions collinear_share_iff_1d_overlap.
Print Assumptions cross_collinear_transfer.
Print Assumptions collinear_share_iff_1d_overlap_2premise.
Print Assumptions segment_intersection_decision.
