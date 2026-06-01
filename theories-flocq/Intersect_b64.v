(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Intersect_b64
   ----------------------------------------------------------------------------
   Phase 1 first slice: a binary64 segment-pair intersection predicate built
   directly on top of `b64_orient_sign_filtered` (Phase 0 Stage A filter).
   Four orientation tests + a case dispatch, returning a five-valued
   `intersect_sign`:

     | IntersectNone        | IntersectPoint
     | IntersectCollinear   | IntersectNan
     | IntersectUncertain

   Same propagation discipline as the orientation filter: NaN dominates,
   then Uncertain, then the classical Pos/Neg/Zero case split.

   This slice ships the predicate, its structural lemmas (decidability,
   totality, 10-way constructor distinctness, NaN-propagation), the
   safe-input predicate `intersect_inputs_int_safe`, and a first
   soundness theorem in the integer regime: when the predicate returns
   `IntersectNone`, the underlying R-side segments don't share a point.
   This is the rejection-soundness direction of `theories/Intersect.v`
   lifted through binary64 in the regime where every orientation call is
   bit-exact.

   PROOF STATUS
   ============
   - `intersect_sign`                       -- 5-valued result type.
   - `b64_intersect_sign_filtered`          -- the predicate.
   - `intersect_inputs_int_safe`            -- precondition: every input
                                               coord is `coord_int_safe`
                                               (integer-valued, |.| <= 2^25).
   - `intersect_sign_eq_dec`                -- decidable equality.
   - `b64_intersect_sign_filtered_total`    -- totality (trivial).
   - `intersect_sign_distinct`              -- 10 pairwise distinct constructors.
   - `b64_intersect_sign_filtered_nan_*`    -- NaN propagation: any of the
                                               four orientation calls
                                               returning OrientRNan forces
                                               the intersect result to
                                               IntersectNan.
   - `BP2P` + `cross_R_BP_eq_cross_BP2P`    -- bridge from BPoint to the
                                               R-side `Point`.
   - `b64_intersect_sign_filtered_none_sound_small_int`
                                            -- `IntersectNone` ⇒ R-side
                                               segments don't share a point
                                               (rejection direction).
   - `b64_intersect_sign_filtered_point_sound_small_int`
                                            -- `IntersectPoint` ⇒ R-side
                                               segments share an interior
                                               point (existence direction).
   - `b64_intersect_sign_filtered_sound_small_int`
                                            -- HEADLINE.  Match-on-five form
                                               bundling both directions; the
                                               `IntersectCollinear` /
                                               `IntersectNan` /
                                               `IntersectUncertain` branches
                                               make no positive claim (`True`)
                                               by design.

   NOT yet claimed:
   - Soundness for `IntersectCollinear`: distinguishing shared endpoint /
     T-junction / collinear overlap requires the algorithmic case analysis
     NTS's `RobustLineIntersector` performs explicitly.
   - Stage A error-bound filter at the intersection level: each
     individual orientation call's filter is in play, but the
     intersection-level decision doesn't add its own filter.
   - Computation of the intersection point coordinates.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Bool.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import Core.

From NTS.Proofs Require Import Distance Orientation Segment Intersect.
From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import Orientation_b64.
From NTS.Proofs.Flocq Require Import B64_bridge.
From NTS.Proofs.Flocq Require Import Orient_b64_R.
From NTS.Proofs.Flocq Require Import Orient_b64_sound.
From NTS.Proofs.Flocq Require Import Orient_b64_exact.

Local Open Scope R_scope.

(* ============================================================================
   Result type.
   ============================================================================ *)

Inductive intersect_sign : Type :=
| IntersectNone
| IntersectPoint
| IntersectCollinear
| IntersectNan
| IntersectUncertain.

(* ============================================================================
   Boolean helpers on `orient_sign_robust`.
   ============================================================================ *)

Definition orient_is_nan (s : orient_sign_robust) : bool :=
  match s with OrientRNan => true | _ => false end.

Definition orient_is_uncertain (s : orient_sign_robust) : bool :=
  match s with OrientRUncertain => true | _ => false end.

Definition orient_is_zero (s : orient_sign_robust) : bool :=
  match s with OrientRZero => true | _ => false end.

(* Both signs are strictly positive, OR both are strictly negative.
   These are the "rejection" cases for the cross-product intersection test. *)
Definition orient_same_strict_side (s1 s2 : orient_sign_robust) : bool :=
  match s1, s2 with
  | OrientRPos, OrientRPos => true
  | OrientRNeg, OrientRNeg => true
  | _, _                   => false
  end.

(* ============================================================================
   The intersection predicate.

   Four orientation tests, then a case dispatch with the priority:
   NaN > Uncertain > rejection (same strict side) > degenerate (zero present)
   > proper crossing.
   ============================================================================ *)

Definition b64_intersect_sign_filtered (P0 P1 Q0 Q1 : BPoint) : intersect_sign :=
  let pq0 := b64_orient_sign_filtered P0 P1 Q0 in
  let pq1 := b64_orient_sign_filtered P0 P1 Q1 in
  let qp0 := b64_orient_sign_filtered Q0 Q1 P0 in
  let qp1 := b64_orient_sign_filtered Q0 Q1 P1 in
  if orient_is_nan pq0 || orient_is_nan pq1
     || orient_is_nan qp0 || orient_is_nan qp1
  then IntersectNan
  else if orient_is_uncertain pq0 || orient_is_uncertain pq1
          || orient_is_uncertain qp0 || orient_is_uncertain qp1
  then IntersectUncertain
  else if orient_same_strict_side pq0 pq1
          || orient_same_strict_side qp0 qp1
  then IntersectNone
  else if orient_is_zero pq0 || orient_is_zero pq1
          || orient_is_zero qp0 || orient_is_zero qp1
  then IntersectCollinear
  else IntersectPoint.

(* ============================================================================
   Safe-input predicate (integer regime).

   Conjunction of `coord_int_safe` on all 8 coordinates -- enough to discharge
   each of the four `orient2d_inputs_int_safe` premises for the four
   orientation calls inside the predicate.
   ============================================================================ *)

Definition intersect_inputs_int_safe (P0 P1 Q0 Q1 : BPoint) : Prop :=
  coord_int_safe (bx P0)  /\ coord_int_safe (by_ P0) /\
  coord_int_safe (bx P1)  /\ coord_int_safe (by_ P1) /\
  coord_int_safe (bx Q0)  /\ coord_int_safe (by_ Q0) /\
  coord_int_safe (bx Q1)  /\ coord_int_safe (by_ Q1).

Lemma intersect_inputs_int_safe_P0P1Q0 :
  forall P0 P1 Q0 Q1,
    intersect_inputs_int_safe P0 P1 Q0 Q1 ->
    orient2d_inputs_int_safe P0 P1 Q0.
Proof.
  intros P0 P1 Q0 Q1
    (HxP0 & HyP0 & HxP1 & HyP1 & HxQ0 & HyQ0 & _ & _).
  unfold orient2d_inputs_int_safe; tauto.
Qed.

Lemma intersect_inputs_int_safe_P0P1Q1 :
  forall P0 P1 Q0 Q1,
    intersect_inputs_int_safe P0 P1 Q0 Q1 ->
    orient2d_inputs_int_safe P0 P1 Q1.
Proof.
  intros P0 P1 Q0 Q1
    (HxP0 & HyP0 & HxP1 & HyP1 & _ & _ & HxQ1 & HyQ1).
  unfold orient2d_inputs_int_safe; tauto.
Qed.

Lemma intersect_inputs_int_safe_Q0Q1P0 :
  forall P0 P1 Q0 Q1,
    intersect_inputs_int_safe P0 P1 Q0 Q1 ->
    orient2d_inputs_int_safe Q0 Q1 P0.
Proof.
  intros P0 P1 Q0 Q1
    (HxP0 & HyP0 & _ & _ & HxQ0 & HyQ0 & HxQ1 & HyQ1).
  unfold orient2d_inputs_int_safe; tauto.
Qed.

Lemma intersect_inputs_int_safe_Q0Q1P1 :
  forall P0 P1 Q0 Q1,
    intersect_inputs_int_safe P0 P1 Q0 Q1 ->
    orient2d_inputs_int_safe Q0 Q1 P1.
Proof.
  intros P0 P1 Q0 Q1
    (_ & _ & HxP1 & HyP1 & HxQ0 & HyQ0 & HxQ1 & HyQ1).
  unfold orient2d_inputs_int_safe; tauto.
Qed.

(* ============================================================================
   Structural lemmas.
   ============================================================================ *)

Lemma intersect_sign_eq_dec :
  forall (s t : intersect_sign), {s = t} + {s <> t}.
Proof. decide equality. Defined.

Lemma b64_intersect_sign_filtered_total :
  forall P0 P1 Q0 Q1, exists s, b64_intersect_sign_filtered P0 P1 Q0 Q1 = s.
Proof. intros. eexists. reflexivity. Qed.

Lemma intersect_sign_distinct :
     IntersectNone      <> IntersectPoint
  /\ IntersectNone      <> IntersectCollinear
  /\ IntersectNone      <> IntersectNan
  /\ IntersectNone      <> IntersectUncertain
  /\ IntersectPoint     <> IntersectCollinear
  /\ IntersectPoint     <> IntersectNan
  /\ IntersectPoint     <> IntersectUncertain
  /\ IntersectCollinear <> IntersectNan
  /\ IntersectCollinear <> IntersectUncertain
  /\ IntersectNan       <> IntersectUncertain.
Proof. repeat split; discriminate. Qed.

(* NaN propagation.  If any of the four orientation calls returns         *)
(* `OrientRNan`, the intersection predicate returns `IntersectNan`.  One   *)
(* lemma per position; the proofs are mechanical case analysis on the     *)
(* remaining three orientation values, which only flow through the        *)
(* `orient_is_nan` reduction.                                              *)

Lemma b64_intersect_sign_filtered_nan_P0P1Q0 :
  forall P0 P1 Q0 Q1,
    b64_orient_sign_filtered P0 P1 Q0 = OrientRNan ->
    b64_intersect_sign_filtered P0 P1 Q0 Q1 = IntersectNan.
Proof.
  intros P0 P1 Q0 Q1 H.
  unfold b64_intersect_sign_filtered.
  rewrite H. reflexivity.
Qed.

Lemma b64_intersect_sign_filtered_nan_P0P1Q1 :
  forall P0 P1 Q0 Q1,
    b64_orient_sign_filtered P0 P1 Q1 = OrientRNan ->
    b64_intersect_sign_filtered P0 P1 Q0 Q1 = IntersectNan.
Proof.
  intros P0 P1 Q0 Q1 H.
  unfold b64_intersect_sign_filtered.
  rewrite H.
  destruct (b64_orient_sign_filtered P0 P1 Q0); reflexivity.
Qed.

Lemma b64_intersect_sign_filtered_nan_Q0Q1P0 :
  forall P0 P1 Q0 Q1,
    b64_orient_sign_filtered Q0 Q1 P0 = OrientRNan ->
    b64_intersect_sign_filtered P0 P1 Q0 Q1 = IntersectNan.
Proof.
  intros P0 P1 Q0 Q1 H.
  unfold b64_intersect_sign_filtered.
  rewrite H.
  destruct (b64_orient_sign_filtered P0 P1 Q0);
    destruct (b64_orient_sign_filtered P0 P1 Q1); reflexivity.
Qed.

Lemma b64_intersect_sign_filtered_nan_Q0Q1P1 :
  forall P0 P1 Q0 Q1,
    b64_orient_sign_filtered Q0 Q1 P1 = OrientRNan ->
    b64_intersect_sign_filtered P0 P1 Q0 Q1 = IntersectNan.
Proof.
  intros P0 P1 Q0 Q1 H.
  unfold b64_intersect_sign_filtered.
  rewrite H.
  destruct (b64_orient_sign_filtered P0 P1 Q0);
    destruct (b64_orient_sign_filtered P0 P1 Q1);
    destruct (b64_orient_sign_filtered Q0 Q1 P0); reflexivity.
Qed.

(* ============================================================================
   Bridge to the R-side `Point` type and `cross` predicate.

   `cross_R_BP` (from Orient_b64_sound.v) is the same polynomial in
   `B2R coord` values as `cross` (from Orientation.v) is in `px coord` /
   `py coord` values, so the two coincide after lifting each `BPoint`
   coord via `B2R`.  This is the bridge needed to compose
   `b64_orient_sign_filtered_sound_small_int` (which speaks in terms of
   `cross_R_BP`) with the R-side intersection rejection theorem (which
   speaks in terms of `cross` on `Point`s).
   ============================================================================ *)

Definition BP2P (p : BPoint) : Point :=
  mkPoint (Binary.B2R prec emax (bx p)) (Binary.B2R prec emax (by_ p)).

Lemma cross_R_BP_eq_cross_BP2P :
  forall P0 P1 Q : BPoint,
    cross_R_BP P0 P1 Q = cross (BP2P P0) (BP2P P1) (BP2P Q).
Proof.
  intros P0 P1 Q.
  unfold cross_R_BP, cross, BP2P, px, py.
  reflexivity.
Qed.

(* ============================================================================
   First soundness theorem (integer regime).

   When `b64_intersect_sign_filtered` returns `IntersectNone`, the
   underlying R-side segments don't share a point.  The proof composes:

     (a) `IntersectNone` ⇒ one of the two `orient_same_strict_side`
         booleans is `true` (the rejection trigger).
     (b) Each `b64_orient_sign_filtered` call is sound w.r.t. `cross_R_BP`
         in the integer regime (via `b64_orient_sign_filtered_sound_small_int`).
     (c) `same_strict_side pq0 pq1 = true` ⇒ either both
         `cross_R_BP P0 P1 Q0 > 0` and `cross_R_BP P0 P1 Q1 > 0`, or both
         `< 0` ⇒ `cross_R_BP P0 P1 Q0 * cross_R_BP P0 P1 Q1 > 0`.
     (d) `cross_R_BP = cross (BP2P ...)` by the bridge above.
     (e) `cross_AB_positive_implies_no_shared` (theories/Intersect.v)
         closes the goal.

   The symmetric case (`same_strict_side qp0 qp1 = true`) is analogous
   with `cross_CD_positive_implies_no_shared`.
   ============================================================================ *)

Theorem b64_intersect_sign_filtered_none_sound_small_int :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_inputs_int_safe P0 P1 Q0 Q1 ->
    b64_intersect_sign_filtered P0 P1 Q0 Q1 = IntersectNone ->
    ~ exists X : Point,
        between (BP2P P0) (BP2P P1) X /\
        between (BP2P Q0) (BP2P Q1) X.
Proof.
  intros P0 P1 Q0 Q1 Hsafe Hres.
  (* Apply orientation soundness to each of the four calls. *)
  pose proof (b64_orient_sign_filtered_sound_small_int _ _ _
                (intersect_inputs_int_safe_P0P1Q0 _ _ _ _ Hsafe)) as Hpq0.
  pose proof (b64_orient_sign_filtered_sound_small_int _ _ _
                (intersect_inputs_int_safe_P0P1Q1 _ _ _ _ Hsafe)) as Hpq1.
  pose proof (b64_orient_sign_filtered_sound_small_int _ _ _
                (intersect_inputs_int_safe_Q0Q1P0 _ _ _ _ Hsafe)) as Hqp0.
  pose proof (b64_orient_sign_filtered_sound_small_int _ _ _
                (intersect_inputs_int_safe_Q0Q1P1 _ _ _ _ Hsafe)) as Hqp1.
  (* Unpack `IntersectNone` -- it forces both NaN- and Uncertain-cascade  *)
  (* booleans false, both rejection booleans... and forces one of them    *)
  (* true.                                                                *)
  unfold b64_intersect_sign_filtered in Hres.
  destruct (b64_orient_sign_filtered P0 P1 Q0) eqn:Epq0;
    destruct (b64_orient_sign_filtered P0 P1 Q1) eqn:Epq1;
    destruct (b64_orient_sign_filtered Q0 Q1 P0) eqn:Eqp0;
    destruct (b64_orient_sign_filtered Q0 Q1 P1) eqn:Eqp1;
    cbn in Hres; try discriminate Hres;
    (* In each surviving case, the four orientation signs are concrete;   *)
    (* apply `cross_AB_positive_implies_no_shared` or its symmetric       *)
    (* counterpart depending on which rejection branch fired.  Hpq0..Hqp1 *)
    (* give us the cross_R_BP sign for each call.                          *)
    rewrite cross_R_BP_eq_cross_BP2P in Hpq0, Hpq1, Hqp0, Hqp1;
    (first
      [ apply cross_AB_positive_implies_no_shared; nra
      | apply cross_CD_positive_implies_no_shared; nra ]).
Qed.

(* ============================================================================
   IntersectPoint soundness in the integer regime.

   When the filter commits to `IntersectPoint`, all four orientation calls
   returned strict Pos / Neg with opposite signs in both pairs.  By the
   integer-regime orientation soundness, both cross-product products are
   strictly negative.  `strict_completeness` (theories/Intersect.v) then
   gives the existence of a shared interior point.
   ============================================================================ *)

Theorem b64_intersect_sign_filtered_point_sound_small_int :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_inputs_int_safe P0 P1 Q0 Q1 ->
    b64_intersect_sign_filtered P0 P1 Q0 Q1 = IntersectPoint ->
    exists X : Point,
      between (BP2P P0) (BP2P P1) X /\
      between (BP2P Q0) (BP2P Q1) X.
Proof.
  intros P0 P1 Q0 Q1 Hsafe Hres.
  pose proof (b64_orient_sign_filtered_sound_small_int _ _ _
                (intersect_inputs_int_safe_P0P1Q0 _ _ _ _ Hsafe)) as Hpq0.
  pose proof (b64_orient_sign_filtered_sound_small_int _ _ _
                (intersect_inputs_int_safe_P0P1Q1 _ _ _ _ Hsafe)) as Hpq1.
  pose proof (b64_orient_sign_filtered_sound_small_int _ _ _
                (intersect_inputs_int_safe_Q0Q1P0 _ _ _ _ Hsafe)) as Hqp0.
  pose proof (b64_orient_sign_filtered_sound_small_int _ _ _
                (intersect_inputs_int_safe_Q0Q1P1 _ _ _ _ Hsafe)) as Hqp1.
  unfold b64_intersect_sign_filtered in Hres.
  destruct (b64_orient_sign_filtered P0 P1 Q0) eqn:Epq0;
    destruct (b64_orient_sign_filtered P0 P1 Q1) eqn:Epq1;
    destruct (b64_orient_sign_filtered Q0 Q1 P0) eqn:Eqp0;
    destruct (b64_orient_sign_filtered Q0 Q1 P1) eqn:Eqp1;
    cbn in Hres; try discriminate Hres;
    rewrite cross_R_BP_eq_cross_BP2P in Hpq0, Hpq1, Hqp0, Hqp1;
    apply strict_completeness; nra.
Qed.

(* ============================================================================
   Intersection point computation.

   Cramer's rule on the parametric system gives the t-parameter on
   segment P0-P1 as `s = orient(Q0,Q1,P0) / (orient(Q0,Q1,P0) -
   orient(Q0,Q1,P1))`, then `X = P0 + s*(P1 - P0)`.  The denominator
   is exactly `b64_orient2d_terms`-style cross-product output, the
   numerator is one of its two terms.

   Implementation chooses the parameter on P0-P1 (matches NTS's
   `RobustLineIntersector` convention).  Returns `None` for any non-
   `IntersectPoint` result so callers can match the predicate's
   five-valued result against an `option BPoint` cleanly.

   Soundness story (deferred):
   - Integer-regime structural soundness: `b64_intersect_point` commits
     to `Some _` exactly when the predicate is `IntersectPoint`.  The
     denominator is a non-zero integer in this regime (Phase 0
     exactness), so `b64_compare den zero` returns `Lt`/`Gt`, not `Eq`
     or `None`.
   - Integer-regime forward error: the rounded `BPoint` is close to
     the true rational intersection -- bounded by the standard
     binary64 division + multiplication + addition error budget.
     Requires `b64_div`-flavoured forward-error analysis; comparable in
     scope to Phase 0 Stage D.  Not in this slice.
   - The C# differential tests in NetTopologySuite.Curve validate
     bit-equality between `RobustLineIntersector.IntersectionPoint`
     and the Coq-extracted reference (both round identically), which
     is the cross-port soundness check this slice ships.
   ============================================================================ *)

Definition b64_intersect_point (P0 P1 Q0 Q1 : BPoint) : option BPoint :=
  match b64_intersect_sign_filtered P0 P1 Q0 Q1 with
  | IntersectPoint =>
      let qp0 := b64_orient2d Q0 Q1 P0 in
      let qp1 := b64_orient2d Q0 Q1 P1 in
      let den := b64_minus qp0 qp1 in
      let zero := Binary.B754_zero prec emax false in
      match b64_compare den zero with
      | Some Eq => None
      | None    => None
      | _ =>
          let s  := b64_div qp0 den in
          let dx := b64_minus (bx P1) (bx P0) in
          let dy := b64_minus (by_ P1) (by_ P0) in
          Some (mkBP (b64_plus (bx P0) (b64_mult s dx))
                     (b64_plus (by_ P0) (b64_mult s dy)))
      end
  | _ => None
  end.

(* Structural lemma: the function commits to `Some _` exactly when the
   predicate is `IntersectPoint`.  Proof is straightforward unfold +
   destruct since `b64_intersect_point` is defined by case on the
   predicate's result; the only sub-case that needs care is showing
   `b64_compare den zero` does not return `Eq` or `None`.  That sub-case
   would need integer-regime exactness on `den` -- a one-step argument
   from Phase 0's `b64_orient2d_exact_for_small_int` and the predicate
   dispatch forcing opposite-sign cross_R values.  This slice ships the
   weaker structural lemma without the integer-regime side condition;
   the stronger version is the natural follow-up. *)

Lemma b64_intersect_point_none_unless_point :
  forall P0 P1 Q0 Q1 X,
    b64_intersect_point P0 P1 Q0 Q1 = Some X ->
    b64_intersect_sign_filtered P0 P1 Q0 Q1 = IntersectPoint.
Proof.
  intros P0 P1 Q0 Q1 X H.
  unfold b64_intersect_point in H.
  destruct (b64_intersect_sign_filtered P0 P1 Q0 Q1); try discriminate H.
  reflexivity.
Qed.

(* ============================================================================
   Headline: full match-on-five soundness in the integer regime.

   Bundles `_none_sound` and `_point_sound` into the canonical
   match-on-five form, dropping claims for `Collinear` / `Nan` /
   `Uncertain` (those branches make no positive claim by design).
   ============================================================================ *)

Theorem b64_intersect_sign_filtered_sound_small_int :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_inputs_int_safe P0 P1 Q0 Q1 ->
    match b64_intersect_sign_filtered P0 P1 Q0 Q1 with
    | IntersectNone =>
        ~ exists X, between (BP2P P0) (BP2P P1) X /\ between (BP2P Q0) (BP2P Q1) X
    | IntersectPoint =>
        exists X, between (BP2P P0) (BP2P P1) X /\ between (BP2P Q0) (BP2P Q1) X
    | IntersectCollinear => True
    | IntersectNan       => True
    | IntersectUncertain => True
    end.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  destruct (b64_intersect_sign_filtered P0 P1 Q0 Q1) eqn:Eres;
    try exact I.
  - apply (b64_intersect_sign_filtered_none_sound_small_int _ _ _ _ Hsafe Eres).
  - apply (b64_intersect_sign_filtered_point_sound_small_int _ _ _ _ Hsafe Eres).
Qed.

(* ============================================================================
   Collinear-overlap soundness (binary64 bridge).

   Companion to the R-side `collinear_overlap_completeness` in
   theories/Intersect.v: lifts to BPoint inputs.  Premises:

   * All four cross-products of input vertices are zero -- A, B, C, D are
     mutually collinear.
   * The 1D-overlap predicate holds (some endpoint of one segment is
     between the endpoints of the other).

   Conclusion: a shared point exists.

   This claim is layer-agnostic (pure R-arithmetic via `cross_R_BP`'s
   identity with `cross (BP2P _)`).  Integer-regime callers can derive
   the cross-zero premises from the orient soundness theorem when the
   four `b64_orient_sign_filtered` results are all `OrientRZero`; that
   composition is a one-liner left to consumers rather than baked into
   this slice.

   The other sub-cases of `IntersectCollinear` (T-junction, shared
   endpoint, collinear without overlap) still make no positive claim in
   the headline match-on-five soundness theorem -- they remain `True` by
   design until the algorithmic disambiguation is shipped separately.
   ============================================================================ *)

Theorem b64_collinear_overlap_share :
  forall P0 P1 Q0 Q1 : BPoint,
    cross_R_BP P0 P1 Q0 = 0 ->
    cross_R_BP P0 P1 Q1 = 0 ->
    cross_R_BP Q0 Q1 P0 = 0 ->
    cross_R_BP Q0 Q1 P1 = 0 ->
    segments_1d_overlap (BP2P P0) (BP2P P1) (BP2P Q0) (BP2P Q1) ->
    exists X : Point,
      between (BP2P P0) (BP2P P1) X /\
      between (BP2P Q0) (BP2P Q1) X.
Proof.
  intros P0 P1 Q0 Q1 H1 H2 H3 H4 Hov.
  rewrite cross_R_BP_eq_cross_BP2P in H1, H2, H3, H4.
  apply collinear_overlap_completeness; assumption.
Qed.

(* ============================================================================
   Full collinear biconditional (BPoint lift).

   Upgrades `b64_collinear_overlap_share` (forward only) to an iff by lifting
   the R-side `collinear_share_iff_1d_overlap` (theories/Intersect.v).  When
   the four input vertices are mutually collinear (all four cross-products
   zero), the two segments share a point IFF their 1D extents overlap.  The
   non-trivial converse (share => overlap) is the collinear-intersection
   characterisation closed on the R side; this is its layer-agnostic lift.

   Integer-regime callers obtain the four cross-zero premises from the
   orientation soundness theorem when all four `b64_orient_sign_filtered`
   results are `OrientRZero`.  (When only *some* are zero -- the general
   `IntersectCollinear` verdict -- see
   `b64_intersect_collinear_implies_some_collinear` below.)
   ============================================================================ *)

Theorem b64_collinear_share_iff_1d_overlap :
  forall P0 P1 Q0 Q1 : BPoint,
    cross_R_BP P0 P1 Q0 = 0 ->
    cross_R_BP P0 P1 Q1 = 0 ->
    cross_R_BP Q0 Q1 P0 = 0 ->
    cross_R_BP Q0 Q1 P1 = 0 ->
    ((exists X : Point,
        between (BP2P P0) (BP2P P1) X /\ between (BP2P Q0) (BP2P Q1) X)
     <-> segments_1d_overlap (BP2P P0) (BP2P P1) (BP2P Q0) (BP2P Q1)).
Proof.
  intros P0 P1 Q0 Q1 H1 H2 H3 H4.
  rewrite cross_R_BP_eq_cross_BP2P in H1, H2, H3, H4.
  apply collinear_share_iff_1d_overlap; assumption.
Qed.

(* ============================================================================
   What the `IntersectCollinear` verdict guarantees (integer regime).

   The dispatch returns `IntersectCollinear` exactly when -- after ruling out
   NaN, Uncertain, and same-strict-side rejection -- at least one of the four
   orientation tests is `Zero`.  In the integer regime an orientation `Zero`
   is exact, so it pins the corresponding cross-product to 0.  Hence the
   verdict implies that at least one endpoint lies on the other segment's
   supporting line.  This converts the headline soundness theorem's
   `IntersectCollinear => True` branch into a usable disjunction; the
   fully-collinear sub-case (all four zero) then feeds
   `b64_collinear_share_iff_1d_overlap`.
   ============================================================================ *)

Theorem b64_intersect_collinear_implies_some_collinear :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_inputs_int_safe P0 P1 Q0 Q1 ->
    b64_intersect_sign_filtered P0 P1 Q0 Q1 = IntersectCollinear ->
    cross_R_BP P0 P1 Q0 = 0 \/ cross_R_BP P0 P1 Q1 = 0 \/
    cross_R_BP Q0 Q1 P0 = 0 \/ cross_R_BP Q0 Q1 P1 = 0.
Proof.
  intros P0 P1 Q0 Q1 Hsafe Hres.
  pose proof (b64_orient_sign_filtered_sound_small_int _ _ _
                (intersect_inputs_int_safe_P0P1Q0 _ _ _ _ Hsafe)) as Hpq0.
  pose proof (b64_orient_sign_filtered_sound_small_int _ _ _
                (intersect_inputs_int_safe_P0P1Q1 _ _ _ _ Hsafe)) as Hpq1.
  pose proof (b64_orient_sign_filtered_sound_small_int _ _ _
                (intersect_inputs_int_safe_Q0Q1P0 _ _ _ _ Hsafe)) as Hqp0.
  pose proof (b64_orient_sign_filtered_sound_small_int _ _ _
                (intersect_inputs_int_safe_Q0Q1P1 _ _ _ _ Hsafe)) as Hqp1.
  unfold b64_intersect_sign_filtered in Hres.
  destruct (b64_orient_sign_filtered P0 P1 Q0) eqn:Epq0;
    destruct (b64_orient_sign_filtered P0 P1 Q1) eqn:Epq1;
    destruct (b64_orient_sign_filtered Q0 Q1 P0) eqn:Eqp0;
    destruct (b64_orient_sign_filtered Q0 Q1 P1) eqn:Eqp1;
    cbn in Hres, Hpq0, Hpq1, Hqp0, Hqp1;
    try discriminate Hres;
    first [ left; exact Hpq0
          | right; left; exact Hpq1
          | right; right; left; exact Hqp0
          | right; right; right; exact Hqp1 ].
Qed.

(* ============================================================================
   Shared-endpoint disambiguation.

   When two segments share an endpoint, the intersection predicate
   classifies as `IntersectCollinear` (because the corresponding orient
   tests return Zero), but the predicate alone doesn't distinguish this
   sub-case from a T-junction or full collinear overlap.  The functions
   below detect the shared-endpoint configuration by direct bit-equality
   on the four pairs of endpoint coordinates -- callers can use this to
   recover a concrete shared-point witness without further computation.

   Bit-equality is decided by Flocq's `Bcompare`: returns `Some Eq` iff
   both operands are finite and `B2R x = B2R y` (NaN inputs give `None`).
   The witness function tries the four pairings and returns the
   coinciding endpoint as the shared point.
   ============================================================================ *)

Definition b64_bpoint_eq (p q : BPoint) : bool :=
  match b64_compare (bx p) (bx q), b64_compare (by_ p) (by_ q) with
  | Some Eq, Some Eq => true
  | _, _             => false
  end.

Definition b64_shared_endpoint_witness
    (P0 P1 Q0 Q1 : BPoint) : option BPoint :=
  if b64_bpoint_eq P0 Q0 then Some P0
  else if b64_bpoint_eq P0 Q1 then Some P0
  else if b64_bpoint_eq P1 Q0 then Some P1
  else if b64_bpoint_eq P1 Q1 then Some P1
  else None.

(* The key bridge: bit-equal finite binary64 values lift to equal R         *)
(* coordinates via `Bcompare_correct`.  Combined with the BP2P record       *)
(* equality, two BPoints with all four coords bit-equal lift to equal       *)
(* Points.                                                                   *)
Lemma b64_bpoint_eq_imp_BP2P_eq :
  forall p q : BPoint,
    Binary.is_finite prec emax (bx p)  = true ->
    Binary.is_finite prec emax (by_ p) = true ->
    Binary.is_finite prec emax (bx q)  = true ->
    Binary.is_finite prec emax (by_ q) = true ->
    b64_bpoint_eq p q = true ->
    BP2P p = BP2P q.
Proof.
  intros p q Fxp Fyp Fxq Fyq Heq.
  unfold b64_bpoint_eq in Heq.
  unfold b64_compare in Heq.
  rewrite (Binary.Bcompare_correct prec emax _ _ Fxp Fxq) in Heq.
  rewrite (Binary.Bcompare_correct prec emax _ _ Fyp Fyq) in Heq.
  destruct (Rcompare (Binary.B2R prec emax (bx p))
                     (Binary.B2R prec emax (bx q))) eqn:Excmp;
    try discriminate.
  destruct (Rcompare (Binary.B2R prec emax (by_ p))
                     (Binary.B2R prec emax (by_ q))) eqn:Eycmp;
    try discriminate.
  apply Rcompare_Eq_inv in Excmp.
  apply Rcompare_Eq_inv in Eycmp.
  unfold BP2P. rewrite Excmp, Eycmp. reflexivity.
Qed.

(* Soundness: when the witness function commits, the witness lies on both *)
(* segments.  Requires all eight input coordinates to be finite.  The     *)
(* proof composes `b64_bpoint_eq_imp_BP2P_eq` with the R-side             *)
(* `shared_endpoint_share_point`.                                         *)

Theorem b64_shared_endpoint_witness_sound :
  forall P0 P1 Q0 Q1 X : BPoint,
    Binary.is_finite prec emax (bx P0)  = true ->
    Binary.is_finite prec emax (by_ P0) = true ->
    Binary.is_finite prec emax (bx P1)  = true ->
    Binary.is_finite prec emax (by_ P1) = true ->
    Binary.is_finite prec emax (bx Q0)  = true ->
    Binary.is_finite prec emax (by_ Q0) = true ->
    Binary.is_finite prec emax (bx Q1)  = true ->
    Binary.is_finite prec emax (by_ Q1) = true ->
    b64_shared_endpoint_witness P0 P1 Q0 Q1 = Some X ->
    between (BP2P P0) (BP2P P1) (BP2P X) /\
    between (BP2P Q0) (BP2P Q1) (BP2P X).
Proof.
  intros P0 P1 Q0 Q1 X FxP0 FyP0 FxP1 FyP1 FxQ0 FyQ0 FxQ1 FyQ1 Hres.
  unfold b64_shared_endpoint_witness in Hres.
  destruct (b64_bpoint_eq P0 Q0) eqn:E00.
  { inversion Hres; subst.
    pose proof (b64_bpoint_eq_imp_BP2P_eq _ _ FxP0 FyP0 FxQ0 FyQ0 E00) as HE.
    split; [apply between_P0 | rewrite <- HE; apply between_P0]. }
  destruct (b64_bpoint_eq P0 Q1) eqn:E01.
  { inversion Hres; subst.
    pose proof (b64_bpoint_eq_imp_BP2P_eq _ _ FxP0 FyP0 FxQ1 FyQ1 E01) as HE.
    split; [apply between_P0 | rewrite <- HE; apply between_P1]. }
  destruct (b64_bpoint_eq P1 Q0) eqn:E10.
  { inversion Hres; subst.
    pose proof (b64_bpoint_eq_imp_BP2P_eq _ _ FxP1 FyP1 FxQ0 FyQ0 E10) as HE.
    split; [apply between_P1 | rewrite <- HE; apply between_P0]. }
  destruct (b64_bpoint_eq P1 Q1) eqn:E11.
  { inversion Hres; subst.
    pose proof (b64_bpoint_eq_imp_BP2P_eq _ _ FxP1 FyP1 FxQ1 FyQ1 E11) as HE.
    split; [apply between_P1 | rewrite <- HE; apply between_P1]. }
  discriminate Hres.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                              *)
(* -------------------------------------------------------------------------- *)

Print Assumptions intersect_sign_eq_dec.
Print Assumptions b64_intersect_sign_filtered_total.
Print Assumptions intersect_sign_distinct.
Print Assumptions b64_intersect_sign_filtered_nan_P0P1Q0.
Print Assumptions b64_intersect_sign_filtered_nan_P0P1Q1.
Print Assumptions b64_intersect_sign_filtered_nan_Q0Q1P0.
Print Assumptions b64_intersect_sign_filtered_nan_Q0Q1P1.
Print Assumptions intersect_inputs_int_safe_P0P1Q0.
Print Assumptions intersect_inputs_int_safe_P0P1Q1.
Print Assumptions intersect_inputs_int_safe_Q0Q1P0.
Print Assumptions intersect_inputs_int_safe_Q0Q1P1.
Print Assumptions cross_R_BP_eq_cross_BP2P.
Print Assumptions b64_intersect_sign_filtered_none_sound_small_int.
Print Assumptions b64_intersect_sign_filtered_point_sound_small_int.
Print Assumptions b64_intersect_sign_filtered_sound_small_int.
Print Assumptions b64_intersect_point_none_unless_point.
Print Assumptions b64_collinear_overlap_share.
Print Assumptions b64_collinear_share_iff_1d_overlap.
Print Assumptions b64_intersect_collinear_implies_some_collinear.
Print Assumptions b64_bpoint_eq_imp_BP2P_eq.
Print Assumptions b64_shared_endpoint_witness_sound.
