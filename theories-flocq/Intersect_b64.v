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
  unfold orient2d_inputs_int_safe; repeat split; assumption.
Qed.

Lemma intersect_inputs_int_safe_P0P1Q1 :
  forall P0 P1 Q0 Q1,
    intersect_inputs_int_safe P0 P1 Q0 Q1 ->
    orient2d_inputs_int_safe P0 P1 Q1.
Proof.
  intros P0 P1 Q0 Q1
    (HxP0 & HyP0 & HxP1 & HyP1 & _ & _ & HxQ1 & HyQ1).
  unfold orient2d_inputs_int_safe; repeat split; assumption.
Qed.

Lemma intersect_inputs_int_safe_Q0Q1P0 :
  forall P0 P1 Q0 Q1,
    intersect_inputs_int_safe P0 P1 Q0 Q1 ->
    orient2d_inputs_int_safe Q0 Q1 P0.
Proof.
  intros P0 P1 Q0 Q1
    (HxP0 & HyP0 & _ & _ & HxQ0 & HyQ0 & HxQ1 & HyQ1).
  unfold orient2d_inputs_int_safe; repeat split; assumption.
Qed.

Lemma intersect_inputs_int_safe_Q0Q1P1 :
  forall P0 P1 Q0 Q1,
    intersect_inputs_int_safe P0 P1 Q0 Q1 ->
    orient2d_inputs_int_safe Q0 Q1 P1.
Proof.
  intros P0 P1 Q0 Q1
    (_ & _ & HxP1 & HyP1 & HxQ0 & HyQ0 & HxQ1 & HyQ1).
  unfold orient2d_inputs_int_safe; repeat split; assumption.
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
