(* ============================================================================
   NetTopologySuite.Proofs.ArcLength
   ----------------------------------------------------------------------------
   Option-A arc primitives, foundation 3/N (issue #64 ask #1): exact arc length
   s = r * theta, with the chord/arc soundness relations a curve-aware buffer
   and linearisation rely on (M-LEN-CS / M-LEN-CC).

     arc_length r theta      := r * theta               (* the r*theta law   *)
     chord_subtended r theta := 2 * r * sin (theta / 2)  (* its chord         *)

   Headlines:
     chord_le_arc_length : 0<=r -> 0<=theta ->
         chord_subtended r theta <= arc_length r theta
       (the chord never exceeds the arc it subtends -- the arc analogue of
        Linearise.v's chord_le_detour; underpins curve length monotonicity).
     chord_subtended_sq  : (chord_subtended r theta)^2 = 2*r^2*(1 - cos theta)
       (half-angle bridge to the cosine/dot-product world: 1 - cos theta
        = 2 sin^2(theta/2); with theta the central angle from AngleBetween,
        cos theta = dot/(r*r), giving the exact rational chord^2 = 2*(r*r - dot)).

   Pure Stdlib trig (no atan2 here), but `chord_le_arc_length` uses Stdlib's
   `sin_lt_x`, which pulls `Classical_Prop.classic`; so this file is 4-axiom
   (see docs/audit-exceptions.txt).  No Admitted.  Refs #64.
   ========================================================================== *)

Require Import Reals.
Require Import Lra.
Local Open Scope R_scope.

Definition arc_length (r theta : R) : R := r * theta.
Definition chord_subtended (r theta : R) : R := 2 * r * sin (theta / 2).

(* sin x <= x for x >= 0 (= at 0, strict above via Stdlib sin_lt_x). *)
Lemma sin_le_x : forall x : R, 0 <= x -> sin x <= x.
Proof.
  intros x Hx. destruct (Req_dec x 0) as [E|E].
  - subst; rewrite sin_0; lra.
  - apply Rlt_le, sin_lt_x; lra.
Qed.

Lemma arc_length_nonneg : forall r theta : R,
  0 <= r -> 0 <= theta -> 0 <= arc_length r theta.
Proof. intros r theta Hr Ht. unfold arc_length. nra. Qed.

(* Sanity: a full turn has arc length = circumference. *)
Lemma arc_length_full_turn : forall r : R, arc_length r (2 * PI) = 2 * PI * r.
Proof. intros r. unfold arc_length. ring. Qed.

(* Headline 1: the chord never exceeds the arc it subtends. *)
Theorem chord_le_arc_length : forall r theta : R,
  0 <= r -> 0 <= theta -> chord_subtended r theta <= arc_length r theta.
Proof.
  intros r theta Hr Ht. unfold chord_subtended, arc_length.
  assert (Hs : sin (theta / 2) <= theta / 2) by (apply sin_le_x; lra).
  nra.
Qed.

(* Headline 2: half-angle bridge to 1 - cos theta (hence to dot products). *)
Theorem chord_subtended_sq : forall r theta : R,
  chord_subtended r theta * chord_subtended r theta
    = 2 * (r * r) * (1 - cos theta).
Proof.
  intros r theta. unfold chord_subtended.
  assert (Hc : cos theta = 1 - 2 * sin (theta / 2) * sin (theta / 2)).
  { replace theta with (2 * (theta / 2)) at 1 by lra. apply cos_2a_sin. }
  rewrite Hc. ring.
Qed.

Print Assumptions chord_le_arc_length.
Print Assumptions chord_subtended_sq.
