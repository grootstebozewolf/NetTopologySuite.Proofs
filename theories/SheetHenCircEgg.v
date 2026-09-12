(* ============================================================================
   NetTopologySuite.Proofs.SheetHenCircEgg
   ----------------------------------------------------------------------------
   CircularEgg payload for host MkCirc (claimId 0007-gamma-mkcirc).
   γ(t) = O + r·(cos(θ₀ + t·Δθ), sin(θ₀ + t·Δθ)). Angles are egg data.
   Endpoints are derived: circ_start := γ(0), circ_end := γ(1).
   circ_eval is total: r=0 collapses to O; Δθ=0 is constant at θ0;
   |Δθ|=2π has γ(0)=γ(1); Δθ<0 is clockwise; split at 0 or 1
   yields a zero-sweep child. on_circ is the parameterized arc.
   Host circ_split reparametrizes the parent; sidecar CircLeftover
   split (CircularCookSplit.circ_split_left_reparam) is different.
   Not sidecar CircEgg. 3-axiom. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import Distance.
Local Open Scope R_scope.

Record CircularEgg : Type := mkCircularEgg {
  circ_o : Point;
  circ_r : R;
  circ_theta0 : R;
  circ_sweep : R
}.

Definition circ_eval (c : CircularEgg) (t : R) : Point :=
  mkPoint (px (circ_o c) + circ_r c * cos (circ_theta0 c + t * circ_sweep c))
          (py (circ_o c) + circ_r c * sin (circ_theta0 c + t * circ_sweep c)).

Definition circ_start (c : CircularEgg) : Point := circ_eval c 0.
Definition circ_end (c : CircularEgg) : Point := circ_eval c 1.

Definition on_circ (c : CircularEgg) (t : R) (p : Point) : Prop :=
  0 <= t <= 1 /\ p = circ_eval c t.

Definition circ_split (c : CircularEgg) (t : R) : CircularEgg * CircularEgg :=
  (mkCircularEgg (circ_o c) (circ_r c) (circ_theta0 c) (t * circ_sweep c),
   mkCircularEgg (circ_o c) (circ_r c)
     (circ_theta0 c + t * circ_sweep c) ((1 - t) * circ_sweep c)).

Lemma circ_eval_at_0 : forall c, circ_eval c 0 = circ_start c.
Proof. reflexivity. Qed.

Lemma circ_eval_at_1 : forall c, circ_eval c 1 = circ_end c.
Proof. reflexivity. Qed.

Lemma circ_split_eval_left :
  forall c t u,
    circ_eval (fst (circ_split c t)) u = circ_eval c (t * u).
Proof.
  intros c t u.
  unfold circ_eval, circ_split.
  cbn [fst circ_o circ_r circ_theta0 circ_sweep].
  replace (circ_theta0 c + u * (t * circ_sweep c))
    with (circ_theta0 c + (t * u) * circ_sweep c) by ring.
  reflexivity.
Qed.

Lemma circ_split_eval_right :
  forall c t u,
    circ_eval (snd (circ_split c t)) u =
    circ_eval c (t + (1 - t) * u).
Proof.
  intros c t u.
  unfold circ_eval, circ_split.
  cbn [snd circ_o circ_r circ_theta0 circ_sweep].
  replace (circ_theta0 c + t * circ_sweep c + u * ((1 - t) * circ_sweep c))
    with (circ_theta0 c + (t + (1 - t) * u) * circ_sweep c) by ring.
  reflexivity.
Qed.

Lemma circ_split_join :
  forall c t,
    circ_eval (fst (circ_split c t)) 1 = circ_eval c t /\
    circ_eval (snd (circ_split c t)) 0 = circ_eval c t.
Proof.
  intros c t.
  rewrite circ_split_eval_left, circ_split_eval_right.
  split; apply f_equal; ring.
Qed.

Lemma circ_split_ends :
  forall c t,
    circ_eval (fst (circ_split c t)) 0 = circ_eval c 0 /\
    circ_eval (snd (circ_split c t)) 1 = circ_eval c 1.
Proof.
  intros c t.
  rewrite circ_split_eval_left, circ_split_eval_right.
  split; apply f_equal; ring.
Qed.

Lemma circ_split_children :
  forall c t,
    circ_o (fst (circ_split c t)) = circ_o c /\
    circ_o (snd (circ_split c t)) = circ_o c /\
    circ_r (fst (circ_split c t)) = circ_r c /\
    circ_r (snd (circ_split c t)) = circ_r c /\
    circ_theta0 (fst (circ_split c t)) = circ_theta0 c /\
    circ_theta0 (snd (circ_split c t)) =
      circ_theta0 c + t * circ_sweep c /\
    circ_sweep (fst (circ_split c t)) = t * circ_sweep c /\
    circ_sweep (snd (circ_split c t)) = (1 - t) * circ_sweep c.
Proof.
  intros c t. unfold circ_split. cbn. repeat split; reflexivity.
Qed.

Print Assumptions circ_eval_at_0.
Print Assumptions circ_eval_at_1.
Print Assumptions circ_split_eval_left.
Print Assumptions circ_split_eval_right.
Print Assumptions circ_split_join.
Print Assumptions circ_split_ends.
Print Assumptions circ_split_children.
