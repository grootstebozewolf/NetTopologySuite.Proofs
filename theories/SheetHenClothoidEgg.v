(* ============================================================================
   NetTopologySuite.Proofs.SheetHenClothoidEgg
   ----------------------------------------------------------------------------
   Closed-form small-angle clothoid (cos θ≈1, sin θ≈θ). Not Fresnel.
   Not chord-parameter. Linear κ, quadratic heading:
     θ(s) = θ0 + k0·s + (k1-k0)·s²/(2L)
     γ(t) = p0 + (tL, ∫₀^{tL} θ)
          = p0 + (tL, θ0·tL + k0·(tL)²/2 + (k1-k0)·(tL)³/(6L))
   θ0 is the small-angle heading (y += θ0·s), not a rotated (cos,sin) frame.
   mk_cloth sets p1 := γ(1). cloth_split rebuilds both children via mk_cloth
   (does not copy a stored p1). Intake bag vertices are γ(0), γ(1).
   claimId: 0007-clothoid-first-cook / 0007-intake-mkclothoid
   WITNESS topic: overlay · board: ADR-0007 · 3-axiom.
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance.
Local Open Scope R_scope.

Record ClothoidEgg : Type := mkClothoidEgg {
  cloth_p0 : Point;
  cloth_p1 : Point;
  cloth_k0 : R;
  cloth_k1 : R;
  cloth_L : R;
  cloth_th0 : R
}.

Definition cloth_k_at (c : ClothoidEgg) (t : R) : R :=
  cloth_k0 c + t * (cloth_k1 c - cloth_k0 c).

Definition cloth_th (c : ClothoidEgg) (t : R) : R :=
  cloth_th0 c
  + cloth_L c *
    (cloth_k0 c * t + (cloth_k1 c - cloth_k0 c) * (t * t) * / 2).

Definition cloth_y_off_seed (k0 k1 L th0 t : R) : R :=
  th0 * (t * L)
  + (k0 * (L * L) * / 2) * (t * t)
  + ((k1 - k0) * (L * L) * / 6) * (t * t * t).

Definition cloth_eval_seed (p0 : Point) (k0 k1 L th0 t : R) : Point :=
  mkPoint (px p0 + t * L) (py p0 + cloth_y_off_seed k0 k1 L th0 t).

Definition cloth_y_off (c : ClothoidEgg) (t : R) : R :=
  cloth_y_off_seed (cloth_k0 c) (cloth_k1 c) (cloth_L c) (cloth_th0 c) t.

Definition cloth_eval (c : ClothoidEgg) (t : R) : Point :=
  cloth_eval_seed (cloth_p0 c) (cloth_k0 c) (cloth_k1 c)
    (cloth_L c) (cloth_th0 c) t.

(* Generator: p1 is γ(1), never a stale chord-seed. *)
Definition mk_cloth (p0 : Point) (k0 k1 L th0 : R) : ClothoidEgg :=
  mkClothoidEgg p0 (cloth_eval_seed p0 k0 k1 L th0 1) k0 k1 L th0.

Definition locked_clothoid_egg : ClothoidEgg :=
  mk_cloth (mkPoint 0 0) 0 (5 / 1000) 80 0.

Definition on_cloth (c : ClothoidEgg) (t : R) (p : Point) : Prop :=
  0 <= t <= 1 /\ p = cloth_eval c t.

Definition cloth_split (c : ClothoidEgg) (t : R) : ClothoidEgg * ClothoidEgg :=
  let mid := cloth_eval c t in
  (mk_cloth (cloth_p0 c) (cloth_k0 c) (cloth_k_at c t)
     (t * cloth_L c) (cloth_th0 c),
   mk_cloth mid (cloth_k_at c t) (cloth_k1 c)
     ((1 - t) * cloth_L c) (cloth_th c t)).

Definition bent_eval_probe : ClothoidEgg :=
  mk_cloth (mkPoint 0 0) 0 3 2 0.

Definition straight_k0k1_zero (c : ClothoidEgg) : ClothoidEgg :=
  mk_cloth (cloth_p0 c) 0 0 (cloth_L c) (cloth_th0 c).

Lemma cloth_eval_at_0 :
  forall c, cloth_eval c 0 = cloth_p0 c.
Proof.
  intros [p0 p1 k0 k1 L th0].
  destruct p0 as [x y].
  unfold cloth_eval, cloth_eval_seed, cloth_y_off_seed.
  cbn [px py cloth_p0 cloth_k0 cloth_k1 cloth_L cloth_th0].
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma cloth_eval_at_1_mk :
  forall p0 k0 k1 L th0,
    cloth_p1 (mk_cloth p0 k0 k1 L th0)
      = cloth_eval (mk_cloth p0 k0 k1 L th0) 1.
Proof.
  intros. reflexivity.
Qed.

Lemma locked_clothoid_egg_p1_is_gamma1 :
  cloth_p1 locked_clothoid_egg = cloth_eval locked_clothoid_egg 1.
Proof.
  unfold locked_clothoid_egg. apply cloth_eval_at_1_mk.
Qed.

Lemma cloth_eval_bent_neq_k0k1_zero :
  cloth_eval bent_eval_probe (1 / 2)
    <> cloth_eval (straight_k0k1_zero bent_eval_probe) (1 / 2).
Proof.
  intros H.
  apply (f_equal py) in H.
  unfold cloth_eval, cloth_eval_seed, cloth_y_off_seed,
         straight_k0k1_zero, bent_eval_probe, mk_cloth in H.
  cbn [px py cloth_p0 cloth_k0 cloth_k1 cloth_L cloth_th0] in H.
  lra.
Qed.

Lemma cloth_y_concat_right_alg :
  forall th0 k0 k1 L t u,
    let T := t + (1 - t) * u in
    let yp s :=
      th0 * (s * L)
      + (k0 * (L * L) * / 2) * (s * s)
      + ((k1 - k0) * (L * L) * / 6) * (s * s * s) in
    yp t
    + (th0 + L * (k0 * t + (k1 - k0) * (t * t) * / 2))
      * (u * ((1 - t) * L))
    + ((k0 + t * (k1 - k0)) * (((1 - t) * L) * ((1 - t) * L)) * / 2)
      * (u * u)
    + ((k1 - (k0 + t * (k1 - k0)))
       * (((1 - t) * L) * ((1 - t) * L)) * / 6)
      * (u * u * u)
    = yp T.
Proof.
  intros th0 k0 k1 L t u.
  unfold Rdiv.
  field.
Qed.

Lemma cloth_split_eval_left :
  forall c t u,
    cloth_eval (fst (cloth_split c t)) u = cloth_eval c (t * u).
Proof.
  intros c t u.
  unfold cloth_eval, cloth_eval_seed, cloth_y_off_seed,
         cloth_split, cloth_k_at, mk_cloth.
  cbn [fst px py cloth_p0 cloth_k0 cloth_k1 cloth_L cloth_th0].
  apply (f_equal2 mkPoint); field.
Qed.

Lemma cloth_split_eval_right :
  forall c t u,
    cloth_eval (snd (cloth_split c t)) u = cloth_eval c (t + (1 - t) * u).
Proof.
  intros c t u.
  destruct c as [p0 p1 k0 k1 L th0].
  unfold cloth_split, mk_cloth, cloth_k_at, cloth_th, cloth_eval.
  cbn [snd px py cloth_p0 cloth_p1 cloth_k0 cloth_k1 cloth_L cloth_th0].
  apply (f_equal2 mkPoint).
  - replace (px (cloth_eval_seed p0 k0 k1 L th0 t))
      with (px p0 + t * L)
      by (unfold cloth_eval_seed; cbn [px]; ring).
    ring.
  - replace (py (cloth_eval_seed p0 k0 k1 L th0 t))
      with (py p0 + cloth_y_off_seed k0 k1 L th0 t)
      by (unfold cloth_eval_seed; cbn [py]; ring).
    unfold cloth_y_off_seed.
    transitivity
      (py p0 +
       (th0 * (t * L)
        + (k0 * (L * L) * / 2) * (t * t)
        + ((k1 - k0) * (L * L) * / 6) * (t * t * t)
        + (th0 + L * (k0 * t + (k1 - k0) * (t * t) * / 2))
          * (u * ((1 - t) * L))
        + ((k0 + t * (k1 - k0)) * (((1 - t) * L) * ((1 - t) * L)) * / 2)
          * (u * u)
        + ((k1 - (k0 + t * (k1 - k0)))
           * (((1 - t) * L) * ((1 - t) * L)) * / 6)
          * (u * u * u))).
    { field. }
    rewrite cloth_y_concat_right_alg.
    field.
Qed.

Lemma cloth_split_left_p1_is_gamma1 :
  forall c t,
    cloth_p1 (fst (cloth_split c t))
      = cloth_eval (fst (cloth_split c t)) 1.
Proof.
  intros c t. unfold cloth_split. cbn [fst]. apply cloth_eval_at_1_mk.
Qed.

Lemma cloth_split_right_p1_is_gamma1 :
  forall c t,
    cloth_p1 (snd (cloth_split c t))
      = cloth_eval (snd (cloth_split c t)) 1.
Proof.
  intros c t. unfold cloth_split. cbn [snd]. apply cloth_eval_at_1_mk.
Qed.
