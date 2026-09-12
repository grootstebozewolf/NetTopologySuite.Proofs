(* ============================================================================
   NetTopologySuite.Proofs.SheetHenClothoidEgg
   ----------------------------------------------------------------------------
   Interpolant (spec): linear κ, quadratic heading, closed-form γ.
     θ(s) = θ0 + k0·s + (k1-k0)·s²/(2L)
     γ(t) = p0 + (tL, ∫₀^{tL} θ)   (* x=s, y=∫θ *)
          = p0 + (tL, θ0·tL + k0·(tL)²/2 + (k1-k0)·(tL)³/(6L))
   cloth_split: mid=γ(t), κ linear, θ0_right=θ(t). Children concat to γ.
   Bent probe (k0,k1)=(0,3), L=2: γ(1/2)=(1,1/4) ≠ straight (1,0).
   Crossing fixture lives in ClothoidCookMkClothoid.v.
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

Definition locked_clothoid_egg : ClothoidEgg :=
  mkClothoidEgg (mkPoint 0 0) (mkPoint 1 0) 0 (5 / 1000) 80 0.

Definition cloth_k_at (c : ClothoidEgg) (t : R) : R :=
  cloth_k0 c + t * (cloth_k1 c - cloth_k0 c).

Definition cloth_th (c : ClothoidEgg) (t : R) : R :=
  cloth_th0 c
  + cloth_L c *
    (cloth_k0 c * t + (cloth_k1 c - cloth_k0 c) * (t * t) * / 2).

Definition cloth_y_off (c : ClothoidEgg) (t : R) : R :=
  cloth_th0 c * (t * cloth_L c)
  + (cloth_k0 c * (cloth_L c * cloth_L c) * / 2) * (t * t)
  + ((cloth_k1 c - cloth_k0 c) * (cloth_L c * cloth_L c) * / 6)
    * (t * t * t).

Definition cloth_eval (c : ClothoidEgg) (t : R) : Point :=
  mkPoint (px (cloth_p0 c) + t * cloth_L c)
          (py (cloth_p0 c) + cloth_y_off c t).

Definition on_cloth (c : ClothoidEgg) (t : R) (p : Point) : Prop :=
  0 <= t <= 1 /\ p = cloth_eval c t.

Definition cloth_split (c : ClothoidEgg) (t : R) : ClothoidEgg * ClothoidEgg :=
  let mid := cloth_eval c t in
  (mkClothoidEgg (cloth_p0 c) mid (cloth_k0 c) (cloth_k_at c t)
     (t * cloth_L c) (cloth_th0 c),
   mkClothoidEgg mid (cloth_p1 c) (cloth_k_at c t) (cloth_k1 c)
     ((1 - t) * cloth_L c) (cloth_th c t)).

(* Bent fixture: (k0,k1)=(0,3) versus the same egg with (k0,k1)=(0,0). *)
Definition bent_eval_probe : ClothoidEgg :=
  mkClothoidEgg (mkPoint 0 0) (mkPoint 2 0) 0 3 2 0.

Definition straight_k0k1_zero (c : ClothoidEgg) : ClothoidEgg :=
  mkClothoidEgg (cloth_p0 c) (cloth_p1 c) 0 0 (cloth_L c) (cloth_th0 c).

Lemma cloth_eval_bent_neq_k0k1_zero :
  cloth_eval bent_eval_probe (1 / 2)
    <> cloth_eval (straight_k0k1_zero bent_eval_probe) (1 / 2).
Proof.
  intros H.
  apply (f_equal py) in H.
  unfold cloth_eval, cloth_y_off, straight_k0k1_zero, bent_eval_probe in H.
  cbn [px py cloth_p0 cloth_p1 cloth_k0 cloth_k1 cloth_L cloth_th0] in H.
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
  unfold cloth_eval, cloth_y_off, cloth_split, cloth_k_at.
  cbn [fst px py cloth_p0 cloth_k0 cloth_k1 cloth_L cloth_th0].
  apply (f_equal2 mkPoint); field.
Qed.

Lemma cloth_split_eval_right :
  forall c t u,
    cloth_eval (snd (cloth_split c t)) u = cloth_eval c (t + (1 - t) * u).
Proof.
  intros c t u.
  destruct c as [p0 p1 k0 k1 L th0].
  unfold cloth_eval, cloth_y_off, cloth_th, cloth_split, cloth_k_at.
  cbn [snd px py cloth_p0 cloth_p1 cloth_k0 cloth_k1 cloth_L cloth_th0].
  apply (f_equal2 mkPoint).
  - replace (px (cloth_eval
      {| cloth_p0 := p0; cloth_p1 := p1; cloth_k0 := k0;
         cloth_k1 := k1; cloth_L := L; cloth_th0 := th0 |} t))
      with (px p0 + t * L)
      by (unfold cloth_eval; cbn [px cloth_p0 cloth_L]; ring).
    ring.
  - replace (py (cloth_eval
      {| cloth_p0 := p0; cloth_p1 := p1; cloth_k0 := k0;
         cloth_k1 := k1; cloth_L := L; cloth_th0 := th0 |} t))
      with (py p0 + cloth_y_off
        {| cloth_p0 := p0; cloth_p1 := p1; cloth_k0 := k0;
           cloth_k1 := k1; cloth_L := L; cloth_th0 := th0 |} t)
      by (unfold cloth_eval; cbn [py cloth_p0]; ring).
    unfold cloth_y_off, cloth_th.
    cbn [cloth_k0 cloth_k1 cloth_L cloth_th0].
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
