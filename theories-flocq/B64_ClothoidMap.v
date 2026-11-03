(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_ClothoidMap
   ----------------------------------------------------------------------------
   S8: the general clothoid integrals mapped onto the canonical Fresnel
   problem of S7, as a separate layer with separate budget lines
   (claimId: s8-b64-clothoid-map, witness: b64_clothoid_Icos_err).

   Mathematics.  cloth_psi c u = sigma u^2 / (2 A^2), so with w = sqrt 2 A
     cloth_Icos c s = w * F_C (s / w),      cloth_Isin c s = sigma * w * F_S (s / w)
   where F_C y = cloth_Icos c (w y) / w and F_S y = sigma cloth_Isin c (w y) / w
   are primitives of cos(y^2) / sin(y^2) vanishing at 0 (cm_FC_deriv,
   cm_FS_deriv) -- exactly the F that B64_Fresnel's theorems take, so no
   uniqueness-of-primitive argument is needed.

   Evaluation (RNE binary64, extractable):
     w^ = fl(fl(sqrt 2) * A),  x^ = fl(s / w^),
     Icos^ = fl(w^ * b64_fresnel_C x^),  Isin^ = +-fl(w^ * b64_fresnel_S x^).
   Intake cm_accept: 2^-500 <= A <= 2^500, |s| <= 2^500, and the S7 intake
   on the COMPUTED argument, fresnel_accept_b x^ (|x^| <= 5/2).

   Budget lines (u = 2^-53), each a lemma:
     E_sqrt    cm_sqrt2_err    |fl(sqrt 2) - sqrt 2| <= u
     E_param   cm_w_alg        |w^ - sqrt 2 A| <= 5/2 u A   (with E_sqrt)
     E_arg     cm_x_alg        |x^ - s / (sqrt 2 A)| <= 7 u
     E_eval    b64_fresnel_*_err (S7, 2^-42) + cm_prim_lip (|F'| <= 1)
     E_out     cm_out_alg      final product and the w^ error
   total: |Icos^ - cloth_Icos c s|, |Isin^ - cloth_Isin c s| <= A / 2^41.
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia ZArith.
From Stdlib Require Import Ranalysis1.
From Flocq Require Import Core IEEE754.Binary IEEE754.BinarySingleNaN.
From NTS.Proofs Require Import RealMonotone LipInt SheetHenClothoidCore ClothoidTangent
  FresnelSeries.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
  B64_AbsErr B64_Horner B64_SinPoly B64_Sin B64_FresnelPoly B64_Fresnel.
Local Open Scope R_scope.

Local Notation B2R := (Binary.B2R prec emax).
Local Notation fin := (Binary.is_finite prec emax).

(* -------------------------------------------------------------------------- *)
(* §1  The canonical primitives of a clothoid.                                *)
(* -------------------------------------------------------------------------- *)

Definition cm_W (c : ClothoidEgg) : R := sqrt 2 * cloth_A c.

Definition cm_FC (c : ClothoidEgg) (y : R) : R := cloth_Icos c (cm_W c * y) / cm_W c.
Definition cm_FS (c : ClothoidEgg) (y : R) : R :=
  cloth_sigma c * cloth_Isin c (cm_W c * y) / cm_W c.

Lemma cm_sigma_pm : forall c, cloth_sigma c = 1 \/ cloth_sigma c = -1.
Proof. intro c. unfold cloth_sigma. destruct (Rle_dec 0 (cloth_cross c)); auto. Qed.

Lemma cm_W_pos : forall c, 0 < cloth_A c -> 0 < cm_W c.
Proof.
  intros c HA. unfold cm_W. apply Rmult_lt_0_compat; [apply sqrt_lt_R0; lra | exact HA].
Qed.

Lemma cm_psi_scaled : forall c y, 0 < cloth_A c ->
  cloth_psi c (cm_W c * y) = cloth_sigma c * (y * y).
Proof.
  intros c y HA. unfold cloth_psi, cm_W.
  assert (H2 : sqrt 2 * sqrt 2 = 2) by (apply sqrt_sqrt; lra).
  replace (cloth_sigma c * (sqrt 2 * cloth_A c * y) * (sqrt 2 * cloth_A c * y))
    with (cloth_sigma c * (sqrt 2 * sqrt 2) * (cloth_A c * cloth_A c) * (y * y)) by ring.
  rewrite H2. field. lra.
Qed.

Lemma cm_lin_deriv : forall K t, derivable_pt_lim (fun y => K * y) t K.
Proof.
  intros K t.
  assert (H : derivable_pt_lim (fun y => K * y) t (K * 1)).
  { eapply derivable_pt_lim_ext;
      [| exact (derivable_pt_lim_scal id K t 1 (derivable_pt_lim_id t))].
    intro z. unfold mult_real_fct, id. reflexivity. }
  rewrite Rmult_1_r in H. exact H.
Qed.

Lemma cm_FC_deriv : forall c, 0 < cloth_A c ->
  forall y, derivable_pt_lim (cm_FC c) y (cos (y * y)).
Proof.
  intros c HA y. pose proof (cm_W_pos c HA) as HW.
  assert (Hc := derivable_pt_lim_comp (fun y => cm_W c * y) (cloth_Icos c) y (cm_W c)
                  (cos (cloth_psi c (cm_W c * y))) (cm_lin_deriv (cm_W c) y)
                  (cloth_Icos_deriv c (cm_W c * y))).
  assert (Hs := derivable_pt_lim_scal _ (/ cm_W c) y _ Hc).
  replace (cos (y * y)) with (/ cm_W c * (cos (cloth_psi c (cm_W c * y)) * cm_W c)).
  - eapply derivable_pt_lim_ext; [| exact Hs].
    intro z. unfold mult_real_fct, comp, cm_FC. unfold Rdiv. ring.
  - rewrite cm_psi_scaled by exact HA.
    destruct (cm_sigma_pm c) as [-> | ->].
    + rewrite Rmult_1_l. field. lra.
    + replace (-1 * (y * y)) with (- (y * y)) by ring. rewrite cos_neg. field. lra.
Qed.

Lemma cm_FS_deriv : forall c, 0 < cloth_A c ->
  forall y, derivable_pt_lim (cm_FS c) y (sin (y * y)).
Proof.
  intros c HA y. pose proof (cm_W_pos c HA) as HW.
  assert (Hc := derivable_pt_lim_comp (fun y => cm_W c * y) (cloth_Isin c) y (cm_W c)
                  (sin (cloth_psi c (cm_W c * y))) (cm_lin_deriv (cm_W c) y)
                  (cloth_Isin_deriv c (cm_W c * y))).
  assert (Hs := derivable_pt_lim_scal _ (cloth_sigma c / cm_W c) y _ Hc).
  replace (sin (y * y))
    with (cloth_sigma c / cm_W c * (sin (cloth_psi c (cm_W c * y)) * cm_W c)).
  - eapply derivable_pt_lim_ext; [| exact Hs].
    intro z. unfold mult_real_fct, comp, cm_FS. unfold Rdiv. ring.
  - rewrite cm_psi_scaled by exact HA.
    destruct (cm_sigma_pm c) as [-> | ->].
    + replace (1 * (y * y)) with (y * y) by ring. field. lra.
    + replace (-1 * (y * y)) with (- (y * y)) by ring. rewrite sin_neg. field. lra.
Qed.

Lemma cm_FC_at0 : forall c, cm_FC c 0 = 0.
Proof. intro c. unfold cm_FC. rewrite Rmult_0_r, cloth_Icos_at0. unfold Rdiv. ring. Qed.

Lemma cm_FS_at0 : forall c, cm_FS c 0 = 0.
Proof. intro c. unfold cm_FS. rewrite Rmult_0_r, cloth_Isin_at0. unfold Rdiv. ring. Qed.

Lemma cm_FC_rescale : forall c s, 0 < cloth_A c ->
  cm_W c * cm_FC c (s / cm_W c) = cloth_Icos c s.
Proof.
  intros c s HA. pose proof (cm_W_pos c HA) as HW. unfold cm_FC.
  replace (cm_W c * (s / cm_W c)) with s by (field; lra). field. lra.
Qed.

Lemma cm_FS_rescale : forall c s, 0 < cloth_A c ->
  cloth_sigma c * (cm_W c * cm_FS c (s / cm_W c)) = cloth_Isin c s.
Proof.
  intros c s HA. pose proof (cm_W_pos c HA) as HW. unfold cm_FS.
  replace (cm_W c * (s / cm_W c)) with s by (field; lra).
  destruct (cm_sigma_pm c) as [-> | ->]; field; lra.
Qed.

(* A primitive with |F'| <= 1 is 1-Lipschitz (classic-free). *)
Lemma cm_prim_lip : forall (F F' : R -> R),
  (forall t, derivable_pt_lim F t (F' t)) -> (forall t, Rabs (F' t) <= 1) ->
  forall a b, Rabs (F a - F b) <= Rabs (a - b).
Proof.
  assert (Hle : forall (F F' : R -> R),
            (forall t, derivable_pt_lim F t (F' t)) -> (forall t, Rabs (F' t) <= 1) ->
            forall a b, a <= b -> Rabs (F b - F a) <= b - a).
  { intros F F' DF HF a b Hab.
    assert (A1 : a + F a <= b + F b).
    { apply (deriv_nonneg_incr (fun t => t + F t) (fun t => 1 + F' t) a b a b).
      - intros t _. apply derivable_pt_lim_plus with (f1 := id) (f2 := F);
          [apply derivable_pt_lim_id | apply DF].
      - intros t _. specialize (HF t). apply fz_abs_le_inv in HF. lra.
      - lra. - lra. - lra. }
    assert (A2 : a - F a <= b - F b).
    { apply (deriv_nonneg_incr (fun t => t - F t) (fun t => 1 - F' t) a b a b).
      - intros t _. apply derivable_pt_lim_minus with (f1 := id) (f2 := F);
          [apply derivable_pt_lim_id | apply DF].
      - intros t _. specialize (HF t). apply fz_abs_le_inv in HF. lra.
      - lra. - lra. - lra. }
    apply Rabs_le. split; lra. }
  intros F F' DF HF a b.
  destruct (Rle_lt_dec a b) as [H|H].
  - rewrite Rabs_minus_sym, (Rabs_minus_sym a b), (Rabs_pos_eq (b - a)) by lra.
    exact (Hle F F' DF HF a b H).
  - rewrite (Rabs_pos_eq (a - b)) by lra. exact (Hle F F' DF HF b a ltac:(lra)).
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The evaluator and its intake.                                          *)
(* -------------------------------------------------------------------------- *)

(* round-to-nearest sqrt 2 = 0x1.6a09e667f3bcdp+0 *)
Definition cm_r2 : binary64 :=
  Binary.B754_finite prec emax false 6369051672525773 (-52) eq_refl.
(* 2^-500, 2^500, -2^500 *)
Definition cm_Alo : binary64 :=
  Binary.B754_finite prec emax false 4503599627370496 (-552) eq_refl.
Definition cm_cap : binary64 :=
  Binary.B754_finite prec emax false 4503599627370496 (448) eq_refl.
Definition cm_mcap : binary64 :=
  Binary.B754_finite prec emax true 4503599627370496 (448) eq_refl.

Definition cm_w (A : binary64) : binary64 := b64_mult cm_r2 A.
Definition cm_x (A s : binary64) : binary64 := b64_div s (cm_w A).

Definition cm_Icos (A s : binary64) : binary64 := b64_mult (cm_w A) (b64_fresnel_C (cm_x A s)).
Definition cm_Isin (neg : bool) (A s : binary64) : binary64 :=
  if neg then sn_neg (b64_mult (cm_w A) (b64_fresnel_S (cm_x A s)))
  else b64_mult (cm_w A) (b64_fresnel_S (cm_x A s)).

Definition cm_accept (A s : binary64) : bool :=
  (b64_le cm_Alo A && b64_le A cm_cap) && (b64_le cm_mcap s && b64_le s cm_cap)
  && fresnel_accept_b (cm_x A s).

Lemma cm_consts_R :
  B2R cm_r2 = 6369051672525773 / 4503599627370496 /\
  B2R cm_Alo = bpow radix2 (-500) /\ B2R cm_cap = bpow radix2 500 /\
  B2R cm_mcap = - bpow radix2 500.
Proof.
  unfold cm_r2, cm_Alo, cm_cap, cm_mcap. cbn [Binary.B2R]. unfold F2R. cbn [Fnum Fexp cond_Zopp].
  replace (bpow radix2 (-500)) with (IZR (Zpos 4503599627370496) * bpow radix2 (-552))
    by (replace (-500)%Z with (52 + -552)%Z by reflexivity; rewrite bpow_plus; reflexivity).
  replace (bpow radix2 500) with (IZR (Zpos 4503599627370496) * bpow radix2 448)
    by (replace 500%Z with (52 + 448)%Z by reflexivity; rewrite bpow_plus; reflexivity).
  split; [cbn; lra|]. split; [reflexivity|]. split; [reflexivity|].
  rewrite Ropp_mult_distr_l, <- opp_IZR. reflexivity.
Qed.

Lemma cm_le_fin : forall lo hi x, fin lo = true -> fin hi = true ->
  andb (b64_le lo x) (b64_le x hi) = true -> fin x = true /\ B2R lo <= B2R x <= B2R hi.
Proof.
  intros lo hi x Flo Fhi H.
  assert (Fx : fin x = true).
  { destruct x as [s|s|s pl Hpl|s m e Hb]; try reflexivity; exfalso;
      apply andb_prop in H as [H1 H2]; destruct lo as [sl|sl|sl pll Hl|sl ml el Hbl];
      try discriminate Flo; destruct hi as [sh|sh|sh plh Hh|sh mh eh Hbh]; try discriminate Fhi;
      destruct s, sl, sh; cbn in H1, H2; try discriminate H1; try discriminate H2. }
  split; [exact Fx|]. apply andb_prop in H as [H1 H2].
  split; [apply (b64ae_le_true _ _ Flo Fx H1) | apply (b64ae_le_true _ _ Fx Fhi H2)].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Budget lines as real algebra.                                          *)
(* -------------------------------------------------------------------------- *)

Lemma cm_abs_div : forall x y, 0 < y -> Rabs (x / y) = Rabs x / y.
Proof.
  intros x y Hy. unfold Rdiv. rewrite Rabs_mult, Rabs_inv, (Rabs_pos_eq y) by lra. reflexivity.
Qed.

(* E_sqrt *)
Lemma cm_sqrt2_err : Rabs (6369051672525773 / 4503599627370496 - sqrt 2) <= / 9007199254740992.
Proof.
  set (r := 6369051672525773 / 4503599627370496).
  assert (L : r - / 9007199254740992 <= sqrt 2).
  { rewrite <- (sqrt_square (r - / 9007199254740992)) by (unfold r; lra).
    apply sqrt_le_1_alt. unfold r. lra. }
  assert (U : sqrt 2 <= r + / 9007199254740992).
  { rewrite <- (sqrt_square (r + / 9007199254740992)) by (unfold r; lra).
    apply sqrt_le_1_alt. unfold r. lra. }
  apply Rabs_le. split; lra.
Qed.

Lemma cm_sqrt2_range : 141421356 / 100000000 <= sqrt 2 <= 141421357 / 100000000.
Proof.
  split.
  - rewrite <- (sqrt_square (141421356 / 100000000)) by lra. apply sqrt_le_1_alt. lra.
  - rewrite <- (sqrt_square (141421357 / 100000000)) by lra. apply sqrt_le_1_alt. lra.
Qed.

(* E_param (with E_sqrt) *)
Lemma cm_w_alg : forall a sq r2 wh e,
  0 < a -> 0 < e -> e <= a * / 2 ^ 500 ->
  141421356 / 100000000 <= sq <= 141421357 / 100000000 ->
  0 <= r2 <= 14143 / 10000 -> Rabs (r2 - sq) <= / 9007199254740992 ->
  Rabs (wh - r2 * a) <= / 9007199254740992 * (r2 * a) + e ->
  Rabs (wh - sq * a) <= a * (5 / 2 * / 9007199254740992) /\ 1414 / 1000 * a <= wh <= 3 / 2 * a.
Proof.
  intros a sq r2 wh e Ha He Hea Hsq Hr2 Hd Hw.
  assert (P500 : 0 < / 2 ^ 500) by (apply Rinv_0_lt_compat, pow_lt; lra).
  assert (S500 : / 2 ^ 500 <= / 9007199254740992 / 1000).
  { replace (/ 9007199254740992 / 1000) with (/ (9007199254740992 * 1000)) by (field; lra).
    apply Rinv_le_contravar; [lra|].
    apply Rle_trans with (2 ^ 63); [cbn [pow]; lra | apply Rle_pow; lia || lra]. }
  assert (Ea : e <= a * (/ 9007199254740992 / 1000)) by
    (eapply Rle_trans; [exact Hea | apply Rmult_le_compat_l; lra]).
  assert (D : Rabs ((r2 - sq) * a) <= / 9007199254740992 * a).
  { rewrite Rabs_mult, (Rabs_pos_eq a) by lra. apply Rmult_le_compat_r; lra. }
  assert (R1 : r2 * a <= 14143 / 10000 * a) by (apply Rmult_le_compat_r; lra).
  assert (S1 : 141421356 / 100000000 * a <= sq * a) by (apply Rmult_le_compat_r; lra).
  assert (S2 : sq * a <= 141421357 / 100000000 * a) by (apply Rmult_le_compat_r; lra).
  assert (E : Rabs (wh - sq * a) <= a * (5 / 2 * / 9007199254740992)).
  { replace (wh - sq * a) with ((wh - r2 * a) + (r2 - sq) * a) by ring.
    pose proof (Rabs_triang (wh - r2 * a) ((r2 - sq) * a)). lra. }
  split; [exact E|]. apply fz_abs_le_inv in E. lra.
Qed.

(* E_arg *)
Lemma cm_x_alg : forall a sq wh s xh e,
  0 < a -> 0 < e <= / 2 ^ 1000 -> 141421356 / 100000000 <= sq ->
  Rabs (wh - sq * a) <= a * (5 / 2 * / 9007199254740992) -> 1414 / 1000 * a <= wh ->
  Rabs (xh - s / wh) <= / 9007199254740992 * Rabs (s / wh) + e -> Rabs xh <= 5 / 2 ->
  Rabs (xh - s / (sq * a)) <= 7 * / 9007199254740992.
Proof.
  intros a sq wh s xh e Ha He Hsq Hw Hwl Hx Hxh.
  assert (Wp : 0 < wh) by lra.
  assert (SA : 0 < sq * a) by (apply Rmult_lt_0_compat; lra).
  assert (E1000 : / 2 ^ 1000 <= / 9007199254740992 / 1000).
  { replace (/ 9007199254740992 / 1000) with (/ (9007199254740992 * 1000)) by (field; lra).
    apply Rinv_le_contravar; [lra|].
    apply Rle_trans with (2 ^ 63); [cbn [pow]; lra | apply Rle_pow; lia || lra]. }
  set (q := s / wh) in *.
  assert (Hq : Rabs q <= 25000001 / 10000000).
  { pose proof (Rabs_triang_inv q xh) as T. rewrite Rabs_minus_sym in T. lra. }
  assert (Id : q - s / (sq * a) = q * ((sq * a - wh) / (sq * a)))
    by (unfold q; field; split; lra).
  assert (Hr : Rabs ((sq * a - wh) / (sq * a)) <= 177 / 100 * / 9007199254740992).
  { rewrite (cm_abs_div _ _ SA).
    rewrite Rabs_minus_sym.
    apply Rle_trans with (a * (5 / 2 * / 9007199254740992) / (sq * a)).
    - apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; lra | exact Hw].
    - replace (a * (5 / 2 * / 9007199254740992) / (sq * a))
        with (5 / 2 * / 9007199254740992 * / sq) by (field; split; lra).
      assert (/ sq <= / (141421356 / 100000000)) by (apply Rinv_le_contravar; lra).
      assert (5 / 2 * / 9007199254740992 * / sq
              <= 5 / 2 * / 9007199254740992 * / (141421356 / 100000000))
        by (apply Rmult_le_compat_l; lra).
      lra. }
  assert (Hqx : Rabs (q - s / (sq * a))
                <= 25000001 / 10000000 * (177 / 100 * / 9007199254740992))
    by (rewrite Id; apply b64ae_abs_mult_le; assumption).
  replace (xh - s / (sq * a)) with ((xh - q) + (q - s / (sq * a))) by ring.
  pose proof (Rabs_triang (xh - q) (q - s / (sq * a))). lra.
Qed.

(* E_eval + E_out *)
Lemma cm_out_alg : forall a sq wh xh x Ch Fxh Fx Ih e,
  0 < a -> 0 < e -> e <= a * / 2 ^ 500 -> 0 <= sq <= 141421357 / 100000000 ->
  Rabs (wh - sq * a) <= a * (5 / 2 * / 9007199254740992) -> 0 <= wh <= 3 / 2 * a ->
  Rabs (Ch - Fxh) <= / 4398046511104 -> Rabs Fxh <= Rabs xh -> Rabs xh <= 5 / 2 ->
  Rabs (Fxh - Fx) <= Rabs (xh - x) -> Rabs (xh - x) <= 7 * / 9007199254740992 ->
  Rabs (Ih - wh * Ch) <= / 9007199254740992 * Rabs (wh * Ch) + e ->
  Rabs (Ih - sq * a * Fx) <= a * / 2199023255552.
Proof.
  intros a sq wh xh x Ch Fxh Fx Ih e Ha He Hea Hsq Hw Hwb HC HF Hxh HL Hx HI.
  assert (P500 : / 2 ^ 500 <= / 9007199254740992 / 1000).
  { replace (/ 9007199254740992 / 1000) with (/ (9007199254740992 * 1000)) by (field; lra).
    apply Rinv_le_contravar; [lra|].
    apply Rle_trans with (2 ^ 63); [cbn [pow]; lra | apply Rle_pow; lia || lra]. }
  assert (Ea : e <= a * (/ 9007199254740992 / 1000))
    by (eapply Rle_trans; [exact Hea | apply Rmult_le_compat_l; lra]).
  assert (Cm : Rabs Ch <= 5 / 2 + / 4398046511104).
  { pose proof (Rabs_triang_inv Ch Fxh). lra. }
  assert (B1 : Rabs (wh * Ch) <= 3 / 2 * a * (5 / 2 + / 4398046511104)).
  { apply b64ae_abs_mult_le; [rewrite Rabs_pos_eq; lra | exact Cm]. }
  assert (B2 : Rabs ((wh - sq * a) * Ch)
               <= a * (5 / 2 * / 9007199254740992) * (5 / 2 + / 4398046511104))
    by (apply b64ae_abs_mult_le; assumption).
  assert (SA : 0 <= sq * a) by (apply Rmult_le_pos; lra).
  assert (SA2 : sq * a <= 141421357 / 100000000 * a) by (apply Rmult_le_compat_r; lra).
  assert (B3 : Rabs (sq * a * (Ch - Fxh)) <= sq * a * / 4398046511104).
  { apply b64ae_abs_mult_le; [rewrite Rabs_pos_eq; lra | exact HC]. }
  assert (B4 : Rabs (sq * a * (Fxh - Fx)) <= sq * a * (7 * / 9007199254740992)).
  { apply b64ae_abs_mult_le; [rewrite Rabs_pos_eq; lra | lra]. }
  assert (B5 : sq * a * / 4398046511104 <= 141421357 / 100000000 * a * / 4398046511104)
    by (apply Rmult_le_compat_r; lra).
  assert (B6 : sq * a * (7 * / 9007199254740992)
               <= 141421357 / 100000000 * a * (7 * / 9007199254740992))
    by (apply Rmult_le_compat_r; lra).
  replace (Ih - sq * a * Fx)
    with ((Ih - wh * Ch) + (wh - sq * a) * Ch + sq * a * (Ch - Fxh) + sq * a * (Fxh - Fx))
    by ring.
  pose proof (Rabs_triang ((Ih - wh * Ch) + (wh - sq * a) * Ch + sq * a * (Ch - Fxh))
                          (sq * a * (Fxh - Fx))) as T1.
  pose proof (Rabs_triang ((Ih - wh * Ch) + (wh - sq * a) * Ch) (sq * a * (Ch - Fxh))) as T2.
  pose proof (Rabs_triang (Ih - wh * Ch) ((wh - sq * a) * Ch)) as T3.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The binary64 chain up to the canonical argument.                       *)
(* -------------------------------------------------------------------------- *)

Lemma cm_b1000 : bpow radix2 1000 = 2 ^ 1000.
Proof. rewrite pow_IZR. reflexivity. Qed.

Lemma cm_bpow500 : bpow radix2 (-500) = / 2 ^ 500 /\ bpow radix2 500 = 2 ^ 500.
Proof.
  assert (P : bpow radix2 500 = 2 ^ 500) by (rewrite pow_IZR; reflexivity).
  split; [|exact P]. change (-500)%Z with (Z.opp 500). rewrite bpow_opp, P. reflexivity.
Qed.

Lemma cm_front : forall A s, cm_accept A s = true ->
  fin A = true /\ fin s = true /\
  / 2 ^ 500 <= B2R A <= 2 ^ 500 /\ Rabs (B2R s) <= 2 ^ 500 /\
  fin (cm_w A) = true /\
  Rabs (B2R (cm_w A) - sqrt 2 * B2R A) <= B2R A * (5 / 2 * / 9007199254740992) /\
  1414 / 1000 * B2R A <= B2R (cm_w A) <= 3 / 2 * B2R A /\
  fin (cm_x A s) = true /\ Rabs (B2R (cm_x A s)) <= 5 / 2 /\
  fresnel_accept_b (cm_x A s) = true /\
  Rabs (B2R (cm_x A s) - B2R s / (sqrt 2 * B2R A)) <= 7 * / 9007199254740992.
Proof.
  intros A s H. unfold cm_accept in H.
  apply andb_prop in H as [H Hx]. apply andb_prop in H as [HA Hs].
  destruct cm_consts_R as [Er [Elo [Ecap Emcap]]]. destruct cm_bpow500 as [Bm Bp].
  destruct (cm_le_fin cm_Alo cm_cap A eq_refl eq_refl HA) as [FA [HAl HAh]].
  destruct (cm_le_fin cm_mcap cm_cap s eq_refl eq_refl Hs) as [Fs [Hsl Hsh]].
  rewrite Elo, Bm in HAl. rewrite Ecap, Bp in HAh, Hsh. rewrite Emcap, Bp in Hsl.
  assert (Hsa : Rabs (B2R s) <= 2 ^ 500) by (apply Rabs_le; split; lra).
  pose proof sp_u_val as Uv. pose proof fr_e0_bounds as [He0 He1].
  assert (P500 : 0 < / 2 ^ 500) by (apply Rinv_0_lt_compat, pow_lt; lra).
  assert (B1000 : 2 ^ 1000 = 2 ^ 500 * 2 ^ 500) by (rewrite <- pow_add; reflexivity).
  assert (Ha0 : 0 < B2R A) by lra.
  assert (E1000 : / 2 ^ 1000 = / 2 ^ 500 * / 2 ^ 500)
    by (rewrite B1000, Rinv_mult; reflexivity).
  assert (He1' : b64ae_e0 <= / 2 ^ 1000).
  { replace (/ 2 ^ 1000) with (/ 10715086071862673209484250490600018105614048117055336074437503883703510511249361224931983788156958581275946729175531468251871452856923140435984577574698574803934567774824230985421074605062371141877954182153046474983581941267398767559165543946077062914571196477686542167660429831652624386837205668069376)
      by (f_equal; rewrite pow_IZR; reflexivity).
    exact He1. }
  assert (Hea : b64ae_e0 <= B2R A * / 2 ^ 500).
  { eapply Rle_trans; [exact He1'|]. rewrite E1000.
    apply Rmult_le_compat_r; lra. }
  (* w^ = fl(r2 * A) *)
  assert (Br : Rabs (B2R cm_r2 * B2R A) <= bpow radix2 1000).
  { rewrite Er, Rabs_mult, !Rabs_pos_eq by lra.
    replace (bpow radix2 1000) with (2 ^ 500 * 2 ^ 500)
      by (rewrite <- B1000, pow_IZR; reflexivity).
    assert (1 <= 2 ^ 500) by (apply pow_R1_Rle; lra).
    assert (B2R A <= 2 ^ 500 * 2 ^ 500 / 2) by nra.
    lra. }
  destruct (b64ae_mult_err cm_r2 A eq_refl FA Br) as [Fw Ew].
  rewrite Uv, Er in Ew. rewrite Rabs_mult, (Rabs_pos_eq (6369051672525773 / 4503599627370496)),
    (Rabs_pos_eq (B2R A)) in Ew by lra.
  destruct (cm_w_alg (B2R A) (sqrt 2) (6369051672525773 / 4503599627370496) (B2R (b64_mult cm_r2 A))
              b64ae_e0 Ha0 He0 Hea cm_sqrt2_range ltac:(split; lra) cm_sqrt2_err Ew) as [Dw [Wl Wh]].
  fold (cm_w A) in Fw, Dw, Wl, Wh.
  (* x^ = fl(s / w^) *)
  assert (Wnz : B2R (cm_w A) <> 0) by lra.
  assert (Bq : Rabs (B2R s / B2R (cm_w A)) <= bpow radix2 1000).
  { rewrite (cm_abs_div (B2R s) (B2R (cm_w A)) ltac:(lra)).
    replace (bpow radix2 1000) with (2 ^ 500 / / 2 ^ 500)
      by (rewrite cm_b1000, B1000; field; apply pow_nonzero; lra).
    unfold Rdiv. apply Rmult_le_compat; try lra.
    - apply Rabs_pos.
    - left. apply Rinv_0_lt_compat. lra.
    - apply Rinv_le_contravar; lra. }
  destruct (b64ae_safe_of Rdiv s (cm_w A) Fs Fw Bq) as [_ [_ Hr]].
  destruct (b64_div_correct s (cm_w A) Fs Fw Wnz Hr) as [Ex Fx].
  pose proof (b64ae_round_err (B2R s / B2R (cm_w A))) as Rx.
  rewrite <- Ex, Uv in Rx. fold (cm_x A s) in Fx, Rx.
  destruct (fresnel_accept_ok _ Hx) as [_ Bx].
  pose proof (cm_x_alg (B2R A) (sqrt 2) (B2R (cm_w A)) (B2R s) (B2R (cm_x A s)) b64ae_e0
                Ha0 (conj He0 He1') (proj1 cm_sqrt2_range) Dw Wl Rx Bx) as Dx.
  repeat split; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  The clothoid theorems.                                                 *)
(* -------------------------------------------------------------------------- *)

Lemma cm_e0_le : forall a, / 2 ^ 500 <= a -> b64ae_e0 <= a * / 2 ^ 500.
Proof.
  intros a Ha. pose proof fr_e0_bounds as [_ He1].
  assert (E : / 2 ^ 1000 = / 2 ^ 500 * / 2 ^ 500)
    by (rewrite <- Rinv_mult, <- pow_add; reflexivity).
  assert (He1' : b64ae_e0 <= / 2 ^ 1000).
  { eapply Rle_trans; [exact He1|]. right. f_equal. rewrite pow_IZR. reflexivity. }
  rewrite E in He1'. eapply Rle_trans; [exact He1'|].
  apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat, pow_lt; lra | exact Ha].
Qed.

Lemma cm_out_mult : forall A (C : binary64), fin (cm_w A) = true -> fin C = true ->
  0 <= B2R (cm_w A) <= 3 / 2 * B2R A -> B2R A <= 2 ^ 500 ->
  Rabs (B2R C) <= 5 / 2 + / 4398046511104 ->
  fin (b64_mult (cm_w A) C) = true /\
  Rabs (B2R (b64_mult (cm_w A) C) - B2R (cm_w A) * B2R C)
    <= / 9007199254740992 * Rabs (B2R (cm_w A) * B2R C) + b64ae_e0.
Proof.
  intros A C Fw FC Hw HA HC.
  pose proof sp_u_val as Uv.
  assert (B : Rabs (B2R (cm_w A) * B2R C) <= bpow radix2 1000).
  { apply Rle_trans with (3 / 2 * 2 ^ 500 * (5 / 2 + / 4398046511104)).
    - apply b64ae_abs_mult_le; [rewrite Rabs_pos_eq; lra | exact HC].
    - replace (bpow radix2 1000) with (2 ^ 500 * 2 ^ 500)
        by (rewrite cm_b1000, <- pow_add; reflexivity).
      assert (16 <= 2 ^ 500) by (apply Rle_trans with (2 ^ 4); [cbn; lra | apply Rle_pow; lia || lra]).
      nra. }
  destruct (b64ae_mult_err _ _ Fw FC B) as [F E]. rewrite Uv in E. split; assumption.
Qed.

(* WITNESS {"claimId":"s8-b64-clothoid-map","topic":"numerics","lemma":"b64_clothoid_Icos_err","title":"Binary64 clothoid integrals through the canonical Fresnel evaluator: w = fl(fl(sqrt 2) A), x = fl(s / w), fl(w * b64_fresnel_C x) and +-fl(w * b64_fresnel_S x) are within A / 2^41 of cloth_Icos c s and cloth_Isin c s, with separate E_sqrt, E_param, E_arg, E_eval, E_out lines","file":"theories-flocq/B64_ClothoidMap.v","witness":"b64_clothoid_Icos_err","board":"ADR-0006"} *)
Theorem b64_clothoid_Icos_err : forall (c : ClothoidEgg) (A s : binary64),
  cloth_A c = B2R A -> cm_accept A s = true ->
  fin (cm_Icos A s) = true /\
  Rabs (B2R (cm_Icos A s) - cloth_Icos c (B2R s)) <= B2R A * / 2199023255552.
Proof.
  intros c A s HcA Hacc.
  destruct (cm_front A s Hacc)
    as [FA [Fs [HA [Hs [Fw [Dw [[Wl Wh] [Fx [Bx [Hx Dx]]]]]]]]]].
  assert (HcA0 : 0 < cloth_A c) by (rewrite HcA; pose proof (Rinv_0_lt_compat (2 ^ 500)
                                                    ltac:(apply pow_lt; lra)); lra).
  destruct (b64_fresnel_C_err (cm_FC c) (cm_FC_at0 c) (cm_FC_deriv c HcA0) _ Hx) as [FC EC].
  replace (bpow radix2 (-42)) with (/ 4398046511104) in EC by (cbn; reflexivity).
  assert (DF : forall t, derivable_pt_lim (cm_FC c) t (cos (t * t))) by exact (cm_FC_deriv c HcA0).
  assert (Lip := cm_prim_lip (cm_FC c) (fun t => cos (t * t)) DF
                   ltac:(intro t; apply Rabs_le; apply COS_bound)).
  assert (HF0 : Rabs (cm_FC c (B2R (cm_x A s))) <= Rabs (B2R (cm_x A s))).
  { pose proof (Lip (B2R (cm_x A s)) 0) as L. rewrite cm_FC_at0, !Rminus_0_r in L. exact L. }
  assert (HC : Rabs (B2R (b64_fresnel_C (cm_x A s))) <= 5 / 2 + / 4398046511104).
  { pose proof (Rabs_triang_inv (B2R (b64_fresnel_C (cm_x A s))) (cm_FC c (B2R (cm_x A s)))). lra. }
  destruct (cm_out_mult A _ Fw FC ltac:(lra) (proj2 HA) HC) as [FI EI].
  pose proof sp_u_val as Uv. pose proof fr_e0_bounds as [He0 He1].
  pose proof (cm_e0_le (B2R A) (proj1 HA)) as Hea.
  split; [exact FI|].
  unfold cm_Icos. rewrite <- (cm_FC_rescale c (B2R s) HcA0). unfold cm_W. rewrite HcA.
  exact (cm_out_alg (B2R A) (sqrt 2) (B2R (cm_w A)) (B2R (cm_x A s)) (B2R s / (sqrt 2 * B2R A))
           (B2R (b64_fresnel_C (cm_x A s))) (cm_FC c (B2R (cm_x A s)))
           (cm_FC c (B2R s / (sqrt 2 * B2R A))) (B2R (b64_mult (cm_w A) (b64_fresnel_C (cm_x A s))))
           b64ae_e0 ltac:(lra) He0 Hea
           ltac:(pose proof cm_sqrt2_range; lra) Dw ltac:(lra) EC HF0 Bx
           ltac:(unfold cm_W in Lip; rewrite <- HcA; apply Lip) Dx EI).
Qed.

Theorem b64_clothoid_Isin_err : forall (c : ClothoidEgg) (neg : bool) (A s : binary64),
  cloth_A c = B2R A -> cloth_sigma c = (if neg then -1 else 1) -> cm_accept A s = true ->
  fin (cm_Isin neg A s) = true /\
  Rabs (B2R (cm_Isin neg A s) - cloth_Isin c (B2R s)) <= B2R A * / 2199023255552.
Proof.
  intros c neg A s HcA Hsg Hacc.
  destruct (cm_front A s Hacc)
    as [FA [Fs [HA [Hs [Fw [Dw [[Wl Wh] [Fx [Bx [Hx Dx]]]]]]]]]].
  assert (HcA0 : 0 < cloth_A c) by (rewrite HcA; pose proof (Rinv_0_lt_compat (2 ^ 500)
                                                    ltac:(apply pow_lt; lra)); lra).
  destruct (b64_fresnel_S_err (cm_FS c) (cm_FS_at0 c) (cm_FS_deriv c HcA0) _ Hx) as [FS ES].
  replace (bpow radix2 (-42)) with (/ 4398046511104) in ES by (cbn; reflexivity).
  assert (DF : forall t, derivable_pt_lim (cm_FS c) t (sin (t * t))) by exact (cm_FS_deriv c HcA0).
  assert (Lip := cm_prim_lip (cm_FS c) (fun t => sin (t * t)) DF
                   ltac:(intro t; apply Rabs_le; apply SIN_bound)).
  assert (HF0 : Rabs (cm_FS c (B2R (cm_x A s))) <= Rabs (B2R (cm_x A s))).
  { pose proof (Lip (B2R (cm_x A s)) 0) as L. rewrite cm_FS_at0, !Rminus_0_r in L. exact L. }
  assert (HS : Rabs (B2R (b64_fresnel_S (cm_x A s))) <= 5 / 2 + / 4398046511104).
  { pose proof (Rabs_triang_inv (B2R (b64_fresnel_S (cm_x A s))) (cm_FS c (B2R (cm_x A s)))). lra. }
  destruct (cm_out_mult A _ Fw FS ltac:(lra) (proj2 HA) HS) as [FI EI].
  pose proof sp_u_val as Uv. pose proof fr_e0_bounds as [He0 He1].
  pose proof (cm_e0_le (B2R A) (proj1 HA)) as Hea.
  pose proof (cm_out_alg (B2R A) (sqrt 2) (B2R (cm_w A)) (B2R (cm_x A s)) (B2R s / (sqrt 2 * B2R A))
           (B2R (b64_fresnel_S (cm_x A s))) (cm_FS c (B2R (cm_x A s)))
           (cm_FS c (B2R s / (sqrt 2 * B2R A))) (B2R (b64_mult (cm_w A) (b64_fresnel_S (cm_x A s))))
           b64ae_e0 ltac:(lra) He0 Hea
           ltac:(pose proof cm_sqrt2_range; lra) Dw ltac:(lra) ES HF0 Bx
           ltac:(unfold cm_W in Lip; rewrite <- HcA; apply Lip) Dx EI) as Out.
  rewrite <- (cm_FS_rescale c (B2R s) HcA0). unfold cm_W. rewrite HcA, Hsg.
  revert Out. unfold cm_Isin.
  generalize (b64_mult (cm_w A) (b64_fresnel_S (cm_x A s))) FI. intros v Fv Out.
  generalize (cm_FS c (B2R s / (sqrt 2 * B2R A))) Out. intros f Out'.
  destruct neg.
  - destruct (sn_neg_ok v Fv) as [Fn En]. split; [exact Fn|]. rewrite En.
    replace (- B2R v - -1 * (sqrt 2 * B2R A * f)) with (- (B2R v - sqrt 2 * B2R A * f)) by ring.
    rewrite Rabs_Ropp. exact Out'.
  - split; [exact Fv|].
    replace (B2R v - 1 * (sqrt 2 * B2R A * f)) with (B2R v - sqrt 2 * B2R A * f) by ring.
    exact Out'.
Qed.

Print Assumptions cm_FC_deriv.
Print Assumptions cm_FS_deriv.
Print Assumptions cm_prim_lip.
Print Assumptions cm_sqrt2_err.
Print Assumptions cm_w_alg.
Print Assumptions cm_x_alg.
Print Assumptions cm_out_alg.
Print Assumptions b64_clothoid_Icos_err.
Print Assumptions b64_clothoid_Isin_err.
