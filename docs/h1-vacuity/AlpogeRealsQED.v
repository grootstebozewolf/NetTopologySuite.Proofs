(* AlpogeRealsQED.v -- twelve of the 39 refined main-line lemmas of the
   claimed RH/GRH Lean development (CocoSgt/riemann-hypothesis-lean @
   7cbf7a0), now PROVED to this corpus's standard: over Stdlib's real
   numbers R with Stdlib's exp, ln, Rpower and sqrt, no abstract operations,
   no "Mathlib fact" hypotheses, and only the three allowlisted axioms of
   docs/axiom-allowlist.txt (ClassicalDedekindReals.sig_not_dec,
   ClassicalDedekindReals.sig_forall_dec,
   FunctionalExtensionality.functional_extensionality_dep).

   Each theorem states the Lean lemma itself, up to representation: complex
   numbers as pairs of reals (x, y) with |w - z| = sqrt((x-x')^2 + (y-y')^2),
   Finset sums as list sums, and the development's abstract parameters
   (families, windows, Tied bounds) as section variables, as in Lean.
   The premises are the Lean lemma's own premises and nothing else.

     1  landau_growth_contra          (LandauGrowthContra.lean)
     2  landau_window_contra          (landauWindow.lean)
     3  landau_kernel_max             (LandauKernelMax.lean)
     4  landau_tails_pow              (landauTails.lean)
     5  eFamC_of_cls                  (ZeroFreeAllOfTopG.lean)
     6  landau_window_re_pos          (landauWindow.lean)
     7  eq_ofReal_sub_of_dist_le_of_le_sub_re (LandauDichotomy.lean)
     8  landau_nearest_equi           (LandauNearest.lean)
     9  exists_small_eps              (TopWin.lean)
    10  level_family                  (LevelFamily.lean: wt_pos, sum, iff)
    11  sigA_le (with chr_bounded's ±1 split) (SigALe.lean)
    12  hypV_of_cls                   (ZeroFreeAllOfTopG.lean)

   Allowlist finding.  Stdlib's ln, Rpower, exp_increasing and exp_ineq1_le
   all carry Classical_Prop.classic (Print Assumptions), which is NOT in
   the allowlist.  Hence:
   - the exp facts needed here (monotonicity, 1 + x <= exp x for every real
     x, (1 - y) exp y <= 1) are re-derived from Stdlib's series E1 x N -> exp x,
     growing_ineq and Rle_cv_lim, all inside the allowlist;
   - landau_growth_contra is proved with eta = (1 - d/e)/2 instead of Lean's
     log(e/d)/2 (the statement only asserts some eta), so no ln is needed;
     this also removes the translation "e^(eta U) <= s^k" that
     LandauWindowCore.v left unproved;
   - lemmas whose STATEMENTS mention Real.log or rpow
     (windowHyp_of_rpow_eventually, level_of_tiedWin, the windowHypU
     auxiliaries) cannot be stated over Stdlib's ln within the allowlist and
     were not chosen.

   Evidence for docs/attacks/2026-11-21-alpoge-twelve-over-reals.md.
   NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import Reals Lra Psatz List Factorial.
Import ListNotations.
Local Open Scope R_scope.

(* ===================================================================== *)
(* Helpers                                                                *)
(* ===================================================================== *)

(* Stdlib's exp_increasing, exp_ineq1_le, ln and Rpower all depend on
   Classical_Prop.classic (Print Assumptions), which is NOT in the corpus
   allowlist.  The exp facts used below are re-derived from Stdlib's series
   E1 x N -> exp x (E1_cvg), growing_ineq and Rle_cv_lim, which stay within
   the allowlist. *)

Lemma E1_term_nonneg : forall x n, 0 <= x -> 0 <= / INR (fact n) * x ^ n.
Proof. intros x n Hx. apply Rmult_le_pos; [left; apply Rinv_0_lt_compat, INR_fact_lt_0|apply pow_le; exact Hx]. Qed.

Lemma E1_growing : forall x, 0 <= x -> Un_growing (E1 x).
Proof. intros x Hx n. unfold E1. rewrite tech5. pose proof (E1_term_nonneg x (S n) Hx). lra. Qed.

Lemma E1_le_exp : forall x n, 0 <= x -> E1 x n <= exp x.
Proof. intros x n Hx. exact (growing_ineq (E1 x) (exp x) (E1_growing x Hx) (E1_cvg x) n). Qed.

(* 1 + h <= exp h for h >= 0 *)
Lemma exp_ge_1_plus : forall h, 0 <= h -> 1 + h <= exp h.
Proof.
  intros h Hh. pose proof (E1_le_exp h 1 Hh) as H. unfold E1 in H. simpl in H.
  replace (/ 1 * 1 + / 1 * (h * 1)) with (1 + h) in H by field. exact H.
Qed.

Lemma exp_le_mono : forall x y, x <= y -> exp x <= exp y.
Proof.
  intros x y H. replace y with (x + (y - x)) by ring. rewrite exp_plus.
  pose proof (exp_ge_1_plus (y - x) ltac:(lra)). pose proof (exp_pos x). nra.
Qed.

Lemma exp_lt_mono : forall x y, x < y -> exp x < exp y.
Proof.
  intros x y H. replace y with (x + (y - x)) by ring. rewrite exp_plus.
  pose proof (exp_ge_1_plus (y - x) ltac:(lra)). pose proof (exp_pos x). nra.
Qed.

Lemma Un_cv_const : forall c, Un_cv (fun _ => c) c.
Proof. intros c eps He. exists 0%nat. intros n _. unfold R_dist. rewrite Rminus_diag, Rabs_R0. exact He. Qed.

(* (1 - y) exp y <= 1 for 0 <= y: partial-sum invariant
   (1-y) E1 y N + y^(N+1)/N! <= 1, then the limit. *)
Lemma exp_upper : forall y, 0 <= y -> (1 - y) * exp y <= 1.
Proof.
  intros y Hy.
  assert (Hinv : forall N, (1 - y) * E1 y N + y ^ (S N) / INR (fact N) <= 1).
  { induction N as [|N IH].
    - unfold E1. simpl. unfold Rdiv. rewrite ?Rinv_1. lra.
    - unfold E1 in *. rewrite tech5.
      assert (Hf : INR (fact N) <= INR (fact (S N))) by (apply le_INR, fact_le; lia).
      assert (Hf0 : 0 < INR (fact N)) by apply INR_fact_lt_0.
      assert (Hp : 0 <= y ^ (S N)) by (apply pow_le; exact Hy).
      assert (Hdiv : y ^ (S N) / INR (fact (S N)) <= y ^ (S N) / INR (fact N)).
      { unfold Rdiv. apply Rmult_le_compat_l; [exact Hp|]. apply Rinv_le_contravar; lra. }
      replace ((1 - y) * (sum_f_R0 (fun k : nat => / INR (fact k) * y ^ k) N + / INR (fact (S N)) * y ^ S N)
               + y ^ S (S N) / INR (fact (S N)))
        with ((1 - y) * sum_f_R0 (fun k : nat => / INR (fact k) * y ^ k) N + y ^ (S N) / INR (fact (S N)))
        by (simpl pow; field; lra).
      lra. }
  assert (Hle : forall N, (1 - y) * E1 y N <= 1).
  { intro N. pose proof (Hinv N).
    assert (0 <= y ^ (S N) / INR (fact N)).
    { unfold Rdiv. apply Rmult_le_pos; [apply pow_le; exact Hy|left; apply Rinv_0_lt_compat, INR_fact_lt_0]. }
    lra. }
  assert (Hcv : Un_cv (fun N => (1 - y) * E1 y N) ((1 - y) * exp y)).
  { apply (CV_mult (fun _ => 1 - y) (E1 y)); [apply Un_cv_const|apply E1_cvg]. }
  exact (@Rle_cv_lim _ (fun _ => 1) _ 1 Hle Hcv (Un_cv_const 1)).
Qed.

(* Real.add_one_le_exp, for every real x, within the allowlist *)
Lemma add_one_le_exp : forall x, 1 + x <= exp x.
Proof.
  intro x. destruct (Rle_lt_dec 0 x) as [H|H]; [exact (exp_ge_1_plus x H)|].
  destruct (Rle_lt_dec x (-1)) as [H1|H1]; [pose proof (exp_pos x); lra|].
  pose proof (exp_upper (- x) ltac:(lra)) as Hu.
  assert (Hm : exp (- x) * exp x = 1) by (rewrite <- exp_plus; replace (- x + x) with 0 by ring; apply exp_0).
  pose proof (exp_pos x). pose proof (exp_pos (- x)).
  replace (1 - - x) with (1 + x) in Hu by ring.
  assert (Hk : (1 + x) * exp (- x) * exp x <= 1 * exp x) by (apply Rmult_le_compat_r; lra).
  rewrite Rmult_assoc, Hm in Hk. lra.
Qed.

Lemma exp_INR_mult : forall (k : nat) L, exp (INR k * L) = exp L ^ k.
Proof.
  intros k L. induction k as [|k IH].
  - simpl. rewrite Rmult_0_l, exp_0. reflexivity.
  - rewrite S_INR, Rmult_plus_distr_r, Rmult_1_l, exp_plus, IH. simpl. ring.
Qed.

Lemma pow_le_mono : forall a b (k : nat), 0 <= a -> a <= b -> a ^ k <= b ^ k.
Proof. intros a b k Ha Hab. apply pow_incr. lra. Qed.

(* ===================================================================== *)
(* 1  landau_growth_contra                                                *)
(* ===================================================================== *)
Theorem landau_growth_contra : forall c d e C, 0 < c -> 0 < d -> d < e ->
  exists eta, 0 < eta /\ exists U0, forall U, U0 <= U -> forall k : nat, U <= INR k ->
    C * exp (eta * U) / e ^ k < c / d ^ k.
Proof.
  intros c d e C Hc Hd Hde.
  assert (He : 0 < e) by lra.
  (* Lean takes L = log (e/d); within the allowlist take t = 1 - d/e, with
     exp t <= e/d from (1 - t) exp t <= 1. *)
  set (t := 1 - d / e).
  assert (Hde' : d / e < 1).
  { apply (Rmult_lt_reg_r e); [lra|]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
  assert (Hde0 : 0 < d / e) by (apply Rdiv_lt_0_compat; lra).
  assert (Ht : 0 < t) by (unfold t; lra).
  assert (Hexp_t : exp t <= e / d).
  { pose proof (exp_upper t ltac:(lra)) as Hu. replace (1 - t) with (d / e) in Hu by (unfold t; ring).
    apply (Rmult_le_reg_l (d / e)); [exact Hde0|]. replace (d / e * (e / d)) with 1 by (field; lra). exact Hu. }
  exists (t / 2). split; [lra|].
  exists (2 * Rabs C / (c * t)). intros U HU k Hk.
  assert (Hdk : 0 < d ^ k) by (apply pow_lt; lra).
  assert (Hek : 0 < e ^ k) by (apply pow_lt; lra).
  assert (Hpow : d ^ k * exp (INR k * t) <= e ^ k).
  { rewrite exp_INR_mult.
    assert (exp t ^ k <= (e / d) ^ k) by (apply pow_le_mono; [left; apply exp_pos|exact Hexp_t]).
    assert (Hed : d ^ k * (e / d) ^ k = e ^ k).
    { unfold Rdiv. rewrite Rpow_mult_distr, pow_inv. field. apply pow_nonzero. lra. }
    rewrite <- Hed. apply Rmult_le_compat_l; lra. }
  set (X := exp (t / 2 * U)).
  assert (HX0 : 0 < X) by apply exp_pos.
  assert (HcL : 0 < c * t) by (apply Rmult_lt_0_compat; lra).
  assert (HU' : 2 * Rabs C <= U * (c * t)).
  { apply (Rmult_le_compat_r (c * t)) in HU; [|lra].
    unfold Rdiv in HU. rewrite Rmult_assoc, Rinv_l in HU by lra. lra. }
  assert (h1 : t / 2 * U + 1 <= X) by (unfold X; pose proof (add_one_le_exp (t / 2 * U)); lra).
  assert (hX : Rabs C < c * X).
  { assert (c * (t / 2 * U + 1) <= c * X) by (apply Rmult_le_compat_l; lra). nra. }
  assert (hY : X * X <= exp (INR k * t)).
  { unfold X. rewrite <- exp_plus. apply exp_le_mono. nra. }
  assert (hCX : C * X * d ^ k <= Rabs C * X * d ^ k).
  { apply Rmult_le_compat_r; [lra|]. apply Rmult_le_compat_r; [lra|]. apply Rle_abs. }
  assert (h2 : Rabs C * X < c * (X * X)) by nra.
  assert (h3 : c * (X * X) <= c * exp (INR k * t)) by (apply Rmult_le_compat_l; lra).
  assert (Hmain : C * X * d ^ k < c * e ^ k).
  { assert (Rabs C * X * d ^ k < c * exp (INR k * t) * d ^ k) by (apply Rmult_lt_compat_r; [exact Hdk|lra]).
    assert (c * exp (INR k * t) * d ^ k <= c * e ^ k).
    { replace (c * exp (INR k * t) * d ^ k) with (c * (d ^ k * exp (INR k * t))) by ring.
      apply Rmult_le_compat_l; lra. }
    lra. }
  apply (Rmult_lt_reg_r (e ^ k * d ^ k)); [apply Rmult_lt_0_compat; assumption|].
  replace (C * X / e ^ k * (e ^ k * d ^ k)) with (C * X * d ^ k) by (field; lra).
  replace (c / d ^ k * (e ^ k * d ^ k)) with (c * e ^ k) by (field; lra).
  exact Hmain.
Qed.

(* ===================================================================== *)
(* 2  landau_window_contra                                                *)
(* ===================================================================== *)
Theorem landau_window_contra : forall c d e E M C, 0 < c -> 0 < d -> d < e -> e <= E ->
  (forall eta, 0 < eta -> forall U0, exists U, U0 <= U /\ exists k : nat, U <= INR k /\
     c / d ^ k <= M / e ^ k + C * exp (eta * U) / E ^ k) -> False.
Proof.
  intros c d e E M C Hc Hd Hde HeE H.
  destruct (landau_growth_contra c d e (Rabs M + Rabs C) Hc Hd Hde) as [eta [Heta [U0 HU0]]].
  destruct (H eta Heta (Rmax U0 0)) as [U [HU [k [Hk Hle]]]].
  assert (HU0' : U0 <= U) by (eapply Rle_trans; [apply Rmax_l|exact HU]).
  assert (HU00 : 0 <= U) by (eapply Rle_trans; [apply Rmax_r|exact HU]).
  pose proof (HU0 U HU0' k Hk) as h1.
  assert (He : 0 < e) by lra.
  assert (Hek : 0 < e ^ k) by (apply pow_lt; lra).
  assert (HEk : e ^ k <= E ^ k) by (apply pow_le_mono; lra).
  assert (HEk0 : 0 < E ^ k) by lra.
  set (X := exp (eta * U)).
  assert (HX : 1 <= X) by (unfold X; pose proof (add_one_le_exp (eta * U)); nra).
  assert (h2 : M / e ^ k <= Rabs M * X / e ^ k).
  { unfold Rdiv. apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; lra|].
    pose proof (Rle_abs M). pose proof (Rabs_pos M). nra. }
  assert (h3 : C * X / E ^ k <= Rabs C * X / e ^ k).
  { assert (HCX : C * X <= Rabs C * X) by (apply Rmult_le_compat_r; [lra|apply Rle_abs]).
    assert (HC0 : 0 <= Rabs C * X) by (pose proof (Rabs_pos C); nra).
    apply Rle_trans with (Rabs C * X / E ^ k).
    - unfold Rdiv. apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; lra|exact HCX].
    - unfold Rdiv. apply Rmult_le_compat_l; [exact HC0|]. apply Rinv_le_contravar; lra. }
  assert (h4 : (Rabs M + Rabs C) * X / e ^ k = Rabs M * X / e ^ k + Rabs C * X / e ^ k) by (field; lra).
  fold X in h1, Hle. lra.
Qed.

(* ===================================================================== *)
(* 3  landau_kernel_max                                                   *)
(* ===================================================================== *)
(* x^k / k! <= exp x for x >= 0, from Stdlib's series E1 x N -> exp x. *)
Lemma pow_div_fact_le_exp : forall x (k : nat), 0 <= x -> x ^ k / INR (fact k) <= exp x.
Proof.
  intros x k Hx.
  assert (Hterm : forall n, 0 <= / INR (fact n) * x ^ n).
  { intro n. apply Rmult_le_pos; [left; apply Rinv_0_lt_compat, INR_fact_lt_0|apply pow_le; exact Hx]. }
  assert (Hgrow : Un_growing (E1 x)).
  { intro n. unfold E1. rewrite tech5. pose proof (Hterm (S n)). lra. }
  assert (Hle : x ^ k / INR (fact k) <= E1 x k).
  { destruct k as [|n].
    - unfold E1. simpl. lra.
    - unfold E1. rewrite tech5.
      pose proof (cond_pos_sum (fun k0 => / INR (fact k0) * x ^ k0) n Hterm).
      unfold Rdiv. rewrite Rmult_comm. lra. }
  pose proof (growing_ineq (E1 x) (exp x) Hgrow (E1_cvg x) k). lra.
Qed.

Theorem landau_kernel_max : forall (k : nat) a u, 0 < a -> 0 <= u ->
  u ^ k * exp (- a * u) / INR (fact k) <= 1 / a ^ k.
Proof.
  intros k a u Ha Hu.
  pose proof (pow_div_fact_le_exp (a * u) k ltac:(nra)) as H.
  assert (Hak : 0 < a ^ k) by (apply pow_lt; exact Ha).
  assert (Hf : 0 < INR (fact k)) by apply INR_fact_lt_0.
  apply (Rmult_le_reg_r (a ^ k)); [exact Hak|].
  replace (1 / a ^ k * a ^ k) with 1 by (field; lra).
  replace (u ^ k * exp (- a * u) / INR (fact k) * a ^ k)
    with ((a * u) ^ k / INR (fact k) * exp (- (a * u))) by (rewrite Rpow_mult_distr; replace (- a * u) with (- (a * u)) by ring; field; lra).
  assert (Hm : (a * u) ^ k / INR (fact k) * exp (- (a * u)) <= exp (a * u) * exp (- (a * u))).
  { apply Rmult_le_compat_r; [left; apply exp_pos|exact H]. }
  rewrite <- exp_plus in Hm. replace (a * u + - (a * u)) with 0 in Hm by ring. rewrite exp_0 in Hm. exact Hm.
Qed.

(* ===================================================================== *)
(* 4  landau_tails_pow                                                    *)
(* ===================================================================== *)
Theorem landau_tails_pow : forall (k : nat) sigma a x c, 0 < sigma -> 0 < a ->
  x + INR k * ((sigma - a) / a) <= c ->
  exp x * / (a ^ (k + 1)) <= exp c / a / sigma ^ k.
Proof.
  intros k sigma a x c Hs Ha Hc.
  assert (h1 : sigma / a <= exp ((sigma - a) / a)).
  { pose proof (add_one_le_exp ((sigma - a) / a)) as H.
    replace (1 + (sigma - a) / a) with (sigma / a) in H by (field; lra). lra. }
  assert (Hsa : 0 <= sigma / a) by (left; apply Rdiv_lt_0_compat; lra).
  assert (h2 : (sigma / a) ^ k <= exp (INR k * ((sigma - a) / a))).
  { rewrite exp_INR_mult. apply pow_le_mono; assumption. }
  assert (h3 : exp x * (sigma / a) ^ k <= exp c).
  { apply Rle_trans with (exp x * exp (INR k * ((sigma - a) / a))).
    - apply Rmult_le_compat_l; [left; apply exp_pos|exact h2].
    - rewrite <- exp_plus. apply exp_le_mono. exact Hc. }
  assert (Hsk : 0 < sigma ^ k) by (apply pow_lt; lra).
  assert (Hak : 0 < a ^ k) by (apply pow_lt; lra).
  replace (exp x * / a ^ (k + 1)) with (exp x * (sigma / a) ^ k / a / sigma ^ k).
  - unfold Rdiv. apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; exact Hsk|].
    apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; exact Ha|exact h3].
  - rewrite pow_add, pow_1. unfold Rdiv. rewrite Rpow_mult_distr, pow_inv. field.
    split; [lra|]. split; apply pow_nonzero; lra.
Qed.

(* ===================================================================== *)
(* 6  landau_window_re_pos  (w in ball z r, r <= Re z  ==>  0 < Re w)     *)
(* ===================================================================== *)
Theorem landau_window_re_pos : forall zr zi wr wi r, r <= zr ->
  sqrt ((wr - zr)² + (wi - zi)²) < r -> 0 < wr.
Proof.
  intros zr zi wr wi r Hr Hd.
  assert (H1 : Rabs (wr - zr) <= sqrt ((wr - zr)² + (wi - zi)²)).
  { rewrite <- sqrt_Rsqr_abs. apply sqrt_le_1_alt. pose proof (Rle_0_sqr (wi - zi)). lra. }
  assert (H2 : Rabs (wr - zr) < r) by lra.
  apply Rabs_def2 in H2. lra.
Qed.

(* ===================================================================== *)
(* 7  eq_ofReal_sub_of_dist_le_of_le_sub_re                               *)
(* ===================================================================== *)
Theorem eq_ofReal_sub_of_dist_le_of_le_sub_re : forall x y sigma D,
  sqrt ((x - sigma)² + y²) <= D -> D <= sigma - x -> x = sigma - D /\ y = 0.
Proof.
  intros x y sigma D H1 H2.
  set (S := (x - sigma)² + y²).
  change (sqrt S <= D) in H1.
  assert (HS : 0 <= S) by (unfold S; pose proof (Rle_0_sqr (x - sigma)); pose proof (Rle_0_sqr y); lra).
  assert (HD : 0 <= D) by (pose proof (sqrt_pos S); lra).
  assert (HSD : S <= D²).
  { rewrite <- (sqrt_sqrt S HS). unfold Rsqr. apply Rmult_le_compat; try apply sqrt_pos; exact H1. }
  assert (HD2 : D² <= (x - sigma)²).
  { unfold Rsqr. replace ((x - sigma) * (x - sigma)) with ((sigma - x) * (sigma - x)) by ring.
    apply Rmult_le_compat; lra. }
  assert (Hy : y² = 0) by (unfold S in HSD; pose proof (Rle_0_sqr y); lra).
  assert (Hy0 : y = 0) by (apply Rsqr_0_uniq; exact Hy).
  split; [|exact Hy0].
  assert (Hxs : (sigma - x)² = D²) by (unfold S in HSD; rewrite Hy in HSD; unfold Rsqr in *; nra).
  assert (sigma - x = D) by (apply Rsqr_inj; lra).
  lra.
Qed.

(* ===================================================================== *)
(* 8  landau_nearest_equi                                                 *)
(* ===================================================================== *)
Theorem landau_nearest_equi : forall sigma g ar ai br bi, ar < sigma -> br < sigma ->
  sqrt ((sigma - ar)² + (g - ai)²) = sqrt ((sigma - br)² + (g - bi)²) ->
  (ai <> bi -> g * (2 * (ai - bi)) <> (sigma - ar)² + ai² - (sigma - br)² - bi²) ->
  ar = br /\ ai = bi.
Proof.
  intros sigma g ar ai br bi Ha Hb Hd Hg.
  assert (HA : 0 <= (sigma - ar)² + (g - ai)²) by (pose proof (Rle_0_sqr (sigma - ar)); pose proof (Rle_0_sqr (g - ai)); lra).
  assert (HB : 0 <= (sigma - br)² + (g - bi)²) by (pose proof (Rle_0_sqr (sigma - br)); pose proof (Rle_0_sqr (g - bi)); lra).
  apply sqrt_inj in Hd; [|exact HA|exact HB].
  assert (Hi : ai = bi).
  { destruct (Req_dec ai bi) as [E|E]; [exact E|]. exfalso. apply (Hg E). unfold Rsqr in *. nra. }
  split; [|exact Hi].
  subst bi. assert (Hs : (sigma - ar)² = (sigma - br)²) by lra.
  apply Rsqr_inj in Hs; lra.
Qed.

(* ===================================================================== *)
(* 9  exists_small_eps                                                    *)
(* ===================================================================== *)
Theorem exists_small_eps : forall C delta eps1, 0 < delta -> 0 < eps1 ->
  exists eps, 0 < eps /\ eps < eps1 /\ C * eps <= delta.
Proof.
  intros C delta eps1 Hd He.
  assert (Hp : 0 < Rabs C + 1) by (pose proof (Rabs_pos C); lra).
  set (e := Rmin (eps1 / 2) (delta / (Rabs C + 1))).
  assert (He1 : e <= eps1 / 2) by apply Rmin_l.
  assert (He2 : e <= delta / (Rabs C + 1)) by apply Rmin_r.
  assert (He0 : 0 < e) by (unfold e; apply Rmin_glb_lt; apply Rdiv_lt_0_compat; lra).
  exists e. split; [exact He0|]. split; [lra|].
  apply Rle_trans with ((Rabs C + 1) * e).
  - pose proof (Rle_abs C). nra.
  - apply Rle_trans with ((Rabs C + 1) * (delta / (Rabs C + 1))).
    + apply Rmult_le_compat_l; lra.
    + right. field. lra.
Qed.

(* ===================================================================== *)
(* 11 sigA_le, with chr_bounded's ±1 split                                *)
(* ===================================================================== *)
Lemma chr_sq_one : forall v : R, v * v = 1 -> v = 1 \/ v = -1.
Proof.
  intros v H. assert (H' : (v - 1) * (v + 1) = 0) by lra.
  apply Rmult_integral in H'. lra.
Qed.

Fixpoint rsum (l : list R) : R := match l with [] => 0 | v :: t => v + rsum t end.

(* SigA = sum over PsiA \ kept of |GPsi| (each <= x^(1/2+eps) by EAtH.bdG),
   card (PsiA \ kept) <= card PsiA = 4 o (card_PsiA, hE.o_eq). *)
Theorem sigA_le : forall (vals : list R) (X o : R),
  0 <= X -> Forall (fun v => v <= X) vals -> INR (length vals) <= 4 * o ->
  rsum vals <= 4 * o * X.
Proof.
  intros vals X o HX Hv Hc.
  assert (H : rsum vals <= INR (length vals) * X).
  { clear Hc. induction Hv as [|v l Hv _ IH]; simpl rsum; simpl length.
    - simpl. lra.
    - rewrite S_INR. lra. }
  assert (INR (length vals) * X <= 4 * o * X) by (apply Rmult_le_compat_r; assumption).
  lra.
Qed.

(* ===================================================================== *)
(* 12 hypV_of_cls                                                         *)
(* ===================================================================== *)
Theorem hypV_of_cls : forall (Ix : Type) (P Qb : R -> Ix -> Prop) (x1 : R),
  (forall x, x1 <= x -> forall i, P x i /\ Qb x i) ->
  exists x0, forall x, x0 <= x -> forall i, Qb x i.
Proof. intros Ix P Qb x1 H. exists (x1 + 1). intros x Hx i. apply (H x ltac:(lra) i). Qed.

(* ===================================================================== *)
(* 5  eFamC_of_cls                                                        *)
(* ===================================================================== *)
Theorem eFamC_of_cls : forall (Ix : Type) (EAt : R -> R -> R -> Ix -> Prop)
  (Lx Le : R -> Ix -> R) (Qb : R -> Ix -> Prop) (x1 eps : R),
  (forall x, x1 <= x -> forall i, EAt (Lx x i) (Le x i) 4 i /\ Qb x i) ->
  (forall x i, x1 <= x -> Lx x i = x) ->           (* Fm.L_x *)
  (forall x i, Le x i = eps) ->                    (* Fm.L_eps *)
  exists Cc xE, forall x, xE <= x -> forall i, EAt x eps Cc i.
Proof.
  intros Ix EAt Lx Le Qb x1 eps H HL HE. exists 4, (x1 + 1). intros x Hx i.
  destruct (H x ltac:(lra) i) as [H1 _]. rewrite (HL x i ltac:(lra)), HE in H1. exact H1.
Qed.

(* ===================================================================== *)
(* 10 level_family                                                       *)
(* ===================================================================== *)
Section LevelFamily.
Variable Ch : Type.
Variable one : Ch.
Hypothesis ch_eq_dec : forall a b : Ch, {a = b} + {a <> b}.
Variable lwt : Ch -> R.                          (* Level.wt *)
Hypothesis lwt_pos : forall c, c <> one -> 0 < lwt c.
Definition wt (c : Ch) : R := if ch_eq_dec c one then 1 else lwt c.   (* level_family_wt *)

Theorem level_family_wt_pos : forall c, 0 < wt c.
Proof. intro c. unfold wt. destruct (ch_eq_dec c one) as [_|Hn]; [lra|exact (lwt_pos c Hn)]. Qed.

Variable Gchi : Ch -> R.
Variable Gz : R.
Hypothesis Gchi_one : Gchi one = Gz.                (* gChi_eq, Gz_eq *)

(* level_family_sum: Λ.Gm y = Gz + sum over KEPT \ {one} of wt * Re Gchi *)
Theorem level_family_sum : forall rest : list Ch, ~ In one rest ->
  rsum (map (fun c => wt c * Gchi c) (one :: rest)) = Gz + rsum (map (fun c => lwt c * Gchi c) rest).
Proof.
  intros rest Hn. simpl. unfold wt at 1. destruct (ch_eq_dec one one) as [_|Hc]; [|congruence].
  rewrite Gchi_one.
  assert (H : rsum (map (fun c => wt c * Gchi c) rest) = rsum (map (fun c => lwt c * Gchi c) rest)).
  { induction rest as [|a rest IH]; simpl; [reflexivity|].
    unfold wt at 1. destruct (ch_eq_dec a one) as [Ha|Ha].
    - subst. exfalso. apply Hn. left. reflexivity.
    - rewrite IH; [reflexivity|]. intro Hin. apply Hn. right. exact Hin. }
  rewrite H. ring.
Qed.

Variable Cx : Type.
Variable re : Cx -> R.
Variable Lz : Ch -> Cx -> Prop.
Variable KEPT : Ch -> Prop.
(* ZeroFree F theta <-> Λ.ZeroFreeAbove theta *)
Theorem level_family_zerofree : forall theta,
  (forall (i : {c | KEPT c}) s, theta < re s -> ~ Lz (proj1_sig i) s) <->
  (forall c, KEPT c -> forall s, theta < re s -> ~ Lz c s).
Proof.
  intro theta. split.
  - intros H c Hc s Hs. exact (H (exist _ c Hc) s Hs).
  - intros H [c Hc] s Hs. exact (H c Hc s Hs).
Qed.
End LevelFamily.

Print Assumptions landau_growth_contra.
Print Assumptions landau_window_contra.
Print Assumptions landau_kernel_max.
Print Assumptions landau_tails_pow.
Print Assumptions eFamC_of_cls.
Print Assumptions landau_window_re_pos.
Print Assumptions eq_ofReal_sub_of_dist_le_of_le_sub_re.
Print Assumptions landau_nearest_equi.
Print Assumptions exists_small_eps.
Print Assumptions level_family_wt_pos.
Print Assumptions level_family_sum.
Print Assumptions level_family_zerofree.
Print Assumptions sigA_le.
Print Assumptions hypV_of_cls.
Print Assumptions add_one_le_exp.
