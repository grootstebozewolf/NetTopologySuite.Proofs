(* AlpogeSixthLandau.v -- four Landau-theorem lemmas of the claimed RH/GRH
   Lean development (CocoSgt/riemann-hypothesis-lean @ 7cbf7a0), REFINED
   over Stdlib's R, within the three-axiom allowlist
   (docs/axiom-allowlist.txt), all under
   src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/:

     1  iteratedDeriv_laplace   IteratedDerivLaplace.lean
     2  landau_finite           LandauFinite.lean
     3  landau_pole_asym        LandauPoleAsym.lean  (+ landau_pole_asym_deriv)
     4  poleData                poleData.lean        (assembled from poleData_char)

   "Refined" (the criterion of AlpogeSkeleton.v / AlpogeRefineBatch.v): the
   Lean proof's own reasoning is rebuilt in Rocq with zero axioms; its
   remaining inputs are only (a) standard Mathlib facts, named hypotheses
   tagged [Mathlib], or (b) other inventory lemmas, tagged [inventory].

   The statements reuse AlpogeDeepStatements.v (Cc = R x R, CDerivWithin,
   IterDerivs, CAnalyticAt, EvPunct, ball, LaplaceAt, PoleData,
   poleData_statement, landau_pole_asym(_deriv)_statement); item 1 produces
   exactly the hypothesis ILAP of AlpogeFifthBatch.v Part B (landau_coeff),
   and feeds it (landau_coeff_of_iteratedDeriv_laplace).  Concrete over R
   where cheap: the complex triangle inequality, uniqueness of derivatives
   on open sets, sum/difference rules, the Laplace bound and the
   convergence of int u^n e^(-b u), finite choice, finite intersections of
   punctured neighbourhoods, linearity of the Laplace integral, and all the
   sign/factorial/residue algebra are proved here, not assumed.

   Each section names its Lean source (file : lemma : line).

   NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import Reals Lra Psatz Lia List Factorial FunctionalExtensionality.
From NTS.Proofs.Probes Require Import AlpogeRealsQED AlpogeRealsQED2 CleanIntegralQED AlpogeDeepStatements AlpogeFifthBatch.
Import ListNotations.
Local Open Scope R_scope.

(* ===================================================================== *)
(* Part 0: complex-number infrastructure over Cc = R x R                  *)
(* ===================================================================== *)
Lemma Cc_ext : forall a b, cre a = cre b -> cim a = cim b -> a = b.
Proof. intros [ar ai] [br bi]; simpl; intros; subst; reflexivity. Qed.

Definition Cc_eq_dec (a b : Cc) : {a = b} + {a <> b}.
Proof.
  destruct (Req_EM_T (cre a) (cre b)) as [E1|N1].
  - destruct (Req_EM_T (cim a) (cim b)) as [E2|N2].
    + left. apply Cc_ext; assumption.
    + right. intro H. apply N2. rewrite H. reflexivity.
  - right. intro H. apply N1. rewrite H. reflexivity.
Defined.

Definition n2 (a : Cc) : R := cre a * cre a + cim a * cim a.

Lemma n2_nonneg : forall a, 0 <= n2 a.
Proof. intro a. unfold n2. nra. Qed.

Lemma n2_pos : forall a, a <> cofR 0 -> 0 < n2 a.
Proof.
  intros a Ha. destruct (Rlt_or_le 0 (n2 a)) as [H|H]; [exact H|].
  exfalso. apply Ha. unfold n2 in H. apply Cc_ext; simpl; nra.
Qed.

Lemma cnorm_nonneg : forall a, 0 <= cnorm a.
Proof. intro a. apply sqrt_pos. Qed.

Lemma cnorm_sq : forall a, cnorm a * cnorm a = n2 a.
Proof. intro a. apply sqrt_sqrt. apply n2_nonneg. Qed.

Lemma cnorm_le_sq : forall a M, 0 <= M -> n2 a <= M * M -> cnorm a <= M.
Proof.
  intros a M HM H. unfold cnorm. rewrite <- (sqrt_square M HM).
  apply sqrt_le_1_alt. exact H.
Qed.

Lemma cre_le_cnorm : forall a, Rabs (cre a) <= cnorm a.
Proof.
  intro a. rewrite <- sqrt_Rsqr_abs. unfold cnorm, Rsqr. apply sqrt_le_1_alt.
  pose proof (Rle_0_sqr (cim a)). unfold Rsqr in H. lra.
Qed.

Lemma cim_le_cnorm : forall a, Rabs (cim a) <= cnorm a.
Proof.
  intro a. rewrite <- sqrt_Rsqr_abs. unfold cnorm, Rsqr. apply sqrt_le_1_alt.
  pose proof (Rle_0_sqr (cre a)). unfold Rsqr in H. lra.
Qed.

Lemma cnorm_cofR : forall x, cnorm (cofR x) = Rabs x.
Proof.
  intro x. unfold cnorm, cofR. simpl. rewrite <- sqrt_Rsqr_abs. unfold Rsqr. f_equal. ring.
Qed.

Lemma cnorm_triangle : forall a b, cnorm (cadd a b) <= cnorm a + cnorm b.
Proof.
  intros a b. pose proof (cnorm_nonneg a) as HA. pose proof (cnorm_nonneg b) as HB.
  pose proof (cnorm_sq a) as SA. pose proof (cnorm_sq b) as SB.
  apply cnorm_le_sq; [lra|]. unfold n2 in *. unfold cadd. simpl.
  set (A := cnorm a) in *. set (B := cnorm b) in *.
  set (t := cre a * cre b + cim a * cim b).
  assert (HAB : 0 <= A * B) by nra.
  assert (Hsq : (A * B) * (A * B) - t * t = (cre a * cim b - cim a * cre b) * (cre a * cim b - cim a * cre b)).
  { unfold t. replace ((A * B) * (A * B)) with ((A * A) * (B * B)) by ring. rewrite SA, SB. ring. }
  assert (Ht : t <= A * B).
  { destruct (Rle_or_lt t 0) as [H|H]; [lra|].
    assert (E : 0 <= (A * B - t) * (A * B + t)).
    { replace ((A * B - t) * (A * B + t)) with ((A * B) * (A * B) - t * t) by ring. rewrite Hsq.
      apply Rle_0_sqr. }
    destruct (Rle_or_lt (A * B - t) 0) as [H3|H3]; [|lra].
    assert (A * B + t > 0) by lra. nra. }
  unfold t in Ht. nra.
Qed.

Lemma csub_split : forall a b c, csub a c = cadd (csub a b) (csub b c).
Proof. intros. apply Cc_ext; unfold csub, cadd; simpl; ring. Qed.

Lemma cnorm_sub_tri : forall a b c, cnorm (csub a c) <= cnorm (csub a b) + cnorm (csub b c).
Proof. intros. rewrite (csub_split a b c). apply cnorm_triangle. Qed.

Lemma cnorm_sub_sym : forall a b, cnorm (csub a b) = cnorm (csub b a).
Proof. intros. unfold cnorm, csub. simpl. f_equal. ring. Qed.

Lemma cnorm_sub_self : forall a, cnorm (csub a a) = 0.
Proof.
  intro a. replace (csub a a) with (cofR 0) by (apply Cc_ext; unfold csub, cofR; simpl; ring).
  rewrite cnorm_cofR. apply Rabs_R0.
Qed.

Lemma cnorm_pos_ne : forall a b, a <> b -> 0 < cnorm (csub a b).
Proof.
  intros a b H. unfold cnorm. apply sqrt_lt_R0. apply (n2_pos (csub a b)).
  intro E. apply H. apply Cc_ext.
  - assert (cre (csub a b) = 0) by (rewrite E; reflexivity). unfold csub in H0; simpl in H0; lra.
  - assert (cim (csub a b) = 0) by (rewrite E; reflexivity). unfold csub in H0; simpl in H0; lra.
Qed.

Lemma cnorm_cofR_mul : forall x a, cnorm (cmul (cofR x) a) = Rabs x * cnorm a.
Proof.
  intros x a. unfold cnorm, cmul, cofR. simpl. rewrite <- sqrt_Rsqr_abs. unfold Rsqr.
  rewrite <- sqrt_mult_alt by nra. f_equal. ring.
Qed.

Lemma cpow_cofR : forall x n, cpow (cofR x) n = cofR (x ^ n).
Proof.
  intros x n. induction n as [|n IH]; simpl; [reflexivity|]. rewrite IH.
  apply Cc_ext; unfold cmul, cofR; simpl; ring.
Qed.

Lemma cinv_cofR : forall x, x <> 0 -> cinv (cofR x) = cofR (/ x).
Proof. intros x Hx. apply Cc_ext; unfold cinv, cofR; simpl; field; exact Hx. Qed.

Lemma cmul_one_r : forall a, cmul a (cofR 1) = a.
Proof. intro a. apply Cc_ext; unfold cmul, cofR; simpl; ring. Qed.

(* --- complex derivative (DeepStatements' CDerivWithin): local lemmas --- *)
Lemma CDW_ext_on : forall f g L S z, (forall w, S w -> f w = g w) -> f z = g z ->
  CDerivWithin f L S z -> CDerivWithin g L S z.
Proof.
  intros f g L S z Hfg Hz H e He. destruct (H e He) as [d [Hd Hw]]. exists d. split; [exact Hd|].
  intros w Sw H1 H2. rewrite <- (Hfg w Sw), <- Hz. apply Hw; assumption.
Qed.

Lemma CDW_loc : forall f g L S z d, 0 < d -> (forall w, cnorm (csub w z) < d -> f w = g w) ->
  CDerivWithin f L S z -> CDerivWithin g L S z.
Proof.
  intros f g L S z d0 Hd0 Hfg H e He. destruct (H e He) as [d [Hd Hw]].
  assert (Hz : f z = g z) by (apply Hfg; rewrite cnorm_sub_self; exact Hd0).
  exists (Rmin d d0). split; [apply Rmin_pos; assumption|].
  intros w Sw H1 H2. rewrite <- (Hfg w) by (eapply Rlt_le_trans; [exact H2|apply Rmin_r]).
  rewrite <- Hz. apply Hw; [exact Sw|exact H1|eapply Rlt_le_trans; [exact H2|apply Rmin_l]].
Qed.

Lemma CDW_mono : forall f L S S' z d, 0 < d -> (forall w, cnorm (csub w z) < d -> S' w -> S w) ->
  CDerivWithin f L S z -> CDerivWithin f L S' z.
Proof.
  intros f L S S' z d0 Hd0 HS H e He. destruct (H e He) as [d [Hd Hw]].
  exists (Rmin d d0). split; [apply Rmin_pos; assumption|].
  intros w Sw H1 H2. apply Hw; [apply HS; [eapply Rlt_le_trans; [exact H2|apply Rmin_r]|exact Sw]|exact H1|].
  eapply Rlt_le_trans; [exact H2|apply Rmin_l].
Qed.

Lemma CDW_univ : forall f L S z, CDerivWithin f L (fun _ => True) z -> CDerivWithin f L S z.
Proof.
  intros f L S z H. apply (CDW_mono f L (fun _ => True) S z 1); [lra|intros; exact I|exact H].
Qed.

Lemma CDW_fun_ext : forall f g L S z, (forall w, f w = g w) -> CDerivWithin f L S z -> CDerivWithin g L S z.
Proof.
  intros f g L S z H. replace g with f by (apply functional_extensionality; exact H). auto.
Qed.

(* uniqueness of the derivative on a set containing a ball: proved, not assumed *)
Lemma CDW_unique : forall f S L1 L2 z d, 0 < d -> (forall w, cnorm (csub w z) < d -> S w) ->
  CDerivWithin f L1 S z -> CDerivWithin f L2 S z -> L1 = L2.
Proof.
  intros f S L1 L2 z d Hd HS H1 H2.
  assert (Hn : forall e, 0 < e -> cnorm (csub L1 L2) < e).
  { intros e He. destruct (H1 (e / 2) ltac:(lra)) as [d1 [Hd1 K1]].
    destruct (H2 (e / 2) ltac:(lra)) as [d2 [Hd2 K2]].
    set (t := Rmin d (Rmin d1 d2) / 2).
    assert (Hmin : 0 < Rmin d (Rmin d1 d2)) by (apply Rmin_pos; [|apply Rmin_pos]; assumption).
    assert (Ht : 0 < t) by (unfold t; lra).
    assert (Htd : t < Rmin d (Rmin d1 d2)) by (unfold t; lra).
    set (w := mkC (cre z + t) (cim z)).
    assert (Ew : cnorm (csub w z) = t).
    { replace (csub w z) with (cofR t) by (apply Cc_ext; unfold w, csub, cofR; simpl; ring).
      rewrite cnorm_cofR. apply Rabs_right. lra. }
    assert (Hm1 : t < d) by (pose proof (Rmin_l d (Rmin d1 d2)); lra).
    assert (Hm2 : t < d1) by (pose proof (Rmin_r d (Rmin d1 d2)); pose proof (Rmin_l d1 d2); lra).
    assert (Hm3 : t < d2) by (pose proof (Rmin_r d (Rmin d1 d2)); pose proof (Rmin_r d1 d2); lra).
    assert (Sw : S w) by (apply HS; lra).
    set (q := cdiv (csub (f w) (f z)) (csub w z)).
    pose proof (K1 w Sw ltac:(lra) ltac:(lra)) as E1. pose proof (K2 w Sw ltac:(lra) ltac:(lra)) as E2.
    fold q in E1, E2. rewrite cnorm_sub_sym in E1.
    pose proof (cnorm_sub_tri L1 q L2). lra. }
  apply Cc_ext; apply close_eq; intros e He.
  - pose proof (cre_le_cnorm (csub L1 L2)) as C. pose proof (Hn e He). unfold csub in C at 1. simpl in C. lra.
  - pose proof (cim_le_cnorm (csub L1 L2)) as C. pose proof (Hn e He). unfold csub in C at 1. simpl in C. lra.
Qed.
Lemma CDW_add : forall f g L1 L2 S z, CDerivWithin f L1 S z -> CDerivWithin g L2 S z ->
  CDerivWithin (fun w => cadd (f w) (g w)) (cadd L1 L2) S z.
Proof.
  intros f g L1 L2 S z H1 H2 e He.
  destruct (H1 (e / 2) ltac:(lra)) as [d1 [Hd1 K1]]. destruct (H2 (e / 2) ltac:(lra)) as [d2 [Hd2 K2]].
  exists (Rmin d1 d2). split; [apply Rmin_pos; assumption|]. intros w Sw P1 P2.
  pose proof (K1 w Sw P1 ltac:(pose proof (Rmin_l d1 d2); lra)) as E1.
  pose proof (K2 w Sw P1 ltac:(pose proof (Rmin_r d1 d2); lra)) as E2.
  set (Y := cinv (csub w z)) in *. unfold cdiv in *. fold Y in E1, E2 |- *.
  replace (csub (cmul (csub (cadd (f w) (g w)) (cadd (f z) (g z))) Y) (cadd L1 L2))
    with (cadd (csub (cmul (csub (f w) (f z)) Y) L1) (csub (cmul (csub (g w) (g z)) Y) L2))
    by (apply Cc_ext; unfold cadd, csub, cmul; simpl; ring).
  pose proof (cnorm_triangle (csub (cmul (csub (f w) (f z)) Y) L1) (csub (cmul (csub (g w) (g z)) Y) L2)). lra.
Qed.

Lemma CDW_sub : forall f g L1 L2 S z, CDerivWithin f L1 S z -> CDerivWithin g L2 S z ->
  CDerivWithin (fun w => csub (f w) (g w)) (csub L1 L2) S z.
Proof.
  intros f g L1 L2 S z H1 H2.
  assert (H2' : CDerivWithin (fun w => cmul (cofR (-1)) (g w)) (cmul (cofR (-1)) L2) S z).
  { intros e He. destruct (H2 e He) as [d [Hd K]]. exists d. split; [exact Hd|]. intros w Sw P1 P2.
    pose proof (K w Sw P1 P2) as E. unfold cdiv in *. set (Y := cinv (csub w z)) in *.
    replace (csub (cmul (csub (cmul (cofR (-1)) (g w)) (cmul (cofR (-1)) (g z))) Y) (cmul (cofR (-1)) L2))
      with (cmul (cofR (-1)) (csub (cmul (csub (g w) (g z)) Y) L2))
      by (apply Cc_ext; unfold cadd, csub, cmul, cofR; simpl; ring).
    rewrite cnorm_cofR_mul. replace (Rabs (-1)) with 1 by (rewrite Rabs_left; lra). lra. }
  pose proof (CDW_add f _ L1 _ S z H1 H2') as H.
  replace (csub L1 L2) with (cadd L1 (cmul (cofR (-1)) L2)) by (apply Cc_ext; unfold cadd, csub, cmul, cofR; simpl; ring).
  apply (CDW_fun_ext (fun w => cadd (f w) (cmul (cofR (-1)) (g w)))); [|exact H].
  intro w. apply Cc_ext; unfold cadd, csub, cmul, cofR; simpl; ring.
Qed.

Lemma avoid_pt : forall w rho v, w <> rho -> cnorm (csub v w) < cnorm (csub w rho) -> v <> rho.
Proof. intros w rho v Hw Hv E. subst v. rewrite cnorm_sub_sym in Hv. lra. Qed.

Lemma neg1_pow_cases : forall k, (-1) ^ k = 1 \/ (-1) ^ k = -1.
Proof. induction k as [|k [IH|IH]]; simpl; [left; ring|right; rewrite IH; ring|left; rewrite IH; ring]. Qed.


(* ===================================================================== *)
(* Part 1: iteratedDeriv_laplace                                          *)
(* ===================================================================== *)
Lemma ball_re : forall s d z, ball s d z -> cre s - d < cre z.
Proof.
  intros s d z H. unfold ball in H. pose proof (cre_le_cnorm (csub z s)) as E.
  unfold csub in E at 1. simpl in E. apply abs_le_elim in E. lra.
Qed.

Lemma neg_mul_cofR : forall w u, cmul (csub (cofR 0) w) (cofR u) = mkC (- cre w * u) (- (cim w * u)).
Proof. intros. apply Cc_ext; unfold cmul, csub, cofR; simpl; ring. Qed.

(* IteratedDerivLaplace.lean : iteratedDeriv_laplace_int : l.9
   int_(0,oo) u^n e^(-b u) du converges, for b > 0 (proved, from the kernel
   antiderivative of CleanIntegralQED / AlpogeFifthBatch kernel_tail) *)
Lemma iteratedDeriv_laplace_int_r : forall n b, 0 < b ->
  exists I, RIntInf (fun u => u ^ n * exp (- b * u)) 0 I.
Proof.
  intros n b Hb. destruct (kernel_tail n b 0 Hb (Rle_refl 0)) as [Ht _].
  exists (INR (fact n) * - Gk n b 0).
  apply (RIntInf_ext (fun u => INR (fact n) * gk n b u)); [|apply RIntInf_scal; exact Ht].
  intros u _. unfold gk. replace (- (b * u)) with (- b * u) by ring.
  field. apply INR_fact_neq_0.
Qed.

Section IterLaplace.
Variable g : R -> R.
(* Lean hg : Measurable g, as local Riemann integrability (AlpogeDeepStatements LocInt).
   IteratedDerivLaplace.lean : iteratedDeriv_laplace_meas : l.16 (fun_prop
   measurability of the integrands) is subsumed: hg is the premise of INTV/DOM. *)
Hypothesis hg : LocInt g.
Variable C : R.
Hypothesis hgC : forall u, 0 <= u -> Rabs (g u) <= C * exp (2 * u).

(* the integrand  g u (-u)^k e^(-z u)  as (re, im) -- exactly the integrands
   of AlpogeFifthBatch's hypothesis ILAP *)
Definition Fk (k : nat) (z : Cc) (u : R) : Cc :=
  mkC (g u * (- u) ^ k * exp (- cre z * u) * cos (cim z * u))
      (- (g u * (- u) ^ k * exp (- cre z * u) * sin (cim z * u))).

(* Ik k z = int_(0,oo) g u (-u)^k e^(-z u) du  (the Bochner integral; Lean's
   fun z => int g u e^(-z u) is Ik 0, since (-u)^0 = 1) *)
Variable Ik : nat -> Cc -> Cc.

(* [Mathlib] Integrable.mono' + MeasureTheory.intervalIntegral_tendsto_integral_Ioi:
   an integrand dominated by an integrable bound is integrable on (0, oo), and
   its integral is the limit of its integrals over [0, T]. *)
Hypothesis INTV : LocInt g -> forall k s,
  (exists B, (forall u, 0 < u -> cnorm (Fk k s u) <= B u) /\ exists IB, RIntInf B 0 IB) ->
  CIntInf (fun u => cre (Fk k s u)) (fun u => cim (Fk k s u)) 0 (Ik k s).

(* [Mathlib] hasDerivAt_integral_of_dominated_loc_of_deriv_le, with
   F z u = Fk k z u, F' z u = Fk (k+1) z u on the ball of radius d about s:
   F s integrable (hF_int), |F' z u| <= B u (h_bound), B integrable
   (bound_integrable), d/dz F z u = F' z u (h_diff)  ==>  HasDerivAt. *)
Hypothesis DOM : LocInt g -> forall k s d (B : R -> R), 0 < d ->
  (exists B0, (forall u, 0 < u -> cnorm (Fk k s u) <= B0 u) /\ exists I0, RIntInf B0 0 I0) ->
  (forall z u, ball s d z -> 0 < u -> cnorm (Fk (S k) z u) <= B u) ->
  (exists IB, RIntInf B 0 IB) ->
  (forall z u, ball s d z -> 0 < u -> CDerivWithin (fun w => Fk k w u) (Fk (S k) z u) (fun _ => True) z) ->
  CDerivWithin (Ik k) (Ik (S k) s) (fun _ => True) s.

(* [Mathlib] HasDerivAt.cexp, HasDerivAt.const_mul (hasDerivAt_id'.neg.mul_const):
   d/dw  A e^(-w u)  =  A (e^(-z u) (-u))  at z *)
Hypothesis CEXPD : forall (A : Cc) (u : R) (z : Cc),
  CDerivWithin (fun w => cmul A (cexp (cmul (csub (cofR 0) w) (cofR u))))
               (cmul A (cmul (cexp (cmul (csub (cofR 0) z) (cofR u))) (cofR (- u)))) (fun _ => True) z.

(* IteratedDerivLaplace.lean : iteratedDeriv_laplace_bound : l.22
   |g u (-u)^k e^(-z u)| <= C u^k e^(-b u)  when 2 + b <= Re z, u > 0 *)
Lemma iteratedDeriv_laplace_bound_r : forall k b z u, 2 + b <= cre z -> 0 < u ->
  cnorm (Fk k z u) <= C * (u ^ k * exp (- b * u)).
Proof.
  intros k b z u Hz Hu.
  set (P := g u * (- u) ^ k * exp (- cre z * u)).
  pose proof (hgC u ltac:(lra)) as Hg. pose proof (exp_pos (2 * u)) as E2.
  pose proof (exp_pos (- cre z * u)) as Ez. pose proof (exp_pos (- b * u)) as Eb.
  assert (HC : 0 <= C).
  { pose proof (Rabs_pos (g u)) as Ha. destruct (Rle_or_lt 0 C) as [H|H]; [exact H|nra]. }
  assert (Huk : 0 <= u ^ k) by (apply pow_le; lra).
  assert (HM : 0 <= C * (u ^ k * exp (- b * u))) by (apply Rmult_le_pos; [exact HC|nra]).
  (* |P| <= C e^(2u) u^k e^(-Re z u) <= C u^k e^(-b u) *)
  assert (HP : Rabs P <= C * (u ^ k * exp (- b * u))).
  { unfold P. rewrite !Rabs_mult, <- RPow_abs, Rabs_Ropp, (Rabs_right u) by lra.
    rewrite (Rabs_right (exp (- cre z * u))) by lra.
    assert (Ex : exp (2 * u) * exp (- cre z * u) <= exp (- b * u)).
    { rewrite <- exp_plus. apply exp_le_mono. nra. }
    pose proof (Rabs_pos (g u)).
    assert (Rabs (g u) * u ^ k * exp (- cre z * u) <= C * exp (2 * u) * u ^ k * exp (- cre z * u)).
    { apply Rmult_le_compat_r; [lra|]. apply Rmult_le_compat_r; [exact Huk|exact Hg]. }
    assert (C * exp (2 * u) * u ^ k * exp (- cre z * u) = C * u ^ k * (exp (2 * u) * exp (- cre z * u))) by ring.
    assert (C * u ^ k * (exp (2 * u) * exp (- cre z * u)) <= C * u ^ k * exp (- b * u))
      by (apply Rmult_le_compat_l; [nra|exact Ex]).
    nra. }
  apply cnorm_le_sq; [exact HM|].
  assert (En : n2 (Fk k z u) = P * P).
  { unfold n2, Fk. simpl. fold P. pose proof (sin2_cos2 (cim z * u)) as S2. unfold Rsqr in S2.
    transitivity (P * P * (sin (cim z * u) * sin (cim z * u) + cos (cim z * u) * cos (cim z * u))); [ring|].
    rewrite S2. ring. }
  rewrite En. pose proof (Rabs_pos P). pose proof (Rsqr_abs P) as SA. unfold Rsqr in SA.
  rewrite SA. nra.
Qed.

Lemma Fk_cexp : forall k w u,
  Fk k w u = cmul (cofR (g u * (- u) ^ k)) (cexp (cmul (csub (cofR 0) w) (cofR u))).
Proof.
  intros k w u. rewrite neg_mul_cofR. unfold cexp. simpl. rewrite cos_neg, sin_neg.
  apply Cc_ext; unfold Fk, cmul, cofR; simpl; ring.
Qed.

(* the pointwise derivative step (h1, h2, congr_deriv + ring of the Lean proof) *)
Lemma laplace_integrand_deriv : forall k z u,
  CDerivWithin (fun w => Fk k w u) (Fk (S k) z u) (fun _ => True) z.
Proof.
  intros k z u. pose proof (CEXPD (cofR (g u * (- u) ^ k)) u z) as H.
  apply (CDW_fun_ext _ (fun w => Fk k w u)) in H; [|intro w; symmetry; apply Fk_cexp].
  assert (E : cmul (cofR (g u * (- u) ^ k)) (cmul (cexp (cmul (csub (cofR 0) z) (cofR u))) (cofR (- u)))
              = Fk (S k) z u).
  { rewrite (Fk_cexp (S k) z u). generalize (cexp (cmul (csub (cofR 0) z) (cofR u))) as E. intro E.
    apply Cc_ext; unfold cmul, cofR; simpl; ring. }
  rewrite E in H. exact H.
Qed.

(* IteratedDerivLaplace.lean : iteratedDeriv_laplace_hasDerivAt : l.48 *)
Theorem iteratedDeriv_laplace_hasDerivAt_r : forall k s, 2 < cre s ->
  CDerivWithin (Ik k) (Ik (S k) s) (fun _ => True) s.
Proof.
  intros k s Hs. set (d := (cre s - 2) / 2).
  assert (Hd : 0 < d) by (unfold d; lra).
  assert (Hre : forall z, ball s d z -> 2 + d <= cre z) by (intros z Hz; apply ball_re in Hz; unfold d in *; lra).
  assert (Bs : ball s d s) by (unfold ball; rewrite cnorm_sub_self; exact Hd).
  destruct (iteratedDeriv_laplace_int_r k d Hd) as [I0 HI0].
  destruct (iteratedDeriv_laplace_int_r (S k) d Hd) as [I1 HI1].
  apply (DOM hg k s d (fun u => C * (u ^ S k * exp (- d * u))) Hd).
  - (* hint: F s is integrable *)
    exists (fun u => C * (u ^ k * exp (- d * u))). split.
    + intros u Hu. apply iteratedDeriv_laplace_bound_r; [apply Hre; exact Bs|exact Hu].
    + exists (C * I0). apply RIntInf_scal. exact HI0.
  - intros z u Hz Hu. apply iteratedDeriv_laplace_bound_r; [apply Hre; exact Hz|exact Hu].
  - exists (C * I1). apply RIntInf_scal. exact HI1.
  - intros z u _ _. apply laplace_integrand_deriv.
Qed.

(* the family (Ik k)_k is the family of iterated derivatives of Ik 0 on Re > 2 *)
Theorem iteratedDeriv_laplace_exists : IterDerivs (Ik 0) (fun z => 2 < cre z) Ik.
Proof.
  split; [reflexivity|]. intros k z Hz. apply CDW_univ. apply iteratedDeriv_laplace_hasDerivAt_r. exact Hz.
Qed.

(* IteratedDerivLaplace.lean : iteratedDeriv_laplace : l.84
   (with Phi = Ik 0 on Re > 2, as PoleData.laplace supplies it in landau_coeff;
   Phi := Ik 0 is the literal Lean statement, iteratedDeriv_laplace_lean) *)
Theorem iteratedDeriv_laplace_r : forall (Phi : Cc -> Cc) (D : nat -> Cc -> Cc),
  (forall z, 2 < cre z -> Phi z = Ik 0 z) ->
  IterDerivs Phi (fun z => 2 < cre z) D ->
  forall k s, 2 < cre s -> D k s = Ik k s.
Proof.
  intros Phi D HPhi [H0 HS] k. induction k as [|k IH]; intros s Hs.
  - rewrite (H0 s Hs). apply HPhi. exact Hs.
  - (* iteratedDeriv_succ; EventuallyEq.deriv_eq on the open set Re > 2; HasDerivAt.deriv *)
    apply (CDW_unique (D k) (fun z => 2 < cre z) _ _ s (cre s - 2)); [lra| |exact (HS k s Hs)|].
    + intros w Hw. apply ball_re in Hw. lra.
    + apply (CDW_ext_on (Ik k)); [intros w Hw; symmetry; apply IH; exact Hw|symmetry; apply IH; exact Hs|].
      apply CDW_univ. apply iteratedDeriv_laplace_hasDerivAt_r. exact Hs.
Qed.

Corollary iteratedDeriv_laplace_lean : forall D : nat -> Cc -> Cc,
  IterDerivs (Ik 0) (fun z => 2 < cre z) D -> forall k s, 2 < cre s -> D k s = Ik k s.
Proof. intros D HD. apply (iteratedDeriv_laplace_r (Ik 0) D); [reflexivity|exact HD]. Qed.

(* the shape of AlpogeFifthBatch's hypothesis ILAP, produced *)
Theorem iteratedDeriv_laplace_ILAP : forall (Phi : Cc -> Cc) (D : nat -> Cc -> Cc),
  (forall z, 2 < cre z -> Phi z = Ik 0 z) ->
  IterDerivs Phi (fun z => 2 < cre z) D ->
  forall (k : nat) s, 2 < cre s ->
  CIntInf (fun u => g u * (- u) ^ k * exp (- cre s * u) * cos (cim s * u))
          (fun u => - (g u * (- u) ^ k * exp (- cre s * u) * sin (cim s * u))) 0 (D k s).
Proof.
  intros Phi D HPhi HD k s Hs. rewrite (iteratedDeriv_laplace_r Phi D HPhi HD k s Hs).
  set (d := (cre s - 2) / 2). assert (Hd : 0 < d) by (unfold d; lra).
  destruct (iteratedDeriv_laplace_int_r k d Hd) as [I0 HI0].
  apply (INTV hg k s). exists (fun u => C * (u ^ k * exp (- d * u))). split.
  - intros u Hu. apply iteratedDeriv_laplace_bound_r; [unfold d; lra|exact Hu].
  - exists (C * I0). apply RIntInf_scal. exact HI0.
Qed.

(* ... which is exactly what AlpogeFifthBatch.landau_coeff consumes *)
Corollary landau_coeff_of_iteratedDeriv_laplace : forall (Phi : Cc -> Cc) (D : nat -> Cc -> Cc),
  (forall z, 2 < cre z -> Phi z = Ik 0 z) ->
  IterDerivs Phi (fun z => 2 < cre z) D ->
  forall (k : nat) s, 2 < cre s ->
  CIntInf (fun u => g u * u ^ k * exp (- cre s * u) * cos (cim s * u) / INR (fact k))
          (fun u => - (g u * u ^ k * exp (- cre s * u) * sin (cim s * u)) / INR (fact k)) 0
          (mkC ((-1) ^ k * cre (D k s) / INR (fact k)) ((-1) ^ k * cim (D k s) / INR (fact k))).
Proof.
  intros Phi D HPhi HD. exact (landau_coeff g D (iteratedDeriv_laplace_ILAP Phi D HPhi HD)).
Qed.
End IterLaplace.

Print Assumptions iteratedDeriv_laplace_bound_r.
Print Assumptions iteratedDeriv_laplace_hasDerivAt_r.
Print Assumptions iteratedDeriv_laplace_r.
Print Assumptions iteratedDeriv_laplace_lean.
Print Assumptions iteratedDeriv_laplace_ILAP.
Print Assumptions landau_coeff_of_iteratedDeriv_laplace.

(* ===================================================================== *)
(* Part 2: landau_finite                                                  *)
(* ===================================================================== *)
(* LandauFinite.lean : landau_finite : l.9 *)
Section LandauFinite.
(* [Mathlib] isCompact_closedBall + IsCompact.elim_nhds_subcover: if every
   point w of the closed ball K = closedBall z r has a neighbourhood U w,
   finitely many of them, at points of K, cover K. *)
Hypothesis COMPACT : forall (z : Cc) (r : R) (U : Cc -> Cc -> Prop),
  (forall w, cnorm (csub w z) <= r -> exists d, 0 < d /\ forall v, cnorm (csub v w) < d -> U w v) ->
  exists t : list Cc, (forall w, In w t -> cnorm (csub w z) <= r) /\
    forall v, cnorm (csub v z) <= r -> exists w, In w t /\ U w v.

(* (Z cap closedBall z r).Finite: every such point is in one finite list *)
Theorem landau_finite_r : forall (Z : Cc -> Prop) (z : Cc) (r : R),
  (forall w, 0 < cre w -> EvPunct w (fun v => ~ Z v)) ->
  r < cre z ->
  exists l : list Cc, forall v, Z v -> cnorm (csub v z) <= r -> In v l.
Proof.
  intros Z z r Hiso Hr.
  (* hpos : points of the closed ball have positive real part *)
  assert (Hpos : forall w, cnorm (csub w z) <= r -> 0 < cre w).
  { intros w Hw. pose proof (cre_le_cnorm (csub w z)) as H. unfold csub in H at 1. simpl in H.
    apply abs_le_elim in H. destruct H as [H _]. lra. }
  (* the neighbourhoods {v | v <> w -> v notin Z} (eventually_nhdsWithin_iff) *)
  destruct (COMPACT z r (fun w v => v <> w -> ~ Z v)) as [t [_ Ht]].
  { intros w Hw. destruct (Hiso w (Hpos w Hw)) as [d [Hd Hev]]. exists d. split; [exact Hd|].
    intros v Hv Hne. apply Hev; [apply cnorm_pos_ne; exact Hne|exact Hv]. }
  exists t. intros v HvZ HvK. destruct (Ht v HvK) as [w [Hw Hvw]].
  destruct (Cc_eq_dec v w) as [E|N].
  - subst. exact Hw.
  - exfalso. exact (Hvw N HvZ).
Qed.
End LandauFinite.

Print Assumptions landau_finite_r.

(* ===================================================================== *)
(* Part 3: landau_pole_asym_deriv and landau_pole_asym                    *)
(* ===================================================================== *)
Section PoleAsym.
(* [Mathlib] hasDerivAt_zpow, HasDerivAt.comp_sub_const, HasDerivAt.const_mul:
   for s <> rho,  d/ds a (s - rho)^-n = a (-n) (s - rho)^-(n+1). *)
Hypothesis DZPOW : forall (a rho w : Cc) (n : nat), w <> rho ->
  CDerivWithin (fun s => cmul a (cinv (cpow (csub s rho) n)))
               (cmul a (cmul (cofR (- INR n)) (cinv (cpow (csub w rho) (S n))))) (fun _ => True) w.

(* the k-th derivative of c (s - rho)^-1, in closed form *)
Definition PoleK (c rho : Cc) (j : nat) (w : Cc) : Cc :=
  cmul (cmul c (cofR ((-1) ^ j * INR (fact j)))) (cinv (cpow (csub w rho) (S j))).

(* the sign/factorial step: (-1)^j j! * (-(j+1)) = (-1)^(j+1) (j+1)! *)
Lemma PoleK_deriv : forall c rho j w, w <> rho ->
  CDerivWithin (PoleK c rho j) (PoleK c rho (S j) w) (fun _ => True) w.
Proof.
  intros c rho j w Hw. pose proof (DZPOW (cmul c (cofR ((-1) ^ j * INR (fact j)))) rho w (S j) Hw) as H.
  assert (E : cmul (cmul c (cofR ((-1) ^ j * INR (fact j))))
                   (cmul (cofR (- INR (S j))) (cinv (cpow (csub w rho) (S (S j)))))
              = PoleK c rho (S j) w).
  { unfold PoleK. generalize (cinv (cpow (csub w rho) (S (S j)))) as Y. intro Y.
    rewrite fact_simpl, mult_INR, S_INR.
    apply Cc_ext; unfold cmul, cofR; simpl; ring. }
  rewrite E in H. exact H.
Qed.

Lemma PoleK_0 : forall c rho w, PoleK c rho 0 w = cmul c (cinv (csub w rho)).
Proof.
  intros c rho w. unfold PoleK. simpl cpow. rewrite cmul_one_r.
  generalize (cinv (csub w rho)) as Y. intro Y. apply Cc_ext; unfold cmul, cofR; simpl; ring.
Qed.

(* LandauPoleAsym.lean : landau_pole_asym_deriv : l.10 *)
Theorem landau_pole_asym_deriv_r : landau_pole_asym_deriv_statement.
Proof.
  intros c rho z k D Hz [H0 HS].
  assert (Key : forall j w, w <> rho -> D j w = PoleK c rho j w).
  { induction j as [|j IH]; intros w Hw.
    - rewrite (H0 w Hw). rewrite PoleK_0. reflexivity.
    - apply (CDW_unique (D j) (fun s => s <> rho) _ _ w (cnorm (csub w rho))).
      + apply cnorm_pos_ne. exact Hw.
      + intros v Hv. exact (avoid_pt w rho v Hw Hv).
      + exact (HS j w Hw).
      + apply (CDW_ext_on (PoleK c rho j)); [intros v Hv; symmetry; apply IH; exact Hv|symmetry; apply IH; exact Hw|].
        apply CDW_univ. apply PoleK_deriv. exact Hw. }
  rewrite (Key k z Hz). unfold PoleK. rewrite cpow_cofR.
  generalize (cinv (cpow (csub z rho) (S k))) as Y. intro Y. apply Cc_ext; unfold cmul, cofR; simpl; ring.
Qed.

(* [Mathlib] AnalyticAt.differentiableAt *)
Hypothesis ANDIFF : forall h rho, CAnalyticAt h rho -> exists L, CDerivWithin h L (fun _ => True) rho.
(* [Mathlib] DifferentiableOn.contDiffOn on an open set (a holomorphic function
   on the ball has iterated derivatives there; iteratedDeriv on the open ball) *)
Hypothesis HOLITER : forall G z r, CDifferentiableOn G (ball z r) -> exists DG, IterDerivs G (ball z r) DG.
(* [inventory] landau_cauchy (LandauCauchy.lean): Cauchy estimates on the ball *)
Hypothesis CAUCHY : forall G DG z r r', CDifferentiableOn G (ball z r) -> IterDerivs G (ball z r) DG ->
  0 < r' -> r' < r -> exists M, forall k, cnorm (cdiv (DG k z) (cofR (INR (fact k)))) <= M / r' ^ k.

(* the final algebra: (-1)^k (iG + c (-1)^k k! X^-1) / k! - c / X = (-1)^k (iG / k!) *)
Lemma pole_asym_algebra : forall (s f : R) (A c Y : Cc), (s = 1 \/ s = -1) -> f <> 0 ->
  csub (cmul (cmul (cofR s) (cadd A (cmul (cmul c (cofR (s * f))) Y))) (cofR (/ f))) (cmul c Y)
  = cmul (cofR s) (cmul A (cofR (/ f))).
Proof.
  intros s f A c Y Hs Hf. destruct Hs as [Hs|Hs]; subst s;
    apply Cc_ext; unfold cmul, cadd, csub, cofR; simpl; field; exact Hf.
Qed.

(* LandauPoleAsym.lean : landau_pole_asym : l.19 *)
Theorem landau_pole_asym_r : landau_pole_asym_statement.
Proof.
  intros Phi z rho c r r' Hrho Hne Hd [h [Han Hev]] Hr0 Hr1 D [HD0 HDS].
  (* G := Phi - c/(s - rho), patched by h rho at rho *)
  set (G := fun s => if Cc_eq_dec s rho then h rho else csub (Phi s) (cdiv c (csub s rho))).
  destruct Hev as [d0 [Hd0 Hev]].
  (* hGeq : G = h near rho *)
  assert (HGeq : forall s, cnorm (csub s rho) < d0 -> G s = h s).
  { intros s Hs. unfold G. destruct (Cc_eq_dec s rho) as [E|N]; [subst; reflexivity|].
    rewrite (Hev s (cnorm_pos_ne s rho N) Hs). apply Cc_ext; unfold csub, cadd; simpl; ring. }
  (* hGd : G is differentiable on the whole ball *)
  assert (HGd : CDifferentiableOn G (ball z r)).
  { intros s Hs. destruct (Cc_eq_dec s rho) as [E|N].
    - subst s. destruct (ANDIFF h rho Han) as [L HL]. exists L. apply CDW_univ.
      apply (CDW_loc h G L _ rho d0 Hd0); [intros w Hw; symmetry; apply HGeq; exact Hw|exact HL].
    - destruct (Hd s (conj Hs N)) as [L HL].
      pose proof (DZPOW c rho s 1 N) as HP.
      apply (CDW_fun_ext _ (fun w => cdiv c (csub w rho))) in HP;
        [|intro w; unfold cdiv; simpl cpow; rewrite cmul_one_r; reflexivity].
      pose proof (CDW_sub Phi _ L _ _ s HL (CDW_univ _ _ _ _ HP)) as HS.
      eexists.
      apply (CDW_mono G _ (fun w => ball z r w /\ w <> rho) (ball z r) s (cnorm (csub s rho)));
        [apply cnorm_pos_ne; exact N|intros w Hw Bw; split; [exact Bw|exact (avoid_pt s rho w N Hw)]|].
      apply (CDW_ext_on (fun w => csub (Phi w) (cdiv c (csub w rho)))); [| |exact HS].
      + intros w [_ Nw]. unfold G. destruct (Cc_eq_dec w rho); [contradiction|reflexivity].
      + unfold G. destruct (Cc_eq_dec s rho); [contradiction|reflexivity]. }
  destruct (HOLITER G z r HGd) as [DG [HG0 HGS]].
  destruct (CAUCHY G DG z r r' HGd (conj HG0 HGS) Hr0 Hr1) as [M HM].
  exists M. intro k.
  (* the punctured ball is open *)
  assert (Hopen : forall w, ball z r w -> w <> rho -> exists d, 0 < d /\
            forall v, cnorm (csub v w) < d -> ball z r v /\ v <> rho).
  { intros w Bw Nw. unfold ball in Bw.
    exists (Rmin (r - cnorm (csub w z)) (cnorm (csub w rho))).
    split; [apply Rmin_pos; [lra|apply cnorm_pos_ne; exact Nw]|].
    intros v Hv. pose proof (Rmin_l (r - cnorm (csub w z)) (cnorm (csub w rho))).
    pose proof (Rmin_r (r - cnorm (csub w z)) (cnorm (csub w rho))). split.
    - unfold ball. pose proof (cnorm_sub_tri v w z). lra.
    - apply (avoid_pt w rho v Nw). lra. }
  (* Phi = G + c (s - rho)^-1 near z, so its derivatives split (iteratedDeriv_add) *)
  assert (Key : forall j w, ball z r w -> w <> rho -> D j w = cadd (DG j w) (PoleK c rho j w)).
  { induction j as [|j IH]; intros w Bw Nw.
    - rewrite (HD0 w (conj Bw Nw)), (HG0 w Bw), PoleK_0. unfold G.
      destruct (Cc_eq_dec w rho); [contradiction|]. unfold cdiv.
      apply Cc_ext; unfold csub, cadd; simpl; ring.
    - destruct (Hopen w Bw Nw) as [d [Hdd HU]].
      apply (CDW_unique (D j) (fun v => ball z r v /\ v <> rho) _ _ w d Hdd HU).
      + exact (HDS j w (conj Bw Nw)).
      + apply (CDW_ext_on (fun v => cadd (DG j v) (PoleK c rho j v)));
          [intros v [Bv Nv]; symmetry; apply IH; assumption|symmetry; apply IH; assumption|].
        apply CDW_add.
        * apply (CDW_mono _ _ (ball z r) _ w 1); [lra|intros v _ [Bv _]; exact Bv|apply HGS; exact Bw].
        * apply CDW_univ. apply PoleK_deriv. exact Nw. }
  assert (Bz : ball z r z) by (unfold ball; rewrite cnorm_sub_self; lra).
  assert (Nz : z <> rho) by (intro E; apply Hne; symmetry; exact E).
  assert (Hf : INR (fact k) <> 0) by apply INR_fact_neq_0.
  specialize (HM k). rewrite (Key k z Bz Nz). unfold cdiv, PoleK in *.
  rewrite cinv_cofR in HM |- * by exact Hf. rewrite cpow_cofR.
  rewrite (pole_asym_algebra _ _ _ _ _ (neg1_pow_cases k) Hf).
  rewrite cnorm_cofR_mul, pow_1_abs, Rmult_1_l. exact HM.
Qed.
End PoleAsym.

Print Assumptions landau_pole_asym_deriv_r.
Print Assumptions landau_pole_asym_r.

(* ===================================================================== *)
(* Part 4: poleData (assembly from poleData_char over the characters)     *)
(* ===================================================================== *)
Fixpoint lsumR (l : list R) : R := match l with [] => 0 | v :: t => v + lsumR t end.
Fixpoint lsumC (l : list Cc) : Cc := match l with [] => cofR 0 | v :: t => cadd v (lsumC t) end.

(* finite choice over an enumerated finite type with decidable equality
   (Lean's `choose` over the Fintype F.iota) *)
Lemma fin_choice : forall (A B : Type) (dec : forall x y : A, {x = y} + {x <> y}) (b0 : B)
  (P : A -> B -> Prop) (l : list A),
  (forall x, In x l -> exists y, P x y) -> exists f : A -> B, forall x, In x l -> P x (f x).
Proof.
  intros A B dec b0 P l. induction l as [|x l IH]; intros H.
  - exists (fun _ => b0). intros y [].
  - destruct (H x (or_introl eq_refl)) as [bx Hx].
    destruct IH as [f Hf]; [intros y Hy; apply H; right; exact Hy|].
    exists (fun y => if dec y x then bx else f y). intros y [E|Hy].
    + subst y. destruct (dec x x) as [_|N]; [exact Hx|contradiction].
    + destruct (dec y x) as [E|_]; [subst y; exact Hx|apply Hf; exact Hy].
Qed.

Lemma lsumC_map_ext : forall {A} (f h : A -> Cc) l, (forall x, In x l -> f x = h x) ->
  lsumC (map f l) = lsumC (map h l).
Proof.
  intros A f h l H. induction l as [|x l IH]; simpl; [reflexivity|].
  rewrite (H x (or_introl eq_refl)), IH; [reflexivity|]. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma lsumR_single_le : forall {A} (f : A -> R) l x0, (forall x, In x l -> 0 <= f x) -> In x0 l ->
  f x0 <= lsumR (map f l).
Proof.
  intros A f l x0 Hnn Hin. induction l as [|x l IH]; [destruct Hin|]. simpl.
  assert (Hr : 0 <= lsumR (map f l)).
  { clear IH Hin. induction l as [|y l IHl]; simpl; [lra|].
    pose proof (Hnn y (or_intror (or_introl eq_refl))).
    assert (0 <= lsumR (map f l)) by (apply IHl; intros z [Ez|Hz]; apply Hnn; [left; exact Ez|right; right; exact Hz]). lra. }
  destruct Hin as [E|Hin].
  - subst. lra.
  - pose proof (Hnn x (or_introl eq_refl)). assert (f x0 <= lsumR (map f l)) by (apply IH; [intros y Hy; apply Hnn; right; exact Hy|exact Hin]). lra.
Qed.

Lemma cmul_assoc : forall a b c, cmul (cmul a b) c = cmul a (cmul b c).
Proof. intros. apply Cc_ext; unfold cmul; simpl; ring. Qed.

Lemma cdiv_cmul_assoc : forall a b c, cdiv (cmul a b) c = cmul a (cdiv b c).
Proof. intros. unfold cdiv. apply cmul_assoc. Qed.

Lemma cmul_cofR : forall x y, cmul (cofR x) (cofR y) = cofR (x * y).
Proof. intros. apply Cc_ext; unfold cmul, cofR; simpl; ring. Qed.

Lemma csub_cofR : forall x y, csub (cofR x) (cofR y) = cofR (x - y).
Proof. intros. apply Cc_ext; unfold csub, cofR; simpl; ring. Qed.

Lemma n2_cmul : forall a b, n2 (cmul a b) = n2 a * n2 b.
Proof. intros. unfold n2, cmul. simpl. ring. Qed.

Lemma n2_cinv : forall a, 0 < n2 a -> n2 (cinv a) = / n2 a.
Proof. intros a H. unfold n2 in *. unfold cinv. simpl. field. lra. Qed.

Lemma n2_zero : n2 (cofR 0) = 0.
Proof. unfold n2, cofR. simpl. ring. Qed.

(* --- EvPunct: finite intersections --- *)
Lemma EvPunct_and : forall z P Q, EvPunct z P -> EvPunct z Q -> EvPunct z (fun w => P w /\ Q w).
Proof.
  intros z P Q [d1 [H1 K1]] [d2 [H2 K2]]. exists (Rmin d1 d2). split; [apply Rmin_pos; assumption|].
  intros s A B. split; [apply K1|apply K2]; try exact A.
  - pose proof (Rmin_l d1 d2); lra.
  - pose proof (Rmin_r d1 d2); lra.
Qed.

Lemma EvPunct_all : forall {A} (P : A -> Cc -> Prop) z l, (forall x, In x l -> EvPunct z (P x)) ->
  EvPunct z (fun w => forall x, In x l -> P x w).
Proof.
  intros A P z l. induction l as [|x l IH]; intros H.
  - exists 1. split; [lra|]. intros s _ _ y [].
  - destruct (EvPunct_and z (P x) (fun w => forall y, In y l -> P y w) (H x (or_introl eq_refl)))
      as [d [Hd K]]; [apply IH; intros y Hy; apply H; right; exact Hy|].
    exists d. split; [exact Hd|]. intros s A1 A2 y [E|Hy]; destruct (K s A1 A2) as [K1 K2];
      [subst; exact K1|exact (K2 y Hy)].
Qed.

(* the zero function is analytic (a power series with zero coefficients) *)
Lemma psum_zero : forall rho w n, psum (fun _ => cofR 0) rho w n = cofR 0.
Proof.
  intros rho w n. induction n as [|n IH]; simpl.
  - apply Cc_ext; unfold cmul, cofR; simpl; ring.
  - rewrite IH. apply Cc_ext; unfold cadd, cmul, cofR; simpl; ring.
Qed.

Lemma CAnalyticAt_zero : forall rho, CAnalyticAt (fun _ => cofR 0) rho.
Proof.
  intro rho. exists 1, (fun _ => cofR 0). split; [lra|]. intros w _.
  assert (E : forall f : Cc -> R, (fun n => f (psum (fun _ => cofR 0) rho w n)) = (fun _ => f (cofR 0)))
    by (intro f; apply functional_extensionality; intro n; rewrite psum_zero; reflexivity).
  split; [rewrite (E cre)|rewrite (E cim)]; apply Un_cv_const.
Qed.

(* --- Riemann-sum integrals (DeepStatements IntVal): linearity --- *)
Lemma IntVal_ext : forall f g a b I, (forall x, f x = g x) -> IntVal f a b I -> IntVal g a b I.
Proof. intros f g a b I H. replace g with f by (apply functional_extensionality; exact H). auto. Qed.

Lemma sum_f_R0_lin : forall (A B : nat -> R) l1 l2 n,
  sum_f_R0 (fun j => l1 * A j + l2 * B j) n = l1 * sum_f_R0 A n + l2 * sum_f_R0 B n.
Proof. intros A B l1 l2 n. induction n as [|n IH]; simpl; [ring|rewrite IH; ring]. Qed.

Lemma sum_f_R0_zero : forall n, sum_f_R0 (fun _ => 0) n = 0.
Proof. intro n. induction n as [|n IH]; simpl; [reflexivity|rewrite IH; ring]. Qed.

Lemma Un_cv_lin : forall A B LA LB l1 l2, Un_cv A LA -> Un_cv B LB ->
  Un_cv (fun n => l1 * A n + l2 * B n) (l1 * LA + l2 * LB).
Proof.
  intros A B LA LB l1 l2 HA HB.
  apply CV_plus; apply CV_mult; try apply Un_cv_const; assumption.
Qed.

Definition LapRe (G : R -> Cc) (s : Cc) (u : R) : R :=
  cre (G u) * exp (- cre s * u) * cos (cim s * u) + cim (G u) * exp (- cre s * u) * sin (cim s * u).
Definition LapIm (G : R -> Cc) (s : Cc) (u : R) : R :=
  cim (G u) * exp (- cre s * u) * cos (cim s * u) - cre (G u) * exp (- cre s * u) * sin (cim s * u).

(* int_(0,oo) G u e^(-s u) du = L for a complex kernel G (real and imaginary
   parts of G u e^(-s u), as in DeepStatements' LaplaceAt) *)
Definition LaplaceAtC (G : R -> Cc) (s : Cc) (L : Cc) : Prop :=
  forall eps, 0 < eps -> exists T0, 0 < T0 /\ forall T, T0 <= T ->
    exists Ir Ii, IntVal (LapRe G s) 0 T Ir /\ IntVal (LapIm G s) 0 T Ii /\
      Rabs (Ir - cre L) < eps /\ Rabs (Ii - cim L) < eps.

Lemma LaplaceAtC_ext : forall G G' s L L', (forall u, G u = G' u) -> L = L' ->
  LaplaceAtC G s L -> LaplaceAtC G' s L'.
Proof.
  intros G G' s L L' H E. subst L'. replace G' with G by (apply functional_extensionality; exact H). auto.
Qed.

(* a real kernel: LaplaceAtC of cofR o g is DeepStatements' LaplaceAt of g *)
Lemma LaplaceAtC_real : forall g s L, LaplaceAtC (fun u => cofR (g u)) s L -> LaplaceAt g s L.
Proof.
  intros g s L H. unfold LaplaceAt. intros eps Heps. destruct (H eps Heps) as [T0 [P0 K]].
  exists T0. split; [exact P0|]. intros T HT. destruct (K T HT) as [Ir [Ii [Vr [Vi [Er Ei]]]]].
  exists Ir, Ii. split; [|split; [|split; assumption]].
  - apply (IntVal_ext (LapRe (fun u => cofR (g u)) s)); [|exact Vr].
    intro x. unfold LapRe, cofR. simpl. ring.
  - apply (IntVal_ext (LapIm (fun u => cofR (g u)) s)); [|exact Vi].
    intro x. unfold LapIm, cofR. simpl. ring.
Qed.

Lemma lin_close : forall l1 l2 x1 x2 y1 y2 q, Rabs (x1 - y1) < q -> Rabs (x2 - y2) < q ->
  Rabs (l1 * x1 + l2 * x2 - (l1 * y1 + l2 * y2)) <= (Rabs l1 + Rabs l2) * q.
Proof.
  intros l1 l2 x1 x2 y1 y2 q H1 H2.
  replace (l1 * x1 + l2 * x2 - (l1 * y1 + l2 * y2)) with (l1 * (x1 - y1) + l2 * (x2 - y2)) by ring.
  eapply Rle_trans; [apply Rabs_triang|]. rewrite !Rabs_mult.
  pose proof (Rabs_pos l1). pose proof (Rabs_pos l2). pose proof (Rabs_pos (x1 - y1)). pose proof (Rabs_pos (x2 - y2)). nra.
Qed.

(* the CharPole statement: the conclusion of
   poleData.lean : poleData_char : l.137 for one character (complex kernel
   G = Gchi chi; LZc s = "L(chi, s) = 0").  AlpogeDeepStatements'
   poleData_char_statement writes it with a real kernel; Lean's Gchi is
   complex-valued and poleData's assembly needs Gchi chi and Gchi chi^-1 =
   conj (Gchi chi) separately, so the kernel here is complex
   (CharPole_real_statement: the real-kernel case is the corpus statement). *)
Definition CharPole (G : R -> Cc) (LZc : Cc -> Prop) (Phi : Cc -> Cc) : Prop :=
  (forall s, 2 < cre s -> LaplaceAtC (fun u => G (exp u)) s (Phi s)) /\
  (forall rho, rho <> cofR 0 -> ~ LZc rho -> CAnalyticAt Phi rho) /\
  (forall rho, rho <> cofR 0 -> exists m : nat, (m = 0%nat <-> ~ LZc rho) /\
     exists h, CAnalyticAt h rho /\
       EvPunct rho (fun s => Phi s =
         cadd (cdiv (cmul (cofR (INR m)) (cdiv (cofR (-1)) (cmul rho (csub rho (cofR 1))))) (csub s rho)) (h s))) /\
  (forall z, EvPunct z (fun w => ~ LZc w)).

(* with a real kernel, CharPole is AlpogeDeepStatements' poleData_char_statement *)
Theorem CharPole_real_statement : forall (Gr : R -> R) (LZc : Cc -> Prop),
  (exists Phi, CharPole (fun y => cofR (Gr y)) LZc Phi) -> poleData_char_statement Gr LZc.
Proof.
  intros Gr LZc [Phi [H1 [H2 [H3 H4]]]]. exists Phi. split; [|split; [exact H2|split; [exact H3|exact H4]]].
  intros s Hs. apply (LaplaceAtC_real (fun u => Gr (exp u))). exact (H1 s Hs).
Qed.

Section PoleDataAssembly.
(* the CharFamily F *)
Variable Ix : Type.                                  (* F.iota *)
Variable ixs : list Ix.                              (* Finset.univ *)
Hypothesis ixs_all : forall i, In i ixs.              (* [Fintype F.iota] *)
Hypothesis ixs_nodup : NoDup ixs.                     (* [Fintype F.iota] *)
Hypothesis Ix_dec : forall i j : Ix, {i = j} + {i <> j}.   (* Lean `classical` *)
Variable a : Ix -> R.                                (* F.a *)
Hypothesis a_pos : forall i, 0 < a i.                (* F.a_pos *)
Variables G1 G2 : Ix -> R -> Cc.                     (* Gchi (F.chi i), Gchi (F.chi i)^-1 *)
Variables LZ1 LZ2 : Ix -> Cc -> Prop.                (* L(F.chi i, s) = 0, L((F.chi i)^-1, s) = 0 *)

(* Gm F y = sum_i F.a i * Re (Gchi (F.chi i) y)   (CharFamily.lean) *)
Definition GmF (y : R) : R := lsumR (map (fun i => a i * cre (G1 i y)) ixs).

(* [Mathlib] Finset.measurable_sum, measurable_const.mul -- with Measurable as
   local Riemann integrability this is the closure of Riemann integrability
   under f + l g (Stdlib RiemannInt_P10, which carries Classical_Prop.classic,
   hence a named hypothesis); also used for integral_add / integral_const_mul *)
Hypothesis RI_lin : forall (f h : R -> R) (lo hi l : R),
  (exists _ : Riemann_integrable f lo hi, True) -> (exists _ : Riemann_integrable h lo hi, True) ->
  exists _ : Riemann_integrable (fun x => f x + l * h x) lo hi, True.
(* [inventory] measurable_Gchi (F.chi i), composed with Real.measurable_exp and
   Complex.measurable_re (Measurable as local Riemann integrability) *)
Hypothesis MEAS : forall i, LocInt (fun u => cre (G1 i (exp u))).
(* [inventory] Gchi_growth (F.chi i) *)
Hypothesis GROWTH : forall i, exists C, forall y, 1 <= y -> cnorm (G1 i y) <= C * y ^ 2.
(* [inventory] Gchi_conj (F.chi i) : conj (Gchi chi y) = Gchi chi^-1 y *)
Hypothesis CONJ : forall i y, cconj (G1 i y) = G2 i y.
(* [inventory] poleData_char (F.chi i) (F.adm i) *)
Hypothesis CHAR1 : forall i, exists Phi, CharPole (G1 i) (LZ1 i) Phi.
(* [inventory] poleData_char (F.chi i)^-1 (adm' i)   (adm' via inv_ne_one) *)
Hypothesis CHAR2 : forall i, exists Phi, CharPole (G2 i) (LZ2 i) Phi.
(* [inventory] poleData_inv_zero (F.chi i)   (poleData.lean l.241, from LFunction_conj) *)
Hypothesis INVZ : forall i w, LZ2 i w <-> LZ1 i (cconj w).
(* [inventory] charFamily_LFunction_ne_zero_of_one_le_re F i *)
Hypothesis NZ1 : forall i s, 1 <= cre s -> ~ LZ1 i s.
(* [Mathlib] AnalyticAt.add, analyticAt_const.mul, AnalyticAt.differentiableAt *)
Hypothesis AN_add : forall f h rho, CAnalyticAt f rho -> CAnalyticAt h rho ->
  CAnalyticAt (fun s => cadd (f s) (h s)) rho.
Hypothesis AN_smul : forall (c : R) f rho, CAnalyticAt f rho -> CAnalyticAt (fun s => cmul (cofR c) (f s)) rho.
Hypothesis AN_diff : forall h rho, CAnalyticAt h rho -> exists L, CDerivWithin h L (fun _ => True) rho.

Lemma IntVal_lin : forall f h lo hi I1 J1 l1 l2, IntVal f lo hi I1 -> IntVal h lo hi J1 ->
  IntVal (fun x => l1 * f x + l2 * h x) lo hi (l1 * I1 + l2 * J1).
Proof.
  intros f h lo hi I1 J1 l1 l2 [Rf Cf] [Rh Ch]. split.
  - pose proof (RI_lin (fun _ => 0) f lo hi l1 (ex_intro _ (RiemannInt_P14 lo hi 0) I) Rf) as R1.
    pose proof (RI_lin _ h lo hi l2 R1 Rh) as R2.
    replace (fun x => l1 * f x + l2 * h x) with (fun x => (fun x => 0 + l1 * f x) x + l2 * h x)
      by (apply functional_extensionality; intro; ring). exact R2.
  - replace (RSum (fun x => l1 * f x + l2 * h x) lo hi)
      with (fun n => l1 * RSum f lo hi n + l2 * RSum h lo hi n).
    + apply Un_cv_lin; assumption.
    + apply functional_extensionality. intro n. unfold RSum.
      rewrite (sum_f_R0_lin (fun j => f (lo + INR j * (hi - lo) / INR (S n))) (fun j => h (lo + INR j * (hi - lo) / INR (S n)))).
      ring.
Qed.

Lemma IntVal_zero : forall lo hi, IntVal (fun _ => 0) lo hi 0.
Proof.
  intros lo hi. split; [exact (ex_intro _ (RiemannInt_P14 lo hi 0) I)|].
  replace (RSum (fun _ => 0) lo hi) with (fun _ : nat => 0); [apply Un_cv_const|].
  apply functional_extensionality. intro n. unfold RSum. rewrite sum_f_R0_zero. ring.
Qed.

(* [Mathlib] integral_add, integral_const_mul, rebuilt for LaplaceAtC *)
Lemma LaplaceAtC_lin : forall G1' G2' s L1 L2 l1 l2, LaplaceAtC G1' s L1 -> LaplaceAtC G2' s L2 ->
  LaplaceAtC (fun u => cadd (cmul (cofR l1) (G1' u)) (cmul (cofR l2) (G2' u))) s
             (cadd (cmul (cofR l1) L1) (cmul (cofR l2) L2)).
Proof.
  intros G1' G2' s L1 L2 l1 l2 H1 H2 eps Heps.
  set (A := Rabs l1 + Rabs l2). assert (HA : 0 <= A) by (unfold A; pose proof (Rabs_pos l1); pose proof (Rabs_pos l2); lra).
  set (q := eps / (2 * (A + 1))). assert (Hq : 0 < q) by (unfold q; apply Rdiv_lt_0_compat; lra).
  assert (HAq : A * q < eps).
  { unfold q. apply (Rmult_lt_reg_r (2 * (A + 1))); [lra|].
    replace (A * (eps / (2 * (A + 1))) * (2 * (A + 1))) with (A * eps) by (field; lra). nra. }
  destruct (H1 q Hq) as [T1 [P1 K1]]. destruct (H2 q Hq) as [T2 [P2 K2]].
  exists (Rmax T1 T2). split; [pose proof (Rmax_l T1 T2); lra|]. intros T HT.
  destruct (K1 T ltac:(pose proof (Rmax_l T1 T2); lra)) as [Ir1 [Ii1 [Vr1 [Vi1 [Er1 Ei1]]]]].
  destruct (K2 T ltac:(pose proof (Rmax_r T1 T2); lra)) as [Ir2 [Ii2 [Vr2 [Vi2 [Er2 Ei2]]]]].
  exists (l1 * Ir1 + l2 * Ir2), (l1 * Ii1 + l2 * Ii2). split; [|split; [|split]].
  - apply (IntVal_ext (fun x => l1 * LapRe G1' s x + l2 * LapRe G2' s x)); [|apply IntVal_lin; assumption].
    intro x. unfold LapRe, cadd, cmul, cofR. simpl. ring.
  - apply (IntVal_ext (fun x => l1 * LapIm G1' s x + l2 * LapIm G2' s x)); [|apply IntVal_lin; assumption].
    intro x. unfold LapIm, cadd, cmul, cofR. simpl. ring.
  - replace (cre (cadd (cmul (cofR l1) L1) (cmul (cofR l2) L2))) with (l1 * cre L1 + l2 * cre L2)
      by (unfold cadd, cmul, cofR; simpl; ring).
    pose proof (lin_close l1 l2 Ir1 Ir2 (cre L1) (cre L2) q Er1 Er2). fold A in H. lra.
  - replace (cim (cadd (cmul (cofR l1) L1) (cmul (cofR l2) L2))) with (l1 * cim L1 + l2 * cim L2)
      by (unfold cadd, cmul, cofR; simpl; ring).
    pose proof (lin_close l1 l2 Ii1 Ii2 (cim L1) (cim L2) q Ei1 Ei2). fold A in H. lra.
Qed.

Lemma LaplaceAtC_zero : forall s, LaplaceAtC (fun _ => cofR 0) s (cofR 0).
Proof.
  intros s eps Heps. exists 1. split; [lra|]. intros T _. exists 0, 0.
  split; [|split; [|split]].
  - apply (IntVal_ext (fun _ => 0)); [intro x; unfold LapRe, cofR; simpl; ring|apply IntVal_zero].
  - apply (IntVal_ext (fun _ => 0)); [intro x; unfold LapIm, cofR; simpl; ring|apply IntVal_zero].
  - simpl. rewrite Rminus_0_r, Rabs_R0. exact Heps.
  - simpl. rewrite Rminus_0_r, Rabs_R0. exact Heps.
Qed.

(* the PoleData fields, for the finite sums over a list of characters *)
Lemma meas_sum : forall l, LocInt (fun u => lsumR (map (fun i => a i * cre (G1 i (exp u))) l)).
Proof.
  intros l lo hi Hlh. induction l as [|i l IH]; simpl.
  - exact (ex_intro _ (RiemannInt_P14 lo hi 0) I).
  - pose proof (RI_lin _ _ lo hi (a i) IH (MEAS i lo hi Hlh)) as H.
    replace (fun u => a i * cre (G1 i (exp u)) + lsumR (map (fun i0 => a i0 * cre (G1 i0 (exp u))) l))
      with (fun x => lsumR (map (fun i0 => a i0 * cre (G1 i0 (exp x))) l) + a i * cre (G1 i (exp x)))
      by (apply functional_extensionality; intro; ring). exact H.
Qed.

Lemma growth_sum : forall l, exists C, forall u, 0 <= u ->
  Rabs (lsumR (map (fun i => a i * cre (G1 i (exp u))) l)) <= C * exp (2 * u).
Proof.
  induction l as [|i l [C HC]]; simpl.
  - exists 0. intros u _. rewrite Rabs_R0. lra.
  - destruct (GROWTH i) as [Ci HCi]. exists (a i * Ci + C). intros u Hu.
    assert (Hy : 1 <= exp u) by (rewrite <- exp_0; apply exp_le_mono; exact Hu).
    assert (He : exp u ^ 2 = exp (2 * u)) by (simpl; rewrite Rmult_1_r, <- exp_plus; f_equal; ring).
    pose proof (HCi (exp u) Hy) as G. rewrite He in G. pose proof (HC u Hu) as R.
    pose proof (cre_le_cnorm (G1 i (exp u))) as Hre. pose proof (a_pos i) as Ha.
    eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_mult, (Rabs_right (a i)) by lra.
    assert (a i * Rabs (cre (G1 i (exp u))) <= a i * (Ci * exp (2 * u))) by (apply Rmult_le_compat_l; lra).
    nra.
Qed.

Lemma re_conj_sum : forall l y,
  lsumC (map (fun i => cmul (cofR (a i / 2)) (cadd (G1 i y) (G2 i y))) l)
  = cofR (lsumR (map (fun i => a i * cre (G1 i y)) l)).
Proof.
  intros l y. induction l as [|i l IH]; simpl; [reflexivity|]. rewrite IH, <- (CONJ i y).
  apply Cc_ext; unfold cadd, cmul, cofR, cconj; simpl; field.
Qed.

Lemma laplace_sum : forall (Phi1 Phi2 : Ix -> Cc -> Cc) l s, 2 < cre s ->
  (forall i, LaplaceAtC (fun u => G1 i (exp u)) s (Phi1 i s)) ->
  (forall i, LaplaceAtC (fun u => G2 i (exp u)) s (Phi2 i s)) ->
  LaplaceAtC (fun u => lsumC (map (fun i => cmul (cofR (a i / 2)) (cadd (G1 i (exp u)) (G2 i (exp u)))) l)) s
             (lsumC (map (fun i => cmul (cofR (a i / 2)) (cadd (Phi1 i s) (Phi2 i s))) l)).
Proof.
  intros Phi1 Phi2 l s Hs H1 H2. induction l as [|i l IH]; simpl; [apply LaplaceAtC_zero|].
  pose proof (LaplaceAtC_lin _ _ s _ _ (a i / 2) (a i / 2) (H1 i) (H2 i)) as Hi.
  pose proof (LaplaceAtC_lin _ _ s _ _ 1 1 Hi IH) as H.
  revert H. apply LaplaceAtC_ext.
  - intro u. apply Cc_ext; unfold cadd, cmul, cofR; simpl; ring.
  - apply Cc_ext; unfold cadd, cmul, cofR; simpl; ring.
Qed.

Lemma analytic_sum : forall (F : Ix -> Cc -> Cc) rho l, (forall i, In i l -> CAnalyticAt (F i) rho) ->
  CAnalyticAt (fun s => lsumC (map (fun i => cmul (cofR (a i / 2)) (F i s)) l)) rho.
Proof.
  intros F rho l. induction l as [|i l IH]; intros H; simpl.
  - apply CAnalyticAt_zero.
  - apply AN_add.
    + apply AN_smul. apply H. left. reflexivity.
    + apply IH. intros j Hj. apply H. right. exact Hj.
Qed.

(* the residue sum: sum_i (a_i/2)((m1_i Q + h1_i) + (m2_i Q + h2_i)) = S Q + sum_i (a_i/2)(h1_i + h2_i) *)
Lemma pole_sum_algebra : forall (m1 m2 : Ix -> nat) (Q : Cc) (H1 H2 : Ix -> Cc) l,
  lsumC (map (fun i => cmul (cofR (a i / 2)) (cadd (cadd (cmul (cofR (INR (m1 i))) Q) (H1 i))
                                                    (cadd (cmul (cofR (INR (m2 i))) Q) (H2 i)))) l)
  = cadd (cmul (cofR (lsumR (map (fun i => a i / 2 * (INR (m1 i) + INR (m2 i))) l))) Q)
         (lsumC (map (fun i => cmul (cofR (a i / 2)) (cadd (H1 i) (H2 i))) l)).
Proof.
  intros m1 m2 Q H1 H2 l. induction l as [|i l IH]; simpl.
  - apply Cc_ext; unfold cadd, cmul, cofR; simpl; ring.
  - rewrite IH. apply Cc_ext; unfold cadd, cmul, cofR; simpl; ring.
Qed.

(* poleData.lean : poleData : l.248 *)
Theorem poleData_r : poleData_statement Ix LZ1 GmF.
Proof.
  (* choose Phi1 ... using fun i => poleData_char (F.chi i) (F.adm i), and Phi2 *)
  destruct (fin_choice Ix (Cc -> Cc) Ix_dec (fun _ => cofR 0) (fun i Phi => CharPole (G1 i) (LZ1 i) Phi) ixs
              (fun i _ => CHAR1 i)) as [Phi1 HP1].
  destruct (fin_choice Ix (Cc -> Cc) Ix_dec (fun _ => cofR 0) (fun i Phi => CharPole (G2 i) (LZ2 i) Phi) ixs
              (fun i _ => CHAR2 i)) as [Phi2 HP2].
  assert (C1 : forall i, CharPole (G1 i) (LZ1 i) (Phi1 i)) by (intro i; apply HP1, ixs_all).
  assert (C2 : forall i, CharPole (G2 i) (LZ2 i) (Phi2 i)) by (intro i; apply HP2, ixs_all).
  clear HP1 HP2.
  exists (fun s => lsumC (map (fun i => cmul (cofR (a i / 2)) (cadd (Phi1 i s) (Phi2 i s))) ixs)).
  unfold PoleData, gm, GmF. split; [|split; [|split; [|split; [|split; [|split]]]]].
  - (* meas *) apply meas_sum.
  - (* growth *) apply growth_sum.
  - (* laplace: Re z = (z + conj z)/2, Gchi_conj, integral_finsetSum/const_mul/add *)
    intros s Hs. apply (LaplaceAtC_real (fun u => lsumR (map (fun i => a i * cre (G1 i (exp u))) ixs))).
    apply (LaplaceAtC_ext (fun u => lsumC (map (fun i => cmul (cofR (a i / 2)) (cadd (G1 i (exp u)) (G2 i (exp u)))) ixs))
             _ s _ _ (fun u => re_conj_sum ixs (exp u)) eq_refl).
    apply laplace_sum; [exact Hs|intro i; apply (proj1 (C1 i)); exact Hs|intro i; apply (proj1 (C2 i)); exact Hs].
  - (* pos *) intros rho [H _]. exact H.
  - (* diff: the sum is analytic off the zero set *)
    intros s [Hs HZ].
    assert (Hs0 : s <> cofR 0) by (intro E; rewrite E in Hs; simpl in Hs; lra).
    assert (HL1 : forall i, ~ LZ1 i s) by (intros i H; apply HZ; split; [exact Hs|exists i; left; exact H]).
    assert (HL2 : forall i, ~ LZ2 i s)
      by (intros i H; apply HZ; split; [exact Hs|exists i; right; apply INVZ; exact H]).
    assert (Han : CAnalyticAt (fun s => lsumC (map (fun i => cmul (cofR (a i / 2)) (cadd (Phi1 i s) (Phi2 i s))) ixs)) s).
    { apply (analytic_sum (fun i s => cadd (Phi1 i s) (Phi2 i s))). intros i _. apply AN_add.
      - destruct (C1 i) as [_ [A _]]. exact (A s Hs0 (HL1 i)).
      - destruct (C2 i) as [_ [A _]]. exact (A s Hs0 (HL2 i)). }
    destruct (AN_diff _ _ Han) as [L HL]. exists L. apply CDW_univ. exact HL.
  - (* iso *)
    intros z _.
    assert (H : EvPunct z (fun w => forall i, In i ixs -> ~ LZ1 i w /\ ~ LZ2 i w)).
    { apply EvPunct_all. intros i _. apply EvPunct_and.
      - destruct (C1 i) as [_ [_ [_ I1]]]. apply I1.
      - destruct (C2 i) as [_ [_ [_ I2]]]. apply I2. }
    destruct H as [d [Hd K]]. exists d. split; [exact Hd|]. intros w A1 A2 [_ [i Hi]].
    destruct (K w A1 A2 i (ixs_all i)) as [N1 N2].
    destruct Hi as [Hi|Hi]; [exact (N1 Hi)|apply N2; apply INVZ; exact Hi].
  - (* pole *)
    intros rho [Hre [i0 Hi0]].
    assert (Hrho0 : rho <> cofR 0) by (intro E; rewrite E in Hre; simpl in Hre; lra).
    assert (Hrho1 : rho <> cofR 1).
    { intro E. subst rho. destruct Hi0 as [H|H].
      - apply (NZ1 i0 (cofR 1)); [simpl; lra|exact H].
      - apply (NZ1 i0 (cconj (cofR 1))); [simpl; lra|exact H]. }
    set (X := cdiv (cofR (-1)) (cmul rho (csub rho (cofR 1)))).
    (* choose m1 h1 ... using fun i => hPhi1pol i rho, and m2 h2 *)
    destruct (fin_choice Ix (nat * (Cc -> Cc))%type Ix_dec (0%nat, fun _ => cofR 0)
      (fun i mh => (fst mh = 0%nat <-> ~ LZ1 i rho) /\ CAnalyticAt (snd mh) rho /\
         EvPunct rho (fun s => Phi1 i s = cadd (cdiv (cmul (cofR (INR (fst mh))) X) (csub s rho)) (snd mh s))) ixs)
      as [mh1 Hm1].
    { intros i _. destruct (C1 i) as [_ [_ [P _]]]. destruct (P rho Hrho0) as [m [Hm [h [Hh Hev]]]].
      exists (m, h). simpl. split; [exact Hm|split; [exact Hh|exact Hev]]. }
    destruct (fin_choice Ix (nat * (Cc -> Cc))%type Ix_dec (0%nat, fun _ => cofR 0)
      (fun i mh => (fst mh = 0%nat <-> ~ LZ2 i rho) /\ CAnalyticAt (snd mh) rho /\
         EvPunct rho (fun s => Phi2 i s = cadd (cdiv (cmul (cofR (INR (fst mh))) X) (csub s rho)) (snd mh s))) ixs)
      as [mh2 Hm2].
    { intros i _. destruct (C2 i) as [_ [_ [P _]]]. destruct (P rho Hrho0) as [m [Hm [h [Hh Hev]]]].
      exists (m, h). simpl. split; [exact Hm|split; [exact Hh|exact Hev]]. }
    set (m1 := fun i => fst (mh1 i)). set (h1 := fun i => snd (mh1 i)).
    set (m2 := fun i => fst (mh2 i)). set (h2 := fun i => snd (mh2 i)).
    set (S := lsumR (map (fun i => a i / 2 * (INR (m1 i) + INR (m2 i))) ixs)).
    (* hS0 : 0 < S, from the character i0 whose L-function vanishes at rho or conj rho *)
    assert (HS0 : 0 < S).
    { assert (Hnn : forall i, In i ixs -> 0 <= a i / 2 * (INR (m1 i) + INR (m2 i))).
      { intros i _. pose proof (a_pos i). pose proof (pos_INR (m1 i)). pose proof (pos_INR (m2 i)). nra. }
      assert (Hpos : 0 < a i0 / 2 * (INR (m1 i0) + INR (m2 i0))).
      { pose proof (a_pos i0). pose proof (pos_INR (m1 i0)). pose proof (pos_INR (m2 i0)).
        assert (1 <= INR (m1 i0) + INR (m2 i0)).
        { destruct Hi0 as [Hz|Hz].
          - assert (m1 i0 <> 0%nat) by (intro E; apply (proj1 (proj1 (Hm1 i0 (ixs_all i0))) E); exact Hz).
            assert (1 <= INR (m1 i0)) by (apply (le_INR 1); lia). lra.
          - assert (m2 i0 <> 0%nat)
              by (intro E; apply (proj1 (proj1 (Hm2 i0 (ixs_all i0))) E); apply INVZ; exact Hz).
            assert (1 <= INR (m2 i0)) by (apply (le_INR 1); lia). lra. }
        nra. }
      pose proof (lsumR_single_le (fun i => a i / 2 * (INR (m1 i) + INR (m2 i))) ixs i0 Hnn (ixs_all i0)).
      unfold S. simpl in *. lra. }
    exists (cmul (cofR S) X). split; [|split].
    + (* c <> 0 *)
      intro E. assert (Hn : n2 (cmul (cofR S) X) = 0) by (rewrite E; apply n2_zero).
      assert (Hr1 : csub rho (cofR 1) <> cofR 0).
      { intro E1. apply Hrho1. apply Cc_ext.
        - assert (cre (csub rho (cofR 1)) = 0) by (rewrite E1; reflexivity). unfold csub in H; simpl in *; lra.
        - assert (cim (csub rho (cofR 1)) = 0) by (rewrite E1; reflexivity). unfold csub in H; simpl in *; lra. }
      assert (Hp : 0 < n2 (cmul rho (csub rho (cofR 1))))
        by (rewrite n2_cmul; apply Rmult_lt_0_compat; apply n2_pos; assumption).
      unfold X, cdiv in Hn. rewrite !n2_cmul, n2_cinv in Hn by exact Hp.
      assert (E2 : n2 (cofR S) = S * S) by (unfold n2, cofR; simpl; ring).
      assert (E3 : n2 (cofR (-1)) = 1) by (unfold n2, cofR; simpl; ring).
      rewrite E2, E3, Rmult_1_l in Hn. pose proof (Rinv_0_lt_compat _ Hp) as Hi.
      assert (0 < S * S * / n2 (cmul rho (csub rho (cofR 1)))) by (apply Rmult_lt_0_compat; nra).
      lra.
    + (* real rho: the residue is real and positive *)
      intro Him. set (x := cre rho).
      assert (Ex : rho = cofR x) by (apply Cc_ext; [reflexivity|exact Him]).
      assert (Hx1 : x < 1).
      { destruct (Rlt_or_le x 1) as [H|H]; [exact H|exfalso]. destruct Hi0 as [Hz|Hz].
        - exact (NZ1 i0 rho H Hz).
        - apply (NZ1 i0 (cconj rho)); [unfold cconj; simpl; exact H|exact Hz]. }
      assert (Hx0 : 0 < x) by exact Hre.
      assert (Hxx : x * (x - 1) <> 0) by nra.
      unfold X. rewrite Ex, csub_cofR, cmul_cofR. unfold cdiv. rewrite cinv_cofR by exact Hxx.
      rewrite !cmul_cofR. simpl. split; [|reflexivity].
      assert (x * (x - 1) < 0) by nra. pose proof (Rinv_lt_0_compat _ H). nra.
    + (* h := sum_i (a_i/2)(h1_i + h2_i) *)
      exists (fun s => lsumC (map (fun i => cmul (cofR (a i / 2)) (cadd (h1 i s) (h2 i s))) ixs)). split.
      * apply (analytic_sum (fun i s => cadd (h1 i s) (h2 i s))). intros i Hi. apply AN_add.
        -- exact (proj1 (proj2 (Hm1 i Hi))).
        -- exact (proj1 (proj2 (Hm2 i Hi))).
      * assert (Hev : EvPunct rho (fun s => forall i, In i ixs ->
            Phi1 i s = cadd (cdiv (cmul (cofR (INR (m1 i))) X) (csub s rho)) (h1 i s) /\
            Phi2 i s = cadd (cdiv (cmul (cofR (INR (m2 i))) X) (csub s rho)) (h2 i s))).
        { apply EvPunct_all. intros i Hi. apply EvPunct_and.
          - exact (proj2 (proj2 (Hm1 i Hi))).
          - exact (proj2 (proj2 (Hm2 i Hi))). }
        destruct Hev as [d [Hd K]]. exists d. split; [exact Hd|]. intros s A1 A2.
        rewrite (lsumC_map_ext _ (fun i => cmul (cofR (a i / 2))
                   (cadd (cadd (cmul (cofR (INR (m1 i))) (cdiv X (csub s rho))) (h1 i s))
                         (cadd (cmul (cofR (INR (m2 i))) (cdiv X (csub s rho))) (h2 i s))))).
        -- rewrite pole_sum_algebra. rewrite cdiv_cmul_assoc. reflexivity.
        -- intros i Hi. destruct (K s A1 A2 i Hi) as [E1 E2]. rewrite E1, E2, !cdiv_cmul_assoc. reflexivity.
Qed.
End PoleDataAssembly.

Print Assumptions CharPole_real_statement.
Print Assumptions poleData_r.

(* ===================================================================== *)
(* Summary: Lean lemma -> Rocq theorem(s) -> hypotheses                   *)
(* ===================================================================== *)
(*
 1  IteratedDerivLaplace.lean : iteratedDeriv_laplace (l.84)
      -> iteratedDeriv_laplace_r (Phi = Ik 0 on Re > 2; D any IterDerivs family)
         iteratedDeriv_laplace_lean (Phi := Ik 0, the literal statement)
         iteratedDeriv_laplace_exists (Ik is an IterDerivs family of Ik 0)
         iteratedDeriv_laplace_ILAP (produces AlpogeFifthBatch's ILAP shape)
         landau_coeff_of_iteratedDeriv_laplace (ILAP fed to landau_coeff)
      sub-lemmas: iteratedDeriv_laplace_int_r (l.9, PROVED via kernel_tail),
         iteratedDeriv_laplace_bound_r (l.22, PROVED over R),
         laplace_integrand_deriv (h1/h2/congr_deriv of l.48),
         iteratedDeriv_laplace_hasDerivAt_r (l.48)
      hypotheses: hg  (Lean premise Measurable g, as LocInt g)
                  hgC (Lean premise |g u| <= C e^(2u))
                  INTV  [Mathlib] Integrable.mono' + intervalIntegral_tendsto_integral_Ioi
                  DOM   [Mathlib] hasDerivAt_integral_of_dominated_loc_of_deriv_le
                  CEXPD [Mathlib] HasDerivAt.cexp, HasDerivAt.const_mul
      (iteratedDeriv_succ / EventuallyEq.deriv_eq / HasDerivAt.deriv: carried by
       IterDerivs + CDW_ext_on + CDW_unique, the last PROVED)

 2  LandauFinite.lean : landau_finite (l.9)
      -> landau_finite_r
      hypotheses: COMPACT [Mathlib] isCompact_closedBall + IsCompact.elim_nhds_subcover
      (hpos via |Re w| <= |w| and the v = w case split: PROVED)

 3  LandauPoleAsym.lean : landau_pole_asym_deriv (l.10)
      -> landau_pole_asym_deriv_r : landau_pole_asym_deriv_statement
         (induction on k, sign/factorial step PoleK_deriv)
      hypotheses: DZPOW [Mathlib] hasDerivAt_zpow, HasDerivAt.comp_sub_const, .const_mul
    LandauPoleAsym.lean : landau_pole_asym (l.19)
      -> landau_pole_asym_r : landau_pole_asym_statement
      hypotheses: DZPOW (as above)
                  ANDIFF  [Mathlib] AnalyticAt.differentiableAt
                  HOLITER [Mathlib] DifferentiableOn.contDiffOn (iterated derivatives
                          of a holomorphic function on the open ball)
                  CAUCHY  [inventory] landau_cauchy (LandauCauchy.lean l.9)
      (removable singularity of G, iteratedDeriv_add, HasDerivWithinAt.add/.sub,
       uniqueness of derivatives on the open punctured ball, final algebra: PROVED)

 4  poleData.lean : poleData (l.248)
      -> poleData_r : poleData_statement Ix LZ1 GmF
         (Phi = sum_i (a_i/2)(Phi1_i + Phi2_i); all seven PoleData fields)
         CharPole_real_statement (CharPole with a real kernel is the corpus's
         poleData_char_statement)
      hypotheses: ixs_all, ixs_nodup (Fintype F.iota), Ix_dec (Lean `classical`),
                  a_pos (F.a_pos)
                  RI_lin [Mathlib] Finset.measurable_sum / measurable_const.mul,
                         integral_add / integral_const_mul (Stdlib RiemannInt_P10,
                         which carries Classical_Prop.classic)
                  AN_add, AN_smul, AN_diff [Mathlib] AnalyticAt.add,
                         analyticAt_const.mul, AnalyticAt.differentiableAt
                  MEAS   [inventory] measurable_Gchi (+ measurable_exp, measurable_re)
                  GROWTH [inventory] Gchi_growth
                  CONJ   [inventory] Gchi_conj
                  CHAR1, CHAR2 [inventory] poleData_char (F.chi i), (F.chi i)^-1
                  INVZ   [inventory] poleData_inv_zero
                  NZ1    [inventory] charFamily_LFunction_ne_zero_of_one_le_re
      (finite choice of Phi1/Phi2/(m,h), growth bound sum, Re = (z + conj z)/2,
       Laplace linearity over the finite sum, finite intersection of punctured
       neighbourhoods, residue S > 0, c <> 0, real residue > 0, residue-sum
       algebra: PROVED.  The proof of poleData_char itself -- zeta /
       L-function analysis via poleData_abstract, logDeriv_local and the
       Mellin transforms -- is NOT refined here.)
*)
