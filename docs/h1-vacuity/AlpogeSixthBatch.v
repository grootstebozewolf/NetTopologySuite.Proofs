(* AlpogeSixthBatch.v -- the sixth batch of the Alpöge main-line audit
   (claimed RH/GRH Lean development, mirror CocoSgt/riemann-hypothesis-lean
   @ 7cbf7a0, read from source, not built).

   PROVED over Stdlib's R (inventory/Mathlib inputs as named premises):
     Part A  sum_A, sum_Th        C = R x R is a field (Cc_field); the
                                  abstract-field refinements of
                                  AlpogeFifthBatch instantiated at C
     Part B  landau_window_ineq   landauWindowIneq.lean, with the complex
                                  triangle inequality rebuilt (unit-vector
                                  trick + pointwise Cauchy-Schwarz)
     Part E  windowHypU_of_windowHyp  WindowHypUOfWindowHyp.lean, via a new
                                  allowlist-clean change of variables
                                  y = e^u for a merely RInt-integrable
                                  integrand (RInt_bounded, RInt_exp_change)
   REFINED (the Lean proof rebuilt; inventory lemmas as hypotheses):
     Part C  TopG     ShapeWin.lean : shapeWin (+ EveryCharacter.lean : plugWin)
     Part D  HostExW  SupplyChi.lean : supplyChi (+ AdmChi.lean)

   Within docs/axiom-allowlist.txt (Print Assumptions after each result).
   Evidence for docs/attacks/2026-11-22-alpoge-sixth-batch.md.
   NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import Reals Lra Psatz Lia List Factorial Ring Field Permutation ZArith.
From NTS.Proofs.Probes Require Import AlpogeRealsQED AlpogeRealsQED2 AlpogeDeepStatements CleanIntegralQED AlpogeFifthBatch.
From NTS.Proofs Require Export TaggedIntegralChange.
Import ListNotations.
Local Open Scope R_scope.

(* ===================================================================== *)
(* Part A: C = R x R is a field; sum_A and sum_Th over it                 *)
(* ===================================================================== *)
Definition copp (a : Cc) : Cc := mkC (- cre a) (- cim a).
Definition c0 : Cc := cofR 0.
Definition c1 : Cc := cofR 1.

Lemma Cc_ext : forall a b, cre a = cre b -> cim a = cim b -> a = b.
Proof. intros [ar ai] [br bi]; simpl; intros -> ->; reflexivity. Qed.

Ltac cc := intros; repeat match goal with z : Cc |- _ => destruct z end;
           apply Cc_ext; unfold cadd, cmul, csub, copp, cofR, c0, c1; simpl; ring.

Lemma Cc_nz_norm : forall a, a <> c0 -> cre a * cre a + cim a * cim a <> 0.
Proof.
  intros [ar ai] H E; simpl in E. apply H. apply Cc_ext; unfold c0, cofR; simpl; nra.
Qed.

Theorem Cc_field : field_theory c0 c1 cadd cmul csub copp cdiv cinv (@eq Cc).
Proof.
  constructor.
  - constructor; try cc.
  - unfold c0, c1, cofR. intro E. injection E. lra.
  - intros p q. reflexivity.
  - intros p Hp. pose proof (Cc_nz_norm p Hp) as Hn. destruct p as [pr pi]; simpl in Hn.
    apply Cc_ext; unfold cmul, cinv, c1, cofR; simpl; field; exact Hn.
Qed.

Definition csum : list Cc -> Cc := ksum Cc c0 cadd.
Definition cnat : nat -> Cc := knat Cc c0 c1 cadd.

Section CharSumsC.
(* the group E0 x H and its C-valued characters (as in AlpogeFifthBatch) *)
Variable Hg G : Type.
Variables (hadd hsub : Hg -> Hg -> Hg) (hneg : Hg -> Hg).
Variables (gadd : G -> G -> G) (gneg : G -> G) (e1 inr : Hg -> G).
Hypothesis Hid : forall s u t, gneg (e1 (hsub (hadd s u) t)) = gadd (gadd (e1 t) (inr (hneg s))) (inr (hneg u)).
Variable A0 : list Hg.
Hypothesis A0_neg : forall s, In s A0 -> In (hneg s) A0.
Hypothesis A0_perm : Permutation (map hneg A0) A0.          (* [Mathlib] Equiv.neg A0 *)

(* sum_A (ChCore.lean l.28) over C = R x R, trivial case *)
Theorem sum_A_trivial_C : forall psi : G -> Cc,
  (forall x y, psi (gadd x y) = cmul (psi x) (psi y)) ->     (* [Mathlib] AddChar.map_add_eq_mul *)
  (forall s, In s A0 -> psi (inr s) = c1) ->
  forall s t, In s A0 ->
    csum (map (fun u => psi (gneg (e1 (hsub (hadd s u) t)))) A0) = cmul (cnat (length A0)) (psi (e1 t)).
Proof. intros psi Hadd Htr. exact (sum_A_trivial Cc c0 c1 cadd cmul csub cdiv copp cinv Cc_field
         Hg G hadd hsub hneg gadd gneg e1 inr Hid A0 A0_neg psi Hadd Htr). Qed.

(* sum_A over C, non-trivial case *)
Theorem sum_A_nontrivial_C : forall psi : G -> Cc,
  (forall x y, psi (gadd x y) = cmul (psi x) (psi y)) ->     (* [Mathlib] AddChar.map_add_eq_mul *)
  ((exists s, In s A0 /\ psi (inr s) <> c1) -> csum (map (fun u => psi (inr u)) A0) = c0) ->
                                                            (* [Mathlib] AddChar.sum_eq_zero_iff_ne_zero *)
  (exists s, In s A0 /\ psi (inr s) <> c1) ->
  forall s t, csum (map (fun u => psi (gneg (e1 (hsub (hadd s u) t)))) A0) = c0.
Proof. intros psi Hadd H0. exact (sum_A_nontrivial Cc c0 c1 cadd cmul csub cdiv copp cinv Cc_field
         Hg G hadd hsub hneg gadd gneg e1 inr Hid A0 A0_perm psi Hadd H0). Qed.

(* sum_Th (ChCore.lean l.56) over C *)
Variable Chars : list (G -> Cc).
Variable inPsi : (G -> Cc) -> bool.
Hypothesis Chars_add : forall psi, In psi Chars -> forall x y, psi (gadd x y) = cmul (psi x) (psi y).
Hypothesis inPsi_true : forall psi, In psi Chars -> inPsi psi = true -> forall s, In s A0 -> psi (inr s) = c1.
Hypothesis inPsi_false : forall psi, In psi Chars -> inPsi psi = false -> exists s, In s A0 /\ psi (inr s) <> c1.
Hypothesis SUM0s : forall psi, In psi Chars ->
  (exists s, In s A0 /\ psi (inr s) <> c1) -> csum (map (fun u => psi (inr u)) A0) = c0.   (* [Mathlib] *)
Variables (b : Cc) (GPsi : (G -> Cc) -> Cc) (T2 : list Hg) (nH : Cc).
Hypothesis T2_A0 : forall s, In s T2 -> In s A0.
Hypothesis nH_nz : nH <> c0.

Definition ThC (u0 t : Hg) : Cc :=
  Th Cc c0 c1 cadd cmul cinv Hg G hadd hsub gneg e1 Chars b GPsi T2 nH u0 t.
Definition PsiSumC (t : Hg) : Cc := PsiSum Cc c0 cadd cmul Hg G e1 Chars inPsi GPsi t.

Theorem sum_Th_C : forall t,
  csum (map (fun u => ThC u t) A0) =
  cmul (cmul (cnat (length A0)) (cmul b (cmul (cdiv (cnat (length T2)) nH) (cinv (cadd c1 c1))))) (PsiSumC t).
Proof.
  intro t. apply (sum_Th Cc c0 c1 cadd cmul csub cdiv copp cinv Cc_field
    Hg G hadd hsub hneg gadd gneg e1 inr Hid A0 A0_neg A0_perm Chars inPsi
    Chars_add inPsi_true inPsi_false SUM0s b GPsi T2 nH T2_A0 nH_nz).
  unfold c1, c0, cofR, cadd; simpl. intro E. injection E. lra.
Qed.
End CharSumsC.

Print Assumptions Cc_field.
Print Assumptions sum_A_trivial_C.
Print Assumptions sum_A_nontrivial_C.
Print Assumptions sum_Th_C.

(* ===================================================================== *)
(* Part B: landau_window_ineq over R (landauWindowIneq.lean)              *)
(* ===================================================================== *)
Lemma exp_le1 : forall y, y <= 0 -> exp y <= 1.
Proof.
  intros y Hy. pose proof (exp_ge_Pk 0 (- y) ltac:(lra)) as H. rewrite Pk_O in H.
  pose proof (exp_pos y) as Hp. assert (E : exp y * exp (- y) = 1) by (rewrite <- exp_plus; replace (y + - y) with 0 by ring; apply exp_0).
  nra.
Qed.

Lemma RIntInf_zero_le : forall f a A, RIntInf f a A -> (forall x, a <= x -> 0 <= f x) -> 0 <= A.
Proof.
  intros f a A HA Hf.
  assert (H0 : RIntInf (fun _ => 0) a 0).
  { pose proof (RIntInf_scal 0 f a A HA) as H. replace (0 * A) with 0 in H by ring.
    apply (RIntInf_ext (fun x => 0 * f x)); [intros; ring|exact H]. }
  exact (RIntInf_le _ _ a 0 A H0 HA Hf).
Qed.

(* the triangle inequality for a complex improper integral, from the
   pointwise bound  c fr + s fi <= f  for every unit vector (c, s):
   |L| = c re L + s im L  with  (c, s) = L / |L|  (Mathlib's
   norm_integral_le_integral_norm, rebuilt) *)
Lemma cnorm_CIntInf_le : forall fr fi f a L A,
  CIntInf fr fi a L -> RIntInf f a A ->
  (forall x, a <= x -> 0 <= f x) ->
  (forall x c s, a <= x -> c * c + s * s = 1 -> c * fr x + s * fi x <= f x) ->
  cnorm L <= A.
Proof.
  intros fr fi f a L A [Hr Hi] HA Hf0 Hpt.
  pose proof (RIntInf_zero_le f a A HA Hf0) as HA0.
  set (n := cnorm L).
  assert (Hn0 : 0 <= n) by apply sqrt_pos.
  assert (Hn2 : n * n = cre L * cre L + cim L * cim L).
  { unfold n, cnorm. apply sqrt_sqrt. nra. }
  destruct (Req_dec n 0) as [Hz|Hnz]; [lra|].
  assert (Hnp : 0 < n) by lra.
  set (c := cre L / n). set (s := cim L / n).
  assert (Hcs : c * c + s * s = 1).
  { unfold c, s. replace (cre L / n * (cre L / n) + cim L / n * (cim L / n))
      with ((cre L * cre L + cim L * cim L) / (n * n)) by (field; lra).
    rewrite <- Hn2. field. lra. }
  assert (Hv : RIntInf (fun x => c * fr x + s * fi x) a (c * cre L + s * cim L)).
  { apply RIntInf_plus; apply RIntInf_scal; assumption. }
  assert (Hval : c * cre L + s * cim L = n).
  { unfold c, s. replace (cre L / n * cre L + cim L / n * cim L)
      with ((cre L * cre L + cim L * cim L) / n) by (field; lra).
    rewrite <- Hn2. field. lra. }
  rewrite <- Hval. apply (RIntInf_le _ _ a _ _ Hv HA). intros x Hx. apply Hpt; assumption.
Qed.

Section WindowIneq.
Variables (g Rm : R -> R) (C0 sigma theta U V gam : R) (k : nat).
Hypothesis hC : forall u, 0 <= u -> Rabs (g u) <= C0 * exp (2 * u).
Hypothesis hsig : 2 < sigma.
Hypothesis htheta : theta < sigma.
Hypothesis hU : 0 < U.
Hypothesis hR' : forall u, U <= u <= V -> 0 <= Rm u /\ g u <= Rm u.

(* w u = u^k e^(-sigma u) / k!,  h u = u^k e^((2 - sigma) u) / k! *)
Definition ww (u : R) : R := u ^ k * exp (- sigma * u) / INR (fact k).
Definition hh (u : R) : R := u ^ k * exp ((2 - sigma) * u) / INR (fact k).
Definition pp (u : R) : R := Rabs (g u) * ww u + g u * ww u.
(* the complex integrand  g u u^k e^(-(sigma + i gam) u) / k!  in parts *)
Definition cfr (gm u : R) : R := g u * ww u * cos (gm * u).
Definition cfi (gm u : R) : R := - (g u * ww u * sin (gm * u)).

Lemma fact_pos' : 0 < INR (fact k).
Proof. apply lt_0_INR. apply lt_O_fact. Qed.

Lemma ww_nonneg : forall u, 0 <= u -> 0 <= ww u.
Proof.
  intros u Hu. unfold ww, Rdiv. pose proof fact_pos'. pose proof (exp_pos (- sigma * u)).
  pose proof (pow_le u k Hu). apply Rmult_le_pos; [apply Rmult_le_pos; lra|].
  left. apply Rinv_0_lt_compat. lra.
Qed.

Lemma C0_nonneg : 0 <= C0.
Proof. pose proof (hC 0 (Rle_refl 0)). pose proof (Rabs_pos (g 0)). pose proof (exp_pos (2 * 0)). nra. Qed.

Lemma hh_eq : forall u, hh u = exp (2 * u) * ww u.
Proof.
  intro u. unfold hh, ww. replace ((2 - sigma) * u) with (2 * u + - sigma * u) by ring.
  rewrite exp_plus. field. pose proof fact_pos'. lra.
Qed.

(* hb:  |g u| w u <= C0 h u  for u >= 0 *)
Lemma hb : forall u, 0 <= u -> Rabs (g u) * ww u <= C0 * hh u.
Proof.
  intros u Hu. rewrite hh_eq. pose proof (ww_nonneg u Hu). pose proof (hC u Hu). nra.
Qed.

Lemma pp_le_hh : forall u, 0 <= u -> pp u <= 2 * C0 * hh u.
Proof.
  intros u Hu. unfold pp. pose proof (hb u Hu). pose proof (ww_nonneg u Hu).
  pose proof (Rle_abs (g u)). nra.
Qed.

Lemma pp_nonneg : forall u, 0 <= u -> 0 <= pp u.
Proof.
  intros u Hu. unfold pp. pose proof (ww_nonneg u Hu).
  pose proof (Rle_abs (- g u)). rewrite Rabs_Ropp in H0. nra.
Qed.

(* p is bounded on every [0, T] (for Chasles) *)
Lemma pp_bounded : forall T, exists M, forall x, 0 <= x <= T -> Rabs (pp x) <= M.
Proof.
  intro T. exists (2 * C0 * (Rabs T) ^ k). intros x Hx.
  rewrite Rabs_right by (apply Rle_ge, pp_nonneg; lra).
  eapply Rle_trans; [apply pp_le_hh; lra|].
  pose proof C0_nonneg. apply Rmult_le_compat_l; [lra|].
  unfold hh, Rdiv. pose proof fact_pos'. pose proof (fact_ge1 k).
  pose proof (exp_le1 ((2 - sigma) * x) ltac:(nra)). pose proof (exp_pos ((2 - sigma) * x)).
  assert (Hxk : x ^ k <= Rabs T ^ k).
  { apply pow_incr. split; [lra|]. rewrite Rabs_right; lra. }
  pose proof (pow_le x k ltac:(lra)).
  assert (Hi : / INR (fact k) <= 1).
  { rewrite <- Rinv_1. apply Rinv_le_contravar; lra. }
  assert (Hi0 : 0 < / INR (fact k)) by (apply Rinv_0_lt_compat; lra).
  assert (x ^ k * exp ((2 - sigma) * x) <= x ^ k) by nra.
  assert (x ^ k * exp ((2 - sigma) * x) * / INR (fact k) <= x ^ k * exp ((2 - sigma) * x)).
  { assert (0 <= x ^ k * exp ((2 - sigma) * x)) by (apply Rmult_le_pos; lra). nra. }
  lra.
Qed.

(* landau_window_ineq (landauWindowIneq.lean), over R.  The integrals are
   values (CIntInf: real and imaginary parts as improper Riemann
   integrals; RInt/RIntInf from CleanIntegralQED).  Lean derives their
   existence from measurability and domination (Integrable.mono'), which
   has no Riemann analogue; here the values are premises, as for
   landau_tails_chernoff.  The region (0, oo) \ [U, V] is [0, U] + [V, oo). *)
Theorem landau_window_ineq_R : forall Lg L0 A J P1 P2 P3 H1 H2,
  CIntInf (cfr gam) (cfi gam) 0 Lg ->                  (* int_(0,oo) g u^k e^(-(sigma + i gam) u)/k! *)
  CIntInf (cfr 0) (cfi 0) 0 L0 ->                      (* int_(0,oo) g u^k e^(-sigma u)/k! *)
  RIntInf (fun u => Rabs (g u) * ww u) 0 A ->
  RInt (fun u => Rm u * exp (- theta * u)) U V J ->   (* hR *)
  RInt pp 0 U P1 -> RInt pp U V P2 -> RIntInf pp V P3 ->
  RInt hh 0 U H1 -> RIntInf hh V H2 ->
  cnorm Lg <= 2 * (1 / (sigma - theta) ^ k) * J - cre L0 + 2 * C0 * (H1 + H2).
Proof.
  intros Lg L0 A J P1 P2 P3 H1 H2 HLg HL0 HA HJ HP1 HP2 HP3 HH1 HH2.
  pose proof C0_nonneg as HC0.
  assert (HUV : U <= V) by exact (RInt_le_ab _ _ _ _ HP2).
  (* hL: |int f| <= int |g| w *)
  assert (HL : cnorm Lg <= A).
  { apply (cnorm_CIntInf_le (cfr gam) (cfi gam) (fun u => Rabs (g u) * ww u) 0 Lg A HLg HA).
    - intros x Hx. pose proof (ww_nonneg x Hx). pose proof (Rabs_pos (g x)). nra.
    - intros x c s Hx Hcs. unfold cfr, cfi.
      set (t := c * cos (gam * x) - s * sin (gam * x)).
      assert (Ht2 : t * t <= 1).
      { pose proof (sin2_cos2 (gam * x)) as E. unfold Rsqr in E. unfold t.
        assert (I : (c * cos (gam * x) - s * sin (gam * x)) * (c * cos (gam * x) - s * sin (gam * x))
                    + (c * sin (gam * x) + s * cos (gam * x)) * (c * sin (gam * x) + s * cos (gam * x))
                    = (c * c + s * s) * (sin (gam * x) * sin (gam * x) + cos (gam * x) * cos (gam * x))) by ring.
        rewrite Hcs, E in I.
        pose proof (Rle_0_sqr (c * sin (gam * x) + s * cos (gam * x))) as Q. unfold Rsqr in Q. lra. }
      assert (Ht : -1 <= t <= 1) by (split; nra).
      replace (c * (g x * ww x * cos (gam * x)) + s * - (g x * ww x * sin (gam * x))) with (g x * ww x * t) by (unfold t; ring).
      clearbody t.
      pose proof (ww_nonneg x Hx).
      destruct (Rle_or_lt 0 (g x)) as [Hg|Hg].
      + rewrite Rabs_right by lra.
        assert (0 <= g x * ww x * (1 - t)) by (apply Rmult_le_pos; [apply Rmult_le_pos|]; lra). nra.
      + rewrite Rabs_left by lra.
        assert (0 <= (- g x) * ww x * (1 + t)) by (apply Rmult_le_pos; [apply Rmult_le_pos|]; lra). nra. }
  (* hM: Re int_(0,oo) g u^k e^(-sigma u)/k! = int g w *)
  assert (HM : RIntInf (fun u => g u * ww u) 0 (cre L0)).
  { destruct HL0 as [Hr _]. apply (RIntInf_ext (cfr 0)); [|exact Hr].
    intros x _. unfold cfr. rewrite Rmult_0_l, cos_0. ring. }
  (* hsplit: int_(0,oo) (|g| w + g w) = int_[0,U] + int_[U,V] + int_[V,oo) *)
  assert (Hsum : A + cre L0 = P1 + P2 + P3).
  { assert (Hall : RIntInf pp 0 (A + cre L0)) by (apply (RIntInf_plus _ _ 0 A (cre L0) HA HM)).
    assert (H12 : RInt pp 0 V (P1 + P2)).
    { destruct (pp_bounded V) as [M HMb]. apply (RInt_chasles pp 0 U V M P1 P2); [|exact HP1|exact HP2].
      exact HMb. }
    assert (H123 : RIntInf pp 0 (P1 + P2 + P3)).
    { apply RIntInf_chasles with (b := V); [|exact H12|exact HP3].
      intros T _. destruct (pp_bounded T) as [M HMb]. exists M. exact HMb. }
    exact (RIntInf_unique pp 0 _ _ Hall H123). }
  (* hA: the window part *)
  assert (HA2 : P2 <= 2 * (1 / (sigma - theta) ^ k) * J).
  { apply (RInt_le pp (fun u => 2 * (1 / (sigma - theta) ^ k) * (Rm u * exp (- theta * u))) U V); [exact HP2| |].
    - apply RInt_scal. exact HJ.
    - intros u Hu. destruct (hR' u Hu) as [HR0 HgR]. assert (Hu0 : 0 <= u) by lra.
      assert (H3 : Rabs (g u) + g u <= 2 * Rm u).
      { destruct (Rle_or_lt 0 (g u)); [rewrite Rabs_right by lra|rewrite Rabs_left by lra]; lra. }
      assert (H4 : ww u <= 1 / (sigma - theta) ^ k * exp (- theta * u)).
      { pose proof (landau_kernel_max k (sigma - theta) u ltac:(lra) Hu0) as H5.
        replace (ww u) with (u ^ k * exp (- (sigma - theta) * u) / INR (fact k) * exp (- theta * u)).
        - apply Rmult_le_compat_r; [left; apply exp_pos|exact H5].
        - unfold ww. replace (- sigma * u) with (- (sigma - theta) * u + - theta * u) by ring.
          rewrite exp_plus. field. pose proof fact_pos'. lra. }
      pose proof (ww_nonneg u Hu0). unfold pp.
      replace (Rabs (g u) * ww u + g u * ww u) with ((Rabs (g u) + g u) * ww u) by ring.
      pose proof (Rmult_le_compat_r _ _ _ H H3).
      pose proof (Rmult_le_compat_l (2 * Rm u) _ _ ltac:(lra) H4). nra. }
  (* hB: the complement *)
  assert (HB1 : P1 <= 2 * C0 * H1).
  { apply (RInt_le pp (fun u => 2 * C0 * hh u) 0 U); [exact HP1|apply RInt_scal; exact HH1|].
    intros u Hu. apply pp_le_hh. lra. }
  assert (HB3 : P3 <= 2 * C0 * H2).
  { apply (RIntInf_le pp (fun u => 2 * C0 * hh u) V); [exact HP3|apply RIntInf_scal; exact HH2|].
    intros u Hu. apply pp_le_hh. lra. }
  lra.
Qed.
End WindowIneq.

Print Assumptions landau_window_ineq_R.

(* ===================================================================== *)
(* Part C: TopG refined (CharacterBoxes/ShapeWin.lean : shapeWin, and    *)
(*         EveryCharacter.lean : plugWin)                                 *)
(* Part D: HostExW refined (CharacterBoxes/SupplyChi.lean : supplyChi,   *)
(*         CoprimeRanks/AdmChi.lean : admissibleClassesTwistedChar)       *)
(* ===================================================================== *)
Section TopRefined.
(* the carriers of AlpogeDeepStatements' TopStatements section *)
Variable Ranks : Type.
Variable Host : Ranks -> Type.
Variable HostCT2 : forall Rk, Host Rk -> R.
Variable RankVal : Scale -> Ranks -> Prop.
Variable HostGood : Scale -> R -> R -> R -> R -> forall Rk, Host Rk -> nat -> Prop.
Variable FamP : R -> Type.
Variable fx1 : forall eps, FamP eps -> R.
Variable fIx : forall eps, FamP eps -> R -> Type.
Variable fWin : forall eps, FamP eps -> R -> Prop.
Variable ChainTied : forall eps, FamP eps -> R -> R -> R -> R -> R -> R -> R -> Prop.
Variable VV : forall eps (Fm : FamP eps) x, fIx eps Fm x -> Prop.
Variable FReq : Type.
Variable req : FReq -> HostReq Ranks Host.
Variable At : FReq -> forall eps (Fm : FamP eps) x, fIx eps Fm x -> Prop.

Local Notation FamCl := (forall eps, FamP eps -> Prop).
Local Notation HostExW' := (HostExW Ranks Host HostCT2 RankVal HostGood).
Local Notation cls' := (cls FamP fx1 fIx fWin FReq At).
Local Notation HypV' := (@HypV FamP fIx VV).
Local Notation FCC := (FamilyClassConnected FamP fWin ChainTied).
Local Notation TopG' := (TopG Ranks Host HostCT2 RankVal HostGood FamP fx1 fIx fWin ChainTied VV FReq req At).

Definition sub (B C : FamCl) : Prop := forall eps (Fm : FamP eps), B eps Fm -> C eps Fm.
Definition capc (B C : FamCl) : FamCl := fun eps Fm => B eps Fm /\ C eps Fm.

(* ---- C. shapeWin ----
   TopShape V NR N G (TopShape.lean) quantifies over the whole shape data
   (the class 𝒜, cT, hEx, sel, hduty, selS, ..., hU, hG): here the type
   Data with its class Acl.  The ONLY datum that mentions (la, G) is
   hEx : MinkDiv -> ExS 𝒜 cT  (ExS.lean), and the ONLY other (la, G)-
   dependent input of the proof is TopG's own premise hV.  Everything else
   feeds the la-, G-independent link facts on WithChN 𝒜. *)
Variable Data : Type.
Variable Acl : Data -> FamCl.                         (* 𝒜 *)
Variable MinkDiv : Prop.
Variable DCh : Data -> FamCl -> Prop.                 (* DesignChoices (WithTw E) 3 cT *)
Variable ChN : FamCl.                                 (* WithChN E = E /\ ChN *)
Definition WithChN (E : FamCl) : FamCl := capc E ChN.
Variable Green : Prop.                                (* GlobalTheory.GLq.Green *)
Variable LinkEx : Data -> FamCl -> Prop.              (* the DesWin data link_ex produces *)
Variable Rest : Data -> FamCl -> Prop.                (* nRest, link_eta, link_irr, smallLevelRankEq,
                                                         linkDIVt, link_gl (both parts), link_g, link_alt *)

(* ExS 𝒜 cT (ExS.lean): every (la, G) with a host supply gives design
   choices for the subclass 𝒜 /\ G.cls la *)
Definition ExS (d : Data) : Prop :=
  forall la (G : FReq), 1 < la -> HostExW' la (req G) -> DCh d (capc (Acl d) (cls' G la)).

(* [inventory] GlobalTheory.Top.link_ex (LinkEx.lean), at a subclass B of 𝒜
   (its sel/hduty/hTu/hn4 inputs are 𝒜's, restricted along B ⊆ 𝒜 by
   Pk.Closed.sub) *)
Hypothesis link_ex : forall d (B : FamCl), sub B (Acl d) -> (MinkDiv -> DCh d B) -> LinkEx d (WithChN B).
(* [inventory] link_gl, link_brest, closed_family_admissible_twist_link,
   selection_closed_of_wu_decay, linkDIVt_closedK, link_eta, link_irr
   (needs Green), smallLevelRankEq_closed_..., link_g, link_alt *)
Hypothesis links : Green -> forall d, Rest d (WithChN (Acl d)).
(* [inventory] UpperTheory.Top.topDesWin (DesWin.lean) *)
Hypothesis topDesWin : forall d (Aall B C : FamCl), LinkEx d B -> sub B Aall -> sub B C ->
  (forall eps (Fm : FamP eps), C eps Fm -> HypV' Fm) -> Rest d Aall -> FCC C.

(* shapeWin : Green -> TopShape True True _ TopG, the shape datum being
   (d, hEx) *)
Theorem shapeWin_r : Green -> forall d, (MinkDiv -> ExS d) -> TopG'.
Proof.
  intros hGreen d hEx la G hla hH hV.
  (* hE := link_ex (𝒜 /\ G.cls la) cT (fun hM => hEx hM la G hla hH) ... *)
  assert (hE : LinkEx d (WithChN (capc (Acl d) (cls' G la)))).
  { apply link_ex.
    - intros eps Fm hc. exact (proj1 hc).
    - intro hM. exact (hEx hM la G hla hH). }
  (* topDesWin (WithChN 𝒜) (WithChN (𝒜 /\ G.cls la)) (G.cls la) ... hE
       (fun _ hc => ⟨hc.1.1, hc.2⟩) (fun _ hc => hc.1.2) hV ... *)
  apply (topDesWin d (WithChN (Acl d)) (WithChN (capc (Acl d) (cls' G la))) (cls' G la) hE).
  - intros eps Fm hc. split; [exact (proj1 (proj1 hc))|exact (proj2 hc)].
  - intros eps Fm hc. exact (proj2 (proj1 hc)).
  - exact hV.
  - exact (links hGreen d).
Qed.

(* plugWin (EveryCharacter.lean): Nonempty (Hyps ...) supplies the shape
   datum (GlobalTheory.Fc.shape_of / of_hyps), so TopG holds outright *)
Theorem topG_of_hyps : Green -> (exists d, MinkDiv -> ExS d) -> TopG'.
Proof. intros hG [d hd]. exact (shapeWin_r hG d hd). Qed.

(* ---- D. HostExW via supplyChi ---- *)
Variable PChar : Type.
Variable GChi : PChar -> FReq.
Variable VWinAt : PChar -> R -> Prop.
Variable Frame : Type.
Variable HostAx : Frame -> Type.
Variable toFrame : Ranks -> Frame.
Variable ford : Frame -> R.                           (* (φ.ord : ℝ) *)
Variable OkO : PChar -> Frame -> Prop.                (* φ.o = (Level.cyc ψ).o *)
Variable KerChi : forall (psi : PChar) (phi : Frame), HostAx phi -> Prop.
Variable admittedR : forall Rk, HostAx (toFrame Rk) -> Prop.

Definition transp {phi} (Rk : Ranks) (h : toFrame Rk = phi) (H0 : HostAx phi) : HostAx (toFrame Rk) :=
  eq_rect phi HostAx H0 (toFrame Rk) (eq_sym h).

(* the premise of supplyOfAdm at psi: frames in the window
   [x^(2+8 eps), 2 x^(2+8 eps)] with KerChi carry an admitted rank (Lean: admitted) *)
Definition AdmPrem (psi : PChar) : Prop :=
  forall eps, 0 < eps -> eps < 1 / 52 -> exists x0, forall (s : Scale) (phi : Frame) (H0 : HostAx phi),
    seps s = eps -> x0 <= sx s ->
    rpc (sx s) (2 + 8 * eps) <= ford phi -> ford phi <= 2 * rpc (sx s) (2 + 8 * eps) ->
    OkO psi phi -> KerChi psi phi H0 ->
    exists (Rk : Ranks) (h : toFrame Rk = phi), RankVal s Rk /\ admittedR Rk (transp Rk h H0).

(* [inventory] UpperTheory.Top.supplyOfAdm (HostOfField.lean) =
   supplyOfAdmOf hostOfField *)
Hypothesis supplyOfAdm : forall psi, VWinAt psi 401 -> AdmPrem psi -> HostExW' (3 / 2) (req (GChi psi)).
(* [inventory] admissibleClassesTwistedChar (AdmChi.lean), stated with the
   scale's own exponent s.eps *)
Hypothesis admissibleClassesTwistedChar :
  forall eps, 0 < eps -> eps < 1 / 52 -> exists x0, forall (s : Scale) (phi : Frame) (H0 : HostAx phi),
    seps s = eps -> x0 <= sx s ->
    rpc (sx s) (2 + 8 * seps s) <= ford phi -> ford phi <= 2 * rpc (sx s) (2 + 8 * seps s) ->
    exists (Rk : Ranks) (h : toFrame Rk = phi), RankVal s Rk /\ admittedR Rk (transp Rk h H0).

(* supplyChi : forall psi, VWinAt psi 401 -> HostExW (3/2) (GChi psi).req *)
Theorem supplyChi_r : forall psi, VWinAt psi 401 -> HostExW' (3 / 2) (req (GChi psi)).
Proof.
  intros psi hpsi. apply (supplyOfAdm psi hpsi).
  intros eps he0 he1.
  destruct (admissibleClassesTwistedChar eps he0 he1) as [x0 hx0].
  exists x0. intros s phi H0 hs hx hlo hhi _ _.
  (* subst hs: the window exponent is the scale's own *)
  subst eps. exact (hx0 s phi H0 eq_refl hx hlo hhi).
Qed.

(* hS of plugWin: HostExW_main_statement at la = 3/2, from VWin *)
Theorem hostExW_main_r : (forall psi, VWinAt psi 401) ->
  HostExW_main_statement Ranks Host HostCT2 RankVal HostGood FReq req PChar GChi (3 / 2).
Proof. intros hV psi. exact (supplyChi_r psi (hV psi)). Qed.
End TopRefined.

Print Assumptions shapeWin_r.
Print Assumptions topG_of_hyps.
Print Assumptions supplyChi_r.
Print Assumptions hostExW_main_r.

(* ===================================================================== *)
(* Part E: windowHypU_of_windowHyp over R (WindowHypUOfWindowHyp.lean)    *)
(* ===================================================================== *)
(* E1 (RInt_bounded) and E2 (RInt_exp_change) live in theories/TaggedIntegralChange.v *)

(* E3. windowHypU_of_windowHyp.  WindowHypR (CleanIntegralQED, Lean's
   WindowHyp with RInt) gives WindowHypU (LandauZeroFreeCriterion.lean l.25)
   for g u = Gm (e^u), with U = log Y and the majorant R o exp. *)
Definition WindowHypUR (g : R -> R) (theta delta : R) : Prop :=
  forall eta, 0 < eta -> forall U0, exists U, U0 <= U /\ exists Rm : R -> R,
    (forall u, U <= u -> u <= (1 + delta) * U -> 0 <= Rm u /\ g u <= Rm u) /\
    exists I, RInt (fun u => Rm u * exp (- theta * u)) U ((1 + delta) * U) I /\ I <= exp (eta * U).

Theorem windowHypU_of_windowHyp_R : forall (Gm : R -> R) theta delta, 0 < delta ->
  WindowHypR Gm theta delta -> WindowHypUR (fun u => Gm (exp u)) theta delta.
Proof.
  intros Gm theta delta Hd h eta Heta U0.
  destruct (h eta Heta (Rmax (exp U0) 1)) as [Y [HY [Rm [HR [I [HI Hb]]]]]].
  assert (HY1 : 1 <= Y) by (eapply Rle_trans; [apply Rmax_r|exact HY]).
  assert (HYe : exp U0 <= Y) by (eapply Rle_trans; [apply Rmax_l|exact HY]).
  assert (HYp : 0 < Y) by lra.
  exists (Lc Y). split.
  { rewrite <- (Lc_exp U0). apply Lc_le_mono; [apply exp_pos|exact HYe]. }
  assert (HL0 : 0 <= Lc Y) by (rewrite <- Lc_1; apply Lc_le_mono; lra).
  exists (fun u => Rm (exp u)). split.
  - intros u Hu1 Hu2. destruct (exp_window_map Y delta u HY1 (conj Hu1 Hu2)) as [E1 E2].
    apply HR; assumption.
  - exists I. split.
    + cbv beta.
      apply (RInt_ext (fun u => (fun y => Rm y * rpc y (- theta - 1)) (exp u) * exp u)
                      (fun u => Rm (exp u) * exp (- theta * u))).
      * intros u _. simpl. unfold rpc. rewrite Lc_exp, Rmult_assoc. f_equal.
        replace (exp u) with (exp (1 * u)) at 2 by (f_equal; ring). rewrite <- exp_plus. f_equal. ring.
      * apply (RInt_exp_change (fun y => Rm y * rpc y (- theta - 1))); [nra|].
        rewrite exp_Lc by exact HYp. replace (exp ((1 + delta) * Lc Y)) with (rpc Y (1 + delta)) by reflexivity.
        exact HI.
    + replace (exp (eta * Lc Y)) with (rpc Y eta) by reflexivity. exact Hb.
Qed.

Print Assumptions windowHypU_of_windowHyp_R.
