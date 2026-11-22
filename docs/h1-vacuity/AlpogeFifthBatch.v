(* AlpogeFifthBatch.v -- two more refined main-line lemmas of the claimed
   RH/GRH Lean development (CocoSgt/riemann-hypothesis-lean @ 7cbf7a0)
   PROVED over Stdlib's R, and two unrefined ones REFINED from the Lean
   proof, all within the three-axiom allowlist (docs/axiom-allowlist.txt).

   Proved over R, with the allowlist-clean integral library of #1047
   (CleanIntegralQED.v: RInt, RIntInf, FTC_C1, kernel antiderivative Gk):
     A  landau_tails_chernoff   (LandauTheorems/landauTails.lean)
     B  landau_coeff            (LandauTheorems/LandauCoeff.lean)

   Refined (the Lean proof's reasoning rebuilt; the Mathlib facts it cites
   are named hypotheses), over an abstract field K standing for C:
     C  sum_A    (ChCore.lean l.28): the subgroup-orthogonality of characters
     D  sum_Th   (ChCore.lean l.56): the orthogonality identity used by core

   Evidence for docs/attacks/2026-11-22-alpoge-fifth-batch.md.
   NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import Reals Lra Psatz Lia List Factorial Ring Field Permutation.
From NTS.Proofs.Probes Require Import AlpogeRealsQED AlpogeRealsQED2 AlpogeDeepStatements CleanIntegralQED.
Import ListNotations.
Local Open Scope R_scope.

(* ===================================================================== *)
(* Part A: landau_tails_chernoff                                          *)
(* ===================================================================== *)
(* gk k a u = u^k e^(-a u)/k!, with antiderivative Gk k a (CleanIntegralQED). *)

Lemma kernel_RInt_ab : forall k a V T, 0 < a -> 0 <= V -> V <= T ->
  RInt (gk k a) V T (Gk k a T - Gk k a V).
Proof.
  intros k a V T Ha HV HT.
  apply (FTC_C1 (Gk k a) (gk k a)
           (fun u => (INR k * u ^ pred k - a * u ^ k) * exp (- (a * u)) / INR (fact k))
           V T (INR k * T ^ pred k + a * T ^ k) HT).
  - intros x _. apply Gk_deriv. exact Ha.
  - intros x _. apply gk_deriv.
  - intros x Hx. apply gk_deriv_bound; [exact Ha|lra].
Qed.

(* Gk k a T -> 0 as T -> oo (the limit step of kernel_integral) *)
Lemma Gk_lim : forall k a V, 0 < a -> forall e, 0 < e -> exists T0, V <= T0 /\
  forall T, T0 <= T -> Rabs (Gk k a T - 0) < e.
Proof.
  intros k a V Ha e He.
  set (c := / a ^ S k). set (C := INR (S k) * INR (fact (S k))).
  assert (Hc : 0 < c) by (unfold c; apply Rinv_0_lt_compat, pow_lt; exact Ha).
  assert (HC : 0 < C).
  { unfold C. apply Rmult_lt_0_compat; [apply lt_0_INR; lia|pose proof (fact_ge1 (S k)); lra]. }
  assert (Hce : 0 <= c * C / e) by (apply Rmult_le_pos; [nra|left; apply Rinv_0_lt_compat; lra]).
  exists (Rmax V ((c * C / e + 1) / a)). split; [apply Rmax_l|].
  intros T HT. assert (HT' : (c * C / e + 1) / a <= T) by (eapply Rle_trans; [apply Rmax_r|exact HT]).
  assert (Hx : c * C / e + 1 <= a * T).
  { apply (Rmult_le_compat_l a) in HT'; [|lra].
    replace (a * ((c * C / e + 1) / a)) with (c * C / e + 1) in HT' by (field; lra). exact HT'. }
  assert (Hx1 : 1 <= a * T) by lra.
  pose proof (exp_Pk_decay k (a * T) Hx1) as Hdec. fold C in Hdec.
  pose proof (Pk_nonneg k (a * T) ltac:(lra)) as HP. pose proof (exp_pos (- (a * T))) as HEp.
  unfold Gk. fold c. rewrite Rminus_0_r.
  rewrite Rabs_left1 by (assert (0 <= exp (- (a * T)) * Pk k (a * T)) by nra; nra).
  assert (HcC : c * C / (a * T) < e).
  { apply (Rmult_lt_reg_r (a * T)); [lra|]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra.
    replace (c * C) with (c * C / e * e) by (field; lra). nra. }
  assert (Hb : c * (exp (- (a * T)) * Pk k (a * T)) <= c * (C / (a * T)))
    by (apply Rmult_le_compat_l; lra).
  unfold Rdiv in HcC, Hb. nra.
Qed.

(* e^(-x) P_k(x) <= 1 for x >= 0 *)
Lemma expPk_le1 : forall k x, 0 <= x -> exp (- x) * Pk k x <= 1.
Proof.
  intros k x Hx. pose proof (exp_ge_Pk k x Hx). pose proof (exp_pos (- x)).
  assert (E : exp (- x) * exp x = 1) by (rewrite <- exp_plus; replace (- x + x) with 0 by ring; apply exp_0).
  assert (exp (- x) * Pk k x <= exp (- x) * exp x) by (apply Rmult_le_compat_l; lra). lra.
Qed.

(* the tail: int_V^oo gk k a = -Gk k a V <= a^-(k+1) *)
Lemma kernel_tail : forall k a V, 0 < a -> 0 <= V ->
  RIntInf (gk k a) V (- Gk k a V) /\ - Gk k a V <= / a ^ S k.
Proof.
  intros k a V Ha HV. split.
  - replace (- Gk k a V) with (0 - Gk k a V) by ring.
    apply (RIntInf_of_antideriv _ (Gk k a) V 0).
    + intros T HT. apply kernel_RInt_ab; lra.
    + intros e He. exact (Gk_lim k a V Ha e He).
  - unfold Gk. pose proof (expPk_le1 k (a * V) ltac:(nra)) as H.
    assert (Hc : 0 < / a ^ S k) by (apply Rinv_0_lt_compat, pow_lt; exact Ha).
    replace (- (a * V)) with (- (a * V)) in H by ring. nra.
Qed.

(* the head: int_0^U gk k a = Gk U - Gk 0 <= a^-(k+1) *)
Lemma kernel_head_le : forall k a U, 0 < a -> 0 <= U -> Gk k a U - Gk k a 0 <= / a ^ S k.
Proof.
  intros k a U Ha HU. rewrite Gk_0. unfold Gk.
  assert (Hc : 0 < / a ^ S k) by (apply Rinv_0_lt_compat, pow_lt; exact Ha).
  pose proof (Pk_nonneg k (a * U) ltac:(nra)). pose proof (exp_pos (- (a * U))).
  assert (0 <= exp (- (a * U)) * Pk k (a * U)) by nra. nra.
Qed.

(* landau_tails_chernoff: for 0 <= l < s, the integral of u^k e^(-s u)/k!
   over (0, oo) \ [U, V] -- here int_0^U + int_V^oo, U <= V -- is at most
   e^(-l V) (s-l)^-(k+1) + e^(l U) (s+l)^-(k+1). *)
Theorem landau_tails_chernoff : forall k s l U V I1 I2,
  0 <= l -> l < s -> 0 <= U -> U <= V ->
  RInt (gk k s) 0 U I1 -> RIntInf (gk k s) V I2 ->
  I1 + I2 <= exp (- (l * V)) * / (s - l) ^ S k + exp (l * U) * / (s + l) ^ S k.
Proof.
  intros k s l U V I1 I2 Hl Hls HU HUV H1 H2.
  assert (HA : 0 < s - l) by lra. assert (HB : 0 < s + l) by lra.
  assert (Hgk0 : forall u, 0 <= u -> 0 <= u ^ k / INR (fact k)).
  { intros u Hu. apply Rmult_le_pos; [apply pow_le; exact Hu|left; apply Rinv_0_lt_compat, INR_fact_lt_0]. }
  (* head: gk k s u <= e^(l U) gk k (s+l) u on [0, U] *)
  assert (Hhead : I1 <= exp (l * U) * (Gk k (s + l) U - Gk k (s + l) 0)).
  { apply (RInt_le (gk k s) (fun u => exp (l * U) * gk k (s + l) u) 0 U); [exact H1| |].
    - apply RInt_scal. apply kernel_RInt_ab; lra.
    - intros u [Hu1 Hu2]. unfold gk.
      assert (Ee : exp (l * U) * exp (- ((s + l) * u)) = exp (- (s * u)) * exp (l * (U - u)))
        by (rewrite <- !exp_plus; f_equal; ring).
      replace (exp (l * U) * (u ^ k * exp (- ((s + l) * u)) / INR (fact k)))
        with (u ^ k / INR (fact k) * (exp (- (s * u)) * exp (l * (U - u))))
        by (unfold Rdiv; rewrite <- Ee; ring).
      replace (u ^ k * exp (- (s * u)) / INR (fact k)) with (u ^ k / INR (fact k) * exp (- (s * u))) by (unfold Rdiv; ring).
      apply Rmult_le_compat_l; [apply (Hgk0 u Hu1)|].
      assert (1 <= exp (l * (U - u))) by (pose proof (add_one_le_exp (l * (U - u))); nra).
      pose proof (exp_pos (- (s * u))). nra. }
  (* tail: gk k s u <= e^(-l V) gk k (s-l) u on [V, oo) *)
  destruct (kernel_tail k (s - l) V HA ltac:(lra)) as [Htail Htail_le].
  assert (Htl : I2 <= exp (- (l * V)) * (- Gk k (s - l) V)).
  { apply (RIntInf_le (gk k s) (fun u => exp (- (l * V)) * gk k (s - l) u) V); [exact H2|apply RIntInf_scal; exact Htail|].
    intros u Hu. unfold gk.
    assert (Ee : exp (- (l * V)) * exp (- ((s - l) * u)) = exp (- (s * u)) * exp (l * (u - V)))
      by (rewrite <- !exp_plus; f_equal; ring).
    replace (exp (- (l * V)) * (u ^ k * exp (- ((s - l) * u)) / INR (fact k)))
      with (u ^ k / INR (fact k) * (exp (- (s * u)) * exp (l * (u - V))))
      by (unfold Rdiv; rewrite <- Ee; ring).
    replace (u ^ k * exp (- (s * u)) / INR (fact k)) with (u ^ k / INR (fact k) * exp (- (s * u))) by (unfold Rdiv; ring).
    apply Rmult_le_compat_l; [apply (Hgk0 u); lra|].
    assert (1 <= exp (l * (u - V))) by (pose proof (add_one_le_exp (l * (u - V))); nra).
    pose proof (exp_pos (- (s * u))). nra. }
  pose proof (kernel_head_le k (s + l) U HB HU) as Hh.
  pose proof (exp_pos (l * U)). pose proof (exp_pos (- (l * V))).
  assert (exp (l * U) * (Gk k (s + l) U - Gk k (s + l) 0) <= exp (l * U) * / (s + l) ^ S k)
    by (apply Rmult_le_compat_l; lra).
  assert (exp (- (l * V)) * (- Gk k (s - l) V) <= exp (- (l * V)) * / (s - l) ^ S k)
    by (apply Rmult_le_compat_l; lra).
  lra.
Qed.

Print Assumptions landau_tails_chernoff.

(* ===================================================================== *)
(* Part B: landau_coeff                                                   *)
(* ===================================================================== *)
(* complex improper integrals, as real and imaginary parts *)
Definition CIntInf (fr fi : R -> R) (a : R) (L : Cc) : Prop := RIntInf fr a (cre L) /\ RIntInf fi a (cim L).

Lemma RIntInf_ext : forall f g a I, (forall x, a <= x -> f x = g x) -> RIntInf f a I -> RIntInf g a I.
Proof.
  intros f g a I Hfg HI e He. destruct (HI e He) as [T0 [A0 H0]]. exists T0. split; [exact A0|].
  intros T HT. destruct (H0 T HT) as [J [HJ LJ]]. exists J. split; [|exact LJ].
  apply (RInt_ext f g a T J); [intros x Hx; apply Hfg; lra|exact HJ].
Qed.

Section Coeff.
Variable g : R -> R.                                 (* g = gm F *)
Variable D : nat -> Cc -> Cc.                        (* iteratedDeriv k Phi s *)
(* [inventory] iteratedDeriv_laplace, with PoleData.laplace near s:
   Phi^(k)(s) = int_0^oo g u (-u)^k e^(-s u) du  for Re s > 2 *)
Hypothesis ILAP : forall (k : nat) s, 2 < cre s ->
  CIntInf (fun u => g u * (- u) ^ k * exp (- cre s * u) * cos (cim s * u))
          (fun u => - (g u * (- u) ^ k * exp (- cre s * u) * sin (cim s * u))) 0 (D k s).

(* landau_coeff: (-1)^k Phi^(k)(s) / k! = int_0^oo g u u^k e^(-s u) / k! du *)
Theorem landau_coeff : forall (k : nat) s, 2 < cre s ->
  CIntInf (fun u => g u * u ^ k * exp (- cre s * u) * cos (cim s * u) / INR (fact k))
          (fun u => - (g u * u ^ k * exp (- cre s * u) * sin (cim s * u)) / INR (fact k)) 0
          (mkC ((-1) ^ k * cre (D k s) / INR (fact k)) ((-1) ^ k * cim (D k s) / INR (fact k))).
Proof.
  intros k s Hs. destruct (ILAP k s Hs) as [Hr Hi].
  set (c := (-1) ^ k / INR (fact k)).
  assert (Hsgn : forall u, (-1) ^ k * (- u) ^ k = u ^ k).
  { intro u. rewrite <- Rpow_mult_distr. f_equal. ring. }
  assert (Hf : INR (fact k) <> 0) by (apply not_0_INR, fact_neq_0).
  split; simpl.
  - replace ((-1) ^ k * cre (D k s) / INR (fact k)) with (c * cre (D k s)) by (unfold c; field; exact Hf).
    apply (RIntInf_ext (fun u => c * (g u * (- u) ^ k * exp (- cre s * u) * cos (cim s * u)))); [|apply RIntInf_scal; exact Hr].
    intros u _. unfold c. rewrite <- (Hsgn u). field. exact Hf.
  - replace ((-1) ^ k * cim (D k s) / INR (fact k)) with (c * cim (D k s)) by (unfold c; field; exact Hf).
    apply (RIntInf_ext (fun u => c * (- (g u * (- u) ^ k * exp (- cre s * u) * sin (cim s * u))))); [|apply RIntInf_scal; exact Hi].
    intros u _. unfold c. rewrite <- (Hsgn u). field. exact Hf.
Qed.
End Coeff.

Print Assumptions landau_coeff.

(* ===================================================================== *)
(* Parts C, D: sum_A and sum_Th, refined over an abstract field           *)
(* ===================================================================== *)
Section CharSums.
Variable K : Type.                                   (* stands for C *)
Variables (k0 k1 : K) (kadd kmul ksub kdiv : K -> K -> K) (kopp kinv : K -> K).
Hypothesis Kfield : field_theory k0 k1 kadd kmul ksub kopp kdiv kinv (@eq K).
Add Field Kf : Kfield.
Local Infix "+'" := kadd (at level 50, left associativity).
Local Infix "*'" := kmul (at level 40, left associativity).

Fixpoint ksum (l : list K) : K := match l with [] => k0 | v :: t => v +' ksum t end.
Fixpoint knat (n : nat) : K := match n with O => k0 | S m => k1 +' knat m end.

Lemma ksum_map_scal : forall {A} (c : K) (f : A -> K) l,
  ksum (map (fun x => c *' f x) l) = c *' ksum (map f l).
Proof. intros A c f l. induction l as [|a l IH]; simpl; [ring|rewrite IH; ring]. Qed.
Lemma ksum_map_ext : forall {A} (f h : A -> K) l, (forall x, In x l -> f x = h x) ->
  ksum (map f l) = ksum (map h l).
Proof.
  intros A f h l H. induction l as [|a l IH]; simpl; [reflexivity|].
  rewrite (H a (or_introl eq_refl)), IH; [reflexivity|]. intros x Hx. apply H. right. exact Hx.
Qed.
Lemma ksum_map_const : forall {A} (c : K) (l : list A), ksum (map (fun _ => c) l) = knat (length l) *' c.
Proof. intros A c l. induction l as [|a l IH]; simpl; [ring|rewrite IH; ring]. Qed.
Lemma ksum_map_plus : forall {A} (f h : A -> K) l,
  ksum (map (fun x => f x +' h x) l) = ksum (map f l) +' ksum (map h l).
Proof. intros A f h l. induction l as [|a l IH]; simpl; [ring|rewrite IH; ring]. Qed.
Lemma ksum_swap : forall {A B} (f : A -> B -> K) (la : list A) (lb : list B),
  ksum (map (fun x => ksum (map (fun y => f x y) lb)) la) = ksum (map (fun y => ksum (map (fun x => f x y) la)) lb).
Proof.
  intros A B f la lb. induction la as [|a la IH]; simpl.
  - induction lb as [|b lb IHb]; simpl; [reflexivity|rewrite <- IHb; ring].
  - rewrite IH, <- ksum_map_plus. reflexivity.
Qed.
(* a sum is invariant under a permutation (Mathlib Equiv.sum_comp) *)
Lemma ksum_perm : forall l l', Permutation l l' -> ksum l = ksum l'.
Proof.
  intros l l' H. induction H; simpl; try reflexivity.
  - rewrite IHPermutation. reflexivity.
  - ring.
  - rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.

(* the group E0 x H and its characters, abstractly *)
Variable Hg G : Type.
Variables (hadd hsub : Hg -> Hg -> Hg) (hneg : Hg -> Hg).
Variables (gadd : G -> G -> G) (gneg : G -> G) (e1 : Hg -> G) (inr : Hg -> G).
(* Lean's  hg :  -(e1 (s + u - t)) = e1 t + (0, -s) + (0, -u)  (ext; simp; abel) *)
Hypothesis Hid : forall s u t, gneg (e1 (hsub (hadd s u) t)) = gadd (gadd (e1 t) (inr (hneg s))) (inr (hneg u)).
Variable A0 : list Hg.                               (* the subgroup A0, enumerated *)
Hypothesis A0_neg : forall s, In s A0 -> In (hneg s) A0.
Hypothesis A0_perm : Permutation (map hneg A0) A0.   (* Equiv.neg A0 *)

Section OneChar.
Variable psi : G -> K.
Hypothesis psi_add : forall x y, psi (gadd x y) = psi x *' psi y.   (* AddChar.map_add_eq_mul *)

Lemma sum_A_factor : forall s t,
  ksum (map (fun u => psi (gneg (e1 (hsub (hadd s u) t)))) A0)
  = psi (e1 t) *' psi (inr (hneg s)) *' ksum (map (fun u => psi (inr (hneg u))) A0).
Proof.
  intros s t. rewrite <- ksum_map_scal. apply ksum_map_ext. intros u _.
  rewrite Hid, !psi_add. reflexivity.
Qed.

(* sum_A, trivial case: psi in PsiA A0 *)
Theorem sum_A_trivial : (forall s, In s A0 -> psi (inr s) = k1) ->
  forall s t, In s A0 -> ksum (map (fun u => psi (gneg (e1 (hsub (hadd s u) t)))) A0) = knat (length A0) *' psi (e1 t).
Proof.
  intros Htr s t Hs. rewrite sum_A_factor.
  rewrite (Htr _ (A0_neg s Hs)).
  rewrite (ksum_map_ext _ (fun _ => k1)) by (intros u Hu; exact (Htr _ (A0_neg u Hu))).
  rewrite ksum_map_const. ring.
Qed.

(* sum_A, non-trivial case: [Mathlib] AddChar.sum_eq_zero_iff_ne_zero for
   the character psi o inr restricted to A0 *)
Hypothesis SUM0 : (exists s, In s A0 /\ psi (inr s) <> k1) -> ksum (map (fun u => psi (inr u)) A0) = k0.

Theorem sum_A_nontrivial : (exists s, In s A0 /\ psi (inr s) <> k1) ->
  forall s t, ksum (map (fun u => psi (gneg (e1 (hsub (hadd s u) t)))) A0) = k0.
Proof.
  intros Hnt s t. rewrite sum_A_factor.
  assert (Hre : ksum (map (fun u => psi (inr (hneg u))) A0) = ksum (map (fun u => psi (inr u)) A0)).
  { replace (map (fun u => psi (inr (hneg u))) A0) with (map (fun u => psi (inr u)) (map hneg A0))
      by (rewrite map_map; reflexivity).
    apply ksum_perm. apply Permutation_map. exact A0_perm. }
  rewrite Hre, (SUM0 Hnt). ring.
Qed.
End OneChar.

(* sum_Th: characters enumerated by the list Chars, PsiA decided by inPsi *)
Variable Chars : list (G -> K).
Variable inPsi : (G -> K) -> bool.
Hypothesis Chars_add : forall psi, In psi Chars -> forall x y, psi (gadd x y) = psi x *' psi y.
Hypothesis inPsi_true : forall psi, In psi Chars -> inPsi psi = true -> forall s, In s A0 -> psi (inr s) = k1.
Hypothesis inPsi_false : forall psi, In psi Chars -> inPsi psi = false -> exists s, In s A0 /\ psi (inr s) <> k1.
Hypothesis SUM0s : forall psi, In psi Chars ->
  (exists s, In s A0 /\ psi (inr s) <> k1) -> ksum (map (fun u => psi (inr u)) A0) = k0.   (* [Mathlib] *)

Variables (b : K) (GPsi : (G -> K) -> K) (T2 : list Hg) (nH : K).
Hypothesis T2_A0 : forall s, In s T2 -> In s A0.
Hypothesis nH_nz : nH <> k0.
Hypothesis two_nz : k1 +' k1 <> k0.
(* |PhiSet| = 2 |H|  (phiSet_card) *)
Definition nPhi : K := (k1 +' k1) *' nH.

(* Th (ChCore.lean l.18) *)
Definition Th (u0 t : Hg) : K :=
  kinv nPhi *' ksum (map (fun s => ksum (map (fun psi => psi (gneg (e1 (hsub (hadd s u0) t))) *' (b *' GPsi psi)) Chars)) T2).

Definition PsiSum (t : Hg) : K := ksum (map (fun psi => if inPsi psi then psi (e1 t) *' GPsi psi else k0) Chars).

(* sum_Th:  sum_{u in A0} Th u t = |A0| * (b * (delta2 / 2)) * sum_{psi in PsiA} psi(e1 t) GPsi psi,
   with delta2 = |T2| / |H|. *)
Theorem sum_Th : forall t,
  ksum (map (fun u => Th u t) A0) =
  knat (length A0) *' (b *' (kdiv (knat (length T2)) nH *' kinv (k1 +' k1))) *' PsiSum t.
Proof.
  intro t. unfold Th.
  rewrite ksum_map_scal.
  (* move the sum over u inside the sums over s and psi *)
  rewrite (ksum_swap (fun u s => ksum (map (fun psi => psi (gneg (e1 (hsub (hadd s u) t))) *' (b *' GPsi psi)) Chars)) A0 T2).
  assert (Hin : forall s, In s T2 ->
    ksum (map (fun u => ksum (map (fun psi => psi (gneg (e1 (hsub (hadd s u) t))) *' (b *' GPsi psi)) Chars)) A0)
    = knat (length A0) *' b *' PsiSum t).
  { intros s Hs.
    rewrite (ksum_swap (fun u psi => psi (gneg (e1 (hsub (hadd s u) t))) *' (b *' GPsi psi)) A0 Chars).
    unfold PsiSum. rewrite <- ksum_map_scal. apply ksum_map_ext. intros psi Hpsi.
    replace (ksum (map (fun u => psi (gneg (e1 (hsub (hadd s u) t))) *' (b *' GPsi psi)) A0))
      with (ksum (map (fun u => psi (gneg (e1 (hsub (hadd s u) t)))) A0) *' (b *' GPsi psi)).
    2:{ transitivity ((b *' GPsi psi) *' ksum (map (fun u => psi (gneg (e1 (hsub (hadd s u) t)))) A0)); [ring|].
        rewrite <- ksum_map_scal. apply ksum_map_ext. intros u _. ring. }
    destruct (inPsi psi) eqn:E.
    - rewrite (sum_A_trivial psi (Chars_add psi Hpsi) (inPsi_true psi Hpsi E) s t (T2_A0 s Hs)). ring.
    - rewrite (sum_A_nontrivial psi (Chars_add psi Hpsi) (SUM0s psi Hpsi) (inPsi_false psi Hpsi E) s t). ring. }
  rewrite (ksum_map_ext _ (fun _ => knat (length A0) *' b *' PsiSum t) T2 Hin).
  rewrite ksum_map_const. unfold nPhi. field. split; assumption.
Qed.
End CharSums.

Print Assumptions sum_A_trivial.
Print Assumptions sum_A_nontrivial.
Print Assumptions sum_Th.
