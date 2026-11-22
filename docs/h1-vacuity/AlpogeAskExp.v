(* AlpogeAskExp.v -- CharacterBalance.askExp of the claimed RH/GRH Lean
   development (CocoSgt/riemann-hypothesis-lean @ 7cbf7a0,
   LandauTheorems/ChBalance.lean, the lemma immediately above ch_balance),
   REFINED, with a NACK check on the cutoff.

   AlpogeSixthCH.ch_balance_r takes askExp as an inventory hypothesis.
   This file replays it:

     * cutoff_uniform: max(a/n - w, 0) = 0 once n > N, from 0 < w and
       a/w <= N alone.  The bound does not depend on t or x.
     * cutoff_needs_hN: a control.  Drop a/w <= N and the max need not
       vanish (a = 3, w = 1, N = 1, n = 2).  Not a NACK of the Lean
       proof, which assumes hN.  No candidate NACK was found.
     * ramified_weights_zero: ramifiedPrimeTerm_eq_zero, from the cutoff
       and D.d <= D.d^i.
     * primeSum_eq / askExp_split_r: the case split hC (p = D.d, p in S0,
       unramified) assembling ASK.
     * hA_r: the three-sum reordering in the first calc of askExp.

   ounram / lunram / lsplit / ld, sum_vonMangoldt_primePow, and the
   identification of Kc * Fc with the character sum stay named
   hypotheses, tagged [inventory].  Within docs/axiom-allowlist.txt.
   No Admitted.  Not a proof of RH.  Verdict on the external development
   stays PASS-STATIC / PENDING.

   Evidence for docs/attacks/2026-11-22-alpoge-askexp.md.
   NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human-reviewed by Jeroen Bloemscheer (2026-11-22).
     Assisted-by: Cursor Grok 4.7
*)
From Stdlib Require Import Reals Lra Lia Arith List.
From NTS.Proofs.Probes Require Import AlpogeSixthCH.
Import ListNotations.
Local Open Scope R_scope.

(* ===================================================================== *)
(* Cutoff.  max_zero_of_gt, used by ramifiedPrimeTerm and by the support *)
(* obligation of sum_vonMangoldt_primePow.                                *)
(* ===================================================================== *)

Lemma cutoff_uniform : forall a w n m,
  0 < w -> a / w <= INR n -> INR n < m -> Rmax (a / m - w) 0 = 0.
Proof.
  intros a w n m Hw HN Hm.
  assert (Hn0 : 0 <= INR n) by apply pos_INR.
  assert (Hm0 : 0 < m) by lra.
  apply Rmax_right.
  assert (E : a / m = (a / w) * (w / m)).
  { unfold Rdiv. rewrite <- Rmult_assoc. rewrite (Rmult_assoc a (/ w) w).
    rewrite Rinv_l by lra. ring. }
  rewrite E.
  assert (H1 : (a / w) * (w / m) <= INR n * (w / m)).
  { apply Rmult_le_compat_r; [|exact HN]. apply Rlt_le. unfold Rdiv.
    apply Rmult_lt_0_compat; [exact Hw|apply Rinv_0_lt_compat; exact Hm0]. }
  assert (H2 : INR n * (w / m) < w).
  { unfold Rdiv. rewrite <- Rmult_assoc.
    apply Rmult_lt_reg_r with m; [exact Hm0|].
    replace (INR n * w * / m * m) with (INR n * w).
    - replace (w * m) with (m * w) by ring.
      apply Rmult_lt_compat_r; [exact Hw|exact Hm].
    - rewrite (Rmult_assoc (INR n * w) (/ m) m). rewrite Rinv_l by lra. ring. }
  lra.
Qed.

Lemma nat_pow_ge_one : forall d i, (1 <= d)%nat -> (1 <= d ^ i)%nat.
Proof.
  intros d i Hd. induction i as [|i IH]; simpl; lia.
Qed.

Lemma nat_pow_ge_base : forall d i, (1 <= d)%nat -> (1 <= i)%nat -> (d <= d ^ i)%nat.
Proof.
  intros d i Hd Hi.
  destruct i as [|i]; [lia|].
  simpl.
  replace d with (d * 1)%nat at 1 by lia.
  apply Nat.mul_le_mono_l. apply nat_pow_ge_one. exact Hd.
Qed.

Lemma ramified_base_exceeds : forall d i N,
  (1 <= d)%nat -> (1 <= i)%nat -> (N < d)%nat -> (N < d ^ i)%nat.
Proof.
  intros d i N Hd Hi HN.
  apply Nat.lt_le_trans with d; [exact HN|apply nat_pow_ge_base; assumption].
Qed.

(* Control.  Not a NACK: the Lean proof assumes hN. *)
Theorem cutoff_needs_hN :
  Rmax (3 / INR 2 - 1) 0 <> 0 /\ ~ (3 / INR 1 <= INR 1).
Proof.
  assert (E1 : INR 1 = 1) by (simpl; ring).
  assert (E2 : INR 2 = 2) by (simpl; ring).
  rewrite E1, E2. split.
  - replace (3 / 2 - 1) with (1 / 2) by field. rewrite Rmax_left by lra. lra.
  - lra.
Qed.

Theorem ramified_weights_zero : forall a (w : nat -> R) (d N : nat) (is : list nat),
  (1 <= d)%nat -> (N < d)%nat ->
  (forall i, In i is -> (1 <= i)%nat) ->
  (forall i, In i is -> 0 < w i) ->
  (forall i, In i is -> a / w i <= INR N) ->
  rsum (map (fun i => Rmax (a / INR (d ^ i) - w i) 0) is) = 0.
Proof.
  intros a w d N is Hd HN Hi Hw Ha. induction is as [|i is IH]; simpl; [reflexivity|].
  assert (Hin : In i (i :: is)) by (left; reflexivity).
  rewrite cutoff_uniform with (n := N).
  - rewrite IH.
    + ring.
    + intros j Hj. apply Hi. right. exact Hj.
    + intros j Hj. apply Hw. right. exact Hj.
    + intros j Hj. apply Ha. right. exact Hj.
  - apply Hw. exact Hin.
  - apply Ha. exact Hin.
  - apply lt_INR. apply ramified_base_exceeds; [exact Hd|apply Hi; exact Hin|exact HN].
Qed.

Lemma rsum_indicator : forall (d : nat) (c : R) (l : list nat),
  NoDup l ->
  rsum (map (fun p => if Nat.eq_dec p d then c else 0) l)
  = if in_dec Nat.eq_dec d l then c else 0.
Proof.
  intros d c l Hnd. induction l as [|p ps IH]; simpl.
  - destruct (in_dec Nat.eq_dec d []) as [H|_]; [destruct H|reflexivity].
  - inversion Hnd as [|p0 ps0 Hp Hnd']; subst p0 ps0.
    destruct (Nat.eq_dec p d) as [Eq|Ne].
    + subst p. assert (Z : rsum (map (fun q => if Nat.eq_dec q d then c else 0) ps) = 0).
      { transitivity (rsum (map (fun _ : nat => 0) ps)).
        - apply rsum_map_ext. intros q Hq. destruct (Nat.eq_dec q d) as [E|_]; [subst; contradiction|reflexivity].
        - clear. induction ps as [|q ps IHp]; simpl; [reflexivity|rewrite IHp; ring]. }
      rewrite Z. destruct (in_dec Nat.eq_dec d (d :: ps)) as [_|Hn].
      * ring.
      * exfalso. apply Hn. left. reflexivity.
    + rewrite IH by exact Hnd'.
      destruct (in_dec Nat.eq_dec d (p :: ps)) as [Hin|Hout];
      destruct (in_dec Nat.eq_dec d ps) as [Hin'|Hout'].
      * ring.
      * destruct Hin as [E|Hin]; [congruence|contradiction].
      * exfalso. apply Hout. right. exact Hin'.
      * ring.
Qed.

(* ===================================================================== *)
(* hC: each prime's von Mangoldt block equals the ASK summand             *)
(* ===================================================================== *)
Section PrimeSplit.
Variable P : list nat.
Variable logp askPv : nat -> R.
Variable askD aN : R.
Variable d N : nat.
Variable inert : nat -> bool.
Variable inS0 : nat -> bool.
Variable primeSum : nat -> R.
Variable exps : list nat.
Variable wexp : nat -> R.
Hypothesis Pnd : NoDup P.
Hypothesis d_ge1 : (1 <= d)%nat.
(* IsInert D.d is impossible: field .2.2.2.1 of IsInert is p <> D.d. *)
Hypothesis inert_not_d : inert d = false.
(* [inventory] lsplit, and split_frob contradicts IsInert *)
Hypothesis lsplit : forall p, In p P -> inS0 p = true -> inert p = false /\ p <> d.
(* [inventory] ld *)
Hypothesis primeSum_d : In d P -> primeSum d = logp d * askD.
(* [inventory] lsplit's sum *)
Hypothesis primeSum_s0 : forall p, In p P -> inS0 p = true -> primeSum p = 0.
(* [inventory] lunram *)
Hypothesis primeSum_free : forall p, In p P -> inS0 p = false -> p <> d ->
  primeSum p = 2 * logp p * askPv p.
(* [inventory] inPhi (frob p) and inPhi_nsmul, so askP p = 0 *)
Hypothesis askP_zero : forall p, In p P -> inert p = false -> inS0 p = false -> p <> d -> askPv p = 0.
(* [reading of unfold askD] *)
Hypothesis askD_unfold : (N < d)%nat ->
  askD = rsum (map (fun i => Rmax (aN / INR (d ^ i) - wexp i) 0) exps).
Hypothesis exps_pos : forall i, In i exps -> (1 <= i)%nat.
Hypothesis exps_w : forall i, In i exps -> 0 < wexp i.
Hypothesis exps_hN : forall i, In i exps -> aN / wexp i <= INR N.

Definition inertTerm (p : nat) : R := if inert p then 2 * logp p * askPv p else 0.
Definition dTerm (p : nat) : R := if Nat.eq_dec p d then logp d * askD else 0.
Definition ASK : R :=
  rsum (map inertTerm P) + (if in_dec Nat.eq_dec d P then logp d * askD else 0).

Lemma primeSum_eq : forall p, In p P -> primeSum p = inertTerm p + dTerm p.
Proof.
  intros p Hp.
  destruct (inS0 p) eqn:Hs.
  - destruct (lsplit p Hp Hs) as [Hi Hne].
    unfold inertTerm, dTerm. rewrite Hi.
    destruct (Nat.eq_dec p d) as [E|_]; [contradiction|].
    rewrite (primeSum_s0 p Hp Hs). ring.
  - destruct (Nat.eq_dec p d) as [E|Hne].
    + subst p. unfold inertTerm, dTerm. rewrite inert_not_d.
      destruct (Nat.eq_dec d d) as [_|Neq]; [|congruence].
      rewrite (primeSum_d Hp). ring.
    + unfold inertTerm, dTerm. destruct (Nat.eq_dec p d) as [E|_]; [contradiction|].
      rewrite (primeSum_free p Hp Hs Hne).
      destruct (inert p) eqn:He; [ring|].
      rewrite (askP_zero p Hp He Hs Hne). ring.
Qed.

Lemma rsum_dterm :
  rsum (map dTerm P) = if in_dec Nat.eq_dec d P then logp d * askD else 0.
Proof.
  unfold dTerm. apply rsum_indicator. exact Pnd.
Qed.

Theorem askD_zero_of_lt : (N < d)%nat -> askD = 0.
Proof.
  intros HN. rewrite askD_unfold by exact HN.
  apply (ramified_weights_zero aN wexp d N exps); assumption.
Qed.

Theorem askExp_split_r : rsum (map primeSum P) = ASK.
Proof.
  unfold ASK.
  assert (He : rsum (map primeSum P) = rsum (map (fun p => inertTerm p + dTerm p) P)).
  { apply rsum_map_ext. intros p Hp. apply primeSum_eq. exact Hp. }
  rewrite He, rsum_plus, rsum_dterm. reflexivity.
Qed.
End PrimeSplit.

(* ===================================================================== *)
(* hA: move n outside the character sum.  The ring step that identifies   *)
(* Kc * Fc is the hypothesis Kc_Fc; the swaps themselves are proved.      *)
(* ===================================================================== *)
Section Reorder.
Variable C : CStr.
Add Field KfA : (kfield C).
Variables (G Ch : Type) (S : list G) (Chars : list Ch) (Ns : list nat).
Variable f : G -> Ch -> nat -> car C.

Lemma hA_swap :
  ksum (map (fun g => ksum (map (fun psi => ksum (map (fun n => f g psi n) Ns)) Chars)) S)
  = ksum (map (fun n => ksum (map (fun g => ksum (map (fun psi => f g psi n) Chars)) S)) Ns).
Proof.
  assert (H1 : ksum (map (fun g => ksum (map (fun psi => ksum (map (fun n => f g psi n) Ns)) Chars)) S)
              = ksum (map (fun g => ksum (map (fun n => ksum (map (fun psi => f g psi n) Chars)) Ns)) S)).
  { apply ksum_map_ext. intros g _. apply ksum_swap. }
  rewrite H1. apply ksum_swap.
Qed.
End Reorder.

Print Assumptions cutoff_uniform.
Print Assumptions cutoff_needs_hN.
Print Assumptions ramified_weights_zero.
Print Assumptions askExp_split_r.
Print Assumptions askD_zero_of_lt.
Print Assumptions hA_swap.
