(* AlpogeRankZero.v -- direct port of rank_zero_of_row_conditions.

   Lean (mirror C:\rh, CocoSgt/riemann-hypothesis-lean @ 7cbf7a0):
     Formalism/LocalToGlobal/NormalizedHeckeFactors/RankZeroOfLevelThree.lean
       theorem rank_zero_of_row_conditions, lines 10-32.
     Development/.../SmallLevelRankEqClosedOfLevelProjectionSurjective.lean
       lines 36-46, the call at max(sel, xr).
   SmallLevelRankEq (GlobalTheoremInputs.lean:52-53) is
     exists x0, forall x >= x0, forall i, forall j in lifts,
       dZ0 j = D0,
   with lifts = Icc 1 m (LiftErrorLocal.lean:31) and
     dZ0 j = finrank (Zj mu0 j) (DataParams₂.lean:194).

   The finrank step (finrank_Zj_of_pin, BaseRowsEqRecordRows.lean:98-108)
   is the linear-algebra call.  It stays a hypothesis.  The omega/max
   steps are theories/LiftIndex.v.

   build.log optimization: exit 3221226505 on stack overrun, and
   `ring` failures that say to use `ring_nf`.  The caller also sets
   maxHeartbeats 1600000.  This file does not re-elaborate that.

   Within docs/axiom-allowlist.txt.  No Admitted.  Not a proof of RH.
   Verdict on the external development: PASS-STATIC / PENDING.

   Evidence for docs/attacks/2026-11-23-alpoge-rank-zero.md.
   NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Cursor Grok 4.7
*)
From Stdlib Require Import Reals Lia Lra.
From NTS.Proofs Require Import LiftIndex.
Local Open Scope R_scope.

(* ===================================================================== *)
(* rank_zero_of_row_conditions                                            *)
(* RankZeroOfLevelThree.lean:10-32.                                       *)
(* ===================================================================== *)

Section RankZeroPort.
Variable x1 : R.
Variable Ix : R -> Type.
Variable m : forall x, Ix x -> nat.
Variable D0n : forall x, Ix x -> nat.
Variable Mu : Type.
Variable mu0 : forall x, Ix x -> Mu.
Variable dZ : forall x (i : Ix x), Mu -> nat -> nat.
Variable Tup : forall x, Ix x -> Type.
Variable tup : forall x (i : Ix x), Tup x i -> Mu.
Variable Surj : forall x (i : Ix x), Tup x i -> nat -> Prop.
(* Row-side premises of the Lean theorem.  Only finrank_Zj_of_pin reads them. *)
Variable Tied RowSide Determined Lam3 DivRows Rows0 : Prop.

(* [QEX] finrank_Zj_of_pin's second component.
   BaseRowsEqRecordRows.lean:98-108.  The equality is at tup t, index k+1.
   dZ0 is dZ at mu0, so the Lean `rw [htup]` still has to fire. *)
Hypothesis finrank_Zj_of_pin :
  Tied -> RowSide -> Determined -> Lam3 -> DivRows -> Rows0 ->
  forall x (i : Ix x) (t : Tup x i) (k : nat),
    (k < m x i)%nat -> Surj x i t k ->
    dZ x i (tup x i t) (S k) = D0n x i.

(* RankZeroOfLevelThree.lean:24-32, the body of refine ⟨max x0 (x1+1), ...⟩. *)
Theorem rank_zero_at_witness_r (x0 : R)
  (ht : forall x, x1 < x -> x0 <= x -> forall i : Ix x,
      exists t : Tup x i, tup x i t = mu0 x i /\
        forall k, (k < m x i)%nat -> Surj x i t k)
  (HT : Tied) (HP : RowSide) (HD : Determined) (HL : Lam3) (HR : DivRows) (H0 : Rows0) :
  forall x, Rmax x0 (x1 + 1) <= x -> forall (i : Ix x) (j : nat),
    (1 <= j <= m x i)%nat -> dZ x i (mu0 x i) j = D0n x i.
Proof.
  intros x Hx i j Hj.
  destruct (rmax_add_one_split x0 x1 x Hx) as [H0x Hx1].
  destruct (exists_fin_pred_of_icc (m x i) j Hj) as [k [Hk Heq]].
  destruct (ht x Hx1 H0x i) as [t [Htup Hsurj]].
  assert (Hpin : dZ x i (tup x i t) (S k) = D0n x i)
    by (apply (finrank_Zj_of_pin HT HP HD HL HR H0 x i t k Hk); exact (Hsurj k Hk)).
  rewrite Htup in Hpin. rewrite <- Heq in Hpin. exact Hpin.
Qed.

Theorem rank_zero_of_row_conditions_r (x0 : R)
  (ht : forall x, x1 < x -> x0 <= x -> forall i : Ix x,
      exists t : Tup x i, tup x i t = mu0 x i /\
        forall k, (k < m x i)%nat -> Surj x i t k)
  (HT : Tied) (HP : RowSide) (HD : Determined) (HL : Lam3) (HR : DivRows) (H0 : Rows0) :
  exists xW : R, forall x, xW <= x -> forall (i : Ix x) (j : nat),
    (1 <= j <= m x i)%nat -> dZ x i (mu0 x i) j = D0n x i.
Proof.
  intros. exists (Rmax x0 (x1 + 1)).
  apply (rank_zero_at_witness_r x0 ht HT HP HD HL HR H0).
Qed.

(* ===================================================================== *)
(* Caller: xr stays inside the member, then x0 = max(sel, xr).           *)
(* SmallLevelRankEqClosedOfLevelProjectionSurjective.lean:36-46.         *)
(* ===================================================================== *)

Variable sel : R.
(* The Lean anonymous constructor's t, whose tup is mu0. *)
Hypothesis mu0_inhab : forall x (i : Ix x), exists t : Tup x i, tup x i t = mu0 x i.
(* zL's ∃ xr is per member.  Surjectivity is stated only once x clears xr. *)
Hypothesis zL : exists xr : R, forall x,
  x1 < x -> sel <= x -> xr <= x ->
  forall (i : Ix x) (t : Tup x i) (k : nat),
    tup x i t = mu0 x i -> (k < m x i)%nat -> Surj x i t k.

Lemma ht_of_zL (xr : R)
  (Hz : forall x, x1 < x -> sel <= x -> xr <= x ->
     forall (i : Ix x) (t : Tup x i) (k : nat),
       tup x i t = mu0 x i -> (k < m x i)%nat -> Surj x i t k)
  (x : R) (hx : x1 < x) (h0 : Rmax sel xr <= x) (i : Ix x) :
  exists t : Tup x i, tup x i t = mu0 x i /\
    forall k, (k < m x i)%nat -> Surj x i t k.
Proof.
  destruct (mu0_inhab x i) as [t Ht].
  destruct (rmax_pair_split sel xr x h0) as [Hs Hxr].
  exists t. split; [exact Ht|].
  intros k Hk. exact (Hz x hx Hs Hxr i t k Ht Hk).
Qed.

Theorem small_level_of_xr_r :
  Tied -> RowSide -> Determined -> Lam3 -> DivRows -> Rows0 ->
  exists (xr xW : R),
    xW = Rmax (Rmax sel xr) (x1 + 1) /\
    forall x, xW <= x -> forall (i : Ix x) (j : nat),
      (1 <= j <= m x i)%nat -> dZ x i (mu0 x i) j = D0n x i.
Proof.
  intros HT HP HD HL HR H0.
  destruct zL as [xr Hz].
  set (x0 := Rmax sel xr).
  exists xr, (Rmax x0 (x1 + 1)). split; [reflexivity|].
  apply (rank_zero_at_witness_r x0 (ht_of_zL xr Hz) HT HP HD HL HR H0).
Qed.
End RankZeroPort.

(* The rw [htup] is load-bearing: equality at tup t is not equality at mu0. *)
Theorem pin_at_tup_misses_mu0 :
  let dZn := fun (mu j : nat) => (mu + j)%nat in
  dZn 1%nat 1%nat = 2%nat /\ dZn 0%nat 1%nat <> 2%nat.
Proof. split; lia. Qed.

(* A threshold built from xr = 0 does not clear a member whose xr is 5. *)
Theorem family_threshold_misses_member :
  Rmax (Rmax 0 0) (0 + 1) = 1 /\ ~ (5 <= Rmax (Rmax 0 0) (0 + 1)).
Proof.
  assert (Hz : Rmax 0 0 = 0) by (apply Rmax_left; lra).
  assert (Ho : Rmax 0 1 = 1) by (apply Rmax_right; lra).
  rewrite Hz. replace (0 + 1) with 1 by lra.
  split; [exact Ho|]. rewrite Ho. lra.
Qed.

(* The Lean witness max(max(sel, xr), x1+1) does clear sel, xr and x1. *)
Theorem threshold_keeps_member_xr (sel xr x1 : R) :
  sel <= Rmax (Rmax sel xr) (x1 + 1) /\
  xr <= Rmax (Rmax sel xr) (x1 + 1) /\
  x1 < Rmax (Rmax sel xr) (x1 + 1).
Proof.
  set (x0 := Rmax sel xr).
  set (xW := Rmax x0 (x1 + 1)).
  assert (Hx0 : x0 <= xW) by apply Rmax_l.
  destruct (rmax_pair_split sel xr xW
    (Rle_trans _ _ _ (Rle_refl x0) Hx0)) as [Hs Hxr].
  destruct (rmax_add_one_split x0 x1 xW) as [_ Hx1]; [apply Rle_refl|].
  unfold xW, x0. repeat split; assumption.
Qed.

Print Assumptions ht_of_zL.
Print Assumptions rank_zero_at_witness_r.
Print Assumptions rank_zero_of_row_conditions_r.
Print Assumptions small_level_of_xr_r.
Print Assumptions pin_at_tup_misses_mu0.
Print Assumptions family_threshold_misses_member.
Print Assumptions threshold_keeps_member_xr.
