(* AlpogeLinkIrr.v -- direct port of linkIRR_of_join_ex.

   Lean (mirror C:\rh, CocoSgt/riemann-hypothesis-lean @ 7cbf7a0):
     Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/
       LinkIRROfJoinEx.lean, theorem linkIRR_of_join_ex, lines 17-32.
   The body obtains 0 < ez from 0 < eps and 1 <= J, takes the witness
   max(x0, (3/2)^(1/ez)) with x0 from the member existential, proves
   3/2 <= x^ez, and fills WeightAllRows by weight_of_join.

   linkIRR_of_allRows (ConcNP.lean:647-655) is the delp conclusion.
   It is link_irreducible_all_rows, whose atTop bounds are not this
   proof.  weight_of_join (AllJoinP.lean:22-24) and rangeW_of_sizes
   (ConcNWeight.lean:221-236, the 2^12 / host.g chain) stay hypotheses.
   tieAdmG_holds (LinkIRROfJoinEx.lean:14-15) is a D7 record projection.

   build.log does not reach this file.  It dies with exit 3221226505
   (STATUS_STACK_BUFFER_OVERRUN) and, where ring fails, says to use
   ring_nf.  The power steps are theories/LogRpowClean.v (lia/lra
   normal form, no Stdlib Rpower).  The max split is LiftIndex.rmax_pair_split.

   Within docs/axiom-allowlist.txt.  No Admitted.  Not a proof of RH.
   Verdict on the external development: PASS-STATIC / PENDING.

   Evidence for docs/attacks/2026-11-23-alpoge-link-irr.md.
   NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Cursor Grok 4.7
*)
From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import LogRpowClean LiftIndex.
Local Open Scope R_scope.

(* ===================================================================== *)
(* linkIRR_of_join_ex                                                     *)
(* LinkIRROfJoinEx.lean:17-32.                                            *)
(* Sz is SizesRec D x ez Cs.  Cs is a parameter of that predicate.        *)
(* ===================================================================== *)

Section LinkIrrPort.
Variable eps c J ez : R.
Hypothesis eps_pos : 0 < eps.
Hypothesis eps_le_one : eps <= 1.
Hypothesis c_pos : 0 < c.
Hypothesis one_le_J : 1 <= J.
Hypothesis ez_eq : ez = eps / J.

Variable Ix : R -> Type.
Variable AllRows : forall x, Ix x -> Type.
Variable Lab : forall x (i : Ix x), AllRows x i -> Prop.
Variable Join : forall x (i : Ix x), AllRows x i -> Prop.
Variable Adm : forall x, Ix x -> Prop.
Variable Cnt : forall x (i : Ix x), AllRows x i -> Prop.
Variable Wgt : forall x (i : Ix x), AllRows x i -> Prop.
Variable Range : forall x, Ix x -> Prop.
Variable Tie : forall x, Ix x -> Prop.
Variable Sz : forall x (i : Ix x), AllRows x i -> Prop.
Variable LinkIRR : Prop.

(* [QEX] tieAdmG_holds.  LinkIRROfJoinEx.lean:14-15. *)
Hypothesis tieAdmG_holds : forall x (i : Ix x), Tie x i.
(* [QEX] rangeW_of_sizes.  ConcNWeight.lean:221-236.
   The 3/2 <= x^ez premise is the proved hxe; the 2^12 chain is not. *)
Hypothesis rangeW_of_sizes :
  forall x (i : Ix x) (A : AllRows x i),
    Sz x i A -> 3 / 2 <= rpc x ez -> Range x i.
(* [QEX] weight_of_join.  AllJoinP.lean:22-24. *)
Hypothesis weight_of_join :
  forall x (i : Ix x) (A : AllRows x i),
    Adm x i -> Tie x i -> Range x i -> Join x i A -> Wgt x i A.
(* [QEX] linkIRR_of_allRows.  ConcNP.lean:647-655.
   Lab, Cnt, Wgt, Sz — the join and adm slots have been consumed. *)
Hypothesis linkIRR_of_allRows :
  0 < eps -> eps <= 1 -> 0 < c ->
  (exists xW : R, forall x, xW <= x -> forall i : Ix x,
      exists A : AllRows x i,
        Lab x i A /\ Cnt x i A /\ Wgt x i A /\ Sz x i A) ->
  LinkIRR.

(* The refine witness max(x0, (3/2)^(1/ez)), and the weight slot. *)
Theorem link_irr_rows_at_witness_r (x0 : R)
  (hx0 : forall x, x0 <= x -> forall i : Ix x,
      exists A : AllRows x i,
        Lab x i A /\ Join x i A /\ Adm x i /\ Cnt x i A /\ Sz x i A) :
  exists xW : R, forall x, xW <= x -> forall i : Ix x,
    exists A : AllRows x i,
      Lab x i A /\ Cnt x i A /\ Wgt x i A /\ Sz x i A.
Proof.
  assert (Hez : 0 < ez)
    by (rewrite ez_eq; apply Rdiv_lt_0_compat; [exact eps_pos | lra]).
  set (root := rpc (3 / 2) (1 / ez)).
  exists (Rmax x0 root). intros x Hx i.
  destruct (rmax_pair_split x0 root x Hx) as [Hx0le Hroot].
  destruct (hx0 x Hx0le i) as [A [hT [hJ [hL [hC hS]]]]].
  assert (Hxe : 3 / 2 <= rpc x ez)
    by (apply rpc_le_of_root; [lra | exact Hez | exact Hroot]).
  exists A. split; [exact hT |]. split; [exact hC |]. split.
  - apply (weight_of_join x i A hL (tieAdmG_holds x i)
      (rangeW_of_sizes x i A hS Hxe) hJ).
  - exact hS.
Qed.

Theorem linkIRR_of_join_ex_r
  (h : exists x0 : R, forall x, x0 <= x -> forall i : Ix x,
      exists A : AllRows x i,
        Lab x i A /\ Join x i A /\ Adm x i /\ Cnt x i A /\ Sz x i A) :
  LinkIRR.
Proof.
  destruct h as [x0 hx0].
  apply linkIRR_of_allRows; [exact eps_pos | exact eps_le_one | exact c_pos |].
  apply (link_irr_rows_at_witness_r x0 hx0).
Qed.
End LinkIrrPort.

(* A witness built from x0 = 0 is 3/2 when ez = 1.
   It does not clear a member whose own x0 is 5. *)
Theorem root_threshold_misses_member :
  Rmax 0 (rpc (3 / 2) (1 / 1)) = 3 / 2 /\
  ~ (5 <= Rmax 0 (rpc (3 / 2) (1 / 1))).
Proof.
  assert (H1 : 1 / 1 = 1) by lra.
  rewrite H1. rewrite (rpc_one (3 / 2) ltac:(lra)).
  assert (Hm : Rmax 0 (3 / 2) = 3 / 2) by (apply Rmax_right; lra).
  rewrite Hm. split; [reflexivity | lra].
Qed.

(* The member witness max(5, (3/2)^1) is 5, and 3/2 <= 5^1. *)
Theorem root_threshold_keeps_member :
  Rmax 5 (rpc (3 / 2) (1 / 1)) = 5 /\
  5 <= Rmax 5 (rpc (3 / 2) (1 / 1)) /\
  rpc (3 / 2) (1 / 1) <= Rmax 5 (rpc (3 / 2) (1 / 1)) /\
  3 / 2 <= rpc (Rmax 5 (rpc (3 / 2) (1 / 1))) 1.
Proof.
  assert (H1 : 1 / 1 = 1) by lra.
  rewrite H1. rewrite (rpc_one (3 / 2) ltac:(lra)).
  assert (Hm : Rmax 5 (3 / 2) = 5) by (apply Rmax_left; lra).
  rewrite Hm. rewrite (rpc_one 5 ltac:(lra)).
  repeat split; lra.
Qed.

(* The Lean calc: ((3/2)^(1/ez))^ez = 3/2 at ez = 2. *)
Theorem pow_id_roundtrip :
  rpc (rpc (3 / 2) (1 / 2)) 2 = 3 / 2.
Proof. apply rpc_inv_cancel; lra. Qed.

(* Raising to 2 after the exponent 1 is (3/2)^2 = 9/4. *)
Theorem pow_id_wrong_exp :
  rpc (rpc (3 / 2) 1) 2 = 9 / 4 /\ rpc (rpc (3 / 2) 1) 2 <> 3 / 2.
Proof.
  rewrite (rpc_one (3 / 2) ltac:(lra)).
  assert (Hsq : rpc (3 / 2) 2 = (3 / 2) * (3 / 2)).
  { replace 2 with (1 + 1) by lra. rewrite rpc_add.
    rewrite !rpc_one by lra. reflexivity. }
  rewrite Hsq. split; lra.
Qed.

(* / 0 = 0 in this reals, so the cancel at exponent 0 is 1. *)
Theorem pow_id_at_zero :
  rpc (rpc (3 / 2) (1 / 0)) 0 = 1 /\
  rpc (rpc (3 / 2) (1 / 0)) 0 <> 3 / 2.
Proof.
  unfold Rdiv. rewrite Rinv_0. rewrite Rmult_1_l.
  assert (Hz : forall x : R, rpc x 0 = 1).
  { intros x. unfold rpc. rewrite Rmult_0_l. exact exp_0. }
  rewrite !Hz. split; [reflexivity | lra].
Qed.

Print Assumptions link_irr_rows_at_witness_r.
Print Assumptions linkIRR_of_join_ex_r.
Print Assumptions root_threshold_misses_member.
Print Assumptions root_threshold_keeps_member.
Print Assumptions pow_id_roundtrip.
Print Assumptions pow_id_wrong_exp.
Print Assumptions pow_id_at_zero.
