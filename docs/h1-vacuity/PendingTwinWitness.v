(* PendingTwinWitness.v -- non-vacuity of the cascade invariant's P branch.

   Binary64, Priest-valid, finite, nonzero.  With M = 2^53 - 1, B = M 2^-53,
   G = 2^-54, X = 2^105:
       e = [X; M; B]        f = [-M; B; G]
   sorted: [G; B; B; M; -M; X].  The cascade errors, oldest first, are
       [-2^-54; -2^-53; +1; 0; +1]
   and the accumulators 1, 2, 2^53, 1, X: the third TwoSum ties (T entry,
   h = +1 = ulp(-M)), the fourth leaves the pending twin Q = h = 1 with newest
   error 0 (P), and X absorbs it (P -> N, pending_twin_settles).

   PROVED: cascade_hyps holds for (e, f); the actual run reaches cinv_P at
   stage 4 with the next input X.  So the P branch of CascadeInvariant is
   inhabited by a Priest-valid input; cascade_reachable_shape and
   fes_carry_clean_nonoverlap are not vacuous there.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human-reviewed (PR #1014).
     Relies on vm_compute for the concrete run (trusted base; fine for a probe).
     Assisted-by: Claude
*)
From Stdlib Require Import Reals ZArith Lia Lra List.
From Flocq Require Import IEEE754.Binary Core Ulp.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_lib B64_Pff_bridge
     B64_Expansion B64_FastExpansionSum B64_FastExpansionSum_Shewchuk
     B64_Overlap_Hierarchy B64_Priest_FES_counterexample
     B64_CarryCleanAlgo B64_CarryCleanCore B64_CarryCleanLadder
     B64_CarryCleanRung2 B64_CarryCleanRung4 B64_CarryCleanOneBit.
From NTS.Proofs.Probes Require Import LookaheadQEX CascadeInvariant.
From NTS.Proofs.Probes Require CascadeTailBound.
Import ListNotations.
Local Open Scope R_scope.
Local Abbreviation b2r := (Binary.B2R prec emax).

Definition wA : binary64 := bM_scaled 0 eq_refl.                                  (* M *)
Definition wAn : binary64 := Binary.B754_finite prec emax true mant_M 0 eq_refl.  (* -M *)
Definition wB : binary64 := bM_scaled (-53) eq_refl.                              (* M 2^-53 *)
Definition wG : binary64 := Binary.B754_finite prec emax false 4503599627370496 (-106) eq_refl. (* 2^-54 *)
Definition wX : binary64 := Binary.B754_finite prec emax false 4503599627370496 53 eq_refl.    (* 2^105 *)
Definition w_m253 : binary64 := Binary.B754_finite prec emax true 4503599627370496 (-105) eq_refl.
Definition w_m254 : binary64 := Binary.B754_finite prec emax true 4503599627370496 (-106) eq_refl.
Definition w_zero : binary64 := Binary.B754_zero prec emax false.

Definition we : list binary64 := [wX; wA; wB].
Definition wf : list binary64 := [wAn; wB; wG].

Lemma w_priest : priest_chain we /\ priest_chain wf.
Proof.
  unfold we, wf, wX, wA, wAn, wB, wG, bM_scaled, mant_M. simpl.
  repeat split; apply priest_fin; zdec.
Qed.

Lemma w_finite : Forall b64_fin we /\ Forall b64_fin wf.
Proof. unfold we, wf, wX, wA, wAn, wB, wG, bM_scaled. repeat split; repeat constructor; reflexivity. Qed.

Lemma abs_p52 : forall s e H,
  Rabs (b2r (Binary.B754_finite prec emax s 4503599627370496 e H)) = bpow radix2 (52 + e).
Proof.
  intros s e H. rewrite abs_B2R_fin. rewrite bpow_plus.
  replace (IZR (Z.pos 4503599627370496)) with (bpow radix2 52)
    by (change (bpow radix2 52) with (IZR (2 ^ 52)); apply f_equal; reflexivity).
  reflexivity.
Qed.

Lemma fin_nz : forall s m e H, b2r (Binary.B754_finite prec emax s m e H) <> 0.
Proof.
  intros s m e H Hz. pose proof (abs_B2R_fin s m e H) as A. rewrite Hz, Rabs_R0 in A.
  assert (0 < IZR (Z.pos m) * bpow radix2 e)
    by (apply Rmult_lt_0_compat; [ apply IZR_lt; lia | apply bpow_gt_0 ]).
  lra.
Qed.

Lemma w_nonzero : Forall (fun x => b2r x <> 0) (we ++ wf).
Proof.
  unfold we, wf, wX, wA, wAn, wB, wG, bM_scaled. cbn [app].
  repeat constructor; apply fin_nz.
Qed.

Lemma term_bnd : forall (m e : Z), (0 <= m <= 2 ^ 53)%Z -> (e <= 53)%Z ->
  IZR m * bpow radix2 e <= bpow radix2 106.
Proof.
  intros m e Hm He.
  assert (H1 : IZR m <= bpow radix2 53)
    by (change (bpow radix2 53) with (IZR (2 ^ 53)); apply IZR_le; lia).
  assert (H2 : bpow radix2 e <= bpow radix2 53) by (apply bpow_le; lia).
  assert (H0 : 0 <= IZR m) by (apply IZR_le; lia).
  pose proof (bpow_gt_0 radix2 e).
  replace 106%Z with (53 + 53)%Z by reflexivity. rewrite bpow_plus.
  apply Rmult_le_compat; [ exact H0 | apply Rlt_le; assumption | exact H1 | exact H2 ].
Qed.

Lemma w_small : abs_sum we + abs_sum wf <= bpow radix2 (emax - 5).
Proof.
  unfold we, wf, wX, wA, wAn, wB, wG, bM_scaled, mant_M. cbn [abs_sum].
  rewrite !abs_B2R_fin.
  assert (T : forall m e, (0 <= Z.pos m <= 2 ^ 53)%Z -> (e <= 53)%Z ->
                IZR (Z.pos m) * bpow radix2 e <= bpow radix2 106) by (intros; apply term_bnd; assumption).
  pose proof (T 4503599627370496%positive 53%Z ltac:(lia) ltac:(lia)).
  pose proof (T 9007199254740991%positive 0%Z ltac:(lia) ltac:(lia)).
  pose proof (T 9007199254740991%positive (-53)%Z ltac:(lia) ltac:(lia)).
  pose proof (T 4503599627370496%positive (-106)%Z ltac:(lia) ltac:(lia)).
  assert (Hb : 8 * bpow radix2 106 <= bpow radix2 (emax - 5)).
  { replace (8 * bpow radix2 106) with (bpow radix2 (106 + 3)) by (rewrite bpow_plus; change (bpow radix2 3) with 8; ring).
    apply bpow_le. unfold emax. lia. }
  pose proof (bpow_gt_0 radix2 106).
  lra.
Qed.

Lemma w_sort : sort_by_abs (we ++ wf) = [wG; wB; wB; wA; wAn; wX].
Proof.
  assert (HGB : Rabs (b2r wG) < Rabs (b2r wB)).
  { unfold wG, wB, bM_scaled, mant_M. rewrite !abs_B2R_fin. apply scaled_lt'; zdec. }
  assert (HBA : Rabs (b2r wB) < Rabs (b2r wA)).
  { unfold wA, wB, bM_scaled, mant_M. rewrite !abs_B2R_fin. apply scaled_lt'; zdec. }
  assert (HAAn : Rabs (b2r wA) = Rabs (b2r wAn)).
  { unfold wA, wAn, bM_scaled. rewrite !abs_B2R_fin. reflexivity. }
  assert (HAX : Rabs (b2r wAn) < Rabs (b2r wX)).
  { unfold wAn, wX, mant_M. rewrite !abs_B2R_fin. apply scaled_lt'; zdec. }
  assert (HBAn : Rabs (b2r wB) < Rabs (b2r wAn)) by lra.
  assert (HAX' : Rabs (b2r wA) < Rabs (b2r wX)) by lra.
  assert (HBX : Rabs (b2r wB) < Rabs (b2r wX)) by lra.
  assert (HGX : Rabs (b2r wG) < Rabs (b2r wX)) by lra.
  assert (HGA : Rabs (b2r wG) < Rabs (b2r wA)) by lra.
  assert (HGAn : Rabs (b2r wG) < Rabs (b2r wAn)) by lra.
  unfold we, wf. cbn [app sort_by_abs].
  repeat first [ rewrite insert_by_abs_nil
               | rewrite insert_by_abs_le by lra
               | rewrite insert_by_abs_gt by lra ].
  reflexivity.
Qed.

Lemma w_hyps : cascade_hyps we wf wG [wB; wB; wA; wAn; wX].
Proof.
  destruct w_priest as [Pe Pf]. destruct w_finite as [Fe Ff].
  exact (conj Pe (conj Pf (conj Fe (conj Ff (conj w_nonzero (conj w_small w_sort)))))).
Qed.

Local Definition wxs : list binary64 := [wB; wB; wA; wAn; wX].

(* the real run: accumulator and error prefix after four TwoSums *)
Lemma w_run :
  [CascadeTailBound.acc wG wxs 4] ++ rev (firstn 4 (fst (b64_grow_expansion_aux wG wxs)))
  = [one_b; w_zero; one_b; w_m253; w_m254].
Proof. apply map_B2FF_inj. unfold wxs. vm_compute. reflexivity. Qed.

Lemma w_fes :
  fast_expansion_sum we wf = [wX; one_b; w_zero; one_b; w_m253; w_m254].
Proof.
  unfold fast_expansion_sum. rewrite w_sort. apply map_B2FF_inj. vm_compute. reflexivity.
Qed.

Theorem pending_twin_witness :
  cascade_hyps we wf wG wxs /\
  fast_expansion_sum we wf = [wX; one_b; w_zero; one_b; w_m253; w_m254] /\
  cinv_P (CascadeTailBound.acc wG wxs 4) (rev (firstn 4 (fst (b64_grow_expansion_aux wG wxs))))
         (skipn 5 (wG :: wxs)).
Proof.
  split; [ exact w_hyps | split; [ exact w_fes | ] ].
  assert (HQ : CascadeTailBound.acc wG wxs 4 = one_b)
    by exact (f_equal (fun l => nth 0 l w_zero) w_run).
  assert (HE : rev (firstn 4 (fst (b64_grow_expansion_aux wG wxs))) = [w_zero; one_b; w_m253; w_m254])
    by exact (f_equal (fun l => tl l) w_run).
  assert (Hskip : skipn 5 (wG :: wxs) = [wX]) by reflexivity.
  rewrite Hskip, HQ, HE.
  assert (Hf1 : b64_fin one_b) by reflexivity.
  assert (Hfz : b64_fin w_zero) by reflexivity.
  assert (Hfm3 : b64_fin w_m253) by reflexivity.
  assert (Hfm4 : b64_fin w_m254) by reflexivity.
  assert (Hfx : b64_fin wX) by reflexivity.
  assert (Habs3 : Rabs (b2r w_m253) = bpow radix2 (-53)) by exact (abs_p52 true (-105) eq_refl).
  assert (Habs4 : Rabs (b2r w_m254) = bpow radix2 (-54)) by exact (abs_p52 true (-106) eq_refl).
  assert (Hone : Rabs (b2r one_b) = bpow radix2 0) by exact (abs_p52 false (-52) eq_refl).
  assert (Hnil : carry_shape [] /\ pairs_aligned []).
  { split; [ split; [ constructor | split; [ exact I | exact I ] ] | exact I ]. }
  destruct Hnil as [Sh0 Al0].
  assert (N3 : b64_nz w_m253) by (split; [ exact Hfm3 | apply fin_nz ]).
  assert (N4 : b64_nz w_m254) by (split; [ exact Hfm4 | apply fin_nz ]).
  destruct (cons_single (-54) w_m254 [] N4 (pow2_multiple_pm (-54) _ Habs4) Sh0 Al0 (Forall_nil _))
    as [Sh1 Al1].
  assert (Kb1 : Forall (key_below (-53)) [CSingle w_m254]).
  { constructor; [ | constructor ]. unfold key_below. cbn [block_key]. rewrite Habs4.
    apply bpow_lt. lia. }
  destruct (cons_single (-53) w_m253 _ N3 (pow2_multiple_pm (-53) _ Habs3) Sh1 Al1 Kb1) as [Sh2 Al2].
  assert (HXr : b2r wX = bpow radix2 105).
  { unfold wX. rewrite B2R_fin. cbn [cond_Zopp].
    replace (IZR (Z.pos 4503599627370496)) with (bpow radix2 52)
      by (change (bpow radix2 52) with (IZR (2 ^ 52)); apply f_equal; reflexivity).
    rewrite <- bpow_plus. reflexivity. }
  assert (HXu : ulp radix2 b64_fexp (b2r wX) = bpow radix2 53).
  { rewrite HXr. rewrite ulp_neq_0 by (apply Rgt_not_eq, bpow_gt_0).
    unfold cexp. rewrite mag_bpow.
    unfold b64_fexp, SpecFloat.fexp, SpecFloat.emin, prec, emax. cbn. reflexivity. }
  assert (Hsafe : b64_TwoSum_safe wX one_b).
  { apply b64_TwoSum_safe_bound; [ exact Hfx | exact Hf1 | | ].
    - rewrite HXr, Rabs_pos_eq by (apply Rlt_le, bpow_gt_0). apply bpow_le. unfold emax. lia.
    - rewrite Hone. apply bpow_le. unfold emax. lia. }
  assert (B4 : 4 < bpow radix2 53).
  { pose proof (bpow_lt radix2 2 53 ltac:(lia)). change (bpow radix2 2) with 4 in H. exact H. }
  exists w_zero, one_b, [w_m253; w_m254], [CSingle w_m253; CSingle w_m254], 0%Z.
  refine (conj eq_refl (conj eq_refl (conj Hfz (conj Hf1 (conj _ (conj eq_refl (conj Hone (conj _ (conj _ (conj Sh2 (conj Al2 (conj _ _)))))))))))).
  - repeat constructor; assumption.
  - change (bpow radix2 0) with 1.
    pose proof (bpow_lt radix2 1 emax ltac:(unfold emax; lia)). change (bpow radix2 1) with 2 in H. lra.
  - vm_compute. reflexivity.
  - constructor; [ | constructor; [ | constructor ] ]; unfold key_below; cbn [block_key].
    + rewrite Habs3. apply bpow_lt. lia.
    + rewrite Habs4. apply bpow_lt. lia.
  - refine (conj Hfx (conj _ (conj Hsafe _))).
    + rewrite HXr. apply Rgt_not_eq, bpow_gt_0.
    + rewrite HXu. change (bpow radix2 0) with 1. lra.
Qed.

(* ... and the pending twin settles: the next state is N, not P. *)
Corollary pending_twin_witness_settles :
  exists Q' E', cinv_N Q' E' [] /\ forall r, ~ cinv_P Q' E' r.
Proof.
  destruct pending_twin_witness as (_ & _ & HP).
  assert (Hsk : skipn 5 (wG :: wxs) = [wX]) by reflexivity. rewrite Hsk in HP.
  destruct (pending_twin_settles _ _ _ _ HP I) as [HN HnP].
  exact (ex_intro _ _ (ex_intro _ _ (conj HN HnP))).
Qed.

Print Assumptions pending_twin_witness.
Print Assumptions pending_twin_witness_settles.
