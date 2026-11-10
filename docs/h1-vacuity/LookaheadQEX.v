(* LookaheadQEX.v -- QEX for the strict look-ahead |h| < ulp(g_next).

   Binary64, Priest-valid, finite, tiny abs-sum.  With M = 2^53 - 1:
       e = [M; M 2^-53]      f = [M; M 2^-53; 2^-54]
   sorted: [2^-54; M2^-53; M2^-53; M; M].  The cascade's third error is
   h = 1 and the next input is M with ulp(M) = 1: EQUALITY, not <.
   Mechanism: two earlier ties leave the accumulator Q = 2 (proved by the
   computed cascade `q_cascade`).  The TwoSum of M and 2 is 2^53 + 1, a
   midpoint of the binade [2^53, 2^54) (spacing 2); round-half-even picks
   2^53 (even mantissa), error +1 = ulp(M).  This is exactly the T state:
   Q = 2^53 = s 2^M, h = 1 = s 2^c with M = mag M = 53, c = 0. 
   Attribution: the strict look-ahead was the corpus's own proof obligation
   (LOOKAHEAD_h in B64_CarryCleanCascade.cinv_N_step), not a claim of any
   published source.  An internal dead route, not an external erratum.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human-reviewed (2026-11-10, J. Bloemscheer, on main @ 4eb6c4b6):
     rung 1 (cascade re-derived by hand under RNE).
     Assisted-by: Claude
*)
From Stdlib Require Import Reals ZArith Lia Lra List.
From Flocq Require Import IEEE754.Binary Core Ulp.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib B64_Pff_bridge
     B64_Expansion B64_FastExpansionSum B64_FastExpansionSum_Shewchuk
     B64_Shewchuk_Thm13_counterexample B64_Overlap_Hierarchy
     B64_Priest_FES_counterexample DivRoundPow2_b64
     B64_CarryCleanAlgo B64_CarryCleanCore B64_CarryCleanLadder.
Import ListNotations.
Local Open Scope R_scope.
Local Abbreviation b2r := (Binary.B2R prec emax).

Definition qA : binary64 := bM_scaled 0 eq_refl.                (* M *)
Definition qB : binary64 := bM_scaled (-53) eq_refl.            (* M 2^-53 *)
Definition qG : binary64 :=
  Binary.B754_finite prec emax false 4503599627370496 (-106) eq_refl.   (* 2^-54 *)
Definition qe : list binary64 := [qA; qB].
Definition qf : list binary64 := [qA; qB; qG].

Definition one_b : binary64 := Binary.B754_finite prec emax false 4503599627370496 (-52) eq_refl.

Lemma q_priest : priest_chain qe /\ priest_chain qf.
Proof.
  unfold qe, qf, qA, qB, qG, bM_scaled, mant_M. simpl.
  repeat split; apply priest_fin; zdec.
Qed.

Lemma q_finite : Forall b64_fin qe /\ Forall b64_fin qf.
Proof. unfold qe, qf, qA, qB, qG, bM_scaled. repeat split; repeat constructor; reflexivity. Qed.

Lemma q_sort : sort_by_abs (qe ++ qf) = [qG; qB; qB; qA; qA].
Proof.
  assert (HGB : Rabs (b2r qG) < Rabs (b2r qB)).
  { unfold qG, qB, bM_scaled, mant_M. rewrite !abs_B2R_fin. apply scaled_lt'; zdec. }
  assert (HBA : Rabs (b2r qB) < Rabs (b2r qA)).
  { unfold qA, qB, bM_scaled, mant_M. rewrite !abs_B2R_fin. apply scaled_lt'; zdec. }
  assert (HAA : Rabs (b2r qA) = Rabs (b2r qA)) by reflexivity.
  assert (HBB : Rabs (b2r qB) = Rabs (b2r qB)) by reflexivity.
  unfold qe, qf. cbn [app sort_by_abs].
  repeat first [ rewrite insert_by_abs_nil
               | rewrite insert_by_abs_le by lra
               | rewrite insert_by_abs_gt by lra ].
  reflexivity.
Qed.

(* The cascade over the sorted list: errors oldest first, final accumulator. *)
Lemma q_cascade :
  fast_expansion_sum qe qf
  = [ Binary.B754_finite prec emax false 4503599627370496 2 eq_refl;     (* 2^54 *)
      Binary.B754_finite prec emax true 4503599627370496 (-52) eq_refl;  (* -1 *)
      one_b;                                                             (* +1 *)
      Binary.B754_finite prec emax true 4503599627370496 (-105) eq_refl; (* -2^-53 *)
      Binary.B754_finite prec emax true 4503599627370496 (-106) eq_refl  (* -2^-54 *) ].
Proof.
  apply map_B2FF_inj. unfold fast_expansion_sum. rewrite q_sort.
  vm_compute. reflexivity.
Qed.

Lemma ulp_qA : ulp radix2 b64_fexp (b2r qA) = 1.
Proof.
  assert (Hq : b2r qA = IZR 9007199254740991).
  { unfold qA, bM_scaled, mant_M. rewrite B2R_fin. cbn [cond_Zopp]. 
    replace (bpow radix2 0) with 1 by reflexivity. rewrite Rmult_1_r. reflexivity. }
  assert (H0 : b2r qA <> 0) by (rewrite Hq; apply not_0_IZR; lia).
  rewrite (ulp_neq_0 _ _ _ H0).
  assert (Hm : mag radix2 (b2r qA) = 53%Z :> Z).
  { apply mag_unique. rewrite Hq. rewrite Rabs_pos_eq by (apply IZR_le; lia). split.
    - change (bpow radix2 (53 - 1)) with (IZR (2 ^ 52)). apply IZR_le. lia.
    - change (bpow radix2 53) with (IZR (2 ^ 53)). apply IZR_lt. lia. }
  unfold cexp. rewrite Hm. unfold b64_fexp, SpecFloat.fexp, SpecFloat.emin, prec, emax. cbn.
  replace (Z.max (53 - 53) (3 - 1024 - 53))%Z with 0%Z by reflexivity. reflexivity.
Qed.

(* abs_sum bound: five numbers each <= 2^53 *)
Lemma q_small : abs_sum qe + abs_sum qf <= bpow radix2 (emax - 5).
Proof.
  assert (Hb : forall k, (k <= 0)%Z -> forall (H : SpecFloat.bounded prec emax mant_M k = true),
           Rabs (b2r (bM_scaled k H)) <= bpow radix2 53).
  { intros k Hk H. unfold bM_scaled. rewrite abs_B2R_fin.
    apply Rle_trans with (IZR 9007199254740991 * 1).
    - apply Rmult_le_compat_l; [ apply IZR_le; lia | ].
      replace 1 with (bpow radix2 0) by reflexivity. apply bpow_le, Hk.
    - rewrite Rmult_1_r. change (bpow radix2 53) with (IZR (2 ^ 53)). apply IZR_le. unfold mant_M. lia. }
  assert (HG : Rabs (b2r qG) <= bpow radix2 53).
  { unfold qG. rewrite abs_B2R_fin.
    assert (IZR 4503599627370496 <= bpow radix2 52 * 1) by (change (bpow radix2 52) with (IZR (2^52)); lra).
    pose proof (bpow_le radix2 (-106) 0 ltac:(lia)) as Hk.
    replace (bpow radix2 0) with 1 in Hk by reflexivity.
    pose proof (bpow_le radix2 52 53 ltac:(lia)).
    pose proof (bpow_gt_0 radix2 (-106)).
    nra. }
  assert (HA := Hb 0%Z ltac:(lia) eq_refl). assert (HB := Hb (-53)%Z ltac:(lia) eq_refl).
  unfold qe, qf. cbn [abs_sum]. unfold qA, qB in *. 
  assert (H56 : 5 * bpow radix2 53 <= bpow radix2 (emax - 5)).
  { assert (E56 : bpow radix2 56 = 8 * bpow radix2 53)
      by (replace 56%Z with (53 + 3)%Z by reflexivity; rewrite bpow_plus; change (bpow radix2 3) with 8; ring).
    pose proof (bpow_le radix2 56 (emax - 5) ltac:(unfold emax; lia)).
    pose proof (bpow_gt_0 radix2 53). lra. }
  lra.
Qed.

(* THE QEX: the errors are [-2^-54; -2^-53; +1; -1] oldest first; the third,
   h_3 = +1, equals ulp of the NEXT input qA. *)
Theorem lookahead_strict_false :
  exists e f g gs,
    priest_chain e /\ priest_chain f /\ Forall b64_fin e /\ Forall b64_fin f /\
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) /\
    sort_by_abs (e ++ f) = g :: gs /\
    exists j, (S j < length gs)%nat /\
      Rabs (b2r (nth j (fst (b64_grow_expansion_aux g gs)) one_b))
      = ulp radix2 b64_fexp (b2r (nth (S j) gs one_b)).
Proof.
  destruct q_priest as [Pe Pf]. destruct q_finite as [Fe Ff].
  exists qe, qf, qG, [qB; qB; qA; qA].
  refine (conj Pe (conj Pf (conj Fe (conj Ff (conj q_small (conj q_sort _)))))).
  exists 2%nat. split; [ cbn; lia | ].
  assert (Hc : fst (b64_grow_expansion_aux qG [qB; qB; qA; qA])
               = [ Binary.B754_finite prec emax true 4503599627370496 (-106) eq_refl;
                   Binary.B754_finite prec emax true 4503599627370496 (-105) eq_refl;
                   one_b;
                   Binary.B754_finite prec emax true 4503599627370496 (-52) eq_refl ]).
  { pose proof q_cascade as H. unfold fast_expansion_sum in H. rewrite q_sort in H.
    destruct (b64_grow_expansion_aux qG [qB; qB; qA; qA]) as [hs q] eqn:E.
    cbn [fst]. injection H as Hq Hhs. apply (f_equal (@rev binary64)) in Hhs.
    rewrite rev_involutive in Hhs. cbn in Hhs. exact Hhs. }
  rewrite Hc. cbn [nth]. rewrite ulp_qA.
  unfold one_b. rewrite abs_B2R_fin.
  change 4503599627370496 with (bpow radix2 52) at 1. 
  rewrite <- bpow_plus. reflexivity.
Qed.

Print Assumptions lookahead_strict_false.
