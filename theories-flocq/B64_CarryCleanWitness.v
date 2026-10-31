(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_CarryCleanWitness
   ----------------------------------------------------------------------------
   The two QEX waypoints (cancel-only on Priest input; carry_clean beyond
   Priest), the concrete mutation pins, and the mutation replay block.

   Part of the B64_CarryClean split (umbrella: B64_CarryClean.v, which keeps
   the full module header: what is proved, what is open, the evidence).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human review pending.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lia Lra List.
From Flocq Require Import IEEE754.Binary Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib B64_Pff_bridge
     B64_Expansion B64_FastExpansionSum B64_FastExpansionSum_Shewchuk
     B64_Shewchuk_Thm13_counterexample B64_Overlap_Hierarchy
     B64_Priest_FES_counterexample DivRoundPow2_b64.
From NTS.Proofs.Flocq Require Import B64_CarryCleanAlgo.

Import ListNotations.
Local Open Scope R_scope.

(* --------------------------------------------------------------------------
   QEX 1 -- cancelling alone is not enough on Priest-valid input.

     e = [2^52, M 2^-53, M 2^-106]     f = [-M 2^-53, M 2^-106, 2^-107]

   (M = 2^53 - 1; both are Priest expansions.)  The sum emits
   [2^52, 2^-53, 0, 2^-53, -2^-106, -2^-107]: two round-half-to-even ties
   leave the same error 2^-53 twice, with a zero between them.  Cancelling
   keeps both; carrying turns them into 2^-52 and the result is clean.
   -------------------------------------------------------------------------- *)

Definition q1_A : binary64 := Binary.B754_finite prec emax false 4503599627370496 0 eq_refl.
Definition q1_D : binary64 := Binary.B754_finite prec emax true mant_M (-53) eq_refl.
Definition q1_G : binary64 := Binary.B754_finite prec emax false 4503599627370496 (-159) eq_refl.

Definition q1_e : list binary64 := [q1_A; bM_scaled (-53) eq_refl; bM_scaled (-106) eq_refl].
Definition q1_f : list binary64 := [q1_D; bM_scaled (-106) eq_refl; q1_G].

Definition q1_p53  : binary64 := Binary.B754_finite prec emax false 4503599627370496 (-105) eq_refl.
Definition q1_p52  : binary64 := Binary.B754_finite prec emax false 4503599627370496 (-104) eq_refl.
Definition q1_n106 : binary64 := Binary.B754_finite prec emax true 4503599627370496 (-158) eq_refl.
Definition q1_n107 : binary64 := Binary.B754_finite prec emax true 4503599627370496 (-159) eq_refl.

Lemma q1_priest : priest_chain q1_e /\ priest_chain q1_f.
Proof.
  unfold q1_e, q1_f, q1_A, q1_D, q1_G, bM_scaled, mant_M. simpl.
  repeat split; apply priest_fin; zdec.
Qed.

Lemma q1_sort :
  sort_by_abs (q1_e ++ q1_f)
  = [q1_G; bM_scaled (-106) eq_refl; bM_scaled (-106) eq_refl;
     bM_scaled (-53) eq_refl; q1_D; q1_A].
Proof.
  assert (HGC : Rabs (Binary.B2R prec emax q1_G)
                < Rabs (Binary.B2R prec emax (bM_scaled (-106) eq_refl))).
  { unfold q1_G, bM_scaled, mant_M. rewrite !abs_B2R_fin. apply scaled_lt'; zdec. }
  assert (HCB : Rabs (Binary.B2R prec emax (bM_scaled (-106) eq_refl))
                < Rabs (Binary.B2R prec emax (bM_scaled (-53) eq_refl))).
  { unfold bM_scaled, mant_M. rewrite !abs_B2R_fin. apply scaled_lt'; zdec. }
  assert (HBD : Rabs (Binary.B2R prec emax (bM_scaled (-53) eq_refl))
                = Rabs (Binary.B2R prec emax q1_D)).
  { unfold q1_D, bM_scaled. rewrite !abs_B2R_fin. reflexivity. }
  assert (HBA : Rabs (Binary.B2R prec emax (bM_scaled (-53) eq_refl))
                < Rabs (Binary.B2R prec emax q1_A)).
  { unfold q1_A, bM_scaled, mant_M. rewrite !abs_B2R_fin. apply scaled_lt'; zdec. }
  unfold q1_e, q1_f. cbn [app sort_by_abs].
  repeat first [ rewrite insert_by_abs_nil
               | rewrite insert_by_abs_le by lra
               | rewrite insert_by_abs_gt by lra ].
  reflexivity.
Qed.

Lemma q1_cancel :
  cancel_clean (fast_expansion_sum q1_e q1_f) = [q1_A; q1_p53; q1_p53; q1_n106; q1_n107].
Proof.
  apply map_B2FF_inj. unfold fast_expansion_sum. rewrite q1_sort.
  vm_compute. reflexivity.
Qed.

Lemma q1_carry :
  carry_clean (fast_expansion_sum q1_e q1_f) = [q1_A; q1_p52; q1_n106; q1_n107].
Proof.
  apply map_B2FF_inj. unfold fast_expansion_sum. rewrite q1_sort.
  vm_compute. reflexivity.
Qed.

Theorem cancel_clean_priest_false :
  ~ (forall e f : list binary64,
        priest_chain e -> priest_chain f ->
        nonoverlapping_chain (cancel_clean (fast_expansion_sum e f))).
Proof.
  intro H. destruct q1_priest as [He Hf].
  specialize (H q1_e q1_f He Hf). rewrite q1_cancel in H.
  destruct H as [_ [H _]].
  revert H. unfold nonoverlapping_b64. apply equal_magnitude_overlaps.
  - unfold q1_p53. apply B2R_fin_nonzero.
  - reflexivity.
Qed.

(* Plan B repairs the plan-A witness. *)
Lemma q1_carry_nonoverlapping :
  nonoverlapping_chain (carry_clean (fast_expansion_sum q1_e q1_f)).
Proof.
  rewrite q1_carry. cbn [nonoverlapping_chain]. unfold nonoverlapping_b64.
  unfold q1_A, q1_p52, q1_n106, q1_n107. rewrite !B2R_fin. cbn [cond_Zopp].
  repeat split.
  - apply (nonov_scaled _ _ 4503599627370496 0); [ reflexivity | ].
    apply abs_scaled_lt_bpow; zdec.
  - apply (nonov_scaled _ _ 4503599627370496 (-104)); [ reflexivity | ].
    apply abs_scaled_lt_bpow; zdec.
  - apply (nonov_scaled _ _ (-1) (-106)).
    + change (Z.neg 4503599627370496) with (- 4503599627370496)%Z.
      rewrite opp_IZR, IZR_mant_bpow.
      replace (bpow radix2 (-106)) with (bpow radix2 52 * bpow radix2 (-158))
        by (rewrite <- bpow_plus; f_equal; lia).
      ring.
    + apply abs_scaled_lt_bpow; zdec.
Qed.

(* Mutation pins for witness 1: the exact flop counts of both cleanups, the
   exact Compress output, and Compress's own repair of the witness. *)
Lemma q1_carry_flops :
  snd (carry_clean_cost (fast_expansion_sum q1_e q1_f)) = 1%nat.
Proof. unfold fast_expansion_sum. rewrite q1_sort. vm_compute. reflexivity. Qed.

Definition q1_cM105 : binary64 := Binary.B754_finite prec emax false mant_M (-105) eq_refl.

Lemma q1_compress :
  shewchuk_compress (fast_expansion_sum q1_e q1_f) = [q1_A; q1_cM105; q1_G].
Proof.
  apply map_B2FF_inj. unfold fast_expansion_sum. rewrite q1_sort.
  vm_compute. reflexivity.
Qed.

Lemma q1_compress_flops :
  snd (shewchuk_compress_cost (fast_expansion_sum q1_e q1_f)) = 21%nat.
Proof. unfold fast_expansion_sum. rewrite q1_sort. vm_compute. reflexivity. Qed.

Lemma q1_compress_nonoverlapping :
  nonoverlapping_chain (shewchuk_compress (fast_expansion_sum q1_e q1_f)).
Proof.
  rewrite q1_compress. cbn [nonoverlapping_chain]. unfold nonoverlapping_b64.
  unfold q1_A, q1_cM105, q1_G, mant_M. rewrite !B2R_fin. cbn [cond_Zopp].
  repeat split.
  - apply (nonov_scaled _ _ 4503599627370496 0); [ reflexivity | ].
    apply abs_scaled_lt_bpow; zdec.
  - apply (nonov_scaled _ _ 9007199254740991 (-105)); [ reflexivity | ].
    apply abs_scaled_lt_bpow; zdec.
Qed.

(* Compress's second sweep drops zero errors; no witness above produces one,
   so pin the branch on a total-function input (not an expansion): the
   first sweep stores 2^53 (2^53 + 1 ties to 2^53), the second sweep adds
   2^53 + 2 exactly and must drop the zero error. *)
Definition b2p53 : binary64 := Binary.B754_finite prec emax false 4503599627370496 1 eq_refl.
Definition b2p53p2 : binary64 := Binary.B754_finite prec emax false 4503599627370497 1 eq_refl.

Lemma compress_drops_zero_error : shewchuk_compress [b2p53; b1; b1] = [b2p53p2].
Proof. apply map_B2FF_inj. vm_compute. reflexivity. Qed.

(* The cancel branch is exercised by no sum trace above; pin it directly. *)
Lemma carry_clean_cancels_pair : carry_clean [q1_p53; b64_neg q1_p53] = [].
Proof. vm_compute. reflexivity. Qed.

(* --------------------------------------------------------------------------
   QEX 2 -- carry_clean needs BOTH inputs Priest-valid.

     e = [-2^52, (2^52+1) 2^-53, -M 2^-106]          Priest-valid
     f = [-1/2, -(2^52-1) 2^-53, -M 2^-106]          nonoverlapping only

   The sum emits [-2^52, -(1/2 - 2^-53), 0, -2^-53, 2^-105, 0].  The tie at
   1 + 2^-53 leaves an error -2^-53 next to -(1/2 - 2^-53), whose lowest bit
   is also 2^-53: an overlap of UNEQUAL magnitudes, which neither the carry
   nor the cancel touches.  The family is uniform in p (found at p = 3, 4).
   -------------------------------------------------------------------------- *)

Definition q2_e1 : binary64 := Binary.B754_finite prec emax true 4503599627370496 0 eq_refl.
Definition q2_e2 : binary64 := Binary.B754_finite prec emax false 4503599627370497 (-53) eq_refl.
Definition q2_e3 : binary64 := Binary.B754_finite prec emax true mant_M (-106) eq_refl.
Definition q2_f1 : binary64 := Binary.B754_finite prec emax true 4503599627370496 (-53) eq_refl.
Definition q2_f2 : binary64 := Binary.B754_finite prec emax true 9007199254740990 (-54) eq_refl.

Definition q2_e : list binary64 := [q2_e1; q2_e2; q2_e3].
Definition q2_f : list binary64 := [q2_f1; q2_f2; q2_e3].

Definition q2_n53  : binary64 := Binary.B754_finite prec emax true 4503599627370496 (-105) eq_refl.
Definition q2_p105 : binary64 := Binary.B754_finite prec emax false 4503599627370496 (-157) eq_refl.

Lemma q2_e_priest : priest_chain q2_e.
Proof.
  unfold q2_e, q2_e1, q2_e2, q2_e3, mant_M. simpl.
  repeat split; apply priest_fin; zdec.
Qed.

(* -(2^53 - 2) 2^-54 has lowest bit 2^-53: rewrite it with an odd
   significand. *)
Lemma q2_f2_odd :
  Binary.B2R prec emax q2_f2 = IZR (- 4503599627370495) * bpow radix2 (-53).
Proof.
  unfold q2_f2. rewrite B2R_fin. cbn [cond_Zopp].
  replace (-53)%Z with (-54 + 1)%Z by ring.
  rewrite IZR_scaled_shift by lia. f_equal.
Qed.

Lemma q2_f_nonoverlapping : nonoverlapping_chain q2_f.
Proof.
  unfold q2_f. cbn [nonoverlapping_chain]. unfold nonoverlapping_b64. repeat split.
  - apply (nonov_scaled _ _ (-1) (-1)).
    + unfold q2_f1. rewrite B2R_fin. cbn [cond_Zopp].
      change (Z.neg 4503599627370496) with (- 4503599627370496)%Z.
      rewrite opp_IZR, IZR_mant_bpow.
      replace (bpow radix2 (-1)) with (bpow radix2 52 * bpow radix2 (-53))
        by (rewrite <- bpow_plus; f_equal; lia).
      ring.
    + unfold q2_f2. rewrite B2R_fin. apply abs_scaled_lt_bpow; zdec.
  - apply (nonov_scaled _ _ (- 4503599627370495) (-53)); [ exact q2_f2_odd | ].
    unfold q2_e3, mant_M. rewrite B2R_fin. apply abs_scaled_lt_bpow; zdec.
Qed.

Lemma q2_sort :
  sort_by_abs (q2_e ++ q2_f) = [q2_e3; q2_e3; q2_f2; q2_f1; q2_e2; q2_e1].
Proof.
  assert (H32 : Rabs (Binary.B2R prec emax q2_e3) < Rabs (Binary.B2R prec emax q2_f2)).
  { unfold q2_e3, q2_f2, mant_M. rewrite !abs_B2R_fin. apply scaled_lt'; zdec. }
  assert (H21 : Rabs (Binary.B2R prec emax q2_f2) < Rabs (Binary.B2R prec emax q2_f1)).
  { unfold q2_f2, q2_f1. rewrite !abs_B2R_fin. apply scaled_lt'; zdec. }
  assert (H1e : Rabs (Binary.B2R prec emax q2_f1) < Rabs (Binary.B2R prec emax q2_e2)).
  { unfold q2_f1, q2_e2. rewrite !abs_B2R_fin. apply scaled_lt'; zdec. }
  assert (He2 : Rabs (Binary.B2R prec emax q2_e2) < Rabs (Binary.B2R prec emax q2_e1)).
  { unfold q2_e2, q2_e1. rewrite !abs_B2R_fin. apply scaled_lt'; zdec. }
  unfold q2_e, q2_f. cbn [app sort_by_abs].
  repeat first [ rewrite insert_by_abs_nil
               | rewrite insert_by_abs_le by lra
               | rewrite insert_by_abs_gt by lra ].
  reflexivity.
Qed.

Lemma q2_carry :
  carry_clean (fast_expansion_sum q2_e q2_f) = [q2_e1; q2_f2; q2_n53; q2_p105].
Proof.
  apply map_B2FF_inj. unfold fast_expansion_sum. rewrite q2_sort.
  vm_compute. reflexivity.
Qed.

Lemma q2_pair_overlap : ~ nonoverlapping_b64 q2_f2 q2_n53.
Proof.
  unfold nonoverlapping_b64, nonoverlapping_R, overlap_within.
  assert (Hb : Binary.B2R prec emax q2_n53 = IZR (-1) * bpow radix2 (-53)).
  { unfold q2_n53. rewrite B2R_fin. cbn [cond_Zopp].
    change (Z.neg 4503599627370496) with (- 4503599627370496)%Z.
    rewrite opp_IZR, IZR_mant_bpow.
    replace (bpow radix2 (-53)) with (bpow radix2 52 * bpow radix2 (-105))
      by (rewrite <- bpow_plus; f_equal; lia).
    ring. }
  assert (Hbabs : Rabs (Binary.B2R prec emax q2_n53) = bpow radix2 (-53)).
  { rewrite Hb, Rabs_mult, <- abs_IZR, (Rabs_pos_eq (bpow radix2 (-53)))
      by (left; apply bpow_gt_0).
    change (Z.abs (-1)) with 1%Z. ring. }
  assert (Haabs : bpow radix2 (-53) <= Rabs (Binary.B2R prec emax q2_f2)).
  { rewrite q2_f2_odd. apply (scaled_nonzero_ge _ (- 4503599627370495) (-53));
      [ reflexivity | ].
    pose proof (bpow_gt_0 radix2 (-53)).
    assert (IZR (- 4503599627370495) < 0) by (apply IZR_lt; lia). nra. }
  intros [ [r [s [Hx Hy]]] | [r [s [Hy Hx]]] ]; rewrite Z.add_0_r in *.
  - (* f2 = r 2^s with |n53| < 2^s: then s > -53, so f2's odd significand
       would be even. *)
    rewrite Hbabs in Hy. apply lt_bpow in Hy.
    rewrite q2_f2_odd in Hx.
    pose proof (scaled_even r s (- 4503599627370495) (-53) (eq_sym Hx) Hy) as Hev.
    vm_compute in Hev. discriminate.
  - (* n53 = r 2^s with |f2| < 2^s: but 2^s <= |n53| = 2^-53 <= |f2|. *)
    assert (Hn0 : Binary.B2R prec emax q2_n53 <> 0) by (unfold q2_n53; apply B2R_fin_nonzero).
    pose proof (scaled_nonzero_ge _ r s Hy Hn0) as Hge. lra.
Qed.

Theorem carry_clean_beyond_priest_false :
  ~ (forall e f : list binary64,
        priest_chain e -> nonoverlapping_chain f ->
        nonoverlapping_chain (carry_clean (fast_expansion_sum e f))).
Proof.
  intro H. specialize (H q2_e q2_f q2_e_priest q2_f_nonoverlapping).
  rewrite q2_carry in H. destruct H as [_ [H _]]. exact (q2_pair_overlap H).
Qed.

(* Corollary: nonoverlapping is not closed under carry_clean after the sum. *)
Theorem carry_clean_nonoverlapping_false :
  ~ (forall e f : list binary64,
        nonoverlapping_chain e -> nonoverlapping_chain f ->
        nonoverlapping_chain (carry_clean (fast_expansion_sum e f))).
Proof.
  intro H. apply carry_clean_beyond_priest_false.
  intros e f He Hf. apply H; [ apply priest_chain_nonoverlapping_chain, He | exact Hf ].
Qed.

(* Compress repairs witness 2 as well: the domain of carry_clean is
   narrower than Compress's. *)
Definition q2_nhalf : binary64 := Binary.B754_finite prec emax true 4503599627370496 (-53) eq_refl.

Lemma q2_compress :
  shewchuk_compress (fast_expansion_sum q2_e q2_f) = [q2_e1; q2_nhalf; q2_p105].
Proof.
  apply map_B2FF_inj. unfold fast_expansion_sum. rewrite q2_sort.
  vm_compute. reflexivity.
Qed.

Lemma q2_compress_nonoverlapping :
  nonoverlapping_chain (shewchuk_compress (fast_expansion_sum q2_e q2_f)).
Proof.
  rewrite q2_compress. cbn [nonoverlapping_chain]. unfold nonoverlapping_b64.
  unfold q2_e1, q2_nhalf, q2_p105. rewrite !B2R_fin. cbn [cond_Zopp].
  repeat split.
  - apply (nonov_scaled _ _ (-4503599627370496) 0); [ reflexivity | ].
    apply abs_scaled_lt_bpow; zdec.
  - apply (nonov_scaled _ _ (-1) (-1)).
    + change (Z.neg 4503599627370496) with (- 4503599627370496)%Z.
      rewrite opp_IZR, IZR_mant_bpow.
      replace (bpow radix2 (-1)) with (bpow radix2 52 * bpow radix2 (-53))
        by (rewrite <- bpow_plus; f_equal; lia).
      ring.
    + apply abs_scaled_lt_bpow; zdec.
Qed.

(* --------------------------------------------------------------------------
   Mutation replay (in-tree; not an ADR-0004 mint).  Flip exactly one line
   of the definitions above, rebuild, then restore it.  Only the concrete
   pins below may kill a mutant; any other proof that breaks is admitted for
   the run (scratch only).  Each flip loses Qed on the named pin:
     C1. `cc_push`: carry branch off (`if false then`)     pin: `q1_carry`
     C2. `cc_push`: cancel branch off              pin: `carry_clean_cancels_pair`
     C3. `cc_push`: carry pushes x, not 2x                 pin: `q1_carry`
     C4. `cc_push`: flop counter `S n` -> `n`              pin: `q1_carry_flops`
     C5. `compress_up`: `3 + n` -> `4 + n`                 pin: `q1_compress_flops`
     C6. `cc_run`: zeros no longer skipped                 pin: `q1_cancel`
     C7. `cc_run`: result `rev st` -> `st`                 pin: `q1_cancel`
     C8. `compress_down`: stored component dropped         pin: `q1_compress`
     C9. `compress_up`: zero errors kept           pin: `compress_drops_zero_error`
   C4 is the reason the flop pins exist: without `q1_carry_flops` it
   survives, because `carry_clean_fewer_flops` is an inequality and an
   undercounting counter only strengthens it.  Replayed 2026-10-29 on
   Rocq 9.2 + Flocq 4.2.2.
   -------------------------------------------------------------------------- *)

(* --------------------------------------------------------------------------
   Assumption audit.
   -------------------------------------------------------------------------- *)

Print Assumptions q1_priest.
Print Assumptions q1_sort.
Print Assumptions q1_cancel.
Print Assumptions q1_carry.
Print Assumptions cancel_clean_priest_false.
Print Assumptions q1_carry_nonoverlapping.
Print Assumptions q1_carry_flops.
Print Assumptions q1_compress.
Print Assumptions q1_compress_flops.
Print Assumptions q1_compress_nonoverlapping.
Print Assumptions carry_clean_cancels_pair.
Print Assumptions compress_drops_zero_error.
Print Assumptions q2_e_priest.
Print Assumptions q2_f_nonoverlapping.
Print Assumptions q2_sort.
Print Assumptions q2_carry.
Print Assumptions q2_pair_overlap.
Print Assumptions carry_clean_beyond_priest_false.
Print Assumptions carry_clean_nonoverlapping_false.
Print Assumptions q2_compress.
Print Assumptions q2_compress_nonoverlapping.
