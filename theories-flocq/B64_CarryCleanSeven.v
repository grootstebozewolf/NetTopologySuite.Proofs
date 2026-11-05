(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_CarryCleanSeven
   ----------------------------------------------------------------------------
   Fast-Expansion-Sum on two Priest expansions with seven components in
   total: after dropping zeros, every adjacent pair of the raw output
   overlaps by at most one bit (`overlap_within_chain 1`).  Seven is the
   first total where one chain can carry two ties (one at step 5, one at
   step 7).

   THE ARGUMENT.  The block-layered state of B64_CarryCleanOneBit, run one
   step further.  A tie at step 5 leaves an anti pair, a twin, or a single;
   after an anti pair or a single the seventh step is the top step again
   (`bstate_top`), after a twin it is a plain step.  A tie at step 6 makes
   step 7 a plain step or the twin step.  With no earlier tie, step 7's
   partner Q5 is at most 7/2 ulp(g7) (half-unit bounds on Q3, Q4, Q5), inside
   the 4 ulp(g7) range of `tie_analysis_wide`.  No carry cascade: a twin
   pending after step 5 or 6 is closed by the next step and meets no tie.

   PROVED HERE:
     fes7_shape_of_keys_aligned       the seven-step chain, aligned shape
     fes_rung6_shape_aligned          the same for sorted Priest inputs
     fes_overlap_within_1_n7          total 7: one bit
     fes_overlap_within_1_le7         every total <= 7
     fes_carry_pattern_n7             carry pattern (a) at total 7
     fes_reduction_nonoverlap_n7      reduction (b) at total 7
     carry_clean_priest_target_le7    carry_clean nonoverlapping, totals <= 7

   NOT COVERED.  Eight or more components.  This is NOT Priest's bound or
   any general Fast-Expansion-Sum theorem: it is the n = 7 instance only.

   topic: binary64
   claimId: fes-overlap-within-1-n7
   witness: fes_overlap_within_1_n7

   NTS / JTS COUNTERPART.  None in-library (JTS/NTS use `CGAlgorithmsDD`,
   double-double); this lane serves the corpus's exact orientation.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Grok Bot
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lia Lra List Permutation.
From Flocq Require Import IEEE754.Binary Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
     B64_Pff_bridge B64_Expansion B64_FastExpansionSum
     B64_FastExpansionSum_Shewchuk B64_Overlap_Hierarchy B64_CarryCleanAlgo
     B64_CarryCleanCore B64_CarryCleanRung2 B64_CarryCleanRung3
     B64_CarryCleanRung4 B64_CarryCleanLadder B64_CarryCleanRung5
     B64_CarryCleanOneBit.

Import ListNotations.
Local Open Scope R_scope.

Local Abbreviation b2r := (Binary.B2R prec emax).
Local Abbreviation RN := (round radix2 b64_fexp (BinarySingleNaN.round_mode mode_b64)).

(* --------------------------------------------------------------------------
   The seven-step chain.
   -------------------------------------------------------------------------- *)

Definition fes7 (g1 g2 g3 g4 g5 g6 g7 : binary64) : list binary64 :=
  fes_chain g1 [g2; g3; g4; g5; g6; g7].

Lemma fes7_shape_of_keys_aligned :
  forall g1 g2 g3 g4 g5 g6 g7 : binary64,
    b64_fin g1 -> b64_fin g2 -> b64_fin g3 -> b64_fin g4 -> b64_fin g5 -> b64_fin g6 -> b64_fin g7 ->
    cascade_safe g1 [g2; g3; g4; g5; g6; g7] ->
    b64_abs_le g3 g4 -> b64_abs_le g4 g5 -> b64_abs_le g5 g6 -> b64_abs_le g6 g7 ->
    b2r g3 <> 0 -> b2r g4 <> 0 -> b2r g5 <> 0 -> b2r g6 <> 0 -> b2r g7 <> 0 ->
    Rabs (b2r g1) < ulp radix2 b64_fexp (b2r g3) ->
    Rabs (b2r g2) < ulp radix2 b64_fexp (b2r g4) ->
    Rabs (b2r g3) < ulp radix2 b64_fexp (b2r g5) ->
    Rabs (b2r g4) < ulp radix2 b64_fexp (b2r g6) ->
    Rabs (b2r g5) < ulp radix2 b64_fexp (b2r g7) ->
    Rabs (b2r g7) <= bpow radix2 (emax - 5) ->
    exists bs, drop_zeros (fes7 g1 g2 g3 g4 g5 g6 g7) = flat_map cblock_expand bs
               /\ carry_shape bs /\ pairs_aligned bs.
Proof.
  intros g1 g2 g3 g4 g5 g6 g7 F1 F2 F3 F4 F5 F6 F7 Hsafe H34 H45 H56 H67 N3 N4 N5 N6 N7
    K1 K2 K3 K4 K5 Hov7.
  cbn [cascade_safe] in Hsafe. destruct Hsafe as [S2 [S3 [S4 [S5 [S6 [S7 _]]]]]].
  unfold fes7, fes_chain. cbn [b64_grow_expansion_aux].
  (* step 2 *)
  pose proof (bstate_step _ _ _ _ g2 (bstate_init g1 F1) F2 S2 (Forall_nil _)) as [St2 _].
  pose proof (ts_facts g2 g1 S2) as T2. cbv zeta in St2, T2.
  destruct (b64_TwoSum g2 g1) as [Q2 h2] eqn:E2. cbn [fst snd] in St2, T2, S3, S4, S5, S6, S7.
  destruct T2 as (FQ2 & Fh2 & RQ2 & Hex2 & _ & _).
  (* step 3: h2 below ulp(g3) *)
  assert (Hh2 : Rabs (b2r h2) <= Rabs (b2r g1)).
  { replace (b2r h2) with (- (RN (b2r g2 + b2r g1) - (b2r g2 + b2r g1))) by (rewrite <- RQ2; lra).
    rewrite Rabs_Ropp. apply round_N_err_le_operand, Binary.generic_format_B2R. }
  assert (P3 : Forall (key_below (cexp radix2 b64_fexp (b2r g3))) (push h2 [])).
  { apply key_below_push; [ apply below_of_ulp; [ exact N3 | lra ] | constructor ]. }
  pose proof (bstate_step _ _ _ _ g3 St2 F3 S3 P3) as [St3 Kb3].
  pose proof (ts_facts g3 Q2 S3) as T3. cbv zeta in St3, Kb3, T3.
  destruct (b64_TwoSum g3 Q2) as [Q3 h3] eqn:E3. cbn [fst snd] in St3, T3, S4, S5, S6, S7.
  destruct T3 as (FQ3 & Fh3 & RQ3 & Hex3 & _ & _).
  (* step 4: h3 below ulp(g4) *)
  pose proof (ulp_mono _ _ H34) as U34. pose proof (ulp_mono _ _ H45) as U45.
  pose proof (ulp_mono _ _ H56) as U56. pose proof (ulp_mono _ _ H67) as U67.
  assert (HQ2 : Rabs (b2r Q2) < 2 * ulp radix2 b64_fexp (b2r g4))
    by (rewrite RQ2; apply rn_sum_lt_two_ulp; [ exact N4 | exact K2 | lra ]).
  assert (Hh3 : Rabs (b2r h3) < ulp radix2 b64_fexp (b2r g4)).
  { replace (b2r h3) with (- (RN (b2r g3 + b2r Q2) - (b2r g3 + b2r Q2))) by (rewrite <- RQ3; lra).
    rewrite Rabs_Ropp. apply rn_err_lt_ulp_top; [ exact N4 | exact H34 | exact HQ2 ]. }
  assert (P4 : Forall (key_below (cexp radix2 b64_fexp (b2r g4))) (push h3 (push h2 []))).
  { apply (bpre_step _ h3 _ g4 Kb3); [ | apply below_of_ulp; assumption ].
    apply Z.le_trans with (cexp radix2 b64_fexp (b2r g3)); [ apply Z.le_min_l | apply cexp_mono_nz; assumption ]. }
  pose proof (bstate_step _ _ _ _ g4 St3 F4 S4 P4) as [St4 Kb4].
  pose proof (ts_facts g4 Q3 S4) as T4. cbv zeta in St4, Kb4, T4.
  destruct (b64_TwoSum g4 Q3) as [Q4 h4] eqn:E4. cbn [fst snd] in St4, T4, S5, S6, S7.
  destruct T4 as (FQ4 & Fh4 & RQ4 & Hex4 & _ & _).
  set (c4 := Z.min (cexp radix2 b64_fexp (b2r g4)) _) in Kb4.
  assert (Hc4 : (c4 <= cexp radix2 b64_fexp (b2r g4))%Z) by apply Z.le_min_l.
  (* the scale facts *)
  assert (HQ3 : Rabs (b2r Q3) <= 3 * ulp radix2 b64_fexp (b2r g5)).
  { rewrite RQ3. change 3 with (IZR 3).
    apply (abs_round_le_generic radix2 b64_fexp (BinarySingleNaN.round_mode mode_b64) _ _
             (fmt_k_ulp g5 3 N5 ltac:(lia))).
    pose proof (Rabs_triang (b2r g3) (b2r Q2)). cbn [IZR IPR IPR_2]. lra. }
  assert (Hug4 : 2 * ulp radix2 b64_fexp (b2r g4) <= ulp radix2 b64_fexp (b2r g6))
    by (apply ulp_half_of_below; assumption).
  assert (Hug5 : 2 * ulp radix2 b64_fexp (b2r g5) <= ulp radix2 b64_fexp (b2r g7))
    by (apply ulp_half_of_below; assumption).
  set (c5 := cexp radix2 b64_fexp (b2r g5)) in *. set (c6 := cexp radix2 b64_fexp (b2r g6)) in *.
  set (c7 := cexp radix2 b64_fexp (b2r g7)) in *.
  assert (Hu5 : ulp radix2 b64_fexp (b2r g5) = bpow radix2 c5) by (apply ulp_neq_0, N5).
  assert (Hu6 : ulp radix2 b64_fexp (b2r g6) = bpow radix2 c6) by (apply ulp_neq_0, N6).
  assert (Hu7 : ulp radix2 b64_fexp (b2r g7) = bpow radix2 c7) by (apply ulp_neq_0, N7).
  assert (Hc56 : (c5 <= c6)%Z) by (apply cexp_mono_nz; assumption).
  assert (Hc67 : (c6 <= c7)%Z) by (apply cexp_mono_nz; assumption).
  assert (Hc45 : (cexp radix2 b64_fexp (b2r g4) <= c5)%Z) by (apply cexp_mono_nz; assumption).
  pose proof (bpow_gt_0 radix2 c5) as Hu5p. pose proof (bpow_gt_0 radix2 c6) as Hu6p.
  pose proof (bpow_gt_0 radix2 c7) as Hu7p.
  assert (Hc57 : (c5 + 1 <= c7)%Z).
  { rewrite Hu5, Hu7 in Hug5. apply le_bpow with radix2.
    rewrite bpow_plus. change (bpow radix2 1) with 2. lra. }
  assert (Hc7e : (3 - emax - prec < c7)%Z).
  { assert (H : (3 - emax - prec <= c5)%Z) by (unfold c5, cexp, SpecFloat.fexp, SpecFloat.emin; lia). lia. }
  assert (Hg5u : bpow radix2 c5 <= Rabs (b2r g5)) by (rewrite <- Hu5; apply ulp_le_abs_b64, N5).
  assert (Hbig : 8 * bpow radix2 (emax - 5) <= bpow radix2 emax).
  { replace (bpow radix2 emax) with (bpow radix2 ((emax - 5) + 5)) by (f_equal; ring).
    rewrite bpow_plus. change (bpow radix2 5) with 32. pose proof (bpow_gt_0 radix2 (emax - 5)). lra. }
  assert (Hg7u : bpow radix2 c7 <= Rabs (b2r g7)) by (rewrite <- Hu7; apply ulp_le_abs_b64, N7).
  assert (Hg6u : bpow radix2 c6 <= Rabs (b2r g6)) by (rewrite <- Hu6; apply ulp_le_abs_b64, N6).
  unfold b64_abs_le in H45, H56, H67.
  assert (Hov5 : 2 * bpow radix2 c5 < bpow radix2 emax) by (pose proof (bpow_gt_0 radix2 (emax - 5)); lra).
  assert (Hov6 : 2 * bpow radix2 c6 < bpow radix2 emax) by (pose proof (bpow_gt_0 radix2 (emax - 5)); lra).
  assert (Hov7' : 2 * ulp radix2 b64_fexp (b2r g7) < bpow radix2 emax)
    by (rewrite Hu7; pose proof (bpow_gt_0 radix2 (emax - 5)); lra).
  (* step 5: h4 is at most ulp(g5); a tie is possible *)
  pose proof (tie_analysis g5 (b2r g4) (b2r Q3) N5 H45 HQ3) as Tie5.
  cbv zeta in Tie5. rewrite <- RQ4 in Tie5. destruct Tie5 as [Bnd5 Tie5].
  assert (Eh4 : Rabs (b2r Q4 - (b2r g4 + b2r Q3)) = Rabs (b2r h4)).
  { replace (b2r Q4 - (b2r g4 + b2r Q3)) with (- b2r h4) by lra. apply Rabs_Ropp. }
  rewrite Eh4 in Bnd5, Tie5. fold c5 in Bnd5, Tie5.
  pose proof St3 as (_ & FE3 & _ & DE3 & Sh3 & Al3 & _).
  destruct (Req_dec (Rabs (b2r h4)) (bpow radix2 c5)) as [Tie | NoTie].
  - (* TIE AT STEP 5 *)
    destruct (Tie5 Tie) as (HMc & HfM & Hz).
    set (M5 := mag radix2 (b2r g5)) in *.
    assert (HM53 : (M5 - c5 = 53)%Z).
    { assert (Hc : c5 = b64_fexp M5) by reflexivity.
      rewrite Hc in HfM |- *. unfold SpecFloat.fexp in *. unfold prec in *. lia. }
    pose proof (bpow_gt_0 radix2 M5) as HB5.
    assert (HK4u : 4 * bpow radix2 c5 <= bpow radix2 M5).
    { replace (bpow radix2 M5) with (bpow radix2 (c5 + 2 + (M5 - c5 - 2))) by (f_equal; ring).
      rewrite !bpow_plus. change (bpow radix2 2) with 4.
      assert (1 <= bpow radix2 (M5 - c5 - 2)) by (change 1 with (bpow radix2 0); apply bpow_le; lia).
      nra. }
    rewrite Hu5 in HQ3.
    assert (Hg4l : bpow radix2 M5 - 2 * bpow radix2 c5 <= Rabs (b2r g4)).
    { pose proof (Rabs_triang_inv (b2r g4 + b2r Q3) (b2r Q3)) as Ht.
      replace (b2r g4 + b2r Q3 - b2r Q3) with (b2r g4) in Ht by ring.
      destruct Hz as [[Hz _] | [Hz _]]; rewrite Hz in Ht;
        [ rewrite Rabs_pos_eq in Ht by lra | rewrite Rabs_Ropp, Rabs_pos_eq in Ht by lra ]; lra. }
    assert (Hc6M : (M5 <= c6)%Z).
    { rewrite Hu6 in K4.
      assert (Hlt : bpow radix2 (M5 - 1) < bpow radix2 c6).
      { rewrite (bpow_succ_pred M5) in Hg4l, HK4u. lra. }
      apply lt_bpow in Hlt. lia. }
    assert (Hsign : exists s : R, (s = 1 \/ s = -1) /\ b2r Q4 = s * bpow radix2 M5
                                  /\ b2r h4 = s * bpow radix2 c5).
    { destruct Hz as [[Hz HQ] | [Hz HQ]].
      - exists 1. split; [ left; reflexivity | split; lra ].
      - exists (-1). split; [ right; reflexivity | split; lra ]. }
    destruct Hsign as (s & Hs & HQ4 & Hh4s).
    assert (Hg5l : bpow radix2 M5 - 2 * bpow radix2 c5 <= Rabs (b2r g5)) by lra.
    assert (Kb4' : Forall (key_below c5) (push h3 (push h2 []))) by (apply (key_below_mono c4); [ lia | exact Kb4 ]).
    pose proof (bstate_tie g5 Q4 h4 [h3; h2] _ s F5 S5 Hs N5 HMc HfM HQ4 Hh4s Hg5l Fh4 FE3 DE3 Sh3 Al3 Kb4') as TS.
    cbv zeta in TS. fold M5 c5 in TS.
    pose proof (ts_facts g5 Q4 S5) as T5.
    destruct (b64_TwoSum g5 Q4) as [Q5 h5] eqn:E5. cbn [fst snd] in TS, T5, S6, S7.
    destruct T5 as (FQ5 & Fh5 & RQ5 & Hex5 & _ & _).
    (* |Q5| <= 2 B5 <= 2 u7, then weakened to the 7/2 u7 that bstate_top takes *)
    assert (HQ5 : Rabs (b2r Q5) <= 7 / 2 * ulp radix2 b64_fexp (b2r g7)).
    { assert (F2B : generic_format radix2 b64_fexp (2 * bpow radix2 M5)).
      { replace (2 * bpow radix2 M5) with (bpow radix2 (M5 + 1))
          by (rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
        apply generic_format_bpow. unfold SpecFloat.fexp, SpecFloat.emin. unfold prec in *.
        assert (H : (3 - emax - 53 <= c5)%Z) by (unfold c5, cexp, SpecFloat.fexp, SpecFloat.emin; unfold prec; lia).
        lia. }
      assert (H2B : Rabs (b2r Q5) <= 2 * bpow radix2 M5).
      { rewrite RQ5. apply (abs_round_le_generic radix2 b64_fexp _ _ _ F2B).
        pose proof (Rabs_triang (b2r g5) (b2r Q4)).
        assert (Rabs (b2r Q4) = bpow radix2 M5)
          by (rewrite HQ4, Rabs_mult, (Rabs_pos_eq (bpow _ _)) by lra;
              destruct Hs as [-> | ->]; [ rewrite Rabs_R1 | rewrite Rabs_left by lra ]; ring).
        assert (Rabs (b2r g5) < bpow radix2 M5)
          by (pose proof (bpow_mag_gt radix2 (b2r g5)) as Hm; fold M5 in Hm; exact Hm).
        lra. }
      assert (bpow radix2 M5 <= bpow radix2 c7) by (apply bpow_le; lia).
      rewrite Hu7. lra. }
    destruct TS as [St5 | [(Hz5 & HQh) | St5]].
    + (* anti pair (h5, h4); step 6 is a plain step, step 7 the top *)
      pose proof St5 as (_ & FE5 & _ & DE5 & Sh5 & Al5 & K5').
      assert (P6 : Forall (key_below c6) (CAnti h5 :: push h3 (push h2 [])))
        by (apply (key_below_mono M5); [ exact Hc6M | exact K5' ]).
      pose proof (bstate_step _ _ _ _ g6 St5 F6 S6 P6) as [St6 _]. cbv zeta in St6.
      pose proof (ts_facts g6 Q5 S6) as T6.
      destruct (b64_TwoSum g6 Q5) as [Q6 h6] eqn:E6. cbn [fst snd] in St6, T6, S7.
      destruct T6 as (FQ6 & Fh6 & RQ6 & Hex6 & _ & _).
      destruct (b64_TwoSum g7 Q6) as [Q7 h7] eqn:E7.
      assert (Kb7 : Forall (key_below c7) (CAnti h5 :: push h3 (push h2 [])))
        by (apply (key_below_mono M5); [ lia | exact K5' ]).
      exact (bstate_top g7 Q6 h6 Q7 h7 _ _ _ (b2r g6) (b2r Q5) F7 N7 S7 E7 St6 FE5 DE5 Sh5 Al5
               Kb7 H67 HQ5 RQ6 Hex6 Hov7').
    + (* twin (Q5, h4), h5 = 0: g6 absorbs Q5; step 7 is a plain step *)
      assert (Hq : bpow radix2 c5 < ulp radix2 b64_fexp (b2r g6) / 4).
      { rewrite Hu6. assert (bpow radix2 (c5 + 2) < bpow radix2 c6) by (apply bpow_lt; lia).
        rewrite bpow_plus in H. change (bpow radix2 2) with 4 in H. lra. }
      pose proof (bstate_twin g6 Q5 h5 h4 [h3; h2] _ c5 F6 N6 S6 Fh5 Fh4 FE3 Hz5 HQh Tie Hq Hov5
                   DE3 Sh3 Al3 Kb4') as St6.
      cbv zeta in St6.
      pose proof St6 as (_ & _ & _ & _ & _ & _ & K6').
      pose proof (bstate_step _ _ _ _ g7 St6 F7 S7 ltac:(apply (key_below_mono c6); [ exact Hc67 | exact K6' ]))
        as [St7 _].
      cbv zeta in St7.
      destruct (b64_TwoSum g6 Q5) as [Q6 h6] eqn:E6. cbn [fst snd] in St7 |- *.
      destruct (b64_TwoSum g7 Q6) as [Q7 h7] eqn:E7. cbn [fst snd] in St7.
      exact (bstate_shape _ _ _ _ St7).
    + (* single h4 at level c5 + 1; step 6 plain, step 7 the top *)
      pose proof St5 as (_ & FE5 & _ & DE5 & Sh5 & Al5 & K5').
      assert (P6 : Forall (key_below c6) (CSingle h4 :: push h3 (push h2 [])))
        by (apply (key_below_mono (c5 + 1)); [ lia | exact K5' ]).
      pose proof (bstate_step _ _ _ _ g6 St5 F6 S6 P6) as [St6 _]. cbv zeta in St6.
      pose proof (ts_facts g6 Q5 S6) as T6.
      destruct (b64_TwoSum g6 Q5) as [Q6 h6] eqn:E6. cbn [fst snd] in St6, T6, S7.
      destruct T6 as (FQ6 & Fh6 & RQ6 & Hex6 & _ & _).
      destruct (b64_TwoSum g7 Q6) as [Q7 h7] eqn:E7.
      assert (Kb7 : Forall (key_below c7) (CSingle h4 :: push h3 (push h2 [])))
        by (apply (key_below_mono (c5 + 1)); [ lia | exact K5' ]).
      exact (bstate_top g7 Q6 h6 Q7 h7 _ _ _ (b2r g6) (b2r Q5) F7 N7 S7 E7 St6 FE5 DE5 Sh5 Al5
               Kb7 H67 HQ5 RQ6 Hex6 Hov7').
  - (* NO TIE AT STEP 5 *)
    assert (Hh4lt : Rabs (b2r h4) < bpow radix2 c5) by lra.
    assert (P5 : Forall (key_below c5) (push h4 (push h3 (push h2 [])))).
    { apply (bpre_step c4 h4 _ g5 Kb4); [ lia | exact Hh4lt ]. }
    pose proof St4 as (_ & FE4 & _ & DE4 & Sh4 & Al4 & _).
    pose proof (bstate_step _ _ _ _ g5 St4 F5 S5 P5) as [St5 Kb5].
    pose proof (ts_facts g5 Q4 S5) as T5. cbv zeta in St5, Kb5, T5.
    destruct (b64_TwoSum g5 Q4) as [Q5 h5] eqn:E5. cbn [fst snd] in St5, T5, S6, S7.
    fold c5 in St5, Kb5.
    destruct T5 as (FQ5 & Fh5 & RQ5 & Hex5 & _ & _).
    (* step 6: h5 is at most ulp(g6) *)
    assert (HQ3b : Rabs (b2r Q3) <= 2 * ulp radix2 b64_fexp (b2r g6)).
    { rewrite RQ3. change 2 with (IZR 2).
      apply (abs_round_le_generic radix2 b64_fexp (BinarySingleNaN.round_mode mode_b64) _ _
               (fmt_k_ulp g6 2 N6 ltac:(lia))).
      pose proof (Rabs_triang (b2r g3) (b2r Q2)). unfold b64_abs_le in H34.
      cbn [IZR IPR IPR_2]. lra. }
    assert (HQ4 : Rabs (b2r Q4) <= 3 * ulp radix2 b64_fexp (b2r g6)).
    { rewrite RQ4. change 3 with (IZR 3).
      apply (abs_round_le_generic radix2 b64_fexp (BinarySingleNaN.round_mode mode_b64) _ _
               (fmt_k_ulp g6 3 N6 ltac:(lia))).
      pose proof (Rabs_triang (b2r g4) (b2r Q3)). cbn [IZR IPR IPR_2]. lra. }
    pose proof (tie_analysis g6 (b2r g5) (b2r Q4) N6 H56 HQ4) as Tie6.
    cbv zeta in Tie6. rewrite <- RQ5 in Tie6. destruct Tie6 as [Bnd6 Tie6].
    assert (Eh5 : Rabs (b2r Q5 - (b2r g5 + b2r Q4)) = Rabs (b2r h5)).
    { replace (b2r Q5 - (b2r g5 + b2r Q4)) with (- b2r h5) by lra. apply Rabs_Ropp. }
    rewrite Eh5 in Bnd6, Tie6. fold c6 in Bnd6, Tie6.
    assert (Kc5 : (Z.min c5 (Z.max c4 (cexp radix2 b64_fexp (b2r Q4))) <= c6)%Z) by lia.
    pose proof St5 as (_ & FE5 & _ & DE5 & Sh5 & Al5 & _).
    destruct (Req_dec (Rabs (b2r h5)) (bpow radix2 c6)) as [Tie' | NoTie'].
    + (* TIE AT STEP 6; step 7 is a plain step *)
      destruct (Tie6 Tie') as (HMc & HfM & Hz).
      set (M6 := mag radix2 (b2r g6)) in *.
      assert (HM53 : (M6 - c6 = 53)%Z).
      { assert (Hc : c6 = b64_fexp M6) by reflexivity.
        rewrite Hc in HfM |- *. unfold SpecFloat.fexp in *. unfold prec in *. lia. }
      pose proof (bpow_gt_0 radix2 M6) as HB6.
      assert (HK5u : 4 * bpow radix2 c6 <= bpow radix2 M6).
      { replace (bpow radix2 M6) with (bpow radix2 (c6 + 2 + (M6 - c6 - 2))) by (f_equal; ring).
        rewrite !bpow_plus. change (bpow radix2 2) with 4.
        assert (1 <= bpow radix2 (M6 - c6 - 2)) by (change 1 with (bpow radix2 0); apply bpow_le; lia).
        nra. }
      rewrite Hu6 in HQ4.
      assert (Hg5l : bpow radix2 M6 - 2 * bpow radix2 c6 <= Rabs (b2r g5)).
      { pose proof (Rabs_triang_inv (b2r g5 + b2r Q4) (b2r Q4)) as Ht.
        replace (b2r g5 + b2r Q4 - b2r Q4) with (b2r g5) in Ht by ring.
        destruct Hz as [[Hz _] | [Hz _]]; rewrite Hz in Ht;
          [ rewrite Rabs_pos_eq in Ht by lra | rewrite Rabs_Ropp, Rabs_pos_eq in Ht by lra ]; lra. }
      assert (Hc7M : (M6 <= c7)%Z).
      { rewrite Hu7 in K5.
        assert (Hlt : bpow radix2 (M6 - 1) < bpow radix2 c7).
        { rewrite (bpow_succ_pred M6) in Hg5l, HK5u. lra. }
        apply lt_bpow in Hlt. lia. }
      assert (Hsign : exists s : R, (s = 1 \/ s = -1) /\ b2r Q5 = s * bpow radix2 M6
                                    /\ b2r h5 = s * bpow radix2 c6).
      { destruct Hz as [[Hz HQ] | [Hz HQ]].
        - exists 1. split; [ left; reflexivity | split; lra ].
        - exists (-1). split; [ right; reflexivity | split; lra ]. }
      destruct Hsign as (s & Hs & HQ5 & Hh5s).
      assert (Hg6l : bpow radix2 M6 - 2 * bpow radix2 c6 <= Rabs (b2r g6)) by lra.
      assert (Kb5' : Forall (key_below c6) (push h4 (push h3 (push h2 [])))) by (apply (key_below_mono _ c6 _ Kc5 Kb5)).
      pose proof (bstate_tie g6 Q5 h5 [h4; h3; h2] _ s F6 S6 Hs N6 HMc HfM HQ5 Hh5s Hg6l Fh5 FE4 DE4 Sh4 Al4 Kb5') as TS.
      cbv zeta in TS. fold M6 c6 in TS.
      pose proof (ts_facts g6 Q5 S6) as T6.
      destruct (b64_TwoSum g6 Q5) as [Q6 h6] eqn:E6. cbn [fst snd] in TS, T6, S7.
      destruct T6 as (FQ6 & Fh6 & RQ6 & Hex6 & _ & _).
      destruct TS as [St6 | [(Hz6 & HQh) | St6]].
      * pose proof St6 as (_ & _ & _ & _ & _ & _ & K6').
        pose proof (bstate_step _ _ _ _ g7 St6 F7 S7 ltac:(apply (key_below_mono M6); [ exact Hc7M | exact K6' ]))
          as [St7 _].
        cbv zeta in St7. destruct (b64_TwoSum g7 Q6) as [Q7 h7] eqn:E7. cbn [fst snd] in St7.
        exact (bstate_shape _ _ _ _ St7).
      * assert (Hq : bpow radix2 c6 < ulp radix2 b64_fexp (b2r g7) / 4).
        { rewrite Hu7. assert (bpow radix2 (c6 + 2) < bpow radix2 c7) by (apply bpow_lt; lia).
          rewrite bpow_plus in H. change (bpow radix2 2) with 4 in H. lra. }
        pose proof (bstate_twin g7 Q6 h6 h5 [h4; h3; h2] _ c6 F7 N7 S7 Fh6 Fh5 FE4 Hz6 HQh Tie' Hq Hov6
                     DE4 Sh4 Al4 Kb5') as St7.
        cbv zeta in St7. destruct (b64_TwoSum g7 Q6) as [Q7 h7] eqn:E7. cbn [fst snd] in St7.
        exact (bstate_shape _ _ _ _ St7).
      * pose proof St6 as (_ & _ & _ & _ & _ & _ & K6').
        pose proof (bstate_step _ _ _ _ g7 St6 F7 S7 ltac:(apply (key_below_mono (c6 + 1)); [ lia | exact K6' ]))
          as [St7 _].
        cbv zeta in St7. destruct (b64_TwoSum g7 Q6) as [Q7 h7] eqn:E7. cbn [fst snd] in St7.
        exact (bstate_shape _ _ _ _ St7).
    + (* NO TIE AT STEP 6; step 7 is the top *)
      assert (P6 : Forall (key_below c6) (push h5 (push h4 (push h3 (push h2 []))))).
      { apply (bpre_step _ h5 _ g6 Kb5); [ fold c6; lia | fold c6; lra ]. }
      pose proof (bstate_step _ _ _ _ g6 St5 F6 S6 P6) as [St6 Kb6].
      pose proof (ts_facts g6 Q5 S6) as T6. cbv zeta in St6, Kb6, T6.
      destruct (b64_TwoSum g6 Q5) as [Q6 h6] eqn:E6. cbn [fst snd] in St6, T6, S7.
      destruct T6 as (FQ6 & Fh6 & RQ6 & Hex6 & _ & _).
      (* |Q5| <= 7/2 u7, in half-units of u7 *)
      rewrite (bpow_succ_pred c7) in Hu7.
      assert (B3 : Rabs (b2r Q3) <= IZR 3 * bpow radix2 (c7 - 1)).
      { rewrite RQ3. apply rn_le_half_units; [ exact Hc7e | lia | ].
        pose proof (Rabs_triang (b2r g3) (b2r Q2)). cbn [IZR IPR IPR_2]. lra. }
      assert (B4 : Rabs (b2r Q4) <= IZR 5 * bpow radix2 (c7 - 1)).
      { rewrite RQ4. apply rn_le_half_units; [ exact Hc7e | lia | ].
        pose proof (Rabs_triang (b2r g4) (b2r Q3)). cbn [IZR IPR IPR_2] in *. lra. }
      assert (B5 : Rabs (b2r Q5) <= IZR 7 * bpow radix2 (c7 - 1)).
      { rewrite RQ5. apply rn_le_half_units; [ exact Hc7e | lia | ].
        pose proof (Rabs_triang (b2r g5) (b2r Q4)). cbn [IZR IPR IPR_2] in *. lra. }
      assert (HQ5 : Rabs (b2r Q5) <= 7 / 2 * ulp radix2 b64_fexp (b2r g7))
        by (rewrite Hu7; cbn [IZR IPR IPR_2] in B5; lra).
      destruct (b64_TwoSum g7 Q6) as [Q7 h7] eqn:E7.
      assert (Kb7 : Forall (key_below c7) (push h5 (push h4 (push h3 (push h2 [])))))
        by (refine (key_below_mono _ c7 _ _ Kb6); lia).
      exact (bstate_top g7 Q6 h6 Q7 h7 _ _ _ (b2r g6) (b2r Q5) F7 N7 S7 E7 St6 FE5 DE5 Sh5 Al5
               Kb7 H67 HQ5 RQ6 Hex6 Hov7').
Qed.

(* --------------------------------------------------------------------------
   Sorted Priest inputs, and the headlines.
   -------------------------------------------------------------------------- *)

Lemma fes_rung6_shape_aligned :
  forall e f : list binary64,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
    (length e + length f = 7)%nat ->
    exists bs, drop_zeros (fast_expansion_sum e f) = flat_map cblock_expand bs
               /\ carry_shape bs /\ pairs_aligned bs.
Proof.
  intros e f He Hf Hef Hff Hov Hlen.
  pose proof (fes_cascade_safe e f Hef Hff Hov) as Hsafe.
  assert (Hfin : Forall b64_fin (sort_by_abs (e ++ f)))
    by (apply sort_by_abs_Forall, Forall_app; split; assumption).
  assert (Hl7 : length (sort_by_abs (e ++ f)) = 7%nat)
    by (rewrite sort_by_abs_length, length_app; exact Hlen).
  assert (Hbig : Forall (fun x => Rabs (b2r x) <= bpow radix2 (emax - 5)) (sort_by_abs (e ++ f))).
  { pose proof (abs_le_abs_sum (sort_by_abs (e ++ f))) as Hs.
    rewrite abs_sum_sort, abs_sum_app in Hs.
    eapply Forall_impl; [ | exact Hs ]. cbn beta. intros x Hx. lra. }
  pose proof (sort_by_abs_sorted (e ++ f)) as Hsort.
  pose proof (fun j => priest_keys_general e f j He Hf) as Hk.
  pose proof (fun j => priest_third_nonzero e f j He Hf) as Hnz.
  cbv zeta in Hk, Hnz.
  destruct (sort_by_abs (e ++ f)) as [| g1 [| g2 [| g3 [| g4 [| g5 [| g6 [| g7 [| g8 rest]]]]]]]] eqn:Hs;
    cbn [length] in Hl7; try lia.
  pose proof (Hk 0%nat ltac:(cbn; lia)) as K1. pose proof (Hk 1%nat ltac:(cbn; lia)) as K2.
  pose proof (Hk 2%nat ltac:(cbn; lia)) as K3. pose proof (Hk 3%nat ltac:(cbn; lia)) as K4.
  pose proof (Hk 4%nat ltac:(cbn; lia)) as K5.
  pose proof (Hnz 2%nat ltac:(lia) ltac:(cbn; lia)) as N3. pose proof (Hnz 3%nat ltac:(lia) ltac:(cbn; lia)) as N4.
  pose proof (Hnz 4%nat ltac:(lia) ltac:(cbn; lia)) as N5. pose proof (Hnz 5%nat ltac:(lia) ltac:(cbn; lia)) as N6.
  pose proof (Hnz 6%nat ltac:(lia) ltac:(cbn; lia)) as N7.
  cbn [nth Nat.add] in K1, K2, K3, K4, K5, N3, N4, N5, N6, N7.
  inversion Hsort as [ | | ? ? ? H12 Hs2 ]; subst.
  inversion Hs2 as [ | | ? ? ? H23 Hs3 ]; subst.
  inversion Hs3 as [ | | ? ? ? H34 Hs4 ]; subst.
  inversion Hs4 as [ | | ? ? ? H45 Hs5 ]; subst.
  inversion Hs5 as [ | | ? ? ? H56 Hs6 ]; subst.
  inversion Hs6 as [ | | ? ? ? H67 _ ]; subst.
  inversion Hfin as [| ? ? F1 Hfin2]; subst.
  inversion Hfin2 as [| ? ? F2 Hfin3]; subst.
  inversion Hfin3 as [| ? ? F3 Hfin4]; subst.
  inversion Hfin4 as [| ? ? F4 Hfin5]; subst.
  inversion Hfin5 as [| ? ? F5 Hfin6]; subst.
  inversion Hfin6 as [| ? ? F6 Hfin7]; subst.
  inversion Hfin7 as [| ? ? F7 _]; subst.
  assert (Hov7 : Rabs (b2r g7) <= bpow radix2 (emax - 5)).
  { rewrite Forall_forall in Hbig. apply Hbig. cbn. tauto. }
  unfold fast_expansion_sum. rewrite Hs.
  exact (fes7_shape_of_keys_aligned g1 g2 g3 g4 g5 g6 g7 F1 F2 F3 F4 F5 F6 F7 Hsafe H34 H45 H56 H67
           N3 N4 N5 N6 N7 K1 K2 K3 K4 K5 Hov7).
Qed.

Theorem fes_overlap_within_1_n7 : fes_overlap_within_1_n 7.
Proof.
  intros e f He Hf Hef Hff Hov Hlen.
  destruct (fes_rung6_shape_aligned e f He Hf Hef Hff Hov Hlen) as [bs [Hl [Hs Ha]]].
  exact (overlap_within_1_of_shape_aligned _ bs Hl Hs Ha).
Qed.

Theorem fes_overlap_within_1_le7 : forall n, (n <= 7)%nat -> fes_overlap_within_1_n n.
Proof.
  intros n Hn. destruct (Nat.eq_dec n 7) as [-> | H7]; [ exact fes_overlap_within_1_n7 | ].
  apply fes_overlap_within_1_le6. lia.
Qed.

(* Bridge part (a) at total length 7. *)
Theorem fes_carry_pattern_n7 : fes_priest_carry_pattern_n 7.
Proof.
  intros e f He Hf Hef Hff Hov Hlen.
  destruct (fes_rung6_shape_aligned e f He Hf Hef Hff Hov Hlen) as [bs [Hl [[Hok [Hdec _]] _]]].
  exists bs. split; [ exact Hl | split; assumption ].
Qed.

(* Bridge part (b) at total length 7, for EVERY decomposition. *)
Theorem fes_reduction_nonoverlap_n7 : fes_priest_reduction_nonoverlap_n 7.
Proof.
  intros e f He Hf Hef Hff Hov Hlen bs Hl Hp.
  destruct (fes_rung6_shape_aligned e f He Hf Hef Hff Hov Hlen) as [bs0 [Hl0 [Hs0 _]]].
  exact (reduction_of_any_pattern _ bs0 bs Hl0 Hs0 Hl Hp).
Qed.

(* The carry/cancel target on every total <= 7. *)
Corollary carry_clean_priest_target_le7 :
  forall e f : list binary64,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
    (length e + length f <= 7)%nat ->
    nonoverlapping_chain (carry_clean (fast_expansion_sum e f)).
Proof.
  intros e f He Hf Hef Hff Hov Hlen.
  destruct (Nat.eq_dec (length e + length f) 7) as [H7 | H7].
  - destruct (fes_rung6_shape_aligned e f He Hf Hef Hff Hov H7) as [bs [Hl [Hs _]]].
    apply (carry_clean_nonoverlap_of_shape _ bs Hl Hs).
  - apply carry_clean_priest_target_rung5; [ assumption .. | lia ].
Qed.

Print Assumptions fes7_shape_of_keys_aligned.
Print Assumptions fes_rung6_shape_aligned.
Print Assumptions fes_overlap_within_1_n7.
Print Assumptions fes_overlap_within_1_le7.
Print Assumptions fes_carry_pattern_n7.
Print Assumptions fes_reduction_nonoverlap_n7.
Print Assumptions carry_clean_priest_target_le7.
