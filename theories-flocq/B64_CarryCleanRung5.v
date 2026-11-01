(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_CarryCleanRung5
   ----------------------------------------------------------------------------
   Rung 5 of the carry_clean bridge (B64_CarryClean.v): SIX components in
   total, i.e. five chained TwoSums.  Composed from B64_CarryCleanLadder.v.

   THE ARGUMENT.  Sort the six components, g1 <= .. <= g6; the keys
   |g_j| < ulp(g_(j+2)) (j = 1..4) come from `priest_keys_general`.
     steps 2-4  the layered state (`sstate_step`): h2 < ulp(g3) and
                h3 < ulp(g4), as on rung 3.
     step 5     |Q3| <= 3 ulp(g5), so |h4| <= ulp(g5) (`tie_analysis`).
                No tie: layered.  Tie: `tie_values` gives an anti pair
                (h5, h4) with Q5 = +-2B5, a twin (Q5, h4), or singles.
     step 6     after no tie at 5: |Q4| <= 3 ulp(g6) (|Q2| < 2 ulp(g4) and
                2 ulp(g4) <= ulp(g6)), so |h5| <= ulp(g6); no tie gives
                singles, a tie at the top gives `tie_finish_tail` over
                [h4; h3; h2].
                after the anti pair: ulp(g6) >= B5 (the key |g4| < ulp(g6)
                with |g4| >= B5 - 2u5), so the sixth TwoSum works in
                multiples of B5 above the pair (`anti_final`).
                after the twin: ulp(g6) >= B5 = 2^53 u5, so g6 absorbs Q5 and
                the twin moves to (h6, h4) (`twin_final`).
                after singles: the layered state continues.

   PROVED HERE, at total length 6:
     fes_carry_pattern_rung5          part (a): fes_priest_carry_pattern_n 6
     fes_reduction_nonoverlap_rung5   part (b): fes_priest_reduction_nonoverlap_n 6,
                                      for EVERY decomposition (`pattern_unique`)
     carry_clean_priest_target_rung5  the target for every total <= 6
   The Priest hypothesis enters only through `priest_keys_general`;
   `fes6_shape_of_keys` takes the four keys, |g3| <= .. <= |g6| and
   g3..g6 nonzero.  Overflow margin 2^(emax-5).

   NOT COVERED.  Seven or more components.

   NTS / JTS COUNTERPART.  None in-library (JTS/NTS use `CGAlgorithmsDD`,
   double-double); this lane serves the corpus's exact orientation.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lia Lra List Permutation.
From Flocq Require Import IEEE754.Binary Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
     B64_Pff_bridge B64_Expansion B64_FastExpansionSum
     B64_FastExpansionSum_Shewchuk B64_Overlap_Hierarchy B64_CarryCleanAlgo
     B64_CarryCleanCore B64_CarryCleanRung2 B64_CarryCleanRung3
     B64_CarryCleanRung4 B64_CarryCleanLadder.

Import ListNotations.
Local Open Scope R_scope.

Local Abbreviation b2r := (Binary.B2R prec emax).
Local Abbreviation RN := (round radix2 b64_fexp (BinarySingleNaN.round_mode mode_b64)).

Lemma cexp_mono_nz :
  forall x y : binary64, b2r x <> 0 -> b64_abs_le x y -> (cexp radix2 b64_fexp (b2r x) <= cexp radix2 b64_fexp (b2r y))%Z.
Proof.
  intros x y Hx Hxy.
  assert (Hy : b2r y <> 0).
  { intro H. unfold b64_abs_le in Hxy. rewrite H, Rabs_R0 in Hxy.
    pose proof (Rabs_pos_lt _ Hx). lra. }
  pose proof (ulp_mono x y Hxy) as U. rewrite !ulp_neq_0 in U by assumption.
  apply (le_bpow radix2). exact U.
Qed.

Lemma below_of_ulp :
  forall g h : binary64, b2r g <> 0 ->
    Rabs (b2r h) < ulp radix2 b64_fexp (b2r g) -> below (cexp radix2 b64_fexp (b2r g)) h.
Proof. intros g h Hg H. unfold below. rewrite <- ulp_neq_0 by exact Hg. exact H. Qed.

Lemma pre_step :
  forall Q h E L K g, sstate Q (h :: E) L K -> (K <= cexp radix2 b64_fexp (b2r g))%Z -> below (cexp radix2 b64_fexp (b2r g)) h ->
    Forall (below (cexp radix2 b64_fexp (b2r g))) (h :: E).
Proof.
  intros Q h E L K g (_ & _ & _ & _ & _ & BK) HK Hh.
  constructor; [ exact Hh | ]. apply (below_mono K); [ exact HK | exact BK ].
Qed.

Lemma ulp_half_of_below :
  forall g x : binary64, b2r x <> 0 -> b2r g <> 0 ->
    Rabs (b2r x) < ulp radix2 b64_fexp (b2r g) ->
    2 * ulp radix2 b64_fexp (b2r x) <= ulp radix2 b64_fexp (b2r g).
Proof.
  intros g x Hx Hg H. rewrite !ulp_neq_0 in * by assumption.
  set (cg := cexp radix2 b64_fexp (b2r g)) in *.
  assert (Hc : (cexp radix2 b64_fexp (b2r x) <= b64_fexp cg)%Z)
    by exact (cexp_le_bpow radix2 b64_fexp (b2r x) cg Hx H).
  assert (Hm : (b64_fexp cg <= cg - 1)%Z).
  { pose proof (b64_nonzero_ge_emin x Hx) as Hge.
    assert (bpow radix2 (3 - emax - prec) < bpow radix2 cg) by lra.
    apply lt_bpow in H0. unfold SpecFloat.fexp, SpecFloat.emin in *. unfold prec, emax in *. lia. }
  replace (2 * bpow radix2 (cexp radix2 b64_fexp (b2r x))) with (bpow radix2 (cexp radix2 b64_fexp (b2r x) + 1))
    by (rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
  apply bpow_le. lia.
Qed.

Lemma abs_sign : forall s x, (s = 1 \/ s = -1) -> 0 <= x -> Rabs (s * x) = x.
Proof.
  intros s x [-> | ->] Hx.
  - rewrite Rmult_1_l. apply Rabs_pos_eq, Hx.
  - replace (-1 * x) with (- x) by ring. rewrite Rabs_Ropp. apply Rabs_pos_eq, Hx.
Qed.

Lemma fmt_k_ulp :
  forall (g : binary64) (j : Z), b2r g <> 0 -> (0 < j <= 3)%Z ->
    generic_format radix2 b64_fexp (IZR j * ulp radix2 b64_fexp (b2r g)).
Proof.
  intros g j Hg Hj. rewrite ulp_neq_0 by exact Hg.
  apply (fmt_scaled j (cexp radix2 b64_fexp (b2r g)) (cexp radix2 b64_fexp (b2r g) + 2)).
  - rewrite Rabs_mult, (Rabs_pos_eq (bpow _ _)) by (left; apply bpow_gt_0).
    rewrite <- abs_IZR. rewrite bpow_plus. change (bpow radix2 2) with 4.
    assert (IZR (Z.abs j) <= 3) by (apply IZR_le; lia).
    pose proof (bpow_gt_0 radix2 (cexp radix2 b64_fexp (b2r g))). nra.
  - unfold cexp, SpecFloat.fexp. unfold prec. lia.
Qed.

(* --------------------------------------------------------------------------
   Five chained TwoSums, given the keys.  No Priest hypothesis here.
   -------------------------------------------------------------------------- *)

Definition fes6 (g1 g2 g3 g4 g5 g6 : binary64) : list binary64 :=
  fes_chain g1 [g2; g3; g4; g5; g6].

Lemma fes6_shape_of_keys :
  forall g1 g2 g3 g4 g5 g6 : binary64,
    b64_fin g1 -> b64_fin g2 -> b64_fin g3 -> b64_fin g4 -> b64_fin g5 -> b64_fin g6 ->
    cascade_safe g1 [g2; g3; g4; g5; g6] ->
    b64_abs_le g3 g4 -> b64_abs_le g4 g5 -> b64_abs_le g5 g6 ->
    b2r g3 <> 0 -> b2r g4 <> 0 -> b2r g5 <> 0 -> b2r g6 <> 0 ->
    Rabs (b2r g1) < ulp radix2 b64_fexp (b2r g3) ->
    Rabs (b2r g2) < ulp radix2 b64_fexp (b2r g4) ->
    Rabs (b2r g3) < ulp radix2 b64_fexp (b2r g5) ->
    Rabs (b2r g4) < ulp radix2 b64_fexp (b2r g6) ->
    Rabs (b2r g6) <= bpow radix2 (emax - 5) ->
    exists bs, drop_zeros (fes6 g1 g2 g3 g4 g5 g6) = flat_map cblock_expand bs
               /\ carry_shape bs.
Proof.
  intros g1 g2 g3 g4 g5 g6 F1 F2 F3 F4 F5 F6 Hsafe H34 H45 H56 N3 N4 N5 N6 K1 K2 K3 K4 Hov6.
  cbn [cascade_safe] in Hsafe. destruct Hsafe as [S2 [S3 [S4 [S5 [S6 _]]]]].
  unfold fes6, fes_chain. cbn [b64_grow_expansion_aux].
  (* step 2 *)
  pose proof (sstate_step _ _ _ _ g2 (sstate_init g1 0%Z F1) F2 S2 (Forall_nil _)) as St2.
  pose proof (ts_facts g2 g1 S2) as T2. cbv zeta in St2, T2.
  destruct (b64_TwoSum g2 g1) as [Q2 h2] eqn:E2. cbn [fst snd] in St2, T2, S3, S4, S5, S6.
  destruct T2 as (FQ2 & Fh2 & RQ2 & Hex2 & _ & _).
  (* step 3: h2 below ulp(g3) *)
  assert (Hh2 : Rabs (b2r h2) <= Rabs (b2r g1)).
  { replace (b2r h2) with (- (RN (b2r g2 + b2r g1) - (b2r g2 + b2r g1))) by (rewrite <- RQ2; lra).
    rewrite Rabs_Ropp. apply round_N_err_le_operand, Binary.generic_format_B2R. }
  assert (P3 : Forall (below (cexp radix2 b64_fexp (b2r g3))) [h2])
    by (constructor; [ apply below_of_ulp; [ exact N3 | lra ] | constructor ]).
  pose proof (sstate_step _ _ _ _ g3 St2 F3 S3 P3) as St3.
  pose proof (ts_facts g3 Q2 S3) as T3. cbv zeta in St3, T3.
  destruct (b64_TwoSum g3 Q2) as [Q3 h3] eqn:E3. cbn [fst snd] in St3, T3, S4, S5, S6.
  destruct T3 as (FQ3 & Fh3 & RQ3 & Hex3 & _ & _).
  (* step 4: h3 below ulp(g4) *)
  pose proof (ulp_mono _ _ H34) as U34. pose proof (ulp_mono _ _ H45) as U45.
  pose proof (ulp_mono _ _ H56) as U56.
  assert (HQ2 : Rabs (b2r Q2) < 2 * ulp radix2 b64_fexp (b2r g4))
    by (rewrite RQ2; apply rn_sum_lt_two_ulp; [ exact N4 | exact K2 | lra ]).
  assert (Hh3 : Rabs (b2r h3) < ulp radix2 b64_fexp (b2r g4)).
  { replace (b2r h3) with (- (RN (b2r g3 + b2r Q2) - (b2r g3 + b2r Q2))) by (rewrite <- RQ3; lra).
    rewrite Rabs_Ropp. apply rn_err_lt_ulp_top; [ exact N4 | exact H34 | exact HQ2 ]. }
  assert (P4 : Forall (below (cexp radix2 b64_fexp (b2r g4))) [h3; h2]).
  { apply (pre_step Q3 h3 [h2] _ _ g4 St3); [ | apply below_of_ulp; assumption ].
    apply Z.le_trans with (cexp radix2 b64_fexp (b2r g3)); [ apply Z.le_min_l | apply cexp_mono_nz; assumption ]. }
  pose proof (sstate_step _ _ _ _ g4 St3 F4 S4 P4) as St4.
  pose proof (ts_facts g4 Q3 S4) as T4. cbv zeta in St4, T4.
  destruct (b64_TwoSum g4 Q3) as [Q4 h4] eqn:E4. cbn [fst snd] in St4, T4, S5, S6.
  destruct T4 as (FQ4 & Fh4 & RQ4 & Hex4 & _ & _).
  set (c4 := Z.min (cexp radix2 b64_fexp (b2r g4)) (Z.max (Z.min (cexp radix2 b64_fexp (b2r g3)) _) (cexp radix2 b64_fexp (b2r Q3)))) in St4.
  assert (Hc4 : (c4 <= cexp radix2 b64_fexp (b2r g4))%Z) by apply Z.le_min_l.
  (* step 5: h4 is at most ulp(g5); a tie is possible *)
  assert (HQ3 : Rabs (b2r Q3) <= 3 * ulp radix2 b64_fexp (b2r g5)).
  { rewrite RQ3. change 3 with (IZR 3).
    apply (abs_round_le_generic radix2 b64_fexp (BinarySingleNaN.round_mode mode_b64) _ _
             (fmt_k_ulp g5 3 N5 ltac:(lia))).
    pose proof (Rabs_triang (b2r g3) (b2r Q2)). cbn [IZR IPR IPR_2]. lra. }
  pose proof (tie_analysis g5 (b2r g4) (b2r Q3) N5 H45 HQ3) as Tie5.
  cbv zeta in Tie5. rewrite <- RQ4 in Tie5. destruct Tie5 as [Bnd5 Tie5].
  assert (Eh4 : Rabs (b2r Q4 - (b2r g4 + b2r Q3)) = Rabs (b2r h4)).
  { replace (b2r Q4 - (b2r g4 + b2r Q3)) with (- b2r h4) by lra. apply Rabs_Ropp. }
  rewrite Eh4 in Bnd5, Tie5.
  set (c5 := cexp radix2 b64_fexp (b2r g5)) in *. set (c6 := cexp radix2 b64_fexp (b2r g6)) in *.
  assert (Hu5 : ulp radix2 b64_fexp (b2r g5) = bpow radix2 c5) by (apply ulp_neq_0, N5).
  assert (Hu6 : ulp radix2 b64_fexp (b2r g6) = bpow radix2 c6) by (apply ulp_neq_0, N6).
  assert (Hc56 : (c5 <= c6)%Z) by (apply cexp_mono_nz; assumption).
  assert (Hc45 : (cexp radix2 b64_fexp (b2r g4) <= c5)%Z) by (apply cexp_mono_nz; assumption).
  pose proof (bpow_gt_0 radix2 c5) as Hu5p. pose proof (bpow_gt_0 radix2 c6) as Hu6p.
  assert (Hg5u : bpow radix2 c5 <= Rabs (b2r g5)) by (rewrite <- Hu5; apply ulp_le_abs_b64, N5).
  assert (Hov5 : 2 * bpow radix2 c5 < bpow radix2 emax).
  { assert (8 * bpow radix2 (emax - 5) <= bpow radix2 emax).
    { replace (bpow radix2 emax) with (bpow radix2 ((emax - 5) + 5)) by (f_equal; ring).
      rewrite bpow_plus. change (bpow radix2 5) with 32. pose proof (bpow_gt_0 radix2 (emax - 5)). lra. }
    unfold b64_abs_le in H56. pose proof (bpow_gt_0 radix2 (emax - 5)). lra. }
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
    (* g4 is large: |g4| >= B5 - 2 u5, so c6 >= M5 *)
    rewrite Hu5 in HQ3.
    assert (Hg4l : bpow radix2 M5 - 2 * bpow radix2 c5 <= Rabs (b2r g4)).
    { pose proof (Rabs_triang_inv (b2r g4 + b2r Q3) (b2r Q3)) as Ht.
      replace (b2r g4 + b2r Q3 - b2r Q3) with (b2r g4) in Ht by ring.
      destruct Hz as [[Hz _] | [Hz _]]; rewrite Hz in Ht;
        [ rewrite Rabs_pos_eq in Ht by lra | rewrite Rabs_Ropp, Rabs_pos_eq in Ht by lra ]; lra. }
    assert (Hc6M : (M5 <= c6)%Z).
    { rewrite Hu6 in K4.
      assert (Hlt : bpow radix2 (M5 - 1) < bpow radix2 c6).
      { replace (bpow radix2 M5) with (2 * bpow radix2 (M5 - 1)) in Hg4l, HK4u.
        - lra.
        - replace (bpow radix2 M5) with (bpow radix2 ((M5 - 1) + 1)) by (f_equal; ring).
          rewrite bpow_plus. change (bpow radix2 1) with 2. ring. }
      apply lt_bpow in Hlt. lia. }
    (* the tail [h3; h2] below u5, layered *)
    destruct St4 as (_ & Ft4 & _ & _ & Lt4 & Bt4).
    inversion Ft4 as [| ? ? _ Ft]; subst.
    cbn [tl] in Bt4. destruct Lt4 as [_ Lt].
    assert (Bt : Forall (below c5) [h3; h2]) by (apply (below_mono c4); [ lia | exact Bt4 ]).
    assert (Hsign : exists s : R, (s = 1 \/ s = -1) /\ b2r Q4 = s * bpow radix2 M5
                                  /\ b2r h4 = s * bpow radix2 c5).
    { destruct Hz as [[Hz HQ] | [Hz HQ]].
      - exists 1. split; [ left; reflexivity | split; lra ].
      - exists (-1). split; [ right; reflexivity | split; lra ]. }
    destruct Hsign as (s & Hs & HQ4 & Hh4s).
    assert (Hg5l : bpow radix2 M5 - 2 * bpow radix2 c5 <= Rabs (b2r g5)) by (unfold b64_abs_le in H45; lra).
    pose proof (tie_values g5 Q4 s F5 S5 Hs N5 HMc HfM HQ4 Hg5l) as TV. cbv zeta in TV.
    pose proof (ts_facts g5 Q4 S5) as T5. cbv zeta in T5.
    destruct (b64_TwoSum g5 Q4) as [Q5 h5] eqn:E5. cbn [fst snd] in TV, T5, S6.
    fold M5 c5 in TV.
    destruct T5 as (FQ5 & Fh5 & RQ5 & Hex5 & Hno5 & _).
    destruct TV as [(Ha & HQ5) | [(Hz5 & HQ5) | (Hz5 & MQ5 & NQ5)]].
    + (* anti pair (h5, h4) *)
      apply (anti_final g6 Q5 h5 h4 [h3; h2] M5 c5); try assumption.
      * rewrite HQ5. unfold pow2_multiple.
        destruct Hs as [-> | ->]; [ exists 2%Z | exists (-2)%Z ];
          cbn [IZR IPR IPR_2]; ring.
      * lia.
      * rewrite Hh4s, Ha. ring.
      * rewrite Ha, Rabs_Ropp. apply abs_sign; [ exact Hs | lra ].
    + (* twin (Q5, h4), h5 = 0 *)
      apply (twin_final g6 Q5 h5 h4 [h3; h2] c5); try assumption.
      * lra.
      * rewrite Hu6.
        assert (bpow radix2 (c5 + 2) < bpow radix2 c6) by (apply bpow_lt; lia).
        rewrite bpow_plus in H. change (bpow radix2 2) with 4 in H. lra.
    + (* singles: the state stays layered at level c5 + 1 *)
      assert (Hh4u : Rabs (b2r h4) = bpow radix2 c5).
      { rewrite Hh4s. apply abs_sign; [ exact Hs | lra ]. }
      assert (H2c : bpow radix2 c5 < bpow radix2 (c5 + 1)) by (apply bpow_lt; lia).
      assert (St5 : sstate Q5 [h5; h4; h3; h2] (c5 + 1) (c5 + 1)).
      { assert (Bt1 : Forall (below (c5 + 1)) [h3; h2]) by (apply (below_mono c5); [ lia | exact Bt ]).
        assert (Bh4 : below (c5 + 1) h4) by (unfold below; lra).
        refine (conj FQ5 (conj _ (conj MQ5 (conj _ (conj _ _))))).
        - repeat constructor; assumption.
        - constructor; [ unfold below; rewrite Hz5, Rabs_R0; apply bpow_gt_0 | ].
          constructor; [ exact Bh4 | exact Bt1 ].
        - split; [ exists (c5 + 1)%Z; split; [ exists 0%Z; rewrite Hz5; cbn [IZR]; ring | ] | ].
          + constructor; [ exact Bh4 | exact Bt1 ].
          + split; [ exists c5; split; [ apply pow2_multiple_pm, Hh4u | exact Bt ] | exact Lt ].
        - cbn [tl]. constructor; [ exact Bh4 | exact Bt1 ]. }
      assert (P6 : Forall (below c6) [h5; h4; h3; h2]).
      { destruct St5 as (_ & _ & _ & B5 & _). apply (below_mono (c5 + 1)); [ lia | exact B5 ]. }
      pose proof (sstate_step _ _ _ _ g6 St5 F6 S6 P6) as St6. cbv zeta in St6.
      destruct (b64_TwoSum g6 Q5) as [Q6 h6] eqn:E6. cbn [fst snd] in St6.
      exact (sstate_shape _ _ _ _ St6).
  - (* NO TIE AT STEP 5 *)
    assert (Hh4lt : Rabs (b2r h4) < bpow radix2 c5) by lra.
    assert (P5 : Forall (below c5) [h4; h3; h2]).
    { apply (pre_step Q4 h4 [h3; h2] _ _ g5 St4); [ lia | exact Hh4lt ]. }
    pose proof (sstate_step _ _ _ _ g5 St4 F5 S5 P5) as St5.
    pose proof (ts_facts g5 Q4 S5) as T5. cbv zeta in St5, T5.
    destruct (b64_TwoSum g5 Q4) as [Q5 h5] eqn:E5. cbn [fst snd] in St5, T5, S6.
    fold c5 in St5.
    destruct T5 as (FQ5 & Fh5 & RQ5 & Hex5 & _ & _).
    (* step 6: h5 is at most ulp(g6) *)
    assert (Hug4 : 2 * ulp radix2 b64_fexp (b2r g4) <= ulp radix2 b64_fexp (b2r g6))
      by (apply ulp_half_of_below; assumption).
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
    destruct (Req_dec (Rabs (b2r h5)) (bpow radix2 c6)) as [Tie' | NoTie'].
    + (* tie at step 6: the top, as on rung 4 *)
      destruct (Tie6 Tie') as (HMc & HfM & Hz).
      set (M6 := mag radix2 (b2r g6)) in *.
      assert (Hsign : exists s : R, (s = 1 \/ s = -1) /\ b2r Q5 = s * bpow radix2 M6
                                    /\ b2r h5 = s * bpow radix2 c6).
      { destruct Hz as [[Hz HQ] | [Hz HQ]].
        - exists 1. split; [ left; reflexivity | split; lra ].
        - exists (-1). split; [ right; reflexivity | split; lra ]. }
      destruct Hsign as (s & Hs & HQ5 & Hh5s).
      assert (Hg6l : bpow radix2 M6 - 2 * bpow radix2 c6 <= Rabs (b2r g6)).
      { rewrite Hu6 in HQ4.
        pose proof (Rabs_triang_inv (b2r g5 + b2r Q4) (b2r Q4)) as Ht.
        replace (b2r g5 + b2r Q4 - b2r Q4) with (b2r g5) in Ht by ring.
        pose proof (bpow_gt_0 radix2 M6).
        destruct Hz as [[Hz _] | [Hz _]]; rewrite Hz in Ht;
          [ rewrite Rabs_pos_eq in Ht by lra | rewrite Rabs_Ropp, Rabs_pos_eq in Ht by lra ];
          unfold b64_abs_le in H56; lra. }
      pose proof (tie_values g6 Q5 s F6 S6 Hs N6 HMc HfM HQ5 Hg6l) as TV. cbv zeta in TV.
      pose proof (ts_facts g6 Q5 S6) as T6. cbv zeta in T6.
      destruct (b64_TwoSum g6 Q5) as [Q6 h6] eqn:E6. cbn [fst snd] in TV, T6.
      fold M6 c6 in TV.
      destruct T6 as (FQ6 & Fh6 & _ & _ & _ & _).
      destruct St5 as (_ & Ft5 & _ & _ & Lt5 & Bt5).
      inversion Ft5 as [| ? ? _ Ft]; subst. cbn [tl] in Bt5. destruct Lt5 as [_ Lt].
      assert (Hh5u : Rabs (b2r h5) = bpow radix2 c6) by exact Tie'.
      assert (Hov6' : 2 * bpow radix2 c6 < bpow radix2 emax).
      { assert (bpow radix2 c6 <= Rabs (b2r g6)) by (rewrite <- Hu6; apply ulp_le_abs_b64, N6).
        assert (8 * bpow radix2 (emax - 5) <= bpow radix2 emax).
        { replace (bpow radix2 emax) with (bpow radix2 ((emax - 5) + 5)) by (f_equal; ring).
          rewrite bpow_plus. change (bpow radix2 5) with 32. pose proof (bpow_gt_0 radix2 (emax - 5)). lra. }
        pose proof (bpow_gt_0 radix2 (emax - 5)). lra. }
      pose proof (bpow_gt_0 radix2 M6).
      assert (HcM6 : bpow radix2 c6 < bpow radix2 M6) by (apply bpow_lt; lia).
      apply (tie_finish_tail Q6 h6 h5 [h4; h3; h2] c6); try assumption.
      * eapply below_mono; [ | exact Bt5 ]. lia.
      * destruct TV as [(Ha & HQ6) | [(Hz6 & HQ6) | (Hz6 & MQ6 & NQ6)]].
        { left. split; [ rewrite Ha, Hh5s; ring | split ].
          - rewrite HQ6.
            assert (HZ : IZR (Zpower radix2 (M6 - c6)) * bpow radix2 c6 = bpow radix2 M6).
            { rewrite IZR_Zpower by lia. rewrite <- bpow_plus. f_equal. ring. }
            destruct Hs as [-> | ->];
              [ exists (2 * Zpower radix2 (M6 - c6))%Z | exists (- (2 * Zpower radix2 (M6 - c6)))%Z ];
              rewrite ?opp_IZR, mult_IZR; rewrite <- HZ; cbn [IZR IPR IPR_2]; ring.
          - rewrite HQ6, abs_sign; [ lra | exact Hs | lra ]. }
        { right; left. split; [ exact Hz6 | rewrite HQ6, Hh5s; ring ]. }
        { right; right. split; [ exact Hz6 | split; assumption ]. }
    + (* no tie at step 6: layered throughout *)
      assert (P6 : Forall (below c6) [h5; h4; h3; h2]).
      { apply (pre_step Q5 h5 [h4; h3; h2] _ _ g6 St5); [ fold c6; lia | unfold below; fold c6; lra ]. }
      pose proof (sstate_step _ _ _ _ g6 St5 F6 S6 P6) as St6. cbv zeta in St6.
      destruct (b64_TwoSum g6 Q5) as [Q6 h6] eqn:E6. cbn [fst snd] in St6.
      exact (sstate_shape _ _ _ _ St6).
Qed.

(* --------------------------------------------------------------------------
   RUNG 5.
   -------------------------------------------------------------------------- *)

Lemma fes_rung5_shape :
  forall e f : list binary64,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
    (length e + length f = 6)%nat ->
    exists bs, drop_zeros (fast_expansion_sum e f) = flat_map cblock_expand bs
               /\ carry_shape bs.
Proof.
  intros e f He Hf Hef Hff Hov Hlen.
  pose proof (fes_cascade_safe e f Hef Hff Hov) as Hsafe.
  assert (Hfin : Forall b64_fin (sort_by_abs (e ++ f)))
    by (apply sort_by_abs_Forall, Forall_app; split; assumption).
  assert (Hl6 : length (sort_by_abs (e ++ f)) = 6%nat)
    by (rewrite sort_by_abs_length, length_app; exact Hlen).
  assert (Hbig : Forall (fun x => Rabs (b2r x) <= bpow radix2 (emax - 5)) (sort_by_abs (e ++ f))).
  { pose proof (abs_le_abs_sum (sort_by_abs (e ++ f))) as Hs.
    rewrite abs_sum_sort, abs_sum_app in Hs.
    eapply Forall_impl; [ | exact Hs ]. cbn beta. intros x Hx. lra. }
  pose proof (sort_by_abs_sorted (e ++ f)) as Hsort.
  pose proof (fun j => priest_keys_general e f j He Hf) as Hk.
  pose proof (fun j => priest_third_nonzero e f j He Hf) as Hnz.
  cbv zeta in Hk, Hnz.
  destruct (sort_by_abs (e ++ f)) as [| g1 [| g2 [| g3 [| g4 [| g5 [| g6 [| g7 rest]]]]]]] eqn:Hs;
    cbn [length] in Hl6; try lia.
  pose proof (Hk 0%nat ltac:(cbn; lia)) as K1. pose proof (Hk 1%nat ltac:(cbn; lia)) as K2.
  pose proof (Hk 2%nat ltac:(cbn; lia)) as K3. pose proof (Hk 3%nat ltac:(cbn; lia)) as K4.
  pose proof (Hnz 2%nat ltac:(lia) ltac:(cbn; lia)) as N3. pose proof (Hnz 3%nat ltac:(lia) ltac:(cbn; lia)) as N4.
  pose proof (Hnz 4%nat ltac:(lia) ltac:(cbn; lia)) as N5. pose proof (Hnz 5%nat ltac:(lia) ltac:(cbn; lia)) as N6.
  cbn [nth Nat.add] in K1, K2, K3, K4, N3, N4, N5, N6.
  inversion Hsort as [ | | ? ? ? H12 Hs2 ]; subst.
  inversion Hs2 as [ | | ? ? ? H23 Hs3 ]; subst.
  inversion Hs3 as [ | | ? ? ? H34 Hs4 ]; subst.
  inversion Hs4 as [ | | ? ? ? H45 Hs5 ]; subst.
  inversion Hs5 as [ | | ? ? ? H56 _ ]; subst.
  inversion Hfin as [| ? ? F1 Hfin2]; subst.
  inversion Hfin2 as [| ? ? F2 Hfin3]; subst.
  inversion Hfin3 as [| ? ? F3 Hfin4]; subst.
  inversion Hfin4 as [| ? ? F4 Hfin5]; subst.
  inversion Hfin5 as [| ? ? F5 Hfin6]; subst.
  inversion Hfin6 as [| ? ? F6 _]; subst.
  assert (Hov6 : Rabs (b2r g6) <= bpow radix2 (emax - 5)).
  { rewrite Forall_forall in Hbig. apply Hbig. cbn. tauto. }
  unfold fast_expansion_sum. rewrite Hs.
  exact (fes6_shape_of_keys g1 g2 g3 g4 g5 g6 F1 F2 F3 F4 F5 F6 Hsafe H34 H45 H56
           N3 N4 N5 N6 K1 K2 K3 K4 Hov6).
Qed.

(* Bridge part (a) at total length 6. *)
Theorem fes_carry_pattern_rung5 : fes_priest_carry_pattern_n 6.
Proof.
  intros e f He Hf Hef Hff Hov Hlen.
  destruct (fes_rung5_shape e f He Hf Hef Hff Hov Hlen) as [bs [Hl [Hok [Hdec _]]]].
  exists bs. split; [ exact Hl | split; assumption ].
Qed.

(* Bridge part (b) at total length 6, for EVERY decomposition. *)
Theorem fes_reduction_nonoverlap_rung5 : fes_priest_reduction_nonoverlap_n 6.
Proof.
  intros e f He Hf Hef Hff Hov Hlen bs Hl Hp.
  destruct (fes_rung5_shape e f He Hf Hef Hff Hov Hlen) as [bs0 [Hl0 Hs0]].
  exact (reduction_of_any_pattern _ bs0 bs Hl0 Hs0 Hl Hp).
Qed.

(* The target on rung 5, and on all of rungs 1-5 together. *)
Corollary carry_clean_priest_target_rung5 :
  forall e f : list binary64,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
    (length e + length f <= 6)%nat ->
    nonoverlapping_chain (carry_clean (fast_expansion_sum e f)).
Proof.
  intros e f He Hf Hef Hff Hov Hlen.
  destruct (Nat.eq_dec (length e + length f) 6) as [H6 | H6].
  - destruct (fes_rung5_shape e f He Hf Hef Hff Hov H6) as [bs [Hl Hs]].
    apply (carry_clean_nonoverlap_of_shape _ bs Hl Hs).
  - apply carry_clean_priest_target_rung4; [ assumption .. | lia ].
Qed.

Print Assumptions fes6_shape_of_keys.
Print Assumptions fes_carry_pattern_rung5.
Print Assumptions fes_reduction_nonoverlap_rung5.
Print Assumptions carry_clean_priest_target_rung5.
