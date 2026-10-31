(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_CarryCleanRung4
   ----------------------------------------------------------------------------
   Rung 4 of the carry_clean bridge (B64_CarryClean.v): FIVE components in
   total, i.e. four chained TwoSums -- the first rung where the raw output
   can contain a twin or an anti pair, so carry and cancel do real work.

   THE ARGUMENT.  Sort the five components by magnitude, g1 <= .. <= g5, and
   let (Q2, h2), .., (Q5, h5) be the four TwoSums; the output is
   [Q5; h5; h4; h3; h2].
     1. Keys (Priest + pigeonhole, by counting): any three of the five
        contain two from one Priest expansion, so |g1| < ulp(g3),
        |g2| < ulp(g4) and |g3| < ulp(g5) (`priest_keys5`).  The counting
        lemmas `stat_lt` / `stat_ge` are stated for any length.
     2. The first three TwoSums are rung 3: Q4, h4 are multiples of 2^c1 and
        h3, h2 lie below it, layered.
     3. |Q3| <= 3 u with u = ulp(g5), so the error h4 of RN(g4 + Q3) is at
        most u, and equals u only at the midpoint g4 + Q3 = +-(B + u),
        B = 2^(mag g5), which rounds to the even +-B (`tie_analysis`).
     4. No tie (|h4| < u): the output is layered, all singles, as on rung 3.
     5. The tie (Q4 = +-B, h4 = +-u): then |g5| is B - u or B - 2u, and the
        fifth TwoSum gives one of
          (i)   Q5 = +-2B, h5 = -h4          an anti pair (h5, h4)
          (iii) Q5 = h4,   h5 = 0            a twin (Q5, h4)
          (ii), (iv) Q5 a multiple of 2u, h5 = 0     singles
        (`tie_finish`); the tail [h3; h2] lies below u in every case.
     6. Uniqueness (`pattern_unique`): a list has at most one decomposition
        with the pattern, since equal neighbouring magnitudes must pair up.
        So part (b) holds for EVERY decomposition.  This replaces rung 2's
        all-singles argument (`desc_all_singles`) and does not depend on n.

   PROVED HERE, at total length 5:
     fes_carry_pattern_rung4          part (a): fes_priest_carry_pattern_n 5
     fes_reduction_nonoverlap_rung4   part (b): fes_priest_reduction_nonoverlap_n 5,
                                      for EVERY decomposition
     carry_clean_priest_target_rung4  the target for every total <= 5
   The Priest hypothesis enters only through `priest_keys5`; everything
   after it is `fes5_shape_of_keys`, which takes the three keys and
   |g3| <= |g4| <= |g5| as hypotheses.  Overflow margin 2^(emax-5).
   Outcomes (ii) and (iv) need |Q3| = 3u exactly; the proof covers them
   without deciding whether they occur.

   NOT COVERED.  Six or more components.

   NTS / JTS COUNTERPART.  None in-library (JTS/NTS use `CGAlgorithmsDD`,
   double-double); this lane serves the corpus's exact orientation.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; reviewed on PR #988 (2026-10-31).
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lia Lra List Permutation.
From Flocq Require Import IEEE754.Binary Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
     B64_Pff_bridge B64_Expansion B64_FastExpansionSum
     B64_FastExpansionSum_Shewchuk B64_Overlap_Hierarchy B64_CarryCleanAlgo
     B64_CarryCleanCore B64_CarryCleanRung2 B64_CarryCleanRung3.

Import ListNotations.
Local Open Scope R_scope.

Local Abbreviation b2r := (Binary.B2R prec emax).

(* --------------------------------------------------------------------------
   Uniqueness: a list has at most one block decomposition with the pattern.
   Equal neighbouring magnitudes must pair up (strict keys forbid two
   singles of equal magnitude), and different ones cannot.
   -------------------------------------------------------------------------- *)

Lemma b64_eq_of_R :
  forall x y : binary64, b64_fin x -> b64_fin y -> b2r x = b2r y -> b2r x <> 0 -> x = y.
Proof.
  intros x y Hx Hy Hxy Hx0.
  apply Binary.B2R_inj; [ | | exact Hxy ].
  - destruct x as [s | s | s pl Hpl | s m e H]; try discriminate; cbn in Hx0 |- *;
      [ exfalso; apply Hx0; reflexivity | reflexivity ].
  - rewrite Hxy in Hx0.
    destruct y as [s | s | s pl Hpl | s m e H]; try discriminate; cbn in Hx0 |- *;
      [ exfalso; apply Hx0; reflexivity | reflexivity ].
Qed.

Lemma expand_head_le_key :
  forall b, exists h t, cblock_expand b = h :: t /\ Rabs (b2r h) <= block_key b.
Proof.
  intros [u | x | x]; cbn [cblock_expand block_key].
  - exists u, []. split; [ reflexivity | lra ].
  - exists x, [x]. split; [ reflexivity | pose proof (Rabs_pos (b2r x)); lra ].
  - exists x, [b64_neg x]. split; [ reflexivity | lra ].
Qed.

(* The first element after block b (if any) is strictly below key b. *)
Lemma next_below_key :
  forall b r h t, keys_decreasing (b :: r) -> flat_map cblock_expand r = h :: t ->
    Rabs (b2r h) < block_key b.
Proof.
  intros b r h t Hk Hr.
  destruct r as [| b' r']; [ discriminate | ].
  destruct Hk as [Hlt _].
  destruct (expand_head_le_key b') as [h' [t' [He Hle]]].
  cbn [flat_map] in Hr. rewrite He in Hr. cbn [app] in Hr. injection Hr as <- _. lra.
Qed.

Lemma pattern_unique :
  forall bs1 bs2, carry_pattern bs1 -> carry_pattern bs2 ->
    flat_map cblock_expand bs1 = flat_map cblock_expand bs2 -> bs1 = bs2.
Proof.
  induction bs1 as [| b1 r1 IH]; intros bs2 [Hok1 Hk1] [Hok2 Hk2] He.
  - destruct bs2 as [| b2 r2]; [ reflexivity | ].
    destruct (expand_head_le_key b2) as [h [t [Hb _]]].
    cbn [flat_map] in He. rewrite Hb in He. discriminate.
  - destruct bs2 as [| b2 r2].
    { destruct (expand_head_le_key b1) as [h [t [Hb _]]].
      cbn [flat_map] in He. rewrite Hb in He. discriminate. }
    inversion Hok1 as [| ? ? Ob1 Or1]; subst. inversion Hok2 as [| ? ? Ob2 Or2]; subst.
    assert (Hk1' : keys_decreasing r1) by (destruct Hk1; assumption).
    assert (Hk2' : keys_decreasing r2) by (destruct Hk2; assumption).
    cbn [flat_map] in He.
    destruct b1 as [u | x | x]; destruct b2 as [v | y | y];
      cbn [cblock_expand app block_ok block_key] in He, Ob1, Ob2, Hk1, Hk2.
    (* same kind: the blocks agree, recurse *)
    + injection He as <- He. f_equal. apply IH; [ split | split | ]; assumption.
    + injection He as <- He.
      pose proof (next_below_key _ _ _ _ Hk1 He). cbn [block_key] in *. lra.
    + injection He as <- He.
      pose proof (next_below_key _ _ _ _ Hk1 He). cbn [block_key] in *.
      rewrite b64_neg_R, Rabs_Ropp in *. lra.
    + injection He as <- He. symmetry in He.
      pose proof (next_below_key _ _ _ _ Hk2 He). cbn [block_key] in *. lra.
    + injection He as <- He. f_equal. apply IH; [ split | split | ]; assumption.
    + injection He as <- E2 He. exfalso.
      destruct Ob1 as [[_ Hx0] _]. apply Hx0.
      assert (Hr := f_equal b2r E2). rewrite b64_neg_R in Hr. lra.
    + injection He as <- He. symmetry in He.
      pose proof (next_below_key _ _ _ _ Hk2 He). cbn [block_key] in *.
      rewrite b64_neg_R, Rabs_Ropp in *. lra.
    + injection He as <- E2 He. exfalso.
      destruct Ob1 as [_ Hx0]. apply Hx0.
      assert (Hr := f_equal b2r E2). rewrite b64_neg_R in Hr. lra.
    + injection He as <- He. f_equal. apply IH; [ split | split | ]; assumption.
Qed.

(* Part (b) for every decomposition follows from one decomposition. *)
Lemma reduction_of_any_pattern :
  forall l bs0 bs, l = flat_map cblock_expand bs0 -> carry_shape bs0 ->
    l = flat_map cblock_expand bs -> carry_pattern bs ->
    nonoverlapping_chain (flat_map cblock_reduce bs).
Proof.
  intros l bs0 bs H0 [Hok [Hdec Hno]] H Hp.
  rewrite <- (pattern_unique bs0 bs (conj Hok Hdec) Hp ltac:(rewrite <- H0; exact H)).
  exact Hno.
Qed.

(* --------------------------------------------------------------------------
   Order statistics by counting.  cnt M l counts the components of l below
   M in magnitude; in a list sorted by magnitude the j-th component is below
   M exactly when at least j + 1 components are.
   -------------------------------------------------------------------------- *)

Definition is_below (M : R) (x : binary64) : bool :=
  if Rlt_dec (Rabs (b2r x)) M then true else false.

Definition cnt (M : R) (l : list binary64) : nat := length (filter (is_below M) l).

Lemma cnt_cons_in : forall M x l, Rabs (b2r x) < M -> cnt M (x :: l) = S (cnt M l).
Proof. intros M x l H. unfold cnt, is_below. cbn [filter]. destruct (Rlt_dec _ _); [ reflexivity | contradiction ]. Qed.

Lemma cnt_cons_out : forall M x l, M <= Rabs (b2r x) -> cnt M (x :: l) = cnt M l.
Proof. intros M x l H. unfold cnt, is_below. cbn [filter]. destruct (Rlt_dec _ _); [ lra | reflexivity ]. Qed.

Lemma cnt_cons_le : forall M x l, (cnt M (x :: l) <= S (cnt M l))%nat.
Proof. intros M x l. unfold cnt, is_below. cbn [filter]. destruct (Rlt_dec _ _); cbn [length]; lia. Qed.

Lemma cnt_cons_ge : forall M x l, (cnt M l <= cnt M (x :: l))%nat.
Proof. intros M x l. unfold cnt, is_below. cbn [filter]. destruct (Rlt_dec _ _); cbn [length]; lia. Qed.

Lemma cnt_perm : forall M l l', Permutation l l' -> cnt M l = cnt M l'.
Proof.
  intros M l l' H. induction H as [| x l l' _ IH | x y l | l l' l'' _ IH1 _ IH2].
  - reflexivity.
  - unfold cnt in *. cbn [filter]. destruct (is_below M x); cbn [length]; lia.
  - unfold cnt. cbn [filter]. destruct (is_below M x), (is_below M y); reflexivity.
  - lia.
Qed.

Lemma sorted_head_le :
  forall x s, sorted_asc (x :: s) -> Forall (fun y => Rabs (b2r x) <= Rabs (b2r y)) s.
Proof.
  intros x s. revert x. induction s as [| y s IH]; intros x H; [ constructor | ].
  inversion H as [ | | ? ? ? Hxy Hs ]; subst.
  constructor; [ exact Hxy | ].
  eapply Forall_impl; [ | exact (IH y Hs) ]. cbn beta. intros z Hz. lra.
Qed.

Lemma stat_upper :
  forall M s j, sorted_asc s -> (j < length s)%nat ->
    M <= Rabs (b2r (nth j s b64_two_unit)) -> (cnt M s <= j)%nat.
Proof.
  intros M s. induction s as [| x s IH]; intros j Hs Hj Hn; [ cbn in Hj; lia | ].
  destruct j as [| j].
  - cbn [nth] in Hn. rewrite cnt_cons_out by exact Hn.
    assert (H0 : cnt M s = 0%nat).
    { pose proof (sorted_head_le x s Hs) as Hf. clear IH Hj Hs.
      induction s as [| y s IHs]; [ reflexivity | ].
      inversion Hf as [| ? ? Hy Hf']; subst.
      rewrite cnt_cons_out by lra. apply IHs, Hf'. }
    lia.
  - cbn [nth length] in Hn, Hj.
    pose proof (IH j (sorted_asc_tail _ _ Hs) ltac:(lia) Hn).
    pose proof (cnt_cons_le M x s). lia.
Qed.

Lemma stat_lower :
  forall M s j, sorted_asc s -> (j < length s)%nat ->
    Rabs (b2r (nth j s b64_two_unit)) < M -> (S j <= cnt M s)%nat.
Proof.
  intros M s. induction s as [| x s IH]; intros j Hs Hj Hn; [ cbn in Hj; lia | ].
  destruct j as [| j].
  - cbn [nth] in Hn. rewrite cnt_cons_in by exact Hn. lia.
  - cbn [nth length] in Hn, Hj.
    pose proof (IH j (sorted_asc_tail _ _ Hs) ltac:(lia) Hn).
    assert (Hx : Rabs (b2r x) < M).
    { pose proof (sorted_head_le x s Hs) as Hf. rewrite Forall_forall in Hf.
      assert (Hin : In (nth j s b64_two_unit) s) by (apply nth_In; lia).
      pose proof (Hf _ Hin). lra. }
    rewrite cnt_cons_in by exact Hx. lia.
Qed.

(* j + 1 components below M put the j-th sorted component below M. *)
Lemma stat_lt :
  forall M l s j, sorted_asc s -> Permutation l s -> (j < length s)%nat ->
    (S j <= cnt M l)%nat -> Rabs (b2r (nth j s b64_two_unit)) < M.
Proof.
  intros M l s j Hs Hp Hj Hc. rewrite (cnt_perm M l s Hp) in Hc.
  destruct (Rlt_or_le (Rabs (b2r (nth j s b64_two_unit))) M) as [H | H]; [ exact H | ].
  pose proof (stat_upper M s j Hs Hj H). lia.
Qed.

(* At most j components below M put the j-th sorted component at or above M. *)
Lemma stat_ge :
  forall M l s j, sorted_asc s -> Permutation l s -> (j < length s)%nat ->
    (cnt M l <= j)%nat -> M <= Rabs (b2r (nth j s b64_two_unit)).
Proof.
  intros M l s j Hs Hp Hj Hc. rewrite (cnt_perm M l s Hp) in Hc.
  destruct (Rlt_or_le (Rabs (b2r (nth j s b64_two_unit))) M) as [H | H]; [ | exact H ].
  pose proof (stat_lower M s j Hs Hj H). lia.
Qed.

(* --------------------------------------------------------------------------
   Round to nearest even at a midpoint.
   -------------------------------------------------------------------------- *)

Lemma round_NE_mid :
  forall (x : R) (n : Z),
    x = (IZR n + / 2) * bpow radix2 (cexp radix2 b64_fexp x) ->
    round radix2 b64_fexp (BinarySingleNaN.round_mode mode_b64) x
    = IZR (if Z.even n then n else n + 1) * bpow radix2 (cexp radix2 b64_fexp x).
Proof.
  intros x n Hx.
  change (BinarySingleNaN.round_mode mode_b64) with (Znearest (fun z => negb (Z.even z))).
  set (e := cexp radix2 b64_fexp x) in *.
  assert (Hsm : scaled_mantissa radix2 b64_fexp x = IZR n + / 2).
  { unfold scaled_mantissa. fold e. rewrite Hx, Rmult_assoc, <- bpow_plus.
    replace (e + - e)%Z with 0%Z by ring. change (bpow radix2 0) with 1. ring. }
  assert (Hfl : Zfloor (IZR n + / 2) = n).
  { apply Zfloor_imp. split; [ lra | rewrite plus_IZR; lra ]. }
  assert (Hce : Zceil (IZR n + / 2) = (n + 1)%Z).
  { apply Zceil_imp. split; [ rewrite minus_IZR, plus_IZR; lra | rewrite plus_IZR; lra ]. }
  assert (Hdn : round radix2 b64_fexp Zfloor x = IZR n * bpow radix2 e).
  { unfold round, F2R. cbn [Fnum Fexp]. fold e. rewrite Hsm, Hfl. reflexivity. }
  assert (Hup : round radix2 b64_fexp Zceil x = IZR (n + 1) * bpow radix2 e).
  { unfold round, F2R. cbn [Fnum Fexp]. fold e. rewrite Hsm, Hce. reflexivity. }
  rewrite round_N_middle.
  - rewrite Hsm, Hfl, Hdn, Hup. destruct (Z.even n); reflexivity.
  - rewrite Hdn, Hup, plus_IZR, Rmult_plus_distr_r.
    rewrite Rmult_plus_distr_r in Hx. lra.
Qed.

(* --------------------------------------------------------------------------
   Five components: the three Priest keys.  Any three of the five contain a
   Priest pair, so |g1| < ulp(g3), |g2| < ulp(g4) and |g3| < ulp(g5).
   -------------------------------------------------------------------------- *)

Definition keys5 (g1 g2 g3 g4 g5 : binary64) : Prop :=
  b2r g3 <> 0 /\ b2r g4 <> 0 /\ b2r g5 <> 0
  /\ Rabs (b2r g1) < ulp radix2 b64_fexp (b2r g3)
  /\ Rabs (b2r g2) < ulp radix2 b64_fexp (b2r g4)
  /\ Rabs (b2r g3) < ulp radix2 b64_fexp (b2r g5).

Definition ord5 (g1 g2 g3 g4 g5 : binary64) : Prop :=
  b64_abs_le g1 g2 /\ b64_abs_le g2 g3 /\ b64_abs_le g3 g4 /\ b64_abs_le g4 g5.

Lemma sorted5_ord :
  forall g1 g2 g3 g4 g5, sorted_asc [g1; g2; g3; g4; g5] -> ord5 g1 g2 g3 g4 g5.
Proof.
  intros g1 g2 g3 g4 g5 Hs.
  inversion Hs as [ | | ? ? ? H12 Hs2 ]; subst.
  inversion Hs2 as [ | | ? ? ? H23 Hs3 ]; subst.
  inversion Hs3 as [ | | ? ? ? H34 Hs4 ]; subst.
  inversion Hs4 as [ | | ? ? ? H45 _ ]; subst.
  unfold ord5, b64_abs_le. auto.
Qed.

Lemma sorted5_max :
  forall l g1 g2 g3 g4 g5, sorted_asc [g1; g2; g3; g4; g5] ->
    Permutation l [g1; g2; g3; g4; g5] ->
    forall y, In y l -> Rabs (b2r y) <= Rabs (b2r g5).
Proof.
  intros l g1 g2 g3 g4 g5 Hs Hp y Hy.
  destruct (sorted5_ord _ _ _ _ _ Hs) as (H12 & H23 & H34 & H45). unfold b64_abs_le in *.
  assert (Hin : In y [g1; g2; g3; g4; g5]) by (eapply Permutation_in; eassumption).
  destruct Hin as [<- | [<- | [<- | [<- | [<- | []]]]]]; lra.
Qed.

Ltac cnt_solve :=
  unfold cnt, is_below; cbn [filter];
  repeat match goal with |- context [Rlt_dec ?a ?b] => destruct (Rlt_dec a b) end;
  cbn [length]; try lia; lra.

Lemma keys5_of_perm :
  forall e f g1 g2 g3 g4 g5,
    priest_chain e -> priest_chain f ->
    (length e + length f = 5)%nat -> (length f <= length e)%nat ->
    sorted_asc [g1; g2; g3; g4; g5] ->
    Permutation (e ++ f) [g1; g2; g3; g4; g5] ->
    keys5 g1 g2 g3 g4 g5.
Proof.
  intros e f g1 g2 g3 g4 g5 He Hf Hlen Hle Hs Hp.
  set (s := [g1; g2; g3; g4; g5]) in *.
  destruct (sorted5_ord _ _ _ _ _ Hs) as (H12 & H23 & H34 & H45). unfold b64_abs_le in *.
  pose proof (sorted5_max _ _ _ _ _ _ Hs Hp) as Hmax.
  assert (St : forall M j, (j < 5)%nat -> (S j <= cnt M (e ++ f))%nat ->
                 Rabs (b2r (nth j s b64_two_unit)) < M)
    by (intros M j Hj Hc; exact (stat_lt M _ s j Hs Hp Hj Hc)).
  assert (Sg : forall M j, (j < 5)%nat -> (cnt M (e ++ f) <= j)%nat ->
                 M <= Rabs (b2r (nth j s b64_two_unit)))
    by (intros M j Hj Hc; exact (stat_ge M _ s j Hs Hp Hj Hc)).
  cbn [nth s] in St, Sg.
  unfold keys5.
  destruct e as [| a1 [| a2 [| a3 [| a4 [| a5 [| a6 e']]]]]];
    destruct f as [| b1 [| b2 [| b3 f']]];
    cbn [length] in Hlen, Hle; try lia; cbn [priest_chain app] in He, Hf, St, Sg, Hmax.
  - (* (3, 2) *)
    destruct He as (P12 & P23 & _). destruct Hf as (R12 & _).
    destruct (priest_pair_lt_ulp _ _ P12) as [A1 U2].
    destruct (priest_pair_lt_ulp _ _ P23) as [A2 U3].
    destruct (priest_pair_lt_ulp _ _ R12) as [C1 V2].
    pose proof (ulp_le_abs_b64 a1 A1). pose proof (ulp_le_abs_b64 a2 A2).
    pose proof (ulp_le_abs_b64 b1 C1).
    pose proof (Rabs_pos_lt _ A1). pose proof (Rabs_pos_lt _ A2). pose proof (Rabs_pos_lt _ C1).
    pose proof (ulp_mono a1 g5 (Hmax a1 ltac:(cbn; tauto))).
    pose proof (ulp_mono b1 g5 (Hmax b1 ltac:(cbn; tauto))).
    assert (K3 : Rabs (b2r g3) < ulp radix2 b64_fexp (b2r g5))
      by (apply (St _ 2%nat); [ lia | cnt_solve ]).
    assert (G4a2 : Rabs (b2r a2) <= Rabs (b2r g4)) by (apply (Sg _ 3%nat); [ lia | cnt_solve ]).
    pose proof (ulp_mono a2 g4 G4a2).
    assert (K2 : Rabs (b2r g2) < ulp radix2 b64_fexp (b2r g4)).
    { destruct (Rle_or_lt (Rabs (b2r a1)) (Rabs (b2r b1))) as [Hab | Hab].
      - assert (Hm : Rabs (b2r a1) <= Rabs (b2r g4)) by (apply (Sg _ 3%nat); [ lia | cnt_solve ]).
        pose proof (ulp_mono a1 g4 Hm). apply (St _ 1%nat); [ lia | cnt_solve ].
      - assert (Hm : Rabs (b2r b1) <= Rabs (b2r g4)) by (apply (Sg _ 3%nat); [ lia | cnt_solve ]).
        pose proof (ulp_mono b1 g4 Hm). apply (St _ 1%nat); [ lia | cnt_solve ]. }
    assert (K1 : 0 < Rabs (b2r g3) /\ Rabs (b2r g1) < ulp radix2 b64_fexp (b2r g3)).
    { destruct (Rle_or_lt (Rabs (b2r a2)) (Rabs (b2r b1))) as [Hab | Hab].
      - assert (Hm : Rabs (b2r a2) <= Rabs (b2r g3)) by (apply (Sg _ 2%nat); [ lia | cnt_solve ]).
        pose proof (ulp_mono a2 g3 Hm).
        split; [ lra | apply (St _ 0%nat); [ lia | cnt_solve ] ].
      - assert (Hm : Rabs (b2r b1) <= Rabs (b2r g3)) by (apply (Sg _ 2%nat); [ lia | cnt_solve ]).
        pose proof (ulp_mono b1 g3 Hm).
        split; [ lra | apply (St _ 0%nat); [ lia | cnt_solve ] ]. }
    destruct K1 as [P3 K1].
    repeat split; try assumption; intro Hz; rewrite Hz, Rabs_R0 in *; lra.
  - (* (4, 1) *)
    destruct He as (P12 & P23 & P34 & _).
    destruct (priest_pair_lt_ulp _ _ P12) as [A1 U2].
    destruct (priest_pair_lt_ulp _ _ P23) as [A2 U3].
    destruct (priest_pair_lt_ulp _ _ P34) as [A3 U4].
    pose proof (ulp_le_abs_b64 a1 A1). pose proof (ulp_le_abs_b64 a2 A2).
    pose proof (ulp_le_abs_b64 a3 A3).
    pose proof (Rabs_pos_lt _ A1). pose proof (Rabs_pos_lt _ A2). pose proof (Rabs_pos_lt _ A3).
    pose proof (ulp_mono a1 g5 (Hmax a1 ltac:(cbn; tauto))).
    assert (K3 : Rabs (b2r g3) < ulp radix2 b64_fexp (b2r g5))
      by (apply (St _ 2%nat); [ lia | cnt_solve ]).
    assert (G4a2 : Rabs (b2r a2) <= Rabs (b2r g4)) by (apply (Sg _ 3%nat); [ lia | cnt_solve ]).
    pose proof (ulp_mono a2 g4 G4a2).
    assert (K2 : Rabs (b2r g2) < ulp radix2 b64_fexp (b2r g4))
      by (apply (St _ 1%nat); [ lia | cnt_solve ]).
    assert (G3a3 : Rabs (b2r a3) <= Rabs (b2r g3)) by (apply (Sg _ 2%nat); [ lia | cnt_solve ]).
    pose proof (ulp_mono a3 g3 G3a3).
    assert (K1 : Rabs (b2r g1) < ulp radix2 b64_fexp (b2r g3))
      by (apply (St _ 0%nat); [ lia | cnt_solve ]).
    repeat split; try assumption; intro Hz; rewrite Hz, Rabs_R0 in *; lra.
  - (* (5, 0) *)
    destruct He as (P12 & P23 & P34 & P45 & _).
    destruct (priest_pair_lt_ulp _ _ P12) as [A1 U2].
    destruct (priest_pair_lt_ulp _ _ P23) as [A2 U3].
    destruct (priest_pair_lt_ulp _ _ P34) as [A3 U4].
    destruct (priest_pair_lt_ulp _ _ P45) as [A4 U5].
    pose proof (ulp_le_abs_b64 a1 A1). pose proof (ulp_le_abs_b64 a2 A2).
    pose proof (ulp_le_abs_b64 a3 A3). pose proof (ulp_le_abs_b64 a4 A4).
    pose proof (Rabs_pos_lt _ A1). pose proof (Rabs_pos_lt _ A2).
    pose proof (Rabs_pos_lt _ A3). pose proof (Rabs_pos_lt _ A4).
    pose proof (ulp_mono a1 g5 (Hmax a1 ltac:(cbn; tauto))).
    assert (K3 : Rabs (b2r g3) < ulp radix2 b64_fexp (b2r g5))
      by (apply (St _ 2%nat); [ lia | cnt_solve ]).
    assert (G4a2 : Rabs (b2r a2) <= Rabs (b2r g4)) by (apply (Sg _ 3%nat); [ lia | cnt_solve ]).
    pose proof (ulp_mono a2 g4 G4a2).
    assert (K2 : Rabs (b2r g2) < ulp radix2 b64_fexp (b2r g4))
      by (apply (St _ 1%nat); [ lia | cnt_solve ]).
    assert (G3a3 : Rabs (b2r a3) <= Rabs (b2r g3)) by (apply (Sg _ 2%nat); [ lia | cnt_solve ]).
    pose proof (ulp_mono a3 g3 G3a3).
    assert (K1 : Rabs (b2r g1) < ulp radix2 b64_fexp (b2r g3))
      by (apply (St _ 0%nat); [ lia | cnt_solve ]).
    repeat split; try assumption; intro Hz; rewrite Hz, Rabs_R0 in *; lra.
Qed.

Lemma priest_keys5 :
  forall e f g1 g2 g3 g4 g5,
    priest_chain e -> priest_chain f -> (length e + length f = 5)%nat ->
    sort_by_abs (e ++ f) = [g1; g2; g3; g4; g5] -> keys5 g1 g2 g3 g4 g5.
Proof.
  intros e f g1 g2 g3 g4 g5 He Hf Hlen Hs.
  pose proof (sort_by_abs_sorted (e ++ f)) as Hsort. rewrite Hs in Hsort.
  assert (Hp : Permutation (e ++ f) [g1; g2; g3; g4; g5])
    by (rewrite <- Hs; apply sort_by_abs_perm).
  destruct (Nat.le_ge_cases (length f) (length e)) as [Hle | Hge].
  - exact (keys5_of_perm e f _ _ _ _ _ He Hf Hlen Hle Hsort Hp).
  - apply (keys5_of_perm f e _ _ _ _ _ Hf He); [ lia | lia | exact Hsort | ].
    eapply Permutation_trans; [ apply Permutation_app_comm | exact Hp ].
Qed.

(* --------------------------------------------------------------------------
   The tie.  With |x| <= |g| and |y| <= 3 ulp(g), the error of RN(x + y)
   is at most ulp(g), and it equals ulp(g) only at the midpoint
   x + y = +-(B + ulp g), B = 2^(mag g), which rounds to +-B.
   -------------------------------------------------------------------------- *)

Lemma fexp_bounds :
  forall k, (b64_fexp k <= b64_fexp (k + 1) <= b64_fexp k + 1)%Z.
Proof. intro k. unfold SpecFloat.fexp. unfold prec. lia. Qed.

Lemma tie_analysis :
  forall (g : binary64) (x y : R),
    b2r g <> 0 -> Rabs x <= Rabs (b2r g) ->
    Rabs y <= 3 * ulp radix2 b64_fexp (b2r g) ->
    let M := mag radix2 (b2r g) in
    let c := cexp radix2 b64_fexp (b2r g) in
    let z := x + y in
    let r := round radix2 b64_fexp (BinarySingleNaN.round_mode mode_b64) z in
    Rabs (r - z) <= bpow radix2 c
    /\ (Rabs (r - z) = bpow radix2 c ->
          (2 <= M - c)%Z /\ b64_fexp (M + 1) = (c + 1)%Z
          /\ ((z = bpow radix2 M + bpow radix2 c /\ r = bpow radix2 M)
              \/ (z = - (bpow radix2 M + bpow radix2 c) /\ r = - bpow radix2 M))).
Proof.
  intros g x y Hg0 Hx Hy M c z r.
  rewrite ulp_neq_0 in Hy by exact Hg0. fold c in Hy.
  assert (Hc : c = b64_fexp M) by reflexivity.
  pose proof (mag_generic_gt radix2 b64_fexp (b2r g) Hg0 (Binary.generic_format_B2R prec emax g))
    as Hgt. fold c M in Hgt.
  assert (Hu : 0 < bpow radix2 c) by apply bpow_gt_0.
  assert (FB : generic_format radix2 b64_fexp (bpow radix2 M))
    by (apply generic_format_bpow, fexp_succ_le; rewrite <- Hc; exact Hgt).
  assert (Hg : Rabs (b2r g) <= bpow radix2 M - bpow radix2 c).
  { rewrite Hc, <- pred_bpow.
    exact (pred_ge_gt radix2 b64_fexp _ _
             (generic_format_abs _ _ _ (Binary.generic_format_B2R prec emax g)) FB
             (bpow_mag_gt radix2 (b2r g))). }
  assert (HcM : bpow radix2 c <= bpow radix2 (M - 1)) by (apply bpow_le; lia).
  assert (HM : bpow radix2 M = 2 * bpow radix2 (M - 1)).
  { replace (bpow radix2 M) with (bpow radix2 ((M - 1) + 1)) by (f_equal; ring).
    rewrite bpow_plus. change (bpow radix2 1) with 2. ring. }
  assert (Hz : Rabs z <= bpow radix2 M + 2 * bpow radix2 c)
    by (unfold z; pose proof (Rabs_triang x y); lra).
  change (BinarySingleNaN.round_mode mode_b64) with (Znearest (fun t => negb (Z.even t))) in r.
  destruct (Req_dec z 0) as [Hz0 | Hz0].
  { assert (Hr0 : r = 0) by (unfold r; rewrite Hz0; apply round_0, valid_rnd_N).
    rewrite Hr0, Hz0, Rminus_0_r, Rabs_R0. split; [ lra | intro H; lra ]. }
  (* the exponent of z is at most c + 1 *)
  set (ez := cexp radix2 b64_fexp z).
  assert (Hmz : (mag radix2 z <= M + 2)%Z).
  { apply mag_le_bpow; [ exact Hz0 | ].
    rewrite bpow_plus. change (bpow radix2 2) with 4. pose proof (bpow_gt_0 radix2 M). lra. }
  assert (Hmz1 : (c + 1 < M)%Z -> (mag radix2 z <= M + 1)%Z).
  { intro Hlt. apply mag_le_bpow; [ exact Hz0 | ].
    assert (H : bpow radix2 (c + 1) <= bpow radix2 (M - 1)) by (apply bpow_le; lia).
    rewrite bpow_plus in H. change (bpow radix2 1) with 2 in H.
    rewrite bpow_plus. change (bpow radix2 1) with 2. lra. }
  assert (Hez : (ez <= c + 1)%Z).
  { unfold ez, cexp.
    destruct (Z_lt_le_dec (c + 1) M) as [Hlt | Hge].
    - specialize (Hmz1 Hlt).
      rewrite Hc in *. unfold SpecFloat.fexp in *. unfold prec in *. lia.
    - rewrite Hc in *. unfold SpecFloat.fexp in *. unfold prec in *. lia. }
  pose proof (error_le_half_ulp radix2 b64_fexp (fun t => negb (Z.even t)) z) as Hhalf.
  fold r in Hhalf. rewrite ulp_neq_0 in Hhalf by exact Hz0. fold ez in Hhalf.
  assert (Hbez : bpow radix2 ez <= 2 * bpow radix2 c).
  { replace (2 * bpow radix2 c) with (bpow radix2 (c + 1))
      by (rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
    apply bpow_le, Hez. }
  split; [ lra | ].
  intro Htie.
  (* the tie: ez = c + 1, so |z| >= 2^M *)
  assert (Hez1 : ez = (c + 1)%Z).
  { destruct (Z.eq_dec ez (c + 1)) as [E | E]; [ exact E | exfalso ].
    assert (bpow radix2 ez <= bpow radix2 c) by (apply bpow_le; lia). lra. }
  assert (HmzM : (M < mag radix2 z)%Z).
  { destruct (Z_lt_le_dec M (mag radix2 z)) as [H | H]; [ exact H | exfalso ].
    assert (b64_fexp (mag radix2 z) <= b64_fexp M)%Z
      by (unfold SpecFloat.fexp; apply Z.max_le_compat_r; lia).
    unfold ez, cexp in Hez1. lia. }
  assert (HzB : bpow radix2 M <= Rabs z).
  { apply Rle_trans with (bpow radix2 (mag radix2 z - 1)); [ apply bpow_le; lia | ].
    apply bpow_mag_le, Hz0. }
  assert (Hk : (2 <= M - c)%Z /\ b64_fexp (M + 1) = (c + 1)%Z).
  { unfold ez, cexp in Hez1.
    destruct (Z_lt_le_dec (c + 1) M) as [Hlt | Hge]; [ specialize (Hmz1 Hlt) | ];
      rewrite Hc in *; unfold SpecFloat.fexp in *; unfold prec in *; lia. }
  split; [ apply Hk | split; [ apply Hk | ] ].
  (* z is a midpoint: z = (n + 1/2) 2^(c+1) *)
  assert (Hr : r = IZR (Znearest (fun t => negb (Z.even t)) (scaled_mantissa radix2 b64_fexp z))
                   * bpow radix2 ez) by reflexivity.
  set (m := Znearest (fun t => negb (Z.even t)) (scaled_mantissa radix2 b64_fexp z)) in Hr.
  assert (He2 : bpow radix2 ez = 2 * bpow radix2 c)
    by (rewrite Hez1, bpow_plus; change (bpow radix2 1) with 2; ring).
  set (k := (M - c - 1)%Z).
  set (N := Zpower radix2 k).
  assert (HBk : bpow radix2 M = IZR N * bpow radix2 ez).
  { unfold N. rewrite IZR_Zpower by (unfold k; lia). rewrite <- bpow_plus. f_equal. unfold k. lia. }
  assert (HNe : Z.even N = true).
  { unfold N. replace k with (1 + (k - 1))%Z by ring.
    rewrite Zpower_plus by (unfold k; lia). cbn [Zpower Z.pow_pos Pos.iter radix_val radix2].
    rewrite Z.even_mul. reflexivity. }
  assert (Hk1 : (1 <= k)%Z) by (unfold k; lia).
  assert (He0 : 0 < bpow radix2 ez) by apply bpow_gt_0.
  (* |r - z| = 2^c = 2^ez / 2: z = (m -+ 1/2) 2^ez *)
  assert (Hmid : exists n : Z, z = (IZR n + / 2) * bpow radix2 ez).
  { destruct (Rcase_abs (r - z)) as [Ha | Ha];
      [ rewrite Rabs_left in Htie by exact Ha | rewrite Rabs_right in Htie by exact Ha ].
    - exists m. lra.
    - exists (m - 1)%Z. rewrite minus_IZR. lra. }
  destruct Hmid as [n Hn].
  assert (Hzu : Rabs z <= (IZR N + 1) * bpow radix2 ez) by lra.
  assert (Hzl : IZR N * bpow radix2 ez <= Rabs z) by lra.
  rewrite Hn, Rabs_mult, (Rabs_pos_eq (bpow radix2 ez)) in Hzu, Hzl by lra.
  apply Rmult_le_reg_r in Hzu; [ | exact He0 ].
  rewrite Rmult_comm in Hzl. rewrite (Rmult_comm (Rabs _)) in Hzl.
  apply Rmult_le_reg_l in Hzl; [ | exact He0 ].
  destruct (Rle_or_lt 0 (IZR n + / 2)) as [Hpos | Hneg].
  - (* n = N = 2^k : z = B + u, rounds down to the even B *)
    rewrite Rabs_pos_eq in Hzu, Hzl by exact Hpos.
    assert (Hn1 : n = N).
    { apply Z.le_antisymm.
      - apply Z.lt_succ_r, lt_IZR. rewrite succ_IZR. lra.
      - apply Z.lt_pred_le, lt_IZR. rewrite <- Z.sub_1_r, minus_IZR. lra. }
    left. split.
    + rewrite Hn, Hn1, HBk, He2. field.
    + unfold r. change (Znearest (fun t => negb (Z.even t))) with (BinarySingleNaN.round_mode mode_b64).
      rewrite (round_NE_mid z n); fold ez; [ | rewrite <- Hn; reflexivity ].
      rewrite Hn1, HNe, HBk. reflexivity.
  - (* n = -N - 1 : z = -(B + u), rounds up to the even -B *)
    rewrite Rabs_left in Hzu, Hzl by exact Hneg.
    assert (Hn1 : n = (- N - 1)%Z).
    { apply Z.le_antisymm.
      - apply Z.lt_succ_r, lt_IZR. rewrite succ_IZR, minus_IZR, opp_IZR. lra.
      - apply Z.lt_pred_le, lt_IZR. rewrite <- Z.sub_1_r, !minus_IZR, opp_IZR. lra. }
    right. split.
    + rewrite Hn, Hn1, minus_IZR, opp_IZR, HBk, He2. field.
    + unfold r. change (Znearest (fun t => negb (Z.even t))) with (BinarySingleNaN.round_mode mode_b64).
      rewrite (round_NE_mid z n); fold ez; [ | rewrite <- Hn; reflexivity ].
      assert (Hodd : Z.even n = false).
      { rewrite Hn1, Z.even_sub, Z.even_opp, HNe. reflexivity. }
      rewrite Hodd, Hn1. replace (- N - 1 + 1)%Z with (- N)%Z by ring.
      rewrite opp_IZR, HBk. ring.
Qed.

(* --------------------------------------------------------------------------
   Shapes with one anti pair or one twin, over a layered tail.
   -------------------------------------------------------------------------- *)

Lemma b64_is_zero_false : forall x, b64_fin x -> b2r x <> 0 -> b64_is_zero x = false.
Proof.
  intros x Hx Hx0. destruct (b64_is_zero x) eqn:Hz; [ | reflexivity ].
  exfalso. apply Hx0, b64_is_zero_R, Hz.
Qed.

Lemma b64_is_zero_true : forall x, b64_fin x -> b2r x = 0 -> b64_is_zero x = true.
Proof.
  intros x Hx Hx0. destruct (b64_is_zero x) eqn:Hz; [ reflexivity | ].
  exfalso. destruct (b64_nz_of_not_zero x Hx Hz) as [_ H]. exact (H Hx0).
Qed.

Lemma keys_prefix :
  forall b t, (forall y, In y t -> Rabs (b2r y) < block_key b) -> strict_desc t ->
    keys_decreasing (b :: map CSingle t).
Proof.
  intros b t Hlt Hd. split; [ | apply keys_singles, Hd ].
  destruct t as [| y t']; [ exact I | cbn [map block_key]; apply Hlt; left; reflexivity ].
Qed.

Lemma below_in : forall c t y, Forall (below c) t -> In y t -> Rabs (b2r y) < bpow radix2 c.
Proof. intros c t y H Hy. rewrite Forall_forall in H. exact (H y Hy). Qed.

(* q, then the anti pair (a, b) with b = -a, then a layered tail below |a|. *)
Lemma shape_anti :
  forall (q a b : binary64) (t : list binary64) (c : Z),
    b64_fin q -> b64_fin a -> b64_fin b -> Forall b64_fin t ->
    b2r b = - b2r a -> bpow radix2 c <= Rabs (b2r a) -> Rabs (b2r a) < Rabs (b2r q) ->
    pow2_multiple c (b2r q) -> Forall (below c) t -> layered t ->
    exists bs, drop_zeros (q :: a :: b :: t) = flat_map cblock_expand bs /\ carry_shape bs.
Proof.
  intros q a b t c Fq Fa Fb Ft Hba Hca Haq Mq Bt Lt.
  pose proof (bpow_gt_0 radix2 c) as Hc0.
  assert (Ha0 : b2r a <> 0) by (intro H; rewrite H, Rabs_R0 in Hca; lra).
  assert (Hq0 : b2r q <> 0) by (intro H; rewrite H, Rabs_R0 in Haq; pose proof (Rabs_pos (b2r a)); lra).
  assert (Hb0 : b2r b <> 0) by (rewrite Hba; intro H; apply Ha0; lra).
  assert (Eb : b = b64_neg a).
  { apply b64_eq_of_R; [ exact Fb | apply b64_neg_fin, Fa | rewrite b64_neg_R; exact Hba | exact Hb0 ]. }
  set (t0 := drop_zeros t).
  pose proof (drop_zeros_nz t Ft) as Nt. fold t0 in Nt.
  assert (Bt0 : Forall (below c) t0) by (apply Forall_filter_sub, Bt).
  assert (Lt0 : layered t0) by (apply layered_filter, Lt).
  destruct (layered_desc t0 Lt0 Nt) as [Dt0 Ct0].
  exists (CSingle q :: CAnti a :: map CSingle t0).
  split.
  { unfold drop_zeros. cbn [filter].
    rewrite (b64_is_zero_false q Fq Hq0), (b64_is_zero_false a Fa Ha0), (b64_is_zero_false b Fb Hb0).
    cbn [negb flat_map cblock_expand app]. rewrite Eb, expand_singles. reflexivity. }
  split; [ | split ].
  - repeat constructor; try assumption. apply Forall_map, Nt.
  - split; [ cbn [block_key]; lra | ].
    apply keys_prefix; [ | exact Dt0 ].
    intros y Hy. cbn [block_key]. pose proof (below_in _ _ _ Bt0 Hy). lra.
  - cbn [flat_map cblock_reduce app]. rewrite reduce_singles.
    assert (Nq : b64_nz q) by (split; assumption).
    apply (layered_desc (q :: t0)); [ | constructor; assumption ].
    split; [ exists c; split; assumption | exact Lt0 ].
Qed.

(* the twin (q, b) with b = q, then a layered tail below |q|. *)
Lemma shape_twin :
  forall (q b : binary64) (t : list binary64) (c : Z),
    b64_fin q -> b64_fin b -> Forall b64_fin t ->
    b2r b = b2r q -> bpow radix2 c <= Rabs (b2r q) ->
    2 * Rabs (b2r q) < bpow radix2 emax ->
    pow2_multiple c (b2r q) -> Forall (below c) t -> layered t ->
    exists bs, drop_zeros (q :: b :: t) = flat_map cblock_expand bs /\ carry_shape bs.
Proof.
  intros q b t c Fq Fb Ft Hbq Hcq Hov [nq Hnq] Bt Lt.
  pose proof (bpow_gt_0 radix2 c) as Hc0.
  assert (Hq0 : b2r q <> 0) by (intro H; rewrite H, Rabs_R0 in Hcq; lra).
  assert (Eb : b = q) by (apply b64_eq_of_R; [ exact Fb | exact Fq | exact Hbq | rewrite Hbq; exact Hq0 ]).
  destruct (double_exact q Fq Hov) as [Hd Fd].
  set (t0 := drop_zeros t).
  pose proof (drop_zeros_nz t Ft) as Nt. fold t0 in Nt.
  assert (Bt0 : Forall (below c) t0) by (apply Forall_filter_sub, Bt).
  assert (Lt0 : layered t0) by (apply layered_filter, Lt).
  destruct (layered_desc t0 Lt0 Nt) as [Dt0 Ct0].
  exists (CTwin q :: map CSingle t0).
  split.
  { unfold drop_zeros. cbn [filter]. subst b.
    rewrite (b64_is_zero_false q Fq Hq0). cbn [negb flat_map cblock_expand app].
    rewrite expand_singles. reflexivity. }
  split; [ | split ].
  - constructor; [ split; [ split; assumption | exact Hov ] | apply Forall_map, Nt ].
  - apply keys_prefix; [ | exact Dt0 ].
    intros y Hy. cbn [block_key]. pose proof (below_in _ _ _ Bt0 Hy).
    pose proof (Rabs_pos (b2r q)). lra.
  - cbn [flat_map cblock_reduce app]. rewrite reduce_singles.
    assert (Nd : b64_nz (b64_mult q b64_two_unit)) by (split; [ exact Fd | rewrite Hd; lra ]).
    apply (layered_desc (b64_mult q b64_two_unit :: t0)); [ | constructor; assumption ].
    split; [ | exact Lt0 ].
    exists c. split; [ exists (2 * nq)%Z; rewrite Hd, Hnq, mult_IZR; ring | exact Bt0 ].
Qed.

Lemma drop_zeros_cons_nz :
  forall x l, b64_is_zero x = false -> drop_zeros (x :: l) = x :: drop_zeros l.
Proof. intros x l Hz. unfold drop_zeros. cbn [filter]. rewrite Hz. reflexivity. Qed.

Lemma drop_zeros_skip2 :
  forall a b l, b64_is_zero b = true -> drop_zeros (a :: b :: l) = drop_zeros (a :: l).
Proof.
  intros a b l Hz. unfold drop_zeros. cbn [filter]. rewrite Hz. cbn [negb].
  destruct (negb (b64_is_zero a)); reflexivity.
Qed.

Lemma pow2_multiple_pm :
  forall c x, Rabs x = bpow radix2 c -> pow2_multiple c x.
Proof.
  intros c x Hx. destruct (Rcase_abs x) as [Hn | Hp].
  - rewrite Rabs_left in Hx by exact Hn. exists (-1)%Z. cbn. lra.
  - rewrite Rabs_right in Hx by exact Hp. exists 1%Z. cbn. lra.
Qed.

(* The tie, finished: h4 = +-2^c and one of three outcomes for (Q5, h5). *)
Lemma tie_finish :
  forall (Q5 h5 h4 h3 h2 : binary64) (c : Z),
    b64_fin Q5 -> b64_fin h5 -> b64_fin h4 -> b64_fin h3 -> b64_fin h2 ->
    Forall (below c) [h3; h2] -> layered [h3; h2] ->
    2 * bpow radix2 c < bpow radix2 emax ->
    Rabs (b2r h4) = bpow radix2 c ->
    (   (b2r h5 = - b2r h4 /\ pow2_multiple c (b2r Q5) /\ bpow radix2 c < Rabs (b2r Q5))
     \/ (b2r h5 = 0 /\ b2r Q5 = b2r h4)
     \/ (b2r h5 = 0 /\ pow2_multiple (c + 1) (b2r Q5) /\ b2r Q5 <> 0)) ->
    exists bs, drop_zeros [Q5; h5; h4; h3; h2] = flat_map cblock_expand bs /\ carry_shape bs.
Proof.
  intros Q5 h5 h4 h3 h2 c FQ Fh5 Fh4 Fh3 Fh2 Bt Lt Hov Hh4 Hcase.
  pose proof (bpow_gt_0 radix2 c) as Hc0.
  assert (Ft : Forall b64_fin [h3; h2]) by (repeat constructor; assumption).
  assert (Hh40 : b2r h4 <> 0) by (intro H; rewrite H, Rabs_R0 in Hh4; lra).
  destruct Hcase as [(Ha & Mq & Hq) | [(Hz & Hq) | (Hz & Mq & Hq0)]].
  - apply (shape_anti Q5 h5 h4 [h3; h2] c); try assumption.
    + lra.
    + rewrite Ha, Rabs_Ropp. lra.
    + rewrite Ha, Rabs_Ropp. lra.
  - rewrite drop_zeros_skip2 by (apply b64_is_zero_true; assumption).
    apply (shape_twin Q5 h4 [h3; h2] c); try assumption.
    + lra.
    + rewrite Hq. lra.
    + rewrite Hq. lra.
    + apply pow2_multiple_pm. rewrite Hq. exact Hh4.
  - destruct (singles_shape_of_layered [Q5; h5; h4; h3; h2]) as [bs [E [S _]]].
    + repeat constructor; assumption.
    + rewrite drop_zeros_skip2 by (apply b64_is_zero_true; assumption).
      rewrite (drop_zeros_cons_nz Q5) by (apply b64_is_zero_false; assumption).
      rewrite (drop_zeros_cons_nz h4) by (apply b64_is_zero_false; assumption).
      assert (Bt0 : Forall (below c) (drop_zeros [h3; h2])) by (apply Forall_filter_sub, Bt).
      assert (H2c : bpow radix2 c < bpow radix2 (c + 1)) by (apply bpow_lt; lia).
      split; [ exists (c + 1)%Z; split; [ exact Mq | ] | ].
      { constructor; [ unfold below; lra | ].
        eapply Forall_impl; [ | exact Bt0 ]. unfold below. intros y Hy. lra. }
      split; [ exists c; split; [ apply pow2_multiple_pm, Hh4 | exact Bt0 ] | ].
      apply layered_filter, Lt.
    + exists bs. split; assumption.
Qed.

Lemma fmt_scaled :
  forall (j e k : Z),
    Rabs (IZR j * bpow radix2 e) < bpow radix2 k -> (b64_fexp k <= e)%Z ->
    generic_format radix2 b64_fexp (IZR j * bpow radix2 e).
Proof.
  intros j e k Hlt Hk.
  change (IZR j * bpow radix2 e) with (F2R (Float radix2 j e)).
  apply generic_format_F2R. intro Hj.
  apply Z.le_trans with (b64_fexp k); [ | exact Hk ].
  assert (H0 : IZR j * bpow radix2 e <> 0).
  { apply Rmult_integral_contrapositive_currified; [ apply not_0_IZR, Hj | ].
    apply Rgt_not_eq, bpow_gt_0. }
  exact (cexp_le_bpow radix2 b64_fexp (IZR j * bpow radix2 e) k H0 Hlt).
Qed.

(* --------------------------------------------------------------------------
   Four chained TwoSums, given the keys.  No Priest hypothesis here.
   -------------------------------------------------------------------------- *)

Definition fes5 (g1 g2 g3 g4 g5 : binary64) : list binary64 :=
  let '(hs, q) := b64_grow_expansion_aux g1 [g2; g3; g4; g5] in q :: rev hs.

Lemma fes5_shape_of_keys :
  forall g1 g2 g3 g4 g5 : binary64,
    b64_fin g1 -> b64_fin g2 -> b64_fin g3 -> b64_fin g4 -> b64_fin g5 ->
    cascade_safe g1 [g2; g3; g4; g5] ->
    b64_abs_le g3 g4 -> b64_abs_le g4 g5 ->
    Rabs (b2r g5) <= bpow radix2 (emax - 5) ->
    keys5 g1 g2 g3 g4 g5 ->
    exists bs, drop_zeros (fes5 g1 g2 g3 g4 g5) = flat_map cblock_expand bs
               /\ carry_shape bs.
Proof.
  intros g1 g2 g3 g4 g5 F1 F2 F3 F4 F5 Hsafe H34 H45 Hov5 (Hg30 & Hg40 & Hg50 & K1 & K2 & K3).
  cbn [cascade_safe] in Hsafe. destruct Hsafe as [S12 [S3 [S4 [S5 _]]]].
  change (fst (b64_TwoSum g2 g1)) with (b64_plus g2 g1) in S3, S4, S5.
  unfold fes5. cbn [b64_grow_expansion_aux].
  (* first TwoSum: (Q2, h2) = TwoSum(g2, g1) *)
  pose proof S12 as (A1 & A2 & A3 & A4 & A5 & A6).
  pose proof (b64_TwoSum_correct g2 g1 A1 A2 A3 A4 A5 A6) as Hex2.
  pose proof (b64_TwoSum_nonoverlap g2 g1 A1 A2 A3 A4 A5 A6) as Hno2.
  destruct (b64_plus_correct g2 g1 A1) as [RQ2 FQ2].
  destruct (b64_plus_correct _ _ A6) as [_ Fh2].
  destruct (b64_TwoSum g2 g1) as [Q2 h2] eqn:E2.
  cbv iota beta in Hex2, Hno2.
  unfold b64_TwoSum in E2. injection E2 as EQ2 Eh2.
  rewrite EQ2 in RQ2, FQ2, S3, S4, S5. rewrite Eh2 in Fh2.
  change (fst (b64_TwoSum g3 Q2)) with (b64_plus g3 Q2) in S4, S5.
  (* second TwoSum: (Q3, h3) = TwoSum(g3, Q2) *)
  pose proof S3 as (B1 & B2 & B3 & B4 & B5 & B6).
  pose proof (b64_TwoSum_correct g3 Q2 B1 B2 B3 B4 B5 B6) as Hex3.
  pose proof (b64_TwoSum_nonoverlap g3 Q2 B1 B2 B3 B4 B5 B6) as Hno3.
  destruct (b64_plus_correct g3 Q2 B1) as [RQ3 FQ3].
  destruct (b64_plus_correct _ _ B6) as [_ Fh3].
  destruct (b64_TwoSum g3 Q2) as [Q3 h3] eqn:E3.
  cbv iota beta in Hex3, Hno3.
  unfold b64_TwoSum in E3. injection E3 as EQ3 Eh3.
  rewrite EQ3 in RQ3, FQ3, S4, S5. rewrite Eh3 in Fh3.
  change (fst (b64_TwoSum g4 Q3)) with (b64_plus g4 Q3) in S5.
  (* third TwoSum: (Q4, h4) = TwoSum(g4, Q3) *)
  pose proof S4 as (C1 & C2 & C3 & C4 & C5 & C6).
  pose proof (b64_TwoSum_correct g4 Q3 C1 C2 C3 C4 C5 C6) as Hex4.
  pose proof (b64_TwoSum_nonoverlap g4 Q3 C1 C2 C3 C4 C5 C6) as Hno4.
  destruct (b64_plus_correct g4 Q3 C1) as [RQ4 FQ4].
  destruct (b64_plus_correct _ _ C6) as [_ Fh4].
  destruct (b64_TwoSum g4 Q3) as [Q4 h4] eqn:E4.
  cbv iota beta in Hex4, Hno4.
  unfold b64_TwoSum in E4. injection E4 as EQ4 Eh4.
  rewrite EQ4 in RQ4, FQ4, S5. rewrite Eh4 in Fh4.
  (* fourth TwoSum: (Q5, h5) = TwoSum(g5, Q4) *)
  pose proof S5 as (D1 & D2 & D3 & D4 & D5 & D6).
  pose proof (b64_TwoSum_correct g5 Q4 D1 D2 D3 D4 D5 D6) as Hex5.
  pose proof (b64_TwoSum_nonoverlap g5 Q4 D1 D2 D3 D4 D5 D6) as Hno5.
  destruct (b64_plus_correct g5 Q4 D1) as [RQ5 FQ5].
  destruct (b64_plus_correct _ _ D6) as [_ Fh5].
  destruct (b64_TwoSum g5 Q4) as [Q5 h5] eqn:E5.
  cbv iota beta in Hex5, Hno5.
  unfold b64_TwoSum in E5. injection E5 as EQ5 Eh5.
  rewrite EQ5 in RQ5, FQ5. rewrite Eh5 in Fh5.
  cbn [rev app].
  unfold strict_succ_b64 in Hno2, Hno3, Hno4.
  (* ulp facts *)
  pose proof (ulp_mono _ _ H34) as U34. pose proof (ulp_mono _ _ H45) as U45.
  assert (HQ2 : Rabs (b2r Q2) < 2 * ulp radix2 b64_fexp (b2r g4)).
  { rewrite RQ2. apply rn_sum_lt_two_ulp; [ exact Hg40 | exact K2 | lra ]. }
  set (c5 := cexp radix2 b64_fexp (b2r g5)).
  assert (Hu5 : ulp radix2 b64_fexp (b2r g5) = bpow radix2 c5) by (apply ulp_neq_0, Hg50).
  assert (Hu4 : ulp radix2 b64_fexp (b2r g4) = bpow radix2 (cexp radix2 b64_fexp (b2r g4)))
    by (apply ulp_neq_0, Hg40).
  assert (Hu3 : ulp radix2 b64_fexp (b2r g3) = bpow radix2 (cexp radix2 b64_fexp (b2r g3)))
    by (apply ulp_neq_0, Hg30).
  assert (Hc45 : (cexp radix2 b64_fexp (b2r g4) <= c5)%Z)
    by (apply (le_bpow radix2); rewrite <- Hu4, <- Hu5; exact U45).
  (* layers 2 and 1, as on rung 3 *)
  set (c2 := Z.min (cexp radix2 b64_fexp (b2r g3)) (cexp radix2 b64_fexp (b2r Q2))).
  assert (Mg3 : pow2_multiple c2 (b2r g3))
    by (apply (pow2_multiple_le _ _ _ (Z.le_min_l _ _)), b64_pow2_multiple_cexp).
  assert (MQ2 : pow2_multiple c2 (b2r Q2))
    by (apply (pow2_multiple_le _ _ _ (Z.le_min_r _ _)), b64_pow2_multiple_cexp).
  assert (MQ3 : pow2_multiple c2 (b2r Q3))
    by (rewrite RQ3; apply round_pow2_multiple, pow2_multiple_plus; assumption).
  assert (Mh3 : pow2_multiple c2 (b2r h3)).
  { replace (b2r h3) with ((b2r g3 + b2r Q2) - b2r Q3) by lra.
    apply pow2_multiple_minus; [ apply pow2_multiple_plus | ]; assumption. }
  assert (Hh2g1 : Rabs (b2r h2) <= Rabs (b2r g1)).
  { replace (b2r h2)
      with (- (round radix2 b64_fexp (BinarySingleNaN.round_mode mode_b64) (b2r g2 + b2r g1)
               - (b2r g2 + b2r g1)))
      by (rewrite <- RQ2; lra).
    rewrite Rabs_Ropp. apply round_N_err_le_operand, Binary.generic_format_B2R. }
  assert (Hh2Q2 := half_ulp_below Q2 h2 Hno2).
  assert (Hh2c2 : Rabs (b2r h2) < bpow radix2 c2).
  { unfold c2. destruct (Z.min_spec (cexp radix2 b64_fexp (b2r g3))
                                    (cexp radix2 b64_fexp (b2r Q2))) as [[_ Hm] | [_ Hm]];
      rewrite Hm; lra. }
  set (L3 := Z.max c2 (cexp radix2 b64_fexp (b2r Q3))).
  assert (MQ3L : pow2_multiple L3 (b2r Q3)).
  { unfold L3. destruct (Z.max_spec c2 (cexp radix2 b64_fexp (b2r Q3))) as [[_ Hm] | [_ Hm]];
      rewrite Hm; [ apply b64_pow2_multiple_cexp | exact MQ3 ]. }
  set (c1 := Z.min (cexp radix2 b64_fexp (b2r g4)) L3).
  assert (Mg4 : pow2_multiple c1 (b2r g4))
    by (apply (pow2_multiple_le _ _ _ (Z.le_min_l _ _)), b64_pow2_multiple_cexp).
  assert (MQ3c1 : pow2_multiple c1 (b2r Q3))
    by (apply (pow2_multiple_le _ _ _ (Z.le_min_r _ _)), MQ3L).
  assert (MQ4 : pow2_multiple c1 (b2r Q4))
    by (rewrite RQ4; apply round_pow2_multiple, pow2_multiple_plus; assumption).
  assert (Mh4 : pow2_multiple c1 (b2r h4)).
  { replace (b2r h4) with ((b2r g4 + b2r Q3) - b2r Q4) by lra.
    apply pow2_multiple_minus; [ apply pow2_multiple_plus | ]; assumption. }
  assert (Hh3g4 : Rabs (b2r h3) < bpow radix2 (cexp radix2 b64_fexp (b2r g4))).
  { replace (b2r h3)
      with (- (round radix2 b64_fexp (BinarySingleNaN.round_mode mode_b64) (b2r g3 + b2r Q2)
               - (b2r g3 + b2r Q2)))
      by (rewrite <- RQ3; lra).
    rewrite Rabs_Ropp, <- Hu4.
    apply rn_err_lt_ulp_top; [ exact Hg40 | exact H34 | exact HQ2 ]. }
  assert (Hh3Q3 := half_ulp_below Q3 h3 Hno3).
  assert (Hh3c1 : below c1 h3).
  { unfold below, c1, L3.
    destruct (Z.min_spec (cexp radix2 b64_fexp (b2r g4))
                         (Z.max c2 (cexp radix2 b64_fexp (b2r Q3)))) as [[_ Hm] | [_ Hm]];
      rewrite Hm; [ exact Hh3g4 | ].
    apply Rlt_le_trans with (1 := Hh3Q3). apply bpow_le, Z.le_max_r. }
  assert (Hh2c1 : below c1 h2).
  { unfold below, c1, L3.
    destruct (Z.min_spec (cexp radix2 b64_fexp (b2r g4))
                         (Z.max c2 (cexp radix2 b64_fexp (b2r Q3)))) as [[_ Hm] | [_ Hm]];
      rewrite Hm; [ rewrite <- Hu4; lra | ].
    apply Rlt_le_trans with (1 := Hh2c2). apply bpow_le, Z.le_max_l. }
  assert (Lt : layered [h3; h2]).
  { split; [ exists c2; split; [ exact Mh3 | constructor; [ exact Hh2c2 | constructor ] ] | ].
    split; [ exists (cexp radix2 b64_fexp (b2r h2));
             split; [ apply b64_pow2_multiple_cexp | constructor ] | exact I ]. }
  assert (Hc15 : (c1 <= c5)%Z) by (unfold c1; lia).
  assert (Bt5 : Forall (below c5) [h3; h2]).
  { assert (bpow radix2 c1 <= bpow radix2 c5) by (apply bpow_le, Hc15).
    unfold below in *. repeat constructor; lra. }
  (* the fourth TwoSum's input error h4: at most ulp(g5), equal only at the tie *)
  assert (F3u : generic_format radix2 b64_fexp (IZR 3 * bpow radix2 c5)).
  { apply (fmt_scaled 3 c5 (c5 + 2)).
    - rewrite Rabs_mult, Rabs_pos_eq by lra. rewrite (Rabs_pos_eq (bpow _ _)) by (left; apply bpow_gt_0).
      rewrite bpow_plus. change (bpow radix2 2) with 4. pose proof (bpow_gt_0 radix2 c5). lra.
    - unfold c5, cexp, SpecFloat.fexp. unfold prec. lia. }
  assert (HQ3 : Rabs (b2r Q3) <= 3 * ulp radix2 b64_fexp (b2r g5)).
  { rewrite RQ3, Hu5. change 3 with (IZR 3).
    apply (abs_round_le_generic radix2 b64_fexp (BinarySingleNaN.round_mode mode_b64) _ _ F3u).
    pose proof (Rabs_triang (b2r g3) (b2r Q2)). rewrite <- Hu5. cbn [IZR IPR IPR_2]. lra. }
  pose proof (tie_analysis g5 (b2r g4) (b2r Q3) Hg50 H45 HQ3) as Htie.
  cbv zeta in Htie. rewrite <- RQ4 in Htie. fold c5 in Htie.
  destruct Htie as [Hbound Htie].
  assert (Hh4e : Rabs (b2r Q4 - (b2r g4 + b2r Q3)) = Rabs (b2r h4)).
  { replace (b2r Q4 - (b2r g4 + b2r Q3)) with (- b2r h4) by lra. apply Rabs_Ropp. }
  rewrite Hh4e in Hbound, Htie.
  pose proof (bpow_gt_0 radix2 c5) as Hc5p.
  destruct (Req_dec (Rabs (b2r h4)) (bpow radix2 c5)) as [Ht | Hnt].
  2: {
    (* NO TIE: the output is layered, all singles *)
    set (L4 := Z.max c1 (cexp radix2 b64_fexp (b2r Q4))).
    assert (MQ4L : pow2_multiple L4 (b2r Q4)).
    { unfold L4. destruct (Z.max_spec c1 (cexp radix2 b64_fexp (b2r Q4))) as [[_ Hm] | [_ Hm]];
        rewrite Hm; [ apply b64_pow2_multiple_cexp | exact MQ4 ]. }
    set (c0 := Z.min c5 L4).
    assert (Mg5 : pow2_multiple c0 (b2r g5))
      by (apply (pow2_multiple_le _ _ _ (Z.le_min_l _ _)), b64_pow2_multiple_cexp).
    assert (MQ4c0 : pow2_multiple c0 (b2r Q4))
      by (apply (pow2_multiple_le _ _ _ (Z.le_min_r _ _)), MQ4L).
    assert (MQ5 : pow2_multiple c0 (b2r Q5))
      by (rewrite RQ5; apply round_pow2_multiple, pow2_multiple_plus; assumption).
    assert (Mh5 : pow2_multiple c0 (b2r h5)).
    { replace (b2r h5) with ((b2r g5 + b2r Q4) - b2r Q5) by lra.
      apply pow2_multiple_minus; [ apply pow2_multiple_plus | ]; assumption. }
    assert (Hh4Q4 := half_ulp_below Q4 h4 Hno4).
    assert (Hh4c0 : below c0 h4).
    { unfold below, c0, L4.
      destruct (Z.min_spec c5 (Z.max c1 (cexp radix2 b64_fexp (b2r Q4)))) as [[_ Hm] | [_ Hm]];
        rewrite Hm; [ lra | ].
      apply Rlt_le_trans with (1 := Hh4Q4). apply bpow_le, Z.le_max_r. }
    assert (Hc10 : (c1 <= c0)%Z) by (unfold c0, L4; lia).
    assert (Hb10 : bpow radix2 c1 <= bpow radix2 c0) by (apply bpow_le, Hc10).
    destruct (singles_shape_of_layered [Q5; h5; h4; h3; h2]) as [bs [E [Sh _]]].
    - repeat constructor; assumption.
    - apply (head_pair_layered Q5 h5 [h4; h3; h2] c0 FQ5 Fh5 Hno5 MQ5 Mh5).
      + unfold below in *. repeat constructor; lra.
      + split; [ exists c1; split; [ exact Mh4 | repeat constructor; assumption ] | exact Lt ].
    - exists bs. split; assumption. }
  (* THE TIE: Q4 = +-2^M, h4 = +-2^c5 *)
  destruct (Htie Ht) as (HMc & HfM & Hz).
  set (M := mag radix2 (b2r g5)) in *.
  set (B := bpow radix2 M) in *.
  set (u := bpow radix2 c5) in *.
  assert (HB0 : 0 < B) by apply bpow_gt_0.
  assert (HcM : c5 = b64_fexp M) by reflexivity.
  set (K := Zpower radix2 (M - c5)).
  assert (HBK : B = IZR K * u).
  { unfold B, u, K. rewrite IZR_Zpower by lia. rewrite <- bpow_plus. f_equal. lia. }
  assert (HKe : Z.even K = true).
  { unfold K. replace (M - c5)%Z with (1 + (M - c5 - 1))%Z by ring.
    rewrite Zpower_plus by lia. cbn [Zpower Z.pow_pos Pos.iter radix_val radix2].
    rewrite Z.even_mul. reflexivity. }
  assert (HK4 : (4 <= K)%Z).
  { unfold K. replace (M - c5)%Z with (2 + (M - c5 - 2))%Z by ring.
    rewrite Zpower_plus by lia. cbn [Zpower Z.pow_pos Pos.iter radix_val radix2].
    assert (0 < Zpower radix2 (M - c5 - 2))%Z by (apply Zpower_gt_0; lia). lia. }
  assert (HK4R : 4 <= IZR K) by (apply IZR_le; exact HK4).
  assert (FB : generic_format radix2 b64_fexp B).
  { apply generic_format_bpow. unfold SpecFloat.fexp in *. unfold prec in *. lia. }
  assert (Hg5B : Rabs (b2r g5) <= B - u).
  { unfold B, u. rewrite HcM, <- pred_bpow.
    exact (pred_ge_gt radix2 b64_fexp _ _
             (generic_format_abs _ _ _ (Binary.generic_format_B2R prec emax g5)) FB
             (bpow_mag_gt radix2 (b2r g5))). }
  assert (Hg4l : B - 2 * u <= Rabs (b2r g4)).
  { rewrite Hu5 in HQ3. fold u in HQ3. destruct Hz as [[Hz _] | [Hz _]].
    - pose proof (Rabs_triang_inv (b2r g4 + b2r Q3) (b2r Q3)).
      replace (b2r g4 + b2r Q3 - b2r Q3) with (b2r g4) in H by ring.
      rewrite Hz, Rabs_pos_eq in H by lra. unfold b64_abs_le in H45. lra.
    - pose proof (Rabs_triang_inv (b2r g4 + b2r Q3) (b2r Q3)).
      replace (b2r g4 + b2r Q3 - b2r Q3) with (b2r g4) in H by ring.
      rewrite Hz, Rabs_Ropp, Rabs_pos_eq in H by lra. lra. }
  unfold b64_abs_le in H45.
  destruct (b64_pow2_multiple_cexp g5) as [m Hm]. fold c5 u in Hm.
  assert (Hmb : (K - 2 <= Z.abs m <= K - 1)%Z).
  { rewrite Hm, Rabs_mult, (Rabs_pos_eq u) in Hg5B, H45 by lra.
    rewrite <- abs_IZR in Hg5B, H45. rewrite HBK in Hg5B, Hg4l.
    split.
    - apply le_IZR. rewrite minus_IZR.
      apply Rmult_le_reg_r with u; [ lra | ]. lra.
    - apply le_IZR. rewrite minus_IZR.
      apply Rmult_le_reg_r with u; [ lra | ]. lra. }
  assert (Hm4 : m = (K - 1)%Z \/ m = (K - 2)%Z \/ m = (- (K - 1))%Z \/ m = (- (K - 2))%Z) by lia.
  (* the exponent of the fifth sum near 2B *)
  assert (Hce : forall v, B <= Rabs v < 2 * B -> cexp radix2 b64_fexp v = (c5 + 1)%Z).
  { intros v [Hl Hh]. unfold cexp.
    assert (Hmv : mag radix2 v = (M + 1)%Z :> Z).
    { apply mag_unique. rewrite Z.add_simpl_r. split; [ exact Hl | ].
      rewrite bpow_plus. change (bpow radix2 1) with 2. unfold B in Hh. lra. }
    rewrite Hmv. exact HfM. }
  assert (Hu2 : 2 * u = bpow radix2 (c5 + 1))
    by (unfold u; rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
  assert (Hfmt : forall j : Z, Rabs (IZR j * (2 * u)) < 2 * B ->
                   generic_format radix2 b64_fexp (IZR j * (2 * u))).
  { intros j Hj. rewrite Hu2. apply (fmt_scaled j (c5 + 1) (M + 1)).
    - rewrite <- Hu2. rewrite bpow_plus. change (bpow radix2 1) with 2. unfold B in Hj. lra.
    - lia. }
  assert (Hfu : generic_format radix2 b64_fexp u).
  { apply generic_format_bpow. unfold c5, cexp, SpecFloat.fexp. unfold prec. lia. }
  assert (Hov2 : 2 * u < bpow radix2 emax).
  { assert (u <= Rabs (b2r g5)) by (rewrite <- Hu5; apply ulp_le_abs_b64, Hg50).
    assert (bpow radix2 (emax - 5) < bpow radix2 emax) by (apply bpow_lt; lia).
    assert (8 * bpow radix2 (emax - 5) <= bpow radix2 emax).
    { replace emax with ((emax - 5) + 5)%Z at 2 by ring. rewrite bpow_plus.
      change (bpow radix2 5) with 32. pose proof (bpow_gt_0 radix2 (emax - 5)). lra. }
    lra. }
  apply (tie_finish Q5 h5 h4 h3 h2 c5 FQ5 Fh5 Fh4 Fh3 Fh2 Bt5 Lt Hov2 Ht). fold u.
  assert (HK : IZR K * u = B) by (symmetry; exact HBK).
  assert (Hrnd : forall v, generic_format radix2 b64_fexp v ->
                   round radix2 b64_fexp (BinarySingleNaN.round_mode mode_b64) v = v)
    by (intros v Hv; apply round_generic; [ apply valid_rnd_N | exact Hv ]).
  destruct Hz as [[Hz HQ4] | [Hz HQ4]].
  - (* Q4 = B, h4 = u *)
    assert (Hh4u : b2r h4 = u) by lra.
    destruct Hm4 as [Em | [Em | [Em | Em]]]; rewrite Em in Hm.
    + (* g5 = B - u: Q5 = 2B (midpoint, to even), h5 = -u : anti pair *)
      assert (Hv : b2r g5 + b2r Q4 = (IZR (K - 1) + / 2) * bpow radix2 (c5 + 1)).
      { rewrite Hm, HQ4, <- Hu2, minus_IZR. rewrite <- HK. field. }
      assert (HcV : cexp radix2 b64_fexp (b2r g5 + b2r Q4) = (c5 + 1)%Z).
      { apply Hce. rewrite Hm, HQ4, minus_IZR, <- HK.
        rewrite Rabs_pos_eq; [ | nra ]. split; nra. }
      assert (HQ5 : b2r Q5 = 2 * B).
      { rewrite RQ5, round_NE_mid with (n := (K - 1)%Z); [ | rewrite HcV; exact Hv ].
        rewrite HcV, Z.even_sub, HKe. cbn. replace (K - 1 + 1)%Z with K by ring.
        rewrite <- Hu2, <- HK. ring. }
      left. split; [ | split ].
      * rewrite Hh4u. rewrite Hm, HQ4, HQ5, minus_IZR, <- HK in Hex5. lra.
      * rewrite HQ5, <- HK. exists (2 * K)%Z. rewrite mult_IZR. unfold u. ring.
      * rewrite HQ5, Rabs_pos_eq by (unfold B; pose proof (bpow_gt_0 radix2 M); lra).
        rewrite <- HK. assert (4 <= IZR K) by (apply IZR_le; lia). nra.
    + (* g5 = B - 2u: Q5 = 2B - 2u exactly, h5 = 0 *)
      assert (Hv : b2r g5 + b2r Q4 = IZR (K - 1) * (2 * u)).
      { rewrite Hm, HQ4, !minus_IZR, <- HK. ring. }
      assert (HQ5 : b2r Q5 = IZR (K - 1) * (2 * u)).
      { rewrite RQ5, Hv. apply Hrnd, Hfmt. rewrite minus_IZR, Rabs_pos_eq.
        - rewrite <- HK. lra.
        - assert (4 <= IZR K) by (apply IZR_le; lia). nra. }
      right; right. split; [ | split ].
      * rewrite Hm, HQ4, HQ5, !minus_IZR, <- HK in Hex5. lra.
      * rewrite HQ5, Hu2. exists (K - 1)%Z. reflexivity.
      * rewrite HQ5. assert (4 <= IZR K) by (apply IZR_le; lia). rewrite minus_IZR. nra.
    + (* g5 = -(B - u): Q5 = u exactly, h5 = 0 : twin with h4 *)
      assert (Hv : b2r g5 + b2r Q4 = u) by (rewrite Hm, HQ4, opp_IZR, minus_IZR, <- HK; ring).
      assert (HQ5 : b2r Q5 = u) by (rewrite RQ5, Hv; apply Hrnd, Hfu).
      right; left. split; [ lra | lra ].
    + (* g5 = -(B - 2u): Q5 = 2u exactly, h5 = 0 *)
      assert (Hv : b2r g5 + b2r Q4 = IZR 1 * (2 * u))
        by (rewrite Hm, HQ4, opp_IZR, minus_IZR, <- HK; cbn; ring).
      assert (HQ5 : b2r Q5 = IZR 1 * (2 * u)).
      { rewrite RQ5, Hv. apply Hrnd, Hfmt. rewrite Rabs_pos_eq by (cbn; lra).
        assert (4 <= IZR K) by (apply IZR_le; lia). rewrite <- HK. cbn. nra. }
      right; right. split; [ | split ].
      * cbn in HQ5. lra.
      * rewrite HQ5, Hu2. exists 1%Z. reflexivity.
      * rewrite HQ5. cbn. lra.
  - (* Q4 = -B, h4 = -u : the mirror image *)
    assert (Hh4u : b2r h4 = - u) by lra.
    destruct Hm4 as [Em | [Em | [Em | Em]]]; rewrite Em in Hm.
    + (* g5 = B - u: Q5 = -u exactly : twin with h4 *)
      assert (Hv : b2r g5 + b2r Q4 = - u) by (rewrite Hm, HQ4, minus_IZR, <- HK; ring).
      assert (HQ5 : b2r Q5 = - u)
        by (rewrite RQ5, Hv; apply Hrnd, generic_format_opp, Hfu).
      right; left. split; [ lra | lra ].
    + (* g5 = B - 2u: Q5 = -2u exactly *)
      assert (Hv : b2r g5 + b2r Q4 = IZR (-1) * (2 * u))
        by (rewrite Hm, HQ4, minus_IZR, <- HK; cbn; ring).
      assert (HQ5 : b2r Q5 = IZR (-1) * (2 * u)).
      { rewrite RQ5, Hv. apply Hrnd, Hfmt. cbn. rewrite Rabs_left by lra.
        assert (4 <= IZR K) by (apply IZR_le; lia). rewrite <- HK. nra. }
      right; right. split; [ | split ].
      * cbn in HQ5. lra.
      * rewrite HQ5, Hu2. exists (-1)%Z. reflexivity.
      * rewrite HQ5. cbn. lra.
    + (* g5 = -(B - u): Q5 = -2B (midpoint, to even), h5 = u : anti pair *)
      assert (Hv : b2r g5 + b2r Q4 = (IZR (- K) + / 2) * bpow radix2 (c5 + 1)).
      { rewrite Hm, HQ4, <- Hu2, opp_IZR, minus_IZR, opp_IZR. rewrite <- HK. field. }
      assert (HcV : cexp radix2 b64_fexp (b2r g5 + b2r Q4) = (c5 + 1)%Z).
      { apply Hce. rewrite Hm, HQ4, opp_IZR, minus_IZR, <- HK.
        rewrite Rabs_left; [ | nra ]. split; nra. }
      assert (HQ5 : b2r Q5 = - (2 * B)).
      { rewrite RQ5, round_NE_mid with (n := (- K)%Z); [ | rewrite HcV; exact Hv ].
        rewrite HcV, Z.even_opp, HKe. rewrite opp_IZR, <- Hu2, <- HK. ring. }
      left. split; [ | split ].
      * rewrite Hh4u. rewrite Hm, HQ4, HQ5, opp_IZR, minus_IZR, <- HK in Hex5. lra.
      * rewrite HQ5, <- HK. exists (- (2 * K))%Z. rewrite opp_IZR, mult_IZR. unfold u. ring.
      * rewrite HQ5, Rabs_Ropp, Rabs_pos_eq by (unfold B; pose proof (bpow_gt_0 radix2 M); lra).
        rewrite <- HK. assert (4 <= IZR K) by (apply IZR_le; lia). nra.
    + (* g5 = -(B - 2u): Q5 = -(2B - 2u) exactly *)
      assert (Hv : b2r g5 + b2r Q4 = IZR (- (K - 1)) * (2 * u)).
      { rewrite Hm, HQ4, !opp_IZR, !minus_IZR, <- HK. ring. }
      assert (HQ5 : b2r Q5 = IZR (- (K - 1)) * (2 * u)).
      { rewrite RQ5, Hv. apply Hrnd, Hfmt. rewrite opp_IZR, minus_IZR, Rabs_left.
        - rewrite <- HK. lra.
        - assert (4 <= IZR K) by (apply IZR_le; lia). nra. }
      right; right. split; [ | split ].
      * rewrite Hm, HQ4, HQ5, !opp_IZR, !minus_IZR, <- HK in Hex5. lra.
      * rewrite HQ5, Hu2. exists (- (K - 1))%Z. reflexivity.
      * rewrite HQ5. assert (4 <= IZR K) by (apply IZR_le; lia). rewrite opp_IZR, minus_IZR. nra.
Qed.

(* --------------------------------------------------------------------------
   RUNG 4.
   -------------------------------------------------------------------------- *)

Lemma fes_rung4_shape :
  forall e f : list binary64,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
    (length e + length f = 5)%nat ->
    exists bs, drop_zeros (fast_expansion_sum e f) = flat_map cblock_expand bs
               /\ carry_shape bs.
Proof.
  intros e f He Hf Hef Hff Hov Hlen.
  pose proof (fes_cascade_safe e f Hef Hff Hov) as Hsafe.
  assert (Hfin : Forall b64_fin (sort_by_abs (e ++ f)))
    by (apply sort_by_abs_Forall, Forall_app; split; assumption).
  assert (Hl5 : length (sort_by_abs (e ++ f)) = 5%nat)
    by (rewrite sort_by_abs_length, length_app; exact Hlen).
  assert (Hbig : Forall (fun x => Rabs (b2r x) <= bpow radix2 (emax - 5)) (sort_by_abs (e ++ f))).
  { pose proof (abs_le_abs_sum (sort_by_abs (e ++ f))) as Hs.
    rewrite abs_sum_sort, abs_sum_app in Hs.
    eapply Forall_impl; [ | exact Hs ]. cbn beta. intros x Hx. lra. }
  pose proof (sort_by_abs_sorted (e ++ f)) as Hsort.
  destruct (sort_by_abs (e ++ f)) as [| g1 [| g2 [| g3 [| g4 [| g5 [| g6 rest]]]]]] eqn:Hs;
    cbn [length] in Hl5; try lia.
  pose proof (priest_keys5 e f g1 g2 g3 g4 g5 He Hf Hlen Hs) as Hkeys.
  destruct (sorted5_ord _ _ _ _ _ Hsort) as (_ & _ & H34 & H45).
  inversion Hfin as [| ? ? F1 Hfin2]; subst.
  inversion Hfin2 as [| ? ? F2 Hfin3]; subst.
  inversion Hfin3 as [| ? ? F3 Hfin4]; subst.
  inversion Hfin4 as [| ? ? F4 Hfin5]; subst.
  inversion Hfin5 as [| ? ? F5 _]; subst.
  assert (Hov5 : Rabs (b2r g5) <= bpow radix2 (emax - 5)).
  { rewrite Forall_forall in Hbig. apply Hbig. cbn. tauto. }
  unfold fast_expansion_sum. rewrite Hs.
  exact (fes5_shape_of_keys g1 g2 g3 g4 g5 F1 F2 F3 F4 F5 Hsafe H34 H45 Hov5 Hkeys).
Qed.

(* Bridge part (a) at total length 5. *)
Theorem fes_carry_pattern_rung4 : fes_priest_carry_pattern_n 5.
Proof.
  intros e f He Hf Hef Hff Hov Hlen.
  destruct (fes_rung4_shape e f He Hf Hef Hff Hov Hlen) as [bs [Hl [Hok [Hdec _]]]].
  exists bs. split; [ exact Hl | split; assumption ].
Qed.

(* Bridge part (b) at total length 5, for EVERY decomposition: the pattern
   decomposition is unique (`pattern_unique`). *)
Theorem fes_reduction_nonoverlap_rung4 : fes_priest_reduction_nonoverlap_n 5.
Proof.
  intros e f He Hf Hef Hff Hov Hlen bs Hl Hp.
  destruct (fes_rung4_shape e f He Hf Hef Hff Hov Hlen) as [bs0 [Hl0 Hs0]].
  exact (reduction_of_any_pattern _ bs0 bs Hl0 Hs0 Hl Hp).
Qed.

(* The target on rung 4, and on all of rungs 1-4 together. *)
Corollary carry_clean_priest_target_rung4 :
  forall e f : list binary64,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
    (length e + length f <= 5)%nat ->
    nonoverlapping_chain (carry_clean (fast_expansion_sum e f)).
Proof.
  intros e f He Hf Hef Hff Hov Hlen.
  destruct (Nat.eq_dec (length e + length f) 5) as [H5 | H5].
  - destruct (fes_rung4_shape e f He Hf Hef Hff Hov H5) as [bs [Hl Hs]].
    apply (carry_clean_nonoverlap_of_shape _ bs Hl Hs).
  - apply carry_clean_priest_target_rung3; [ assumption .. | lia ].
Qed.

Print Assumptions pattern_unique.
Print Assumptions stat_lt.
Print Assumptions stat_ge.
Print Assumptions round_NE_mid.
Print Assumptions priest_keys5.
Print Assumptions tie_analysis.
Print Assumptions fes5_shape_of_keys.
Print Assumptions fes_carry_pattern_rung4.
Print Assumptions fes_reduction_nonoverlap_rung4.
Print Assumptions carry_clean_priest_target_rung4.
