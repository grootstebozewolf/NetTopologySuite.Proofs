(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_CarryCleanRung2
   ----------------------------------------------------------------------------
   Rung 2 of the carry_clean bridge (B64_CarryClean.v): THREE components in
   total, i.e. two chained TwoSums.  The first rung where the Priest
   hypothesis is needed -- with arbitrary inputs the output can overlap
   (e.g. f = [y; -y]) -- and the first that is not a single TwoSum.

   THE ARGUMENT.  Sort the three components by magnitude, g1 <= g2 <= g3,
   and let (Q2, h2) = TwoSum(g2, g1), (Q3, h3) = TwoSum(g3, Q2); the output
   is [Q3; h3; h2].
     1. Key (Priest + pigeonhole): two of the three come from one Priest
        expansion, and the smaller of those is below one ulp of the larger;
        so |g1| < ulp(g3).
     2. |h2| <= |g1| (round-to-nearest is at least as close as g2 itself) and
        |h2| <= ulp(Q2)/2; so |h2| < 2^c, c = min(cexp g3, cexp Q2).
     3. g3 and Q2 are multiples of 2^c, hence so are Q3 = RN(g3 + Q2) and
        h3 = g3 + Q2 - Q3.
     4. So [Q3; h3; h2] (zeros dropped) is nonoverlapping with strictly
        decreasing magnitudes: Q3/h3 by the TwoSum half-ulp bound, h3/h2 (or
        Q3/h2 when h3 = 0) by 2 and 3.  No twins or anti pairs occur.

   PROVED HERE, at total length 3:
     fes_carry_pattern_rung2          part (a): fes_priest_carry_pattern_n 3
     fes_reduction_nonoverlap_rung2   part (b): fes_priest_reduction_nonoverlap_n 3,
                                      for EVERY decomposition -- the output is
                                      strictly decreasing, so every
                                      decomposition is all singles
                                      (`desc_all_singles`)
     carry_clean_priest_target_rung2  the target for every total <= 3
   The Priest hypothesis enters only through `key_lt_ulp`; everything after
   it is `fes3_shape_of_key`, which takes |g1| < ulp(g3) as a hypothesis.
   Overflow margin 2^(emax-5) (the base case alone needs 2^(emax-4)).
   Nothing here covers four or more components.

   NTS / JTS COUNTERPART.  None in-library (JTS/NTS use `CGAlgorithmsDD`,
   double-double); this lane serves the corpus's exact orientation.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; reviewed on PR #986 (2026-10-31).
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lia Lra List Permutation.
From Flocq Require Import IEEE754.Binary Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
     B64_Pff_bridge B64_Expansion B64_FastExpansionSum
     B64_FastExpansionSum_Shewchuk B64_Overlap_Hierarchy B64_CarryCleanAlgo
     B64_CarryCleanCore.

Import ListNotations.
Local Open Scope R_scope.

(* --------------------------------------------------------------------------
   Sorting (`sort_by_abs_perm`, `sort_by_abs_sorted`: B64_FastExpansionSum_Shewchuk).
   -------------------------------------------------------------------------- *)

Definition b64_abs_le (x y : binary64) : Prop :=
  Rabs (Binary.B2R prec emax x) <= Rabs (Binary.B2R prec emax y).

(* For a sorted three-element list, the first is the minimum and the last
   the maximum of every element of the original list. *)
Lemma sorted3_bounds :
  forall l g1 g2 g3, sort_by_abs l = [g1; g2; g3] ->
    forall y, In y l -> b64_abs_le g1 y /\ b64_abs_le y g3.
Proof.
  intros l g1 g2 g3 Hs y Hy.
  pose proof (sort_by_abs_sorted l) as Hsort. rewrite Hs in Hsort.
  assert (Hin : In y [g1; g2; g3]).
  { rewrite <- Hs. eapply Permutation_in; [ apply sort_by_abs_perm | exact Hy ]. }
  inversion Hsort as [ | | ? ? ? H12 Hs23 ]; subst.
  inversion Hs23 as [ | | ? ? ? H23 _ ]; subst. unfold b64_abs_le.
  destruct Hin as [<- | [<- | [<- | []]]]; split; lra.
Qed.

(* --------------------------------------------------------------------------
   A Priest pair: the smaller component is below one ulp of the larger.
   -------------------------------------------------------------------------- *)

Lemma priest_pair_lt_ulp :
  forall a b : binary64,
    priest_nonoverlapping_b64 a b ->
    Binary.B2R prec emax a <> 0
    /\ Rabs (Binary.B2R prec emax b)
       < ulp radix2 (SpecFloat.fexp prec emax) (Binary.B2R prec emax a).
Proof.
  intros a b [mx [my [kx [ky [Hx [Hy [[Hxlo Hxhi] [[Hylo Hyhi] Hgap]]]]]]]].
  assert (Hpk : forall k, 0 < bpow radix2 k) by (intro; apply bpow_gt_0).
  assert (Habsx : Rabs (Binary.B2R prec emax a) = Rabs (IZR mx) * bpow radix2 kx).
  { rewrite Hx, Rabs_mult, (Rabs_pos_eq (bpow radix2 kx)) by (left; apply Hpk). ring. }
  assert (Ha0 : Binary.B2R prec emax a <> 0).
  { intro H0. rewrite H0, Rabs_R0 in Habsx.
    pose proof (Hpk (prec - 1)%Z). pose proof (Hpk kx). nra. }
  split; [ exact Ha0 | ].
  rewrite ulp_neq_0 by exact Ha0.
  (* |b| < 2^(ky + prec) <= 2^kx <= 2^(cexp a) *)
  apply Rlt_le_trans with (bpow radix2 kx).
  - rewrite Hy, Rabs_mult, (Rabs_pos_eq (bpow radix2 ky)) by (left; apply Hpk).
    apply Rlt_le_trans with (bpow radix2 prec * bpow radix2 ky).
    + apply Rmult_lt_compat_r; [ apply Hpk | exact Hyhi ].
    + rewrite <- bpow_plus. apply bpow_le. lia.
  - apply bpow_le. unfold cexp.
    assert (Hmag : mag radix2 (Binary.B2R prec emax a) = (kx + prec)%Z :> Z).
    { apply mag_unique. rewrite Habsx. split.
      - replace (kx + prec - 1)%Z with ((prec - 1) + kx)%Z by ring.
        rewrite bpow_plus. apply Rmult_le_compat_r; [ left; apply Hpk | exact Hxlo ].
      - replace (kx + prec)%Z with (prec + kx)%Z by ring.
        rewrite bpow_plus. apply Rmult_lt_compat_r; [ apply Hpk | exact Hxhi ]. }
    rewrite Hmag. unfold SpecFloat.fexp. lia.
Qed.

(* --------------------------------------------------------------------------
   Multiples of 2^c.
   -------------------------------------------------------------------------- *)

Definition pow2_multiple (c : Z) (x : R) : Prop := exists n : Z, x = IZR n * bpow radix2 c.

Lemma pow2_multiple_le : forall c c' x, (c <= c')%Z -> pow2_multiple c' x -> pow2_multiple c x.
Proof.
  intros c c' x Hc [n Hn]. exists (n * Zpower radix2 (c' - c))%Z.
  rewrite Hn. replace c' with (c + (c' - c))%Z at 1 by ring.
  apply IZR_scaled_shift. lia.
Qed.

Lemma pow2_multiple_plus : forall c x y, pow2_multiple c x -> pow2_multiple c y -> pow2_multiple c (x + y).
Proof. intros c x y [n Hn] [m Hm]. exists (n + m)%Z. rewrite Hn, Hm, plus_IZR. ring. Qed.

Lemma pow2_multiple_minus : forall c x y, pow2_multiple c x -> pow2_multiple c y -> pow2_multiple c (x - y).
Proof. intros c x y [n Hn] [m Hm]. exists (n - m)%Z. rewrite Hn, Hm, minus_IZR. ring. Qed.

(* A binary64 value is a multiple of 2^(cexp of itself). *)
Lemma b64_pow2_multiple_cexp :
  forall x : binary64,
    pow2_multiple (cexp radix2 (SpecFloat.fexp prec emax) (Binary.B2R prec emax x))
            (Binary.B2R prec emax x).
Proof.
  intro x. pose proof (Binary.generic_format_B2R prec emax x) as Hf.
  unfold generic_format, F2R in Hf. cbn [Fnum Fexp] in Hf.
  eexists. exact Hf.
Qed.

(* Rounding a multiple of 2^c gives a multiple of 2^c. *)
Lemma round_pow2_multiple :
  forall c z, pow2_multiple c z -> pow2_multiple c (round radix2 (SpecFloat.fexp prec emax)
                                (BinarySingleNaN.round_mode mode_b64) z).
Proof.
  intros c z [m Hm].
  destruct (Z_le_gt_dec (cexp radix2 (SpecFloat.fexp prec emax) z) c) as [Hle | Hgt].
  - (* z is representable: rounding is the identity *)
    assert (Hfz : generic_format radix2 (SpecFloat.fexp prec emax) z).
    { rewrite Hm. change (IZR m * bpow radix2 c) with (F2R (Float radix2 m c)).
      apply generic_format_F2R. intros _.
      replace (F2R (Float radix2 m c)) with z by (rewrite Hm; reflexivity). exact Hle. }
    rewrite (round_generic radix2 (SpecFloat.fexp prec emax)
               (BinarySingleNaN.round_mode mode_b64) z Hfz).
    exists m. exact Hm.
  - (* the rounded value is a multiple of 2^(cexp z), and cexp z > c *)
    apply (pow2_multiple_le c (cexp radix2 (SpecFloat.fexp prec emax) z)); [ lia | ].
    unfold round, F2R. cbn [Fnum Fexp]. eexists. reflexivity.
Qed.

(* --------------------------------------------------------------------------
   Singles and uniqueness.  A list with strictly decreasing magnitudes has no
   adjacent equal magnitudes, so EVERY block decomposition of it is all
   singles and its reduction is the list itself.
   -------------------------------------------------------------------------- *)

Definition is_single (b : cblock) : Prop :=
  match b with CSingle _ => True | _ => False end.

Fixpoint strict_desc (l : list binary64) : Prop :=
  match l with
  | a :: ((b :: _) as rest) =>
      Rabs (Binary.B2R prec emax b) < Rabs (Binary.B2R prec emax a) /\ strict_desc rest
  | _ => True
  end.

Lemma strict_desc_tail : forall a l, strict_desc (a :: l) -> strict_desc l.
Proof. intros a [| b l] H; [ exact I | exact (proj2 H) ]. Qed.

Lemma singles_reduce :
  forall bs, Forall is_single bs -> flat_map cblock_reduce bs = flat_map cblock_expand bs.
Proof.
  induction bs as [| b bs IH]; intro H; [ reflexivity | ].
  inversion H as [| ? ? Hb Hbs]; subst.
  destruct b as [u | x | x]; cbn [is_single] in Hb; try contradiction.
  cbn [flat_map cblock_reduce cblock_expand app]. rewrite (IH Hbs). reflexivity.
Qed.

Lemma singles_strict_desc :
  forall bs, Forall is_single bs -> keys_decreasing bs ->
    strict_desc (flat_map cblock_expand bs).
Proof.
  induction bs as [| b bs IH]; intros H Hk; [ exact I | ].
  inversion H as [| ? ? Hb Hbs]; subst. destruct Hk as [Hk1 Hk2].
  destruct b as [u | x | x]; cbn [is_single] in Hb; try contradiction.
  cbn [flat_map cblock_expand app].
  specialize (IH Hbs Hk2).
  destruct bs as [| b' bs']; [ exact I | ].
  inversion Hbs as [| ? ? Hb' _]; subst.
  destruct b' as [v | y | y]; cbn [is_single] in Hb'; try contradiction.
  cbn [flat_map cblock_expand app block_key] in *.
  split; [ exact Hk1 | exact IH ].
Qed.

(* Uniqueness: on a strictly decreasing list, every decomposition reduces
   to the list itself. *)
Lemma desc_all_singles :
  forall bs, strict_desc (flat_map cblock_expand bs) ->
    flat_map cblock_reduce bs = flat_map cblock_expand bs.
Proof.
  induction bs as [| b bs IH]; intro Hd; [ reflexivity | ].
  destruct b as [u | x | x]; cbn [flat_map cblock_reduce cblock_expand app] in *.
  - rewrite (IH (strict_desc_tail _ _ Hd)). reflexivity.
  - destruct Hd as [Hlt _]. lra.
  - destruct Hd as [Hlt _]. rewrite b64_neg_R, Rabs_Ropp in Hlt. lra.
Qed.

(* --------------------------------------------------------------------------
   Three outputs, all singles.  If |b| <= ulp(a)/2, a and b are multiples of
   2^c and |d| < 2^c, then [a; b; d] (zeros dropped) has the shape.
   -------------------------------------------------------------------------- *)

Lemma b64_fin_zero_or_nz :
  forall x, b64_fin x ->
    (b64_is_zero x = true /\ Binary.B2R prec emax x = 0)
    \/ (b64_is_zero x = false /\ b64_nz x).
Proof.
  intros x Hx. destruct (b64_is_zero x) eqn:Hz.
  - left. split; [ reflexivity | apply b64_is_zero_R, Hz ].
  - right. split; [ reflexivity | apply b64_nz_of_not_zero; assumption ].
Qed.


Lemma three_singles_shape :
  forall (a b d : binary64) (c : Z),
    b64_fin a -> b64_fin b -> b64_fin d ->
    strict_succ_b64 a b ->
    pow2_multiple c (Binary.B2R prec emax a) ->
    pow2_multiple c (Binary.B2R prec emax b) ->
    Rabs (Binary.B2R prec emax d) < bpow radix2 c ->
    exists bs, drop_zeros [a; b; d] = flat_map cblock_expand bs /\ carry_shape bs
               /\ Forall is_single bs.
Proof.
  intros a b d c Ha Hb Hd Hab [na Hna] [nb Hnb] Hdc.
  unfold strict_succ_b64 in Hab.
  destruct (b64_fin_zero_or_nz a Ha) as [[Hza Ha0] | [Hza Hanz]];
  destruct (b64_fin_zero_or_nz b Hb) as [[Hzb Hb0] | [Hzb Hbnz]];
  destruct (b64_fin_zero_or_nz d Hd) as [[Hzd Hd0] | [Hzd Hdnz]];
  unfold drop_zeros; cbn [filter]; rewrite ?Hza, ?Hzb, ?Hzd; cbn [negb].
  (* a = 0 forces b = 0 *)
  all: try (exfalso; destruct Hbnz as [_ Hb0']; apply Hb0';
            apply binary64_below_emin_is_zero; rewrite Ha0 in Hab;
            change (ulp radix2 (SpecFloat.fexp prec emax) 0) with (b64_ulp 0) in Hab;
            rewrite b64_ulp_FLT_0 in Hab;
            pose proof (bpow_gt_0 radix2 (3 - emax - prec)); lra).
  (* the shapes that remain *)
  - exists []. split; [ reflexivity | split; [ repeat split; constructor | constructor ] ].
  - exists [CSingle d]. split; [ reflexivity | split; [ | repeat (apply Forall_cons; [ exact I | ]); apply Forall_nil ] ].
    split; [ apply Forall_cons; [ exact Hdnz | apply Forall_nil ] | repeat split ].
  - exists [CSingle a]. split; [ reflexivity | split; [ | repeat (apply Forall_cons; [ exact I | ]); apply Forall_nil ] ].
    split; [ apply Forall_cons; [ exact Hanz | apply Forall_nil ] | repeat split ].
  - (* [a; d] *)
    exists [CSingle a; CSingle d]. split; [ reflexivity | split; [ | repeat (apply Forall_cons; [ exact I | ]); apply Forall_nil ] ].
    destruct Hanz as [Haf Han0].
    assert (Hge : bpow radix2 c <= Rabs (Binary.B2R prec emax a))
      by (apply (scaled_nonzero_ge _ na c Hna Han0)).
    split; [ apply Forall_cons; [ split; assumption
                                | apply Forall_cons; [ exact Hdnz | apply Forall_nil ] ] | ].
    split; [ cbn [keys_decreasing block_key]; split; [ lra | exact (conj I I) ] | ].
    cbn [flat_map cblock_reduce app nonoverlapping_chain]. split; [ | exact I ].
    apply (nonov_scaled _ _ na c Hna Hdc).
  - (* [a; b] *)
    exists [CSingle a; CSingle b]. split; [ reflexivity | split; [ | repeat (apply Forall_cons; [ exact I | ]); apply Forall_nil ] ].
    destruct Hanz as [Haf Han0].
    pose proof (b64_ulp_le_abs _ Han0 (Binary.generic_format_B2R prec emax a)).
    pose proof (Rabs_pos_lt _ Han0).
    split; [ apply Forall_cons; [ split; assumption
                                | apply Forall_cons; [ exact Hbnz | apply Forall_nil ] ] | ].
    split; [ cbn [keys_decreasing block_key]; split; [ lra | exact (conj I I) ] | ].
    cbn [flat_map cblock_reduce app nonoverlapping_chain]. split; [ | exact I ].
    apply strict_succ_b64_nonoverlapping. exact Hab.
  - (* [a; b; d] *)
    exists [CSingle a; CSingle b; CSingle d]. split; [ reflexivity | split; [ | repeat (apply Forall_cons; [ exact I | ]); apply Forall_nil ] ].
    destruct Hanz as [Haf Han0]. pose proof Hbnz as [Hbf Hbn0].
    pose proof (b64_ulp_le_abs _ Han0 (Binary.generic_format_B2R prec emax a)).
    pose proof (Rabs_pos_lt _ Han0).
    assert (Hge : bpow radix2 c <= Rabs (Binary.B2R prec emax b))
      by (apply (scaled_nonzero_ge _ nb c Hnb Hbn0)).
    split; [ apply Forall_cons; [ split; assumption | ];
             apply Forall_cons; [ exact Hbnz | ];
             apply Forall_cons; [ exact Hdnz | apply Forall_nil ] | ].
    split; [ cbn [keys_decreasing block_key]; repeat split; lra | ].
    cbn [flat_map cblock_reduce app nonoverlapping_chain].
    split; [ apply strict_succ_b64_nonoverlapping; exact Hab | ].
    split; [ apply (nonov_scaled _ _ nb c Hnb Hdc) | exact I ].
Qed.

(* --------------------------------------------------------------------------
   Three components: two of them share a Priest expansion.
   -------------------------------------------------------------------------- *)

Lemma priest_pair_of_three :
  forall e f : list binary64,
    priest_chain e -> priest_chain f -> (length e + length f = 3)%nat ->
    exists a b, In a (e ++ f) /\ In b (e ++ f) /\ priest_nonoverlapping_b64 a b.
Proof.
  intros e f He Hf Hlen.
  destruct e as [| a [| b [| c e']]]; destruct f as [| x [| y [| z f']]];
    cbn [length] in Hlen; try lia; cbn [priest_chain] in He, Hf.
  - exists x, y. split; [ cbn; auto | split; [ cbn; auto | apply Hf ] ].
  - exists x, y. split; [ cbn; auto | split; [ cbn; auto | apply Hf ] ].
  - exists a, b. split; [ cbn; auto | split; [ cbn; auto | apply He ] ].
  - exists a, b. split; [ cbn; auto | split; [ cbn; auto | apply He ] ].
Qed.

(* The smallest of the three is below one ulp of the largest. *)
Lemma key_lt_ulp :
  forall e f g1 g2 g3,
    priest_chain e -> priest_chain f -> (length e + length f = 3)%nat ->
    sort_by_abs (e ++ f) = [g1; g2; g3] ->
    Binary.B2R prec emax g3 <> 0
    /\ Rabs (Binary.B2R prec emax g1)
       < ulp radix2 (SpecFloat.fexp prec emax) (Binary.B2R prec emax g3).
Proof.
  intros e f g1 g2 g3 He Hf Hlen Hs.
  destruct (priest_pair_of_three e f He Hf Hlen) as [a [b [Ha [Hb Hab]]]].
  destruct (priest_pair_lt_ulp a b Hab) as [Ha0 Hbu].
  destruct (sorted3_bounds _ g1 g2 g3 Hs b Hb) as [H1b _].
  destruct (sorted3_bounds _ g1 g2 g3 Hs a Ha) as [_ Ha3].
  unfold b64_abs_le in *.
  assert (Hg30 : Binary.B2R prec emax g3 <> 0).
  { intro H0. rewrite H0, Rabs_R0 in Ha3. pose proof (Rabs_pos_lt _ Ha0). lra. }
  split; [ exact Hg30 | ].
  pose proof (ulp_le radix2 (SpecFloat.fexp prec emax)
                (Binary.B2R prec emax a) (Binary.B2R prec emax g3) Ha3) as Hul.
  lra.
Qed.

(* --------------------------------------------------------------------------
   Two chained TwoSums, given the key bound.  No Priest hypothesis here: it
   enters only through |g1| < ulp(g3).
   -------------------------------------------------------------------------- *)

Definition fes3 (g1 g2 g3 : binary64) : list binary64 :=
  let '(hs, q) := b64_grow_expansion_aux g1 [g2; g3] in q :: rev hs.

Lemma fes3_shape_of_key :
  forall g1 g2 g3 : binary64,
    b64_fin g1 -> b64_fin g2 -> b64_fin g3 ->
    cascade_safe g1 [g2; g3] ->
    Binary.B2R prec emax g3 <> 0 ->
    Rabs (Binary.B2R prec emax g1)
      < ulp radix2 (SpecFloat.fexp prec emax) (Binary.B2R prec emax g3) ->
    exists bs, drop_zeros (fes3 g1 g2 g3) = flat_map cblock_expand bs
               /\ carry_shape bs /\ Forall is_single bs.
Proof.
  intros g1 g2 g3 F1 F2 F3 Hsafe Hg30 Hkey.
  cbn [cascade_safe] in Hsafe. destruct Hsafe as [S12 [S3 _]].
  unfold fes3. cbn [b64_grow_expansion_aux].
  (* first TwoSum: (Q2, h2) = TwoSum(g2, g1) *)
  pose proof S12 as (A1 & A2 & A3 & A4 & A5 & A6).
  pose proof (b64_TwoSum_correct g2 g1 A1 A2 A3 A4 A5 A6) as Hex2.
  pose proof (b64_TwoSum_nonoverlap g2 g1 A1 A2 A3 A4 A5 A6) as Hno2.
  destruct (b64_plus_correct g2 g1 A1) as [RQ2 FQ2].
  destruct (b64_plus_correct _ _ A6) as [_ Fh2].
  change (fst (b64_TwoSum g2 g1)) with (b64_plus g2 g1) in S3.
  destruct (b64_TwoSum g2 g1) as [Q2 h2] eqn:E2.
  cbv iota beta in Hex2, Hno2.
  unfold b64_TwoSum in E2. injection E2 as EQ2 Eh2.
  rewrite EQ2 in RQ2, FQ2, S3. rewrite Eh2 in Fh2.
  (* second TwoSum: (Q3, h3) = TwoSum(g3, Q2) *)
  pose proof S3 as (B1 & B2 & B3 & B4 & B5 & B6).
  pose proof (b64_TwoSum_correct g3 Q2 B1 B2 B3 B4 B5 B6) as Hex3.
  pose proof (b64_TwoSum_nonoverlap g3 Q2 B1 B2 B3 B4 B5 B6) as Hno3.
  destruct (b64_plus_correct g3 Q2 B1) as [RQ3 FQ3].
  destruct (b64_plus_correct _ _ B6) as [_ Fh3].
  destruct (b64_TwoSum g3 Q2) as [Q3 h3] eqn:E3.
  cbv iota beta in Hex3, Hno3.
  unfold b64_TwoSum in E3. injection E3 as EQ3 Eh3.
  rewrite EQ3 in RQ3, FQ3. rewrite Eh3 in Fh3.
  cbn [rev app].
  (* 2^c with c = min(cexp g3, cexp Q2) *)
  set (c := Z.min (cexp radix2 (SpecFloat.fexp prec emax) (Binary.B2R prec emax g3))
                  (cexp radix2 (SpecFloat.fexp prec emax) (Binary.B2R prec emax Q2))).
  assert (Mg3 : pow2_multiple c (Binary.B2R prec emax g3))
    by (apply (pow2_multiple_le _ _ _ (Z.le_min_l _ _)), b64_pow2_multiple_cexp).
  assert (MQ2 : pow2_multiple c (Binary.B2R prec emax Q2))
    by (apply (pow2_multiple_le _ _ _ (Z.le_min_r _ _)), b64_pow2_multiple_cexp).
  assert (MQ3 : pow2_multiple c (Binary.B2R prec emax Q3)).
  { rewrite RQ3. apply round_pow2_multiple, pow2_multiple_plus; assumption. }
  assert (Mh3 : pow2_multiple c (Binary.B2R prec emax h3)).
  { replace (Binary.B2R prec emax h3)
      with ((Binary.B2R prec emax g3 + Binary.B2R prec emax Q2) - Binary.B2R prec emax Q3)
      by lra.
    apply pow2_multiple_minus; [ apply pow2_multiple_plus | ]; assumption. }
  (* |h2| < 2^c *)
  assert (Hh2g1 : Rabs (Binary.B2R prec emax h2) <= Rabs (Binary.B2R prec emax g1)).
  { replace (Binary.B2R prec emax h2)
      with (- (round radix2 (SpecFloat.fexp prec emax) (BinarySingleNaN.round_mode mode_b64)
                 (Binary.B2R prec emax g2 + Binary.B2R prec emax g1)
               - (Binary.B2R prec emax g2 + Binary.B2R prec emax g1)))
      by (rewrite <- RQ2; lra).
    rewrite Rabs_Ropp.
    apply round_N_err_le_operand, Binary.generic_format_B2R. }
  assert (Hh2c : Rabs (Binary.B2R prec emax h2) < bpow radix2 c).
  { unfold c. destruct (Z.min_spec (cexp radix2 (SpecFloat.fexp prec emax) (Binary.B2R prec emax g3))
                                  (cexp radix2 (SpecFloat.fexp prec emax) (Binary.B2R prec emax Q2)))
      as [[_ Hm] | [_ Hm]]; rewrite Hm.
    - rewrite <- ulp_neq_0 by exact Hg30. lra.
    - destruct (Req_dec (Binary.B2R prec emax Q2) 0) as [HQ0 | HQ0].
      + assert (Hh20 : Binary.B2R prec emax h2 = 0).
        { apply binary64_below_emin_is_zero. rewrite HQ0 in Hno2.
          change (ulp radix2 (SpecFloat.fexp prec emax) 0) with (b64_ulp 0) in Hno2.
          rewrite b64_ulp_FLT_0 in Hno2.
          pose proof (bpow_gt_0 radix2 (3 - emax - prec)). lra. }
        rewrite Hh20, Rabs_R0. apply bpow_gt_0.
      + rewrite ulp_neq_0 in Hno2 by exact HQ0.
        pose proof (bpow_gt_0 radix2 (cexp radix2 (SpecFloat.fexp prec emax)
                                         (Binary.B2R prec emax Q2))). lra. }
  apply (three_singles_shape Q3 h3 h2 c FQ3 Fh3 Fh2 Hno3 MQ3 Mh3 Hh2c).
Qed.

(* --------------------------------------------------------------------------
   RUNG 2.
   -------------------------------------------------------------------------- *)

(* The exhibited decomposition, as singles. *)
Lemma fes_rung2_singles :
  forall e f : list binary64,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
    (length e + length f = 3)%nat ->
    exists bs, drop_zeros (fast_expansion_sum e f) = flat_map cblock_expand bs
               /\ carry_shape bs /\ Forall is_single bs.
Proof.
  intros e f He Hf Hef Hff Hov Hlen.
  pose proof (fes_cascade_safe e f Hef Hff Hov) as Hsafe.
  assert (Hfin : Forall b64_fin (sort_by_abs (e ++ f)))
    by (apply sort_by_abs_Forall, Forall_app; split; assumption).
  assert (Hl3 : length (sort_by_abs (e ++ f)) = 3%nat)
    by (rewrite sort_by_abs_length, length_app; exact Hlen).
  destruct (sort_by_abs (e ++ f)) as [| g1 [| g2 [| g3 [| g4 rest]]]] eqn:Hs;
    cbn [length] in Hl3; try lia.
  destruct (key_lt_ulp e f g1 g2 g3 He Hf Hlen Hs) as [Hg30 Hkey].
  inversion Hfin as [| ? ? F1 Hfin2]; subst.
  inversion Hfin2 as [| ? ? F2 Hfin3]; subst.
  inversion Hfin3 as [| ? ? F3 _]; subst.
  unfold fast_expansion_sum. rewrite Hs.
  exact (fes3_shape_of_key g1 g2 g3 F1 F2 F3 Hsafe Hg30 Hkey).
Qed.

(* The shape for the exhibited decomposition (what the target consumes). *)
Theorem fes_carry_bridge_rung2 :
  forall e f : list binary64,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
    (length e + length f = 3)%nat ->
    exists bs, drop_zeros (fast_expansion_sum e f) = flat_map cblock_expand bs
               /\ carry_shape bs.
Proof.
  intros e f He Hf Hef Hff Hov Hlen.
  destruct (fes_rung2_singles e f He Hf Hef Hff Hov Hlen) as [bs [Hl [Hs _]]].
  exists bs. split; assumption.
Qed.

(* Bridge part (a) at total length 3. *)
Theorem fes_carry_pattern_rung2 : fes_priest_carry_pattern_n 3.
Proof.
  intros e f He Hf Hef Hff Hov Hlen.
  destruct (fes_rung2_singles e f He Hf Hef Hff Hov Hlen) as [bs [Hl [[Hok [Hdec _]] _]]].
  exists bs. split; [ exact Hl | split; assumption ].
Qed.

(* Bridge part (b) at total length 3, for EVERY decomposition. *)
Theorem fes_reduction_nonoverlap_rung2 : fes_priest_reduction_nonoverlap_n 3.
Proof.
  intros e f He Hf Hef Hff Hov Hlen bs Hl _.
  destruct (fes_rung2_singles e f He Hf Hef Hff Hov Hlen)
    as [bs0 [Hl0 [[Hok0 [Hdec0 Hno0]] Hsg0]]].
  assert (Hdesc : strict_desc (flat_map cblock_expand bs)).
  { rewrite <- Hl, Hl0. apply singles_strict_desc; assumption. }
  rewrite (desc_all_singles bs Hdesc), <- Hl, Hl0, <- (singles_reduce bs0 Hsg0).
  exact Hno0.
Qed.

(* The target on rung 2, and on all of rungs 1-2 together. *)
Corollary carry_clean_priest_target_rung2 :
  forall e f : list binary64,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
    (length e + length f <= 3)%nat ->
    nonoverlapping_chain (carry_clean (fast_expansion_sum e f)).
Proof.
  intros e f He Hf Hef Hff Hov Hlen.
  destruct (Nat.eq_dec (length e + length f) 3) as [H3 | H3].
  - destruct (fes_carry_bridge_rung2 e f He Hf Hef Hff Hov H3) as [bs [Hl Hs]].
    apply (carry_clean_nonoverlap_of_shape _ bs Hl Hs).
  - apply carry_clean_priest_target_base_case; [ lia | assumption | assumption | ].
    assert (bpow radix2 (emax - 5) <= bpow radix2 (emax - 4)) by (apply bpow_le; lia).
    lra.
Qed.

Print Assumptions sorted3_bounds.
Print Assumptions priest_pair_lt_ulp.
Print Assumptions round_pow2_multiple.
Print Assumptions three_singles_shape.
Print Assumptions key_lt_ulp.
Print Assumptions fes_carry_bridge_rung2.
Print Assumptions carry_clean_priest_target_rung2.
Print Assumptions desc_all_singles.
Print Assumptions fes3_shape_of_key.
Print Assumptions fes_carry_pattern_rung2.
Print Assumptions fes_reduction_nonoverlap_rung2.
