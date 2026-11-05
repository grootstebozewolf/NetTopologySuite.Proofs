(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_CarryCleanOneBit
   ----------------------------------------------------------------------------
   Fast-Expansion-Sum on two Priest expansions, up to six components in
   total: after dropping zeros, every adjacent pair of the raw output
   overlaps by at most one bit (`overlap_within_chain 1`).  No carry/cancel
   post-pass: the statement is about `fast_expansion_sum` itself.

   THE ARGUMENT.  The rungs (B64_CarryCleanRung2 .. Rung5) decompose the
   output into blocks -- singles, twins (x, x), anti pairs (x, -x) -- whose
   reduction is nonoverlapping.  Two extra facts, read off the same case
   analysis, make the raw list one-bit-overlapping:
     - every twin and anti component is +-2^c (`block_pow2`);
     - the element before an anti pair at 2^c is a multiple of 2^c
       (`anti_step`).
   `overlap_within_1_of_aligned_shape` is the rounding-free step from such
   a decomposition to the one-bit chain.  Rungs 2 and 3 are all singles, so
   their outputs are nonoverlapping outright; rungs 4 and 5 re-run the rung
   proofs as `_aligned` siblings that also return the two facts.  The rung
   files are untouched.

   PROVED HERE:
     overlap_within_1_of_aligned_shape  blocks with the two facts -> one bit
     fes_overlap_within_1_short         totals 0 .. 2
     fes_overlap_within_1_rung2 .. 5    totals 3 .. 6
     fes_overlap_within_1_le6           every total <= 6

   NOT COVERED.  Seven or more components.  This is NOT Priest's bound or
   any general Fast-Expansion-Sum theorem: it is the n <= 6 instance only.

   topic: binary64
   claimId: fes-overlap-within-1-le6
   witness: fes_overlap_within_1_le6

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
     B64_CarryCleanRung4 B64_CarryCleanLadder B64_CarryCleanRung5.

Import ListNotations.
Local Open Scope R_scope.

Local Abbreviation b2r := (Binary.B2R prec emax).
Local Abbreviation RN := (round radix2 b64_fexp (BinarySingleNaN.round_mode mode_b64)).

(* --------------------------------------------------------------------------
   Aligned decompositions.
   -------------------------------------------------------------------------- *)

Definition block_first (b : cblock) : binary64 :=
  match b with CSingle u => u | CTwin x => x | CAnti x => x end.

Definition block_last (b : cblock) : binary64 :=
  match b with CSingle u => u | CTwin x => x | CAnti x => b64_neg x end.

(* twin and anti components are powers of two in magnitude *)
Definition block_pow2 (b : cblock) : Prop :=
  match b with
  | CSingle _ => True
  | CTwin x | CAnti x => exists c : Z, Rabs (b2r x) = bpow radix2 c
  end.

(* the element before an anti pair at 2^c is a multiple of 2^c *)
Definition anti_step (b b' : cblock) : Prop :=
  match b' with
  | CAnti y => forall c : Z, Rabs (b2r y) = bpow radix2 c -> pow2_multiple c (b2r (block_last b))
  | _ => True
  end.

Fixpoint pairs_aligned (bs : list cblock) : Prop :=
  match bs with
  | [] => True
  | b :: rest =>
      block_pow2 b
      /\ match rest with [] => True | b' :: _ => anti_step b b' end
      /\ pairs_aligned rest
  end.

Definition aligned_pattern (bs : list cblock) : Prop :=
  carry_pattern bs /\ pairs_aligned bs.

Lemma expand_last : forall b d, last (cblock_expand b) d = block_last b.
Proof. intros [u | x | x] d; reflexivity. Qed.

Lemma expand_hd : forall b r d, hd d (flat_map cblock_expand (b :: r)) = block_first b.
Proof. intros [u | x | x] r d; reflexivity. Qed.

Lemma within_block :
  forall b, block_ok b -> block_pow2 b -> overlap_within_chain 1 (cblock_expand b).
Proof.
  intros [u | x | x] Hok Hp; cbn [cblock_expand overlap_within_chain]; [ exact I | | ].
  - destruct Hp as [c Hc]. split; [ | exact I ]. unfold overlap_within_b64.
    apply (overlap_within_1_pow2 c); [ exact Hc | rewrite Hc; apply bpow_lt_succ ].
  - destruct Hp as [c Hc]. split; [ | exact I ]. unfold overlap_within_b64.
    apply (overlap_within_1_pow2 c); [ exact Hc | ].
    rewrite b64_neg_R, Rabs_Ropp, Hc. apply bpow_lt_succ.
Qed.

Lemma link_step :
  forall (b b' : cblock) (r : list cblock),
    block_ok b -> block_ok b' -> block_key b' < block_key b ->
    block_pow2 b -> block_pow2 b' -> anti_step b b' ->
    nonoverlapping_chain (flat_map cblock_reduce (b :: b' :: r)) ->
    overlap_within_b64 1 (block_last b) (block_first b').
Proof.
  intros b b' r Hok Hok' Hk Hp Hp' Hst Hn. unfold overlap_within_b64.
  destruct b' as [v | y | y].
  3: { cbn [block_first]. destruct Hp' as [c Hc]. destruct (Hst c Hc) as [n Hm].
       apply (overlap_within_1_multiple n c); [ exact Hm | rewrite Hc; apply bpow_lt_succ ]. }
  all: destruct b as [u | x | x].
  (* b an anti pair: its last component is +-2^c, the next key is below 2^c *)
  3, 6: cbn [block_first block_last]; destruct Hp as [c Hc];
        apply (overlap_within_1_pow2 c); [ rewrite b64_neg_R, Rabs_Ropp; exact Hc | ];
        cbn [block_key] in Hk; pose proof (bpow_lt_succ c);
        first [ pose proof (Rabs_pos (b2r y)) | pose proof (Rabs_pos (b2r v)) ]; lra.
  (* otherwise: the reduction's first link, halved where a twin doubled *)
  all: cbn [flat_map cblock_reduce app nonoverlapping_chain] in Hn; destruct Hn as [Hn _];
       unfold nonoverlapping_b64, nonoverlapping_R in Hn; cbn [block_first block_last].
  - apply (overlap_within_mono 0 1); [ lia | exact Hn ].
  - destruct Hok as [[Fx _] Hovx]. destruct (double_exact x Fx Hovx) as [Hd _]. rewrite Hd in Hn.
    exact (overlap_within_half_l 0 _ _ Hn).
  - destruct Hok' as [[Fy _] Hovy]. destruct (double_exact y Fy Hovy) as [Hd _]. rewrite Hd in Hn.
    exact (overlap_within_half_r 0 _ _ Hn).
  - destruct Hok as [[Fx _] Hovx]. destruct (double_exact x Fx Hovx) as [Hd _]. rewrite Hd in Hn.
    destruct Hok' as [[Fy _] Hovy]. destruct (double_exact y Fy Hovy) as [Hd' _]. rewrite Hd' in Hn.
    apply (overlap_within_mono 0 1); [ lia | exact (overlap_within_half_both 0 _ _ Hn) ].
Qed.

(* The rounding-free step: an aligned decomposition whose reduction is
   nonoverlapping expands to a one-bit-overlapping list. *)
Theorem overlap_within_1_of_aligned_shape :
  forall bs : list cblock,
    aligned_pattern bs -> nonoverlapping_chain (flat_map cblock_reduce bs) ->
    overlap_within_chain 1 (flat_map cblock_expand bs).
Proof.
  induction bs as [| b r IH]; intros [[Hok Hk] Ha] Hn; [ exact I | ].
  apply Forall_cons_iff in Hok as [Hb Hr].
  destruct Hk as [Hk1 Hkr]. destruct Ha as (Hpb & Hst & Har).
  cbn [flat_map]. apply (overlap_within_chain_app 1 _ _ (block_first b)).
  - apply within_block; assumption.
  - apply IH; [ split; [ split; assumption | exact Har ] | ].
    cbn [flat_map] in Hn. exact (nonoverlapping_chain_app_r _ _ Hn).
  - intros _ Hne. destruct r as [| b' r'].
    + exfalso. apply Hne. reflexivity.
    + rewrite expand_last, expand_hd.
      apply Forall_cons_iff in Hr as [Hb' _]. destruct Har as (Hpb' & _ & _).
      exact (link_step b b' r' Hb Hb' Hk1 Hpb Hpb' Hst Hn).
Qed.

Lemma overlap_within_1_of_shape_aligned :
  forall (l : list binary64) (bs : list cblock),
    l = flat_map cblock_expand bs -> carry_shape bs -> pairs_aligned bs ->
    overlap_within_chain 1 l.
Proof.
  intros l bs -> (Hok & Hk & Hn) Ha.
  exact (overlap_within_1_of_aligned_shape bs (conj (conj Hok Hk) Ha) Hn).
Qed.

(* --------------------------------------------------------------------------
   Building aligned decompositions.
   -------------------------------------------------------------------------- *)

Lemma aligned_singles : forall l, pairs_aligned (map CSingle l).
Proof.
  induction l as [| x l IH]; [ exact I | ].
  cbn [map pairs_aligned]. split; [ exact I | split; [ | exact IH ] ].
  destruct l; exact I.
Qed.

Lemma aligned_of_singles : forall bs, Forall is_single bs -> pairs_aligned bs.
Proof.
  induction bs as [| b r IH]; intro H; [ exact I | ].
  apply Forall_cons_iff in H as [Hb Hr].
  destruct b as [u | x | x]; cbn [is_single] in Hb; try contradiction.
  cbn [pairs_aligned]. split; [ exact I | split; [ | exact (IH Hr) ] ].
  destruct r as [| b' r']; [ exact I | ].
  apply Forall_cons_iff in Hr as [Hb' _].
  destruct b' as [v | y | y]; cbn [is_single] in Hb'; try contradiction. exact I.
Qed.

Lemma aligned_insert :
  forall (pre : list binary64) (b : cblock) (t : list binary64),
    block_pow2 b -> Forall (fun y => anti_step (CSingle y) b) pre ->
    pairs_aligned (map CSingle pre ++ b :: map CSingle t).
Proof.
  induction pre as [| y pre IH]; intros b t Hb Hpre.
  - cbn [map app pairs_aligned]. split; [ exact Hb | split; [ | apply aligned_singles ] ].
    destruct t; exact I.
  - apply Forall_cons_iff in Hpre as [Hy Hpre].
    cbn [map app pairs_aligned]. split; [ exact I | split; [ | apply IH; assumption ] ].
    destruct pre as [| z pre]; [ exact Hy | exact I ].
Qed.

Lemma anti_step_single :
  forall (q a : binary64) (c : Z),
    Rabs (b2r a) = bpow radix2 c -> pow2_multiple c (b2r q) -> anti_step (CSingle q) (CAnti a).
Proof.
  intros q a c Ha Mq c' Hc'.
  assert (E : c' = c) by (apply (bpow_inj radix2); lra).
  subst c'. exact Mq.
Qed.

(* --------------------------------------------------------------------------
   Rung 4 leaves, aligned (copies of B64_CarryCleanRung4's, one more bullet).
   -------------------------------------------------------------------------- *)

Lemma shape_anti_aligned :
  forall (q a b : binary64) (t : list binary64) (c : Z),
    b64_fin q -> b64_fin a -> b64_fin b -> Forall b64_fin t ->
    b2r b = - b2r a -> Rabs (b2r a) = bpow radix2 c -> Rabs (b2r a) < Rabs (b2r q) ->
    pow2_multiple c (b2r q) -> Forall (below c) t -> layered t ->
    exists bs, drop_zeros (q :: a :: b :: t) = flat_map cblock_expand bs /\ carry_shape bs /\ pairs_aligned bs.
Proof.
  intros q a b t c Fq Fa Fb Ft Hba Hea Haq Mq Bt Lt.
  assert (Hca : bpow radix2 c <= Rabs (b2r a)) by lra.
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
  split; [ split; [ | split ] | ].
  - repeat constructor; try assumption. apply Forall_map, Nt.
  - split; [ cbn [block_key]; lra | ].
    apply keys_prefix; [ | exact Dt0 ].
    intros y Hy. cbn [block_key]. pose proof (below_in _ _ _ Bt0 Hy). lra.
  - cbn [flat_map cblock_reduce app]. rewrite reduce_singles.
    assert (Nq : b64_nz q) by (split; assumption).
    apply (layered_desc (q :: t0)); [ | constructor; assumption ].
    split; [ exists c; split; assumption | exact Lt0 ].
  - change (CSingle q :: CAnti a :: map CSingle t0) with (map CSingle [q] ++ CAnti a :: map CSingle t0).
    apply aligned_insert; [ exists c; exact Hea | ].
    constructor; [ apply (anti_step_single q a c Hea Mq) | constructor ].
Qed.

Lemma shape_twin_aligned :
  forall (q b : binary64) (t : list binary64) (c : Z),
    b64_fin q -> b64_fin b -> Forall b64_fin t ->
    b2r b = b2r q -> Rabs (b2r q) = bpow radix2 c ->
    2 * Rabs (b2r q) < bpow radix2 emax ->
    pow2_multiple c (b2r q) -> Forall (below c) t -> layered t ->
    exists bs, drop_zeros (q :: b :: t) = flat_map cblock_expand bs /\ carry_shape bs /\ pairs_aligned bs.
Proof.
  intros q b t c Fq Fb Ft Hbq Heq Hov [nq Hnq] Bt Lt.
  assert (Hcq : bpow radix2 c <= Rabs (b2r q)) by lra.
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
  split; [ split; [ | split ] | ].
  - constructor; [ split; [ split; assumption | exact Hov ] | apply Forall_map, Nt ].
  - apply keys_prefix; [ | exact Dt0 ].
    intros y Hy. cbn [block_key]. pose proof (below_in _ _ _ Bt0 Hy).
    pose proof (Rabs_pos (b2r q)). lra.
  - cbn [flat_map cblock_reduce app]. rewrite reduce_singles.
    assert (Nd : b64_nz (b64_mult q b64_two_unit)) by (split; [ exact Fd | rewrite Hd; lra ]).
    apply (layered_desc (b64_mult q b64_two_unit :: t0)); [ | constructor; assumption ].
    split; [ | exact Lt0 ].
    exists c. split; [ exists (2 * nq)%Z; rewrite Hd, Hnq, mult_IZR; ring | exact Bt0 ].
  - change (CTwin q :: map CSingle t0) with (map CSingle [] ++ CTwin q :: map CSingle t0).
    apply aligned_insert; [ exists c; exact Heq | constructor ].
Qed.

Lemma tie_finish_aligned :
  forall (Q5 h5 h4 h3 h2 : binary64) (c : Z),
    b64_fin Q5 -> b64_fin h5 -> b64_fin h4 -> b64_fin h3 -> b64_fin h2 ->
    Forall (below c) [h3; h2] -> layered [h3; h2] ->
    2 * bpow radix2 c < bpow radix2 emax ->
    Rabs (b2r h4) = bpow radix2 c ->
    (   (b2r h5 = - b2r h4 /\ pow2_multiple c (b2r Q5) /\ bpow radix2 c < Rabs (b2r Q5))
     \/ (b2r h5 = 0 /\ b2r Q5 = b2r h4)
     \/ (b2r h5 = 0 /\ pow2_multiple (c + 1) (b2r Q5) /\ b2r Q5 <> 0)) ->
    exists bs, drop_zeros [Q5; h5; h4; h3; h2] = flat_map cblock_expand bs /\ carry_shape bs /\ pairs_aligned bs.
Proof.
  intros Q5 h5 h4 h3 h2 c FQ Fh5 Fh4 Fh3 Fh2 Bt Lt Hov Hh4 Hcase.
  pose proof (bpow_gt_0 radix2 c) as Hc0.
  assert (Ft : Forall b64_fin [h3; h2]) by (repeat constructor; assumption).
  assert (Hh40 : b2r h4 <> 0) by (intro H; rewrite H, Rabs_R0 in Hh4; lra).
  destruct Hcase as [(Ha & Mq & Hq) | [(Hz & Hq) | (Hz & Mq & Hq0)]].
  - apply (shape_anti_aligned Q5 h5 h4 [h3; h2] c); try assumption.
    + lra.
    + rewrite Ha, Rabs_Ropp. lra.
    + rewrite Ha, Rabs_Ropp. lra.
  - rewrite drop_zeros_skip2 by (apply b64_is_zero_true; assumption).
    apply (shape_twin_aligned Q5 h4 [h3; h2] c); try assumption.
    + lra.
    + rewrite Hq. lra.
    + rewrite Hq. lra.
    + apply pow2_multiple_pm. rewrite Hq. exact Hh4.
  - destruct (singles_shape_of_layered [Q5; h5; h4; h3; h2]) as [bs [E [S Sg]]].
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
    + exists bs. split; [ exact E | split; [ exact S | apply aligned_of_singles, Sg ] ].
Qed.

(* --------------------------------------------------------------------------
   Ladder leaves, aligned (copies of B64_CarryCleanLadder's).
   -------------------------------------------------------------------------- *)

Lemma sstate_shape_aligned :
  forall Q E L K, sstate Q E L K ->
    exists bs, drop_zeros (Q :: E) = flat_map cblock_expand bs /\ carry_shape bs /\ pairs_aligned bs.
Proof.
  intros Q E L K (FQ & FE & MQ & BE & LE & _).
  destruct (singles_shape_of_layered (Q :: E)) as [bs [Hl [Hs Sg]]].
  - constructor; assumption.
  - apply layered_filter. split; [ exists L; split; assumption | exact LE ].
  - exists bs. split; [ exact Hl | split; [ exact Hs | apply aligned_of_singles, Sg ] ].
Qed.

Lemma shape_insert_anti_aligned :
  forall (pre t : list binary64) (a b : binary64) (c : Z),
    Forall b64_nz pre -> Forall b64_nz t -> b64_fin a -> b64_fin b ->
    b2r b = - b2r a -> b2r a <> 0 ->
    Forall (fun x => Rabs (b2r a) < Rabs (b2r x)) pre ->
    Forall (fun x => Rabs (b2r x) < Rabs (b2r a)) t ->
    layered (pre ++ t) ->
    Rabs (b2r a) = bpow radix2 c -> Forall (fun x => pow2_multiple c (b2r x)) pre ->
    exists bs, pre ++ a :: b :: t = flat_map cblock_expand bs /\ carry_shape bs /\ pairs_aligned bs.
Proof.
  intros pre t a b c Np Nt Fa Fb Hba Ha0 Hp Ht Lpt Hea Mp.
  assert (Nb : b2r b <> 0) by (rewrite Hba; intro H; apply Ha0; lra).
  assert (Eb : b = b64_neg a).
  { apply b64_eq_of_R; [ exact Fb | apply b64_neg_fin, Fa | rewrite b64_neg_R; exact Hba | exact Nb ]. }
  assert (Npt : Forall b64_nz (pre ++ t)) by (apply Forall_app; split; assumption).
  destruct (layered_desc _ Lpt Npt) as [Dpt Cpt].
  destruct (strict_desc_app _ _ Dpt) as [Dp Dt].
  exists (map CSingle pre ++ CAnti a :: map CSingle t).
  split; [ rewrite expand_insert, Eb; reflexivity | ].
  split; [ split; [ | split ] | ].
  - apply Forall_app. split; [ apply Forall_map, Np | ].
    constructor; [ split; assumption | apply Forall_map, Nt ].
  - apply keys_insert; assumption.
  - rewrite reduce_insert. cbn [cblock_reduce app]. exact Cpt.
  - apply aligned_insert; [ exists c; exact Hea | ].
    eapply Forall_impl; [ | exact Mp ]. intros y My. exact (anti_step_single y a c Hea My).
Qed.

Lemma shape_insert_twin_aligned :
  forall (pre t : list binary64) (x : binary64) (c : Z),
    Forall b64_nz pre -> Forall b64_nz t -> b64_fin x -> b2r x <> 0 ->
    2 * Rabs (b2r x) < bpow radix2 emax ->
    Forall (fun y => 2 * Rabs (b2r x) < Rabs (b2r y)) pre ->
    Forall (fun y => Rabs (b2r y) < 2 * Rabs (b2r x)) t ->
    layered (pre ++ b64_mult x b64_two_unit :: t) ->
    Rabs (b2r x) = bpow radix2 c ->
    exists bs, pre ++ x :: x :: t = flat_map cblock_expand bs /\ carry_shape bs /\ pairs_aligned bs.
Proof.
  intros pre t x c Np Nt Fx Hx0 Hov Hp Ht Lpt Hex.
  destruct (double_exact x Fx Hov) as [Hd Fd].
  assert (Nd : b64_nz (b64_mult x b64_two_unit)) by (split; [ exact Fd | rewrite Hd; lra ]).
  assert (Npt : Forall b64_nz (pre ++ b64_mult x b64_two_unit :: t))
    by (apply Forall_app; split; [ exact Np | constructor; assumption ]).
  destruct (layered_desc _ Lpt Npt) as [Dpt Cpt].
  destruct (strict_desc_app _ _ Dpt) as [Dp Dt]. pose proof (strict_desc_tail _ _ Dt) as Dt'.
  exists (map CSingle pre ++ CTwin x :: map CSingle t).
  split; [ rewrite expand_insert; reflexivity | ].
  split; [ split; [ | split ] | ].
  - apply Forall_app. split; [ apply Forall_map, Np | ].
    constructor; [ split; [ split; assumption | exact Hov ] | apply Forall_map, Nt ].
  - apply keys_insert; assumption.
  - rewrite reduce_insert. cbn [cblock_reduce app]. exact Cpt.
  - apply aligned_insert; [ exists c; exact Hex | ].
    apply Forall_forall. intros y _. exact I.
Qed.

Lemma tie_finish_tail_aligned :
  forall (Q h' h : binary64) (t : list binary64) (c : Z),
    b64_fin Q -> b64_fin h' -> b64_fin h -> Forall b64_fin t ->
    Forall (below c) t -> layered t ->
    2 * bpow radix2 c < bpow radix2 emax ->
    Rabs (b2r h) = bpow radix2 c ->
    (   (b2r h' = - b2r h /\ pow2_multiple c (b2r Q) /\ bpow radix2 c < Rabs (b2r Q))
     \/ (b2r h' = 0 /\ b2r Q = b2r h)
     \/ (b2r h' = 0 /\ pow2_multiple (c + 1) (b2r Q) /\ b2r Q <> 0)) ->
    exists bs, drop_zeros (Q :: h' :: h :: t) = flat_map cblock_expand bs /\ carry_shape bs /\ pairs_aligned bs.
Proof.
  intros Q h' h t c FQ Fh' Fh Ft Bt Lt Hov Hh Hcase.
  pose proof (bpow_gt_0 radix2 c) as Hc0.
  assert (Hh0 : b2r h <> 0) by (intro H; rewrite H, Rabs_R0 in Hh; lra).
  destruct Hcase as [(Ha & Mq & Hq) | [(Hz & Hq) | (Hz & Mq & Hq0)]].
  - apply (shape_anti_aligned Q h' h t c); try assumption.
    + lra.
    + rewrite Ha, Rabs_Ropp. lra.
    + rewrite Ha, Rabs_Ropp. lra.
  - rewrite drop_zeros_skip2 by (apply b64_is_zero_true; assumption).
    apply (shape_twin_aligned Q h t c); try assumption.
    + lra.
    + rewrite Hq. lra.
    + rewrite Hq. lra.
    + apply pow2_multiple_pm. rewrite Hq. exact Hh.
  - destruct (singles_shape_of_layered (Q :: h' :: h :: t)) as [bs [E [S Sg]]].
    + repeat constructor; assumption.
    + rewrite drop_zeros_skip2 by (apply b64_is_zero_true; assumption).
      rewrite (drop_zeros_cons_nz Q) by (apply b64_is_zero_false; assumption).
      rewrite (drop_zeros_cons_nz h) by (apply b64_is_zero_false; assumption).
      assert (Bt0 : Forall (below c) (drop_zeros t)) by (apply Forall_filter_sub, Bt).
      assert (H2c : bpow radix2 c < bpow radix2 (c + 1)) by (apply bpow_lt; lia).
      split; [ exists (c + 1)%Z; split; [ exact Mq | ] | ].
      { constructor; [ unfold below; lra | ].
        eapply Forall_impl; [ | exact Bt0 ]. unfold below. intros y Hy. lra. }
      split; [ exists c; split; [ apply pow2_multiple_pm, Hh | exact Bt0 ] | ].
      apply layered_filter, Lt.
    + exists bs. split; [ exact E | split; [ exact S | apply aligned_of_singles, Sg ] ].
Qed.

Lemma anti_final_aligned :
  forall (g Q a b : binary64) (t : list binary64) (Mlev c : Z),
    b64_fin g -> b64_TwoSum_safe g Q -> b64_fin a -> b64_fin b -> Forall b64_fin t ->
    pow2_multiple Mlev (b2r Q) -> (Mlev <= cexp radix2 b64_fexp (b2r g))%Z -> (c < Mlev)%Z ->
    b2r b = - b2r a -> Rabs (b2r a) = bpow radix2 c ->
    Forall (below c) t -> layered t ->
    let Q' := fst (b64_TwoSum g Q) in
    let h' := snd (b64_TwoSum g Q) in
    exists bs, drop_zeros (Q' :: h' :: a :: b :: t) = flat_map cblock_expand bs /\ carry_shape bs /\ pairs_aligned bs.
Proof.
  intros g Q a b t Mlev c Fg S Fa Fb Ft MQ HMg HcM Hba Ha Bt Lt Q' h'.
  destruct (ts_facts g Q S) as (FQ' & Fh & RQ' & Hex & Hno & _). fold Q' h' in FQ', Fh, RQ', Hex, Hno.
  pose proof (bpow_gt_0 radix2 c) as Hc0.
  assert (HcM' : bpow radix2 c < bpow radix2 Mlev) by (apply bpow_lt, HcM).
  assert (Ha0 : b2r a <> 0) by (intro H; rewrite H, Rabs_R0 in Ha; lra).
  assert (Hb0 : b2r b <> 0) by (rewrite Hba; intro H; apply Ha0; lra).
  assert (Mg : pow2_multiple Mlev (b2r g)) by (apply (pow2_multiple_le _ _ _ HMg), b64_pow2_multiple_cexp).
  assert (MQ' : pow2_multiple Mlev (b2r Q'))
    by (rewrite RQ'; apply round_pow2_multiple, pow2_multiple_plus; assumption).
  assert (Mh : pow2_multiple Mlev (b2r h')).
  { replace (b2r h') with ((b2r g + b2r Q) - b2r Q') by lra.
    apply pow2_multiple_minus; [ apply pow2_multiple_plus | ]; assumption. }
  assert (BtM : Forall (below Mlev) t) by (apply (below_mono c); [ lia | exact Bt ]).
  pose proof (head_pair_layered Q' h' t Mlev FQ' Fh Hno MQ' Mh BtM Lt) as Lall.
  change (Q' :: h' :: t) with ([Q'; h'] ++ t) in Lall. rewrite drop_zeros_app in Lall.
  change (Q' :: h' :: a :: b :: t) with ([Q'; h'] ++ a :: b :: t).
  rewrite drop_zeros_app.
  rewrite (drop_zeros_cons_nz a) by (apply b64_is_zero_false; assumption).
  rewrite (drop_zeros_cons_nz b) by (apply b64_is_zero_false; assumption).
  apply (shape_insert_anti_aligned _ _ _ _ c); try assumption.
  - apply drop_zeros_nz. repeat constructor; assumption.
  - apply drop_zeros_nz, Ft.
  - pose proof (drop_zeros_nonzero_mult Mlev [Q'; h']) as Hge.
    assert (Hm2 : Forall (pow2_multiple Mlev) (map b2r [Q'; h'])) by (repeat constructor; assumption).
    specialize (Hge Hm2 ltac:(repeat constructor; assumption)).
    eapply Forall_impl; [ | exact Hge ]. cbn beta. intros y Hy. lra.
  - eapply Forall_impl; [ | apply Forall_filter_sub, Bt ]. unfold below. intros y Hy. lra.
  - (* everything above the pair is a multiple of 2^Mlev, hence of 2^c *)
    apply Forall_filter_sub. constructor; [ exact (pow2_multiple_le c Mlev _ ltac:(lia) MQ') | ].
    constructor; [ exact (pow2_multiple_le c Mlev _ ltac:(lia) Mh) | constructor ].
Qed.

Lemma twin_final_aligned :
  forall (g Q z h : binary64) (t : list binary64) (c : Z),
    b64_fin g -> b2r g <> 0 -> b64_TwoSum_safe g Q -> b64_fin z -> b64_fin h -> Forall b64_fin t ->
    b2r z = 0 -> b2r Q = b2r h -> Rabs (b2r h) = bpow radix2 c ->
    bpow radix2 c < ulp radix2 b64_fexp (b2r g) / 4 ->
    2 * bpow radix2 c < bpow radix2 emax ->
    Forall (below c) t -> layered t ->
    let Q' := fst (b64_TwoSum g Q) in
    let h' := snd (b64_TwoSum g Q) in
    exists bs, drop_zeros (Q' :: h' :: z :: h :: t) = flat_map cblock_expand bs /\ carry_shape bs /\ pairs_aligned bs.
Proof.
  intros g Q z h t c Fg Hg0 S Fz Fh Ft Hz HQh Hh Hsmall Hov Bt Lt Q' h'.
  destruct (ts_facts g Q S) as (FQ' & Fh' & RQ' & Hex & _ & _). fold Q' h' in FQ', Fh', RQ', Hex.
  pose proof (bpow_gt_0 radix2 c) as Hc0.
  assert (Hh0 : b2r h <> 0) by (intro H; rewrite H, Rabs_R0 in Hh; lra).
  assert (HQ' : b2r Q' = b2r g) by (rewrite RQ'; apply rn_absorb; [ exact Hg0 | rewrite HQh, Hh; exact Hsmall ]).
  assert (Hh' : b2r h' = b2r h) by lra.
  assert (Eh : h = h') by (apply b64_eq_of_R; [ exact Fh | exact Fh' | symmetry; exact Hh' | exact Hh0 ]).
  assert (HQ0 : b2r Q' <> 0) by (rewrite HQ'; exact Hg0).
  rewrite (drop_zeros_cons_nz Q') by (apply b64_is_zero_false; assumption).
  rewrite (drop_zeros_cons_nz h') by (apply b64_is_zero_false; [ exact Fh' | rewrite Hh'; exact Hh0 ]).
  rewrite (drop_zeros_cons_zero z) by (apply b64_is_zero_true; assumption).
  rewrite (drop_zeros_cons_nz h) by (apply b64_is_zero_false; assumption).
  rewrite <- Eh.
  change (Q' :: h :: h :: drop_zeros t) with ([Q'] ++ h :: h :: drop_zeros t).
  assert (Hov' : 2 * Rabs (b2r h) < bpow radix2 emax) by (rewrite Hh; exact Hov).
  pose proof (ulp_le_abs_b64 g Hg0) as Hug.
  set (eg := cexp radix2 b64_fexp (b2r g)).
  assert (Hue : ulp radix2 b64_fexp (b2r g) = bpow radix2 eg) by (apply ulp_neq_0, Hg0).
  destruct (double_exact h Fh Hov') as [Hd Fd].
  apply (shape_insert_twin_aligned _ _ _ c); try assumption.
  - constructor; [ split; assumption | constructor ].
  - apply drop_zeros_nz, Ft.
  - constructor; [ rewrite HQ', Hh; lra | constructor ].
  - eapply Forall_impl; [ | apply Forall_filter_sub, Bt ]. unfold below. intros y Hy. rewrite Hh. lra.
  - (* layered [Q'; 2h] ++ tail *)
    cbn [app]. split.
    + exists eg. split.
      * rewrite HQ'. apply b64_pow2_multiple_cexp.
      * constructor.
        { unfold below. rewrite Hd, Rabs_mult, Rabs_pos_eq by lra. rewrite <- Hue. lra. }
        eapply Forall_impl; [ | apply Forall_filter_sub, Bt ]. unfold below. intros y Hy. rewrite <- Hue. lra.
    + split; [ | apply layered_filter, Lt ].
      exists (c + 1)%Z. split.
      * rewrite Hd. destruct (pow2_multiple_pm c (b2r h) Hh) as [n Hn].
        exists n. rewrite Hn, bpow_plus. change (bpow radix2 1) with 2. ring.
      * apply (below_mono c); [ lia | apply Forall_filter_sub, Bt ].
Qed.

(* --------------------------------------------------------------------------
   Rung 4, aligned: B64_CarryCleanRung4's case analysis, aligned leaves.
   -------------------------------------------------------------------------- *)

Lemma fes5_shape_of_keys_aligned :
  forall g1 g2 g3 g4 g5 : binary64,
    b64_fin g1 -> b64_fin g2 -> b64_fin g3 -> b64_fin g4 -> b64_fin g5 ->
    cascade_safe g1 [g2; g3; g4; g5] ->
    b64_abs_le g3 g4 -> b64_abs_le g4 g5 ->
    Rabs (b2r g5) <= bpow radix2 (emax - 5) ->
    keys5 g1 g2 g3 g4 g5 ->
    exists bs, drop_zeros (fes5 g1 g2 g3 g4 g5) = flat_map cblock_expand bs
               /\ carry_shape bs /\ pairs_aligned bs.
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
    destruct (singles_shape_of_layered [Q5; h5; h4; h3; h2]) as [bs [E [Sh Sg]]].
    - repeat constructor; assumption.
    - apply (head_pair_layered Q5 h5 [h4; h3; h2] c0 FQ5 Fh5 Hno5 MQ5 Mh5).
      + unfold below in *. repeat constructor; lra.
      + split; [ exists c1; split; [ exact Mh4 | repeat constructor; assumption ] | exact Lt ].
    - exists bs. split; [ exact E | split; [ exact Sh | apply aligned_of_singles, Sg ] ]. }
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
  apply (tie_finish_aligned Q5 h5 h4 h3 h2 c5 FQ5 Fh5 Fh4 Fh3 Fh2 Bt5 Lt Hov2 Ht). fold u.
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

Lemma fes_rung4_shape_aligned :
  forall e f : list binary64,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
    (length e + length f = 5)%nat ->
    exists bs, drop_zeros (fast_expansion_sum e f) = flat_map cblock_expand bs
               /\ carry_shape bs /\ pairs_aligned bs.
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
  exact (fes5_shape_of_keys_aligned g1 g2 g3 g4 g5 F1 F2 F3 F4 F5 Hsafe H34 H45 Hov5 Hkeys).
Qed.

(* --------------------------------------------------------------------------
   Rung 5, aligned: B64_CarryCleanRung5's case analysis, aligned leaves.
   -------------------------------------------------------------------------- *)

Lemma fes6_shape_of_keys_aligned :
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
               /\ carry_shape bs /\ pairs_aligned bs.
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
      apply (anti_final_aligned g6 Q5 h5 h4 [h3; h2] M5 c5); try assumption.
      * rewrite HQ5. unfold pow2_multiple.
        destruct Hs as [-> | ->]; [ exists 2%Z | exists (-2)%Z ];
          cbn [IZR IPR IPR_2]; ring.
      * lia.
      * rewrite Hh4s, Ha. ring.
      * rewrite Ha, Rabs_Ropp. apply abs_sign; [ exact Hs | lra ].
    + (* twin (Q5, h4), h5 = 0 *)
      apply (twin_final_aligned g6 Q5 h5 h4 [h3; h2] c5); try assumption.
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
      exact (sstate_shape_aligned _ _ _ _ St6).
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
      apply (tie_finish_tail_aligned Q6 h6 h5 [h4; h3; h2] c6); try assumption.
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
      exact (sstate_shape_aligned _ _ _ _ St6).
Qed.

Lemma fes_rung5_shape_aligned :
  forall e f : list binary64,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
    (length e + length f = 6)%nat ->
    exists bs, drop_zeros (fast_expansion_sum e f) = flat_map cblock_expand bs
               /\ carry_shape bs /\ pairs_aligned bs.
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
  exact (fes6_shape_of_keys_aligned g1 g2 g3 g4 g5 g6 F1 F2 F3 F4 F5 F6 Hsafe H34 H45 H56
           N3 N4 N5 N6 K1 K2 K3 K4 Hov6).
Qed.

(* --------------------------------------------------------------------------
   The headline.
   -------------------------------------------------------------------------- *)

Definition fes_overlap_within_1_n (n : nat) : Prop :=
  forall e f : list binary64,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
    (length e + length f = n)%nat ->
    overlap_within_chain 1 (drop_zeros (fast_expansion_sum e f)).

(* Totals 0 .. 2: at most one TwoSum, whose output is strictly successive. *)
Theorem fes_overlap_within_1_short : forall n, (n <= 2)%nat -> fes_overlap_within_1_n n.
Proof.
  intros n Hn e f He Hf Hef Hff Hov Hlen.
  pose proof (fes_cascade_safe e f Hef Hff Hov) as Hsafe.
  assert (Hl : (length (sort_by_abs (e ++ f)) <= 2)%nat)
    by (rewrite sort_by_abs_length, length_app; lia).
  unfold fast_expansion_sum.
  destruct (sort_by_abs (e ++ f)) as [| a [| b [| c rest]]]; cbn [length] in Hl; try lia.
  - exact I.
  - cbn [b64_grow_expansion_aux rev app]. apply overlap_within_chain_short.
    unfold drop_zeros. cbn [filter]. destruct (negb (b64_is_zero a)); cbn [length]; lia.
  - destruct Hsafe as [S _].
    pose proof (ts_facts b a S) as T. cbv zeta in T.
    cbn [b64_grow_expansion_aux].
    destruct (b64_TwoSum b a) as [s h] eqn:Ets. cbn [fst snd] in T.
    destruct T as (_ & _ & _ & _ & Hss & _).
    cbn [b64_grow_expansion_aux rev app].
    unfold drop_zeros. cbn [filter].
    destruct (negb (b64_is_zero s)), (negb (b64_is_zero h)); try exact I.
    split; [ apply strict_succ_overlap_within_1, Hss | exact I ].
Qed.

(* Totals 3 and 4: all singles, so the output is nonoverlapping outright. *)
Theorem fes_overlap_within_1_rung2 : fes_overlap_within_1_n 3.
Proof.
  intros e f He Hf Hef Hff Hov Hlen.
  destruct (fes_rung2_singles e f He Hf Hef Hff Hov Hlen) as [bs [Hl [Hs Hsg]]].
  rewrite Hl. apply nonoverlapping_chain_overlap_within_1.
  rewrite <- (singles_reduce bs Hsg). exact (proj2 (proj2 Hs)).
Qed.

Theorem fes_overlap_within_1_rung3 : fes_overlap_within_1_n 4.
Proof.
  intros e f He Hf Hef Hff Hov Hlen.
  destruct (fes_rung3_singles e f He Hf Hef Hff Hov Hlen) as [bs [Hl [Hs Hsg]]].
  rewrite Hl. apply nonoverlapping_chain_overlap_within_1.
  rewrite <- (singles_reduce bs Hsg). exact (proj2 (proj2 Hs)).
Qed.

(* Totals 5 and 6: the aligned decompositions. *)
Theorem fes_overlap_within_1_rung4 : fes_overlap_within_1_n 5.
Proof.
  intros e f He Hf Hef Hff Hov Hlen.
  destruct (fes_rung4_shape_aligned e f He Hf Hef Hff Hov Hlen) as [bs [Hl [Hs Ha]]].
  exact (overlap_within_1_of_shape_aligned _ bs Hl Hs Ha).
Qed.

Theorem fes_overlap_within_1_rung5 : fes_overlap_within_1_n 6.
Proof.
  intros e f He Hf Hef Hff Hov Hlen.
  destruct (fes_rung5_shape_aligned e f He Hf Hef Hff Hov Hlen) as [bs [Hl [Hs Ha]]].
  exact (overlap_within_1_of_shape_aligned _ bs Hl Hs Ha).
Qed.

Theorem fes_overlap_within_1_le6 : forall n, (n <= 6)%nat -> fes_overlap_within_1_n n.
Proof.
  intros n Hn.
  destruct (Nat.le_gt_cases n 2) as [H2 | H2]; [ exact (fes_overlap_within_1_short n H2) | ].
  assert (Hc : (n = 3 \/ n = 4 \/ n = 5 \/ n = 6)%nat) by lia.
  destruct Hc as [-> | [-> | [-> | ->]]].
  - exact fes_overlap_within_1_rung2.
  - exact fes_overlap_within_1_rung3.
  - exact fes_overlap_within_1_rung4.
  - exact fes_overlap_within_1_rung5.
Qed.

Print Assumptions overlap_within_1_of_aligned_shape.
Print Assumptions fes_rung4_shape_aligned.
Print Assumptions fes_rung5_shape_aligned.
Print Assumptions fes_overlap_within_1_short.
Print Assumptions fes_overlap_within_1_rung2.
Print Assumptions fes_overlap_within_1_rung3.
Print Assumptions fes_overlap_within_1_rung4.
Print Assumptions fes_overlap_within_1_rung5.
Print Assumptions fes_overlap_within_1_le6.
