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
   their outputs are nonoverlapping outright.  Totals 5 and 6 run through a
   block-layered state `bstate Q E L bs`: the running sum Q is a multiple of
   2^L, the errors so far expand to blocks bs, each below 2^L, already in
   aligned carry shape.  Three step lemmas move it one TwoSum on: no tie
   (`bstate_step`), a tie (`bstate_tie`), and the twin that absorbs a
   pending tie (`bstate_twin`); `bstate_top` packages the last step.  The
   rung files are untouched.

   PROVED HERE:
     overlap_within_1_of_aligned_shape  blocks with the two facts -> one bit
     fes_overlap_within_1_short         totals 0 .. 2
     fes_overlap_within_1_rung2 .. 5    totals 3 .. 6
     fes_overlap_within_1_le6           every total <= 6
     bstate_step / _tie / _twin / _top  the block-state ladder (also used
                                        by B64_CarryCleanSeven)

   NOT COVERED.  Seven or more components (total 7: B64_CarryCleanSeven).
   This is NOT Priest's bound or any general Fast-Expansion-Sum theorem: it
   is the n <= 6 instance only.

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
   The block-layered state.  After each TwoSum, the running sum Q is a
   multiple of 2^L and the errors so far, zeros dropped, expand an aligned
   carry-shaped block list whose keys all lie below 2^L.  Three steps keep
   it: no tie (`bstate_step`), the tie (`bstate_tie`), and the step after a
   pending twin (`bstate_twin`); anti pairs and singles need no special
   after-tie step.  `bstate_shape` reads off the final output.
   -------------------------------------------------------------------------- *)

Definition key_below (L : Z) (b : cblock) : Prop := block_key b < bpow radix2 L.

Definition push (h : binary64) (bs : list cblock) : list cblock :=
  if b64_is_zero h then bs else CSingle h :: bs.

Definition bstate (Q : binary64) (E : list binary64) (L : Z) (bs : list cblock) : Prop :=
  b64_fin Q /\ Forall b64_fin E /\ pow2_multiple L (b2r Q)
  /\ drop_zeros E = flat_map cblock_expand bs
  /\ carry_shape bs /\ pairs_aligned bs /\ Forall (key_below L) bs.

Lemma key_below_mono :
  forall L L' bs, (L <= L')%Z -> Forall (key_below L) bs -> Forall (key_below L') bs.
Proof.
  intros L L' bs HL H. eapply Forall_impl; [ | exact H ]. unfold key_below. intros b Hb.
  apply Rlt_le_trans with (1 := Hb). apply bpow_le, HL.
Qed.

Lemma key_below_min :
  forall a b bs, Forall (key_below a) bs -> Forall (key_below b) bs -> Forall (key_below (Z.min a b)) bs.
Proof.
  intros a b bs Ha Hb. destruct (Z.min_spec a b) as [[_ Hm] | [_ Hm]]; rewrite Hm; assumption.
Qed.

Lemma reduce_le_key :
  forall b, block_ok b -> Forall (fun y => Rabs (b2r y) <= block_key b) (cblock_reduce b).
Proof.
  intros [u | x | x] Hok; cbn [cblock_reduce block_key]; [ | | constructor ].
  - constructor; [ lra | constructor ].
  - destruct Hok as [[Fx _] Hov]. destruct (double_exact x Fx Hov) as [Hd _].
    constructor; [ rewrite Hd, Rabs_mult, (Rabs_pos_eq 2) by lra; lra | constructor ].
Qed.

Lemma reduce_below :
  forall L bs, Forall block_ok bs -> Forall (key_below L) bs -> Forall (below L) (flat_map cblock_reduce bs).
Proof.
  intros L bs Hok Hk. apply Forall_forall. intros y Hy.
  apply in_flat_map in Hy. destruct Hy as [b [Hb Hy]].
  rewrite Forall_forall in Hok, Hk.
  pose proof (reduce_le_key b (Hok b Hb)) as R. rewrite Forall_forall in R.
  pose proof (R y Hy). pose proof (Hk b Hb). unfold key_below in *. unfold below. lra.
Qed.

Lemma nonoverlap_cons_mult :
  forall L x l, pow2_multiple L (b2r x) -> Forall (below L) l -> nonoverlapping_chain l ->
    nonoverlapping_chain (x :: l).
Proof.
  intros L x [| y l] [n Hn] Hb Hl; [ exact I | ]. split; [ | exact Hl ].
  unfold nonoverlapping_b64, nonoverlapping_R, overlap_within. left. exists n, L.
  split; [ exact Hn | ]. rewrite Z.add_0_r. inversion Hb; assumption.
Qed.

Lemma anti_step_mult :
  forall L b b', pow2_multiple L (b2r (block_last b)) -> key_below L b' -> anti_step b b'.
Proof.
  intros L b [v | y | y] Hm Hk; try exact I. intros c Hc. unfold key_below in Hk. cbn [block_key] in Hk.
  rewrite Hc in Hk. apply lt_bpow in Hk. apply (pow2_multiple_le c L); [ lia | exact Hm ].
Qed.

(* Three ways to put a block on top of an aligned, carry-shaped stack. *)
Lemma cons_single :
  forall L x bs, b64_nz x -> pow2_multiple L (b2r x) ->
    carry_shape bs -> pairs_aligned bs -> Forall (key_below L) bs ->
    carry_shape (CSingle x :: bs) /\ pairs_aligned (CSingle x :: bs).
Proof.
  intros L x bs Nx Mx (Ok & Kd & No) Al Kb.
  assert (Hge : bpow radix2 L <= Rabs (b2r x))
    by (destruct Mx as [n Hn]; exact (scaled_nonzero_ge _ n L Hn (proj2 Nx))).
  split; [ split; [ | split ] | ].
  - constructor; assumption.
  - split; [ | exact Kd ]. destruct bs as [| b' r]; [ exact I | ].
    inversion Kb as [| ? ? Hk _]; subst. unfold key_below in Hk. cbn [block_key]. lra.
  - cbn [flat_map cblock_reduce app]. apply (nonoverlap_cons_mult L); [ exact Mx | | exact No ].
    apply reduce_below; assumption.
  - cbn [pairs_aligned]. split; [ exact I | split; [ | exact Al ] ].
    destruct bs as [| b' r]; [ exact I | ].
    inversion Kb as [| ? ? Hk _]; subst. exact (anti_step_mult L (CSingle x) b' Mx Hk).
Qed.

Lemma cons_twin :
  forall c x bs, b64_fin x -> Rabs (b2r x) = bpow radix2 c -> 2 * bpow radix2 c < bpow radix2 emax ->
    carry_shape bs -> pairs_aligned bs -> Forall (key_below c) bs ->
    carry_shape (CTwin x :: bs) /\ pairs_aligned (CTwin x :: bs).
Proof.
  intros c x bs Fx Hx Hov (Ok & Kd & No) Al Kb.
  pose proof (bpow_gt_0 radix2 c) as Hc0.
  assert (Nx : b64_nz x) by (split; [ exact Fx | intro H; rewrite H, Rabs_R0 in Hx; lra ]).
  assert (Hov' : 2 * Rabs (b2r x) < bpow radix2 emax) by (rewrite Hx; exact Hov).
  assert (Mx : pow2_multiple c (b2r x)) by (apply pow2_multiple_pm, Hx).
  split; [ split; [ | split ] | ].
  - constructor; [ split; assumption | exact Ok ].
  - split; [ | exact Kd ]. destruct bs as [| b' r]; [ exact I | ].
    inversion Kb as [| ? ? Hk _]; subst. unfold key_below in Hk. cbn [block_key]. lra.
  - cbn [flat_map cblock_reduce app]. apply (nonoverlap_cons_mult c); [ | | exact No ].
    + destruct (double_exact x Fx Hov') as [Hd _]. rewrite Hd. destruct Mx as [n Hn].
      exists (2 * n)%Z. rewrite Hn, mult_IZR. cbn [IZR IPR IPR_2]. ring.
    + apply reduce_below; assumption.
  - cbn [pairs_aligned]. split; [ exists c; exact Hx | split; [ | exact Al ] ].
    destruct bs as [| b' r]; [ exact I | ].
    inversion Kb as [| ? ? Hk _]; subst. exact (anti_step_mult c (CTwin x) b' Mx Hk).
Qed.

Lemma cons_anti :
  forall c x bs, b64_fin x -> Rabs (b2r x) = bpow radix2 c ->
    carry_shape bs -> pairs_aligned bs -> Forall (key_below c) bs ->
    carry_shape (CAnti x :: bs) /\ pairs_aligned (CAnti x :: bs).
Proof.
  intros c x bs Fx Hx (Ok & Kd & No) Al Kb.
  pose proof (bpow_gt_0 radix2 c) as Hc0.
  assert (Nx : b64_nz x) by (split; [ exact Fx | intro H; rewrite H, Rabs_R0 in Hx; lra ]).
  assert (Mx : pow2_multiple c (b2r (b64_neg x)))
    by (apply pow2_multiple_pm; rewrite b64_neg_R, Rabs_Ropp; exact Hx).
  split; [ split; [ | split ] | ].
  - constructor; [ exact Nx | exact Ok ].
  - split; [ | exact Kd ]. destruct bs as [| b' r]; [ exact I | ].
    inversion Kb as [| ? ? Hk _]; subst. unfold key_below in Hk. cbn [block_key]. lra.
  - exact No.
  - cbn [pairs_aligned]. split; [ exists c; exact Hx | split; [ | exact Al ] ].
    destruct bs as [| b' r]; [ exact I | ].
    inversion Kb as [| ? ? Hk _]; subst. exact (anti_step_mult c (CAnti x) b' Mx Hk).
Qed.

Lemma drop_zeros_push :
  forall h E bs, drop_zeros E = flat_map cblock_expand bs ->
    drop_zeros (h :: E) = flat_map cblock_expand (push h bs).
Proof.
  intros h E bs H. unfold push. destruct (b64_is_zero h) eqn:Hz.
  - rewrite drop_zeros_cons_zero by exact Hz. exact H.
  - rewrite drop_zeros_cons_nz by exact Hz. cbn [flat_map cblock_expand app]. rewrite H. reflexivity.
Qed.

Lemma push_nz : forall h bs, b64_fin h -> b2r h <> 0 -> push h bs = CSingle h :: bs.
Proof. intros h bs Fh Hh. unfold push. rewrite (b64_is_zero_false h Fh Hh). reflexivity. Qed.

Lemma key_below_push :
  forall L h bs, Rabs (b2r h) < bpow radix2 L -> Forall (key_below L) bs -> Forall (key_below L) (push h bs).
Proof.
  intros L h bs Hh Hb. unfold push. destruct (b64_is_zero h); [ exact Hb | constructor; assumption ].
Qed.

(* Pushing a fresh error h, a multiple of 2^c over a stack below 2^c. *)
Lemma bstate_push :
  forall Q h E bs L c,
    b64_fin Q -> b64_fin h -> Forall b64_fin E -> pow2_multiple L (b2r Q) ->
    drop_zeros E = flat_map cblock_expand bs -> carry_shape bs -> pairs_aligned bs ->
    Forall (key_below c) bs -> pow2_multiple c (b2r h) -> Rabs (b2r h) < bpow radix2 L -> (c <= L)%Z ->
    bstate Q (h :: E) L (push h bs).
Proof.
  intros Q h E bs L c FQ Fh FE MQ DE Sh Al Kc Mh Hh HcL.
  refine (conj FQ (conj (Forall_cons _ Fh FE) (conj MQ (conj (drop_zeros_push h E bs DE) _)))).
  assert (KL : Forall (key_below L) bs) by exact (key_below_mono c L bs HcL Kc).
  unfold push. destruct (b64_is_zero h) eqn:Hz.
  - split; [ exact Sh | split; [ exact Al | exact KL ] ].
  - destruct (cons_single c h bs (b64_nz_of_not_zero h Fh Hz) Mh Sh Al Kc) as [S' A'].
    split; [ exact S' | split; [ exact A' | constructor; [ exact Hh | exact KL ] ] ].
Qed.

Lemma bstate_init : forall g, b64_fin g -> bstate g [] (cexp radix2 b64_fexp (b2r g)) [].
Proof.
  intros g Fg. repeat split; try constructor; try exact I; try reflexivity; try assumption.
  apply b64_pow2_multiple_cexp.
Qed.

(* The final output Q :: E. *)
Lemma bstate_shape :
  forall Q E L bs, bstate Q E L bs ->
    exists bs', drop_zeros (Q :: E) = flat_map cblock_expand bs' /\ carry_shape bs' /\ pairs_aligned bs'.
Proof.
  intros Q E L bs (FQ & FE & MQ & DE & Sh & Al & Kb).
  exists (push Q bs). split; [ exact (drop_zeros_push Q E bs DE) | ].
  unfold push. destruct (b64_is_zero Q) eqn:Hz; [ split; assumption | ].
  exact (cons_single L Q bs (b64_nz_of_not_zero Q FQ Hz) MQ Sh Al Kb).
Qed.

(* STEP 1, no tie: every block so far lies below ulp(g). *)
Lemma bstate_step :
  forall Q E L bs g,
    bstate Q E L bs -> b64_fin g -> b64_TwoSum_safe g Q ->
    Forall (key_below (cexp radix2 b64_fexp (b2r g))) bs ->
    let Q' := fst (b64_TwoSum g Q) in
    let h := snd (b64_TwoSum g Q) in
    let c := Z.min (cexp radix2 b64_fexp (b2r g)) L in
    bstate Q' (h :: E) (Z.max c (cexp radix2 b64_fexp (b2r Q'))) (push h bs)
    /\ Forall (key_below c) bs.
Proof.
  intros Q E L bs g (FQ & FE & MQ & DE & Sh & Al & Kb) Fg S Kg Q' h c.
  destruct (ts_facts g Q S) as (FQ' & Fh & RQ' & Hex & Hno & _). fold Q' h in FQ', Fh, RQ', Hex, Hno.
  assert (Mg : pow2_multiple c (b2r g))
    by (apply (pow2_multiple_le _ _ _ (Z.le_min_l _ _)), b64_pow2_multiple_cexp).
  assert (MQc : pow2_multiple c (b2r Q)) by (apply (pow2_multiple_le _ _ _ (Z.le_min_r _ _)), MQ).
  assert (MQ' : pow2_multiple c (b2r Q'))
    by (rewrite RQ'; apply round_pow2_multiple, pow2_multiple_plus; assumption).
  assert (Mh : pow2_multiple c (b2r h)).
  { replace (b2r h) with ((b2r g + b2r Q) - b2r Q') by lra.
    apply pow2_multiple_minus; [ apply pow2_multiple_plus | ]; assumption. }
  assert (Kc : Forall (key_below c) bs) by (apply key_below_min; assumption).
  unfold strict_succ_b64 in Hno. pose proof (half_ulp_below Q' h Hno) as Hh.
  split; [ | exact Kc ].
  apply (bstate_push Q' h E bs _ c); try assumption.
  - destruct (Z.max_spec c (cexp radix2 b64_fexp (b2r Q'))) as [[_ Hm] | [_ Hm]];
      rewrite Hm; [ apply b64_pow2_multiple_cexp | exact MQ' ].
  - apply Rlt_le_trans with (1 := Hh); apply bpow_le, Z.le_max_r.
  - apply Z.le_max_l.
Qed.

(* STEP 2, the tie: Q = s 2^M and the newest error h = s 2^c sit at a
   midpoint for g.  Anti pair, a pending twin (Q' = h), or a single. *)
Lemma bstate_tie :
  forall (g Q h : binary64) (E0 : list binary64) (bs0 : list cblock) (s : R),
    b64_fin g -> b64_TwoSum_safe g Q -> (s = 1 \/ s = -1) ->
    let c := cexp radix2 b64_fexp (b2r g) in
    let M := mag radix2 (b2r g) in
    b2r g <> 0 -> (2 <= M - c)%Z -> b64_fexp (M + 1) = (c + 1)%Z ->
    b2r Q = s * bpow radix2 M -> b2r h = s * bpow radix2 c ->
    bpow radix2 M - 2 * bpow radix2 c <= Rabs (b2r g) ->
    b64_fin h -> Forall b64_fin E0 -> drop_zeros E0 = flat_map cblock_expand bs0 ->
    carry_shape bs0 -> pairs_aligned bs0 -> Forall (key_below c) bs0 ->
    let Q' := fst (b64_TwoSum g Q) in
    let h' := snd (b64_TwoSum g Q) in
       bstate Q' (h' :: h :: E0) M (CAnti h' :: bs0)
    \/ (b2r h' = 0 /\ Q' = h)
    \/ bstate Q' (h' :: h :: E0) (c + 1) (CSingle h :: bs0).
Proof.
  intros g Q h E0 bs0 s Fg S Hs c M Hg0 HMc HfM HQ Hh Hgl Fh FE DE Sh Al Kb Q' h'.
  pose proof (tie_values g Q s Fg S Hs Hg0 HMc HfM HQ Hgl) as TV. cbv zeta in TV. fold c M Q' h' in TV.
  destruct (ts_facts g Q S) as (FQ' & Fh' & _ & _ & _ & _). fold Q' h' in FQ', Fh'.
  pose proof (bpow_gt_0 radix2 c) as Hc0.
  assert (Hhc : Rabs (b2r h) = bpow radix2 c) by (rewrite Hh; apply abs_sign; [ exact Hs | lra ]).
  assert (Hh0 : b2r h <> 0) by (intro H; rewrite H, Rabs_R0 in Hhc; lra).
  assert (HcM : bpow radix2 c < bpow radix2 M) by (apply bpow_lt; lia).
  destruct TV as [(Ha & HQ') | [(Hz & HQ') | (Hz & MQ' & NQ')]].
  - left.
    assert (Hac : Rabs (b2r h') = bpow radix2 c) by (rewrite Ha, Rabs_Ropp, <- Hh; exact Hhc).
    assert (Ha0 : b2r h' <> 0) by (intro H; rewrite H, Rabs_R0 in Hac; lra).
    assert (Eh : h = b64_neg h').
    { apply b64_eq_of_R; [ exact Fh | apply b64_neg_fin, Fh' | rewrite b64_neg_R, Ha; lra | exact Hh0 ]. }
    destruct (cons_anti c h' bs0 Fh' Hac Sh Al Kb) as [S' A'].
    refine (conj FQ' (conj _ (conj _ (conj _ (conj S' (conj A' _)))))).
    + repeat constructor; assumption.
    + rewrite HQ'. destruct Hs as [-> | ->]; [ exists 2%Z | exists (-2)%Z ]; cbn [IZR IPR IPR_2]; ring.
    + rewrite (drop_zeros_cons_nz h') by (apply b64_is_zero_false; assumption).
      rewrite (drop_zeros_cons_nz h) by (apply b64_is_zero_false; assumption).
      rewrite DE, Eh. reflexivity.
    + constructor; [ unfold key_below; cbn [block_key]; lra | ].
      apply (key_below_mono c); [ lia | exact Kb ].
  - right; left. split; [ exact Hz | ].
    apply b64_eq_of_R; [ exact FQ' | exact Fh | rewrite HQ', Hh; reflexivity | rewrite HQ', <- Hh; exact Hh0 ].
  - right; right.
    assert (Mh : pow2_multiple c (b2r h)) by (apply pow2_multiple_pm, Hhc).
    destruct (cons_single c h bs0 (conj Fh Hh0) Mh Sh Al Kb) as [S' A'].
    refine (conj FQ' (conj _ (conj MQ' (conj _ (conj S' (conj A' _)))))).
    + repeat constructor; assumption.
    + rewrite (drop_zeros_cons_zero h') by (apply b64_is_zero_true; assumption).
      rewrite (drop_zeros_cons_nz h) by (apply b64_is_zero_false; assumption).
      rewrite DE. reflexivity.
    + assert (H2c : bpow radix2 c < bpow radix2 (c + 1)) by (apply bpow_lt; lia).
      constructor; [ unfold key_below; cbn [block_key]; lra | ].
      apply (key_below_mono c); [ lia | exact Kb ].
Qed.

(* STEP 3a, after a pending twin (Q = h at 2^c): g absorbs Q, the twin
   (h', h) settles below g. *)
Lemma bstate_twin :
  forall (g Q z h : binary64) (E0 : list binary64) (bs0 : list cblock) (c : Z),
    b64_fin g -> b2r g <> 0 -> b64_TwoSum_safe g Q -> b64_fin z -> b64_fin h -> Forall b64_fin E0 ->
    b2r z = 0 -> Q = h -> Rabs (b2r h) = bpow radix2 c ->
    bpow radix2 c < ulp radix2 b64_fexp (b2r g) / 4 ->
    2 * bpow radix2 c < bpow radix2 emax ->
    drop_zeros E0 = flat_map cblock_expand bs0 ->
    carry_shape bs0 -> pairs_aligned bs0 -> Forall (key_below c) bs0 ->
    let Q' := fst (b64_TwoSum g Q) in
    let h' := snd (b64_TwoSum g Q) in
    bstate Q' (h' :: z :: h :: E0) (cexp radix2 b64_fexp (b2r g)) (CTwin h :: bs0).
Proof.
  intros g Q z h E0 bs0 c Fg Hg0 S Fz Fh FE Hz HQh Hh Hsmall Hov DE Sh Al Kb Q' h'.
  destruct (ts_facts g Q S) as (FQ' & Fh' & RQ' & Hex & _ & _). fold Q' h' in FQ', Fh', RQ', Hex.
  pose proof (bpow_gt_0 radix2 c) as Hc0. subst Q.
  assert (Hh0 : b2r h <> 0) by (intro H; rewrite H, Rabs_R0 in Hh; lra).
  assert (HQ' : b2r Q' = b2r g) by (rewrite RQ'; apply rn_absorb; [ exact Hg0 | rewrite Hh; exact Hsmall ]).
  assert (Hh' : b2r h' = b2r h) by lra.
  assert (Eh : h' = h) by (apply b64_eq_of_R; [ exact Fh' | exact Fh | exact Hh' | rewrite Hh'; exact Hh0 ]).
  assert (Hue : ulp radix2 b64_fexp (b2r g) = bpow radix2 (cexp radix2 b64_fexp (b2r g))) by (apply ulp_neq_0, Hg0).
  destruct (cons_twin c h bs0 Fh Hh Hov Sh Al Kb) as [S' A'].
  refine (conj FQ' (conj _ (conj _ (conj _ (conj S' (conj A' _)))))).
  - repeat constructor; assumption.
  - rewrite HQ'. apply b64_pow2_multiple_cexp.
  - rewrite Eh. rewrite (drop_zeros_cons_nz h) by (apply b64_is_zero_false; assumption).
    rewrite (drop_zeros_cons_zero z) by (apply b64_is_zero_true; assumption).
    rewrite (drop_zeros_cons_nz h) by (apply b64_is_zero_false; assumption).
    rewrite DE. reflexivity.
  - constructor.
    + unfold key_below. cbn [block_key]. rewrite <- Hue, Hh. lra.
    + eapply Forall_impl; [ | exact Kb ]. unfold key_below. intros b Hb. rewrite <- Hue. lra.
Qed.

(* STEP 3b, a pending twin at the top of the output. *)
Lemma twin_top_shape :
  forall (Q z h : binary64) (E0 : list binary64) (bs0 : list cblock) (c : Z),
    b64_fin z -> b64_fin h -> b2r z = 0 -> Q = h -> Rabs (b2r h) = bpow radix2 c ->
    2 * bpow radix2 c < bpow radix2 emax ->
    drop_zeros E0 = flat_map cblock_expand bs0 ->
    carry_shape bs0 -> pairs_aligned bs0 -> Forall (key_below c) bs0 ->
    exists bs, drop_zeros (Q :: z :: h :: E0) = flat_map cblock_expand bs
               /\ carry_shape bs /\ pairs_aligned bs.
Proof.
  intros Q z h E0 bs0 c Fz Fh Hz HQh Hh Hov DE Sh Al Kb. subst Q.
  pose proof (bpow_gt_0 radix2 c) as Hc0.
  assert (Hh0 : b2r h <> 0) by (intro H; rewrite H, Rabs_R0 in Hh; lra).
  exists (CTwin h :: bs0). split; [ | exact (cons_twin c h bs0 Fh Hh Hov Sh Al Kb) ].
  rewrite (drop_zeros_cons_nz h) by (apply b64_is_zero_false; assumption).
  rewrite (drop_zeros_cons_zero z) by (apply b64_is_zero_true; assumption).
  rewrite (drop_zeros_cons_nz h) by (apply b64_is_zero_false; assumption).
  rewrite DE. reflexivity.
Qed.

Lemma bpre_step :
  forall K h bs g, Forall (key_below K) bs -> (K <= cexp radix2 b64_fexp (b2r g))%Z ->
    Rabs (b2r h) < bpow radix2 (cexp radix2 b64_fexp (b2r g)) ->
    Forall (key_below (cexp radix2 b64_fexp (b2r g))) (push h bs).
Proof. intros K h bs g Hb HK Hh. apply key_below_push; [ exact Hh | exact (key_below_mono K _ bs HK Hb) ]. Qed.


(* --------------------------------------------------------------------------
   The top step.  The last TwoSum of a chain may meet an incoming error that
   ties ulp(g); `tie_analysis` (rung 4) allows a partner up to 3 ulp(g), the
   wide form below up to 4 ulp(g), which the seventh step needs.
   -------------------------------------------------------------------------- *)

(* A tie at the top is still the canonical one when |y| < 4 ulp(g). *)
Lemma tie_analysis_wide :
  forall (g : binary64) (x y : R),
    b2r g <> 0 -> Rabs x <= Rabs (b2r g) ->
    Rabs y < 4 * ulp radix2 b64_fexp (b2r g) ->
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
  assert (Hz : Rabs z < bpow radix2 M + 3 * bpow radix2 c)
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
  assert (Hzu : Rabs z < (IZR N + 3 / 2) * bpow radix2 ez) by lra.
  assert (Hzl : IZR N * bpow radix2 ez <= Rabs z) by lra.
  rewrite Hn, Rabs_mult, (Rabs_pos_eq (bpow radix2 ez)) in Hzu, Hzl by lra.
  apply Rmult_lt_reg_r in Hzu; [ | exact He0 ].
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

(* Half-units j * 2^(c-1), j <= 7, are representable above the subnormal floor. *)
Lemma fmt_half_units :
  forall (c j : Z), (3 - emax - prec < c)%Z -> (0 < j <= 7)%Z ->
    generic_format radix2 b64_fexp (IZR j * bpow radix2 (c - 1)).
Proof.
  intros c j Hc Hj.
  apply (fmt_scaled j (c - 1) (c + 2)).
  - rewrite Rabs_mult, (Rabs_pos_eq (bpow _ _)) by (left; apply bpow_gt_0).
    rewrite Rabs_pos_eq by (apply IZR_le; lia).
    replace (bpow radix2 (c + 2)) with (8 * bpow radix2 (c - 1))
      by (replace (c + 2)%Z with ((c - 1) + 3)%Z by ring; rewrite bpow_plus; change (bpow radix2 3) with 8; ring).
    pose proof (bpow_gt_0 radix2 (c - 1)). assert (IZR j <= 7) by (apply IZR_le; lia). nra.
  - unfold SpecFloat.fexp, SpecFloat.emin. unfold prec in *. lia.
Qed.

(* THE TOP STEP: the last TwoSum of a chain, whose incoming error h may tie
   ulp(g).  The block state below h must already sit under ulp(g). *)
Lemma bstate_top :
  forall (g Q h Q' h' : binary64) (E0 : list binary64) (bs0 : list cblock) (L : Z) (x y : R),
    b64_fin g -> b2r g <> 0 -> b64_TwoSum_safe g Q -> b64_TwoSum g Q = (Q', h') ->
    bstate Q (h :: E0) L (push h bs0) ->
    Forall b64_fin E0 -> drop_zeros E0 = flat_map cblock_expand bs0 ->
    carry_shape bs0 -> pairs_aligned bs0 ->
    Forall (key_below (cexp radix2 b64_fexp (b2r g))) bs0 ->
    Rabs x <= Rabs (b2r g) -> Rabs y <= 7 / 2 * ulp radix2 b64_fexp (b2r g) ->
    b2r Q = RN (x + y) -> b2r Q + b2r h = x + y ->
    2 * ulp radix2 b64_fexp (b2r g) < bpow radix2 emax ->
    exists bs, drop_zeros (Q' :: h' :: h :: E0) = flat_map cblock_expand bs
               /\ carry_shape bs /\ pairs_aligned bs.
Proof.
  intros g Q h Q' h' E0 bs0 L x y Fg Hg0 S Heq St FE DE Sh Al Kb Hx Hy RQ Hex Hov.
  assert (Hu0 : 0 < ulp radix2 b64_fexp (b2r g)) by (rewrite ulp_neq_0 by exact Hg0; apply bpow_gt_0).
  pose proof (tie_analysis_wide g x y Hg0 Hx ltac:(lra)) as Tie.
  cbv zeta in Tie. rewrite <- RQ in Tie. destruct Tie as [Bnd Tie].
  assert (Eh : Rabs (b2r Q - (x + y)) = Rabs (b2r h)).
  { replace (b2r Q - (x + y)) with (- b2r h) by lra. apply Rabs_Ropp. }
  rewrite Eh in Bnd, Tie.
  set (c := cexp radix2 b64_fexp (b2r g)) in *.
  assert (Hu : ulp radix2 b64_fexp (b2r g) = bpow radix2 c) by (apply ulp_neq_0, Hg0).
  rewrite Hu in Hy, Hov.
  pose proof (bpow_gt_0 radix2 c) as Hc0.
  pose proof St as (FQ & FEh & _ & _ & _ & _ & _).
  inversion FEh as [| ? ? Fh _]; subst.
  destruct (Req_dec (Rabs (b2r h)) (bpow radix2 c)) as [Ht | Hnt].
  - destruct (Tie Ht) as (HMc & HfM & Hz).
    set (M := mag radix2 (b2r g)) in *.
    pose proof (bpow_gt_0 radix2 M) as HB.
    assert (Hsign : exists s : R, (s = 1 \/ s = -1) /\ b2r Q = s * bpow radix2 M
                                  /\ b2r h = s * bpow radix2 c).
    { destruct Hz as [[Hz HQ] | [Hz HQ]].
      - exists 1. split; [ left; reflexivity | split; lra ].
      - exists (-1). split; [ right; reflexivity | split; lra ]. }
    destruct Hsign as (s & Hs & HQs & Hhs).
    assert (Hgl : bpow radix2 M - 2 * bpow radix2 c <= Rabs (b2r g)).
    { destruct (b64_pow2_multiple_cexp g) as [n Hn].
      apply (mult_gap _ n c M Hn ltac:(lia)).
      pose proof (Rabs_triang_inv (x + y) y) as Ht'.
      replace (x + y - y) with x in Ht' by ring.
      destruct Hz as [[Hz _] | [Hz _]]; rewrite Hz in Ht';
        [ rewrite Rabs_pos_eq in Ht' by lra | rewrite Rabs_Ropp, Rabs_pos_eq in Ht' by lra ]; lra. }
    pose proof (bstate_tie g Q h E0 bs0 s Fg S Hs Hg0 HMc HfM HQs Hhs Hgl Fh FE DE Sh Al Kb) as TS.
    cbv zeta in TS. rewrite Heq in TS. cbn [fst snd] in TS.
    pose proof (ts_facts g Q S) as T. rewrite Heq in T. cbn [fst snd] in T.
    destruct T as (_ & Fh' & _ & _ & _ & _).
    destruct TS as [St' | [(Hz' & HQh) | St']].
    + exact (bstate_shape _ _ _ _ St').
    + exact (twin_top_shape Q' h' h E0 bs0 c Fh' Fh Hz' HQh Ht Hov DE Sh Al Kb).
    + exact (bstate_shape _ _ _ _ St').
  - assert (P : Forall (key_below c) (push h bs0)) by (apply key_below_push; [ lra | exact Kb ]).
    pose proof (bstate_step _ _ _ _ g St Fg S P) as [St' _].
    cbv zeta in St'. rewrite Heq in St'. cbn [fst snd] in St'.
    exact (bstate_shape _ _ _ _ St').
Qed.

(* RN of a value below j half-units of 2^c stays within j half-units. *)
Lemma rn_le_half_units :
  forall (c j : Z) (z : R), (3 - emax - prec < c)%Z -> (0 < j <= 7)%Z ->
    Rabs z <= IZR j * bpow radix2 (c - 1) -> Rabs (RN z) <= IZR j * bpow radix2 (c - 1).
Proof.
  intros c j z Hc Hj Hz.
  exact (abs_round_le_generic radix2 b64_fexp (BinarySingleNaN.round_mode mode_b64) _ _
           (fmt_half_units c j Hc Hj) Hz).
Qed.


(* --------------------------------------------------------------------------
   Rung 4 through the block state.
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
  intros g1 g2 g3 g4 g5 F1 F2 F3 F4 F5 Hsafe H34 H45 Hov5 (N3 & N4 & N5 & K1 & K2 & K3).
  cbn [cascade_safe] in Hsafe. destruct Hsafe as [S2 [S3 [S4 [S5 _]]]].
  unfold fes5. cbn [b64_grow_expansion_aux].
  (* step 2 *)
  pose proof (bstate_step _ _ _ _ g2 (bstate_init g1 F1) F2 S2 (Forall_nil _)) as [St2 _].
  pose proof (ts_facts g2 g1 S2) as T2. cbv zeta in St2, T2.
  destruct (b64_TwoSum g2 g1) as [Q2 h2] eqn:E2. cbn [fst snd] in St2, T2, S3, S4, S5.
  destruct T2 as (FQ2 & Fh2 & RQ2 & Hex2 & _ & _).
  (* step 3: h2 below ulp(g3) *)
  assert (Hh2 : Rabs (b2r h2) <= Rabs (b2r g1)).
  { replace (b2r h2) with (- (RN (b2r g2 + b2r g1) - (b2r g2 + b2r g1))) by (rewrite <- RQ2; lra).
    rewrite Rabs_Ropp. apply round_N_err_le_operand, Binary.generic_format_B2R. }
  assert (P3 : Forall (key_below (cexp radix2 b64_fexp (b2r g3))) (push h2 [])).
  { apply key_below_push; [ apply below_of_ulp; [ exact N3 | lra ] | constructor ]. }
  pose proof (bstate_step _ _ _ _ g3 St2 F3 S3 P3) as [St3 Kb3].
  pose proof (ts_facts g3 Q2 S3) as T3. cbv zeta in St3, Kb3, T3.
  destruct (b64_TwoSum g3 Q2) as [Q3 h3] eqn:E3. cbn [fst snd] in St3, T3, S4, S5.
  destruct T3 as (FQ3 & Fh3 & RQ3 & Hex3 & _ & _).
  (* step 4: h3 below ulp(g4) *)
  pose proof (ulp_mono _ _ H34) as U34. pose proof (ulp_mono _ _ H45) as U45.
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
  destruct (b64_TwoSum g4 Q3) as [Q4 h4] eqn:E4. cbn [fst snd] in St4, T4, S5.
  destruct T4 as (FQ4 & Fh4 & RQ4 & Hex4 & _ & _).
  set (c4 := Z.min (cexp radix2 b64_fexp (b2r g4)) _) in Kb4.
  assert (Hc4 : (c4 <= cexp radix2 b64_fexp (b2r g4))%Z) by apply Z.le_min_l.
  (* step 5, the top: h4 is at most ulp(g5) and may tie it *)
  assert (HQ3 : Rabs (b2r Q3) <= 3 * ulp radix2 b64_fexp (b2r g5)).
  { rewrite RQ3. change 3 with (IZR 3).
    apply (abs_round_le_generic radix2 b64_fexp (BinarySingleNaN.round_mode mode_b64) _ _
             (fmt_k_ulp g5 3 N5 ltac:(lia))).
    pose proof (Rabs_triang (b2r g3) (b2r Q2)). cbn [IZR IPR IPR_2]. lra. }
  pose proof (ulp_ge_0 radix2 b64_fexp (b2r g5)) as Hu5.
  pose proof (ulp_le_abs_b64 g5 N5) as Hg5u.
  assert (Hov5' : 2 * ulp radix2 b64_fexp (b2r g5) < bpow radix2 emax).
  { assert (8 * bpow radix2 (emax - 5) <= bpow radix2 emax).
    { replace (bpow radix2 emax) with (bpow radix2 ((emax - 5) + 5)) by (f_equal; ring).
      rewrite bpow_plus. change (bpow radix2 5) with 32. pose proof (bpow_gt_0 radix2 (emax - 5)). lra. }
    pose proof (bpow_gt_0 radix2 (emax - 5)). lra. }
  pose proof St3 as (_ & FE3 & _ & DE3 & Sh3 & Al3 & _).
  assert (Kb4' : Forall (key_below (cexp radix2 b64_fexp (b2r g5))) (push h3 (push h2 []))).
  { apply (key_below_mono c4); [ | exact Kb4 ].
    apply (Z.le_trans _ _ _ Hc4). apply cexp_mono_nz; assumption. }
  destruct (b64_TwoSum g5 Q4) as [Q5 h5] eqn:E5.
  exact (bstate_top g5 Q4 h4 Q5 h5 _ _ _ (b2r g4) (b2r Q3) F5 N5 S5 E5 St4 FE3 DE3 Sh3 Al3 Kb4'
           H45 ltac:(lra) RQ4 Hex4 Hov5').
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
   Rung 5 through the block state.
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
  pose proof (bstate_step _ _ _ _ g2 (bstate_init g1 F1) F2 S2 (Forall_nil _)) as [St2 _].
  pose proof (ts_facts g2 g1 S2) as T2. cbv zeta in St2, T2.
  destruct (b64_TwoSum g2 g1) as [Q2 h2] eqn:E2. cbn [fst snd] in St2, T2, S3, S4, S5, S6.
  destruct T2 as (FQ2 & Fh2 & RQ2 & Hex2 & _ & _).
  (* step 3: h2 below ulp(g3) *)
  assert (Hh2 : Rabs (b2r h2) <= Rabs (b2r g1)).
  { replace (b2r h2) with (- (RN (b2r g2 + b2r g1) - (b2r g2 + b2r g1))) by (rewrite <- RQ2; lra).
    rewrite Rabs_Ropp. apply round_N_err_le_operand, Binary.generic_format_B2R. }
  assert (P3 : Forall (key_below (cexp radix2 b64_fexp (b2r g3))) (push h2 [])).
  { apply key_below_push; [ apply below_of_ulp; [ exact N3 | lra ] | constructor ]. }
  pose proof (bstate_step _ _ _ _ g3 St2 F3 S3 P3) as [St3 Kb3].
  pose proof (ts_facts g3 Q2 S3) as T3. cbv zeta in St3, Kb3, T3.
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
  assert (P4 : Forall (key_below (cexp radix2 b64_fexp (b2r g4))) (push h3 (push h2 []))).
  { apply (bpre_step _ h3 _ g4 Kb3); [ | apply below_of_ulp; assumption ].
    apply Z.le_trans with (cexp radix2 b64_fexp (b2r g3)); [ apply Z.le_min_l | apply cexp_mono_nz; assumption ]. }
  pose proof (bstate_step _ _ _ _ g4 St3 F4 S4 P4) as [St4 Kb4].
  pose proof (ts_facts g4 Q3 S4) as T4. cbv zeta in St4, Kb4, T4.
  destruct (b64_TwoSum g4 Q3) as [Q4 h4] eqn:E4. cbn [fst snd] in St4, T4, S5, S6.
  destruct T4 as (FQ4 & Fh4 & RQ4 & Hex4 & _ & _).
  set (c4 := Z.min (cexp radix2 b64_fexp (b2r g4)) _) in Kb4.
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
  destruct St3 as (_ & FE3 & _ & DE3 & Sh3 & Al3 & _).
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
    assert (Hsign : exists s : R, (s = 1 \/ s = -1) /\ b2r Q4 = s * bpow radix2 M5
                                  /\ b2r h4 = s * bpow radix2 c5).
    { destruct Hz as [[Hz HQ] | [Hz HQ]].
      - exists 1. split; [ left; reflexivity | split; lra ].
      - exists (-1). split; [ right; reflexivity | split; lra ]. }
    destruct Hsign as (s & Hs & HQ4 & Hh4s).
    assert (Hg5l : bpow radix2 M5 - 2 * bpow radix2 c5 <= Rabs (b2r g5)) by (unfold b64_abs_le in H45; lra).
    assert (Kb4' : Forall (key_below c5) (push h3 (push h2 []))) by (apply (key_below_mono c4); [ lia | exact Kb4 ]).
    pose proof (bstate_tie g5 Q4 h4 [h3; h2] _ s F5 S5 Hs N5 HMc HfM HQ4 Hh4s Hg5l Fh4 FE3 DE3 Sh3 Al3 Kb4') as TS.
    cbv zeta in TS. fold M5 c5 in TS.
    destruct (b64_TwoSum g5 Q4) as [Q5 h5] eqn:E5. cbn [fst snd] in TS, S6.
    destruct TS as [St5 | [(Hz5 & HQh) | St5]].
    + (* anti pair (h5, h4); g6 sits above it *)
      assert (P6 : Forall (key_below c6) (CAnti h5 :: push h3 (push h2 [])))
        by (destruct St5 as (_ & _ & _ & _ & _ & _ & K5); apply (key_below_mono M5); [ exact Hc6M | exact K5 ]).
      pose proof (bstate_step _ _ _ _ g6 St5 F6 S6 P6) as [St6 _]. cbv zeta in St6.
      exact (bstate_shape _ _ _ _ St6).
    + (* twin (Q5, h4), h5 = 0: g6 absorbs Q5 *)
      pose proof (ts_facts g5 Q4 S5) as T5. rewrite E5 in T5. cbn [fst snd] in T5.
      destruct T5 as (_ & Fh5 & _ & _ & _ & _).
      assert (Hh4u : Rabs (b2r h4) = bpow radix2 c5) by exact Tie.
      assert (Hq : bpow radix2 c5 < ulp radix2 b64_fexp (b2r g6) / 4).
      { rewrite Hu6. assert (bpow radix2 (c5 + 2) < bpow radix2 c6) by (apply bpow_lt; lia).
        rewrite bpow_plus in H. change (bpow radix2 2) with 4 in H. lra. }
      pose proof (bstate_twin g6 Q5 h5 h4 [h3; h2] _ c5 F6 N6 S6 Fh5 Fh4 FE3 Hz5 HQh Hh4u Hq Hov5
                   DE3 Sh3 Al3 Kb4') as St6.
      exact (bstate_shape _ _ _ _ St6).
    + (* single h4; the state stays layered at level c5 + 1 *)
      assert (P6 : Forall (key_below c6) (CSingle h4 :: push h3 (push h2 [])))
        by (destruct St5 as (_ & _ & _ & _ & _ & _ & K5); apply (key_below_mono (c5 + 1)); [ lia | exact K5 ]).
      pose proof (bstate_step _ _ _ _ g6 St5 F6 S6 P6) as [St6 _]. cbv zeta in St6.
      exact (bstate_shape _ _ _ _ St6).
  - (* NO TIE AT STEP 5 *)
    assert (Hh4lt : Rabs (b2r h4) < bpow radix2 c5) by lra.
    assert (P5 : Forall (key_below c5) (push h4 (push h3 (push h2 [])))).
    { apply (bpre_step c4 h4 _ g5 Kb4); [ lia | exact Hh4lt ]. }
    pose proof St4 as St4'.
    pose proof (bstate_step _ _ _ _ g5 St4 F5 S5 P5) as [St5 Kb5].
    pose proof (ts_facts g5 Q4 S5) as T5. cbv zeta in St5, Kb5, T5.
    destruct (b64_TwoSum g5 Q4) as [Q5 h5] eqn:E5. cbn [fst snd] in St5, T5, S6.
    fold c5 in St5, Kb5.
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
    (* step 6, the top *)
    assert (Kb5' : Forall (key_below c6) (push h4 (push h3 (push h2 []))))
      by (refine (key_below_mono _ c6 _ _ Kb5); lia).
    assert (Hov6' : 2 * ulp radix2 b64_fexp (b2r g6) < bpow radix2 emax).
    { assert (bpow radix2 c6 <= Rabs (b2r g6)) by (rewrite <- Hu6; apply ulp_le_abs_b64, N6).
      assert (8 * bpow radix2 (emax - 5) <= bpow radix2 emax).
      { replace (bpow radix2 emax) with (bpow radix2 ((emax - 5) + 5)) by (f_equal; ring).
        rewrite bpow_plus. change (bpow radix2 5) with 32. pose proof (bpow_gt_0 radix2 (emax - 5)). lra. }
      rewrite Hu6. pose proof (bpow_gt_0 radix2 (emax - 5)). lra. }
    destruct St4' as (_ & FE4 & _ & DE4 & Sh4 & Al4 & _).
    destruct (b64_TwoSum g6 Q5) as [Q6 h6] eqn:E6.
    exact (bstate_top g6 Q5 h5 Q6 h6 _ _ _ (b2r g5) (b2r Q4) F6 N6 S6 E6 St5 FE4 DE4 Sh4 Al4 Kb5'
             H56 ltac:(lra) RQ5 Hex5 Hov6').
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
