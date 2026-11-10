(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_CarryCleanTailBound
   ----------------------------------------------------------------------------
   binary64 realization of the cascade tail bound: the actual
   b64_grow_expansion_aux on sort_by_abs (e ++ f) runs the FLX cascade of
   B64_CarryCleanTailModel.v, so its bounds hold with binary64 ulp.  All Qed.
   Promoted from the probe lane (second half of
   docs/h1-vacuity/CascadeTailBound.v, PR #1012) for #1015; split from
   B64_CarryCleanTailModel.v by the module split gate, declarations
   byte-identical.

   PROVED HERE
     b64_cascade_tail_bound, b64_closed_lookahead, fes_output_error_bound:
       priest_chain e, f, finite nonzero components and
       abs_sum e + abs_sum f <= 2^(emax-5).
     Bridge: b64_RN_agree (binary64 RN = FLX RN on every sum of two binary64
       values; below the subnormal threshold the sum is exact), ulp_X_le_64,
       acc / nth_hs / acc_real / h_real (the implementation's recurrence is
       the FLX one), chain_of_priest.
     b64_equality_entry, b64_keys: the N -> T entry and the keys
       |g_j| < ulp(g_(j+2)) on the actual run (B64_CarryCleanCascade.v).
     priest_chains_nonzero: the nonzero hypothesis follows from the chains
       except for singleton chains (chain_nz).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.  Rung 4
     (b64_cascade_tail_bound, fes_output_error_bound: statement, adequacy to
     the corpus fast_expansion_sum, FLX->binary64 bridge) human-reviewed
     2026-11-10 (J. Bloemscheer); the file stays pending until rung 3
     (B64_CarryCleanTailModel.v, which it builds on) is reviewed.
     Assisted-by: Claude
   ========================================================================== *)
From Stdlib Require Import Reals ZArith Lia Lra List Permutation.
Import ListNotations.
From Flocq Require Import Core IEEE754.Binary.
From Flocq.Prop Require Import Plus_error.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_lib B64_Pff_bridge
     B64_Expansion B64_FastExpansionSum B64_FastExpansionSum_Shewchuk
     B64_Overlap_Hierarchy B64_CarryCleanAlgo B64_CarryCleanCore B64_CarryCleanLadder
     B64_CarryCleanTailModel.

Local Open Scope R_scope.

(* ==================================================================== *)
(* binary64 realization: b64_grow_expansion_aux runs the FLX cascade    *)
(* ==================================================================== *)

Section B64.

Local Abbreviation b2r := (Binary.B2R prec emax).
Local Abbreviation emin64 := (3 - emax - prec)%Z.
Local Abbreviation FLT := (FLT_exp emin64 prec).
Let d : binary64 := Binary.B754_zero prec emax false.

Local Instance prec_gt_0_64 : Prec_gt_0 prec.
Proof. unfold Prec_gt_0, prec. lia. Qed.

Lemma prec2 : (2 <= prec)%Z.
Proof. unfold prec. lia. Qed.

Lemma fmt64 : forall x : binary64, generic_format radix2 FLT (b2r x).
Proof. intro x. exact (Binary.generic_format_B2R prec emax x). Qed.

Lemma fmtX : forall x : binary64, generic_format radix2 (FLX_exp prec) (b2r x).
Proof. intro x. apply (generic_format_FLX_FLT radix2 emin64). apply fmt64. Qed.

(* RN of binary64 agrees with FLX RN on every sum of two binary64 values:
   above the subnormal threshold by round_FLT_FLX, below it the sum is
   exact in both formats.  So underflow costs nothing here. *)
Lemma b64_RN_agree : forall a b,
  generic_format radix2 FLT a -> generic_format radix2 FLT b ->
  round radix2 (SpecFloat.fexp prec emax) (BinarySingleNaN.round_mode mode_b64) (a + b)
  = round radix2 (FLX_exp prec) ZnearestE (a + b).
Proof.
  intros a b Fa Fb.
  change (BinarySingleNaN.round_mode mode_b64) with ZnearestE.
  change (SpecFloat.fexp prec emax) with FLT.
  destruct (Rle_or_lt (bpow radix2 (emin64 + prec - 1)) (Rabs (a + b))) as [H | H].
  - apply round_FLT_FLX. exact H.
  - assert (Fs : generic_format radix2 FLT (a + b)).
    { apply (FLT_format_plus_small radix2 emin64 prec a b Fa Fb).
      assert (bpow radix2 (emin64 + prec - 1) <= bpow radix2 (prec + emin64)) by (apply bpow_le; lia). lra. }
    rewrite (round_generic radix2 FLT ZnearestE _ Fs).
    rewrite round_generic; [ reflexivity | auto with typeclass_instances | ].
    apply (generic_format_FLX_FLT radix2 emin64). exact Fs.
Qed.

Lemma ulp_X_le_64 : forall x, x <> 0 ->
  ulp radix2 (FLX_exp prec) x <= ulp radix2 (SpecFloat.fexp prec emax) x.
Proof.
  intros x Hx. rewrite !ulp_neq_0 by exact Hx. apply bpow_le.
  unfold cexp, FLX_exp, SpecFloat.fexp. lia.
Qed.

(* the accumulator after j steps of b64_grow_expansion_aux *)
Fixpoint acc (q : binary64) (xs : list binary64) (j : nat) : binary64 :=
  match j with O => q | S j' => fst (b64_TwoSum (nth j' xs d) (acc q xs j')) end.

Lemma acc_shift : forall j q x xs, acc q (x :: xs) (S j) = acc (fst (b64_TwoSum x q)) xs j.
Proof.
  induction j as [| j IH]; intros q x xs; [ reflexivity | ].
  change (acc q (x :: xs) (S (S j))) with (fst (b64_TwoSum (nth (S j) (x :: xs) d) (acc q (x :: xs) (S j)))).
  rewrite IH. reflexivity.
Qed.

Lemma nth_hs : forall xs q j, (j < length xs)%nat ->
  nth j (fst (b64_grow_expansion_aux q xs)) d = snd (b64_TwoSum (nth j xs d) (acc q xs j)).
Proof.
  induction xs as [| x xs IH]; intros q j Hj; [ simpl in Hj; lia | ].
  cbn [b64_grow_expansion_aux]. destruct (b64_TwoSum x q) as [qn h0] eqn:E.
  destruct (b64_grow_expansion_aux qn xs) as [hs qf] eqn:E2. cbn [fst].
  destruct j as [| j].
  - cbn [nth acc]. rewrite E. reflexivity.
  - cbn [nth]. rewrite acc_shift, E. cbn [fst].
    specialize (IH qn j ltac:(simpl in Hj; lia)). rewrite E2 in IH. exact IH.
Qed.

Lemma safe_nth : forall xs q j, cascade_safe q xs -> (j < length xs)%nat ->
  b64_TwoSum_safe (nth j xs d) (acc q xs j).
Proof.
  induction xs as [| x xs IH]; intros q j Hs Hj; [ simpl in Hj; lia | ].
  destruct Hs as [S1 S2]. destruct j as [| j]; [ exact S1 | ].
  rewrite acc_shift. apply IH; [ exact S2 | simpl in Hj; lia ].
Qed.

Section Run64.
Variables (x0 : binary64) (xs : list binary64).
Let s := x0 :: xs.
Let g := fun j => b2r (nth j s d).
Hypothesis Hfin0 : b64_fin x0.
Hypothesis Hsafe : cascade_safe x0 xs.

Lemma acc_real : forall j, (j <= length xs)%nat ->
  b64_fin (acc x0 xs j) /\ b2r (acc x0 xs j) = Q prec g j.
Proof.
  induction j as [| j IH]; intro Hj; [ split; [ exact Hfin0 | reflexivity ] | ].
  destruct (IH ltac:(lia)) as [Fj Rj].
  pose proof (ts_facts _ _ (safe_nth xs x0 j Hsafe ltac:(lia))) as (FQ & _ & RQ & _ & _ & _).
  change (acc x0 xs (S j)) with (fst (b64_TwoSum (nth j xs d) (acc x0 xs j))).
  split; [ exact FQ | ]. rewrite RQ, b64_RN_agree by apply fmt64.
  change (Q prec g (S j)) with (round radix2 (FLX_exp prec) ZnearestE (g (S j) + Q prec g j)).
  rewrite <- Rj. reflexivity.
Qed.

Lemma h_real : forall j, (1 <= j <= length xs)%nat ->
  b2r (nth (j - 1) (fst (b64_grow_expansion_aux x0 xs)) d) = h prec g j.
Proof.
  intros [| j] Hj; [ lia | ]. replace (S j - 1)%nat with j by lia.
  rewrite nth_hs by lia.
  pose proof (ts_facts _ _ (safe_nth xs x0 j Hsafe ltac:(lia))) as (_ & _ & _ & Ex & _ & _).
  destruct (acc_real j ltac:(lia)) as [_ Rj]. destruct (acc_real (S j) ltac:(lia)) as [_ RSj].
  change (acc x0 xs (S j)) with (fst (b64_TwoSum (nth j xs d) (acc x0 xs j))) in RSj.
  unfold h. rewrite <- Rj, <- RSj. change (g (S j)) with (b2r (nth j xs d)). lra.
Qed.

End Run64.

Lemma chain_of_priest : forall e, priest_chain e -> chainR prec (map b2r e).
Proof.
  induction e as [| a e IH]; intro H; [ exact I | ].
  destruct e as [| b e']; [ exact I | ]. destruct H as [H1 H2].
  split; [ exact H1 | exact (IH H2) ].
Qed.

Lemma map_nth_seq_s : forall l : list binary64, map (fun j => nth j l d) (seq 0 (length l)) = l.
Proof.
  induction l as [| x l IH]; [ reflexivity | ].
  cbn [length seq map nth]. f_equal. rewrite <- seq_shift, map_map. exact IH.
Qed.

Lemma map_g_seq : forall s : list binary64,
  map (fun j => b2r (nth j s d)) (seq 0 (length s)) = map b2r s.
Proof.
  intro s0. rewrite <- (map_nth_seq_s s0) at 2. rewrite map_map. reflexivity.
Qed.

Lemma sorted_g : forall s, sorted_asc s -> forall j, (S j < length s)%nat ->
  Rabs (b2r (nth j s d)) <= Rabs (b2r (nth (S j) s d)).
Proof.
  intros s0 Hs. induction Hs as [| x | x y rest Hxy Hs IH]; intros j Hj; simpl in Hj; [ lia | lia | ].
  destruct j as [| j]; [ exact Hxy | ]. apply (IH j). simpl. lia.
Qed.

(* THE binary64 THEOREM: the actual implementation's accumulators and
   errors obey the tail bound and the error bound, with binary64 ulp. *)
Theorem b64_cascade_tail_bound :
  forall e f x0 xs,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    Forall (fun x => b2r x <> 0) (e ++ f) ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
    sort_by_abs (e ++ f) = x0 :: xs ->
    forall j, (1 <= j <= length xs)%nat ->
      Rabs (b2r (acc x0 xs (j - 1)) - b2r (nth (j - 1) (x0 :: xs) d))
        <= 2 * ulp radix2 (SpecFloat.fexp prec emax) (b2r (nth j (x0 :: xs) d))
      /\ Rabs (b2r (nth (j - 1) (fst (b64_grow_expansion_aux x0 xs)) d))
        <= ulp radix2 (SpecFloat.fexp prec emax) (b2r (nth j (x0 :: xs) d)).
Proof.
  intros e f x0 xs Pe Pf Fe Ff Nz Hov Hs j Hj.
  set (s0 := x0 :: xs). set (g := fun j => b2r (nth j s0 d)).
  assert (Hperm : Permutation (e ++ f) s0) by (unfold s0; rewrite <- Hs; apply sort_by_abs_perm).
  assert (Fs : Forall b64_fin s0) by (unfold s0; rewrite <- Hs; apply sort_by_abs_Forall, Forall_app; split; assumption).
  assert (Hsafe : cascade_safe x0 xs) by (pose proof (fes_cascade_safe e f Fe Ff Hov) as C; rewrite Hs in C; exact C).
  assert (Hfin0 : b64_fin x0) by (inversion Fs; assumption).
  assert (Hsorted : sorted_asc s0) by (unfold s0; rewrite <- Hs; apply sort_by_abs_sorted).
  assert (Nz' : forall j, (j <= length xs)%nat -> g j <> 0).
  { intros i Hi. unfold g. rewrite Forall_forall in Nz. apply Nz.
    apply (Permutation_in _ (Permutation_sym Hperm)). apply nth_In. unfold s0. simpl. lia. }
  assert (Hpm : Permutation (map g (seq 0 (S (length xs)))) (map b2r e ++ map b2r f)).
  { unfold g. change (S (length xs)) with (length s0). rewrite map_g_seq, <- map_app.
    apply Permutation_map, Permutation_sym, Hperm. }
  destruct (cascade_tail_bound prec prec2 g (length xs) (map b2r e) (map b2r f)
              (fun i _ => fmtX (nth i s0 d)) Nz'
              (fun i Hi => sorted_g s0 Hsorted i ltac:(unfold s0; simpl; lia))
              (chain_of_priest e Pe) (chain_of_priest f Pf) Hpm j Hj) as [T L].
  assert (Hg0 : g j <> 0) by (apply Nz'; lia).
  pose proof (ulp_X_le_64 (g j) Hg0) as U.
  destruct (acc_real x0 xs Hfin0 Hsafe (j - 1) ltac:(lia)) as [_ R].
  rewrite (h_real x0 xs Hfin0 Hsafe j Hj).
  fold s0 g in R. rewrite R.
  change (b2r (nth (j - 1) s0 d)) with (g (j - 1)%nat). change (b2r (nth j s0 d)) with (g j).
  change (h prec (fun j0 : nat => b2r (nth j0 (x0 :: xs) d)) j) with (h prec g j).
  split; lra.
Qed.

(* The closed look-ahead on the implementation: error <= ulp(next input). *)
Corollary b64_closed_lookahead :
  forall e f x0 xs,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    Forall (fun x => b2r x <> 0) (e ++ f) ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
    sort_by_abs (e ++ f) = x0 :: xs ->
    forall j, (1 <= j)%nat -> (j < length xs)%nat ->
      Rabs (b2r (nth (j - 1) (fst (b64_grow_expansion_aux x0 xs)) d))
        <= ulp radix2 (SpecFloat.fexp prec emax) (b2r (nth (S j) (x0 :: xs) d)).
Proof.
  intros e f x0 xs Pe Pf Fe Ff Nz Hov Hs j Hj Hj'.
  destruct (b64_cascade_tail_bound e f x0 xs Pe Pf Fe Ff Nz Hov Hs j ltac:(lia)) as [_ L].
  apply Rle_trans with (1 := L).
  assert (Hle : Rabs (b2r (nth j (x0 :: xs) d)) <= Rabs (b2r (nth (S j) (x0 :: xs) d)))
    by (apply (sorted_g (x0 :: xs)); [ rewrite <- Hs; apply sort_by_abs_sorted | simpl; lia ]).
  apply ulp_le; try typeclasses eauto. exact Hle.
Qed.

(* N -> T entry, binary64: equality in the closed look-ahead gives every
   numeric conjunct of B64_CarryCleanCascade.cinv_T for the next state. *)
Theorem b64_equality_entry :
  forall e f x0 xs,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    Forall (fun x => b2r x <> 0) (e ++ f) ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
    sort_by_abs (e ++ f) = x0 :: xs ->
    forall j, (1 <= j)%nat -> (j < length xs)%nat ->
    let gj := nth j (x0 :: xs) d in
    let g2 := nth (S j) (x0 :: xs) d in
    let q := acc x0 xs (j - 1) in
    Rabs (b2r (snd (b64_TwoSum gj q))) = ulp radix2 (SpecFloat.fexp prec emax) (b2r g2) ->
    let M := mag radix2 (b2r g2) in
    let c := cexp radix2 (SpecFloat.fexp prec emax) (b2r g2) in
    exists sg : R, (sg = 1 \/ sg = -1)
      /\ b2r (fst (b64_TwoSum gj q)) = sg * bpow radix2 M
      /\ b2r (snd (b64_TwoSum gj q)) = sg * bpow radix2 c
      /\ (2 <= M - c)%Z
      /\ SpecFloat.fexp prec emax (M + 1) = (c + 1)%Z
      /\ Rabs (b2r gj) = bpow radix2 M - bpow radix2 c
      /\ Rabs (b2r gj) <= Rabs (b2r g2)
      /\ bpow radix2 M - 2 * bpow radix2 c <= Rabs (b2r g2)
      /\ c = (M - prec)%Z.
Proof.
  intros e f x0 xs Pe Pf Fe Ff Nz Hov Hs j Hj1 Hj2 gj g2 q Heq M c.
  set (s0 := x0 :: xs). set (g := fun j => b2r (nth j s0 d)).
  assert (Hperm : Permutation (e ++ f) s0) by (unfold s0; rewrite <- Hs; apply sort_by_abs_perm).
  assert (Fs : Forall b64_fin s0) by (unfold s0; rewrite <- Hs; apply sort_by_abs_Forall, Forall_app; split; assumption).
  assert (Hsafe : cascade_safe x0 xs) by (pose proof (fes_cascade_safe e f Fe Ff Hov) as C; rewrite Hs in C; exact C).
  assert (Hfin0 : b64_fin x0) by (inversion Fs; assumption).
  assert (Hsorted : sorted_asc s0) by (unfold s0; rewrite <- Hs; apply sort_by_abs_sorted).
  assert (Nz' : forall j, (j <= length xs)%nat -> g j <> 0).
  { intros i Hi. unfold g. rewrite Forall_forall in Nz. apply Nz.
    apply (Permutation_in _ (Permutation_sym Hperm)). apply nth_In. unfold s0. simpl. lia. }
  assert (Hpm : Permutation (map g (seq 0 (S (length xs)))) (map b2r e ++ map b2r f)).
  { unfold g. change (S (length xs)) with (length s0). rewrite map_g_seq, <- map_app.
    apply Permutation_map, Permutation_sym, Hperm. }
  pose proof (fun i (_ : (i <= length xs)%nat) => fmtX (nth i s0 d)) as HfX.
  pose proof (fun i (Hi : (S i <= length xs)%nat) => sorted_g s0 Hsorted i ltac:(unfold s0; simpl; lia)) as Hso.
  (* the implementation values are the FLX values *)
  destruct j as [| j']; [ lia | ].
  assert (RQ : b2r (fst (b64_TwoSum gj q)) = Q prec g (S j')).
  { destruct (acc_real x0 xs Hfin0 Hsafe (S j') ltac:(lia)) as [_ R]. unfold gj, q. simpl Nat.sub. rewrite Nat.sub_0_r. exact R. }
  assert (Rh : b2r (snd (b64_TwoSum gj q)) = h prec g (S j')).
  { pose proof (h_real x0 xs Hfin0 Hsafe (S j') ltac:(lia)) as R. replace (S j' - 1)%nat with j' in R by lia.
    rewrite nth_hs in R by lia. unfold gj, q. simpl Nat.sub. rewrite Nat.sub_0_r. exact R. }
  change (b2r g2) with (g (S (S j'))) in *. change (b2r gj) with (g (S j')) in *.
  (* binary64 equality forces FLX equality and the normal range *)
  destruct (cascade_tail_bound prec prec2 g (length xs) (map b2r e) (map b2r f) HfX Nz' Hso
              (chain_of_priest e Pe) (chain_of_priest f Pf) Hpm (S j') ltac:(lia)) as [_ LA].
  assert (H20 : g (S (S j')) <> 0) by (apply Nz'; lia).
  pose proof (ulp_X_le_64 _ H20) as U64.
  assert (UX : ulp radix2 (FLX_exp prec) (g (S j')) <= ulp radix2 (FLX_exp prec) (g (S (S j')))).
  { apply ulp_le; try typeclasses eauto. apply Hso. lia. }
  rewrite Rh in Heq.
  assert (EqX : Rabs (h prec g (S j')) = ulp radix2 (FLX_exp prec) (g (S (S j')))) by lra.
  assert (E64 : ulp radix2 (FLX_exp prec) (g (S (S j'))) = ulp radix2 (SpecFloat.fexp prec emax) (g (S (S j')))) by lra.
  assert (Hc : c = (M - prec)%Z /\ (3 - emax - prec <= M - prec)%Z).
  { rewrite !ulp_neq_0 in E64 by exact H20. apply bpow_inj in E64.
    unfold c, M. change (b2r g2) with (g (S (S j'))). unfold cexp, FLX_exp, SpecFloat.fexp in *. unfold SpecFloat.emin in *. change IntDef.Z.max with Z.max in *. split; lia. }
  destruct Hc as [Hc Hnorm].
  destruct (cascade_eq_shape prec prec2 g (length xs) (map b2r e) (map b2r f) HfX Nz' Hso
              (chain_of_priest e Pe) (chain_of_priest f Pf) Hpm (S j') ltac:(lia) ltac:(lia) EqX)
    as [_ (sg & Hsg & HQ & Hh & Hg)].
  assert (UXc : ulp radix2 (FLX_exp prec) (g (S (S j'))) = bpow radix2 c).
  { rewrite ulp_neq_0 by exact H20. rewrite Hc. reflexivity. }
  fold M in HQ, Hg. rewrite UXc in Hh, Hg.
  exists sg. split; [ exact Hsg | ]. split; [ rewrite RQ; exact HQ | ]. split; [ rewrite Rh; exact Hh | ].
  split; [ rewrite Hc; unfold prec; lia | ]. split; [ unfold SpecFloat.fexp, SpecFloat.emin; change IntDef.Z.max with Z.max; lia | ].
  split; [ exact Hg | ].
  assert (Hle : Rabs (g (S j')) <= Rabs (g (S (S j')))) by (apply Hso; lia).
  split; [ exact Hle | ]. split; [ pose proof (bpow_gt_0 radix2 c); lra | exact Hc ].
Qed.

(* The Priest keys on the binary64 sorted list, with binary64 ulp. *)
Theorem b64_keys :
  forall e f x0 xs,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    Forall (fun x => b2r x <> 0) (e ++ f) ->
    sort_by_abs (e ++ f) = x0 :: xs ->
    forall j, (j + 2 <= length xs)%nat ->
      Rabs (b2r (nth j (x0 :: xs) d)) < ulp radix2 (SpecFloat.fexp prec emax) (b2r (nth (j + 2) (x0 :: xs) d)).
Proof.
  intros e f x0 xs Pe Pf Fe Ff Nz Hs j Hj.
  set (s0 := x0 :: xs). set (g := fun j => b2r (nth j s0 d)).
  assert (Hperm : Permutation (e ++ f) s0) by (unfold s0; rewrite <- Hs; apply sort_by_abs_perm).
  assert (Hsorted : sorted_asc s0) by (unfold s0; rewrite <- Hs; apply sort_by_abs_sorted).
  assert (Nz' : forall j, (j <= length xs)%nat -> g j <> 0).
  { intros i Hi. unfold g. rewrite Forall_forall in Nz. apply Nz.
    apply (Permutation_in _ (Permutation_sym Hperm)). apply nth_In. unfold s0. simpl. lia. }
  assert (Hpm : Permutation (map g (seq 0 (S (length xs)))) (map b2r e ++ map b2r f)).
  { unfold g. change (S (length xs)) with (length s0). rewrite map_g_seq, <- map_app.
    apply Permutation_map, Permutation_sym, Hperm. }
  pose proof (keys_derived prec prec2 g (length xs) (map b2r e) (map b2r f) Nz'
                (fun i (Hi : (S i <= length xs)%nat) => sorted_g s0 Hsorted i ltac:(unfold s0; simpl; lia))
                (chain_of_priest e Pe) (chain_of_priest f Pf) Hpm j Hj) as K.
  assert (H2 : g (j + 2)%nat <> 0) by (apply Nz'; lia).
  pose proof (ulp_X_le_64 _ H2). unfold g in *. lra.
Qed.

(* Only singleton chains can hold a zero: Priest's relation normalises both
   members of every adjacent pair.  So the zero-free hypothesis of the
   binary64 theorems reduces to the singleton case. *)
Definition chain_nz (c : list binary64) : Prop :=
  match c with x :: nil => b2r x <> 0 | _ => True end.

Lemma priest_chain_nonzero : forall c, priest_chain c -> chain_nz c -> Forall (fun x => b2r x <> 0) c.
Proof.
  induction c as [| a c IH]; intros Hc Hn; [ constructor | ].
  destruct c as [| b c'].
  - constructor; [ exact Hn | constructor ].
  - destruct Hc as [Hab Hrest].
    destruct Hab as (mx & my & kx & ky & Hx & Hy & Nx & Ny & _).
    destruct (norm_facts prec prec2 mx kx Nx) as (Ha0 & _). destruct (norm_facts prec prec2 my ky Ny) as (Hb0 & _).
    constructor; [ rewrite Hx; exact Ha0 | ].
    apply IH; [ exact Hrest | ]. destruct c'; [ simpl; rewrite Hy; exact Hb0 | exact I ].
Qed.

Corollary priest_chains_nonzero : forall e f, priest_chain e -> priest_chain f ->
  chain_nz e -> chain_nz f -> Forall (fun x => b2r x <> 0) (e ++ f).
Proof.
  intros e f Pe Pf Ne Nf. apply Forall_app. split; apply priest_chain_nonzero; assumption.
Qed.

Lemma grow_len : forall xs q, length (fst (b64_grow_expansion_aux q xs)) = length xs.
Proof.
  induction xs as [| x xs IH]; intro q; [ reflexivity | ].
  cbn [b64_grow_expansion_aux]. destruct (b64_TwoSum x q) as [qn h0].
  specialize (IH qn). destruct (b64_grow_expansion_aux qn xs) as [hs qf]. simpl in *. rewrite IH. reflexivity.
Qed.

(* The error bound read off fast_expansion_sum's own output
   qfinal :: rev hs: the component at position (length xs - j + 1) is h_j. *)
Corollary fes_output_error_bound :
  forall e f x0 xs,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    Forall (fun x => b2r x <> 0) (e ++ f) ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
    sort_by_abs (e ++ f) = x0 :: xs ->
    forall j, (1 <= j <= length xs)%nat ->
      Rabs (b2r (nth (length xs - j + 1) (fast_expansion_sum e f) d))
        <= ulp radix2 (SpecFloat.fexp prec emax) (b2r (nth j (x0 :: xs) d)).
Proof.
  intros e f x0 xs Pe Pf Fe Ff Nz Hov Hs j Hj.
  destruct (b64_cascade_tail_bound e f x0 xs Pe Pf Fe Ff Nz Hov Hs j Hj) as [_ L].
  unfold fast_expansion_sum. rewrite Hs.
  pose proof (grow_len xs x0) as Hl.
  destruct (b64_grow_expansion_aux x0 xs) as [hs qf] eqn:E. cbn [fst] in Hl, L.
  replace (length xs - j + 1)%nat with (S (length xs - j)) by lia. cbn [nth].
  rewrite rev_nth by lia. rewrite Hl. replace (length xs - S (length xs - j))%nat with (j - 1)%nat by lia.
  exact L.
Qed.

End B64.

Print Assumptions b64_cascade_tail_bound.
Print Assumptions b64_closed_lookahead.
Print Assumptions fes_output_error_bound.
