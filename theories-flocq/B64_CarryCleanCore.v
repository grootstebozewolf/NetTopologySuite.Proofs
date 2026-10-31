(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_CarryCleanCore
   ----------------------------------------------------------------------------
   The core slice (carry_clean computes the block reduction), the two-part
   open bridge, the trivial base case and cascade safety.

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
From NTS.Proofs.Flocq Require Import B64_CarryCleanAlgo B64_CarryCleanWitness.

Import ListNotations.
Local Open Scope R_scope.

(* ==========================================================================
   THE CORE SLICE -- rounding-free.

   `carry_clean` performs no arithmetic that can round.  On any input whose
   nonzero components split into BLOCKS -- a single u, a twin (x, x), or an
   anti pair (x, -x) -- with strictly decreasing block magnitudes (the
   PATTERN), the sweep acts block by block: anti pairs are DELETED, twins
   are replaced by their exact double, singles pass through.
   `carry_clean_priest_core` states exactly that, plus exactness of the sum.
   No property of `fast_expansion_sum` or of rounding enters.

   The bridge from Priest's floating-point conditions is the OPEN part, in
   two Definitions: (a) the pattern (`fes_priest_carry_pattern`) and (b)
   nonoverlap of the reduction (`fes_priest_reduction_nonoverlap`).
   `carry_clean_priest_target_of_bridge` proves that they imply
   `carry_clean_priest_target` -- one way only; nothing here proves them.
   ========================================================================== *)

Inductive cblock : Type :=
  | CSingle (u : binary64)
  | CTwin (x : binary64)
  | CAnti (x : binary64).

Definition cblock_expand (b : cblock) : list binary64 :=
  match b with
  | CSingle u => [u]
  | CTwin x => [x; x]
  | CAnti x => [x; b64_neg x]
  end.

Definition cblock_reduce (b : cblock) : list binary64 :=
  match b with
  | CSingle u => [u]
  | CTwin x => [b64_mult x b64_two_unit]
  | CAnti _ => []
  end.

Definition block_key (b : cblock) : R :=
  match b with
  | CSingle u => Rabs (Binary.B2R prec emax u)
  | CTwin x => 2 * Rabs (Binary.B2R prec emax x)
  | CAnti x => Rabs (Binary.B2R prec emax x)
  end.

Definition b64_nz (x : binary64) : Prop :=
  b64_fin x /\ Binary.B2R prec emax x <> 0.

Definition block_ok (b : cblock) : Prop :=
  match b with
  | CSingle u => b64_nz u
  | CTwin x => b64_nz x /\ 2 * Rabs (Binary.B2R prec emax x) < bpow radix2 emax
  | CAnti x => b64_nz x
  end.

Fixpoint keys_decreasing (bs : list cblock) : Prop :=
  match bs with
  | nil => True
  | b :: rest =>
      match rest with
      | nil => True
      | b' :: _ => block_key b' < block_key b
      end /\ keys_decreasing rest
  end.

(* (a) the block PATTERN: valid blocks, strictly decreasing magnitudes. *)
Definition carry_pattern (bs : list cblock) : Prop :=
  Forall block_ok bs /\ keys_decreasing bs.

(* (a) and (b): the pattern, plus nonoverlap of the reduction. *)
Definition carry_shape (bs : list cblock) : Prop :=
  Forall block_ok bs /\ keys_decreasing bs
  /\ nonoverlapping_chain (flat_map cblock_reduce bs).

Definition drop_zeros (l : list binary64) : list binary64 :=
  filter (fun x => negb (b64_is_zero x)) l.

(* The sweep's stack after a prefix, without the flop count. *)
Fixpoint run_stack (carry : bool) (xs st : list binary64) : list binary64 :=
  match xs with
  | nil => st
  | x :: xs' =>
      if b64_is_zero x then run_stack carry xs' st
      else run_stack carry xs' (fst (cc_push carry x st))
  end.

Lemma cc_run_fst :
  forall carry xs st, fst (cc_run carry xs st) = rev (run_stack carry xs st).
Proof.
  intros carry xs. induction xs as [| x xs' IH]; intro st; [ reflexivity | ].
  cbn [cc_run run_stack]. destruct (b64_is_zero x); [ apply IH | ].
  destruct (cc_push carry x st) as [st1 n1].
  specialize (IH st1). destruct (cc_run carry xs' st1) as [r n2].
  cbn [fst] in *. exact IH.
Qed.

Lemma run_stack_app :
  forall carry l1 l2 st,
    run_stack carry (l1 ++ l2) st = run_stack carry l2 (run_stack carry l1 st).
Proof.
  intros carry l1. induction l1 as [| x l1 IH]; intros l2 st; [ reflexivity | ].
  cbn [app run_stack]. destruct (b64_is_zero x); apply IH.
Qed.

Lemma run_stack_drop_zeros :
  forall carry l st, run_stack carry (drop_zeros l) st = run_stack carry l st.
Proof.
  intros carry l. induction l as [| x l IH]; intro st; [ reflexivity | ].
  unfold drop_zeros in *. cbn [filter run_stack].
  destruct (b64_is_zero x) eqn:Hz; cbn [negb run_stack]; rewrite ?Hz; apply IH.
Qed.

Lemma carry_clean_drop_zeros :
  forall l, carry_clean (drop_zeros l) = carry_clean l.
Proof.
  intro l. unfold carry_clean, carry_clean_cost.
  rewrite !cc_run_fst, run_stack_drop_zeros. reflexivity.
Qed.

Lemma b64_same_refl : forall x, b64_fin x -> b64_same x x = true.
Proof.
  intros x Hx. unfold b64_same.
  rewrite (Binary.Bcompare_correct prec emax x x Hx Hx), Rcompare_Eq; reflexivity.
Qed.

Lemma b64_same_abs_neq :
  forall a b, b64_fin a -> b64_fin b ->
    Rabs (Binary.B2R prec emax a) <> Rabs (Binary.B2R prec emax b) ->
    b64_same a b = false.
Proof.
  intros a b Ha Hb Hne. destruct (b64_same a b) eqn:H; [ | reflexivity ].
  exfalso. apply Hne. rewrite (b64_same_R a b Ha Hb H). reflexivity.
Qed.

(* A nonzero component never cancels against itself. *)
Lemma b64_same_neg_self : forall x, b64_nz x -> b64_same x (b64_neg x) = false.
Proof.
  intros x [Hxf Hx0]. destruct (b64_same x (b64_neg x)) eqn:H; [ | reflexivity ].
  exfalso. apply b64_same_R in H; [ | exact Hxf | apply b64_neg_fin, Hxf ].
  rewrite b64_neg_R in H. apply Hx0. lra.
Qed.

Lemma b64_nz_not_zero : forall x, b64_nz x -> b64_is_zero x = false.
Proof. intros [s | s | s pl Hpl | s m e H] [_ Hx]; try reflexivity. exfalso; apply Hx; reflexivity. Qed.

Lemma b64_neg_neg : forall x, b64_neg (b64_neg x) = x.
Proof. intros [s | s | s pl Hpl | s m e H]; try reflexivity. simpl. rewrite Bool.negb_involutive. reflexivity. Qed.

Lemma b64_neg_nz : forall x, b64_nz x -> b64_nz (b64_neg x).
Proof.
  intros x [Hf Hx]. split; [ apply b64_neg_fin, Hf | ].
  rewrite b64_neg_R. intro H. apply Hx. lra.
Qed.

Definition top_above (st : list binary64) (k : R) : Prop :=
  match st with nil => True | t :: _ => k < Rabs (Binary.B2R prec emax t) end.

(* A component strictly below the stack top is pushed unchanged. *)
Lemma cc_push_fresh :
  forall x st, b64_nz x -> Forall b64_fin st ->
    top_above st (Rabs (Binary.B2R prec emax x)) ->
    fst (cc_push true x st) = x :: st.
Proof.
  intros x [| t st'] Hx Hst Htop; [ reflexivity | ].
  inversion Hst as [| ? ? Ht _]; subst. destruct Hx as [Hxf Hx0].
  cbn [top_above] in Htop. cbn [cc_push].
  rewrite (b64_same_abs_neq t (b64_neg x)); [ | exact Ht | apply b64_neg_fin, Hxf | ].
  2: { rewrite b64_neg_R, Rabs_Ropp. lra. }
  rewrite (b64_same_abs_neq t x); [ reflexivity | exact Ht | exact Hxf | lra ].
Qed.

(* One block: the stack grows by the block's reduction, nothing else. *)
Lemma run_stack_block :
  forall b st, block_ok b -> Forall b64_fin st -> top_above st (block_key b) ->
    run_stack true (cblock_expand b) st = rev (cblock_reduce b) ++ st
    /\ Forall b64_fin (rev (cblock_reduce b) ++ st).
Proof.
  intros [u | x | x] st Hok Hst Htop; cbn [block_ok block_key] in Hok, Htop.
  - (* single *)
    cbn [cblock_expand cblock_reduce run_stack rev app].
    rewrite (b64_nz_not_zero u Hok), (cc_push_fresh u st Hok Hst Htop).
    split; [ reflexivity | constructor; [ apply Hok | exact Hst ] ].
  - (* twin: push x, then x meets x and carries 2x *)
    destruct Hok as [Hx Hov]. pose proof Hx as [Hxf Hx0].
    assert (Hpos : 0 < Rabs (Binary.B2R prec emax x)) by (apply Rabs_pos_lt; exact Hx0).
    destruct (double_exact x Hxf Hov) as [HdR Hdf].
    cbn [cblock_expand cblock_reduce run_stack rev app].
    rewrite (b64_nz_not_zero x Hx).
    rewrite (cc_push_fresh x st Hx Hst);
      [ | destruct st as [| t st']; cbn [top_above] in *; lra ].
    cbn [cc_push].
    rewrite (b64_same_neg_self x Hx), (b64_same_refl x Hxf). cbn [andb].
    assert (Hd : b64_nz (b64_mult x b64_two_unit)).
    { split; [ exact Hdf | rewrite HdR; lra ]. }
    pose proof (cc_push_fresh (b64_mult x b64_two_unit) st Hd Hst) as Hp.
    destruct (cc_push true (b64_mult x b64_two_unit) st) as [r n] eqn:E.
    cbn [fst] in *. rewrite Hp.
    + split; [ reflexivity | constructor; [ exact Hdf | exact Hst ] ].
    + rewrite HdR, Rabs_mult, (Rabs_pos_eq 2) by lra. exact Htop.
  - (* anti: push x, then -x cancels it *)
    pose proof Hok as [Hxf Hx0].
    cbn [cblock_expand cblock_reduce run_stack rev app].
    rewrite (b64_nz_not_zero x Hok), (cc_push_fresh x st Hok Hst Htop).
    rewrite (b64_nz_not_zero (b64_neg x) (b64_neg_nz x Hok)).
    cbn [cc_push]. rewrite b64_neg_neg, (b64_same_refl x Hxf).
    split; [ reflexivity | exact Hst ].
Qed.

Lemma run_stack_blocks :
  forall bs st,
    Forall block_ok bs -> keys_decreasing bs -> Forall b64_fin st ->
    (match bs with nil => True | b :: _ => top_above st (block_key b) end) ->
    run_stack true (flat_map cblock_expand bs) st = rev (flat_map cblock_reduce bs) ++ st.
Proof.
  induction bs as [| b bs IH]; intros st Hok Hdec Hst Htop; [ reflexivity | ].
  inversion Hok as [| ? ? Hb Hbs]; subst. destruct Hdec as [Hnext Hdec].
  cbn [flat_map]. rewrite run_stack_app.
  destruct (run_stack_block b st Hb Hst Htop) as [Hrun Hfin].
  rewrite Hrun, (IH _ Hbs Hdec Hfin).
  - rewrite rev_app_distr, app_assoc. reflexivity.
  - (* the next block sits strictly below the new top *)
    destruct bs as [| b' bs']; [ exact I | ].
    destruct b as [u | x | x]; cbn [cblock_reduce rev app top_above block_key] in *.
    + exact Hnext.
    + destruct Hb as [[Hxf _] Hov]. destruct (double_exact x Hxf Hov) as [HdR _].
      rewrite HdR, Rabs_mult, (Rabs_pos_eq 2) by lra. exact Hnext.
    + destruct st as [| t st']; cbn [top_above] in *; [ exact I | lra ].
Qed.

(* Sum preservation of one reduction: deletion of x, -x and the exact
   double of x, x.  No rounding. *)
Lemma reduce_sum :
  forall bs, Forall block_ok bs ->
    expansion_R (flat_map cblock_reduce bs) = expansion_R (flat_map cblock_expand bs).
Proof.
  induction bs as [| b bs IH]; intro Hok; [ reflexivity | ].
  inversion Hok as [| ? ? Hb Hbs]; subst. cbn [flat_map].
  rewrite !expansion_R_app, (IH Hbs). f_equal.
  destruct b as [u | x | x]; cbn [cblock_reduce cblock_expand expansion_R].
  - reflexivity.
  - destruct Hb as [[Hxf _] Hov]. destruct (double_exact x Hxf Hov) as [HdR _].
    rewrite HdR. ring.
  - rewrite b64_neg_R. ring.
Qed.

Lemma expansion_R_drop_zeros :
  forall l, expansion_R (drop_zeros l) = expansion_R l.
Proof.
  induction l as [| x l IH]; [ reflexivity | ].
  unfold drop_zeros in *. cbn [filter expansion_R].
  destruct (b64_is_zero x) eqn:Hz; cbn [negb expansion_R]; rewrite IH;
    [ rewrite (b64_is_zero_R x Hz); ring | reflexivity ].
Qed.

(* THE CORE THEOREM.  Rounding-free: on the block PATTERN alone, the stack
   sweep computes exactly the block reduction -- anti pairs deleted, twins
   doubled exactly -- and preserves the sum.  Nonoverlap is NOT concluded
   here: it is part (b) of the shape, a property of the reduction. *)
Theorem carry_clean_priest_core :
  forall (l : list binary64) (bs : list cblock),
    drop_zeros l = flat_map cblock_expand bs -> carry_pattern bs ->
    carry_clean l = flat_map cblock_reduce bs
    /\ expansion_R (carry_clean l) = expansion_R l
    /\ (forall x, In (CTwin x) bs ->
          Binary.B2R prec emax (b64_mult x b64_two_unit)
          = 2 * Binary.B2R prec emax x).
Proof.
  intros l bs Hl [Hok Hdec].
  assert (Hcc : carry_clean l = flat_map cblock_reduce bs).
  { rewrite <- carry_clean_drop_zeros, Hl.
    unfold carry_clean, carry_clean_cost. rewrite cc_run_fst.
    rewrite (run_stack_blocks bs nil Hok Hdec (Forall_nil _));
      [ rewrite app_nil_r, rev_involutive; reflexivity | ].
    destruct bs; exact I. }
  split; [ exact Hcc | split ].
  - rewrite Hcc, reduce_sum, <- Hl, expansion_R_drop_zeros by exact Hok. reflexivity.
  - intros x Hin. rewrite Forall_forall in Hok. specialize (Hok _ Hin).
    destruct Hok as [[Hxf _] Hov]. apply (double_exact x Hxf Hov).
Qed.

(* With the reduction nonoverlapping too, so is carry_clean's output.  This
   conclusion is part (b) passed through; the content is the core above. *)
Corollary carry_clean_nonoverlap_of_shape :
  forall (l : list binary64) (bs : list cblock),
    drop_zeros l = flat_map cblock_expand bs -> carry_shape bs ->
    nonoverlapping_chain (carry_clean l).
Proof.
  intros l bs Hl [Hok [Hdec Hno]].
  destruct (carry_clean_priest_core l bs Hl (conj Hok Hdec)) as [Hcc _].
  rewrite Hcc. exact Hno.
Qed.

(* --------------------------------------------------------------------------
   The open bridge, in two parts, stated as Definitions so that nothing reads
   as proved.  (a) is a pattern on the raw output; (b) is where the
   round-to-even content sits.  The proved implication runs ONE way:
   bridge -> target.  The bridge is strictly stronger than the target --
   strict keys exclude carry cascades (a 2x followed by a twin (x, x) carries
   twice, which `cc_push` handles and `carry_pattern` rejects) -- so a
   counterexample to the bridge refutes only the bridge.
   -------------------------------------------------------------------------- *)

Definition fes_priest_carry_pattern : Prop :=
  forall e f : list binary64,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
    exists bs, drop_zeros (fast_expansion_sum e f) = flat_map cblock_expand bs
               /\ carry_pattern bs.

Definition fes_priest_reduction_nonoverlap : Prop :=
  forall e f : list binary64,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
    forall bs, drop_zeros (fast_expansion_sum e f) = flat_map cblock_expand bs ->
               carry_pattern bs ->
               nonoverlapping_chain (flat_map cblock_reduce bs).

(* The core reduces the target to the two bridge parts -- one way only. *)
Theorem carry_clean_priest_target_of_bridge :
  fes_priest_carry_pattern -> fes_priest_reduction_nonoverlap ->
  carry_clean_priest_target.
Proof.
  intros Hpat Hred e f He Hf Hef Hff Hov.
  destruct (Hpat e f He Hf Hef Hff Hov) as [bs [Hl [Hok Hdec]]].
  apply (carry_clean_nonoverlap_of_shape _ bs Hl).
  split; [ exact Hok | split; [ exact Hdec | ] ].
  apply (Hred e f He Hf Hef Hff Hov bs Hl (conj Hok Hdec)).
Qed.

Lemma two_scaled :
  forall (m : Z) (e : Z), 2 * (IZR m * bpow radix2 e) = IZR m * bpow radix2 (e + 1).
Proof.
  intros m e. rewrite bpow_plus.
  assert (H2 : bpow radix2 1 = 2) by (rewrite bpow_1; reflexivity).
  rewrite H2. ring.
Qed.

(* The bridge's shape is attained by a real sum: witness 1 (two Priest
   inputs) decomposes as single, twin, single, single. *)
Definition q1_blocks : list cblock :=
  [CSingle q1_A; CTwin q1_p53; CSingle q1_n106; CSingle q1_n107].

Lemma q1_drop_zeros :
  drop_zeros (fast_expansion_sum q1_e q1_f) = flat_map cblock_expand q1_blocks.
Proof.
  apply map_B2FF_inj. unfold fast_expansion_sum. rewrite q1_sort.
  vm_compute. reflexivity.
Qed.

Lemma q1_reduce : flat_map cblock_reduce q1_blocks = [q1_A; q1_p52; q1_n106; q1_n107].
Proof. apply map_B2FF_inj. vm_compute. reflexivity. Qed.

Lemma q1_carry_shape : carry_shape q1_blocks.
Proof.
  assert (Hnz : forall s m e H, b64_nz (Binary.B754_finite prec emax s m e H))
    by (intros; split; [ reflexivity | apply B2R_fin_nonzero ]).
  split; [ | split ].
  - unfold q1_blocks. repeat constructor; try apply Hnz.
    unfold q1_p53. rewrite abs_B2R_fin, two_scaled.
    apply Rle_lt_trans
      with (Rabs (IZR (Z.pos 4503599627370496) * bpow radix2 (-105 + 1)));
      [ apply Rle_abs | apply abs_scaled_lt_bpow; unfold emax; zdec ].
  - unfold q1_blocks, q1_A, q1_p53, q1_n106, q1_n107.
    cbn [keys_decreasing block_key]. rewrite !abs_B2R_fin.
    rewrite two_scaled.
    repeat split; apply scaled_lt'; zdec.
  - rewrite q1_reduce. pose proof q1_carry_nonoverlapping as H.
    rewrite q1_carry in H. exact H.
Qed.

(* ==========================================================================
   BRIDGE, BASE CASE (trivial) -- at most two components in total.

   When `e ++ f` has at most two components the sum is at most one TwoSum,
   and its output has the shape (as singles): this is `b64_TwoSum_nonoverlap`
   plus the overflow bound below.  No twins or anti pairs occur, so carry and
   cancel never run, and the Priest hypothesis is not needed.  The reusable
   results of this section are the overflow bounds: one TwoSum
   (`b64_TwoSum_safe_bound`) and every TwoSum of the cascade
   (`fes_cascade_safe`).

   Overflow: `b64_TwoSum_safe_bound` discharges all six per-operation
   no-overflow conditions of one TwoSum from |x|, |y| <= 2^(emax - 4).  In
   units of u = 2^(emax - 4) the six intermediates stay below 2u, 3u, 5u,
   6u, 4u and 10u, all under 16u = 2^emax.  This is why the target's margin
   is `abs_sum e + abs_sum f <= 2^(emax - 4)`.
   ========================================================================== *)

Lemma format_k_u :
  forall k : Z, (Z.abs k <= 2 ^ prec)%Z ->
    generic_format radix2 (SpecFloat.fexp prec emax) (IZR k * bpow radix2 (emax - 4)).
Proof.
  intros k Hk.
  change (IZR k * bpow radix2 (emax - 4)) with (F2R (Float radix2 k (emax - 4))).
  apply generic_format_F2R_le_pow_prec; [ exact Hk | unfold emax, prec; lia ].
Qed.

(* One safe operation, with the bound its rounded result inherits. *)
Lemma safe_within :
  forall (op : R -> R -> R) (x y : binary64) (k : Z),
    b64_fin x -> b64_fin y -> (0 <= k < 16)%Z ->
    Rabs (op (Binary.B2R prec emax x) (Binary.B2R prec emax y))
      <= IZR k * bpow radix2 (emax - 4) ->
    b64_safe op x y
    /\ Rabs (round radix2 (SpecFloat.fexp prec emax) (BinarySingleNaN.round_mode mode_b64)
               (op (Binary.B2R prec emax x) (Binary.B2R prec emax y)))
       <= IZR k * bpow radix2 (emax - 4).
Proof.
  intros op x y k Hx Hy Hk Hb.
  assert (Hr : Rabs (round radix2 (SpecFloat.fexp prec emax) (BinarySingleNaN.round_mode mode_b64)
                       (op (Binary.B2R prec emax x) (Binary.B2R prec emax y)))
               <= IZR k * bpow radix2 (emax - 4)).
  { apply abs_round_le_generic;
      [ typeclasses eauto | apply BinarySingleNaN.valid_rnd_round_mode
      | apply format_k_u; unfold prec; lia | exact Hb ]. }
  split; [ | exact Hr ].
  split; [ exact Hx | split; [ exact Hy | ] ].
  eapply Rle_lt_trans; [ exact Hr | ].
  replace (bpow radix2 emax) with (IZR 16 * bpow radix2 (emax - 4)).
  - apply Rmult_lt_compat_r; [ apply bpow_gt_0 | apply IZR_lt; lia ].
  - replace emax with (4 + (emax - 4))%Z at 2 by ring.
    rewrite bpow_plus. reflexivity.
Qed.

Lemma b64_TwoSum_safe_bound :
  forall x y : binary64,
    b64_fin x -> b64_fin y ->
    Rabs (Binary.B2R prec emax x) <= bpow radix2 (emax - 4) ->
    Rabs (Binary.B2R prec emax y) <= bpow radix2 (emax - 4) ->
    b64_TwoSum_safe x y.
Proof.
  intros x y Hx Hy Hxb Hyb.
  assert (Hu : 0 < bpow radix2 (emax - 4)) by apply bpow_gt_0.
  (* a = x + y *)
  destruct (safe_within Rplus x y 2 Hx Hy ltac:(lia)) as [S1 B1].
  { eapply Rle_trans; [ apply Rabs_triang | ]. lra. }
  destruct (b64_plus_correct x y S1) as [Ra Fa].
  set (a := b64_plus x y) in *. rewrite <- Ra in B1.
  (* x' = a - x *)
  destruct (safe_within Rminus a x 3 Fa Hx ltac:(lia)) as [S2 B2].
  { unfold Rminus. eapply Rle_trans; [ apply Rabs_triang | ].
    rewrite Rabs_Ropp. lra. }
  destruct (b64_minus_correct a x S2) as [Rx' Fx'].
  set (x' := b64_minus a x) in *. rewrite <- Rx' in B2.
  (* y' = a - x' *)
  destruct (safe_within Rminus a x' 5 Fa Fx' ltac:(lia)) as [S3 B3].
  { unfold Rminus. eapply Rle_trans; [ apply Rabs_triang | ].
    rewrite Rabs_Ropp. lra. }
  destruct (b64_minus_correct a x' S3) as [Ry' Fy'].
  set (y' := b64_minus a x') in *. rewrite <- Ry' in B3.
  (* dx = x - y' *)
  destruct (safe_within Rminus x y' 6 Hx Fy' ltac:(lia)) as [S4 B4].
  { unfold Rminus. eapply Rle_trans; [ apply Rabs_triang | ].
    rewrite Rabs_Ropp. lra. }
  destruct (b64_minus_correct x y' S4) as [Rdx Fdx].
  rewrite <- Rdx in B4.
  (* dy = y - x' *)
  destruct (safe_within Rminus y x' 4 Hy Fx' ltac:(lia)) as [S5 B5].
  { unfold Rminus. eapply Rle_trans; [ apply Rabs_triang | ].
    rewrite Rabs_Ropp. lra. }
  destruct (b64_minus_correct y x' S5) as [Rdy Fdy].
  rewrite <- Rdy in B5.
  (* b = dx + dy *)
  destruct (safe_within Rplus (b64_minus x y') (b64_minus y x') 10 Fdx Fdy ltac:(lia))
    as [S6 _].
  { eapply Rle_trans; [ apply Rabs_triang | ]. lra. }
  exact (conj S1 (conj S2 (conj S3 (conj S4 (conj S5 S6))))).
Qed.

Lemma b64_fin_zero_is_zero :
  forall x, b64_fin x -> Binary.B2R prec emax x = 0 -> b64_is_zero x = true.
Proof.
  intros [s | s | s pl Hpl | s m e H] Hf Hx; try reflexivity; try discriminate.
  exfalso. exact (B2R_fin_nonzero s m e H Hx).
Qed.

Lemma b64_nz_of_not_zero :
  forall x, b64_fin x -> b64_is_zero x = false -> b64_nz x.
Proof.
  intros [s | s | s pl Hpl | s m e H] Hf Hz; try discriminate.
  split; [ exact Hf | apply B2R_fin_nonzero ].
Qed.

(* One TwoSum's output always has the shape (as at most two singles). *)
Lemma twosum_carry_shape :
  forall v u : binary64,
    b64_fin v -> b64_fin u ->
    Rabs (Binary.B2R prec emax v) <= bpow radix2 (emax - 4) ->
    Rabs (Binary.B2R prec emax u) <= bpow radix2 (emax - 4) ->
    exists bs,
      drop_zeros [fst (b64_TwoSum v u); snd (b64_TwoSum v u)]
      = flat_map cblock_expand bs
      /\ carry_shape bs.
Proof.
  intros v u Hv Hu Hvb Hub.
  pose proof (b64_TwoSum_safe_bound v u Hv Hu Hvb Hub) as Hsafe.
  destruct Hsafe as (S1 & S2 & S3 & S4 & S5 & S6).
  pose proof (b64_TwoSum_nonoverlap v u S1 S2 S3 S4 S5 S6) as Hno.
  destruct (b64_plus_correct v u S1) as [_ Fs].
  destruct (b64_plus_correct _ _ S6) as [_ Fh].
  unfold b64_TwoSum in *. cbn [fst snd] in *.
  set (s := b64_plus v u) in *.
  set (h := b64_plus _ _) in Hno, Fh |- *.
  destruct (Req_dec (Binary.B2R prec emax s) 0) as [Hs0 | Hs0].
  - (* s = 0: then |h| <= ulp(0)/2 < 2^emin, so h = 0 too *)
    assert (Hh0 : Binary.B2R prec emax h = 0).
    { apply binary64_below_emin_is_zero.
      rewrite Hs0 in Hno.
      change (ulp radix2 (SpecFloat.fexp prec emax) 0) with (b64_ulp 0) in Hno.
      rewrite b64_ulp_FLT_0 in Hno.
      pose proof (bpow_gt_0 radix2 (3 - emax - prec)). lra. }
    exists []. split; [ | repeat split; constructor ].
    unfold drop_zeros. cbn [filter].
    rewrite (b64_fin_zero_is_zero s Fs Hs0), (b64_fin_zero_is_zero h Fh Hh0).
    reflexivity.
  - assert (Hsz : b64_is_zero s = false).
    { destruct (b64_is_zero s) eqn:E; [ | reflexivity ].
      exfalso. apply Hs0. apply b64_is_zero_R, E. }
    pose proof (b64_nz_of_not_zero s Fs Hsz) as Hsnz.
    destruct (b64_is_zero h) eqn:Hhz.
    + exists [CSingle s]. split.
      * unfold drop_zeros. cbn [filter]. rewrite Hsz, Hhz. reflexivity.
      * repeat split; [ constructor; [ exact Hsnz | constructor ] ].
    + pose proof (b64_nz_of_not_zero h Fh Hhz) as Hhnz.
      exists [CSingle s; CSingle h]. split.
      * unfold drop_zeros. cbn [filter]. rewrite Hsz, Hhz. reflexivity.
      * split; [ constructor; [ exact Hsnz | constructor; [ exact Hhnz | constructor ] ] | split ].
        -- (* |h| <= ulp(s)/2 <= |s|/2 < |s| *)
           cbn [keys_decreasing block_key]. split; [ | exact (conj I I) ].
           pose proof (ulp_le_abs radix2 (SpecFloat.fexp prec emax)
                         (Binary.B2R prec emax s) Hs0
                         (Binary.generic_format_B2R prec emax s)) as Hulp.
           pose proof (Rabs_pos_lt _ Hs0). lra.
        -- cbn [flat_map cblock_reduce app nonoverlapping_chain].
           split; [ | exact I ].
           apply strict_succ_b64_nonoverlapping. exact Hno.
Qed.

Lemma sort_by_abs_Forall :
  forall (P : binary64 -> Prop) l, Forall P l -> Forall P (sort_by_abs l).
Proof.
  intros P l. induction l as [| x l IH]; intro H; [ constructor | ].
  inversion H as [| ? ? Hx Hl]; subst. cbn [sort_by_abs].
  specialize (IH Hl). clear H Hl.
  induction (sort_by_abs l) as [| y ys IHy]; cbn [insert_by_abs].
  - constructor; [ exact Hx | constructor ].
  - inversion IH as [| ? ? Hy Hys]; subst.
    destruct (Rle_dec _ _); [ constructor; assumption | ].
    constructor; [ exact Hy | apply IHy, Hys ].
Qed.

Lemma sort_by_abs_length : forall l, length (sort_by_abs l) = length l.
Proof.
  induction l as [| x l IH]; [ reflexivity | ]. cbn [sort_by_abs length].
  rewrite <- IH. clear IH. induction (sort_by_abs l) as [| y ys IHy]; [ reflexivity | ].
  cbn [insert_by_abs]. destruct (Rle_dec _ _); cbn [length]; [ reflexivity | rewrite IHy; reflexivity ].
Qed.

Lemma abs_sum_app : forall l1 l2, abs_sum (l1 ++ l2) = abs_sum l1 + abs_sum l2.
Proof. induction l1 as [| x l1 IH]; intro l2; cbn [app abs_sum]; [ lra | rewrite IH; lra ]. Qed.

Lemma abs_le_abs_sum :
  forall l, Forall (fun x => Rabs (Binary.B2R prec emax x) <= abs_sum l) l.
Proof.
  induction l as [| x l IH]; [ constructor | ]. cbn [abs_sum].
  pose proof (abs_sum_nonneg l). pose proof (Rabs_pos (Binary.B2R prec emax x)).
  constructor; [ lra | ].
  eapply Forall_impl; [ | exact IH ]. intros y Hy. cbn beta in Hy. lra.
Qed.

(* The trivial base case. *)
Theorem fes_carry_bridge_base_case :
  forall e f : list binary64,
    (length e + length f <= 2)%nat ->
    Forall b64_fin e -> Forall b64_fin f ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 4) ->
    exists bs, drop_zeros (fast_expansion_sum e f) = flat_map cblock_expand bs
               /\ carry_shape bs.
Proof.
  intros e f Hlen He Hf Hov.
  assert (Hfin : Forall b64_fin (sort_by_abs (e ++ f)))
    by (apply sort_by_abs_Forall, Forall_app; split; assumption).
  assert (Hbnd : Forall (fun x => Rabs (Binary.B2R prec emax x) <= bpow radix2 (emax - 4))
                   (sort_by_abs (e ++ f))).
  { apply sort_by_abs_Forall. eapply Forall_impl; [ | apply abs_le_abs_sum ].
    intros x Hx. cbn beta in Hx. rewrite abs_sum_app in Hx. lra. }
  assert (Hl : (length (sort_by_abs (e ++ f)) <= 2)%nat)
    by (rewrite sort_by_abs_length, length_app; exact Hlen).
  unfold fast_expansion_sum.
  destruct (sort_by_abs (e ++ f)) as [| a [| b [| c rest]]].
  - exists []. split; [ reflexivity | repeat split; constructor ].
  - cbn [b64_grow_expansion_aux rev]. inversion Hfin as [| ? ? Ha _]; subst.
    destruct (b64_is_zero a) eqn:Hz.
    + exists []. split; [ unfold drop_zeros; cbn [filter]; rewrite Hz; reflexivity | ].
      repeat split; constructor.
    + exists [CSingle a]. split; [ unfold drop_zeros; cbn [filter]; rewrite Hz; reflexivity | ].
      repeat split; [ constructor; [ apply b64_nz_of_not_zero; assumption | constructor ] ].
  - inversion Hfin as [| ? ? Ha Hb']; subst. inversion Hb' as [| ? ? Hb _]; subst.
    inversion Hbnd as [| ? ? Hab Hbb']; subst. inversion Hbb' as [| ? ? Hbb _]; subst.
    destruct (twosum_carry_shape b a Hb Ha Hbb Hab) as [bs [Hd Hs]].
    exists bs. split; [ | exact Hs ]. rewrite <- Hd.
    cbn [b64_grow_expansion_aux]. destruct (b64_TwoSum b a) as [s h]. reflexivity.
  - cbn [length] in Hl. lia.
Qed.

(* The target on the base case. *)
Corollary carry_clean_priest_target_base_case :
  forall e f : list binary64,
    (length e + length f <= 2)%nat ->
    Forall b64_fin e -> Forall b64_fin f ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 4) ->
    nonoverlapping_chain (carry_clean (fast_expansion_sum e f)).
Proof.
  intros e f Hlen He Hf Hov.
  destruct (fes_carry_bridge_base_case e f Hlen He Hf Hov) as [bs [Hl Hs]].
  apply (carry_clean_nonoverlap_of_shape _ bs Hl Hs).
Qed.

(* --------------------------------------------------------------------------
   Every TwoSum of the cascade is overflow-free (for every later rung).

   Round-to-nearest returns a float at least as close to q + e as q itself,
   so the rounding error is at most |e| and |RN(q + e)| <= |q| + 2|e|.
   Hence every accumulator stays below 2 * abs_sum, and with
   abs_sum e + abs_sum f <= 2^(emax-5) every TwoSum's inputs are at most
   2^(emax-4) -- where `b64_TwoSum_safe_bound` applies.
   -------------------------------------------------------------------------- *)

Lemma round_N_err_le_operand :
  forall a b : R,
    generic_format radix2 (SpecFloat.fexp prec emax) a ->
    Rabs (round radix2 (SpecFloat.fexp prec emax)
            (BinarySingleNaN.round_mode mode_b64) (a + b) - (a + b)) <= Rabs b.
Proof.
  intros a b Ha.
  change (BinarySingleNaN.round_mode mode_b64) with (Znearest (fun x => negb (Z.even x))).
  destruct (round_N_pt radix2 (SpecFloat.fexp prec emax)
              (fun x => negb (Z.even x)) (a + b)) as [_ Hmin].
  specialize (Hmin a Ha).
  replace (a - (a + b)) with (- b) in Hmin by ring.
  rewrite Rabs_Ropp in Hmin. exact Hmin.
Qed.

Fixpoint cascade_safe (q : binary64) (es : list binary64) : Prop :=
  match es with
  | nil => True
  | e :: es' => b64_TwoSum_safe e q /\ cascade_safe (fst (b64_TwoSum e q)) es'
  end.

Lemma cascade_safe_bounded :
  forall es q,
    b64_fin q -> Forall b64_fin es ->
    Rabs (Binary.B2R prec emax q) + 2 * abs_sum es <= bpow radix2 (emax - 4) ->
    cascade_safe q es.
Proof.
  induction es as [| e es IH]; intros q Hq Hes Hb; [ exact I | ].
  inversion Hes as [| ? ? He Hes']; subst. cbn [cascade_safe abs_sum] in *.
  pose proof (abs_sum_nonneg es) as Hsn.
  pose proof (Rabs_pos (Binary.B2R prec emax e)) as Hep.
  pose proof (Rabs_pos (Binary.B2R prec emax q)) as Hqp.
  assert (Heb : Rabs (Binary.B2R prec emax e) <= bpow radix2 (emax - 4)) by lra.
  assert (Hqb : Rabs (Binary.B2R prec emax q) <= bpow radix2 (emax - 4)) by lra.
  pose proof (b64_TwoSum_safe_bound e q He Hq Heb Hqb) as Hsafe.
  split; [ exact Hsafe | ].
  destruct Hsafe as [S1 _].
  destruct (b64_plus_correct e q S1) as [HR Hf].
  change (fst (b64_TwoSum e q)) with (b64_plus e q).
  apply IH; [ exact Hf | exact Hes' | ].
  (* |RN(e + q)| <= |q| + 2 |e| *)
  assert (Hstep : Rabs (Binary.B2R prec emax (b64_plus e q))
                  <= Rabs (Binary.B2R prec emax q) + 2 * Rabs (Binary.B2R prec emax e)).
  { rewrite HR, Rplus_comm.
    pose proof (round_N_err_le_operand (Binary.B2R prec emax q) (Binary.B2R prec emax e)
                  (Binary.generic_format_B2R prec emax q)) as Herr.
    pose proof (Rabs_triang (Binary.B2R prec emax q) (Binary.B2R prec emax e)) as Ht.
    set (r := round radix2 (SpecFloat.fexp prec emax) (BinarySingleNaN.round_mode mode_b64)
                (Binary.B2R prec emax q + Binary.B2R prec emax e)) in *.
    replace r with ((r - (Binary.B2R prec emax q + Binary.B2R prec emax e))
                    + (Binary.B2R prec emax q + Binary.B2R prec emax e)) by ring.
    pose proof (Rabs_triang (r - (Binary.B2R prec emax q + Binary.B2R prec emax e))
                  (Binary.B2R prec emax q + Binary.B2R prec emax e)). lra. }
  lra.
Qed.

Lemma abs_sum_insert :
  forall x l, abs_sum (insert_by_abs x l) = Rabs (Binary.B2R prec emax x) + abs_sum l.
Proof.
  intros x l. induction l as [| y l IH]; [ reflexivity | ].
  cbn [insert_by_abs]. destruct (Rle_dec _ _); cbn [abs_sum]; [ reflexivity | rewrite IH; ring ].
Qed.

Lemma abs_sum_sort : forall l, abs_sum (sort_by_abs l) = abs_sum l.
Proof.
  induction l as [| x l IH]; [ reflexivity | ].
  cbn [sort_by_abs abs_sum]. rewrite abs_sum_insert, IH. reflexivity.
Qed.

(* The cascade of `fast_expansion_sum` never overflows. *)
Theorem fes_cascade_safe :
  forall e f : list binary64,
    Forall b64_fin e -> Forall b64_fin f ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
    match sort_by_abs (e ++ f) with
    | nil => True
    | x :: xs => cascade_safe x xs
    end.
Proof.
  intros e f He Hf Hov.
  assert (Hfin : Forall b64_fin (sort_by_abs (e ++ f)))
    by (apply sort_by_abs_Forall, Forall_app; split; assumption).
  assert (Hsum : abs_sum (sort_by_abs (e ++ f)) <= bpow radix2 (emax - 5))
    by (rewrite abs_sum_sort, abs_sum_app; exact Hov).
  destruct (sort_by_abs (e ++ f)) as [| x xs]; [ exact I | ].
  inversion Hfin as [| ? ? Hx Hxs]; subst. cbn [abs_sum] in Hsum.
  apply cascade_safe_bounded; [ exact Hx | exact Hxs | ].
  assert (H45 : bpow radix2 (emax - 4) = 2 * bpow radix2 (emax - 5)).
  { replace (emax - 4)%Z with ((emax - 5) + 1)%Z by ring.
    rewrite bpow_plus. rewrite (bpow_1 radix2). simpl. ring. }
  pose proof (Rabs_pos (Binary.B2R prec emax x)). lra.
Qed.

(* --------------------------------------------------------------------------
   Assumption audit.
   -------------------------------------------------------------------------- *)

Print Assumptions carry_clean_drop_zeros.
Print Assumptions run_stack_block.
Print Assumptions run_stack_blocks.
Print Assumptions reduce_sum.
Print Assumptions carry_clean_priest_core.
Print Assumptions carry_clean_nonoverlap_of_shape.
Print Assumptions carry_clean_priest_target_of_bridge.
Print Assumptions q1_drop_zeros.
Print Assumptions q1_carry_shape.
Print Assumptions b64_TwoSum_safe_bound.
Print Assumptions twosum_carry_shape.
Print Assumptions fes_carry_bridge_base_case.
Print Assumptions carry_clean_priest_target_base_case.
Print Assumptions cascade_safe_bounded.
Print Assumptions fes_cascade_safe.
