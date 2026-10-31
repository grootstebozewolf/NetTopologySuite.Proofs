(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_CarryClean
   ----------------------------------------------------------------------------
   Going beyond Priest and Shewchuk: a cleanup pass for the output of the
   corpus's `fast_expansion_sum` that does no rounding work at all, measured
   against Shewchuk's Compress (1997 Fig. 15) as the baseline.

   THE PROBLEM.  B64_Priest_FES_counterexample.v shows `fast_expansion_sum`
   does not keep even Shewchuk-nonoverlapping output on Priest-valid input.
   Priest repairs his sum with a renormalization pass; Shewchuk's cleanup is
   Compress, two Fast-Two-Sum sweeps under IEEE round-to-nearest-even.

   THE ALGORITHM (`carry_clean`).  One sweep over the components, largest
   first, with a stack whose top is compared to each incoming nonzero x:

     top = -x   ->  pop          (the pair cancels exactly; no arithmetic)
     top =  x   ->  pop, carry 2x and compare again   (one exact doubling)
     otherwise  ->  push x

   Zeros are skipped.  The idea is the carry of binary addition: the
   overlaps observed in `fast_expansion_sum` output on Priest-valid input are
   pairs of equal-magnitude powers of two, created by two round-half-to-even
   ties in a row (see the traces below).  Equal pairs carry, opposite pairs
   cancel, and nothing is ever rounded.  `cancel_clean` is the same sweep
   without the carry, kept as the first (refuted) plan.

   WHAT IS PROVED, all Qed:

     COST     carry_clean_flops_le       flops(carry_clean e) <= |e|
              compress_flops_ge          flops(Compress e)    >= 3 (|e| - 1)
              carry_clean_cheaper        strictly fewer for |e| >= 2
     EXACT    carry_clean_exact          the exact sum is preserved, given
                                         finite components whose absolute
                                         values sum below 2^emax
     QEX 1    cancel_clean_priest_false  cancelling alone does not give a
                                         nonoverlapping result on
                                         Priest-valid input
     QEX 2    carry_clean_beyond_priest_false
                                         carry_clean does not give one when
                                         only ONE input is Priest-valid and
                                         the other is merely nonoverlapping
     CORE     carry_clean_priest_core    rounding-free: on any list whose
                                         nonzero components split into
                                         singles, twins (x, x) and anti pairs
                                         (x, -x) with strictly decreasing
                                         block magnitudes and a nonoverlapping
                                         reduction, carry_clean IS that
                                         reduction -- anti pairs deleted,
                                         twins doubled exactly -- the sum is
                                         preserved and the result is
                                         nonoverlapping
     BRIDGE   carry_clean_priest_target_of_shape
                                         fes_priest_carry_shape implies
                                         carry_clean_priest_target

   The flop counts are produced by the algorithm definitions themselves
   (each returns its result paired with the number of `b64_plus` /
   `b64_minus` / `b64_mult` calls it made); `carry_clean` and
   `shewchuk_compress` are the first projections.  Comparisons are not
   counted: Compress makes 2(m-1) zero tests; carry_clean makes at most 5m
   (one zero test per component, up to two equality tests per stack step,
   at most 2m steps).  On witness 1 the counts are pinned exactly: 1 flop
   for carry_clean (`q1_carry_flops`), 21 for Compress (`q1_compress_flops`).

   WHAT IS NOT PROVED (do not overclaim).  The correctness claim that would
   make the cost result matter -- that `carry_clean` output IS nonoverlapping
   on `fast_expansion_sum` of two Priest-valid inputs -- is stated below as
   `carry_clean_priest_target`, a Definition, and is OPEN.  After the core
   slice, all that it lacks is `fes_priest_carry_shape` (also a Definition,
   also OPEN): that the floating-point sum of two Priest-valid inputs has
   the block shape.  That bridge is the round-to-even part, and it is the
   whole of what remains; `q1_carry_shape` shows the shape is attained by a
   real sum, so the bridge is not vacuous.  A counterexample to it would
   refute the target as stated, not the core.  "Rounding-free" describes the
   CONTENT of the core: its axiom footprint still carries `classic`, because
   `cblock_reduce` mentions `b64_mult` (Flocq C1).  Evidence: an
   exhaustive check in a p-bit round-to-nearest-even model of the same
   algorithm (tests/CarryCleanExhaustive) finds no failure over every
   Priest-valid input pair with p = 3 (lengths <= 3, 366,766,976 pairs),
   p = 4 (lengths <= 3, 2,146,417,920 pairs), p = 3 again with lengths
   <= 4 (4,670,763,328 pairs), p = 2 (lengths <= 4, 148,581,504 pairs) and
   p = 5 (lengths <= 2, 420,560,896 pairs), against
   680 failures for `cancel_clean` at p = 3;
   600,000 adversarial binary64 cases agree.  Evidence, not proof.  Nor is
   `carry_clean` a drop-in replacement for Compress: QEX 2 shows its domain
   is narrower, and Compress repairs both QEX witnesses
   (`q1_compress_nonoverlapping`, `q2_compress_nonoverlapping`).

   THE BASELINE.  `shewchuk_compress` transcribes Fig. 15: a top-down sweep
   of Fast-Two-Sum keeping each nonzero error as the new accumulator, then a
   bottom-up sweep emitting nonzero errors.  `b64_Fast2Sum` (B64_Pff_bridge)
   is three operations, so Compress costs 3 (m - 1) + 3 g flops, g the number
   of components kept by the first sweep.

   NTS / JTS COUNTERPART.  None in-library: JTS and NTS compute robust
   orientation with double-double arithmetic (`CGAlgorithmsDD`, `DD`), not
   with Shewchuk expansions.  This lane serves the corpus's exact
   orientation (Orient_b64_expansion.v), the predicate behind
   `Orientation.Index`, where expansion sums are chained.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human review pending.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lia Lra List.
From Flocq Require Import IEEE754.Binary Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_Pff_bridge
     B64_Expansion B64_FastExpansionSum B64_FastExpansionSum_Shewchuk
     B64_Shewchuk_Thm13_counterexample B64_Overlap_Hierarchy
     B64_Priest_FES_counterexample DivRoundPow2_b64.

Import ListNotations.
Local Open Scope R_scope.

(* --------------------------------------------------------------------------
   Primitives.  All computable, so concrete traces reduce by `vm_compute`.
   -------------------------------------------------------------------------- *)

Definition b64_is_zero (x : binary64) : bool :=
  match x with Binary.B754_zero _ => true | _ => false end.

(* Sign flip on a finite float; the identity elsewhere (only finite,
   nonzero components reach it). *)
Definition b64_neg (x : binary64) : binary64 :=
  match x with
  | Binary.B754_finite s m e H => Binary.B754_finite prec emax (negb s) m e H
  | _ => x
  end.

Definition b64_same (a b : binary64) : bool :=
  match Binary.Bcompare prec emax a b with Some Eq => true | _ => false end.

(* 2 = 2^52 * 2^-51. *)
Definition b64_two_unit : binary64 :=
  Binary.B754_finite prec emax false 4503599627370496 (-51) eq_refl.

(* --------------------------------------------------------------------------
   The cleanup.  `carry` selects plan B (cancel or carry) over plan A
   (cancel only).  The stack keeps its top at the head; the result is the
   stack reversed, i.e. in input order.  The nat is the flop count.
   -------------------------------------------------------------------------- *)

Fixpoint cc_push (carry : bool) (x : binary64) (st : list binary64)
  : list binary64 * nat :=
  match st with
  | nil => ([x], 0%nat)
  | t :: st' =>
      if b64_same t (b64_neg x) then (st', 0%nat)
      else if (carry && b64_same t x)%bool then
        let '(r, n) := cc_push carry (b64_mult x b64_two_unit) st' in
        (r, S n)
      else (x :: st, 0%nat)
  end.

Fixpoint cc_run (carry : bool) (xs st : list binary64) : list binary64 * nat :=
  match xs with
  | nil => (rev st, 0%nat)
  | x :: xs' =>
      if b64_is_zero x then cc_run carry xs' st
      else
        let '(st1, n1) := cc_push carry x st in
        let '(r, n2) := cc_run carry xs' st1 in
        (r, (n1 + n2)%nat)
  end.

Definition carry_clean_cost (e : list binary64) : list binary64 * nat :=
  cc_run true e nil.
Definition carry_clean (e : list binary64) : list binary64 :=
  fst (carry_clean_cost e).
Definition cancel_clean (e : list binary64) : list binary64 :=
  fst (cc_run false e nil).

(* --------------------------------------------------------------------------
   The baseline: Shewchuk's Compress, 1997 Fig. 15, flop-instrumented.
   Input and output are largest first (the corpus convention).
   -------------------------------------------------------------------------- *)

(* First sweep, largest to smallest: (Q, q) := Fast-Two-Sum(Q, e_i); a
   nonzero q stores Q and continues with q.  Returns the stored components
   (largest first), the final accumulator, and the flop count. *)
Fixpoint compress_down (q : binary64) (xs : list binary64)
  : list binary64 * binary64 * nat :=
  match xs with
  | nil => (nil, q, 0%nat)
  | x :: xs' =>
      let '(q1, r) := b64_Fast2Sum q x in
      if b64_is_zero r then
        let '(gs, qf, n) := compress_down q1 xs' in (gs, qf, (3 + n)%nat)
      else
        let '(gs, qf, n) := compress_down r xs' in (q1 :: gs, qf, (3 + n)%nat)
  end.

(* Second sweep, smallest to largest: (Q, q) := Fast-Two-Sum(g_i, Q),
   emitting each nonzero q (smallest first). *)
Fixpoint compress_up (q : binary64) (gs : list binary64)
  : list binary64 * binary64 * nat :=
  match gs with
  | nil => (nil, q, 0%nat)
  | g :: gs' =>
      let '(q1, r) := b64_Fast2Sum g q in
      let '(hs, qf, n) := compress_up q1 gs' in
      ((if b64_is_zero r then hs else r :: hs), qf, (3 + n)%nat)
  end.

Definition shewchuk_compress_cost (e : list binary64) : list binary64 * nat :=
  match e with
  | nil => (nil, 0%nat)
  | x :: xs =>
      let '(gs, qb, n1) := compress_down x xs in
      let '(hs, qt, n2) := compress_up qb (rev gs) in
      (qt :: rev hs, (n1 + n2)%nat)
  end.

Definition shewchuk_compress (e : list binary64) : list binary64 :=
  fst (shewchuk_compress_cost e).

(* --------------------------------------------------------------------------
   COST.
   -------------------------------------------------------------------------- *)

Lemma cc_push_flops :
  forall carry st x,
    (snd (cc_push carry x st) + length (fst (cc_push carry x st))
     <= S (length st))%nat.
Proof.
  intros carry st. induction st as [| t st' IH]; intro x; [ simpl; lia | ].
  simpl.
  destruct (b64_same t (b64_neg x)); [ simpl; lia | ].
  destruct ((carry && b64_same t x)%bool).
  - specialize (IH (b64_mult x b64_two_unit)).
    destruct (cc_push carry (b64_mult x b64_two_unit) st') as [r n].
    simpl in *. lia.
  - simpl. lia.
Qed.

Lemma cc_run_flops :
  forall carry xs st,
    (snd (cc_run carry xs st) + length (fst (cc_run carry xs st))
     <= length xs + length st)%nat.
Proof.
  intros carry xs. induction xs as [| x xs' IH]; intro st.
  - simpl. rewrite length_rev. lia.
  - simpl. destruct (b64_is_zero x).
    + specialize (IH st). lia.
    + pose proof (cc_push_flops carry st x) as Hp.
      destruct (cc_push carry x st) as [st1 n1].
      specialize (IH st1).
      destruct (cc_run carry xs' st1) as [r n2].
      simpl in *. lia.
Qed.

(* Each carry consumes one component, so the doublings never exceed the
   input length -- and every component left in the output is one fewer. *)
Theorem carry_clean_flops_le :
  forall e : list binary64,
    (snd (carry_clean_cost e) + length (carry_clean e) <= length e)%nat.
Proof.
  intro e. unfold carry_clean, carry_clean_cost.
  pose proof (cc_run_flops true e nil) as H. simpl in H. lia.
Qed.

Lemma compress_down_flops :
  forall xs q, (let '(_, _, n) := compress_down q xs in n) = (3 * length xs)%nat.
Proof.
  induction xs as [| x xs' IH]; intro q; [ reflexivity | ].
  cbn [compress_down length]. destruct (b64_Fast2Sum q x) as [q1 r].
  destruct (b64_is_zero r).
  - specialize (IH q1). destruct (compress_down q1 xs') as [[gs qf] n].
    cbn in *. lia.
  - specialize (IH r). destruct (compress_down r xs') as [[gs qf] n].
    cbn in *. lia.
Qed.

Lemma compress_up_flops :
  forall gs q, (let '(_, _, n) := compress_up q gs in n) = (3 * length gs)%nat.
Proof.
  induction gs as [| g gs' IH]; intro q; [ reflexivity | ].
  cbn [compress_up length]. destruct (b64_Fast2Sum g q) as [q1 r].
  specialize (IH q1). destruct (compress_up q1 gs') as [[hs qf] n].
  cbn in *. lia.
Qed.

Theorem compress_flops_ge :
  forall e : list binary64,
    (3 * (length e - 1) <= snd (shewchuk_compress_cost e))%nat.
Proof.
  intros [| x xs]; [ simpl; lia | ].
  unfold shewchuk_compress_cost.
  pose proof (compress_down_flops xs x) as Hd.
  destruct (compress_down x xs) as [[gs qb] n1].
  pose proof (compress_up_flops (rev gs) qb) as Hu.
  destruct (compress_up qb (rev gs)) as [[hs qt] n2].
  simpl in *. lia.
Qed.

(* The headline cost comparison. *)
Theorem carry_clean_cheaper :
  forall e : list binary64,
    (2 <= length e)%nat ->
    (snd (carry_clean_cost e) < snd (shewchuk_compress_cost e))%nat.
Proof.
  intros e He.
  pose proof (carry_clean_flops_le e) as Hc.
  pose proof (compress_flops_ge e) as Hs.
  lia.
Qed.

(* --------------------------------------------------------------------------
   EXACTNESS.
   -------------------------------------------------------------------------- *)

Definition b64_fin (x : binary64) : Prop := Binary.is_finite prec emax x = true.

Fixpoint abs_sum (e : list binary64) : R :=
  match e with
  | nil => 0
  | x :: e' => Rabs (Binary.B2R prec emax x) + abs_sum e'
  end.

Lemma abs_sum_nonneg : forall e, 0 <= abs_sum e.
Proof.
  induction e as [| x e IH]; simpl; [ lra | ].
  pose proof (Rabs_pos (Binary.B2R prec emax x)). lra.
Qed.

Lemma abs_sum_rev : forall e, abs_sum (rev e) = abs_sum e.
Proof.
  induction e as [| x e IH]; [ reflexivity | ].
  simpl. assert (Happ : forall l1 l2, abs_sum (l1 ++ l2) = abs_sum l1 + abs_sum l2).
  { induction l1 as [| y l1 IH1]; intro l2; simpl; [ lra | rewrite IH1; lra ]. }
  rewrite Happ, IH. simpl. lra.
Qed.

Lemma b64_same_R :
  forall a b, b64_fin a -> b64_fin b -> b64_same a b = true ->
    Binary.B2R prec emax a = Binary.B2R prec emax b.
Proof.
  intros a b Ha Hb H. unfold b64_same in H.
  rewrite (Binary.Bcompare_correct prec emax a b Ha Hb) in H.
  destruct (Rcompare _ _) eqn:Hc; try discriminate.
  apply Rcompare_Eq_inv. exact Hc.
Qed.

Lemma b64_neg_R : forall x, Binary.B2R prec emax (b64_neg x) = - Binary.B2R prec emax x.
Proof.
  intros [s | s | s pl Hpl | s m e H]; simpl; try lra.
  unfold F2R; cbn [Fnum Fexp].
  destruct s; cbn [negb cond_Zopp].
  - change (Z.neg m) with (- Z.pos m)%Z. rewrite opp_IZR. ring.
  - change (Z.neg m) with (- Z.pos m)%Z. rewrite opp_IZR. ring.
Qed.

Lemma b64_neg_fin : forall x, b64_fin x -> b64_fin (b64_neg x).
Proof. intros [s | s | s pl Hpl | s m e H]; unfold b64_fin; simpl; auto. Qed.

Lemma b64_is_zero_R : forall x, b64_is_zero x = true -> Binary.B2R prec emax x = 0.
Proof. intros [s | s | s pl Hpl | s m e H] Hz; try discriminate. reflexivity. Qed.

Lemma b64_two_unit_R : Binary.B2R prec emax b64_two_unit = bpow radix2 1.
Proof.
  unfold b64_two_unit. cbn [Binary.B2R]. unfold F2R; cbn [Fnum Fexp cond_Zopp].
  rewrite IZR_mant_bpow, <- bpow_plus. reflexivity.
Qed.

Lemma double_exact :
  forall x, b64_fin x ->
    2 * Rabs (Binary.B2R prec emax x) < bpow radix2 emax ->
    Binary.B2R prec emax (b64_mult x b64_two_unit) = 2 * Binary.B2R prec emax x
    /\ b64_fin (b64_mult x b64_two_unit).
Proof.
  intros x Hx Hov.
  assert (H2 : bpow radix2 1 = 2) by (rewrite bpow_1; reflexivity).
  destruct (b64_mult_pow2_exact x b64_two_unit 1 Hx eq_refl b64_two_unit_R
              ltac:(lia)) as [HR Hf].
  - rewrite H2, Rabs_mult, (Rabs_pos_eq 2) by lra. lra.
  - split; [ rewrite HR, H2; ring | exact Hf ].
Qed.

Lemma cc_push_exact :
  forall carry st x,
    Forall b64_fin st -> b64_fin x ->
    abs_sum st + Rabs (Binary.B2R prec emax x) < bpow radix2 emax ->
    Forall b64_fin (fst (cc_push carry x st))
    /\ expansion_R (fst (cc_push carry x st))
       = Binary.B2R prec emax x + expansion_R st
    /\ abs_sum (fst (cc_push carry x st))
       <= Rabs (Binary.B2R prec emax x) + abs_sum st.
Proof.
  intros carry st. induction st as [| t st' IH]; intros x Hst Hx Hov.
  - cbn [cc_push fst expansion_R abs_sum]. split; [ apply Forall_cons; [ exact Hx | apply Forall_nil ] | split; lra ].
  - inversion Hst as [| ? ? Ht Hst']; subst.
    cbn [abs_sum cc_push] in Hov |- *.
    pose proof (Rabs_pos (Binary.B2R prec emax t)) as Hta.
    pose proof (Rabs_pos (Binary.B2R prec emax x)) as Hxa.
    pose proof (abs_sum_nonneg st') as Hsa.
    destruct (b64_same t (b64_neg x)) eqn:Hneg.
    + apply b64_same_R in Hneg; [ | exact Ht | apply b64_neg_fin, Hx ].
      rewrite b64_neg_R in Hneg.
      cbn [fst expansion_R abs_sum]. split; [ exact Hst' | split; [ rewrite Hneg; ring | lra ] ].
    + destruct ((carry && b64_same t x)%bool) eqn:Hcar.
      * apply andb_prop in Hcar as [_ Heq].
        apply b64_same_R in Heq; [ | exact Ht | exact Hx ].
        assert (Htx : Rabs (Binary.B2R prec emax t)
                      = Rabs (Binary.B2R prec emax x)) by (rewrite Heq; reflexivity).
        destruct (double_exact x Hx ltac:(lra)) as [HdR Hdf].
        assert (Hd2 : Rabs (Binary.B2R prec emax (b64_mult x b64_two_unit))
                      = 2 * Rabs (Binary.B2R prec emax x)).
        { rewrite HdR, Rabs_mult, (Rabs_pos_eq 2) by lra. reflexivity. }
        destruct (IH (b64_mult x b64_two_unit) Hst' Hdf ltac:(lra))
          as [Hf [HR Ha]].
        destruct (cc_push carry (b64_mult x b64_two_unit) st') as [r n].
        cbn [fst snd expansion_R abs_sum] in *. split; [ exact Hf | split; [ rewrite HR, HdR, Heq; ring | lra ] ].
      * cbn [fst expansion_R abs_sum]. split; [ | split; [ reflexivity | lra ] ].
        apply Forall_cons; [ exact Hx | apply Forall_cons; [ exact Ht | exact Hst' ] ].
Qed.

Lemma cc_run_exact :
  forall carry xs st,
    Forall b64_fin xs -> Forall b64_fin st ->
    abs_sum st + abs_sum xs < bpow radix2 emax ->
    expansion_R (fst (cc_run carry xs st)) = expansion_R st + expansion_R xs.
Proof.
  intros carry xs. induction xs as [| x xs' IH]; intros st Hxs Hst Hov.
  - cbn [cc_run fst]. rewrite expansion_R_rev. cbn [expansion_R]. lra.
  - inversion Hxs as [| ? ? Hx Hxs']; subst.
    cbn [abs_sum cc_run expansion_R] in Hov |- *.
    pose proof (Rabs_pos (Binary.B2R prec emax x)) as Hxa.
    destruct (b64_is_zero x) eqn:Hz.
    + rewrite (IH st Hxs' Hst ltac:(lra)), (b64_is_zero_R x Hz). ring.
    + pose proof (abs_sum_nonneg xs') as Hxsa.
      destruct (cc_push_exact carry st x Hst Hx ltac:(lra)) as [Hf [HR Ha]].
      destruct (cc_push carry x st) as [st1 n1].
      cbn [fst] in Hf, HR, Ha.
      pose proof (IH st1 Hxs' Hf ltac:(lra)) as HIH.
      destruct (cc_run carry xs' st1) as [r n2].
      cbn [fst] in *. rewrite HIH, HR. ring.
Qed.

Theorem carry_clean_exact :
  forall e : list binary64,
    Forall b64_fin e -> abs_sum e < bpow radix2 emax ->
    expansion_R (carry_clean e) = expansion_R e.
Proof.
  intros e Hf Hov. unfold carry_clean, carry_clean_cost.
  rewrite (cc_run_exact true e nil Hf (Forall_nil _)); cbn [abs_sum expansion_R]; lra.
Qed.

Theorem cancel_clean_exact :
  forall e : list binary64,
    Forall b64_fin e -> abs_sum e < bpow radix2 emax ->
    expansion_R (cancel_clean e) = expansion_R e.
Proof.
  intros e Hf Hov. unfold cancel_clean.
  rewrite (cc_run_exact false e nil Hf (Forall_nil _)); cbn [abs_sum expansion_R]; lra.
Qed.

(* --------------------------------------------------------------------------
   The open target.  Stated, not claimed.  The overflow margin keeps every
   intermediate of the cascade finite.
   -------------------------------------------------------------------------- *)

Definition carry_clean_priest_target : Prop :=
  forall e f : list binary64,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    abs_sum e + abs_sum f < bpow radix2 (emax - 2) ->
    nonoverlapping_chain (carry_clean (fast_expansion_sum e f)).

(* --------------------------------------------------------------------------
   Arithmetic helpers for the concrete witnesses.
   -------------------------------------------------------------------------- *)

Lemma B2R_fin :
  forall s m e H,
    Binary.B2R prec emax (Binary.B754_finite prec emax s m e H)
    = IZR (cond_Zopp s (Z.pos m)) * bpow radix2 e.
Proof. reflexivity. Qed.

Lemma abs_B2R_fin :
  forall s m e H,
    Rabs (Binary.B2R prec emax (Binary.B754_finite prec emax s m e H))
    = IZR (Z.pos m) * bpow radix2 e.
Proof.
  intros s m e H. rewrite B2R_fin, Rabs_mult, <- abs_IZR.
  rewrite (Rabs_pos_eq (bpow radix2 e)) by (left; apply bpow_gt_0).
  destruct s; reflexivity.
Qed.

Lemma B2R_fin_nonzero :
  forall s m e H, Binary.B2R prec emax (Binary.B754_finite prec emax s m e H) <> 0.
Proof.
  intros s m e H. rewrite B2R_fin.
  apply Rmult_integral_contrapositive_currified.
  - apply eq_IZR_contrapositive. destruct s; discriminate.
  - apply Rgt_not_eq, bpow_gt_0.
Qed.

Lemma IZR_scaled_shift :
  forall (n : Z) (d e : Z), (0 <= d)%Z ->
    IZR n * bpow radix2 (e + d) = IZR (n * Zpower radix2 d) * bpow radix2 e.
Proof.
  intros n d e Hd. rewrite mult_IZR, IZR_Zpower by exact Hd.
  rewrite bpow_plus. ring.
Qed.

(* Magnitude comparison of two scaled integers, decided on Z. *)
Lemma scaled_lt :
  forall (m1 m2 : Z) (e1 e2 : Z),
    (e2 <= e1)%Z -> (m1 * Zpower radix2 (e1 - e2) < m2)%Z ->
    IZR m1 * bpow radix2 e1 < IZR m2 * bpow radix2 e2.
Proof.
  intros m1 m2 e1 e2 He Hm.
  replace e1 with (e2 + (e1 - e2))%Z at 1 by ring.
  rewrite IZR_scaled_shift by lia.
  apply Rmult_lt_compat_r; [ apply bpow_gt_0 | apply IZR_lt; exact Hm ].
Qed.

Lemma scaled_lt' :
  forall (m1 m2 : Z) (e1 e2 : Z),
    (e1 <= e2)%Z -> (m1 < m2 * Zpower radix2 (e2 - e1))%Z ->
    IZR m1 * bpow radix2 e1 < IZR m2 * bpow radix2 e2.
Proof.
  intros m1 m2 e1 e2 He Hm.
  replace e2 with (e1 + (e2 - e1))%Z at 1 by ring.
  rewrite IZR_scaled_shift by lia.
  apply Rmult_lt_compat_r; [ apply bpow_gt_0 | apply IZR_lt; exact Hm ].
Qed.

Lemma abs_scaled_lt_bpow :
  forall (n k s : Z),
    (k <= s)%Z -> (Z.abs n < Zpower radix2 (s - k))%Z ->
    Rabs (IZR n * bpow radix2 k) < bpow radix2 s.
Proof.
  intros n k s Hk Hn.
  rewrite Rabs_mult, <- abs_IZR, (Rabs_pos_eq (bpow radix2 k))
    by (left; apply bpow_gt_0).
  replace (bpow radix2 s) with (IZR 1 * bpow radix2 (k + (s - k)))
    by (replace (k + (s - k))%Z with s by ring; simpl; ring).
  rewrite IZR_scaled_shift by lia. rewrite Z.mul_1_l.
  apply Rmult_lt_compat_r; [ apply bpow_gt_0 | apply IZR_lt; exact Hn ].
Qed.

Lemma nonov_scaled :
  forall x y (r s : Z),
    x = IZR r * bpow radix2 s -> Rabs y < bpow radix2 s -> nonoverlapping_R x y.
Proof.
  intros x y r s Hx Hy. left. exists r, s. rewrite Z.add_0_r. split; assumption.
Qed.

(* A nonzero multiple of 2^s is at least 2^s in magnitude. *)
Lemma scaled_nonzero_ge :
  forall x (r s : Z), x = IZR r * bpow radix2 s -> x <> 0 -> bpow radix2 s <= Rabs x.
Proof.
  intros x r s Hx Hx0. subst x.
  assert (Hr : r <> 0%Z) by (intro Hr; subst r; apply Hx0; simpl; ring).
  rewrite Rabs_mult, <- abs_IZR, (Rabs_pos_eq (bpow radix2 s))
    by (left; apply bpow_gt_0).
  assert (H1 : 1 <= IZR (Z.abs r)) by (apply IZR_le; lia).
  pose proof (bpow_gt_0 radix2 s). nra.
Qed.

(* A multiple of 2^s with s > k has an even significand at scale 2^k. *)
Lemma scaled_even :
  forall (r s n k : Z),
    IZR r * bpow radix2 s = IZR n * bpow radix2 k -> (k < s)%Z -> Z.even n = true.
Proof.
  intros r s n k Heq Hks.
  replace s with (k + (s - k))%Z in Heq by ring.
  rewrite IZR_scaled_shift in Heq by lia.
  apply Rmult_eq_reg_r in Heq; [ | apply Rgt_not_eq, bpow_gt_0 ].
  apply eq_IZR in Heq. subst n.
  replace (s - k)%Z with (1 + (s - k - 1))%Z by ring.
  rewrite Zpower_plus by lia. rewrite Z.even_mul, Z.even_mul. simpl.
  rewrite Bool.orb_true_r. reflexivity.
Qed.

Lemma priest_fin :
  forall s1 m1 e1 H1 s2 m2 e2 H2,
    (Zpower radix2 (prec - 1) <= Z.pos m1 < Zpower radix2 prec)%Z ->
    (Zpower radix2 (prec - 1) <= Z.pos m2 < Zpower radix2 prec)%Z ->
    (e1 - e2 >= prec)%Z ->
    priest_nonoverlapping_b64 (Binary.B754_finite prec emax s1 m1 e1 H1)
                              (Binary.B754_finite prec emax s2 m2 e2 H2).
Proof.
  intros s1 m1 e1 H1 s2 m2 e2 H2 Hm1 Hm2 Hgap.
  exists (cond_Zopp s1 (Z.pos m1)), (cond_Zopp s2 (Z.pos m2)), e1, e2.
  assert (Hb : forall s m, (Zpower radix2 (prec - 1) <= Z.pos m < Zpower radix2 prec)%Z ->
             bpow radix2 (prec - 1) <= Rabs (IZR (cond_Zopp s (Z.pos m)))
             < bpow radix2 prec).
  { intros s m [Hlo Hhi]. rewrite <- abs_IZR.
    replace (Z.abs (cond_Zopp s (Z.pos m))) with (Z.pos m) by (destruct s; reflexivity).
    rewrite <- !IZR_Zpower by (unfold prec; lia).
    split; [ apply IZR_le | apply IZR_lt ]; assumption. }
  repeat split; try reflexivity; try apply Hb; try assumption.
Qed.

Ltac zdec := unfold prec; vm_compute; first [ reflexivity | split; congruence | congruence ].

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

(* ==========================================================================
   THE CORE SLICE -- rounding-free.

   `carry_clean` performs no arithmetic that can round.  On any input whose
   nonzero components split into BLOCKS -- a single u, a twin (x, x), or an
   anti pair (x, -x) -- with strictly decreasing block magnitudes and a
   nonoverlapping reduced list, the sweep acts block by block: anti pairs
   are DELETED, twins are replaced by their exact double, singles pass
   through.  `carry_clean_priest_core` states exactly that, plus exactness
   of the sum and nonoverlap of the result.  No property of
   `fast_expansion_sum` or of rounding enters.

   The bridge from Priest's floating-point conditions to this shape is the
   OPEN part: `fes_priest_carry_shape` says the sum of two Priest-valid
   inputs always has the shape.  `carry_clean_priest_target_of_shape` proves
   that it implies `carry_clean_priest_target`; nothing here proves it.
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

(* THE CORE THEOREM.  Rounding-free: the output is the block reduction,
   the sum is preserved exactly, the result is nonoverlapping, and the only
   arithmetic performed is the exact doubling of twins. *)
Theorem carry_clean_priest_core :
  forall (l : list binary64) (bs : list cblock),
    drop_zeros l = flat_map cblock_expand bs -> carry_shape bs ->
    carry_clean l = flat_map cblock_reduce bs
    /\ expansion_R (carry_clean l) = expansion_R l
    /\ nonoverlapping_chain (carry_clean l)
    /\ (forall x, In (CTwin x) bs ->
          Binary.B2R prec emax (b64_mult x b64_two_unit)
          = 2 * Binary.B2R prec emax x).
Proof.
  intros l bs Hl [Hok [Hdec Hno]].
  assert (Hcc : carry_clean l = flat_map cblock_reduce bs).
  { rewrite <- carry_clean_drop_zeros, Hl.
    unfold carry_clean, carry_clean_cost. rewrite cc_run_fst.
    rewrite (run_stack_blocks bs nil Hok Hdec (Forall_nil _));
      [ rewrite app_nil_r, rev_involutive; reflexivity | ].
    destruct bs; exact I. }
  split; [ exact Hcc | split; [ | split ] ].
  - rewrite Hcc, reduce_sum, <- Hl, expansion_R_drop_zeros by exact Hok. reflexivity.
  - rewrite Hcc. exact Hno.
  - intros x Hin. rewrite Forall_forall in Hok. specialize (Hok _ Hin).
    destruct Hok as [[Hxf _] Hov]. apply (double_exact x Hxf Hov).
Qed.

(* --------------------------------------------------------------------------
   The open bridge, stated as a Definition so that nothing reads as proved.
   -------------------------------------------------------------------------- *)

Definition fes_priest_carry_shape : Prop :=
  forall e f : list binary64,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    abs_sum e + abs_sum f < bpow radix2 (emax - 2) ->
    exists bs, drop_zeros (fast_expansion_sum e f) = flat_map cblock_expand bs
               /\ carry_shape bs.

(* The core reduces the target to the bridge -- and to nothing else. *)
Theorem carry_clean_priest_target_of_shape :
  fes_priest_carry_shape -> carry_clean_priest_target.
Proof.
  intros Hshape e f He Hf Hef Hff Hov.
  destruct (Hshape e f He Hf Hef Hff Hov) as [bs [Hl Hs]].
  apply (carry_clean_priest_core _ bs Hl Hs).
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
   survives, because `carry_clean_cheaper` is an inequality and an
   undercounting counter only strengthens it.  Replayed 2026-10-29 on
   Rocq 9.2 + Flocq 4.2.2.
   -------------------------------------------------------------------------- *)

(* --------------------------------------------------------------------------
   Assumption audit.
   -------------------------------------------------------------------------- *)

Print Assumptions carry_clean_flops_le.
Print Assumptions compress_flops_ge.
Print Assumptions carry_clean_cheaper.
Print Assumptions carry_clean_exact.
Print Assumptions cancel_clean_exact.
Print Assumptions B2R_fin_nonzero.
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
Print Assumptions carry_clean_drop_zeros.
Print Assumptions run_stack_block.
Print Assumptions run_stack_blocks.
Print Assumptions reduce_sum.
Print Assumptions carry_clean_priest_core.
Print Assumptions carry_clean_priest_target_of_shape.
Print Assumptions q1_drop_zeros.
Print Assumptions q1_carry_shape.
