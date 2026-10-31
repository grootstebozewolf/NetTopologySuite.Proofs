(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_CarryCleanAlgo
   ----------------------------------------------------------------------------
   carry_clean and Shewchuk's Compress: the algorithms, their flop counts,
   exactness, the open target, and the arithmetic helpers used by the rest.

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

(* The cost comparison, in FLOPS ONLY.  Comparisons are not counted:
   carry_clean makes at most 5m, Compress 2(m-1), so on total operations
   this does not show carry_clean cheaper, and its branches are
   data-dependent.  The two algorithms also have different domains:
   Compress repairs inputs carry_clean does not (QEX 2 below). *)
Theorem carry_clean_fewer_flops :
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
   The open target.  Stated, not claimed.  The overflow margin
   2^(emax-5) keeps every accumulator of the cascade below 2^(emax-4)
   (`fes_accumulators_bounded`), where every TwoSum is overflow-free
   (`b64_TwoSum_safe_bound`).  It started at 2^(emax-2); the crude per-step
   bound forced 2^(emax-4), the accumulator bound one more bit.
   -------------------------------------------------------------------------- *)

Definition carry_clean_priest_target : Prop :=
  forall e f : list binary64,
    priest_chain e -> priest_chain f ->
    Forall b64_fin e -> Forall b64_fin f ->
    abs_sum e + abs_sum f <= bpow radix2 (emax - 5) ->
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
   Assumption audit.
   -------------------------------------------------------------------------- *)

Print Assumptions carry_clean_flops_le.
Print Assumptions compress_flops_ge.
Print Assumptions carry_clean_fewer_flops.
Print Assumptions carry_clean_exact.
Print Assumptions cancel_clean_exact.
Print Assumptions B2R_fin_nonzero.
