(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_FastExpansionSum
   ----------------------------------------------------------------------------
   Stage D chain composition primitive: Shewchuk's GROW-EXPANSION at binary64.

   Sum correctness (`b64_grow_expansion_correct`) -- Qed-closed in this
   session.  Nonoverlap preservation (`b64_grow_expansion_nonoverlap`) --
   still Admitted, the load-bearing piece for the next session.

   CI's Qed-invariant grep (no Admitted, no Axiom, no Parameter) continues
   to flag this file for the remaining Admitted theorem.  THAT FLAG IS THE
   CORRECT BEHAVIOUR for now.  The marker comes out when the nonoverlap
   proof comes in.

   Design rationale, survey, and proof plan: see
   `docs/stage-d-chain-composition-approach.md`.

   Why not `b64_TwoSum_chain3_nonoverlap` directly?  Because the naive
   `b64_TwoSum_chain3` output `(s2, e2, e1)` does NOT satisfy
   `nonoverlap_strict` -- the survey in the doc walks the
   counterexample.  `b64_grow_expansion` is the replacement entry point
   for nonoverlap-requiring consumers; it has the same exact sum but a
   structurally different component ordering (cascade-sorted via
   TwoSum, not naive composition).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lra.
From Stdlib Require Import List.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import IEEE754.BinarySingleNaN.
From Flocq Require Import Core.

From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import B64_bridge.
From NTS.Proofs.Flocq Require Import B64_lib.
From NTS.Proofs.Flocq Require Import B64_Expansion.
From NTS.Proofs.Flocq Require Import B64_Pff_bridge.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* The cascade body.                                                          *)
(*                                                                            *)
(* `b64_grow_expansion_aux q es` is Shewchuk's inner loop: it threads the     *)
(* accumulator `q` through the components of `es` (taken in smallest-first   *)
(* order), produces a list of `h_i` outputs (in the order they were          *)
(* generated, smallest-magnitude h first), and returns the final             *)
(* accumulator.                                                              *)
(*                                                                            *)
(* For each step the loop body is `(Q_{i}, h_i) := b64_TwoSum e_i Q_{i-1}`.  *)
(* We use TwoSum (not Fast2Sum) because we cannot assume the magnitude       *)
(* ordering `|Q| <= |e_i|` in general -- the cascade invariant has to be    *)
(* established by the calling context (or by the proof, in the next         *)
(* session).                                                                  *)
(* -------------------------------------------------------------------------- *)

Fixpoint b64_grow_expansion_aux (q : binary64) (es : list binary64)
  : list binary64 * binary64 :=
  match es with
  | nil => (nil, q)
  | e :: es' =>
      let '(qnew, h) := b64_TwoSum e q in
      let '(hs, qfinal) := b64_grow_expansion_aux qnew es' in
      (h :: hs, qfinal)
  end.

(* -------------------------------------------------------------------------- *)
(* The top-level entry point.                                                 *)
(*                                                                            *)
(* `b64_grow_expansion e b` takes a non-overlapping expansion `e` (in our    *)
(* `nonoverlap_strict` convention -- largest magnitude first) and grows it   *)
(* by adding a single binary64 `b`.  Output is a (length+1)-component        *)
(* expansion in the same convention.                                          *)
(*                                                                            *)
(* The function:                                                              *)
(*   1. Reverses `e` to get smallest-first ordering (as the cascade expects).*)
(*   2. Runs the cascade with `b` as the initial accumulator.                *)
(*   3. Re-orders the output to largest-first.                               *)
(*                                                                            *)
(* The output is `qfinal :: rev hs` where `hs` was accumulated smallest-first*)
(* by the cascade.  This puts the final accumulator (largest magnitude) at  *)
(* the head and the smallest `h_1` at the tail, matching                    *)
(* `nonoverlap_strict`.                                                      *)
(* -------------------------------------------------------------------------- *)

Definition b64_grow_expansion (e : list binary64) (b : binary64)
  : list binary64 :=
  let '(hs, qfinal) := b64_grow_expansion_aux b (rev e) in
  qfinal :: rev hs.

(* -------------------------------------------------------------------------- *)
(* Specialisation to the chain3 use case.                                     *)
(*                                                                            *)
(* For `(a, b, c)`, the corresponding grow_expansion call is                  *)
(* `b64_grow_expansion [s1; e1] c` where `(s1, e1) := b64_TwoSum a b`.        *)
(* This produces a 3-component expansion whose sum is `a + b + c` and which  *)
(* (under the deferred nonoverlap proof) satisfies `nonoverlap_strict`.       *)
(*                                                                            *)
(* Replaces `b64_TwoSum_chain3` as the entry point for                       *)
(* nonoverlap-requiring consumers.  The naive `b64_TwoSum_chain3` is         *)
(* unchanged and continues to serve sum-correctness consumers.                *)
(* -------------------------------------------------------------------------- *)

Definition b64_TwoSum_chain3_sorted (a b c : binary64) : list binary64 :=
  let '(s1, e1) := b64_TwoSum a b in
  b64_grow_expansion (s1 :: e1 :: nil) c.

(* -------------------------------------------------------------------------- *)
(* SAFETY PRECONDITION for `b64_grow_expansion`.                              *)
(*                                                                            *)
(* The cascade visits each component of `rev e` in order, processing each   *)
(* with the current accumulator.  Per-step safety is the six-conjunct       *)
(* `b64_TwoSum_safe e_i Q_{i-1}`, where `Q_{i-1}` is the running            *)
(* accumulator.  We express this as a structural recursion on the cascade   *)
(* list.                                                                      *)
(*                                                                            *)
(* The previous spec commit (22b6ffe) had this as a `True` placeholder       *)
(* with a comment naming this exact obligation.  Filled in here in the      *)
(* proof session, as that commit's commit message anticipated.               *)
(* -------------------------------------------------------------------------- *)

Fixpoint b64_grow_expansion_aux_safe (q : binary64) (es : list binary64)
  : Prop :=
  match es with
  | nil => True
  | e :: es' =>
      b64_TwoSum_safe e q /\
      b64_grow_expansion_aux_safe (b64_plus e q) es'
  end.

Definition b64_grow_expansion_safe (e : list binary64) (b : binary64) : Prop :=
  b64_grow_expansion_aux_safe b (rev e).

(* -------------------------------------------------------------------------- *)
(* Structural helpers on `expansion_R`.                                       *)
(*                                                                            *)
(* These are list-shape lemmas the sum-correctness proof needs to thread     *)
(* the cascade's reverse-and-cascade-and-reverse structure to the           *)
(* underlying R-sum.  Local to this file because they are                   *)
(* `b64_FastExpansionSum`-specific consumers; if a downstream module needs  *)
(* them they can be promoted to `B64_Expansion.v`.                          *)
(* -------------------------------------------------------------------------- *)

Lemma expansion_R_app :
  forall xs ys : list binary64,
    expansion_R (xs ++ ys) = expansion_R xs + expansion_R ys.
Proof.
  induction xs as [|x xs' IH]; intros ys.
  - simpl. lra.
  - simpl. rewrite IH. lra.
Qed.

Lemma expansion_R_rev :
  forall xs : list binary64,
    expansion_R (rev xs) = expansion_R xs.
Proof.
  induction xs as [|x xs' IH]; simpl.
  - reflexivity.
  - rewrite expansion_R_app. simpl. rewrite IH. lra.
Qed.

(* The first projection of `b64_TwoSum x y` is exactly `b64_plus x y` --     *)
(* this is the defining shape of the TwoSum algorithm.  Reflexivity-close   *)
(* via zeta+iota reduction; named here as a helper so the proof below can   *)
(* relate the destructed-pair variable to the safety predicate's spelling.  *)
Lemma b64_TwoSum_fst :
  forall x y : binary64, fst (b64_TwoSum x y) = b64_plus x y.
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Cascade invariant (sum-correctness form).                                  *)
(*                                                                            *)
(* For any accumulator `q` and any input list `es` with per-step safety,    *)
(* the cascade's output `(hs, qfinal)` satisfies                             *)
(*   expansion_R hs + B2R qfinal = expansion_R es + B2R q.                  *)
(* Proof: structural induction on `es`, applying `b64_TwoSum_correct` at    *)
(* each cons step.  The first-projection identity `b64_TwoSum_fst` connects *)
(* the destructed `qnew` variable to the `b64_plus e q` spelling that       *)
(* `b64_grow_expansion_aux_safe`'s recursive call uses.                      *)
(* -------------------------------------------------------------------------- *)

Lemma b64_grow_expansion_aux_correct :
  forall (es : list binary64) (q : binary64),
    b64_grow_expansion_aux_safe q es ->
    forall hs qfinal,
      b64_grow_expansion_aux q es = (hs, qfinal) ->
      expansion_R hs + Binary.B2R prec emax qfinal
        = expansion_R es + Binary.B2R prec emax q.
Proof.
  induction es as [|e es' IH]; intros q Hsafe hs qfinal Heq.
  - (* Base case: empty cascade returns (nil, q). *)
    cbn [b64_grow_expansion_aux] in Heq.
    injection Heq as <- <-.
    cbn [expansion_R].
    lra.
  - (* Cons case: one TwoSum step, then recurse. *)
    cbn [b64_grow_expansion_aux_safe] in Hsafe.
    destruct Hsafe as [Hstep Hrest].
    unfold b64_TwoSum_safe in Hstep.
    destruct Hstep as [Hsa [Hsb [Hsc [Hsd [Hse Hsf]]]]].
    pose proof (b64_TwoSum_correct e q Hsa Hsb Hsc Hsd Hse Hsf) as HTC.
    cbn [b64_grow_expansion_aux] in Heq.
    destruct (b64_TwoSum e q) as [qnew hh] eqn:HTS.
    destruct (b64_grow_expansion_aux qnew es') as [hs' qfinal'] eqn:Hrec.
    (* `destruct ... eqn:` substitutes the discriminee everywhere and       *)
    (* iota-reduces the resulting let-patterns, so HTC is already in the   *)
    (* `B2R qnew + B2R hh = B2R e + B2R q` shape and Heq has collapsed to  *)
    (* the bare pair equality.                                              *)
    injection Heq as <- <-.
    assert (Hqnew : qnew = b64_plus e q).
    { rewrite <- (b64_TwoSum_fst e q). rewrite HTS. reflexivity. }
    subst qnew.
    specialize (IH (b64_plus e q) Hrest hs' qfinal' Hrec).
    cbn [expansion_R].
    lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* THEOREM 1: sum preservation.                                               *)
(*                                                                            *)
(* Composes `b64_grow_expansion_aux_correct` with the `expansion_R_rev`       *)
(* invariant of the top-level reverse-cascade-reverse structure.              *)
(* -------------------------------------------------------------------------- *)

Theorem b64_grow_expansion_correct :
  forall (e : list binary64) (b : binary64),
    b64_grow_expansion_safe e b ->
    expansion_R (b64_grow_expansion e b)
      = expansion_R e + Binary.B2R prec emax b.
Proof.
  intros e b Hsafe.
  unfold b64_grow_expansion, b64_grow_expansion_safe in *.
  destruct (b64_grow_expansion_aux b (rev e)) as [hs qfinal] eqn:Hrec.
  pose proof (b64_grow_expansion_aux_correct (rev e) b Hsafe hs qfinal Hrec)
    as Hinv.
  rewrite expansion_R_rev in Hinv.
  rewrite expansion_R_cons.
  rewrite expansion_R_rev.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* THEOREM 2: nonoverlap preservation.                                        *)
(*                                                                            *)
(* HEADLINE.  This is the load-bearing piece for the rest of Stage D:         *)
(* every consumer of `sign_of_expansion_correct` on a chain output relies   *)
(* on this property to discharge the precondition.                            *)
(*                                                                            *)
(* STATUS: TANGENT.  The theorem is NOT provable as stated.                   *)
(* See `docs/stage-d-grow-expansion-nonoverlap-tangent.md` for the full      *)
(* analysis: `nonoverlap_strict` (B64_Expansion.v:90) does not tolerate      *)
(* internal zeros, but the cascade naturally produces zeros at any step      *)
(* whose TwoSum is exact.  A binary64 counterexample is documented in the   *)
(* tangent doc (input `e = [2^100; 2^45]`, `b = 2^48 - 2^45 + 2^(-5)`):     *)
(* the cascade output `[2^100 + 2^48; 0; 2^(-5)]` violates                  *)
(* `strict_succ_b64 0 (2^(-5))` by a factor of `2^(1070)`.                  *)
(*                                                                            *)
(* The next session makes a design call between two options:                 *)
(*   A. Weaken `nonoverlap_strict` to tolerate internal zeros, re-prove     *)
(*      `sign_of_expansion_correct` for the weaker predicate.                *)
(*   B. Add a `compress` step to `b64_grow_expansion` that filters zeros.   *)
(* The tangent doc recommends Option A on three grounds.                     *)
(* -------------------------------------------------------------------------- *)

Theorem b64_grow_expansion_nonoverlap :
  forall (e : list binary64) (b : binary64),
    b64_grow_expansion_safe e b ->
    nonoverlap_strict e ->
    nonoverlap_strict (b64_grow_expansion e b).
Proof.
  (* TANGENT: documented in docs/stage-d-grow-expansion-nonoverlap-tangent.md *)
  (* Theorem statement is incompatible with the algorithm; the next session  *)
  (* picks the predicate-weakening or compress-filter resolution.            *)
Admitted.

(* -------------------------------------------------------------------------- *)
(* COROLLARY (deferred): chain3-sorted sum + nonoverlap.                      *)
(*                                                                            *)
(* The intended consumer of this file: composing the two theorems above to  *)
(* get a chain3 output that satisfies both sum-correctness and nonoverlap.  *)
(* Sum half can land now (since `b64_grow_expansion_correct` is Qed-closed) *)
(* but is kept off until the nonoverlap half lands too, so the file's      *)
(* corollaries ship as a single block.                                      *)
(* -------------------------------------------------------------------------- *)

(* Theorem b64_TwoSum_chain3_sorted_correct : ... (deferred) *)
(* Theorem b64_TwoSum_chain3_sorted_nonoverlap : ... (deferred) *)

(* ============================================================================
   Option C: magnitude-dominated cascade.

   Per `docs/stage-d-grow-expansion-nonoverlap-tangent.md` §9, the
   cascade with `b64_TwoSum` only preserves `nonoverlap_strict` under
   a magnitude precondition on the new value `b` relative to the
   input expansion `e`.  Specifically, when `b` sits at the bottom of
   the nonoverlap chain (`nonoverlap_strict (e ++ [b])` holds for the
   appended list), every `b64_TwoSum` step in the cascade is exact:
   `b64_TwoSum e_i Q_{i-1}` returns `(e_i, Q_{i-1})` without rounding
   error.  The cascade output is then structurally `e ++ [b]`, which
   is nonoverlap_strict by the precondition.

   This is the RESTRICTED Option C: handles the "small b" regime where
   b is dominated by the smallest input.  The general b case (b not
   dominated) is the deferred multi-session work.

   HYPOTHESIS (for the helper lemma): under STRICT `|y| < ulp(x)/2`
   and `x in format`, `round(x + y) = x`.  Holds for positive
   non-boundary x via Flocq's `round_N_le_midp` + `succ_eq_pos`.
   Boundary cases (x at binade boundaries, x = 0, x negative) need
   additional case analysis and are the remaining tangent in the
   helper.
   ============================================================================ *)

(* ============================================================================
   COUNTEREXAMPLE: the naive helper `|y| < ulp(x)/2` is FALSE at
   binade boundaries (`x = 2^k`).
   ----------------------------------------------------------------------------
   Witness:  x = 1 (= bpow 0, a positive binade boundary).
             y = -3 * bpow(-55).
   - |y| = 3 * bpow(-55) < bpow(-53) = ulp(1)/2.  Precondition HOLDS.
   - pred 1 = 1 - ulp(pred 1) = 1 - bpow(-53)  (lower binade has half ulp).
   - midpoint = (1 + pred 1) / 2 = 1 - bpow(-54).
   - x + y = 1 - 3 * bpow(-55) < 1 - bpow(-54).
   - So round(x + y) <= pred 1 < 1.  Conclusion FAILS.
   ============================================================================ *)

Lemma b64_bpow_minus_53_eq_4 :
  bpow radix2 (-53) = 4 * bpow radix2 (-55).
Proof.
  assert (Hbpow2 : bpow radix2 2 = 4).
  simpl. lra.
  rewrite <- Hbpow2.
  rewrite <- bpow_plus.
  reflexivity.
Qed.

Lemma b64_bpow_minus_54_eq_2 :
  bpow radix2 (-54) = 2 * bpow radix2 (-55).
Proof.
  assert (Hbpow1 : bpow radix2 1 = 2).
  simpl. lra.
  rewrite <- Hbpow1.
  rewrite <- bpow_plus.
  reflexivity.
Qed.

(* P1: the witness's |y| satisfies the loose precondition |y| < ulp(x)/2. *)
Lemma counterex_loose_precondition_holds :
  Rabs (- (3 * bpow radix2 (-55))) < bpow radix2 (-53).
Proof.
  rewrite Rabs_Ropp.
  rewrite Rabs_pos_eq.
  - rewrite b64_bpow_minus_53_eq_4.
    pose proof (bpow_gt_0 radix2 (-55)).
    lra.
  - pose proof (bpow_gt_0 radix2 (-55)).
    lra.
Qed.

(* P2: the witness x + y is strictly below the FLT midpoint. *)
Lemma counterex_below_midpoint :
  1 + - (3 * bpow radix2 (-55)) < 1 - bpow radix2 (-54).
Proof.
  rewrite b64_bpow_minus_54_eq_2.
  pose proof (bpow_gt_0 radix2 (-55)).
  lra.
Qed.

(* P3: the gap magnitude. |y| = 3 * bpow(-55) sits STRICTLY between
   the boundary-needed bound ulp(pred x)/2 = bpow(-54) and the loose
   ulp(x)/2 = bpow(-53).  Factor of 2 violation at the boundary. *)
Lemma counterex_gap_magnitude :
  bpow radix2 (-54) < 3 * bpow radix2 (-55) < bpow radix2 (-53).
Proof.
  rewrite b64_bpow_minus_53_eq_4.
  rewrite b64_bpow_minus_54_eq_2.
  pose proof (bpow_gt_0 radix2 (-55)).
  split; lra.
Qed.

(* ============================================================================
   PATH A: TIGHTER PRECONDITION using `ulp(pred x) / 2` instead of
   `ulp(x) / 2`.  At interior `x` this is the same (ulp constant within
   binade); at boundary `x = 2^k` this is half as much (the lower-binade
   ulp).  The counterexample witness is excluded under this stricter
   bound by the gap (P3 above).

   `round_eq_pathA_positive` is Qed-closed: positive x in any binade,
   strict ulp-of-pred dominance => round(x+y) = x.  The negative case
   is the next bounded tangent.
   ============================================================================ *)

Lemma round_eq_pathA_positive :
  forall x y : R,
    0 < x ->
    generic_format radix2 (SpecFloat.fexp prec emax) x ->
    Rabs y < ulp radix2 (SpecFloat.fexp prec emax)
                  (pred radix2 (SpecFloat.fexp prec emax) x) / 2 ->
    round radix2 (SpecFloat.fexp prec emax) (round_mode mode_b64) (x + y) = x.
Proof.
  intros x y Hxpos Hfx Hy.
  pose proof (@pred_ge_0 radix2 _ b64_fexp_valid x Hxpos Hfx) as Hpred_ge0.
  pose proof (pred_le_id radix2 (SpecFloat.fexp prec emax) x) as Hpred_le_x.
  pose proof (@ulp_le_pos radix2 _ b64_fexp_valid b64_fexp_monotone _ _
                Hpred_ge0 Hpred_le_x) as Hulp_le.
  apply Rle_antisym.
  - change (round_mode mode_b64) with (Znearest (fun n => negb (Z.even n))).
    apply (@round_N_le_midp radix2 (SpecFloat.fexp prec emax) b64_fexp_valid
             (fun n => negb (Z.even n)) x (x + y) Hfx).
    rewrite (succ_eq_pos radix2 _ _ (Rlt_le _ _ Hxpos)).
    apply Rabs_lt_inv in Hy. lra.
  - change (round_mode mode_b64) with (Znearest (fun n => negb (Z.even n))).
    apply (@round_N_ge_midp radix2 (SpecFloat.fexp prec emax) b64_fexp_valid
             (fun n => negb (Z.even n)) x (x + y) Hfx).
    apply Rabs_lt_inv in Hy.
    pose proof (@pred_plus_ulp radix2 _ b64_fexp_valid x Hxpos Hfx) as Hpp.
    lra.
Qed.

(* The negative-x case via `round_NE_opp` symmetry.  For x < 0, the
   asymmetric midpoint flips: succ x (not pred x) has the boundary
   issue, so the precondition uses `ulp(succ x) / 2`. *)
Lemma round_eq_pathA_negative :
  forall x y : R,
    x < 0 ->
    generic_format radix2 (SpecFloat.fexp prec emax) x ->
    Rabs y < ulp radix2 (SpecFloat.fexp prec emax)
                  (succ radix2 (SpecFloat.fexp prec emax) x) / 2 ->
    round radix2 (SpecFloat.fexp prec emax) (round_mode mode_b64) (x + y) = x.
Proof.
  intros x y Hxneg Hfx Hy.
  assert (Hxopp : 0 < -x) by lra.
  assert (Hfx_opp : generic_format radix2 (SpecFloat.fexp prec emax) (-x)).
  { apply generic_format_opp. exact Hfx. }
  assert (Hy_opp : Rabs (-y) <
                   ulp radix2 (SpecFloat.fexp prec emax)
                       (pred radix2 (SpecFloat.fexp prec emax) (-x)) / 2).
  { rewrite Rabs_Ropp. rewrite pred_opp. rewrite ulp_opp. exact Hy. }
  pose proof (round_eq_pathA_positive (-x) (-y) Hxopp Hfx_opp Hy_opp) as Hr.
  replace (-x + -y) with (-(x + y)) in Hr by ring.
  rewrite round_NE_opp in Hr.
  apply (f_equal Ropp) in Hr.
  rewrite !Ropp_involutive in Hr.
  exact Hr.
Qed.

(* The zero case: x = 0.  The round-to-0 interval is symmetric
   (-ulp(0)/2, +ulp(0)/2) since both pred 0 and succ 0 are at distance
   ulp(0).  Simpler than positive/negative because no binade boundary. *)
Lemma round_eq_pathA_zero :
  forall y : R,
    Rabs y < ulp radix2 (SpecFloat.fexp prec emax) 0 / 2 ->
    round radix2 (SpecFloat.fexp prec emax) (round_mode mode_b64) (0 + y) = 0.
Proof.
  intros y Hy.
  rewrite Rplus_0_l.
  pose proof (pred_0 radix2 (SpecFloat.fexp prec emax)) as Hp.
  pose proof (succ_0 radix2 (SpecFloat.fexp prec emax)) as Hs.
  apply Rle_antisym.
  - change (round_mode mode_b64) with (Znearest (fun n => negb (Z.even n))).
    apply (@round_N_le_midp radix2 (SpecFloat.fexp prec emax) b64_fexp_valid
             (fun n => negb (Z.even n)) 0 y).
    + apply generic_format_0.
    + rewrite Hs.
      apply Rabs_lt_inv in Hy. lra.
  - change (round_mode mode_b64) with (Znearest (fun n => negb (Z.even n))).
    apply (@round_N_ge_midp radix2 (SpecFloat.fexp prec emax) b64_fexp_valid
             (fun n => negb (Z.even n)) 0 y).
    + apply generic_format_0.
    + rewrite Hp.
      apply Rabs_lt_inv in Hy. lra.
Qed.

(* The original loose-precondition helper -- NOT provable as stated
   (counterexample above).  Kept as documentation of the failed
   hypothesis; the cascade theorem migrates to Path A's tighter
   precondition. *)
Lemma round_eq_under_strict_dominance :
  forall x y : R,
    generic_format radix2 (SpecFloat.fexp prec emax) x ->
    Rabs y < ulp radix2 (SpecFloat.fexp prec emax) x / 2 ->
    round radix2 (SpecFloat.fexp prec emax) (round_mode mode_b64) (x + y) = x.
Proof.
  (* TANGENT: FALSE at binade boundaries x = 2^k.  See counterexample
     lemmas counterex_loose_precondition_holds, counterex_below_midpoint,
     counterex_gap_magnitude above (all Qed-closed).  Resolution: migrate
     to `round_eq_pathA_positive` with tighter precondition `|y| < ulp(pred x)/2`. *)
Admitted.

(* Under strict dominance, `b64_plus x y = x` at the R-level.  This is
   the Path A version using the tighter `ulp(pred x)/2` bound and
   restricted to positive x.  Qed-closed. *)
Lemma b64_plus_under_pathA_dominance :
  forall x y : binary64,
    0 < Binary.B2R prec emax x ->
    b64_safe Rplus x y ->
    Rabs (Binary.B2R prec emax y) <
      ulp radix2 (SpecFloat.fexp prec emax)
        (pred radix2 (SpecFloat.fexp prec emax) (Binary.B2R prec emax x)) / 2 ->
    Binary.B2R prec emax (b64_plus x y) = Binary.B2R prec emax x.
Proof.
  intros x y Hxpos Hsafe Hy.
  pose proof (b64_plus_correct x y Hsafe) as [HB2R _].
  rewrite HB2R.
  apply round_eq_pathA_positive.
  - exact Hxpos.
  - apply b64_format_B2R.
  - exact Hy.
Qed.

(* The original `b64_plus_under_strict_dominance` is admitted because  *)
(* it cites the false `round_eq_under_strict_dominance`.  Kept as the  *)
(* historical statement; consumers should use Path A's variant.        *)
Lemma b64_plus_under_strict_dominance :
  forall x y : binary64,
    b64_safe Rplus x y ->
    Rabs (Binary.B2R prec emax y)
      < ulp radix2 (SpecFloat.fexp prec emax) (Binary.B2R prec emax x) / 2 ->
    Binary.B2R prec emax (b64_plus x y) = Binary.B2R prec emax x.
Proof.
  intros x y Hsafe Hy.
  pose proof (b64_plus_correct x y Hsafe) as [HB2R _].
  rewrite HB2R.
  apply round_eq_under_strict_dominance.
  - apply b64_format_B2R.
  - exact Hy.
Qed.

(* The cascade theorem statement under the dominance precondition.
   Captures the "b sits at the bottom of the nonoverlap chain" case.

   The proof requires showing each TwoSum step is exact, which needs
   `round_eq_under_strict_dominance` (admitted above for boundary
   cases).  Even under that helper, the cascade-structure proof
   threads the dominance invariant through each induction step,
   relating `Q_i` (= `e_i` under dominance) to the next step's `e_{i+1}`.

   STATUS: theorem stated, structural shape compiles, proof attempts
   the induction.  The actual Qed-close depends on (a) the helper
   lemma's tangent resolution and (b) the cascade invariant's
   formalisation.  Both are concrete follow-up work, not blockers
   for the Option C scoping. *)

Theorem b64_grow_expansion_nonoverlap_dominated :
  forall (e : list binary64) (b : binary64),
    b64_grow_expansion_safe e b ->
    nonoverlap_strict (e ++ b :: nil) ->
    nonoverlap_strict (b64_grow_expansion e b).
Proof.
  (* TANGENT: proof depends on `round_eq_under_strict_dominance`        *)
  (* (admitted above pending boundary-case resolution) AND the cascade  *)
  (* invariant lemma that the cascade output equals `e ++ [b]` under    *)
  (* this precondition.  The cascade invariant has been proved below as *)
  (* `b64_grow_expansion_aux_pathA_matches`; the remaining work is the  *)
  (* compress + nonoverlap-from-B2R lemmas to finish the composition.    *)
Admitted.

(* ============================================================================
   PATH A CASCADE-STRUCTURE INVARIANT (Qed-closed).

   Three new artifacts piece together the cascade-structure argument:

     - `strict_succ_pathA_R` / `cascade_pathA_dominates_aux`:
       the Path A predicate chain on B2R values.

     - `b64_TwoSum_pathA_exact_step`: under Path A's pairwise strict
       precondition + positivity, the TwoSum step is R-exact:
       `B2R (fst (b64_TwoSum e q)) = B2R e` AND
       `B2R (snd (b64_TwoSum e q)) = B2R q`.

     - `b64_grow_expansion_aux_pathA_matches`: the load-bearing
       invariant.  Under cascade_pathA_dominates_aux on (q, es) +
       per-op safety, the cascade output's B2R values match
       `rev es ++ [q]` componentwise.

   With these, the composition into `b64_grow_expansion_nonoverlap_*`
   is mechanical: combine with a nonoverlap-preserves-under-B2R-equiv
   lemma plus a compress-no-op-when-nonzero argument.  Both are bounded
   list-shape lemmas, ~30-50 lines each.  Total remaining: ~couple of
   hours for the composition.
   ============================================================================ *)

Definition strict_succ_pathA_R (a b : R) : Prop :=
  Rabs b < ulp radix2 (SpecFloat.fexp prec emax)
                 (pred radix2 (SpecFloat.fexp prec emax) a) / 2.

Fixpoint cascade_pathA_dominates_aux
  (q : binary64) (es : list binary64) : Prop :=
  match es with
  | nil => True
  | e :: es' =>
      0 < Binary.B2R prec emax e /\
      strict_succ_pathA_R (Binary.B2R prec emax e) (Binary.B2R prec emax q) /\
      cascade_pathA_dominates_aux e es'
  end.

Lemma b64_TwoSum_pathA_exact_step :
  forall e q : binary64,
    0 < Binary.B2R prec emax e ->
    strict_succ_pathA_R (Binary.B2R prec emax e) (Binary.B2R prec emax q) ->
    b64_TwoSum_safe e q ->
    Binary.B2R prec emax (fst (b64_TwoSum e q)) = Binary.B2R prec emax e /\
    Binary.B2R prec emax (snd (b64_TwoSum e q))
      = Binary.B2R prec emax q.
Proof.
  intros e q He Hpw Hsafe.
  unfold b64_TwoSum_safe in Hsafe.
  destruct Hsafe as [Hs1 [Hs2 [Hs3 [Hs4 [Hs5 Hs6]]]]].
  pose proof (b64_TwoSum_correct e q Hs1 Hs2 Hs3 Hs4 Hs5 Hs6) as HTC.
  destruct (b64_TwoSum e q) as [a b] eqn:HTS.
  cbn [fst snd] in *.
  assert (Ha : a = b64_plus e q).
  { rewrite <- (b64_TwoSum_fst e q). rewrite HTS. reflexivity. }
  subst a.
  pose proof (b64_plus_under_pathA_dominance e q He Hs1 Hpw) as HBplus_eq.
  split. exact HBplus_eq. lra.
Qed.

Lemma cascade_pathA_dominates_aux_B2R_compat :
  forall a b es,
    Binary.B2R prec emax a = Binary.B2R prec emax b ->
    cascade_pathA_dominates_aux a es ->
    cascade_pathA_dominates_aux b es.
Proof.
  intros a b es Hab Hdom.
  destruct es as [|e es']; cbn [cascade_pathA_dominates_aux] in *.
  exact I.
  destruct Hdom as [He [Hpw Hchain]].
  split. exact He. split. rewrite <- Hab. exact Hpw. exact Hchain.
Qed.

Definition cascade_output_R_matches
  (hs : list binary64) (qfinal : binary64)
  (q : binary64) (es : list binary64) : Prop :=
  map (Binary.B2R prec emax) (qfinal :: rev hs)
  = map (Binary.B2R prec emax) (rev es ++ q :: nil).

(* The headline cascade-structure invariant: under Path A's chain
   precondition + safety, the cascade output's B2R values match
   `rev es ++ [q]` componentwise. *)
Lemma b64_grow_expansion_aux_pathA_matches :
  forall (es : list binary64) (q : binary64),
    b64_grow_expansion_aux_safe q es ->
    cascade_pathA_dominates_aux q es ->
    let '(hs, qfinal) := b64_grow_expansion_aux q es in
    cascade_output_R_matches hs qfinal q es.
Proof.
  induction es as [|e es' IH]; intros q Hsafe Hdom.
  - cbn [b64_grow_expansion_aux].
    unfold cascade_output_R_matches.
    cbn. reflexivity.
  - cbn [b64_grow_expansion_aux].
    cbn [b64_grow_expansion_aux_safe] in Hsafe.
    destruct Hsafe as [Hstep Hrest].
    cbn [cascade_pathA_dominates_aux] in Hdom.
    destruct Hdom as [He [Hpw Hchain]].
    destruct (b64_TwoSum e q) as [qnew hh] eqn:HTS.
    pose proof (b64_TwoSum_pathA_exact_step e q He Hpw Hstep) as [Hqnew Hhh].
    rewrite HTS in Hqnew, Hhh. cbn [fst snd] in Hqnew, Hhh.
    assert (Hqnew_eq : qnew = b64_plus e q).
    { rewrite <- (b64_TwoSum_fst e q). rewrite HTS. reflexivity. }
    rewrite <- Hqnew_eq in Hrest.
    pose proof (cascade_pathA_dominates_aux_B2R_compat e qnew es'
                  (eq_sym Hqnew) Hchain) as Hchain'.
    specialize (IH qnew Hrest Hchain').
    destruct (b64_grow_expansion_aux qnew es') as [hs' qfinal'] eqn:Hrec.
    unfold cascade_output_R_matches in IH.
    unfold cascade_output_R_matches.
    cbn [rev]. cbn [rev] in IH.
    rewrite app_comm_cons.
    rewrite map_app, map_app, map_app.
    rewrite map_app in IH.
    cbn [map] in IH |- *.
    rewrite Hqnew in IH.
    rewrite Hhh.
    f_equal.
    exact IH.
Qed.

(* ============================================================================
   PATH A COMPOSITION (Piece-3): the final theorem under the strict
   Path A precondition.

   `b64_grow_expansion_nonoverlap_pathA` Qed-closes:  under
   `cascade_pathA_dominates_aux b (rev e)` + safety, the cascade output
   is `nonoverlap_strict`.

   Three structural helpers + the composition.  Total ~80 lines.
   ============================================================================ *)

(* Helper P3-1: nonoverlap_strict is B2R-componentwise compatible. *)
Lemma nonoverlap_strict_B2R_compat :
  forall xs ys : list binary64,
    map (Binary.B2R prec emax) xs = map (Binary.B2R prec emax) ys ->
    nonoverlap_strict xs <-> nonoverlap_strict ys.
Proof.
  induction xs as [|x xs IH]; intros ys Hmap.
  - destruct ys as [|y ys].
    + split; intros; cbn; exact I.
    + simpl in Hmap. discriminate.
  - destruct ys as [|y ys].
    + simpl in Hmap. discriminate.
    + simpl in Hmap. inversion Hmap as [[Hxy Hxsys]].
      destruct xs as [|x' xs'].
      * destruct ys as [|y' ys'].
        -- split; intros _; exact I.
        -- simpl in Hxsys. discriminate.
      * destruct ys as [|y' ys'].
        -- simpl in Hxsys. discriminate.
        -- simpl in Hxsys. inversion Hxsys as [[Hxy' Hrest]].
           split; intros [Hsucc Hno].
           ++ split.
              ** unfold strict_succ_b64 in *. rewrite <- Hxy, <- Hxy'. exact Hsucc.
              ** specialize (IH (y' :: ys')).
                 simpl in IH.
                 destruct (IH ltac:(simpl; f_equal; auto)) as [Hxy_imp _].
                 apply Hxy_imp. exact Hno.
           ++ split.
              ** unfold strict_succ_b64 in *. rewrite Hxy, Hxy'. exact Hsucc.
              ** specialize (IH (y' :: ys')).
                 destruct (IH ltac:(simpl; f_equal; auto)) as [_ Hyx_imp].
                 apply Hyx_imp. exact Hno.
Qed.

(* Helper P3-2: snoc preserves nonoverlap_strict when the new tail is
   in strict_succ relation with the (current) last element. *)
Lemma nonoverlap_strict_snoc :
  forall xs x y,
    nonoverlap_strict (xs ++ x :: nil) ->
    strict_succ_b64 x y ->
    nonoverlap_strict (xs ++ x :: y :: nil).
Proof.
  induction xs as [|x' xs' IH]; intros x y Hno Hsucc.
  - cbn in Hno |- *.
    split. exact Hsucc. exact I.
  - cbn in Hno |- *.
    destruct xs' as [|x'' xs''] eqn:Hxs'.
    + cbn in *. destruct Hno as [Hsucc' _].
      split. exact Hsucc'. split. exact Hsucc. exact I.
    + cbn in *. destruct Hno as [Hsucc' Hrest].
      split. exact Hsucc'. apply IH. exact Hrest. exact Hsucc.
Qed.

(* Path A's strict bound implies the loose `strict_succ_b64`. *)
Lemma strict_succ_pathA_R_implies_strict_succ_b64 :
  forall a b : binary64,
    0 < Binary.B2R prec emax a ->
    strict_succ_pathA_R (Binary.B2R prec emax a) (Binary.B2R prec emax b) ->
    strict_succ_b64 a b.
Proof.
  intros a b Ha Hpw.
  unfold strict_succ_pathA_R in Hpw.
  unfold strict_succ_b64.
  pose proof (b64_format_B2R a) as Hfa.
  pose proof (@pred_ge_0 radix2 _ b64_fexp_valid (Binary.B2R prec emax a) Ha Hfa) as Hpa.
  pose proof (pred_le_id radix2 (SpecFloat.fexp prec emax) (Binary.B2R prec emax a)) as Hpa_le.
  pose proof (@ulp_le_pos radix2 _ b64_fexp_valid b64_fexp_monotone _ _
                Hpa Hpa_le) as Hulp_le.
  lra.
Qed.

(* Helper P3-3: cascade_pathA_dominates_aux implies nonoverlap_strict
   on the appended chain (rev es ++ [b]). *)
Lemma cascade_pathA_dominates_implies_nonoverlap :
  forall es b,
    cascade_pathA_dominates_aux b es ->
    nonoverlap_strict (rev es ++ b :: nil).
Proof.
  induction es as [|e es' IH]; intros b Hdom.
  - cbn. exact I.
  - cbn [cascade_pathA_dominates_aux] in Hdom.
    destruct Hdom as [He [Hpw Hchain]].
    specialize (IH e Hchain).
    cbn [rev]. rewrite <- app_assoc. cbn [app].
    apply nonoverlap_strict_snoc.
    + exact IH.
    + apply strict_succ_pathA_R_implies_strict_succ_b64; assumption.
Qed.

(* HEADLINE: under the Path A precondition + safety, the cascade
   output is `nonoverlap_strict`.  Composition of the cascade
   invariant + the B2R-compat lemma + the dominates-implies-nonoverlap
   chain.

   Differs from the original `b64_grow_expansion_nonoverlap_dominated`
   in using the STRICTER `cascade_pathA_dominates_aux` precondition
   instead of the loose `nonoverlap_strict (e ++ [b])`.  The latter
   is not sufficient at binade boundaries (see counterexample
   lemmas above); the Path A precondition rules those out. *)
Theorem b64_grow_expansion_nonoverlap_pathA :
  forall (e : list binary64) (b : binary64),
    b64_grow_expansion_safe e b ->
    cascade_pathA_dominates_aux b (rev e) ->
    nonoverlap_strict (b64_grow_expansion e b).
Proof.
  intros e b Hsafe Hdom.
  unfold b64_grow_expansion.
  unfold b64_grow_expansion_safe in Hsafe.
  destruct (b64_grow_expansion_aux b (rev e)) as [hs qfinal] eqn:Hrec.
  pose proof (b64_grow_expansion_aux_pathA_matches (rev e) b Hsafe Hdom) as Hinv.
  rewrite Hrec in Hinv.
  unfold cascade_output_R_matches in Hinv.
  rewrite rev_involutive in Hinv.
  pose proof (cascade_pathA_dominates_implies_nonoverlap (rev e) b Hdom) as Hno_input.
  rewrite rev_involutive in Hno_input.
  apply (proj2 (nonoverlap_strict_B2R_compat _ _ Hinv)).
  exact Hno_input.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_grow_expansion_correct.
Print Assumptions b64_grow_expansion_nonoverlap_pathA.
