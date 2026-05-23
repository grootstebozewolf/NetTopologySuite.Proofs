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
From Flocq Require Import Core.

From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import B64_bridge.
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
(* Proof plan (next session):                                                *)
(*   - Induction on the cascade.  At each step, the TwoSum's output         *)
(*     satisfies `|h_i| <= ulp(Q_i) / 2` via `b64_TwoSum_nonoverlap`.       *)
(*   - The chained `Q_i` accumulator is monotonically larger in magnitude   *)
(*     than the previous `h_{i-1}`, giving the chain                          *)
(*     `|h_{i-1}| <= ulp(Q_i) / 2 <= ulp(h_i_prev) / 2`.                     *)
(*   - The exact invariant carrying the cascade is the deferred work.       *)
(* -------------------------------------------------------------------------- *)

Theorem b64_grow_expansion_nonoverlap :
  forall (e : list binary64) (b : binary64),
    b64_grow_expansion_safe e b ->
    nonoverlap_strict e ->
    nonoverlap_strict (b64_grow_expansion e b).
Proof.
  (* TANGENT: proof deferred pending design validation *)
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

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_grow_expansion_correct.
