(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_FastExpansionSum
   ----------------------------------------------------------------------------
   Stage D chain composition primitive: Shewchuk's GROW-EXPANSION at binary64.

   DESIGN ARTIFACT (Approach A).  This file lands the definition of
   `b64_grow_expansion` (and the auxiliary cascade body) plus the
   theorem statements that the next session is expected to close.
   Both headline theorems are `Admitted` and tagged with the
   `(* TANGENT: proof deferred pending design validation *)` marker.

   CI's Qed-invariant grep (no Admitted, no Axiom, no Parameter) flags
   this file on every push of this branch.  THAT FLAG IS THE CORRECT
   BEHAVIOUR.  The companion commit message acknowledges the flag
   explicitly.  Do not edit the markers or suppress the check; the
   markers come out when the proofs come in.

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
(* ordering `|Q| ≤ |e_i|` in general -- the cascade invariant has to be     *)
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
(* (under the deferred proof) satisfies `nonoverlap_strict`.                  *)
(*                                                                            *)
(* Replaces `b64_TwoSum_chain3` as the entry point for                       *)
(* nonoverlap-requiring consumers.  The naive `b64_TwoSum_chain3` is         *)
(* unchanged and continues to serve sum-correctness consumers.                *)
(* -------------------------------------------------------------------------- *)

Definition b64_TwoSum_chain3_sorted (a b c : binary64) : list binary64 :=
  let '(s1, e1) := b64_TwoSum a b in
  b64_grow_expansion (s1 :: e1 :: nil) c.

(* -------------------------------------------------------------------------- *)
(* SAFETY PRECONDITIONS for `b64_grow_expansion`.                             *)
(*                                                                            *)
(* Placeholder: in this session we name the obligation but do not unfold it. *)
(* The next session will derive the concrete per-op safety conjuncts from   *)
(* a magnitude-bounded interface (the analogue of `b64_orient2d_inputs_safe`*)
(* for chain3 inputs).                                                        *)
(* -------------------------------------------------------------------------- *)

Definition b64_grow_expansion_safe (e : list binary64) (b : binary64) : Prop :=
  expansion_finite e /\
  Binary.is_finite prec emax b = true /\
  (* The full safety predicate is the conjunction of `b64_TwoSum_safe` for *)
  (* every TwoSum invocation in the cascade.  Concrete form deferred to    *)
  (* the proof session; this placeholder keeps the theorem statements      *)
  (* well-typed.                                                            *)
  True.

(* -------------------------------------------------------------------------- *)
(* THEOREM STATEMENT 1: sum preservation.                                     *)
(*                                                                            *)
(* `b64_grow_expansion e b` represents exactly `expansion_R e + B2R b` as    *)
(* the sum of its components.  The TwoSum cascade is exact at every step,   *)
(* so the running sum is preserved through the entire chain.                *)
(*                                                                            *)
(* Proof plan (next session):                                                *)
(*   - Induction on `es` for `b64_grow_expansion_aux`.                       *)
(*   - Each `b64_TwoSum` step preserves the sum exactly via                  *)
(*     `b64_TwoSum_correct`.                                                  *)
(*   - The reverse/cascade/reverse structure preserves the total sum         *)
(*     (sum is commutative under R).                                          *)
(* -------------------------------------------------------------------------- *)

Theorem b64_grow_expansion_correct :
  forall (e : list binary64) (b : binary64),
    b64_grow_expansion_safe e b ->
    expansion_R (b64_grow_expansion e b) = expansion_R e + Binary.B2R prec emax b.
Proof.
  (* TANGENT: proof deferred pending design validation *)
Admitted.

(* -------------------------------------------------------------------------- *)
(* THEOREM STATEMENT 2: nonoverlap preservation.                              *)
(*                                                                            *)
(* HEADLINE.  This is the load-bearing piece for the rest of Stage D:         *)
(* every consumer of `sign_of_expansion_correct` on a chain output relies   *)
(* on this property to discharge the precondition.                            *)
(*                                                                            *)
(* Proof plan (next session):                                                *)
(*   - Induction on the cascade.  At each step, the TwoSum's output         *)
(*     satisfies `|h_i| ≤ ulp(Q_i) / 2` via `b64_TwoSum_nonoverlap`.        *)
(*   - The chained `Q_i` accumulator is monotonically larger in magnitude   *)
(*     than the previous `h_{i-1}`, giving the chain                          *)
(*     `|h_{i-1}| ≤ ulp(Q_i) / 2 ≤ ulp(h_i_prev) / 2`.                       *)
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
(* Will be Qed-closed in the next session as a consequence of                *)
(* `b64_grow_expansion_correct` + `b64_TwoSum_correct` +                    *)
(* `b64_grow_expansion_nonoverlap` + `b64_TwoSum_nonoverlap`.                *)
(* -------------------------------------------------------------------------- *)

(* Theorem b64_TwoSum_chain3_sorted_correct : ... (deferred) *)
(* Theorem b64_TwoSum_chain3_sorted_nonoverlap : ... (deferred) *)

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(*                                                                            *)
(* Print Assumptions blocks intentionally NOT included here while the        *)
(* headline theorems are Admitted -- they would surface the Admitted axiom  *)
(* in the per-theorem audit and obscure the (also valid) Classical_Prop     *)
(* tracking.  Reinstate once the proofs land.                                *)
(* -------------------------------------------------------------------------- *)
