(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_pathB_trace_4A
   ----------------------------------------------------------------------------
   Shewchuk Theorem 13, §4.A verification (obligation gating).

   Machine-checked vm_compute witnesses that pathB (exact-cancellation TwoSum:
   snd = b64_zero) does NOT fire only when `compress (rev cs_output) = nil`.

   Three cross-sign cascade traces on concrete binary64 inputs, using the
   Route-2 cascade (`initial_cascade_state` + `cascade_step_state`) with
   magnitude-ascending processing order.

   Trace A — e = [1, 2^60], f = [-1]: pathB at step 1, empty output-so-far.
   Trace B — e = [2^60, 1], f = [-2^60]: pathB at step 2, output len = 1
             (refutes `pathB_fires_only_when_output_compressed_empty`).
   Trace C — e = [1, 2^60], f = [-(2^60-2^8)]: pathB at step 2, nonzero
             residue 2^8 with nonempty output-so-far.

   Consequence (documented in docs/history/sessions/shewchuk-thm13-4A-verify-outcome.md):
   resolution-1-extended — O1′ granularity + O1 core head_replace, not a full
   cs_carry-dominates-output invariant.

   Pure vm_compute witnesses; no Admitted / Axiom / Parameter.  No deferred-
   headline dependence.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import List ZArith Reals.
From Flocq Require Import IEEE754.Binary Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_Pff_bridge
                                     B64_Expansion_Shewchuk
                                     B64_FastExpansionSum_Shewchuk_Route2.
Import ListNotations.
Local Open Scope positive_scope.
Local Open Scope R_scope.

Definition b64_one60 : binary64 :=
  Binary.B754_finite prec emax false 4503599627370496%positive (-52)%Z eq_refl.

Definition b64_pow2_60 : binary64 :=
  Binary.B754_finite prec emax false 4503599627370496%positive 8%Z eq_refl.

Definition b64_neg_pow2_60 : binary64 :=
  Binary.B754_finite prec emax true 4503599627370496%positive 8%Z eq_refl.

Definition b64_neg_one : binary64 :=
  Binary.B754_finite prec emax true 4503599627370496%positive (-52)%Z eq_refl.

Definition b64_neg_pow2_60_minus_256 : binary64 :=
  Binary.B754_finite prec emax true 9007199254740990%positive 7%Z eq_refl.

Definition b64_pow2_8 : binary64 :=
  Binary.B754_finite prec emax false 4503599627370496%positive (-44)%Z eq_refl.

Definition pathB_snd_zero (state : cascade_state) (x : binary64) : Prop :=
  snd (b64_TwoSum x (cs_carry state)) = b64_zero.

(* Trace A: sorted [1, -1, 2^60]; pathB cancels 1 + (-1). *)
Definition traceA_init : cascade_state :=
  initial_cascade_state b64_one60 from_e.

(* Trace B: sorted [1, 2^60, -2^60]; pathB cancels 2^60 + (-2^60). *)
Definition traceB_init : cascade_state :=
  initial_cascade_state b64_one60 from_e.

Definition traceB_s1 : cascade_state :=
  cascade_step_state traceB_init b64_pow2_60 from_e.

Definition traceB_s2 : cascade_state :=
  cascade_step_state traceB_s1 b64_neg_pow2_60 from_f.

(* Trace C: sorted [1, 2^60, -(2^60-2^8)]; partial cancellation. *)
Definition traceC_init : cascade_state :=
  initial_cascade_state b64_one60 from_e.

Definition traceC_s1 : cascade_state :=
  cascade_step_state traceC_init b64_pow2_60 from_e.

Definition traceC_s2 : cascade_state :=
  cascade_step_state traceC_s1 b64_neg_pow2_60_minus_256 from_f.

Lemma traceA_pathB_snd_zero :
  pathB_snd_zero traceA_init b64_neg_one.
Proof. vm_compute. reflexivity. Qed.

Lemma traceA_output_rev_nil :
  rev (cs_output traceA_init) = nil.
Proof. vm_compute. reflexivity. Qed.

Lemma traceB_pathB_snd_zero :
  pathB_snd_zero traceB_s1 b64_neg_pow2_60.
Proof. vm_compute. reflexivity. Qed.

Lemma traceB_carry_before_B2R :
  Binary.B2R prec emax (cs_carry traceB_s1) = Binary.B2R prec emax b64_pow2_60.
Proof. vm_compute. reflexivity. Qed.

Lemma traceB_output_before_len : length (cs_output traceB_s1) = 1%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma traceB_carry_after_B2R :
  Binary.B2R prec emax (cs_carry traceB_s2) = 0%R.
Proof. vm_compute. reflexivity. Qed.

Lemma traceC_pathB_snd_zero :
  pathB_snd_zero traceC_s1 b64_neg_pow2_60_minus_256.
Proof. vm_compute. reflexivity. Qed.

Lemma traceC_carry_after_B2R :
  Binary.B2R prec emax (cs_carry traceC_s2) = Binary.B2R prec emax b64_pow2_8.
Proof. vm_compute. reflexivity. Qed.

Lemma traceC_output_before_len : length (cs_output traceC_s1) = 1%nat.
Proof. vm_compute. reflexivity. Qed.

(* Refutation of the beachhead lemma target: pathB at traceB_s1 with
   nonempty output-so-far (length = 1, not compress-nil). *)
Lemma pathB_fires_with_nonempty_output :
  pathB_snd_zero traceB_s1 b64_neg_pow2_60 /\
  length (cs_output traceB_s1) = 1%nat.
Proof. split; [exact traceB_pathB_snd_zero | exact traceB_output_before_len]. Qed.

(* -------------------------------------------------------------------------- *)
(* §4.A gating dovetail.  See docs/shewchuk-theorem-13-proof-structure.md and  *)
(* docs/history/sessions/shewchuk-thm13-4A-verify-outcome.md.                  *)
(*                                                                            *)
(* The witnesses above are a *gating* artifact, not an invariant lemma: they  *)
(* settle which O1-integration route the cascade proof must take, by refuting *)
(* one candidate hypothesis with concrete vm_compute evidence.                *)
(*                                                                            *)
(* The refuted hypothesis is `pathB_fires_only_when_output_compressed_empty`  *)
(* — the claim that the exact-cancellation branch (pathB: snd TwoSum =        *)
(* b64_zero) fires only when `compress (rev cs_output) = nil`.  Trace B fires  *)
(* pathB at step 2 with `length (cs_output) = 1` (lemma                        *)
(* `pathB_fires_with_nonempty_output`), and Trace C does so with a nonzero    *)
(* residue (`2^8`) sitting above a nonempty output-so-far.  So the empty-      *)
(* output-only hypothesis is false, and the two resolutions it would have     *)
(* licensed are both ruled out as the *whole* story:                          *)
(*                                                                            *)
(*   - Resolution-1 (empty output only) is INSUFFICIENT — refuted by B/C.     *)
(*   - Resolution-2 (a global cs_carry-dominates-output invariant) is NOT     *)
(*     REQUIRED — Trace C shows the residue is governed by local granularity, *)
(*     not by carry magnitude dominating the entire accumulated output.       *)
(*                                                                            *)
(* The route these traces select — resolution-1-extended — is now realised    *)
(* (Qed-closed) downstream in `B64_Shewchuk_Thm13_pathAB.v` as               *)
(* `cascade_step_pathB_preserves_output`.  That proof case-splits exactly     *)
(* along the boundary these traces map out:                                    *)
(*                                                                            *)
(*   1. zero residue (`x + cs_carry = 0`, Traces A/B): discharged by O1 core  *)
(*      `nonoverlap_shewchuk_cons_zero` (#135) + `..._head_replace` (#137),    *)
(*      via `cascade_step_pathB_preserves_output_zero_residue`.                *)
(*   2. `compress (rev cs_output) = nil` (Trace A empty regime): the empty-    *)
(*      tail disjunct of `head_replace`, via                                   *)
(*      `cascade_step_pathB_preserves_output_nil_compress`.                    *)
(*   3. nonempty output AND nonzero residue (Trace C): the *lightweight*       *)
(*      output-bound clause `pathB_output_head_bound` (|h| <= ½·ulp of the     *)
(*      emitted carry) together with O1′ granularity (`residue_ge_half_ulp`,   *)
(*      #136) — NOT a global dominance invariant.                              *)
(*                                                                            *)
(* In short: these vm_compute traces are the load-bearing justification for    *)
(* the third hypothesis of `cascade_step_pathB_preserves_output` being a      *)
(* per-step head bound rather than a global carry-dominance clause.  Were      *)
(* `pathB_fires_only_when_output_compressed_empty` true, subcase (3) would be  *)
(* vacuous and that hypothesis could be dropped; Trace C is the concrete       *)
(* witness that it cannot.                                                      *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                              *)
(* -------------------------------------------------------------------------- *)

Print Assumptions traceA_pathB_snd_zero.
Print Assumptions pathB_fires_with_nonempty_output.