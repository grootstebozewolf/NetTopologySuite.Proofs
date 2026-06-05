(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_lib
   ----------------------------------------------------------------------------
   Wrapper module minimising the seam between Flocq's abstract format
   machinery and concrete binary64 work.

   Accumulated during the Stage D engagement.  Provides:

     - Module-level notations: `b64_fexp`, `b64_round`, `b64_ulp`,
       `b64_format`, `b64_emin`.  Eliminates the `Local Notation` boilerplate
       repeated in five files (B64_bridge, Orient_b64_exact, HotPixel_b64,
       Intersect_b64_exact, B64_Pff_bridge).

     - Typeclass instances: `b64_prec_gt_0`, `b64_fexp_valid`,
       `b64_fexp_monotone`.  Eliminates the explicit
       `@error_le_half_ulp_round radix2 (SpecFloat.fexp prec emax)
         (fexp_correct prec emax prec_gt_0_b64) (fexp_monotone prec emax)
         (fun z => negb (Z.even z))` mouthful at every call site.

     - Pre-instantiated Flocq lemmas: `b64_ulp_le_abs`, `b64_ulp_FLT_0`,
       `b64_error_le_half_ulp_round`, `b64_format_B2R`,
       `b64_generic_format_round`.  Same theorems, no parameter threading.

     - Recurring helpers from Stage D: `b64_round_minus_swap`,
       `b64_round_eq_R_eq` (`f_equal` for the round function).

   This file is a forward-looking convenience.  Existing files continue
   to compile with their `Local Notation b64_*` boilerplate; new work
   imports B64_lib and gets the clean API.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ============================================================================ *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Lra.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import IEEE754.BinarySingleNaN.
From Flocq Require Import Core.

From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import B64_bridge.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Module-level notations (non-Local, accessible to importers).               *)
(* -------------------------------------------------------------------------- *)

Notation b64_fexp   := (SpecFloat.fexp prec emax).
Notation b64_round  := (round radix2 b64_fexp (round_mode mode_b64)).
Notation b64_ulp    := (ulp radix2 b64_fexp).
Notation b64_format := (generic_format radix2 b64_fexp).
Notation b64_emin   := (3 - emax - prec)%Z.

(* -------------------------------------------------------------------------- *)
(* Typeclass instances pre-resolved for binary64.                             *)
(*                                                                            *)
(* Without these, every call to a Flocq theorem like `ulp_le_abs` or         *)
(* `error_le_half_ulp_round` requires explicit instance threading:           *)
(*                                                                            *)
(*   @error_le_half_ulp_round radix2 (SpecFloat.fexp prec emax)              *)
(*     (fexp_correct prec emax prec_gt_0_b64)                                *)
(*     (fexp_monotone prec emax)                                              *)
(*     (fun z => negb (Z.even z)) x                                          *)
(*                                                                            *)
(* With the instances below, Coq's typeclass resolution finds them           *)
(* automatically.  Call sites shrink to:                                     *)
(*                                                                            *)
(*   error_le_half_ulp_round (fun z => negb (Z.even z)) x                    *)
(* -------------------------------------------------------------------------- *)

#[export] Existing Instance prec_gt_0_b64.

#[export] Instance b64_fexp_valid : Valid_exp b64_fexp :=
  fexp_correct prec emax _.

#[export] Instance b64_fexp_monotone : Monotone_exp b64_fexp :=
  fexp_monotone prec emax.

(* -------------------------------------------------------------------------- *)
(* Format witness for binary64 values: B2R is always in `b64_format`.        *)
(* -------------------------------------------------------------------------- *)

Lemma b64_format_B2R :
  forall x : binary64, b64_format (Binary.B2R prec emax x).
Proof. exact (Binary.generic_format_B2R prec emax). Qed.

(* -------------------------------------------------------------------------- *)
(* ulp-related lemmas pre-instantiated for binary64.                          *)
(* -------------------------------------------------------------------------- *)

Lemma b64_ulp_le_abs :
  forall x : R,
    x <> 0 ->
    b64_format x ->
    b64_ulp x <= Rabs x.
Proof. intros; apply ulp_le_abs; assumption. Qed.

Lemma b64_ulp_FLT_0 : b64_ulp 0 = bpow radix2 b64_emin.
Proof.
  apply (@ulp_FLT_0 radix2 b64_emin prec _).
Qed.

(* -------------------------------------------------------------------------- *)
(* Rounding error bound at b64 precision (the workhorse for nonoverlap       *)
(* proofs on TwoSum / Dekker output).                                         *)
(* -------------------------------------------------------------------------- *)

Lemma b64_error_le_half_ulp_round :
  forall x : R,
    Rabs (b64_round x - x) <= b64_ulp (b64_round x) / 2.
Proof.
  intros x.
  pose proof (@error_le_half_ulp_round radix2 b64_fexp
                _ _ (fun z => negb (Z.even z)) x) as H.
  change (Znearest (fun z => negb (Z.even z)))
    with (round_mode mode_b64) in H.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* `b64_round` is identity on values in the binary64 format.                  *)
(* -------------------------------------------------------------------------- *)

Lemma b64_round_generic :
  forall x : R, b64_format x -> b64_round x = x.
Proof. intros; apply round_generic; auto with typeclass_instances. Qed.

(* -------------------------------------------------------------------------- *)
(* Helper accumulated from Dekker: rounding a `(a - b)` form equals rounding *)
(* a `(- b + a)` form.  Used to bridge Pff's `-r + x1y1` order with our      *)
(* natural `b64_minus x1y1 r` form.                                          *)
(* -------------------------------------------------------------------------- *)

Lemma b64_round_minus_swap :
  forall a b : R, b64_round (a - b) = b64_round (- b + a).
Proof. intros; f_equal; ring. Qed.

(* -------------------------------------------------------------------------- *)
(* Congruence lemma for `b64_round`: equal inputs give equal outputs.        *)
(* Useful as a `rewrite` target when arguments are ring-equal but            *)
(* syntactically different.                                                   *)
(* -------------------------------------------------------------------------- *)

Lemma b64_round_eq_R_eq :
  forall a b : R, a = b -> b64_round a = b64_round b.
Proof. intros a b ->; reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Tactic helpers for the recurring tangent patterns documented in           *)
(* docs/stage-d-feasibility.md.                                              *)
(* -------------------------------------------------------------------------- *)

(* Align `FLT_exp (3 - emax - prec) prec` ↔ `SpecFloat.fexp prec emax` and  *)
(* `Znearest (fun z => negb (Z.even z))` ↔ `round_mode mode_b64` in both    *)
(* goal and all hypotheses.  These are def-equal but syntactically          *)
(* different and trip up Coq's `rewrite` and `reflexivity`.                 *)
Ltac b64_align_forms :=
  repeat first
    [ change (FLT_exp b64_emin prec) with b64_fexp in *
    | change (Znearest (fun z => negb (Z.even z)))
        with (round_mode mode_b64) in *
    | change (bpow radix2 (prec - Z.div2 prec)) with (bpow radix2 27) in * ].

(* -------------------------------------------------------------------------- *)
(* Sanity test: re-prove a Stage D nonoverlap-style lemma using ONLY the    *)
(* wrapper API (no manual instance threading, no `Local Notation`).         *)
(*                                                                            *)
(* This is the SAME shape of proof as `b64_TwoSum_nonoverlap` in            *)
(* `B64_Pff_bridge.v`, but for the rounding-error of a single binary64      *)
(* operation.  If you can read this and understand it, the wrapper has      *)
(* succeeded in minimizing the seam.                                         *)
(* -------------------------------------------------------------------------- *)

Lemma b64_round_error_bounded_by_ulp :
  forall x : R,
    Rabs (x - b64_round x) <= b64_ulp (b64_round x) / 2.
Proof.
  intros x.
  pose proof (b64_error_le_half_ulp_round x) as H.
  rewrite Rabs_minus_sym in H.
  exact H.
Qed.

(* The contrast with the pre-wrapper version (from B64_Pff_bridge.v):       *)
(*                                                                            *)
(*   pose proof (@error_le_half_ulp_round radix2 (SpecFloat.fexp prec emax) *)
(*                 (fexp_correct prec emax prec_gt_0_b64)                    *)
(*                 (fexp_monotone prec emax)                                  *)
(*                 (fun z => negb (Z.even z)) x) as H.                       *)
(*   change (Znearest (fun z => negb (Z.even z)))                            *)
(*     with (round_mode mode_b64) in H.                                      *)
(*                                                                            *)
(* Both forms are now equally easy to write; the wrapper version is        *)
(* readable.                                                                *)

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_format_B2R.
Print Assumptions b64_ulp_le_abs.
Print Assumptions b64_ulp_FLT_0.
Print Assumptions b64_error_le_half_ulp_round.
Print Assumptions b64_round_generic.
Print Assumptions b64_round_minus_swap.
Print Assumptions b64_round_eq_R_eq.
