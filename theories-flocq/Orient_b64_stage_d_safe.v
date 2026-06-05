(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Orient_b64_stage_d_safe
   ----------------------------------------------------------------------------
   A corrected Stage D decoder that closes the underflow gap exposed by
   `Orient_b64_underflow_unsound.v` / `Orient_b64_underflow_recovery.v`.

   The shipped `b64_orient_sign_stage_d` (Orient_b64_stage_d.v) trusts the
   Stage A filter's OrientRZero verdict and only falls back to the EXPANSION
   exact path on OrientRUncertain / OrientRNan.  Under catastrophic underflow
   the determinant rounds to *exactly* 0, so the filter commits confidently to
   OrientRZero and the fallback never fires -- the decoder returns a wrong
   "collinear".  And even when the fallback does fire, the expansion path is
   only sound under `b64_orient2d_expansion_safe` (Dekker's no-underflow
   precondition), so it is no remedy for underflow either.

   THE FIX.  Route EVERY non-committal filter verdict -- OrientRZero,
   OrientRUncertain, OrientRNan -- through the INTEGER-MANTISSA exact decoder
   `b64_orient_sign_intexact` (Orient_b64_underflow_recovery.v), which is sound
   over the entire finite plane with NO underflow / regime precondition and is
   always definite.  Only the filter's confident OrientRPos / OrientRNeg are
   kept as the fast path.

   WHAT IS PROVED (honest layering).

   1. `b64_orient_sign_stage_d_safe_sound_when_filter_indefinite`
        UNCONDITIONAL (all_finite only): whenever the filter does NOT commit to
        Pos/Neg -- which includes every underflow-to-zero case -- the decoder
        is sound.  This is the "including underflow" guarantee.

   2. `b64_orient_sign_stage_d_safe_sound`
        Sound under `orient2d_inputs_int_safe` ALONE -- strictly WEAKER than the
        shipped Stage D, which additionally needs `b64_orient2d_expansion_safe`.
        The fast Pos/Neg path is discharged by the existing filter soundness;
        the fallback by integer-exact soundness.

   3. `b64_orient_sign_stage_d_safe_never_indefinite`
        The corrected decoder is TOTAL: it never returns Nan/Uncertain (the
        integer-exact fallback always yields a definite sign).

   4. `stage_d_safe_recovers_under_underflow`
        On the witness it returns the correct OrientRPos, where the shipped
        Stage D returns OrientRZero.

   NOT CLAIMED.  Unconditional soundness of the fast Pos/Neg path itself
   (filter commits => correct sign for *arbitrary* finite coordinates) is the
   general Shewchuk Stage A error-bound theorem, which the corpus proves only
   in the integer regime; it is deliberately NOT assumed away here.  This file
   removes the underflow hazard and the expansion-safety hypothesis; it does
   not discharge that separate open piece.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (claude-opus-4-8)
   ============================================================================ *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.

From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import Orientation_b64.
From NTS.Proofs.Flocq Require Import Orient_b64_sound.
From NTS.Proofs.Flocq Require Import Orient_b64_exact.
From NTS.Proofs.Flocq Require Import Orient_b64_exact_full.
From NTS.Proofs.Flocq Require Import Orient_b64_stage_d.
From NTS.Proofs.Flocq Require Import Orient_b64_underflow_unsound.
From NTS.Proofs.Flocq Require Import Orient_b64_underflow_recovery.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* The corrected decoder.  Fast float path for confident Pos/Neg; integer-     *)
(* mantissa exact for every non-committal verdict.                             *)
(* -------------------------------------------------------------------------- *)

Definition b64_orient_sign_stage_d_safe (P0 P1 Q : BPoint) : orient_sign_robust :=
  match b64_orient_sign_filtered P0 P1 Q with
  | OrientRPos => OrientRPos
  | OrientRNeg => OrientRNeg
  | OrientRZero | OrientRNan | OrientRUncertain =>
      b64_orient_sign_intexact P0 P1 Q
  end.

(* int-safe inputs are in particular all finite (coord_int_safe carries        *)
(* is_finite as its first conjunct).                                           *)
Lemma orient2d_inputs_int_safe_all_finite :
  forall P0 P1 Q : BPoint,
    orient2d_inputs_int_safe P0 P1 Q -> all_finite P0 P1 Q.
Proof.
  intros P0 P1 Q (HxP0 & HyP0 & HxP1 & HyP1 & HxQ & HyQ).
  unfold all_finite.
  repeat split.
  - exact (proj1 HxP0).
  - exact (proj1 HxP1).
  - exact (proj1 HxQ).
  - exact (proj1 HyP0).
  - exact (proj1 HyP1).
  - exact (proj1 HyQ).
Qed.

(* ========================================================================== *)
(* (1) UNCONDITIONAL soundness whenever the filter is not confidently Pos/Neg. *)
(*     This is precisely where the underflow witness lands.                    *)
(* ========================================================================== *)

Theorem b64_orient_sign_stage_d_safe_sound_when_filter_indefinite :
  forall P0 P1 Q : BPoint,
    all_finite P0 P1 Q ->
    b64_orient_sign_filtered P0 P1 Q <> OrientRPos ->
    b64_orient_sign_filtered P0 P1 Q <> OrientRNeg ->
    match b64_orient_sign_stage_d_safe P0 P1 Q with
    | OrientRPos       => 0 < cross_R_BP P0 P1 Q
    | OrientRNeg       => cross_R_BP P0 P1 Q < 0
    | OrientRZero      => cross_R_BP P0 P1 Q = 0
    | OrientRNan       => True
    | OrientRUncertain => True
    end.
Proof.
  intros P0 P1 Q Hfin Hnp Hnn.
  unfold b64_orient_sign_stage_d_safe.
  destruct (b64_orient_sign_filtered P0 P1 Q) eqn:Hf.
  - exfalso; apply Hnp; reflexivity.
  - exfalso; apply Hnn; reflexivity.
  - apply b64_orient_sign_intexact_sound; exact Hfin.
  - apply b64_orient_sign_intexact_sound; exact Hfin.
  - apply b64_orient_sign_intexact_sound; exact Hfin.
Qed.

(* ========================================================================== *)
(* (2) Sound under int-safety ALONE -- no expansion-safety hypothesis, unlike  *)
(*     the shipped b64_orient_sign_stage_d_sound.                              *)
(* ========================================================================== *)

Theorem b64_orient_sign_stage_d_safe_sound :
  forall P0 P1 Q : BPoint,
    orient2d_inputs_int_safe P0 P1 Q ->
    match b64_orient_sign_stage_d_safe P0 P1 Q with
    | OrientRPos       => 0 < cross_R_BP P0 P1 Q
    | OrientRNeg       => cross_R_BP P0 P1 Q < 0
    | OrientRZero      => cross_R_BP P0 P1 Q = 0
    | OrientRNan       => True
    | OrientRUncertain => True
    end.
Proof.
  intros P0 P1 Q Hint.
  pose proof (orient2d_inputs_int_safe_all_finite _ _ _ Hint) as Hfin.
  pose proof (b64_orient_sign_filtered_sound_small_int _ _ _ Hint) as Hfilt.
  unfold b64_orient_sign_stage_d_safe.
  destruct (b64_orient_sign_filtered P0 P1 Q) eqn:Hf.
  - (* Pos: filter's verdict is sound in the int regime *) exact Hfilt.
  - (* Neg *) exact Hfilt.
  - (* Zero -> integer-exact fallback *)
    apply b64_orient_sign_intexact_sound; exact Hfin.
  - (* Nan -> fallback *)
    apply b64_orient_sign_intexact_sound; exact Hfin.
  - (* Uncertain -> fallback *)
    apply b64_orient_sign_intexact_sound; exact Hfin.
Qed.

(* ========================================================================== *)
(* (3) The corrected decoder is TOTAL: never Nan/Uncertain.                    *)
(* ========================================================================== *)

Theorem b64_orient_sign_stage_d_safe_never_indefinite :
  forall P0 P1 Q : BPoint,
    b64_orient_sign_stage_d_safe P0 P1 Q <> OrientRNan /\
    b64_orient_sign_stage_d_safe P0 P1 Q <> OrientRUncertain.
Proof.
  intros P0 P1 Q. unfold b64_orient_sign_stage_d_safe.
  destruct (b64_orient_sign_filtered P0 P1 Q) eqn:Hf;
    try (split; discriminate);
    apply b64_orient_sign_intexact_never_indefinite.
Qed.

(* ========================================================================== *)
(* (4) Recovery on the underflow witness: the corrected decoder returns        *)
(*     OrientRPos where the shipped Stage D returns OrientRZero.               *)
(* ========================================================================== *)

Theorem stage_d_safe_recovers_under_underflow :
  b64_orient_sign_stage_d_safe uP0 uP1 uQ = OrientRPos /\
  b64_orient_sign_stage_d      uP0 uP1 uQ = OrientRZero /\
  0 < cross_R_BP uP0 uP1 uQ.
Proof.
  split; [vm_compute; reflexivity |].
  split; [vm_compute; reflexivity | exact uWitness_true_cross_pos].
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_orient_sign_stage_d_safe_sound_when_filter_indefinite.
Print Assumptions b64_orient_sign_stage_d_safe_sound.
Print Assumptions stage_d_safe_recovers_under_underflow.
