(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Orient_b64_stage_d
   ----------------------------------------------------------------------------
   Slice A Piece 7: Stage D headline.

   COMPOSES
   --------
     - Piece 6's `b64_orient2d_expansion_sign_correct`
       (Orient_b64_expansion.v): sign of the expansion equals sign of
       cross_R_BP, under `b64_orient2d_expansion_safe` (modulo Piece 5b
       deferred-proof).
     - The existing `b64_orient_sign_filtered_sound_small_int`
       (Orient_b64_exact.v): Stage A filter is sound vs cross_R_BP in
       the small-int regime.

   DELIVERABLES
   ------------
     1. `expansion_sign_to_orient_robust`: translation between
        `expansion_sign` (3-valued) and `orient_sign_robust`
        (5-valued).  Pos -> Pos, Neg -> Neg, Zero -> Zero.  The exact
        path never produces Nan or Uncertain.
     2. `b64_orient_sign_exact`: Stage D's exact-via-expansion decoder.
     3. `b64_orient_sign_exact_sound`: sound vs cross_R_BP under
        `b64_orient2d_expansion_safe` (modulo Piece 5b).
     4. `b64_orient_sign_stage_d`: full Stage D decoder.  Tries Stage A
        filter first; if it commits to Pos/Neg/Zero, returns it; if it
        returns Uncertain or Nan, falls back to the expansion-based
        exact decoder.
     5. `b64_orient_sign_stage_d_sound`: sound vs cross_R_BP under
        BOTH the small-int safety (for the filter path) and the
        expansion safety (for the fallback path).  In small-int regime
        these can be discharged simultaneously.

   The headline of Slice A is `b64_orient_sign_stage_d_sound`, completing
   the path from the existing Path A's Qed-closed dominated-case work
   through the Slice A fast-expansion-sum machinery to the Stage D
   top-level theorem.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ============================================================================ *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import IEEE754.BinarySingleNaN.
From Flocq Require Import Core.

From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import B64_bridge.
From NTS.Proofs.Flocq Require Import B64_lib.
From NTS.Proofs.Flocq Require Import Orient_b64_sound.
From NTS.Proofs.Flocq Require Import Orient_b64_exact.
From NTS.Proofs.Flocq Require Import Orientation_b64.
From NTS.Proofs.Flocq Require Import B64_Expansion.
From NTS.Proofs.Flocq Require Import B64_Expansion_Shewchuk.
From NTS.Proofs.Flocq Require Import Orient_b64_expansion.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Translation: expansion_sign -> orient_sign_robust.                         *)
(*                                                                            *)
(* The exact path (b64_orient2d_expansion_sign) never produces Nan or         *)
(* Uncertain because the expansion is exact.  The translation maps the      *)
(* three expansion_sign values directly to their orient_sign_robust          *)
(* counterparts.                                                              *)
(* -------------------------------------------------------------------------- *)

Definition expansion_sign_to_orient_robust (s : expansion_sign)
  : orient_sign_robust :=
  match s with
  | ExpPos  => OrientRPos
  | ExpNeg  => OrientRNeg
  | ExpZero => OrientRZero
  end.

(* -------------------------------------------------------------------------- *)
(* Stage D exact decoder.                                                     *)
(* -------------------------------------------------------------------------- *)

Definition b64_orient_sign_exact (P0 P1 Q : BPoint) : orient_sign_robust :=
  expansion_sign_to_orient_robust (b64_orient2d_expansion_sign P0 P1 Q).

Theorem b64_orient_sign_exact_sound :
  forall P0 P1 Q : BPoint,
    fast_expansion_sum_strong_nonoverlap_headline ->
    b64_orient2d_expansion_safe P0 P1 Q ->
    match b64_orient_sign_exact P0 P1 Q with
    | OrientRPos       => 0 < cross_R_BP P0 P1 Q
    | OrientRNeg       => cross_R_BP P0 P1 Q < 0
    | OrientRZero      => cross_R_BP P0 P1 Q = 0
    | OrientRNan       => True
    | OrientRUncertain => True
    end.
Proof.
  intros P0 P1 Q Hheadline Hsafe.
  unfold b64_orient_sign_exact, expansion_sign_to_orient_robust.
  pose proof (b64_orient2d_expansion_sign_correct P0 P1 Q Hheadline Hsafe) as Hsign.
  destruct (b64_orient2d_expansion_sign P0 P1 Q); exact Hsign.
Qed.

(* -------------------------------------------------------------------------- *)
(* Stage D full decoder: filter, then fall back to expansion-based exact.    *)
(*                                                                            *)
(* Stage A's `b64_orient_sign_filtered` returns:                              *)
(*   - Pos/Neg/Zero: filtered with enough confidence, sign is decisive.       *)
(*   - Uncertain: filter bound did not separate from zero; need more.         *)
(*   - Nan: a binary64 op produced NaN (degenerate input or overflow).        *)
(*                                                                            *)
(* The Stage D decoder accepts Pos/Neg/Zero, and recomputes via the           *)
(* exact expansion when the filter returns Uncertain or Nan.                  *)
(* -------------------------------------------------------------------------- *)

Definition b64_orient_sign_stage_d (P0 P1 Q : BPoint) : orient_sign_robust :=
  match b64_orient_sign_filtered P0 P1 Q with
  | OrientRPos       => OrientRPos
  | OrientRNeg       => OrientRNeg
  | OrientRZero      => OrientRZero
  | OrientRUncertain => b64_orient_sign_exact P0 P1 Q
  | OrientRNan       => b64_orient_sign_exact P0 P1 Q
  end.

(* -------------------------------------------------------------------------- *)
(* Stage D headline: sound in the small-int regime + under expansion safety. *)
(*                                                                            *)
(* Composes:                                                                  *)
(*   1. `b64_orient_sign_filtered_sound_small_int`: filter sound vs           *)
(*      cross_R_BP under small-int safety.                                    *)
(*   2. `b64_orient_sign_exact_sound`: exact decoder sound vs cross_R_BP      *)
(*      under expansion safety.                                               *)
(*                                                                            *)
(* Both safeties together cover the small-int regime cleanly.  Outside the   *)
(* small-int regime, only the exact path is sound, and small_int safety      *)
(* is not assumed; the filter's Pos/Neg cases would need Shewchuk Stage A's  *)
(* forward-error bound (a separate deferred slice).  For now, this headline  *)
(* is stated for inputs that satisfy BOTH safeties.                          *)
(* -------------------------------------------------------------------------- *)

Theorem b64_orient_sign_stage_d_sound :
  forall P0 P1 Q : BPoint,
    fast_expansion_sum_strong_nonoverlap_headline ->
    orient2d_inputs_int_safe P0 P1 Q ->
    b64_orient2d_expansion_safe P0 P1 Q ->
    match b64_orient_sign_stage_d P0 P1 Q with
    | OrientRPos       => 0 < cross_R_BP P0 P1 Q
    | OrientRNeg       => cross_R_BP P0 P1 Q < 0
    | OrientRZero      => cross_R_BP P0 P1 Q = 0
    | OrientRNan       => True
    | OrientRUncertain => True
    end.
Proof.
  intros P0 P1 Q Hheadline Hint Hexp.
  unfold b64_orient_sign_stage_d.
  pose proof (b64_orient_sign_filtered_sound_small_int P0 P1 Q Hint) as Hfilt.
  pose proof (b64_orient_sign_exact_sound P0 P1 Q Hheadline Hexp) as Hexact.
  destruct (b64_orient_sign_filtered P0 P1 Q);
    [exact Hfilt | exact Hfilt | exact Hfilt | exact Hexact | exact Hexact].
Qed.

(* -------------------------------------------------------------------------- *)
(* Tiny-regime decisive headline: in the tiny regime (coordinates fitting    *)
(* in 23 bits), Stage D never returns OrientRUncertain.  Composes with      *)
(* `b64_orient_sign_filtered_tiny_regime_decisive` -- in that regime, the    *)
(* filter already returns a decisive sign, so the fallback never fires.      *)
(* -------------------------------------------------------------------------- *)

Theorem b64_orient_sign_stage_d_tiny_regime_decisive :
  forall P0 P1 Q : BPoint,
    orient2d_inputs_tiny_int_safe P0 P1 Q ->
    cross_R_BP P0 P1 Q <> 0 ->
    b64_orient_sign_stage_d P0 P1 Q <> OrientRUncertain.
Proof.
  intros P0 P1 Q Htiny Hnz.
  pose proof (b64_orient_sign_filtered_tiny_regime_decisive P0 P1 Q Htiny Hnz)
    as HnotU.
  unfold b64_orient_sign_stage_d.
  destruct (b64_orient_sign_filtered P0 P1 Q) eqn:Hf.
  - congruence.
  - congruence.
  - congruence.
  - (* Filter says Nan: stage_d falls back to b64_orient_sign_exact, *)
    (* which never returns Uncertain.                                *)
    unfold b64_orient_sign_exact, expansion_sign_to_orient_robust.
    destruct (b64_orient2d_expansion_sign P0 P1 Q); congruence.
  - (* Filter says Uncertain: contradicts HnotU. *)
    exfalso. apply HnotU. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_orient_sign_exact_sound.
Print Assumptions b64_orient_sign_stage_d_sound.
Print Assumptions b64_orient_sign_stage_d_tiny_regime_decisive.
