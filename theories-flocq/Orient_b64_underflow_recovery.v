(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Orient_b64_underflow_recovery
   ----------------------------------------------------------------------------
   Which "deeper stage" actually recovers the correct sign in the underflow
   regime of `Orient_b64_underflow_unsound.v`?

   The natural conjecture is "Stages B/C/D recover where Stage A failed."  On
   the concrete witness P0=(0,0), P1=(2^-200,0), Q=(2^-200,2^-900), that
   conjecture is FALSE for the float-based adaptive decoder, and this file
   proves it Qed-closed, then shows what DOES recover.

   FINDING 1 (negative, Qed-closed).  The full Stage D decoder
   `b64_orient_sign_stage_d` *also* returns OrientRZero here -- it does NOT
   recover.  Two compounding reasons:

     (a) Wiring.  Stage D only consults its exact fallback on OrientRUncertain
         / OrientRNan.  Underflow makes the determinant round to *exactly* 0,
         so the Stage A filter takes its `Some Eq => OrientRZero` branch and
         commits *confidently* to "collinear".  Stage D passes that verdict
         straight through; the expansion fallback is never invoked.

     (b) Even if it were invoked, the expansion path gives no guarantee here.
         Its soundness theorem requires `b64_orient2d_expansion_safe`, which
         entails Dekker's no-underflow precondition -- and that precondition
         is *violated*: the true product 2^-200 * 2^-900 = 2^-1100 lies below
         half the smallest subnormal (2^-1075), so Dekker's TwoProduct rounds
         both its result and its error term to 0.  Shewchuk's error-free
         transforms assume no underflow; this regime is outside their model.

   FINDING 2 (positive, Qed-closed).  What recovers is NOT the float EFT
   stages but the *integer-mantissa* exact model `b64_orient2d_exact`
   (Orient_b64_exact_full.v), which never forms the float product.  We package
   it as a decoder `b64_orient_sign_intexact` and prove:

     - `b64_orient_sign_intexact_sound`: SOUND over the ENTIRE finite binary64
       plane (`all_finite`), with NO underflow / safety precondition.
     - `b64_orient_sign_intexact_never_indefinite`: never returns Nan/Uncertain.
     - `intexact_recovers_under_underflow`: on the witness it returns
       OrientRPos -- the correct sign the float stages missed.

   Net: the honest "deeper-stage recovery" story is integer-mantissa exact
   arithmetic, not the binary64 EFT expansion.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (claude-opus-4-8)
   ============================================================================ *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import Core.

From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import Orientation_b64.
From NTS.Proofs.Flocq Require Import Orient_b64_sound.
From NTS.Proofs.Flocq Require Import Orient_b64_exact_full.
From NTS.Proofs.Flocq Require Import Orient_b64_stage_d.
From NTS.Proofs.Flocq Require Import Orient_b64_underflow_unsound.

Local Open Scope Z_scope.
Local Open Scope R_scope.

(* ========================================================================== *)
(* FINDING 1: the float Stage D decoder does NOT recover.                     *)
(* ========================================================================== *)

Theorem stage_d_does_not_recover_under_underflow :
  (* Stage D (Stages A through D as wired) reports "collinear" ...           *)
  b64_orient_sign_stage_d uP0 uP1 uQ = OrientRZero
  (* ... while the true sign is strictly positive.                           *)
  /\ b64_orient2d_exact uP0 uP1 uQ = 1%Z
  /\ 0 < cross_R_BP uP0 uP1 uQ.
Proof.
  split; [vm_compute; reflexivity |].
  split; [exact uWitness_exact_says_pos | exact uWitness_true_cross_pos].
Qed.

(* ========================================================================== *)
(* FINDING 2: an integer-mantissa-exact decoder, sound over the whole plane.  *)
(* ========================================================================== *)

(* Decode the exact integer-determinant sign (in {1,0,-1}) into the robust    *)
(* 5-valued sign.  Unlike the float stages it never forms a float product,    *)
(* so underflow cannot corrupt it.                                            *)
Definition b64_orient_sign_intexact (P0 P1 Q : BPoint) : orient_sign_robust :=
  if Z.eqb (b64_orient2d_exact P0 P1 Q) 1 then OrientRPos
  else if Z.eqb (b64_orient2d_exact P0 P1 Q) (-1) then OrientRNeg
  else OrientRZero.

(* Sound over the ENTIRE finite plane -- no underflow / integer-regime        *)
(* precondition, only finiteness.                                             *)
Theorem b64_orient_sign_intexact_sound :
  forall P0 P1 Q : BPoint,
    all_finite P0 P1 Q ->
    match b64_orient_sign_intexact P0 P1 Q with
    | OrientRPos       => 0 < cross_R_BP P0 P1 Q
    | OrientRNeg       => cross_R_BP P0 P1 Q < 0
    | OrientRZero      => cross_R_BP P0 P1 Q = 0
    | OrientRNan       => True
    | OrientRUncertain => True
    end.
Proof.
  intros P0 P1 Q Hfin.
  pose proof (b64_orient2d_exact_sound P0 P1 Q Hfin) as (Hpos & Hneg & Hzero).
  unfold b64_orient_sign_intexact.
  destruct (Z.eqb_spec (b64_orient2d_exact P0 P1 Q) 1) as [E1 | N1].
  - apply (proj2 Hpos). exact E1.
  - destruct (Z.eqb_spec (b64_orient2d_exact P0 P1 Q) (-1)) as [E2 | N2].
    + apply (proj2 Hneg). exact E2.
    + (* Z.sgn is in {1,0,-1}; not 1 and not -1, so it is 0. *)
      apply (proj2 Hzero).
      unfold b64_orient2d_exact in *.
      destruct (Z.sgn_spec (b64_orient2d_intdet P0 P1 Q))
        as [[_ Hs] | [[_ Hs] | [_ Hs]]].
      * exfalso. apply N1. exact Hs.
      * exact Hs.
      * exfalso. apply N2. exact Hs.
Qed.

(* The integer-exact decoder is always definite (never Nan/Uncertain). *)
Theorem b64_orient_sign_intexact_never_indefinite :
  forall P0 P1 Q : BPoint,
    b64_orient_sign_intexact P0 P1 Q <> OrientRNan /\
    b64_orient_sign_intexact P0 P1 Q <> OrientRUncertain.
Proof.
  intros P0 P1 Q. unfold b64_orient_sign_intexact.
  destruct (Z.eqb (b64_orient2d_exact P0 P1 Q) 1);
    [| destruct (Z.eqb (b64_orient2d_exact P0 P1 Q) (-1))];
    split; discriminate.
Qed.

(* On the witness it returns the correct OrientRPos -- the recovery the float  *)
(* stages missed.                                                              *)
Theorem intexact_recovers_under_underflow :
  b64_orient_sign_intexact uP0 uP1 uQ = OrientRPos.
Proof. vm_compute. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* The two findings side by side: on identical inputs the float Stage D        *)
(* decoder says "collinear" while the integer-exact decoder says "positive",   *)
(* and the integer-exact verdict matches the truth.                            *)
(* -------------------------------------------------------------------------- *)

Theorem underflow_recovery_contrast :
  b64_orient_sign_stage_d   uP0 uP1 uQ = OrientRZero /\
  b64_orient_sign_intexact  uP0 uP1 uQ = OrientRPos  /\
  0 < cross_R_BP uP0 uP1 uQ.
Proof.
  split; [vm_compute; reflexivity |].
  split; [exact intexact_recovers_under_underflow | exact uWitness_true_cross_pos].
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_orient_sign_intexact_sound.
Print Assumptions underflow_recovery_contrast.
