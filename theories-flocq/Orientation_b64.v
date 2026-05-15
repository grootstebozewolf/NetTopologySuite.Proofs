(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Orientation_b64
   ----------------------------------------------------------------------------
   Executable binary64 orientation predicate.  This is Phase 0 of the NTS
   topological chokepoint sequence (see README).

   The plain `cross`-based orientation in binary64 is NOT robust at near-
   collinear inputs -- the rounding error can flip the sign.  Shewchuk's
   1997 adaptive-precision algorithm is the canonical fix and is the
   long-term target for this file.  The first slice below sets up the
   ground for it:

     - `b64_orient2d`        — the cross-product signed area, in binary64.
     - `b64_orient_sign`     — a 4-valued sign type (Pos / Neg / Zero / Nan)
                               that explicitly admits the NaN case rather
                               than collapsing it.
     - Companion file `Orientation_b64_extract.v` extracts the executable
       layer to OCaml native float, mirroring the simplifier pattern.

   PROOF STATUS
   ============
   - Computational implementation : complete + extracted to OCaml.
   - Structural invariants        : limited.  Decidability of the sign type
                                    and totality of `b64_orient_sign` are
                                    Qed-closed.  Arithmetic identities
                                    (antisymmetry, cyclic permutation,
                                    translation invariance) hold in ℝ but
                                    in binary64 require Flocq's
                                    `Bminus_correct` / `Bmult_correct` no-
                                    overflow preconditions.  They are NOT
                                    YET CLAIMED here -- the same proof
                                    slice that closes the simplifier R-
                                    bridge will close them in one pass.
   - Shewchuk-adaptive filter     : NOT YET claimed.  This file is the
                                    naive cross-product layer; the
                                    filter + expansion-arithmetic fallback
                                    is the next slice.

   No `Admitted` theorems.  The corpus-wide invariant applies: properties
   that are not yet proven are absent from the file rather than stubbed.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import IEEE754.BinarySingleNaN.
From Flocq Require Import Core.

From NTS.Proofs.Flocq Require Import Validate_binary64.

(* -------------------------------------------------------------------------- *)
(* The signed twice-area on `BPoint` reusing the helpers from                 *)
(* `Validate_binary64`:                                                       *)
(*    (P1.x - P0.x) * (Q.y  - P0.y)                                          *)
(*  - (Q.x  - P0.x) * (P1.y - P0.y)                                          *)
(* -------------------------------------------------------------------------- *)

Definition b64_orient2d (P0 P1 Q : BPoint) : binary64 :=
  b64_minus
    (b64_mult (b64_minus (bx P1) (bx P0)) (b64_minus (by_ Q)  (by_ P0)))
    (b64_mult (b64_minus (bx Q)  (bx P0)) (b64_minus (by_ P1) (by_ P0))).

(* `b64_orient2d` IS `b64_cross` from Validate_binary64 -- aliased here so   *)
(* downstream consumers can import the orientation file without the          *)
(* simplifier file.  This is the only function `Orientation_b64.v` exports  *)
(* that does not factor through the simplifier's existing helpers.           *)

(* -------------------------------------------------------------------------- *)
(* Four-valued sign type.  Unlike a tri-state `Lt`/`Eq`/`Gt`, this admits   *)
(* the NaN case explicitly.  Any caller that wants to be NaN-safe MUST     *)
(* handle `OrientNan` rather than treat it as a default sign.               *)
(* -------------------------------------------------------------------------- *)

Inductive orient_sign : Type :=
| OrientPos
| OrientNeg
| OrientZero
| OrientNan.

(* Decision procedure.  Routes through `b64_compare`, which itself returns *)
(* `None` exactly on NaN inputs -- we surface that as `OrientNan`.         *)

Definition b64_orient_sign (P0 P1 Q : BPoint) : orient_sign :=
  let v := b64_orient2d P0 P1 Q in
  let zero := Binary.B754_zero prec emax false in
  match b64_compare v zero with
  | Some Eq => OrientZero
  | Some Lt => OrientNeg
  | Some Gt => OrientPos
  | None    => OrientNan
  end.

(* -------------------------------------------------------------------------- *)
(* Structural Qed-closed lemmas.                                              *)
(* -------------------------------------------------------------------------- *)

(* Decidable equality of `orient_sign`.  Trivial but useful as a building   *)
(* block downstream (every orientation-driven branch needs case analysis).  *)
Lemma orient_sign_eq_dec :
  forall (s t : orient_sign), {s = t} + {s <> t}.
Proof. decide equality. Defined.

(* `b64_orient_sign` is total: the match is exhaustive on `b64_compare`'s   *)
(* return value.  Phrased as an existence claim, suitable for downstream    *)
(* case-splits that need an explicit witness.                                *)
Lemma b64_orient_sign_total :
  forall P0 P1 Q, exists s, b64_orient_sign P0 P1 Q = s.
Proof. intros. eexists. reflexivity. Qed.

(* The four sign constructors are pairwise distinct.  Eight cases; one      *)
(* tactic block via `discriminate`.                                          *)
Lemma orient_sign_distinct :
     OrientPos  <> OrientNeg
  /\ OrientPos  <> OrientZero
  /\ OrientPos  <> OrientNan
  /\ OrientNeg  <> OrientZero
  /\ OrientNeg  <> OrientNan
  /\ OrientZero <> OrientNan.
Proof. repeat split; discriminate. Qed.

(* If `b64_orient_sign` returns anything other than `OrientNan`, then       *)
(* `b64_compare`'s result on the underlying value was `Some _`, i.e. the    *)
(* orient2d value was a non-NaN float.  Useful for downstream proofs that   *)
(* dispatch on whether the predicate gave a definite answer.                 *)
Lemma b64_orient_sign_non_nan_iff_compare_some :
  forall P0 P1 Q,
    b64_orient_sign P0 P1 Q <> OrientNan
    <-> exists c, b64_compare (b64_orient2d P0 P1 Q)
                              (Binary.B754_zero prec emax false) = Some c.
Proof.
  intros P0 P1 Q. unfold b64_orient_sign.
  destruct (b64_compare _ _) eqn:Hcmp.
  - split.
    + intros _. exists c. reflexivity.
    + intros _.
      destruct c; discriminate.
  - split.
    + intros H. exfalso. apply H. reflexivity.
    + intros [c Hc]. discriminate.
Qed.

(* ============================================================================
   SHEWCHUK STAGE A: error-bounded filter.
   ----------------------------------------------------------------------------
   The naive `b64_orient_sign` above can flip sign at near-collinear inputs
   because of rounding error.  Shewchuk's adaptive orient2d (1997) closes
   that with a four-stage refinement: a fast filter (Stage A) that returns
   the naive sign when it's reliable, falling back to increasingly precise
   expansion arithmetic (Stages B / C / D) only when the filter cannot
   decide.  This file ships Stage A only -- the deeper stages are deferred.

   The filter:

     det     = orient2d(P0, P1, Q)               -- the naive value
     detsum  = |t1| + |t2|                       -- magnitude budget
              where t1 = (P1.x - P0.x)(Q.y - P0.y)
                    t2 = (Q.x  - P0.x)(P1.y - P0.y)
     errbnd  = (3 + 16 * EPSILON) * EPSILON * detsum

     |det| > errbnd  ==>  sign(det) is reliable.
     else            ==>  Stage A is uncertain; deeper stages would refine.

   Returning `OrientUncertain` in the latter case makes the imprecision
   honest: callers can either fall back to a slower predicate or treat
   uncertain as collinear with a documented caveat -- but they cannot
   confuse a near-zero rounding artefact with a confident sign.
   ============================================================================ *)

(* Flocq constants for the Stage A error bound.  All built via              *)
(* `binary_normalize prec emax _ _ mode_NE m e false`, which constructs the *)
(* binary_float representing `m * 2^e` -- no axioms, no Admitted.           *)

Definition b64_three : binary64 :=
  Binary.binary_normalize prec emax prec_gt_0_b64 prec_lt_emax_b64
    mode_NE 3 0 false.

Definition b64_sixteen : binary64 :=
  Binary.binary_normalize prec emax prec_gt_0_b64 prec_lt_emax_b64
    mode_NE 16 0 false.

(* IEEE 754 binary64 has 52 explicit mantissa bits + 1 implicit; the spacing
   at 1.0 is therefore 2^-52, which is Shewchuk's `epsilon`. *)
Definition b64_eps : binary64 :=
  Binary.binary_normalize prec emax prec_gt_0_b64 prec_lt_emax_b64
    mode_NE 1 (-52) false.

(* The Stage A coefficient `(3 + 16 * eps) * eps`.  Computed in binary64    *)
(* via the same Bplus / Bmult primitives used everywhere else -- so the    *)
(* OCaml extraction (which extracts these to native +. / *.) gets the      *)
(* identical IEEE 754 binary64 value.  Approximately 6.66e-16.              *)
Definition b64_errbound_A_coeff : binary64 :=
  b64_mult (b64_plus b64_three (b64_mult b64_sixteen b64_eps)) b64_eps.

(* Absolute value on binary64.  `Babs`'s NaN handler is unary (one arg),   *)
(* unlike `Bplus`/`Bmult`'s binary NaN handlers, so a separate constant is *)
(* needed.  Concrete payload, no axiom -- same pattern as `default_nan_b64`.*)
Definition default_abs_nan_b64
    (x : Binary.binary_float prec emax)
  : { z : Binary.binary_float prec emax | Binary.is_nan prec emax z = true } :=
  exist _ (Binary.B754_nan prec emax false 1 eq_refl) eq_refl.

Definition b64_abs (x : binary64) : binary64 :=
  Binary.Babs prec emax default_abs_nan_b64 x.

(* `detsum = |t1| + |t2|`.  t1 and t2 are the two halves of the cross      *)
(* product before the final subtraction in `b64_orient2d`.                 *)
Definition b64_orient2d_detsum (P0 P1 Q : BPoint) : binary64 :=
  let t1 := b64_mult (b64_minus (bx P1) (bx P0)) (b64_minus (by_ Q)  (by_ P0)) in
  let t2 := b64_mult (b64_minus (bx Q)  (bx P0)) (b64_minus (by_ P1) (by_ P0)) in
  b64_plus (b64_abs t1) (b64_abs t2).

(* The Stage A error threshold for the triangle: `errbnd = coeff * detsum`. *)
Definition b64_orient2d_errbound (P0 P1 Q : BPoint) : binary64 :=
  b64_mult b64_errbound_A_coeff (b64_orient2d_detsum P0 P1 Q).

(* Five-valued sign type extending `orient_sign` with `OrientUncertain` for *)
(* the Stage A filter-cannot-decide case.  Same NaN-explicit discipline.   *)
Inductive orient_sign_robust : Type :=
| OrientRPos
| OrientRNeg
| OrientRZero
| OrientRNan
| OrientRUncertain.

(* Robust sign decoder.  Stage A filter: if |det| strictly exceeds the     *)
(* error bound, the naive sign is reliable.  Otherwise return Uncertain.   *)
(* NaN inputs (either det itself NaN or comparisons returning None)        *)
(* propagate to OrientRNan, matching the naive decoder's discipline.       *)
Definition b64_orient_sign_filtered (P0 P1 Q : BPoint) : orient_sign_robust :=
  let det := b64_orient2d P0 P1 Q in
  let bnd := b64_orient2d_errbound P0 P1 Q in
  let abs_det := b64_abs det in
  let zero := Binary.B754_zero prec emax false in
  (* First check: is det itself NaN?  b64_compare with anything yields None. *)
  match b64_compare det zero with
  | None => OrientRNan
  | Some Eq => OrientRZero
  | Some c =>
      (* det is non-NaN, non-zero; check the filter against bnd. *)
      match b64_compare bnd abs_det with
      | None => OrientRNan
      | Some Lt =>
          (* bnd < |det| -- filter passes, naive sign is reliable. *)
          match c with
          | Lt => OrientRNeg
          | Gt => OrientRPos
          | Eq => OrientRZero  (* unreachable: c was matched non-Eq above *)
          end
      | Some _ =>
          (* bnd >= |det| -- filter cannot decide. *)
          OrientRUncertain
      end
  end.

(* -------------------------------------------------------------------------- *)
(* Structural lemmas about the filtered sign.                                 *)
(* -------------------------------------------------------------------------- *)

Lemma orient_sign_robust_eq_dec :
  forall (s t : orient_sign_robust), {s = t} + {s <> t}.
Proof. decide equality. Defined.

Lemma b64_orient_sign_filtered_total :
  forall P0 P1 Q, exists s, b64_orient_sign_filtered P0 P1 Q = s.
Proof. intros. eexists. reflexivity. Qed.

Lemma orient_sign_robust_distinct :
     OrientRPos <> OrientRNeg
  /\ OrientRPos <> OrientRZero
  /\ OrientRPos <> OrientRNan
  /\ OrientRPos <> OrientRUncertain
  /\ OrientRNeg <> OrientRZero
  /\ OrientRNeg <> OrientRNan
  /\ OrientRNeg <> OrientRUncertain
  /\ OrientRZero <> OrientRNan
  /\ OrientRZero <> OrientRUncertain
  /\ OrientRNan <> OrientRUncertain.
Proof. repeat split; discriminate. Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit -- should match the existing Validate_binary64 set.           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_orient_sign_total.
Print Assumptions b64_orient_sign_non_nan_iff_compare_some.
Print Assumptions b64_orient_sign_filtered_total.
