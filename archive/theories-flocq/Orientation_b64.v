(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Orientation_b64
   ----------------------------------------------------------------------------
   Executable binary64 orientation predicate.  Phase 0 of the NTS topological
   chokepoint sequence (see README), two layers:

     - Naive layer
         `b64_orient2d`            : the cross-product signed twice-area.
         `Inductive orient_sign`    : four-valued Pos / Neg / Zero / Nan.
         `b64_orient_sign_naive`    : sign of the naive cross product, can
                                      flip at near-collinear inputs due
                                      to rounding.

     - Shewchuk Stage A filter
         `b64_three`, `b64_sixteen`, `b64_eps`
                                   : Flocq constants for the error bound.
         `b64_errbound_A_coeff`    : `(3 + 16 * eps) * eps`, Shewchuk's
                                      Stage A forward-error coefficient.
         `b64_orient2d_detsum`     : `|t1| + |t2|`, the operand-magnitude
                                      budget.
         `b64_orient2d_errbound`   : `errbound_A_coeff * detsum`.
         `Inductive orient_sign_robust`
                                   : five-valued, adds OrientRUncertain.
         `b64_orient_sign_filtered`: refuses to commit to a sign when
                                      `|det|` is within the bound of zero.

   Both layers extract to OCaml native float through
   `Validate_binary64_extract.v` and ship into the
   [NetTopologySuite.Curve] `Robust.Orientation` namespace.

   PROOF STATUS
   ============
   - Computational implementation : both layers complete + extracted to OCaml.
   - Structural invariants        : Qed-closed.  Decidable equality on the
                                    four- and five-valued sign types;
                                    totality of `b64_orient_sign_naive` and
                                    `b64_orient_sign_filtered`; pairwise
                                    distinctness of constructors; non-NaN
                                    naive sign iff `b64_compare` returned
                                    `Some _`.
   - Arithmetic identities        : NOT YET CLAIMED.  Antisymmetry, cyclic
                                    permutation, translation invariance
                                    hold over ℝ but in binary64 need
                                    Flocq's `Bminus_correct` /
                                    `Bmult_correct` no-overflow
                                    preconditions -- the same proof slice
                                    deferred for the simplifier R-bridge.
                                    Both close together when that slice
                                    lands.
   - Shewchuk Stages B / C / D    : NOT YET CLAIMED.  Expansion-arithmetic
                                    refinement that would resolve
                                    `OrientRUncertain` into a definite
                                    Pos / Neg / Zero is the next slice on
                                    top of Stage A.

   No `Admitted` theorems.  The corpus-wide invariant applies: properties
   that are not yet proven are absent from the file rather than stubbed.

   TARGET THEOREM (Stages B / C, planned, not yet stated as Coq syntax)
   ===================================================================
   The endgame of Phase 0 is an `exact` predicate that closes the
   robustness loop by resolving `OrientRUncertain` cases via Shewchuk
   expansion arithmetic.  Sketch of the planned theorem (prose only,
   no `Admitted` Lemma in the corpus -- see also the companion audit
   in `docs/audit-shewchuk-stages.md`):

       Definition no_overflow_precond (p0 p1 q : BPoint) : Prop :=
         is_finite_bp p0 = true  /\
         is_finite_bp p1 = true  /\
         is_finite_bp q  = true  /\
         coords_bounded_by p0 p1 q two_to_the_500.
         (* Conservative: |coord| < 2^500 leaves ~24 bits of margin    *)
         (* for intermediate expansion ops before overflow risk.       *)

       Inductive orient_sign_exact : Type :=
       | OrientXPos
       | OrientXNeg
       | OrientXZero.

       Definition b64_orient2d_exact (p0 p1 q : BPoint)
                : option orient_sign_exact.
         (* On `OrientRPos` / `OrientRNeg` / `OrientRZero` from Stage A,
            return the corresponding `OrientX*`.  On `OrientRUncertain`,
            run the expansion-arithmetic refinement.  On `OrientRNan`,
            return None -- the caller falls back to MPFR or rationals. *)

       Theorem b64_orient2d_exact_sound :
         forall p0 p1 q,
           no_overflow_precond p0 p1 q ->
           match b64_orient2d_exact p0 p1 q with
           | Some OrientXPos  => 0 < cross_R (B2R_pt p0) (B2R_pt p1) (B2R_pt q)
           | Some OrientXNeg  => cross_R (B2R_pt p0) (B2R_pt p1) (B2R_pt q) < 0
           | Some OrientXZero => cross_R (B2R_pt p0) (B2R_pt p1) (B2R_pt q) = 0
           | None             => True  (* no claim; caller must fall back *)
           end.

   Where `cross_R` is the R-valued cross product on the corpus's `Point`
   record (see `theories/Orientation.v`) and `B2R_pt` lifts a `BPoint`
   to a `Point` via `Binary.B2R` on each coordinate (the same lift used
   by the simplifier R-bridge target).

   Critical-path dependency.  The whole theorem rests on a binary64-to-R
   bridge that wraps Flocq's `Bplus_correct` / `Bmult_correct` for our
   specific `b64_plus` / `b64_minus` / `b64_mult` helpers under the
   `no_overflow_precond`.  The per-op lifts (`b64_plus_correct`,
   `b64_minus_correct`, `b64_mult_correct`) are now Qed-closed in
   `theories-flocq/B64_bridge.v`.  The remaining work is threading the
   precondition through the recursive / expansion structure of each
   downstream theorem.  See `docs/audit-shewchuk-stages.md` for the
   expected ordering of work.

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
(* The two halves of the cross-product, factored out so both `b64_orient2d`  *)
(* and the Stage A filter's `detsum` share the same intermediate values:     *)
(*    t1 = (P1.x - P0.x) * (Q.y  - P0.y)                                     *)
(*    t2 = (Q.x  - P0.x) * (P1.y - P0.y)                                     *)
(* `b64_orient2d` is `t1 - t2`; `detsum` is `|t1| + |t2|`.  The filtered    *)
(* sign decoder calls `_terms` once and reuses the pair.                     *)
(* -------------------------------------------------------------------------- *)

(* Internal sharing helper.  `Local` so it doesn't pollute the         *)
(* `NTS.Proofs.Flocq` namespace -- the only callers are inside this    *)
(* file.  Extraction still emits it (referenced transitively).         *)
Local Definition b64_orient2d_terms (P0 P1 Q : BPoint) : binary64 * binary64 :=
  (b64_mult (b64_minus (bx P1) (bx P0)) (b64_minus (by_ Q)  (by_ P0)),
   b64_mult (b64_minus (bx Q)  (bx P0)) (b64_minus (by_ P1) (by_ P0))).

Definition b64_orient2d (P0 P1 Q : BPoint) : binary64 :=
  let (t1, t2) := b64_orient2d_terms P0 P1 Q in
  b64_minus t1 t2.

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

(* Naive decision procedure.  Routes through `b64_compare`, which itself   *)
(* returns `None` exactly on NaN inputs -- we surface that as `OrientNan`. *)
(* Called `_naive` for symmetry with `b64_orient_sign_filtered` below.     *)

Definition b64_orient_sign_naive (P0 P1 Q : BPoint) : orient_sign :=
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

(* `b64_orient_sign_naive` is total: the match is exhaustive on            *)
(* `b64_compare`'s return value.                                            *)
Lemma b64_orient_sign_naive_total :
  forall P0 P1 Q, exists s, b64_orient_sign_naive P0 P1 Q = s.
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

(* If `b64_orient_sign_naive` returns anything other than `OrientNan`, then  *)
(* `b64_compare`'s result on the underlying value was `Some _`, i.e. the    *)
(* orient2d value was a non-NaN float.  Useful for downstream proofs that   *)
(* dispatch on whether the predicate gave a definite answer.                 *)
Lemma b64_orient_sign_naive_non_nan_iff_compare_some :
  forall P0 P1 Q,
    b64_orient_sign_naive P0 P1 Q <> OrientNan
    <-> exists c, b64_compare (b64_orient2d P0 P1 Q)
                              (Binary.B754_zero prec emax false) = Some c.
Proof.
  intros P0 P1 Q. unfold b64_orient_sign_naive.
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

(* `detsum = |t1| + |t2|`.  Reuses the shared `b64_orient2d_terms` helper  *)
(* so the filtered decoder below does not recompute t1 / t2.                *)
Definition b64_orient2d_detsum (P0 P1 Q : BPoint) : binary64 :=
  let (t1, t2) := b64_orient2d_terms P0 P1 Q in
  b64_plus (b64_abs t1) (b64_abs t2).

(* The Stage A error threshold for the triangle: `errbnd = coeff * detsum`. *)
Definition b64_orient2d_errbound (P0 P1 Q : BPoint) : binary64 :=
  b64_mult b64_errbound_A_coeff (b64_orient2d_detsum P0 P1 Q).

(* Five-valued sign type extending `orient_sign` with `OrientRUncertain`   *)
(* for the Stage A filter-cannot-decide case.  Same NaN-explicit discipline.*)
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
(*                                                                          *)
(* Calls `b64_orient2d_terms` exactly once and threads (t1, t2) through    *)
(* both the det computation and the detsum / errbound computation, so no   *)
(* binary64 arithmetic is duplicated between the two halves of the filter. *)
(* The outer match on `b64_compare det zero` splits Lt / Gt / Eq into       *)
(* three branches so there is no dead `Eq` case inside the filter check.    *)
Definition b64_orient_sign_filtered (P0 P1 Q : BPoint) : orient_sign_robust :=
  let (t1, t2) := b64_orient2d_terms P0 P1 Q in
  let det      := b64_minus t1 t2 in
  let detsum   := b64_plus (b64_abs t1) (b64_abs t2) in
  let bnd      := b64_mult b64_errbound_A_coeff detsum in
  let abs_det  := b64_abs det in
  let zero     := Binary.B754_zero prec emax false in
  match b64_compare det zero with
  | None        => OrientRNan
  | Some Eq     => OrientRZero
  | Some Lt =>
      (* det is strictly negative; if filter passes, sign is Neg.            *)
      match b64_compare bnd abs_det with
      | None        => OrientRNan
      | Some Lt     => OrientRNeg
      | Some _      => OrientRUncertain
      end
  | Some Gt =>
      (* det is strictly positive; if filter passes, sign is Pos.            *)
      match b64_compare bnd abs_det with
      | None        => OrientRNan
      | Some Lt     => OrientRPos
      | Some _      => OrientRUncertain
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

Print Assumptions b64_orient_sign_naive_total.
Print Assumptions b64_orient_sign_naive_non_nan_iff_compare_some.
Print Assumptions b64_orient_sign_filtered_total.
