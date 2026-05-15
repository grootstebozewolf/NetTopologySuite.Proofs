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

(* -------------------------------------------------------------------------- *)
(* Axiom audit -- should match the existing Validate_binary64 set.           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_orient_sign_total.
Print Assumptions b64_orient_sign_non_nan_iff_compare_some.
