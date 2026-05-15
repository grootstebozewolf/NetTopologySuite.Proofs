(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Validate_binary64
   ----------------------------------------------------------------------------
   Sound executable validation using Flocq's binary64 representation:
   the computational + structural layer of the binary64 simplifier.

     - A `binary64` type instantiating Flocq's `binary_float prec emax`.
     - A `BPoint` record of two binary64 coordinates.
     - Executable binary64 arithmetic helpers (`b64_plus` / `b64_minus`
       / `b64_mult` / `b64_le`) and the geometric `b64_cross` /
       `b64_dist_sq`.
     - The greedy perpendicular-distance simplifier on `list BPoint`.
     - Structural Qed-closed invariants about the simplifier.

   This file does NOT import the classical real line.  The R-bridge
   wrappers (`b64_to_R`, `B2R_pt`, `map_B2R`, `is_finite_bp`) and the
   semantic soundness theorem against `Simplify.simp_star` live in the
   companion file `Validate_binary64_bridge.v`.  Splitting the two keeps
   this file's axiom footprint minimal -- the classical-reals axioms
   only get paid for when soundness against the R-spec is actually used.

   Lives in `theories-flocq/` rather than `theories/` because the file
   depends on Flocq, which is not available on the host CI runner.  Only
   the containerised build (driven by `_CoqProject.full` plus
   `coq-flocq.4.2.2`) compiles it.  The corpus's "no Admitted, no Axiom,
   no Parameter" invariant applies HERE TOO -- the directory split is
   about which CI builds the file, not about which proof standard it
   meets.

   PROOF STATUS
   ============
   - Computational implementation : complete + extracted to OCaml.
   - Structural invariants        : fully Qed-closed
                                    (`_nil`, `_singleton`, `_two_points`,
                                    `_never_none`, `_some_eq`, `_aux_head`,
                                    `_preserves_head`, `_aux_nonempty`,
                                    `_nonempty`, `_aux_length_le`,
                                    `_length_le`, `_aux_in_kept`,
                                    `_in_head`).
   - Semantic soundness bridge    : NOT YET CLAIMED.  Lives in the
       companion bridge file together with the `B2R`-based statements.
       Requires threading Flocq's `Bplus_correct` / `Bmult_correct`
       no-overflow preconditions through the Fixpoint -- a dedicated
       proof slice (Phase 0/1 of the chokepoint roadmap, see README),
       explicitly deferred rather than stubbed with `Admitted`.

   EXPECTED AXIOMS (verified by `Print Assumptions` at end of file):
     - ClassicalDedekindReals.sig_not_dec
     - ClassicalDedekindReals.sig_forall_dec
     - FunctionalExtensionality.functional_extensionality_dep
     - Classical_Prop.classic
   Empirical boundary of axiom hygiene in this file (probed with in-file
   diagnostic lemmas that are now removed, see commit history):
     - Pure list/nat/boolean proofs                              -> Closed.
     - Refl-style proofs about BPoint                            -> Closed.
     - `destruct (b64_le _ _)` alone                             -> Closed.
     - Anything traversing `greedy_simplify_perp_b64_aux`'s body -> 4 axioms.
   The four axioms enter through `Binary.Bplus` / `Bminus` / `Bmult`,
   which Flocq defines in terms of R-valued rounding (`Round_NE_pt`).
   `Bcompare` itself is structural and axiom-clean.  Dropping the
   `Stdlib.Reals` and `NTS.Proofs.*` imports (done) did not reduce the
   set -- Flocq itself pulls them in transitively through the rounding
   semantics of its arithmetic operations.
   A future axiom-free structural layer would parametrize the Fixpoint
   over abstract `le` / `mult` / `cross` / `dist_sq` operations and
   instantiate them with the Flocq versions only at the bridge file --
   tracked as a follow-up, not in scope for the current slice.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import IEEE754.BinarySingleNaN.
From Flocq Require Import Core.

(* Deliberately NO imports from `Stdlib.Reals` or `NTS.Proofs.*` here.  This *)
(* file is the executable + structural layer for the binary64 simplifier:   *)
(* nothing it proves needs the classical real line.  The R-bridge wrappers  *)
(* (`b64_to_R`, `B2R_pt`, `map_B2R`, `is_finite_bp`) live in a separate     *)
(* `_bridge.v` file, paid for only when the semantic soundness theorem is   *)
(* tackled.                                                                  *)

(* -------------------------------------------------------------------------- *)
(* Binary64 setup: IEEE 754 double precision = binary_float 53 1024.          *)
(* -------------------------------------------------------------------------- *)

Definition prec  : Z := 53.
Definition emax  : Z := 1024.
Definition binary64 := Binary.binary_float prec emax.

Record BPoint : Type := mkBP { bx : binary64; by_ : binary64 }.
(* `by` is a reserved tactical token in Rocq; using `by_` to avoid the clash. *)

(* -------------------------------------------------------------------------- *)
(* Flocq plumbing: pin prec/emax proof witnesses, NaN handler, rounding mode. *)
(*                                                                            *)
(* Flocq's `Bplus`, `Bminus`, `Bmult` each take six leading arguments before *)
(* the operands: `prec`, `emax`, a proof `Prec_gt_0 prec`, a proof          *)
(* `Prec_lt_emax prec emax`, a NaN-pair-to-NaN propagation function, and    *)
(* a rounding `mode`.  We fix all five for binary64 once, then wrap the     *)
(* operators in zero-argument-overhead helpers.                              *)
(* -------------------------------------------------------------------------- *)

Lemma prec_gt_0_b64 : FLX.Prec_gt_0 prec.
Proof. unfold prec, FLX.Prec_gt_0. lia. Qed.

Lemma prec_lt_emax_b64 : Prec_lt_emax prec emax.
Proof. unfold prec, emax, Prec_lt_emax. lia. Qed.

(* Default NaN-propagation convention: produce a quiet NaN with payload 1.  *)
(* The IEEE-754 standard underspecifies NaN payload propagation; CompCert  *)
(* makes the same choice.  The construction below is concrete -- no axiom: *)
(* `nan_pl 53 1` evaluates to `true` by computation, and `is_nan` of any   *)
(* `B754_nan` is `true` by construction.                                    *)
Definition default_nan_b64
    (x y : Binary.binary_float prec emax)
  : { z : Binary.binary_float prec emax | Binary.is_nan prec emax z = true } :=
  exist _ (Binary.B754_nan prec emax false 1 eq_refl) eq_refl.

Definition mode_b64 : mode := mode_NE.

Definition b64_plus  (x y : binary64) : binary64 :=
  Binary.Bplus  prec emax prec_gt_0_b64 prec_lt_emax_b64 default_nan_b64 mode_b64 x y.

Definition b64_minus (x y : binary64) : binary64 :=
  Binary.Bminus prec emax prec_gt_0_b64 prec_lt_emax_b64 default_nan_b64 mode_b64 x y.

Definition b64_mult  (x y : binary64) : binary64 :=
  Binary.Bmult  prec emax prec_gt_0_b64 prec_lt_emax_b64 default_nan_b64 mode_b64 x y.

Definition b64_compare (x y : binary64) : option comparison :=
  Binary.Bcompare prec emax x y.

(* Boolean <= test.  Returns `false` on NaN inputs (the safe default for our *)
(* simplifier: "if uncertain, do not drop").                                 *)
Definition b64_le (x y : binary64) : bool :=
  match b64_compare x y with
  | Some Lt | Some Eq => true
  | _                 => false
  end.

(* -------------------------------------------------------------------------- *)
(* Geometric helpers on BPoint.                                               *)
(*                                                                            *)
(* `b64_cross P0 P1 Q` mirrors `Orientation.cross` from the corpus:           *)
(*    (P1.x - P0.x) * (Q.y  - P0.y)                                          *)
(*  - (Q.x  - P0.x) * (P1.y - P0.y)                                          *)
(*                                                                            *)
(* `b64_dist_sq P Q` mirrors `Distance.dist_sq`:                              *)
(*    (P.x - Q.x)^2 + (P.y - Q.y)^2                                          *)
(* -------------------------------------------------------------------------- *)

Definition b64_cross (p0 p1 q : BPoint) : binary64 :=
  b64_minus
    (b64_mult (b64_minus (bx p1) (bx p0)) (b64_minus (by_ q)  (by_ p0)))
    (b64_mult (b64_minus (bx q)  (bx p0)) (b64_minus (by_ p1) (by_ p0))).

Definition b64_dist_sq (p q : BPoint) : binary64 :=
  b64_plus
    (b64_mult (b64_minus (bx p) (bx q)) (b64_minus (bx p) (bx q)))
    (b64_mult (b64_minus (by_ p) (by_ q)) (b64_minus (by_ p) (by_ q))).

(* -------------------------------------------------------------------------- *)
(* Greedy perpendicular-distance simplifier on binary64.                     *)
(*                                                                            *)
(* Mirrors `Validate.greedy_simplify_perp_aux` from the R version, with     *)
(* the squared-cross-product perpendicular test:                            *)
(*     (cross kept r q)^2  <=  eps^2 * dist_sq kept r                       *)
(* expressed in binary64 as:                                                *)
(*     b64_mult c c  <=  b64_mult (b64_mult eps eps) (b64_dist_sq kept r)   *)
(* where c = b64_cross kept r q.                                            *)
(* -------------------------------------------------------------------------- *)

Fixpoint greedy_simplify_perp_b64_aux
    (eps : binary64) (kept : BPoint) (rest : list BPoint) : list BPoint :=
  match rest with
  | []          => [kept]
  | q :: more =>
      match more with
      | []          => [kept; q]
      | r :: _tail =>
          let c   := b64_cross kept r q in
          let lhs := b64_mult c c in
          let rhs := b64_mult (b64_mult eps eps) (b64_dist_sq kept r) in
          if b64_le lhs rhs
          then greedy_simplify_perp_b64_aux eps kept more
          else kept :: greedy_simplify_perp_b64_aux eps q more
      end
  end.

Definition greedy_simplify_perp_b64
    (eps : binary64) (pts : list BPoint) : list BPoint :=
  match pts with
  | []         => []
  | p :: rest  => greedy_simplify_perp_b64_aux eps p rest
  end.

(* The original `greedy_simplify_binary64` interface preserved as a thin    *)
(* wrapper returning `option` for backward compatibility with the soundness *)
(* theorems below; for now it routes everything through the perp form.     *)
Definition greedy_simplify_binary64
    (eps : binary64) (pts : list BPoint) : option (list BPoint) :=
  Some (greedy_simplify_perp_b64 eps pts).

(* -------------------------------------------------------------------------- *)
(* Structural Qed-closed lemmas about the binary64 simplifier.               *)
(*                                                                            *)
(* The corpus's "no Admitted, no Axiom, no Parameter" invariant applies to   *)
(* BOTH theories/ and theories-flocq/ -- the directory split is about which *)
(* CI runner builds the file (host vs container), not about which standard  *)
(* the proofs meet.  Anything we claim here must close with Qed.            *)
(*                                                                            *)
(* The headline soundness bridge -- "the binary64 result is simp_star-      *)
(* related to the input under the R interpretation, provided no             *)
(* intermediate computation overflows" -- requires threading Flocq's        *)
(* Bplus_correct / Bmult_correct no-overflow preconditions through the      *)
(* recursive case of the Fixpoint.  That's a substantial proof slice (Phase *)
(* 0/1 of the chokepoint roadmap, see README) and is deferred until a       *)
(* dedicated work item.  Until then this file ships the executable function *)
(* + extraction directive + a small set of structural sanity lemmas.        *)
(* -------------------------------------------------------------------------- *)

Lemma greedy_simplify_perp_b64_nil :
  forall eps, greedy_simplify_perp_b64 eps [] = [].
Proof. reflexivity. Qed.

Lemma greedy_simplify_perp_b64_singleton :
  forall eps p, greedy_simplify_perp_b64 eps [p] = [p].
Proof. reflexivity. Qed.

(* greedy_simplify_binary64 is greedy_simplify_perp_b64 wrapped in `Some`.  *)
Lemma greedy_simplify_binary64_never_none :
  forall eps pts, greedy_simplify_binary64 eps pts <> None.
Proof. intros eps pts. unfold greedy_simplify_binary64. discriminate. Qed.

(* Structural head preservation: the auxiliary-form output begins with the *)
(* `kept` argument.                                                         *)
Lemma greedy_simplify_perp_b64_aux_head :
  forall eps kept rest default,
    hd default (greedy_simplify_perp_b64_aux eps kept rest) = kept.
Proof.
  intros eps kept rest d. revert kept.
  induction rest as [| q more IH]; intros kept.
  - reflexivity.
  - destruct more as [| r tail].
    + reflexivity.
    + cbn.
      destruct (b64_le _ _).
      * apply IH.
      * reflexivity.
Qed.

(* Top-level head preservation: for non-empty input, head of output equals *)
(* head of input.                                                          *)
Theorem greedy_simplify_perp_b64_preserves_head :
  forall eps p rest default,
    hd default (greedy_simplify_perp_b64 eps (p :: rest)) = p.
Proof.
  intros eps p rest d.
  unfold greedy_simplify_perp_b64.
  apply greedy_simplify_perp_b64_aux_head.
Qed.

(* Two-point base case: no decision is made because there is no third       *)
(* point to triangulate against, so output is the input verbatim.           *)
Lemma greedy_simplify_perp_b64_two_points :
  forall eps p q, greedy_simplify_perp_b64 eps [p; q] = [p; q].
Proof. reflexivity. Qed.

(* The auxiliary form always emits at least the `kept` point.               *)
Lemma greedy_simplify_perp_b64_aux_nonempty :
  forall eps kept rest, greedy_simplify_perp_b64_aux eps kept rest <> [].
Proof.
  intros eps kept rest. revert kept.
  induction rest as [| q more IH]; intros kept.
  - cbn. discriminate.
  - destruct more as [| r tail].
    + cbn. discriminate.
    + cbn. destruct (b64_le _ _).
      * apply IH.
      * discriminate.
Qed.

(* Top-level: non-empty input gives non-empty output.                       *)
Lemma greedy_simplify_perp_b64_nonempty :
  forall eps p rest, greedy_simplify_perp_b64 eps (p :: rest) <> [].
Proof.
  intros eps p rest.
  unfold greedy_simplify_perp_b64.
  apply greedy_simplify_perp_b64_aux_nonempty.
Qed.

(* Length bound on the auxiliary form: output has at most `S (length rest)` *)
(* points -- one for `kept` plus one per remaining input.  The simplifier   *)
(* may drop but never inserts.                                              *)
Lemma greedy_simplify_perp_b64_aux_length_le :
  forall eps kept rest,
    (length (greedy_simplify_perp_b64_aux eps kept rest) <= S (length rest))%nat.
Proof.
  intros eps kept rest. revert kept.
  induction rest as [| q more IH]; intros kept.
  - cbn. lia.
  - destruct more as [| r tail].
    + cbn. lia.
    + cbn. destruct (b64_le _ _).
      * (* drop q: recurse with the same kept *)
        specialize (IH kept). cbn in IH. lia.
      * (* keep kept, recurse with q *)
        cbn. specialize (IH q). cbn in IH. lia.
Qed.

(* Top-level length bound: output length never exceeds input length.        *)
Lemma greedy_simplify_perp_b64_length_le :
  forall eps pts,
    (length (greedy_simplify_perp_b64 eps pts) <= length pts)%nat.
Proof.
  intros eps [|p rest].
  - cbn. lia.
  - unfold greedy_simplify_perp_b64.
    pose proof (greedy_simplify_perp_b64_aux_length_le eps p rest) as H.
    cbn. lia.
Qed.

(* `greedy_simplify_binary64` is `Some` of the perp-form output.            *)
(* Strengthens `_never_none` by giving the exact body.                      *)
Lemma greedy_simplify_binary64_some_eq :
  forall eps pts,
    greedy_simplify_binary64 eps pts = Some (greedy_simplify_perp_b64 eps pts).
Proof. reflexivity. Qed.

(* Membership: `kept` appears in the auxiliary-form output for any `rest`.  *)
Lemma greedy_simplify_perp_b64_aux_in_kept :
  forall eps kept rest, In kept (greedy_simplify_perp_b64_aux eps kept rest).
Proof.
  intros eps kept rest. revert kept.
  induction rest as [| q more IH]; intros kept.
  - cbn. left; reflexivity.
  - destruct more as [| r tail].
    + cbn. left; reflexivity.
    + cbn. destruct (b64_le _ _).
      * apply IH.
      * left; reflexivity.
Qed.

(* Top-level: the head of the input appears in the output.                  *)
Lemma greedy_simplify_perp_b64_in_head :
  forall eps p rest, In p (greedy_simplify_perp_b64 eps (p :: rest)).
Proof.
  intros eps p rest.
  unfold greedy_simplify_perp_b64.
  apply greedy_simplify_perp_b64_aux_in_kept.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                              *)
(* -------------------------------------------------------------------------- *)

Print Assumptions greedy_simplify_perp_b64_preserves_head.
Print Assumptions greedy_simplify_perp_b64_aux_length_le.
Print Assumptions greedy_simplify_perp_b64_aux_in_kept.

(* -------------------------------------------------------------------------- *)
(* Extraction directive.  M-fast style: no native-float binding yet --       *)
(* binary64 extracts as a Coq record of integers, sound but slow.  A future *)
(* slice can add an Extract Inductive directive binding binary_float to     *)
(* OCaml float, with a no-double-rounding caveat citing JAR 2015 sec 3.2.   *)
(* -------------------------------------------------------------------------- *)

Require Extraction.
Extraction Language OCaml.

Recursive Extraction greedy_simplify_binary64 greedy_simplify_perp_b64.
