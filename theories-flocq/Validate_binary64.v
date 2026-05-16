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

(* Transparent (`Defined.`) so `vm_compute` / `cbv` can reduce through
   `Binary.binary_normalize`-style constructors that take these as
   prop-level witnesses.  The proof bodies are trivial `lia`s; making them
   transparent doesn't expand the API or weaken the spec. *)
Lemma prec_gt_0_b64 : FLX.Prec_gt_0 prec.
Proof. unfold prec, FLX.Prec_gt_0. lia. Defined.

Lemma prec_lt_emax_b64 : Prec_lt_emax prec emax.
Proof. unfold prec, emax, Prec_lt_emax. lia. Defined.

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

(* Division.  Like Bplus/Bminus/Bmult, Bdiv takes a NaN handler and a       *)
(* rounding mode.  Phase 1 intersection-point computation is the first      *)
(* consumer; division is needed for the t-parameter of a segment            *)
(* intersection.  Unlike the other ops, division is not exact even in the   *)
(* integer regime -- two integer-valued binary64s with |a|, |b| <= 2^25     *)
(* can give a non-integer quotient.  Soundness theorems for divisions       *)
(* therefore have a forward-error shape rather than the bit-exactness       *)
(* shape Phase 0/1 enjoyed for + / - / *.                                    *)
Definition b64_div   (x y : binary64) : binary64 :=
  Binary.Bdiv   prec emax prec_gt_0_b64 prec_lt_emax_b64 default_nan_b64 mode_b64 x y.

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

(* -------------------------------------------------------------------------- *)
(* Abstract simplifier.                                                       *)
(*                                                                            *)
(* The simplifier is parametric in a 4-argument boolean predicate             *)
(* `pred eps kept r q`.  Inside this Section, neither the fixpoint nor the   *)
(* structural lemmas mention `b64_cross`, `b64_dist_sq`, `b64_plus`,         *)
(* `b64_minus`, or `b64_mult`.  Per-theorem `Print Assumptions` on the        *)
(* lemmas below is therefore classic-clean: the only axioms inherited are    *)
(* the structural ones from `Stdlib.List` etc., not the Flocq classical-    *)
(* rounding chain.                                                            *)
(*                                                                            *)
(* The concrete perpendicular-distance predicate `perp_predicate` and the    *)
(* concrete simplifier `greedy_simplify_perp_b64` are defined *outside* the *)
(* section, after the abstract layer closes.  The concrete definitions       *)
(* mention `b64_mult` / `b64_cross` / `b64_dist_sq` and so are classic-       *)
(* tainted at the definition level (since Flocq's `Bplus`/`Bminus`/`Bmult`  *)
(* directly carry `Classical_Prop.classic`).  Callers that want a structural *)
(* property on the concrete form invoke the abstract lemma here with         *)
(* `perp_predicate` as the predicate argument at the call site -- pushing   *)
(* the classic-taint to the call and keeping every theorem in this file     *)
(* classic-clean.                                                             *)
(* -------------------------------------------------------------------------- *)

Section AbstractSimplifier.

  Variable pred : binary64 -> BPoint -> BPoint -> BPoint -> bool.

  Fixpoint greedy_simplify_aux
      (eps : binary64) (kept : BPoint) (rest : list BPoint) : list BPoint :=
    match rest with
    | []          => [kept]
    | q :: more =>
        match more with
        | []          => [kept; q]
        | r :: _tail =>
            if pred eps kept r q
            then greedy_simplify_aux eps kept more
            else kept :: greedy_simplify_aux eps q more
        end
    end.

  Definition greedy_simplify
      (eps : binary64) (pts : list BPoint) : list BPoint :=
    match pts with
    | []         => []
    | p :: rest  => greedy_simplify_aux eps p rest
    end.

End AbstractSimplifier.

(* -------------------------------------------------------------------------- *)
(* Concrete perpendicular-distance predicate and simplifier.                   *)
(*                                                                            *)
(* These mention the classic-tainted Flocq binary arithmetic and so cannot    *)
(* be the subject of a classic-clean theorem.  The abstract layer above      *)
(* covers every structural property; callers apply those with `perp_pred`    *)
(* in place.                                                                  *)
(* -------------------------------------------------------------------------- *)

Definition perp_pred (eps : binary64) (kept r q : BPoint) : bool :=
  let c   := b64_cross kept r q in
  let lhs := b64_mult c c in
  let rhs := b64_mult (b64_mult eps eps) (b64_dist_sq kept r) in
  b64_le lhs rhs.

Definition greedy_simplify_perp_b64
    (eps : binary64) (pts : list BPoint) : list BPoint :=
  greedy_simplify perp_pred eps pts.

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

(* -------------------------------------------------------------------------- *)
(* Structural lemmas, all stated against the abstract simplifier so that no  *)
(* theorem here mentions the classic-tainted Flocq binary operations.        *)
(*                                                                            *)
(* The lemmas live in a second section parameterised again by `pred`.        *)
(* After `End AbstractSimplifierLemmas.`, each lemma has the shape           *)
(*    forall (pred : ...) ..., ...                                           *)
(* so a caller wanting a concrete property on `greedy_simplify_perp_b64`     *)
(* writes                                                                     *)
(*    apply (greedy_simplify_preserves_head perp_pred)                       *)
(* and the classic-taint flows into the *application* (which mentions the   *)
(* concrete predicate) rather than into the shipped theorem.                 *)
(* -------------------------------------------------------------------------- *)

Section AbstractSimplifierLemmas.

  Variable pred : binary64 -> BPoint -> BPoint -> BPoint -> bool.

  Lemma greedy_simplify_nil :
    forall eps, greedy_simplify pred eps [] = [].
  Proof. reflexivity. Qed.

  Lemma greedy_simplify_singleton :
    forall eps p, greedy_simplify pred eps [p] = [p].
  Proof. reflexivity. Qed.

  (* Two-point base case: no decision is made because there is no third     *)
  (* point to triangulate against, so output is the input verbatim.         *)
  Lemma greedy_simplify_two_points :
    forall eps p q, greedy_simplify pred eps [p; q] = [p; q].
  Proof. reflexivity. Qed.

  (* Structural head preservation: the auxiliary-form output begins with    *)
  (* the `kept` argument.                                                   *)
  Lemma greedy_simplify_aux_head :
    forall eps kept rest default,
      hd default (greedy_simplify_aux pred eps kept rest) = kept.
  Proof.
    intros eps kept rest d. revert kept.
    induction rest as [| q more IH]; intros kept.
    - reflexivity.
    - destruct more as [| r tail].
      + reflexivity.
      + cbn.
        destruct (pred _ _ _ _).
        * apply IH.
        * reflexivity.
  Qed.

  (* Top-level head preservation: for non-empty input, head of output       *)
  (* equals head of input.                                                  *)
  Theorem greedy_simplify_preserves_head :
    forall eps p rest default,
      hd default (greedy_simplify pred eps (p :: rest)) = p.
  Proof.
    intros eps p rest d.
    unfold greedy_simplify.
    apply greedy_simplify_aux_head.
  Qed.

  (* The auxiliary form always emits at least the `kept` point.             *)
  Lemma greedy_simplify_aux_nonempty :
    forall eps kept rest, greedy_simplify_aux pred eps kept rest <> [].
  Proof.
    intros eps kept rest. revert kept.
    induction rest as [| q more IH]; intros kept.
    - cbn. discriminate.
    - destruct more as [| r tail].
      + cbn. discriminate.
      + cbn. destruct (pred _ _ _ _).
        * apply IH.
        * discriminate.
  Qed.

  (* Top-level: non-empty input gives non-empty output.                     *)
  Lemma greedy_simplify_nonempty :
    forall eps p rest, greedy_simplify pred eps (p :: rest) <> [].
  Proof.
    intros eps p rest.
    unfold greedy_simplify.
    apply greedy_simplify_aux_nonempty.
  Qed.

  (* Length bound on the auxiliary form: output has at most `S (length     *)
  (* rest)` points -- one for `kept` plus one per remaining input.  The    *)
  (* simplifier may drop but never inserts.                                 *)
  Lemma greedy_simplify_aux_length_le :
    forall eps kept rest,
      (length (greedy_simplify_aux pred eps kept rest) <= S (length rest))%nat.
  Proof.
    intros eps kept rest. revert kept.
    induction rest as [| q more IH]; intros kept.
    - cbn. lia.
    - destruct more as [| r tail].
      + cbn. lia.
      + cbn. destruct (pred _ _ _ _).
        * specialize (IH kept). cbn in IH. lia.
        * cbn. specialize (IH q). cbn in IH. lia.
  Qed.

  (* Top-level length bound: output length never exceeds input length.      *)
  Lemma greedy_simplify_length_le :
    forall eps pts,
      (length (greedy_simplify pred eps pts) <= length pts)%nat.
  Proof.
    intros eps [|p rest].
    - cbn. lia.
    - unfold greedy_simplify.
      pose proof (greedy_simplify_aux_length_le eps p rest) as H.
      cbn. lia.
  Qed.

  (* Membership: `kept` appears in the auxiliary-form output for any        *)
  (* `rest`.                                                                 *)
  Lemma greedy_simplify_aux_in_kept :
    forall eps kept rest, In kept (greedy_simplify_aux pred eps kept rest).
  Proof.
    intros eps kept rest. revert kept.
    induction rest as [| q more IH]; intros kept.
    - cbn. left; reflexivity.
    - destruct more as [| r tail].
      + cbn. left; reflexivity.
      + cbn. destruct (pred _ _ _ _).
        * apply IH.
        * left; reflexivity.
  Qed.

  (* Top-level: the head of the input appears in the output.                *)
  Lemma greedy_simplify_in_head :
    forall eps p rest, In p (greedy_simplify pred eps (p :: rest)).
  Proof.
    intros eps p rest.
    unfold greedy_simplify.
    apply greedy_simplify_aux_in_kept.
  Qed.

End AbstractSimplifierLemmas.

(* -------------------------------------------------------------------------- *)
(* CATEGORY C theorem -- documented architectural boundary.                  *)
(*                                                                            *)
(* `greedy_simplify_binary64_never_none` makes a claim *about* the concrete *)
(* `greedy_simplify_binary64` wrapper as a named entity: that this specific *)
(* option-wrapped form never returns `None`.  Its statement is               *)
(*                                                                            *)
(*    forall eps pts, greedy_simplify_binary64 eps pts <> None               *)
(*                                                                            *)
(* and its proof is `unfold + discriminate` because the wrapper is defined  *)
(* as `Some(greedy_simplify_perp_b64 ...)` by construction.                  *)
(*                                                                            *)
(* The theorem cannot be reformulated parametrically while preserving its    *)
(* content.  A parametric attempt                                             *)
(*                                                                            *)
(*    forall (pred : ...) eps pts, Some (greedy_simplify pred eps pts) <>    *)
(*                                  None                                      *)
(*                                                                            *)
(* would lose the connection to the named wrapper and become a tautology    *)
(* about the `option` type, instantiated to this specific arity.  The       *)
(* concrete-wrapper specificity is the content; it cannot be lifted to the  *)
(* abstract layer.                                                            *)
(*                                                                            *)
(* The theorem therefore pulls `Classical_Prop.classic` in its per-theorem  *)
(* `Print Assumptions` closure, because its type mentions                   *)
(* `greedy_simplify_binary64`, which transitively mentions `b64_cross` /    *)
(* `b64_dist_sq` / `b64_mult`, which alias `Binary.Bmult` etc., which       *)
(* directly carry `classic` in their definition closure.                    *)
(*                                                                            *)
(* This is the first identified Category C theorem in the corpus:           *)
(* substantive content that the parametric architecture cannot cover         *)
(* without losing what the theorem is documenting.  Resolution of how       *)
(* Category C theorems are treated in the corpus is pending policy          *)
(* discussion (see `docs/category-c-policy.md`, to be written).             *)
(*                                                                            *)
(* The lemma is retained here as honest documentation of the wrapper's     *)
(* contract, with the contamination made visible by the `Print              *)
(* Assumptions` call below.                                                 *)
(* -------------------------------------------------------------------------- *)

Lemma greedy_simplify_binary64_never_none :
  forall eps pts, greedy_simplify_binary64 eps pts <> None.
Proof. intros eps pts. unfold greedy_simplify_binary64. discriminate. Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                               *)
(*                                                                            *)
(* Three abstract lemmas: per-theorem `Print Assumptions` is `Closed under  *)
(*    the global context` (zero axioms).  Stronger than the README           *)
(*    requires.                                                               *)
(*                                                                            *)
(* One Category C lemma: per-theorem `Print Assumptions` pulls the four-    *)
(*    axiom set including `Classical_Prop.classic`.  Contamination is       *)
(*    documented above; resolution pending policy.                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions greedy_simplify_preserves_head.
Print Assumptions greedy_simplify_aux_length_le.
Print Assumptions greedy_simplify_aux_in_kept.
Print Assumptions greedy_simplify_binary64_never_none.

(* -------------------------------------------------------------------------- *)
(* Extraction directive.  M-fast style: no native-float binding yet --       *)
(* binary64 extracts as a Coq record of integers, sound but slow.  A future *)
(* slice can add an Extract Inductive directive binding binary_float to     *)
(* OCaml float, with a no-double-rounding caveat citing JAR 2015 sec 3.2.   *)
(* -------------------------------------------------------------------------- *)

Require Extraction.
Extraction Language OCaml.

Recursive Extraction greedy_simplify_binary64 greedy_simplify_perp_b64.
