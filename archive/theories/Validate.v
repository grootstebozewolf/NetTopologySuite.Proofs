(* ============================================================================
   NetTopologySuite.Proofs.Validate
   ----------------------------------------------------------------------------
   Constructive (extractable) polyline simplifiers and their soundness proofs.

   This module turns the declarative spec `simp_star` / `simp_star_perp`
   from Simplify.v into actual functions that:

     - take a list of points and a tolerance,
     - return a simplified list,
     - come with a Coq proof that the result is in the relation -- i.e.
       the function is a sound witness for the inductive spec.

   The function uses Stdlib's `Rle_dec` (decidable real comparison) so that
   the body is a genuine sumbool dispatch.  No new axioms beyond the three
   classical-reals axioms the corpus already imports via Real.v.

   Once extracted to OCaml (next slice), these functions become callable
   from NTS C# code; their soundness theorems are the C#-side contract.

   No Admitted, no Axiom (except the three classical-reals axioms inherited
   from the corpus's Real.v).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import List.
Import ListNotations.
From NTS.Proofs Require Import Distance Orientation Linearise Simplify.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Cons-lifting lemmas: simp_star and simp_star_perp commute with prepending  *)
(* a fresh head.  Used by the correctness proofs of the greedy simplifiers   *)
(* (in the "keep" branch, the recursive call simplifies the tail and we     *)
(* prepend the kept vertex).                                                 *)
(* -------------------------------------------------------------------------- *)

Lemma simp_star_cons :
  forall (eps : R) (p : Point) (pts pts' : list Point),
    simp_star eps pts pts' ->
    simp_star eps (p :: pts) (p :: pts').
Proof.
  intros eps p pts pts' Hstar.
  induction Hstar as [pts | pts pts' pts'' Hstep _ IH].
  - apply simp_star_refl.
  - eapply simp_star_step.
    + apply simp_drop_later. exact Hstep.
    + exact IH.
Qed.

Lemma simp_star_perp_cons :
  forall (eps : R) (p : Point) (pts pts' : list Point),
    simp_star_perp eps pts pts' ->
    simp_star_perp eps (p :: pts) (p :: pts').
Proof.
  intros eps p pts pts' Hstar.
  induction Hstar as [pts | pts pts' pts'' Hstep _ IH].
  - apply simp_star_perp_refl.
  - eapply simp_star_perp_step.
    + apply simp_drop_later_perp. exact Hstep.
    + exact IH.
Qed.

(* -------------------------------------------------------------------------- *)
(* Chord-deficit greedy simplifier.                                           *)
(*                                                                            *)
(* The function walks the list once, left-to-right, carrying a `kept`        *)
(* vertex (the most recently emitted point).  At each interior position     *)
(* it tries to drop the candidate q if the chord-deficit through q is       *)
(* within 2*eps; otherwise it commits to keeping q.                          *)
(*                                                                            *)
(* Structural recursion: the inner match binds `more` and recursion is on    *)
(* `more`, a sub-term of `rest`.  No Function/measure needed.                *)
(* -------------------------------------------------------------------------- *)

Fixpoint greedy_simplify_aux (eps : R) (kept : Point) (rest : list Point)
  : list Point :=
  match rest with
  | []          => [kept]
  | q :: more =>
      match more with
      | []          => [kept; q]
      | r :: _tail =>
          if Rle_dec (dist kept q + dist q r) (dist kept r + 2 * eps)
          then (* drop q, keep walking from `kept` *)
               greedy_simplify_aux eps kept more
          else (* commit `kept`, recurse with q as the new `kept` *)
               kept :: greedy_simplify_aux eps q more
      end
  end.

Definition greedy_simplify (eps : R) (pts : list Point) : list Point :=
  match pts with
  | []         => []
  | p :: rest  => greedy_simplify_aux eps p rest
  end.

(* -------------------------------------------------------------------------- *)
(* Soundness: the greedy result is in simp_star relation with the input.    *)
(* -------------------------------------------------------------------------- *)

Lemma greedy_simplify_aux_correct :
  forall (eps : R) (kept : Point) (rest : list Point),
    simp_star eps (kept :: rest) (greedy_simplify_aux eps kept rest).
Proof.
  intros eps kept rest. revert kept.
  induction rest as [| q more IH]; intros kept.
  - cbn. apply simp_star_refl.
  - destruct more as [| r tail].
    + cbn. apply simp_star_refl.
    + cbn.
      destruct (Rle_dec (dist kept q + dist q r) (dist kept r + 2 * eps))
        as [Hle | _].
      * (* drop branch *)
        eapply simp_star_step.
        -- apply simp_drop_here. exact Hle.
        -- apply IH.
      * (* keep branch: prepend kept to the recursive result. *)
        apply simp_star_cons. apply IH.
Qed.

Theorem greedy_simplify_correct :
  forall (eps : R) (pts : list Point),
    simp_star eps pts (greedy_simplify eps pts).
Proof.
  intros eps pts. destruct pts as [| p rest].
  - cbn. apply simp_star_refl.
  - cbn. apply greedy_simplify_aux_correct.
Qed.

(* -------------------------------------------------------------------------- *)
(* Perpendicular-distance greedy simplifier (the Douglas-Peucker form        *)
(* matching Zygmunt & Rog 2026).  Same structure as above; only the test    *)
(* changes from chord deficit to squared cross-product.                      *)
(* -------------------------------------------------------------------------- *)

Fixpoint greedy_simplify_perp_aux (eps : R) (kept : Point) (rest : list Point)
  : list Point :=
  match rest with
  | []          => [kept]
  | q :: more =>
      match more with
      | []          => [kept; q]
      | r :: _tail =>
          if Rle_dec (cross kept r q * cross kept r q)
                     (eps * eps * dist_sq kept r)
          then greedy_simplify_perp_aux eps kept more
          else kept :: greedy_simplify_perp_aux eps q more
      end
  end.

Definition greedy_simplify_perp (eps : R) (pts : list Point) : list Point :=
  match pts with
  | []         => []
  | p :: rest  => greedy_simplify_perp_aux eps p rest
  end.

Lemma greedy_simplify_perp_aux_correct :
  forall (eps : R) (kept : Point) (rest : list Point),
    simp_star_perp eps (kept :: rest) (greedy_simplify_perp_aux eps kept rest).
Proof.
  intros eps kept rest. revert kept.
  induction rest as [| q more IH]; intros kept.
  - cbn. apply simp_star_perp_refl.
  - destruct more as [| r tail].
    + cbn. apply simp_star_perp_refl.
    + cbn.
      destruct (Rle_dec (cross kept r q * cross kept r q)
                        (eps * eps * dist_sq kept r))
        as [Hle | _].
      * eapply simp_star_perp_step.
        -- apply simp_drop_here_perp. exact Hle.
        -- apply IH.
      * apply simp_star_perp_cons. apply IH.
Qed.

Theorem greedy_simplify_perp_correct :
  forall (eps : R) (pts : list Point),
    simp_star_perp eps pts (greedy_simplify_perp eps pts).
Proof.
  intros eps pts. destruct pts as [| p rest].
  - cbn. apply simp_star_perp_refl.
  - cbn. apply greedy_simplify_perp_aux_correct.
Qed.

(* -------------------------------------------------------------------------- *)
(* Inheritance corollaries: the greedy outputs automatically satisfy all     *)
(* the spec-level invariants from Simplify.v -- length monotonicity, head   *)
(* and last vertex preservation.  These are the "contract methods" that an  *)
(* NTS C# wrapper can rely on after calling the extracted function.         *)
(* -------------------------------------------------------------------------- *)

Corollary greedy_simplify_length_monotone :
  forall eps pts,
    polyline_length (greedy_simplify eps pts) <= polyline_length pts.
Proof.
  intros eps pts.
  apply simp_star_length_monotone with (eps := eps).
  apply greedy_simplify_correct.
Qed.

Corollary greedy_simplify_preserves_head :
  forall eps pts default,
    hd default pts = hd default (greedy_simplify eps pts).
Proof.
  intros eps pts d.
  apply simp_star_preserves_head with (eps := eps).
  apply greedy_simplify_correct.
Qed.

Corollary greedy_simplify_preserves_last :
  forall eps pts default,
    last pts default = last (greedy_simplify eps pts) default.
Proof.
  intros eps pts d.
  apply simp_star_preserves_last with (eps := eps).
  apply greedy_simplify_correct.
Qed.

Corollary greedy_simplify_perp_length_monotone :
  forall eps pts,
    polyline_length (greedy_simplify_perp eps pts) <= polyline_length pts.
Proof.
  intros eps pts.
  apply simp_star_perp_length_monotone with (eps := eps).
  apply greedy_simplify_perp_correct.
Qed.

Corollary greedy_simplify_perp_preserves_head :
  forall eps pts default,
    hd default pts = hd default (greedy_simplify_perp eps pts).
Proof.
  intros eps pts d.
  apply simp_star_perp_preserves_head with (eps := eps).
  apply greedy_simplify_perp_correct.
Qed.

Corollary greedy_simplify_perp_preserves_last :
  forall eps pts default,
    last pts default = last (greedy_simplify_perp eps pts) default.
Proof.
  intros eps pts d.
  apply simp_star_perp_preserves_last with (eps := eps).
  apply greedy_simplify_perp_correct.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                              *)
(* -------------------------------------------------------------------------- *)

Print Assumptions greedy_simplify_correct.
Print Assumptions greedy_simplify_perp_correct.
Print Assumptions greedy_simplify_length_monotone.
Print Assumptions greedy_simplify_perp_length_monotone.
