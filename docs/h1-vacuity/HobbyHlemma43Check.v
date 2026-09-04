(* ============================================================================
   NetTopologySuite.Proofs.H1Vacuity.HobbyHlemma43Check
   ----------------------------------------------------------------------------
   Hunt probe: the *anonymous second premise* of
   hobby_theorem_4_1_conditional is uninhabitable.  Same parallel-collapse
   pair as HobbyCounterexample_b64.  Evidence, not a product headline.

   Target behaviour: snap-rounding of a fully_intersected arrangement
   stays fully_intersected (Hobby 1999, Theorem 4.1).

   Hlemma43 is house slang from docs/hobby-lemma-4-3-no-proper-refutation.md.
   It is NOT a Hypothesis / ident in HobbyTheorem_b64.v.  The Definition
   below reconstructs the second arrow of hobby_theorem_4_1_conditional.

   Qed-only; no axioms, no parameters.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance.
From NTS.Proofs.Flocq Require Import HotPixel_b64 HobbyTheorem_b64
                               HobbyCounterexample_b64.
Import ListNotations.
Local Open Scope R_scope.

(* Probe alias for the anonymous second premise of
   hobby_theorem_4_1_conditional, copied verbatim.  Not a kernel binder. *)
Definition Hlemma43 : Prop :=
  forall s1 s2 : Point * Point,
    segments_intersect_only_at_endpoints s1 s2 ->
    forall sigma1 sigma2 : Point * Point,
      In sigma1 (snap_round_segments [s1]) ->
      In sigma2 (snap_round_segments [s2]) ->
      sigma1 <> sigma2 ->
      segments_intersect_only_at_endpoints sigma1 sigma2.

(* B: the second premise's antecedent is inhabited — ~proper suffices. *)
Theorem collapse_pair_only_at_endpoints :
  segments_intersect_only_at_endpoints (A0, A1) (B0, B1).
Proof. unfold segments_intersect_only_at_endpoints. left. exact originals_no_proper. Qed.

(* A: that reconstructed second premise derives False. *)
Theorem Hlemma43_uninhabitable : Hlemma43 -> False.
Proof.
  intros H.
  assert (HinA : In (snap_round A0 1, snap_round A1 1) (snap_round_segments [(A0, A1)]))
    by (unfold snap_round_segments; simpl; left; reflexivity).
  assert (HinB : In (snap_round B0 1, snap_round B1 1) (snap_round_segments [(B0, B1)]))
    by (unfold snap_round_segments; simpl; left; reflexivity).
  assert (Hne : (snap_round A0 1, snap_round A1 1) <> (snap_round B0 1, snap_round B1 1)).
  { rewrite snap_A0, snap_A1, snap_B0, snap_B1. intro E.
    assert (px (snd (mkPoint 0 1, mkPoint 10 1)) = px (snd (mkPoint 3 1, mkPoint 7 1)))
      by (rewrite E; reflexivity). cbn in *. lra. }
  pose proof (H (A0, A1) (B0, B1) collapse_pair_only_at_endpoints
                (snap_round A0 1, snap_round A1 1) (snap_round B0 1, snap_round B1 1)
                HinA HinB Hne) as Honly.
  unfold segments_intersect_only_at_endpoints in Honly.
  destruct Honly as [Hnp | Hshare].
  - exact (Hnp snapped_proper).
  - rewrite snap_A0, snap_A1, snap_B0, snap_B1 in Hshare.
    destruct Hshare as [E | [E | [E | E]]];
      apply (f_equal px) in E; cbn in E; lra.
Qed.

Print Assumptions Hlemma43_uninhabitable.
Print Assumptions collapse_pair_only_at_endpoints.
