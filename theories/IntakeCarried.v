(* ============================================================================
   NetTopologySuite.Proofs.IntakeCarried
   ----------------------------------------------------------------------------
   GML / LandXML carried θ₀/Δθ, accepted only by try_carried.
   Not a CST carrier (#866b stays QEX). Three-point arcs only.
   Not on the WKT path (IntakeWalker.map_cs_unknown).

   claimId: none (packaging of 0007-intake-angles). No new witness.
   3-axiom host. No Admitted / Axiom / Parameter.
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals List.
From NTS.Proofs Require Import Distance SheetHenCook IntakeAngles IntakeWalker.
Import ListNotations.
Local Open Scope R_scope.
Local Open Scope list_scope.

Definition map_cs_carried (s : Sheet) (pts : list Point) (th dth : R)
  : IntakeResult :=
  match pts with
  | [a; m; b] =>
      match try_carried a m b th dth with
      | inr f => IntakeDecline (angle_fail_reason f)
      | inl e => IntakeBag (map_cs_from_build s [e] [a; b])
      end
  | _ => IntakeDecline ID_BadPointCount
  end.

Lemma map_cs_carried_bag : forall s a m b th dth e,
  try_carried a m b th dth = inl e ->
  map_cs_carried s [a; m; b] th dth =
    IntakeBag (map_cs_from_build s [e] [a; b]).
Proof.
  intros s a m b th dth e H.
  unfold map_cs_carried. rewrite H. reflexivity.
Qed.

Print Assumptions map_cs_carried_bag.
