(* ============================================================================
   NetTopologySuite.Proofs.EllipseBagIntake
   ----------------------------------------------------------------------------
   ADR-0007: host MkEllipse and the rho bag loop (claimId: none; packaging
   for claimId 0007-ellipse-first-cook). NTS has no elliptic arc type.

   try_cook_hit is the pairwise cook step. It mints MkEllipse children
   (EllipseCookMkEllipse). The bag loop is a different machine: it never
   calls try_cook_hit, and its supports are chord or circle only.
     ellipse_declined_at_intake: bag_intake answers BagIntakeDecline on
       MkEllipse, explicitly, for every support.
     realizing_not_ellipse: no piece that realizes its support carries
       MkEllipse, so no piece of a bag under bag_inv does.
     split_piece_ellipse_unreachable: split_piece's fall-through arm
       (pc, pc) is therefore never taken on an ellipse inside the loop.
   So minted MkEllipse children live in the pairwise step only. Nothing
   in the loop drops or duplicates one. Loop support for ellipses is
   not claimed.
   3-axiom host. No Admitted, no stub declaration.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List.
From NTS.Proofs Require Import Distance SheetHenCook SheetHenBag.
Local Open Scope R_scope.

Lemma ellipse_declined_at_intake :
  forall ck e sup w prov,
    ck_egg ck = MkEllipse e -> bag_intake ck sup w prov = BagIntakeDecline.
Proof.
  intros [src dst egg] e sup w prov He.
  simpl in He. subst egg. destruct sup; reflexivity.
Qed.

Lemma realizing_not_ellipse :
  forall pc e, piece_realizes pc -> ck_egg (bp_ck pc) <> MkEllipse e.
Proof.
  intros [[src dst egg] sup w prov] e Hr.
  destruct sup; destruct egg; simpl in Hr; try contradiction; discriminate.
Qed.

Lemma bag_inv_no_ellipse :
  forall sh pcs pc e,
    bag_inv (BagLive sh pcs) -> In pc pcs -> ck_egg (bp_ck pc) <> MkEllipse e.
Proof.
  intros sh pcs pc e Hinv Hin.
  apply realizing_not_ellipse. exact (proj1 (Hinv pc Hin)).
Qed.

Lemma split_piece_ellipse_unreachable :
  forall pc u h e,
    piece_realizes pc ->
    ck_egg (bp_ck (fst (split_piece pc u h))) <> MkEllipse e /\
    ck_egg (bp_ck (snd (split_piece pc u h))) <> MkEllipse e.
Proof.
  intros [[src dst egg] sup w prov] u h e Hr.
  destruct sup; destruct egg; simpl in Hr; try contradiction;
    simpl; split; discriminate.
Qed.

Print Assumptions ellipse_declined_at_intake.
Print Assumptions realizing_not_ellipse.
Print Assumptions bag_inv_no_ellipse.
Print Assumptions split_piece_ellipse_unreachable.
