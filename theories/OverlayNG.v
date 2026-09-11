(* ============================================================================
   NetTopologySuite.Proofs.OverlayNG
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: OverlayNG sheet lane
   (claimId 0007-overlayng-sheet).

   Product face: OverlayNG = a finite snap-sequence on one sheet.
   Accepted ADR-0007 OverlayNGRobust is snap maps S → Λ attempted
   until validate or give up, sitting on the same sheet as ℝ
   realization, under the Hobby-shaped assumption that G was
   already noded. This module packages SheetHenCook inhabitance —
   it is not a remint of that vocabulary, not 𝓘, not cook, not
   NodingNG, not OverlayNGCurve Phase-0 point-set algebra (G1–G5),
   not RelateNG, not Shewchuk A–D, not Hobby 4.1 Discharge, not
   Jordan, not a DCEL kernel, and not a Geometry subclass.

   QED: named OverlayNG sheet inhabitant — finite snap-sequence
   ≠ 𝓘, same-sheet realization, Hobby-shaped already-noded G
   (SheetHenCook.noded_crossing; NodingNG #712 / NodingNG.v when
   present). Failure to validate is not 𝓘 Decline and not Empty.

   QEX: full Hobby 4.1 “image stays noded” / unconditional overlay
   correctness stays Honest remaining. Named missing constructor,
   not a bool. Do not fake Hobby 4.1 Discharge.

   Parks Γ / ι / ρ (named QEX, landed). This letter cites them
   once; it does not remint CircGamma, ι, leftover_width, or
   LoopDischarged. First cook stays chord–chord. Host CircGamma
   stays QEX. No H⊥ / Multi Landed / Phase B done-when / SQL/MM
   cathedral / MerkatorBV / 522-n.

   ADR-0007 is Accepted (2026-09-07). This letter does not reopen
   Status. QEX is not a new Accept cycle.

   Testable 𝓘 / cook results sit on the accepted Oracle line
   protocol (ADR-0006). This module mints no keyword and no
   second external seam. OverlayNG is not 𝓘.

   WITNESS topic: overlay · claimId: 0007-overlayng-sheet
   witness: 0007-overlayng-sheet
   board: ADR-0007
   3-axiom host. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From NTS.Proofs Require Import SheetHenCook.

(* -------------------------------------------------------------------------- *)
(* Product face: an OverlayNG sheet run is a finite snap-sequence on one      *)
(* sheet, under already-noded G. Not 𝓘. Not a cook.                           *)
(* -------------------------------------------------------------------------- *)

Record OverlayNGSheetRun : Type := mkOngSheetRun {
  ong_run_sheet : Sheet;
  ong_run_g : NodedOnSheet;
  ong_run_bound : nat
}.

(* Locked inhabitant: Hobby-shaped G is SheetHenCook.noded_crossing
   (NodingNG #712 / NodingNG.v when that letter is present). *)
Definition overlayng_locked_run : OverlayNGSheetRun :=
  mkOngSheetRun default_sheet noded_crossing 0.

Lemma overlayng_locked_run_g_on_sheet :
  noded_sheet (ong_run_g overlayng_locked_run) = ong_run_sheet overlayng_locked_run.
Proof.
  reflexivity.
Qed.

Lemma overlayng_assumes_noded_crossing :
  ong_run_g overlayng_locked_run = noded_crossing /\
  noded_sheet (ong_run_g overlayng_locked_run) = default_sheet.
Proof.
  split; reflexivity.
Qed.

(* Each attempt is CtorSnapRound on the run's sheet. *)
Definition overlayng_run_is_finite_snap (r : OverlayNGSheetRun) : Prop :=
  overlay_ng_robust_is_finite_snap (ong_run_sheet r) (ong_run_bound r).

Lemma overlayng_locked_run_is_finite_snap :
  overlayng_run_is_finite_snap overlayng_locked_run.
Proof.
  exact (overlay_ng_robust_is_finite_snap_holds
           (ong_run_sheet overlayng_locked_run)
           (ong_run_bound overlayng_locked_run)).
Qed.

Lemma overlayng_is_finite_snap :
  forall s n, overlay_ng_robust_is_finite_snap s n.
Proof.
  exact overlay_ng_robust_is_finite_snap_holds.
Qed.

Lemma overlayng_attempt_is_snap :
  forall s i,
    ong_snap_kind (overlay_ng_robust_attempt s i) = CtorSnapRound.
Proof.
  exact overlay_ng_robust_attempt_is_snap.
Qed.

Lemma overlayng_attempt_not_I :
  forall s i,
    ong_snap_kind (overlay_ng_robust_attempt s i) <> CtorI.
Proof.
  exact overlay_ng_robust_attempt_not_I.
Qed.

Lemma overlayng_attempt_same_sheet :
  forall s i, ong_on (overlay_ng_robust_attempt s i) = s.
Proof.
  exact overlay_ng_robust_attempt_same_sheet.
Qed.

(* -------------------------------------------------------------------------- *)
(* Reused SheetHenCook laws: snap ≠ 𝓘; binary64 realizes the same sheet.      *)
(* -------------------------------------------------------------------------- *)

Lemma overlayng_snap_neq_I : CtorSnapRound <> CtorI.
Proof.
  exact snap_round_neq_I.
Qed.

Lemma overlayng_is_snap_not_I : CtorSnapRound <> CtorI.
Proof.
  exact overlay_ng_robust_is_snap_not_I.
Qed.

Lemma overlayng_coord_preserves_sheet :
  forall (s : Sheet) (n1 n2 : CoordRealization),
    realiz_sheet (mkSheetRealization s n1) =
    realiz_sheet (mkSheetRealization s n2).
Proof.
  exact coord_realization_preserves_sheet.
Qed.

Lemma overlayng_same_sheet_as_R :
  forall s : Sheet,
    realiz_sheet (mkSheetRealization s RealizeBinary64) =
    realiz_sheet (mkSheetRealization s RealizeR).
Proof.
  exact binary64_same_sheet_as_R.
Qed.

(* -------------------------------------------------------------------------- *)
(* What OverlayNG is / is not. Kind tag, not a second kernel.                 *)
(* -------------------------------------------------------------------------- *)

Inductive OverlayNGKind : Type :=
| ONG_SnapSequence
| ONG_I_plus_cook
| ONG_OverlayNGCurve
| ONG_RelateNG
| ONG_Shewchuk
| ONG_Hobby41Discharge
| ONG_Jordan
| ONG_DCEL.

Definition overlayng_kind : OverlayNGKind := ONG_SnapSequence.

Lemma overlayng_is_snap_sequence : overlayng_kind = ONG_SnapSequence.
Proof.
  reflexivity.
Qed.

Lemma overlayng_not_nodingng : overlayng_kind <> ONG_I_plus_cook.
Proof.
  discriminate.
Qed.

Lemma overlayng_not_overlayngcurve : overlayng_kind <> ONG_OverlayNGCurve.
Proof.
  discriminate.
Qed.

Lemma overlayng_not_relateng : overlayng_kind <> ONG_RelateNG.
Proof.
  discriminate.
Qed.

Lemma overlayng_not_shewchuk : overlayng_kind <> ONG_Shewchuk.
Proof.
  discriminate.
Qed.

Lemma overlayng_not_hobby41_discharge : overlayng_kind <> ONG_Hobby41Discharge.
Proof.
  discriminate.
Qed.

Lemma overlayng_not_jordan : overlayng_kind <> ONG_Jordan.
Proof.
  discriminate.
Qed.

Lemma overlayng_not_dcel : overlayng_kind <> ONG_DCEL.
Proof.
  discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* Hobby 4.1 / unconditional overlay correctness — named QEX park.            *)
(* Honest remaining. Do not fake Discharge.                                   *)
(* -------------------------------------------------------------------------- *)

Inductive OverlayNGHobbyCtor : Type :=
| Hobby41ImageStaysNoded
| OverlayUnconditionalCorrect.

Definition overlayng_hobby_inhabits (c : OverlayNGHobbyCtor) : Prop :=
  match c with
  | Hobby41ImageStaysNoded => False
  | OverlayUnconditionalCorrect => False
  end.

Lemma overlayng_hobby41_missing :
  ~ overlayng_hobby_inhabits Hobby41ImageStaysNoded.
Proof.
  intro H. exact H.
Qed.

Lemma overlayng_unconditional_missing :
  ~ overlayng_hobby_inhabits OverlayUnconditionalCorrect.
Proof.
  intro H. exact H.
Qed.

Inductive OverlayNGLetterStatus : Type :=
| OverlayNGSheetLanded
| OverlayNGHobby41Discharged.

Definition overlayng_letter_status : OverlayNGLetterStatus :=
  OverlayNGSheetLanded.

Lemma overlayng_letter_is_landed :
  overlayng_letter_status = OverlayNGSheetLanded /\
  overlayng_letter_status <> OverlayNGHobby41Discharged /\
  ~ overlayng_hobby_inhabits Hobby41ImageStaysNoded /\
  ~ overlayng_hobby_inhabits OverlayUnconditionalCorrect.
Proof.
  split; [reflexivity|].
  split; [discriminate|].
  split; [exact overlayng_hobby41_missing|].
  exact overlayng_unconditional_missing.
Qed.

(* Named QED package: finite snap-sequence ≠ 𝓘, same-sheet realization. *)
Lemma overlayng_sheet_inhabits :
  (forall s n, overlay_ng_robust_is_finite_snap s n) /\
  CtorSnapRound <> CtorI /\
  (forall (s : Sheet) (n1 n2 : CoordRealization),
     realiz_sheet (mkSheetRealization s n1) =
     realiz_sheet (mkSheetRealization s n2)) /\
  (forall s : Sheet,
     realiz_sheet (mkSheetRealization s RealizeBinary64) =
     realiz_sheet (mkSheetRealization s RealizeR)) /\
  overlayng_kind = ONG_SnapSequence /\
  overlayng_kind <> ONG_I_plus_cook /\
  overlayng_kind <> ONG_OverlayNGCurve /\
  overlayng_kind <> ONG_RelateNG /\
  overlayng_kind <> ONG_Shewchuk /\
  overlayng_kind <> ONG_Jordan /\
  overlayng_kind <> ONG_DCEL /\
  overlayng_run_is_finite_snap overlayng_locked_run.
Proof.
  split; [exact overlayng_is_finite_snap|].
  split; [exact overlayng_snap_neq_I|].
  split; [exact overlayng_coord_preserves_sheet|].
  split; [exact overlayng_same_sheet_as_R|].
  split; [exact overlayng_is_snap_sequence|].
  split; [exact overlayng_not_nodingng|].
  split; [exact overlayng_not_overlayngcurve|].
  split; [exact overlayng_not_relateng|].
  split; [exact overlayng_not_shewchuk|].
  split; [exact overlayng_not_jordan|].
  split; [exact overlayng_not_dcel|].
  exact overlayng_locked_run_is_finite_snap.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-overlayng-sheet","topic":"overlay","lemma":"ticket_0007_overlayng_sheet_qed_or_qex","title":"OverlayNG sheet is a finite snap-sequence not I on the same sheet as R realization (QED) or snap equals I (QEX); discharged QED; not NodingNG / OverlayNGCurve / RelateNG / Shewchuk / Jordan / DCEL","file":"theories/OverlayNG.v","witness":"0007-overlayng-sheet","board":"ADR-0007"} *)
Theorem ticket_0007_overlayng_sheet_qed_or_qex :
  ((forall s n, overlay_ng_robust_is_finite_snap s n) /\
   CtorSnapRound <> CtorI /\
   (forall (s : Sheet) (n1 n2 : CoordRealization),
      realiz_sheet (mkSheetRealization s n1) =
      realiz_sheet (mkSheetRealization s n2)) /\
   (forall s : Sheet,
      realiz_sheet (mkSheetRealization s RealizeBinary64) =
      realiz_sheet (mkSheetRealization s RealizeR)) /\
   overlayng_kind = ONG_SnapSequence /\
   overlayng_kind <> ONG_I_plus_cook /\
   overlayng_kind <> ONG_OverlayNGCurve /\
   overlayng_kind <> ONG_RelateNG /\
   overlayng_kind <> ONG_Shewchuk /\
   overlayng_kind <> ONG_Jordan /\
   overlayng_kind <> ONG_DCEL /\
   overlayng_run_is_finite_snap overlayng_locked_run)
  \/
  CtorSnapRound = CtorI.
Proof.
  left.
  exact overlayng_sheet_inhabits.
Qed.

(* OverlayNG assumes already-noded G (noded_crossing; NodingNG #712
   when present). It does not cook and does not mint 𝓘. *)
(* WITNESS {"claimId":"0007-overlayng-sheet","topic":"overlay","lemma":"ticket_0007_overlayng_assumes_noded_qed_or_qex","title":"OverlayNG sheet assumes already-noded G on the same sheet (QED) or the locked run leaves noded_crossing (QEX); discharged QED; Hobby-shaped; not I plus cook","file":"theories/OverlayNG.v","witness":"0007-overlayng-sheet","board":"ADR-0007"} *)
Theorem ticket_0007_overlayng_assumes_noded_qed_or_qex :
  (ong_run_g overlayng_locked_run = noded_crossing /\
   noded_sheet (ong_run_g overlayng_locked_run) = ong_run_sheet overlayng_locked_run /\
   noded_sheet (ong_run_g overlayng_locked_run) = default_sheet /\
   overlayng_kind = ONG_SnapSequence /\
   overlayng_kind <> ONG_I_plus_cook)
  \/
  ong_run_g overlayng_locked_run <> noded_crossing.
Proof.
  left.
  split; [reflexivity|].
  split; [exact overlayng_locked_run_g_on_sheet|].
  split; [reflexivity|].
  split; [exact overlayng_is_snap_sequence|].
  exact overlayng_not_nodingng.
Qed.

(* Hobby 4.1 “image stays noded” / unconditional overlay correctness
   stay Honest remaining. Named QEX. Do not fake Discharge. *)
(* WITNESS {"claimId":"0007-overlayng-sheet","topic":"overlay","lemma":"ticket_0007_overlayng_hobby41_qed_or_qex","title":"OverlayNG sheet discharges Hobby 4.1 image-stays-noded and unconditional overlay correctness (QED) or parks them as Honest remaining named missing constructors (QEX); discharged QEX; not Hobby 4.1 Discharge theater","file":"theories/OverlayNG.v","witness":"0007-overlayng-sheet","board":"ADR-0007"} *)
Theorem ticket_0007_overlayng_hobby41_qed_or_qex :
  (overlayng_letter_status = OverlayNGHobby41Discharged
   /\ overlayng_hobby_inhabits Hobby41ImageStaysNoded
   /\ overlayng_hobby_inhabits OverlayUnconditionalCorrect)
  \/
  (overlayng_letter_status = OverlayNGSheetLanded
   /\ ~ overlayng_hobby_inhabits Hobby41ImageStaysNoded
   /\ ~ overlayng_hobby_inhabits OverlayUnconditionalCorrect
   /\ overlayng_kind = ONG_SnapSequence
   /\ overlayng_kind <> ONG_Hobby41Discharge).
Proof.
  right.
  split; [reflexivity|].
  split; [exact overlayng_hobby41_missing|].
  split; [exact overlayng_unconditional_missing|].
  split; [exact overlayng_is_snap_sequence|].
  exact overlayng_not_hobby41_discharge.
Qed.

Print Assumptions overlayng_is_finite_snap.
Print Assumptions overlayng_snap_neq_I.
Print Assumptions overlayng_same_sheet_as_R.
Print Assumptions overlayng_locked_run_is_finite_snap.
Print Assumptions overlayng_assumes_noded_crossing.
Print Assumptions overlayng_sheet_inhabits.
Print Assumptions overlayng_hobby41_missing.
Print Assumptions ticket_0007_overlayng_sheet_qed_or_qex.
Print Assumptions ticket_0007_overlayng_assumes_noded_qed_or_qex.
Print Assumptions ticket_0007_overlayng_hobby41_qed_or_qex.
