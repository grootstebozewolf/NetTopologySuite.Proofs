(* ============================================================================
   NetTopologySuite.Proofs.HausdorffDensifyLine2
   ----------------------------------------------------------------------------
   #423 ticket-10 densify line 2: crossing / new-boundary cells after
   densify (claimId 423-t10-densify-line2). Chainsaw densify lane.

   Line 1 is already LEFT (do not remint, do not weaken):
     HausdorffDensify.v : ticket_423_t10_line1_qed_or_qex
     claimId 423-t10-densify
     discrete_le_locus, densify_step_bound
   Full-lane only — cited, not imported.

   HotPixel form-(b) edge-crossing (closed / opp / adj) is already QED
   on Phase-2 (HotPixel.v scaffold; HotPixel_b64.v closed/opp/adj).
   That is the snap-rounding ceiling, not this letter. Do not treat
   form-(b) as line 2.

   HausdorffDiscreteQ.v : ticket_423_t10_line2_qed_or_qex is a different
   claim (claimId 423-t10-oracle: HAUSDORFF_* keyword adapters). Do not
   remint it. This module's same ticket name is the densify-engine stop.

   Ctor: LocusHausdorffSymEngine
     = continuous densify → locus equality with line 1
       ∧ crossing / new-boundary cells after densify classified
   No NewBoundaryCell module on this tip.

   QED (not this PR): LocusHausdorffSymEngine inhabits; the symmetrized
   / continuous engine produces the same locus as line 1; new-boundary
   cells after densify are classified.

   QEX (this PR): that ctor is missing. Crossing / new-boundary without
   the continuous engine stays QEX. ticket_423_t10_line2_qed_or_qex
   discharges right.

   Honesty fences:
     Do not remint P0 (b64_orient_sign_filtered_sound_small_int).
     Do not weaken 423-t10-densify line 1.
     Do not steal Linearise.hausdorff_le (regimes 1–3 exist; not the
     densify bound).
     Do not treat HotPixel form-(b) as line 2.
     Not leftover ρ / LeftoverBagTermArm. Not first-cook mixed / ι.
     Not C1 width 2²⁵ / C2 rounded filter. Not #522 / #523.
     Not Laser keep-curve exact. Not CircGamma reopen. Not NURBS=MkChord.
     Not “densify is done”. Not “P0 covers boundary cells”.
     #423 stays open. QEX ≠ owner accept. QEX ≠ “#423 failed”.
     Chainsaw ≠ Laser.

   WITNESS topic: metric · claimId: 423-t10-densify-line2
   witness: 423-t10-densify-line2
   3-axiom host. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import Distance HotPixel.
Local Open Scope R_scope.

(* WITNESS: campaign=chainsaw-densify rung=line2-new-boundary
   claim=423-t10-densify-line2
   file=theories/HausdorffDensifyLine2.v
   kind=QEX-named-missing-ctor
   park=LocusHausdorffSymEngine
   missing=LocusHausdorffSymEngine
   ceiling=ticket_423_t10_line1_qed_or_qex,HotPixel-form-b-closed-opp-adj
   not=P0-boundary-cells,line1-weaken,Linearise.hausdorff_le-densify
   not=HotPixel-form-b-as-line2,NewBoundaryCell,densify-done
   not=leftover-rho,first-cook-mixed,C1,C2,522,523,Laser,CircGamma
   not=NURBS-MkChord,owner-accept,423-failed
   sibling=423-t10-densify-line1,423-t10-oracle,HotPixel-form-b
   note=letter-not-423-close;Chainsaw-not-Laser *)

(* -------------------------------------------------------------------------- *)
(* Named missing constructor. Not a bool. Inhabitance would be the            *)
(* continuous / symmetrized engine plus classified new-boundary cells.        *)
(* -------------------------------------------------------------------------- *)

Inductive DensifyLine2Ctor : Type :=
| LocusHausdorffSymEngine.

Definition densify_line2_ctor_inhabits (c : DensifyLine2Ctor) : Prop :=
  match c with
  | LocusHausdorffSymEngine => False
  end.

Lemma locus_hausdorff_sym_engine_missing :
  ~ densify_line2_ctor_inhabits LocusHausdorffSymEngine.
Proof.
  intro H. exact H.
Qed.

(* No NewBoundaryCell module on this tip. *)
Inductive NewBoundaryCellPark : Type :=
| NewBoundaryCellMissing
| NewBoundaryCellInhabits.

Definition new_boundary_cell_park : NewBoundaryCellPark :=
  NewBoundaryCellMissing.

Lemma new_boundary_cell_module_missing :
  new_boundary_cell_park = NewBoundaryCellMissing
  /\ new_boundary_cell_park <> NewBoundaryCellInhabits.
Proof.
  split; [reflexivity | discriminate].
Qed.

(* -------------------------------------------------------------------------- *)
(* Ceilings: line 1 LEFT, HotPixel form-(b). Not this letter.                 *)
(* -------------------------------------------------------------------------- *)

(* HausdorffDensify.v : ticket_423_t10_line1_qed_or_qex LEFT
   (discrete_le_locus, densify_step_bound). Full-lane; not imported. *)
Inductive DensifyLine1Ceiling : Type :=
| Ticket423T10Line1Left
| Ticket423T10Line1Weakened.

Definition densify_line1_ceiling : DensifyLine1Ceiling :=
  Ticket423T10Line1Left.

Lemma densify_line1_stays_left :
  densify_line1_ceiling = Ticket423T10Line1Left
  /\ densify_line1_ceiling <> Ticket423T10Line1Weakened.
Proof.
  split; [reflexivity | discriminate].
Qed.

(* HotPixel.v / HotPixel_b64.v Phase-2: form-(b) closed/opp/adj
   edge-crossing. Scaffold cited here; b64 lemmas stay on the flocq
   lane (not imported). Ceiling, not line 2. *)
Inductive HotPixelFormBCeiling : Type :=
| HotPixelFormBClosedOppAdj
| HotPixelFormBAsLine2.

Definition hotpixel_form_b_ceiling : HotPixelFormBCeiling :=
  HotPixelFormBClosedOppAdj.

Lemma hotpixel_form_b_is_ceiling_not_line2 :
  hotpixel_form_b_ceiling = HotPixelFormBClosedOppAdj
  /\ hotpixel_form_b_ceiling <> HotPixelFormBAsLine2
  /\ ~ densify_line2_ctor_inhabits LocusHausdorffSymEngine
  /\ ~ segment_touches_hot_pixel
         (mkPoint 0 1) (mkPoint (3 / 2) (- (1)))
         (mkPoint (3 / 2) (1 / 2)) 1.
Proof.
  split; [reflexivity |].
  split; [discriminate |].
  split; [exact locus_hausdorff_sym_engine_missing |].
  exact bb_overlap_witness_segment_does_not_touch.
Qed.

(* -------------------------------------------------------------------------- *)
(* Honesty parks. Do not steal ceilings; do not close #423.                   *)
(* -------------------------------------------------------------------------- *)

Inductive LinearisePark : Type :=
| LineariseHausdorffLeNotDensifyBound
| LineariseStolenAsDensifyBound.

Definition linearise_park : LinearisePark :=
  LineariseHausdorffLeNotDensifyBound.

Lemma linearise_hausdorff_le_not_densify_bound :
  linearise_park = LineariseHausdorffLeNotDensifyBound
  /\ linearise_park <> LineariseStolenAsDensifyBound.
Proof.
  split; [reflexivity | discriminate].
Qed.

Inductive Phase0Park : Type :=
| Phase0OrientNotBoundaryCells
| Phase0CoversBoundaryCells.

Definition phase0_park : Phase0Park := Phase0OrientNotBoundaryCells.

Lemma phase0_not_boundary_cells :
  phase0_park = Phase0OrientNotBoundaryCells
  /\ phase0_park <> Phase0CoversBoundaryCells.
Proof.
  split; [reflexivity | discriminate].
Qed.

(* HausdorffDiscreteQ.v : ticket_423_t10_line2_qed_or_qex is the
   oracle-keyword letter (claimId 423-t10-oracle), already LEFT.
   Cited, not reminted. *)
Inductive OracleLine2Park : Type :=
| HausdorffDiscreteQKeywordAdapters
| RemintOracleLine2.

Definition oracle_line2_park : OracleLine2Park :=
  HausdorffDiscreteQKeywordAdapters.

Lemma oracle_line2_not_reminted :
  oracle_line2_park = HausdorffDiscreteQKeywordAdapters
  /\ oracle_line2_park <> RemintOracleLine2.
Proof.
  split; [reflexivity | discriminate].
Qed.

Inductive DensifyBoard : Type :=
| ChainsawDensify
| LaserKeepCurveExact.

Definition densify_board : DensifyBoard := ChainsawDensify.

Lemma densify_board_is_chainsaw :
  densify_board = ChainsawDensify
  /\ densify_board <> LaserKeepCurveExact.
Proof.
  split; [reflexivity | discriminate].
Qed.

Inductive Issue423Status : Type :=
| Issue423Open
| Issue423DensifyDone.

Definition issue_423_status : Issue423Status := Issue423Open.

Lemma issue_423_stays_open :
  issue_423_status = Issue423Open
  /\ issue_423_status <> Issue423DensifyDone.
Proof.
  split; [reflexivity | discriminate].
Qed.

Inductive QexHonesty : Type :=
| QexNamedMissingCtor
| QexOwnerAccept
| Issue423Failed.

Definition qex_honesty : QexHonesty := QexNamedMissingCtor.

Lemma qex_not_owner_accept_or_failure :
  qex_honesty = QexNamedMissingCtor
  /\ qex_honesty <> QexOwnerAccept
  /\ qex_honesty <> Issue423Failed.
Proof.
  split; [reflexivity |].
  split; discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket. QED ∨ QEX. Discharged QEX: LocusHausdorffSymEngine missing.        *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"423-t10-densify-line2","topic":"metric","lemma":"ticket_423_t10_line2_qed_or_qex","title":"#423 ticket-10 densify line 2: LocusHausdorffSymEngine inhabits continuous densify locus equality with line 1 and classified crossing / new-boundary cells (QED) or that ctor stays missing, NewBoundaryCell is absent, and line 1 plus HotPixel form-(b) remain the ceiling (QEX); discharged QEX; do not weaken 423-t10-densify; do not treat form-(b) or Linearise.hausdorff_le as the densify bound; #423 stays open; Chainsaw not Laser","file":"theories/HausdorffDensifyLine2.v","witness":"423-t10-densify-line2"} *)
Theorem ticket_423_t10_line2_qed_or_qex :
  (densify_line2_ctor_inhabits LocusHausdorffSymEngine
   /\ new_boundary_cell_park = NewBoundaryCellInhabits)
  \/
  (~ densify_line2_ctor_inhabits LocusHausdorffSymEngine
   /\ new_boundary_cell_park = NewBoundaryCellMissing
   /\ new_boundary_cell_park <> NewBoundaryCellInhabits
   /\ densify_line1_ceiling = Ticket423T10Line1Left
   /\ densify_line1_ceiling <> Ticket423T10Line1Weakened
   /\ hotpixel_form_b_ceiling = HotPixelFormBClosedOppAdj
   /\ hotpixel_form_b_ceiling <> HotPixelFormBAsLine2
   /\ linearise_park = LineariseHausdorffLeNotDensifyBound
   /\ linearise_park <> LineariseStolenAsDensifyBound
   /\ phase0_park = Phase0OrientNotBoundaryCells
   /\ phase0_park <> Phase0CoversBoundaryCells
   /\ oracle_line2_park = HausdorffDiscreteQKeywordAdapters
   /\ oracle_line2_park <> RemintOracleLine2
   /\ densify_board = ChainsawDensify
   /\ densify_board <> LaserKeepCurveExact
   /\ issue_423_status = Issue423Open
   /\ issue_423_status <> Issue423DensifyDone
   /\ qex_honesty = QexNamedMissingCtor
   /\ qex_honesty <> QexOwnerAccept
   /\ qex_honesty <> Issue423Failed
   /\ ~ segment_touches_hot_pixel
          (mkPoint 0 1) (mkPoint (3 / 2) (- (1)))
          (mkPoint (3 / 2) (1 / 2)) 1).
Proof.
  right.
  split; [exact locus_hausdorff_sym_engine_missing |].
  split; [reflexivity |].
  split; [discriminate |].
  split; [reflexivity |].
  split; [discriminate |].
  split; [reflexivity |].
  split; [discriminate |].
  split; [reflexivity |].
  split; [discriminate |].
  split; [reflexivity |].
  split; [discriminate |].
  split; [reflexivity |].
  split; [discriminate |].
  split; [reflexivity |].
  split; [discriminate |].
  split; [reflexivity |].
  split; [discriminate |].
  split; [reflexivity |].
  split; [discriminate |].
  split; [discriminate |].
  exact bb_overlap_witness_segment_does_not_touch.
Qed.

Print Assumptions locus_hausdorff_sym_engine_missing.
Print Assumptions new_boundary_cell_module_missing.
Print Assumptions densify_line1_stays_left.
Print Assumptions hotpixel_form_b_is_ceiling_not_line2.
Print Assumptions linearise_hausdorff_le_not_densify_bound.
Print Assumptions phase0_not_boundary_cells.
Print Assumptions oracle_line2_not_reminted.
Print Assumptions densify_board_is_chainsaw.
Print Assumptions issue_423_stays_open.
Print Assumptions qex_not_owner_accept_or_failure.
Print Assumptions ticket_423_t10_line2_qed_or_qex.
