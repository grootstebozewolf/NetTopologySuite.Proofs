(* ============================================================================
   NetTopologySuite.Proofs.IntakeSpiralJtsMap
   ----------------------------------------------------------------------------
   Walker face of SPIRALCURVE intake and the JTS decline taxonomy
   (claimId 0007-intake-spiral, witness 0007-intake-spiral).
   Not a remint of 0007-intake-mkclothoid.

   QED: clothoid SPIRALCURVE reuses map_clothoid; a non-locked
   ISO payload bags a non-locked MkClothoid egg; every
   SpiralOther declines ID_SpiralOther; JTS L <= 0 declines
   ID_JtsNonPositiveLength before the example5 test; any other
   positive triple declines ID_JtsClothoidNotYet; example5
   still bags locked_clothoid_egg. MemberState projects.

   QEX: parse ∘ emit = id, the compound member-state fold,
   and JTS G1. Named missing constructors. Not inhabited.

   ADR-0005: lenient intake, not isValid. 3-axiom host.
   No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals List.
From NTS.Proofs Require Import SheetHenCook IntakeWalker IntakeSpiralJts
  IsoClothoidIntake IsoClothoidIntakeMap IntakeWalkerClothoid.
Import ListNotations.
Local Open Scope R_scope.
Local Open Scope list_scope.

Lemma spiral_clothoid_reuses_iso : forall s f,
  intake_map s (TSpiralCurve (SpiralOfClothoid f)) =
    intake_map s (TClothoidIso f).
Proof.
  intros s f.
  unfold intake_map, intake_map_atom, map_spiral, cert_of_spiral.
  reflexivity.
Qed.

Lemma intake_matches_cert : forall s sp,
  match cert_of_spiral sp with
  | inr f =>
      intake_map s (TSpiralCurve sp) = intake_map s (TClothoidIso f)
  | inl d =>
      intake_map s (TSpiralCurve sp) =
        IntakeDecline (intake_decline_of d)
  end.
Proof.
  intros s sp.
  unfold intake_map, intake_map_atom, map_spiral.
  destruct sp as [f|k]; reflexivity.
Qed.

Lemma spiral_clothoid_sample_hits :
  exists b c,
    intake_map default_sheet (TSpiralCurve (SpiralOfClothoid sample_iso)) =
      IntakeBag b /\
    b = clothoid_bag default_sheet sample_egg /\
    In c (bag_chickens b) /\
    ck_egg c = MkClothoid sample_egg /\
    sample_egg <> locked_clothoid_egg /\
    cloth_wf sample_egg.
Proof.
  destruct iso_sample_intake_hits as [Hb [Hneq Hwf]].
  exists (clothoid_bag default_sheet sample_egg).
  exists (mkChicken 0%nat 1%nat (MkClothoid sample_egg)).
  split; [rewrite spiral_clothoid_reuses_iso; exact Hb|].
  split; [reflexivity|].
  split; [now left|].
  split; [reflexivity|].
  split; [exact Hneq|exact Hwf].
Qed.

Lemma spiral_other_declines : forall k,
  intake_map default_sheet (TSpiralCurve (SpiralOther k)) =
    IntakeDecline ID_SpiralOther.
Proof.
  intros k.
  unfold intake_map, intake_map_atom, map_spiral, cert_of_spiral,
    intake_decline_of.
  reflexivity.
Qed.

Lemma spiral_clothoid_nameplate_declines :
  intake_map default_sheet
    (TSpiralCurve (SpiralOther SOK_ClothoidNameplate)) =
    IntakeDecline ID_SpiralOther.
Proof. exact (spiral_other_declines SOK_ClothoidNameplate). Qed.

Lemma jts_matches_class : forall s k0 k1 len,
  match classify_jts k0 k1 len with
  | JC_Example5 =>
      intake_map s (TClothoidJts k0 k1 len) =
        map_clothoid s locked_iso_clothoid
  | JC_NonPositiveLength =>
      intake_map s (TClothoidJts k0 k1 len) =
        IntakeDecline (intake_decline_of (CD_JtsNonPositiveLength k0 k1 len))
  | JC_TripleNotYet =>
      intake_map s (TClothoidJts k0 k1 len) =
        IntakeDecline (intake_decline_of (CD_JtsTripleNotYet k0 k1 len))
  end.
Proof.
  intros s k0 k1 len.
  unfold intake_map, intake_map_atom, map_jts_clothoid.
  destruct (classify_jts k0 k1 len); reflexivity.
Qed.

Lemma jts_length_before_example5 :
  intake_map default_sheet
    (TClothoidJts example5_jts_k0 example5_jts_k1 0) =
    IntakeDecline ID_JtsNonPositiveLength.
Proof.
  unfold intake_map, intake_map_atom, map_jts_clothoid, intake_decline_of.
  rewrite classify_length_first. reflexivity.
Qed.

Lemma jts_nonpositive_length_declines :
  intake_map default_sheet (TClothoidJts 0 0 0) =
    IntakeDecline ID_JtsNonPositiveLength.
Proof.
  unfold intake_map, intake_map_atom, map_jts_clothoid, intake_decline_of.
  rewrite classify_jts_nonpos. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Named QEX. Do not inhabit. Next letters, not this one.                     *)
(* -------------------------------------------------------------------------- *)

Inductive SpiralJtsMissing : Type :=
| SJ_EmitParseId
| SJ_CompoundFold
| SJ_JtsG1.

Definition spiral_jts_missing (_ : SpiralJtsMissing) : Prop := False.

Lemma spiral_emit_parse_missing :
  ~ spiral_jts_missing SJ_EmitParseId.
Proof. intro H. exact H. Qed.

Lemma spiral_compound_fold_missing :
  ~ spiral_jts_missing SJ_CompoundFold.
Proof. intro H. exact H. Qed.

Lemma spiral_jts_g1_missing :
  ~ spiral_jts_missing SJ_JtsG1.
Proof. intro H. exact H. Qed.

(* WITNESS {"claimId":"0007-intake-spiral","topic":"overlay","lemma":"ticket_0007_intake_spiral_qed_or_qex","title":"SPIRALCURVE clothoid kind reuses normalizer 1 and can bag a non-locked MkClothoid; every SpiralOther declines ID_SpiralOther; JTS L<=0 declines ID_JtsNonPositiveLength; other triples decline ID_JtsClothoidNotYet; example5 stays locked_clothoid_egg; MemberState projects (QED) or parse-emit id / compound fold / JTS G1 inhabit (QEX); discharged QED; not a remint of 0007-intake-mkclothoid","file":"theories/IntakeSpiralJtsMap.v","witness":"0007-intake-spiral","board":"ADR-0007"} *)
Theorem ticket_0007_intake_spiral_qed_or_qex :
  ((forall s f,
      intake_map s (TSpiralCurve (SpiralOfClothoid f)) =
        intake_map s (TClothoidIso f)) /\
   (exists b c,
      intake_map default_sheet (TSpiralCurve (SpiralOfClothoid sample_iso)) =
        IntakeBag b /\
      b = clothoid_bag default_sheet sample_egg /\
      In c (bag_chickens b) /\
      ck_egg c = MkClothoid sample_egg /\
      sample_egg <> locked_clothoid_egg /\
      cloth_wf sample_egg) /\
   (forall k,
      intake_map default_sheet (TSpiralCurve (SpiralOther k)) =
        IntakeDecline ID_SpiralOther) /\
   intake_map default_sheet
     (TSpiralCurve (SpiralOther SOK_ClothoidNameplate)) =
     IntakeDecline ID_SpiralOther /\
   intake_map default_sheet
     (TClothoidJts example5_jts_k0 example5_jts_k1 0) =
     IntakeDecline ID_JtsNonPositiveLength /\
   intake_map default_sheet (TClothoidJts 0 0 1) =
     IntakeDecline ID_JtsClothoidNotYet /\
   intake_map default_sheet example5_jts_cst =
     IntakeBag (clothoid_bag default_sheet locked_clothoid_egg) /\
   (forall p d k,
      mst_end (mkMemberState p d k) = p /\
      mst_dir (mkMemberState p d k) = d /\
      mst_curvature (mkMemberState p d k) = k))
  \/
  (spiral_jts_missing SJ_EmitParseId /\
   spiral_jts_missing SJ_CompoundFold /\
   spiral_jts_missing SJ_JtsG1).
Proof.
  left.
  split; [exact spiral_clothoid_reuses_iso|].
  split; [exact spiral_clothoid_sample_hits|].
  split; [exact spiral_other_declines|].
  split; [exact spiral_clothoid_nameplate_declines|].
  split; [exact jts_length_before_example5|].
  split; [exact jts_other_triple_declines|].
  split; [exact jts_clothoid_maps|].
  exact member_state_proj.
Qed.

Print Assumptions spiral_clothoid_reuses_iso.
Print Assumptions intake_matches_cert.
Print Assumptions spiral_clothoid_sample_hits.
Print Assumptions spiral_other_declines.
Print Assumptions spiral_clothoid_nameplate_declines.
Print Assumptions jts_matches_class.
Print Assumptions jts_length_before_example5.
Print Assumptions jts_nonpositive_length_declines.
Print Assumptions spiral_emit_parse_missing.
Print Assumptions spiral_compound_fold_missing.
Print Assumptions spiral_jts_g1_missing.
Print Assumptions ticket_0007_intake_spiral_qed_or_qex.
