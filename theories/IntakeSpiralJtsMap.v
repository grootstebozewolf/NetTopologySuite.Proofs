(* ============================================================================
   NetTopologySuite.Proofs.IntakeSpiralJtsMap
   ----------------------------------------------------------------------------
   Walker face of SPIRALCURVE intake and the JTS decline taxonomy
   (claimId 0007-intake-spiral, witness 0007-intake-spiral).
   Not a remint of 0007-intake-mkclothoid.

   QED: a start-placed clothoid SPIRALCURVE declines
   ID_SpiralClothoidNotYet (it is not an IsoClothoid); every
   SpiralOther declines ID_SpiralOther; JTS L <= 0 declines
   ID_JtsNonPositiveLength before the example5 test; any other
   positive triple declines ID_JtsClothoidNotYet; example5
   still bags locked_clothoid_egg. MemberState projects.

   QEX: normalizer 2 is the False marker (that definition does
   not exist yet). Emit/parse identity on the JTS and spiral
   forms, the MemberState compound fold, and JTS G1 are
   Definitions of type Prop over types that exist. The ticket
   lists them. It does not claim the negation of that list.

   ADR-0005: lenient intake, not isValid. 3-axiom host.
   No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals List.
From NTS.Proofs Require Import Distance SheetHenCook IntakeWalker IntakeSpiralJts
  IsoClothoidIntake IsoClothoidIntakeMap IntakeWalkerClothoid.
Import ListNotations.
Local Open Scope R_scope.
Local Open Scope list_scope.

Lemma spiral_clothoid_declines : forall sh sc,
  intake_map sh (TSpiralCurve (SpiralOfClothoid sc)) =
    IntakeDecline ID_SpiralClothoidNotYet.
Proof.
  intros sh sc.
  unfold intake_map, intake_map_atom, map_spiral, cert_of_spiral,
    intake_decline_of.
  reflexivity.
Qed.

Lemma intake_matches_cert : forall sh sp,
  intake_map sh (TSpiralCurve sp) =
    IntakeDecline (intake_decline_of (cert_of_spiral sp)).
Proof.
  intros sh sp.
  unfold intake_map, intake_map_atom, map_spiral.
  destruct sp as [sc|k]; reflexivity.
Qed.

Lemma spiral_clothoid_not_iso :
  intake_map default_sheet
    (TSpiralCurve (SpiralOfClothoid sample_spiral_clothoid)) =
    IntakeDecline ID_SpiralClothoidNotYet /\
  intake_map default_sheet
    (TSpiralCurve (SpiralOfClothoid sample_spiral_clothoid)) <>
    intake_map default_sheet example5_jts_cst.
Proof.
  split.
  - exact (spiral_clothoid_declines default_sheet sample_spiral_clothoid).
  - rewrite spiral_clothoid_declines, jts_clothoid_maps. discriminate.
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
(* QEX. Normalizer 2 is a missing definition (False marker). The other       *)
(* three gaps are proofs about types that already exist: named Props,        *)
(* not Admitted, not proved, and their negation is not a lemma.              *)
(* -------------------------------------------------------------------------- *)

Inductive SpiralJtsMissing : Type :=
| SJ_Normalizer2.

Definition spiral_jts_missing (_ : SpiralJtsMissing) : Prop := False.

Lemma spiral_normalizer2_missing :
  ~ spiral_jts_missing SJ_Normalizer2.
Proof. intro H. exact H. Qed.

(* Decline ids drop the CST payload, so identity is on the intake
   image: re-parsing an emit of the result recovers that result.
   CST-level parse ∘ emit = id is not this statement. *)
Definition spiral_emit_parse_id : Prop :=
  exists emit : IntakeResult -> TaggedCst,
    forall sh t,
      (exists sp, t = TSpiralCurve sp) \/
      (exists k0 k1 len, t = TClothoidJts k0 k1 len) ->
      intake_map sh (emit (intake_map sh t)) = intake_map sh t.

(* Compound fold on MemberState. A joint carries the next member's
   start state and its end state. Empty keeps the running state.
   A joint whose start meets the predecessor in position, direction,
   and curvature continues from that member's end. A mismatch is None. *)
Definition spiral_compound_fold : Prop :=
  exists fold : MemberState -> list (MemberState * MemberState) -> option MemberState,
    (forall pred, fold pred [] = Some pred) /\
    (forall pred start_s end_s rest,
       mst_end pred = mst_end start_s /\
       mst_dir pred = mst_dir start_s /\
       mst_curvature pred = mst_curvature start_s ->
       fold pred ((start_s, end_s) :: rest) = fold end_s rest) /\
    (forall pred start_s end_s rest,
       ~ (mst_end pred = mst_end start_s /\
          mst_dir pred = mst_dir start_s /\
          mst_curvature pred = mst_curvature start_s) ->
       fold pred ((start_s, end_s) :: rest) = None).

(* JTS G1 at the example5 bag, the JTS form that already has an egg.
   Start position is cloth_p0, start direction is the unit tangent at
   sd, and start curvature k0 equals sigma * sd / A^2. A MemberState
   can carry that joint. Other positive triples have no egg until
   normalizer 2. *)
Definition spiral_jts_g1 : Prop :=
  example5_jts_k0 =
    cloth_sigma locked_clothoid_egg * cloth_sd locked_clothoid_egg /
    (cloth_A locked_clothoid_egg * cloth_A locked_clothoid_egg) /\
  cloth_vx locked_clothoid_egg (cloth_sd locked_clothoid_egg) *
    cloth_vx locked_clothoid_egg (cloth_sd locked_clothoid_egg) +
  cloth_vy locked_clothoid_egg (cloth_sd locked_clothoid_egg) *
    cloth_vy locked_clothoid_egg (cloth_sd locked_clothoid_egg) = 1 /\
  exists pred : MemberState,
    mst_end pred = cloth_p0 locked_clothoid_egg /\
    px (mst_dir pred) =
      cloth_vx locked_clothoid_egg (cloth_sd locked_clothoid_egg) /\
    py (mst_dir pred) =
      cloth_vy locked_clothoid_egg (cloth_sd locked_clothoid_egg) /\
    mst_curvature pred = example5_jts_k0.

(* WITNESS {"claimId":"0007-intake-spiral","topic":"overlay","lemma":"ticket_0007_intake_spiral_qed_or_qex","title":"Start-placed clothoid SPIRALCURVE declines ID_SpiralClothoidNotYet until normalizer 2; every SpiralOther declines ID_SpiralOther; JTS L<=0 declines ID_JtsNonPositiveLength; other triples decline ID_JtsClothoidNotYet; example5 stays locked_clothoid_egg; MemberState projects (QED). QEX lists SJ_Normalizer2 (missing definition) and obligations spiral_emit_parse_id, spiral_compound_fold, spiral_jts_g1; their negation is not claimed. Not a remint of 0007-intake-mkclothoid","file":"theories/IntakeSpiralJtsMap.v","witness":"0007-intake-spiral","board":"ADR-0007"} *)
Theorem ticket_0007_intake_spiral_qed_or_qex :
  ((forall sh sc,
      intake_map sh (TSpiralCurve (SpiralOfClothoid sc)) =
        IntakeDecline ID_SpiralClothoidNotYet) /\
   (intake_map default_sheet
      (TSpiralCurve (SpiralOfClothoid sample_spiral_clothoid)) =
      IntakeDecline ID_SpiralClothoidNotYet /\
    intake_map default_sheet
      (TSpiralCurve (SpiralOfClothoid sample_spiral_clothoid)) <>
      intake_map default_sheet example5_jts_cst) /\
   (forall k,
      intake_map default_sheet (TSpiralCurve (SpiralOther k)) =
        IntakeDecline ID_SpiralOther) /\
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
  (spiral_jts_missing SJ_Normalizer2 /\
   spiral_emit_parse_id /\
   spiral_compound_fold /\
   spiral_jts_g1).
Proof.
  (* QED arm. The right disjunct only names the gaps. *)
  left.
  split; [exact spiral_clothoid_declines|].
  split; [exact spiral_clothoid_not_iso|].
  split; [exact spiral_other_declines|].
  split; [exact jts_length_before_example5|].
  split; [exact jts_other_triple_declines|].
  split; [exact jts_clothoid_maps|].
  exact member_state_proj.
Qed.

Print Assumptions spiral_clothoid_declines.
Print Assumptions intake_matches_cert.
Print Assumptions spiral_clothoid_not_iso.
Print Assumptions spiral_other_declines.
Print Assumptions jts_matches_class.
Print Assumptions jts_length_before_example5.
Print Assumptions jts_nonpositive_length_declines.
Print Assumptions spiral_normalizer2_missing.
Print Assumptions ticket_0007_intake_spiral_qed_or_qex.
