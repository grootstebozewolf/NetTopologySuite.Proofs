(* ============================================================================
   NetTopologySuite.Proofs.IntakeSpiralJtsMap
   ----------------------------------------------------------------------------
   Walker face of SPIRALCURVE intake and the JTS decline taxonomy
   (claimId 0007-intake-spiral, witness 0007-intake-spiral).
   Not a remint of 0007-intake-mkclothoid.

   QED: a clothoid SPIRALCURVE bags norm2 when try hits, and
   otherwise declines by name (length, k0 = k1, similarity).
   SpiralOther declines ID_SpiralOther. The sample bag is not
   the locked example5 egg (cloth_A <> 1). JTS L <= 0, other
   triples, and example5 are unchanged. MemberState projects.
   Statement change: the universal ID_SpiralClothoidNotYet
   arm is gone. claimId 0007-intake-spiral is not reminted.

   QEX: emit/parse identity only. Fold and JTS G1 are discharged.
   Normalizer 2 exists (ClothoidNorm2). The ticket lists emit/parse.
   It does not claim the negation of that obligation.

   ADR-0005: lenient intake, not isValid. 3-axiom host.
   No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance SheetHenCook IntakeWalker IntakeSpiralJts
  IsoClothoidIntake IsoClothoidIntakeMap IntakeWalkerClothoid IntakeSpiralFront
  SignedCurvature ClothoidNorm2 SheetHenClothoidFrames SheetHenClothoidBounds
  IntakeCompoundFold.
Import ListNotations.
Local Open Scope R_scope.
Local Open Scope list_scope.

Lemma spiral_clothoid_bags : forall sh sc e,
  try_spiral_clothoid sc = inr e ->
  intake_map sh (TSpiralCurve (SpiralOfClothoid sc)) =
    IntakeBag (clothoid_bag sh e).
Proof.
  intros sh sc e H.
  unfold intake_map, intake_map_atom, map_spiral. rewrite H. reflexivity.
Qed.

Lemma intake_matches_cert : forall sh k,
  intake_map sh (TSpiralCurve (SpiralOther k)) =
    IntakeDecline (intake_decline_of (cert_of_spiral (SpiralOther k))).
Proof.
  intros sh k.
  unfold intake_map, intake_map_atom, map_spiral, cert_of_spiral,
    intake_decline_of. reflexivity.
Qed.

Lemma spiral_clothoid_not_iso :
  exists e,
    intake_map default_sheet
      (TSpiralCurve (SpiralOfClothoid sample_spiral_clothoid)) =
      IntakeBag (clothoid_bag default_sheet e) /\
    cloth_A e <> 1 /\
    intake_map default_sheet
      (TSpiralCurve (SpiralOfClothoid sample_spiral_clothoid)) <>
      intake_map default_sheet example5_jts_cst.
Proof.
  destruct sample_spiral_hits as [e [Ht HA]].
  exists e.
  split; [exact (spiral_clothoid_bags _ _ _ Ht)|].
  split; [exact HA|].
  intro H.
  rewrite (spiral_clothoid_bags _ _ _ Ht), jts_clothoid_maps in H.
  apply (f_equal (fun r => match r with
    | IntakeBag b => bag_chickens b
    | IntakeDecline _ => []
    end)) in H.
  cbn in H. injection H as He. rewrite He in HA.
  unfold locked_clothoid_egg in HA. cbn in HA. contradiction.
Qed.

Lemma spiral_other_declines : forall k,
  intake_map default_sheet (TSpiralCurve (SpiralOther k)) =
    IntakeDecline ID_SpiralOther.
Proof.
  intros k. unfold intake_map, intake_map_atom, map_spiral. reflexivity.
Qed.

Lemma spiral_length_first :
  intake_map default_sheet
    (TSpiralCurve (SpiralOfClothoid zero_len_spiral)) =
    IntakeDecline ID_SpiralNonPositiveLength.
Proof.
  unfold intake_map, intake_map_atom, map_spiral.
  rewrite zero_len_even_equal_k. reflexivity.
Qed.

Lemma spiral_constant_curvature :
  intake_map default_sheet
    (TSpiralCurve (SpiralOfClothoid const_k_spiral)) =
    IntakeDecline ID_SpiralConstantCurvature.
Proof.
  unfold intake_map, intake_map_atom, map_spiral.
  rewrite const_k_unit_frame. reflexivity.
Qed.

Lemma spiral_not_similarity :
  intake_map default_sheet
    (TSpiralCurve (SpiralOfClothoid shear_spiral)) =
    IntakeDecline ID_NotSimilarityFrame.
Proof.
  unfold intake_map, intake_map_atom, map_spiral.
  rewrite shear_spiral_fails. reflexivity.
Qed.

Lemma spiral_parallel_refs :
  intake_map default_sheet
    (TSpiralCurve (SpiralOfClothoid parallel_spiral)) =
    IntakeDecline ID_NotSimilarityFrame.
Proof.
  unfold intake_map, intake_map_atom, map_spiral.
  rewrite parallel_spiral_fails. reflexivity.
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
(* Emit/parse stays an unproved Prop. The fold and JTS G1 are proved.        *)
(* Their negation is not a lemma.                                             *)
(* -------------------------------------------------------------------------- *)

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
   can carry that joint. Other positive JTS triples still decline. *)
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

Definition reals5_meet (pred start_s : MemberState) : bool :=
  if Req_EM_T (px (mst_end pred)) (px (mst_end start_s)) then
    if Req_EM_T (py (mst_end pred)) (py (mst_end start_s)) then
      if Req_EM_T (px (mst_dir pred)) (px (mst_dir start_s)) then
        if Req_EM_T (py (mst_dir pred)) (py (mst_dir start_s)) then
          if Req_EM_T (mst_curvature pred) (mst_curvature start_s) then true
          else false
        else false
      else false
    else false
  else false.

Fixpoint ms_fold (pred : MemberState) (xs : list (MemberState * MemberState))
  : option MemberState :=
  match xs with
  | [] => Some pred
  | (start_s, end_s) :: rest =>
      if reals5_meet pred start_s then ms_fold end_s rest else None
  end.

Lemma reals5_meet_spec : forall pred start_s,
  reals5_meet pred start_s = true <->
  mst_end pred = mst_end start_s /\
  mst_dir pred = mst_dir start_s /\
  mst_curvature pred = mst_curvature start_s.
Proof.
  intros pred start_s. split.
  - intro Hm. unfold reals5_meet in Hm.
    destruct (Req_EM_T (px (mst_end pred)) (px (mst_end start_s))) as [Hx|Hx];
      [|discriminate].
    destruct (Req_EM_T (py (mst_end pred)) (py (mst_end start_s))) as [Hy|Hy];
      [|discriminate].
    destruct (Req_EM_T (px (mst_dir pred)) (px (mst_dir start_s))) as [Hdx|Hdx];
      [|discriminate].
    destruct (Req_EM_T (py (mst_dir pred)) (py (mst_dir start_s))) as [Hdy|Hdy];
      [|discriminate].
    destruct (Req_EM_T (mst_curvature pred) (mst_curvature start_s)) as [Hk|Hk];
      [|discriminate].
    split; [|split].
    + destruct (mst_end pred) as [x1 y1], (mst_end start_s) as [x2 y2].
      cbn in Hx, Hy. subst. reflexivity.
    + destruct (mst_dir pred) as [u1 v1], (mst_dir start_s) as [u2 v2].
      cbn in Hdx, Hdy. subst. reflexivity.
    + exact Hk.
  - intros [He [Hd Hk]]. unfold reals5_meet. rewrite He, Hd, Hk.
    destruct (Req_EM_T (px (mst_end start_s)) (px (mst_end start_s))) as [_|H];
      [|exfalso; apply H; reflexivity].
    destruct (Req_EM_T (py (mst_end start_s)) (py (mst_end start_s))) as [_|H];
      [|exfalso; apply H; reflexivity].
    destruct (Req_EM_T (px (mst_dir start_s)) (px (mst_dir start_s))) as [_|H];
      [|exfalso; apply H; reflexivity].
    destruct (Req_EM_T (py (mst_dir start_s)) (py (mst_dir start_s))) as [_|H];
      [|exfalso; apply H; reflexivity].
    destruct (Req_EM_T (mst_curvature start_s) (mst_curvature start_s)) as [_|H];
      [|exfalso; apply H; reflexivity].
    reflexivity.
Qed.

Lemma spiral_compound_fold_qed : spiral_compound_fold.
Proof.
  unfold spiral_compound_fold. exists ms_fold. split; [|split].
  - intros pred. reflexivity.
  - intros pred start_s end_s rest Hmeet. simpl.
    apply (proj2 (reals5_meet_spec pred start_s)) in Hmeet.
    rewrite Hmeet. reflexivity.
  - intros pred start_s end_s rest Hmiss. simpl.
    destruct (reals5_meet pred start_s) eqn:Hm.
    + exfalso. apply Hmiss. apply (proj1 (reals5_meet_spec pred start_s)). exact Hm.
    + reflexivity.
Qed.

Lemma spiral_jts_g1_qed : spiral_jts_g1.
Proof.
  unfold spiral_jts_g1.
  split.
  - unfold example5_jts_k0, locked_clothoid_egg.
    rewrite (east_sigma (mkPoint 0 0)).
    cbn [cloth_sd cloth_A mk_cloth]. field.
  - split.
    + unfold locked_clothoid_egg. cbn [cloth_sd mk_cloth].
      rewrite east_vx, east_vy.
      unfold fresnel_cx_integrand, fresnel_cy_integrand, fresnel_angle.
      assert (Hz : 0 * 0 / 2 = 0) by field.
      rewrite Hz. rewrite cos_0, sin_0. ring.
    + exists (mkMemberState (cloth_p0 locked_clothoid_egg)
               (mkPoint 1 0) example5_jts_k0).
      split; [reflexivity|].
      split.
      { cbn. unfold locked_clothoid_egg. cbn [cloth_sd mk_cloth].
        rewrite east_vx. unfold fresnel_cx_integrand, fresnel_angle.
        assert (Hz : 0 * 0 / 2 = 0) by field.
        rewrite Hz. rewrite cos_0. reflexivity. }
      split.
      { cbn. unfold locked_clothoid_egg. cbn [cloth_sd mk_cloth].
        rewrite east_vy. unfold fresnel_cy_integrand, fresnel_angle.
        assert (Hz : 0 * 0 / 2 = 0) by field.
        rewrite Hz. rewrite sin_0. reflexivity. }
      { cbn. reflexivity. }
Qed.

(* WITNESS {"claimId":"0007-intake-spiral","topic":"overlay","lemma":"ticket_0007_intake_spiral_qed_or_qex","title":"Statement change, claimId not reminted: a clothoid SPIRALCURVE bags norm2 on try hit and otherwise declines ID_SpiralNonPositiveLength, ID_SpiralConstantCurvature, or ID_NotSimilarityFrame; sample cloth_A <> 1 so it is not the locked example5 bag; SpiralOther declines ID_SpiralOther; JTS L<=0, other triples, and example5 stay; MemberState projects (QED). QEX is spiral_emit_parse_id; the compound fold and JTS G1 are discharged; SJ_Normalizer2 stays dropped because norm2 exists. Negation of the QEX obligation is not claimed. Not a remint of 0007-intake-mkclothoid","file":"theories/IntakeSpiralJtsMap.v","witness":"0007-intake-spiral","board":"ADR-0007"} *)
Theorem ticket_0007_intake_spiral_qed_or_qex :
  ((forall sh sc e,
      try_spiral_clothoid sc = inr e ->
      intake_map sh (TSpiralCurve (SpiralOfClothoid sc)) =
        IntakeBag (clothoid_bag sh e)) /\
   (exists e,
      intake_map default_sheet
        (TSpiralCurve (SpiralOfClothoid sample_spiral_clothoid)) =
        IntakeBag (clothoid_bag default_sheet e) /\
      cloth_A e <> 1 /\
      intake_map default_sheet
        (TSpiralCurve (SpiralOfClothoid sample_spiral_clothoid)) <>
        intake_map default_sheet example5_jts_cst) /\
   (forall k,
      intake_map default_sheet (TSpiralCurve (SpiralOther k)) =
        IntakeDecline ID_SpiralOther) /\
   intake_map default_sheet
     (TSpiralCurve (SpiralOfClothoid zero_len_spiral)) =
     IntakeDecline ID_SpiralNonPositiveLength /\
   intake_map default_sheet
     (TSpiralCurve (SpiralOfClothoid const_k_spiral)) =
     IntakeDecline ID_SpiralConstantCurvature /\
   intake_map default_sheet
     (TSpiralCurve (SpiralOfClothoid shear_spiral)) =
     IntakeDecline ID_NotSimilarityFrame /\
   intake_map default_sheet
     (TSpiralCurve (SpiralOfClothoid parallel_spiral)) =
     IntakeDecline ID_NotSimilarityFrame /\
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
  spiral_emit_parse_id.
Proof.
  (* QED arm. The right disjunct only names the gaps. *)
  left.
  split; [exact spiral_clothoid_bags|].
  split; [exact spiral_clothoid_not_iso|].
  split; [exact spiral_other_declines|].
  split; [exact spiral_length_first|].
  split; [exact spiral_constant_curvature|].
  split; [exact spiral_not_similarity|].
  split; [exact spiral_parallel_refs|].
  split; [exact jts_length_before_example5|].
  split; [exact jts_other_triple_declines|].
  split; [exact jts_clothoid_maps|].
  exact member_state_proj.
Qed.

Print Assumptions spiral_clothoid_bags.
Print Assumptions intake_matches_cert.
Print Assumptions spiral_clothoid_not_iso.
Print Assumptions spiral_other_declines.
Print Assumptions spiral_length_first.
Print Assumptions spiral_constant_curvature.
Print Assumptions spiral_not_similarity.
Print Assumptions spiral_parallel_refs.
Print Assumptions jts_matches_class.
Print Assumptions jts_length_before_example5.
Print Assumptions jts_nonpositive_length_declines.
Print Assumptions ticket_0007_intake_spiral_qed_or_qex.
Print Assumptions reals5_meet_spec.
Print Assumptions spiral_compound_fold_qed.
Print Assumptions spiral_jts_g1_qed.
