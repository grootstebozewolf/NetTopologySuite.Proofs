(* ============================================================================
   NetTopologySuite.Proofs.SidecarClothoidEgg
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: clothoid egg sidecar
   (claimId 0007-clothoid-egg).

   Product / sidecar face: clothoid as an EggClass on the ADR-0007
   sheet / hen / cook vocabulary. Host already has EggClothoid /
   MkOutOfScope EggClothoid, clothoid_clothoid_not_first_scope,
   clothoid_decline_I_ok / clothoid_decline_witness. This module
   packages that Decline-on-host fence plus one already-Qed
   constructive witness (RelateClothoid chord-seed; residual
   uniqueness stays metric). Prefer SidecarClothoid* over reminting
   host cook (same preference as SidecarCirc* over CircularCook*
   for non-host).

   The existing clothoid corpus (RelateClothoid, ClothoidLength*,
   ClothoidHalley, ClothoidResidual, Fresnel inhab, …) is
   metric / relate / buffer research. This letter packages what
   is already Qed into the egg / cook sidecar story. It does
   NOT remint Fresnel / Halley as noding progress.

   One honest first rung. One locked fixture. Do not ship
   Campaign I–II in this letter.

   QED: sidecar egg packaging on EggClothoid; host I_ok Decline
   and try_cook_hit None; locked unit-square clothoid chords
   reuse clothoid_chord_proper_cross_share; demote-to-chord is
   NodingNG / host first cook, not a clothoid Hit.

   QEX: clothoid×clothoid is not first cook (checklist 4). Named
   missing constructor: no MkClothoid on Egg, no I_ok Hit arm
   on clothoid eggs. Do not fake first-cook expand or
   LoopDischarged.

   What this is not:
     Host first_cook_scope / try_cook_hit expand to
     clothoid×clothoid. CircGamma / ι / ρ remint. MkCirc. Host
     circular cook. Shewchuk / Hobby / Priest / Jordan /
     HotPixel / OverlayNG snap remint. SQL/MM Multi Landed /
     Phase B done-when / H⊥ / MerkatorBV / 522-n. Full
     clothoid×clothoid noder. Bag-loop ρ Discharge.

   Parks Γ / ι / ρ (named QEX, landed). This letter cites them
   once; it does not remint CircGamma, ι, leftover_width, or
   LoopDischarged. First cook stays chord–chord. Host CircGamma
   stays QEX.

   ADR-0007 is Accepted (2026-09-07). This letter does not reopen
   Status. QEX is not a new Accept cycle. ADR-0006 Status stays
   Accepted. Testable 𝓘 / cook results sit on the accepted Oracle
   line protocol. This module mints no keyword and no second
   external seam.

   WITNESS topic: overlay · claimId: 0007-clothoid-egg
   witness: 0007-clothoid-egg
   board: ADR-0007
   3-axiom host. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra Ranalysis1.
From NTS.Proofs Require Import Distance SheetHenCook NodingNG RelateLineLine
  RelateClothoid.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Product face: a sidecar clothoid egg is a named EggClothoid interpolant    *)
(* tag plus its already-Qed chord seed. Host Egg has no MkClothoid.           *)
(* -------------------------------------------------------------------------- *)

Record SidecarClothoidEgg : Type := mkSidecarClothoidEgg {
  sce_sheet : Sheet;
  sce_chord : ClothoidChord
}.

Definition sidecar_clothoid_host_egg (_ : SidecarClothoidEgg) : Egg :=
  MkOutOfScope EggClothoid.

Definition sidecar_clothoid_demote (e : SidecarClothoidEgg) : ChordEgg :=
  mkChordEgg (cc_start (sce_chord e)) (cc_end (sce_chord e)).

Definition sidecar_clothoid_chicken (src dst : Hen) (e : SidecarClothoidEgg)
  : Chicken :=
  mkChicken src dst (sidecar_clothoid_host_egg e).

Lemma sidecar_clothoid_class :
  forall e, egg_class (sidecar_clothoid_host_egg e) = EggClothoid.
Proof.
  intros e. reflexivity.
Qed.

Lemma sidecar_clothoid_only_out_of_scope :
  forall e, sidecar_clothoid_host_egg e = MkOutOfScope EggClothoid.
Proof.
  intros e. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked fixture: unit-square diagonals as clothoid chords. Same geometry    *)
(* as NodingNG's crossing pair — the chord seed, not a clothoid cook.         *)
(* -------------------------------------------------------------------------- *)

Definition locked_clothoid_ab : ClothoidChord :=
  mkClothoidChord (ce_p0 diag_ab) (ce_p1 diag_ab).

Definition locked_clothoid_cd : ClothoidChord :=
  mkClothoidChord (ce_p0 diag_cd) (ce_p1 diag_cd).

Definition locked_sce_ab : SidecarClothoidEgg :=
  mkSidecarClothoidEgg default_sheet locked_clothoid_ab.

Definition locked_sce_cd : SidecarClothoidEgg :=
  mkSidecarClothoidEgg default_sheet locked_clothoid_cd.

Definition locked_clothoid_ck1 : Chicken :=
  sidecar_clothoid_chicken 0%nat 1%nat locked_sce_ab.

Definition locked_clothoid_ck2 : Chicken :=
  sidecar_clothoid_chicken 2%nat 3%nat locked_sce_cd.

Lemma locked_clothoid_demote_is_host_crossing :
  sidecar_clothoid_demote locked_sce_ab = diag_ab /\
  sidecar_clothoid_demote locked_sce_cd = diag_cd.
Proof.
  split; reflexivity.
Qed.

Lemma locked_clothoid_same_sheet_as_nodingng :
  sce_sheet locked_sce_ab = default_sheet /\
  sce_sheet locked_sce_cd = nng_sheet nodingng_crossing_pair.
Proof.
  split; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Decline-on-host. Clothoid eggs stay MkOutOfScope. Not a constructed Hit.   *)
(* -------------------------------------------------------------------------- *)

Lemma sidecar_clothoid_host_decline :
  I_ok (sidecar_clothoid_host_egg locked_sce_ab)
       (sidecar_clothoid_host_egg locked_sce_cd) IDecline.
Proof.
  exact clothoid_decline_I_ok.
Qed.

Lemma sidecar_clothoid_host_hit_false :
  forall p ti tj,
    ~ I_ok (sidecar_clothoid_host_egg locked_sce_ab)
           (sidecar_clothoid_host_egg locked_sce_cd) (IHit p ti tj).
Proof.
  intros p ti tj H. exact H.
Qed.

Lemma sidecar_clothoid_host_empty_false :
  ~ I_ok (sidecar_clothoid_host_egg locked_sce_ab)
         (sidecar_clothoid_host_egg locked_sce_cd) IEmpty.
Proof.
  intro H. exact H.
Qed.

Lemma sidecar_clothoid_try_cook_none :
  try_cook_hit locked_clothoid_ck1 locked_clothoid_ck2 IDecline crossing_hen
    = None.
Proof.
  reflexivity.
Qed.

Lemma sidecar_clothoid_try_cook_hit_none :
  forall p ti tj h,
    try_cook_hit locked_clothoid_ck1 locked_clothoid_ck2 (IHit p ti tj) h
      = None.
Proof.
  intros p ti tj h.
  apply try_cook_hit_out_of_scope_none.
  left. discriminate.
Qed.

Lemma sidecar_clothoid_empty_neq_decline : IEmpty <> IDecline.
Proof.
  exact IEmpty_neq_IDecline.
Qed.

(* -------------------------------------------------------------------------- *)
(* Constructive chord-seed reuse. RelateClothoid already Qed: a clothoid      *)
(* chord that properly crosses a segment shares a point. That is the          *)
(* demoted-chord geometry, not a clothoid×clothoid cook Hit.                  *)
(* -------------------------------------------------------------------------- *)

Lemma locked_clothoid_chord_proper_cross :
  clothoid_chord_proper_cross locked_clothoid_ab
    (cc_start locked_clothoid_cd) (cc_end locked_clothoid_cd).
Proof.
  unfold clothoid_chord_proper_cross, segments_proper_cross,
         locked_clothoid_ab, locked_clothoid_cd, diag_ab, diag_cd, cross.
  simpl. split; lra.
Qed.

(* WITNESS {"claimId":"0007-clothoid-egg","topic":"overlay","lemma":"sidecar_clothoid_chord_seed","title":"Sidecar clothoid locked unit-square chords reuse RelateClothoid proper-cross share; demoted-chord geometry, not a clothoid times clothoid cook Hit","file":"theories/SidecarClothoidEgg.v","witness":"0007-clothoid-egg","board":"ADR-0007"} *)
Lemma sidecar_clothoid_chord_seed :
  clothoid_chord_share locked_clothoid_ab
    (cc_start locked_clothoid_cd) (cc_end locked_clothoid_cd).
Proof.
  apply clothoid_chord_proper_cross_share.
  exact locked_clothoid_chord_proper_cross.
Qed.

(* Demote-to-chord inhabits host / NodingNG first cook. Not a clothoid Hit. *)
Lemma sidecar_clothoid_demote_is_nodingng_crossing :
  sidecar_clothoid_demote locked_sce_ab = diag_ab /\
  sidecar_clothoid_demote locked_sce_cd = diag_cd /\
  I_ok (MkChord (sidecar_clothoid_demote locked_sce_ab))
       (MkChord (sidecar_clothoid_demote locked_sce_cd))
       (IHit cross_pt (1 / 2) (1 / 2)) /\
  nodingng_hit_cooks nodingng_crossing_pair crossing_hen.
Proof.
  destruct locked_clothoid_demote_is_host_crossing as [Hab Hcd].
  split; [exact Hab|].
  split; [exact Hcd|].
  rewrite Hab, Hcd.
  split; [exact crossing_I_ok|].
  exact nodingng_crossing_hit_cooks.
Qed.

Lemma sidecar_clothoid_demote_hit_not_clothoid_I_ok :
  I_ok (MkChord (sidecar_clothoid_demote locked_sce_ab))
       (MkChord (sidecar_clothoid_demote locked_sce_cd))
       (IHit cross_pt (1 / 2) (1 / 2)) /\
  ~ I_ok (sidecar_clothoid_host_egg locked_sce_ab)
         (sidecar_clothoid_host_egg locked_sce_cd)
         (IHit cross_pt (1 / 2) (1 / 2)).
Proof.
  split.
  - apply sidecar_clothoid_demote_is_nodingng_crossing.
  - apply sidecar_clothoid_host_hit_false.
Qed.

(* Residual uniqueness is already Qed on the monotone branch
   (RelateClothoid re-export of ClothoidResidual). Metric /
   solver well-posedness — not a cook Hit, not Fresnel noding. *)
Lemma sidecar_clothoid_residual_is_metric :
  forall (f f' : R -> R) (kappa : R),
    (forall L : R, derivable_pt_lim f L (f' L)) ->
    (forall L : R, 0 < L -> Rabs (kappa * L) <= PI -> 0 < f' L) ->
    (forall a b : R,
       a < b ->
       (forall c : R, a <= c <= b -> derivable_pt_lim f c (f' c)) ->
       exists c : R, f b - f a = f' c * (b - a) /\ a < c < b) ->
    forall L1 L2 : R,
      0 < L1 -> 0 < L2 ->
      Rabs (kappa * L1) <= PI -> Rabs (kappa * L2) <= PI ->
      f L1 = 0 -> f L2 = 0 ->
      L1 = L2.
Proof.
  exact clothoid_L_unique_on_branch.
Qed.

(* -------------------------------------------------------------------------- *)
(* Named missing constructors. 508-style, not bools.                          *)
(* -------------------------------------------------------------------------- *)

Inductive SidecarClothoidCookCtor : Type :=
| ClothoidMkClothoid
| ClothoidClothoidHitArm
| ClothoidFirstCookExpand.

Definition sidecar_clothoid_ctor_inhabits
  (c : SidecarClothoidCookCtor) : Prop :=
  match c with
  | ClothoidMkClothoid => False
  | ClothoidClothoidHitArm => False
  | ClothoidFirstCookExpand => False
  end.

Lemma sidecar_clothoid_mkclothoid_missing :
  ~ sidecar_clothoid_ctor_inhabits ClothoidMkClothoid.
Proof.
  intro H. exact H.
Qed.

Lemma sidecar_clothoid_hit_arm_missing :
  ~ sidecar_clothoid_ctor_inhabits ClothoidClothoidHitArm.
Proof.
  intro H. exact H.
Qed.

Lemma sidecar_clothoid_first_cook_expand_missing :
  ~ sidecar_clothoid_ctor_inhabits ClothoidFirstCookExpand.
Proof.
  intro H. exact H.
Qed.

Lemma sidecar_clothoid_not_first_cook :
  ~ first_cook_scope EggClothoid EggClothoid.
Proof.
  exact clothoid_clothoid_not_first_scope.
Qed.

Lemma sidecar_clothoid_first_cook_stays_chord_chord :
  first_cook_scope EggChord EggChord /\
  ~ first_cook_scope EggClothoid EggClothoid /\
  ~ first_cook_scope EggCircularArc EggCircularArc.
Proof.
  split; [exact first_cook_scope_chord_chord|].
  split; [exact clothoid_clothoid_not_first_scope|].
  exact circular_egg_not_first_cook_scope.
Qed.

(* -------------------------------------------------------------------------- *)
(* What the sidecar is / is not. Kind tag, not a second kernel.               *)
(* -------------------------------------------------------------------------- *)

Inductive SidecarClothoidKind : Type :=
| SCE_EggPackaging
| SCE_HostCook
| SCE_NodingNG
| SCE_FresnelNoding
| SCE_CampaignI
| SCE_LoopNoder.

Definition sidecar_clothoid_kind : SidecarClothoidKind := SCE_EggPackaging.

Lemma sidecar_clothoid_is_egg_packaging :
  sidecar_clothoid_kind = SCE_EggPackaging.
Proof.
  reflexivity.
Qed.

Lemma sidecar_clothoid_not_host_cook :
  sidecar_clothoid_kind <> SCE_HostCook.
Proof.
  discriminate.
Qed.

Lemma sidecar_clothoid_not_nodingng :
  sidecar_clothoid_kind <> SCE_NodingNG.
Proof.
  discriminate.
Qed.

Lemma sidecar_clothoid_not_fresnel_noding :
  sidecar_clothoid_kind <> SCE_FresnelNoding.
Proof.
  discriminate.
Qed.

Lemma sidecar_clothoid_not_campaign_i :
  sidecar_clothoid_kind <> SCE_CampaignI.
Proof.
  discriminate.
Qed.

Lemma sidecar_clothoid_not_loop_noder :
  sidecar_clothoid_kind <> SCE_LoopNoder.
Proof.
  discriminate.
Qed.

Inductive SidecarClothoidLetterStatus : Type :=
| SidecarClothoidEggLanded
| SidecarClothoidFirstCookExpanded
| SidecarClothoidCampaignDischarged.

Definition sidecar_clothoid_letter_status : SidecarClothoidLetterStatus :=
  SidecarClothoidEggLanded.

Lemma sidecar_clothoid_letter_is_landed :
  sidecar_clothoid_letter_status = SidecarClothoidEggLanded.
Proof.
  reflexivity.
Qed.

Lemma sidecar_clothoid_not_first_cook_expanded :
  sidecar_clothoid_letter_status <> SidecarClothoidFirstCookExpanded.
Proof.
  discriminate.
Qed.

Lemma sidecar_clothoid_campaign_not_discharged :
  sidecar_clothoid_letter_status <> SidecarClothoidCampaignDischarged.
Proof.
  discriminate.
Qed.

(* Named QED package: egg + Decline-on-host + locked chord-seed. *)
Lemma sidecar_clothoid_egg_inhabits :
  egg_class (sidecar_clothoid_host_egg locked_sce_ab) = EggClothoid /\
  sidecar_clothoid_host_egg locked_sce_ab = MkOutOfScope EggClothoid /\
  I_ok (sidecar_clothoid_host_egg locked_sce_ab)
       (sidecar_clothoid_host_egg locked_sce_cd) IDecline /\
  try_cook_hit locked_clothoid_ck1 locked_clothoid_ck2 IDecline crossing_hen
    = None /\
  clothoid_chord_share locked_clothoid_ab
    (cc_start locked_clothoid_cd) (cc_end locked_clothoid_cd) /\
  I_ok (MkChord (sidecar_clothoid_demote locked_sce_ab))
       (MkChord (sidecar_clothoid_demote locked_sce_cd))
       (IHit cross_pt (1 / 2) (1 / 2)) /\
  IEmpty <> IDecline /\
  sidecar_clothoid_kind = SCE_EggPackaging.
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact sidecar_clothoid_host_decline|].
  split; [exact sidecar_clothoid_try_cook_none|].
  split; [exact sidecar_clothoid_chord_seed|].
  split; [apply sidecar_clothoid_demote_hit_not_clothoid_I_ok|].
  split; [exact sidecar_clothoid_empty_neq_decline|].
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-clothoid-egg","topic":"overlay","lemma":"ticket_0007_clothoid_egg_qed_or_qex","title":"Sidecar clothoid egg packages EggClothoid Decline-on-host and locked RelateClothoid chord-seed (QED) or host I_ok is a clothoid Hit (QEX); discharged QED; demote-to-chord is NodingNG first cook, not a clothoid times clothoid cook","file":"theories/SidecarClothoidEgg.v","witness":"0007-clothoid-egg","board":"ADR-0007"} *)
Theorem ticket_0007_clothoid_egg_qed_or_qex :
  (egg_class (sidecar_clothoid_host_egg locked_sce_ab) = EggClothoid /\
   sidecar_clothoid_host_egg locked_sce_ab = MkOutOfScope EggClothoid /\
   I_ok (sidecar_clothoid_host_egg locked_sce_ab)
        (sidecar_clothoid_host_egg locked_sce_cd) IDecline /\
   try_cook_hit locked_clothoid_ck1 locked_clothoid_ck2 IDecline crossing_hen
     = None /\
   clothoid_chord_share locked_clothoid_ab
     (cc_start locked_clothoid_cd) (cc_end locked_clothoid_cd) /\
   I_ok (MkChord (sidecar_clothoid_demote locked_sce_ab))
        (MkChord (sidecar_clothoid_demote locked_sce_cd))
        (IHit cross_pt (1 / 2) (1 / 2)) /\
   ~ I_ok (sidecar_clothoid_host_egg locked_sce_ab)
          (sidecar_clothoid_host_egg locked_sce_cd)
          (IHit cross_pt (1 / 2) (1 / 2)) /\
   IEmpty <> IDecline /\
   sidecar_clothoid_kind = SCE_EggPackaging /\
   sidecar_clothoid_kind <> SCE_HostCook /\
   sidecar_clothoid_kind <> SCE_NodingNG /\
   sidecar_clothoid_kind <> SCE_FresnelNoding)
  \/
  (exists p ti tj,
     I_ok (MkOutOfScope EggClothoid) (MkOutOfScope EggClothoid)
          (IHit p ti tj)).
Proof.
  left.
  destruct sidecar_clothoid_egg_inhabits
    as [Hcls [Htag [Hdec [Hnone [Hseed [Hdem [Hneq Hkind]]]]]]].
  split; [exact Hcls|].
  split; [exact Htag|].
  split; [exact Hdec|].
  split; [exact Hnone|].
  split; [exact Hseed|].
  split; [exact Hdem|].
  split; [apply sidecar_clothoid_host_hit_false|].
  split; [exact Hneq|].
  split; [exact Hkind|].
  split; [exact sidecar_clothoid_not_host_cook|].
  split; [exact sidecar_clothoid_not_nodingng|].
  exact sidecar_clothoid_not_fresnel_noding.
Qed.

(* WITNESS {"claimId":"0007-clothoid-egg","topic":"overlay","lemma":"ticket_0007_clothoid_not_first_cook_qed_or_qex","title":"Sidecar clothoid expands first_cook_scope to clothoid times clothoid and inhabits I_ok Hit (QED) or clothoid times clothoid stays QEX with named MkClothoid / Hit-arm gaps (QEX); discharged QEX; checklist 4; do not fake first-cook expand","file":"theories/SidecarClothoidEgg.v","witness":"0007-clothoid-egg","board":"ADR-0007"} *)
Theorem ticket_0007_clothoid_not_first_cook_qed_or_qex :
  (first_cook_scope EggClothoid EggClothoid /\
   sidecar_clothoid_ctor_inhabits ClothoidMkClothoid /\
   sidecar_clothoid_ctor_inhabits ClothoidClothoidHitArm /\
   sidecar_clothoid_ctor_inhabits ClothoidFirstCookExpand /\
   sidecar_clothoid_letter_status = SidecarClothoidFirstCookExpanded /\
   exists p ti tj,
     I_ok (MkOutOfScope EggClothoid) (MkOutOfScope EggClothoid)
          (IHit p ti tj))
  \/
  (~ first_cook_scope EggClothoid EggClothoid /\
   first_cook_scope EggChord EggChord /\
   ~ sidecar_clothoid_ctor_inhabits ClothoidMkClothoid /\
   ~ sidecar_clothoid_ctor_inhabits ClothoidClothoidHitArm /\
   ~ sidecar_clothoid_ctor_inhabits ClothoidFirstCookExpand /\
   sidecar_clothoid_letter_status = SidecarClothoidEggLanded /\
   I_ok (MkOutOfScope EggClothoid) (MkOutOfScope EggClothoid) IDecline /\
   (forall p ti tj,
      ~ I_ok (MkOutOfScope EggClothoid) (MkOutOfScope EggClothoid)
           (IHit p ti tj)) /\
   try_cook_hit clothoid_ck1 clothoid_ck2 IDecline crossing_hen = None).
Proof.
  right.
  split; [exact clothoid_clothoid_not_first_scope|].
  split; [exact first_cook_scope_chord_chord|].
  split; [exact sidecar_clothoid_mkclothoid_missing|].
  split; [exact sidecar_clothoid_hit_arm_missing|].
  split; [exact sidecar_clothoid_first_cook_expand_missing|].
  split; [exact sidecar_clothoid_letter_is_landed|].
  split; [exact clothoid_decline_I_ok|].
  split; [intros p ti tj H; exact H|].
  exact try_cook_hit_clothoid_none.
Qed.

(* WITNESS {"claimId":"0007-clothoid-egg","topic":"overlay","lemma":"ticket_0007_clothoid_parks_qed_or_qex","title":"Sidecar clothoid discharges Campaign I-II, remints Fresnel/Halley as noding, and flips LoopDischarged (QED) or names them parked and cites Parks Gamma/iota/rho once (QEX); discharged QEX; letter landed != first-cook expand / Campaign / bag noder","file":"theories/SidecarClothoidEgg.v","witness":"0007-clothoid-egg","board":"ADR-0007"} *)
Theorem ticket_0007_clothoid_parks_qed_or_qex :
  (sidecar_clothoid_letter_status = SidecarClothoidCampaignDischarged /\
   sidecar_clothoid_kind = SCE_CampaignI /\
   sidecar_clothoid_kind = SCE_FresnelNoding /\
   sidecar_clothoid_kind = SCE_LoopNoder /\
   cook_loop_status = LoopDischarged)
  \/
  (sidecar_clothoid_letter_status = SidecarClothoidEggLanded /\
   sidecar_clothoid_letter_status <> SidecarClothoidCampaignDischarged /\
   sidecar_clothoid_kind = SCE_EggPackaging /\
   sidecar_clothoid_kind <> SCE_CampaignI /\
   sidecar_clothoid_kind <> SCE_FresnelNoding /\
   sidecar_clothoid_kind <> SCE_LoopNoder /\
   cook_loop_status = LoopObligation /\
   cook_loop_status <> LoopDischarged /\
   first_cook_scope EggChord EggChord /\
   ~ first_cook_scope EggClothoid EggClothoid).
Proof.
  right.
  split; [exact sidecar_clothoid_letter_is_landed|].
  split; [exact sidecar_clothoid_campaign_not_discharged|].
  split; [exact sidecar_clothoid_is_egg_packaging|].
  split; [exact sidecar_clothoid_not_campaign_i|].
  split; [exact sidecar_clothoid_not_fresnel_noding|].
  split; [exact sidecar_clothoid_not_loop_noder|].
  split; [exact cook_loop_is_obligation|].
  split; [exact cook_loop_not_discharged|].
  split; [exact first_cook_scope_chord_chord|].
  exact clothoid_clothoid_not_first_scope.
Qed.

Print Assumptions sidecar_clothoid_class.
Print Assumptions sidecar_clothoid_host_decline.
Print Assumptions sidecar_clothoid_try_cook_none.
Print Assumptions sidecar_clothoid_chord_seed.
Print Assumptions sidecar_clothoid_demote_is_nodingng_crossing.
Print Assumptions sidecar_clothoid_residual_is_metric.
Print Assumptions sidecar_clothoid_mkclothoid_missing.
Print Assumptions sidecar_clothoid_hit_arm_missing.
Print Assumptions sidecar_clothoid_egg_inhabits.
Print Assumptions ticket_0007_clothoid_egg_qed_or_qex.
Print Assumptions ticket_0007_clothoid_not_first_cook_qed_or_qex.
Print Assumptions ticket_0007_clothoid_parks_qed_or_qex.
