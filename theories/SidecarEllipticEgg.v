(* ============================================================================
   NetTopologySuite.Proofs.SidecarEllipticEgg
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: Elliptical Curve / EllipticArc egg sidecar
   (claimId 0007-elliptical-curve-egg).

   Product / sidecar face: EggEllipse on the ADR-0007 sheet / hen /
   cook vocabulary. Host already has EggEllipse / MkOutOfScope
   EggEllipse and ellipse_ellipse_not_first_scope. SheetHenCook is
   at the module-split ceiling after Circle #720 — this letter does
   not grow it. Decline / not-first-cook / try_cook None live here
   and cite the existing first_cook_scope / I_ok /
   try_cook_hit_out_of_scope_none machinery. Prefer SidecarElliptic*
   over reminting host cook (same preference as SidecarCircEgg* /
   SidecarSin* / SidecarNurbs* / SidecarClothoid* for non-host).

   Reuse RelateEllipticArc.v EllipticArcChord the way clothoid reused
   ClothoidChord. Demote-to-chord is NodingNG / host first cook, not
   an elliptic Hit. #508 ellipse length / elliptic-E
   (EllipseLength / EllipseSpeedIntegral) stay metric — not a cook
   Hit and not EllipseLength synonym theater.

   One honest first rung. One locked fixture. Do not ship an
   elliptic×elliptic noder or Campaign I–II in this letter.

   QED: sidecar egg packaging on EggEllipse; host I_ok Decline
   and try_cook_hit None; locked unit-square EllipticArcChord
   reuse elliptic_arc_chord_proper_cross_share; demote-to-chord
   is NodingNG / host first cook, not an elliptic Hit.

   QEX: ellipse×ellipse is not first cook (checklist 4). Named
   missing constructor: no MkElliptic on Egg, no I_ok Hit arm
   on elliptic eggs, no first-cook expand. Do not fake first-cook
   expand or LoopDischarged. Do not remint EllipseLength /
   EllipseSpeedIntegral as noding.

   What this is not:
     Host first_cook_scope / try_cook_hit expand to
     ellipse×ellipse. EllipseLength / EllipseSpeedIntegral remint
     as noding. CircGamma / circular remint. MkCirc. Host circular
     cook. Shewchuk / Hobby / Priest / Jordan / HotPixel / kiss /
     ρ Discharge. SQL/MM Multi Landed / Phase B done-when / H⊥ /
     MerkatorBV / 522-n. Full elliptic noder. Campaign I–II.

   Parks Γ / ι / ρ (named QEX, landed). This letter cites them
   once; it does not remint CircGamma, ι, leftover_width, or
   LoopDischarged. First cook stays chord–chord. Host CircGamma
   stays QEX.

   ADR-0007 is Accepted (2026-09-07). This letter does not reopen
   Status. QEX is not a new Accept cycle. ADR-0006 Status stays
   Accepted. Testable 𝓘 / cook results sit on the accepted Oracle
   line protocol. This module mints no keyword and no second
   external seam.

   WITNESS topic: overlay · claimId: 0007-elliptical-curve-egg
   witness: 0007-elliptical-curve-egg
   board: ADR-0007
   3-axiom host. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import Distance SheetHenCook NodingNG RelateEllipticArc.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Product face: a sidecar elliptic egg is a named EggEllipse interpolant     *)
(* tag plus the already-Qed EllipticArcChord seed. Host Egg has no            *)
(* MkElliptic.                                                                *)
(* -------------------------------------------------------------------------- *)

Record SidecarEllipticEgg : Type := mkSidecarEllipticEgg {
  see_sheet : Sheet;
  see_chord : EllipticArcChord
}.

Definition sidecar_elliptic_host_egg (_ : SidecarEllipticEgg) : Egg :=
  MkOutOfScope EggEllipse.

Definition sidecar_elliptic_demote (e : SidecarEllipticEgg) : ChordEgg :=
  mkChordEgg (eac_start (see_chord e)) (eac_end (see_chord e)).

Definition sidecar_elliptic_chicken (src dst : Hen) (e : SidecarEllipticEgg)
  : Chicken :=
  mkChicken src dst (sidecar_elliptic_host_egg e).

Lemma sidecar_elliptic_class :
  forall e, egg_class (sidecar_elliptic_host_egg e) = EggEllipse.
Proof.
  intros e. reflexivity.
Qed.

Lemma sidecar_elliptic_only_out_of_scope :
  forall e, sidecar_elliptic_host_egg e = MkOutOfScope EggEllipse.
Proof.
  intros e. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked fixture: unit-square diagonals as EllipticArcChord. Same geometry   *)
(* as NodingNG's crossing pair — the chord seed, not an elliptic cook.        *)
(* -------------------------------------------------------------------------- *)

Definition locked_elliptic_ab : EllipticArcChord :=
  mkEllipticArcChord (ce_p0 diag_ab) (ce_p1 diag_ab).

Definition locked_elliptic_cd : EllipticArcChord :=
  mkEllipticArcChord (ce_p0 diag_cd) (ce_p1 diag_cd).

Definition locked_see_ab : SidecarEllipticEgg :=
  mkSidecarEllipticEgg default_sheet locked_elliptic_ab.

Definition locked_see_cd : SidecarEllipticEgg :=
  mkSidecarEllipticEgg default_sheet locked_elliptic_cd.

Definition locked_elliptic_ck1 : Chicken :=
  sidecar_elliptic_chicken 0%nat 1%nat locked_see_ab.

Definition locked_elliptic_ck2 : Chicken :=
  sidecar_elliptic_chicken 2%nat 3%nat locked_see_cd.

Lemma locked_elliptic_demote_is_host_crossing :
  sidecar_elliptic_demote locked_see_ab = diag_ab /\
  sidecar_elliptic_demote locked_see_cd = diag_cd.
Proof.
  split; reflexivity.
Qed.

Lemma locked_elliptic_same_sheet_as_nodingng :
  see_sheet locked_see_ab = default_sheet /\
  see_sheet locked_see_cd = nng_sheet nodingng_crossing_pair.
Proof.
  split; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Decline-on-host. Elliptic eggs stay MkOutOfScope. Not a constructed Hit.   *)
(* Lemmas live here (SheetHenCook must not grow). Cite first_cook_scope /    *)
(* I_ok / try_cook_hit — same occupants as SIN #719 sidecar copies.          *)
(* Host already has ellipse_ellipse_not_first_scope; Decline / try_cook      *)
(* None are packaged here.                                                    *)
(* -------------------------------------------------------------------------- *)

Lemma ellipse_decline_I_ok :
  I_ok (MkOutOfScope EggEllipse) (MkOutOfScope EggEllipse) IDecline.
Proof.
  unfold I_ok, first_cook_scope, egg_class.
  intro H. exact H.
Qed.

Lemma sidecar_elliptic_host_decline :
  I_ok (sidecar_elliptic_host_egg locked_see_ab)
       (sidecar_elliptic_host_egg locked_see_cd) IDecline.
Proof.
  exact ellipse_decline_I_ok.
Qed.

Lemma sidecar_elliptic_host_hit_false :
  forall p ti tj,
    ~ I_ok (sidecar_elliptic_host_egg locked_see_ab)
           (sidecar_elliptic_host_egg locked_see_cd) (IHit p ti tj).
Proof.
  intros p ti tj H. exact H.
Qed.

Lemma sidecar_elliptic_host_empty_false :
  ~ I_ok (sidecar_elliptic_host_egg locked_see_ab)
         (sidecar_elliptic_host_egg locked_see_cd) IEmpty.
Proof.
  intro H. exact H.
Qed.

Lemma sidecar_elliptic_try_cook_none :
  try_cook_hit locked_elliptic_ck1 locked_elliptic_ck2 IDecline crossing_hen
    = None.
Proof.
  reflexivity.
Qed.

Lemma sidecar_elliptic_try_cook_hit_none :
  forall p ti tj h,
    try_cook_hit locked_elliptic_ck1 locked_elliptic_ck2 (IHit p ti tj) h
      = None.
Proof.
  intros p ti tj h.
  apply try_cook_hit_out_of_scope_none.
  left. discriminate.
Qed.

Lemma sidecar_elliptic_empty_neq_decline : IEmpty <> IDecline.
Proof.
  exact IEmpty_neq_IDecline.
Qed.

(* -------------------------------------------------------------------------- *)
(* Constructive chord-seed reuse. RelateEllipticArc already Qed: an           *)
(* EllipticArcChord that properly crosses a segment shares a point. That is   *)
(* the demoted-chord geometry, not an elliptic×elliptic cook Hit.             *)
(* -------------------------------------------------------------------------- *)

Lemma locked_elliptic_chord_proper_cross :
  elliptic_arc_chord_proper_cross locked_elliptic_ab
    (eac_start locked_elliptic_cd) (eac_end locked_elliptic_cd).
Proof.
  unfold elliptic_arc_chord_proper_cross, locked_elliptic_ab, locked_elliptic_cd.
  cbn [eac_start eac_end].
  exact crossing_proper_cross_signs.
Qed.

(* WITNESS {"claimId":"0007-elliptical-curve-egg","topic":"overlay","lemma":"sidecar_elliptic_chord_seed","title":"Sidecar elliptic locked unit-square chords reuse RelateEllipticArc proper-cross share; demoted-chord geometry, not an elliptic times elliptic cook Hit","file":"theories/SidecarEllipticEgg.v","witness":"0007-elliptical-curve-egg","board":"ADR-0007"} *)
Lemma sidecar_elliptic_chord_seed :
  elliptic_arc_chord_share locked_elliptic_ab
    (eac_start locked_elliptic_cd) (eac_end locked_elliptic_cd).
Proof.
  apply elliptic_arc_chord_proper_cross_share.
  exact locked_elliptic_chord_proper_cross.
Qed.

(* Demote-to-chord inhabits host / NodingNG first cook. Not an elliptic Hit. *)
Lemma sidecar_elliptic_demote_is_nodingng_crossing :
  sidecar_elliptic_demote locked_see_ab = diag_ab /\
  sidecar_elliptic_demote locked_see_cd = diag_cd /\
  I_ok (MkChord (sidecar_elliptic_demote locked_see_ab))
       (MkChord (sidecar_elliptic_demote locked_see_cd))
       (IHit cross_pt (1 / 2) (1 / 2)) /\
  nodingng_hit_cooks nodingng_crossing_pair crossing_hen.
Proof.
  destruct locked_elliptic_demote_is_host_crossing as [Hab Hcd].
  split; [exact Hab|].
  split; [exact Hcd|].
  rewrite Hab, Hcd.
  split; [exact crossing_I_ok|].
  exact nodingng_crossing_hit_cooks.
Qed.

Lemma sidecar_elliptic_demote_hit_not_elliptic_I_ok :
  I_ok (MkChord (sidecar_elliptic_demote locked_see_ab))
       (MkChord (sidecar_elliptic_demote locked_see_cd))
       (IHit cross_pt (1 / 2) (1 / 2)) /\
  ~ I_ok (sidecar_elliptic_host_egg locked_see_ab)
         (sidecar_elliptic_host_egg locked_see_cd)
         (IHit cross_pt (1 / 2) (1 / 2)).
Proof.
  split.
  - apply sidecar_elliptic_demote_is_nodingng_crossing.
  - apply sidecar_elliptic_host_hit_false.
Qed.

(* #508 ellipse length / elliptic-E (EllipseLength.v :
   ellipse_length_sandwich, ellipse_conditional_is_curve_length;
   EllipseSpeedIntegral.v : ellipse_speed_integral_is_curve_length)
   stay metric / length research — not a cook Hit, not noding. *)
Inductive SidecarEllipticMetricKind : Type :=
| SEM_EllipseLengthE
| SEM_CookHit.

Definition sidecar_elliptic_metric_kind : SidecarEllipticMetricKind :=
  SEM_EllipseLengthE.

Lemma sidecar_elliptic_metric_is_length :
  sidecar_elliptic_metric_kind = SEM_EllipseLengthE.
Proof.
  reflexivity.
Qed.

Lemma sidecar_elliptic_metric_not_cook_hit :
  sidecar_elliptic_metric_kind <> SEM_CookHit.
Proof.
  discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* Named missing constructors. 508-style, not bools.                          *)
(* -------------------------------------------------------------------------- *)

Inductive SidecarEllipticCookCtor : Type :=
| EllipticMkElliptic
| EllipticEllipseHitArm
| EllipticFirstCookExpand.

Definition sidecar_elliptic_ctor_inhabits
  (c : SidecarEllipticCookCtor) : Prop :=
  match c with
  | EllipticMkElliptic => False
  | EllipticEllipseHitArm => False
  | EllipticFirstCookExpand => False
  end.

Lemma sidecar_elliptic_mkelliptic_missing :
  ~ sidecar_elliptic_ctor_inhabits EllipticMkElliptic.
Proof.
  intro H. exact H.
Qed.

Lemma sidecar_elliptic_hit_arm_missing :
  ~ sidecar_elliptic_ctor_inhabits EllipticEllipseHitArm.
Proof.
  intro H. exact H.
Qed.

Lemma sidecar_elliptic_first_cook_expand_missing :
  ~ sidecar_elliptic_ctor_inhabits EllipticFirstCookExpand.
Proof.
  intro H. exact H.
Qed.

Lemma sidecar_elliptic_not_first_cook :
  ~ first_cook_scope EggEllipse EggEllipse.
Proof.
  exact ellipse_ellipse_not_first_scope.
Qed.

Lemma sidecar_elliptic_first_cook_stays_chord_chord :
  first_cook_scope EggChord EggChord /\
  ~ first_cook_scope EggEllipse EggEllipse /\
  ~ first_cook_scope EggNurbs EggNurbs /\
  ~ first_cook_scope EggClothoid EggClothoid /\
  ~ first_cook_scope EggCircularArc EggCircularArc.
Proof.
  split; [exact first_cook_scope_chord_chord|].
  split; [exact ellipse_ellipse_not_first_scope|].
  split; [exact nurbs_nurbs_not_first_scope|].
  split; [exact clothoid_clothoid_not_first_scope|].
  exact circular_egg_not_first_cook_scope.
Qed.

(* -------------------------------------------------------------------------- *)
(* What the sidecar is / is not. Kind tag, not a second kernel.               *)
(* -------------------------------------------------------------------------- *)

Inductive SidecarEllipticKind : Type :=
| SEE_EggPackaging
| SEE_HostCook
| SEE_NodingNG
| SEE_EllipseLengthNoding
| SEE_CircGamma
| SEE_CampaignI
| SEE_LoopNoder.

Definition sidecar_elliptic_kind : SidecarEllipticKind := SEE_EggPackaging.

Lemma sidecar_elliptic_is_egg_packaging :
  sidecar_elliptic_kind = SEE_EggPackaging.
Proof.
  reflexivity.
Qed.

Lemma sidecar_elliptic_not_host_cook :
  sidecar_elliptic_kind <> SEE_HostCook.
Proof.
  discriminate.
Qed.

Lemma sidecar_elliptic_not_nodingng :
  sidecar_elliptic_kind <> SEE_NodingNG.
Proof.
  discriminate.
Qed.

Lemma sidecar_elliptic_not_length_noding :
  sidecar_elliptic_kind <> SEE_EllipseLengthNoding.
Proof.
  discriminate.
Qed.

Lemma sidecar_elliptic_not_circgamma :
  sidecar_elliptic_kind <> SEE_CircGamma.
Proof.
  discriminate.
Qed.

Lemma sidecar_elliptic_not_campaign_i :
  sidecar_elliptic_kind <> SEE_CampaignI.
Proof.
  discriminate.
Qed.

Lemma sidecar_elliptic_not_loop_noder :
  sidecar_elliptic_kind <> SEE_LoopNoder.
Proof.
  discriminate.
Qed.

Inductive SidecarEllipticLetterStatus : Type :=
| SidecarEllipticEggLanded
| SidecarEllipticFirstCookExpanded
| SidecarEllipticCampaignDischarged.

Definition sidecar_elliptic_letter_status : SidecarEllipticLetterStatus :=
  SidecarEllipticEggLanded.

Lemma sidecar_elliptic_letter_is_landed :
  sidecar_elliptic_letter_status = SidecarEllipticEggLanded.
Proof.
  reflexivity.
Qed.

Lemma sidecar_elliptic_not_first_cook_expanded :
  sidecar_elliptic_letter_status <> SidecarEllipticFirstCookExpanded.
Proof.
  discriminate.
Qed.

Lemma sidecar_elliptic_campaign_not_discharged :
  sidecar_elliptic_letter_status <> SidecarEllipticCampaignDischarged.
Proof.
  discriminate.
Qed.

(* Named QED package: egg + Decline-on-host + locked chord-seed. *)
Lemma sidecar_elliptic_egg_inhabits :
  egg_class (sidecar_elliptic_host_egg locked_see_ab) = EggEllipse /\
  sidecar_elliptic_host_egg locked_see_ab = MkOutOfScope EggEllipse /\
  I_ok (sidecar_elliptic_host_egg locked_see_ab)
       (sidecar_elliptic_host_egg locked_see_cd) IDecline /\
  try_cook_hit locked_elliptic_ck1 locked_elliptic_ck2 IDecline crossing_hen
    = None /\
  elliptic_arc_chord_share locked_elliptic_ab
    (eac_start locked_elliptic_cd) (eac_end locked_elliptic_cd) /\
  I_ok (MkChord (sidecar_elliptic_demote locked_see_ab))
       (MkChord (sidecar_elliptic_demote locked_see_cd))
       (IHit cross_pt (1 / 2) (1 / 2)) /\
  IEmpty <> IDecline /\
  sidecar_elliptic_kind = SEE_EggPackaging /\
  sidecar_elliptic_metric_kind = SEM_EllipseLengthE.
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact sidecar_elliptic_host_decline|].
  split; [exact sidecar_elliptic_try_cook_none|].
  split; [exact sidecar_elliptic_chord_seed|].
  split; [apply sidecar_elliptic_demote_hit_not_elliptic_I_ok|].
  split; [exact sidecar_elliptic_empty_neq_decline|].
  split; [reflexivity|].
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-elliptical-curve-egg","topic":"overlay","lemma":"ticket_0007_elliptic_egg_qed_or_qex","title":"Sidecar elliptic egg packages EggEllipse Decline-on-host and locked RelateEllipticArc chord-seed (QED) or host I_ok is an elliptic Hit (QEX); discharged QED; demote-to-chord is NodingNG first cook, not an elliptic times elliptic cook; #508 ellipse length / elliptic-E stay metric","file":"theories/SidecarEllipticEgg.v","witness":"0007-elliptical-curve-egg","board":"ADR-0007"} *)
Theorem ticket_0007_elliptic_egg_qed_or_qex :
  (egg_class (sidecar_elliptic_host_egg locked_see_ab) = EggEllipse /\
   sidecar_elliptic_host_egg locked_see_ab = MkOutOfScope EggEllipse /\
   I_ok (sidecar_elliptic_host_egg locked_see_ab)
        (sidecar_elliptic_host_egg locked_see_cd) IDecline /\
   try_cook_hit locked_elliptic_ck1 locked_elliptic_ck2 IDecline crossing_hen
     = None /\
   elliptic_arc_chord_share locked_elliptic_ab
     (eac_start locked_elliptic_cd) (eac_end locked_elliptic_cd) /\
   I_ok (MkChord (sidecar_elliptic_demote locked_see_ab))
        (MkChord (sidecar_elliptic_demote locked_see_cd))
        (IHit cross_pt (1 / 2) (1 / 2)) /\
   ~ I_ok (sidecar_elliptic_host_egg locked_see_ab)
          (sidecar_elliptic_host_egg locked_see_cd)
          (IHit cross_pt (1 / 2) (1 / 2)) /\
   IEmpty <> IDecline /\
   sidecar_elliptic_kind = SEE_EggPackaging /\
   sidecar_elliptic_kind <> SEE_HostCook /\
   sidecar_elliptic_kind <> SEE_NodingNG /\
   sidecar_elliptic_kind <> SEE_EllipseLengthNoding /\
   sidecar_elliptic_metric_kind = SEM_EllipseLengthE /\
   sidecar_elliptic_metric_kind <> SEM_CookHit)
  \/
  (exists p ti tj,
     I_ok (MkOutOfScope EggEllipse) (MkOutOfScope EggEllipse)
          (IHit p ti tj)).
Proof.
  left.
  destruct sidecar_elliptic_egg_inhabits
    as [Hcls [Htag [Hdec [Hnone [Hseed [Hdem [Hneq [Hkind Hmet]]]]]]]].
  split; [exact Hcls|].
  split; [exact Htag|].
  split; [exact Hdec|].
  split; [exact Hnone|].
  split; [exact Hseed|].
  split; [exact Hdem|].
  split; [apply sidecar_elliptic_host_hit_false|].
  split; [exact Hneq|].
  split; [exact Hkind|].
  split; [exact sidecar_elliptic_not_host_cook|].
  split; [exact sidecar_elliptic_not_nodingng|].
  split; [exact sidecar_elliptic_not_length_noding|].
  split; [exact Hmet|].
  exact sidecar_elliptic_metric_not_cook_hit.
Qed.

(* WITNESS {"claimId":"0007-elliptical-curve-egg","topic":"overlay","lemma":"ticket_0007_elliptic_not_first_cook_qed_or_qex","title":"Sidecar elliptic expands first_cook_scope to ellipse times ellipse and inhabits I_ok Hit (QED) or ellipse times ellipse stays QEX with named MkElliptic / Hit-arm gaps (QEX); discharged QEX; checklist 4; do not fake first-cook expand","file":"theories/SidecarEllipticEgg.v","witness":"0007-elliptical-curve-egg","board":"ADR-0007"} *)
Theorem ticket_0007_elliptic_not_first_cook_qed_or_qex :
  (first_cook_scope EggEllipse EggEllipse /\
   sidecar_elliptic_ctor_inhabits EllipticMkElliptic /\
   sidecar_elliptic_ctor_inhabits EllipticEllipseHitArm /\
   sidecar_elliptic_ctor_inhabits EllipticFirstCookExpand /\
   sidecar_elliptic_letter_status = SidecarEllipticFirstCookExpanded /\
   exists p ti tj,
     I_ok (MkOutOfScope EggEllipse) (MkOutOfScope EggEllipse)
          (IHit p ti tj))
  \/
  (~ first_cook_scope EggEllipse EggEllipse /\
   first_cook_scope EggChord EggChord /\
   ~ sidecar_elliptic_ctor_inhabits EllipticMkElliptic /\
   ~ sidecar_elliptic_ctor_inhabits EllipticEllipseHitArm /\
   ~ sidecar_elliptic_ctor_inhabits EllipticFirstCookExpand /\
   sidecar_elliptic_letter_status = SidecarEllipticEggLanded /\
   I_ok (MkOutOfScope EggEllipse) (MkOutOfScope EggEllipse) IDecline /\
   (forall p ti tj,
      ~ I_ok (MkOutOfScope EggEllipse) (MkOutOfScope EggEllipse)
           (IHit p ti tj)) /\
   try_cook_hit locked_elliptic_ck1 locked_elliptic_ck2 IDecline crossing_hen
     = None).
Proof.
  right.
  split; [exact ellipse_ellipse_not_first_scope|].
  split; [exact first_cook_scope_chord_chord|].
  split; [exact sidecar_elliptic_mkelliptic_missing|].
  split; [exact sidecar_elliptic_hit_arm_missing|].
  split; [exact sidecar_elliptic_first_cook_expand_missing|].
  split; [exact sidecar_elliptic_letter_is_landed|].
  split; [exact ellipse_decline_I_ok|].
  split; [intros p ti tj H; exact H|].
  exact sidecar_elliptic_try_cook_none.
Qed.

(* WITNESS {"claimId":"0007-elliptical-curve-egg","topic":"overlay","lemma":"ticket_0007_elliptic_parks_qed_or_qex","title":"Sidecar elliptic discharges Campaign I-II, remints EllipseLength/elliptic-E as noding, remints CircGamma, and flips LoopDischarged (QED) or names them parked and cites Parks Gamma/iota/rho once (QEX); discharged QEX; letter landed != first-cook expand / Campaign / bag noder","file":"theories/SidecarEllipticEgg.v","witness":"0007-elliptical-curve-egg","board":"ADR-0007"} *)
Theorem ticket_0007_elliptic_parks_qed_or_qex :
  (sidecar_elliptic_letter_status = SidecarEllipticCampaignDischarged /\
   sidecar_elliptic_kind = SEE_CampaignI /\
   sidecar_elliptic_kind = SEE_EllipseLengthNoding /\
   sidecar_elliptic_kind = SEE_CircGamma /\
   sidecar_elliptic_kind = SEE_LoopNoder /\
   cook_loop_status = LoopDischarged)
  \/
  (sidecar_elliptic_letter_status = SidecarEllipticEggLanded /\
   sidecar_elliptic_letter_status <> SidecarEllipticCampaignDischarged /\
   sidecar_elliptic_kind = SEE_EggPackaging /\
   sidecar_elliptic_kind <> SEE_CampaignI /\
   sidecar_elliptic_kind <> SEE_EllipseLengthNoding /\
   sidecar_elliptic_kind <> SEE_CircGamma /\
   sidecar_elliptic_kind <> SEE_LoopNoder /\
   cook_loop_status = LoopObligation /\
   cook_loop_status <> LoopDischarged /\
   first_cook_scope EggChord EggChord /\
   ~ first_cook_scope EggEllipse EggEllipse).
Proof.
  right.
  split; [exact sidecar_elliptic_letter_is_landed|].
  split; [exact sidecar_elliptic_campaign_not_discharged|].
  split; [exact sidecar_elliptic_is_egg_packaging|].
  split; [exact sidecar_elliptic_not_campaign_i|].
  split; [exact sidecar_elliptic_not_length_noding|].
  split; [exact sidecar_elliptic_not_circgamma|].
  split; [exact sidecar_elliptic_not_loop_noder|].
  split; [exact cook_loop_is_obligation|].
  split; [exact cook_loop_not_discharged|].
  split; [exact first_cook_scope_chord_chord|].
  exact ellipse_ellipse_not_first_scope.
Qed.

Print Assumptions sidecar_elliptic_class.
Print Assumptions sidecar_elliptic_host_decline.
Print Assumptions sidecar_elliptic_try_cook_none.
Print Assumptions sidecar_elliptic_chord_seed.
Print Assumptions sidecar_elliptic_demote_is_nodingng_crossing.
Print Assumptions sidecar_elliptic_metric_not_cook_hit.
Print Assumptions sidecar_elliptic_mkelliptic_missing.
Print Assumptions sidecar_elliptic_hit_arm_missing.
Print Assumptions sidecar_elliptic_egg_inhabits.
Print Assumptions ticket_0007_elliptic_egg_qed_or_qex.
Print Assumptions ticket_0007_elliptic_not_first_cook_qed_or_qex.
Print Assumptions ticket_0007_elliptic_parks_qed_or_qex.
