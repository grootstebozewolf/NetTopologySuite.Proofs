(* ============================================================================
   NetTopologySuite.Proofs.SidecarCircEgg
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: circle / circular egg sidecar
   (claimId 0007-circle-egg).

   Product / sidecar face: EggCircularArc on the ADR-0007 sheet /
   hen / cook vocabulary. Host already has EggCircularArc /
   MkOutOfScope EggCircularArc, circular_decline_I_ok,
   circular_egg_first_cook_scope, try_cook_hit_circular_hit_none,
   circular_hit_not_I_ok, chord_circular_decline_I_ok. This letter
   packages that already-Qed Decline fence. SheetHenCook is at the
   module-split ceiling after SIN #719 — this letter does not grow
   it. New lemmas live here.

   Prefer SidecarCircEgg* over reminting CircularCook* Campaign I/II,
   Parks Γ CircGamma, MkCirc, or ι/ρ. Sidecar I_ok_circ / I_ok_mixed
   Hit is not host I_ok. Host first cook stays chord–chord.

   QED: sidecar egg packaging on EggCircularArc; host I_ok Decline
   and try_cook_hit None (even on IHit); locked unit-square circular
   chords demote to the host crossing pair; demote-to-chord is
   NodingNG / host first cook, not a circular Hit. Chord × circular
   Decline is the honest host mixed arm.

   QEX: circular×circular is not first cook (checklist 4). Named
   missing constructors: no MkCirc on Egg (Parks Γ), CircGamma
   stays QEX (cite Parks Γ — do not fake Discharge), no host I_ok
   Hit arm, no first-cook expand. Do not remint CircGammaConstructor
   / CircGammaStatus / CircularCookHit/Split/Span/OkCirc.

   What this is not:
     CircGamma discharge / MkCirc on Egg. Host try_cook_hit expand
     to circular. Remint of CircularCookHit / Split / Span /
     OkCirc / I_ok_circ / Campaign I–II. ι / ρ remint. Shewchuk /
     Hobby / HotPixel / kiss procedure. SQL/MM cathedral / H⊥ /
     MerkatorBV / 522-n. Full circular noder. Bag-loop ρ Discharge.

   Parks Γ / ι / ρ (named QEX, landed). This letter cites them
   once; it does not remint CircGamma, ι, leftover_width, or
   LoopDischarged. First cook stays chord–chord. Host CircGamma
   stays QEX.

   ADR-0007 is Accepted (2026-09-07). This letter does not reopen
   Status. QEX is not a new Accept cycle. ADR-0006 Status stays
   Accepted. Testable 𝓘 / cook results sit on the accepted Oracle
   line protocol. This module mints no keyword and no second
   external seam.

   WITNESS topic: overlay · claimId: 0007-circle-egg
   witness: 0007-circle-egg
   board: ADR-0007
   3-axiom host. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import Distance SheetHenCook NodingNG RelateLineLine.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Product face: a sidecar circular egg is a named EggCircularArc             *)
(* interpolant tag plus a start/end chord seed. Host Egg has no MkCirc.       *)
(* The seed is demote-to-chord packaging, not host CircGamma.                 *)
(* -------------------------------------------------------------------------- *)

Record CircChord : Type := mkCircChord {
  crc_start : Point;
  crc_end   : Point
}.

Record SidecarCircEgg : Type := mkSidecarCircEgg {
  cce_sheet : Sheet;
  cce_chord : CircChord
}.

Definition sidecar_circ_egg_host_egg (_ : SidecarCircEgg) : Egg :=
  MkOutOfScope EggCircularArc.

Definition sidecar_circ_egg_demote (e : SidecarCircEgg) : ChordEgg :=
  mkChordEgg (crc_start (cce_chord e)) (crc_end (cce_chord e)).

Definition sidecar_circ_egg_chicken (src dst : Hen) (e : SidecarCircEgg)
  : Chicken :=
  mkChicken src dst (sidecar_circ_egg_host_egg e).

Definition circ_chord_proper_cross (c : CircChord) (P Q : Point) : Prop :=
  segments_proper_cross (crc_start c) (crc_end c) P Q.

Definition circ_chord_share (c : CircChord) (P Q : Point) : Prop :=
  segments_share (crc_start c) (crc_end c) P Q.

Lemma sidecar_circ_egg_class :
  forall e, egg_class (sidecar_circ_egg_host_egg e) = EggCircularArc.
Proof.
  intros e. reflexivity.
Qed.

Lemma sidecar_circ_egg_only_out_of_scope :
  forall e, sidecar_circ_egg_host_egg e = MkOutOfScope EggCircularArc.
Proof.
  intros e. reflexivity.
Qed.

(* Sidecar CircEgg is not a host Egg constructor. Host circular
   interpolants are MkCirc; CircularArc may also appear as a tag.
   Sidecar CircEggMkCirc / CircEggCircGamma stay uninhabited — this
   letter does not remint sidecar as host Γ. *)
Lemma sidecar_circ_egg_host_only_out_of_scope :
  forall e : Egg,
    egg_class e = EggCircularArc ->
    (exists ce, e = MkCirc ce) \/ e = MkOutOfScope EggCircularArc.
Proof.
  intros e He.
  destruct e as [c | ce | clth | cl].
  - unfold egg_class in He. discriminate.
  - left. exists ce. reflexivity.
  - unfold egg_class in He. discriminate.
  - unfold egg_class in He. subst cl. right. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked fixture: unit-square diagonals as circular start/end. Same          *)
(* geometry as NodingNG's crossing pair — the demoted chord seed, not a       *)
(* circular cook and not CircGamma.                                           *)
(* -------------------------------------------------------------------------- *)

Definition locked_circ_ab : CircChord :=
  mkCircChord (ce_p0 diag_ab) (ce_p1 diag_ab).

Definition locked_circ_cd : CircChord :=
  mkCircChord (ce_p0 diag_cd) (ce_p1 diag_cd).

Definition locked_cce_ab : SidecarCircEgg :=
  mkSidecarCircEgg default_sheet locked_circ_ab.

Definition locked_cce_cd : SidecarCircEgg :=
  mkSidecarCircEgg default_sheet locked_circ_cd.

Definition locked_circ_ck1 : Chicken :=
  sidecar_circ_egg_chicken 0%nat 1%nat locked_cce_ab.

Definition locked_circ_ck2 : Chicken :=
  sidecar_circ_egg_chicken 2%nat 3%nat locked_cce_cd.

Lemma locked_circ_demote_is_host_crossing :
  sidecar_circ_egg_demote locked_cce_ab = diag_ab /\
  sidecar_circ_egg_demote locked_cce_cd = diag_cd.
Proof.
  split; reflexivity.
Qed.

Lemma locked_circ_same_sheet_as_nodingng :
  cce_sheet locked_cce_ab = default_sheet /\
  cce_sheet locked_cce_cd = nng_sheet nodingng_crossing_pair.
Proof.
  split; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Decline-on-host. Circular eggs stay MkOutOfScope. Not a constructed Hit.   *)
(* Lemmas live here (SheetHenCook must not grow). Cite the already-Qed host   *)
(* circular_decline_I_ok / circular_egg_first_cook_scope /                    *)
(* try_cook_hit_circular_hit_none / chord_circular_decline_I_ok fence.        *)
(* -------------------------------------------------------------------------- *)

Lemma sidecar_circ_egg_host_decline :
  I_ok (sidecar_circ_egg_host_egg locked_cce_ab)
       (sidecar_circ_egg_host_egg locked_cce_cd) IDecline.
Proof.
  exact circular_decline_I_ok.
Qed.

Lemma sidecar_circ_egg_host_hit_false :
  forall p ti tj,
    ~ I_ok (sidecar_circ_egg_host_egg locked_cce_ab)
           (sidecar_circ_egg_host_egg locked_cce_cd) (IHit p ti tj).
Proof.
  intros p ti tj.
  exact (circular_hit_not_I_ok p ti tj).
Qed.

Lemma sidecar_circ_egg_host_empty_false :
  ~ I_ok (sidecar_circ_egg_host_egg locked_cce_ab)
         (sidecar_circ_egg_host_egg locked_cce_cd) IEmpty.
Proof.
  exact circular_empty_not_I_ok.
Qed.

Lemma sidecar_circ_egg_try_cook_none :
  try_cook_hit locked_circ_ck1 locked_circ_ck2 IDecline crossing_hen
    = None.
Proof.
  reflexivity.
Qed.

Lemma sidecar_circ_egg_try_cook_hit_none :
  forall p ti tj h,
    try_cook_hit locked_circ_ck1 locked_circ_ck2 (IHit p ti tj) h
      = None.
Proof.
  intros p ti tj h.
  reflexivity.
Qed.

(* Host circular IHit still does not feed try_cook_hit. *)
Lemma sidecar_circ_egg_host_try_cook_circular_hit_none :
  forall p ti tj h,
    try_cook_hit circular_ck1 circular_ck2 (IHit p ti tj) h = None.
Proof.
  exact try_cook_hit_circular_hit_none.
Qed.

Lemma sidecar_circ_egg_empty_neq_decline : IEmpty <> IDecline.
Proof.
  exact IEmpty_neq_IDecline.
Qed.

(* I.1 mixed arm: chord × circular is Decline, not a constructed Hit. *)
Lemma sidecar_circ_egg_chord_circ_decline :
  I_ok (MkChord hor_bot) (sidecar_circ_egg_host_egg locked_cce_cd) IDecline.
Proof.
  exact chord_circular_decline_I_ok.
Qed.

Lemma sidecar_circ_egg_chord_circ_hit_false :
  forall p ti tj,
    ~ I_ok (MkChord hor_bot) (sidecar_circ_egg_host_egg locked_cce_cd)
         (IHit p ti tj).
Proof.
  intros p ti tj.
  exact (chord_circular_hit_not_I_ok p ti tj).
Qed.

Lemma sidecar_circ_egg_demote_chord_circ_decline :
  I_ok (MkChord (sidecar_circ_egg_demote locked_cce_ab))
       (sidecar_circ_egg_host_egg locked_cce_cd) IDecline.
Proof.
  unfold sidecar_circ_egg_host_egg, sidecar_circ_egg_demote.
  unfold I_ok, first_cook_scope, egg_class.
  intro H. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* Constructive chord-seed. Demoted start/end properly cross and share        *)
(* a point. That is the demoted-chord geometry, not a circular×circular       *)
(* cook Hit and not CircGamma. Reuses RelateLineLine.                         *)
(* -------------------------------------------------------------------------- *)

Lemma locked_circ_chord_proper_cross :
  circ_chord_proper_cross locked_circ_ab
    (crc_start locked_circ_cd) (crc_end locked_circ_cd).
Proof.
  unfold circ_chord_proper_cross, locked_circ_ab, locked_circ_cd.
  cbn [crc_start crc_end].
  exact crossing_proper_cross_signs.
Qed.

(* WITNESS {"claimId":"0007-circle-egg","topic":"overlay","lemma":"sidecar_circ_egg_chord_seed","title":"Sidecar circular locked unit-square chords reuse line-line proper-cross share; demoted-chord geometry, not a circular times circular cook Hit and not CircGamma","file":"theories/SidecarCircEgg.v","witness":"0007-circle-egg","board":"ADR-0007"} *)
Lemma sidecar_circ_egg_chord_seed :
  circ_chord_share locked_circ_ab
    (crc_start locked_circ_cd) (crc_end locked_circ_cd).
Proof.
  unfold circ_chord_share, circ_chord_proper_cross in *.
  eapply line_line_proper_cross_geom.
  exact locked_circ_chord_proper_cross.
Qed.

(* Demote-to-chord inhabits host / NodingNG first cook. Not a circular Hit. *)
Lemma sidecar_circ_egg_demote_is_nodingng_crossing :
  sidecar_circ_egg_demote locked_cce_ab = diag_ab /\
  sidecar_circ_egg_demote locked_cce_cd = diag_cd /\
  I_ok (MkChord (sidecar_circ_egg_demote locked_cce_ab))
       (MkChord (sidecar_circ_egg_demote locked_cce_cd))
       (IHit cross_pt (1 / 2) (1 / 2)) /\
  nodingng_hit_cooks nodingng_crossing_pair crossing_hen.
Proof.
  destruct locked_circ_demote_is_host_crossing as [Hab Hcd].
  split; [exact Hab|].
  split; [exact Hcd|].
  rewrite Hab, Hcd.
  split; [exact crossing_I_ok|].
  exact nodingng_crossing_hit_cooks.
Qed.

Lemma sidecar_circ_egg_demote_hit_not_circ_I_ok :
  I_ok (MkChord (sidecar_circ_egg_demote locked_cce_ab))
       (MkChord (sidecar_circ_egg_demote locked_cce_cd))
       (IHit cross_pt (1 / 2) (1 / 2)) /\
  ~ I_ok (sidecar_circ_egg_host_egg locked_cce_ab)
         (sidecar_circ_egg_host_egg locked_cce_cd)
         (IHit cross_pt (1 / 2) (1 / 2)).
Proof.
  split.
  - apply sidecar_circ_egg_demote_is_nodingng_crossing.
  - apply sidecar_circ_egg_host_hit_false.
Qed.

(* Campaign I/II circular corpus is already Qed on the sidecar cook
   stack. This letter packages host Decline — it does not remint
   CircularCookHit / Split / Span / OkCirc / I_ok_circ as host cook. *)
Inductive SidecarCircEggCampaignKind : Type :=
| CCEM_HostDeclineFence
| CCEM_CampaignHit.

Definition sidecar_circ_egg_campaign_kind : SidecarCircEggCampaignKind :=
  CCEM_HostDeclineFence.

Lemma sidecar_circ_egg_campaign_is_host_decline :
  sidecar_circ_egg_campaign_kind = CCEM_HostDeclineFence.
Proof.
  reflexivity.
Qed.

Lemma sidecar_circ_egg_campaign_not_hit :
  sidecar_circ_egg_campaign_kind <> CCEM_CampaignHit.
Proof.
  discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* Named missing constructors. 508-style, not bools. Cite Parks Γ.            *)
(* CircEggMkCirc / CircEggCircGamma cite CircularCook.v :                      *)
(* circ_gamma_mkcirc_inhabits / circular_gamma_is_discharged — they do not    *)
(* remint sidecar CircEgg as host CircGammaConstructor.                       *)
(* -------------------------------------------------------------------------- *)

Inductive SidecarCircEggCookCtor : Type :=
| CircEggMkCirc
| CircEggCircGamma
| CircEggHostHitArm
| CircEggFirstCookExpand.

Definition sidecar_circ_egg_ctor_inhabits
  (c : SidecarCircEggCookCtor) : Prop :=
  match c with
  | CircEggMkCirc => False
  | CircEggCircGamma => False
  | CircEggHostHitArm => False
  | CircEggFirstCookExpand => False
  end.

Lemma sidecar_circ_egg_mkcirc_missing :
  ~ sidecar_circ_egg_ctor_inhabits CircEggMkCirc.
Proof.
  intro H. exact H.
Qed.

Lemma sidecar_circ_egg_circgamma_missing :
  ~ sidecar_circ_egg_ctor_inhabits CircEggCircGamma.
Proof.
  intro H. exact H.
Qed.

Lemma sidecar_circ_egg_hit_arm_missing :
  ~ sidecar_circ_egg_ctor_inhabits CircEggHostHitArm.
Proof.
  intro H. exact H.
Qed.

Lemma sidecar_circ_egg_first_cook_expand_missing :
  ~ sidecar_circ_egg_ctor_inhabits CircEggFirstCookExpand.
Proof.
  intro H. exact H.
Qed.

Lemma sidecar_circ_egg_not_first_cook :
  first_cook_scope EggCircularArc EggCircularArc.
Proof.
  exact circular_egg_first_cook_scope.
Qed.

Lemma sidecar_circ_egg_first_cook_stays_chord_chord :
  first_cook_scope EggChord EggChord /\
  first_cook_scope EggCircularArc EggCircularArc /\
  ~ first_cook_scope EggChord EggCircularArc /\
  ~ first_cook_scope EggClothoid EggClothoid /\
  ~ first_cook_scope EggNurbs EggNurbs.
Proof.
  split; [exact first_cook_scope_chord_chord|].
  split; [exact circular_egg_first_cook_scope|].
  split; [exact chord_circular_not_first_cook_scope|].
  split; [exact clothoid_clothoid_not_first_scope|].
  exact nurbs_nurbs_not_first_scope.
Qed.

(* -------------------------------------------------------------------------- *)
(* What the sidecar is / is not. Kind tag, not a second kernel.               *)
(* -------------------------------------------------------------------------- *)

Inductive SidecarCircEggKind : Type :=
| CCE_EggPackaging
| CCE_HostCook
| CCE_NodingNG
| CCE_CircGammaDischarge
| CCE_CampaignI
| CCE_LoopNoder.

Definition sidecar_circ_egg_kind : SidecarCircEggKind := CCE_EggPackaging.

Lemma sidecar_circ_egg_is_egg_packaging :
  sidecar_circ_egg_kind = CCE_EggPackaging.
Proof.
  reflexivity.
Qed.

Lemma sidecar_circ_egg_not_host_cook :
  sidecar_circ_egg_kind <> CCE_HostCook.
Proof.
  discriminate.
Qed.

Lemma sidecar_circ_egg_not_nodingng :
  sidecar_circ_egg_kind <> CCE_NodingNG.
Proof.
  discriminate.
Qed.

Lemma sidecar_circ_egg_not_circgamma_discharge :
  sidecar_circ_egg_kind <> CCE_CircGammaDischarge.
Proof.
  discriminate.
Qed.

Lemma sidecar_circ_egg_not_campaign_i :
  sidecar_circ_egg_kind <> CCE_CampaignI.
Proof.
  discriminate.
Qed.

Lemma sidecar_circ_egg_not_loop_noder :
  sidecar_circ_egg_kind <> CCE_LoopNoder.
Proof.
  discriminate.
Qed.

Inductive SidecarCircEggLetterStatus : Type :=
| SidecarCircEggLanded
| SidecarCircEggFirstCookExpanded
| SidecarCircEggCircGammaDischarged.

Definition sidecar_circ_egg_letter_status : SidecarCircEggLetterStatus :=
  SidecarCircEggLanded.

Lemma sidecar_circ_egg_letter_is_landed :
  sidecar_circ_egg_letter_status = SidecarCircEggLanded.
Proof.
  reflexivity.
Qed.

Lemma sidecar_circ_egg_not_first_cook_expanded :
  sidecar_circ_egg_letter_status <> SidecarCircEggFirstCookExpanded.
Proof.
  discriminate.
Qed.

Lemma sidecar_circ_egg_circgamma_not_discharged :
  sidecar_circ_egg_letter_status <> SidecarCircEggCircGammaDischarged.
Proof.
  discriminate.
Qed.

(* Named QED package: egg + Decline-on-host + locked chord-seed. *)
Lemma sidecar_circ_egg_inhabits :
  egg_class (sidecar_circ_egg_host_egg locked_cce_ab) = EggCircularArc /\
  sidecar_circ_egg_host_egg locked_cce_ab = MkOutOfScope EggCircularArc /\
  I_ok (sidecar_circ_egg_host_egg locked_cce_ab)
       (sidecar_circ_egg_host_egg locked_cce_cd) IDecline /\
  try_cook_hit locked_circ_ck1 locked_circ_ck2 IDecline crossing_hen
    = None /\
  (forall p ti tj h,
     try_cook_hit locked_circ_ck1 locked_circ_ck2 (IHit p ti tj) h
       = None) /\
  I_ok (MkChord hor_bot) (sidecar_circ_egg_host_egg locked_cce_cd) IDecline /\
  circ_chord_share locked_circ_ab
    (crc_start locked_circ_cd) (crc_end locked_circ_cd) /\
  I_ok (MkChord (sidecar_circ_egg_demote locked_cce_ab))
       (MkChord (sidecar_circ_egg_demote locked_cce_cd))
       (IHit cross_pt (1 / 2) (1 / 2)) /\
  IEmpty <> IDecline /\
  sidecar_circ_egg_kind = CCE_EggPackaging /\
  sidecar_circ_egg_campaign_kind = CCEM_HostDeclineFence.
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact sidecar_circ_egg_host_decline|].
  split; [exact sidecar_circ_egg_try_cook_none|].
  split; [exact sidecar_circ_egg_try_cook_hit_none|].
  split; [exact sidecar_circ_egg_chord_circ_decline|].
  split; [exact sidecar_circ_egg_chord_seed|].
  split; [apply sidecar_circ_egg_demote_hit_not_circ_I_ok|].
  split; [exact sidecar_circ_egg_empty_neq_decline|].
  split; [reflexivity|].
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-circle-egg","topic":"overlay","lemma":"ticket_0007_circle_egg_qed_or_qex","title":"Sidecar circular egg packages EggCircularArc host Decline fence and locked demoted-chord seed (QED) or host I_ok is a circular Hit (QEX); discharged QED; demote-to-chord is NodingNG first cook, not a circular times circular cook; try_cook_hit stays None even on IHit","file":"theories/SidecarCircEgg.v","witness":"0007-circle-egg","board":"ADR-0007"} *)
Theorem ticket_0007_circle_egg_qed_or_qex :
  (egg_class (sidecar_circ_egg_host_egg locked_cce_ab) = EggCircularArc /\
   sidecar_circ_egg_host_egg locked_cce_ab = MkOutOfScope EggCircularArc /\
   I_ok (sidecar_circ_egg_host_egg locked_cce_ab)
        (sidecar_circ_egg_host_egg locked_cce_cd) IDecline /\
   try_cook_hit locked_circ_ck1 locked_circ_ck2 IDecline crossing_hen
     = None /\
   (forall p ti tj h,
      try_cook_hit locked_circ_ck1 locked_circ_ck2 (IHit p ti tj) h
        = None) /\
   I_ok (MkChord hor_bot) (sidecar_circ_egg_host_egg locked_cce_cd) IDecline /\
   circ_chord_share locked_circ_ab
     (crc_start locked_circ_cd) (crc_end locked_circ_cd) /\
   I_ok (MkChord (sidecar_circ_egg_demote locked_cce_ab))
        (MkChord (sidecar_circ_egg_demote locked_cce_cd))
        (IHit cross_pt (1 / 2) (1 / 2)) /\
   ~ I_ok (sidecar_circ_egg_host_egg locked_cce_ab)
          (sidecar_circ_egg_host_egg locked_cce_cd)
          (IHit cross_pt (1 / 2) (1 / 2)) /\
   IEmpty <> IDecline /\
   sidecar_circ_egg_kind = CCE_EggPackaging /\
   sidecar_circ_egg_kind <> CCE_HostCook /\
   sidecar_circ_egg_kind <> CCE_NodingNG /\
   sidecar_circ_egg_kind <> CCE_CircGammaDischarge /\
   sidecar_circ_egg_campaign_kind = CCEM_HostDeclineFence /\
   sidecar_circ_egg_campaign_kind <> CCEM_CampaignHit)
  \/
  (exists p ti tj,
     I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
          (IHit p ti tj)).
Proof.
  left.
  destruct sidecar_circ_egg_inhabits
    as [Hcls [Htag [Hdec [Hnone [Hhitn [Hmix [Hseed [Hdem [Hneq [Hkind Hcamp]]]]]]]]]].
  split; [exact Hcls|].
  split; [exact Htag|].
  split; [exact Hdec|].
  split; [exact Hnone|].
  split; [exact Hhitn|].
  split; [exact Hmix|].
  split; [exact Hseed|].
  split; [exact Hdem|].
  split; [apply sidecar_circ_egg_host_hit_false|].
  split; [exact Hneq|].
  split; [exact Hkind|].
  split; [exact sidecar_circ_egg_not_host_cook|].
  split; [exact sidecar_circ_egg_not_nodingng|].
  split; [exact sidecar_circ_egg_not_circgamma_discharge|].
  split; [exact Hcamp|].
  exact sidecar_circ_egg_campaign_not_hit.
Qed.

(* WITNESS {"claimId":"0007-circle-egg","topic":"overlay","lemma":"ticket_0007_circle_not_first_cook_qed_or_qex","title":"Sidecar circular expands first_cook_scope to circular times circular, inhabits host I_ok Hit, and discharges CircGamma / MkCirc (QED) or circular times circular stays QEX with named MkCirc / CircGamma / Hit-arm / first-cook-expand gaps citing Parks Gamma (QEX); discharged QEX; do not fake CircGamma Discharge","file":"theories/SidecarCircEgg.v","witness":"0007-circle-egg","board":"ADR-0007"} *)
Theorem ticket_0007_circle_not_first_cook_qed_or_qex :
  (first_cook_scope EggCircularArc EggCircularArc /\
   sidecar_circ_egg_ctor_inhabits CircEggMkCirc /\
   sidecar_circ_egg_ctor_inhabits CircEggCircGamma /\
   sidecar_circ_egg_ctor_inhabits CircEggHostHitArm /\
   sidecar_circ_egg_ctor_inhabits CircEggFirstCookExpand /\
   sidecar_circ_egg_letter_status = SidecarCircEggFirstCookExpanded /\
   sidecar_circ_egg_letter_status = SidecarCircEggCircGammaDischarged /\
   exists p ti tj,
     I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
          (IHit p ti tj))
  \/
  (first_cook_scope EggCircularArc EggCircularArc /\
   first_cook_scope EggChord EggChord /\
   ~ sidecar_circ_egg_ctor_inhabits CircEggMkCirc /\
   ~ sidecar_circ_egg_ctor_inhabits CircEggCircGamma /\
   ~ sidecar_circ_egg_ctor_inhabits CircEggHostHitArm /\
   ~ sidecar_circ_egg_ctor_inhabits CircEggFirstCookExpand /\
   sidecar_circ_egg_letter_status = SidecarCircEggLanded /\
   I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc) IDecline /\
   (forall p ti tj,
      ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
           (IHit p ti tj)) /\
   try_cook_hit circular_ck1 circular_ck2 IDecline crossing_hen = None /\
   (forall p ti tj h,
      try_cook_hit circular_ck1 circular_ck2 (IHit p ti tj) h = None)).
Proof.
  right.
  split; [exact circular_egg_first_cook_scope|].
  split; [exact first_cook_scope_chord_chord|].
  split; [exact sidecar_circ_egg_mkcirc_missing|].
  split; [exact sidecar_circ_egg_circgamma_missing|].
  split; [exact sidecar_circ_egg_hit_arm_missing|].
  split; [exact sidecar_circ_egg_first_cook_expand_missing|].
  split; [exact sidecar_circ_egg_letter_is_landed|].
  split; [exact circular_decline_I_ok|].
  split; [intros p ti tj; exact (circular_hit_not_I_ok p ti tj)|].
  split; [reflexivity|].
  exact try_cook_hit_circular_hit_none.
Qed.

(* WITNESS {"claimId":"0007-circle-egg","topic":"overlay","lemma":"ticket_0007_circle_parks_qed_or_qex","title":"Sidecar circular discharges CircGamma, remints CircularCook Campaign I-II as host cook, and flips LoopDischarged (QED) or names them parked and cites Parks Gamma/iota/rho once (QEX); discharged QEX; letter landed != CircGamma Discharge / Campaign remint / bag noder","file":"theories/SidecarCircEgg.v","witness":"0007-circle-egg","board":"ADR-0007"} *)
Theorem ticket_0007_circle_parks_qed_or_qex :
  (sidecar_circ_egg_letter_status = SidecarCircEggCircGammaDischarged /\
   sidecar_circ_egg_kind = CCE_CampaignI /\
   sidecar_circ_egg_kind = CCE_CircGammaDischarge /\
   sidecar_circ_egg_kind = CCE_LoopNoder /\
   cook_loop_status = LoopDischarged)
  \/
  (sidecar_circ_egg_letter_status = SidecarCircEggLanded /\
   sidecar_circ_egg_letter_status <> SidecarCircEggCircGammaDischarged /\
   sidecar_circ_egg_kind = CCE_EggPackaging /\
   sidecar_circ_egg_kind <> CCE_CampaignI /\
   sidecar_circ_egg_kind <> CCE_CircGammaDischarge /\
   sidecar_circ_egg_kind <> CCE_LoopNoder /\
   cook_loop_status = LoopObligation /\
   cook_loop_status <> LoopDischarged /\
   first_cook_scope EggChord EggChord /\
   first_cook_scope EggCircularArc EggCircularArc).
Proof.
  right.
  split; [exact sidecar_circ_egg_letter_is_landed|].
  split; [exact sidecar_circ_egg_circgamma_not_discharged|].
  split; [exact sidecar_circ_egg_is_egg_packaging|].
  split; [exact sidecar_circ_egg_not_campaign_i|].
  split; [exact sidecar_circ_egg_not_circgamma_discharge|].
  split; [exact sidecar_circ_egg_not_loop_noder|].
  split; [exact cook_loop_is_obligation|].
  split; [exact cook_loop_not_discharged|].
  split; [exact first_cook_scope_chord_chord|].
  exact circular_egg_first_cook_scope.
Qed.

Print Assumptions sidecar_circ_egg_class.
Print Assumptions sidecar_circ_egg_host_decline.
Print Assumptions sidecar_circ_egg_try_cook_none.
Print Assumptions sidecar_circ_egg_host_try_cook_circular_hit_none.
Print Assumptions sidecar_circ_egg_chord_circ_decline.
Print Assumptions sidecar_circ_egg_chord_seed.
Print Assumptions sidecar_circ_egg_demote_is_nodingng_crossing.
Print Assumptions sidecar_circ_egg_mkcirc_missing.
Print Assumptions sidecar_circ_egg_circgamma_missing.
Print Assumptions sidecar_circ_egg_hit_arm_missing.
Print Assumptions sidecar_circ_egg_inhabits.
Print Assumptions ticket_0007_circle_egg_qed_or_qex.
Print Assumptions ticket_0007_circle_not_first_cook_qed_or_qex.
Print Assumptions ticket_0007_circle_parks_qed_or_qex.
