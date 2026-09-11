(* ============================================================================
   NetTopologySuite.Proofs.SidecarSinEgg
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: SIN / sinusoid egg sidecar
   (claimId 0007-sin-egg).

   Product / sidecar face: sinusoid as an EggClass on the ADR-0007
   sheet / hen / cook vocabulary. Host already has EggSinusoid /
   MkOutOfScope EggSinusoid. SheetHenCook is at the module-split
   ceiling after NURBS #718 — this letter does not grow it.
   Decline / not-first-cook / try_cook None live here and cite the
   existing first_cook_scope / I_ok / try_cook_hit_out_of_scope_none
   machinery, plus one locked demoted-chord fixture. Prefer
   SidecarSin* over reminting host cook (same preference as
   SidecarNurbs* / SidecarClothoid* / SidecarCirc* for non-host).

   The existing sinusoid corpus is thin versus clothoid / NURBS
   (SpectreCurvedEdge sine_profile / sine_edge is profile research,
   not a cook interpolant). This letter does NOT invent a heavy
   metric remint. Packaging + Decline + named QEX + one reusable
   locked demote-to-chord / chord-seed fixture is the letter.

   One honest first rung. One locked fixture. Do not ship a
   sinusoid×sinusoid noder or Campaign I–II in this letter.

   QED: sidecar egg packaging on EggSinusoid; host I_ok Decline
   and try_cook_hit None; locked unit-square sinusoid chords
   demote to the host crossing pair; demote-to-chord is NodingNG /
   host first cook, not a sinusoid Hit.

   QEX: sinusoid×sinusoid is not first cook (checklist 4). Named
   missing constructor: no MkSinusoid on Egg, no I_ok Hit arm
   on sinusoid eggs. Do not fake first-cook expand or
   LoopDischarged. Do not remint Spectre sine_profile as cook Hit.

   What this is not:
     Host first_cook_scope / try_cook_hit expand to
     sinusoid×sinusoid. CircGamma / ι / ρ remint. MkCirc.
     Clothoid / NURBS remint. Host circular cook. Shewchuk /
     Hobby / Priest / Jordan / HotPixel / OverlayNG snap remint.
     SQL/MM Multi Landed / Phase B done-when / H⊥ / MerkatorBV /
     522-n. Full sinusoid noder. Bag-loop ρ Discharge.
     Campaign I–II.

   Parks Γ / ι / ρ (named QEX, landed). This letter cites them
   once; it does not remint CircGamma, ι, leftover_width, or
   LoopDischarged. First cook stays chord–chord. Host CircGamma
   stays QEX.

   ADR-0007 is Accepted (2026-09-07). This letter does not reopen
   Status. QEX is not a new Accept cycle. ADR-0006 Status stays
   Accepted. Testable 𝓘 / cook results sit on the accepted Oracle
   line protocol. This module mints no keyword and no second
   external seam.

   WITNESS topic: overlay · claimId: 0007-sin-egg
   witness: 0007-sin-egg
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
(* Product face: a sidecar sinusoid egg is a named EggSinusoid interpolant    *)
(* tag plus a start/end/amplitude chord seed. Host Egg has no MkSinusoid.     *)
(* Amplitude is a packaging tag, not a cook interpolant.                      *)
(* -------------------------------------------------------------------------- *)

Record SinusoidChord : Type := mkSinusoidChord {
  sc_start : Point;
  sc_end   : Point;
  sc_amp   : R
}.

Record SidecarSinEgg : Type := mkSidecarSinEgg {
  sse_sheet : Sheet;
  sse_chord : SinusoidChord
}.

Definition sidecar_sin_host_egg (_ : SidecarSinEgg) : Egg :=
  MkOutOfScope EggSinusoid.

Definition sidecar_sin_demote (e : SidecarSinEgg) : ChordEgg :=
  mkChordEgg (sc_start (sse_chord e)) (sc_end (sse_chord e)).

Definition sidecar_sin_chicken (src dst : Hen) (e : SidecarSinEgg)
  : Chicken :=
  mkChicken src dst (sidecar_sin_host_egg e).

Definition sinusoid_chord_proper_cross (c : SinusoidChord) (P Q : Point) : Prop :=
  segments_proper_cross (sc_start c) (sc_end c) P Q.

Definition sinusoid_chord_share (c : SinusoidChord) (P Q : Point) : Prop :=
  segments_share (sc_start c) (sc_end c) P Q.

Lemma sidecar_sin_class :
  forall e, egg_class (sidecar_sin_host_egg e) = EggSinusoid.
Proof.
  intros e. reflexivity.
Qed.

Lemma sidecar_sin_only_out_of_scope :
  forall e, sidecar_sin_host_egg e = MkOutOfScope EggSinusoid.
Proof.
  intros e. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked fixture: unit-square diagonals as sinusoid start/end, with a        *)
(* locked amplitude tag. Same geometry as NodingNG's crossing pair —          *)
(* the demoted chord seed, not a sinusoid cook.                               *)
(* -------------------------------------------------------------------------- *)

Definition locked_sin_amp : R := 1.

Definition locked_sin_ab : SinusoidChord :=
  mkSinusoidChord (ce_p0 diag_ab) (ce_p1 diag_ab) locked_sin_amp.

Definition locked_sin_cd : SinusoidChord :=
  mkSinusoidChord (ce_p0 diag_cd) (ce_p1 diag_cd) locked_sin_amp.

Definition locked_sse_ab : SidecarSinEgg :=
  mkSidecarSinEgg default_sheet locked_sin_ab.

Definition locked_sse_cd : SidecarSinEgg :=
  mkSidecarSinEgg default_sheet locked_sin_cd.

Definition locked_sin_ck1 : Chicken :=
  sidecar_sin_chicken 0%nat 1%nat locked_sse_ab.

Definition locked_sin_ck2 : Chicken :=
  sidecar_sin_chicken 2%nat 3%nat locked_sse_cd.

Lemma locked_sin_demote_is_host_crossing :
  sidecar_sin_demote locked_sse_ab = diag_ab /\
  sidecar_sin_demote locked_sse_cd = diag_cd.
Proof.
  split; reflexivity.
Qed.

Lemma locked_sin_same_sheet_as_nodingng :
  sse_sheet locked_sse_ab = default_sheet /\
  sse_sheet locked_sse_cd = nng_sheet nodingng_crossing_pair.
Proof.
  split; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Decline-on-host. Sinusoid eggs stay MkOutOfScope. Not a constructed Hit.   *)
(* Lemmas live here (SheetHenCook must not grow). Cite first_cook_scope /    *)
(* I_ok / try_cook_hit — same occupants as clothoid / NURBS host copies.     *)
(* -------------------------------------------------------------------------- *)

Lemma sinusoid_sinusoid_not_first_scope :
  ~ first_cook_scope EggSinusoid EggSinusoid.
Proof.
  intro H. exact H.
Qed.

Lemma sinusoid_decline_I_ok :
  I_ok (MkOutOfScope EggSinusoid) (MkOutOfScope EggSinusoid) IDecline.
Proof.
  unfold I_ok, first_cook_scope, egg_class.
  intro H. exact H.
Qed.

Lemma sidecar_sin_host_decline :
  I_ok (sidecar_sin_host_egg locked_sse_ab)
       (sidecar_sin_host_egg locked_sse_cd) IDecline.
Proof.
  exact sinusoid_decline_I_ok.
Qed.

Lemma sidecar_sin_host_hit_false :
  forall p ti tj,
    ~ I_ok (sidecar_sin_host_egg locked_sse_ab)
           (sidecar_sin_host_egg locked_sse_cd) (IHit p ti tj).
Proof.
  intros p ti tj H. exact H.
Qed.

Lemma sidecar_sin_host_empty_false :
  ~ I_ok (sidecar_sin_host_egg locked_sse_ab)
         (sidecar_sin_host_egg locked_sse_cd) IEmpty.
Proof.
  intro H. exact H.
Qed.

Lemma sidecar_sin_try_cook_none :
  try_cook_hit locked_sin_ck1 locked_sin_ck2 IDecline crossing_hen
    = None.
Proof.
  reflexivity.
Qed.

Lemma sidecar_sin_try_cook_hit_none :
  forall p ti tj h,
    try_cook_hit locked_sin_ck1 locked_sin_ck2 (IHit p ti tj) h
      = None.
Proof.
  intros p ti tj h.
  reflexivity.
Qed.

Lemma sidecar_sin_empty_neq_decline : IEmpty <> IDecline.
Proof.
  exact IEmpty_neq_IDecline.
Qed.

(* -------------------------------------------------------------------------- *)
(* Constructive chord-seed. Demoted start/end properly cross and share        *)
(* a point. That is the demoted-chord geometry, not a sinusoid×sinusoid       *)
(* cook Hit. Reuses RelateLineLine; no new sinusoid metric.                   *)
(* -------------------------------------------------------------------------- *)

Lemma locked_sin_chord_proper_cross :
  sinusoid_chord_proper_cross locked_sin_ab
    (sc_start locked_sin_cd) (sc_end locked_sin_cd).
Proof.
  unfold sinusoid_chord_proper_cross, locked_sin_ab, locked_sin_cd.
  cbn [sc_start sc_end].
  exact crossing_proper_cross_signs.
Qed.

(* WITNESS {"claimId":"0007-sin-egg","topic":"overlay","lemma":"sidecar_sin_chord_seed","title":"Sidecar sinusoid locked unit-square chords reuse line-line proper-cross share; demoted-chord geometry, not a sinusoid times sinusoid cook Hit","file":"theories/SidecarSinEgg.v","witness":"0007-sin-egg","board":"ADR-0007"} *)
Lemma sidecar_sin_chord_seed :
  sinusoid_chord_share locked_sin_ab
    (sc_start locked_sin_cd) (sc_end locked_sin_cd).
Proof.
  unfold sinusoid_chord_share, sinusoid_chord_proper_cross in *.
  eapply line_line_proper_cross_geom.
  exact locked_sin_chord_proper_cross.
Qed.

(* Demote-to-chord inhabits host / NodingNG first cook. Not a sinusoid Hit. *)
Lemma sidecar_sin_demote_is_nodingng_crossing :
  sidecar_sin_demote locked_sse_ab = diag_ab /\
  sidecar_sin_demote locked_sse_cd = diag_cd /\
  I_ok (MkChord (sidecar_sin_demote locked_sse_ab))
       (MkChord (sidecar_sin_demote locked_sse_cd))
       (IHit cross_pt (1 / 2) (1 / 2)) /\
  nodingng_hit_cooks nodingng_crossing_pair crossing_hen.
Proof.
  destruct locked_sin_demote_is_host_crossing as [Hab Hcd].
  split; [exact Hab|].
  split; [exact Hcd|].
  rewrite Hab, Hcd.
  split; [exact crossing_I_ok|].
  exact nodingng_crossing_hit_cooks.
Qed.

Lemma sidecar_sin_demote_hit_not_sin_I_ok :
  I_ok (MkChord (sidecar_sin_demote locked_sse_ab))
       (MkChord (sidecar_sin_demote locked_sse_cd))
       (IHit cross_pt (1 / 2) (1 / 2)) /\
  ~ I_ok (sidecar_sin_host_egg locked_sse_ab)
         (sidecar_sin_host_egg locked_sse_cd)
         (IHit cross_pt (1 / 2) (1 / 2)).
Proof.
  split.
  - apply sidecar_sin_demote_is_nodingng_crossing.
  - apply sidecar_sin_host_hit_false.
Qed.

(* Thin existing sinusoid corpus (SpectreCurvedEdge sine_profile /
   sine_edge) is profile research — not a cook Hit, not a sinusoid
   noder. Named: profile ≠ cook. No heavy metric remint. *)
Inductive SidecarSinMetricKind : Type :=
| SSM_ProfileResearch
| SSM_CookHit.

Definition sidecar_sin_metric_kind : SidecarSinMetricKind :=
  SSM_ProfileResearch.

Lemma sidecar_sin_metric_is_profile :
  sidecar_sin_metric_kind = SSM_ProfileResearch.
Proof.
  reflexivity.
Qed.

Lemma sidecar_sin_metric_not_cook_hit :
  sidecar_sin_metric_kind <> SSM_CookHit.
Proof.
  discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* Named missing constructors. 508-style, not bools.                          *)
(* -------------------------------------------------------------------------- *)

Inductive SidecarSinCookCtor : Type :=
| SinMkSinusoid
| SinSinusoidHitArm
| SinFirstCookExpand.

Definition sidecar_sin_ctor_inhabits
  (c : SidecarSinCookCtor) : Prop :=
  match c with
  | SinMkSinusoid => False
  | SinSinusoidHitArm => False
  | SinFirstCookExpand => False
  end.

Lemma sidecar_sin_mksinusoid_missing :
  ~ sidecar_sin_ctor_inhabits SinMkSinusoid.
Proof.
  intro H. exact H.
Qed.

Lemma sidecar_sin_hit_arm_missing :
  ~ sidecar_sin_ctor_inhabits SinSinusoidHitArm.
Proof.
  intro H. exact H.
Qed.

Lemma sidecar_sin_first_cook_expand_missing :
  ~ sidecar_sin_ctor_inhabits SinFirstCookExpand.
Proof.
  intro H. exact H.
Qed.

Lemma sidecar_sin_not_first_cook :
  ~ first_cook_scope EggSinusoid EggSinusoid.
Proof.
  exact sinusoid_sinusoid_not_first_scope.
Qed.

Lemma sidecar_sin_first_cook_stays_chord_chord :
  first_cook_scope EggChord EggChord /\
  ~ first_cook_scope EggSinusoid EggSinusoid /\
  ~ first_cook_scope EggNurbs EggNurbs /\
  ~ first_cook_scope EggClothoid EggClothoid /\
  first_cook_scope EggCircularArc EggCircularArc.
Proof.
  split; [exact first_cook_scope_chord_chord|].
  split; [exact sinusoid_sinusoid_not_first_scope|].
  split; [exact nurbs_nurbs_not_first_scope|].
  split; [exact clothoid_clothoid_not_first_scope|].
  exact circular_egg_first_cook_scope.
Qed.

(* -------------------------------------------------------------------------- *)
(* What the sidecar is / is not. Kind tag, not a second kernel.               *)
(* -------------------------------------------------------------------------- *)

Inductive SidecarSinKind : Type :=
| SSE_EggPackaging
| SSE_HostCook
| SSE_NodingNG
| SSE_ProfileNoding
| SSE_CampaignI
| SSE_LoopNoder.

Definition sidecar_sin_kind : SidecarSinKind := SSE_EggPackaging.

Lemma sidecar_sin_is_egg_packaging :
  sidecar_sin_kind = SSE_EggPackaging.
Proof.
  reflexivity.
Qed.

Lemma sidecar_sin_not_host_cook :
  sidecar_sin_kind <> SSE_HostCook.
Proof.
  discriminate.
Qed.

Lemma sidecar_sin_not_nodingng :
  sidecar_sin_kind <> SSE_NodingNG.
Proof.
  discriminate.
Qed.

Lemma sidecar_sin_not_profile_noding :
  sidecar_sin_kind <> SSE_ProfileNoding.
Proof.
  discriminate.
Qed.

Lemma sidecar_sin_not_campaign_i :
  sidecar_sin_kind <> SSE_CampaignI.
Proof.
  discriminate.
Qed.

Lemma sidecar_sin_not_loop_noder :
  sidecar_sin_kind <> SSE_LoopNoder.
Proof.
  discriminate.
Qed.

Inductive SidecarSinLetterStatus : Type :=
| SidecarSinEggLanded
| SidecarSinFirstCookExpanded
| SidecarSinCampaignDischarged.

Definition sidecar_sin_letter_status : SidecarSinLetterStatus :=
  SidecarSinEggLanded.

Lemma sidecar_sin_letter_is_landed :
  sidecar_sin_letter_status = SidecarSinEggLanded.
Proof.
  reflexivity.
Qed.

Lemma sidecar_sin_not_first_cook_expanded :
  sidecar_sin_letter_status <> SidecarSinFirstCookExpanded.
Proof.
  discriminate.
Qed.

Lemma sidecar_sin_campaign_not_discharged :
  sidecar_sin_letter_status <> SidecarSinCampaignDischarged.
Proof.
  discriminate.
Qed.

(* Named QED package: egg + Decline-on-host + locked chord-seed. *)
Lemma sidecar_sin_egg_inhabits :
  egg_class (sidecar_sin_host_egg locked_sse_ab) = EggSinusoid /\
  sidecar_sin_host_egg locked_sse_ab = MkOutOfScope EggSinusoid /\
  I_ok (sidecar_sin_host_egg locked_sse_ab)
       (sidecar_sin_host_egg locked_sse_cd) IDecline /\
  try_cook_hit locked_sin_ck1 locked_sin_ck2 IDecline crossing_hen
    = None /\
  sinusoid_chord_share locked_sin_ab
    (sc_start locked_sin_cd) (sc_end locked_sin_cd) /\
  I_ok (MkChord (sidecar_sin_demote locked_sse_ab))
       (MkChord (sidecar_sin_demote locked_sse_cd))
       (IHit cross_pt (1 / 2) (1 / 2)) /\
  IEmpty <> IDecline /\
  sidecar_sin_kind = SSE_EggPackaging /\
  sidecar_sin_metric_kind = SSM_ProfileResearch.
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact sidecar_sin_host_decline|].
  split; [exact sidecar_sin_try_cook_none|].
  split; [exact sidecar_sin_chord_seed|].
  split; [apply sidecar_sin_demote_hit_not_sin_I_ok|].
  split; [exact sidecar_sin_empty_neq_decline|].
  split; [reflexivity|].
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-sin-egg","topic":"overlay","lemma":"ticket_0007_sin_egg_qed_or_qex","title":"Sidecar sinusoid egg packages EggSinusoid Decline-on-host and locked demoted-chord seed (QED) or host I_ok is a sinusoid Hit (QEX); discharged QED; demote-to-chord is NodingNG first cook, not a sinusoid times sinusoid cook","file":"theories/SidecarSinEgg.v","witness":"0007-sin-egg","board":"ADR-0007"} *)
Theorem ticket_0007_sin_egg_qed_or_qex :
  (egg_class (sidecar_sin_host_egg locked_sse_ab) = EggSinusoid /\
   sidecar_sin_host_egg locked_sse_ab = MkOutOfScope EggSinusoid /\
   I_ok (sidecar_sin_host_egg locked_sse_ab)
        (sidecar_sin_host_egg locked_sse_cd) IDecline /\
   try_cook_hit locked_sin_ck1 locked_sin_ck2 IDecline crossing_hen
     = None /\
   sinusoid_chord_share locked_sin_ab
     (sc_start locked_sin_cd) (sc_end locked_sin_cd) /\
   I_ok (MkChord (sidecar_sin_demote locked_sse_ab))
        (MkChord (sidecar_sin_demote locked_sse_cd))
        (IHit cross_pt (1 / 2) (1 / 2)) /\
   ~ I_ok (sidecar_sin_host_egg locked_sse_ab)
          (sidecar_sin_host_egg locked_sse_cd)
          (IHit cross_pt (1 / 2) (1 / 2)) /\
   IEmpty <> IDecline /\
   sidecar_sin_kind = SSE_EggPackaging /\
   sidecar_sin_kind <> SSE_HostCook /\
   sidecar_sin_kind <> SSE_NodingNG /\
   sidecar_sin_kind <> SSE_ProfileNoding /\
   sidecar_sin_metric_kind = SSM_ProfileResearch /\
   sidecar_sin_metric_kind <> SSM_CookHit)
  \/
  (exists p ti tj,
     I_ok (MkOutOfScope EggSinusoid) (MkOutOfScope EggSinusoid)
          (IHit p ti tj)).
Proof.
  left.
  destruct sidecar_sin_egg_inhabits
    as [Hcls [Htag [Hdec [Hnone [Hseed [Hdem [Hneq [Hkind Hmet]]]]]]]].
  split; [exact Hcls|].
  split; [exact Htag|].
  split; [exact Hdec|].
  split; [exact Hnone|].
  split; [exact Hseed|].
  split; [exact Hdem|].
  split; [apply sidecar_sin_host_hit_false|].
  split; [exact Hneq|].
  split; [exact Hkind|].
  split; [exact sidecar_sin_not_host_cook|].
  split; [exact sidecar_sin_not_nodingng|].
  split; [exact sidecar_sin_not_profile_noding|].
  split; [exact Hmet|].
  exact sidecar_sin_metric_not_cook_hit.
Qed.

(* WITNESS {"claimId":"0007-sin-egg","topic":"overlay","lemma":"ticket_0007_sin_not_first_cook_qed_or_qex","title":"Sidecar sinusoid expands first_cook_scope to sinusoid times sinusoid and inhabits I_ok Hit (QED) or sinusoid times sinusoid stays QEX with named MkSinusoid / Hit-arm gaps (QEX); discharged QEX; checklist 4; do not fake first-cook expand","file":"theories/SidecarSinEgg.v","witness":"0007-sin-egg","board":"ADR-0007"} *)
Theorem ticket_0007_sin_not_first_cook_qed_or_qex :
  (first_cook_scope EggSinusoid EggSinusoid /\
   sidecar_sin_ctor_inhabits SinMkSinusoid /\
   sidecar_sin_ctor_inhabits SinSinusoidHitArm /\
   sidecar_sin_ctor_inhabits SinFirstCookExpand /\
   sidecar_sin_letter_status = SidecarSinFirstCookExpanded /\
   exists p ti tj,
     I_ok (MkOutOfScope EggSinusoid) (MkOutOfScope EggSinusoid)
          (IHit p ti tj))
  \/
  (~ first_cook_scope EggSinusoid EggSinusoid /\
   first_cook_scope EggChord EggChord /\
   ~ sidecar_sin_ctor_inhabits SinMkSinusoid /\
   ~ sidecar_sin_ctor_inhabits SinSinusoidHitArm /\
   ~ sidecar_sin_ctor_inhabits SinFirstCookExpand /\
   sidecar_sin_letter_status = SidecarSinEggLanded /\
   I_ok (MkOutOfScope EggSinusoid) (MkOutOfScope EggSinusoid) IDecline /\
   (forall p ti tj,
      ~ I_ok (MkOutOfScope EggSinusoid) (MkOutOfScope EggSinusoid)
           (IHit p ti tj)) /\
   try_cook_hit locked_sin_ck1 locked_sin_ck2 IDecline crossing_hen = None).
Proof.
  right.
  split; [exact sinusoid_sinusoid_not_first_scope|].
  split; [exact first_cook_scope_chord_chord|].
  split; [exact sidecar_sin_mksinusoid_missing|].
  split; [exact sidecar_sin_hit_arm_missing|].
  split; [exact sidecar_sin_first_cook_expand_missing|].
  split; [exact sidecar_sin_letter_is_landed|].
  split; [exact sinusoid_decline_I_ok|].
  split; [intros p ti tj H; exact H|].
  exact sidecar_sin_try_cook_none.
Qed.

(* WITNESS {"claimId":"0007-sin-egg","topic":"overlay","lemma":"ticket_0007_sin_parks_qed_or_qex","title":"Sidecar sinusoid discharges Campaign I-II, remints Spectre sine_profile as noding, and flips LoopDischarged (QED) or names them parked and cites Parks Gamma/iota/rho once (QEX); discharged QEX; letter landed != first-cook expand / Campaign / bag noder","file":"theories/SidecarSinEgg.v","witness":"0007-sin-egg","board":"ADR-0007"} *)
Theorem ticket_0007_sin_parks_qed_or_qex :
  (sidecar_sin_letter_status = SidecarSinCampaignDischarged /\
   sidecar_sin_kind = SSE_CampaignI /\
   sidecar_sin_kind = SSE_ProfileNoding /\
   sidecar_sin_kind = SSE_LoopNoder /\
   cook_loop_status = LoopDischarged)
  \/
  (sidecar_sin_letter_status = SidecarSinEggLanded /\
   sidecar_sin_letter_status <> SidecarSinCampaignDischarged /\
   sidecar_sin_kind = SSE_EggPackaging /\
   sidecar_sin_kind <> SSE_CampaignI /\
   sidecar_sin_kind <> SSE_ProfileNoding /\
   sidecar_sin_kind <> SSE_LoopNoder /\
   cook_loop_status = LoopObligation /\
   cook_loop_status <> LoopDischarged /\
   first_cook_scope EggChord EggChord /\
   ~ first_cook_scope EggSinusoid EggSinusoid).
Proof.
  right.
  split; [exact sidecar_sin_letter_is_landed|].
  split; [exact sidecar_sin_campaign_not_discharged|].
  split; [exact sidecar_sin_is_egg_packaging|].
  split; [exact sidecar_sin_not_campaign_i|].
  split; [exact sidecar_sin_not_profile_noding|].
  split; [exact sidecar_sin_not_loop_noder|].
  split; [exact cook_loop_is_obligation|].
  split; [exact cook_loop_not_discharged|].
  split; [exact first_cook_scope_chord_chord|].
  exact sinusoid_sinusoid_not_first_scope.
Qed.

Print Assumptions sidecar_sin_class.
Print Assumptions sidecar_sin_host_decline.
Print Assumptions sidecar_sin_try_cook_none.
Print Assumptions sidecar_sin_chord_seed.
Print Assumptions sidecar_sin_demote_is_nodingng_crossing.
Print Assumptions sidecar_sin_metric_not_cook_hit.
Print Assumptions sidecar_sin_mksinusoid_missing.
Print Assumptions sidecar_sin_hit_arm_missing.
Print Assumptions sidecar_sin_egg_inhabits.
Print Assumptions ticket_0007_sin_egg_qed_or_qex.
Print Assumptions ticket_0007_sin_not_first_cook_qed_or_qex.
Print Assumptions ticket_0007_sin_parks_qed_or_qex.
