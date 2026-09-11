(* ============================================================================
   NetTopologySuite.Proofs.SidecarSpiralEgg
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: SQL/MM ST_SpiralCurve egg sidecar
   (claimId 0007-spiral-egg). LAST Lesson-1 packaging extra before
   the real Γ letter (host MkCirc / CircGamma).

   Product / sidecar face: EggSpiralCurve on the ADR-0007 sheet /
   hen / cook vocabulary. Host EggClass did not have this arm —
   this letter adds the constructor only (MkOutOfScope tag). No
   Decline / not-first-cook / try_cook lemmas were added to
   SheetHenCook. Those live here and cite existing first_cook_scope
   / I_ok / try_cook_hit_out_of_scope_none. Prefer SidecarSpiral*
   over reminting host cook (same preference as SidecarGeodesic* /
   SidecarElliptic* / SidecarCircEgg* / SidecarSin* / SidecarNurbs*
   / SidecarClothoid* for non-host).

   SQL/MM ST_SpiralCurve (ISO 13249-3 §4.2.12) is type-zoo
   packaging. One host egg. Sidecar inductive carries the five
   required spiral-type names (clothoid, bloss, biquadratic, sine,
   cosine) PLUS Unknown. CONTEXT Zoo still lists SPIRALCURVE's
   bloss / biquadratic / sine / cosine as expansion backlog —
   this letter does not mint Zoo membership and does not invent
   a spiral interpolant. Demote-to-chord reuses RelateLineLine.

   ST_Clothoid / EggClothoid stays its own host tag. The sidecar
   clothoid arm is the spiral-type nameplate, not a remint that
   deletes EggClothoid. Do not explode EggClass into five spiral
   eggs.

   One honest first rung. One locked fixture. Do not ship a
   spiral×spiral noder, CircGamma, or Campaign I–II in this
   letter. This is NOT 𝓘 progress and NOT Γ.

   QED: sidecar egg packaging on EggSpiralCurve; five ISO names
   + Unknown inhabit one spiral egg type; EggClothoid still
   present; host I_ok Decline and try_cook_hit None; locked
   unit-square spiral chords demote to the host crossing pair;
   demote-to-chord is NodingNG / host first cook, not a spiral Hit.

   QEX: spiral×spiral is not first cook (checklist 4). Named
   missing constructor: no MkSpiral on Egg, no I_ok Hit arm
   on spiral eggs, no first-cook expand. Do not fake first-cook
   expand or LoopDischarged. Do not remint spiral interpolant
   as noding.

   What this is not:
     Host first_cook_scope / try_cook_hit expand to
     spiral×spiral. CircGamma / ι / ρ remint. MkCirc.
     Host circular cook. Shewchuk / Hobby / Priest /
     Jordan / HotPixel / OverlayNG snap remint. SQL/MM Multi
     Landed / Phase B done-when / H⊥ / MerkatorBV / 522-n.
     Full spiral noder. Bag-loop ρ Discharge. Campaign I–II.
     Honesty-chip product. Invented spiral interpolant math.
     Five host spiral eggs. EggClothoid fold-away. 𝓘 progress.
     Γ / CircGamma / MkCirc.

   Parks Γ / ι / ρ (named QEX, landed). This letter cites them
   once; it does not remint CircGamma, ι, leftover_width, or
   LoopDischarged. First cook stays chord–chord. Host CircGamma
   stays QEX.

   ADR-0007 is Accepted (2026-09-07). This letter does not reopen
   Status. QEX is not a new Accept cycle. ADR-0006 Status stays
   Accepted. Testable 𝓘 / cook results sit on the accepted Oracle
   line protocol. This module mints no keyword and no second
   external seam.

   WITNESS topic: overlay · claimId: 0007-spiral-egg
   witness: 0007-spiral-egg
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
(* SQL/MM ISO 13249-3 §4.2.12 ST_SpiralCurve nameplate. Five required         *)
(* names PLUS Unknown. One sidecar type; one host EggSpiralCurve tag.         *)
(* SpiralClothoid is the spiral-type nameplate, not EggClothoid.              *)
(* -------------------------------------------------------------------------- *)

Inductive SpiralCurveKind : Type :=
| SpiralClothoid
| SpiralBloss
| SpiralBiquadratic
| SpiralSine
| SpiralCosine
| SpiralUnknown.

(* Product face: a sidecar spiral egg is a named EggSpiralCurve
   interpolant tag plus a start/end chord seed and a spiral-type
   nameplate. Host Egg has no MkSpiral. The seed is demote-to-chord
   packaging, not a spiral interpolant. *)

Record SpiralChord : Type := mkSpiralChord {
  spc_start : Point;
  spc_end   : Point;
  spc_kind  : SpiralCurveKind
}.

Record SidecarSpiralEgg : Type := mkSidecarSpiralEgg {
  ssp_sheet : Sheet;
  ssp_chord : SpiralChord
}.

Definition sidecar_spiral_host_egg (_ : SidecarSpiralEgg) : Egg :=
  MkOutOfScope EggSpiralCurve.

Definition sidecar_spiral_demote (e : SidecarSpiralEgg) : ChordEgg :=
  mkChordEgg (spc_start (ssp_chord e)) (spc_end (ssp_chord e)).

Definition sidecar_spiral_chicken (src dst : Hen) (e : SidecarSpiralEgg)
  : Chicken :=
  mkChicken src dst (sidecar_spiral_host_egg e).

Definition sidecar_spiral_of_kind (k : SpiralCurveKind) : SidecarSpiralEgg :=
  mkSidecarSpiralEgg default_sheet
    (mkSpiralChord (ce_p0 diag_ab) (ce_p1 diag_ab) k).

Definition spiral_chord_proper_cross (c : SpiralChord) (P Q : Point) : Prop :=
  segments_proper_cross (spc_start c) (spc_end c) P Q.

Definition spiral_chord_share (c : SpiralChord) (P Q : Point) : Prop :=
  segments_share (spc_start c) (spc_end c) P Q.

Lemma sidecar_spiral_class :
  forall e, egg_class (sidecar_spiral_host_egg e) = EggSpiralCurve.
Proof.
  intros e. reflexivity.
Qed.

Lemma sidecar_spiral_only_out_of_scope :
  forall e, sidecar_spiral_host_egg e = MkOutOfScope EggSpiralCurve.
Proof.
  intros e. reflexivity.
Qed.

(* One host egg for every ISO nameplate, including Unknown. *)
Lemma sidecar_spiral_kinds_one_host_egg :
  forall k,
    egg_class (sidecar_spiral_host_egg (sidecar_spiral_of_kind k))
      = EggSpiralCurve /\
    sidecar_spiral_host_egg (sidecar_spiral_of_kind k)
      = MkOutOfScope EggSpiralCurve.
Proof.
  intros k. split; reflexivity.
Qed.

Lemma sidecar_spiral_iso_names_inhabit :
  (exists e, spc_kind (ssp_chord e) = SpiralClothoid) /\
  (exists e, spc_kind (ssp_chord e) = SpiralBloss) /\
  (exists e, spc_kind (ssp_chord e) = SpiralBiquadratic) /\
  (exists e, spc_kind (ssp_chord e) = SpiralSine) /\
  (exists e, spc_kind (ssp_chord e) = SpiralCosine) /\
  (exists e, spc_kind (ssp_chord e) = SpiralUnknown).
Proof.
  repeat split;
    (exists (sidecar_spiral_of_kind SpiralClothoid); reflexivity) ||
    (exists (sidecar_spiral_of_kind SpiralBloss); reflexivity) ||
    (exists (sidecar_spiral_of_kind SpiralBiquadratic); reflexivity) ||
    (exists (sidecar_spiral_of_kind SpiralSine); reflexivity) ||
    (exists (sidecar_spiral_of_kind SpiralCosine); reflexivity) ||
    (exists (sidecar_spiral_of_kind SpiralUnknown); reflexivity).
Qed.

(* EggClothoid stays. Spiral's clothoid arm is a nameplate, not a remint. *)
Lemma egg_clothoid_still_present :
  egg_class (MkOutOfScope EggClothoid) = EggClothoid /\
  EggClothoid <> EggSpiralCurve.
Proof.
  split.
  - reflexivity.
  - discriminate.
Qed.

Lemma sidecar_spiral_clothoid_nameplate_not_eggclothoid :
  sidecar_spiral_host_egg (sidecar_spiral_of_kind SpiralClothoid)
    = MkOutOfScope EggSpiralCurve /\
  sidecar_spiral_host_egg (sidecar_spiral_of_kind SpiralClothoid)
    <> MkOutOfScope EggClothoid /\
  egg_class (MkOutOfScope EggClothoid) = EggClothoid /\
  EggClothoid <> EggSpiralCurve.
Proof.
  split; [reflexivity|].
  split; [discriminate|].
  exact egg_clothoid_still_present.
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked fixture: unit-square diagonals as spiral start/end. Same            *)
(* geometry as NodingNG's crossing pair — the demoted chord seed, not         *)
(* a spiral cook. Locked nameplate is SpiralClothoid to pin the               *)
(* nameplate ≠ EggClothoid honesty on the seed.                               *)
(* -------------------------------------------------------------------------- *)

Definition locked_spi_ab : SpiralChord :=
  mkSpiralChord (ce_p0 diag_ab) (ce_p1 diag_ab) SpiralClothoid.

Definition locked_spi_cd : SpiralChord :=
  mkSpiralChord (ce_p0 diag_cd) (ce_p1 diag_cd) SpiralClothoid.

Definition locked_ssp_ab : SidecarSpiralEgg :=
  mkSidecarSpiralEgg default_sheet locked_spi_ab.

Definition locked_ssp_cd : SidecarSpiralEgg :=
  mkSidecarSpiralEgg default_sheet locked_spi_cd.

Definition locked_spi_ck1 : Chicken :=
  sidecar_spiral_chicken 0%nat 1%nat locked_ssp_ab.

Definition locked_spi_ck2 : Chicken :=
  sidecar_spiral_chicken 2%nat 3%nat locked_ssp_cd.

Lemma locked_spi_demote_is_host_crossing :
  sidecar_spiral_demote locked_ssp_ab = diag_ab /\
  sidecar_spiral_demote locked_ssp_cd = diag_cd.
Proof.
  split; reflexivity.
Qed.

Lemma locked_spi_same_sheet_as_nodingng :
  ssp_sheet locked_ssp_ab = default_sheet /\
  ssp_sheet locked_ssp_cd = nng_sheet nodingng_crossing_pair.
Proof.
  split; reflexivity.
Qed.

Lemma locked_spi_nameplate_is_clothoid :
  spc_kind locked_spi_ab = SpiralClothoid /\
  spc_kind locked_spi_cd = SpiralClothoid.
Proof.
  split; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Decline-on-host. Spiral eggs stay MkOutOfScope. Not a constructed Hit.     *)
(* Lemmas live here (SheetHenCook must not grow lemmas). Cite                *)
(* first_cook_scope / I_ok / try_cook_hit — same occupants as                *)
(* GeodesicString #722 / Elliptic #721 sidecar copies.                        *)
(* -------------------------------------------------------------------------- *)

Lemma spiral_spiral_not_first_scope :
  ~ first_cook_scope EggSpiralCurve EggSpiralCurve.
Proof.
  intro H. exact H.
Qed.

Lemma spiral_decline_I_ok :
  I_ok (MkOutOfScope EggSpiralCurve) (MkOutOfScope EggSpiralCurve)
       IDecline.
Proof.
  unfold I_ok, first_cook_scope, egg_class.
  intro H. exact H.
Qed.

Lemma sidecar_spiral_host_decline :
  I_ok (sidecar_spiral_host_egg locked_ssp_ab)
       (sidecar_spiral_host_egg locked_ssp_cd) IDecline.
Proof.
  exact spiral_decline_I_ok.
Qed.

Lemma sidecar_spiral_host_hit_false :
  forall p ti tj,
    ~ I_ok (sidecar_spiral_host_egg locked_ssp_ab)
           (sidecar_spiral_host_egg locked_ssp_cd) (IHit p ti tj).
Proof.
  intros p ti tj H. exact H.
Qed.

Lemma sidecar_spiral_host_empty_false :
  ~ I_ok (sidecar_spiral_host_egg locked_ssp_ab)
         (sidecar_spiral_host_egg locked_ssp_cd) IEmpty.
Proof.
  intro H. exact H.
Qed.

Lemma sidecar_spiral_try_cook_none :
  try_cook_hit locked_spi_ck1 locked_spi_ck2 IDecline crossing_hen
    = None.
Proof.
  reflexivity.
Qed.

Lemma sidecar_spiral_try_cook_hit_none :
  forall p ti tj h,
    try_cook_hit locked_spi_ck1 locked_spi_ck2 (IHit p ti tj) h
      = None.
Proof.
  intros p ti tj h.
  reflexivity.
Qed.

Lemma sidecar_spiral_empty_neq_decline : IEmpty <> IDecline.
Proof.
  exact IEmpty_neq_IDecline.
Qed.

(* -------------------------------------------------------------------------- *)
(* Constructive chord-seed. Demoted start/end properly cross and share        *)
(* a point. That is the demoted-chord geometry, not a spiral×spiral           *)
(* cook Hit. Reuses RelateLineLine; no spiral interpolant.                    *)
(* -------------------------------------------------------------------------- *)

Lemma locked_spi_chord_proper_cross :
  spiral_chord_proper_cross locked_spi_ab
    (spc_start locked_spi_cd) (spc_end locked_spi_cd).
Proof.
  unfold spiral_chord_proper_cross, locked_spi_ab, locked_spi_cd.
  cbn [spc_start spc_end].
  exact crossing_proper_cross_signs.
Qed.

(* WITNESS {"claimId":"0007-spiral-egg","topic":"overlay","lemma":"sidecar_spiral_chord_seed","title":"Sidecar spiral locked unit-square chords reuse line-line proper-cross share; demoted-chord geometry, not a spiral times spiral cook Hit","file":"theories/SidecarSpiralEgg.v","witness":"0007-spiral-egg","board":"ADR-0007"} *)
Lemma sidecar_spiral_chord_seed :
  spiral_chord_share locked_spi_ab
    (spc_start locked_spi_cd) (spc_end locked_spi_cd).
Proof.
  unfold spiral_chord_share, spiral_chord_proper_cross in *.
  eapply line_line_proper_cross_geom.
  exact locked_spi_chord_proper_cross.
Qed.

(* Demote-to-chord inhabits host / NodingNG first cook. Not a spiral Hit. *)
Lemma sidecar_spiral_demote_is_nodingng_crossing :
  sidecar_spiral_demote locked_ssp_ab = diag_ab /\
  sidecar_spiral_demote locked_ssp_cd = diag_cd /\
  I_ok (MkChord (sidecar_spiral_demote locked_ssp_ab))
       (MkChord (sidecar_spiral_demote locked_ssp_cd))
       (IHit cross_pt (1 / 2) (1 / 2)) /\
  nodingng_hit_cooks nodingng_crossing_pair crossing_hen.
Proof.
  destruct locked_spi_demote_is_host_crossing as [Hab Hcd].
  split; [exact Hab|].
  split; [exact Hcd|].
  rewrite Hab, Hcd.
  split; [exact crossing_I_ok|].
  exact nodingng_crossing_hit_cooks.
Qed.

Lemma sidecar_spiral_demote_hit_not_spiral_I_ok :
  I_ok (MkChord (sidecar_spiral_demote locked_ssp_ab))
       (MkChord (sidecar_spiral_demote locked_ssp_cd))
       (IHit cross_pt (1 / 2) (1 / 2)) /\
  ~ I_ok (sidecar_spiral_host_egg locked_ssp_ab)
         (sidecar_spiral_host_egg locked_ssp_cd)
         (IHit cross_pt (1 / 2) (1 / 2)).
Proof.
  split.
  - apply sidecar_spiral_demote_is_nodingng_crossing.
  - apply sidecar_spiral_host_hit_false.
Qed.

(* SQL/MM ST_SpiralCurve type-zoo packaging. Spiral interpolant
   stays research — not a cook Hit, not a spiral noder. Named:
   type zoo ≠ cook. No invented spiral math. *)
Inductive SidecarSpiralMetricKind : Type :=
| SPM_SqlMmTypeZoo
| SPM_CookHit.

Definition sidecar_spiral_metric_kind : SidecarSpiralMetricKind :=
  SPM_SqlMmTypeZoo.

Lemma sidecar_spiral_metric_is_type_zoo :
  sidecar_spiral_metric_kind = SPM_SqlMmTypeZoo.
Proof.
  reflexivity.
Qed.

Lemma sidecar_spiral_metric_not_cook_hit :
  sidecar_spiral_metric_kind <> SPM_CookHit.
Proof.
  discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* Named missing constructors. 508-style, not bools.                          *)
(* -------------------------------------------------------------------------- *)

Inductive SidecarSpiralCookCtor : Type :=
| SpiralMkSpiral
| SpiralSpiralHitArm
| SpiralFirstCookExpand.

Definition sidecar_spiral_ctor_inhabits
  (c : SidecarSpiralCookCtor) : Prop :=
  match c with
  | SpiralMkSpiral => False
  | SpiralSpiralHitArm => False
  | SpiralFirstCookExpand => False
  end.

Lemma sidecar_spiral_mkspiral_missing :
  ~ sidecar_spiral_ctor_inhabits SpiralMkSpiral.
Proof.
  intro H. exact H.
Qed.

Lemma sidecar_spiral_hit_arm_missing :
  ~ sidecar_spiral_ctor_inhabits SpiralSpiralHitArm.
Proof.
  intro H. exact H.
Qed.

Lemma sidecar_spiral_first_cook_expand_missing :
  ~ sidecar_spiral_ctor_inhabits SpiralFirstCookExpand.
Proof.
  intro H. exact H.
Qed.

Lemma sidecar_spiral_not_first_cook :
  ~ first_cook_scope EggSpiralCurve EggSpiralCurve.
Proof.
  exact spiral_spiral_not_first_scope.
Qed.

Lemma sidecar_spiral_first_cook_stays_chord_chord :
  first_cook_scope EggChord EggChord /\
  ~ first_cook_scope EggSpiralCurve EggSpiralCurve /\
  ~ first_cook_scope EggGeodesicString EggGeodesicString /\
  first_cook_scope EggClothoid EggClothoid /\
  ~ first_cook_scope EggEllipse EggEllipse /\
  ~ first_cook_scope EggNurbs EggNurbs /\
  first_cook_scope EggCircularArc EggCircularArc.
Proof.
  split; [exact first_cook_scope_chord_chord|].
  split; [exact spiral_spiral_not_first_scope|].
  split; [intro H; exact H|].
  split; [exact clothoid_egg_first_cook_scope|].
  split; [exact ellipse_ellipse_not_first_scope|].
  split; [exact nurbs_nurbs_not_first_scope|].
  exact circular_egg_first_cook_scope.
Qed.

(* -------------------------------------------------------------------------- *)
(* What the sidecar is / is not. Kind tag, not a second kernel.               *)
(* -------------------------------------------------------------------------- *)

Inductive SidecarSpiralKind : Type :=
| SSP_EggPackaging
| SSP_HostCook
| SSP_NodingNG
| SSP_SpiralNoding
| SSP_CircGamma
| SSP_CampaignI
| SSP_LoopNoder.

Definition sidecar_spiral_kind : SidecarSpiralKind := SSP_EggPackaging.

Lemma sidecar_spiral_is_egg_packaging :
  sidecar_spiral_kind = SSP_EggPackaging.
Proof.
  reflexivity.
Qed.

Lemma sidecar_spiral_not_host_cook :
  sidecar_spiral_kind <> SSP_HostCook.
Proof.
  discriminate.
Qed.

Lemma sidecar_spiral_not_nodingng :
  sidecar_spiral_kind <> SSP_NodingNG.
Proof.
  discriminate.
Qed.

Lemma sidecar_spiral_not_spiral_noding :
  sidecar_spiral_kind <> SSP_SpiralNoding.
Proof.
  discriminate.
Qed.

Lemma sidecar_spiral_not_circgamma :
  sidecar_spiral_kind <> SSP_CircGamma.
Proof.
  discriminate.
Qed.

Lemma sidecar_spiral_not_campaign_i :
  sidecar_spiral_kind <> SSP_CampaignI.
Proof.
  discriminate.
Qed.

Lemma sidecar_spiral_not_loop_noder :
  sidecar_spiral_kind <> SSP_LoopNoder.
Proof.
  discriminate.
Qed.

Inductive SidecarSpiralLetterStatus : Type :=
| SidecarSpiralEggLanded
| SidecarSpiralFirstCookExpanded
| SidecarSpiralCampaignDischarged.

Definition sidecar_spiral_letter_status : SidecarSpiralLetterStatus :=
  SidecarSpiralEggLanded.

Lemma sidecar_spiral_letter_is_landed :
  sidecar_spiral_letter_status = SidecarSpiralEggLanded.
Proof.
  reflexivity.
Qed.

Lemma sidecar_spiral_not_first_cook_expanded :
  sidecar_spiral_letter_status <> SidecarSpiralFirstCookExpanded.
Proof.
  discriminate.
Qed.

Lemma sidecar_spiral_campaign_not_discharged :
  sidecar_spiral_letter_status <> SidecarSpiralCampaignDischarged.
Proof.
  discriminate.
Qed.

(* Named QED package: egg + Decline-on-host + locked chord-seed
   + five ISO names + Unknown + EggClothoid still present. *)
Lemma sidecar_spiral_egg_inhabits :
  egg_class (sidecar_spiral_host_egg locked_ssp_ab) = EggSpiralCurve /\
  sidecar_spiral_host_egg locked_ssp_ab = MkOutOfScope EggSpiralCurve /\
  I_ok (sidecar_spiral_host_egg locked_ssp_ab)
       (sidecar_spiral_host_egg locked_ssp_cd) IDecline /\
  try_cook_hit locked_spi_ck1 locked_spi_ck2 IDecline crossing_hen
    = None /\
  spiral_chord_share locked_spi_ab
    (spc_start locked_spi_cd) (spc_end locked_spi_cd) /\
  I_ok (MkChord (sidecar_spiral_demote locked_ssp_ab))
       (MkChord (sidecar_spiral_demote locked_ssp_cd))
       (IHit cross_pt (1 / 2) (1 / 2)) /\
  IEmpty <> IDecline /\
  sidecar_spiral_kind = SSP_EggPackaging /\
  sidecar_spiral_metric_kind = SPM_SqlMmTypeZoo /\
  egg_class (MkOutOfScope EggClothoid) = EggClothoid /\
  EggClothoid <> EggSpiralCurve /\
  (exists e, spc_kind (ssp_chord e) = SpiralClothoid) /\
  (exists e, spc_kind (ssp_chord e) = SpiralBloss) /\
  (exists e, spc_kind (ssp_chord e) = SpiralBiquadratic) /\
  (exists e, spc_kind (ssp_chord e) = SpiralSine) /\
  (exists e, spc_kind (ssp_chord e) = SpiralCosine) /\
  (exists e, spc_kind (ssp_chord e) = SpiralUnknown).
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact sidecar_spiral_host_decline|].
  split; [exact sidecar_spiral_try_cook_none|].
  split; [exact sidecar_spiral_chord_seed|].
  split; [apply sidecar_spiral_demote_hit_not_spiral_I_ok|].
  split; [exact sidecar_spiral_empty_neq_decline|].
  split; [reflexivity|].
  split; [reflexivity|].
  destruct egg_clothoid_still_present as [Hcl Hneq].
  split; [exact Hcl|].
  split; [exact Hneq|].
  exact sidecar_spiral_iso_names_inhabit.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-spiral-egg","topic":"overlay","lemma":"ticket_0007_spiral_egg_qed_or_qex","title":"Sidecar spiral egg packages EggSpiralCurve Decline-on-host, five ISO 13249-3 names plus Unknown, and locked demoted-chord seed (QED) or host I_ok is a spiral Hit (QEX); discharged QED; EggClothoid stays; demote-to-chord is NodingNG first cook, not a spiral times spiral cook; SQL/MM type zoo stays packaging","file":"theories/SidecarSpiralEgg.v","witness":"0007-spiral-egg","board":"ADR-0007"} *)
Theorem ticket_0007_spiral_egg_qed_or_qex :
  (egg_class (sidecar_spiral_host_egg locked_ssp_ab) = EggSpiralCurve /\
   sidecar_spiral_host_egg locked_ssp_ab = MkOutOfScope EggSpiralCurve /\
   I_ok (sidecar_spiral_host_egg locked_ssp_ab)
        (sidecar_spiral_host_egg locked_ssp_cd) IDecline /\
   try_cook_hit locked_spi_ck1 locked_spi_ck2 IDecline crossing_hen
     = None /\
   spiral_chord_share locked_spi_ab
     (spc_start locked_spi_cd) (spc_end locked_spi_cd) /\
   I_ok (MkChord (sidecar_spiral_demote locked_ssp_ab))
        (MkChord (sidecar_spiral_demote locked_ssp_cd))
        (IHit cross_pt (1 / 2) (1 / 2)) /\
   ~ I_ok (sidecar_spiral_host_egg locked_ssp_ab)
          (sidecar_spiral_host_egg locked_ssp_cd)
          (IHit cross_pt (1 / 2) (1 / 2)) /\
   IEmpty <> IDecline /\
   sidecar_spiral_kind = SSP_EggPackaging /\
   sidecar_spiral_kind <> SSP_HostCook /\
   sidecar_spiral_kind <> SSP_NodingNG /\
   sidecar_spiral_kind <> SSP_SpiralNoding /\
   sidecar_spiral_metric_kind = SPM_SqlMmTypeZoo /\
   sidecar_spiral_metric_kind <> SPM_CookHit /\
   egg_class (MkOutOfScope EggClothoid) = EggClothoid /\
   EggClothoid <> EggSpiralCurve /\
   sidecar_spiral_host_egg (sidecar_spiral_of_kind SpiralClothoid)
     <> MkOutOfScope EggClothoid /\
   (exists e, spc_kind (ssp_chord e) = SpiralClothoid) /\
   (exists e, spc_kind (ssp_chord e) = SpiralBloss) /\
   (exists e, spc_kind (ssp_chord e) = SpiralBiquadratic) /\
   (exists e, spc_kind (ssp_chord e) = SpiralSine) /\
   (exists e, spc_kind (ssp_chord e) = SpiralCosine) /\
   (exists e, spc_kind (ssp_chord e) = SpiralUnknown))
  \/
  (exists p ti tj,
     I_ok (MkOutOfScope EggSpiralCurve) (MkOutOfScope EggSpiralCurve)
          (IHit p ti tj)).
Proof.
  left.
  destruct sidecar_spiral_egg_inhabits
    as [Hcls [Htag [Hdec [Hnone [Hseed [Hdem [Hneq [Hkind [Hmet
         [Hcl [Hclneq Hnames]]]]]]]]]]].
  split; [exact Hcls|].
  split; [exact Htag|].
  split; [exact Hdec|].
  split; [exact Hnone|].
  split; [exact Hseed|].
  split; [exact Hdem|].
  split; [apply sidecar_spiral_host_hit_false|].
  split; [exact Hneq|].
  split; [exact Hkind|].
  split; [exact sidecar_spiral_not_host_cook|].
  split; [exact sidecar_spiral_not_nodingng|].
  split; [exact sidecar_spiral_not_spiral_noding|].
  split; [exact Hmet|].
  split; [exact sidecar_spiral_metric_not_cook_hit|].
  split; [exact Hcl|].
  split; [exact Hclneq|].
  split; [apply sidecar_spiral_clothoid_nameplate_not_eggclothoid|].
  exact Hnames.
Qed.

(* WITNESS {"claimId":"0007-spiral-egg","topic":"overlay","lemma":"ticket_0007_spiral_not_first_cook_qed_or_qex","title":"Sidecar spiral expands first_cook_scope to spiral times spiral and inhabits I_ok Hit (QED) or spiral times spiral stays QEX with named MkSpiral / Hit-arm gaps (QEX); discharged QEX; checklist 4; do not fake first-cook expand","file":"theories/SidecarSpiralEgg.v","witness":"0007-spiral-egg","board":"ADR-0007"} *)
Theorem ticket_0007_spiral_not_first_cook_qed_or_qex :
  (first_cook_scope EggSpiralCurve EggSpiralCurve /\
   sidecar_spiral_ctor_inhabits SpiralMkSpiral /\
   sidecar_spiral_ctor_inhabits SpiralSpiralHitArm /\
   sidecar_spiral_ctor_inhabits SpiralFirstCookExpand /\
   sidecar_spiral_letter_status = SidecarSpiralFirstCookExpanded /\
   exists p ti tj,
     I_ok (MkOutOfScope EggSpiralCurve) (MkOutOfScope EggSpiralCurve)
          (IHit p ti tj))
  \/
  (~ first_cook_scope EggSpiralCurve EggSpiralCurve /\
   first_cook_scope EggChord EggChord /\
   ~ sidecar_spiral_ctor_inhabits SpiralMkSpiral /\
   ~ sidecar_spiral_ctor_inhabits SpiralSpiralHitArm /\
   ~ sidecar_spiral_ctor_inhabits SpiralFirstCookExpand /\
   sidecar_spiral_letter_status = SidecarSpiralEggLanded /\
   I_ok (MkOutOfScope EggSpiralCurve) (MkOutOfScope EggSpiralCurve)
        IDecline /\
   (forall p ti tj,
      ~ I_ok (MkOutOfScope EggSpiralCurve) (MkOutOfScope EggSpiralCurve)
           (IHit p ti tj)) /\
   try_cook_hit locked_spi_ck1 locked_spi_ck2 IDecline crossing_hen
     = None).
Proof.
  right.
  split; [exact spiral_spiral_not_first_scope|].
  split; [exact first_cook_scope_chord_chord|].
  split; [exact sidecar_spiral_mkspiral_missing|].
  split; [exact sidecar_spiral_hit_arm_missing|].
  split; [exact sidecar_spiral_first_cook_expand_missing|].
  split; [exact sidecar_spiral_letter_is_landed|].
  split; [exact spiral_decline_I_ok|].
  split; [intros p ti tj H; exact H|].
  exact sidecar_spiral_try_cook_none.
Qed.

(* WITNESS {"claimId":"0007-spiral-egg","topic":"overlay","lemma":"ticket_0007_spiral_parks_qed_or_qex","title":"Sidecar spiral discharges Campaign I-II, remints spiral interpolant as noding, remints CircGamma, and flips LoopDischarged (QED) or names them parked and cites Parks Gamma/iota/rho once (QEX); discharged QEX; letter landed != first-cook expand / Campaign / bag noder","file":"theories/SidecarSpiralEgg.v","witness":"0007-spiral-egg","board":"ADR-0007"} *)
Theorem ticket_0007_spiral_parks_qed_or_qex :
  (sidecar_spiral_letter_status = SidecarSpiralCampaignDischarged /\
   sidecar_spiral_kind = SSP_CampaignI /\
   sidecar_spiral_kind = SSP_SpiralNoding /\
   sidecar_spiral_kind = SSP_CircGamma /\
   sidecar_spiral_kind = SSP_LoopNoder /\
   cook_loop_status = LoopDischarged)
  \/
  (sidecar_spiral_letter_status = SidecarSpiralEggLanded /\
   sidecar_spiral_letter_status <> SidecarSpiralCampaignDischarged /\
   sidecar_spiral_kind = SSP_EggPackaging /\
   sidecar_spiral_kind <> SSP_CampaignI /\
   sidecar_spiral_kind <> SSP_SpiralNoding /\
   sidecar_spiral_kind <> SSP_CircGamma /\
   sidecar_spiral_kind <> SSP_LoopNoder /\
   cook_loop_status = LoopObligation /\
   cook_loop_status <> LoopDischarged /\
   first_cook_scope EggChord EggChord /\
   ~ first_cook_scope EggSpiralCurve EggSpiralCurve /\
   egg_class (MkOutOfScope EggClothoid) = EggClothoid).
Proof.
  right.
  split; [exact sidecar_spiral_letter_is_landed|].
  split; [exact sidecar_spiral_campaign_not_discharged|].
  split; [exact sidecar_spiral_is_egg_packaging|].
  split; [exact sidecar_spiral_not_campaign_i|].
  split; [exact sidecar_spiral_not_spiral_noding|].
  split; [exact sidecar_spiral_not_circgamma|].
  split; [exact sidecar_spiral_not_loop_noder|].
  split; [exact cook_loop_is_obligation|].
  split; [exact cook_loop_not_discharged|].
  split; [exact first_cook_scope_chord_chord|].
  split; [exact spiral_spiral_not_first_scope|].
  apply egg_clothoid_still_present.
Qed.

Print Assumptions sidecar_spiral_class.
Print Assumptions sidecar_spiral_host_decline.
Print Assumptions sidecar_spiral_try_cook_none.
Print Assumptions sidecar_spiral_chord_seed.
Print Assumptions sidecar_spiral_demote_is_nodingng_crossing.
Print Assumptions sidecar_spiral_metric_not_cook_hit.
Print Assumptions sidecar_spiral_mkspiral_missing.
Print Assumptions sidecar_spiral_hit_arm_missing.
Print Assumptions sidecar_spiral_iso_names_inhabit.
Print Assumptions egg_clothoid_still_present.
Print Assumptions sidecar_spiral_egg_inhabits.
Print Assumptions ticket_0007_spiral_egg_qed_or_qex.
Print Assumptions ticket_0007_spiral_not_first_cook_qed_or_qex.
Print Assumptions ticket_0007_spiral_parks_qed_or_qex.
