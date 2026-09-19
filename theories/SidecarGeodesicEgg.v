(* ============================================================================
   NetTopologySuite.Proofs.SidecarGeodesicEgg
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: SQL/MM GeodesicString egg sidecar
   (claimId 0007-geodesicstring-egg).

   Product / sidecar face: EggGeodesicString on the ADR-0007 sheet /
   hen / cook vocabulary. Host EggClass did not have this arm —
   this letter adds the constructor only (MkOutOfScope tag). No
   Decline / not-first-cook / try_cook lemmas were added to
   SheetHenCook. Those live here and cite existing first_cook_scope
   / I_ok / try_cook_hit_out_of_scope_none. Prefer SidecarGeodesic*
   over reminting host cook (same preference as SidecarElliptic* /
   SidecarCircEgg* / SidecarSin* / SidecarNurbs* / SidecarClothoid*
   for non-host).

   SQL/MM ST_GeodesicString (ISO 13249-3 §4.2.8) is type-zoo
   packaging. CONTEXT Zoo still lists GEODESICSTRING as expansion
   backlog — this letter does not mint Zoo membership and does not
   invent a geodesic interpolant. Demote-to-chord reuses
   RelateLineLine; no ellipsoid / CRS math.

   One honest first rung. One locked fixture. Do not ship a
   geodesic×geodesic noder, Spiral egg, or Campaign I–II in this
   letter.

   QED: sidecar egg packaging on EggGeodesicString; host I_ok
   Decline and try_cook_hit None; locked unit-square geodesic
   chords demote to the host crossing pair; demote-to-chord is
   NodingNG / host first cook, not a geodesic Hit.

   QEX: geodesic×geodesic is not first cook (checklist 4). Named
   missing constructor: no MkGeodesic on Egg, no I_ok Hit arm
   on geodesic eggs, no first-cook expand. Do not fake first-cook
   expand or LoopDischarged. Do not remint geodetic interpolant
   as noding.

   What this is not:
     Host first_cook_scope / try_cook_hit expand to
     geodesic×geodesic. CircGamma / ι / ρ remint. MkCirc.
     Spiral egg. Host circular cook. Shewchuk / Hobby / Priest /
     Jordan / HotPixel / OverlayNG snap remint. SQL/MM Multi
     Landed / Phase B done-when / H⊥ / MerkatorBV / 522-n.
     Full geodesic noder. Bag-loop ρ Discharge. Campaign I–II.
     Honesty-chip product. Invented geodesic math.

   Parks Γ / ι / ρ (named QEX, landed). This letter cites them
   once; it does not remint CircGamma, ι, leftover_width, or
   LoopDischarged. First cook stays chord–chord. Host CircGamma
   stays QEX.

   ADR-0007 is Accepted (2026-09-07). This letter does not reopen
   Status. QEX is not a new Accept cycle. ADR-0006 Status stays
   Accepted. Testable 𝓘 / cook results sit on the accepted Oracle
   line protocol. This module mints no keyword and no second
   external seam.

   WITNESS topic: overlay · claimId: 0007-geodesicstring-egg
   witness: 0007-geodesicstring-egg
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
(* Product face: a sidecar geodesic egg is a named EggGeodesicString          *)
(* interpolant tag plus a start/end chord seed. Host Egg has no               *)
(* MkGeodesic. The seed is demote-to-chord packaging, not a geodetic          *)
(* interpolant.                                                               *)
(* -------------------------------------------------------------------------- *)

Record GeodesicChord : Type := mkGeodesicChord {
  gc_start : Point;
  gc_end   : Point
}.

Record SidecarGeodesicEgg : Type := mkSidecarGeodesicEgg {
  sge_sheet : Sheet;
  sge_chord : GeodesicChord
}.

Definition sidecar_geodesic_host_egg (_ : SidecarGeodesicEgg) : Egg :=
  MkOutOfScope EggGeodesicString.

Definition sidecar_geodesic_demote (e : SidecarGeodesicEgg) : ChordEgg :=
  mkChordEgg (gc_start (sge_chord e)) (gc_end (sge_chord e)).

Definition sidecar_geodesic_chicken (src dst : Hen) (e : SidecarGeodesicEgg)
  : Chicken :=
  mkChicken src dst (sidecar_geodesic_host_egg e).

Definition geodesic_chord_proper_cross (c : GeodesicChord) (P Q : Point) : Prop :=
  segments_proper_cross (gc_start c) (gc_end c) P Q.

Definition geodesic_chord_share (c : GeodesicChord) (P Q : Point) : Prop :=
  segments_share (gc_start c) (gc_end c) P Q.

Lemma sidecar_geodesic_class :
  forall e, egg_class (sidecar_geodesic_host_egg e) = EggGeodesicString.
Proof.
  intros e. reflexivity.
Qed.

Lemma sidecar_geodesic_only_out_of_scope :
  forall e, sidecar_geodesic_host_egg e = MkOutOfScope EggGeodesicString.
Proof.
  intros e. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked fixture: unit-square diagonals as geodesic start/end. Same          *)
(* geometry as NodingNG's crossing pair — the demoted chord seed, not         *)
(* a geodesic cook.                                                           *)
(* -------------------------------------------------------------------------- *)

Definition locked_geo_ab : GeodesicChord :=
  mkGeodesicChord (ce_p0 diag_ab) (ce_p1 diag_ab).

Definition locked_geo_cd : GeodesicChord :=
  mkGeodesicChord (ce_p0 diag_cd) (ce_p1 diag_cd).

Definition locked_sge_ab : SidecarGeodesicEgg :=
  mkSidecarGeodesicEgg default_sheet locked_geo_ab.

Definition locked_sge_cd : SidecarGeodesicEgg :=
  mkSidecarGeodesicEgg default_sheet locked_geo_cd.

Definition locked_geo_ck1 : Chicken :=
  sidecar_geodesic_chicken 0%nat 1%nat locked_sge_ab.

Definition locked_geo_ck2 : Chicken :=
  sidecar_geodesic_chicken 2%nat 3%nat locked_sge_cd.

Lemma locked_geo_demote_is_host_crossing :
  sidecar_geodesic_demote locked_sge_ab = diag_ab /\
  sidecar_geodesic_demote locked_sge_cd = diag_cd.
Proof.
  split; reflexivity.
Qed.

Lemma locked_geo_same_sheet_as_nodingng :
  sge_sheet locked_sge_ab = default_sheet /\
  sge_sheet locked_sge_cd = nng_sheet nodingng_crossing_pair.
Proof.
  split; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Decline-on-host. Geodesic eggs stay MkOutOfScope. Not a constructed Hit.   *)
(* Lemmas live here (SheetHenCook must not grow lemmas). Cite                *)
(* first_cook_scope / I_ok / try_cook_hit — same occupants as SIN #719 /     *)
(* Elliptic #721 sidecar copies.                                              *)
(* -------------------------------------------------------------------------- *)

Lemma geodesic_geodesic_not_first_scope :
  ~ first_cook_scope EggGeodesicString EggGeodesicString.
Proof.
  intro H. exact H.
Qed.

Lemma geodesic_decline_I_ok :
  I_ok (MkOutOfScope EggGeodesicString) (MkOutOfScope EggGeodesicString)
       IDecline.
Proof.
  unfold I_ok, first_cook_scope, egg_class.
  intro H. exact H.
Qed.

Lemma sidecar_geodesic_host_decline :
  I_ok (sidecar_geodesic_host_egg locked_sge_ab)
       (sidecar_geodesic_host_egg locked_sge_cd) IDecline.
Proof.
  exact geodesic_decline_I_ok.
Qed.

Lemma sidecar_geodesic_host_hit_false :
  forall p ti tj,
    ~ I_ok (sidecar_geodesic_host_egg locked_sge_ab)
           (sidecar_geodesic_host_egg locked_sge_cd) (IHit p ti tj).
Proof.
  intros p ti tj H. exact H.
Qed.

Lemma sidecar_geodesic_host_empty_false :
  ~ I_ok (sidecar_geodesic_host_egg locked_sge_ab)
         (sidecar_geodesic_host_egg locked_sge_cd) IEmpty.
Proof.
  intro H. exact H.
Qed.

Lemma sidecar_geodesic_try_cook_none :
  try_cook_hit locked_geo_ck1 locked_geo_ck2 IDecline crossing_hen
    = None.
Proof.
  reflexivity.
Qed.

Lemma sidecar_geodesic_try_cook_hit_none :
  forall p ti tj h,
    try_cook_hit locked_geo_ck1 locked_geo_ck2 (IHit p ti tj) h
      = None.
Proof.
  intros p ti tj h.
  reflexivity.
Qed.

Lemma sidecar_geodesic_empty_neq_decline : IEmpty <> IDecline.
Proof.
  exact IEmpty_neq_IDecline.
Qed.

(* -------------------------------------------------------------------------- *)
(* Constructive chord-seed. Demoted start/end properly cross and share        *)
(* a point. That is the demoted-chord geometry, not a geodesic×geodesic       *)
(* cook Hit. Reuses RelateLineLine; no geodesic interpolant.                  *)
(* -------------------------------------------------------------------------- *)

Lemma locked_geo_chord_proper_cross :
  geodesic_chord_proper_cross locked_geo_ab
    (gc_start locked_geo_cd) (gc_end locked_geo_cd).
Proof.
  unfold geodesic_chord_proper_cross, locked_geo_ab, locked_geo_cd.
  cbn [gc_start gc_end].
  exact crossing_proper_cross_signs.
Qed.

(* WITNESS {"claimId":"0007-geodesicstring-egg","topic":"overlay","lemma":"sidecar_geodesic_chord_seed","title":"Sidecar geodesic locked unit-square chords reuse line-line proper-cross share; demoted-chord geometry, not a geodesic times geodesic cook Hit","file":"theories/SidecarGeodesicEgg.v","witness":"0007-geodesicstring-egg","board":"ADR-0007"} *)
Lemma sidecar_geodesic_chord_seed :
  geodesic_chord_share locked_geo_ab
    (gc_start locked_geo_cd) (gc_end locked_geo_cd).
Proof.
  unfold geodesic_chord_share, geodesic_chord_proper_cross in *.
  eapply line_line_proper_cross_geom.
  exact locked_geo_chord_proper_cross.
Qed.

(* Demote-to-chord inhabits host / NodingNG first cook. Not a geodesic Hit. *)
Lemma sidecar_geodesic_demote_is_nodingng_crossing :
  sidecar_geodesic_demote locked_sge_ab = diag_ab /\
  sidecar_geodesic_demote locked_sge_cd = diag_cd /\
  I_ok (MkChord (sidecar_geodesic_demote locked_sge_ab))
       (MkChord (sidecar_geodesic_demote locked_sge_cd))
       (IHit cross_pt (1 / 2) (1 / 2)) /\
  nodingng_hit_cooks nodingng_crossing_pair crossing_hen.
Proof.
  destruct locked_geo_demote_is_host_crossing as [Hab Hcd].
  split; [exact Hab|].
  split; [exact Hcd|].
  rewrite Hab, Hcd.
  split; [exact crossing_I_ok|].
  exact nodingng_crossing_hit_cooks.
Qed.

Lemma sidecar_geodesic_demote_hit_not_geodesic_I_ok :
  I_ok (MkChord (sidecar_geodesic_demote locked_sge_ab))
       (MkChord (sidecar_geodesic_demote locked_sge_cd))
       (IHit cross_pt (1 / 2) (1 / 2)) /\
  ~ I_ok (sidecar_geodesic_host_egg locked_sge_ab)
         (sidecar_geodesic_host_egg locked_sge_cd)
         (IHit cross_pt (1 / 2) (1 / 2)).
Proof.
  split.
  - apply sidecar_geodesic_demote_is_nodingng_crossing.
  - apply sidecar_geodesic_host_hit_false.
Qed.

(* SQL/MM ST_GeodesicString type-zoo packaging. Geodetic interpolant
   stays research — not a cook Hit, not a geodesic noder. Named:
   type zoo ≠ cook. No invented ellipsoid math. *)
Inductive SidecarGeodesicMetricKind : Type :=
| SGM_SqlMmTypeZoo
| SGM_CookHit.

Definition sidecar_geodesic_metric_kind : SidecarGeodesicMetricKind :=
  SGM_SqlMmTypeZoo.

Lemma sidecar_geodesic_metric_is_type_zoo :
  sidecar_geodesic_metric_kind = SGM_SqlMmTypeZoo.
Proof.
  reflexivity.
Qed.

Lemma sidecar_geodesic_metric_not_cook_hit :
  sidecar_geodesic_metric_kind <> SGM_CookHit.
Proof.
  discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* Named missing constructors. 508-style, not bools.                          *)
(* -------------------------------------------------------------------------- *)

Inductive SidecarGeodesicCookCtor : Type :=
| GeodesicMkGeodesic
| GeodesicGeodesicHitArm
| GeodesicFirstCookExpand.

Definition sidecar_geodesic_ctor_inhabits
  (c : SidecarGeodesicCookCtor) : Prop :=
  match c with
  | GeodesicMkGeodesic => False
  | GeodesicGeodesicHitArm => False
  | GeodesicFirstCookExpand => False
  end.

Lemma sidecar_geodesic_mkgeodesic_missing :
  ~ sidecar_geodesic_ctor_inhabits GeodesicMkGeodesic.
Proof.
  intro H. exact H.
Qed.

Lemma sidecar_geodesic_hit_arm_missing :
  ~ sidecar_geodesic_ctor_inhabits GeodesicGeodesicHitArm.
Proof.
  intro H. exact H.
Qed.

Lemma sidecar_geodesic_first_cook_expand_missing :
  ~ sidecar_geodesic_ctor_inhabits GeodesicFirstCookExpand.
Proof.
  intro H. exact H.
Qed.

Lemma sidecar_geodesic_not_first_cook :
  ~ first_cook_scope EggGeodesicString EggGeodesicString.
Proof.
  exact geodesic_geodesic_not_first_scope.
Qed.

Lemma sidecar_geodesic_first_cook_stays_chord_chord :
  first_cook_scope EggChord EggChord /\
  ~ first_cook_scope EggGeodesicString EggGeodesicString /\
  ~ first_cook_scope EggEllipse EggEllipse /\
  ~ first_cook_scope EggNurbs EggNurbs /\
  first_cook_scope EggClothoid EggClothoid /\
  first_cook_scope EggCircularArc EggCircularArc.
Proof.
  split; [exact first_cook_scope_chord_chord|].
  split; [exact geodesic_geodesic_not_first_scope|].
  split; [exact ellipse_ellipse_not_first_scope|].
  split; [exact nurbs_nurbs_not_first_scope|].
  split; [exact clothoid_egg_first_cook_scope|].
  exact circular_egg_first_cook_scope.
Qed.

(* -------------------------------------------------------------------------- *)
(* What the sidecar is / is not. Kind tag, not a second kernel.               *)
(* -------------------------------------------------------------------------- *)

Inductive SidecarGeodesicKind : Type :=
| SGE_EggPackaging
| SGE_HostCook
| SGE_NodingNG
| SGE_GeodeticNoding
| SGE_CircGamma
| SGE_CampaignI
| SGE_LoopNoder.

Definition sidecar_geodesic_kind : SidecarGeodesicKind := SGE_EggPackaging.

Lemma sidecar_geodesic_is_egg_packaging :
  sidecar_geodesic_kind = SGE_EggPackaging.
Proof.
  reflexivity.
Qed.

Lemma sidecar_geodesic_not_host_cook :
  sidecar_geodesic_kind <> SGE_HostCook.
Proof.
  discriminate.
Qed.

Lemma sidecar_geodesic_not_nodingng :
  sidecar_geodesic_kind <> SGE_NodingNG.
Proof.
  discriminate.
Qed.

Lemma sidecar_geodesic_not_geodetic_noding :
  sidecar_geodesic_kind <> SGE_GeodeticNoding.
Proof.
  discriminate.
Qed.

Lemma sidecar_geodesic_not_circgamma :
  sidecar_geodesic_kind <> SGE_CircGamma.
Proof.
  discriminate.
Qed.

Lemma sidecar_geodesic_not_campaign_i :
  sidecar_geodesic_kind <> SGE_CampaignI.
Proof.
  discriminate.
Qed.

Lemma sidecar_geodesic_not_loop_noder :
  sidecar_geodesic_kind <> SGE_LoopNoder.
Proof.
  discriminate.
Qed.

Inductive SidecarGeodesicLetterStatus : Type :=
| SidecarGeodesicEggLanded
| SidecarGeodesicFirstCookExpanded
| SidecarGeodesicCampaignDischarged.

Definition sidecar_geodesic_letter_status : SidecarGeodesicLetterStatus :=
  SidecarGeodesicEggLanded.

Lemma sidecar_geodesic_letter_is_landed :
  sidecar_geodesic_letter_status = SidecarGeodesicEggLanded.
Proof.
  reflexivity.
Qed.

Lemma sidecar_geodesic_not_first_cook_expanded :
  sidecar_geodesic_letter_status <> SidecarGeodesicFirstCookExpanded.
Proof.
  discriminate.
Qed.

Lemma sidecar_geodesic_campaign_not_discharged :
  sidecar_geodesic_letter_status <> SidecarGeodesicCampaignDischarged.
Proof.
  discriminate.
Qed.

(* Named QED package: egg + Decline-on-host + locked chord-seed. *)
Lemma sidecar_geodesic_egg_inhabits :
  egg_class (sidecar_geodesic_host_egg locked_sge_ab) = EggGeodesicString /\
  sidecar_geodesic_host_egg locked_sge_ab = MkOutOfScope EggGeodesicString /\
  I_ok (sidecar_geodesic_host_egg locked_sge_ab)
       (sidecar_geodesic_host_egg locked_sge_cd) IDecline /\
  try_cook_hit locked_geo_ck1 locked_geo_ck2 IDecline crossing_hen
    = None /\
  geodesic_chord_share locked_geo_ab
    (gc_start locked_geo_cd) (gc_end locked_geo_cd) /\
  I_ok (MkChord (sidecar_geodesic_demote locked_sge_ab))
       (MkChord (sidecar_geodesic_demote locked_sge_cd))
       (IHit cross_pt (1 / 2) (1 / 2)) /\
  IEmpty <> IDecline /\
  sidecar_geodesic_kind = SGE_EggPackaging /\
  sidecar_geodesic_metric_kind = SGM_SqlMmTypeZoo.
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact sidecar_geodesic_host_decline|].
  split; [exact sidecar_geodesic_try_cook_none|].
  split; [exact sidecar_geodesic_chord_seed|].
  split; [apply sidecar_geodesic_demote_hit_not_geodesic_I_ok|].
  split; [exact sidecar_geodesic_empty_neq_decline|].
  split; [reflexivity|].
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-geodesicstring-egg","topic":"overlay","lemma":"ticket_0007_geodesic_egg_qed_or_qex","title":"Sidecar geodesic egg packages EggGeodesicString Decline-on-host and locked demoted-chord seed (QED) or host I_ok is a geodesic Hit (QEX); discharged QED; demote-to-chord is NodingNG first cook, not a geodesic times geodesic cook; SQL/MM type zoo stays packaging","file":"theories/SidecarGeodesicEgg.v","witness":"0007-geodesicstring-egg","board":"ADR-0007"} *)
Theorem ticket_0007_geodesic_egg_qed_or_qex :
  (egg_class (sidecar_geodesic_host_egg locked_sge_ab) = EggGeodesicString /\
   sidecar_geodesic_host_egg locked_sge_ab = MkOutOfScope EggGeodesicString /\
   I_ok (sidecar_geodesic_host_egg locked_sge_ab)
        (sidecar_geodesic_host_egg locked_sge_cd) IDecline /\
   try_cook_hit locked_geo_ck1 locked_geo_ck2 IDecline crossing_hen
     = None /\
   geodesic_chord_share locked_geo_ab
     (gc_start locked_geo_cd) (gc_end locked_geo_cd) /\
   I_ok (MkChord (sidecar_geodesic_demote locked_sge_ab))
        (MkChord (sidecar_geodesic_demote locked_sge_cd))
        (IHit cross_pt (1 / 2) (1 / 2)) /\
   ~ I_ok (sidecar_geodesic_host_egg locked_sge_ab)
          (sidecar_geodesic_host_egg locked_sge_cd)
          (IHit cross_pt (1 / 2) (1 / 2)) /\
   IEmpty <> IDecline /\
   sidecar_geodesic_kind = SGE_EggPackaging /\
   sidecar_geodesic_kind <> SGE_HostCook /\
   sidecar_geodesic_kind <> SGE_NodingNG /\
   sidecar_geodesic_kind <> SGE_GeodeticNoding /\
   sidecar_geodesic_metric_kind = SGM_SqlMmTypeZoo /\
   sidecar_geodesic_metric_kind <> SGM_CookHit)
  \/
  (exists p ti tj,
     I_ok (MkOutOfScope EggGeodesicString) (MkOutOfScope EggGeodesicString)
          (IHit p ti tj)).
Proof.
  left.
  destruct sidecar_geodesic_egg_inhabits
    as [Hcls [Htag [Hdec [Hnone [Hseed [Hdem [Hneq [Hkind Hmet]]]]]]]].
  split; [exact Hcls|].
  split; [exact Htag|].
  split; [exact Hdec|].
  split; [exact Hnone|].
  split; [exact Hseed|].
  split; [exact Hdem|].
  split; [apply sidecar_geodesic_host_hit_false|].
  split; [exact Hneq|].
  split; [exact Hkind|].
  split; [exact sidecar_geodesic_not_host_cook|].
  split; [exact sidecar_geodesic_not_nodingng|].
  split; [exact sidecar_geodesic_not_geodetic_noding|].
  split; [exact Hmet|].
  exact sidecar_geodesic_metric_not_cook_hit.
Qed.

(* WITNESS {"claimId":"0007-geodesicstring-egg","topic":"overlay","lemma":"ticket_0007_geodesic_not_first_cook_qed_or_qex","title":"Sidecar geodesic expands first_cook_scope to geodesic times geodesic and inhabits I_ok Hit (QED) or geodesic times geodesic stays QEX with named MkGeodesic / Hit-arm gaps (QEX); discharged QEX; checklist 4; do not fake first-cook expand","file":"theories/SidecarGeodesicEgg.v","witness":"0007-geodesicstring-egg","board":"ADR-0007"} *)
Theorem ticket_0007_geodesic_not_first_cook_qed_or_qex :
  (first_cook_scope EggGeodesicString EggGeodesicString /\
   sidecar_geodesic_ctor_inhabits GeodesicMkGeodesic /\
   sidecar_geodesic_ctor_inhabits GeodesicGeodesicHitArm /\
   sidecar_geodesic_ctor_inhabits GeodesicFirstCookExpand /\
   sidecar_geodesic_letter_status = SidecarGeodesicFirstCookExpanded /\
   exists p ti tj,
     I_ok (MkOutOfScope EggGeodesicString) (MkOutOfScope EggGeodesicString)
          (IHit p ti tj))
  \/
  (~ first_cook_scope EggGeodesicString EggGeodesicString /\
   first_cook_scope EggChord EggChord /\
   ~ sidecar_geodesic_ctor_inhabits GeodesicMkGeodesic /\
   ~ sidecar_geodesic_ctor_inhabits GeodesicGeodesicHitArm /\
   ~ sidecar_geodesic_ctor_inhabits GeodesicFirstCookExpand /\
   sidecar_geodesic_letter_status = SidecarGeodesicEggLanded /\
   I_ok (MkOutOfScope EggGeodesicString) (MkOutOfScope EggGeodesicString)
        IDecline /\
   (forall p ti tj,
      ~ I_ok (MkOutOfScope EggGeodesicString) (MkOutOfScope EggGeodesicString)
           (IHit p ti tj)) /\
   try_cook_hit locked_geo_ck1 locked_geo_ck2 IDecline crossing_hen
     = None).
Proof.
  right.
  split; [exact geodesic_geodesic_not_first_scope|].
  split; [exact first_cook_scope_chord_chord|].
  split; [exact sidecar_geodesic_mkgeodesic_missing|].
  split; [exact sidecar_geodesic_hit_arm_missing|].
  split; [exact sidecar_geodesic_first_cook_expand_missing|].
  split; [exact sidecar_geodesic_letter_is_landed|].
  split; [exact geodesic_decline_I_ok|].
  split; [intros p ti tj H; exact H|].
  exact sidecar_geodesic_try_cook_none.
Qed.

(* WITNESS {"claimId":"0007-geodesicstring-egg","topic":"overlay","lemma":"ticket_0007_geodesic_parks_qed_or_qex","title":"Sidecar geodesic discharges Campaign I-II, remints geodetic interpolant as noding, remints CircGamma, and flips LoopDischarged (QED) or names them parked and cites Parks Gamma/iota/rho once (QEX); discharged QEX; letter landed != first-cook expand / Campaign / bag noder","file":"theories/SidecarGeodesicEgg.v","witness":"0007-geodesicstring-egg","board":"ADR-0007"} *)
Theorem ticket_0007_geodesic_parks_qed_or_qex :
  (sidecar_geodesic_letter_status = SidecarGeodesicCampaignDischarged /\
   sidecar_geodesic_kind = SGE_CampaignI /\
   sidecar_geodesic_kind = SGE_GeodeticNoding /\
   sidecar_geodesic_kind = SGE_CircGamma /\
   sidecar_geodesic_kind = SGE_LoopNoder /\
   cook_loop_status = LoopDischarged)
  \/
  (sidecar_geodesic_letter_status = SidecarGeodesicEggLanded /\
   sidecar_geodesic_letter_status <> SidecarGeodesicCampaignDischarged /\
   sidecar_geodesic_kind = SGE_EggPackaging /\
   sidecar_geodesic_kind <> SGE_CampaignI /\
   sidecar_geodesic_kind <> SGE_GeodeticNoding /\
   sidecar_geodesic_kind <> SGE_CircGamma /\
   sidecar_geodesic_kind <> SGE_LoopNoder /\
   cook_loop_status = LoopObligation /\
   cook_loop_status <> LoopDischarged /\
   first_cook_scope EggChord EggChord /\
   ~ first_cook_scope EggGeodesicString EggGeodesicString).
Proof.
  right.
  split; [exact sidecar_geodesic_letter_is_landed|].
  split; [exact sidecar_geodesic_campaign_not_discharged|].
  split; [exact sidecar_geodesic_is_egg_packaging|].
  split; [exact sidecar_geodesic_not_campaign_i|].
  split; [exact sidecar_geodesic_not_geodetic_noding|].
  split; [exact sidecar_geodesic_not_circgamma|].
  split; [exact sidecar_geodesic_not_loop_noder|].
  split; [exact cook_loop_is_obligation|].
  split; [exact cook_loop_not_discharged|].
  split; [exact first_cook_scope_chord_chord|].
  exact geodesic_geodesic_not_first_scope.
Qed.

Print Assumptions sidecar_geodesic_class.
Print Assumptions sidecar_geodesic_host_decline.
Print Assumptions sidecar_geodesic_try_cook_none.
Print Assumptions sidecar_geodesic_chord_seed.
Print Assumptions sidecar_geodesic_demote_is_nodingng_crossing.
Print Assumptions sidecar_geodesic_metric_not_cook_hit.
Print Assumptions sidecar_geodesic_mkgeodesic_missing.
Print Assumptions sidecar_geodesic_hit_arm_missing.
Print Assumptions sidecar_geodesic_egg_inhabits.
Print Assumptions ticket_0007_geodesic_egg_qed_or_qex.
Print Assumptions ticket_0007_geodesic_not_first_cook_qed_or_qex.
Print Assumptions ticket_0007_geodesic_parks_qed_or_qex.
