(* ============================================================================
   NetTopologySuite.Proofs.SidecarNurbsEgg
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: NURBS egg sidecar
   (claimId 0007-nurbs-egg).

   Product / sidecar face: NURBS as an EggClass on the ADR-0007
   sheet / hen / cook vocabulary. Host already has EggNurbs /
   MkOutOfScope EggNurbs. This letter packages Decline-on-tag
   (nurbs_decline_I_ok / try_cook_hit_nurbs_none) plus one locked
   demoted-chord fixture. Host MkNurbs + NURBS×NURBS first cook
   live in NurbsCookMkNurbs.v. Prefer SidecarNurbs* for the
   tag-packaging face, same preference as SidecarClothoid*.

   The existing NURBS corpus (NurbsQuadraticLength, NurbsGeneralLength,
   NurbsKnotSpans, NurbsConicExact, BernsteinBasis, #508 length lane)
   is metric / length research. This letter packages what is already
   Qed into the egg / cook sidecar story. It does NOT remint
   length / Cox-de-Boor as noding progress. Golden quarter
   (nurbs2_golden_quarter_length) stays a metric cite.
   Host MkNurbs + NURBS×NURBS first cook live in
   NurbsCookMkNurbs.v (claimId 0007-nurbs-first-cook).

   One honest first rung. One locked fixture. Do not ship a
   NURBS×NURBS noder or Campaign I–II in this letter.

   QED: sidecar egg packaging on EggNurbs; host I_ok Decline
   and try_cook_hit None; locked unit-square NURBS chords demote
   to the host crossing pair; demote-to-chord is NodingNG / host
   first cook, not a NURBS Hit.

   Host MkNurbs inhabits. NURBS×NURBS is first cook
   (NurbsCookMkNurbs.v). Tags stay Decline. Do not remint
   #508 length as cook Hit. Parks length-as-noding /
   Cox-de-Boor / Campaign / ρ.

   What this is not:
     Length / Cox-de-Boor reminted as noding. CircGamma / ι / ρ
     remint. MkCirc. Clothoid remint. Host circular cook.
     Shewchuk / Hobby / Priest / Jordan / HotPixel / OverlayNG
     snap remint. SQL/MM Multi Landed / Phase B done-when / H⊥ /
     MerkatorBV / 522-n. Exact* zoo / CurveSegment growth. Full
     NURBS×NURBS noder. Bag-loop ρ Discharge. Tag Hit.

   Parks Γ / ι / ρ (named QEX, landed). This letter cites them
   once; it does not remint CircGamma, ι, leftover_width, or
   LoopDischarged. ι row already records #717 discharge.
   First cook includes NURBS×NURBS (host letter). Host CircGamma
   is discharged (MkCirc).

   ADR-0007 is Accepted (2026-09-07). This letter does not reopen
   Status. QEX is not a new Accept cycle. ADR-0006 Status stays
   Accepted. Testable 𝓘 / cook results sit on the accepted Oracle
   line protocol. This module mints no keyword and no second
   external seam.

   WITNESS topic: overlay · claimId: 0007-nurbs-egg
   witness: 0007-nurbs-egg
   board: ADR-0007
   3-axiom host. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import Distance SheetHenCook NodingNG RelateLineLine
  NurbsCookMkNurbs.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Product face: a sidecar NURBS egg is a named EggNurbs interpolant          *)
(* tag plus a quadratic control net. Sidecar host_egg stays the               *)
(* MkOutOfScope tag (packaging). Host Egg now also has MkNurbs.               *)
(* -------------------------------------------------------------------------- *)

Record NurbsChord : Type := mkNurbsChord {
  nc_start : Point;
  nc_ctrl  : Point;
  nc_end   : Point
}.

Record SidecarNurbsEgg : Type := mkSidecarNurbsEgg {
  sne_sheet : Sheet;
  sne_chord : NurbsChord
}.

Definition sidecar_nurbs_host_egg (_ : SidecarNurbsEgg) : Egg :=
  MkOutOfScope EggNurbs.

Definition sidecar_nurbs_demote (e : SidecarNurbsEgg) : ChordEgg :=
  mkChordEgg (nc_start (sne_chord e)) (nc_end (sne_chord e)).

Definition sidecar_nurbs_chicken (src dst : Hen) (e : SidecarNurbsEgg)
  : Chicken :=
  mkChicken src dst (sidecar_nurbs_host_egg e).

Definition nurbs_chord_proper_cross (c : NurbsChord) (P Q : Point) : Prop :=
  segments_proper_cross (nc_start c) (nc_end c) P Q.

Definition nurbs_chord_share (c : NurbsChord) (P Q : Point) : Prop :=
  segments_share (nc_start c) (nc_end c) P Q.

Lemma sidecar_nurbs_class :
  forall e, egg_class (sidecar_nurbs_host_egg e) = EggNurbs.
Proof.
  intros e. reflexivity.
Qed.

Lemma sidecar_nurbs_only_out_of_scope :
  forall e, sidecar_nurbs_host_egg e = MkOutOfScope EggNurbs.
Proof.
  intros e. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked fixture: unit-square diagonals as NURBS start/end, with an          *)
(* off-chord control point. Same geometry as NodingNG's crossing pair —       *)
(* the demoted chord seed, not a NURBS cook.                                  *)
(* -------------------------------------------------------------------------- *)

Definition locked_nurbs_ab : NurbsChord :=
  mkNurbsChord (ce_p0 diag_ab) (mkPoint 2 0) (ce_p1 diag_ab).

Definition locked_nurbs_cd : NurbsChord :=
  mkNurbsChord (ce_p0 diag_cd) (mkPoint 0 0) (ce_p1 diag_cd).

Definition locked_sne_ab : SidecarNurbsEgg :=
  mkSidecarNurbsEgg default_sheet locked_nurbs_ab.

Definition locked_sne_cd : SidecarNurbsEgg :=
  mkSidecarNurbsEgg default_sheet locked_nurbs_cd.

Definition locked_nurbs_ck1 : Chicken :=
  sidecar_nurbs_chicken 0%nat 1%nat locked_sne_ab.

Definition locked_nurbs_ck2 : Chicken :=
  sidecar_nurbs_chicken 2%nat 3%nat locked_sne_cd.

Lemma locked_nurbs_demote_is_host_crossing :
  sidecar_nurbs_demote locked_sne_ab = diag_ab /\
  sidecar_nurbs_demote locked_sne_cd = diag_cd.
Proof.
  split; reflexivity.
Qed.

Lemma locked_nurbs_same_sheet_as_nodingng :
  sne_sheet locked_sne_ab = default_sheet /\
  sne_sheet locked_sne_cd = nng_sheet nodingng_crossing_pair.
Proof.
  split; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Decline-on-host. NURBS eggs stay MkOutOfScope. Not a constructed Hit.      *)
(* -------------------------------------------------------------------------- *)

Lemma sidecar_nurbs_host_decline :
  I_ok (sidecar_nurbs_host_egg locked_sne_ab)
       (sidecar_nurbs_host_egg locked_sne_cd) IDecline.
Proof.
  exact nurbs_decline_I_ok.
Qed.

Lemma sidecar_nurbs_host_hit_false :
  forall p ti tj,
    ~ I_ok (sidecar_nurbs_host_egg locked_sne_ab)
           (sidecar_nurbs_host_egg locked_sne_cd) (IHit p ti tj).
Proof.
  intros p ti tj H. exact H.
Qed.

Lemma sidecar_nurbs_host_empty_false :
  ~ I_ok (sidecar_nurbs_host_egg locked_sne_ab)
         (sidecar_nurbs_host_egg locked_sne_cd) IEmpty.
Proof.
  intro H. exact H.
Qed.

Lemma sidecar_nurbs_try_cook_none :
  try_cook_hit locked_nurbs_ck1 locked_nurbs_ck2 IDecline crossing_hen
    = None.
Proof.
  reflexivity.
Qed.

Lemma sidecar_nurbs_try_cook_hit_none :
  forall p ti tj h,
    try_cook_hit locked_nurbs_ck1 locked_nurbs_ck2 (IHit p ti tj) h
      = None.
Proof.
  intros p ti tj h.
  reflexivity.
Qed.

Lemma sidecar_nurbs_empty_neq_decline : IEmpty <> IDecline.
Proof.
  exact IEmpty_neq_IDecline.
Qed.

(* -------------------------------------------------------------------------- *)
(* Constructive chord-seed. Demoted start/end properly cross and share        *)
(* a point. That is the demoted-chord geometry, not a NURBS×NURBS cook Hit.   *)
(* -------------------------------------------------------------------------- *)

Lemma locked_nurbs_chord_proper_cross :
  nurbs_chord_proper_cross locked_nurbs_ab
    (nc_start locked_nurbs_cd) (nc_end locked_nurbs_cd).
Proof.
  unfold nurbs_chord_proper_cross, locked_nurbs_ab, locked_nurbs_cd.
  cbn [nc_start nc_end].
  exact crossing_proper_cross_signs.
Qed.

(* WITNESS {"claimId":"0007-nurbs-egg","topic":"overlay","lemma":"sidecar_nurbs_chord_seed","title":"Sidecar NURBS locked unit-square chords reuse line-line proper-cross share; demoted-chord geometry, not a NURBS times NURBS cook Hit","file":"theories/SidecarNurbsEgg.v","witness":"0007-nurbs-egg","board":"ADR-0007"} *)
Lemma sidecar_nurbs_chord_seed :
  nurbs_chord_share locked_nurbs_ab
    (nc_start locked_nurbs_cd) (nc_end locked_nurbs_cd).
Proof.
  unfold nurbs_chord_share, nurbs_chord_proper_cross in *.
  eapply line_line_proper_cross_geom.
  exact locked_nurbs_chord_proper_cross.
Qed.

(* Demote-to-chord inhabits host / NodingNG first cook. Not a NURBS Hit. *)
Lemma sidecar_nurbs_demote_is_nodingng_crossing :
  sidecar_nurbs_demote locked_sne_ab = diag_ab /\
  sidecar_nurbs_demote locked_sne_cd = diag_cd /\
  I_ok (MkChord (sidecar_nurbs_demote locked_sne_ab))
       (MkChord (sidecar_nurbs_demote locked_sne_cd))
       (IHit cross_pt (1 / 2) (1 / 2)) /\
  nodingng_hit_cooks nodingng_crossing_pair crossing_hen.
Proof.
  destruct locked_nurbs_demote_is_host_crossing as [Hab Hcd].
  split; [exact Hab|].
  split; [exact Hcd|].
  rewrite Hab, Hcd.
  split; [exact crossing_I_ok|].
  exact nodingng_crossing_hit_cooks.
Qed.

Lemma sidecar_nurbs_demote_hit_not_nurbs_I_ok :
  I_ok (MkChord (sidecar_nurbs_demote locked_sne_ab))
       (MkChord (sidecar_nurbs_demote locked_sne_cd))
       (IHit cross_pt (1 / 2) (1 / 2)) /\
  ~ I_ok (sidecar_nurbs_host_egg locked_sne_ab)
         (sidecar_nurbs_host_egg locked_sne_cd)
         (IHit cross_pt (1 / 2) (1 / 2)).
Proof.
  split.
  - apply sidecar_nurbs_demote_is_nodingng_crossing.
  - apply sidecar_nurbs_host_hit_false.
Qed.

(* #508 length lane is already Qed (golden quarter, equal-weights
   N⊃B, knot-span additivity). Metric / length research — not a
   cook Hit, not Cox-de-Boor noding. Named: length ≠ cook. *)
Inductive SidecarNurbsMetricKind : Type :=
| SNM_LengthResearch
| SNM_CookHit.

Definition sidecar_nurbs_metric_kind : SidecarNurbsMetricKind :=
  SNM_LengthResearch.

Lemma sidecar_nurbs_metric_is_length :
  sidecar_nurbs_metric_kind = SNM_LengthResearch.
Proof.
  reflexivity.
Qed.

Lemma sidecar_nurbs_metric_not_cook_hit :
  sidecar_nurbs_metric_kind <> SNM_CookHit.
Proof.
  discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* Named missing constructors. 508-style, not bools.                          *)
(* -------------------------------------------------------------------------- *)

Inductive SidecarNurbsCookCtor : Type :=
| NurbsMkNurbs
| NurbsNurbsHitArm
| NurbsFirstCookExpand.

Definition sidecar_nurbs_ctor_inhabits
  (c : SidecarNurbsCookCtor) : Prop :=
  match c with
  | NurbsMkNurbs => True
  | NurbsNurbsHitArm => True
  | NurbsFirstCookExpand => True
  end.

Lemma sidecar_nurbs_mknurbs_inhabits :
  sidecar_nurbs_ctor_inhabits NurbsMkNurbs.
Proof.
  exact I.
Qed.

Lemma nurbs_egg_mknurbs_or_tag :
  forall e : Egg,
    egg_class e = EggNurbs ->
    (exists n, e = MkNurbs n) \/ e = MkOutOfScope EggNurbs.
Proof.
  intros e He.
  destruct e as [ch | circ | clth | nrbs | cl].
  - unfold egg_class in He. discriminate.
  - unfold egg_class in He. discriminate.
  - unfold egg_class in He. discriminate.
  - left. exists nrbs. reflexivity.
  - unfold egg_class in He. subst cl. right. reflexivity.
Qed.

Lemma mknurbs_class :
  forall n, egg_class (MkNurbs n) = EggNurbs.
Proof.
  intros n. reflexivity.
Qed.

Lemma mknurbs_neq_mkchord :
  forall n d, MkNurbs n <> MkChord d.
Proof.
  intros n d H. discriminate.
Qed.

Lemma mknurbs_pair_is_interpolant :
  forall n1 n2,
    interpolant_pair (MkNurbs n1) (MkNurbs n2).
Proof.
  intros n1 n2. exact I.
Qed.

Lemma mknurbs_pair_hit_I_ok :
  I_ok (MkNurbs locked_nurbs_egg) (MkNurbs locked_nurbs_egg)
       (IHit (mkPoint (1 / 2) 0) (1 / 2) (1 / 2)).
Proof.
  exact locked_payload_egg_self_hit.
Qed.

Definition locked_mknurbs_ck1 : Chicken :=
  mkChicken 0%nat 1%nat (MkNurbs locked_nurbs_egg).

Definition locked_mknurbs_ck2 : Chicken :=
  mkChicken 2%nat 3%nat (MkNurbs locked_nurbs_egg).

Definition cooked_payload_mknurbs : CookedPair :=
  cook_hit_nurbs locked_mknurbs_ck1 locked_mknurbs_ck2
    locked_nurbs_egg locked_nurbs_egg (1 / 2) (1 / 2) crossing_hen.

Lemma try_cook_hit_mknurbs_some :
  try_cook_hit locked_mknurbs_ck1 locked_mknurbs_ck2
    (IHit (mkPoint (1 / 2) 0) (1 / 2) (1 / 2)) crossing_hen
    = Some cooked_payload_mknurbs.
Proof.
  reflexivity.
Qed.

Lemma sidecar_nurbs_hit_arm_inhabits :
  sidecar_nurbs_ctor_inhabits NurbsNurbsHitArm.
Proof.
  exact I.
Qed.

Lemma sidecar_nurbs_first_cook_expand_inhabits :
  sidecar_nurbs_ctor_inhabits NurbsFirstCookExpand.
Proof.
  exact I.
Qed.

Lemma sidecar_nurbs_is_first_cook :
  first_cook_scope EggNurbs EggNurbs.
Proof.
  exact nurbs_egg_first_cook_scope.
Qed.

Lemma sidecar_nurbs_first_cook_includes_nurbs :
  first_cook_scope EggChord EggChord /\
  first_cook_scope EggNurbs EggNurbs /\
  first_cook_scope EggClothoid EggClothoid /\
  first_cook_scope EggCircularArc EggCircularArc.
Proof.
  split; [exact first_cook_scope_chord_chord|].
  split; [exact nurbs_egg_first_cook_scope|].
  split; [exact clothoid_egg_first_cook_scope|].
  exact circular_egg_first_cook_scope.
Qed.

(* -------------------------------------------------------------------------- *)
(* What the sidecar is / is not. Kind tag, not a second kernel.               *)
(* -------------------------------------------------------------------------- *)

Inductive SidecarNurbsKind : Type :=
| SNE_EggPackaging
| SNE_HostCook
| SNE_NodingNG
| SNE_LengthNoding
| SNE_CoxDeBoor
| SNE_CampaignI
| SNE_LoopNoder.

Definition sidecar_nurbs_kind : SidecarNurbsKind := SNE_EggPackaging.

Lemma sidecar_nurbs_is_egg_packaging :
  sidecar_nurbs_kind = SNE_EggPackaging.
Proof.
  reflexivity.
Qed.

Lemma sidecar_nurbs_not_host_cook :
  sidecar_nurbs_kind <> SNE_HostCook.
Proof.
  discriminate.
Qed.

Lemma sidecar_nurbs_not_nodingng :
  sidecar_nurbs_kind <> SNE_NodingNG.
Proof.
  discriminate.
Qed.

Lemma sidecar_nurbs_not_length_noding :
  sidecar_nurbs_kind <> SNE_LengthNoding.
Proof.
  discriminate.
Qed.

Lemma sidecar_nurbs_not_cox_de_boor :
  sidecar_nurbs_kind <> SNE_CoxDeBoor.
Proof.
  discriminate.
Qed.

Lemma sidecar_nurbs_not_campaign_i :
  sidecar_nurbs_kind <> SNE_CampaignI.
Proof.
  discriminate.
Qed.

Lemma sidecar_nurbs_not_loop_noder :
  sidecar_nurbs_kind <> SNE_LoopNoder.
Proof.
  discriminate.
Qed.

Inductive SidecarNurbsLetterStatus : Type :=
| SidecarNurbsEggLanded
| SidecarNurbsFirstCookExpanded
| SidecarNurbsCampaignDischarged.

Definition sidecar_nurbs_letter_status : SidecarNurbsLetterStatus :=
  SidecarNurbsFirstCookExpanded.

Lemma sidecar_nurbs_letter_is_first_cook_expanded :
  sidecar_nurbs_letter_status = SidecarNurbsFirstCookExpanded.
Proof.
  reflexivity.
Qed.

Lemma sidecar_nurbs_letter_is_landed :
  sidecar_nurbs_letter_status <> SidecarNurbsEggLanded.
Proof.
  discriminate.
Qed.

Lemma sidecar_nurbs_campaign_not_discharged :
  sidecar_nurbs_letter_status <> SidecarNurbsCampaignDischarged.
Proof.
  discriminate.
Qed.

(* Named QED package: egg + Decline-on-host + locked chord-seed. *)
Lemma sidecar_nurbs_egg_inhabits :
  egg_class (sidecar_nurbs_host_egg locked_sne_ab) = EggNurbs /\
  sidecar_nurbs_host_egg locked_sne_ab = MkOutOfScope EggNurbs /\
  I_ok (sidecar_nurbs_host_egg locked_sne_ab)
       (sidecar_nurbs_host_egg locked_sne_cd) IDecline /\
  try_cook_hit locked_nurbs_ck1 locked_nurbs_ck2 IDecline crossing_hen
    = None /\
  nurbs_chord_share locked_nurbs_ab
    (nc_start locked_nurbs_cd) (nc_end locked_nurbs_cd) /\
  I_ok (MkChord (sidecar_nurbs_demote locked_sne_ab))
       (MkChord (sidecar_nurbs_demote locked_sne_cd))
       (IHit cross_pt (1 / 2) (1 / 2)) /\
  IEmpty <> IDecline /\
  sidecar_nurbs_kind = SNE_EggPackaging /\
  sidecar_nurbs_metric_kind = SNM_LengthResearch.
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact sidecar_nurbs_host_decline|].
  split; [exact sidecar_nurbs_try_cook_none|].
  split; [exact sidecar_nurbs_chord_seed|].
  split; [apply sidecar_nurbs_demote_hit_not_nurbs_I_ok|].
  split; [exact sidecar_nurbs_empty_neq_decline|].
  split; [reflexivity|].
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-nurbs-egg","topic":"overlay","lemma":"ticket_0007_nurbs_egg_qed_or_qex","title":"Sidecar NURBS egg packages EggNurbs Decline-on-host and locked demoted-chord seed (QED) or host I_ok is a NURBS Hit (QEX); discharged QED; demote-to-chord is NodingNG first cook, not a NURBS times NURBS cook","file":"theories/SidecarNurbsEgg.v","witness":"0007-nurbs-egg","board":"ADR-0007"} *)
Theorem ticket_0007_nurbs_egg_qed_or_qex :
  (egg_class (sidecar_nurbs_host_egg locked_sne_ab) = EggNurbs /\
   sidecar_nurbs_host_egg locked_sne_ab = MkOutOfScope EggNurbs /\
   I_ok (sidecar_nurbs_host_egg locked_sne_ab)
        (sidecar_nurbs_host_egg locked_sne_cd) IDecline /\
   try_cook_hit locked_nurbs_ck1 locked_nurbs_ck2 IDecline crossing_hen
     = None /\
   nurbs_chord_share locked_nurbs_ab
     (nc_start locked_nurbs_cd) (nc_end locked_nurbs_cd) /\
   I_ok (MkChord (sidecar_nurbs_demote locked_sne_ab))
        (MkChord (sidecar_nurbs_demote locked_sne_cd))
        (IHit cross_pt (1 / 2) (1 / 2)) /\
   ~ I_ok (sidecar_nurbs_host_egg locked_sne_ab)
          (sidecar_nurbs_host_egg locked_sne_cd)
          (IHit cross_pt (1 / 2) (1 / 2)) /\
   IEmpty <> IDecline /\
   sidecar_nurbs_kind = SNE_EggPackaging /\
   sidecar_nurbs_kind <> SNE_HostCook /\
   sidecar_nurbs_kind <> SNE_NodingNG /\
   sidecar_nurbs_kind <> SNE_LengthNoding /\
   sidecar_nurbs_metric_kind = SNM_LengthResearch /\
   sidecar_nurbs_metric_kind <> SNM_CookHit)
  \/
  (exists p ti tj,
     I_ok (MkOutOfScope EggNurbs) (MkOutOfScope EggNurbs)
          (IHit p ti tj)).
Proof.
  left.
  destruct sidecar_nurbs_egg_inhabits
    as [Hcls [Htag [Hdec [Hnone [Hseed [Hdem [Hneq [Hkind Hmet]]]]]]]].
  split; [exact Hcls|].
  split; [exact Htag|].
  split; [exact Hdec|].
  split; [exact Hnone|].
  split; [exact Hseed|].
  split; [exact Hdem|].
  split; [apply sidecar_nurbs_host_hit_false|].
  split; [exact Hneq|].
  split; [exact Hkind|].
  split; [exact sidecar_nurbs_not_host_cook|].
  split; [exact sidecar_nurbs_not_nodingng|].
  split; [exact sidecar_nurbs_not_length_noding|].
  split; [exact Hmet|].
  exact sidecar_nurbs_metric_not_cook_hit.
Qed.

(* WITNESS {"claimId":"0007-nurbs-egg","topic":"overlay","lemma":"ticket_0007_nurbs_not_first_cook_qed_or_qex","title":"Sidecar NURBS expands first_cook_scope to NURBS times NURBS and inhabits I_ok Hit (QED) or NURBS times NURBS stays QEX with named MkNurbs / Hit-arm gaps (QEX); discharged QED; host first-cook letter 0007-nurbs-first-cook; tags stay Decline","file":"theories/SidecarNurbsEgg.v","witness":"0007-nurbs-egg","board":"ADR-0007"} *)
Theorem ticket_0007_nurbs_not_first_cook_qed_or_qex :
  (first_cook_scope EggNurbs EggNurbs /\
   sidecar_nurbs_ctor_inhabits NurbsMkNurbs /\
   sidecar_nurbs_ctor_inhabits NurbsNurbsHitArm /\
   sidecar_nurbs_ctor_inhabits NurbsFirstCookExpand /\
   sidecar_nurbs_letter_status = SidecarNurbsFirstCookExpanded /\
   exists p ti tj,
     I_ok (MkNurbs locked_nurbs_egg) (MkNurbs locked_nurbs_egg)
          (IHit p ti tj))
  \/
  (~ first_cook_scope EggNurbs EggNurbs /\
   first_cook_scope EggChord EggChord /\
   ~ sidecar_nurbs_ctor_inhabits NurbsMkNurbs /\
   ~ sidecar_nurbs_ctor_inhabits NurbsNurbsHitArm /\
   ~ sidecar_nurbs_ctor_inhabits NurbsFirstCookExpand /\
   sidecar_nurbs_letter_status = SidecarNurbsEggLanded /\
   I_ok (MkOutOfScope EggNurbs) (MkOutOfScope EggNurbs) IDecline /\
   (forall p ti tj,
      ~ I_ok (MkOutOfScope EggNurbs) (MkOutOfScope EggNurbs)
           (IHit p ti tj)) /\
   try_cook_hit nurbs_ck1 nurbs_ck2 IDecline crossing_hen = None).
Proof.
  left.
  split; [exact nurbs_egg_first_cook_scope|].
  split; [exact sidecar_nurbs_mknurbs_inhabits|].
  split; [exact sidecar_nurbs_hit_arm_inhabits|].
  split; [exact sidecar_nurbs_first_cook_expand_inhabits|].
  split; [exact sidecar_nurbs_letter_is_first_cook_expanded|].
  exists (mkPoint (1 / 2) 0), (1 / 2), (1 / 2).
  exact mknurbs_pair_hit_I_ok.
Qed.

(* WITNESS {"claimId":"0007-nurbs-egg","topic":"overlay","lemma":"ticket_0007_nurbs_parks_qed_or_qex","title":"Sidecar NURBS discharges Campaign I-II, remints length/Cox-de-Boor as noding, and flips LoopDischarged (QED) or names them parked and cites Parks Gamma/iota/rho once (QEX); discharged QEX; first-cook expand landed != Campaign / length-as-noding / bag noder","file":"theories/SidecarNurbsEgg.v","witness":"0007-nurbs-egg","board":"ADR-0007"} *)
Theorem ticket_0007_nurbs_parks_qed_or_qex :
  (sidecar_nurbs_letter_status = SidecarNurbsCampaignDischarged /\
   sidecar_nurbs_kind = SNE_CampaignI /\
   sidecar_nurbs_kind = SNE_LengthNoding /\
   sidecar_nurbs_kind = SNE_CoxDeBoor /\
   sidecar_nurbs_kind = SNE_LoopNoder /\
   cook_loop_status = LoopDischarged)
  \/
  (sidecar_nurbs_letter_status = SidecarNurbsFirstCookExpanded /\
   sidecar_nurbs_letter_status <> SidecarNurbsCampaignDischarged /\
   sidecar_nurbs_kind = SNE_EggPackaging /\
   sidecar_nurbs_kind <> SNE_CampaignI /\
   sidecar_nurbs_kind <> SNE_LengthNoding /\
   sidecar_nurbs_kind <> SNE_CoxDeBoor /\
   sidecar_nurbs_kind <> SNE_LoopNoder /\
   cook_loop_status = LoopObligation /\
   cook_loop_status <> LoopDischarged /\
   first_cook_scope EggChord EggChord /\
   first_cook_scope EggNurbs EggNurbs /\
   ~ first_cook_scope EggEllipse EggEllipse).
Proof.
  right.
  split; [exact sidecar_nurbs_letter_is_first_cook_expanded|].
  split; [exact sidecar_nurbs_campaign_not_discharged|].
  split; [exact sidecar_nurbs_is_egg_packaging|].
  split; [exact sidecar_nurbs_not_campaign_i|].
  split; [exact sidecar_nurbs_not_length_noding|].
  split; [exact sidecar_nurbs_not_cox_de_boor|].
  split; [exact sidecar_nurbs_not_loop_noder|].
  split; [exact cook_loop_is_obligation|].
  split; [exact cook_loop_not_discharged|].
  split; [exact first_cook_scope_chord_chord|].
  split; [exact nurbs_egg_first_cook_scope|].
  exact ellipse_ellipse_not_first_scope.
Qed.

Print Assumptions sidecar_nurbs_class.
Print Assumptions sidecar_nurbs_host_decline.
Print Assumptions sidecar_nurbs_try_cook_none.
Print Assumptions sidecar_nurbs_chord_seed.
Print Assumptions sidecar_nurbs_demote_is_nodingng_crossing.
Print Assumptions sidecar_nurbs_metric_not_cook_hit.
Print Assumptions sidecar_nurbs_mknurbs_inhabits.
Print Assumptions sidecar_nurbs_hit_arm_inhabits.
Print Assumptions mknurbs_pair_hit_I_ok.
Print Assumptions try_cook_hit_mknurbs_some.
Print Assumptions sidecar_nurbs_egg_inhabits.
Print Assumptions ticket_0007_nurbs_egg_qed_or_qex.
Print Assumptions ticket_0007_nurbs_not_first_cook_qed_or_qex.
Print Assumptions ticket_0007_nurbs_parks_qed_or_qex.
