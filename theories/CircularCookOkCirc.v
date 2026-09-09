(* ============================================================================
   NetTopologySuite.Proofs.CircularCookOkCirc
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: Campaign II rung II.3 — I_ok_circ on
   EggCircularArc × EggCircularArc using sidecar arc_gamma.

   SQL/MM Part 3 required-type *path*: CircularString is a sequence of
   CircularArc primitives. This letter is the single-arc glossary-type
   inhabitant. A CS theorem needs a concatenation argument; this is not
   that. Not CompoundCurve. Not CurvePolygon. Not the SQL/MM cathedral.

   Host I_ok on circular eggs is Decline (first cook stays chord–chord;
   CircGamma stays QEX). Span Hit ≠ host I_ok (II.1 / II.2). This letter
   is the license rung those fences pointed at: I_ok_circ inhabits the
   glossary 𝓘 shape (Hit / Empty / Decline) on sidecar CircEgg :=
   CircularArc — the EggCircularArc payload host MkOutOfScope does not
   carry. An I_ok_circ Hit licenses the II.2 span_split cook.

   Locked fixture: (0,0)/(7,0) r=5 proper arcs inhabit Hit at p+ and
   license leftovers-at-p*. Pair-level Empty is a far quarter of the
   I.3 (0,0)/(20,0) r=5 disjoint circles (not the locked A×B pair —
   that pair is Hit, so per-root p− Empty is not pair Empty).
   Decline is the invalid control. ∀ Hit / Empty / Decline as a Prop
   are definitional; this letter does not mint a computed classifier
   that finds the Hit (I_circles_gamma stays Campaign I).

   QED: I_ok_circ Hit iff on_arc_gamma both (valid arcs); locked p+
   inhabits Hit and licenses span_split; Empty ≠ Decline; invalid
   Decline; locked far pair inhabits Empty; pair Hit ≠ per-root Empty.
   QEX: host CircGamma stays QEX; first cook stays chord–chord;
   I_ok_circ Hit ≠ host I_ok; II.4, H⊥, and SQL/MM CS / CC / CP
   cathedral stay parked.

   Honesty fences:
     Host-Decline / CircGamma-QEX at the top of this module.
     I_circles_z ≠ I_circles_gamma ≠ sidecar cook ≠ span filter ≠
     span split ≠ I_ok_circ ≠ glossary I_gloss / host I_ok.
     I_ok_circ ≠ I_span_root (pair vs per-root).
     Not first cook scope. Not a noder. Not ArcSplitAtNode.
     Not CircularString concatenation. Not CompoundCurve / CurvePolygon.
     Not a remint of CurveSegment / Exact* / Dart / Hobby /
     leftover_width / ArcSplitAtNode leftover-width / host circ_split.
     Do not fake atan2-free host γ. Do not expand first_cook_scope.
     Do not start II.4 honesty letter / H⊥ / Phase B / a CRV-TOUCH
     kiss procedure / full SQL/MM cathedral.
     No new kernel.

   WITNESS topic: overlay · claimId: 0007
   witness: 0007-II.3-I-ok-circ
   board: ADR-0007
   4-axiom (atan2 / Classical_Prop.classic via CircularCookSpan).
   No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance SheetHenCook CurveGeometry
  ArcOffsetThreePoint CircularCook CircularCookHit CircularCookSpan
  CircularCookSpanFilter CircularCookSpanSplit.
Local Open Scope R_scope.

(* WITNESS: campaign=II rung=II.3 claim=0007
   file=theories/CircularCookOkCirc.v
   kind=QED-or-QEX-I-ok-circ-glossary-inhabitant
   gamma=arc-span-not-gamma-full
   lock=Hit-Empty-inhabitants-definitional-forall
   not=CircGamma-Discharge,first-cook-noding,II.4,Hperp
   not=SQL-MM-cathedral,CircularString-concat,CRV-TOUCH-kiss
   not=computed-classifier *)

(* -------------------------------------------------------------------------- *)
(* Host-Decline / CircGamma-QEX fence (load-bearing, not decoration).         *)
(* -------------------------------------------------------------------------- *)

Lemma ii3_host_circgamma_qex :
  circular_gamma_status = CircGammaQEX.
Proof.
  exact circular_gamma_is_qex.
Qed.

Lemma ii3_host_not_first_cook :
  ~ first_cook_scope EggCircularArc EggCircularArc.
Proof.
  exact circular_not_first_cook_scope.
Qed.

Lemma ii3_host_circular_decline :
  I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc) IDecline.
Proof.
  exact circular_decline_I_ok.
Qed.

Lemma ii3_host_circular_hit_false :
  forall p ti tj,
    ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
         (IHit p ti tj).
Proof.
  exact circular_hit_not_I_ok.
Qed.

Lemma ii3_first_cook_stays_chord_chord :
  first_cook_scope EggChord EggChord.
Proof.
  exact first_cook_scope_chord_chord.
Qed.

Lemma ii3_host_egg_class :
  egg_class (MkOutOfScope EggCircularArc) = EggCircularArc.
Proof.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Glossary-type inhabitant. Sidecar CircEgg is the EggCircularArc payload.   *)
(* Host MkOutOfScope EggCircularArc carries no interpolant.                   *)
(* -------------------------------------------------------------------------- *)

Definition CircEgg : Type := CircularArc.

(* Pair-level meet: some point sits on both span interpolants. *)
Definition span_images_meet (a b : CircEgg) : Prop :=
  exists p : Point, on_arc_gamma_both a b p.

Definition I_ok_circ (a b : CircEgg) (o : IResult) : Prop :=
  match o with
  | IHit p ti tj =>
      valid_arc a /\ valid_arc b /\
      on_arc_gamma a ti p /\ on_arc_gamma b tj p
  | IEmpty =>
      valid_arc a /\ valid_arc b /\ ~ span_images_meet a b
  | IDecline =>
      ~ valid_arc a \/ ~ valid_arc b
  end.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"I_ok_circ_hit_iff","title":"II.3 I_ok_circ Hit iff valid arcs and on_arc_gamma both (span gamma, not gamma_full); definitional forall","file":"theories/CircularCookOkCirc.v","witness":"0007-II.3-I-ok-circ","board":"ADR-0007"} *)

Theorem I_ok_circ_hit_iff :
  forall a b p ti tj,
    I_ok_circ a b (IHit p ti tj) <->
      valid_arc a /\ valid_arc b /\
      on_arc_gamma a ti p /\ on_arc_gamma b tj p.
Proof.
  intros a b p ti tj.
  unfold I_ok_circ.
  split; [intros H; exact H | intros H; exact H].
Qed.

Theorem I_ok_circ_empty_iff :
  forall a b,
    I_ok_circ a b IEmpty <->
      valid_arc a /\ valid_arc b /\ ~ span_images_meet a b.
Proof.
  intros a b.
  unfold I_ok_circ.
  split; [intros H; exact H | intros H; exact H].
Qed.

Theorem I_ok_circ_decline_iff :
  forall a b,
    I_ok_circ a b IDecline <->
      ~ valid_arc a \/ ~ valid_arc b.
Proof.
  intros a b.
  unfold I_ok_circ.
  split; [intros H; exact H | intros H; exact H].
Qed.

Lemma I_ok_circ_hit_imp_span_root :
  forall a b p ti tj,
    I_ok_circ a b (IHit p ti tj) ->
    I_span_root a b p (IHit p ti tj).
Proof.
  intros a b p ti tj H.
  apply I_ok_circ_hit_iff in H.
  destruct H as [_ [_ [Ha Hb]]].
  unfold I_span_root.
  split; [reflexivity | split; [exact Ha | exact Hb]].
Qed.

Lemma I_ok_circ_empty_neq_decline :
  IEmpty <> IDecline.
Proof.
  exact IEmpty_neq_IDecline.
Qed.

(* -------------------------------------------------------------------------- *)
(* License: I_ok_circ Hit feeds II.2 span_split. Empty / Decline mint none.   *)
(* -------------------------------------------------------------------------- *)

Lemma I_ok_circ_hit_licenses_span_cook :
  forall a b p ti tj,
    I_ok_circ a b (IHit p ti tj) ->
    try_cook_span_root a b (IHit p ti tj) = Some (cook_span_root a b ti tj) /\
    span_cooked_meets (cook_span_root a b ti tj) p.
Proof.
  intros a b p ti tj H.
  apply I_ok_circ_hit_iff in H.
  destruct H as [_ [_ [[_ Ha] [_ Hb]]]].
  split; [reflexivity|].
  apply cook_span_root_meets; [exact Ha | exact Hb].
Qed.

Lemma I_ok_circ_empty_no_cook :
  forall a b, try_cook_span_root a b IEmpty = None.
Proof.
  intros. apply try_cook_span_empty_none.
Qed.

Lemma I_ok_circ_decline_no_cook :
  forall a b, try_cook_span_root a b IDecline = None.
Proof.
  intros. apply try_cook_span_decline_none.
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked (0,0)/(7,0) r=5 proper arcs: pair-level Hit at p+ licenses cook.    *)
(* -------------------------------------------------------------------------- *)

Definition locked_ok_circ_hit : IResult :=
  IHit locked_p_plus locked_span_ti_plus locked_span_tj_plus.

Lemma ii3_locked_plus_I_ok_circ :
  I_ok_circ span_arc_A span_arc_B locked_ok_circ_hit.
Proof.
  unfold locked_ok_circ_hit.
  apply I_ok_circ_hit_iff.
  split; [exact span_arc_A_valid|].
  split; [exact span_arc_B_valid|].
  split; [exact span_p_plus_on_gamma_A | exact span_p_plus_on_gamma_B].
Qed.

Lemma ii3_locked_plus_licenses_cook :
  try_cook_span_root span_arc_A span_arc_B locked_ok_circ_hit
    = Some cooked_span_plus /\
  span_cooked_meets cooked_span_plus locked_p_plus.
Proof.
  unfold locked_ok_circ_hit, cooked_span_plus.
  apply (I_ok_circ_hit_licenses_span_cook span_arc_A span_arc_B
           locked_p_plus locked_span_ti_plus locked_span_tj_plus).
  exact ii3_locked_plus_I_ok_circ.
Qed.

Lemma ii3_locked_pair_not_empty :
  ~ I_ok_circ span_arc_A span_arc_B IEmpty.
Proof.
  intros Hemp.
  apply I_ok_circ_empty_iff in Hemp.
  destruct Hemp as [_ [_ Hn]].
  apply Hn.
  exists locked_p_plus.
  exists locked_span_ti_plus, locked_span_tj_plus.
  split; [exact span_p_plus_on_gamma_A | exact span_p_plus_on_gamma_B].
Qed.

(* Pair-level Hit ≠ per-root Empty. Locked p− is II.1 Empty; the pair is Hit. *)
Lemma ii3_pair_hit_neq_root_empty :
  I_ok_circ span_arc_A span_arc_B locked_ok_circ_hit /\
  I_span_root span_arc_A span_arc_B locked_p_minus IEmpty /\
  ~ I_ok_circ span_arc_A span_arc_B IEmpty.
Proof.
  split; [exact ii3_locked_plus_I_ok_circ|].
  split; [exact ii1_locked_minus_span_empty|].
  exact ii3_locked_pair_not_empty.
Qed.

(* I_ok_circ Hit is not host I_ok. The #666 fence still holds. *)
Lemma ii3_I_ok_circ_hit_not_host_I_ok :
  I_ok_circ span_arc_A span_arc_B locked_ok_circ_hit /\
  ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
       locked_ok_circ_hit.
Proof.
  split; [exact ii3_locked_plus_I_ok_circ|].
  unfold locked_ok_circ_hit.
  apply circular_hit_not_I_ok.
Qed.

Lemma ii3_invalid_decline :
  I_ok_circ span_decline_arc span_arc_B IDecline.
Proof.
  apply I_ok_circ_decline_iff.
  left.
  exact span_decline_arc_invalid.
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked Empty: far quarter of the I.3 (0,0)/(20,0) r=5 disjoint circles.    *)
(* Not the locked A×B pair. ∀ Empty as a Prop is I_ok_circ_empty_iff.         *)
(* -------------------------------------------------------------------------- *)

Definition span_empty_far : CircularArc :=
  mkCircularArc (mkPoint 25 0) (mkPoint 20 5) (mkPoint 15 0).

Definition span_empty_far_O : Point := mkPoint 20 0.

Lemma span_empty_far_valid : valid_arc span_empty_far.
Proof.
  unfold valid_arc, span_empty_far.
  cbn [px py arc_start arc_mid arc_end].
  lra.
Qed.

Lemma span_empty_far_equidistant :
  dist_sq span_empty_far_O (arc_start span_empty_far)
    = dist_sq span_empty_far_O (arc_mid span_empty_far) /\
  dist_sq span_empty_far_O (arc_start span_empty_far)
    = dist_sq span_empty_far_O (arc_end span_empty_far).
Proof.
  unfold span_empty_far, span_empty_far_O, dist_sq.
  cbn [px py arc_start arc_mid arc_end].
  split; lra.
Qed.

Lemma span_empty_far_center :
  arc_center span_empty_far = span_empty_far_O.
Proof.
  symmetry.
  apply equidistant_point_is_arc_center.
  - exact span_empty_far_valid.
  - apply (proj1 span_empty_far_equidistant).
  - apply (proj2 span_empty_far_equidistant).
Qed.

Lemma span_empty_far_radius : arc_radius span_empty_far = 5.
Proof.
  unfold arc_radius. rewrite span_empty_far_center.
  unfold span_empty_far_O, span_empty_far, dist, dist_sq.
  cbn [px py arc_start].
  replace ((20 - 25) * (20 - 25) + (0 - 0) * (0 - 0)) with (Rsqr 5)
    by (unfold Rsqr; ring).
  apply sqrt_Rsqr. lra.
Qed.

Lemma ii3_empty_images_disjoint :
  ~ span_images_meet span_arc_A span_empty_far.
Proof.
  intros [p Hboth].
  destruct Hboth as [ti [tj [Ha Hb]]].
  destruct Ha as [_ Ha]. destruct Hb as [_ Hb].
  pose proof (arc_gamma_on_circle span_arc_A ti) as HA.
  pose proof (arc_gamma_on_circle span_empty_far tj) as HB.
  rewrite <- Ha in HA. rewrite <- Hb in HB.
  rewrite span_arc_A_center, span_arc_A_radius in HA.
  rewrite span_empty_far_center, span_empty_far_radius in HB.
  unfold locked_O1, locked_r, dist_sq in HA.
  unfold span_empty_far_O, dist_sq in HB.
  cbn [px py] in HA, HB.
  replace ((0 - px p) * (0 - px p) + (0 - py p) * (0 - py p))
    with (px p * px p + py p * py p) in HA by ring.
  replace ((20 - px p) * (20 - px p) + (0 - py p) * (0 - py p))
    with ((20 - px p) * (20 - px p) + py p * py p) in HB by ring.
  assert (Hdiff : (20 - px p) * (20 - px p) - px p * px p = 0) by lra.
  replace ((20 - px p) * (20 - px p) - px p * px p)
    with (400 - 40 * px p) in Hdiff by ring.
  assert (Hpx : px p = 10) by lra.
  rewrite Hpx in HA.
  assert (Hnn : 0 <= py p * py p) by nra.
  lra.
Qed.

Lemma ii3_locked_empty :
  I_ok_circ span_arc_A span_empty_far IEmpty.
Proof.
  apply I_ok_circ_empty_iff.
  split; [exact span_arc_A_valid|].
  split; [exact span_empty_far_valid|].
  exact ii3_empty_images_disjoint.
Qed.

Lemma ii3_locked_empty_no_cook :
  I_ok_circ span_arc_A span_empty_far IEmpty /\
  try_cook_span_root span_arc_A span_empty_far IEmpty = None /\
  ~ I_ok_circ span_arc_A span_empty_far IDecline.
Proof.
  split; [exact ii3_locked_empty|].
  split; [reflexivity|].
  intros Hdec.
  apply I_ok_circ_decline_iff in Hdec.
  destruct Hdec as [Ha | Hb].
  - apply Ha. exact span_arc_A_valid.
  - apply Hb. exact span_empty_far_valid.
Qed.

(* -------------------------------------------------------------------------- *)
(* II.3 lands this letter. II.4 / H⊥ / SQL/MM cathedral stay parked.          *)
(* -------------------------------------------------------------------------- *)

Inductive CampaignII3Status : Type :=
| CampaignII3Landed
| CampaignII3Parked.

Definition campaign_ii3_status : CampaignII3Status := CampaignII3Landed.

Lemma campaign_ii3_is_landed :
  campaign_ii3_status = CampaignII3Landed.
Proof.
  reflexivity.
Qed.

Inductive CampaignII4Status : Type :=
| CampaignII4Discharged
| CampaignII4Parked.

Definition campaign_ii4_status : CampaignII4Status := CampaignII4Parked.

Lemma campaign_ii4_is_parked :
  campaign_ii4_status = CampaignII4Parked.
Proof.
  reflexivity.
Qed.

Inductive HperpIIStatus : Type :=
| HperpIIDischarged
| HperpIIParked.

Definition hperp_ii_status : HperpIIStatus := HperpIIParked.

Lemma hperp_ii_is_parked :
  hperp_ii_status = HperpIIParked.
Proof.
  reflexivity.
Qed.

Inductive SqlMmCathedralStatus : Type :=
| SqlMmCathedralDone
| SqlMmCathedralParked.

Definition sql_mm_cathedral_status : SqlMmCathedralStatus :=
  SqlMmCathedralParked.

Lemma sql_mm_cathedral_is_parked :
  sql_mm_cathedral_status = SqlMmCathedralParked.
Proof.
  reflexivity.
Qed.

Lemma ii3_rest_parked :
  campaign_ii4_status = CampaignII4Parked /\
  hperp_ii_status = HperpIIParked /\
  sql_mm_cathedral_status = SqlMmCathedralParked.
Proof.
  repeat split; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_ii3_hit_qed_or_qex","title":"II.3 I_ok_circ Hit iff on_arc_gamma both and locked p+ inhabits (QED) or locked p+ declines I_ok_circ (QEX); discharged QED; definitional forall; locked fixture","file":"theories/CircularCookOkCirc.v","witness":"0007-II.3-I-ok-circ","board":"ADR-0007"} *)

Theorem ticket_0007_ii3_hit_qed_or_qex :
  ((forall a b p ti tj,
      I_ok_circ a b (IHit p ti tj) <->
        valid_arc a /\ valid_arc b /\
        on_arc_gamma a ti p /\ on_arc_gamma b tj p) /\
   I_ok_circ span_arc_A span_arc_B locked_ok_circ_hit)
  \/
  I_ok_circ span_arc_A span_arc_B IDecline.
Proof.
  left.
  split; [exact I_ok_circ_hit_iff|].
  exact ii3_locked_plus_I_ok_circ.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_ii3_license_qed_or_qex","title":"II.3 I_ok_circ Hit licenses span_split leftovers at locked p+ (QED) or the cook declines the Hit (QEX); discharged QED; license rung; span Hit is now I_ok_circ","file":"theories/CircularCookOkCirc.v","witness":"0007-II.3-I-ok-circ","board":"ADR-0007"} *)

Theorem ticket_0007_ii3_license_qed_or_qex :
  (try_cook_span_root span_arc_A span_arc_B locked_ok_circ_hit
     = Some cooked_span_plus /\
   span_cooked_meets cooked_span_plus locked_p_plus /\
   I_ok_circ span_arc_A span_arc_B locked_ok_circ_hit /\
   I_span_root span_arc_A span_arc_B locked_p_plus
     (I_span_hit_val span_arc_A span_arc_B locked_p_plus))
  \/
  try_cook_span_root span_arc_A span_arc_B locked_ok_circ_hit = None.
Proof.
  left.
  destruct ii3_locked_plus_licenses_cook as [Htry Hmeet].
  split; [exact Htry|].
  split; [exact Hmeet|].
  split; [exact ii3_locked_plus_I_ok_circ|].
  exact ii1_locked_plus_span_hit.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_ii3_empty_qed_or_qex","title":"II.3 I_ok_circ Empty on a locked far pair, Empty differs from Decline, pair Hit is not per-root Empty (QED) or the far pair is Decline (QEX); discharged QED; locked Empty inhabitant; forall Empty is definitional","file":"theories/CircularCookOkCirc.v","witness":"0007-II.3-I-ok-circ","board":"ADR-0007"} *)

Theorem ticket_0007_ii3_empty_qed_or_qex :
  (I_ok_circ span_arc_A span_empty_far IEmpty /\
   try_cook_span_root span_arc_A span_empty_far IEmpty = None /\
   IEmpty <> IDecline /\
   ~ I_ok_circ span_arc_A span_empty_far IDecline /\
   I_ok_circ span_decline_arc span_arc_B IDecline /\
   I_ok_circ span_arc_A span_arc_B locked_ok_circ_hit /\
   I_span_root span_arc_A span_arc_B locked_p_minus IEmpty /\
   ~ I_ok_circ span_arc_A span_arc_B IEmpty)
  \/
  I_ok_circ span_arc_A span_empty_far IDecline.
Proof.
  left.
  destruct ii3_locked_empty_no_cook as [He [Hn Hd]].
  destruct ii3_pair_hit_neq_root_empty as [Hh [Hr Hp]].
  split; [exact He|].
  split; [exact Hn|].
  split; [exact I_ok_circ_empty_neq_decline|].
  split; [exact Hd|].
  split; [exact ii3_invalid_decline|].
  split; [exact Hh|].
  split; [exact Hr|].
  exact Hp.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_ii3_host_qed_or_qex","title":"II.3 discharges CircGamma and expands first cook (QED) or CircGamma stays QEX, first cook stays chord-chord, I_ok_circ Hit is not host I_ok (QEX); discharged QEX; host circular I_ok is Decline","file":"theories/CircularCookOkCirc.v","witness":"0007-II.3-I-ok-circ","board":"ADR-0007"} *)

Theorem ticket_0007_ii3_host_qed_or_qex :
  (circular_gamma_status = CircGammaDischarged /\
   first_cook_scope EggCircularArc EggCircularArc /\
   exists p ti tj,
     I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
          (IHit p ti tj))
  \/
  (circular_gamma_status = CircGammaQEX /\
   ~ first_cook_scope EggCircularArc EggCircularArc /\
   first_cook_scope EggChord EggChord /\
   I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc) IDecline /\
   (forall p ti tj,
      ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
           (IHit p ti tj)) /\
   I_ok_circ span_arc_A span_arc_B locked_ok_circ_hit /\
   ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
        locked_ok_circ_hit).
Proof.
  right.
  destruct ii3_I_ok_circ_hit_not_host_I_ok as [Hhit Hhost].
  split; [exact ii3_host_circgamma_qex|].
  split; [exact ii3_host_not_first_cook|].
  split; [exact ii3_first_cook_stays_chord_chord|].
  split; [exact ii3_host_circular_decline|].
  split; [exact ii3_host_circular_hit_false|].
  split; [exact Hhit|].
  exact Hhost.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_ii3_park_qed_or_qex","title":"II.3 discharges II.4, Hperp, and the SQL/MM cathedral (QED) or names them parked (QEX); discharged QEX; II.3 landed; not CircularString concat","file":"theories/CircularCookOkCirc.v","witness":"0007-II.3-I-ok-circ","board":"ADR-0007"} *)

Theorem ticket_0007_ii3_park_qed_or_qex :
  (campaign_ii4_status = CampaignII4Discharged /\
   hperp_ii_status = HperpIIDischarged /\
   sql_mm_cathedral_status = SqlMmCathedralDone)
  \/
  (campaign_ii3_status = CampaignII3Landed /\
   campaign_ii4_status = CampaignII4Parked /\
   hperp_ii_status = HperpIIParked /\
   sql_mm_cathedral_status = SqlMmCathedralParked).
Proof.
  right.
  split; [exact campaign_ii3_is_landed|].
  exact ii3_rest_parked.
Qed.

Print Assumptions ii3_host_circgamma_qex.
Print Assumptions I_ok_circ_hit_iff.
Print Assumptions I_ok_circ_empty_iff.
Print Assumptions I_ok_circ_decline_iff.
Print Assumptions I_ok_circ_hit_licenses_span_cook.
Print Assumptions ii3_locked_plus_I_ok_circ.
Print Assumptions ii3_locked_plus_licenses_cook.
Print Assumptions ii3_pair_hit_neq_root_empty.
Print Assumptions ii3_I_ok_circ_hit_not_host_I_ok.
Print Assumptions ii3_invalid_decline.
Print Assumptions ii3_locked_empty.
Print Assumptions ticket_0007_ii3_hit_qed_or_qex.
Print Assumptions ticket_0007_ii3_license_qed_or_qex.
Print Assumptions ticket_0007_ii3_empty_qed_or_qex.
Print Assumptions ticket_0007_ii3_host_qed_or_qex.
Print Assumptions ticket_0007_ii3_park_qed_or_qex.
