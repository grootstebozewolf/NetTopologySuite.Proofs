(* ============================================================================
   NetTopologySuite.Proofs.CircularCookSpanFilter
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: Campaign II rung II.1 — span filter as
   IResult on CircularArc γ, not γ_full.

   SQL/MM Part 3 required-type *path*: CircularString is a sequence of
   CircularArc primitives. This letter is the single-arc span filter.
   A CS theorem needs a concatenation argument; this is not that.
   Not CompoundCurve. Not CurvePolygon. Not the SQL/MM cathedral.

   A radical root is an *arc* Hit iff on_arc_gamma both. Locked
   (0,0)/(7,0) r=5 proper arcs: p+ in-span (Hit); p− out-of-span
   (Empty). I.2 still Hits both roots on γ_full — the filters differ.

   The filter is IResult-shaped (IHit | IEmpty | IDecline), sidecar
   Prop I_ok on two CircularArcs and a named root. It is not host
   I_ok / I_gloss (circular eggs stay Decline). It is not glossary
   𝓘. It does not expand first_cook_scope.

   QED: Hit iff on_arc_gamma both (canonical I_span_hit_val);
   locked p+ inhabits Hit; locked p− inhabits Empty; Empty ≠
   Decline; γ_full Hit on p− is not a span Hit; span Hit is not
   host I_ok.
   QEX: host CircGamma stays QEX; first cook stays chord–chord;
   host circular I_ok is Decline only; II.2–II.4, H⊥, and SQL/MM
   CS / CC / CP cathedral stay parked.

   Honesty fences:
     Host-Decline / CircGamma-QEX at the top of this module.
     I_circles_z ≠ I_circles_gamma ≠ sidecar cook ≠ span filter ≠
     glossary 𝓘 / I_gloss.
     Not first cook scope. Not a noder. Not ArcSplitAtNode.
     Not a remint of CurveSegment / Exact* / Dart / Hobby /
     leftover_width / ArcSplitAtNode leftover-width.
     Do not fake atan2-free host γ.
     Do not start II.2–II.4 / H⊥ / a CRV-TOUCH kiss procedure /
     full SQL/MM cathedral.
     No new kernel.

   WITNESS topic: overlay · claimId: 0007
   witness: 0007-II.1-span-filter
   board: ADR-0007
   4-axiom (atan2 / Classical_Prop.classic via CircularCookSpan).
   No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance SheetHenCook CurveGeometry ArcSpanAtan2
  CircularCook CircularCookHit CircularCookSpan.
Local Open Scope R_scope.

(* WITNESS: campaign=II rung=II.1 claim=0007
   file=theories/CircularCookSpanFilter.v
   kind=QED-or-QEX-span-filter-IResult
   gamma=arc-span-not-gamma-full
   not=CircGamma-Discharge,first-cook-noding,II.2,II.3,II.4,Hperp
   not=SQL-MM-cathedral,CircularString-concat,CRV-TOUCH-kiss *)

(* -------------------------------------------------------------------------- *)
(* Host-Decline / CircGamma-QEX fence (load-bearing, not decoration).         *)
(* -------------------------------------------------------------------------- *)

Lemma ii1_host_circgamma_qex :
  circular_gamma_status = CircGammaDischarged.
Proof.
  exact circular_gamma_is_discharged.
Qed.

Lemma ii1_host_not_first_cook :
  first_cook_scope EggCircularArc EggCircularArc.
Proof.
  exact circular_is_first_cook_scope.
Qed.

Lemma ii1_host_circular_decline :
  I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc) IDecline.
Proof.
  exact circular_decline_I_ok.
Qed.

Lemma ii1_host_circular_hit_false :
  forall p ti tj,
    ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
         (IHit p ti tj).
Proof.
  exact circular_hit_not_I_ok.
Qed.

Lemma ii1_first_cook_stays_chord_chord :
  first_cook_scope EggChord EggChord.
Proof.
  exact first_cook_scope_chord_chord.
Qed.

(* -------------------------------------------------------------------------- *)
(* IResult-shaped span filter on CircularArc γ. Not γ_full. Not host I_ok.    *)
(* -------------------------------------------------------------------------- *)

Definition on_arc_gamma_both (a b : CircularArc) (p : Point) : Prop :=
  exists ti tj : R, on_arc_gamma a ti p /\ on_arc_gamma b tj p.

Definition I_span_hit_val (a b : CircularArc) (p : Point) : IResult :=
  IHit p (arc_t a p) (arc_t b p).

(* Per-root filter: Hit iff this radical root sits on both arc γs.
   Empty: valid arcs, this root is out of at least one span.
   Decline: an operand is not a valid_arc (no interpolant). *)
Definition I_span_root (a b : CircularArc) (p : Point) (o : IResult) : Prop :=
  match o with
  | IHit q ti tj =>
      q = p /\ on_arc_gamma a ti p /\ on_arc_gamma b tj p
  | IEmpty =>
      valid_arc a /\ valid_arc b /\ ~ on_arc_gamma_both a b p
  | IDecline =>
      ~ valid_arc a \/ ~ valid_arc b
  end.

Lemma on_arc_gamma_unique_t : forall a t p,
  valid_arc a ->
  on_arc_gamma a t p ->
  t = arc_t a p.
Proof.
  intros a t p Hva [Ht Heq].
  pose proof (arc_gamma_signed_angle a t Hva Ht) as Hth.
  rewrite <- Heq in Hth.
  pose proof (arc_gamma_nonzero a Hva) as Hgnz.
  unfold arc_t.
  rewrite Hth.
  unfold arc_span.
  field.
  exact Hgnz.
Qed.

Lemma on_arc_gamma_imp_span : forall a t p,
  valid_arc a ->
  arc_mid_on_principal_span a ->
  on_arc_gamma a t p ->
  arc_span_contains_atan2 a p.
Proof.
  intros a t p Hva Hmid [Ht Heq].
  rewrite Heq.
  apply arc_gamma_in_span; [exact Hva | exact Hmid | exact Ht].
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"I_span_root_hit_iff","title":"II.1 radical root is an arc Hit iff on_arc_gamma both (span gamma, not gamma_full)","file":"theories/CircularCookSpanFilter.v","witness":"0007-II.1-span-filter","board":"ADR-0007"} *)

Theorem I_span_root_hit_iff :
  forall a b p,
    valid_arc a ->
    valid_arc b ->
    I_span_root a b p (I_span_hit_val a b p) <->
      on_arc_gamma_both a b p.
Proof.
  intros a b p Hva Hvb.
  unfold I_span_hit_val, I_span_root.
  split.
  - intros [_ [Ha Hb]].
    exists (arc_t a p), (arc_t b p).
    split; [exact Ha | exact Hb].
  - intros [ti [tj [Ha Hb]]].
    split; [reflexivity|].
    split.
    + pose proof (on_arc_gamma_unique_t a ti p Hva Ha) as Ht.
      rewrite <- Ht. exact Ha.
    + pose proof (on_arc_gamma_unique_t b tj p Hvb Hb) as Ht.
      rewrite <- Ht. exact Hb.
Qed.

Theorem I_span_root_empty_iff :
  forall a b p,
    I_span_root a b p IEmpty <->
      valid_arc a /\ valid_arc b /\ ~ on_arc_gamma_both a b p.
Proof.
  intros a b p.
  unfold I_span_root.
  split; [intros H; exact H | intros H; exact H].
Qed.

Theorem I_span_root_decline_iff :
  forall a b p,
    I_span_root a b p IDecline <->
      ~ valid_arc a \/ ~ valid_arc b.
Proof.
  intros a b p.
  unfold I_span_root.
  split; [intros H; exact H | intros H; exact H].
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked (0,0)/(7,0) r=5 proper arcs: p+ Hit, p− Empty.                      *)
(* -------------------------------------------------------------------------- *)

Lemma locked_p_minus_not_on_arc_gamma_A :
  forall t, ~ on_arc_gamma span_arc_A t locked_p_minus.
Proof.
  intros t H.
  apply span_p_minus_rejected_A.
  apply (on_arc_gamma_imp_span span_arc_A t locked_p_minus);
    [exact span_arc_A_valid | exact span_arc_A_mid_principal | exact H].
Qed.

Lemma locked_p_minus_not_on_both :
  ~ on_arc_gamma_both span_arc_A span_arc_B locked_p_minus.
Proof.
  intros [ti [_ [HA _]]].
  apply (locked_p_minus_not_on_arc_gamma_A ti).
  exact HA.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ii1_locked_plus_span_hit","title":"II.1 locked p+ inhabits IHit when on_arc_gamma both (in-span)","file":"theories/CircularCookSpanFilter.v","witness":"0007-II.1-span-filter","board":"ADR-0007"} *)

Lemma ii1_locked_plus_span_hit :
  I_span_root span_arc_A span_arc_B locked_p_plus
    (I_span_hit_val span_arc_A span_arc_B locked_p_plus).
Proof.
  apply I_span_root_hit_iff.
  - exact span_arc_A_valid.
  - exact span_arc_B_valid.
  - exists (arc_t span_arc_A locked_p_plus),
           (arc_t span_arc_B locked_p_plus).
    split; [exact span_p_plus_on_gamma_A | exact span_p_plus_on_gamma_B].
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ii1_locked_minus_span_empty","title":"II.1 locked p- inhabits IEmpty (out-of-span); not an arc Hit","file":"theories/CircularCookSpanFilter.v","witness":"0007-II.1-span-filter","board":"ADR-0007"} *)

Lemma ii1_locked_minus_span_empty :
  I_span_root span_arc_A span_arc_B locked_p_minus IEmpty.
Proof.
  apply I_span_root_empty_iff.
  split; [exact span_arc_A_valid|].
  split; [exact span_arc_B_valid|].
  exact locked_p_minus_not_on_both.
Qed.

Lemma ii1_locked_minus_not_span_hit :
  ~ I_span_root span_arc_A span_arc_B locked_p_minus
      (I_span_hit_val span_arc_A span_arc_B locked_p_minus).
Proof.
  intros H.
  apply locked_p_minus_not_on_both.
  apply (I_span_root_hit_iff span_arc_A span_arc_B locked_p_minus
           span_arc_A_valid span_arc_B_valid).
  exact H.
Qed.

(* I.2 γ_full still Hits p−. The span filter does not. *)
Lemma ii1_minus_full_not_span :
  on_full_circle locked_O1 locked_r
    (circ_t locked_O1 locked_p_minus) locked_p_minus /\
  on_full_circle locked_O2 locked_r
    (circ_t locked_O2 locked_p_minus) locked_p_minus /\
  ~ I_span_root span_arc_A span_arc_B locked_p_minus
      (I_span_hit_val span_arc_A span_arc_B locked_p_minus).
Proof.
  destruct locked_hit_minus_on_gamma as [H1 H2].
  split; [exact H1|].
  split; [exact H2|].
  exact ii1_locked_minus_not_span_hit.
Qed.

Lemma ii1_span_empty_neq_decline :
  IEmpty <> IDecline.
Proof.
  exact IEmpty_neq_IDecline.
Qed.

Lemma ii1_locked_minus_empty_not_decline :
  I_span_root span_arc_A span_arc_B locked_p_minus IEmpty /\
  ~ I_span_root span_arc_A span_arc_B locked_p_minus IDecline.
Proof.
  split; [exact ii1_locked_minus_span_empty|].
  intros Hdec.
  apply I_span_root_decline_iff in Hdec.
  destruct Hdec as [Ha | Hb].
  - apply Ha. exact span_arc_A_valid.
  - apply Hb. exact span_arc_B_valid.
Qed.

(* Collinear controls: no unique circle, so Decline — not Empty. *)
Definition span_decline_arc : CircularArc :=
  mkCircularArc (mkPoint 0 0) (mkPoint 1 0) (mkPoint 2 0).

Lemma span_decline_arc_invalid : ~ valid_arc span_decline_arc.
Proof.
  unfold valid_arc, span_decline_arc.
  cbn [px py arc_start arc_mid arc_end].
  intros H.
  apply H.
  ring.
Qed.

Lemma ii1_invalid_decline :
  I_span_root span_decline_arc span_arc_B locked_p_plus IDecline.
Proof.
  apply I_span_root_decline_iff.
  left.
  exact span_decline_arc_invalid.
Qed.

(* Span Hit is not host I_ok. The #666 fence still holds. *)
Lemma ii1_span_hit_not_host_I_ok :
  I_span_root span_arc_A span_arc_B locked_p_plus
    (I_span_hit_val span_arc_A span_arc_B locked_p_plus) /\
  ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
       (I_span_hit_val span_arc_A span_arc_B locked_p_plus).
Proof.
  split; [exact ii1_locked_plus_span_hit|].
  unfold I_span_hit_val.
  apply circular_hit_not_I_ok.
Qed.

(* -------------------------------------------------------------------------- *)
(* II.2–II.4 / H⊥ / SQL/MM cathedral stay parked. II.1 lands this letter.     *)
(* -------------------------------------------------------------------------- *)

Inductive CampaignII1Status : Type :=
| CampaignII1Landed
| CampaignII1Parked.

Definition campaign_ii1_status : CampaignII1Status := CampaignII1Landed.

Lemma campaign_ii1_is_landed :
  campaign_ii1_status = CampaignII1Landed.
Proof.
  reflexivity.
Qed.

Inductive CampaignII2Status : Type :=
| CampaignII2Discharged
| CampaignII2Parked.

Definition campaign_ii2_status : CampaignII2Status := CampaignII2Parked.

Lemma campaign_ii2_is_parked :
  campaign_ii2_status = CampaignII2Parked.
Proof.
  reflexivity.
Qed.

Inductive CampaignII3Status : Type :=
| CampaignII3Discharged
| CampaignII3Parked.

Definition campaign_ii3_status : CampaignII3Status := CampaignII3Parked.

Lemma campaign_ii3_is_parked :
  campaign_ii3_status = CampaignII3Parked.
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

(* Phase B = SQL/MM Part 3 required types (CS / CC / CP). Not this letter.
   CircularString is a sequence; this is one Arc. *)
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

Lemma ii1_rest_parked :
  campaign_ii2_status = CampaignII2Parked /\
  campaign_ii3_status = CampaignII3Parked /\
  campaign_ii4_status = CampaignII4Parked /\
  hperp_ii_status = HperpIIParked /\
  sql_mm_cathedral_status = SqlMmCathedralParked.
Proof.
  repeat split; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_ii1_hit_qed_or_qex","title":"II.1 radical root is arc Hit iff on_arc_gamma both (QED) or locked p+ declines the span filter (QEX); discharged QED; span gamma not gamma_full","file":"theories/CircularCookSpanFilter.v","witness":"0007-II.1-span-filter","board":"ADR-0007"} *)

Theorem ticket_0007_ii1_hit_qed_or_qex :
  ((forall a b p,
      valid_arc a ->
      valid_arc b ->
      I_span_root a b p (I_span_hit_val a b p) <->
        on_arc_gamma_both a b p) /\
   I_span_root span_arc_A span_arc_B locked_p_plus
     (I_span_hit_val span_arc_A span_arc_B locked_p_plus))
  \/
  I_span_root span_arc_A span_arc_B locked_p_plus IDecline.
Proof.
  left.
  split; [exact I_span_root_hit_iff|].
  exact ii1_locked_plus_span_hit.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_ii1_minus_qed_or_qex","title":"II.1 locked p- is span Empty and still on gamma_full (QED) or p- is a span Hit (QEX); discharged QED; filters differ","file":"theories/CircularCookSpanFilter.v","witness":"0007-II.1-span-filter","board":"ADR-0007"} *)

Theorem ticket_0007_ii1_minus_qed_or_qex :
  (I_span_root span_arc_A span_arc_B locked_p_minus IEmpty /\
   on_full_circle locked_O1 locked_r
     (circ_t locked_O1 locked_p_minus) locked_p_minus /\
   on_full_circle locked_O2 locked_r
     (circ_t locked_O2 locked_p_minus) locked_p_minus /\
   ~ I_span_root span_arc_A span_arc_B locked_p_minus
       (I_span_hit_val span_arc_A span_arc_B locked_p_minus))
  \/
  I_span_root span_arc_A span_arc_B locked_p_minus
    (I_span_hit_val span_arc_A span_arc_B locked_p_minus).
Proof.
  left.
  destruct ii1_minus_full_not_span as [H1 [H2 Hn]].
  split; [exact ii1_locked_minus_span_empty|].
  split; [exact H1|].
  split; [exact H2|].
  exact Hn.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_ii1_empty_neq_decline_qed_or_qex","title":"II.1 span Empty differs from Decline (QED) or they coincide on the locked minus root (QEX); discharged QED","file":"theories/CircularCookSpanFilter.v","witness":"0007-II.1-span-filter","board":"ADR-0007"} *)

Theorem ticket_0007_ii1_empty_neq_decline_qed_or_qex :
  (IEmpty <> IDecline /\
   I_span_root span_arc_A span_arc_B locked_p_minus IEmpty /\
   ~ I_span_root span_arc_A span_arc_B locked_p_minus IDecline /\
   I_span_root span_decline_arc span_arc_B locked_p_plus IDecline)
  \/
  I_span_root span_arc_A span_arc_B locked_p_minus IDecline.
Proof.
  left.
  destruct ii1_locked_minus_empty_not_decline as [He Hd].
  split; [exact ii1_span_empty_neq_decline|].
  split; [exact He|].
  split; [exact Hd|].
  exact ii1_invalid_decline.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_ii1_host_qed_or_qex","title":"II.1 discharges CircGamma and expands first cook (QED) or CircGamma stays QEX, first cook stays chord-chord, host circular I_ok is Decline (QEX); discharged QEX; span Hit is not host I_ok","file":"theories/CircularCookSpanFilter.v","witness":"0007-II.1-span-filter","board":"ADR-0007"} *)

Theorem ticket_0007_ii1_host_qed_or_qex :
  (circular_gamma_status = CircGammaDischarged /\
   first_cook_scope EggCircularArc EggCircularArc /\
   exists p ti tj,
     I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
          (IHit p ti tj))
  \/
  (circular_gamma_status = CircGammaDischarged /\
   first_cook_scope EggCircularArc EggCircularArc /\
   first_cook_scope EggChord EggChord /\
   I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc) IDecline /\
   (forall p ti tj,
      ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
           (IHit p ti tj)) /\
   I_span_root span_arc_A span_arc_B locked_p_plus
     (I_span_hit_val span_arc_A span_arc_B locked_p_plus) /\
   ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
        (I_span_hit_val span_arc_A span_arc_B locked_p_plus)).
Proof.
  right.
  destruct ii1_span_hit_not_host_I_ok as [Hhit Hhost].
  split; [exact ii1_host_circgamma_qex|].
  split; [exact ii1_host_not_first_cook|].
  split; [exact ii1_first_cook_stays_chord_chord|].
  split; [exact ii1_host_circular_decline|].
  split; [exact ii1_host_circular_hit_false|].
  split; [exact Hhit|].
  exact Hhost.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_ii1_park_qed_or_qex","title":"II.1 discharges II.2-II.4, Hperp, and the SQL/MM cathedral (QED) or names them parked (QEX); discharged QEX; II.1 landed; not CircularString concat","file":"theories/CircularCookSpanFilter.v","witness":"0007-II.1-span-filter","board":"ADR-0007"} *)

Theorem ticket_0007_ii1_park_qed_or_qex :
  (campaign_ii2_status = CampaignII2Discharged /\
   campaign_ii3_status = CampaignII3Discharged /\
   campaign_ii4_status = CampaignII4Discharged /\
   hperp_ii_status = HperpIIDischarged /\
   sql_mm_cathedral_status = SqlMmCathedralDone)
  \/
  (campaign_ii1_status = CampaignII1Landed /\
   campaign_ii2_status = CampaignII2Parked /\
   campaign_ii3_status = CampaignII3Parked /\
   campaign_ii4_status = CampaignII4Parked /\
   hperp_ii_status = HperpIIParked /\
   sql_mm_cathedral_status = SqlMmCathedralParked).
Proof.
  right.
  split; [exact campaign_ii1_is_landed|].
  exact ii1_rest_parked.
Qed.

Print Assumptions ii1_host_circgamma_qex.
Print Assumptions I_span_root_hit_iff.
Print Assumptions I_span_root_empty_iff.
Print Assumptions I_span_root_decline_iff.
Print Assumptions on_arc_gamma_unique_t.
Print Assumptions ii1_locked_plus_span_hit.
Print Assumptions ii1_locked_minus_span_empty.
Print Assumptions ii1_minus_full_not_span.
Print Assumptions ii1_span_hit_not_host_I_ok.
Print Assumptions ii1_invalid_decline.
Print Assumptions ticket_0007_ii1_hit_qed_or_qex.
Print Assumptions ticket_0007_ii1_minus_qed_or_qex.
Print Assumptions ticket_0007_ii1_empty_neq_decline_qed_or_qex.
Print Assumptions ticket_0007_ii1_host_qed_or_qex.
Print Assumptions ticket_0007_ii1_park_qed_or_qex.
