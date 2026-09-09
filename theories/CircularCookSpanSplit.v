(* ============================================================================
   NetTopologySuite.Proofs.CircularCookSpanSplit
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: Campaign II rung II.2 — split γ_span
   at in-span t; leftovers meet at p*.

   SQL/MM Part 3 required-type *path*: CircularString is a sequence of
   CircularArc primitives. This letter splits one Arc's span interpolant.
   A CS theorem needs a concatenation argument; this is not that.
   Not CompoundCurve. Not CurvePolygon. Not the SQL/MM cathedral.

   Takes an in-span Hit from II.1 (on_arc_gamma / I_span_root / locked
   p+ on the locked (0,0)/(7,0) r=5 proper arcs) and splits each
   span interpolant arc_gamma at the Hit's in-span parameters tᵢ / tⱼ.
   Not γ_full. Not circ_split from CircularCookSplit.

   QED: leftovers meet at p* (shared endpoint = Hit incidence, not a
   kiss); leftover γ stays on the parent circle and on the parent
   arc_gamma honesty story; locked p− stays II.1 Empty and gets no
   invented span cook.
   QEX: host CircGamma stays QEX; first cook stays chord–chord;
   host circular I_ok is Decline only; II.3–II.4, H⊥, and SQL/MM
   CS / CC / CP cathedral stay parked.

   Honesty fences:
     Host-Decline / CircGamma-QEX at the top of this module.
     I_circles_z ≠ I_circles_gamma ≠ sidecar cook ≠ span filter ≠
     span split ≠ glossary 𝓘 / I_gloss.
     Span split ≠ γ_full cook (CircularCookSplit). Span Hit ≠ host I_ok.
     Not first cook scope. Not a noder. Not ArcSplitAtNode.
     Not CircularString concatenation. Not CompoundCurve / CurvePolygon.
     Not a remint of CurveSegment / Exact* / Dart / Hobby /
     leftover_width / ArcSplitAtNode leftover-width / host circ_split.
     Do not fake atan2-free host γ.
     Do not start II.3 (I_ok_circ) / II.4 honesty letter / H⊥ /
     Phase B / a CRV-TOUCH kiss procedure / full SQL/MM cathedral.
     Locked p− stays out-of-span Empty — do not invent a span cook.
     No new kernel.

   WITNESS topic: overlay · claimId: 0007
   witness: 0007-II.2-span-split
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
  CircularCook CircularCookHit CircularCookSpan CircularCookSpanFilter.
Local Open Scope R_scope.

(* WITNESS: campaign=II rung=II.2 claim=0007
   file=theories/CircularCookSpanSplit.v
   kind=QED-or-QEX-span-split-meet-at-pstar
   gamma=arc-span-not-gamma-full
   not=circ-split,CircGamma-Discharge,first-cook-noding,II.3,II.4,Hperp
   not=SQL-MM-cathedral,CircularString-concat,CRV-TOUCH-kiss,span-cook-pminus *)

(* -------------------------------------------------------------------------- *)
(* Host-Decline / CircGamma-QEX fence (load-bearing, not decoration).         *)
(* -------------------------------------------------------------------------- *)

Lemma ii2_host_circgamma_qex :
  circular_gamma_status = CircGammaQEX.
Proof.
  exact circular_gamma_is_qex.
Qed.

Lemma ii2_host_not_first_cook :
  ~ first_cook_scope EggCircularArc EggCircularArc.
Proof.
  exact circular_not_first_cook_scope.
Qed.

Lemma ii2_host_circular_decline :
  I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc) IDecline.
Proof.
  exact circular_decline_I_ok.
Qed.

Lemma ii2_host_circular_hit_false :
  forall p ti tj,
    ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
         (IHit p ti tj).
Proof.
  exact circular_hit_not_I_ok.
Qed.

Lemma ii2_first_cook_stays_chord_chord :
  first_cook_scope EggChord EggChord.
Proof.
  exact first_cook_scope_chord_chord.
Qed.

(* -------------------------------------------------------------------------- *)
(* Span leftovers. Reuses arc_gamma. Not CircLeftover / circ_split.           *)
(* -------------------------------------------------------------------------- *)

Record SpanLeftover : Type := mkSpanLeftover {
  sl_arc : CircularArc;
  sl_t0 : R;
  sl_t1 : R
}.

Definition span_leftover_eval (sl : SpanLeftover) (u : R) : Point :=
  arc_gamma (sl_arc sl) ((1 - u) * sl_t0 sl + u * sl_t1 sl).

Definition span_split (a : CircularArc) (t : R) : SpanLeftover * SpanLeftover :=
  (mkSpanLeftover a 0 t, mkSpanLeftover a t 1).

Lemma span_split_left_reparam :
  forall a t u,
    span_leftover_eval (fst (span_split a t)) u = arc_gamma a (u * t).
Proof.
  intros a t u.
  unfold span_leftover_eval, span_split.
  simpl.
  apply f_equal.
  ring.
Qed.

Lemma span_split_right_reparam :
  forall a t u,
    span_leftover_eval (snd (span_split a t)) u =
    arc_gamma a (t + u * (1 - t)).
Proof.
  intros a t u.
  unfold span_leftover_eval, span_split.
  simpl.
  apply f_equal.
  ring.
Qed.

Lemma span_split_join :
  forall a t,
    span_leftover_eval (fst (span_split a t)) 1 = arc_gamma a t /\
    span_leftover_eval (snd (span_split a t)) 0 = arc_gamma a t.
Proof.
  intros a t.
  rewrite span_split_left_reparam, span_split_right_reparam.
  split; [apply f_equal; ring | apply f_equal; ring].
Qed.

Lemma span_split_ends :
  forall a t,
    span_leftover_eval (fst (span_split a t)) 0 = arc_gamma a 0 /\
    span_leftover_eval (snd (span_split a t)) 1 = arc_gamma a 1.
Proof.
  intros a t.
  rewrite span_split_left_reparam, span_split_right_reparam.
  split; [apply f_equal; ring | apply f_equal; ring].
Qed.

Lemma span_leftover_on_circle :
  forall sl u,
    dist_sq (arc_center (sl_arc sl)) (span_leftover_eval sl u)
      = arc_radius (sl_arc sl) * arc_radius (sl_arc sl).
Proof.
  intros sl u.
  unfold span_leftover_eval.
  apply arc_gamma_on_circle.
Qed.

Lemma span_param_left_in_unit : forall t u,
  0 <= t <= 1 ->
  0 <= u <= 1 ->
  0 <= u * t <= 1.
Proof.
  intros t u Ht Hu. nra.
Qed.

Lemma span_param_right_in_unit : forall t u,
  0 <= t <= 1 ->
  0 <= u <= 1 ->
  0 <= t + u * (1 - t) <= 1.
Proof.
  intros t u Ht Hu. nra.
Qed.

Lemma span_split_leftover_on_parent : forall a t u,
  0 <= t <= 1 ->
  0 <= u <= 1 ->
  on_arc_gamma a (u * t)
    (span_leftover_eval (fst (span_split a t)) u) /\
  on_arc_gamma a (t + u * (1 - t))
    (span_leftover_eval (snd (span_split a t)) u).
Proof.
  intros a t u Ht Hu.
  rewrite span_split_left_reparam, span_split_right_reparam.
  split.
  - split; [apply span_param_left_in_unit; [exact Ht | exact Hu] | reflexivity].
  - split; [apply span_param_right_in_unit; [exact Ht | exact Hu] | reflexivity].
Qed.

(* -------------------------------------------------------------------------- *)
(* Same-shape cook of an II.1 span Hit. Not circ_split. Not MintTwo.          *)
(* -------------------------------------------------------------------------- *)

Record SpanCookedPair : Type := mkSpanCookedPair {
  scp_L1 : SpanLeftover;
  scp_R1 : SpanLeftover;
  scp_L2 : SpanLeftover;
  scp_R2 : SpanLeftover
}.

Definition cook_span_root
  (a b : CircularArc) (ti tj : R) : SpanCookedPair :=
  mkSpanCookedPair
    (fst (span_split a ti))
    (snd (span_split a ti))
    (fst (span_split b tj))
    (snd (span_split b tj)).

Definition span_cooked_meets (cp : SpanCookedPair) (p : Point) : Prop :=
  span_leftover_eval (scp_L1 cp) 1 = p /\
  span_leftover_eval (scp_R1 cp) 0 = p /\
  span_leftover_eval (scp_L2 cp) 1 = p /\
  span_leftover_eval (scp_R2 cp) 0 = p.

Definition try_cook_span_root
  (a b : CircularArc) (o : IResult) : option SpanCookedPair :=
  match o with
  | IHit _ ti tj => Some (cook_span_root a b ti tj)
  | IEmpty => None
  | IDecline => None
  end.

Lemma try_cook_span_empty_none :
  forall a b, try_cook_span_root a b IEmpty = None.
Proof.
  intros. reflexivity.
Qed.

Lemma try_cook_span_decline_none :
  forall a b, try_cook_span_root a b IDecline = None.
Proof.
  intros. reflexivity.
Qed.

Lemma cook_span_root_meets : forall a b ti tj p,
  p = arc_gamma a ti ->
  p = arc_gamma b tj ->
  span_cooked_meets (cook_span_root a b ti tj) p.
Proof.
  intros a b ti tj p Ha Hb.
  unfold span_cooked_meets, cook_span_root.
  cbn [scp_L1 scp_R1 scp_L2 scp_R2].
  rewrite !span_split_left_reparam, !span_split_right_reparam.
  replace (1 * ti) with ti by ring.
  replace (ti + 0 * (1 - ti)) with ti by ring.
  replace (1 * tj) with tj by ring.
  replace (tj + 0 * (1 - tj)) with tj by ring.
  rewrite <- Ha, <- Hb.
  repeat split; reflexivity.
Qed.

Lemma cook_span_root_on_circle : forall a b ti tj u,
  dist_sq (arc_center a)
    (span_leftover_eval (scp_L1 (cook_span_root a b ti tj)) u)
    = arc_radius a * arc_radius a /\
  dist_sq (arc_center a)
    (span_leftover_eval (scp_R1 (cook_span_root a b ti tj)) u)
    = arc_radius a * arc_radius a /\
  dist_sq (arc_center b)
    (span_leftover_eval (scp_L2 (cook_span_root a b ti tj)) u)
    = arc_radius b * arc_radius b /\
  dist_sq (arc_center b)
    (span_leftover_eval (scp_R2 (cook_span_root a b ti tj)) u)
    = arc_radius b * arc_radius b.
Proof.
  intros a b ti tj u.
  unfold cook_span_root.
  cbn [scp_L1 scp_R1 scp_L2 scp_R2].
  rewrite !span_split_left_reparam, !span_split_right_reparam.
  repeat split; apply arc_gamma_on_circle.
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked (0,0)/(7,0) r=5 proper arcs: cook the II.1 in-span p+ Hit.          *)
(* -------------------------------------------------------------------------- *)

Definition locked_span_ti_plus : R := arc_t span_arc_A locked_p_plus.
Definition locked_span_tj_plus : R := arc_t span_arc_B locked_p_plus.

Definition cooked_span_plus : SpanCookedPair :=
  cook_span_root span_arc_A span_arc_B
    locked_span_ti_plus locked_span_tj_plus.

Lemma locked_span_plus_gamma :
  locked_p_plus = arc_gamma span_arc_A locked_span_ti_plus /\
  locked_p_plus = arc_gamma span_arc_B locked_span_tj_plus.
Proof.
  unfold locked_span_ti_plus, locked_span_tj_plus.
  destruct span_p_plus_on_gamma_A as [_ Ha].
  destruct span_p_plus_on_gamma_B as [_ Hb].
  split; [exact Ha | exact Hb].
Qed.

Lemma locked_span_plus_t_in_unit :
  0 <= locked_span_ti_plus <= 1 /\
  0 <= locked_span_tj_plus <= 1.
Proof.
  unfold locked_span_ti_plus, locked_span_tj_plus.
  destruct span_p_plus_on_gamma_A as [Ha _].
  destruct span_p_plus_on_gamma_B as [Hb _].
  split; [exact Ha | exact Hb].
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"cooked_span_plus_meets","title":"II.2 locked in-span p+ leftovers of arc_gamma meet at p* (Hit incidence, not a kiss)","file":"theories/CircularCookSpanSplit.v","witness":"0007-II.2-span-split","board":"ADR-0007"} *)

Lemma cooked_span_plus_meets :
  span_cooked_meets cooked_span_plus locked_p_plus.
Proof.
  unfold cooked_span_plus.
  destruct locked_span_plus_gamma as [Ha Hb].
  apply cook_span_root_meets; [exact Ha | exact Hb].
Qed.

Lemma cooked_span_plus_try :
  try_cook_span_root span_arc_A span_arc_B
    (I_span_hit_val span_arc_A span_arc_B locked_p_plus)
    = Some cooked_span_plus.
Proof.
  unfold try_cook_span_root, I_span_hit_val, cooked_span_plus,
         cook_span_root, locked_span_ti_plus, locked_span_tj_plus.
  reflexivity.
Qed.

Lemma leftover_meet_is_hit_not_kiss :
  span_cooked_meets cooked_span_plus locked_p_plus /\
  I_span_root span_arc_A span_arc_B locked_p_plus
    (I_span_hit_val span_arc_A span_arc_B locked_p_plus) /\
  ~ I_span_root span_arc_A span_arc_B locked_p_plus IEmpty /\
  IHit locked_p_plus locked_span_ti_plus locked_span_tj_plus <> IEmpty.
Proof.
  split; [exact cooked_span_plus_meets|].
  split; [exact ii1_locked_plus_span_hit|].
  split.
  - intros Hemp.
    apply I_span_root_empty_iff in Hemp.
    destruct Hemp as [_ [_ Hn]].
    apply Hn.
    exists locked_span_ti_plus, locked_span_tj_plus.
    split; [exact span_p_plus_on_gamma_A | exact span_p_plus_on_gamma_B].
  - apply IHit_neq_IEmpty.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"cooked_span_plus_on_parent","title":"II.2 leftover gamma stays on the parent circle and on_arc_gamma of the parent span","file":"theories/CircularCookSpanSplit.v","witness":"0007-II.2-span-split","board":"ADR-0007"} *)

Lemma cooked_span_plus_on_parent : forall u,
  0 <= u <= 1 ->
  dist_sq (arc_center span_arc_A)
    (span_leftover_eval (scp_L1 cooked_span_plus) u)
    = arc_radius span_arc_A * arc_radius span_arc_A /\
  dist_sq (arc_center span_arc_A)
    (span_leftover_eval (scp_R1 cooked_span_plus) u)
    = arc_radius span_arc_A * arc_radius span_arc_A /\
  dist_sq (arc_center span_arc_B)
    (span_leftover_eval (scp_L2 cooked_span_plus) u)
    = arc_radius span_arc_B * arc_radius span_arc_B /\
  dist_sq (arc_center span_arc_B)
    (span_leftover_eval (scp_R2 cooked_span_plus) u)
    = arc_radius span_arc_B * arc_radius span_arc_B /\
  on_arc_gamma span_arc_A (u * locked_span_ti_plus)
    (span_leftover_eval (scp_L1 cooked_span_plus) u) /\
  on_arc_gamma span_arc_A
    (locked_span_ti_plus + u * (1 - locked_span_ti_plus))
    (span_leftover_eval (scp_R1 cooked_span_plus) u) /\
  on_arc_gamma span_arc_B (u * locked_span_tj_plus)
    (span_leftover_eval (scp_L2 cooked_span_plus) u) /\
  on_arc_gamma span_arc_B
    (locked_span_tj_plus + u * (1 - locked_span_tj_plus))
    (span_leftover_eval (scp_R2 cooked_span_plus) u).
Proof.
  intros u Hu.
  unfold cooked_span_plus.
  destruct (cook_span_root_on_circle span_arc_A span_arc_B
              locked_span_ti_plus locked_span_tj_plus u)
    as [Hc1 [Hc2 [Hc3 Hc4]]].
  destruct locked_span_plus_t_in_unit as [Hti Htj].
  destruct (span_split_leftover_on_parent span_arc_A locked_span_ti_plus u
              Hti Hu) as [Hl1 Hr1].
  destruct (span_split_leftover_on_parent span_arc_B locked_span_tj_plus u
              Htj Hu) as [Hl2 Hr2].
  repeat split; assumption.
Qed.

(* Locked p− stays II.1 Empty. Do not invent a span cook. *)
Lemma cooked_span_minus_none :
  I_span_root span_arc_A span_arc_B locked_p_minus IEmpty /\
  try_cook_span_root span_arc_A span_arc_B IEmpty = None /\
  ~ I_span_root span_arc_A span_arc_B locked_p_minus
      (I_span_hit_val span_arc_A span_arc_B locked_p_minus).
Proof.
  split; [exact ii1_locked_minus_span_empty|].
  split; [reflexivity|].
  exact ii1_locked_minus_not_span_hit.
Qed.

Lemma ii2_span_hit_not_host_I_ok :
  I_span_root span_arc_A span_arc_B locked_p_plus
    (I_span_hit_val span_arc_A span_arc_B locked_p_plus) /\
  ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
       (I_span_hit_val span_arc_A span_arc_B locked_p_plus).
Proof.
  exact ii1_span_hit_not_host_I_ok.
Qed.

(* Span split evaluates arc_gamma, not circ_gamma / γ_full. *)
Lemma span_split_uses_arc_gamma :
  forall a t u,
    span_leftover_eval (fst (span_split a t)) u = arc_gamma a (u * t) /\
    span_leftover_eval (snd (span_split a t)) u =
      arc_gamma a (t + u * (1 - t)).
Proof.
  intros a t u.
  split; [apply span_split_left_reparam | apply span_split_right_reparam].
Qed.

(* -------------------------------------------------------------------------- *)
(* II.2 lands this letter. II.3 (I_ok_circ) / II.4 / H⊥ / SQL/MM stay parked. *)
(* -------------------------------------------------------------------------- *)

Inductive CampaignII2Status : Type :=
| CampaignII2Landed
| CampaignII2Parked.

Definition campaign_ii2_status : CampaignII2Status := CampaignII2Landed.

Lemma campaign_ii2_is_landed :
  campaign_ii2_status = CampaignII2Landed.
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
   CircularString is a sequence; this is one Arc split. *)
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

Lemma ii2_rest_parked :
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

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_ii2_meet_qed_or_qex","title":"II.2 span leftovers meet at locked p+ and that join is the II.1 Hit (QED) or leftovers miss p+ (QEX); discharged QED; Hit incidence not a kiss","file":"theories/CircularCookSpanSplit.v","witness":"0007-II.2-span-split","board":"ADR-0007"} *)

Theorem ticket_0007_ii2_meet_qed_or_qex :
  (span_cooked_meets cooked_span_plus locked_p_plus /\
   try_cook_span_root span_arc_A span_arc_B
     (I_span_hit_val span_arc_A span_arc_B locked_p_plus)
     = Some cooked_span_plus /\
   I_span_root span_arc_A span_arc_B locked_p_plus
     (I_span_hit_val span_arc_A span_arc_B locked_p_plus) /\
   ~ I_span_root span_arc_A span_arc_B locked_p_plus IEmpty /\
   IHit locked_p_plus locked_span_ti_plus locked_span_tj_plus <> IEmpty)
  \/
  ~ span_cooked_meets cooked_span_plus locked_p_plus.
Proof.
  left.
  destruct leftover_meet_is_hit_not_kiss as [Hm [Hh [He Hk]]].
  split; [exact Hm|].
  split; [exact cooked_span_plus_try|].
  split; [exact Hh|].
  split; [exact He|].
  exact Hk.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_ii2_honesty_qed_or_qex","title":"II.2 leftover gamma stays on the parent circle and parent on_arc_gamma (QED) or leaves the parent circle (QEX); discharged QED; span gamma not gamma_full","file":"theories/CircularCookSpanSplit.v","witness":"0007-II.2-span-split","board":"ADR-0007"} *)

Theorem ticket_0007_ii2_honesty_qed_or_qex :
  ((forall u,
      0 <= u <= 1 ->
      dist_sq (arc_center span_arc_A)
        (span_leftover_eval (scp_L1 cooked_span_plus) u)
        = arc_radius span_arc_A * arc_radius span_arc_A /\
      dist_sq (arc_center span_arc_B)
        (span_leftover_eval (scp_L2 cooked_span_plus) u)
        = arc_radius span_arc_B * arc_radius span_arc_B /\
      on_arc_gamma span_arc_A (u * locked_span_ti_plus)
        (span_leftover_eval (scp_L1 cooked_span_plus) u) /\
      on_arc_gamma span_arc_B (u * locked_span_tj_plus)
        (span_leftover_eval (scp_L2 cooked_span_plus) u)) /\
   (forall a t u,
      span_leftover_eval (fst (span_split a t)) u = arc_gamma a (u * t)))
  \/
  exists u,
    0 <= u <= 1 /\
    dist_sq (arc_center span_arc_A)
      (span_leftover_eval (scp_L1 cooked_span_plus) u)
      <> arc_radius span_arc_A * arc_radius span_arc_A.
Proof.
  left.
  split.
  - intros u Hu.
    destruct (cooked_span_plus_on_parent u Hu)
      as [Hc1 [_ [Hc3 [_ [Hl1 [_ [Hl2 _]]]]]]].
    split; [exact Hc1|].
    split; [exact Hc3|].
    split; [exact Hl1|].
    exact Hl2.
  - intros a t u.
    apply span_split_left_reparam.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_ii2_minus_qed_or_qex","title":"II.2 locked p- stays span Empty and is not cooked (QED) or Empty mints a span cook (QEX); discharged QED; do not invent a span cook","file":"theories/CircularCookSpanSplit.v","witness":"0007-II.2-span-split","board":"ADR-0007"} *)

Theorem ticket_0007_ii2_minus_qed_or_qex :
  (I_span_root span_arc_A span_arc_B locked_p_minus IEmpty /\
   try_cook_span_root span_arc_A span_arc_B IEmpty = None /\
   try_cook_span_root span_arc_A span_arc_B IDecline = None /\
   ~ I_span_root span_arc_A span_arc_B locked_p_minus
       (I_span_hit_val span_arc_A span_arc_B locked_p_minus))
  \/
  try_cook_span_root span_arc_A span_arc_B IEmpty <> None.
Proof.
  left.
  destruct cooked_span_minus_none as [He [Hn Hhit]].
  split; [exact He|].
  split; [exact Hn|].
  split; [reflexivity|].
  exact Hhit.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_ii2_host_qed_or_qex","title":"II.2 discharges CircGamma and expands first cook (QED) or CircGamma stays QEX, first cook stays chord-chord, host circular I_ok is Decline (QEX); discharged QEX; span Hit is not host I_ok","file":"theories/CircularCookSpanSplit.v","witness":"0007-II.2-span-split","board":"ADR-0007"} *)

Theorem ticket_0007_ii2_host_qed_or_qex :
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
   I_span_root span_arc_A span_arc_B locked_p_plus
     (I_span_hit_val span_arc_A span_arc_B locked_p_plus) /\
   ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
        (I_span_hit_val span_arc_A span_arc_B locked_p_plus)).
Proof.
  right.
  destruct ii2_span_hit_not_host_I_ok as [Hhit Hhost].
  split; [exact ii2_host_circgamma_qex|].
  split; [exact ii2_host_not_first_cook|].
  split; [exact ii2_first_cook_stays_chord_chord|].
  split; [exact ii2_host_circular_decline|].
  split; [exact ii2_host_circular_hit_false|].
  split; [exact Hhit|].
  exact Hhost.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_ii2_park_qed_or_qex","title":"II.2 discharges II.3-II.4, Hperp, and the SQL/MM cathedral (QED) or names them parked (QEX); discharged QEX; II.2 landed; not CircularString concat; not I_ok_circ","file":"theories/CircularCookSpanSplit.v","witness":"0007-II.2-span-split","board":"ADR-0007"} *)

Theorem ticket_0007_ii2_park_qed_or_qex :
  (campaign_ii3_status = CampaignII3Discharged /\
   campaign_ii4_status = CampaignII4Discharged /\
   hperp_ii_status = HperpIIDischarged /\
   sql_mm_cathedral_status = SqlMmCathedralDone)
  \/
  (campaign_ii2_status = CampaignII2Landed /\
   campaign_ii3_status = CampaignII3Parked /\
   campaign_ii4_status = CampaignII4Parked /\
   hperp_ii_status = HperpIIParked /\
   sql_mm_cathedral_status = SqlMmCathedralParked).
Proof.
  right.
  split; [exact campaign_ii2_is_landed|].
  exact ii2_rest_parked.
Qed.

Print Assumptions ii2_host_circgamma_qex.
Print Assumptions span_split_join.
Print Assumptions span_leftover_on_circle.
Print Assumptions span_split_leftover_on_parent.
Print Assumptions cook_span_root_meets.
Print Assumptions cooked_span_plus_meets.
Print Assumptions leftover_meet_is_hit_not_kiss.
Print Assumptions cooked_span_plus_on_parent.
Print Assumptions cooked_span_minus_none.
Print Assumptions span_split_uses_arc_gamma.
Print Assumptions ticket_0007_ii2_meet_qed_or_qex.
Print Assumptions ticket_0007_ii2_honesty_qed_or_qex.
Print Assumptions ticket_0007_ii2_minus_qed_or_qex.
Print Assumptions ticket_0007_ii2_host_qed_or_qex.
Print Assumptions ticket_0007_ii2_park_qed_or_qex.
