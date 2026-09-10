(* ============================================================================
   NetTopologySuite.Proofs.SidecarCircMixed
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: Phase B mixed LS–CS joints — host-facing
   sidecar Hit for LineString × CircularString / CircularString ×
   LineString concat incidence (claimId 0007-B-mixed).

   B.2 / B.3 already prove same-kind joints Hit (LS–LS via host I_ok;
   CS–CS via I_ok_circ). Mixed joints were host I_ok Decline because
   MkOutOfScope EggCircularArc carries no interpolant and
   first_cook_scope stays chord–chord (I.1). That Decline is the
   fence, not missing geometry at a contiguous endpoint.

   This letter cuts the smallest honest Hit: a contiguous mixed joint
   inhabits I_ok_mixed at (p, tᵢ=1, tⱼ=0) via host chord_eval and
   sidecar arc_gamma. Joint params are not interior. Concat incidence
   is already a hen — not an interior arc–chord cook and not a
   CRV-TOUCH kiss certificate.

   I_ok_mixed is the glossary-type inhabitant. It is not host I_ok
   (MkChord × MkOutOfScope stays Decline; a constructed mixed
   interior Hit still does not inhabit I_ok). Host CircGamma stays
   QEX — this sidecar reuses arc_gamma; it does not remint CircGamma
   and does not expand first_cook_scope to circular×chord interiors.

   Locked fixtures (reused by B.2 / B.3, not reminted here):
     LS×CS : COMPOUNDCURVE((-5 0, 5 0), CIRCULARSTRING(5 0, 0 -5, -5 0))
             joint at (5,0)
     CS×LS : the mixed-ring close at (-5,0)

   QED: ∀ LS–CS joint is I_ok_mixed Hit at (end, 1, 0); ∀ CS–LS
   joint is I_ok_mixed Hit at (end, 1, 0); joint params are not
   interior; Hit licenses already-hen incidence (no new split mint);
   I_ok_mixed Hit ≠ host I_ok.
   QEX: host CircGamma stays QEX; first cook stays chord–chord;
   host mixed I_ok is Decline; interior mixed cook stays out of
   first cook (not invented here); H⊥ / bag noder / MultiCurve /
   CircGamma remint stay parked; SQL/MM is not done.

   Honesty fences:
     Host-Decline / CircGamma-QEX at the top of this module.
     I_circles_z ≠ I_circles_gamma ≠ sidecar cook ≠ span filter ≠
     span split ≠ I_ok_circ ≠ I_ok_mixed ≠ CS concat joint ≠
     CC member joint ≠ glossary I_gloss / host I_ok.
     Sidecar ≠ host try_cook_hit / host I_ok.
     Joint is concat incidence, not an interior span cook and not
     a CRV-TOUCH kiss certificate.
     Not first cook scope. Not a bag noder. Not ArcSplitAtNode.
     Not G¹ / H⊥. Not MultiCurve. Not MerkatorBV.
     Not a remint of CurveSegment / Exact* / Dart / Hobby /
     leftover_width / ArcSplitAtNode leftover-width / host circ_split /
     CircularStringValid / CompoundCurveKoc family / CircGamma.
     Do not fake atan2-free host γ. Do not expand first_cook_scope
     to circular×chord interiors. Do not start H⊥ / a CRV-TOUCH
     kiss procedure / CircGamma remint / full SQL/MM cathedral.
     No new kernel. Not SQL/MM done.

   WITNESS topic: overlay · claimId: 0007
   witness: 0007-B-mixed-ls-cs-joints
   board: ADR-0007
   4-axiom (atan2 / Classical_Prop.classic via CircularCookCsConcat /
     CircularCookOkCirc). Category C audit-exception: same atan2
     lineage as B.1; no extra axioms.
   No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance SheetHenCook CurveGeometry
  CircularCook CircularCookHit CircularCookSpan CircularCookOkCirc.
From NTS.Proofs Require CircularCookCsConcat.
Local Open Scope R_scope.

(* WITNESS: campaign=B rung=B-mixed claim=0007
   file=theories/SidecarCircMixed.v
   kind=QED-or-QEX-mixed-ls-cs-joint-hit-sidecar
   gamma=arc-span-not-gamma-full
   reuse=chord_eval,arc_gamma,on_chord,on_arc_gamma
   not=new-kernel,CircGamma-Discharge,first-cook-noding,SQL-MM-done
   not=bag-noder,interior-arc-chord-cook,CRV-TOUCH-kiss
   park=Hperp,interior-mixed-cook,CircGamma-remint
   land=Phase-B-mixed-joint-Hit *)

(* -------------------------------------------------------------------------- *)
(* Host-Decline / CircGamma-QEX fence (load-bearing, not decoration).         *)
(* -------------------------------------------------------------------------- *)

Lemma mixed_host_circgamma_qex :
  circular_gamma_status = CircGammaQEX.
Proof.
  exact circular_gamma_is_qex.
Qed.

Lemma mixed_host_not_first_cook :
  ~ first_cook_scope EggCircularArc EggCircularArc.
Proof.
  exact circular_not_first_cook_scope.
Qed.

Lemma mixed_first_cook_stays_chord_chord :
  first_cook_scope EggChord EggChord.
Proof.
  exact first_cook_scope_chord_chord.
Qed.

Lemma mixed_not_first_cook :
  ~ first_cook_scope EggChord EggCircularArc.
Proof.
  exact chord_circular_not_first_cook_scope.
Qed.

Lemma mixed_host_ls_cs_decline :
  forall c,
    I_ok (MkChord c) (MkOutOfScope EggCircularArc) IDecline.
Proof.
  intros c.
  unfold I_ok, first_cook_scope, egg_class.
  intro H. exact H.
Qed.

Lemma mixed_host_cs_ls_decline :
  forall c,
    I_ok (MkOutOfScope EggCircularArc) (MkChord c) IDecline.
Proof.
  intros c.
  unfold I_ok, first_cook_scope, egg_class.
  intro H. exact H.
Qed.

Lemma mixed_host_ls_cs_hit_false :
  forall c p ti tj,
    ~ I_ok (MkChord c) (MkOutOfScope EggCircularArc) (IHit p ti tj).
Proof.
  intros c p ti tj H. exact H.
Qed.

Lemma mixed_host_cs_ls_hit_false :
  forall c p ti tj,
    ~ I_ok (MkOutOfScope EggCircularArc) (MkChord c) (IHit p ti tj).
Proof.
  intros c p ti tj H. exact H.
Qed.

Lemma mixed_host_ls_cs_empty_false :
  forall c,
    ~ I_ok (MkChord c) (MkOutOfScope EggCircularArc) IEmpty.
Proof.
  intros c H. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* Mixed glossary inhabitant. Chord payload × CircEgg payload.                *)
(* Host MkOutOfScope EggCircularArc still carries no interpolant.             *)
(* -------------------------------------------------------------------------- *)

Definition mixed_joint_params (ti tj : R) : Prop :=
  (ti = 1 /\ tj = 0) \/ (ti = 0 /\ tj = 1).

Definition interior_span_params :=
  CircularCookCsConcat.interior_span_params.

Inductive MixedEggs : Type :=
| MixLsCs (c : ChordEgg) (a : CircEgg)
| MixCsLs (a : CircEgg) (c : ChordEgg).

Definition I_ok_mixed (m : MixedEggs) (o : IResult) : Prop :=
  match m, o with
  | MixLsCs c a, IHit p ti tj =>
      valid_arc a /\
      on_chord c ti p /\
      on_arc_gamma a tj p /\
      mixed_joint_params ti tj
  | MixCsLs a c, IHit p ti tj =>
      valid_arc a /\
      on_arc_gamma a ti p /\
      on_chord c tj p /\
      mixed_joint_params ti tj
  | _, IEmpty => False
  | MixLsCs _ a, IDecline => ~ valid_arc a
  | MixCsLs a _, IDecline => ~ valid_arc a
  end.

Definition I_ok_mixed_ls_cs (c : ChordEgg) (a : CircEgg) (o : IResult) : Prop :=
  I_ok_mixed (MixLsCs c a) o.

Definition I_ok_mixed_cs_ls (a : CircEgg) (c : ChordEgg) (o : IResult) : Prop :=
  I_ok_mixed (MixCsLs a c) o.

Definition ls_cs_joint (c : ChordEgg) (a : CircEgg) : Prop :=
  valid_arc a /\ ce_p1 c = arc_start a.

Definition cs_ls_joint (a : CircEgg) (c : ChordEgg) : Prop :=
  valid_arc a /\ arc_end a = ce_p0 c.

Definition ls_cs_joint_hit (c : ChordEgg) (a : CircEgg) : IResult :=
  IHit (ce_p1 c) 1 0.

Definition cs_ls_joint_hit (a : CircEgg) (c : ChordEgg) : IResult :=
  IHit (arc_end a) 1 0.

Lemma mixed_on_chord_at_start : forall c,
  on_chord c 0 (ce_p0 c).
Proof.
  intros c.
  unfold on_chord.
  split; [lra|].
  symmetry. apply chord_eval_at_0.
Qed.

Lemma mixed_on_chord_at_end : forall c,
  on_chord c 1 (ce_p1 c).
Proof.
  intros c.
  unfold on_chord.
  split; [lra|].
  symmetry. apply chord_eval_at_1.
Qed.

Lemma mixed_joint_params_end_start :
  mixed_joint_params 1 0.
Proof.
  left. split; reflexivity.
Qed.

Lemma mixed_joint_params_not_interior :
  forall ti tj,
    mixed_joint_params ti tj -> ~ interior_span_params ti tj.
Proof.
  intros ti tj [ [Hti Htj] | [Hti Htj] ];
    intros [[_ Hi] _]; subst; lra.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ls_cs_joint_I_ok_mixed","title":"Phase B mixed forall LS-CS CompoundCurve joint is I_ok_mixed Hit at (ce_p1, t=1, t=0) via chord_eval and sidecar arc_gamma; concat incidence; no interior arc-chord cook; no new kernel","file":"theories/SidecarCircMixed.v","witness":"0007-B-mixed-ls-cs-joints","board":"ADR-0007"} *)

Theorem ls_cs_joint_I_ok_mixed :
  forall c a,
    ls_cs_joint c a ->
    I_ok_mixed (MixLsCs c a) (ls_cs_joint_hit c a).
Proof.
  intros c a [Hva Heq].
  unfold I_ok_mixed, ls_cs_joint_hit.
  split; [exact Hva|].
  split; [apply mixed_on_chord_at_end|].
  split.
  - rewrite Heq. apply CircularCookCsConcat.on_arc_gamma_at_start. exact Hva.
  - exact mixed_joint_params_end_start.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"cs_ls_joint_I_ok_mixed","title":"Phase B mixed forall CS-LS CompoundCurve / CurvePolygon closing joint is I_ok_mixed Hit at (arc_end, t=1, t=0) via sidecar arc_gamma and chord_eval; concat incidence; no interior arc-chord cook; no new kernel","file":"theories/SidecarCircMixed.v","witness":"0007-B-mixed-ls-cs-joints","board":"ADR-0007"} *)

Theorem cs_ls_joint_I_ok_mixed :
  forall a c,
    cs_ls_joint a c ->
    I_ok_mixed (MixCsLs a c) (cs_ls_joint_hit a c).
Proof.
  intros a c [Hva Heq].
  unfold I_ok_mixed, cs_ls_joint_hit.
  split; [exact Hva|].
  split.
  - apply CircularCookCsConcat.on_arc_gamma_at_end. exact Hva.
  - split.
    + rewrite Heq. apply mixed_on_chord_at_start.
    + exact mixed_joint_params_end_start.
Qed.

(* Joint Hit is already-hen incidence. Empty / Decline mint none.
   Does not feed host try_cook_hit. Does not invent interior cook. *)
Lemma I_ok_mixed_hit_licenses_joint_hen :
  forall c a,
    ls_cs_joint c a ->
    I_ok_mixed (MixLsCs c a) (ls_cs_joint_hit c a) /\
    ce_p1 c = arc_start a /\
    ~ interior_span_params 1 0.
Proof.
  intros c a Hj.
  split; [apply ls_cs_joint_I_ok_mixed; exact Hj|].
  split; [apply Hj|].
  exact CircularCookCsConcat.joint_params_not_interior.
Qed.

Lemma I_ok_mixed_rev_hit_licenses_joint_hen :
  forall a c,
    cs_ls_joint a c ->
    I_ok_mixed (MixCsLs a c) (cs_ls_joint_hit a c) /\
    arc_end a = ce_p0 c /\
    ~ interior_span_params 1 0.
Proof.
  intros a c Hj.
  split; [apply cs_ls_joint_I_ok_mixed; exact Hj|].
  split; [apply Hj|].
  exact CircularCookCsConcat.joint_params_not_interior.
Qed.

Lemma I_ok_mixed_hit_not_host_I_ok :
  forall c a,
    ls_cs_joint c a ->
    I_ok_mixed (MixLsCs c a) (ls_cs_joint_hit c a) /\
    ~ I_ok (MkChord c) (MkOutOfScope EggCircularArc) (ls_cs_joint_hit c a).
Proof.
  intros c a Hj.
  split; [apply ls_cs_joint_I_ok_mixed; exact Hj|].
  unfold ls_cs_joint_hit.
  apply mixed_host_ls_cs_hit_false.
Qed.

Lemma I_ok_mixed_rev_hit_not_host_I_ok :
  forall a c,
    cs_ls_joint a c ->
    I_ok_mixed (MixCsLs a c) (cs_ls_joint_hit a c) /\
    ~ I_ok (MkOutOfScope EggCircularArc) (MkChord c) (cs_ls_joint_hit a c).
Proof.
  intros a c Hj.
  split; [apply cs_ls_joint_I_ok_mixed; exact Hj|].
  unfold cs_ls_joint_hit.
  apply mixed_host_cs_ls_hit_false.
Qed.

Lemma I_ok_mixed_empty_false :
  forall m, ~ I_ok_mixed m IEmpty.
Proof.
  intros [c a | a c] H; exact H.
Qed.

Lemma I_ok_mixed_empty_neq_decline :
  IEmpty <> IDecline.
Proof.
  exact IEmpty_neq_IDecline.
Qed.

(* Interior mixed cook is not this letter. first_cook_scope stays
   chord–chord; host I_ok mixed Hit stays False. *)
Lemma mixed_interior_not_first_cook :
  ~ first_cook_scope EggChord EggCircularArc
  /\ (forall c p ti tj,
        ~ I_ok (MkChord c) (MkOutOfScope EggCircularArc) (IHit p ti tj)).
Proof.
  split; [exact mixed_not_first_cook|].
  exact mixed_host_ls_cs_hit_false.
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked mixed joints (B.2 sequential / B.3 closing).                        *)
(* -------------------------------------------------------------------------- *)

Definition locked_mixed_ls : ChordEgg :=
  mkChordEgg (mkPoint (-5) 0) (mkPoint 5 0).

Definition locked_mixed_cs : CircEgg :=
  CircularCookCsConcat.locked_cs_arc_2.

Definition locked_mixed_ls_cs_pt : Point := mkPoint 5 0.

Definition locked_mixed_cs_ls_pt : Point := mkPoint (-5) 0.

Lemma locked_mixed_ls_cs_joint :
  ls_cs_joint locked_mixed_ls locked_mixed_cs.
Proof.
  unfold ls_cs_joint, locked_mixed_ls, locked_mixed_cs.
  split; [exact CircularCookCsConcat.locked_cs_arc_2_valid|].
  reflexivity.
Qed.

Lemma locked_mixed_cs_ls_joint :
  cs_ls_joint locked_mixed_cs locked_mixed_ls.
Proof.
  unfold cs_ls_joint, locked_mixed_ls, locked_mixed_cs.
  split; [exact CircularCookCsConcat.locked_cs_arc_2_valid|].
  reflexivity.
Qed.

Lemma locked_mixed_ls_cs_I_ok_mixed :
  I_ok_mixed (MixLsCs locked_mixed_ls locked_mixed_cs)
    (ls_cs_joint_hit locked_mixed_ls locked_mixed_cs).
Proof.
  apply ls_cs_joint_I_ok_mixed.
  exact locked_mixed_ls_cs_joint.
Qed.

Lemma locked_mixed_cs_ls_I_ok_mixed :
  I_ok_mixed (MixCsLs locked_mixed_cs locked_mixed_ls)
    (cs_ls_joint_hit locked_mixed_cs locked_mixed_ls).
Proof.
  apply cs_ls_joint_I_ok_mixed.
  exact locked_mixed_cs_ls_joint.
Qed.

Lemma locked_mixed_ls_cs_host_decline :
  I_ok (MkChord locked_mixed_ls) (MkOutOfScope EggCircularArc) IDecline.
Proof.
  apply mixed_host_ls_cs_decline.
Qed.

Lemma locked_mixed_cs_ls_host_decline :
  I_ok (MkOutOfScope EggCircularArc) (MkChord locked_mixed_ls) IDecline.
Proof.
  apply mixed_host_cs_ls_decline.
Qed.

Lemma locked_mixed_ls_cs_hit_not_host_I_ok :
  I_ok_mixed (MixLsCs locked_mixed_ls locked_mixed_cs)
    (ls_cs_joint_hit locked_mixed_ls locked_mixed_cs)
  /\ ~ I_ok (MkChord locked_mixed_ls) (MkOutOfScope EggCircularArc)
        (IHit locked_mixed_ls_cs_pt 1 0).
Proof.
  split; [exact locked_mixed_ls_cs_I_ok_mixed|].
  apply mixed_host_ls_cs_hit_false.
Qed.

Lemma locked_mixed_cs_ls_hit_not_host_I_ok :
  I_ok_mixed (MixCsLs locked_mixed_cs locked_mixed_ls)
    (cs_ls_joint_hit locked_mixed_cs locked_mixed_ls)
  /\ ~ I_ok (MkOutOfScope EggCircularArc) (MkChord locked_mixed_ls)
        (IHit locked_mixed_cs_ls_pt 1 0).
Proof.
  split; [exact locked_mixed_cs_ls_I_ok_mixed|].
  apply mixed_host_cs_ls_hit_false.
Qed.

Lemma locked_mixed_joint_pt_eq :
  ce_p1 locked_mixed_ls = locked_mixed_ls_cs_pt
  /\ arc_end locked_mixed_cs = locked_mixed_cs_ls_pt.
Proof.
  split; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Host stays QEX. Reuse: no new interpolant.                                 *)
(* -------------------------------------------------------------------------- *)

Lemma mixed_host_stays_qex :
  circular_gamma_status = CircGammaQEX
  /\ ~ first_cook_scope EggCircularArc EggCircularArc
  /\ first_cook_scope EggChord EggChord
  /\ ~ first_cook_scope EggChord EggCircularArc
  /\ I_ok (MkChord locked_mixed_ls) (MkOutOfScope EggCircularArc) IDecline
  /\ (forall p ti tj,
        ~ I_ok (MkChord locked_mixed_ls) (MkOutOfScope EggCircularArc)
             (IHit p ti tj)).
Proof.
  split; [exact mixed_host_circgamma_qex|].
  split; [exact mixed_host_not_first_cook|].
  split; [exact mixed_first_cook_stays_chord_chord|].
  split; [exact mixed_not_first_cook|].
  split; [exact locked_mixed_ls_cs_host_decline|].
  apply mixed_host_ls_cs_hit_false.
Qed.

Lemma mixed_reuse_no_new_kernel :
  CircEgg = CircularArc
  /\ I_ok_mixed (MixLsCs locked_mixed_ls locked_mixed_cs)
       (ls_cs_joint_hit locked_mixed_ls locked_mixed_cs)
  /\ I_ok_mixed (MixCsLs locked_mixed_cs locked_mixed_ls)
       (cs_ls_joint_hit locked_mixed_cs locked_mixed_ls).
Proof.
  split; [reflexivity|].
  split; [exact locked_mixed_ls_cs_I_ok_mixed|].
  exact locked_mixed_cs_ls_I_ok_mixed.
Qed.

(* -------------------------------------------------------------------------- *)
(* Letter-local parks. Interior mixed cook / H⊥ / SQL/MM stay parked.         *)
(* Required-type CC / CP land only in B.2 / B.3 after this Hit is reused.     *)
(* -------------------------------------------------------------------------- *)

Inductive MixedLetterStatus : Type :=
| MixedLetterLanded
| MixedLetterParked.

Definition mixed_letter_status : MixedLetterStatus := MixedLetterLanded.

Lemma mixed_letter_is_landed :
  mixed_letter_status = MixedLetterLanded.
Proof.
  reflexivity.
Qed.

Inductive MixedInteriorCookStatus : Type :=
| MixedInteriorCookLanded
| MixedInteriorCookParked.

Definition mixed_interior_cook_status : MixedInteriorCookStatus :=
  MixedInteriorCookParked.

Lemma mixed_interior_cook_is_parked :
  mixed_interior_cook_status = MixedInteriorCookParked.
Proof.
  reflexivity.
Qed.

Inductive MixedHperpStatus : Type :=
| MixedHperpDischarged
| MixedHperpParked.

Definition mixed_hperp_status : MixedHperpStatus := MixedHperpParked.

Lemma mixed_hperp_is_parked :
  mixed_hperp_status = MixedHperpParked.
Proof.
  reflexivity.
Qed.

Inductive MixedSqlMmStatus : Type :=
| MixedSqlMmDone
| MixedSqlMmNotDone.

Definition mixed_sql_mm_status : MixedSqlMmStatus := MixedSqlMmNotDone.

Lemma mixed_sql_mm_is_not_done :
  mixed_sql_mm_status = MixedSqlMmNotDone.
Proof.
  reflexivity.
Qed.

Inductive MixedCircGammaRemintStatus : Type :=
| MixedCircGammaReminted
| MixedCircGammaRemintParked.

Definition mixed_circgamma_remint_status : MixedCircGammaRemintStatus :=
  MixedCircGammaRemintParked.

Lemma mixed_circgamma_remint_is_parked :
  mixed_circgamma_remint_status = MixedCircGammaRemintParked.
Proof.
  reflexivity.
Qed.

Lemma mixed_not_bag_noder :
  cook_loop_status = LoopObligation
  /\ cook_loop_status <> LoopDischarged.
Proof.
  split; [exact cook_loop_is_obligation|].
  exact cook_loop_not_discharged.
Qed.

Lemma mixed_rest_parked :
  mixed_letter_status = MixedLetterLanded
  /\ mixed_interior_cook_status = MixedInteriorCookParked
  /\ mixed_hperp_status = MixedHperpParked
  /\ mixed_circgamma_remint_status = MixedCircGammaRemintParked
  /\ mixed_sql_mm_status = MixedSqlMmNotDone
  /\ cook_loop_status = LoopObligation.
Proof.
  repeat split; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_b_mixed_hit_qed_or_qex","title":"Phase B mixed forall LS-CS and CS-LS contiguous joints inhabit I_ok_mixed Hit at (end, 1, 0) (QED) or a locked mixed pair declines I_ok_mixed (QEX); discharged QED; sidecar chord_eval plus arc_gamma; host I_ok mixed stays Decline; not a constructed interior mixed Hit","file":"theories/SidecarCircMixed.v","witness":"0007-B-mixed-ls-cs-joints","board":"ADR-0007"} *)

Theorem ticket_0007_b_mixed_hit_qed_or_qex :
  ((forall c a, ls_cs_joint c a ->
      I_ok_mixed (MixLsCs c a) (ls_cs_joint_hit c a))
   /\ (forall a c, cs_ls_joint a c ->
         I_ok_mixed (MixCsLs a c) (cs_ls_joint_hit a c))
   /\ I_ok_mixed (MixLsCs locked_mixed_ls locked_mixed_cs)
        (ls_cs_joint_hit locked_mixed_ls locked_mixed_cs)
   /\ I_ok_mixed (MixCsLs locked_mixed_cs locked_mixed_ls)
        (cs_ls_joint_hit locked_mixed_cs locked_mixed_ls)
   /\ I_ok (MkChord locked_mixed_ls) (MkOutOfScope EggCircularArc) IDecline
   /\ ~ I_ok (MkChord locked_mixed_ls) (MkOutOfScope EggCircularArc)
          (IHit locked_mixed_ls_cs_pt 1 0))
  \/
  I_ok_mixed (MixLsCs locked_mixed_ls locked_mixed_cs) IDecline.
Proof.
  left.
  split; [exact ls_cs_joint_I_ok_mixed|].
  split; [exact cs_ls_joint_I_ok_mixed|].
  split; [exact locked_mixed_ls_cs_I_ok_mixed|].
  split; [exact locked_mixed_cs_ls_I_ok_mixed|].
  split; [exact locked_mixed_ls_cs_host_decline|].
  apply mixed_host_ls_cs_hit_false.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_b_mixed_license_qed_or_qex","title":"Phase B mixed I_ok_mixed Hit licenses already-hen concat incidence and joint params are not interior (QED) or a locked pair is not a joint (QEX); discharged QED; no new split mint; not an interior arc-chord cook; not a kiss certificate","file":"theories/SidecarCircMixed.v","witness":"0007-B-mixed-ls-cs-joints","board":"ADR-0007"} *)

Theorem ticket_0007_b_mixed_license_qed_or_qex :
  (ce_p1 locked_mixed_ls = arc_start locked_mixed_cs
   /\ arc_end locked_mixed_cs = ce_p0 locked_mixed_ls
   /\ ~ interior_span_params 1 0
   /\ IHit locked_mixed_ls_cs_pt 1 0 <> IEmpty
   /\ CircEgg = CircularArc)
  \/
  ~ ls_cs_joint locked_mixed_ls locked_mixed_cs.
Proof.
  left.
  destruct locked_mixed_ls_cs_joint as [_ Hls].
  destruct locked_mixed_cs_ls_joint as [_ Hcs].
  split; [exact Hls|].
  split; [exact Hcs|].
  split; [exact CircularCookCsConcat.joint_params_not_interior|].
  split; [apply IHit_neq_IEmpty|].
  reflexivity.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_b_mixed_host_qed_or_qex","title":"Phase B mixed discharges CircGamma and expands first cook to circular times chord interiors (QED) or CircGamma stays QEX and first cook stays chord-chord (QEX); discharged QEX; host mixed I_ok is Decline; I_ok_mixed Hit is not host I_ok; interior mixed cook is not invented","file":"theories/SidecarCircMixed.v","witness":"0007-B-mixed-ls-cs-joints","board":"ADR-0007"} *)

Theorem ticket_0007_b_mixed_host_qed_or_qex :
  (circular_gamma_status = CircGammaDischarged
   /\ first_cook_scope EggChord EggCircularArc
   /\ exists p ti tj,
        I_ok (MkChord locked_mixed_ls) (MkOutOfScope EggCircularArc)
             (IHit p ti tj))
  \/
  (circular_gamma_status = CircGammaQEX
   /\ ~ first_cook_scope EggCircularArc EggCircularArc
   /\ first_cook_scope EggChord EggChord
   /\ ~ first_cook_scope EggChord EggCircularArc
   /\ I_ok (MkChord locked_mixed_ls) (MkOutOfScope EggCircularArc) IDecline
   /\ (forall p ti tj,
         ~ I_ok (MkChord locked_mixed_ls) (MkOutOfScope EggCircularArc)
              (IHit p ti tj))
   /\ I_ok_mixed (MixLsCs locked_mixed_ls locked_mixed_cs)
        (ls_cs_joint_hit locked_mixed_ls locked_mixed_cs)
   /\ ~ I_ok (MkChord locked_mixed_ls) (MkOutOfScope EggCircularArc)
        (ls_cs_joint_hit locked_mixed_ls locked_mixed_cs)
   /\ mixed_interior_cook_status = MixedInteriorCookParked).
Proof.
  right.
  destruct mixed_host_stays_qex as [Hq [Hn [Hc [Hm [Hd Hf]]]]].
  destruct locked_mixed_ls_cs_hit_not_host_I_ok as [Hhit Hhost].
  split; [exact Hq|].
  split; [exact Hn|].
  split; [exact Hc|].
  split; [exact Hm|].
  split; [exact Hd|].
  split; [exact Hf|].
  split; [exact Hhit|].
  split; [exact Hhost|].
  exact mixed_interior_cook_is_parked.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_b_mixed_park_qed_or_qex","title":"Phase B mixed discharges interior mixed cook, Hperp, CircGamma remint, bag noder, and SQL/MM (QED) or names them parked / not-done (QEX); discharged QEX; mixed letter landed; I_ok_mixed Hit is real; letter landed != host I_ok Hit / SQL/MM done","file":"theories/SidecarCircMixed.v","witness":"0007-B-mixed-ls-cs-joints","board":"ADR-0007"} *)

Theorem ticket_0007_b_mixed_park_qed_or_qex :
  (mixed_interior_cook_status = MixedInteriorCookLanded
   /\ mixed_hperp_status = MixedHperpDischarged
   /\ mixed_circgamma_remint_status = MixedCircGammaReminted
   /\ mixed_sql_mm_status = MixedSqlMmDone
   /\ cook_loop_status = LoopDischarged)
  \/
  (mixed_letter_status = MixedLetterLanded
   /\ mixed_interior_cook_status = MixedInteriorCookParked
   /\ mixed_hperp_status = MixedHperpParked
   /\ mixed_circgamma_remint_status = MixedCircGammaRemintParked
   /\ mixed_sql_mm_status = MixedSqlMmNotDone
   /\ cook_loop_status = LoopObligation).
Proof.
  right.
  exact mixed_rest_parked.
Qed.

Print Assumptions mixed_host_circgamma_qex.
Print Assumptions ls_cs_joint_I_ok_mixed.
Print Assumptions cs_ls_joint_I_ok_mixed.
Print Assumptions I_ok_mixed_hit_licenses_joint_hen.
Print Assumptions I_ok_mixed_hit_not_host_I_ok.
Print Assumptions locked_mixed_ls_cs_I_ok_mixed.
Print Assumptions locked_mixed_cs_ls_I_ok_mixed.
Print Assumptions locked_mixed_ls_cs_host_decline.
Print Assumptions mixed_reuse_no_new_kernel.
Print Assumptions mixed_not_bag_noder.
Print Assumptions mixed_letter_is_landed.
Print Assumptions mixed_interior_cook_is_parked.
Print Assumptions mixed_sql_mm_is_not_done.
Print Assumptions ticket_0007_b_mixed_hit_qed_or_qex.
Print Assumptions ticket_0007_b_mixed_license_qed_or_qex.
Print Assumptions ticket_0007_b_mixed_host_qed_or_qex.
Print Assumptions ticket_0007_b_mixed_park_qed_or_qex.
