(* ============================================================================
   NetTopologySuite.Proofs.SidecarCircInteriorHit
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: ι interior Hit discharge
   (claimId 0007-iota-interior-discharge).

   Parks ι (#707 @ 1dbc2c2, SidecarCircInterior.v) already landed as
   QEX: I_ok_mixed Hit is gated by mixed_joint_params; the interior-
   params arm does not inhabit (interior_mixed_hit_arm_missing).
   That gate is the μ story. This letter does not remint it.

   Constructive discharge lives on a distinct predicate / arm:
   I_ok_interior. Hit is I_ok_mixed_interior_arm (already named in
   SidecarCircInterior) — valid_arc ∧ on_chord ∧ on_arc_gamma ∧
   interior_span_params. Joint Hit stays I_ok_mixed. Do not drop
   mixed_joint_params. Do not widen I_ok_mixed.

   Locked fixture packages Campaign II span material, not a remint:
     CS  : span_arc_A = CIRCULARSTRING(5 0, 3 4, 0 5)
     LS  : horizontal chord through locked p+
     Hit : (p+, tᵢ=1/2, tⱼ=arc_t span_arc_A p+)
   on_arc_gamma at p+ is already Qed (CircularCookSpan.v :
   span_p_plus_on_gamma_A). Chord incidence is host chord_eval.

   QED: locked MixLsCs / MixCsLs inhabit I_ok_interior Hit at
   interior_span_params; that Hit is the named interior arm; it
   does not inhabit I_ok_mixed; μ joint still inhabits I_ok_mixed
   and is not interior; joint gate stands.
   QEX: host CircGamma stays QEX; first cook stays chord–chord;
   host mixed I_ok is Decline; I_ok_interior Hit ≠ host I_ok;
   I_ok_mixed still has no interior-params arm; host interior
   cook / H⊥ / bag noder / SQL/MM cathedral stay parked.

   Honesty fences:
     Host-Decline / CircGamma-QEX at the top of this module.
     I_circles_z ≠ I_circles_gamma ≠ sidecar cook ≠ span filter ≠
     span split ≠ I_ok_circ ≠ I_ok_mixed ≠ I_ok_interior ≠
     CS concat joint ≠ CC member joint ≠ μ joint ≠
     glossary I_gloss / host I_ok.
     I_ok_interior Hit ≠ I_ok_mixed Hit ≠ host I_ok.
     Sidecar ≠ host try_cook_hit / host I_ok.
     Package Parks ι; do not remint mixed_joint_params /
     InteriorMixedHitArm / CircGamma / host I_ok.
     Not first cook scope. Not a bag noder. Not ArcSplitAtNode.
     Not G¹ / H⊥. Not MultiCurve cathedral. Not MerkatorBV.
     Not a remint of CurveSegment / Exact* / Dart / Hobby /
     leftover_width / ArcSplitAtNode leftover-width / host circ_split /
     CircularStringValid / CompoundCurveKoc family / CircGamma /
     I_ok_mixed (do not drop mixed_joint_params).
     Do not fake atan2-free host γ. Do not expand first_cook_scope
     to circular×chord interiors. Do not start H⊥ / a CRV-TOUCH
     kiss procedure / CircGamma remint / full SQL/MM cathedral /
     bag-loop / Multi Landed theater / Phase B done-when /
     Campaign I–II remint / Shewchuk / Hobby / HotPixel / Jordan /
     522-n.
     No new kernel. Not SQL/MM done.

   WITNESS topic: overlay · claimId: 0007-iota-interior-discharge
   witness: 0007-iota-interior-discharge
   board: ADR-0007
   4-axiom (atan2 / Classical_Prop.classic via SidecarCircInterior /
     CircularCookSpan). Category C audit-exception: same atan2
     lineage as Parks ι; no extra axioms.
   Host lane stays 3-axiom. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance SheetHenCook CurveGeometry
  CircularCook CircularCookHit CircularCookSpan CircularCookOkCirc.
From NTS.Proofs Require CircularCookCsConcat.
From NTS.Proofs Require CircularCookCpConcat.
From NTS.Proofs Require SidecarCircMixed.
From NTS.Proofs Require SidecarCircInterior.
Local Open Scope R_scope.

(* WITNESS: campaign=B rung=iota-discharge claim=0007-iota-interior-discharge
   file=theories/SidecarCircInteriorHit.v
   kind=QED-or-QEX-interior-mixed-ls-cs-hit-sidecar
   gamma=arc-span-not-gamma-full
   reuse=I_ok_mixed_interior_arm,chord_eval,arc_gamma,span_p_plus_on_gamma_A
   not=new-kernel,CircGamma-Discharge,first-cook-noding,SQL-MM-done
   not=I_ok_mixed-remint,mixed_joint_params-drop,host-I_ok
   park=Hperp,host-interior-cook,CircGamma-remint,SQL-MM-cathedral
   land=Phase-B-iota-interior-Hit-sidecar *)

(* -------------------------------------------------------------------------- *)
(* Package Parks ι. Joint gate stands. Not a remint.                          *)
(* -------------------------------------------------------------------------- *)

Definition I_ok_mixed := SidecarCircInterior.I_ok_mixed.
Definition mixed_joint_params := SidecarCircInterior.mixed_joint_params.
Definition interior_span_params := SidecarCircInterior.interior_span_params.
Definition MixedEggs := SidecarCircInterior.MixedEggs.
Definition MixLsCs := SidecarCircInterior.MixLsCs.
Definition MixCsLs := SidecarCircInterior.MixCsLs.
Definition I_ok_mixed_interior_arm :=
  SidecarCircInterior.I_ok_mixed_interior_arm.

Lemma iota_joint_gate_stands :
  ~ SidecarCircInterior.interior_mixed_constructor_inhabits
      SidecarCircInterior.InteriorMixedHitArm
  /\ (forall m p ti tj,
        I_ok_mixed m (IHit p ti tj) ->
        mixed_joint_params ti tj /\ ~ interior_span_params ti tj).
Proof.
  split; [exact SidecarCircInterior.interior_mixed_hit_arm_missing|].
  exact SidecarCircInterior.I_ok_mixed_hit_is_joint_params.
Qed.

(* -------------------------------------------------------------------------- *)
(* Host-Decline / CircGamma-QEX fence (load-bearing, not decoration).         *)
(* -------------------------------------------------------------------------- *)

Lemma iota_hit_host_circgamma_qex :
  circular_gamma_status = CircGammaQEX.
Proof.
  exact circular_gamma_is_qex.
Qed.

Lemma iota_hit_first_cook_stays_chord_chord :
  first_cook_scope EggChord EggChord.
Proof.
  exact first_cook_scope_chord_chord.
Qed.

Lemma iota_hit_not_first_cook_mixed :
  ~ first_cook_scope EggChord EggCircularArc.
Proof.
  exact chord_circular_not_first_cook_scope.
Qed.

Lemma iota_hit_host_ls_cs_decline :
  forall c,
    I_ok (MkChord c) (MkOutOfScope EggCircularArc) IDecline.
Proof.
  exact SidecarCircInterior.iota_host_ls_cs_decline.
Qed.

Lemma iota_hit_host_ls_cs_hit_false :
  forall c p ti tj,
    ~ I_ok (MkChord c) (MkOutOfScope EggCircularArc) (IHit p ti tj).
Proof.
  exact SidecarCircInterior.iota_host_ls_cs_hit_false.
Qed.

(* -------------------------------------------------------------------------- *)
(* Distinct interior arm. Packages I_ok_mixed_interior_arm; not I_ok_mixed.  *)
(* -------------------------------------------------------------------------- *)

Definition I_ok_interior (m : MixedEggs) (o : IResult) : Prop :=
  match o with
  | IHit p ti tj => I_ok_mixed_interior_arm m p ti tj
  | IEmpty => False
  | IDecline =>
      match m with
      | SidecarCircMixed.MixLsCs _ a => ~ valid_arc a
      | SidecarCircMixed.MixCsLs a _ => ~ valid_arc a
      end
  end.

Lemma I_ok_interior_hit_is_arm :
  forall m p ti tj,
    I_ok_interior m (IHit p ti tj) <->
    I_ok_mixed_interior_arm m p ti tj.
Proof.
  intros m p ti tj. unfold I_ok_interior. split; intro H; exact H.
Qed.

Lemma I_ok_interior_hit_not_I_ok_mixed :
  forall m p ti tj,
    I_ok_interior m (IHit p ti tj) ->
    ~ I_ok_mixed m (IHit p ti tj).
Proof.
  intros m p ti tj H.
  apply SidecarCircInterior.interior_arm_not_I_ok_mixed.
  apply I_ok_interior_hit_is_arm. exact H.
Qed.

Lemma I_ok_interior_empty_false :
  forall m, ~ I_ok_interior m IEmpty.
Proof.
  intros m H. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked proper-cross: horizontal chord through Campaign II p+.              *)
(* -------------------------------------------------------------------------- *)

Definition locked_interior_ls : ChordEgg :=
  mkChordEgg
    (mkPoint (px locked_p_plus - 1) (py locked_p_plus))
    (mkPoint (px locked_p_plus + 1) (py locked_p_plus)).

Definition locked_interior_cs : CircEgg := span_arc_A.

Definition locked_interior_ti : R := 1 / 2.

Definition locked_interior_tj : R := arc_t span_arc_A locked_p_plus.

Definition locked_interior_hit : IResult :=
  IHit locked_p_plus locked_interior_ti locked_interior_tj.

Definition locked_interior_rev_hit : IResult :=
  IHit locked_p_plus locked_interior_tj locked_interior_ti.

Lemma locked_interior_on_chord :
  on_chord locked_interior_ls locked_interior_ti locked_p_plus.
Proof.
  unfold on_chord, locked_interior_ls, locked_interior_ti, chord_eval.
  split; [lra|].
  apply (f_equal2 mkPoint); simpl; field.
Qed.

Lemma locked_p_plus_neq_span_A_start :
  locked_p_plus <> arc_start span_arc_A.
Proof.
  unfold span_arc_A. cbn [arc_start].
  intro H. apply (f_equal py) in H.
  pose proof span_p_plus_y_pos as Hy.
  cbn [py] in H.
  change (py (mkPoint 5 0)) with 0 in H.
  lra.
Qed.

Lemma locked_p_plus_neq_span_A_end :
  locked_p_plus <> arc_end span_arc_A.
Proof.
  unfold span_arc_A. cbn [arc_end].
  intro H. apply (f_equal px) in H.
  destruct span_p_plus_coords as [Hx _].
  cbn [px] in H.
  change (px (mkPoint 0 5)) with 0 in H.
  rewrite Hx in H.
  lra.
Qed.

Lemma locked_interior_tj_interior :
  0 < locked_interior_tj < 1.
Proof.
  unfold locked_interior_tj.
  destruct span_p_plus_on_gamma_A as [[Hlo Hhi] Heq].
  split.
  - destruct (Rle_lt_or_eq_dec _ _ Hlo) as [Hlt | Heq0].
    + exact Hlt.
    + rewrite <- Heq0 in Heq.
      rewrite (arc_gamma_start span_arc_A span_arc_A_valid) in Heq.
      exfalso. apply locked_p_plus_neq_span_A_start.
      symmetry. exact Heq.
  - destruct (Rle_lt_or_eq_dec _ _ Hhi) as [Hlt | Heq1].
    + exact Hlt.
    + rewrite Heq1 in Heq.
      rewrite (arc_gamma_end span_arc_A span_arc_A_valid) in Heq.
      exfalso. apply locked_p_plus_neq_span_A_end.
      symmetry. exact Heq.
Qed.

Lemma locked_interior_params :
  interior_span_params locked_interior_ti locked_interior_tj.
Proof.
  unfold interior_span_params, SidecarCircInterior.interior_span_params,
         SidecarCircMixed.interior_span_params,
         CircularCookCsConcat.interior_span_params,
         locked_interior_ti.
  split; [lra|].
  exact locked_interior_tj_interior.
Qed.

Lemma locked_interior_params_rev :
  interior_span_params locked_interior_tj locked_interior_ti.
Proof.
  unfold interior_span_params, SidecarCircInterior.interior_span_params,
         SidecarCircMixed.interior_span_params,
         CircularCookCsConcat.interior_span_params,
         locked_interior_ti.
  split; [exact locked_interior_tj_interior|].
  lra.
Qed.

(* WITNESS {"claimId":"0007-iota-interior-discharge","topic":"overlay","lemma":"locked_interior_I_ok_interior","title":"iota interior Hit discharge: locked MixLsCs horizontal chord through Campaign II p+ inhabits I_ok_interior at interior_span_params; distinct arm; not I_ok_mixed; not host I_ok","file":"theories/SidecarCircInteriorHit.v","witness":"0007-iota-interior-discharge","board":"ADR-0007"} *)

Theorem locked_interior_I_ok_interior :
  I_ok_interior (MixLsCs locked_interior_ls locked_interior_cs)
    locked_interior_hit.
Proof.
  unfold I_ok_interior, locked_interior_hit, locked_interior_cs,
         I_ok_mixed_interior_arm, SidecarCircInterior.I_ok_mixed_interior_arm.
  split; [exact span_arc_A_valid|].
  split; [exact locked_interior_on_chord|].
  split; [exact span_p_plus_on_gamma_A|].
  exact locked_interior_params.
Qed.

Theorem locked_interior_rev_I_ok_interior :
  I_ok_interior (MixCsLs locked_interior_cs locked_interior_ls)
    locked_interior_rev_hit.
Proof.
  unfold I_ok_interior, locked_interior_rev_hit, locked_interior_cs,
         I_ok_mixed_interior_arm, SidecarCircInterior.I_ok_mixed_interior_arm.
  split; [exact span_arc_A_valid|].
  split; [exact span_p_plus_on_gamma_A|].
  split; [exact locked_interior_on_chord|].
  exact locked_interior_params_rev.
Qed.

Lemma locked_interior_not_I_ok_mixed :
  I_ok_interior (MixLsCs locked_interior_ls locked_interior_cs)
    locked_interior_hit
  /\ ~ I_ok_mixed (MixLsCs locked_interior_ls locked_interior_cs)
        locked_interior_hit.
Proof.
  split; [exact locked_interior_I_ok_interior|].
  unfold locked_interior_hit.
  apply I_ok_interior_hit_not_I_ok_mixed.
  exact locked_interior_I_ok_interior.
Qed.

Lemma locked_interior_hit_not_host_I_ok :
  I_ok_interior (MixLsCs locked_interior_ls locked_interior_cs)
    locked_interior_hit
  /\ ~ I_ok (MkChord locked_interior_ls) (MkOutOfScope EggCircularArc)
        locked_interior_hit.
Proof.
  split; [exact locked_interior_I_ok_interior|].
  unfold locked_interior_hit.
  apply iota_hit_host_ls_cs_hit_false.
Qed.

Lemma locked_interior_host_decline :
  I_ok (MkChord locked_interior_ls) (MkOutOfScope EggCircularArc) IDecline.
Proof.
  apply iota_hit_host_ls_cs_decline.
Qed.

(* -------------------------------------------------------------------------- *)
(* μ joint still inhabits I_ok_mixed and is not this interior Hit.            *)
(* -------------------------------------------------------------------------- *)

Lemma iota_hit_mu_joint_not_interior :
  I_ok_mixed
    (MixLsCs SidecarCircInterior.locked_mixed_ls
             SidecarCircInterior.locked_mixed_cs)
    (SidecarCircMixed.ls_cs_joint_hit
       SidecarCircInterior.locked_mixed_ls
       SidecarCircInterior.locked_mixed_cs)
  /\ ~ interior_span_params 1 0.
Proof.
  exact SidecarCircInterior.iota_mu_joint_not_interior.
Qed.

(* -------------------------------------------------------------------------- *)
(* Letter-local parks. Sidecar interior Hit landed ≠ host interior cook.      *)
(* -------------------------------------------------------------------------- *)

Inductive IotaInteriorHitLetterStatus : Type :=
| IotaInteriorHitLetterLanded
| IotaInteriorHitLetterParked.

Definition iota_interior_hit_letter_status : IotaInteriorHitLetterStatus :=
  IotaInteriorHitLetterLanded.

Lemma iota_interior_hit_letter_is_landed :
  iota_interior_hit_letter_status = IotaInteriorHitLetterLanded.
Proof.
  reflexivity.
Qed.

Inductive IotaInteriorHitHostCookStatus : Type :=
| IotaInteriorHitHostCookLanded
| IotaInteriorHitHostCookParked.

Definition iota_interior_hit_host_cook_status
  : IotaInteriorHitHostCookStatus :=
  IotaInteriorHitHostCookParked.

Lemma iota_interior_hit_host_cook_is_parked :
  iota_interior_hit_host_cook_status = IotaInteriorHitHostCookParked.
Proof.
  reflexivity.
Qed.

Lemma iota_interior_hit_host_cook_stays_parked :
  SidecarCircInterior.iota_interior_cook_status
  = SidecarCircInterior.IotaInteriorCookParked.
Proof.
  exact SidecarCircInterior.iota_interior_cook_is_parked.
Qed.

Inductive IotaInteriorHitHperpStatus : Type :=
| IotaInteriorHitHperpDischarged
| IotaInteriorHitHperpParked.

Definition iota_interior_hit_hperp_status : IotaInteriorHitHperpStatus :=
  IotaInteriorHitHperpParked.

Lemma iota_interior_hit_hperp_is_parked :
  iota_interior_hit_hperp_status = IotaInteriorHitHperpParked.
Proof.
  reflexivity.
Qed.

Inductive IotaInteriorHitSqlMmStatus : Type :=
| IotaInteriorHitSqlMmDone
| IotaInteriorHitSqlMmNotDone.

Definition iota_interior_hit_sql_mm_status : IotaInteriorHitSqlMmStatus :=
  IotaInteriorHitSqlMmNotDone.

Lemma iota_interior_hit_sql_mm_is_not_done :
  iota_interior_hit_sql_mm_status = IotaInteriorHitSqlMmNotDone.
Proof.
  reflexivity.
Qed.

Inductive IotaInteriorHitCircGammaRemintStatus : Type :=
| IotaInteriorHitCircGammaReminted
| IotaInteriorHitCircGammaRemintParked.

Definition iota_interior_hit_circgamma_remint_status
  : IotaInteriorHitCircGammaRemintStatus :=
  IotaInteriorHitCircGammaRemintParked.

Lemma iota_interior_hit_circgamma_remint_is_parked :
  iota_interior_hit_circgamma_remint_status
  = IotaInteriorHitCircGammaRemintParked.
Proof.
  reflexivity.
Qed.

Lemma iota_interior_hit_phase_b_stays_open :
  CircularCookCpConcat.phase_b_status = CircularCookCpConcat.PhaseBOpen.
Proof.
  exact CircularCookCpConcat.phase_b_is_open.
Qed.

Lemma iota_interior_hit_not_bag_noder :
  cook_loop_status = LoopObligation
  /\ cook_loop_status <> LoopDischarged.
Proof.
  split; [exact cook_loop_is_obligation|].
  exact cook_loop_not_discharged.
Qed.

Lemma iota_interior_hit_rest_parked :
  iota_interior_hit_letter_status = IotaInteriorHitLetterLanded
  /\ iota_interior_hit_host_cook_status = IotaInteriorHitHostCookParked
  /\ iota_interior_hit_hperp_status = IotaInteriorHitHperpParked
  /\ iota_interior_hit_circgamma_remint_status
     = IotaInteriorHitCircGammaRemintParked
  /\ iota_interior_hit_sql_mm_status = IotaInteriorHitSqlMmNotDone
  /\ cook_loop_status = LoopObligation
  /\ CircularCookCpConcat.phase_b_status = CircularCookCpConcat.PhaseBOpen
  /\ SidecarCircInterior.iota_interior_cook_status
     = SidecarCircInterior.IotaInteriorCookParked.
Proof.
  repeat split; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops. Headline is QED on the distinct arm.         *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-iota-interior-discharge","topic":"overlay","lemma":"ticket_0007_iota_interior_hit_qed_or_qex","title":"iota interior Hit discharge locked MixLsCs and MixCsLs inhabit I_ok_interior at interior_span_params (QED) or the named interior arm stays uninhabited (QEX); discharged QED; packages I_ok_mixed_interior_arm; not a remint of I_ok_mixed; not CircGamma; not host I_ok","file":"theories/SidecarCircInteriorHit.v","witness":"0007-iota-interior-discharge","board":"ADR-0007"} *)

Theorem ticket_0007_iota_interior_hit_qed_or_qex :
  (I_ok_interior (MixLsCs locked_interior_ls locked_interior_cs)
     locked_interior_hit
   /\ I_ok_interior (MixCsLs locked_interior_cs locked_interior_ls)
        locked_interior_rev_hit
   /\ interior_span_params locked_interior_ti locked_interior_tj
   /\ I_ok_mixed_interior_arm
        (MixLsCs locked_interior_ls locked_interior_cs)
        locked_p_plus locked_interior_ti locked_interior_tj
   /\ I_ok (MkChord locked_interior_ls) (MkOutOfScope EggCircularArc)
        IDecline)
  \/
  (forall m p ti tj,
     ~ I_ok_interior m (IHit p ti tj)).
Proof.
  left.
  split; [exact locked_interior_I_ok_interior|].
  split; [exact locked_interior_rev_I_ok_interior|].
  split; [exact locked_interior_params|].
  split.
  - apply I_ok_interior_hit_is_arm.
    exact locked_interior_I_ok_interior.
  - exact locked_interior_host_decline.
Qed.

(* WITNESS {"claimId":"0007-iota-interior-discharge","topic":"overlay","lemma":"ticket_0007_iota_interior_not_mixed_qed_or_qex","title":"iota interior Hit discharge I_ok_interior Hit is not I_ok_mixed and the mixed_joint_params gate stands (QED) or I_ok_mixed accepts interior_span_params (QEX); discharged QED; Parks iota packaged; do not drop the joint gate","file":"theories/SidecarCircInteriorHit.v","witness":"0007-iota-interior-discharge","board":"ADR-0007"} *)

Theorem ticket_0007_iota_interior_not_mixed_qed_or_qex :
  (I_ok_interior (MixLsCs locked_interior_ls locked_interior_cs)
     locked_interior_hit
   /\ ~ I_ok_mixed (MixLsCs locked_interior_ls locked_interior_cs)
         locked_interior_hit
   /\ ~ SidecarCircInterior.interior_mixed_constructor_inhabits
         SidecarCircInterior.InteriorMixedHitArm
   /\ (forall m p ti tj,
         I_ok_mixed m (IHit p ti tj) ->
         mixed_joint_params ti tj /\ ~ interior_span_params ti tj)
   /\ I_ok_mixed
        (MixLsCs SidecarCircInterior.locked_mixed_ls
                 SidecarCircInterior.locked_mixed_cs)
        (SidecarCircMixed.ls_cs_joint_hit
           SidecarCircInterior.locked_mixed_ls
           SidecarCircInterior.locked_mixed_cs)
   /\ ~ interior_span_params 1 0)
  \/
  I_ok_mixed (MixLsCs locked_interior_ls locked_interior_cs)
    locked_interior_hit.
Proof.
  left.
  destruct locked_interior_not_I_ok_mixed as [Hhit Hn].
  destruct iota_joint_gate_stands as [Hmiss Hgate].
  destruct iota_hit_mu_joint_not_interior as [Hmu Hnmu].
  split; [exact Hhit|].
  split; [exact Hn|].
  split; [exact Hmiss|].
  split; [exact Hgate|].
  split; [exact Hmu|].
  exact Hnmu.
Qed.

(* WITNESS {"claimId":"0007-iota-interior-discharge","topic":"overlay","lemma":"ticket_0007_iota_interior_host_qed_or_qex","title":"iota interior Hit discharge expands first cook to circular times chord and inhabits host I_ok Hit (QED) or CircGamma stays QEX and first cook stays chord-chord (QEX); discharged QEX; host mixed I_ok is Decline; I_ok_interior Hit is not host I_ok; host interior cook stays parked","file":"theories/SidecarCircInteriorHit.v","witness":"0007-iota-interior-discharge","board":"ADR-0007"} *)

Theorem ticket_0007_iota_interior_host_qed_or_qex :
  (circular_gamma_status = CircGammaDischarged
   /\ first_cook_scope EggChord EggCircularArc
   /\ SidecarCircInterior.interior_mixed_constructor_inhabits
        SidecarCircInterior.InteriorMixedHitArm
   /\ exists p ti tj,
        I_ok (MkChord locked_interior_ls) (MkOutOfScope EggCircularArc)
             (IHit p ti tj))
  \/
  (circular_gamma_status = CircGammaQEX
   /\ ~ first_cook_scope EggCircularArc EggCircularArc
   /\ first_cook_scope EggChord EggChord
   /\ ~ first_cook_scope EggChord EggCircularArc
   /\ ~ SidecarCircInterior.interior_mixed_constructor_inhabits
         SidecarCircInterior.InteriorMixedHitArm
   /\ I_ok (MkChord locked_interior_ls) (MkOutOfScope EggCircularArc)
        IDecline
   /\ (forall p ti tj,
         ~ I_ok (MkChord locked_interior_ls) (MkOutOfScope EggCircularArc)
              (IHit p ti tj))
   /\ I_ok_interior (MixLsCs locked_interior_ls locked_interior_cs)
        locked_interior_hit
   /\ ~ I_ok (MkChord locked_interior_ls) (MkOutOfScope EggCircularArc)
        locked_interior_hit
   /\ iota_interior_hit_host_cook_status = IotaInteriorHitHostCookParked
   /\ SidecarCircInterior.iota_interior_cook_status
      = SidecarCircInterior.IotaInteriorCookParked).
Proof.
  right.
  destruct locked_interior_hit_not_host_I_ok as [Hhit Hhost].
  split; [exact iota_hit_host_circgamma_qex|].
  split; [exact circular_not_first_cook_scope|].
  split; [exact iota_hit_first_cook_stays_chord_chord|].
  split; [exact iota_hit_not_first_cook_mixed|].
  split; [exact SidecarCircInterior.interior_mixed_hit_arm_missing|].
  split; [exact locked_interior_host_decline|].
  split; [apply iota_hit_host_ls_cs_hit_false|].
  split; [exact Hhit|].
  split; [exact Hhost|].
  split; [exact iota_interior_hit_host_cook_is_parked|].
  exact iota_interior_hit_host_cook_stays_parked.
Qed.

(* WITNESS {"claimId":"0007-iota-interior-discharge","topic":"overlay","lemma":"ticket_0007_iota_interior_park_qed_or_qex","title":"iota interior Hit discharge discharges host interior cook, Hperp, CircGamma remint, bag noder, SQL/MM cathedral, and Phase B done-when (QED) or names them parked / not-done (QEX); discharged QEX; sidecar interior Hit letter landed; letter landed != host interior cook Landed / cathedral Landed / Phase B done-when","file":"theories/SidecarCircInteriorHit.v","witness":"0007-iota-interior-discharge","board":"ADR-0007"} *)

Theorem ticket_0007_iota_interior_park_qed_or_qex :
  (iota_interior_hit_host_cook_status = IotaInteriorHitHostCookLanded
   /\ iota_interior_hit_hperp_status = IotaInteriorHitHperpDischarged
   /\ iota_interior_hit_circgamma_remint_status
      = IotaInteriorHitCircGammaReminted
   /\ iota_interior_hit_sql_mm_status = IotaInteriorHitSqlMmDone
   /\ cook_loop_status = LoopDischarged
   /\ CircularCookCpConcat.phase_b_status
      = CircularCookCpConcat.PhaseBLanded
   /\ SidecarCircInterior.iota_interior_cook_status
      = SidecarCircInterior.IotaInteriorCookLanded)
  \/
  (iota_interior_hit_letter_status = IotaInteriorHitLetterLanded
   /\ iota_interior_hit_host_cook_status = IotaInteriorHitHostCookParked
   /\ iota_interior_hit_hperp_status = IotaInteriorHitHperpParked
   /\ iota_interior_hit_circgamma_remint_status
      = IotaInteriorHitCircGammaRemintParked
   /\ iota_interior_hit_sql_mm_status = IotaInteriorHitSqlMmNotDone
   /\ cook_loop_status = LoopObligation
   /\ CircularCookCpConcat.phase_b_status = CircularCookCpConcat.PhaseBOpen
   /\ SidecarCircInterior.iota_interior_cook_status
      = SidecarCircInterior.IotaInteriorCookParked).
Proof.
  right.
  exact iota_interior_hit_rest_parked.
Qed.

Print Assumptions iota_joint_gate_stands.
Print Assumptions I_ok_interior_hit_is_arm.
Print Assumptions I_ok_interior_hit_not_I_ok_mixed.
Print Assumptions locked_interior_on_chord.
Print Assumptions locked_interior_tj_interior.
Print Assumptions locked_interior_params.
Print Assumptions locked_interior_I_ok_interior.
Print Assumptions locked_interior_rev_I_ok_interior.
Print Assumptions locked_interior_not_I_ok_mixed.
Print Assumptions locked_interior_hit_not_host_I_ok.
Print Assumptions iota_hit_mu_joint_not_interior.
Print Assumptions iota_interior_hit_letter_is_landed.
Print Assumptions iota_interior_hit_host_cook_is_parked.
Print Assumptions ticket_0007_iota_interior_hit_qed_or_qex.
Print Assumptions ticket_0007_iota_interior_not_mixed_qed_or_qex.
Print Assumptions ticket_0007_iota_interior_host_qed_or_qex.
Print Assumptions ticket_0007_iota_interior_park_qed_or_qex.
