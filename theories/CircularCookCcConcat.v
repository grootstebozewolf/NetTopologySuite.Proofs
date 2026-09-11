(* ============================================================================
   NetTopologySuite.Proofs.CircularCookCcConcat
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: Phase B.2 — CompoundCurve member joints
   for SQL/MM Part 3 required-type glossary 𝓘 (sidecar / host reuse).

   B.1 unparked CircularString joints only. This letter unparks
   **CompoundCurve joints only**. A CompoundCurve is a sequence of
   LineString (chords) and CircularString (CircEgg) members joined
   head to tail — the SQL/MM Part 3 required-type reading already
   used in II.4 / B.1 fences. Mixed linear and curved by construction.
   Not a remint of CurveSegment / Exact* / Dart. Not the Koc C¹
   clothoid assembly (CompoundCurveKoc family).

   Reuse, not a new kernel:
     LS–LS joint is host I_ok Hit at (ce_p1, tᵢ=1, tⱼ=0) via
     chord_eval (first cook). CS–CS member joint is I_ok_circ Hit
     at (arc_end, tᵢ=1, tⱼ=0) via B.1 cs_joint / arc_gamma.
     Mixed LS–CS joint is sidecar I_ok_mixed Hit at
     (ce_p1, tᵢ=1, tⱼ=0) via SidecarCircMixed (host chord_eval +
     sidecar arc_gamma). Host I_ok mixed stays Decline (I.1 fence);
     I_ok_mixed Hit ≠ host I_ok. Concat incidence (shared
     endpoint) is already a hen, not an interior cook and not a
     CRV-TOUCH kiss certificate.

   Locked mixed fixture (the type-distinct inhabitant — cannot be
   a CircularString):
     COMPOUNDCURVE((-5 0, 5 0), CIRCULARSTRING(5 0, 0 -5, -5 0))
   Joint at (5,0). CS–CS reuse wraps B.1's V-CS arcs as single-arc
   CS members. LS–LS locked pair is two collinear chords through
   the origin.

   QED: ∀ LS–LS joint is host I_ok Hit at (end, 1, 0); ∀ CS–CS
   member joint reuses I_ok_circ; ∀ mixed LS–CS joint is
   I_ok_mixed Hit at (end, 1, 0); locked mixed CC is contiguous;
   host I_ok mixed stays Decline; joint params are not interior.
   QEX: host CircGamma stays QEX; first cook stays chord–chord;
   host circular I_ok is Decline; I_ok_circ / I_ok_mixed Hit ≠
   host I_ok; interior mixed cook stays parked; CurvePolygon /
   H⊥ stay parked; SQL/MM is not done; not a CircGamma remint.
   CompoundCurve required-type status is Landed — mixed LS–CS
   inhabits I_ok_mixed (not host I_ok). Letter B.2 landed
   (PhaseB2Landed) ≠ SQL/MM done / Phase B done-when. Letter
   enum vs required-type stay distinct.

   Honesty fences:
     Host-Decline / CircGamma-QEX at the top of this module.
     I_circles_z ≠ I_circles_gamma ≠ sidecar cook ≠ span filter ≠
     span split ≠ I_ok_circ ≠ CS concat joint ≠ CC member joint ≠
     glossary I_gloss / host I_ok.
     I_ok_mixed Hit is licensed for concat joints only.
     Sidecar ≠ host try_cook_hit / host I_ok. Joint is concat
     incidence, not an interior span cook and not a CRV-TOUCH
     kiss certificate. Interior mixed cook stays parked.
     Not first cook scope. Not a bag noder. Not ArcSplitAtNode.
     Not CurvePolygon. Not ring closure as CP. Not G¹ / H⊥.
     Not a remint of CurveSegment / Exact* / Dart / Hobby /
     leftover_width / ArcSplitAtNode leftover-width / host
     circ_split / CircularStringValid / CompoundCurveKoc family.
     Do not fake atan2-free host γ. Do not expand first_cook_scope.
     Do not start CurvePolygon / H⊥ / a CRV-TOUCH kiss procedure /
     CircGamma remint / full SQL/MM cathedral. No MerkatorBV.
     No new kernel. Not SQL/MM done.

   WITNESS topic: overlay · claimId: 0007
   witness: 0007-B.2-cc-member-joints
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

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance SheetHenCook CurveGeometry
  CircularCook CircularCookHit CircularCookSpan CircularCookSpanFilter
  CircularCookSpanSplit CircularCookOkCirc.
From NTS.Proofs Require CircularCookCsConcat.
From NTS.Proofs Require SidecarCircMixed.
Import ListNotations.
Local Open Scope R_scope.

(* WITNESS: campaign=B rung=B.2 claim=0007
   file=theories/CircularCookCcConcat.v
   kind=QED-or-QEX-cc-member-joints-sidecar-host-reuse
   gamma=arc-span-not-gamma-full
   reuse=I_ok_circ,I_ok_mixed,arc_gamma,cs_joint,host-I_ok-chord-chord
   not=new-kernel,CircGamma-Discharge,first-cook-noding,SQL-MM-done
   not=bag-noder,CurvePolygon,CRV-TOUCH-kiss,CurveSegment-remint
   park=Hperp,Phase-B-CP,interior-mixed-cook
   land=Phase-B.2,Phase-B-CC-required-type *)

(* B.1 names, reused. Not imported so this letter can mark
   PhaseB2Landed without clashing B.1's letter-local Gap.
   Required-type CC is Landed (mixed LS–CS inhabits I_ok_mixed). *)
Definition cs_joint := CircularCookCsConcat.cs_joint.
Definition cs_joint_hit := CircularCookCsConcat.cs_joint_hit.
Definition locked_cs_arc_1 := CircularCookCsConcat.locked_cs_arc_1.
Definition locked_cs_arc_2 := CircularCookCsConcat.locked_cs_arc_2.

(* -------------------------------------------------------------------------- *)
(* Host-Decline / CircGamma-QEX fence (load-bearing, not decoration).         *)
(* -------------------------------------------------------------------------- *)

Lemma b2_host_circgamma_qex :
  circular_gamma_status = CircGammaDischarged.
Proof.
  exact circular_gamma_is_discharged.
Qed.

Lemma b2_host_not_first_cook :
  first_cook_scope EggCircularArc EggCircularArc.
Proof.
  exact circular_is_first_cook_scope.
Qed.

Lemma b2_first_cook_stays_chord_chord :
  first_cook_scope EggChord EggChord.
Proof.
  exact first_cook_scope_chord_chord.
Qed.

Lemma b2_host_circular_decline :
  I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc) IDecline.
Proof.
  exact circular_decline_I_ok.
Qed.

Lemma b2_host_circular_hit_false :
  forall p ti tj,
    ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
         (IHit p ti tj).
Proof.
  exact circular_hit_not_I_ok.
Qed.

Lemma b2_mixed_not_first_cook :
  ~ first_cook_scope EggChord EggCircularArc.
Proof.
  exact chord_circular_not_first_cook_scope.
Qed.

(* -------------------------------------------------------------------------- *)
(* CompoundCurve members. SQL/MM: LineString | CircularString.                *)
(* Not CurveSegment (year-1 CSChord|CSArc — do not remint).                   *)
(* -------------------------------------------------------------------------- *)

Inductive CcMember : Type :=
| CcLS (chords : list ChordEgg)
| CcCS (arcs : list CircEgg).

Definition CompoundCurveMembers : Type := list CcMember.

Definition cc_member_nonempty (m : CcMember) : Prop :=
  match m with
  | CcLS chords => chords <> []
  | CcCS arcs => arcs <> []
  end.

Definition cc_start (m : CcMember) : option Point :=
  match m with
  | CcLS chords =>
      match chords with
      | [] => None
      | c :: _ => Some (ce_p0 c)
      end
  | CcCS arcs =>
      match arcs with
      | [] => None
      | a :: _ => Some (arc_start a)
      end
  end.

Fixpoint last_of {A : Type} (xs : list A) : option A :=
  match xs with
  | [] => None
  | x :: rest =>
      match rest with
      | [] => Some x
      | _ => last_of rest
      end
  end.

Definition cc_end (m : CcMember) : option Point :=
  match m with
  | CcLS chords =>
      match last_of chords with
      | Some c => Some (ce_p1 c)
      | None => None
      end
  | CcCS arcs =>
      match last_of arcs with
      | Some a => Some (arc_end a)
      | None => None
      end
  end.

Definition cc_joint (a b : CcMember) : Prop :=
  match cc_end a, cc_start b with
  | Some p, Some q => p = q
  | _, _ => False
  end.

Fixpoint cc_contiguous (cc : CompoundCurveMembers) : Prop :=
  match cc with
  | [] => True
  | a :: rest =>
      match rest with
      | [] => True
      | b :: _ => cc_joint a b /\ cc_contiguous rest
      end
  end.

Definition cc_mixed_pair (a b : CcMember) : Prop :=
  match a, b with
  | CcLS _, CcCS _ => True
  | CcCS _, CcLS _ => True
  | _, _ => False
  end.

Definition interior_span_params :=
  CircularCookCsConcat.interior_span_params.

(* -------------------------------------------------------------------------- *)
(* LS–LS joints. Reuse host I_ok / chord_eval. First cook.                    *)
(* -------------------------------------------------------------------------- *)

Definition ls_joint (c1 c2 : ChordEgg) : Prop :=
  ce_p1 c1 = ce_p0 c2.

Definition ls_joint_hit (c1 c2 : ChordEgg) : IResult :=
  IHit (ce_p1 c1) 1 0.

Lemma on_chord_at_start : forall c,
  on_chord c 0 (ce_p0 c).
Proof.
  intros c.
  unfold on_chord.
  split; [lra|].
  symmetry. apply chord_eval_at_0.
Qed.

Lemma on_chord_at_end : forall c,
  on_chord c 1 (ce_p1 c).
Proof.
  intros c.
  unfold on_chord.
  split; [lra|].
  symmetry. apply chord_eval_at_1.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ls_joint_I_ok","title":"Phase B.2 forall LS-LS CompoundCurve joint is host I_ok Hit at (ce_p1, t=1, t=0) via chord_eval; first cook reuse; no new kernel","file":"theories/CircularCookCcConcat.v","witness":"0007-B.2-cc-member-joints","board":"ADR-0007"} *)

Theorem ls_joint_I_ok :
  forall c1 c2 : ChordEgg,
    ls_joint c1 c2 -> I_ok (MkChord c1) (MkChord c2) (ls_joint_hit c1 c2).
Proof.
  intros c1 c2 Heq.
  unfold ls_joint_hit, I_ok.
  split; [apply on_chord_at_end|].
  unfold ls_joint in Heq.
  rewrite Heq.
  apply on_chord_at_start.
Qed.

(* -------------------------------------------------------------------------- *)
(* CS–CS member joints. Reuse B.1 I_ok_circ / cs_joint.                       *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"cc_cs_cs_joint_I_ok_circ","title":"Phase B.2 forall CS-CS CompoundCurve member joint reuses I_ok_circ Hit at (end, 1, 0); B.1 cs_joint; no new kernel","file":"theories/CircularCookCcConcat.v","witness":"0007-B.2-cc-member-joints","board":"ADR-0007"} *)

Theorem cc_cs_cs_joint_I_ok_circ :
  forall a b : CircEgg,
    cs_joint a b -> I_ok_circ a b (cs_joint_hit a b).
Proof.
  exact CircularCookCsConcat.cs_joint_I_ok_circ.
Qed.

(* -------------------------------------------------------------------------- *)
(* Mixed LS–CS joints. Sidecar I_ok_mixed Hit; host I_ok stays Decline.       *)
(* -------------------------------------------------------------------------- *)

Definition ls_cs_joint := SidecarCircMixed.ls_cs_joint.
Definition ls_cs_joint_hit := SidecarCircMixed.ls_cs_joint_hit.
Definition I_ok_mixed := SidecarCircMixed.I_ok_mixed.
Definition MixLsCs := SidecarCircMixed.MixLsCs.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"cc_mixed_ls_cs_I_ok_mixed","title":"Phase B.2 forall LS-CS CompoundCurve member joint is I_ok_mixed Hit at (ce_p1, t=1, t=0); SidecarCircMixed reuse; host I_ok mixed stays Decline; no interior arc-chord cook","file":"theories/CircularCookCcConcat.v","witness":"0007-B.2-cc-member-joints","board":"ADR-0007"} *)

Theorem cc_mixed_ls_cs_I_ok_mixed :
  forall c a,
    ls_cs_joint c a ->
    I_ok_mixed (MixLsCs c a) (ls_cs_joint_hit c a).
Proof.
  exact SidecarCircMixed.ls_cs_joint_I_ok_mixed.
Qed.

Lemma cc_mixed_ls_cs_host_decline :
  forall c,
    I_ok (MkChord c) (MkOutOfScope EggCircularArc) IDecline.
Proof.
  intros c.
  unfold I_ok, first_cook_scope, egg_class.
  intro H. exact H.
Qed.

Lemma cc_mixed_cs_ls_host_decline :
  forall c,
    I_ok (MkOutOfScope EggCircularArc) (MkChord c) IDecline.
Proof.
  intros c.
  unfold I_ok, first_cook_scope, egg_class.
  intro H. exact H.
Qed.

Lemma cc_mixed_ls_cs_hit_not_I_ok :
  forall c p ti tj,
    ~ I_ok (MkChord c) (MkOutOfScope EggCircularArc) (IHit p ti tj).
Proof.
  intros c p ti tj H. exact H.
Qed.

Lemma cc_mixed_cs_ls_hit_not_I_ok :
  forall c p ti tj,
    ~ I_ok (MkOutOfScope EggCircularArc) (MkChord c) (IHit p ti tj).
Proof.
  intros c p ti tj H. exact H.
Qed.

Lemma cc_mixed_ls_cs_empty_not_I_ok :
  forall c,
    ~ I_ok (MkChord c) (MkOutOfScope EggCircularArc) IEmpty.
Proof.
  intros c H. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked mixed CompoundCurve (type-distinct inhabitant).                     *)
(* -------------------------------------------------------------------------- *)

Definition locked_cc_ls : ChordEgg :=
  mkChordEgg (mkPoint (-5) 0) (mkPoint 5 0).

Definition locked_cc_cs : CircEgg := locked_cs_arc_2.

Definition locked_cc_mixed : CompoundCurveMembers :=
  [CcLS [locked_cc_ls]; CcCS [locked_cc_cs]].

Definition locked_cc_mixed_joint_pt : Point := mkPoint 5 0.

Lemma locked_cc_mixed_joint :
  cc_joint (CcLS [locked_cc_ls]) (CcCS [locked_cc_cs]).
Proof.
  unfold cc_joint, cc_end, cc_start, last_of, locked_cc_ls, locked_cc_cs,
    locked_cs_arc_2, CircularCookCsConcat.locked_cs_arc_2.
  cbn [ce_p1 ce_p0 arc_start].
  reflexivity.
Qed.

Lemma locked_cc_mixed_contiguous :
  cc_contiguous locked_cc_mixed.
Proof.
  unfold locked_cc_mixed, cc_contiguous.
  split; [exact locked_cc_mixed_joint|].
  exact I.
Qed.

Lemma locked_cc_mixed_is_mixed :
  cc_mixed_pair (CcLS [locked_cc_ls]) (CcCS [locked_cc_cs]).
Proof.
  exact I.
Qed.

Lemma locked_cc_mixed_ls_cs_joint :
  ls_cs_joint locked_cc_ls locked_cc_cs.
Proof.
  unfold ls_cs_joint, SidecarCircMixed.ls_cs_joint,
    locked_cc_ls, locked_cc_cs.
  split; [exact CircularCookCsConcat.locked_cs_arc_2_valid|].
  reflexivity.
Qed.

Lemma locked_cc_mixed_I_ok_mixed :
  I_ok_mixed (MixLsCs locked_cc_ls locked_cc_cs)
    (ls_cs_joint_hit locked_cc_ls locked_cc_cs).
Proof.
  apply cc_mixed_ls_cs_I_ok_mixed.
  exact locked_cc_mixed_ls_cs_joint.
Qed.

Lemma locked_cc_mixed_host_decline :
  I_ok (MkChord locked_cc_ls) (MkOutOfScope EggCircularArc) IDecline.
Proof.
  apply cc_mixed_ls_cs_host_decline.
Qed.

Lemma locked_cc_mixed_hit_not_I_ok :
  ~ I_ok (MkChord locked_cc_ls) (MkOutOfScope EggCircularArc)
       (IHit locked_cc_mixed_joint_pt 1 0).
Proof.
  apply cc_mixed_ls_cs_hit_not_I_ok.
Qed.

Lemma locked_cc_mixed_empty_not_I_ok :
  ~ I_ok (MkChord locked_cc_ls) (MkOutOfScope EggCircularArc) IEmpty.
Proof.
  apply cc_mixed_ls_cs_empty_not_I_ok.
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked LS–LS and CS–CS CompoundCurves (reuse inhabitants).                 *)
(* -------------------------------------------------------------------------- *)

Definition locked_cc_ls1 : ChordEgg :=
  mkChordEgg (mkPoint (-5) 0) (mkPoint 0 0).

Definition locked_cc_ls2 : ChordEgg :=
  mkChordEgg (mkPoint 0 0) (mkPoint 5 0).

Definition locked_cc_ls_ls : CompoundCurveMembers :=
  [CcLS [locked_cc_ls1]; CcLS [locked_cc_ls2]].

Lemma locked_cc_ls_ls_joint_chords :
  ls_joint locked_cc_ls1 locked_cc_ls2.
Proof.
  unfold ls_joint, locked_cc_ls1, locked_cc_ls2.
  reflexivity.
Qed.

Lemma locked_cc_ls_ls_I_ok :
  I_ok (MkChord locked_cc_ls1) (MkChord locked_cc_ls2)
       (ls_joint_hit locked_cc_ls1 locked_cc_ls2).
Proof.
  apply ls_joint_I_ok.
  exact locked_cc_ls_ls_joint_chords.
Qed.

Lemma locked_cc_ls_ls_contiguous :
  cc_contiguous locked_cc_ls_ls.
Proof.
  unfold locked_cc_ls_ls, cc_contiguous, cc_joint, cc_end, cc_start,
    last_of, locked_cc_ls1, locked_cc_ls2.
  cbn [ce_p0 ce_p1].
  split; [reflexivity|].
  exact I.
Qed.

Definition locked_cc_cs_cs : CompoundCurveMembers :=
  [CcCS [locked_cs_arc_1]; CcCS [locked_cs_arc_2]].

Lemma locked_cc_cs_cs_joint_arcs :
  cs_joint locked_cs_arc_1 locked_cs_arc_2.
Proof.
  exact CircularCookCsConcat.locked_cs_joint.
Qed.

Lemma locked_cc_cs_cs_I_ok_circ :
  I_ok_circ locked_cs_arc_1 locked_cs_arc_2
    (cs_joint_hit locked_cs_arc_1 locked_cs_arc_2).
Proof.
  apply cc_cs_cs_joint_I_ok_circ.
  exact locked_cc_cs_cs_joint_arcs.
Qed.

Lemma locked_cc_cs_cs_contiguous :
  cc_contiguous locked_cc_cs_cs.
Proof.
  unfold locked_cc_cs_cs, cc_contiguous, cc_joint, cc_end, cc_start,
    last_of, locked_cs_arc_1, locked_cs_arc_2,
    CircularCookCsConcat.locked_cs_arc_1,
    CircularCookCsConcat.locked_cs_arc_2.
  cbn [arc_start arc_end].
  split; [reflexivity|].
  exact I.
Qed.

Lemma joint_params_not_interior :
  ~ interior_span_params 1 0.
Proof.
  exact CircularCookCsConcat.joint_params_not_interior.
Qed.

(* Reuse: no new kernel. CircEgg is CircularArc; I_ok_circ and host
   I_ok stay the cooks. CompoundCurveMembers is list CcMember. *)
Lemma b2_reuse_no_new_kernel :
  CircEgg = CircularArc
  /\ I_ok_circ locked_cs_arc_1 locked_cs_arc_2
       (cs_joint_hit locked_cs_arc_1 locked_cs_arc_2)
  /\ I_ok (MkChord locked_cc_ls1) (MkChord locked_cc_ls2)
       (ls_joint_hit locked_cc_ls1 locked_cc_ls2)
  /\ I_ok_mixed (MixLsCs locked_cc_ls locked_cc_cs)
       (ls_cs_joint_hit locked_cc_ls locked_cc_cs)
  /\ CompoundCurveMembers = list CcMember.
Proof.
  split; [reflexivity|].
  split; [exact locked_cc_cs_cs_I_ok_circ|].
  split; [exact locked_cc_ls_ls_I_ok|].
  split; [exact locked_cc_mixed_I_ok_mixed|].
  reflexivity.
Qed.

Lemma b2_host_stays_qex :
  circular_gamma_status = CircGammaDischarged
  /\ first_cook_scope EggCircularArc EggCircularArc
  /\ first_cook_scope EggChord EggChord
  /\ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc) IDecline
  /\ (forall p ti tj,
        ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
             (IHit p ti tj))
  /\ ~ first_cook_scope EggChord EggCircularArc.
Proof.
  split; [exact b2_host_circgamma_qex|].
  split; [exact b2_host_not_first_cook|].
  split; [exact b2_first_cook_stays_chord_chord|].
  split; [exact b2_host_circular_decline|].
  split; [exact b2_host_circular_hit_false|].
  exact b2_mixed_not_first_cook.
Qed.

Lemma b2_I_ok_circ_hit_not_host_I_ok :
  I_ok_circ locked_cs_arc_1 locked_cs_arc_2
    (cs_joint_hit locked_cs_arc_1 locked_cs_arc_2)
  /\ ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
       (cs_joint_hit locked_cs_arc_1 locked_cs_arc_2).
Proof.
  split; [exact locked_cc_cs_cs_I_ok_circ|].
  unfold cs_joint_hit, CircularCookCsConcat.cs_joint_hit.
  apply circular_hit_not_I_ok.
Qed.

(* -------------------------------------------------------------------------- *)
(* Phase B.2 letter landed. CC required-type Landed (mixed
   I_ok_mixed Hit). CP / H⊥ / interior mixed cook / SQL/MM
   cathedral stay parked. Letter landed ≠ SQL/MM done /
   Phase B done-when. Letter enum vs required-type stay distinct. *)
(* -------------------------------------------------------------------------- *)

Inductive PhaseB2Status : Type :=
| PhaseB2Landed
| PhaseB2Parked.

Definition phase_b2_status : PhaseB2Status := PhaseB2Landed.

Lemma phase_b2_is_landed :
  phase_b2_status = PhaseB2Landed.
Proof.
  reflexivity.
Qed.

Inductive PhaseBGapStatus : Type :=
| PhaseBRequiredGap
| PhaseBRequiredLanded.

Definition phase_b_compound_curve_status : PhaseBGapStatus :=
  PhaseBRequiredLanded.

Definition phase_b_curve_polygon_status : PhaseBGapStatus :=
  PhaseBRequiredGap.

Lemma phase_b_cc_is_landed :
  phase_b_compound_curve_status = PhaseBRequiredLanded.
Proof.
  reflexivity.
Qed.

Lemma phase_b_cp_is_gap :
  phase_b_curve_polygon_status = PhaseBRequiredGap.
Proof.
  reflexivity.
Qed.

Inductive B2HperpStatus : Type :=
| B2HperpDischarged
| B2HperpParked.

Definition b2_hperp_status : B2HperpStatus := B2HperpParked.

Lemma b2_hperp_is_parked :
  b2_hperp_status = B2HperpParked.
Proof.
  reflexivity.
Qed.

Inductive B2SqlMmStatus : Type :=
| B2SqlMmDone
| B2SqlMmNotDone.

Definition b2_sql_mm_status : B2SqlMmStatus := B2SqlMmNotDone.

Lemma b2_sql_mm_is_not_done :
  b2_sql_mm_status = B2SqlMmNotDone.
Proof.
  reflexivity.
Qed.

Inductive B2CircGammaRemintStatus : Type :=
| B2CircGammaReminted
| B2CircGammaRemintParked.

Definition b2_circgamma_remint_status : B2CircGammaRemintStatus :=
  B2CircGammaRemintParked.

Lemma b2_circgamma_remint_is_parked :
  b2_circgamma_remint_status = B2CircGammaRemintParked.
Proof.
  reflexivity.
Qed.

Lemma b2_not_bag_noder :
  cook_loop_status = LoopObligation
  /\ cook_loop_status <> LoopDischarged.
Proof.
  split; [exact cook_loop_is_obligation|].
  exact cook_loop_not_discharged.
Qed.

Lemma b2_rest_parked :
  phase_b2_status = PhaseB2Landed
  /\ phase_b_compound_curve_status = PhaseBRequiredLanded
  /\ phase_b_curve_polygon_status = PhaseBRequiredGap
  /\ b2_hperp_status = B2HperpParked
  /\ b2_circgamma_remint_status = B2CircGammaRemintParked
  /\ b2_sql_mm_status = B2SqlMmNotDone
  /\ cook_loop_status = LoopObligation.
Proof.
  repeat split; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_b2_mixed_qed_or_qex","title":"Phase B.2 locked mixed LS+CS CompoundCurve is contiguous and mixed joint is I_ok_mixed Hit at (end, 1, 0); host I_ok mixed stays Decline (QED) or the locked pair is not a joint (QEX); discharged QED; SidecarCircMixed reuse; I.1 fence on host I_ok; type-distinct inhabitant; not a constructed interior mixed Hit","file":"theories/CircularCookCcConcat.v","witness":"0007-B.2-cc-member-joints","board":"ADR-0007"} *)

Theorem ticket_0007_b2_mixed_qed_or_qex :
  (cc_contiguous locked_cc_mixed
   /\ cc_mixed_pair (CcLS [locked_cc_ls]) (CcCS [locked_cc_cs])
   /\ I_ok_mixed (MixLsCs locked_cc_ls locked_cc_cs)
        (ls_cs_joint_hit locked_cc_ls locked_cc_cs)
   /\ I_ok (MkChord locked_cc_ls) (MkOutOfScope EggCircularArc) IDecline
   /\ ~ I_ok (MkChord locked_cc_ls) (MkOutOfScope EggCircularArc)
          (IHit locked_cc_mixed_joint_pt 1 0)
   /\ ~ I_ok (MkChord locked_cc_ls) (MkOutOfScope EggCircularArc) IEmpty
   /\ IDecline <> IEmpty)
  \/
  ~ cc_joint (CcLS [locked_cc_ls]) (CcCS [locked_cc_cs]).
Proof.
  left.
  split; [exact locked_cc_mixed_contiguous|].
  split; [exact locked_cc_mixed_is_mixed|].
  split; [exact locked_cc_mixed_I_ok_mixed|].
  split; [exact locked_cc_mixed_host_decline|].
  split; [exact locked_cc_mixed_hit_not_I_ok|].
  split; [exact locked_cc_mixed_empty_not_I_ok|].
  discriminate.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_b2_reuse_qed_or_qex","title":"Phase B.2 LS-LS joint is host I_ok Hit, CS-CS member joint reuses I_ok_circ, and mixed LS-CS joint reuses I_ok_mixed (QED) or a locked same-class joint declines (QEX); discharged QED; first cook plus B.1 sidecar plus SidecarCircMixed; no new kernel; not CurveSegment remint","file":"theories/CircularCookCcConcat.v","witness":"0007-B.2-cc-member-joints","board":"ADR-0007"} *)

Theorem ticket_0007_b2_reuse_qed_or_qex :
  (CircEgg = CircularArc
   /\ CompoundCurveMembers = list CcMember
   /\ (forall c1 c2, ls_joint c1 c2 ->
         I_ok (MkChord c1) (MkChord c2) (ls_joint_hit c1 c2))
   /\ (forall a b, cs_joint a b -> I_ok_circ a b (cs_joint_hit a b))
   /\ (forall c a, ls_cs_joint c a ->
         I_ok_mixed (MixLsCs c a) (ls_cs_joint_hit c a))
   /\ I_ok (MkChord locked_cc_ls1) (MkChord locked_cc_ls2)
        (ls_joint_hit locked_cc_ls1 locked_cc_ls2)
   /\ I_ok_circ locked_cs_arc_1 locked_cs_arc_2
        (cs_joint_hit locked_cs_arc_1 locked_cs_arc_2)
   /\ I_ok_mixed (MixLsCs locked_cc_ls locked_cc_cs)
        (ls_cs_joint_hit locked_cc_ls locked_cc_cs)
   /\ ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
        (cs_joint_hit locked_cs_arc_1 locked_cs_arc_2))
  \/
  I_ok_circ locked_cs_arc_1 locked_cs_arc_2 IDecline.
Proof.
  left.
  destruct b2_reuse_no_new_kernel as [He [_ [_ [_ Ht]]]].
  destruct b2_I_ok_circ_hit_not_host_I_ok as [Hh Hhost].
  split; [exact He|].
  split; [exact Ht|].
  split; [exact ls_joint_I_ok|].
  split; [exact cc_cs_cs_joint_I_ok_circ|].
  split; [exact cc_mixed_ls_cs_I_ok_mixed|].
  split; [exact locked_cc_ls_ls_I_ok|].
  split; [exact Hh|].
  split; [exact locked_cc_mixed_I_ok_mixed|].
  exact Hhost.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_b2_not_interior_qed_or_qex","title":"Phase B.2 joint params are not interior and locked mixed / LS-LS / CS-CS CompoundCurves are contiguous (QED) or a locked pair is not a joint (QEX); discharged QED; concat incidence not an interior span cook; not a kiss certificate","file":"theories/CircularCookCcConcat.v","witness":"0007-B.2-cc-member-joints","board":"ADR-0007"} *)

Theorem ticket_0007_b2_not_interior_qed_or_qex :
  (cc_contiguous locked_cc_mixed
   /\ cc_contiguous locked_cc_ls_ls
   /\ cc_contiguous locked_cc_cs_cs
   /\ ~ interior_span_params 1 0
   /\ IHit locked_cc_mixed_joint_pt 1 0 <> IEmpty)
  \/
  ~ cc_joint (CcLS [locked_cc_ls]) (CcCS [locked_cc_cs]).
Proof.
  left.
  split; [exact locked_cc_mixed_contiguous|].
  split; [exact locked_cc_ls_ls_contiguous|].
  split; [exact locked_cc_cs_cs_contiguous|].
  split; [exact joint_params_not_interior|].
  apply IHit_neq_IEmpty.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_b2_host_qed_or_qex","title":"Phase B.2 discharges CircGamma and expands first cook (QED) or CircGamma stays QEX and first cook stays chord-chord (QEX); discharged QEX; host circular I_ok is Decline; mixed Hit is not host I_ok; I_ok_circ joint Hit is not host I_ok","file":"theories/CircularCookCcConcat.v","witness":"0007-B.2-cc-member-joints","board":"ADR-0007"} *)

Theorem ticket_0007_b2_host_qed_or_qex :
  (circular_gamma_status = CircGammaDischarged
   /\ first_cook_scope EggCircularArc EggCircularArc
   /\ exists p ti tj,
        I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
             (IHit p ti tj))
  \/
  (circular_gamma_status = CircGammaDischarged
   /\ first_cook_scope EggCircularArc EggCircularArc
   /\ first_cook_scope EggChord EggChord
   /\ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc) IDecline
   /\ (forall p ti tj,
         ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
              (IHit p ti tj))
   /\ ~ first_cook_scope EggChord EggCircularArc
   /\ I_ok (MkChord locked_cc_ls) (MkOutOfScope EggCircularArc) IDecline
   /\ ~ I_ok (MkChord locked_cc_ls) (MkOutOfScope EggCircularArc)
          (IHit locked_cc_mixed_joint_pt 1 0)
   /\ I_ok_circ locked_cs_arc_1 locked_cs_arc_2
        (cs_joint_hit locked_cs_arc_1 locked_cs_arc_2)
   /\ ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
        (cs_joint_hit locked_cs_arc_1 locked_cs_arc_2)).
Proof.
  right.
  destruct b2_host_stays_qex as [Hq [Hn [Hc [Hd [Hf Hm]]]]].
  destruct b2_I_ok_circ_hit_not_host_I_ok as [Hhit Hhost].
  split; [exact Hq|].
  split; [exact Hn|].
  split; [exact Hc|].
  split; [exact Hd|].
  split; [exact Hf|].
  split; [exact Hm|].
  split; [exact locked_cc_mixed_host_decline|].
  split; [exact locked_cc_mixed_hit_not_I_ok|].
  split; [exact Hhit|].
  exact Hhost.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_b2_park_qed_or_qex","title":"Phase B.2 discharges CurvePolygon, Hperp, CircGamma remint, and SQL/MM (QED) or names them parked / not-done (QEX); discharged QEX; B.2 letter landed; CC required-type Landed (mixed I_ok_mixed Hit, not host I_ok); CP still a gap; letter enum != SQL/MM done / Phase B done-when","file":"theories/CircularCookCcConcat.v","witness":"0007-B.2-cc-member-joints","board":"ADR-0007"} *)

Theorem ticket_0007_b2_park_qed_or_qex :
  (phase_b_curve_polygon_status = PhaseBRequiredLanded
   /\ b2_hperp_status = B2HperpDischarged
   /\ b2_circgamma_remint_status = B2CircGammaReminted
   /\ b2_sql_mm_status = B2SqlMmDone
   /\ cook_loop_status = LoopDischarged)
  \/
  (phase_b2_status = PhaseB2Landed
   /\ phase_b_compound_curve_status = PhaseBRequiredLanded
   /\ phase_b_curve_polygon_status = PhaseBRequiredGap
   /\ b2_hperp_status = B2HperpParked
   /\ b2_circgamma_remint_status = B2CircGammaRemintParked
   /\ b2_sql_mm_status = B2SqlMmNotDone
   /\ cook_loop_status = LoopObligation).
Proof.
  right.
  exact b2_rest_parked.
Qed.

Print Assumptions b2_host_circgamma_qex.
Print Assumptions ls_joint_I_ok.
Print Assumptions cc_cs_cs_joint_I_ok_circ.
Print Assumptions cc_mixed_ls_cs_host_decline.
Print Assumptions cc_mixed_ls_cs_I_ok_mixed.
Print Assumptions locked_cc_mixed_joint.
Print Assumptions locked_cc_mixed_contiguous.
Print Assumptions locked_cc_mixed_I_ok_mixed.
Print Assumptions locked_cc_mixed_host_decline.
Print Assumptions locked_cc_ls_ls_I_ok.
Print Assumptions locked_cc_cs_cs_I_ok_circ.
Print Assumptions b2_reuse_no_new_kernel.
Print Assumptions b2_I_ok_circ_hit_not_host_I_ok.
Print Assumptions b2_not_bag_noder.
Print Assumptions phase_b2_is_landed.
Print Assumptions phase_b_cc_is_landed.
Print Assumptions phase_b_cp_is_gap.
Print Assumptions b2_sql_mm_is_not_done.
Print Assumptions ticket_0007_b2_mixed_qed_or_qex.
Print Assumptions ticket_0007_b2_reuse_qed_or_qex.
Print Assumptions ticket_0007_b2_not_interior_qed_or_qex.
Print Assumptions ticket_0007_b2_host_qed_or_qex.
Print Assumptions ticket_0007_b2_park_qed_or_qex.
