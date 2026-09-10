(* ============================================================================
   NetTopologySuite.Proofs.SidecarCircBags
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: Phase B MultiCurve / MultiSurface as
   bags of already-Qed members (claimId 0007-B-bags).

   B.1–B.3 plus SidecarCircMixed already inhabit CS concat joints
   (I_ok_circ), CC member joints (host I_ok / I_ok_circ /
   I_ok_mixed), and CP ring closure (same reuse). This letter
   unparks **Multi as bags only**. A MultiCurve is a bag of Curve
   members (CircularString / CompoundCurve). A MultiSurface is a
   bag of Surface members (CurvePolygon). Members need not be
   contiguous — that is the bag vs sequence distinction. Pairwise
   / membership joints reuse existing I_ok / I_ok_circ /
   I_ok_mixed. No new intersection kernel.

   Not a bag-level cook loop (cook_loop stays LoopObligation).
   Not a remint of CurveSegment / CurveGeometry.CurvePolygon.
   Not SQL/MM cathedral / Phase B done-when.

   Locked MultiCurve (type-distinct CS + CC, may share a point):
     MULTICURVE(
       CIRCULARSTRING(-5 0, 0 5, 5 0, 0 -5, -5 0),
       COMPOUNDCURVE((-5 0, 5 0), CIRCULARSTRING(5 0, 0 -5, -5 0)))
   Locked MultiCurve apart (bag ≠ concat):
     MULTICURVE(
       CIRCULARSTRING(-5 0, 0 5, 5 0, 0 -5, -5 0),
       CIRCULARSTRING(15 0, 20 5, 25 0, 20 -5, 15 0))
   Locked MultiSurface (two already-Qed CPs):
     MULTISURFACE(
       CURVEPOLYGON((CIRCULARSTRING(-5 0, 0 5, 5 0, 0 -5, -5 0))),
       CURVEPOLYGON((COMPOUNDCURVE((-5 0, 5 0),
         CIRCULARSTRING(5 0, 0 -5, -5 0)))))

   QED: MultiCurve / MultiSurface inhabit as bags of already-Qed
   members; membership joints reuse I_ok / I_ok_circ / I_ok_mixed;
   a two-member far MultiCurve is bag-ok and not contiguous;
   optional shared-endpoint pair reuses I_ok_mixed; no new kernel.
   QEX: host CircGamma stays QEX; first cook stays chord–chord;
   host mixed I_ok is Decline; interior circular×chord cook
   parked; bag-noder / H⊥ / CircGamma remint parked; SQL/MM is
   not done; Multi required-type stays Gap; Phase B stays Open;
   letter landed ≠ cathedral Landed / Phase B done-when.

   Honesty fences:
     Host-Decline / CircGamma-QEX at the top of this module.
     I_circles_z ≠ I_circles_gamma ≠ sidecar cook ≠ span filter ≠
     span split ≠ I_ok_circ ≠ I_ok_mixed ≠ CS concat joint ≠
     CC member joint ≠ CP closing ≠ Multi bag ≠ glossary I_gloss /
     host I_ok.
     Sidecar ≠ host try_cook_hit / host I_ok.
     Bag ≠ cook_loop noder. Bag ≠ required-type cathedral.
     Joints inside members are already-hen concat incidence, not
     an interior span cook and not a CRV-TOUCH kiss certificate.
     Not first cook scope. Not ArcSplitAtNode. Not G¹ / H⊥.
     Not a remint of CurveSegment / Exact* / Dart / Hobby /
     leftover_width / ArcSplitAtNode leftover-width / host circ_split /
     CircularStringValid / CompoundCurveKoc family / CircGamma /
     CurveGeometry.CurvePolygon.
     Do not fake atan2-free host γ. Do not expand first_cook_scope
     to circular×chord interiors. Do not start H⊥ / a CRV-TOUCH
     kiss procedure / CircGamma remint / full SQL/MM cathedral.
     No MerkatorBV. No 522-n. No mass-rename CircularCook*.
     No new kernel. Not SQL/MM done.

   WITNESS topic: overlay · claimId: 0007
   witness: 0007-B-bags
   board: ADR-0007
   4-axiom (atan2 / Classical_Prop.classic via CircularCookCpConcat /
     CircularCookCcConcat / CircularCookCsConcat / CircularCookOkCirc).
   Category C audit-exception: same atan2 lineage as B.1–B.3; no
   extra axioms.
   No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance SheetHenCook CurveGeometry
  CircularCook CircularCookHit CircularCookSpan CircularCookOkCirc.
From NTS.Proofs Require CircularCookCsConcat.
From NTS.Proofs Require CircularCookCcConcat.
From NTS.Proofs Require CircularCookCpConcat.
From NTS.Proofs Require SidecarCircMixed.
Import ListNotations.
Local Open Scope R_scope.

(* WITNESS: campaign=B rung=B-bags claim=0007
   file=theories/SidecarCircBags.v
   kind=QED-or-QEX-multi-as-bags-of-qed-members
   reuse=I_ok,I_ok_circ,I_ok_mixed,cs_joint,cc_joint,cp_closing
   not=new-kernel,CircGamma-Discharge,first-cook-noding,SQL-MM-done
   not=bag-noder,interior-arc-chord-cook,CRV-TOUCH-kiss,Phase-B-done-when
   park=Hperp,interior-mixed-cook,CircGamma-remint,SQL-MM-cathedral
   land=Phase-B-bags-letter *)

(* -------------------------------------------------------------------------- *)
(* Host-Decline / CircGamma-QEX fence (load-bearing, not decoration).         *)
(* -------------------------------------------------------------------------- *)

Lemma bags_host_circgamma_qex :
  circular_gamma_status = CircGammaQEX.
Proof.
  exact circular_gamma_is_qex.
Qed.

Lemma bags_host_not_first_cook :
  ~ first_cook_scope EggCircularArc EggCircularArc.
Proof.
  exact circular_not_first_cook_scope.
Qed.

Lemma bags_first_cook_stays_chord_chord :
  first_cook_scope EggChord EggChord.
Proof.
  exact first_cook_scope_chord_chord.
Qed.

Lemma bags_not_first_cook_mixed :
  ~ first_cook_scope EggChord EggCircularArc.
Proof.
  exact chord_circular_not_first_cook_scope.
Qed.

Lemma bags_host_circular_decline :
  I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc) IDecline.
Proof.
  exact circular_decline_I_ok.
Qed.

Lemma bags_host_circular_hit_false :
  forall p ti tj,
    ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
         (IHit p ti tj).
Proof.
  exact circular_hit_not_I_ok.
Qed.

Lemma bags_host_ls_cs_decline :
  forall c,
    I_ok (MkChord c) (MkOutOfScope EggCircularArc) IDecline.
Proof.
  exact SidecarCircMixed.mixed_host_ls_cs_decline.
Qed.

Lemma bags_host_ls_cs_hit_false :
  forall c p ti tj,
    ~ I_ok (MkChord c) (MkOutOfScope EggCircularArc) (IHit p ti tj).
Proof.
  exact SidecarCircMixed.mixed_host_ls_cs_hit_false.
Qed.

(* -------------------------------------------------------------------------- *)
(* MultiCurve / MultiSurface bags. Members are already-Qed CS / CC / CP.      *)
(* Bags do not require inter-member joints.                                   *)
(* -------------------------------------------------------------------------- *)

Definition CircularStringArcs := CircularCookCsConcat.CircularStringArcs.
Definition CompoundCurveMembers := CircularCookCcConcat.CompoundCurveMembers.
Definition CpPoly := CircularCookCpConcat.CpPoly.

Inductive McMember : Type :=
| McCS (arcs : CircularStringArcs)
| McCC (cc : CompoundCurveMembers).

Definition MultiCurveBag : Type := list McMember.

Inductive MsMember : Type :=
| MsCP (cp : CpPoly).

Definition MultiSurfaceBag : Type := list MsMember.

Definition mc_member_ok (m : McMember) : Prop :=
  match m with
  | McCS arcs =>
      arcs <> [] /\ CircularCookCsConcat.cs_contiguous arcs
  | McCC cc =>
      cc <> [] /\ CircularCookCcConcat.cc_contiguous cc
  end.

Definition ms_member_ok (m : MsMember) : Prop :=
  match m with
  | MsCP cp => CircularCookCpConcat.cp_poly_ok cp
  end.

Definition mc_bag_ok (mc : MultiCurveBag) : Prop :=
  Forall mc_member_ok mc.

Definition ms_bag_ok (ms : MultiSurfaceBag) : Prop :=
  Forall ms_member_ok ms.

Definition last_of {A : Type} := @CircularCookCcConcat.last_of A.

Definition mc_member_start (m : McMember) : option Point :=
  match m with
  | McCS arcs =>
      match arcs with
      | [] => None
      | a :: _ => Some (arc_start a)
      end
  | McCC cc =>
      match cc with
      | [] => None
      | a :: _ => CircularCookCcConcat.cc_start a
      end
  end.

Definition mc_member_end (m : McMember) : option Point :=
  match m with
  | McCS arcs =>
      match last_of arcs with
      | Some a => Some (arc_end a)
      | None => None
      end
  | McCC cc =>
      match last_of cc with
      | Some z => CircularCookCcConcat.cc_end z
      | None => None
      end
  end.

Definition mc_member_joint (a b : McMember) : Prop :=
  match mc_member_end a, mc_member_start b with
  | Some p, Some q => p = q
  | _, _ => False
  end.

Fixpoint mc_contiguous (mc : MultiCurveBag) : Prop :=
  match mc with
  | [] => True
  | a :: rest =>
      match rest with
      | [] => True
      | b :: _ => mc_member_joint a b /\ mc_contiguous rest
      end
  end.

(* -------------------------------------------------------------------------- *)
(* Locked already-Qed members (B.1 / B.2 / B.3 reuse).                        *)
(* -------------------------------------------------------------------------- *)

Definition locked_cs := CircularCookCsConcat.locked_cs.
Definition locked_cs_arc_1 := CircularCookCsConcat.locked_cs_arc_1.
Definition locked_cs_arc_2 := CircularCookCsConcat.locked_cs_arc_2.
Definition locked_cc_mixed := CircularCookCcConcat.locked_cc_mixed.
Definition locked_cc_ls := CircularCookCcConcat.locked_cc_ls.
Definition locked_cc_cs := CircularCookCcConcat.locked_cc_cs.
Definition locked_cp_cs := CircularCookCpConcat.locked_cp_cs.
Definition locked_cp_mixed := CircularCookCpConcat.locked_cp_mixed.

Definition locked_cs_far_1 : CircEgg :=
  mkCircularArc (mkPoint 15 0) (mkPoint 20 5) (mkPoint 25 0).

Definition locked_cs_far_2 : CircEgg :=
  mkCircularArc (mkPoint 25 0) (mkPoint 20 (-5)) (mkPoint 15 0).

Definition locked_cs_far : CircularStringArcs :=
  [locked_cs_far_1; locked_cs_far_2].

Lemma locked_cs_far_1_valid : valid_arc locked_cs_far_1.
Proof.
  unfold valid_arc, locked_cs_far_1.
  cbn [px py arc_start arc_mid arc_end].
  lra.
Qed.

Lemma locked_cs_far_2_valid : valid_arc locked_cs_far_2.
Proof.
  unfold valid_arc, locked_cs_far_2.
  cbn [px py arc_start arc_mid arc_end].
  lra.
Qed.

Lemma locked_cs_far_joint :
  CircularCookCsConcat.cs_joint locked_cs_far_1 locked_cs_far_2.
Proof.
  unfold CircularCookCsConcat.cs_joint, locked_cs_far_1, locked_cs_far_2.
  cbn [arc_start arc_end].
  split; [exact locked_cs_far_1_valid|].
  split; [exact locked_cs_far_2_valid|].
  reflexivity.
Qed.

Lemma locked_cs_far_contiguous :
  CircularCookCsConcat.cs_contiguous locked_cs_far.
Proof.
  unfold locked_cs_far, CircularCookCsConcat.cs_contiguous.
  split; [exact locked_cs_far_joint|].
  exact I.
Qed.

Lemma locked_cs_far_I_ok_circ :
  I_ok_circ locked_cs_far_1 locked_cs_far_2
    (CircularCookCsConcat.cs_joint_hit locked_cs_far_1 locked_cs_far_2).
Proof.
  apply CircularCookCsConcat.cs_joint_I_ok_circ.
  exact locked_cs_far_joint.
Qed.

Lemma locked_cs_member_ok :
  mc_member_ok (McCS locked_cs).
Proof.
  unfold mc_member_ok, locked_cs, CircularCookCsConcat.locked_cs.
  split; [discriminate|].
  exact CircularCookCsConcat.locked_cs_contiguous.
Qed.

Lemma locked_cc_member_ok :
  mc_member_ok (McCC locked_cc_mixed).
Proof.
  unfold mc_member_ok, locked_cc_mixed,
    CircularCookCcConcat.locked_cc_mixed.
  split; [discriminate|].
  exact CircularCookCcConcat.locked_cc_mixed_contiguous.
Qed.

Lemma locked_cs_far_member_ok :
  mc_member_ok (McCS locked_cs_far).
Proof.
  unfold mc_member_ok, locked_cs_far.
  split; [discriminate|].
  exact locked_cs_far_contiguous.
Qed.

Lemma locked_cp_cs_member_ok :
  ms_member_ok (MsCP locked_cp_cs).
Proof.
  exact CircularCookCpConcat.locked_cp_cs_ok.
Qed.

Lemma locked_cp_mixed_member_ok :
  ms_member_ok (MsCP locked_cp_mixed).
Proof.
  exact CircularCookCpConcat.locked_cp_mixed_ok.
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked bags.                                                               *)
(* -------------------------------------------------------------------------- *)

Definition locked_mc_typed : MultiCurveBag :=
  [McCS locked_cs; McCC locked_cc_mixed].

Definition locked_mc_apart : MultiCurveBag :=
  [McCS locked_cs; McCS locked_cs_far].

Definition locked_ms : MultiSurfaceBag :=
  [MsCP locked_cp_cs; MsCP locked_cp_mixed].

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"locked_mc_typed_ok","title":"Phase B bags locked type-distinct MultiCurve is a bag of already-Qed CS and CC members; no new kernel; bag does not invent a Multi cook","file":"theories/SidecarCircBags.v","witness":"0007-B-bags","board":"ADR-0007"} *)

Lemma locked_mc_typed_ok :
  mc_bag_ok locked_mc_typed.
Proof.
  unfold locked_mc_typed, mc_bag_ok.
  constructor; [exact locked_cs_member_ok|].
  constructor; [exact locked_cc_member_ok|].
  constructor.
Qed.

Lemma locked_mc_apart_ok :
  mc_bag_ok locked_mc_apart.
Proof.
  unfold locked_mc_apart, mc_bag_ok.
  constructor; [exact locked_cs_member_ok|].
  constructor; [exact locked_cs_far_member_ok|].
  constructor.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"locked_ms_ok","title":"Phase B bags locked MultiSurface is a bag of already-Qed CurvePolygon members; B.3 reuse; no new kernel","file":"theories/SidecarCircBags.v","witness":"0007-B-bags","board":"ADR-0007"} *)

Lemma locked_ms_ok :
  ms_bag_ok locked_ms.
Proof.
  unfold locked_ms, ms_bag_ok.
  constructor; [exact locked_cp_cs_member_ok|].
  constructor; [exact locked_cp_mixed_member_ok|].
  constructor.
Qed.

Lemma locked_cs_end_pt :
  mc_member_end (McCS locked_cs) = Some (mkPoint (-5) 0).
Proof.
  unfold mc_member_end, last_of, locked_cs,
    CircularCookCsConcat.locked_cs, locked_cs_arc_2,
    CircularCookCsConcat.locked_cs_arc_2.
  cbn [CircularCookCcConcat.last_of arc_end px py].
  reflexivity.
Qed.

Lemma locked_cs_far_start_pt :
  mc_member_start (McCS locked_cs_far) = Some (mkPoint 15 0).
Proof.
  unfold mc_member_start, locked_cs_far, locked_cs_far_1.
  cbn [arc_start px py].
  reflexivity.
Qed.

Lemma locked_mc_apart_not_contiguous :
  ~ mc_contiguous locked_mc_apart.
Proof.
  unfold locked_mc_apart, mc_contiguous, mc_member_joint.
  rewrite locked_cs_end_pt, locked_cs_far_start_pt.
  intros [H _].
  apply (f_equal px) in H.
  cbn in H.
  lra.
Qed.

(* Bags are not sequences: bag_ok does not require inter-member joints. *)
(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"bags_not_concat","title":"Phase B bags MultiCurve bag-ok does not require inter-member contiguity; locked far pair is bag-ok and not contiguous; bag != cook loop","file":"theories/SidecarCircBags.v","witness":"0007-B-bags","board":"ADR-0007"} *)

Lemma bags_not_concat :
  mc_bag_ok locked_mc_apart
  /\ ~ mc_contiguous locked_mc_apart.
Proof.
  split; [exact locked_mc_apart_ok|].
  exact locked_mc_apart_not_contiguous.
Qed.

(* -------------------------------------------------------------------------- *)
(* Membership joints reuse existing I_ok / I_ok_circ / I_ok_mixed.            *)
(* -------------------------------------------------------------------------- *)

Lemma bags_cs_member_joint_I_ok_circ :
  I_ok_circ locked_cs_arc_1 locked_cs_arc_2
    (CircularCookCsConcat.cs_joint_hit locked_cs_arc_1 locked_cs_arc_2).
Proof.
  exact CircularCookCsConcat.locked_cs_joint_I_ok_circ.
Qed.

Lemma bags_cc_member_joint_I_ok_mixed :
  SidecarCircMixed.I_ok_mixed
    (SidecarCircMixed.MixLsCs locked_cc_ls locked_cc_cs)
    (SidecarCircMixed.ls_cs_joint_hit locked_cc_ls locked_cc_cs).
Proof.
  exact CircularCookCcConcat.locked_cc_mixed_I_ok_mixed.
Qed.

Lemma bags_cc_ls_ls_joint_I_ok :
  I_ok (MkChord CircularCookCcConcat.locked_cc_ls1)
       (MkChord CircularCookCcConcat.locked_cc_ls2)
       (CircularCookCcConcat.ls_joint_hit
          CircularCookCcConcat.locked_cc_ls1
          CircularCookCcConcat.locked_cc_ls2).
Proof.
  exact CircularCookCcConcat.locked_cc_ls_ls_I_ok.
Qed.

Lemma bags_cp_cs_closing_I_ok_circ :
  I_ok_circ locked_cs_arc_2 locked_cs_arc_1
    (CircularCookCsConcat.cs_joint_hit locked_cs_arc_2 locked_cs_arc_1).
Proof.
  exact CircularCookCpConcat.locked_cp_cs_closing_I_ok_circ.
Qed.

Lemma bags_cp_mixed_closing_I_ok_mixed :
  SidecarCircMixed.I_ok_mixed
    (SidecarCircMixed.MixCsLs locked_cc_cs locked_cc_ls)
    (SidecarCircMixed.cs_ls_joint_hit locked_cc_cs locked_cc_ls).
Proof.
  exact CircularCookCpConcat.locked_cp_mixed_closing_I_ok_mixed.
Qed.

(* Optional pairwise: typed MultiCurve members share (-5,0). Reuse
   I_ok_mixed; do not mint I_ok_multi. Bags still do not require it. *)
Lemma bags_optional_pair_I_ok_mixed :
  SidecarCircMixed.cs_ls_joint locked_cs_arc_2 locked_cc_ls
  /\ SidecarCircMixed.I_ok_mixed
       (SidecarCircMixed.MixCsLs locked_cs_arc_2 locked_cc_ls)
       (SidecarCircMixed.cs_ls_joint_hit locked_cs_arc_2 locked_cc_ls).
Proof.
  split.
  - unfold SidecarCircMixed.cs_ls_joint, locked_cs_arc_2, locked_cc_ls.
    split; [exact CircularCookCsConcat.locked_cs_arc_2_valid|].
    reflexivity.
  - apply SidecarCircMixed.cs_ls_joint_I_ok_mixed.
    unfold SidecarCircMixed.cs_ls_joint, locked_cs_arc_2, locked_cc_ls.
    split; [exact CircularCookCsConcat.locked_cs_arc_2_valid|].
    reflexivity.
Qed.

Lemma bags_reuse_no_new_kernel :
  CircEgg = CircularArc
  /\ MultiCurveBag = list McMember
  /\ MultiSurfaceBag = list MsMember
  /\ I_ok_circ locked_cs_arc_1 locked_cs_arc_2
       (CircularCookCsConcat.cs_joint_hit locked_cs_arc_1 locked_cs_arc_2)
  /\ SidecarCircMixed.I_ok_mixed
       (SidecarCircMixed.MixLsCs locked_cc_ls locked_cc_cs)
       (SidecarCircMixed.ls_cs_joint_hit locked_cc_ls locked_cc_cs)
  /\ I_ok (MkChord CircularCookCcConcat.locked_cc_ls1)
       (MkChord CircularCookCcConcat.locked_cc_ls2)
       (CircularCookCcConcat.ls_joint_hit
          CircularCookCcConcat.locked_cc_ls1
          CircularCookCcConcat.locked_cc_ls2)
  /\ mc_bag_ok locked_mc_typed
  /\ ms_bag_ok locked_ms.
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact bags_cs_member_joint_I_ok_circ|].
  split; [exact bags_cc_member_joint_I_ok_mixed|].
  split; [exact bags_cc_ls_ls_joint_I_ok|].
  split; [exact locked_mc_typed_ok|].
  exact locked_ms_ok.
Qed.

Lemma bags_I_ok_mixed_hit_not_host_I_ok :
  SidecarCircMixed.I_ok_mixed
    (SidecarCircMixed.MixLsCs locked_cc_ls locked_cc_cs)
    (SidecarCircMixed.ls_cs_joint_hit locked_cc_ls locked_cc_cs)
  /\ ~ I_ok (MkChord locked_cc_ls) (MkOutOfScope EggCircularArc)
        (SidecarCircMixed.ls_cs_joint_hit locked_cc_ls locked_cc_cs).
Proof.
  split; [exact bags_cc_member_joint_I_ok_mixed|].
  unfold SidecarCircMixed.ls_cs_joint_hit.
  apply bags_host_ls_cs_hit_false.
Qed.

Lemma bags_host_stays_qex :
  circular_gamma_status = CircGammaQEX
  /\ ~ first_cook_scope EggCircularArc EggCircularArc
  /\ first_cook_scope EggChord EggChord
  /\ ~ first_cook_scope EggChord EggCircularArc
  /\ I_ok (MkChord locked_cc_ls) (MkOutOfScope EggCircularArc) IDecline
  /\ (forall p ti tj,
        ~ I_ok (MkChord locked_cc_ls) (MkOutOfScope EggCircularArc)
             (IHit p ti tj)).
Proof.
  split; [exact bags_host_circgamma_qex|].
  split; [exact bags_host_not_first_cook|].
  split; [exact bags_first_cook_stays_chord_chord|].
  split; [exact bags_not_first_cook_mixed|].
  split; [apply bags_host_ls_cs_decline|].
  apply bags_host_ls_cs_hit_false.
Qed.

(* -------------------------------------------------------------------------- *)
(* Letter-local parks. Bag noder / H⊥ / SQL/MM / cathedral stay parked.       *)
(* Letter landed ≠ Phase B done-when / Multi required-type Landed.            *)
(* -------------------------------------------------------------------------- *)

Inductive BagsLetterStatus : Type :=
| BagsLetterLanded
| BagsLetterParked.

Definition bags_letter_status : BagsLetterStatus := BagsLetterLanded.

Lemma bags_letter_is_landed :
  bags_letter_status = BagsLetterLanded.
Proof.
  reflexivity.
Qed.

Inductive MultiRequiredStatus : Type :=
| MultiRequiredGap
| MultiRequiredLanded.

Definition multi_required_status : MultiRequiredStatus := MultiRequiredGap.

Lemma multi_required_is_gap :
  multi_required_status = MultiRequiredGap.
Proof.
  reflexivity.
Qed.

Inductive BagsHperpStatus : Type :=
| BagsHperpDischarged
| BagsHperpParked.

Definition bags_hperp_status : BagsHperpStatus := BagsHperpParked.

Lemma bags_hperp_is_parked :
  bags_hperp_status = BagsHperpParked.
Proof.
  reflexivity.
Qed.

Inductive BagsSqlMmStatus : Type :=
| BagsSqlMmDone
| BagsSqlMmNotDone.

Definition bags_sql_mm_status : BagsSqlMmStatus := BagsSqlMmNotDone.

Lemma bags_sql_mm_is_not_done :
  bags_sql_mm_status = BagsSqlMmNotDone.
Proof.
  reflexivity.
Qed.

Inductive BagsCircGammaRemintStatus : Type :=
| BagsCircGammaReminted
| BagsCircGammaRemintParked.

Definition bags_circgamma_remint_status : BagsCircGammaRemintStatus :=
  BagsCircGammaRemintParked.

Lemma bags_circgamma_remint_is_parked :
  bags_circgamma_remint_status = BagsCircGammaRemintParked.
Proof.
  reflexivity.
Qed.

Inductive BagsInteriorCookStatus : Type :=
| BagsInteriorCookLanded
| BagsInteriorCookParked.

Definition bags_interior_cook_status : BagsInteriorCookStatus :=
  BagsInteriorCookParked.

Lemma bags_interior_cook_is_parked :
  bags_interior_cook_status = BagsInteriorCookParked.
Proof.
  reflexivity.
Qed.

Inductive BagsCathedralStatus : Type :=
| BagsCathedralLanded
| BagsCathedralNotLanded.

Definition bags_cathedral_status : BagsCathedralStatus :=
  BagsCathedralNotLanded.

Lemma bags_cathedral_is_not_landed :
  bags_cathedral_status = BagsCathedralNotLanded.
Proof.
  reflexivity.
Qed.

Lemma bags_phase_b_stays_open :
  CircularCookCpConcat.phase_b_status = CircularCookCpConcat.PhaseBOpen.
Proof.
  exact CircularCookCpConcat.phase_b_is_open.
Qed.

Lemma bags_not_bag_noder :
  cook_loop_status = LoopObligation
  /\ cook_loop_status <> LoopDischarged.
Proof.
  split; [exact cook_loop_is_obligation|].
  exact cook_loop_not_discharged.
Qed.

Lemma bags_rest_parked :
  bags_letter_status = BagsLetterLanded
  /\ multi_required_status = MultiRequiredGap
  /\ bags_interior_cook_status = BagsInteriorCookParked
  /\ bags_hperp_status = BagsHperpParked
  /\ bags_circgamma_remint_status = BagsCircGammaRemintParked
  /\ bags_sql_mm_status = BagsSqlMmNotDone
  /\ bags_cathedral_status = BagsCathedralNotLanded
  /\ cook_loop_status = LoopObligation
  /\ CircularCookCpConcat.phase_b_status = CircularCookCpConcat.PhaseBOpen.
Proof.
  repeat split; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_b_bags_inhabit_qed_or_qex","title":"Phase B bags MultiCurve and MultiSurface inhabit as bags of already-Qed CS CC CP members (QED) or a locked bag is empty (QEX); discharged QED; bag != concat; bag != cook loop; no new kernel","file":"theories/SidecarCircBags.v","witness":"0007-B-bags","board":"ADR-0007"} *)

Theorem ticket_0007_b_bags_inhabit_qed_or_qex :
  (mc_bag_ok locked_mc_typed
   /\ mc_bag_ok locked_mc_apart
   /\ ms_bag_ok locked_ms
   /\ ~ mc_contiguous locked_mc_apart)
  \/
  locked_mc_typed = [].
Proof.
  left.
  split; [exact locked_mc_typed_ok|].
  split; [exact locked_mc_apart_ok|].
  split; [exact locked_ms_ok|].
  exact locked_mc_apart_not_contiguous.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_b_bags_reuse_qed_or_qex","title":"Phase B bags membership joints reuse I_ok I_ok_circ I_ok_mixed and optional shared-endpoint pair reuses I_ok_mixed (QED) or a locked member joint declines (QEX); discharged QED; no new kernel; not a Multi cook","file":"theories/SidecarCircBags.v","witness":"0007-B-bags","board":"ADR-0007"} *)

Theorem ticket_0007_b_bags_reuse_qed_or_qex :
  (I_ok_circ locked_cs_arc_1 locked_cs_arc_2
     (CircularCookCsConcat.cs_joint_hit locked_cs_arc_1 locked_cs_arc_2)
   /\ SidecarCircMixed.I_ok_mixed
        (SidecarCircMixed.MixLsCs locked_cc_ls locked_cc_cs)
        (SidecarCircMixed.ls_cs_joint_hit locked_cc_ls locked_cc_cs)
   /\ I_ok (MkChord CircularCookCcConcat.locked_cc_ls1)
        (MkChord CircularCookCcConcat.locked_cc_ls2)
        (CircularCookCcConcat.ls_joint_hit
           CircularCookCcConcat.locked_cc_ls1
           CircularCookCcConcat.locked_cc_ls2)
   /\ I_ok_circ locked_cs_arc_2 locked_cs_arc_1
        (CircularCookCsConcat.cs_joint_hit locked_cs_arc_2 locked_cs_arc_1)
   /\ SidecarCircMixed.I_ok_mixed
        (SidecarCircMixed.MixCsLs locked_cc_cs locked_cc_ls)
        (SidecarCircMixed.cs_ls_joint_hit locked_cc_cs locked_cc_ls)
   /\ SidecarCircMixed.I_ok_mixed
        (SidecarCircMixed.MixCsLs locked_cs_arc_2 locked_cc_ls)
        (SidecarCircMixed.cs_ls_joint_hit locked_cs_arc_2 locked_cc_ls)
   /\ CircEgg = CircularArc)
  \/
  ~ CircularCookCsConcat.cs_joint locked_cs_arc_1 locked_cs_arc_2.
Proof.
  left.
  split; [exact bags_cs_member_joint_I_ok_circ|].
  split; [exact bags_cc_member_joint_I_ok_mixed|].
  split; [exact bags_cc_ls_ls_joint_I_ok|].
  split; [exact bags_cp_cs_closing_I_ok_circ|].
  split; [exact bags_cp_mixed_closing_I_ok_mixed|].
  destruct bags_optional_pair_I_ok_mixed as [_ Hpair].
  split; [exact Hpair|].
  reflexivity.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_b_bags_host_qed_or_qex","title":"Phase B bags discharges CircGamma and expands first cook to circular times chord interiors (QED) or CircGamma stays QEX and first cook stays chord-chord (QEX); discharged QEX; host mixed I_ok is Decline; I_ok_mixed Hit is not host I_ok; interior mixed cook is not invented","file":"theories/SidecarCircBags.v","witness":"0007-B-bags","board":"ADR-0007"} *)

Theorem ticket_0007_b_bags_host_qed_or_qex :
  (circular_gamma_status = CircGammaDischarged
   /\ first_cook_scope EggChord EggCircularArc
   /\ exists p ti tj,
        I_ok (MkChord locked_cc_ls) (MkOutOfScope EggCircularArc)
             (IHit p ti tj))
  \/
  (circular_gamma_status = CircGammaQEX
   /\ ~ first_cook_scope EggCircularArc EggCircularArc
   /\ first_cook_scope EggChord EggChord
   /\ ~ first_cook_scope EggChord EggCircularArc
   /\ I_ok (MkChord locked_cc_ls) (MkOutOfScope EggCircularArc) IDecline
   /\ (forall p ti tj,
         ~ I_ok (MkChord locked_cc_ls) (MkOutOfScope EggCircularArc)
              (IHit p ti tj))
   /\ SidecarCircMixed.I_ok_mixed
        (SidecarCircMixed.MixLsCs locked_cc_ls locked_cc_cs)
        (SidecarCircMixed.ls_cs_joint_hit locked_cc_ls locked_cc_cs)
   /\ ~ I_ok (MkChord locked_cc_ls) (MkOutOfScope EggCircularArc)
        (SidecarCircMixed.ls_cs_joint_hit locked_cc_ls locked_cc_cs)
   /\ bags_interior_cook_status = BagsInteriorCookParked).
Proof.
  right.
  destruct bags_host_stays_qex as [Hq [Hn [Hc [Hm [Hd Hf]]]]].
  destruct bags_I_ok_mixed_hit_not_host_I_ok as [Hhit Hhost].
  split; [exact Hq|].
  split; [exact Hn|].
  split; [exact Hc|].
  split; [exact Hm|].
  split; [exact Hd|].
  split; [exact Hf|].
  split; [exact Hhit|].
  split; [exact Hhost|].
  exact bags_interior_cook_is_parked.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_b_bags_park_qed_or_qex","title":"Phase B bags discharges bag noder, Hperp, CircGamma remint, SQL/MM cathedral, and Phase B done-when (QED) or names them parked / not-done (QEX); discharged QEX; bags letter landed; Multi required-type Gap; Phase B Open; letter landed != cathedral Landed","file":"theories/SidecarCircBags.v","witness":"0007-B-bags","board":"ADR-0007"} *)

Theorem ticket_0007_b_bags_park_qed_or_qex :
  (bags_interior_cook_status = BagsInteriorCookLanded
   /\ bags_hperp_status = BagsHperpDischarged
   /\ bags_circgamma_remint_status = BagsCircGammaReminted
   /\ bags_sql_mm_status = BagsSqlMmDone
   /\ bags_cathedral_status = BagsCathedralLanded
   /\ multi_required_status = MultiRequiredLanded
   /\ cook_loop_status = LoopDischarged
   /\ CircularCookCpConcat.phase_b_status = CircularCookCpConcat.PhaseBLanded)
  \/
  (bags_letter_status = BagsLetterLanded
   /\ multi_required_status = MultiRequiredGap
   /\ bags_interior_cook_status = BagsInteriorCookParked
   /\ bags_hperp_status = BagsHperpParked
   /\ bags_circgamma_remint_status = BagsCircGammaRemintParked
   /\ bags_sql_mm_status = BagsSqlMmNotDone
   /\ bags_cathedral_status = BagsCathedralNotLanded
   /\ cook_loop_status = LoopObligation
   /\ CircularCookCpConcat.phase_b_status = CircularCookCpConcat.PhaseBOpen).
Proof.
  right.
  exact bags_rest_parked.
Qed.

Print Assumptions bags_host_circgamma_qex.
Print Assumptions locked_mc_typed_ok.
Print Assumptions locked_ms_ok.
Print Assumptions bags_not_concat.
Print Assumptions bags_cs_member_joint_I_ok_circ.
Print Assumptions bags_cc_member_joint_I_ok_mixed.
Print Assumptions bags_optional_pair_I_ok_mixed.
Print Assumptions bags_reuse_no_new_kernel.
Print Assumptions bags_I_ok_mixed_hit_not_host_I_ok.
Print Assumptions bags_not_bag_noder.
Print Assumptions bags_letter_is_landed.
Print Assumptions multi_required_is_gap.
Print Assumptions bags_cathedral_is_not_landed.
Print Assumptions bags_phase_b_stays_open.
Print Assumptions ticket_0007_b_bags_inhabit_qed_or_qex.
Print Assumptions ticket_0007_b_bags_reuse_qed_or_qex.
Print Assumptions ticket_0007_b_bags_host_qed_or_qex.
Print Assumptions ticket_0007_b_bags_park_qed_or_qex.
