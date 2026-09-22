(* ============================================================================
   NetTopologySuite.Proofs.NurbsMkNurbs
   ----------------------------------------------------------------------------
   ADR-0007 letter: host MkNurbs (claimId 0007-mk-nurbs).

   Year-1 cook scope may include NURBS×NURBS. That is not this letter.
   MkNurbs is the host Egg constructor: control net + knots + weights
   give an interpolant γ on sheet S. Sidecar MkOutOfScope EggNurbs
   (SidecarNurbsEgg) is packaging, not this ctor.

   Searched the corpus. Host Egg is MkChord | MkCirc | MkClothoid |
   MkOutOfScope. No MkNurbs arm. No OnNurbs. No NurbsGammaOnSheet.
   nurbs2_pt / nurbs3_pt (NurbsQuadraticLength / NurbsGeneralLength)
   are #508 single-span rational Curves for length. They are not an
   Egg constructor, they do not carry a knot vector, and Cox-de Boor
   multi-span evaluation is out of scope there. Promoting them would
   demote host γ to a quadratic metric curve. Not done.

   QED would be one inhabitant: a non-tag Egg whose class is EggNurbs
   (the MkCirc shape: exists ne, egg_class (MkNurbs ne) = EggNurbs).
   That term does not typecheck. This letter does not add it.

   QEX (this letter): named missing constructors
     MkNurbs
     OnNurbs
     NurbsGammaOnSheet
   Host class EggNurbs is only MkOutOfScope EggNurbs. That tag is not
   an interpolant pair. Not a silent MkCirc / MkChord / MkClothoid.
   Ellipse / sinusoid / geodesic / spiral stay tags. No IEEE evaluator.

   Honesty fences:
     Do not remint CircGamma / MkCirc / LoopDischarged.
     Do not remint leftover Ⅹ. I_ok_mixed is not host I_ok.
     Do not inhabit MkEllipse / MkSinusoid / MkGeodesic / MkSpiral.
     Do not start ExactNurbsSegment. No new oracle keyword.
     #508 length stays metric (sidecar_nurbs_metric_not_cook_hit).
     ADR-0007 stays Accepted. QEX is not owner accept.

   WITNESS topic: overlay · claimId: 0007-mk-nurbs
   witness: 0007-mk-nurbs
   board: ADR-0007
   3-axiom host. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import Distance SheetHenCook SidecarNurbsEgg.
Local Open Scope R_scope.

(* WITNESS: campaign=nurbs rung=mk-nurbs claim=0007-mk-nurbs
   file=theories/NurbsMkNurbs.v
   kind=QEX-named-missing-ctors
   missing=MkNurbs,OnNurbs,NurbsGammaOnSheet
   not=MkCirc-demote,MkChord-demote,MkClothoid-demote
   not=ellipse,sinusoid,geodesic,spiral,ExactNurbsSegment
   not=CircGamma-remint,LoopDischarged,I_ok_mixed-as-host
   not=length-as-ctor,Cox-de-Boor,IEEE-evaluator
   note=tag-MkOutOfScope-is-not-MkNurbs *)

(* -------------------------------------------------------------------------- *)
(* Named missing host constructors. Not bools. Inhabitance would be a         *)
(* non-tag Egg of class EggNurbs (MkCirc shape). The tag is not that.         *)
(* -------------------------------------------------------------------------- *)

Inductive NurbsHostCtor : Type :=
| MkNurbs
| OnNurbs
| NurbsGammaOnSheet.

Definition nurbs_host_ctor_inhabits (c : NurbsHostCtor) : Prop :=
  match c with
  | MkNurbs | OnNurbs | NurbsGammaOnSheet =>
      exists e, egg_class e = EggNurbs /\ e <> MkOutOfScope EggNurbs
  end.

Lemma egg_nurbs_only_out_of_scope :
  forall e, egg_class e = EggNurbs -> e = MkOutOfScope EggNurbs.
Proof.
  intros e H.
  destruct e as [ch|ce|cl|k]; simpl in H; try discriminate.
  rewrite <- H. reflexivity.
Qed.

Lemma no_host_nurbs_ctor :
  ~ exists e, egg_class e = EggNurbs /\ e <> MkOutOfScope EggNurbs.
Proof.
  intros [e [Hcls Hneq]].
  apply Hneq. apply egg_nurbs_only_out_of_scope. exact Hcls.
Qed.

Lemma mk_nurbs_missing : ~ nurbs_host_ctor_inhabits MkNurbs.
Proof. exact no_host_nurbs_ctor. Qed.

Lemma on_nurbs_missing : ~ nurbs_host_ctor_inhabits OnNurbs.
Proof. exact no_host_nurbs_ctor. Qed.

Lemma nurbs_gamma_on_sheet_missing :
  ~ nurbs_host_ctor_inhabits NurbsGammaOnSheet.
Proof. exact no_host_nurbs_ctor. Qed.

Lemma nurbs_tag_is_packaging :
  egg_class (MkOutOfScope EggNurbs) = EggNurbs.
Proof. reflexivity. Qed.

Lemma nurbs_tag_not_interpolant_pair :
  ~ interpolant_pair (MkOutOfScope EggNurbs) (MkOutOfScope EggNurbs).
Proof. intro H. exact H. Qed.

Lemma nurbs_tag_not_silent_demote :
  (forall c, MkOutOfScope EggNurbs <> MkCirc c) /\
  (forall c, MkOutOfScope EggNurbs <> MkChord c) /\
  (forall c, MkOutOfScope EggNurbs <> MkClothoid c).
Proof.
  repeat split; intro c; discriminate.
Qed.

(* Ellipse / sinusoid / geodesic / spiral: same host fact, not new ctors. *)
Lemma other_tagged_eggs_stay_out_of_scope :
  (forall e, egg_class e = EggEllipse -> e = MkOutOfScope EggEllipse) /\
  (forall e, egg_class e = EggSinusoid -> e = MkOutOfScope EggSinusoid) /\
  (forall e, egg_class e = EggGeodesicString ->
             e = MkOutOfScope EggGeodesicString) /\
  (forall e, egg_class e = EggSpiralCurve -> e = MkOutOfScope EggSpiralCurve).
Proof.
  repeat split; intros e H;
    destruct e as [ch|ce|cl|k]; simpl in H; try discriminate;
    rewrite <- H; reflexivity.
Qed.

(* #508 length lane is not this ctor. Sidecar already records that. *)
Lemma nurbs_length_lane_not_this_ctor :
  sidecar_nurbs_metric_kind = SNM_LengthResearch /\
  sidecar_nurbs_metric_kind <> SNM_CookHit /\
  ~ sidecar_nurbs_ctor_inhabits NurbsMkNurbs.
Proof.
  split; [exact sidecar_nurbs_metric_is_length|].
  split; [exact sidecar_nurbs_metric_not_cook_hit|].
  exact sidecar_nurbs_mknurbs_missing.
Qed.

(* WITNESS {"claimId":"0007-mk-nurbs","topic":"overlay","lemma":"ticket_0007_mk_nurbs_qed_or_qex","title":"Host MkNurbs inhabits Egg as control-net knots weights to gamma on S (QED) or MkNurbs / OnNurbs / NurbsGammaOnSheet stay missing and EggNurbs is only MkOutOfScope (QEX); discharged QEX; nurbs2_pt is length not this ctor; no silent MkCirc","file":"theories/NurbsMkNurbs.v","witness":"0007-mk-nurbs","board":"ADR-0007"} *)
Theorem ticket_0007_mk_nurbs_qed_or_qex :
  (nurbs_host_ctor_inhabits MkNurbs /\
   nurbs_host_ctor_inhabits OnNurbs /\
   nurbs_host_ctor_inhabits NurbsGammaOnSheet)
  \/
  (~ nurbs_host_ctor_inhabits MkNurbs /\
   ~ nurbs_host_ctor_inhabits OnNurbs /\
   ~ nurbs_host_ctor_inhabits NurbsGammaOnSheet /\
   (forall e, egg_class e = EggNurbs -> e = MkOutOfScope EggNurbs) /\
   egg_class (MkOutOfScope EggNurbs) = EggNurbs /\
   ~ interpolant_pair (MkOutOfScope EggNurbs) (MkOutOfScope EggNurbs) /\
   (forall c, MkOutOfScope EggNurbs <> MkCirc c) /\
   sidecar_nurbs_metric_kind <> SNM_CookHit).
Proof.
  right.
  split; [exact mk_nurbs_missing|].
  split; [exact on_nurbs_missing|].
  split; [exact nurbs_gamma_on_sheet_missing|].
  split; [exact egg_nurbs_only_out_of_scope|].
  split; [exact nurbs_tag_is_packaging|].
  split; [exact nurbs_tag_not_interpolant_pair|].
  split; [exact (proj1 nurbs_tag_not_silent_demote)|].
  exact sidecar_nurbs_metric_not_cook_hit.
Qed.

Print Assumptions egg_nurbs_only_out_of_scope.
Print Assumptions no_host_nurbs_ctor.
Print Assumptions mk_nurbs_missing.
Print Assumptions on_nurbs_missing.
Print Assumptions nurbs_gamma_on_sheet_missing.
Print Assumptions nurbs_tag_not_silent_demote.
Print Assumptions other_tagged_eggs_stay_out_of_scope.
Print Assumptions nurbs_length_lane_not_this_ctor.
Print Assumptions ticket_0007_mk_nurbs_qed_or_qex.
