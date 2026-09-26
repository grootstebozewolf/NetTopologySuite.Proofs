(* ============================================================================
   NetTopologySuite.Proofs.NurbsMkNurbs
   ----------------------------------------------------------------------------
   ADR-0007 letter: host MkNurbs (claimId 0007-mk-nurbs).

   Year-1 exact NURBS×NURBS is not this letter. NTS linearizes, so
   exact NURBS×NURBS is year 2. This draft adds the fail-closed
   MkNurbs arm only. OnNurbs and NurbsGammaOnSheet stay missing.
   first_cook_scope EggNurbs EggNurbs remains a class-pair flag.
   The cook of a MkNurbs egg is IDecline. Not a freeze lift by itself:
   merge waits on the dated ruling.
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

(* The three names used to share one Prop (exists a non-tag EggNurbs).
   That Prop becomes true for all three the moment MkNurbs exists, which
   would flip OnNurbs and NurbsGammaOnSheet. They are split.
   OnNurbs and NurbsGammaOnSheet stay False: the predicates are not
   defined in this letter. *)
Definition nurbs_host_ctor_inhabits (c : NurbsHostCtor) : Prop :=
  match c with
  | MkNurbs => True
  | OnNurbs => False
  | NurbsGammaOnSheet => False
  end.

Lemma egg_nurbs_tag_or_arm :
  forall e, egg_class e = EggNurbs ->
    e = MkOutOfScope EggNurbs \/ exists ne, e = MkNurbs ne.
Proof.
  intros e H.
  destruct e as [ch|ce|cl|k|ne]; simpl in H; try discriminate.
  - left. rewrite <- H. reflexivity.
  - right. exists ne. reflexivity.
Qed.

Lemma mk_nurbs_failclosed : forall ne,
  egg_class (MkNurbs ne) = EggNurbs /\
  I_ok (MkNurbs ne) (MkNurbs ne) IDecline /\
  ~ interpolant_pair (MkNurbs ne) (MkNurbs ne).
Proof.
  intros ne. split; [reflexivity|].
  split.
  - unfold I_ok. exact I.
  - intro H. exact H.
Qed.

Lemma mk_nurbs_arm_present : nurbs_host_ctor_inhabits MkNurbs.
Proof. exact I. Qed.

Lemma on_nurbs_missing : ~ nurbs_host_ctor_inhabits OnNurbs.
Proof. intro H. exact H. Qed.

Lemma nurbs_gamma_on_sheet_missing :
  ~ nurbs_host_ctor_inhabits NurbsGammaOnSheet.
Proof. intro H. exact H. Qed.

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
    destruct e as [ch|ce|cl|k|ne]; simpl in H; try discriminate;
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

(* WITNESS {"claimId":"0007-mk-nurbs","topic":"overlay","lemma":"ticket_0007_mk_nurbs_qed_or_qex","title":"Host MkNurbs arm is fail-closed IDecline and OnNurbs / NurbsGammaOnSheet stay missing (QEX) or both predicates inhabit (QED); discharged QEX; not an exact NURBS cook; EggNurbs is the tag or the arm","file":"theories/NurbsMkNurbs.v","witness":"0007-mk-nurbs","board":"ADR-0007"} *)
Theorem ticket_0007_mk_nurbs_qed_or_qex :
  (nurbs_host_ctor_inhabits OnNurbs /\
   nurbs_host_ctor_inhabits NurbsGammaOnSheet)
  \/
  (~ nurbs_host_ctor_inhabits OnNurbs /\
   ~ nurbs_host_ctor_inhabits NurbsGammaOnSheet /\
   nurbs_host_ctor_inhabits MkNurbs /\
   (forall ne, I_ok (MkNurbs ne) (MkNurbs ne) IDecline) /\
   (forall e, egg_class e = EggNurbs ->
      e = MkOutOfScope EggNurbs \/ exists ne, e = MkNurbs ne) /\
   egg_class (MkOutOfScope EggNurbs) = EggNurbs /\
   ~ interpolant_pair (MkOutOfScope EggNurbs) (MkOutOfScope EggNurbs) /\
   (forall c, MkOutOfScope EggNurbs <> MkCirc c) /\
   sidecar_nurbs_metric_kind <> SNM_CookHit).
Proof.
  right.
  split; [exact on_nurbs_missing|].
  split; [exact nurbs_gamma_on_sheet_missing|].
  split; [exact mk_nurbs_arm_present|].
  split; [intros ne; exact (proj1 (proj2 (mk_nurbs_failclosed ne)))|].
  split; [exact egg_nurbs_tag_or_arm|].
  split; [exact nurbs_tag_is_packaging|].
  split; [exact nurbs_tag_not_interpolant_pair|].
  split; [exact (proj1 nurbs_tag_not_silent_demote)|].
  exact sidecar_nurbs_metric_not_cook_hit.
Qed.

Print Assumptions egg_nurbs_tag_or_arm.
Print Assumptions mk_nurbs_failclosed.
Print Assumptions mk_nurbs_arm_present.
Print Assumptions on_nurbs_missing.
Print Assumptions nurbs_gamma_on_sheet_missing.
Print Assumptions nurbs_tag_not_silent_demote.
Print Assumptions other_tagged_eggs_stay_out_of_scope.
Print Assumptions nurbs_length_lane_not_this_ctor.
Print Assumptions ticket_0007_mk_nurbs_qed_or_qex.
