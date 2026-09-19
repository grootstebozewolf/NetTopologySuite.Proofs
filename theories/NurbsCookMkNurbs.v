(* ============================================================================
   NetTopologySuite.Proofs.NurbsCookMkNurbs
   ----------------------------------------------------------------------------
   ADR-0007 letter: NURBS×NURBS first-cook / Hit arm
   (claimId 0007-nurbs-first-cook).

   QEX. on_nurbs is endpoint-chord lerp; nurbs_ctrl is unused
   (SheetHenNurbsEgg.v : nurbs_eval_ignores_ctrl). That is a silent
   on_chord demote. first_cook_scope EggNurbs EggNurbs is False.
   MkNurbs stays scaffolding; interpolant_pair / I_ok Hit / try_cook
   mint do not treat it as a cook interpolant.

   Named missing ctor: NurbsNotChordDemote — a host IHit whose
   on_nurbs is not definitionally endpoint-chord lerp / uses ctrl
   (or true NURBS eval) without Cox-de-Boor-as-noder.

   MkOutOfScope EggNurbs stays Decline. Mixed NURBS×chord stays
   Decline. SIN / ellipse / spiral / geodesic stay out of first
   cook. ρ / Campaign / length-as-noding stay parked. Epic
   completeness stays ellipse–ellipse QEX.

   WITNESS topic: overlay · claimId: 0007-nurbs-first-cook
   witness: 0007-nurbs-first-cook
   board: ADR-0007
   3-axiom. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance SheetHenCook.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Locked MkNurbs eggs. Same endpoints as diag_ab / diag_cd.                  *)
(* -------------------------------------------------------------------------- *)

Definition locked_nurbs_A : NurbsEgg :=
  mkNurbsEgg (mkPoint 0 0) (mkPoint 2 2) (mkPoint 2 0).

Definition locked_nurbs_B : NurbsEgg :=
  mkNurbsEgg (mkPoint 0 2) (mkPoint 2 0) (mkPoint 0 0).

Definition locked_nurbs_hit_pt : Point := mkPoint 1 1.
Definition locked_nurbs_ti : R := 1 / 2.
Definition locked_nurbs_tj : R := 1 / 2.

Definition locked_nurbs_ck1 : Chicken :=
  mkChicken 0%nat 1%nat (MkNurbs locked_nurbs_A).

Definition locked_nurbs_ck2 : Chicken :=
  mkChicken 2%nat 3%nat (MkNurbs locked_nurbs_B).

Definition locked_mknurbs_hit : IResult :=
  IHit locked_nurbs_hit_pt locked_nurbs_ti locked_nurbs_tj.

(* Honesty: eval ignores ctrl. Not a first-cook interpolant. *)
Lemma locked_nurbs_eval_ignores_ctrl :
  nurbs_eval locked_nurbs_A locked_nurbs_ti =
  nurbs_eval (mkNurbsEgg (nurbs_p0 locked_nurbs_A)
                         (nurbs_p1 locked_nurbs_A)
                         (mkPoint 0 0)) locked_nurbs_ti.
Proof.
  apply nurbs_eval_ignores_ctrl.
Qed.

Lemma locked_on_nurbs_is_endpoint_lerp :
  on_nurbs locked_nurbs_A locked_nurbs_ti locked_nurbs_hit_pt ->
  locked_nurbs_hit_pt =
    mkPoint ((1 - locked_nurbs_ti) * px (nurbs_p0 locked_nurbs_A)
             + locked_nurbs_ti * px (nurbs_p1 locked_nurbs_A))
            ((1 - locked_nurbs_ti) * py (nurbs_p0 locked_nurbs_A)
             + locked_nurbs_ti * py (nurbs_p1 locked_nurbs_A)).
Proof.
  intro H.
  apply on_nurbs_is_endpoint_lerp in H.
  apply H.
Qed.

(* -------------------------------------------------------------------------- *)
(* Named missing constructor. 508-style, not a bool.                          *)
(* -------------------------------------------------------------------------- *)

Inductive NurbsFirstCookCtor : Type :=
| NurbsNotChordDemote.

Definition nurbs_first_cook_ctor_inhabits
  (c : NurbsFirstCookCtor) : Prop :=
  match c with
  | NurbsNotChordDemote => False
  end.

Lemma nurbs_not_chord_demote_missing :
  ~ nurbs_first_cook_ctor_inhabits NurbsNotChordDemote.
Proof.
  intro H. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* Host cook path does not Hit / mint on MkNurbs. Mixed / tags Decline.       *)
(* -------------------------------------------------------------------------- *)

Lemma locked_mknurbs_hit_false :
  forall p ti tj,
    ~ I_ok (MkNurbs locked_nurbs_A) (MkNurbs locked_nurbs_B)
         (IHit p ti tj).
Proof.
  intros p ti tj H. exact H.
Qed.

Lemma locked_mknurbs_not_interpolant :
  ~ interpolant_pair (MkNurbs locked_nurbs_A) (MkNurbs locked_nurbs_B).
Proof.
  intro H. exact H.
Qed.

Lemma locked_mknurbs_decline :
  I_ok (MkNurbs locked_nurbs_A) (MkNurbs locked_nurbs_B) IDecline.
Proof.
  unfold I_ok, interpolant_pair. intro H. exact H.
Qed.

Lemma cooked_mknurbs_try_none :
  try_cook_hit locked_nurbs_ck1 locked_nurbs_ck2
    locked_mknurbs_hit crossing_hen = None.
Proof.
  reflexivity.
Qed.

Lemma mknurbs_tag_still_decline :
  I_ok (MkOutOfScope EggNurbs) (MkOutOfScope EggNurbs) IDecline.
Proof.
  exact nurbs_decline_I_ok.
Qed.

Lemma mknurbs_tag_hit_false :
  forall p ti tj,
    ~ I_ok (MkOutOfScope EggNurbs) (MkOutOfScope EggNurbs)
         (IHit p ti tj).
Proof.
  intros p ti tj H. exact H.
Qed.

Lemma mknurbs_mixed_still_decline :
  I_ok (MkChord hor_bot) (MkNurbs locked_nurbs_A) IDecline.
Proof.
  unfold I_ok, interpolant_pair. intro H. exact H.
Qed.

Lemma nurbs_chord_not_first_cook_scope :
  ~ first_cook_scope EggNurbs EggChord.
Proof.
  intro H. exact H.
Qed.

Lemma mknurbs_neq_mkchord_locked :
  MkNurbs locked_nurbs_A <> MkChord diag_ab.
Proof.
  discriminate.
Qed.

Lemma locked_payload_egg_hit_false :
  forall p ti tj,
    ~ I_ok (MkNurbs locked_nurbs_egg) (MkNurbs locked_nurbs_egg)
         (IHit p ti tj).
Proof.
  intros p ti tj H. exact H.
Qed.

(* WITNESS {"claimId":"0007-nurbs-first-cook","topic":"overlay","lemma":"nurbs_not_chord_demote_missing","title":"Named missing ctor NurbsNotChordDemote: a host IHit whose on_nurbs is not definitionally endpoint-chord lerp / uses ctrl without Cox-de-Boor-as-noder","file":"theories/NurbsCookMkNurbs.v","witness":"0007-nurbs-first-cook","board":"ADR-0007"} *)

(* WITNESS {"claimId":"0007-nurbs-first-cook","topic":"overlay","lemma":"locked_mknurbs_hit_false","title":"Host I_ok does not Hit two MkNurbs chickens; on_nurbs is silent chord demote","file":"theories/NurbsCookMkNurbs.v","witness":"0007-nurbs-first-cook","board":"ADR-0007"} *)

(* WITNESS {"claimId":"0007-nurbs-first-cook","topic":"overlay","lemma":"ticket_0007_nurbs_first_cook_qed_or_qex","title":"NURBS times NURBS is first cook with a locked MkNurbs IHit whose on_nurbs is not endpoint-chord lerp (QED) or NURBS times NURBS stays QEX with named missing ctor NurbsNotChordDemote (QEX); discharged QEX; tags and mixed stay Decline; length-as-noding / Cox-de-Boor / Campaign / rho stay parked","file":"theories/NurbsCookMkNurbs.v","witness":"0007-nurbs-first-cook","board":"ADR-0007"} *)
Theorem ticket_0007_nurbs_first_cook_qed_or_qex :
  (first_cook_scope EggNurbs EggNurbs /\
   nurbs_first_cook_ctor_inhabits NurbsNotChordDemote /\
   interpolant_pair (MkNurbs locked_nurbs_A) (MkNurbs locked_nurbs_B) /\
   I_ok (MkNurbs locked_nurbs_A) (MkNurbs locked_nurbs_B)
        (IHit locked_nurbs_hit_pt locked_nurbs_ti locked_nurbs_tj) /\
   try_cook_hit locked_nurbs_ck1 locked_nurbs_ck2
     locked_mknurbs_hit crossing_hen <> None /\
   I_ok (MkOutOfScope EggNurbs) (MkOutOfScope EggNurbs) IDecline /\
   I_ok (MkChord hor_bot) (MkNurbs locked_nurbs_A) IDecline /\
   ~ first_cook_scope EggNurbs EggChord /\
   ~ first_cook_scope EggEllipse EggEllipse /\
   cook_loop_status = LoopObligation)
  \/
  (~ first_cook_scope EggNurbs EggNurbs /\
   ~ nurbs_first_cook_ctor_inhabits NurbsNotChordDemote /\
   (forall p ti tj,
      ~ I_ok (MkNurbs locked_nurbs_A) (MkNurbs locked_nurbs_B)
           (IHit p ti tj)) /\
   I_ok (MkOutOfScope EggNurbs) (MkOutOfScope EggNurbs) IDecline /\
   I_ok (MkChord hor_bot) (MkNurbs locked_nurbs_A) IDecline /\
   ~ first_cook_scope EggNurbs EggChord /\
   ~ first_cook_scope EggEllipse EggEllipse /\
   cook_loop_status = LoopObligation).
Proof.
  right.
  split; [exact nurbs_nurbs_not_first_scope|].
  split; [exact nurbs_not_chord_demote_missing|].
  split; [exact locked_mknurbs_hit_false|].
  split; [exact mknurbs_tag_still_decline|].
  split; [exact mknurbs_mixed_still_decline|].
  split; [exact nurbs_chord_not_first_cook_scope|].
  split; [exact ellipse_ellipse_not_first_scope|].
  exact cook_loop_is_obligation.
Qed.

Print Assumptions nurbs_eval_ignores_ctrl.
Print Assumptions on_nurbs_is_endpoint_lerp.
Print Assumptions locked_nurbs_eval_ignores_ctrl.
Print Assumptions nurbs_not_chord_demote_missing.
Print Assumptions locked_mknurbs_hit_false.
Print Assumptions locked_mknurbs_not_interpolant.
Print Assumptions locked_mknurbs_decline.
Print Assumptions cooked_mknurbs_try_none.
Print Assumptions mknurbs_mixed_still_decline.
Print Assumptions locked_payload_egg_hit_false.
Print Assumptions ticket_0007_nurbs_first_cook_qed_or_qex.
