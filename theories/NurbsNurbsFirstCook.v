(* ============================================================================
   NetTopologySuite.Proofs.NurbsNurbsFirstCook
   ----------------------------------------------------------------------------
   ADR-0007 letter: NURBS×NURBS first-cook scope flip
   (claimId 0007-nurbs-nurbs-first-cook).

   Owner #838 Yes flip: nurbs_nurbs_not_first_scope was the wrong
   ceiling. A NURBS can fully overlap a circle, so ×self is in cook
   scope. Constructor = first_cook_scope EggNurbs EggNurbs.

   LEFT: inhabit that Prop (SheetHenCook match arm, exact I), same
   shape as circular_egg_first_cook_scope / clothoid_egg_first_cook_scope.
   Old pin nurbs_nurbs_not_first_scope is discharged (named status),
   not silently deleted. No circular-NURBS restricted predicate —
   general ×self scope inhabit does not need one. Tags stay
   MkOutOfScope Decline. No MkNurbs. No on_nurbs. No host IHit.

   RIGHT would name an obstruction and keep the old QEX. Not this
   letter: silent NURBS=MkCirc / NURBS=MkChord (#729) are named
   refused paths, not the inhabit.

   Honesty fences:
     No silent NURBS=MkCirc. No silent NURBS=MkChord.
     No CurveSegment ctor for NURBS. No CircGamma remint.
     I_ok_mixed is not host I_ok. leftover Ⅹ stays leftover Ⅹ.
     #767 stays owner of circ×chord 𝓘 (HostMixedHitTi / Span).
     LeftoverBagTermArm / LoopDischarged stay QEX.
     SidecarNurbsEgg package (0007-nurbs-egg) is not reminted.

   QEX is not owner accept. ADR-0007 stays Accepted.

   WITNESS topic: overlay · claimId: 0007-nurbs-nurbs-first-cook
   witness: 0007-nurbs-nurbs-first-cook
   board: ADR-0007
   3-axiom. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import Distance SheetHenCook.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Scope inhabit. Mirrors circ / clothoid: first_cook_scope is a              *)
(* class-pair Prop, not a Hit interpolant.                                    *)
(* -------------------------------------------------------------------------- *)

Lemma nurbs_nurbs_in_first_cook_scope :
  first_cook_scope EggNurbs EggNurbs.
Proof.
  exact nurbs_nurbs_first_cook_scope.
Qed.

Lemma first_cook_scope_same_kind_with_nurbs :
  first_cook_scope EggChord EggChord
  /\ first_cook_scope EggCircularArc EggCircularArc
  /\ first_cook_scope EggClothoid EggClothoid
  /\ first_cook_scope EggNurbs EggNurbs.
Proof.
  split; [exact first_cook_scope_chord_chord|].
  split; [exact circular_egg_first_cook_scope|].
  split; [exact clothoid_egg_first_cook_scope|].
  exact nurbs_nurbs_first_cook_scope.
Qed.

(* -------------------------------------------------------------------------- *)
(* Old QEX pin nurbs_nurbs_not_first_scope: discharged, not deleted.          *)
(* No circular-NURBS restricted predicate; ×self scope is the inhabit.        *)
(* -------------------------------------------------------------------------- *)

Inductive NurbsNurbsOldPin : Type :=
| NurbsNurbsNotFirstScope.

Inductive NurbsNurbsPinStatus : Type :=
| NurbsNurbsOldPinCeiling
| NurbsNurbsOldPinDischarged.

Definition nurbs_nurbs_old_pin_status : NurbsNurbsPinStatus :=
  NurbsNurbsOldPinDischarged.

Lemma nurbs_nurbs_not_first_scope_discharged :
  nurbs_nurbs_old_pin_status = NurbsNurbsOldPinDischarged
  /\ nurbs_nurbs_old_pin_status <> NurbsNurbsOldPinCeiling
  /\ first_cook_scope EggNurbs EggNurbs.
Proof.
  split; [reflexivity|].
  split; [discriminate|].
  exact nurbs_nurbs_first_cook_scope.
Qed.

Inductive NurbsNurbsRestrictedPred : Type :=
| NurbsCircularOverlapPred.

Definition nurbs_nurbs_restricted_pred_inhabits
  (p : NurbsNurbsRestrictedPred) : Prop :=
  match p with
  | NurbsCircularOverlapPred => False
  end.

Lemma nurbs_circular_overlap_pred_not_needed :
  ~ nurbs_nurbs_restricted_pred_inhabits NurbsCircularOverlapPred
  /\ first_cook_scope EggNurbs EggNurbs.
Proof.
  split; [intro H; exact H|].
  exact nurbs_nurbs_first_cook_scope.
Qed.

Inductive NurbsNurbsSilentPath : Type :=
| NurbsNotSilentCircDemote
| NurbsNotChordDemote.

Definition nurbs_nurbs_silent_path_inhabits
  (p : NurbsNurbsSilentPath) : Prop :=
  match p with
  | NurbsNotSilentCircDemote => False
  | NurbsNotChordDemote => False
  end.

Lemma nurbs_not_silent_circ_demote :
  ~ nurbs_nurbs_silent_path_inhabits NurbsNotSilentCircDemote.
Proof.
  intro H. exact H.
Qed.

Lemma nurbs_not_chord_demote :
  ~ nurbs_nurbs_silent_path_inhabits NurbsNotChordDemote.
Proof.
  intro H. exact H.
Qed.

(* EggNurbs is the out-of-scope tag or the fail-closed MkNurbs arm.
   The arm is not an interpolant. Exact cook is not this letter. *)
Lemma egg_nurbs_is_tag :
  forall e, egg_class e = EggNurbs ->
    e = MkOutOfScope EggNurbs \/ exists ne, e = MkNurbs ne.
Proof.
  intros e H.
  destruct e as [ch|ce|cl|k|ne]; simpl in H; try discriminate.
  - left. rewrite H. reflexivity.
  - right. exists ne. reflexivity.
Qed.

Lemma nurbs_tag_not_mkcirc :
  forall c, MkOutOfScope EggNurbs <> MkCirc c.
Proof.
  intros c H. discriminate.
Qed.

Lemma nurbs_tag_not_mkchord :
  forall c, MkOutOfScope EggNurbs <> MkChord c.
Proof.
  intros c H. discriminate.
Qed.

Lemma nurbs_tag_not_mkclothoid :
  forall c, MkOutOfScope EggNurbs <> MkClothoid c.
Proof.
  intros c H. discriminate.
Qed.

Lemma interpolant_pair_nurbs_tag_false :
  ~ interpolant_pair (MkOutOfScope EggNurbs) (MkOutOfScope EggNurbs).
Proof.
  intro H. exact H.
Qed.

Lemma nurbs_tag_still_decline :
  I_ok (MkOutOfScope EggNurbs) (MkOutOfScope EggNurbs) IDecline.
Proof.
  exact nurbs_decline_I_ok.
Qed.

Lemma nurbs_tag_hit_false :
  forall p ti tj,
    ~ I_ok (MkOutOfScope EggNurbs) (MkOutOfScope EggNurbs)
         (IHit p ti tj).
Proof.
  intros p ti tj H. exact H.
Qed.

Lemma nurbs_tag_empty_false :
  ~ I_ok (MkOutOfScope EggNurbs) (MkOutOfScope EggNurbs) IEmpty.
Proof.
  intro H. exact H.
Qed.

Lemma nurbs_try_cook_still_none :
  try_cook_hit nurbs_ck1 nurbs_ck2 IDecline crossing_hen = None.
Proof.
  exact try_cook_hit_nurbs_none.
Qed.

(* -------------------------------------------------------------------------- *)
(* Parks that this letter does not flip.                                      *)
(* -------------------------------------------------------------------------- *)

Lemma circ_chord_stays_767 :
  ~ first_cook_scope EggChord EggCircularArc
  /\ ~ first_cook_scope EggCircularArc EggChord.
Proof.
  split; [exact chord_circular_not_first_cook_scope|].
  intro H. exact H.
Qed.

Lemma leftover_loop_stays_obligation :
  cook_loop_status = LoopObligation
  /\ cook_loop_status <> LoopDischarged.
Proof.
  split; [exact cook_loop_is_obligation|].
  exact cook_loop_not_discharged.
Qed.

Lemma ellipse_still_not_first_cook :
  ~ first_cook_scope EggEllipse EggEllipse.
Proof.
  exact ellipse_ellipse_not_first_scope.
Qed.

Lemma other_eggs_stay_out :
  ~ first_cook_scope EggSinusoid EggSinusoid
  /\ ~ first_cook_scope EggGeodesicString EggGeodesicString
  /\ ~ first_cook_scope EggSpiralCurve EggSpiralCurve.
Proof.
  split; [intro H; exact H|].
  split; [intro H; exact H|].
  intro H. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket. QED ∨ QEX. Discharged LEFT: scope inhabit, no fake Hit.            *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-nurbs-nurbs-first-cook","topic":"overlay","lemma":"ticket_0007_nurbs_nurbs_first_cook_qed_or_qex","title":"NURBS times NURBS first_cook_scope inhabited and old pin nurbs_nurbs_not_first_scope discharged (QED) or named obstruction keeps the old QEX (QEX); discharged QED; no circular-NURBS restricted pred; no silent MkCirc / MkChord; #767 stays circ times chord I; LoopDischarged stays QEX","file":"theories/NurbsNurbsFirstCook.v","witness":"0007-nurbs-nurbs-first-cook","board":"ADR-0007"} *)
Theorem ticket_0007_nurbs_nurbs_first_cook_qed_or_qex :
  (first_cook_scope EggNurbs EggNurbs
   /\ nurbs_nurbs_old_pin_status = NurbsNurbsOldPinDischarged
   /\ nurbs_nurbs_old_pin_status <> NurbsNurbsOldPinCeiling
   /\ ~ nurbs_nurbs_restricted_pred_inhabits NurbsCircularOverlapPred
   /\ ~ nurbs_nurbs_silent_path_inhabits NurbsNotSilentCircDemote
   /\ ~ nurbs_nurbs_silent_path_inhabits NurbsNotChordDemote
   /\ first_cook_scope EggChord EggChord
   /\ first_cook_scope EggCircularArc EggCircularArc
   /\ first_cook_scope EggClothoid EggClothoid
   /\ I_ok (MkOutOfScope EggNurbs) (MkOutOfScope EggNurbs) IDecline
   /\ (forall p ti tj,
         ~ I_ok (MkOutOfScope EggNurbs) (MkOutOfScope EggNurbs)
              (IHit p ti tj))
   /\ (forall e, egg_class e = EggNurbs ->
         e = MkOutOfScope EggNurbs \/ exists ne, e = MkNurbs ne)
   /\ (forall c, MkOutOfScope EggNurbs <> MkCirc c)
   /\ (forall c, MkOutOfScope EggNurbs <> MkChord c)
   /\ ~ interpolant_pair (MkOutOfScope EggNurbs) (MkOutOfScope EggNurbs)
   /\ ~ first_cook_scope EggChord EggCircularArc
   /\ ~ first_cook_scope EggCircularArc EggChord
   /\ cook_loop_status = LoopObligation
   /\ cook_loop_status <> LoopDischarged
   /\ ~ first_cook_scope EggEllipse EggEllipse
   /\ ~ first_cook_scope EggSinusoid EggSinusoid
   /\ ~ first_cook_scope EggGeodesicString EggGeodesicString
   /\ ~ first_cook_scope EggSpiralCurve EggSpiralCurve)
  \/
  (~ first_cook_scope EggNurbs EggNurbs
   /\ nurbs_nurbs_old_pin_status = NurbsNurbsOldPinCeiling).
Proof.
  left.
  split; [exact nurbs_nurbs_first_cook_scope|].
  split; [reflexivity|].
  split; [discriminate|].
  split; [intro H; exact H|].
  split; [exact nurbs_not_silent_circ_demote|].
  split; [exact nurbs_not_chord_demote|].
  split; [exact first_cook_scope_chord_chord|].
  split; [exact circular_egg_first_cook_scope|].
  split; [exact clothoid_egg_first_cook_scope|].
  split; [exact nurbs_tag_still_decline|].
  split; [exact nurbs_tag_hit_false|].
  split; [exact egg_nurbs_is_tag|].
  split; [exact nurbs_tag_not_mkcirc|].
  split; [exact nurbs_tag_not_mkchord|].
  split; [exact interpolant_pair_nurbs_tag_false|].
  split; [exact chord_circular_not_first_cook_scope|].
  split; [intro H; exact H|].
  split; [exact cook_loop_is_obligation|].
  split; [exact cook_loop_not_discharged|].
  split; [exact ellipse_ellipse_not_first_scope|].
  destruct other_eggs_stay_out as [Hsin [Hgeo Hspi]].
  split; [exact Hsin|].
  split; [exact Hgeo|].
  exact Hspi.
Qed.

Print Assumptions nurbs_nurbs_in_first_cook_scope.
Print Assumptions first_cook_scope_same_kind_with_nurbs.
Print Assumptions nurbs_nurbs_not_first_scope_discharged.
Print Assumptions nurbs_circular_overlap_pred_not_needed.
Print Assumptions nurbs_not_silent_circ_demote.
Print Assumptions nurbs_not_chord_demote.
Print Assumptions egg_nurbs_is_tag.
Print Assumptions nurbs_tag_not_mkcirc.
Print Assumptions nurbs_tag_not_mkchord.
Print Assumptions nurbs_tag_still_decline.
Print Assumptions nurbs_tag_hit_false.
Print Assumptions interpolant_pair_nurbs_tag_false.
Print Assumptions circ_chord_stays_767.
Print Assumptions leftover_loop_stays_obligation.
Print Assumptions other_eggs_stay_out.
Print Assumptions ticket_0007_nurbs_nurbs_first_cook_qed_or_qex.
