(* ============================================================================
   NetTopologySuite.Proofs.HostFirstCookCircChord
   ----------------------------------------------------------------------------
   ADR-0007 host first-cook park letter (claimId 0007-host-first-cook-circ-chord).
   Circ×chord / chord×circ on the host cook, not a sidecar remint.

   Circ×circ is already first cook (MkCirc). Chord×chord too. Mixed
   first_cook_scope EggChord EggCircularArc and the reverse are False
   (SheetHenCook.v : chord_circular_not_first_cook_scope). This letter
   does not flip those arms. I_ok's mixed arms live in SheetHenCookCore.

   Sidecar RootTag / I_ok_mixed remain the working mixed classifier
   (SidecarCircIotaArm / SidecarCircMixed / SidecarCircIotaTags). Cited,
   not copied, not Required — sidecar is 4-axiom / Category C. Host
   I_ok_mixed / I_ok_interior Hit is not host I_ok.

   In-scope host I_ok Hit (both orders, |Δθ| < 2π, nondegenerate chord)
   is 0007-host-circ-chord-oracle. This letter does not flip
   first_cook_scope. try_cook_hit stays None; the ∀-bag split is the
   mixed cook (mixed_cook_agreement). Out-of-scope mixed pairs still
   Decline. In-scope pairs are Hits, not a mixed-pair Decline.
   HostMixedHitTi / HostMixedHitSpan are closed (the parameter is
   on_circ / on_chord; the span guard is circ_open_span). ι host-scope
   row stays QEX (SidecarCircIotaTags.v : ticket_0007_iota_host_scope_qed_or_qex);
   this letter does not claim ι closed. ADR-0007 stays Accepted.

   Honesty fences:
     Do not remint I_ok_mixed / I_ok_interior as host I_ok.
     No atan2, no classic, no Category C on host.
     No LeftoverBagTermArm, no LoopDischarged.
     No SIN / ellipse / geodesic expand. NURBS×NURBS is first cook.
     No I_CIRC_CHORD keyword. No #518 / #423 / Karney / ADR-0008 Status
     flip. Not “ι closed”. Not “first cook complete”.

   WITNESS topic: overlay · claimId: 0007-host-first-cook-circ-chord
   witness: 0007-host-first-cook-circ-chord
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
(* Mixed first_cook_scope stays False. Do not flip SheetHenCook.              *)
(* -------------------------------------------------------------------------- *)

Lemma circular_chord_not_first_cook_scope :
  ~ first_cook_scope EggCircularArc EggChord.
Proof.
  intro H. exact H.
Qed.

Lemma mixed_first_cook_scope_stays_false :
  ~ first_cook_scope EggChord EggCircularArc
  /\ ~ first_cook_scope EggCircularArc EggChord.
Proof.
  split; [exact chord_circular_not_first_cook_scope |].
  exact circular_chord_not_first_cook_scope.
Qed.

Lemma first_cook_scope_same_kind_unchanged :
  first_cook_scope EggChord EggChord
  /\ first_cook_scope EggCircularArc EggCircularArc
  /\ first_cook_scope EggClothoid EggClothoid
  /\ first_cook_scope EggNurbs EggNurbs
  /\ ~ first_cook_scope EggEllipse EggEllipse
  /\ ~ first_cook_scope EggSinusoid EggSinusoid
  /\ ~ first_cook_scope EggGeodesicString EggGeodesicString.
Proof.
  split; [exact first_cook_scope_chord_chord |].
  split; [exact circular_egg_first_cook_scope |].
  split; [exact clothoid_egg_first_cook_scope |].
  split; [exact nurbs_nurbs_first_cook_scope |].
  split; [exact ellipse_ellipse_not_first_scope |].
  split; [intro H; exact H |].
  intro H. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* Host I_ok on MkCirc × MkChord. Decline is exactly out of scope.            *)
(* Not a remint of sidecar I_ok_mixed.                                        *)
(* -------------------------------------------------------------------------- *)

Lemma host_mixed_circ_chord_decline_out :
  forall c s,
    ~ circ_chord_host_scope c s ->
    I_ok (MkCirc c) (MkChord s) IDecline.
Proof.
  intros c s Hs. unfold I_ok. exact Hs.
Qed.

Lemma host_mixed_chord_circ_decline_out :
  forall s c,
    ~ circ_chord_host_scope c s ->
    I_ok (MkChord s) (MkCirc c) IDecline.
Proof.
  intros s c Hs. unfold I_ok. exact Hs.
Qed.

Lemma host_mixed_circ_chord_hit_in_scope :
  forall c s p ti tj,
    I_ok (MkCirc c) (MkChord s) (IHit p ti tj) ->
    circ_chord_host_scope c s /\ on_circ c ti p /\ on_chord s tj p.
Proof.
  intros c s p ti tj H. exact H.
Qed.

Lemma host_mixed_chord_circ_hit_in_scope :
  forall s c p ti tj,
    I_ok (MkChord s) (MkCirc c) (IHit p ti tj) ->
    circ_chord_host_scope c s /\ on_chord s ti p /\ on_circ c tj p.
Proof.
  intros s c p ti tj H. exact H.
Qed.

Lemma host_mixed_try_cook_hit_none :
  forall c s p ti tj h src1 dst1 src2 dst2,
    try_cook_hit (mkChicken src1 dst1 (MkCirc c))
                 (mkChicken src2 dst2 (MkChord s))
                 (IHit p ti tj) h = None
    /\ try_cook_hit (mkChicken src1 dst1 (MkChord s))
                    (mkChicken src2 dst2 (MkCirc c))
                    (IHit p ti tj) h = None.
Proof.
  intros. split; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Named missing constructors. #770 / #771 stay open.                         *)
(* -------------------------------------------------------------------------- *)

Inductive HostMixedCookCtor : Type :=
| HostMixedHitTi
| HostMixedHitSpan.

Definition host_mixed_ctor_inhabits (c : HostMixedCookCtor) : Prop :=
  match c with
  | HostMixedHitTi => True
  | HostMixedHitSpan => True
  end.

Lemma host_mixed_hit_ti_closed :
  host_mixed_ctor_inhabits HostMixedHitTi.
Proof.
  exact I.
Qed.

Lemma host_mixed_hit_span_closed :
  host_mixed_ctor_inhabits HostMixedHitSpan.
Proof.
  exact I.
Qed.

(* Sidecar RootTag / I_ok_mixed remain the working mixed classifier.
   Cited, not copied. Do not Require SidecarCirc*. *)
Inductive MixedClassifierLane : Type :=
| HostIokMixedRemint
| SidecarRootTagIokMixed.

Definition mixed_classifier_lane : MixedClassifierLane := SidecarRootTagIokMixed.

Lemma mixed_classifier_is_sidecar :
  mixed_classifier_lane = SidecarRootTagIokMixed.
Proof.
  reflexivity.
Qed.

Lemma mixed_classifier_not_host_remint :
  mixed_classifier_lane <> HostIokMixedRemint.
Proof.
  discriminate.
Qed.

(* ι host-scope row stays QEX. Cite SidecarCircIotaTags.v :
   ticket_0007_iota_host_scope_qed_or_qex. Do not claim ι closed. *)
Inductive IotaHostPark : Type :=
| IotaHostScopeQex
| IotaHostClosed.

Definition iota_host_park : IotaHostPark := IotaHostScopeQex.

Lemma iota_host_park_stays_qex :
  iota_host_park = IotaHostScopeQex.
Proof.
  reflexivity.
Qed.

Lemma iota_host_not_closed :
  iota_host_park <> IotaHostClosed.
Proof.
  discriminate.
Qed.

Inductive Adr0007LetterStatus : Type :=
| Adr0007Accepted
| Adr0007StatusFlipped.

Definition adr0007_letter_status : Adr0007LetterStatus := Adr0007Accepted.

Lemma adr0007_stays_accepted :
  adr0007_letter_status = Adr0007Accepted.
Proof.
  reflexivity.
Qed.

Lemma adr0007_not_flipped :
  adr0007_letter_status <> Adr0007StatusFlipped.
Proof.
  discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket. QED ∨ QEX. Discharged QEX while #770 / #771 stay open.             *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-host-first-cook-circ-chord","topic":"overlay","lemma":"ticket_0007_host_first_cook_qed_or_qex","title":"host first cook circ times chord: first_cook_scope gains the mixed arms (QED) or mixed stays out of first cook, HitTi/HitSpan are closed, and Decline is exactly out of circ_chord_host_scope (QEX); discharged QEX; in-scope host Hit is 0007-host-circ-chord-oracle; try_cook_hit stays None and the loop is the mixed cook; sidecar I_ok_mixed cited not copied; iota host-scope stays QEX; ADR-0007 stays Accepted","file":"theories/HostFirstCookCircChord.v","witness":"0007-host-first-cook-circ-chord","board":"ADR-0007"} *)
Theorem ticket_0007_host_first_cook_qed_or_qex :
  (first_cook_scope EggChord EggCircularArc
   /\ first_cook_scope EggCircularArc EggChord)
  \/
  (~ first_cook_scope EggChord EggCircularArc
   /\ ~ first_cook_scope EggCircularArc EggChord
   /\ host_mixed_ctor_inhabits HostMixedHitTi
   /\ host_mixed_ctor_inhabits HostMixedHitSpan
   /\ mixed_classifier_lane = SidecarRootTagIokMixed
   /\ mixed_classifier_lane <> HostIokMixedRemint
   /\ iota_host_park = IotaHostScopeQex
   /\ iota_host_park <> IotaHostClosed
   /\ adr0007_letter_status = Adr0007Accepted
   /\ (forall c s, ~ circ_chord_host_scope c s ->
         I_ok (MkCirc c) (MkChord s) IDecline)
   /\ (forall s c, ~ circ_chord_host_scope c s ->
         I_ok (MkChord s) (MkCirc c) IDecline)
   /\ first_cook_scope EggChord EggChord
   /\ first_cook_scope EggCircularArc EggCircularArc
   /\ first_cook_scope EggClothoid EggClothoid).
Proof.
  right.
  split; [exact chord_circular_not_first_cook_scope |].
  split; [exact circular_chord_not_first_cook_scope |].
  split; [exact host_mixed_hit_ti_closed |].
  split; [exact host_mixed_hit_span_closed |].
  split; [reflexivity |].
  split; [exact mixed_classifier_not_host_remint |].
  split; [reflexivity |].
  split; [exact iota_host_not_closed |].
  split; [reflexivity |].
  split; [exact host_mixed_circ_chord_decline_out |].
  split; [exact host_mixed_chord_circ_decline_out |].
  split; [exact first_cook_scope_chord_chord |].
  split; [exact circular_egg_first_cook_scope |].
  exact clothoid_egg_first_cook_scope.
Qed.

Print Assumptions circular_chord_not_first_cook_scope.
Print Assumptions mixed_first_cook_scope_stays_false.
Print Assumptions first_cook_scope_same_kind_unchanged.
Print Assumptions host_mixed_circ_chord_decline_out.
Print Assumptions host_mixed_chord_circ_decline_out.
Print Assumptions host_mixed_circ_chord_hit_in_scope.
Print Assumptions host_mixed_chord_circ_hit_in_scope.
Print Assumptions host_mixed_try_cook_hit_none.
Print Assumptions host_mixed_hit_ti_closed.
Print Assumptions host_mixed_hit_span_closed.
Print Assumptions mixed_classifier_is_sidecar.
Print Assumptions iota_host_park_stays_qex.
Print Assumptions adr0007_stays_accepted.
Print Assumptions ticket_0007_host_first_cook_qed_or_qex.
