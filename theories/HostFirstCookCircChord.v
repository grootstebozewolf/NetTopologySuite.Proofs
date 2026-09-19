(* ============================================================================
   NetTopologySuite.Proofs.HostFirstCookCircChord
   ----------------------------------------------------------------------------
   ADR-0007 host first-cook circ×chord letter
   (claimId 0007-host-first-cook-circ-chord-qed).
   Circ×chord / chord×circ on the host cook, not a sidecar remint.

   QED: host I_ok Hit on (MkCirc c, MkChord s) inhabited as
   IHit p ti tj with on_circ c ti p ∧ on_chord s tj p on the locked
   quarter-circle × x=y fixture (and the swap). ti = 1/2 is egg-data
   sweep fraction (shape C / #770), not atan2. Sweep is π/2, not ±2π
   (#771). first_cook_scope has exactly the two mixed arms.
   HostMixedHitTi and HostMixedHitSpan inhabit.
   Cook step, Touch, MintTwo, tag-Decline live in HostCookCircChord.v.

   Sidecar RootTag / I_ok_mixed remain the working mixed classifier
   for tags / joints (SidecarCircIotaArm / SidecarCircMixed). Cited,
   not copied, not Required — sidecar is 4-axiom / Category C.
   I_ok_mixed / I_ok_interior Hit is not host I_ok.

   ι host-scope row stays QEX (SidecarCircIotaTags.v :
   ticket_0007_iota_host_scope_qed_or_qex). This letter does not
   claim ι closed. ADR-0007 stays Accepted.

   Honesty fences:
     Do not remint I_ok_mixed / I_ok_interior as host I_ok.
     No atan2, no classic, no Category C on host.
     No LeftoverBagTermArm, no LoopDischarged.
     No NURBS / SIN / ellipse / geodesic in first_cook_scope.
     No I_CIRC_CHORD keyword. No #518 / #423 / Karney / ADR-0008 Status
     flip. Not “ι closed”. Not “first cook complete”.

   WITNESS topic: overlay · claimId: 0007-host-first-cook-circ-chord-qed
   witness: 0007-host-first-cook-circ-chord-qed
   board: ADR-0007
   3-axiom. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import Distance SheetHenCook HostCookCircChord.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Mixed first_cook_scope is True. Same-kind first cook unchanged.            *)
(* -------------------------------------------------------------------------- *)

Lemma circular_chord_first_cook_scope :
  first_cook_scope EggCircularArc EggChord.
Proof.
  exact first_cook_scope_circular_chord.
Qed.

Lemma mixed_first_cook_scope_both :
  first_cook_scope EggChord EggCircularArc
  /\ first_cook_scope EggCircularArc EggChord.
Proof.
  split; [exact first_cook_scope_chord_circular |].
  exact first_cook_scope_circular_chord.
Qed.

Lemma first_cook_scope_same_kind_unchanged :
  first_cook_scope EggChord EggChord
  /\ first_cook_scope EggCircularArc EggCircularArc
  /\ first_cook_scope EggClothoid EggClothoid
  /\ ~ first_cook_scope EggNurbs EggNurbs
  /\ ~ first_cook_scope EggEllipse EggEllipse
  /\ ~ first_cook_scope EggSinusoid EggSinusoid
  /\ ~ first_cook_scope EggGeodesicString EggGeodesicString.
Proof.
  split; [exact first_cook_scope_chord_chord |].
  split; [exact circular_egg_first_cook_scope |].
  split; [exact clothoid_egg_first_cook_scope |].
  split; [exact nurbs_nurbs_not_first_scope |].
  split; [exact ellipse_ellipse_not_first_scope |].
  split; [intro H; exact H |].
  intro H. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* Named constructors. #770 / #771 discharged by the locked fixture.          *)
(* -------------------------------------------------------------------------- *)

Inductive HostMixedCookCtor : Type :=
| HostMixedHitTi
| HostMixedHitSpan.

Definition host_mixed_ctor_inhabits (c : HostMixedCookCtor) : Prop :=
  match c with
  | HostMixedHitTi =>
      exists circ chord p ti tj,
        I_ok (MkCirc circ) (MkChord chord) (IHit p ti tj)
        /\ on_circ circ ti p /\ on_chord chord tj p
  | HostMixedHitSpan =>
      exists circ chord p ti tj,
        I_ok (MkCirc circ) (MkChord chord) (IHit p ti tj)
        /\ on_circ circ ti p /\ on_chord chord tj p
        /\ circ_sweep circ <> 2 * PI
        /\ circ_sweep circ <> - (2 * PI)
  end.

Lemma host_mixed_hit_ti_inhabits :
  host_mixed_ctor_inhabits HostMixedHitTi.
Proof.
  exists mixed_circ, mixed_chord, mixed_hit_pt, mixed_ti, mixed_tj.
  split; [exact mixed_circ_chord_I_ok|].
  split; [exact mixed_on_circ | exact mixed_on_chord].
Qed.

Lemma host_mixed_hit_span_inhabits :
  host_mixed_ctor_inhabits HostMixedHitSpan.
Proof.
  exists mixed_circ, mixed_chord, mixed_hit_pt, mixed_ti, mixed_tj.
  split; [exact mixed_circ_chord_I_ok|].
  split; [exact mixed_on_circ|].
  split; [exact mixed_on_chord|].
  exact mixed_sweep_not_full.
Qed.

(* Sidecar RootTag / I_ok_mixed remain the working mixed classifier
   for tags / joints. Cited, not copied. Do not Require SidecarCirc*. *)
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
(* Ticket. QED ∨ QEX. Discharged QED: mixed arms + constructed Hit.           *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-host-first-cook-circ-chord-qed","topic":"overlay","lemma":"ticket_0007_host_first_cook_qed_or_qex","title":"host first cook circ times chord: first_cook_scope mixed arms plus host I_ok Hit on MkCirc times MkChord with on_circ / on_chord (QED) or mixed stays out of first cook with named HostMixedHitTi / HostMixedHitSpan gaps (QEX); discharged QED; sidecar I_ok_mixed cited not copied; iota host-scope stays QEX; ADR-0007 stays Accepted","file":"theories/HostFirstCookCircChord.v","witness":"0007-host-first-cook-circ-chord-qed","board":"ADR-0007"} *)
Theorem ticket_0007_host_first_cook_qed_or_qex :
  (first_cook_scope EggChord EggCircularArc
   /\ first_cook_scope EggCircularArc EggChord
   /\ host_mixed_ctor_inhabits HostMixedHitTi
   /\ host_mixed_ctor_inhabits HostMixedHitSpan
   /\ exists c s p ti tj,
        I_ok (MkCirc c) (MkChord s) (IHit p ti tj)
        /\ on_circ c ti p /\ on_chord s tj p)
  \/
  (~ first_cook_scope EggChord EggCircularArc
   /\ ~ first_cook_scope EggCircularArc EggChord
   /\ ~ host_mixed_ctor_inhabits HostMixedHitTi
   /\ ~ host_mixed_ctor_inhabits HostMixedHitSpan
   /\ mixed_classifier_lane = SidecarRootTagIokMixed
   /\ mixed_classifier_lane <> HostIokMixedRemint
   /\ iota_host_park = IotaHostScopeQex
   /\ iota_host_park <> IotaHostClosed
   /\ adr0007_letter_status = Adr0007Accepted
   /\ (forall c s, I_ok (MkCirc c) (MkChord s) IDecline)
   /\ (forall s c, I_ok (MkChord s) (MkCirc c) IDecline)
   /\ (forall c s p ti tj, ~ I_ok (MkCirc c) (MkChord s) (IHit p ti tj))
   /\ (forall s c p ti tj, ~ I_ok (MkChord s) (MkCirc c) (IHit p ti tj))
   /\ first_cook_scope EggChord EggChord
   /\ first_cook_scope EggCircularArc EggCircularArc
   /\ first_cook_scope EggClothoid EggClothoid).
Proof.
  left.
  split; [exact first_cook_scope_chord_circular |].
  split; [exact first_cook_scope_circular_chord |].
  split; [exact host_mixed_hit_ti_inhabits |].
  split; [exact host_mixed_hit_span_inhabits |].
  exists mixed_circ, mixed_chord, mixed_hit_pt, mixed_ti, mixed_tj.
  split; [exact mixed_circ_chord_I_ok|].
  split; [exact mixed_on_circ | exact mixed_on_chord].
Qed.

Print Assumptions circular_chord_first_cook_scope.
Print Assumptions mixed_first_cook_scope_both.
Print Assumptions first_cook_scope_same_kind_unchanged.
Print Assumptions host_mixed_hit_ti_inhabits.
Print Assumptions host_mixed_hit_span_inhabits.
Print Assumptions mixed_classifier_is_sidecar.
Print Assumptions iota_host_park_stays_qex.
Print Assumptions adr0007_stays_accepted.
Print Assumptions ticket_0007_host_first_cook_qed_or_qex.
