(* ============================================================================
   NetTopologySuite.Proofs.HostNoIOkMixedRemint
   ----------------------------------------------------------------------------
   ADR-0007 remint fence (claimId 0007-no-i-ok-mixed-remint).
   Sidecar I_ok_mixed Hit is not host I_ok. No new cook.

   Sidecar mixed cook inhabits Hit on circ×chord
   (SidecarCircMixed.v : locked_mixed_cs_ls_I_ok_mixed). Host I_ok
   (MkCirc c) (MkChord s) inhabits IDecline only. first_cook_scope
   mixed arms stay False. ι host-scope stays QEX
   (SidecarCircIotaTags.v : ticket_0007_iota_host_scope_qed_or_qex).

   Host Decline on MkCirc × MkChord is restated from PR #796
   (HostFirstCookCircChord.v : host_mixed_circ_chord_decline /
   host_mixed_circ_chord_hit_false), not reminted. #796 is not
   merged. HostMixedHitTi / HostMixedHitSpan stay uninhabited.

   QED: MixedSidecarNotHostIOk — on the locked circ×chord fixture
   ~ (I_ok_mixed → I_ok) and
   I_ok (MkCirc c) (MkChord s) r → r = IDecline.
   ticket_0007_no_i_ok_mixed_remint_qed_or_qex takes LEFT because
   that fence is inhabited, not because first_cook_scope grew.

   QEX: MixedSidecarDistinct — I_ok_mixed definitionally I_ok, or a
   coercion identifies them. They do not collapse (different types;
   host Hit stays False). Do not “fix” collapse by making host I_ok
   accept Hit.

   Honesty fences:
     Do not remint I_ok_mixed / I_ok_interior as host I_ok.
     Do not expand first_cook_scope.
     Do not inhabit HostMixedHitTi / HostMixedHitSpan.
     No LeftoverBagTermArm / Hobby / Karney.
     Not “ι closed”. ADR-0007 stays Accepted.

   WITNESS topic: overlay · claimId: 0007-no-i-ok-mixed-remint
   witness: 0007-no-i-ok-mixed-remint
   board: ADR-0007
   Host Decline lemmas are 3-axiom. The named fence reuses sidecar
   I_ok_mixed Hit (4-axiom atan2 / classic via SidecarCircMixed).
   Category C: same lineage as SidecarCircMixed; no extra axioms.
   No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import Distance SheetHenCook.
From NTS.Proofs Require SidecarCircMixed.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* #796 restatement. Host I_ok on MkCirc × MkChord is Decline only.           *)
(* -------------------------------------------------------------------------- *)

Definition locked_host_circ : CircularEgg :=
  mkCircularEgg (mkPoint 0 0) 5 0 (-PI).

Definition locked_host_chord : ChordEgg :=
  SidecarCircMixed.locked_mixed_ls.

Lemma host_mixed_circ_chord_decline :
  forall c s, I_ok (MkCirc c) (MkChord s) IDecline.
Proof.
  intros c s.
  unfold I_ok, interpolant_pair.
  intro H. exact H.
Qed.

Lemma host_mixed_chord_circ_decline :
  forall s c, I_ok (MkChord s) (MkCirc c) IDecline.
Proof.
  intros s c.
  unfold I_ok, interpolant_pair.
  intro H. exact H.
Qed.

Lemma host_mixed_circ_chord_hit_false :
  forall c s p ti tj,
    ~ I_ok (MkCirc c) (MkChord s) (IHit p ti tj).
Proof.
  intros c s p ti tj H. exact H.
Qed.

Lemma host_mixed_circ_chord_empty_false :
  forall c s, ~ I_ok (MkCirc c) (MkChord s) IEmpty.
Proof.
  intros c s H. exact H.
Qed.

Lemma host_mixed_circ_chord_result_is_decline :
  forall c s r, I_ok (MkCirc c) (MkChord s) r -> r = IDecline.
Proof.
  intros c s [p ti tj | | ] H.
  - exfalso; exact H.
  - exfalso; exact H.
  - reflexivity.
Qed.

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

(* -------------------------------------------------------------------------- *)
(* Collapse ctor. Uninhabited: I_ok_mixed is not host I_ok.                   *)
(* -------------------------------------------------------------------------- *)

Inductive MixedSidecarCollapseCtor : Type :=
| MixedSidecarDistinct.

Definition mixed_sidecar_collapse_inhabits
  (c : MixedSidecarCollapseCtor) : Prop :=
  match c with
  | MixedSidecarDistinct => False
  end.

Lemma mixed_sidecar_not_definitionally_collapsed :
  ~ mixed_sidecar_collapse_inhabits MixedSidecarDistinct.
Proof.
  intro H. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* Named fence. Locked MixCsLs Hit does not transport to host I_ok.           *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-no-i-ok-mixed-remint","topic":"overlay","lemma":"MixedSidecarNotHostIOk","title":"sidecar I_ok_mixed does not imply host I_ok on the locked circ times chord fixture; host I_ok MkCirc times MkChord inhabits only IDecline; restated from PR 796; not a remint; first_cook_scope mixed arms stay False","file":"theories/HostNoIOkMixedRemint.v","witness":"0007-no-i-ok-mixed-remint","board":"ADR-0007"} *)
Theorem MixedSidecarNotHostIOk :
  ~ (forall r,
       SidecarCircMixed.I_ok_mixed
         (SidecarCircMixed.MixCsLs
            SidecarCircMixed.locked_mixed_cs
            SidecarCircMixed.locked_mixed_ls) r ->
       I_ok (MkCirc locked_host_circ) (MkChord locked_host_chord) r)
  /\
  (forall c s r, I_ok (MkCirc c) (MkChord s) r -> r = IDecline).
Proof.
  split.
  - intro Himpl.
    exact (Himpl (SidecarCircMixed.cs_ls_joint_hit
                    SidecarCircMixed.locked_mixed_cs
                    SidecarCircMixed.locked_mixed_ls)
                 SidecarCircMixed.locked_mixed_cs_ls_I_ok_mixed).
  - exact host_mixed_circ_chord_result_is_decline.
Qed.

(* WITNESS {"claimId":"0007-no-i-ok-mixed-remint","topic":"overlay","lemma":"ticket_0007_no_i_ok_mixed_remint_qed_or_qex","title":"no I_ok_mixed remint: MixedSidecarNotHostIOk on locked circ times chord (QED) or I_ok_mixed is definitionally I_ok / MixedSidecarDistinct (QEX); discharged QED because the fence is inhabited, not because first_cook_scope grew mixed arms; iota host-scope stays QEX; ADR-0007 stays Accepted","file":"theories/HostNoIOkMixedRemint.v","witness":"0007-no-i-ok-mixed-remint","board":"ADR-0007"} *)
Theorem ticket_0007_no_i_ok_mixed_remint_qed_or_qex :
  MixedSidecarNotHostIOk
  \/
  mixed_sidecar_collapse_inhabits MixedSidecarDistinct.
Proof.
  left.
  exact MixedSidecarNotHostIOk.
Qed.

Print Assumptions host_mixed_circ_chord_decline.
Print Assumptions host_mixed_circ_chord_result_is_decline.
Print Assumptions mixed_first_cook_scope_stays_false.
Print Assumptions mixed_sidecar_not_definitionally_collapsed.
Print Assumptions MixedSidecarNotHostIOk.
Print Assumptions ticket_0007_no_i_ok_mixed_remint_qed_or_qex.
