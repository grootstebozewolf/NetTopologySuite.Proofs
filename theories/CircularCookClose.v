(* ============================================================================
   NetTopologySuite.Proofs.CircularCookClose
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: I.10 Campaign-I close letter.

   Campaign I is the circular sidecar cook programme on Accepted
   ADR-0007 (#666 + #686–#692). This letter tickets the close. It
   does not start Campaign II or H⊥. It does not remint a kernel.
   II.1 (later letter) lives in CircularCookSpanFilter.v.

   QED: sidecar cook exists on a constructed circular Hit (both
   radical roots / MintTwo); I_CIRCULAR stays a classifier (tags
   0/1); the #666 four-object fence holds by observation.
   QEX: host CircGamma stays QEX; first_cook_scope stays
   chord–chord; Campaign II and H⊥ are named parked; SQL/MM is
   not done.

   Honesty fences:
     I_circles_z ≠ I_circles_gamma ≠ sidecar cook ≠ glossary 𝓘.
     Not first cook scope. Not a noder. Not ArcSplitAtNode.
     Not a remint of CurveSegment / Exact* / Dart / Hobby /
     leftover_width / ArcSplitAtNode leftover-width.
     Do not fake atan2-free host γ.
     Do not start Campaign II / H⊥ / a CRV-TOUCH kiss procedure.
     No new kernel. Not SQL/MM done.

   WITNESS topic: overlay · claimId: 0007
   witness: 0007-I.10-campaign-i-close
   board: ADR-0007
   4-axiom (atan2 / Classical_Prop.classic via CircularCookSplit).
   No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import ZArith Reals.
(* CircularCookHit is required for locked_O1 / locked_O2 / locked_r /
   locked_p_plus / locked_p_minus. CircularCookSplit Imports Hit and
   does not Export those witnesses. CircularCookLicense exports the
   I.9 tag lemmas. *)
From NTS.Proofs Require Import Distance SheetHenCook CircularCookZ
  CircularCook CircularCookHit CircularCookSplit CircularCookLicense.
Local Open Scope R_scope.

(* WITNESS: campaign=I rung=I.10 claim=0007
   file=theories/CircularCookClose.v
   kind=QED-or-QEX-campaign-I-close-letter
   not=new-kernel,CircGamma-Discharge,first-cook-noding,SQL-MM-done
   park=Campaign-II,Hperp *)

(* -------------------------------------------------------------------------- *)
(* Named parks. Campaign II and H⊥ are named here so they are not            *)
(* silently treated as done. SQL/MM is named not-done. These are             *)
(* honesty flags, not a kernel and not a cook.                               *)
(* -------------------------------------------------------------------------- *)

Inductive CampaignIIStatus : Type :=
| CampaignIIDischarged
| CampaignIIParked.

Definition campaign_ii_status : CampaignIIStatus := CampaignIIParked.

Lemma campaign_ii_is_parked :
  campaign_ii_status = CampaignIIParked.
Proof.
  reflexivity.
Qed.

Inductive HperpStatus : Type :=
| HperpDischarged
| HperpParked.

Definition hperp_status : HperpStatus := HperpParked.

Lemma hperp_is_parked :
  hperp_status = HperpParked.
Proof.
  reflexivity.
Qed.

Inductive SqlMmStatus : Type :=
| SqlMmDone
| SqlMmNotDone.

Definition sql_mm_status : SqlMmStatus := SqlMmNotDone.

Lemma sql_mm_is_not_done :
  sql_mm_status = SqlMmNotDone.
Proof.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Landed Campaign I facts, composed — no new cook.                           *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"i10_sidecar_cook_both_roots","title":"I.10 sidecar cook exists on constructed circular Hit both radical roots MintTwo; CircGamma stays QEX","file":"theories/CircularCookClose.v","witness":"0007-I.10-campaign-i-close","board":"ADR-0007"} *)

Lemma i10_sidecar_cook_both_roots :
  try_cook_circ_hit_mint_two locked_O1 locked_r locked_O2 locked_r
    (I_circles_gamma 0 0 5 7 0 5) = Some cooked_circ_mint_two
  /\ circ_mint_two_ok cooked_circ_mint_two
       hen_plus hen_minus locked_p_plus locked_p_minus
  /\ circular_gamma_status = CircGammaQEX.
Proof.
  split; [exact cooked_circ_mint_two_try|].
  split; [exact cooked_circ_mint_two_ok|].
  exact circular_gamma_is_qex.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"i10_classifier_stays_tags","title":"I.10 I_CIRCULAR / I_circles_z Hit stays tags 0/1, not (p*, t_i, t_j)","file":"theories/CircularCookClose.v","witness":"0007-I.10-campaign-i-close","board":"ADR-0007"} *)

Lemma i10_classifier_stays_tags :
  hen_plus = 0%nat /\ hen_minus = 1%nat
  /\ I_circles_z 0 0 5 7 0 5 = IZHit 0%nat 1%nat.
Proof.
  (* hen_plus := 0, hen_minus := 1. Do not rewrite 0%nat — that
     rewrites the 0 inside 1%nat (= S 0) and leaves no 1%nat. *)
  destruct classifier_hens_are_tags as [Hp Hm].
  split; [exact Hp|].
  split; [exact Hm|].
  exact i9_locked_z_hit_is_tags.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"i10_fence_holds","title":"I.10 #666 fence holds: Z classifier ≠ gamma Hit ≠ sidecar cook ≠ host I_gloss","file":"theories/CircularCookClose.v","witness":"0007-I.10-campaign-i-close","board":"ADR-0007"} *)

Lemma i10_fence_holds :
  I_circles_z 0 0 5 7 0 5 = IZHit hen_plus hen_minus
  /\ I_circles_gamma 0 0 5 7 0 5 =
       ICircGHit hen_plus locked_p_plus
         (circ_t locked_O1 locked_p_plus) (circ_t locked_O2 locked_p_plus)
         hen_minus locked_p_minus
         (circ_t locked_O1 locked_p_minus) (circ_t locked_O2 locked_p_minus)
  /\ try_cook_circ_hit_mint_two locked_O1 locked_r locked_O2 locked_r
       (I_circles_gamma 0 0 5 7 0 5) = Some cooked_circ_mint_two
  /\ (forall p ti tj h,
        try_cook_hit circular_ck1 circular_ck2 (IHit p ti tj) h = None)
  /\ circular_gamma_status = CircGammaQEX.
Proof.
  destruct i1_z_neq_gamma_obs as [Hz [Hg _]].
  destruct i1_sidecar_neq_gloss_obs as [Hc [Hh Hq]].
  split; [exact Hz|].
  split; [exact Hg|].
  split; [exact Hc|].
  split; [exact Hh|].
  exact Hq.
Qed.

Lemma i10_host_stays_qex :
  circular_gamma_status = CircGammaQEX
  /\ ~ first_cook_scope EggCircularArc EggCircularArc
  /\ first_cook_scope EggChord EggChord.
Proof.
  split; [exact circular_gamma_is_qex|].
  split; [exact circular_not_first_cook_scope|].
  exact first_cook_scope_chord_chord.
Qed.

Lemma i10_parks_named :
  campaign_ii_status = CampaignIIParked
  /\ hperp_status = HperpParked
  /\ sql_mm_status = SqlMmNotDone.
Proof.
  split; [exact campaign_ii_is_parked|].
  split; [exact hperp_is_parked|].
  exact sql_mm_is_not_done.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_i10_sidecar_qed_or_qex","title":"I.10 sidecar cook exists on constructed circular Hit both roots (QED) or MintTwo declines the locked Hit (QEX); discharged QED; CircGamma stays QEX","file":"theories/CircularCookClose.v","witness":"0007-I.10-campaign-i-close","board":"ADR-0007"} *)

Theorem ticket_0007_i10_sidecar_qed_or_qex :
  (try_cook_circ_hit_mint_two locked_O1 locked_r locked_O2 locked_r
     (I_circles_gamma 0 0 5 7 0 5) = Some cooked_circ_mint_two
   /\ circ_mint_two_ok cooked_circ_mint_two
        hen_plus hen_minus locked_p_plus locked_p_minus
   /\ circular_gamma_status = CircGammaQEX)
  \/
  try_cook_circ_hit_mint_two locked_O1 locked_r locked_O2 locked_r
    (I_circles_gamma 0 0 5 7 0 5) = None.
Proof.
  left.
  exact i10_sidecar_cook_both_roots.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_i10_classifier_qed_or_qex","title":"I.10 I_CIRCULAR stays a classifier and the #666 fence holds (QED) or a Z Hit mints some other hen (QEX); discharged QED; tags 0/1 are not a cook","file":"theories/CircularCookClose.v","witness":"0007-I.10-campaign-i-close","board":"ADR-0007"} *)

Theorem ticket_0007_i10_classifier_qed_or_qex :
  (hen_plus = 0%nat /\ hen_minus = 1%nat
   /\ I_circles_z 0 0 5 7 0 5 = IZHit 0%nat 1%nat
   /\ I_circles_z 0 0 5 7 0 5 = IZHit hen_plus hen_minus
   /\ I_circles_gamma 0 0 5 7 0 5 =
        ICircGHit hen_plus locked_p_plus
          (circ_t locked_O1 locked_p_plus) (circ_t locked_O2 locked_p_plus)
          hen_minus locked_p_minus
          (circ_t locked_O1 locked_p_minus) (circ_t locked_O2 locked_p_minus)
   /\ try_cook_circ_hit_mint_two locked_O1 locked_r locked_O2 locked_r
        (I_circles_gamma 0 0 5 7 0 5) = Some cooked_circ_mint_two
   /\ (forall p ti tj h,
         try_cook_hit circular_ck1 circular_ck2 (IHit p ti tj) h = None)
   /\ circular_gamma_status = CircGammaQEX)
  \/
  (exists hp hm,
     I_circles_z 0 0 5 7 0 5 = IZHit hp hm
     /\ (hp <> 0%nat \/ hm <> 1%nat)).
Proof.
  left.
  destruct i10_classifier_stays_tags as [Hp [Hm Hz]].
  destruct i10_fence_holds as [Hf [Hg [Hc [Hh Hq]]]].
  split; [exact Hp|].
  split; [exact Hm|].
  split; [exact Hz|].
  split; [exact Hf|].
  split; [exact Hg|].
  split; [exact Hc|].
  split; [exact Hh|].
  exact Hq.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_i10_host_qed_or_qex","title":"I.10 discharges CircGamma and expands first cook scope (QED) or CircGamma stays QEX and first cook stays chord-chord (QEX); discharged QEX; not Campaign II","file":"theories/CircularCookClose.v","witness":"0007-I.10-campaign-i-close","board":"ADR-0007"} *)

Theorem ticket_0007_i10_host_qed_or_qex :
  (circular_gamma_status = CircGammaDischarged
   /\ first_cook_scope EggCircularArc EggCircularArc)
  \/
  (circular_gamma_status = CircGammaQEX
   /\ ~ first_cook_scope EggCircularArc EggCircularArc
   /\ first_cook_scope EggChord EggChord).
Proof.
  right.
  exact i10_host_stays_qex.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_i10_park_qed_or_qex","title":"I.10 discharges Campaign II, Hperp, and SQL/MM (QED) or names them parked / not-done (QEX); discharged QEX; no new kernel","file":"theories/CircularCookClose.v","witness":"0007-I.10-campaign-i-close","board":"ADR-0007"} *)

Theorem ticket_0007_i10_park_qed_or_qex :
  (campaign_ii_status = CampaignIIDischarged
   /\ hperp_status = HperpDischarged
   /\ sql_mm_status = SqlMmDone)
  \/
  (campaign_ii_status = CampaignIIParked
   /\ hperp_status = HperpParked
   /\ sql_mm_status = SqlMmNotDone).
Proof.
  right.
  exact i10_parks_named.
Qed.

Print Assumptions campaign_ii_is_parked.
Print Assumptions hperp_is_parked.
Print Assumptions sql_mm_is_not_done.
Print Assumptions i10_sidecar_cook_both_roots.
Print Assumptions i10_classifier_stays_tags.
Print Assumptions i10_fence_holds.
Print Assumptions i10_host_stays_qex.
Print Assumptions i10_parks_named.
Print Assumptions ticket_0007_i10_sidecar_qed_or_qex.
Print Assumptions ticket_0007_i10_classifier_qed_or_qex.
Print Assumptions ticket_0007_i10_host_qed_or_qex.
Print Assumptions ticket_0007_i10_park_qed_or_qex.
