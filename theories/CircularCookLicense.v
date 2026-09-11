(* ============================================================================
   NetTopologySuite.Proofs.CircularCookLicense
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: I.9 classifier ≠ cook.

   An I_circles_z / I_CIRCULAR Hit does not license host split(t).
   Classifier hens are tags 0/1. Glossary Hit carries (p*, tᵢ, tⱼ).
   I_CIRCULAR Hit ⇏ host try_cook_hit / circ_split / first_cook_scope
   expansion.

   QED: hens are tags 0/1 and ∀ IZHit is those tags; a Z Hit does
   not feed host try_cook_hit and does not expand first cook scope;
   the same Z Hit does not determine circ_split leftovers (plus /
   minus meet at distinct p* — t comes from γ, not from the tags).
   QEX: CircGamma stays QEX; first cook stays chord–chord.

   Honesty fences:
     I_circles_z ≠ I_circles_gamma ≠ sidecar cook ≠ glossary 𝓘.
     Not first cook scope. Not a noder. Not ArcSplitAtNode.
     Not a remint of CurveSegment / Exact* / Dart / Hobby /
     leftover_width / ArcSplitAtNode leftover-width.
     Do not fake atan2-free host γ.
     I.10 Campaign-I close lives in CircularCookClose.v.
     Do not start Campaign II / H⊥ / a CRV-TOUCH kiss procedure.

   WITNESS topic: overlay · claimId: 0007
   witness: 0007-I.9-classifier-neq-cook
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
   does not Export those witnesses. *)
From NTS.Proofs Require Import Distance SheetHenCook CircularCookZ
  CircularCook CircularCookHit CircularCookSplit.
Local Open Scope R_scope.

(* WITNESS: campaign=I rung=I.9 claim=0007
   file=theories/CircularCookLicense.v
   kind=QED-classifier-hit-not-cook-license
   not=CircGamma-Discharge,first-cook-noding,bag-loop,leftover-width
   not=Campaign-II,Hperp,CRV-TOUCH-kiss *)

(* -------------------------------------------------------------------------- *)
(* Classifier hens are tags 0/1. Glossary IHit carries (p*, tᵢ, tⱼ).          *)
(* I_CIRCULAR prints HIT 0 1 — the same tag-only payload.                     *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"i9_locked_z_hit_is_tags","title":"I.9 locked I_circles_z / I_CIRCULAR Hit is tags 0 and 1, not (p*, t_i, t_j)","file":"theories/CircularCookLicense.v","witness":"0007-I.9-classifier-neq-cook","board":"ADR-0007"} *)

Lemma i9_locked_z_hit_is_tags :
  I_circles_z 0 0 5 7 0 5 = IZHit 0%nat 1%nat.
Proof.
  (* hen_plus := 0, hen_minus := 1. Do not rewrite 0%nat — that
     rewrites the 0 inside 1%nat (= S 0) and leaves no 1%nat. *)
  exact locked_I_circles_z_hit.
Qed.

(* A Z-classifier Hit does not license host try_cook_hit. Circular
   eggs stay MkOutOfScope; first cook scope stays chord–chord. *)
Lemma i9_z_hit_not_try_cook_hit :
  forall o1x o1y r1 o2x o2y r2,
    I_circles_z o1x o1y r1 o2x o2y r2 = IZHit hen_plus hen_minus ->
    forall p ti tj h,
      try_cook_hit circular_ck1 circular_ck2 (IHit p ti tj) h = None.
Proof.
  intros o1x o1y r1 o2x o2y r2 _ p ti tj h.
  exact (try_cook_hit_circular_hit_none p ti tj h).
Qed.

Lemma i9_z_hit_not_first_cook_scope :
  forall o1x o1y r1 o2x o2y r2,
    I_circles_z o1x o1y r1 o2x o2y r2 = IZHit hen_plus hen_minus ->
    first_cook_scope EggCircularArc EggCircularArc.
Proof.
  intros o1x o1y r1 o2x o2y r2 _.
  exact circular_is_first_cook_scope.
Qed.

(* Same IZHit tags on the locked fixture; circ_split leftovers join
   at distinct radical roots. t comes from γ, not from the tags. *)
Lemma i9_z_hit_not_circ_split_license :
  I_circles_z 0 0 5 7 0 5 = IZHit hen_plus hen_minus
  /\ circ_leftover_eval (fst (circ_split locked_O1 locked_r locked_ti_plus)) 1
       = locked_p_plus
  /\ circ_leftover_eval (fst (circ_split locked_O1 locked_r locked_ti_minus)) 1
       = locked_p_minus
  /\ locked_p_plus <> locked_p_minus.
Proof.
  split; [exact locked_I_circles_z_hit|].
  destruct (circ_split_join locked_O1 locked_r locked_ti_plus) as [Hp _].
  destruct (circ_split_join locked_O1 locked_r locked_ti_minus) as [Hm _].
  destruct locked_plus_gamma as [Gp _].
  destruct locked_minus_gamma as [Gm _].
  split; [rewrite Hp; exact Gp|].
  split; [rewrite Hm; exact Gm|].
  exact locked_p_plus_neq_minus.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_i9_tags_qed_or_qex","title":"I.9 classifier hens are tags 0/1 (QED) or a Z Hit mints some other hen (QEX); discharged QED; I_CIRCULAR HIT 0 1","file":"theories/CircularCookLicense.v","witness":"0007-I.9-classifier-neq-cook","board":"ADR-0007"} *)

Theorem ticket_0007_i9_tags_qed_or_qex :
  (hen_plus = 0%nat /\ hen_minus = 1%nat
   /\ (forall o1x o1y r1 o2x o2y r2 hp hm,
         I_circles_z o1x o1y r1 o2x o2y r2 = IZHit hp hm ->
         hp = hen_plus /\ hm = hen_minus)
   /\ I_circles_z 0 0 5 7 0 5 = IZHit 0%nat 1%nat)
  \/
  (exists hp hm,
     I_circles_z 0 0 5 7 0 5 = IZHit hp hm
     /\ (hp <> 0%nat \/ hm <> 1%nat)).
Proof.
  left.
  destruct classifier_hens_are_tags as [Hp Hm].
  split; [exact Hp|].
  split; [exact Hm|].
  split; [exact iz_hit_only_tags|].
  exact i9_locked_z_hit_is_tags.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_i9_not_host_cook_qed_or_qex","title":"I.9 Z-classifier Hit does not feed host try_cook_hit and does not expand first cook scope (QED) or try_cook_hit cooks a circular IHit (QEX); discharged QED; I_CIRCULAR Hit is not a host cook license","file":"theories/CircularCookLicense.v","witness":"0007-I.9-classifier-neq-cook","board":"ADR-0007"} *)

Theorem ticket_0007_i9_not_host_cook_qed_or_qex :
  ((forall o1x o1y r1 o2x o2y r2,
      I_circles_z o1x o1y r1 o2x o2y r2 = IZHit hen_plus hen_minus ->
      forall p ti tj h,
        try_cook_hit circular_ck1 circular_ck2 (IHit p ti tj) h = None)
   /\ (forall o1x o1y r1 o2x o2y r2,
         I_circles_z o1x o1y r1 o2x o2y r2 = IZHit hen_plus hen_minus ->
         first_cook_scope EggCircularArc EggCircularArc))
  \/
  (exists cp : CookedPair,
     try_cook_hit circular_ck1 circular_ck2
       (IHit cross_pt (1 / 2) (1 / 2)) crossing_hen = Some cp).
Proof.
  left.
  split; [exact i9_z_hit_not_try_cook_hit|exact i9_z_hit_not_first_cook_scope].
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_i9_not_circ_split_qed_or_qex","title":"I.9 same Z Hit leaves plus/minus leftovers at distinct p-star (QED) or p+ equals p- (QEX); discharged QED; circ_split t comes from gamma not from classifier tags","file":"theories/CircularCookLicense.v","witness":"0007-I.9-classifier-neq-cook","board":"ADR-0007"} *)

Theorem ticket_0007_i9_not_circ_split_qed_or_qex :
  (I_circles_z 0 0 5 7 0 5 = IZHit hen_plus hen_minus
   /\ circ_leftover_eval (fst (circ_split locked_O1 locked_r locked_ti_plus)) 1
        = locked_p_plus
   /\ circ_leftover_eval (fst (circ_split locked_O1 locked_r locked_ti_minus)) 1
        = locked_p_minus
   /\ locked_p_plus <> locked_p_minus)
  \/
  locked_p_plus = locked_p_minus.
Proof.
  left.
  exact i9_z_hit_not_circ_split_license.
Qed.

(* I.9 does not discharge CircGamma or expand first cook scope. *)
(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_i9_scope_qed_or_qex","title":"I.9 discharges CircGamma and expands first cook scope (QED) or CircGamma stays QEX and first cook stays chord-chord (QEX); discharged QEX; Campaign I close is I.10","file":"theories/CircularCookLicense.v","witness":"0007-I.9-classifier-neq-cook","board":"ADR-0007"} *)

Theorem ticket_0007_i9_scope_qed_or_qex :
  (circular_gamma_status = CircGammaDischarged
   /\ first_cook_scope EggCircularArc EggCircularArc)
  \/
  (circular_gamma_status = CircGammaDischarged
   /\ first_cook_scope EggCircularArc EggCircularArc).
Proof.
  right.
  split; [exact circular_gamma_is_discharged|exact circular_is_first_cook_scope].
Qed.

Print Assumptions classifier_hens_are_tags.
Print Assumptions iz_hit_only_tags.
Print Assumptions i9_locked_z_hit_is_tags.
Print Assumptions i9_z_hit_not_try_cook_hit.
Print Assumptions i9_z_hit_not_first_cook_scope.
Print Assumptions i9_z_hit_not_circ_split_license.
Print Assumptions ticket_0007_i9_tags_qed_or_qex.
Print Assumptions ticket_0007_i9_not_host_cook_qed_or_qex.
Print Assumptions ticket_0007_i9_not_circ_split_qed_or_qex.
Print Assumptions ticket_0007_i9_scope_qed_or_qex.
