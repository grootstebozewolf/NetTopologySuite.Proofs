(* ============================================================================
   NetTopologySuite.Proofs.CircularCookConfluence
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: I.8 one-step leftover confluence on
   γ_full. Circular analogue of SheetHenCook.split_step_confluent.

   CircLeftover / circ_split already live in CircularCookSplit. This
   sidecar names the leftover bag (A then B vs B then A) and tickets
   that the bags are equal. Cook leftovers inhabit that bag. Locked
   plus / minus cooks recover it.

   QED: leftovers_ab = leftovers_ba on γ_full; cook bag inhabits it;
   one-step ≠ bag loop (cook_loop stays LoopObligation).
   QEX: CircGamma stays QEX; not CircularArc span; first cook stays
   chord–chord. Not the bag-level repeat-until-noded loop.

   Honesty fences:
     I_circles_z ≠ I_circles_gamma ≠ sidecar cook ≠ glossary 𝓘.
     Not first cook scope. Not a noder. Not ArcSplitAtNode.
     Not a remint of CurveSegment / Exact* / Dart / Hobby /
     leftover_width / ArcSplitAtNode leftover-width.
     Do not fake atan2-free host γ.
     I.9 classifier ≠ cook lives in CircularCookLicense.v.
     I.10 Campaign-I close lives in CircularCookClose.v.
     Do not start Campaign II / H⊥ / a CRV-TOUCH kiss procedure.

   WITNESS topic: overlay · claimId: 0007
   witness: 0007-I.8-leftover-confluence
   board: ADR-0007
   4-axiom (atan2 / Classical_Prop.classic via CircularCookSplit).
   No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals.
(* CircularCookHit is required for locked_O1 / locked_O2 / locked_r.
   CircularCookSplit Imports Hit and does not Export those witnesses. *)
From NTS.Proofs Require Import Distance SheetHenCook CircularCook
  CircularCookHit CircularCookSplit.
Local Open Scope R_scope.

(* WITNESS: campaign=I rung=I.8 claim=0007
   file=theories/CircularCookConfluence.v
   kind=QED-one-step-leftover-confluence-gamma-full
   analogue=SheetHenCook.split_step_confluent
   not=bag-loop,leftover-width,CircGamma-Discharge,CircularArc-span
   not=Campaign-II,Hperp,CRV-TOUCH-kiss *)

(* -------------------------------------------------------------------------- *)
(* Leftover bags on γ_full. Named circ_* because SheetHenCook already          *)
(* exports leftovers_ab / leftovers_ba on ChordEgg. Same tuple order:         *)
(* A-left, A-right, B-left, B-right. Splitting A then B, or B then A,         *)
(* produces the same bag. Not leftover_width. Not the bag cook loop.          *)
(* -------------------------------------------------------------------------- *)

Definition circ_leftover_quad : Type :=
  (CircLeftover * CircLeftover * CircLeftover * CircLeftover)%type.

Definition circ_leftovers_ab
  (O1 : Point) (r1 : R) (O2 : Point) (r2 : R) (ti tj : R)
  : circ_leftover_quad :=
  let a := circ_split O1 r1 ti in
  let b := circ_split O2 r2 tj in
  (fst a, snd a, fst b, snd b).

Definition circ_leftovers_ba
  (O1 : Point) (r1 : R) (O2 : Point) (r2 : R) (ti tj : R)
  : circ_leftover_quad :=
  let b := circ_split O2 r2 tj in
  let a := circ_split O1 r1 ti in
  (fst a, snd a, fst b, snd b).

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"circ_split_step_confluent","title":"I.8 one-step leftover confluence: leftovers_ab = leftovers_ba on gamma_full (circular analogue of split_step_confluent)","file":"theories/CircularCookConfluence.v","witness":"0007-I.8-leftover-confluence","board":"ADR-0007"} *)

Lemma circ_split_step_confluent :
  forall O1 r1 O2 r2 ti tj,
    circ_leftovers_ab O1 r1 O2 r2 ti tj =
    circ_leftovers_ba O1 r1 O2 r2 ti tj.
Proof.
  intros O1 r1 O2 r2 ti tj.
  reflexivity.
Qed.

Definition circ_leftovers_of_cook (cp : CircCookedPair) : circ_leftover_quad :=
  (ccp_L1 cp, ccp_R1 cp, ccp_L2 cp, ccp_R2 cp).

Lemma cook_circ_root_is_leftovers_ab :
  forall O1 r1 O2 r2 ti tj h,
    circ_leftovers_of_cook (cook_circ_root O1 r1 O2 r2 ti tj h) =
    circ_leftovers_ab O1 r1 O2 r2 ti tj.
Proof.
  intros O1 r1 O2 r2 ti tj h.
  reflexivity.
Qed.

Lemma cook_circ_root_is_leftovers_ba :
  forall O1 r1 O2 r2 ti tj h,
    circ_leftovers_of_cook (cook_circ_root O1 r1 O2 r2 ti tj h) =
    circ_leftovers_ba O1 r1 O2 r2 ti tj.
Proof.
  intros O1 r1 O2 r2 ti tj h.
  rewrite cook_circ_root_is_leftovers_ab.
  apply circ_split_step_confluent.
Qed.

(* Locked R3 cooks inhabit the confluent bag. *)
Lemma i8_recovers_locked_plus :
  circ_leftovers_of_cook cooked_circ_plus =
  circ_leftovers_ab locked_O1 locked_r locked_O2 locked_r
    locked_ti_plus locked_tj_plus.
Proof.
  reflexivity.
Qed.

Lemma i8_recovers_locked_minus :
  circ_leftovers_of_cook cooked_circ_minus =
  circ_leftovers_ab locked_O1 locked_r locked_O2 locked_r
    locked_ti_minus locked_tj_minus.
Proof.
  reflexivity.
Qed.

(* One-step leftover confluence is not the bag-level cook loop. *)
Lemma i8_one_step_not_bag_loop :
  (forall O1 r1 O2 r2 ti tj,
     circ_leftovers_ab O1 r1 O2 r2 ti tj =
     circ_leftovers_ba O1 r1 O2 r2 ti tj)
  /\ cook_loop_status = LoopObligation
  /\ cook_loop_status <> LoopDischarged.
Proof.
  split; [exact circ_split_step_confluent|].
  split; [exact cook_loop_is_obligation|exact cook_loop_not_discharged].
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_i8_confluent_qed_or_qex","title":"I.8 leftovers_ab equals leftovers_ba on gamma_full (QED) or parent order changes the leftover bag (QEX); discharged QED; circular analogue of split_step_confluent","file":"theories/CircularCookConfluence.v","witness":"0007-I.8-leftover-confluence","board":"ADR-0007"} *)

Theorem ticket_0007_i8_confluent_qed_or_qex :
  (forall O1 r1 O2 r2 ti tj,
     circ_leftovers_ab O1 r1 O2 r2 ti tj =
     circ_leftovers_ba O1 r1 O2 r2 ti tj)
  \/
  circ_leftovers_ab locked_O1 locked_r locked_O2 locked_r
    locked_ti_plus locked_tj_plus <>
  circ_leftovers_ba locked_O1 locked_r locked_O2 locked_r
    locked_ti_plus locked_tj_plus.
Proof.
  left.
  exact circ_split_step_confluent.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_i8_cook_qed_or_qex","title":"I.8 cook leftovers inhabit the confluent bag (QED) or the locked plus-root cook misses leftovers_ab (QEX); discharged QED on cook_circ_root and locked plus/minus","file":"theories/CircularCookConfluence.v","witness":"0007-I.8-leftover-confluence","board":"ADR-0007"} *)

Theorem ticket_0007_i8_cook_qed_or_qex :
  ((forall O1 r1 O2 r2 ti tj h,
      circ_leftovers_of_cook (cook_circ_root O1 r1 O2 r2 ti tj h) =
      circ_leftovers_ab O1 r1 O2 r2 ti tj)
   /\ circ_leftovers_of_cook cooked_circ_plus =
        circ_leftovers_ab locked_O1 locked_r locked_O2 locked_r
          locked_ti_plus locked_tj_plus
   /\ circ_leftovers_of_cook cooked_circ_minus =
        circ_leftovers_ab locked_O1 locked_r locked_O2 locked_r
          locked_ti_minus locked_tj_minus)
  \/
  circ_leftovers_of_cook cooked_circ_plus <>
    circ_leftovers_ab locked_O1 locked_r locked_O2 locked_r
      locked_ti_plus locked_tj_plus.
Proof.
  left.
  split; [exact cook_circ_root_is_leftovers_ab|].
  split; [exact i8_recovers_locked_plus|exact i8_recovers_locked_minus].
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_i8_neq_bag_qed_or_qex","title":"I.8 one-step leftover confluence is not the bag cook loop (QED) or the bag loop is discharged (QEX); discharged QED; cook_loop stays LoopObligation","file":"theories/CircularCookConfluence.v","witness":"0007-I.8-leftover-confluence","board":"ADR-0007"} *)

Theorem ticket_0007_i8_neq_bag_qed_or_qex :
  ((forall O1 r1 O2 r2 ti tj,
      circ_leftovers_ab O1 r1 O2 r2 ti tj =
      circ_leftovers_ba O1 r1 O2 r2 ti tj)
   /\ cook_loop_status = LoopObligation
   /\ cook_loop_status <> LoopDischarged)
  \/
  cook_loop_status = LoopDischarged.
Proof.
  left.
  exact i8_one_step_not_bag_loop.
Qed.

(* I.8 is γ_full leftover-bag confluence, not CircularArc span and
   not the bag loop. CircGamma stays QEX. *)
(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_i8_scope_qed_or_qex","title":"I.8 discharges CircGamma and the bag loop (QED) or gamma_full one-step confluence while CircGamma stays QEX (QEX); discharged QEX; Campaign I close is I.10","file":"theories/CircularCookConfluence.v","witness":"0007-I.8-leftover-confluence","board":"ADR-0007"} *)

Theorem ticket_0007_i8_scope_qed_or_qex :
  (circular_gamma_status = CircGammaDischarged
   /\ cook_loop_status = LoopDischarged
   /\ first_cook_scope EggCircularArc EggCircularArc)
  \/
  (circular_gamma_status = CircGammaQEX
   /\ cook_loop_status = LoopObligation
   /\ ~ first_cook_scope EggCircularArc EggCircularArc).
Proof.
  right.
  split; [exact circular_gamma_is_qex|].
  split; [exact cook_loop_is_obligation|exact circular_not_first_cook_scope].
Qed.

Print Assumptions circ_split_step_confluent.
Print Assumptions cook_circ_root_is_leftovers_ab.
Print Assumptions i8_recovers_locked_plus.
Print Assumptions i8_one_step_not_bag_loop.
Print Assumptions ticket_0007_i8_confluent_qed_or_qex.
Print Assumptions ticket_0007_i8_cook_qed_or_qex.
Print Assumptions ticket_0007_i8_neq_bag_qed_or_qex.
Print Assumptions ticket_0007_i8_scope_qed_or_qex.
