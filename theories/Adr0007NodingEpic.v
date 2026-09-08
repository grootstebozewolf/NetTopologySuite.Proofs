(* ============================================================================
   NetTopologySuite.Proofs.Adr0007NodingEpic
   ----------------------------------------------------------------------------
   ADR-0007 ticket-named QED ∨ QEX stops (same shape as ticket 508 /
   ticket 522).

   The noding constructor is part of the specification: sheet, hen,
   egg, chicken, cook / 𝓘. First cook scope is chord–chord only.

   QED: chord–chord inhabits the cook interface; Empty ≠ Decline;
   ShareOne mints one hen; noded-on-S is cook evidence.
   `ticket_0007_chord_chord_qed_or_qex` discharges left.
   `ticket_0007_empty_neq_decline_qed_or_qex` discharges left.
   `ticket_0007_identity_qed_or_qex` discharges left.
   `ticket_0007_noded_cook_qed_or_qex` discharges left.

   QEX: a documented out-of-scope pair (clothoid–clothoid) is missing
   from first cook scope; numeric coord-pair equality does not decide
   hen identity; silent pairwise_nodable excludes the proper-crossing
   case a noder exists for.
   `ticket_0007_qed_or_qex` discharges right on clothoid–clothoid
   (`clothoid_clothoid_not_first_scope`), 508-style.
   `ticket_0007_dart_eq_qed_or_qex` discharges right.
   `ticket_0007_silent_nodable_qed_or_qex` discharges right.

   Cook termination host-lane close: pairwise interior split is
   finite and one Hit-split is confluent (leftover bag independent
   of parent order).
   `ticket_0007_pairwise_split_qed_or_qex` discharges left.
   The bag-level repeat-until-noded loop stays an 𝓘-family /
   CRV-TOUCH obligation (not a named soft gap).
   `ticket_0007_cook_term_qed_or_qex` discharges right.

   binary64 / OverlayNGRobust sit on one sheet (QED).
   `ticket_0007_sheet_realiz_qed_or_qex` discharges left.

   Chicken vs Dart: DdirDart := (Hen * Hen) is the chicken
   projection (QED). One type equation, not three types.
   `ticket_0007_chicken_dart_qed_or_qex` discharges left.

   QEX is not BDFL accept. ADR-0007 stays Proposed. Do not remint
   CurveSegment / Exact* zoo types / Dart. Do not steal 508-* / 522-*
   board mints. Do not claim a complete FP noder or close Hobby.

   Testable 𝓘 / cook results sit on the accepted Oracle line protocol
   (ADR-0006). This module mints no keyword and no second external seam.
   A later keyword attaches as an Oracle adapter, never as FFI or
   RocqRefRunner.

   WITNESS topic: overlay · claimId: 0007 · witness: 0007-qed-qex
   lane: proofs
   board: ADR-0007

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import Distance Segment SheetHenCook.
Local Open Scope R_scope.

(* ADR-0007 stop: every egg-class pair is in first cook scope (QED)
   or a documented out-of-scope pair is missing (QEX). Discharged QEX
   on clothoid–clothoid — the 508-style carrier miss. *)
(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_qed_or_qex","title":"ADR-0007 stop is first-cook-scope completeness (QED) or a documented out-of-scope pair (QEX); discharged QEX on clothoid-clothoid","file":"theories/Adr0007NodingEpic.v","witness":"0007-qed-qex","board":"ADR-0007"} *)

Theorem ticket_0007_qed_or_qex :
  (forall a b : EggClass, first_cook_scope a b)
  \/
  (exists a b : EggClass, ~ first_cook_scope a b).
Proof.
  right.
  exists EggClothoid, EggClothoid.
  exact clothoid_clothoid_not_first_scope.
Qed.

(* Chord–chord inhabits the cook interface (QED) or a documented
   miss (QEX). Crossing Hit + disjoint Empty + never Decline in
   scope. First cook scope is chord–chord. *)
Theorem ticket_0007_chord_chord_qed_or_qex :
  (first_cook_scope EggChord EggChord /\
   egg_class (cw_e1 crossing_witness) = EggChord /\
   egg_class (cw_e2 crossing_witness) = EggChord /\
   (exists p ti tj, cw_result crossing_witness = IHit p ti tj) /\
   cw_result disjoint_witness = IEmpty /\
   (forall c1 c2 o,
      I_ok (MkChord c1) (MkChord c2) o -> o <> IDecline))
  \/
  (exists a b : EggClass, ~ first_cook_scope a b).
Proof.
  left.
  split; [exact first_cook_scope_chord_chord|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [|split].
  - exists cross_pt, (1 / 2), (1 / 2).
    reflexivity.
  - reflexivity.
  - exact I_ok_chord_not_decline.
Qed.

(* Empty ≠ Decline as distinct 𝓘 outcomes (QED) or they coincide (QEX).
   Discharged QED. *)
Theorem ticket_0007_empty_neq_decline_qed_or_qex :
  IEmpty <> IDecline
  \/
  IEmpty = IDecline.
Proof.
  left.
  exact IEmpty_neq_IDecline.
Qed.

(* Structural identity: coincident cook successes share one hen when
   the cook so decides (QED) or the share policy fails (QEX).
   Discharged QED on ShareOne. *)
Theorem ticket_0007_identity_qed_or_qex :
  (forall h : Hen,
     fst (apply_id_decision (ShareOne h)) =
     snd (apply_id_decision (ShareOne h)))
  \/
  (exists h : Hen,
     fst (apply_id_decision (ShareOne h)) <>
     snd (apply_id_decision (ShareOne h))).
Proof.
  left.
  exact share_one_same_hen.
Qed.

(* Numeric coord-pair equality decides hen identity (QED) or it does
   not (QEX). Discharged QEX — dart_eq_dec answers the wrong question.
   Local CoordDart mirrors Dart.v:50; not a remint. *)
Theorem ticket_0007_dart_eq_qed_or_qex :
  (forall (h1 h2 : Hen) (d1 d2 : CoordDart),
     h1 = h2 <-> d1 = d2)
  \/
  ~ (forall (h1 h2 : Hen) (d1 d2 : CoordDart),
       h1 = h2 <-> d1 = d2).
Proof.
  right.
  exact coord_eq_not_hen_eq.
Qed.

(* Noded on S is cook evidence (QED) or no such package exists (QEX).
   Discharged QED on the crossing witness. *)
Theorem ticket_0007_noded_cook_qed_or_qex :
  (exists n : NodedOnSheet,
     I_ok (cw_e1 (noded_cook n)) (cw_e2 (noded_cook n))
          (cw_result (noded_cook n)))
  \/
  (forall n : NodedOnSheet,
     ~ I_ok (cw_e1 (noded_cook n)) (cw_e2 (noded_cook n))
            (cw_result (noded_cook n))).
Proof.
  left.
  exists noded_crossing.
  exact (noded_on_sheet_carries_I_ok noded_crossing).
Qed.

(* Silent pairwise_nodable / fully_intersected discharges the
   constructor (QED) or a documented proper-crossing pair is excluded
   by that hypothesis (QEX). Discharged QEX — the noder's job is the
   excluded case. Epic-stop shaped; not a Hobby rewrite. *)
Theorem ticket_0007_silent_nodable_qed_or_qex :
  (forall A B C D : Point,
     (exists X, between A B X /\ between C D X) ->
     pairwise_nodable_shadow A B C D)
  \/
  (exists A B C D : Point,
     (exists X, between A B X /\ between C D X) /\
     ~ pairwise_nodable_shadow A B C D).
Proof.
  right.
  exists (mkPoint 0 0), (mkPoint 2 2), (mkPoint 0 2), (mkPoint 2 0).
  split.
  - exists cross_pt.
    split; [exact crossing_midpoint_ab | exact crossing_midpoint_cd].
  - exact crossing_not_nodable_shadow.
Qed.

(* Pairwise interior split + one-step confluence on the chord lane
   (QED) or the leftover-width measure fails (QEX). Discharged QED —
   interior Hit splits [0,1] into two strictly shorter leftovers
   whose bag does not depend on parent order. The bag loop is not
   this stop. *)
(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_pairwise_split_qed_or_qex","title":"ADR-0007 pairwise chord split is finite and one Hit-split is confluent (QED) or the leftover-width measure fails (QEX); discharged QED","file":"theories/Adr0007NodingEpic.v","witness":"0007-pairwise-split","board":"ADR-0007"} *)
Theorem ticket_0007_pairwise_split_qed_or_qex :
  (interior_split_finite /\ split_step_confluent_holds)
  \/
  ~ interior_split_finite.
Proof.
  left.
  split; [exact interior_split_finite_holds|].
  exact split_step_confluent_holds_proof.
Qed.

(* Bag-level cook loop on the chord lane (QED: discharged) or the
   loop remains an 𝓘-family / CRV-TOUCH obligation (QEX). Discharged
   QEX — pairwise width decrease is not that discharge. Not a named
   soft gap; Honest remaining open. *)
(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_cook_term_qed_or_qex","title":"ADR-0007 bag cook loop is discharged (QED) or an I-family CRV-TOUCH obligation (QEX); discharged QEX; pairwise split is a sibling QED stop","file":"theories/Adr0007NodingEpic.v","witness":"0007-cook-term","board":"ADR-0007"} *)
Theorem ticket_0007_cook_term_qed_or_qex :
  (cook_loop_status = LoopDischarged /\ interior_split_finite)
  \/
  (cook_loop_status = LoopObligation /\ interior_split_finite).
Proof.
  right.
  split; [exact cook_loop_is_obligation|].
  exact interior_split_finite_holds.
Qed.

(* binary64 / OverlayNGRobust sit on one sheet (QED) or changing the
   number type yields a second sheet (QEX). Discharged QED —
   realization preserves S; OverlayNGRobust is a finite snap-sequence,
   not 𝓘. *)
(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_sheet_realiz_qed_or_qex","title":"ADR-0007 binary64 and OverlayNGRobust sit on one sheet (QED) or a second sheet appears (QEX); discharged QED","file":"theories/Adr0007NodingEpic.v","witness":"0007-sheet-realiz","board":"ADR-0007"} *)
Theorem ticket_0007_sheet_realiz_qed_or_qex :
  ((forall (s : Sheet) (n1 n2 : CoordRealization),
      realiz_sheet (mkSheetRealization s n1) =
      realiz_sheet (mkSheetRealization s n2))
   /\
   (forall (s : Sheet) (n : nat),
      overlay_ng_robust_is_finite_snap s n)
   /\
   CtorSnapRound <> CtorI)
  \/
  (exists (s : Sheet) (n1 n2 : CoordRealization),
     realiz_sheet (mkSheetRealization s n1) <>
     realiz_sheet (mkSheetRealization s n2)).
Proof.
  left.
  split; [exact coord_realization_preserves_sheet|].
  split; [exact overlay_ng_robust_is_finite_snap_holds|].
  exact overlay_ng_robust_is_snap_not_I.
Qed.

(* DdirDart := (Hen * Hen) is the chicken projection (QED) or the
   hen-id view is not that pair (QEX). Discharged QED — one type
   equation; CoordDart stays the Dart.v:50 story; no third type. *)
(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_chicken_dart_qed_or_qex","title":"ADR-0007 ddir migration is Hen-id pair equals chicken ends (QED) or that equation fails (QEX); discharged QED","file":"theories/Adr0007NodingEpic.v","witness":"0007-chicken-dart","board":"ADR-0007"} *)
Theorem ticket_0007_chicken_dart_qed_or_qex :
  (DdirDart = (Hen * Hen)%type /\
   RoleHenIdDart <> RoleCoordDart /\
   (forall c : Chicken, hen_id_dart_of_chicken c = (ck_src c, ck_dst c)) /\
   (forall c : Chicken, chicken_gamma_source c = ck_egg c))
  \/
  DdirDart <> (Hen * Hen)%type.
Proof.
  left.
  exact ddir_migration_one_equation.
Qed.

(* Core-slice circular tickets: ticket_64_circ_hit_params_qed_or_qex
   (QED, CircularCookHit.v, full/atan2), CircularCookSpan.v span γ
   (QED, 4-axiom sidecar), and ticket_64_circ_gamma_qed_or_qex (QEX,
   CircularCook.v host flag). Not Required here — host lane stays
   atan2-free. Host CircGamma stays QEX; first cook stays chord–chord. *)

Print Assumptions ticket_0007_qed_or_qex.
Print Assumptions ticket_0007_chord_chord_qed_or_qex.
Print Assumptions ticket_0007_empty_neq_decline_qed_or_qex.
Print Assumptions ticket_0007_identity_qed_or_qex.
Print Assumptions ticket_0007_dart_eq_qed_or_qex.
Print Assumptions ticket_0007_noded_cook_qed_or_qex.
Print Assumptions ticket_0007_silent_nodable_qed_or_qex.
Print Assumptions ticket_0007_pairwise_split_qed_or_qex.
Print Assumptions ticket_0007_cook_term_qed_or_qex.
Print Assumptions ticket_0007_sheet_realiz_qed_or_qex.
Print Assumptions ticket_0007_chicken_dart_qed_or_qex.
