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

   QEX is not BDFL accept. ADR-0007 stays Proposed. Do not remint
   CurveSegment / Exact* zoo types / Dart. Do not steal 508-* / 522-*
   board mints. Do not claim a complete FP noder or close Hobby.

   Testable 𝓘 / cook results sit on the accepted Oracle line protocol
   (ADR-0006). This module mints no keyword and no second external seam.

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

Print Assumptions ticket_0007_qed_or_qex.
Print Assumptions ticket_0007_chord_chord_qed_or_qex.
Print Assumptions ticket_0007_empty_neq_decline_qed_or_qex.
Print Assumptions ticket_0007_identity_qed_or_qex.
Print Assumptions ticket_0007_dart_eq_qed_or_qex.
Print Assumptions ticket_0007_noded_cook_qed_or_qex.
Print Assumptions ticket_0007_silent_nodable_qed_or_qex.
