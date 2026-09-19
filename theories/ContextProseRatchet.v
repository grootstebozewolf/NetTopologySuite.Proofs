(* ============================================================================
   NetTopologySuite.Proofs.ContextProseRatchet
   ----------------------------------------------------------------------------
   Bible / CONTEXT narrative — QED-cite or cut (claimId
   508-context-prose-ratchet). Docs + claim citation only. No new
   geometry. Does not remint 508-e/g/h, 64-a, #791, 522/523 stops,
   CircGamma, I_ok_mixed, or ADR-0004/0007.

   QED: each priority-list sentence reduces to an existing Qed / named
   QEX ticket (LEFT).
     1. CircGamma — CircularCook.v : ticket_64_circ_gamma_qed_or_qex LEFT
        (CircGammaDischarged / MkCirc)
     2. leftover Ⅰ–Ⅸ classified —
        RelateNGEpic522.v : ticket_522_classified_qed_or_qex LEFT;
        completeness QEX after Ⅸ —
        RelateNGEpic522.v : ticket_522_qed_or_qex RIGHT
     3. first cook — SheetHenCook.v : first_cook_scope_*
        (chord, circ, clothoid IN; mixed/ellipse/NURBS/sin/geodesic/spiral QEX)
     4. CurveSegment year-1 CSChord|CSArc —
        ExactCurveEpic508.v : ticket_508_carrier_qed_or_qex LEFT
     5. #791 taut polygonal Jordan —
        RelateNGFace.v : relateng_jordan_true_region_inhabits;
        RNG_JordanUncond stays park —
        RelateNGFace.v : relateng_not_jordan_uncond
     6. zoo is not exact —
        ExactCurveEpic508.v : ticket_508_qed_or_qex RIGHT on ECZ_Ellipse

   QEX: a leftover load-bearing prose sentence with no owner. Not
   inhabited this letter.

   QEX is not owner accept. Epic #508 stays open.

   WITNESS topic: docs · claimId: 508-context-prose-ratchet
   witness: 508-context-prose-ratchet
   board: #508
   3-axiom (inherited). No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From NTS.Proofs Require Import
  SheetHenCook
  CircularCook
  ExactCurveEpic508
  RelateNGEpic522
  RelateNGFace.

(* WITNESS {"claimId":"508-context-prose-ratchet","topic":"docs","lemma":"ticket_508_context_prose_qed_or_qex","title":"CONTEXT/Bible priority sentences reduce to existing Qed/QEX tickets (QED) or a leftover unowned prose sentence is named (QEX); discharged QED; epic #508 stays open; QEX is not owner accept","file":"theories/ContextProseRatchet.v","witness":"508-context-prose-ratchet","board":"#508"} *)

Theorem ticket_508_context_prose_qed_or_qex :
  (circular_gamma_status = CircGammaDischarged
   /\ ticket_64_circ_gamma_qed_or_qex
   /\ first_cook_scope EggChord EggChord
   /\ first_cook_scope EggCircularArc EggCircularArc
   /\ first_cook_scope EggClothoid EggClothoid
   /\ ~ first_cook_scope EggChord EggCircularArc
   /\ ~ first_cook_scope EggEllipse EggEllipse
   /\ ~ first_cook_scope EggNurbs EggNurbs
   /\ ~ first_cook_scope EggSinusoid EggSinusoid
   /\ ~ first_cook_scope EggGeodesicString EggGeodesicString
   /\ ~ first_cook_scope EggSpiralCurve EggSpiralCurve
   /\ ticket_508_carrier_qed_or_qex
   /\ ticket_508_qed_or_qex
   /\ ticket_522_classified_qed_or_qex
   /\ ticket_522_qed_or_qex
   /\ relateng_park_inhabits RelateNGJordanTrueRegion
   /\ relateng_kind <> RNG_JordanUncond)
  \/
  False.
Proof.
  left.
  split; [exact circular_gamma_is_discharged|].
  split; [exact ticket_64_circ_gamma_qed_or_qex|].
  split; [exact first_cook_scope_chord_chord|].
  split; [exact circular_egg_first_cook_scope|].
  split; [exact clothoid_egg_first_cook_scope|].
  split; [exact chord_circular_not_first_cook_scope|].
  split; [exact ellipse_ellipse_not_first_scope|].
  split; [exact nurbs_nurbs_not_first_scope|].
  split; [intro H; exact H|].
  split; [intro H; exact H|].
  split; [intro H; exact H|].
  split; [exact ticket_508_carrier_qed_or_qex|].
  split; [exact ticket_508_qed_or_qex|].
  split; [exact ticket_522_classified_qed_or_qex|].
  split; [exact ticket_522_qed_or_qex|].
  split; [exact relateng_jordan_true_region_inhabits|].
  exact relateng_not_jordan_uncond.
Qed.

Print Assumptions ticket_508_context_prose_qed_or_qex.
