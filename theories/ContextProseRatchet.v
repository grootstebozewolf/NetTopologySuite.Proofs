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
        (chord, circ, clothoid, NURBS IN; mixed/ellipse/sin/geodesic/spiral QEX)
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

From Stdlib Require Import Reals.
From NTS.Proofs Require Import
  SheetHenCook
  CircularCook
  CurveGeometry
  ExactCurveEpic508
  GeneralTriangleSeparation
  RelateMatrixTriangle
  RelateNGCore
  RelateNGEpic522
  RelateNGFace.
Local Open Scope R_scope.

(* WITNESS {"claimId":"508-context-prose-ratchet","topic":"docs","lemma":"ticket_508_context_prose_qed_or_qex","title":"CONTEXT/Bible priority sentences reduce to existing Qed/QEX tickets (QED) or a leftover unowned prose sentence is named (QEX); discharged QED; epic #508 stays open; QEX is not owner accept","file":"theories/ContextProseRatchet.v","witness":"508-context-prose-ratchet","board":"#508"} *)

Theorem ticket_508_context_prose_qed_or_qex :
  (circular_gamma_status = CircGammaDischarged
   /\ circ_gamma_constructor_inhabits CircGammaMkCirc
   /\ first_cook_scope EggChord EggChord
   /\ first_cook_scope EggCircularArc EggCircularArc
   /\ first_cook_scope EggClothoid EggClothoid
   /\ ~ first_cook_scope EggChord EggCircularArc
   /\ ~ first_cook_scope EggEllipse EggEllipse
   /\ first_cook_scope EggNurbs EggNurbs
   /\ ~ first_cook_scope EggSinusoid EggSinusoid
   /\ ~ first_cook_scope EggGeodesicString EggGeodesicString
   /\ ~ first_cook_scope EggSpiralCurve EggSpiralCurve
   /\ ((zoo_inhabits_curve_segment ECZ_Chord
        /\ zoo_inhabits_curve_segment ECZ_CircularArc
        /\ forall s : CurveSegment,
             (exists p q, s = CSChord p q) \/ (exists a, s = CSArc a))
       \/ (exists z : ExactCurveZoo, ~ zoo_inhabits_curve_segment z))
   /\ ((forall z : ExactCurveZoo, zoo_inhabits_curve_segment z)
       \/ (exists z : ExactCurveZoo, ~ zoo_inhabits_curve_segment z))
   /\ ((triangle_pair_regime 0 0 2 0 0 1 1 0 3 0 2 1 = TPR_TouchPartialEdge
        /\ triangle_pair_regime 0 0 2 0 0 2 0 0 (-2) 0 1 (-1) = TPR_TouchObtuse
        /\ triangle_pair_regime 0 0 2 0 0 1 1 0 (1/2) (-1) (3/2) (-1)
             = TPR_TouchOnesided
        /\ triangle_pair_regime 0 0 2 0 0 1 1 0 (5/4) (1/4) (3/4) (1/4)
             = TPR_TouchOnesided
        /\ triangle_pair_regime 0 0 2 0 0 2 0 0 (-1) (-1) 3 1 = TPR_MixedCone
        /\ triangle_pair_regime 0 0 2 0 0 2 0 0 3 1 1 3 = TPR_SameCone
        /\ triangle_pair_regime 0 0 3 0 0 3 2 (-1) 2 2 (-1) 2 = TPR_Lens
        /\ triangle_pair_regime 1 1 2 1 1 2 0 0 4 0 0 4 = TPR_Inside
        /\ triangle_pair_regime 0 0 4 0 0 4 0 0 4 0 1 1 = TPR_Nest)
       \/ triangle_pair_regime 0 0 4 0 1 1 0 0 4 0 0 4 = TPR_Unsupported)
   /\ ((forall ax ay bx by_ cx cy dx dy ex ey fx fy : R,
          0 < gdbl ax ay bx by_ cx cy ->
          0 < gdbl dx dy ex ey fx fy ->
          triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy
            <> TPR_Unsupported)
       \/ (exists ax ay bx by_ cx cy dx dy ex ey fx fy : R,
             0 < gdbl ax ay bx by_ cx cy /\
             0 < gdbl dx dy ex ey fx fy /\
             triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy
               = TPR_Unsupported))
   /\ relateng_park_inhabits RelateNGJordanTrueRegion
   /\ relateng_kind <> RNG_JordanUncond)
  \/
  False.
Proof.
  left.
  split; [exact circular_gamma_is_discharged|].
  split; [exact circ_gamma_mkcirc_inhabits|].
  split; [exact first_cook_scope_chord_chord|].
  split; [exact circular_egg_first_cook_scope|].
  split; [exact clothoid_egg_first_cook_scope|].
  split; [exact chord_circular_not_first_cook_scope|].
  split; [exact ellipse_ellipse_not_first_scope|].
  split; [exact nurbs_nurbs_first_cook_scope|].
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
