(* ============================================================================
   NetTopologySuite.Proofs.ContextProseRatchet2
   ----------------------------------------------------------------------------
   Bible / CONTEXT narrative — QED-cite or cut, pass 2 (claimId
   508-context-prose-ratchet-2). Docs + claim citation only. No new
   geometry. Does not remint 508-e/g/h, 64-a, #791, 522/523 stops,
   CircGamma, I_ok_mixed, ADR-0004/0007, or 508-context-prose-ratchet.

   QED: leftover dual-source sentences reduce to existing Qed / named
   QEX tickets (LEFT).
     1. Emit / WKT parse QEX —
        SqlMmSignedTag.v : ticket_sqlmm_factory_emit_qed_or_qex RIGHT
     2. Production-level τ=π on full-span CIRCULARSTRING text QEX —
        SqlMmSignedTag.v : sqlmm_tau_eq_pi_fullspan_cs_missing
        (RIGHT arm of ticket_sqlmm_tau_mu_qed_or_qex; locked exists-b-e
        is that ticket LEFT)
     3. #508 stays open / QEX ≠ owner accept —
        ExactCurveEpic508.v : ticket_508_qed_or_qex RIGHT on ECZ_Ellipse
     4. Year-1 CSChord|CSArc —
        ExactCurveEpic508.v : ticket_508_carrier_qed_or_qex LEFT
     5. CircGamma is discharged, not QEX —
        CircularCook.v : ticket_64_circ_gamma_qed_or_qex LEFT
        (CircGammaDischarged / MkCirc)

   QEX: a leftover load-bearing prose sentence with no owner. Not
   inhabited this letter.

   QEX is not owner accept. Epic #508 stays open.

   WITNESS topic: docs · claimId: 508-context-prose-ratchet-2
   witness: 508-context-prose-ratchet-2
   board: #508
   3-axiom (inherited). No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import
  CircularCook
  CurveGeometry
  ExactCurveEpic508
  SqlMmSignedTag.
Local Open Scope R_scope.

(* WITNESS {"claimId":"508-context-prose-ratchet-2","topic":"docs","lemma":"ticket_508_context_prose_2_qed_or_qex","title":"CONTEXT/Bible leftover dual sentences reduce to existing Qed/QEX tickets (emit/WKT QEX RIGHT; production τ=π named miss; #508 QEX RIGHT; CSChord|CSArc LEFT; CircGamma LEFT) or a leftover unowned prose sentence is named (QEX); discharged QED; epic #508 stays open; QEX is not owner accept","file":"theories/ContextProseRatchet2.v","witness":"508-context-prose-ratchet-2","board":"#508"} *)

Theorem ticket_508_context_prose_2_qed_or_qex :
  (~ sqlmm_emit_inhabits EmitWktBytes
   /\ ~ sqlmm_emit_inhabits EmitWkbHex
   /\ ~ sqlmm_emit_inhabits EmitAntlrParse
   /\ ~ sqlmm_prod_tag_fullspan_cs_text
   /\ circular_gamma_status = CircGammaDischarged
   /\ circ_gamma_constructor_inhabits CircGammaMkCirc
   /\ ((forall z : ExactCurveZoo, zoo_inhabits_curve_segment z)
       \/ (exists z : ExactCurveZoo, ~ zoo_inhabits_curve_segment z))
   /\ ((zoo_inhabits_curve_segment ECZ_Chord
        /\ zoo_inhabits_curve_segment ECZ_CircularArc
        /\ forall s : CurveSegment,
             (exists p q, s = CSChord p q) \/ (exists a, s = CSArc a))
       \/ (exists z : ExactCurveZoo, ~ zoo_inhabits_curve_segment z)))
  \/
  False.
Proof.
  left.
  split; [exact sqlmm_wkt_emit_missing|].
  split; [exact sqlmm_wkb_emit_missing|].
  split; [exact sqlmm_antlr_missing|].
  split; [exact sqlmm_tau_eq_pi_fullspan_cs_missing|].
  split; [exact circular_gamma_is_discharged|].
  split; [exact circ_gamma_mkcirc_inhabits|].
  split; [exact ticket_508_qed_or_qex|].
  exact ticket_508_carrier_qed_or_qex.
Qed.

Print Assumptions ticket_508_context_prose_2_qed_or_qex.
