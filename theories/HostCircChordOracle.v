(* ============================================================================
   NetTopologySuite.Proofs.HostCircChordOracle
   ----------------------------------------------------------------------------
   NTS/JTS: MCIndexNoder mixed segment (LineString chord × CircularString).
   claimId: 0007-host-circ-chord-oracle

   Host 𝓘 on MkCirc × MkChord and the reverse. In scope
   (|Δθ| < 2π, nondegenerate chord) a Hit is on both curves, and every
   such incidence is a Hit. Full-span eggs and degenerate chords Decline
   by name. circ×circ stays the existing host arm (Decline is False).
   first_cook_scope does not gain the mixed arms.

   The locked CC LS+CS joint is a host Hit, so the ∀-bag loop does not
   StepIDecline on that pair. The joint is already a vertex of both
   pieces, so it is not a progress_hit. An interior hit of the same
   locked quarter (F1) is a bag_progress_step and the children keep
   same_support.

   3-axiom host. No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import
  Distance SheetHenCook SheetHenBag ZetaHostHit ZetaEggBridge
  CircularCookMkCirc IntakeWalker.
Import ListNotations.
Local Open Scope R_scope.
Local Open Scope list_scope.

(* partial upload marker; replaced by the full module *)
