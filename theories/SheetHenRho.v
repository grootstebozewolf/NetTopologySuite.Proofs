(* ============================================================================
   NetTopologySuite.Proofs.SheetHenRho
   ----------------------------------------------------------------------------
   ∀-bag letter 2 of 6. ρ and finiteness. claimId: none.
   Does not remint 0007-forall-bag and does not steal its witness.
   Does not redefine SheetHenBag objects. Does not touch
   LeftoverBagTermArm or circ_leftover_bag_term_forall.
   Strict decrease and termination are letter 3.
   ρ is the sum, over Leibniz-distinct support pairs, of the length of
   an explicit candidate list deduplicated with Req_EM_T. A pair is
   counted once (triple point). Line×line contributes at most one
   point, line×circle at most two (host Hit iff incidence, C1
   quadratic), circle×circle at most two (radical line). Geometrically
   equal carriers contribute only the overlap-interval endpoints.
   rho_candidates_complete: a common window point that is not a vertex
   of both families is in that list, by class (transverse carriers from
   the finiteness roots; equal carriers only when the point is an
   overlap endpoint). #892's two half-turns contribute 0.
   SPLIT: SheetHenRhoCarrier.v, SheetHenRhoCount.v, SheetHenRhoWitness.v.
   This file is the Require Export umbrella. Declarations are unchanged.
   3-axiom host. No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From NTS.Proofs Require Export SheetHenRhoCarrier.
From NTS.Proofs Require Export SheetHenRhoCount.
From NTS.Proofs Require Export SheetHenRhoWitness.
