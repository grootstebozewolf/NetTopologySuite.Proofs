(* ============================================================================
   NetTopologySuite.Proofs.SheetHenCook
   ----------------------------------------------------------------------------
   ADR-0007 vocabulary: sheet, hen, egg, chicken, cook / 𝑼.
   Thin host-lane types for Adr0007NodingEpic.v. Not a noder / Geometry
   subclass / remint of CurveSegment, Exact* zoo, Dart, or Hobby.
   First cook: chord–chord, circular–circular (MkCirc), clothoid–clothoid
   (MkClothoid), NURBS–NURBS (scope). Tags Decline. In-scope circ×chord
   is a host Hit; full-span and degenerate chords Decline. Empty ≠ Decline. Snap ≠ 𝑼.
   Bag cook loop is named QEX (LeftoverBagTermArm). CircGamma discharged
   by MkCirc. No new oracle keyword (ADR-0006). Accepted 2026-09-07.
   WITNESS topic: overlay · claimId: 0007 · witness: 0007-qed-qex

   Umbrella re-export (module-split gate, docs/module-split-allowlist.txt
   "the allowlist may not grow"): the content lives in SheetHenCookCore.v
   (sheet/hen/egg/chicken, 𝑼, identity, noded-on-sheet, leftover-split
   confluence, binary64/OverlayNGRobust, ddir) and SheetHenCookConstructed.v
   (chord_split / try_cook_hit, constructive 𝑼). This file re-exports both so
   `Require Import SheetHenCook` keeps working unchanged.
   No `Admitted`, no `Axiom`, no `Parameter`.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From NTS.Proofs Require Export SheetHenCircEgg SheetHenClothoidEgg.
From NTS.Proofs Require Export SheetHenCookCore.
From NTS.Proofs Require Export SheetHenCookConstructed.
