(* ============================================================================
   NetTopologySuite.Proofs.SheetHenClothoidEgg
   ----------------------------------------------------------------------------
   ClothoidEgg payload for host MkClothoid
   (claimId 0007-intake-mkclothoid). Locked inhabitance record:
   chord-seed ends plus JTS (k0, k1, L). Not a Fresnel interpolant.
   Not clothoid×clothoid first cook. 3-axiom. No Admitted / Axiom /
   Parameter.

   Grammar has two surface forms (ISO REFERENCELOCATION, JTS
   (k0,k1,L)). One host egg. OGC≡ISO bag discipline lives in
   IntakeWalker.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import Distance.
Local Open Scope R_scope.

(* Locked clothoid egg. Chord-seed ends are inhabitance data — not
   Fresnel γ(1). k0 / k1 / L reuse the JTS surface triple from
   grammars-v4 #4997 example5.txt. ISO form maps onto the same
   record. Do not evaluate Fresnel here. *)
Record ClothoidEgg : Type := mkClothoidEgg {
  cloth_p0 : Point;
  cloth_p1 : Point;
  cloth_k0 : R;
  cloth_k1 : R;
  cloth_L : R
}.

Definition locked_clothoid_egg : ClothoidEgg :=
  mkClothoidEgg (mkPoint 0 0) (mkPoint 1 0) 0 (5 / 1000) 80.
