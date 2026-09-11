(* ============================================================================
   NetTopologySuite.Proofs.SheetHenClothoidEgg
   ----------------------------------------------------------------------------
   ClothoidEgg payload for host MkClothoid
   (claimId 0007-intake-mkclothoid) plus the Fresnel-free
   first-cook interpolant (claimId 0007-clothoid-first-cook).
   Locked inhabitance record: chord-seed ends plus JTS (k0, k1, L).
   cloth_eval is the chord-parameter witness — not Fresnel γ and
   not a silent I_ok demote to on_chord. cloth_split interpolates
   curvature linearly and keeps MkClothoid children. 3-axiom.
   No Admitted, no Axiom, no Parameter.

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

(* Fresnel-free first-cook interpolant: chord-parameter of the
   inhabitance ends. Curvature (k0, k1) and length L travel with
   the egg; cloth_split interpolates them. Not Fresnel-as-noding.
   I_ok uses on_cloth, not on_chord. *)
Definition cloth_eval (c : ClothoidEgg) (t : R) : Point :=
  mkPoint ((1 - t) * px (cloth_p0 c) + t * px (cloth_p1 c))
          ((1 - t) * py (cloth_p0 c) + t * py (cloth_p1 c)).

Definition cloth_k_at (c : ClothoidEgg) (t : R) : R :=
  cloth_k0 c + t * (cloth_k1 c - cloth_k0 c).

Definition on_cloth (c : ClothoidEgg) (t : R) (p : Point) : Prop :=
  0 <= t <= 1 /\ p = cloth_eval c t.

Definition cloth_split (c : ClothoidEgg) (t : R) : ClothoidEgg * ClothoidEgg :=
  let mid := cloth_eval c t in
  (mkClothoidEgg (cloth_p0 c) mid (cloth_k0 c) (cloth_k_at c t) (t * cloth_L c),
   mkClothoidEgg mid (cloth_p1 c) (cloth_k_at c t) (cloth_k1 c)
     ((1 - t) * cloth_L c)).
