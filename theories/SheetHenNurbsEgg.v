(* ============================================================================
   NetTopologySuite.Proofs.SheetHenNurbsEgg
   ----------------------------------------------------------------------------
   NurbsEgg payload for host MkNurbs (claimId 0007-nurbs-first-cook).
   Locked inhabitance record: chord-seed ends plus one off-chord
   control point (sidecar NurbsChord shape). nurbs_eval is the
   chord-parameter witness — not Cox-de-Boor γ and not a silent
   I_ok demote to on_chord. nurbs_split keeps MkNurbs children
   and copies the control payload. 3-axiom.
   No Admitted, no Axiom, no Parameter.

   First cook only. Do not remint #508 length / knot-span as
   the noding engine.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import Distance.
Local Open Scope R_scope.

(* Locked NURBS egg. Chord-seed ends are inhabitance data — not
   Cox-de-Boor γ(1). The control point travels with the egg;
   first-cook interpolant does not evaluate it. Do not run
   knot-span / length here. *)
Record NurbsEgg : Type := mkNurbsEgg {
  nurbs_p0 : Point;
  nurbs_p1 : Point;
  nurbs_ctrl : Point
}.

Definition locked_nurbs_egg : NurbsEgg :=
  mkNurbsEgg (mkPoint 0 0) (mkPoint 1 0) (mkPoint (1 / 2) (1 / 2)).

(* Chord-parameter of the inhabitance ends. Control travels with
   the egg; nurbs_split copies it. Not Cox-de-Boor-as-noding.
   I_ok uses on_nurbs, not on_chord. *)
Definition nurbs_eval (n : NurbsEgg) (t : R) : Point :=
  mkPoint ((1 - t) * px (nurbs_p0 n) + t * px (nurbs_p1 n))
          ((1 - t) * py (nurbs_p0 n) + t * py (nurbs_p1 n)).

Definition on_nurbs (n : NurbsEgg) (t : R) (p : Point) : Prop :=
  0 <= t <= 1 /\ p = nurbs_eval n t.

Definition nurbs_split (n : NurbsEgg) (t : R) : NurbsEgg * NurbsEgg :=
  let mid := nurbs_eval n t in
  (mkNurbsEgg (nurbs_p0 n) mid (nurbs_ctrl n),
   mkNurbsEgg mid (nurbs_p1 n) (nurbs_ctrl n)).
