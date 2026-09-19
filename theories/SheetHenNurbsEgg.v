(* ============================================================================
   NetTopologySuite.Proofs.SheetHenNurbsEgg
   ----------------------------------------------------------------------------
   NurbsEgg payload for host MkNurbs (claimId 0007-nurbs-first-cook).
   Scaffolding only. nurbs_eval is endpoint-chord lerp; nurbs_ctrl is
   copied and never used. on_nurbs is a silent on_chord demote under
   another name — not first cook, not Cox-de-Boor-as-noder.
   Missing ctor: NurbsNotChordDemote (NurbsCookMkNurbs.v).
   3-axiom. No Admitted, no Axiom, no Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import Distance.
Local Open Scope R_scope.

(* Locked NURBS egg. Chord-seed ends plus one off-chord control.
   Control travels with the egg; evaluation ignores it. *)
Record NurbsEgg : Type := mkNurbsEgg {
  nurbs_p0 : Point;
  nurbs_p1 : Point;
  nurbs_ctrl : Point
}.

Definition locked_nurbs_egg : NurbsEgg :=
  mkNurbsEgg (mkPoint 0 0) (mkPoint 1 0) (mkPoint (1 / 2) (1 / 2)).

(* Endpoint-chord lerp. Control is not an argument. *)
Definition nurbs_eval (n : NurbsEgg) (t : R) : Point :=
  mkPoint ((1 - t) * px (nurbs_p0 n) + t * px (nurbs_p1 n))
          ((1 - t) * py (nurbs_p0 n) + t * py (nurbs_p1 n)).

Definition on_nurbs (n : NurbsEgg) (t : R) (p : Point) : Prop :=
  0 <= t <= 1 /\ p = nurbs_eval n t.

Definition nurbs_split (n : NurbsEgg) (t : R) : NurbsEgg * NurbsEgg :=
  let mid := nurbs_eval n t in
  (mkNurbsEgg (nurbs_p0 n) mid (nurbs_ctrl n),
   mkNurbsEgg mid (nurbs_p1 n) (nurbs_ctrl n)).

Lemma nurbs_eval_ignores_ctrl :
  forall p0 p1 c1 c2 t,
    nurbs_eval (mkNurbsEgg p0 p1 c1) t = nurbs_eval (mkNurbsEgg p0 p1 c2) t.
Proof.
  intros. reflexivity.
Qed.

Lemma on_nurbs_is_endpoint_lerp :
  forall n t p,
    on_nurbs n t p ->
    0 <= t <= 1 /\
    p = mkPoint ((1 - t) * px (nurbs_p0 n) + t * px (nurbs_p1 n))
                ((1 - t) * py (nurbs_p0 n) + t * py (nurbs_p1 n)).
Proof.
  intros n t p [H01 Heq].
  split; [exact H01|].
  rewrite Heq. reflexivity.
Qed.
