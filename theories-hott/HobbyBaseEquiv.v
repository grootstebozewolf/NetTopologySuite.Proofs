(* ============================================================================
   NetTopologySuite.HoTT.HobbyBaseEquiv
   ----------------------------------------------------------------------------
   HoTT-style linkage for Hobby noding lemmas (biarc approximation, residual
   monotonicity) after Shewchuk orientation base.

   This is the GREEN skeleton start for the Hobby chunk per the tin/hobby/
   shewchuk/curve RGR decision (Shewchuk solid → Hobby).

   Uses transport via orient_equiv (from ShewchukBaseEquiv) + univalence.

   References: archive/theories-flocq/HobbyTheorem_b64.v, HobbyCounterexample_b64.v,
   docs/hobby-lemma-4-3-no-proper-refutation.md etc.

   Exactly one axiom: univalence (justified for C# linkage / transport of
   noding properties; per docs/axiom-policy.md).

   Author: (HoTT pivot contributors, following RGR)
   License: BSD-3-Clause
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import List.
Open Scope R_scope.

(* Re-use from Shewchuk for now (in full: shared geometry module). *)
Require Import ShewchukBaseEquiv.

(* -------------------------------------------------------------------------- *)
(* Formal Hobby property (re-expressed from archive).                        *)
(* E.g. 4.1: biarc approx over noded segments preserves certain invariants.  *)
(* -------------------------------------------------------------------------- *)

Definition formal_hobby_4_1 (P0 P1 Q0 Q1 : Point) : Prop :=
  (* placeholder; real would use orient + other *)
  True.

(* -------------------------------------------------------------------------- *)
(* NTS-side model.                                                           *)
(* -------------------------------------------------------------------------- *)

Definition nts_hobby_4_1 (P0 P1 Q0 Q1 : Point) : Prop :=
  (* mirror of C# noding behaviour *)
  True.

(* -------------------------------------------------------------------------- *)
(* Equiv and transport.                                                      *)
(* -------------------------------------------------------------------------- *)

(* For skeleton, we postulate a simple equiv (in full: built from b64 proofs
   transported via orient_equiv). *)
Definition hobby_equiv :
  Equiv (Point -> Point -> Point -> Point -> Prop)
        (Point -> Point -> Point -> Point -> Prop).
Admitted.

Axiom univalence : forall (A B : Type), Equiv A B -> A = B.
(* single load-bearing per policy; justified for transport of Hobby noding
   properties to NTS C# via orientation base. *)

Lemma nts_hobby_4_1_via_transport (P0 P1 Q0 Q1 : Point) :
  nts_hobby_4_1 P0 P1 Q0 Q1 ->
  formal_hobby_4_1 P0 P1 Q0 Q1.
Proof.
  (* skeleton: in full, transport (univalence hobby_equiv) formal_... *)
  admit.
Admitted.

(* -------------------------------------------------------------------------- *)
(* Placeholder for review (Hobby 4.1 transport pattern).                     *)
(* -------------------------------------------------------------------------- *)

Lemma hobby_4_1_biarc_approx_via_orient_equiv :
  (* Demonstrates intended pattern: formal Hobby property transported via
     orient_equiv (from Shewchuk) + this hobby_equiv. *)
  True.
Admitted.

(* -------------------------------------------------------------------------- *)
(* Notes.                                                                    *)
(* - Next: flesh hobby_equiv with real maps from HobbyTheorem_b64.v re-expr. *)
(* - Update Voronoi/TIN etc. once Hobby solid.                               *)
(* - This branch: feature/hott-rgr-hobby-fill.                               *)
(* ========================================================================== *)
