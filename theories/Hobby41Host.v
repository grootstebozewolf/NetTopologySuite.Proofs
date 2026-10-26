(* ============================================================================
   NetTopologySuite.Proofs.Hobby41Host
   ----------------------------------------------------------------------------
   Hobby (1999) Theorem 4.1 on the host lane (claimId 0007-hobby-41-host).

   Finding.  There is no host_snap operator on the host lane.
   SheetHenCook.CtorSnapRound is a kind tag on OverlayNG attempts, not an
   arrangement map on list Edge. So a host theorem of the shape
     fully_intersected_host A -> fully_intersected_host (host_snap A)
   has no host_snap to be about.

   What is checked.  With snap left abstract, the 4.1 shape is vacuous:
   the identity map satisfies it (hobby_41_shape_trivial). Proving 4.1 for
   "some snap" says nothing. The real gap is a snap-rounding spec for
   host_snap, which is not built here. Any later "4.1 discharged" on the
   host lane must name that spec. A witness of the bare shape, id
   included, does not count.

   Status.  PassesThroughC2WidthPark.hobby41_host_status stays
   OverlayNGHobby41Qex. This file consumes the #805 hold; the status does
   not move.

   fully_intersected_host (NodedGeneralPositionHost.v) is the #518 hyp
   (ticket_518_core_qed_or_qex QEX arm), not a 4.1 transport. This letter
   uses that predicate; it does not remint HobbyFullyIntersectedToHost,
   noded_gp_of_fully_intersected_host, or ticket_518_core_qed_or_qex.

   Cite, do not Require, the flocq lane:
     HobbyCounterexample_b64.hobby_lemma_4_3_no_proper_is_false.
   Do not remint hobby_lemma_4_3_no_proper as true. Do not move
   HobbyTheorem_b64.v onto host _CoqProject. Do not claim Hobby 4.1
   unconditional. OverlayNG's ticket_0007_overlayng_hobby41_qed_or_qex
   (claimId 0007-overlayng-sheet) is a different park and is not reminted.

   Not: first_cook_scope, LeftoverBagTermArm, Karney, K3, ADR-0007 Status.

   Registered in _CoqProject.full only: NodedGeneralPositionHost is not on
   the host target.

   WITNESS topic: overlay · claimId: 0007-hobby-41-host
   witness: 0007-hobby-41-host · board: ADR-0007
   3-axiom (Stdlib Reals). No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import List.
From NTS.Proofs Require Import Overlay NodedGeneralPositionHost
  PassesThroughC2WidthPark.

(* The shape of Hobby 4.1 on the host lane, with snap abstract. *)
Definition hobby_41_shape (snap : list Edge -> list Edge) : Prop :=
  forall A : list Edge,
    fully_intersected_host A -> fully_intersected_host (snap A).

(* Vacuity: the identity is a witness. Without a snap-rounding spec the
   shape constrains nothing. *)
Lemma hobby_41_shape_trivial :
  exists snap : list Edge -> list Edge, hobby_41_shape snap.
Proof.
  exists (fun A => A).
  intros A HA.
  exact HA.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket stop.                                                               *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-hobby-41-host","topic":"overlay","lemma":"ticket_0007_hobby_41_host_qed_or_qex","title":"Hobby 4.1 host status is Hobby41Discharged (QED); or it is not, and the bare 4.1 shape fully_intersected_host A -> fully_intersected_host (snap A) is witnessed by the identity, so 4.1 without a host_snap spec is vacuous (QEX); discharged QEX; hobby41_host_status stays OverlayNGHobby41Qex; #518 consumed not reminted; flocq HobbyTheorem_b64 untouched","file":"theories/Hobby41Host.v","witness":"0007-hobby-41-host","board":"ADR-0007"} *)
Theorem ticket_0007_hobby_41_host_qed_or_qex :
  hobby41_host_status = Hobby41Discharged
  \/
  (hobby41_host_status <> Hobby41Discharged
   /\ exists snap : list Edge -> list Edge, hobby_41_shape snap).
Proof.
  right.
  split; [exact hobby41_not_discharged |].
  exact hobby_41_shape_trivial.
Qed.

Print Assumptions hobby_41_shape_trivial.
Print Assumptions ticket_0007_hobby_41_host_qed_or_qex.
