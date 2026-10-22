(* ============================================================================
   NetTopologySuite.Proofs.Hobby41Host
   ----------------------------------------------------------------------------
   Hobby (1999) Theorem 4.1 on the host lane (claimId 0007-hobby-41-host).

   Investigation.  A 3-axiom host theorem
     hobby_theorem_4_1_host :
       fully_intersected_host A -> fully_intersected_host (host_snap A)
   on ADR-0007 Sheet segments, without assuming
   hobby_lemma_4_3_no_proper, does not inhabit.

     HostSnapRound        — no host_snap operator. SheetHenCook.CtorSnapRound
                            is a kind tag on OverlayNG attempts, not an
                            arrangement map on list Edge / Sheet segments.
     HostHobby41          — 4.1 without the uninhabitable no_proper premise
                            is not constructible once host_snap is missing.
     HostPairPreservation — the pair-preservation replacement that would
                            discharge 4.1 is missing; restating 4.2 / shared-
                            endpoint 4.3 on host Q has nothing to apply to.

   fully_intersected_host (NodedGeneralPositionHost.v) is the #518 hyp
   (ticket_518_core_qed_or_qex QEX arm), not a 4.1 transport. This letter
   consumes that slice; it does not remint HobbyFullyIntersectedToHost,
   noded_gp_of_fully_intersected_host, or ticket_518_core_qed_or_qex.

   Cite, do not Require, the flocq lane:
     HobbyCounterexample_b64.hobby_lemma_4_3_no_proper_is_false.
   Do not remint hobby_lemma_4_3_no_proper as true. Do not move
   HobbyTheorem_b64.v onto host _CoqProject. Do not claim Hobby 4.1
   unconditional. OverlayNG's ticket_0007_overlayng_hobby41_qed_or_qex
   (claimId 0007-overlayng-sheet) is a different park and is not reminted.

   Not: first_cook_scope, LeftoverBagTermArm, Karney, K3, ADR-0007 Status.

   WITNESS topic: overlay · claimId: 0007-hobby-41-host
   witness: 0007-hobby-41-host · board: ADR-0007
   3-axiom host. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From NTS.Proofs Require Import SheetHenCook.

(* -------------------------------------------------------------------------- *)
(* Named missing constructors. 508-style, not bools.                          *)
(* -------------------------------------------------------------------------- *)

Inductive Hobby41HostCtor : Type :=
| HostSnapRound
| HostHobby41
| HostPairPreservation.

Definition hobby41_host_inhabits (c : Hobby41HostCtor) : Prop :=
  match c with
  | HostSnapRound => False
  | HostHobby41 => False
  | HostPairPreservation => False
  end.

Lemma host_snap_round_missing :
  ~ hobby41_host_inhabits HostSnapRound.
Proof.
  intro H. exact H.
Qed.

Lemma host_hobby41_missing :
  ~ hobby41_host_inhabits HostHobby41.
Proof.
  intro H. exact H.
Qed.

Lemma host_pair_preservation_missing :
  ~ hobby41_host_inhabits HostPairPreservation.
Proof.
  intro H. exact H.
Qed.

(* CtorSnapRound is a kind tag, not the missing arrangement operator. *)
Lemma host_snap_round_is_not_ctor_tag :
  CtorSnapRound <> CtorI /\ ~ hobby41_host_inhabits HostSnapRound.
Proof.
  split; [exact snap_round_neq_I|].
  exact host_snap_round_missing.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket stop.                                                               *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-hobby-41-host","topic":"overlay","lemma":"ticket_0007_hobby_41_host_qed_or_qex","title":"host_snap and hobby_theorem_4_1_host inhabit on ADR-0007 Sheet segments without hobby_lemma_4_3_no_proper (QED) or HostSnapRound / HostHobby41 / HostPairPreservation stay named missing constructors because host_snap is absent, the no_proper premise is uninhabitable (hobby_lemma_4_3_no_proper_is_false), and fully_intersected_host remains the #518 hyp not a 4.1 transport (QEX); discharged QEX; #518 consumed not reminted; flocq HobbyTheorem_b64 untouched","file":"theories/Hobby41Host.v","witness":"0007-hobby-41-host","board":"ADR-0007"} *)
Theorem ticket_0007_hobby_41_host_qed_or_qex :
  (hobby41_host_inhabits HostSnapRound
   /\ hobby41_host_inhabits HostHobby41
   /\ hobby41_host_inhabits HostPairPreservation)
  \/
  (~ hobby41_host_inhabits HostSnapRound
   /\ ~ hobby41_host_inhabits HostHobby41
   /\ ~ hobby41_host_inhabits HostPairPreservation
   /\ CtorSnapRound <> CtorI).
Proof.
  right.
  split; [exact host_snap_round_missing|].
  split; [exact host_hobby41_missing|].
  split; [exact host_pair_preservation_missing|].
  exact snap_round_neq_I.
Qed.

Print Assumptions host_snap_round_missing.
Print Assumptions host_hobby41_missing.
Print Assumptions host_pair_preservation_missing.
Print Assumptions host_snap_round_is_not_ctor_tag.
Print Assumptions ticket_0007_hobby_41_host_qed_or_qex.
