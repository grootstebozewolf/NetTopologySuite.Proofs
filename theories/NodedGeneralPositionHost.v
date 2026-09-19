(* ============================================================================
   NetTopologySuite.Proofs.NodedGeneralPositionHost
   ----------------------------------------------------------------------------
   #518 core slice: from "fully intersected" (Hobby's input invariant, read on
   the host lane) plus ONE NAMED side condition to `noded_general_position`.

   Host reading.  Overlay.v carries `segments_intersect_properly` (a textual
   twin of theories-flocq/HobbyTheorem_b64.v's) but NO "only at endpoints"
   predicate.  So this sibling defines, on `list Edge` with Overlay's proper
   crossing:

     segments_intersect_only_at_endpoints_host s1 s2 :=
       ~ properly-cross  \/  share_endpoint s1 s2
     fully_intersected_host S :=
       every distinct pair of S meets only at endpoints (host)

   -- the same shape as HobbyTheorem_b64.fully_intersected, without
   Requiring that module (flocq lane).

   The named side condition (do not hide it):

     shared_endpoints_noncollinear S :=
       distinct segments of S that share an endpoint have non-parallel
       directions (seg_dir_cross <> 0).

   Result:  fully_intersected_host S -> shared_endpoints_noncollinear S ->
            noded_general_position S              (noded_gp_of_fully_intersected_host)

   Honesty.  The side condition is NECESSARY: slice 3i's collinear pair
   [gp_cx_long; gp_cx_short] IS fully_intersected_host (they share (0,0)),
   fails shared_endpoints_noncollinear (seg_dir_cross = 0), and is not in
   general position (NodedGeneralPosition.collinear_pair_not_gp).  So the
   arrow without the second conjunct is false (side_condition_necessary).

   QEX residue.  The lemma
       HobbyTheorem_b64.fully_intersected segs -> fully_intersected_host segs
   is a named missing constructor here (HobbyFullyIntersectedToHost): it
   cannot be stated without Requiring the flocq module, and Overlay's
   only-at-endpoints predicate does not exist to be definitionally Hobby's.
   Not imported to force it.

   Not: well_noded_darts, extract_rings_valid unconditional, #519 / #520,
   Hobby 4.1, OverlayNG headline, first_cook_scope, Karney, ADR status.
   NodedGeneralPosition.v is not edited.

   WITNESS topic: overlay · claimId: 518-core-host · witness: 518-core-host
   3-axiom (Stdlib Reals). No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay NodedGeneralPosition.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Host predicates.                                                       *)
(* -------------------------------------------------------------------------- *)

Definition segments_intersect_only_at_endpoints_host (s1 s2 : Edge) : Prop :=
  ~ segments_intersect_properly (fst s1) (snd s1) (fst s2) (snd s2)
  \/ share_endpoint s1 s2.

Definition fully_intersected_host (S : list Edge) : Prop :=
  forall s1 s2 : Edge,
    In s1 S -> In s2 S -> s1 <> s2 ->
    segments_intersect_only_at_endpoints_host s1 s2.

(* THE SIDE CONDITION, named. *)
Definition shared_endpoints_noncollinear (S : list Edge) : Prop :=
  forall s1 s2 : Edge,
    In s1 S -> In s2 S -> s1 <> s2 ->
    share_endpoint s1 s2 -> seg_dir_cross s1 s2 <> 0.

(* -------------------------------------------------------------------------- *)
(* §2  The arrow.                                                             *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"518-core-host","topic":"overlay","lemma":"noded_gp_of_fully_intersected_host","title":"fully_intersected_host S and the named side condition shared_endpoints_noncollinear S imply noded_general_position S on list Edge, host lane","file":"theories/NodedGeneralPositionHost.v","witness":"518-core-host"} *)
Theorem noded_gp_of_fully_intersected_host :
  forall S : list Edge,
    fully_intersected_host S ->
    shared_endpoints_noncollinear S ->
    noded_general_position S.
Proof.
  intros S Hfi Hsc s1 s2 H1 H2 Hne.
  destruct (Hfi s1 s2 H1 H2 Hne) as [Hnp | Hsh].
  - left. exact Hnp.
  - right. split; [ exact Hsh | exact (Hsc s1 s2 H1 H2 Hne Hsh) ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Honesty: the side condition is necessary.                              *)
(* -------------------------------------------------------------------------- *)

Lemma gp_cx_distinct : gp_cx_long <> gp_cx_short.
Proof.
  unfold gp_cx_long, gp_cx_short. intro H. inversion H as [H1].
  assert (px (mkPoint 2 0) = px (mkPoint 1 0)) by (rewrite H1; reflexivity).
  cbn in *. lra.
Qed.

Lemma collinear_pair_shares : share_endpoint gp_cx_long gp_cx_short.
Proof. left. reflexivity. Qed.

Lemma collinear_pair_cross_zero : seg_dir_cross gp_cx_long gp_cx_short = 0.
Proof. unfold seg_dir_cross, gp_cx_long, gp_cx_short. cbn. ring. Qed.

(* The collinear pair IS fully intersected on the host reading: it shares
   (0,0), so the shared-endpoint disjunct absorbs the proper crossing. *)
Lemma collinear_pair_fully_intersected_host :
  fully_intersected_host [gp_cx_long; gp_cx_short].
Proof.
  intros s1 s2 H1 H2 Hne.
  destruct H1 as [<- | [<- | []]]; destruct H2 as [<- | [<- | []]];
    try (exfalso; apply Hne; reflexivity).
  - right. left. reflexivity.
  - right. left. reflexivity.
Qed.

Lemma collinear_pair_not_side :
  ~ shared_endpoints_noncollinear [gp_cx_long; gp_cx_short].
Proof.
  intro Hsc.
  apply (Hsc gp_cx_long gp_cx_short (or_introl eq_refl) (or_intror (or_introl eq_refl))
           gp_cx_distinct collinear_pair_shares).
  exact collinear_pair_cross_zero.
Qed.

(* WITNESS {"claimId":"518-core-host","topic":"overlay","lemma":"side_condition_necessary","title":"the arrow fully_intersected_host -> noded_general_position is false without the side condition: the collinear pair (0,0)-(2,0), (0,0)-(1,0) is fully intersected on the host reading yet not in general position","file":"theories/NodedGeneralPositionHost.v","witness":"518-core-host"} *)
Theorem side_condition_necessary :
  ~ (forall S : list Edge, fully_intersected_host S -> noded_general_position S).
Proof.
  intro Harrow.
  exact (collinear_pair_not_gp (Harrow _ collinear_pair_fully_intersected_host)).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The Hobby bridge stays a named missing constructor.                    *)
(* -------------------------------------------------------------------------- *)

(* Intended statement (not statable here without Requiring the flocq lane):
     HobbyTheorem_b64.fully_intersected segs -> fully_intersected_host segs.
   Hobby's segments_intersect_properly is a textual copy of Overlay's, so in
   a lane that sees both the bridge is an unfolding; Overlay itself carries
   no only-at-endpoints predicate, so it is not definitionally Hobby's. *)
Inductive HobbyBridgePark : Type :=
| HobbyFullyIntersectedToHost.

Definition hobby_bridge_inhabits (_ : HobbyBridgePark) : Prop := False.

Lemma hobby_fully_intersected_to_host_missing :
  ~ hobby_bridge_inhabits HobbyFullyIntersectedToHost.
Proof. intro H. exact H. Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Ticket stop.                                                           *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"518-core-host","topic":"overlay","lemma":"ticket_518_core_qed_or_qex","title":"#518 core slice: host arrow fully_intersected_host + shared_endpoints_noncollinear -> noded_general_position, side condition necessary, and the Hobby fully_intersected -> host bridge inhabited (QED); or the host arrow and necessity hold while the Hobby bridge stays a named missing constructor because Overlay has no only-at-endpoints predicate and the flocq module is not Required (QEX); discharged QEX","file":"theories/NodedGeneralPositionHost.v","witness":"518-core-host"} *)
Theorem ticket_518_core_qed_or_qex :
  ((forall S, fully_intersected_host S -> shared_endpoints_noncollinear S ->
      noded_general_position S)
   /\ ~ (forall S, fully_intersected_host S -> noded_general_position S)
   /\ hobby_bridge_inhabits HobbyFullyIntersectedToHost)
  \/
  ((forall S, fully_intersected_host S -> shared_endpoints_noncollinear S ->
      noded_general_position S)
   /\ ~ (forall S, fully_intersected_host S -> noded_general_position S)
   /\ ~ shared_endpoints_noncollinear [gp_cx_long; gp_cx_short]
   /\ ~ hobby_bridge_inhabits HobbyFullyIntersectedToHost).
Proof.
  right.
  split; [ exact noded_gp_of_fully_intersected_host | ].
  split; [ exact side_condition_necessary | ].
  split; [ exact collinear_pair_not_side | ].
  exact hobby_fully_intersected_to_host_missing.
Qed.

Print Assumptions noded_gp_of_fully_intersected_host.
Print Assumptions side_condition_necessary.
Print Assumptions ticket_518_core_qed_or_qex.
