(* ============================================================================
   NetTopologySuite.Proofs.Flocq.OverlayBridge
   ----------------------------------------------------------------------------
   Phase 3 Milestone 4 (Flocq layer): the noding-to-graph bridge.

   The R-side `theories/OverlayGraph.v` ships `extract_segments`,
   `build_graph`, `edge_in_result`, `label_from_A`, `label_from_B`,
   `build_labeled_graph`, and the structural correctness theorems
   `valid_topology_graph_build_graph` and
   `valid_topology_graph_build_labeled_graph`.  All Flocq-free.

   This file connects those to the Phase 2 snap-rounding noding stack:

     - `noded_segments A B`: applies `snap_round_segments` from
       theories-flocq/HobbyTheorem_b64.v to the concatenated edge lists
       of A and B.

     - `snap_noding_bridge`: connects `fully_intersected (noded_segments
       A B)` to `valid_topology_graph (build_graph (noded_segments A B))`.
       The proof is trivial -- structural validity of `build_graph` does
       not depend on `fully_intersected`.  The statement records the
       precondition shape that downstream proofs (Milestone 5) will
       discharge via `hobby_theorem_4_1_conditional`.

     - `noded_labeled_graph A B`: applies snap-rounding to each input
       geometry separately and assembles a labelled topology graph via
       M4's `build_labeled_graph`.

     - `valid_topology_graph_noded_labeled_graph`: the labelled-graph
       version of the bridge.  Also trivial, lifting the R-side
       structural correctness through the snap-rounding step.

   ----------------------------------------------------------------------------
   Audit footprint.  This file imports `theories-flocq/HobbyTheorem_b64.v`
   for `snap_round_segments`, which pulls `Classical_Prop.classic` via
   Flocq's binary arithmetic closure.  Listed in docs/audit-exceptions.txt
   for the Category C lineage.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import List.

From NTS.Proofs        Require Import Distance.
From NTS.Proofs        Require Import Overlay.
From NTS.Proofs        Require Import OverlayGraph.
From NTS.Proofs.Flocq  Require Import HobbyTheorem_b64.

Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  noded_segments: A and B's segments, snap-rounded together.             *)
(* -------------------------------------------------------------------------- *)

(* The Phase 3 noding input: concatenate the edges of A and B (R-side,
   no snapping yet), then apply snap_round_segments (Flocq layer) to
   produce the snap-rounded arrangement. *)
Definition noded_segments (A B : Geometry) : list (Point * Point) :=
  snap_round_segments (extract_segments A ++ extract_segments B).

(* -------------------------------------------------------------------------- *)
(* §2  snap_noding_bridge: the Link 2 statement of Phase 3.                   *)
(* -------------------------------------------------------------------------- *)

(* Valid input geometries with a fully-intersected noded arrangement
   produce a valid topology graph.  Proof: the structural M3 theorem
   `valid_topology_graph_build_graph` holds for any segment list, so
   the bridge is a forgetful composition.

   The `fully_intersected` precondition is the connection point for
   `hobby_theorem_4_1_conditional` from theories-flocq/HobbyTheorem_b64.v:
   given a fully-intersected R-side arrangement plus Hobby Lemma 4.3,
   `hobby_theorem_4_1_conditional` yields `fully_intersected
   (snap_round_segments _)` -- precisely this hypothesis. *)
Theorem snap_noding_bridge :
  forall (A B : Geometry),
    valid_geometry A ->
    valid_geometry B ->
    fully_intersected (noded_segments A B) ->
    valid_topology_graph (build_graph (noded_segments A B)).
Proof.
  intros A B _ _ _.
  apply valid_topology_graph_build_graph.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  noded_labeled_graph: assemble a labelled graph from snap-rounded       *)
(*     A and B separately so the labels can be assigned per source.           *)
(* -------------------------------------------------------------------------- *)

(* Snap-round each input geometry's edges separately, then assemble
   into a labelled topology graph via M4's `build_labeled_graph`.
   Labels: A's edges get `in_left := true`, B's edges get `in_right := true`. *)
Definition noded_labeled_graph (A B : Geometry) : TopologyGraph :=
  build_labeled_graph
    (snap_round_segments (extract_segments A))
    (snap_round_segments (extract_segments B)).

(* The labelled-graph version of the bridge.  Same shape as
   `snap_noding_bridge` but for `build_labeled_graph`. *)
Theorem valid_topology_graph_noded_labeled_graph :
  forall (A B : Geometry),
    valid_topology_graph (noded_labeled_graph A B).
Proof.
  intros A B. unfold noded_labeled_graph.
  apply valid_topology_graph_build_labeled_graph.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Audit footprint.                                                        *)
(* -------------------------------------------------------------------------- *)

Print Assumptions snap_noding_bridge.
Print Assumptions valid_topology_graph_noded_labeled_graph.
