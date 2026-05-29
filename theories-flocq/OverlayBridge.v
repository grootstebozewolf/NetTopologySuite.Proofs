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
(* -------------------------------------------------------------------------- *)
(* §4  Phase 3 Milestone 5 Session 2: correct_labels + Union case.            *)
(* -------------------------------------------------------------------------- *)

(* The geometric notion of "edge (p, q) belongs to the boolean-op result"
   for each operation, stated over snap-rounded segments. *)
Definition edge_geometrically_in_result
    (op : BooleanOp) (p q : Point) (A B : Geometry) : Prop :=
  let A_seg := snap_round_segments (extract_segments A) in
  let B_seg := snap_round_segments (extract_segments B) in
  match op with
  | Union =>
      In (p, q) A_seg \/ In (p, q) B_seg
  | Intersection =>
      In (p, q) A_seg /\ In (p, q) B_seg
  | Difference =>
      In (p, q) A_seg /\ ~ In (p, q) B_seg
  | SymDiff =>
      (In (p, q) A_seg /\ ~ In (p, q) B_seg) \/
      (In (p, q) B_seg /\ ~ In (p, q) A_seg)
  end.

(* The labelling-correctness predicate: every edge's computable label
   agrees with the geometric "is in result" condition. *)
Definition correct_labels
    (op : BooleanOp) (g : TopologyGraph)
    (A B : Geometry) : Prop :=
  forall p q l,
    In (p, q, l) (tg_edges g) ->
    edge_in_result op l = true <->
    edge_geometrically_in_result op p q A B.

(* -------------------------------------------------------------------------- *)
(* §5  correct_labels for Union -- directly Qed-closed.                       *)
(*                                                                            *)
(* The Union case is structurally trivial under M4's labelling scheme:        *)
(*   - Edges from `label_from_A` have `in_left := true`, so                   *)
(*     `edge_in_result Union l = orb true _ = true` AND the edge is in A's    *)
(*     snap-rounded segments.                                                 *)
(*   - Edges from `label_from_B` have `in_right := true`, symmetric.          *)
(* Both sides of the iff are always true; both directions discharge by       *)
(* construction.                                                              *)
(* -------------------------------------------------------------------------- *)

Theorem correct_labels_union :
  forall (A B : Geometry),
    correct_labels Union (noded_labeled_graph A B) A B.
Proof.
  intros A B p q l Hin.
  unfold noded_labeled_graph, build_labeled_graph in Hin. simpl in Hin.
  apply List.in_app_iff in Hin.
  unfold edge_in_result, edge_geometrically_in_result. simpl.
  destruct Hin as [HA | HB].
  - (* Edge from A: in_left l = true.  Both sides hold. *)
    unfold label_from_A in HA.
    apply List.in_map_iff in HA.
    destruct HA as [s [Heq Hin']].
    destruct s as [s_p s_q]. simpl in Heq.
    inversion Heq. subst.
    simpl. split.
    + intros _. left. exact Hin'.
    + intros _. reflexivity.
  - (* Edge from B: in_right l = true.  Both sides hold. *)
    unfold label_from_B in HB.
    apply List.in_map_iff in HB.
    destruct HB as [s [Heq Hin']].
    destruct s as [s_p s_q]. simpl in Heq.
    inversion Heq. subst.
    simpl. split.
    + intros _. right. exact Hin'.
    + intros _. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Intersection / Difference / SymDiff -- M4-revision finding.            *)
(*                                                                            *)
(* The audit doc (docs/audit-phase3-milestone5.md §4.4) anticipated these     *)
(* cases as Sessions 6 and 7.  Session 2 discovered that the current M4       *)
(* labelling scheme does NOT support them as-is:                              *)
(*                                                                            *)
(* Under `noded_labeled_graph A B`, an edge `(p,q)` that appears in BOTH     *)
(* A's snapped segments AND B's snapped segments is represented as TWO       *)
(* separate edges with disjoint labels (one with `in_left:=true`, one with   *)
(* `in_right:=true`).  For Intersection's `edge_in_result l =                 *)
(* andb (in_left l) (in_right l)`, neither edge satisfies the rule -- so     *)
(* Intersection would extract no edges, contradicting the geometric          *)
(* expectation that `(p,q)` IS in the intersection.                          *)
(*                                                                            *)
(* The fix: a `merge_labels` step folding over the edge list that combines   *)
(* labels for identical `(p,q)` pairs into a single edge with combined       *)
(* `{ in_left := A_has; in_right := B_has }`.  Once merged, Intersection /   *)
(* Difference / SymDiff become provable analogously to Union.                *)
(*                                                                            *)
(* This is an M4-revision item.  Documented here so Session 3+ has the gap   *)
(* on the record.  The deferred-proof registry does NOT yet contain a         *)
(* corresponding entry -- only the eventually-provable theorems do.          *)
(* Session 1.5 (DCEL adoption) is the natural place to also add label        *)
(* merging.                                                                   *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* §7  Audit footprint.                                                        *)
(* -------------------------------------------------------------------------- *)

Print Assumptions snap_noding_bridge.
Print Assumptions valid_topology_graph_noded_labeled_graph.
Print Assumptions correct_labels_union.
