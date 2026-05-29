(* ============================================================================
   NetTopologySuite.Proofs.OverlayGraph
   ----------------------------------------------------------------------------
   Phase 3 Milestone 2: the planar topology graph representation.

   `TopologyGraph` is a planar graph whose vertices are points in the
   plane (the snap-rounded intersection vertices of a noded
   arrangement) and whose edges are inter-vertex line segments, each
   carrying a label (`EdgeLabel`) that records which input geometries
   the edge belongs to in a binary overlay operation.

   This is the second link of the Phase 3 proof chain
   (docs/audit-phase3-overlay.md §1):

       Link 2: fully_intersected segs ->
               valid_topology_graph (build_graph segs)

   The graph TYPE lands here; the `build_graph` FUNCTION and the
   noding-to-graph bridge land in Milestone 3.  This file delivers:

     - the `TopologyGraph` record (vertices, edges with EdgeLabel),
     - the `valid_topology_graph` well-formedness predicate (every
       edge's endpoints appear in the vertex list),
     - construction helpers (`empty_graph`, `add_vertex`, `add_edge`),
     - five Qed-closed structural lemmas confirming the construction
       helpers compose under the validity predicate.

   ----------------------------------------------------------------------------
   Representation choice (Shape Y -- separate validity predicate).

   Two shapes were considered:

     Shape X.  Dependent record: a `tg_wf` proof field baked in.
       Pros: every TopologyGraph is automatically valid.
       Cons: construction requires providing the proof at the record
         literal, awkward for `build_graph` to assemble incrementally.

     Shape Y.  Separate predicate.
       Pros: construction helpers are simple record-updates; the
         validity predicate composes with `valid_geometry` (Milestone 1
         used the same pattern -- `Geometry := list Polygon` plus a
         separate `valid_geometry`).
       Cons: every downstream lemma carries `valid_topology_graph g`
         as a hypothesis.

   Shape Y is the corpus-consistent choice.  Matches Milestone 1's
   `valid_geometry` pattern, and makes `build_graph` (Milestone 3) a
   plain Fixpoint instead of a dependent-record assembler.

   ----------------------------------------------------------------------------
   Deferred from this milestone (registered in audit-phase3-overlay.md
   §3.7):

     - Decidable `Point` equality + the `has_vertex` lookup helper.
       Not needed by the five structural lemmas in this milestone;
       Milestone 3 picks it up alongside `build_graph`.

   ----------------------------------------------------------------------------
   Audit footprint.  Imports `From Stdlib Require Import List` and the
   corpus's `Distance` (for `Point`).  No Flocq dependency; no
   `Classical_Prop.classic` pull; not listed in
   docs/audit-exceptions.txt.  No `Admitted` / `Axiom` / `Parameter`.
   Closed under the global context (no axioms at all).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import List.
From Stdlib Require Import Reals.
From NTS.Proofs Require Import Distance.

Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  Edge label.                                                            *)
(* -------------------------------------------------------------------------- *)

(* An edge in the topology graph carries two boolean flags recording
   which of the two input geometries the edge belongs to in a binary
   overlay operation.  The labelling rule per BooleanOp lives in
   Milestone 4 (`correct_labels`); this record is the carrier. *)
Record EdgeLabel : Type := mkEdgeLabel {
  in_left  : bool;
  in_right : bool
}.

(* -------------------------------------------------------------------------- *)
(* §2  Topology graph.                                                        *)
(* -------------------------------------------------------------------------- *)

(* A topology graph is a vertex list paired with an edge list.  Each
   edge is a triple of its two endpoints plus the edge label.  The
   well-formedness predicate `valid_topology_graph` (below) requires
   that every edge's endpoints appear in the vertex list. *)
Record TopologyGraph : Type := mkTopologyGraph {
  tg_vertices : list Point;
  tg_edges    : list (Point * Point * EdgeLabel)
}.

(* Well-formedness: every edge's endpoints lie in the vertex list.
   Matches Milestone 1's separate-predicate pattern (`valid_geometry`
   over `Geometry := list Polygon`). *)
Definition valid_topology_graph (g : TopologyGraph) : Prop :=
  forall p q l,
    In (p, q, l) (tg_edges g) ->
    In p (tg_vertices g) /\ In q (tg_vertices g).

(* -------------------------------------------------------------------------- *)
(* §3  Construction helpers.                                                  *)
(* -------------------------------------------------------------------------- *)

(* The empty graph: no vertices, no edges.  The base case for
   incremental construction in Milestone 3's `build_graph`. *)
Definition empty_graph : TopologyGraph := {|
  tg_vertices := [];
  tg_edges    := []
|}.

(* Add a vertex to the graph.  Vertices are stored as a list; duplicates
   are allowed at this level (deduplication is a Milestone 3 concern,
   when decidable Point equality is in scope). *)
Definition add_vertex (p : Point) (g : TopologyGraph) : TopologyGraph := {|
  tg_vertices := p :: tg_vertices g;
  tg_edges    := tg_edges g
|}.

(* Add an edge to the graph.  The caller is responsible for ensuring
   that `p` and `q` are already in the vertex list -- the
   `valid_topology_graph_add_edge` lemma below makes this precondition
   explicit. *)
Definition add_edge (p q : Point) (l : EdgeLabel) (g : TopologyGraph)
  : TopologyGraph := {|
  tg_vertices := tg_vertices g;
  tg_edges    := (p, q, l) :: tg_edges g
|}.

(* -------------------------------------------------------------------------- *)
(* §4  Structural lemmas.                                                     *)
(*                                                                            *)
(* Five warmup theorems confirming the construction helpers compose          *)
(* under `valid_topology_graph`.  Each closes by elementary list-membership  *)
(* reasoning; none requires a Point-equality decision.                        *)
(* -------------------------------------------------------------------------- *)

(* The empty graph is vacuously valid. *)
Lemma valid_topology_graph_empty : valid_topology_graph empty_graph.
Proof.
  intros p q l Hin. simpl in Hin. contradiction.
Qed.

(* Adding a vertex preserves validity: existing edges' endpoints remain
   in the (now larger) vertex list. *)
Lemma valid_topology_graph_add_vertex :
  forall p g,
    valid_topology_graph g ->
    valid_topology_graph (add_vertex p g).
Proof.
  intros p g Hg q r l Hin.
  unfold add_vertex in Hin. simpl in Hin.
  specialize (Hg q r l Hin) as [Hq Hr].
  split; simpl; right; assumption.
Qed.

(* Adding an edge preserves validity when both endpoints are already in
   the vertex list.  The precondition makes the well-formedness invariant
   explicit. *)
Lemma valid_topology_graph_add_edge :
  forall p q l g,
    valid_topology_graph g ->
    In p (tg_vertices g) ->
    In q (tg_vertices g) ->
    valid_topology_graph (add_edge p q l g).
Proof.
  intros p q l g Hg Hp Hq r s lab Hin.
  unfold valid_topology_graph in *.
  simpl in *.
  destruct Hin as [Heq | Hin'].
  - inversion Heq. subst r s lab. split; assumption.
  - apply (Hg r s lab). exact Hin'.
Qed.

(* Edge endpoints are in the vertex set.  An immediate restatement of
   `valid_topology_graph`'s definition; included for the proof chain's
   readability in Milestone 3 (where `build_graph`'s output is
   destructured against this lemma rather than against the raw
   definition). *)
Lemma tg_edge_endpoints_in_vertices :
  forall g p q l,
    valid_topology_graph g ->
    In (p, q, l) (tg_edges g) ->
    In p (tg_vertices g) /\ In q (tg_vertices g).
Proof.
  intros g p q l Hg Hin. unfold valid_topology_graph in Hg.
  apply (Hg p q l). exact Hin.
Qed.

(* The empty graph has no edges. *)
Lemma empty_graph_no_edges : tg_edges empty_graph = [].
Proof.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Phase 3 Milestone 3: `build_graph`.                                    *)
(*                                                                            *)
(* Discretization-operator-shaped construction of a TopologyGraph from a      *)
(* list of snap-rounded segments.  Mirrors Hobby's `D_T(A)` informally:       *)
(* collect endpoints as vertices (deduplicated), emit one edge per input     *)
(* segment with a `default_label`.  Labels are assigned in Milestone 4        *)
(* (`correct_labels`).                                                        *)
(*                                                                            *)
(* TYPE NOTE.  The Phase 2 noding infrastructure                              *)
(* (`fully_intersected`, `snap_round_segments`,                               *)
(*  `hobby_theorem_4_1_conditional`) is stated over `list (Point * Point)`,   *)
(* not `list Segment` from theories/Segment.v.  build_graph therefore takes   *)
(* `list (Point * Point)` to compose with the Phase 2 corpus without a        *)
(* coercion layer.  Milestone 3's audit-doc sketch suggested `list Segment`; *)
(* this milestone's grep confirmed the noding types use point pairs, so the  *)
(* coercion is unnecessary.                                                   *)
(* -------------------------------------------------------------------------- *)

(* Decidable equality on Point, required by `List.nodup` for vertex
   deduplication.  Uses Stdlib's `Req_EM_T` on each coordinate.  Axioms
   inherited: the two README-allowlisted classical-reals decidability
   axioms (`ClassicalDedekindReals.sig_not_dec`, `sig_forall_dec`).  No
   `Classical_Prop.classic`. *)
Definition point_eq_dec (p q : Point) : {p = q} + {p <> q}.
Proof.
  destruct p as [px1 py1]. destruct q as [px2 py2].
  destruct (Req_EM_T px1 px2) as [Hx | Hx].
  - destruct (Req_EM_T py1 py2) as [Hy | Hy].
    + left. subst. reflexivity.
    + right. intros H. inversion H. contradiction.
  - right. intros H. inversion H. contradiction.
Defined.

(* Collect all endpoints from a list of segment-pairs. *)
Definition segment_endpoints (segs : list (Point * Point)) : list Point :=
  List.flat_map (fun s => [fst s; snd s]) segs.

(* Deduplicated vertex list. *)
Definition dedup_vertices (pts : list Point) : list Point :=
  List.nodup point_eq_dec pts.

(* Default unlabelled edge label; Milestone 4 fills in the real labels. *)
Definition default_label : EdgeLabel := {|
  in_left  := false;
  in_right := false
|}.

(* The Phase 3 Milestone 3 headline: a function constructing a
   TopologyGraph from a list of snap-rounded segment pairs. *)
Definition build_graph (segs : list (Point * Point)) : TopologyGraph := {|
  tg_vertices := dedup_vertices (segment_endpoints segs);
  tg_edges    := List.map
                   (fun s => (fst s, snd s, default_label))
                   segs
|}.

(* -------------------------------------------------------------------------- *)
(* §6  Structural correctness of `build_graph`.                                *)
(* -------------------------------------------------------------------------- *)

(* Helper: a segment's first endpoint is in the endpoint list. *)
Lemma segment_endpoints_fst :
  forall s segs,
    In s segs ->
    In (fst s) (segment_endpoints segs).
Proof.
  intros s segs Hin. unfold segment_endpoints.
  apply List.in_flat_map. exists s. split.
  - exact Hin.
  - simpl. left. reflexivity.
Qed.

(* Helper: a segment's second endpoint is in the endpoint list. *)
Lemma segment_endpoints_snd :
  forall s segs,
    In s segs ->
    In (snd s) (segment_endpoints segs).
Proof.
  intros s segs Hin. unfold segment_endpoints.
  apply List.in_flat_map. exists s. split.
  - exact Hin.
  - simpl. right. left. reflexivity.
Qed.

(* The Phase 3 Milestone 3 correctness theorem: every `build_graph` of a
   segment list satisfies `valid_topology_graph`.  Structural -- no
   `fully_intersected` precondition needed at this level.  The
   topology-aware bridge (linking `fully_intersected` from Phase 2 to
   downstream label-correctness via `hobby_theorem_4_1_conditional`)
   lands in Milestone 4 when `extract_segments` and `noded_segments`
   get concrete definitions. *)
Theorem valid_topology_graph_build_graph :
  forall segs : list (Point * Point),
    valid_topology_graph (build_graph segs).
Proof.
  intros segs.
  unfold valid_topology_graph, build_graph. simpl.
  intros p q l Hedge.
  apply List.in_map_iff in Hedge.
  destruct Hedge as [s [Heq Hin]].
  inversion Heq. subst.
  split.
  - apply (proj2 (List.nodup_In point_eq_dec _ _)).
    apply segment_endpoints_fst. exact Hin.
  - apply (proj2 (List.nodup_In point_eq_dec _ _)).
    apply segment_endpoints_snd. exact Hin.
Qed.

(* The empty segment list yields the empty graph. *)
Lemma build_graph_nil : build_graph [] = empty_graph.
Proof.
  reflexivity.
Qed.
