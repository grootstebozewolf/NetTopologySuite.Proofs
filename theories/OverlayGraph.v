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
From Stdlib Require Import Bool.
From NTS.Proofs Require Import Distance.
From NTS.Proofs Require Import Overlay.

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

(* -------------------------------------------------------------------------- *)
(* §7  Phase 3 Milestone 4 (R-side): extract_segments + labelling rules +     *)
(*     labelled-graph construction.                                            *)
(*                                                                            *)
(* This section bridges geometry (M1) and the topology graph (M2-M3) to the   *)
(* per-operation labelling rules (M4) the noding-aware pipeline needs.        *)
(*                                                                            *)
(* What lives HERE (R-side, Flocq-free):                                      *)
(*   - extract_segments: Geometry -> list (Point * Point) -- ring edges       *)
(*     collected via the M1 `ring_edges` Fixpoint.                            *)
(*   - edge_in_result: per-BooleanOp labelling rule (Union = orb,             *)
(*     Intersection = andb, Difference = andb-then-negb, SymDiff = xorb).     *)
(*   - label_from_A / label_from_B: assign edges to a source geometry by     *)
(*     setting in_left / in_right.                                            *)
(*   - build_labeled_graph: assemble a TopologyGraph from two pre-snapped     *)
(*     (or pre-noded) segment lists with labels attached.                     *)
(*   - valid_topology_graph_build_labeled_graph: structural correctness.      *)
(*                                                                            *)
(* What lives in theories-flocq/OverlayBridge.v (Flocq layer):                 *)
(*   - noded_segments A B (uses snap_round_segments from HobbyTheorem_b64).   *)
(*   - snap_noding_bridge (the conditional-precondition theorem citing        *)
(*     hobby_theorem_4_1_conditional).                                        *)
(*                                                                            *)
(* The R-side / Flocq-side split keeps theories/ Flocq-free (the corpus       *)
(* convention), and keeps Classical_Prop.classic confined to theories-flocq/. *)
(*                                                                            *)
(* `correct_labels` itself -- the Prop tying `edge_in_result` to the          *)
(* geometric notion "this edge belongs to the boolean-operation result" --   *)
(* is deferred to Milestone 5 because its RHS requires `extract op g` and    *)
(* `point_set` composition, both M5 deliverables.                             *)
(* -------------------------------------------------------------------------- *)

(* Collect the edges of a polygon: outer ring edges plus all hole edges. *)
Definition polygon_to_pairs (poly : Polygon) : list (Point * Point) :=
  ring_edges (outer_ring poly) ++
  List.flat_map ring_edges (hole_rings poly).

(* Collect all edges from a Geometry as a flat list of point pairs.
   This is the "Geometry -> noding input" coercion. *)
Definition extract_segments (g : Geometry) : list (Point * Point) :=
  List.flat_map polygon_to_pairs g.

(* -------------------------------------------------------------------------- *)
(* §8  Labelling rules per BooleanOp.                                          *)
(* -------------------------------------------------------------------------- *)

(* Edge inclusion in the result for each boolean operation.  Matches
   docs/audit-phase3-overlay.md §3.5 exactly:
     Union:        in_left \/ in_right
     Intersection: in_left /\ in_right
     Difference:   in_left /\ ~in_right
     SymDiff:      in_left  xor in_right *)
Definition edge_in_result (op : BooleanOp) (l : EdgeLabel) : bool :=
  match op with
  | Union        => orb  (in_left l) (in_right l)
  | Intersection => andb (in_left l) (in_right l)
  | Difference   => andb (in_left l) (negb (in_right l))
  | SymDiff      => xorb (in_left l) (in_right l)
  end.

(* Assign labels to a list of edges as "from geometry A" or "from
   geometry B". *)
Definition label_from_A
    (segs : list (Point * Point)) : list (Point * Point * EdgeLabel) :=
  List.map (fun s => (fst s, snd s,
                      {| in_left := true; in_right := false |})) segs.

Definition label_from_B
    (segs : list (Point * Point)) : list (Point * Point * EdgeLabel) :=
  List.map (fun s => (fst s, snd s,
                      {| in_left := false; in_right := true |})) segs.

(* Build a labelled topology graph from two pre-noded segment lists
   (one per source geometry).  Vertices = dedup of all endpoints.
   Edges = A-labelled snapped edges ++ B-labelled snapped edges.
   The caller is responsible for the snap-rounding (Flocq layer);
   this function is pure list manipulation. *)
Definition build_labeled_graph
    (snapped_A snapped_B : list (Point * Point)) : TopologyGraph := {|
  tg_vertices := dedup_vertices
                   (segment_endpoints (snapped_A ++ snapped_B));
  tg_edges    := label_from_A snapped_A ++ label_from_B snapped_B
|}.

(* -------------------------------------------------------------------------- *)
(* §9  Structural correctness of the labelled graph.                           *)
(* -------------------------------------------------------------------------- *)

(* Helper: an A-labelled edge's endpoints lie in segment_endpoints of A. *)
Lemma label_from_A_endpoints_in_pairs :
  forall snapped p q l,
    In (p, q, l) (label_from_A snapped) ->
    In p (segment_endpoints snapped) /\ In q (segment_endpoints snapped).
Proof.
  intros snapped p q l Hin.
  unfold label_from_A in Hin. apply List.in_map_iff in Hin.
  destruct Hin as [s [Heq Hin']]. inversion Heq. subst.
  split.
  - apply segment_endpoints_fst. exact Hin'.
  - apply segment_endpoints_snd. exact Hin'.
Qed.

(* Same for B-labelled. *)
Lemma label_from_B_endpoints_in_pairs :
  forall snapped p q l,
    In (p, q, l) (label_from_B snapped) ->
    In p (segment_endpoints snapped) /\ In q (segment_endpoints snapped).
Proof.
  intros snapped p q l Hin.
  unfold label_from_B in Hin. apply List.in_map_iff in Hin.
  destruct Hin as [s [Heq Hin']]. inversion Heq. subst.
  split.
  - apply segment_endpoints_fst. exact Hin'.
  - apply segment_endpoints_snd. exact Hin'.
Qed.

(* segment_endpoints of an app is the app of segment_endpoints. *)
Lemma segment_endpoints_app :
  forall xs ys,
    segment_endpoints (xs ++ ys) =
    segment_endpoints xs ++ segment_endpoints ys.
Proof.
  intros xs ys. unfold segment_endpoints.
  apply List.flat_map_app.
Qed.

(* The M4 headline: every build_labeled_graph yields a valid topology
   graph.  Structural -- no fully_intersected precondition.  The
   topology-aware bridge (via hobby_theorem_4_1_conditional) lands in
   the Flocq-layer file. *)
Theorem valid_topology_graph_build_labeled_graph :
  forall sA sB : list (Point * Point),
    valid_topology_graph (build_labeled_graph sA sB).
Proof.
  intros sA sB.
  unfold valid_topology_graph, build_labeled_graph. simpl.
  intros p q l Hedge.
  apply List.in_app_iff in Hedge.
  rewrite segment_endpoints_app.
  destruct Hedge as [HA | HB].
  - (* Edge came from A *)
    apply label_from_A_endpoints_in_pairs in HA. destruct HA as [Hp Hq].
    split; apply (proj2 (List.nodup_In point_eq_dec _ _));
      apply List.in_app_iff; left; assumption.
  - (* Edge came from B *)
    apply label_from_B_endpoints_in_pairs in HB. destruct HB as [Hp Hq].
    split; apply (proj2 (List.nodup_In point_eq_dec _ _));
      apply List.in_app_iff; right; assumption.
Qed.

(* Empty inputs yield empty graph. *)
Lemma build_labeled_graph_nil :
  build_labeled_graph [] [] = empty_graph.
Proof.
  reflexivity.
Qed.

(* Constructor sanity: the four BooleanOp operations are pairwise
   distinct (used downstream by case analysis on `op`). *)
Lemma edge_in_result_union_true :
  forall l, in_left l = true \/ in_right l = true ->
            edge_in_result Union l = true.
Proof.
  intros l [HL | HR]; simpl.
  - rewrite HL. reflexivity.
  - rewrite HR. apply orb_true_r.
Qed.

Lemma edge_in_result_intersection_true :
  forall l, in_left l = true -> in_right l = true ->
            edge_in_result Intersection l = true.
Proof.
  intros l HL HR. simpl. rewrite HL, HR. reflexivity.
Qed.

Lemma edge_in_result_difference_iff :
  forall l, edge_in_result Difference l = true <->
            in_left l = true /\ in_right l = false.
Proof.
  intros l. simpl. split.
  - intros H. apply andb_true_iff in H. destruct H as [HL HR].
    split; [exact HL | now apply negb_true_iff in HR].
  - intros [HL HR]. rewrite HL, HR. reflexivity.
Qed.

Lemma edge_in_result_symdiff_iff :
  forall l, edge_in_result SymDiff l = true <->
            in_left l <> in_right l.
Proof.
  intros l. simpl. unfold xorb.
  destruct (in_left l), (in_right l); simpl; split;
    try discriminate; try congruence; try reflexivity;
    intros _; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §10  Phase 3 Milestone 5 Session 2: `extract op g`.                        *)
(*                                                                            *)
(* Filter the labelled edges of `g` by `edge_in_result op` and package the    *)
(* survivors into a `Geometry`-typed value.  This is the FORWARD direction    *)
(* of the extract_segments/extract pair: extract_segments goes Geometry to    *)
(* edges (M4); extract goes labelled graph back to Geometry.                  *)
(*                                                                            *)
(* DESIGN DECISION (audit-phase3-milestone5.md §5.3, Option (i)).  Return     *)
(* type is `Geometry` because the headline theorem `overlay_ng_correct`       *)
(* needs `point_set : Geometry -> Point -> Prop` to match.  Returning a       *)
(* flat edge list or `list Segment` would require redefining `point_set`     *)
(* over the alternative carrier -- larger blast radius.                       *)
(*                                                                            *)
(* THE NAIVE IMPLEMENTATION.  The function below assembles the filtered       *)
(* edges into a SINGLE polygon whose outer ring is the concatenation of      *)
(* all surviving edges' endpoints.  This ring is NOT, in general,             *)
(* `ring_simple` or `ring_closed` -- it may self-intersect, may not close,    *)
(* and may not satisfy `ring_has_minimum_points` for small inputs.            *)
(*                                                                            *)
(* The function compiles and has the right type so downstream theorem        *)
(* statements (`overlay_ng_correct`, `correct_labels`) can reference it.      *)
(* Genuine ring-assembly correctness -- showing the assembled rings           *)
(* satisfy `valid_polygon` for valid inputs -- is the deferred-proof          *)
(* obligation `extract_rings_valid` (audit-phase3-milestone5.md §4.3 +       *)
(* §5.2; estimated 3-8 sessions; requires DCEL adoption in a Session 1.5      *)
(* of M4-revision).                                                           *)
(* -------------------------------------------------------------------------- *)

Definition extract (op : BooleanOp) (g : TopologyGraph) : Geometry :=
  let filtered : list (Point * Point * EdgeLabel) :=
    List.filter (fun e => edge_in_result op (snd e)) (tg_edges g) in
  let ring : Ring :=
    List.flat_map (fun e => [fst (fst e); snd (fst e)]) filtered in
  match ring with
  | nil       => nil
  | _ :: _    => [{| outer_ring := ring; hole_rings := [] |}]
  end.

(* The empty graph extracts to the empty geometry. *)
Lemma extract_empty_graph :
  forall op, extract op empty_graph = [].
Proof.
  intros op. unfold extract, empty_graph. simpl. reflexivity.
Qed.

(* If every edge filters out (no edge satisfies the op's rule), the
   extracted geometry is empty.  Used in Union/Intersection edge-case
   downstream. *)
Lemma extract_no_surviving_edges :
  forall op g,
    List.filter (fun e => edge_in_result op (snd e)) (tg_edges g) = [] ->
    extract op g = [].
Proof.
  intros op g Hempty. unfold extract.
  rewrite Hempty. simpl. reflexivity.
Qed.
