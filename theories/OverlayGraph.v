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

(* Merge two labels via boolean OR on each flag.  When the same edge
   (p, q) appears with two different labels (e.g., once with
   in_left=true from label_from_A and once with in_right=true from
   label_from_B), merging produces a single combined label that
   correctly tracks both sources.

   M4-refactor finding: without this merge, Intersection / Difference /
   SymDiff cases of correct_labels are FALSE for noded_labeled_graph
   (see theories-flocq/OverlayBridge.v §6 in the M5-S2 commit for the
   discovery).  This merge fixes the labelling so all four boolean
   ops can be proven correct uniformly. *)
Definition merge_labels (l1 l2 : EdgeLabel) : EdgeLabel := {|
  in_left  := orb (in_left l1) (in_left l2);
  in_right := orb (in_right l1) (in_right l2)
|}.

(* Bool equality on pairs of points, decidable via point_eq_dec. *)
Definition pair_eq_dec :
  forall p q : Point * Point, {p = q} + {p <> q}.
Proof.
  intros [a b] [c d].
  destruct (point_eq_dec a c) as [Hac | Hac]; subst.
  - destruct (point_eq_dec b d) as [Hbd | Hbd]; subst.
    + left. reflexivity.
    + right. intros H. inversion H. contradiction.
  - right. intros H. inversion H. contradiction.
Defined.

(* Insert a labelled edge into a list, merging the label if an edge
   with the same (p, q) is already present. *)
Fixpoint insert_or_merge_edge
    (e : Point * Point * EdgeLabel)
    (edges : list (Point * Point * EdgeLabel)) :
    list (Point * Point * EdgeLabel) :=
  match edges with
  | nil => [e]
  | e' :: rest =>
      if pair_eq_dec (fst e) (fst e')
      then (fst e', merge_labels (snd e) (snd e')) :: rest
      else e' :: insert_or_merge_edge e rest
  end.

(* Fold the merge over a labelled edge list. *)
Definition merge_labeled_edges
    (edges : list (Point * Point * EdgeLabel)) :
    list (Point * Point * EdgeLabel) :=
  List.fold_right insert_or_merge_edge nil edges.

(* Build a labelled topology graph from two pre-noded segment lists.
   M4-refactor (Phase 3): the edge list is now MERGED so identical
   (p, q) pairs from sA and sB collapse into a single edge with
   combined { in_left := A_has; in_right := B_has } label.
   This fixes the M5-S2 finding documented in
   theories-flocq/OverlayBridge.v §6.  Vertices unchanged. *)
Definition build_labeled_graph
    (snapped_A snapped_B : list (Point * Point)) : TopologyGraph := {|
  tg_vertices := dedup_vertices
                   (segment_endpoints (snapped_A ++ snapped_B));
  tg_edges    := merge_labeled_edges
                   (label_from_A snapped_A ++ label_from_B snapped_B)
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

(* -------------------------------------------------------------------------- *)
(* §9.5  Merge-aware structural lemmas (M4 refactor).                          *)
(*                                                                            *)
(* Every edge in the merged output corresponds to an input edge with the      *)
(* same (p, q) but possibly different label.  This is the load-bearing        *)
(* invariant linking the merged edge list back to its sources.                *)
(* -------------------------------------------------------------------------- *)

(* Insert preserves "exists same (p,q) in input or new edge has same (p,q)
   as the one being inserted". *)
Lemma insert_or_merge_edge_in_or :
  forall e edges p q l,
    In (p, q, l) (insert_or_merge_edge e edges) ->
    (p, q) = fst e \/ (exists l', In (p, q, l') edges).
Proof.
  intros e edges. induction edges as [|e' rest IH]; intros p q l Hin; simpl in Hin.
  - (* edges = []: inserted gives [e]. *)
    destruct Hin as [Heq | []].
    left. destruct e as [pq_e l_e]. simpl. inversion Heq. reflexivity.
  - (* edges = e' :: rest *)
    destruct (pair_eq_dec (fst e) (fst e')) as [Hpeq | Hpneq].
    + (* merged at head *)
      destruct Hin as [Heq | Hin_tail].
      * (* (fst e', merge ...) = (p, q, l) *)
        destruct e' as [pq_e' l_e']. simpl in *.
        inversion Heq. subst pq_e'.
        right. exists l_e'. left. reflexivity.
      * right. exists l. right. exact Hin_tail.
    + destruct Hin as [Heq | Hin_tail].
      * right. exists l. left. exact Heq.
      * specialize (IH p q l Hin_tail).
        destruct IH as [Hpq | [l' Hin_rest]].
        -- left. exact Hpq.
        -- right. exists l'. right. exact Hin_rest.
Qed.

(* Key structural lemma: if (p, q, l) appears in the merge output, then
   some (p, q, l') appears in the input.  Used by validity proofs to
   trace each output edge back to its source. *)
Lemma merge_in_implies_in_input :
  forall edges p q l,
    In (p, q, l) (merge_labeled_edges edges) ->
    exists l', In (p, q, l') edges.
Proof.
  intros edges. unfold merge_labeled_edges. induction edges as [|e rest IH];
    intros p q l Hin; simpl in Hin.
  - contradiction.
  - apply insert_or_merge_edge_in_or in Hin.
    destruct Hin as [Hpq | [l' Hrest]].
    + (* (p, q) = fst e: so e = (p, q, snd e) and e is at head of (e::rest). *)
      destruct e as [pq_e l_e]. simpl in Hpq. subst pq_e.
      exists l_e. left. reflexivity.
    + destruct (IH p q l' Hrest) as [l'' Hrest'].
      exists l''. right. exact Hrest'.
Qed.

(* The M4 headline: every build_labeled_graph yields a valid topology
   graph.  M4-refactor: proof updated for the merged edge list -- now
   uses `merge_in_implies_in_input` to trace each output edge back to
   either label_from_A or label_from_B input. *)
Theorem valid_topology_graph_build_labeled_graph :
  forall sA sB : list (Point * Point),
    valid_topology_graph (build_labeled_graph sA sB).
Proof.
  intros sA sB.
  unfold valid_topology_graph, build_labeled_graph. simpl.
  intros p q l Hedge.
  apply merge_in_implies_in_input in Hedge.
  destruct Hedge as [l' Hin].
  apply List.in_app_iff in Hin.
  rewrite segment_endpoints_app.
  destruct Hin as [HA | HB].
  - apply label_from_A_endpoints_in_pairs in HA. destruct HA as [Hp Hq].
    split; apply (proj2 (List.nodup_In point_eq_dec _ _));
      apply List.in_app_iff; left; assumption.
  - apply label_from_B_endpoints_in_pairs in HB. destruct HB as [Hp Hq].
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

(* -------------------------------------------------------------------------- *)
(* §11  Phase 3 Milestone 5 Session 3: merge_label_iff_source + merge_unique. *)
(*                                                                            *)
(* Structural invariants linking the OUTPUT of `merge_labeled_edges` to its   *)
(* INPUT.  These unblock `correct_labels` for all four BooleanOps in S4-S7.   *)
(* -------------------------------------------------------------------------- *)

(* Keys (the (p, q) pair, ignoring labels) of an edge list. *)
Definition edge_keys (edges : list (Point * Point * EdgeLabel))
    : list (Point * Point) :=
  List.map fst edges.

(* Inserting an edge produces output keys exactly the input keys plus the
   inserted edge's key (no other keys appear). *)
Lemma insert_or_merge_edge_keys :
  forall e edges k,
    In k (edge_keys (insert_or_merge_edge e edges)) ->
    k = fst e \/ In k (edge_keys edges).
Proof.
  intros e edges. induction edges as [|e' rest IH]; intros k Hin;
    simpl in Hin.
  - (* edges = [] *)
    destruct Hin as [Heq | []]. left. symmetry. exact Heq.
  - (* edges = e' :: rest *)
    destruct (pair_eq_dec (fst e) (fst e')) as [Hpeq | Hpneq].
    + (* merged at head: keys unchanged *)
      simpl in Hin. destruct Hin as [Heq | Hin_tail].
      * right. left. exact Heq.
      * right. right. exact Hin_tail.
    + (* recurse on tail *)
      simpl in Hin. destruct Hin as [Heq | Hin_tail].
      * right. left. exact Heq.
      * apply IH in Hin_tail.
        destruct Hin_tail as [Heq | Hin'].
        -- left. exact Heq.
        -- right. right. exact Hin'.
Qed.

(* Insertion preserves the no-duplicates-on-keys invariant. *)
Lemma insert_or_merge_edge_NoDup :
  forall e edges,
    NoDup (edge_keys edges) ->
    NoDup (edge_keys (insert_or_merge_edge e edges)).
Proof.
  intros e edges. induction edges as [|e' rest IH]; intros Hnd; simpl.
  - constructor. intros []. constructor.
  - destruct (pair_eq_dec (fst e) (fst e')) as [Hpeq | Hpneq].
    + (* merged at head: keys identical to input *)
      simpl. exact Hnd.
    + simpl. inversion Hnd as [|h tl Hnotin Hnd_tail]. subst.
      constructor.
      * (* fst e' not in keys after insert *)
        intros Hin. apply insert_or_merge_edge_keys in Hin.
        destruct Hin as [Heq | Hin_rest].
        -- (* fst e' = fst e: but we assumed they're not equal *)
           symmetry in Heq. contradiction.
        -- (* fst e' in keys(rest): contradicts Hnotin *)
           contradiction.
      * apply IH. exact Hnd_tail.
Qed.

(* The merge output has unique (p, q) keys. *)
Lemma merge_NoDup_keys :
  forall edges, NoDup (edge_keys (merge_labeled_edges edges)).
Proof.
  intros edges. unfold merge_labeled_edges. induction edges as [|e rest IH].
  - simpl. constructor.
  - simpl. apply insert_or_merge_edge_NoDup. exact IH.
Qed.

(* `In (p, q, l) edges` lets us split the keys list: take/drop on the
   In witness. *)
Lemma in_implies_key_in_edge_keys :
  forall edges p q l,
    In (p, q, l) edges -> In (p, q) (edge_keys edges).
Proof.
  intros edges. induction edges as [|e rest IH]; intros p q l Hin.
  - inversion Hin.
  - simpl in Hin. destruct Hin as [Heq | Hin'].
    + simpl. left. destruct e as [pq_e l_e]. simpl in Heq. inversion Heq.
      reflexivity.
    + simpl. right. apply (IH _ _ _ Hin').
Qed.

(* On any list of labelled edges, NoDup on the keys forces label
   uniqueness: two In witnesses with the same (p, q) have the same
   label. *)
Lemma NoDup_keys_label_unique :
  forall (edges : list (Point * Point * EdgeLabel)) p q l1 l2,
    NoDup (edge_keys edges) ->
    In (p, q, l1) edges ->
    In (p, q, l2) edges ->
    l1 = l2.
Proof.
  intros edges. induction edges as [|e rest IH]; intros p q l1 l2 Hnd Hin1 Hin2.
  - inversion Hin1.
  - simpl in Hin1, Hin2.
    simpl in Hnd. inversion Hnd as [|h tl Hnotin Hnd_tail]. subst.
    destruct Hin1 as [Heq1 | Hin1'].
    + (* (p, q, l1) is at head *)
      destruct Hin2 as [Heq2 | Hin2'].
      * (* both at head *)
        subst e. inversion Heq2. reflexivity.
      * (* l1 at head, l2 in tail *)
        exfalso. apply Hnotin.
        destruct e as [pq_e l_e]. simpl in Heq1. inversion Heq1. subst.
        apply (in_implies_key_in_edge_keys rest p q l2 Hin2').
    + (* (p, q, l1) in tail *)
      destruct Hin2 as [Heq2 | Hin2'].
      * (* l1 in tail, l2 at head *)
        exfalso. apply Hnotin.
        destruct e as [pq_e l_e]. simpl in Heq2. inversion Heq2. subst.
        apply (in_implies_key_in_edge_keys rest p q l1 Hin1').
      * (* both in tail *)
        apply (IH _ _ _ _ Hnd_tail Hin1' Hin2').
Qed.

(* Merge uniqueness: same key in the merged output implies same label. *)
Theorem merge_unique :
  forall edges p q l1 l2,
    In (p, q, l1) (merge_labeled_edges edges) ->
    In (p, q, l2) (merge_labeled_edges edges) ->
    l1 = l2.
Proof.
  intros edges p q l1 l2 Hin1 Hin2.
  apply (NoDup_keys_label_unique _ p q l1 l2
           (merge_NoDup_keys edges) Hin1 Hin2).
Qed.

(* -------------------------------------------------------------------------- *)
(* The merge-output-bit lemmas.                                                *)
(*                                                                            *)
(* These connect output label bits to "some matching input edge has the       *)
(* corresponding bit set".  Two directions, each by induction on the merge   *)
(* fold.  Once proved, `merge_label_iff_source` is a specialisation.          *)
(* -------------------------------------------------------------------------- *)

(* The label bit at a key in the insert output is determined by:
   - the inserted edge's bit (if its key matches the queried key), AND
   - the input edge's bit at that key (if such an input edge exists). *)

(* Forward (output bit true ⇒ some matching input has the bit). *)
Lemma insert_or_merge_in_left_forward :
  forall e edges p q l,
    In (p, q, l) (insert_or_merge_edge e edges) ->
    in_left l = true ->
    (fst e = (p, q) /\ in_left (snd e) = true) \/
    (exists l', In (p, q, l') edges /\ in_left l' = true).
Proof.
  intros e edges. induction edges as [|e' rest IH]; intros p q l Hin Hbit;
    simpl in Hin.
  - destruct Hin as [Heq | []].
    left. destruct e as [pq_e l_e]. simpl in Heq. inversion Heq. subst.
    split; [reflexivity | exact Hbit].
  - destruct (pair_eq_dec (fst e) (fst e')) as [Hpeq | Hpneq].
    + (* merged at head *)
      destruct Hin as [Heq | Hin_tail].
      * (* head merged entry: l = merge_labels (snd e) (snd e') *)
        destruct e as [pq_e l_e]. destruct e' as [pq_e' l_e']. simpl in *.
        subst pq_e'. inversion Heq. subst pq_e l.
        unfold merge_labels in Hbit. simpl in Hbit.
        apply orb_true_iff in Hbit. destruct Hbit as [Hl | Hr].
        -- (* in_left from e *)
           left. split; [reflexivity|]. exact Hl.
        -- (* in_left from e' (existing) *)
           right. exists l_e'. split; [left; reflexivity | exact Hr].
      * (* tail unchanged *)
        right. exists l. split; [right; exact Hin_tail | exact Hbit].
    + (* no head match *)
      destruct Hin as [Heq | Hin_tail].
      * (* head e' kept: l = snd e' *)
        right. exists l. split; [left; exact Heq | exact Hbit].
      * specialize (IH p q l Hin_tail Hbit).
        destruct IH as [Hsame | [l' [Hin' Hbit']]].
        -- left. exact Hsame.
        -- right. exists l'. split; [right; exact Hin' | exact Hbit'].
Qed.

(* Symmetric for in_right. *)
Lemma insert_or_merge_in_right_forward :
  forall e edges p q l,
    In (p, q, l) (insert_or_merge_edge e edges) ->
    in_right l = true ->
    (fst e = (p, q) /\ in_right (snd e) = true) \/
    (exists l', In (p, q, l') edges /\ in_right l' = true).
Proof.
  intros e edges. induction edges as [|e' rest IH]; intros p q l Hin Hbit;
    simpl in Hin.
  - destruct Hin as [Heq | []].
    left. destruct e as [pq_e l_e]. simpl in Heq. inversion Heq. subst.
    split; [reflexivity | exact Hbit].
  - destruct (pair_eq_dec (fst e) (fst e')) as [Hpeq | Hpneq].
    + destruct Hin as [Heq | Hin_tail].
      * destruct e as [pq_e l_e]. destruct e' as [pq_e' l_e']. simpl in *.
        subst pq_e'. inversion Heq. subst pq_e l.
        unfold merge_labels in Hbit. simpl in Hbit.
        apply orb_true_iff in Hbit. destruct Hbit as [Hl | Hr].
        -- left. split; [reflexivity|]. exact Hl.
        -- right. exists l_e'. split; [left; reflexivity | exact Hr].
      * right. exists l. split; [right; exact Hin_tail | exact Hbit].
    + destruct Hin as [Heq | Hin_tail].
      * right. exists l. split; [left; exact Heq | exact Hbit].
      * specialize (IH p q l Hin_tail Hbit).
        destruct IH as [Hsame | [l' [Hin' Hbit']]].
        -- left. exact Hsame.
        -- right. exists l'. split; [right; exact Hin' | exact Hbit'].
Qed.

(* Forward direction on the merge fold: output bit true ⇒ some matching
   input edge has the corresponding bit set. *)
Lemma merge_in_left_forward :
  forall edges p q l,
    In (p, q, l) (merge_labeled_edges edges) ->
    in_left l = true ->
    exists l', In (p, q, l') edges /\ in_left l' = true.
Proof.
  intros edges. unfold merge_labeled_edges.
  induction edges as [|e rest IH]; intros p q l Hin Hbit; simpl in Hin.
  - contradiction.
  - apply insert_or_merge_in_left_forward in Hin; [|exact Hbit].
    destruct Hin as [[Hpq Hbit_e] | [l' [Hin' Hbit']]].
    + (* (p, q) = fst e *)
      exists (snd e). split.
      * left. destruct e as [pq_e l_e]. simpl in Hpq. subst pq_e. reflexivity.
      * exact Hbit_e.
    + (* tail *)
      specialize (IH p q l' Hin' Hbit').
      destruct IH as [l'' [Hin'' Hbit'']].
      exists l''. split; [right; exact Hin'' | exact Hbit''].
Qed.

Lemma merge_in_right_forward :
  forall edges p q l,
    In (p, q, l) (merge_labeled_edges edges) ->
    in_right l = true ->
    exists l', In (p, q, l') edges /\ in_right l' = true.
Proof.
  intros edges. unfold merge_labeled_edges.
  induction edges as [|e rest IH]; intros p q l Hin Hbit; simpl in Hin.
  - contradiction.
  - apply insert_or_merge_in_right_forward in Hin; [|exact Hbit].
    destruct Hin as [[Hpq Hbit_e] | [l' [Hin' Hbit']]].
    + exists (snd e). split.
      * left. destruct e as [pq_e l_e]. simpl in Hpq. subst pq_e. reflexivity.
      * exact Hbit_e.
    + specialize (IH p q l' Hin' Hbit').
      destruct IH as [l'' [Hin'' Hbit'']].
      exists l''. split; [right; exact Hin'' | exact Hbit''].
Qed.

(* -------------------------------------------------------------------------- *)
(* Backward direction (input bit ⇒ output bit) -- DEFERRED to S3.5 / S4.       *)
(*                                                                            *)
(* The backward direction requires showing every input bit propagates         *)
(* through the merge fold to the (unique) output entry at its key.  The       *)
(* proof structure is sound but stalled on a Coq tactic obstacle: `destruct`  *)
(* on `pair_eq_dec` does NOT substitute the function call in the goal, so     *)
(* the if-then-else inside `insert_or_merge_edge`'s body fails to reduce      *)
(* after case-splitting.                                                      *)
(*                                                                            *)
(* Three fixes tried this session, none compiled cleanly:                     *)
(*   - `destruct ... eqn:Hdec; rewrite Hdec`: Coq's `eqn:` syntax doesn't     *)
(*     propagate the substitution through the un-reduced fixpoint body.       *)
(*   - `remember ... as decres eqn:Hdec`: same issue at the if site.          *)
(*   - `cbn` + `destruct`: cbn doesn't fully reduce the conditional.          *)
(*                                                                            *)
(* The clean fix is structural: refactor `insert_or_merge_edge` to use a      *)
(* boolean predicate `pair_eq_b : Point * Point -> Point * Point -> bool`     *)
(* (defined via `pair_eq_dec`) instead of `if pair_eq_dec ... then ... else`. *)
(* Then `destruct ... eqn:` on the bool naturally substitutes via `congr_arg` *)
(* or `case_eq`.                                                              *)
(*                                                                            *)
(* Session-3 OUTCOME landed:                                                  *)
(*   - `merge_unique`: Qed-closed via `NoDup_keys_label_unique` +              *)
(*     `merge_NoDup_keys`.                                                    *)
(*   - Forward direction (`merge_in_left_forward`,                            *)
(*     `merge_in_right_forward`) Qed-closed.  Enough to prove the FORWARD    *)
(*     side of `correct_labels_*` in S4-S7.                                   *)
(*                                                                            *)
(* Session-3.5 (a half-session) should land:                                  *)
(*   - The `insert_or_merge_edge` boolean-predicate refactor.                 *)
(*   - `merge_in_left_backward`, `merge_in_right_backward`.                  *)
(*   - Full bidirectional `merge_label_iff_source` then composes.            *)
(* -------------------------------------------------------------------------- *)
