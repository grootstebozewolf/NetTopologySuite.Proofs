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
(* Corrected extractor + the well-noded/orbit bridge slices: close
   extract_rings_valid as a conditional Qed over a 2-edge-connected
   precondition (replaces the S9 Admitted). *)
From NTS.Proofs        Require Import Dart.
From NTS.Proofs        Require Import DartNextSpec.
From NTS.Proofs        Require Import RingExtract.
From NTS.Proofs        Require Import FaceChain.
From NTS.Proofs        Require Import FacePolygonHoles.
From NTS.Proofs        Require Import ExtractFaces.
From NTS.Proofs        Require Import ExtractFacesHoles.
From NTS.Proofs        Require Import VertexGeneralPosition.
From NTS.Proofs        Require Import NoShortFaces.
From NTS.Proofs        Require Import FaceOrbitSep.
From NTS.Proofs        Require Import EdgeConnectivity.
From NTS.Proofs        Require Import EdgeFaceBridge.
From NTS.Proofs        Require Import MapCounts.
From NTS.Proofs        Require Import EulerArrangement.
From NTS.Proofs        Require Import HBridgeEuler.

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
(* §5  correct_labels for Union: forward direction only.                      *)
(*                                                                            *)
(* M4 REFACTOR NOTE.  The M5-S2 version of `correct_labels_union` proved      *)
(* the full iff directly by destructuring the un-merged edge list             *)
(* `label_from_A sA ++ label_from_B sB` via `List.in_app_iff`.  The           *)
(* M4-refactor wraps that list in `merge_labeled_edges`, which collapses      *)
(* duplicate (p, q) pairs into one edge with OR-ed labels.  The backward      *)
(* direction of the iff now requires a "merge dominates input bits"          *)
(* lemma (in_left l_in = true -> in_left l_out = true for the merge's        *)
(* output label) which is multi-line induction and pushed to a dedicated      *)
(* session.                                                                   *)
(*                                                                            *)
(* The FORWARD direction (label -> geometric) still closes Qed: given         *)
(* `In (p, q, l)` in the merged list, `merge_in_implies_in_input` extracts    *)
(* some input `(p, q, l')` in `label_from_A sA ++ label_from_B sB`, and      *)
(* in_app_iff / in_map_iff finish the disjunctive conclusion.                 *)
(*                                                                            *)
(* NOTE: the `edge_in_result Union l = true` hypothesis is intentionally     *)
(* discarded by the proof (`_` in the intros pattern).  The conclusion        *)
(* holds UNCONDITIONALLY for any edge in `tg_edges (noded_labeled_graph A B)` *)
(* because every such edge came from either A's or B's snapped segments by  *)
(* construction.  The hypothesis is kept in the LEMMA STATEMENT for          *)
(* composability with the future iff form (S4): `edge_in_result Union l =   *)
(* true <-> ...`.  Stating the lemma in the iff's forward-direction shape   *)
(* lets S4 compose this lemma with the (forthcoming, S3.5) backward          *)
(* direction without restating types.  See Copilot review on PR #32 for     *)
(* the alternative naming.                                                   *)
(* -------------------------------------------------------------------------- *)

Theorem correct_labels_union_forward :
  forall (A B : Geometry) (p q : Point) (l : EdgeLabel),
    In (p, q, l) (tg_edges (noded_labeled_graph A B)) ->
    edge_in_result Union l = true ->
    edge_geometrically_in_result Union p q A B.
Proof.
  intros A B p q l Hin _.
  unfold noded_labeled_graph, build_labeled_graph in Hin. simpl in Hin.
  apply merge_in_implies_in_input in Hin.
  destruct Hin as [l' Hin'].
  apply List.in_app_iff in Hin'.
  unfold edge_geometrically_in_result. simpl.
  destruct Hin' as [HA | HB].
  - unfold label_from_A in HA.
    apply List.in_map_iff in HA.
    destruct HA as [s [Heq Hin_s]].
    destruct s as [s_p s_q]. simpl in Heq.
    inversion Heq. subst.
    left. exact Hin_s.
  - unfold label_from_B in HB.
    apply List.in_map_iff in HB.
    destruct HB as [s [Heq Hin_s]].
    destruct s as [s_p s_q]. simpl in Heq.
    inversion Heq. subst.
    right. exact Hin_s.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Intersection / Difference / SymDiff -- label merging LANDED in this    *)
(*     PR (#32).  Original discovery and fix history.                          *)
(*                                                                            *)
(* The audit doc (docs/audit-phase3-milestone5.md §4.4) anticipated these     *)
(* cases as Sessions 5-7.  Session 2 discovered the underlying gap:           *)
(*                                                                            *)
(* Under the PRE-REFACTOR `noded_labeled_graph A B`, an edge `(p,q)` that    *)
(* appeared in BOTH A's snapped segments AND B's snapped segments was       *)
(* represented as TWO separate edges with disjoint labels (one with         *)
(* `in_left:=true`, one with `in_right:=true`).  For Intersection's          *)
(* `edge_in_result l = andb (in_left l) (in_right l)`, neither edge          *)
(* satisfied the rule -- so Intersection would extract no edges,             *)
(* contradicting the geometric expectation that `(p,q)` IS in the            *)
(* intersection.                                                              *)
(*                                                                            *)
(* The fix LANDED in this PR (M4 refactor + replan, PR #32): `merge_labels`  *)
(* + `merge_labeled_edges` in theories/OverlayGraph.v fold over the edge     *)
(* list combining labels for identical `(p,q)` pairs into a single edge      *)
(* with combined `{ in_left := A_has; in_right := B_has }`.                  *)
(* `build_labeled_graph` is now defined in terms of this merged form.        *)
(*                                                                            *)
(* Open follow-up (S3.5 / S4): under the merged labelling, Intersection /   *)
(* Difference / SymDiff are PROVABLE analogously to Union once the backward *)
(* direction of `merge_in_left_iff` / `_right_iff` lands (deferred from     *)
(* S3 -- see theories/OverlayGraph.v §11 for the tactic-obstacle             *)
(* explanation).                                                              *)
(*                                                                            *)
(* OPEN ARCHITECTURAL FINDING (Copilot PR #32 review): the merge matches    *)
(* on EXACT (p, q) pairs and does NOT canonicalize edge orientation.        *)
(* `ring_edges` produces oriented edges per ring traversal; A's ring may    *)
(* traverse `(p, q)` while B's ring traverses the same geometric segment    *)
(* as `(q, p)`.  These will NOT be merged.  Fix options: edge               *)
(* canonicalization (sort endpoints) inside `merge_labeled_edges`, or an    *)
(* unordered-pair-match version of `pair_eq_dec`.  Either is a focused      *)
(* refactor for S3.5 or S4.  Recorded here for downstream attention.        *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* §7  Phase 3 Milestone 5 Sessions 4-7 (consolidated): correct_labels for    *)
(*     all four BooleanOps.                                                    *)
(*                                                                            *)
(* With S3 + S3.5 closed (`merge_in_left_iff` / `merge_in_right_iff` full),  *)
(* `correct_labels_*` collapses to mechanical composition through two helper *)
(* iff lemmas linking output bits to source membership.                       *)
(*                                                                            *)
(* Originally scheduled as S4 (Union), S5 (Intersection), S6 (Difference),   *)
(* S7 (SymDiff).  Same proof pattern across all four; consolidated.          *)
(* -------------------------------------------------------------------------- *)

Lemma in_left_iff_in_A :
  forall (A B : Geometry) (p q : Point) (l : EdgeLabel),
    In (p, q, l) (tg_edges (noded_labeled_graph A B)) ->
    in_left l = true <->
    In (p, q) (snap_round_segments (extract_segments A)).
Proof.
  intros A B p q l Hin.
  unfold noded_labeled_graph, build_labeled_graph in Hin. simpl in Hin.
  split.
  - (* forward *)
    intros Hbit.
    apply (merge_in_left_forward _ p q l Hin) in Hbit.
    destruct Hbit as [l' [Hin' Hbit']].
    apply List.in_app_iff in Hin'.
    destruct Hin' as [HA | HB].
    + unfold label_from_A in HA. apply List.in_map_iff in HA.
      destruct HA as [s [Heq Hin_s]].
      destruct s as [s_p s_q]. simpl in Heq. inversion Heq. subst.
      exact Hin_s.
    + unfold label_from_B in HB. apply List.in_map_iff in HB.
      destruct HB as [s [Heq Hin_s]].
      destruct s as [s_p s_q]. simpl in Heq. inversion Heq. subst.
      simpl in Hbit'. discriminate.
  - (* backward *)
    intros HA_mem.
    set (sA := snap_round_segments (extract_segments A)) in *.
    set (sB := snap_round_segments (extract_segments B)) in *.
    assert (Hin_A : In ((p, q), {| in_left := true; in_right := false |})
                       (label_from_A sA)).
    { unfold label_from_A. apply List.in_map_iff.
      exists (p, q). split; [reflexivity | exact HA_mem]. }
    assert (Hin_concat : In ((p, q), {| in_left := true; in_right := false |})
                            (label_from_A sA ++ label_from_B sB)).
    { apply List.in_app_iff. left. exact Hin_A. }
    destruct (merge_in_left_backward
                (label_from_A sA ++ label_from_B sB) (p, q)
                {| in_left := true; in_right := false |}
                Hin_concat eq_refl)
      as [l_out [Hin_out Hbit_out]].
    pose proof (merge_unique _ p q l l_out Hin Hin_out) as Heq_l.
    rewrite Heq_l. exact Hbit_out.
Qed.

Lemma in_right_iff_in_B :
  forall (A B : Geometry) (p q : Point) (l : EdgeLabel),
    In (p, q, l) (tg_edges (noded_labeled_graph A B)) ->
    in_right l = true <->
    In (p, q) (snap_round_segments (extract_segments B)).
Proof.
  intros A B p q l Hin.
  unfold noded_labeled_graph, build_labeled_graph in Hin. simpl in Hin.
  split.
  - intros Hbit.
    apply (merge_in_right_forward _ p q l Hin) in Hbit.
    destruct Hbit as [l' [Hin' Hbit']].
    apply List.in_app_iff in Hin'.
    destruct Hin' as [HA | HB].
    + unfold label_from_A in HA. apply List.in_map_iff in HA.
      destruct HA as [s [Heq Hin_s]].
      destruct s as [s_p s_q]. simpl in Heq. inversion Heq. subst.
      simpl in Hbit'. discriminate.
    + unfold label_from_B in HB. apply List.in_map_iff in HB.
      destruct HB as [s [Heq Hin_s]].
      destruct s as [s_p s_q]. simpl in Heq. inversion Heq. subst.
      exact Hin_s.
  - intros HB_mem.
    set (sA := snap_round_segments (extract_segments A)) in *.
    set (sB := snap_round_segments (extract_segments B)) in *.
    assert (Hin_B : In ((p, q), {| in_left := false; in_right := true |})
                       (label_from_B sB)).
    { unfold label_from_B. apply List.in_map_iff.
      exists (p, q). split; [reflexivity | exact HB_mem]. }
    assert (Hin_concat : In ((p, q), {| in_left := false; in_right := true |})
                            (label_from_A sA ++ label_from_B sB)).
    { apply List.in_app_iff. right. exact Hin_B. }
    destruct (merge_in_right_backward
                (label_from_A sA ++ label_from_B sB) (p, q)
                {| in_left := false; in_right := true |}
                Hin_concat eq_refl)
      as [l_out [Hin_out Hbit_out]].
    pose proof (merge_unique _ p q l l_out Hin Hin_out) as Heq_l.
    rewrite Heq_l. exact Hbit_out.
Qed.

(* Bool helper: in_right l = false iff in_right l <> true. *)
Lemma in_right_false_iff_not_true :
  forall l : EdgeLabel,
    in_right l = false <-> in_right l <> true.
Proof.
  intros l. destruct (in_right l).
  - split; intro H; [discriminate | exfalso; apply H; reflexivity].
  - split; intro H; [discriminate | reflexivity].
Qed.

(* S4 headline: correct_labels for Union. *)
Theorem correct_labels_union :
  forall (A B : Geometry),
    correct_labels Union (noded_labeled_graph A B) A B.
Proof.
  intros A B p q l Hin.
  unfold edge_in_result, edge_geometrically_in_result.
  rewrite Bool.orb_true_iff.
  rewrite (in_left_iff_in_A A B p q l Hin).
  rewrite (in_right_iff_in_B A B p q l Hin).
  reflexivity.
Qed.

(* S5: correct_labels for Intersection. *)
Theorem correct_labels_intersection :
  forall (A B : Geometry),
    correct_labels Intersection (noded_labeled_graph A B) A B.
Proof.
  intros A B p q l Hin.
  unfold edge_in_result, edge_geometrically_in_result.
  rewrite Bool.andb_true_iff.
  rewrite (in_left_iff_in_A A B p q l Hin).
  rewrite (in_right_iff_in_B A B p q l Hin).
  reflexivity.
Qed.

(* S6: correct_labels for Difference. *)
Theorem correct_labels_difference :
  forall (A B : Geometry),
    correct_labels Difference (noded_labeled_graph A B) A B.
Proof.
  intros A B p q l Hin.
  unfold edge_in_result, edge_geometrically_in_result.
  rewrite Bool.andb_true_iff.
  rewrite Bool.negb_true_iff.
  rewrite (in_left_iff_in_A A B p q l Hin).
  rewrite (in_right_false_iff_not_true l).
  rewrite (in_right_iff_in_B A B p q l Hin).
  reflexivity.
Qed.

(* S7: correct_labels for SymDiff. *)
Theorem correct_labels_symdiff :
  forall (A B : Geometry),
    correct_labels SymDiff (noded_labeled_graph A B) A B.
Proof.
  intros A B p q l Hin.
  unfold edge_in_result, edge_geometrically_in_result. unfold xorb.
  pose proof (in_left_iff_in_A A B p q l Hin) as HL.
  pose proof (in_right_iff_in_B A B p q l Hin) as HR.
  destruct (in_left l) eqn:HLeq; destruct (in_right l) eqn:HReq; simpl.
  - (* both true: edge_in_result xorb true true = false; geometric must fail *)
    split; intro H; [discriminate|].
    exfalso. destruct H as [[Ha Hb] | [Ha Hb]].
    + apply Hb. apply HR. reflexivity.
    + apply Hb. apply HL. reflexivity.
  - (* in_left true, in_right false: edge_in_result xorb true false = true *)
    split; intros _.
    + left. split.
      * apply HL. reflexivity.
      * intros Hin_B. apply HR in Hin_B. congruence.
    + reflexivity.
  - (* in_left false, in_right true *)
    split; intros _.
    + right. split.
      * apply HR. reflexivity.
      * intros Hin_A. apply HL in Hin_A. congruence.
    + reflexivity.
  - (* both false: edge_in_result xorb false false = false *)
    split; intro H; [discriminate|].
    exfalso. destruct H as [[Ha Hb] | [Ha Hb]].
    + apply HL in Ha. congruence.
    + apply HR in Ha. congruence.
Qed.

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* §7  Phase 3 Milestone 5 Session 8: correct_labels uniform composition.     *)
(*                                                                            *)
(* Case-on-op composition of the four operation-specific correct_labels      *)
(* theorems.  Useful in S15 for the headline theorem's structural proof:     *)
(* given any op, the labels are correct on `noded_labeled_graph A B`.        *)
(*                                                                            *)
(* This is the only Coq deliverable of S8.  The session's primary content    *)
(* is documentation (audit-phase3-milestone5.md updated with JCT-search      *)
(* outcome and S8 closure note).                                              *)
(* -------------------------------------------------------------------------- *)

Theorem correct_labels_all_ops :
  forall (op : BooleanOp) (A B : Geometry),
    correct_labels op (noded_labeled_graph A B) A B.
Proof.
  intros op A B. destruct op.
  - apply correct_labels_union.
  - apply correct_labels_intersection.
  - apply correct_labels_difference.
  - apply correct_labels_symdiff.
Qed.

(* -------------------------------------------------------------------------- *)
(* §8  extract_rings_valid -- CLOSED as a conditional Qed (2026-06-13).        *)
(*                                                                            *)
(* The S9 statement was Admitted over the naive `extract` (theories/          *)
(* OverlayGraph.v) -- the single-polygon flatten that slice 3i refuted        *)
(* (`ExtractFlattenCounterexample.extract_unordered_not_valid`).  The bridge  *)
(* ladder (docs/extract-faces-bridge.md) relocated the obligation onto the    *)
(* corrected face extractor `extract_faces` and reduced it, via               *)
(* `FaceOrbitSep.extract_faces_valid_sep`, to three structural conditions     *)
(* plus ONE remaining mathematical fact:                                      *)
(*                                                                            *)
(*   well_noded_darts + no_spurs + twins_in_different_faces                    *)
(*     ==> every extracted polygon is valid_polygon         (Qed, capstone).  *)
(*                                                                            *)
(* `twins_in_different_faces` is exactly no-dart-shares-an-fstep-orbit-with-   *)
(* its-twin, i.e. no cut edge -- a 2-edge-connected arrangement.  The          *)
(* rotation-system characterisation `edge_2_connected E ->                     *)
(* twins_in_different_faces (darts_of E)` is discharged by                     *)
(* EdgeFaceBridge.H_bridge_well_noded (combinatorial bridge; modulo the two    *)
(* core Admitted reach lemmas on Print Assumptions — four total in            *)
(* EdgeFaceBridge.v, registry LIVE).  Contrast:                                 *)
(* OverlayCorrectness.overlay_ng_correct_conditional still carries a           *)
(* *geometric* H_bridge (JCT-gated).  See EdgeConnectivity.v §5 /              *)
(* docs/extract-faces-bridge.md §19.                                           *)
(* -------------------------------------------------------------------------- *)

(* H4 (face_twin_free closure rung 2): the survivor edge list of the noded graph
   is duplicate-free.  `tg_edges (noded_labeled_graph A B)` is `merge_labeled_edges
   ..`, whose KEYS (`edge_keys := map fst`) are NoDup by
   `OverlayGraph.merge_NoDup_keys`; `result_edges` projects those keys through a
   filter, so `NoDup_result_edges_of_keys` carries it over.  This discharges the
   carried `NoDup` hypothesis of the headlines below. *)
Lemma NoDup_result_edges_noded :
  forall op A B, NoDup (result_edges op (noded_labeled_graph A B)).
Proof.
  intros op A B. apply NoDup_result_edges_of_keys.
  unfold noded_labeled_graph, build_labeled_graph. cbn [tg_edges].
  apply merge_NoDup_keys.
Qed.

Theorem extract_rings_valid :
  forall (op : BooleanOp) (A B : Geometry),
    well_noded_darts (result_edges op (noded_labeled_graph A B)) ->
    no_spurs (result_darts op (noded_labeled_graph A B)) ->
    edge_2_connected (result_edges op (noded_labeled_graph A B)) ->
    euler_characteristic (result_edges op (noded_labeled_graph A B)) ->
    (forall e, In e (result_edges op (noded_labeled_graph A B)) ->
       euler_characteristic (E_minus (result_edges op (noded_labeled_graph A B)) e)) ->
    forall poly,
      In poly (extract_faces op (noded_labeled_graph A B)) ->
      valid_polygon poly.
Proof.
  intros op A B Hwn Hns H2ec Heul HeulM poly Hin.
  assert (Hnd : NoDup (result_edges op (noded_labeled_graph A B)))
    by (apply NoDup_result_edges_noded).
  assert (Hfan : forall v : Point,
            fan_ok (outgoing v (darts_of (result_edges op (noded_labeled_graph A B))))).
  { intro v. apply well_noded_fan_ok. exact Hwn. }
  assert (Hbr : H_bridge_premise (result_edges op (noded_labeled_graph A B)))
    by (apply H_bridge_premise_from_euler; assumption).
  exact (extract_faces_valid_sep op (noded_labeled_graph A B) Hwn Hns
           (H_bridge_well_noded (result_edges op (noded_labeled_graph A B))
              Hbr Hwn Hns H2ec) poly Hin).
Qed.

(* With-holes companion: the same closure over the holes extractor, threading
   the oracle well-formedness + hole_inside_outer nesting clauses unchanged. *)
Theorem extract_rings_valid_holes :
  forall (hassign : Dart -> list Dart) (op : BooleanOp) (A B : Geometry),
    well_noded_darts (result_edges op (noded_labeled_graph A B)) ->
    no_spurs (result_darts op (noded_labeled_graph A B)) ->
    edge_2_connected (result_edges op (noded_labeled_graph A B)) ->
    euler_characteristic (result_edges op (noded_labeled_graph A B)) ->
    (forall e, In e (result_edges op (noded_labeled_graph A B)) ->
       euler_characteristic (E_minus (result_edges op (noded_labeled_graph A B)) e)) ->
    (forall d, In d (result_darts op (noded_labeled_graph A B)) ->
       forall h, In h (hassign d) ->
         In h (result_darts op (noded_labeled_graph A B))) ->
    (forall d, In d (result_darts op (noded_labeled_graph A B)) ->
       forall h, In h (hassign d) ->
       hole_inside_outer
         (ring_of_chain (face_chain (result_darts op (noded_labeled_graph A B)) d
                           (face_period (result_darts op (noded_labeled_graph A B)) d)))
         (hole_ring_of (result_darts op (noded_labeled_graph A B))
            (h, face_period (result_darts op (noded_labeled_graph A B)) h))) ->
    forall poly,
      In poly (extract_faces_holes hassign op (noded_labeled_graph A B)) ->
      valid_polygon poly.
Proof.
  intros hassign op A B Hwn Hns H2ec Heul HeulM Hwf Hinside poly Hin.
  assert (Hnd : NoDup (result_edges op (noded_labeled_graph A B)))
    by (apply NoDup_result_edges_noded).
  assert (Hfan : forall v : Point,
            fan_ok (outgoing v (darts_of (result_edges op (noded_labeled_graph A B))))).
  { intro v. apply well_noded_fan_ok. exact Hwn. }
  assert (Hbr : H_bridge_premise (result_edges op (noded_labeled_graph A B)))
    by (apply H_bridge_premise_from_euler; assumption).
  exact (extract_faces_holes_valid_sep hassign op (noded_labeled_graph A B)
           Hwn Hns (H_bridge_well_noded (result_edges op (noded_labeled_graph A B))
              Hbr Hwn Hns H2ec)
           Hwf Hinside poly Hin).
Qed.

(* -------------------------------------------------------------------------- *)
(* valid_geometry of the extracted Geometry -- corollary of the closed        *)
(* extract_rings_valid, restated over the corrected `extract_faces`.          *)
(* -------------------------------------------------------------------------- *)

Theorem valid_geometry_extract :
  forall (op : BooleanOp) (A B : Geometry),
    well_noded_darts (result_edges op (noded_labeled_graph A B)) ->
    no_spurs (result_darts op (noded_labeled_graph A B)) ->
    edge_2_connected (result_edges op (noded_labeled_graph A B)) ->
    euler_characteristic (result_edges op (noded_labeled_graph A B)) ->
    (forall e, In e (result_edges op (noded_labeled_graph A B)) ->
       euler_characteristic (E_minus (result_edges op (noded_labeled_graph A B)) e)) ->
    valid_geometry (extract_faces op (noded_labeled_graph A B)).
Proof.
  intros op A B Hwn Hns H2ec Heul HeulM.
  unfold valid_geometry.
  intros poly Hin.
  apply (extract_rings_valid op A B Hwn Hns H2ec Heul HeulM poly Hin).
Qed.

(* -------------------------------------------------------------------------- *)
(* §9  Audit footprint.                                                        *)
(* -------------------------------------------------------------------------- *)

Print Assumptions snap_noding_bridge.
Print Assumptions valid_topology_graph_noded_labeled_graph.
Print Assumptions correct_labels_union_forward.
Print Assumptions correct_labels_union.
Print Assumptions correct_labels_intersection.
Print Assumptions correct_labels_difference.
Print Assumptions correct_labels_symdiff.
Print Assumptions correct_labels_all_ops.
Print Assumptions extract_rings_valid.
Print Assumptions extract_rings_valid_holes.
Print Assumptions valid_geometry_extract.
