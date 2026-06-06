(* ============================================================================
   NetTopologySuite.Proofs.ExtractFlattenCounterexample
   ----------------------------------------------------------------------------
   extract_rings_valid R5 (docs/extract-rings-proof-structure.md §7): the naive
   `OverlayGraph.extract` flatten is NOT a valid ring assembler -- counterexample
   (RED) + the trace that fixes it (GREEN).

   `OverlayGraph.extract` (OverlayGraph.v) keeps the surviving edges and
   FLATTENS their endpoints in edge-list order:

       ring := flat_map (fun e => [fst (fst e); snd (fst e)]) filtered

   with no tracing / ordering / closure.  The file's own header already warns
   this "is NOT, in general, ring_simple or ring_closed".  This module turns that
   warning into a Qed-closed refutation: a concrete labelled graph whose surviving
   edges form a perfectly good closed triangle boundary, yet `extract` emits a
   polygon that FAILS `valid_polygon` -- so the stub violates the conclusion of
   the deferred `extract_rings_valid` obligation.  This is the assembly analogue
   of `RingSimple.not_ring_simple_bowtie` (raw input insufficient -> a real step
   is required), and it pins exactly what R5 must add.

   RED:
     - extract_unordered_not_valid : the out-of-order triangle edge set yields a
       polygon whose outer ring is not `ring_closed` (flatten preserves edge
       order, so the head/last vertices differ).
     - extract_single_not_valid    : a single surviving edge yields a 2-vertex
       ring, failing `ring_has_minimum_points`.

   GREEN (the fix is to TRACE, i.e. RingExtract.ring_of_chain on the ordered face
   walk -- which is what R5/R6 do):
     - ring_of_chain_traces_valid_shape : the SAME triangle, ordered into a face
       walk and traced by `ring_of_chain`, is `ring_closed` AND
       `ring_has_minimum_points` (RingExtract.face_walk_closed / _min_points).
     - ring_of_chain_tri_value          : that trace is the clean 4-vertex ring
       [A;B;C;A] (start-points + close), versus the stub's duplicated 6-vertex
       [A;B;C;A;B;C].

   Pure combinatorics + concrete points; no JCT, no analytic content.  No
   `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List Lia Lra.
From NTS.Proofs Require Import Distance Overlay OverlayGraph RingExtract.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  A concrete triangle and a "keep" label.                                 *)
(* -------------------------------------------------------------------------- *)

Definition cA : Point := mkPoint 0 0.
Definition cB : Point := mkPoint 1 0.
Definition cC : Point := mkPoint 0 1.

(* in_left = true makes Union keep the edge (orb true _ = true). *)
Definition Lkeep : EdgeLabel := mkEdgeLabel true false.

Lemma cA_neq_cC : cA <> cC.
Proof.
  intro H. assert (Hy : py cA = py cC) by (rewrite H; reflexivity).
  cbn in Hy. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  RED 1: a closed triangle boundary, given out of walk order, flattens    *)
(*     to a NON-CLOSED ring -- so `extract` emits an invalid polygon.          *)
(* -------------------------------------------------------------------------- *)

(* The three triangle edges, listed NOT in head-to-tail walk order. *)
Definition G_unordered : TopologyGraph :=
  mkTopologyGraph [cA; cB; cC]
    [ (cA, cB, Lkeep); (cC, cA, Lkeep); (cB, cC, Lkeep) ].

(* `extract Union` keeps all three and flattens their endpoints in list order. *)
Lemma extract_unordered_value :
  extract Union G_unordered
  = [ {| outer_ring := [cA; cB; cC; cA; cB; cC]; hole_rings := [] |} ].
Proof. reflexivity. Qed.

(* That flattened ring is not closed: its head (cA) and last (cC) differ. *)
Lemma flatten_ring_not_closed :
  ~ ring_closed [cA; cB; cC; cA; cB; cC].
Proof.
  intros [p [ps Heq]]. cbn in Heq.
  injection Heq as Hhd Htl.            (* Hhd : cA = p ; Htl : tail = ps ++ [p] *)
  assert (Hlast : last [cB; cC; cA; cB; cC] cA = last (ps ++ [p]) cA)
    by (rewrite Htl; reflexivity).
  rewrite last_last in Hlast.          (* RHS = p *)
  cbn in Hlast.                        (* LHS = cC, so Hlast : cC = p *)
  apply cA_neq_cC. rewrite Hhd. symmetry. exact Hlast.
Qed.

(* RED headline 1: every polygon the stub extracts from G_unordered is invalid. *)
Theorem extract_unordered_not_valid :
  forall poly, In poly (extract Union G_unordered) -> ~ valid_polygon poly.
Proof.
  rewrite extract_unordered_value.
  intros poly Hin. cbn in Hin.
  destruct Hin as [Heq | []]. subst poly.
  intros [Hclosed _]. cbn in Hclosed.
  exact (flatten_ring_not_closed Hclosed).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  RED 2: a single surviving edge flattens to a 2-vertex (degenerate) ring *)
(*     -- fails the minimum-vertex count.                                       *)
(* -------------------------------------------------------------------------- *)

Definition G_single : TopologyGraph :=
  mkTopologyGraph [cA; cB] [ (cA, cB, Lkeep) ].

Lemma extract_single_value :
  extract Union G_single
  = [ {| outer_ring := [cA; cB]; hole_rings := [] |} ].
Proof. reflexivity. Qed.

Theorem extract_single_not_valid :
  forall poly, In poly (extract Union G_single) -> ~ valid_polygon poly.
Proof.
  rewrite extract_single_value.
  intros poly Hin. cbn in Hin.
  destruct Hin as [Heq | []]. subst poly.
  intros (_ & _ & Hmin & _).
  unfold ring_has_minimum_points in Hmin. cbn in Hmin. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  GREEN: the fix is to TRACE.  The SAME triangle, ordered into a face      *)
(*     walk and traced by RingExtract.ring_of_chain, is a valid-shape ring.     *)
(* -------------------------------------------------------------------------- *)

(* The triangle as a head-to-tail face walk (what R5's tracing must recover). *)
Definition tri_chain : list (Point * Point) :=
  [ (cA, cB); (cB, cC); (cC, cA) ].

(* The trace is the clean 4-vertex closed ring (start-points + closing vertex),
   in contrast to the stub's duplicated 6-vertex non-closed flatten. *)
Lemma ring_of_chain_tri_value :
  ring_of_chain tri_chain = [cA; cB; cC; cA].
Proof. reflexivity. Qed.

(* GREEN headline: the traced ring is closed and has the minimum vertex count
   -- the two combinatorial `valid_polygon` conjuncts the stub flatten loses,
   recovered for free by RingExtract once the edges are walk-ordered. *)
Theorem ring_of_chain_traces_valid_shape :
  ring_closed (ring_of_chain tri_chain) /\
  ring_has_minimum_points (ring_of_chain tri_chain).
Proof.
  split.
  - apply face_walk_closed. discriminate.
  - apply face_walk_min_points. cbn. lia.
Qed.
