(* ============================================================================
   NetTopologySuite.Proofs.Flocq.ExtractFacesBridge
   ----------------------------------------------------------------------------
   extract_rings_valid R5, slice 3i: THE BRIDGE DISCHARGE -- attempted.

   GOAL (per docs/extract-faces.md "What remains" item 2): re-point the
   registered deferred proof `OverlayBridge.extract_rings_valid` onto the face
   extractor by DERIVING the three structural hypotheses of
   `ExtractFaces.extract_faces_valid` from the noder's `fully_intersected`
   guarantee:
     (H1) `pairwise_no_proper_cross (result_darts op g)`
     (H2) `forall v, fan_ok (outgoing v (result_darts op g))`
     (H3) `no_short_faces (result_darts op g)`

   OUTCOME: a RED -- H1, the hypothesis slice 3g's header and the prompt's R3
   both rated "expected TRUE", is in fact UNSATISFIABLE for any arrangement
   with a non-degenerate surviving edge, and the obstruction is STRUCTURAL
   (independent of `fully_intersected`).  This file machine-checks that finding
   and pins its precise shape; the GREEN re-point is therefore BLOCKED on a
   reformulation of H1 (a twin-aware simplicity predicate + a no-twin-in-face
   combinatorial lemma), documented in the outcome doc.

   The root cause, in one line:

       `result_darts op g = darts_of (result_edges op g) = E ++ map twin E`,
       and a non-degenerate segment PROPERLY CROSSES ITS OWN REVERSAL
       (the twin's parameter `s = 1 - t` reproduces every interior point),
       so the twin pair `(e, twin e)` -- present by construction -- always
       violates `pairwise_no_proper_cross`.

   The same degeneracy refutes the prompt's R3 lemma "endpoint-sharing => not
   proper": two distinct COLLINEAR edges sharing an endpoint (e.g.
   (0,0)-(2,0) and (0,0)-(1,0)) satisfy `fully_intersected` via its
   shared-endpoint disjunct yet properly cross at an interior point.  So
   `fully_intersected -> pairwise_no_proper_cross` is false EVEN on the
   undirected edge set, before `darts_of` ever doubles it.

   What this file proves (all Qed; no `Admitted` / `Axiom` / `Parameter`):

     - `seg_properly_crosses_reversal`            : a non-degenerate segment
                                                    properly crosses its reversal.
     - `sip_overlay_iff_hobby`                    : the two `segments_intersect_
                                                    properly` notions (Overlay vs
                                                    HobbyTheorem_b64) agree.
     - `darts_of_nondeg_not_pairwise`             : a non-degenerate edge in `E`
                                                    refutes `pairwise_no_proper_
                                                    cross (darts_of E)`.
     - `pairwise_darts_of_forces_degenerate`      : conversely, `pairwise_no_
                                                    proper_cross (darts_of E)`
                                                    forces every edge degenerate.
     - `result_darts_nondeg_not_pairwise`         : H1 is false whenever any
                                                    surviving edge is non-degenerate
                                                    -- the bridge to slice 3g's
                                                    actual hypothesis.
     - `fully_intersected_darts_of_not_pairwise`  : a concrete `fully_intersected`
                                                    witness whose `darts_of`
                                                    breaks H1 (the twin route).
     - `fully_intersected_not_pairwise_collinear` : a concrete `fully_intersected`
                                                    witness breaking pairwise on
                                                    the EDGE set (the collinear
                                                    route; refutes R3).
     - `extract_rings_valid_faces{,_holes}_named`  : the obligation relocated onto
                                                    the correct extractor (hole-free
                                                    slice 3g and with-holes slice 3h)
                                                    -- both share the unsatisfiable
                                                    H1, so both are blocked.

   Pure-R + list combinatorics; the only axioms are the allowlisted
   classical-reals pair inherited through the dart machinery.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import List Reals Lra.
From NTS.Proofs Require Import Distance Overlay Dart RingSimple
                               OverlayGraph DartNextSpec RingExtract FaceChain
                               FacePolygonHoles ExtractFaces ExtractFacesHoles.
From NTS.Proofs.Flocq Require Import HobbyTheorem_b64 OverlayBridge.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §0  The two `segments_intersect_properly` notions agree.                    *)
(*                                                                            *)
(* `Overlay.segments_intersect_properly` (what `pairwise_no_proper_cross`     *)
(* speaks about) and `HobbyTheorem_b64.segments_intersect_properly` (what     *)
(* `fully_intersected` speaks about) have textually identical bodies; they    *)
(* are convertible, so the bridge between the noder's output and the          *)
(* simplicity predicate is a pure renaming -- not a geometric seam.            *)
(* -------------------------------------------------------------------------- *)

Lemma sip_overlay_iff_hobby :
  forall P0 P1 Q0 Q1 : Point,
    Overlay.segments_intersect_properly P0 P1 Q0 Q1 <->
    HobbyTheorem_b64.segments_intersect_properly P0 P1 Q0 Q1.
Proof.
  intros P0 P1 Q0 Q1.
  split; intro H; exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* §1  A non-degenerate segment properly crosses its own reversal.             *)
(*                                                                            *)
(* This is the lemma the prompt's D1 needed to be FALSE for the twin pair to  *)
(* be harmless ("a segment does not properly cross its own reversal").  It is  *)
(* TRUE: the reversal's parameter `s = 1 - t` reproduces every interior        *)
(* point, so the midpoint (t = s = 1/2) is a proper crossing.                  *)
(* -------------------------------------------------------------------------- *)

Lemma seg_properly_crosses_reversal :
  forall p q : Point, p <> q ->
    Overlay.segments_intersect_properly p q q p.
Proof.
  intros p q _.
  unfold Overlay.segments_intersect_properly.
  exists (1/2), (1/2).
  repeat split; try lra.
Qed.

(* A concrete collinear overlap that properly crosses, used by §5's witness:
   (0,0)-(2,0) and (0,0)-(1,0) cross at (1/2, 0) (t = 1/4, s = 1/2). *)
Lemma collinear_overlap_properly_crosses :
  Overlay.segments_intersect_properly
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 0) (mkPoint 1 0).
Proof.
  unfold Overlay.segments_intersect_properly.
  exists (1/4), (1/2).
  cbn [px py]. repeat split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  H1 is unsatisfiable for non-degenerate edges (the structural RED).      *)
(* -------------------------------------------------------------------------- *)

(* A single non-degenerate edge already refutes `pairwise_no_proper_cross` of
   the dart set: the edge and its twin are distinct darts of `darts_of E` that
   properly cross. *)
Lemma darts_of_nondeg_not_pairwise :
  forall (E : list Edge) (e : Edge),
    In e E -> fst e <> snd e ->
    ~ pairwise_no_proper_cross (darts_of E).
Proof.
  intros E e He Hnd Hpw.
  assert (Hd1 : In e (darts_of E)) by (apply in_darts_of_orig; exact He).
  assert (Hd2 : In (twin e) (darts_of E)) by (apply in_darts_of_twin; exact He).
  assert (Hne : e <> twin e).
  { intro Heq. apply (twin_neq_self e Hnd). symmetry. exact Heq. }
  apply (Hpw e (twin e) Hd1 Hd2 Hne).
  destruct e as [p q]. cbn [fst snd twin] in *.
  apply seg_properly_crosses_reversal. exact Hnd.
Qed.

(* The contrapositive characterisation: the only way the dart set is
   `pairwise_no_proper_cross` is for EVERY edge to be degenerate (a point). *)
Lemma pairwise_darts_of_forces_degenerate :
  forall (E : list Edge),
    pairwise_no_proper_cross (darts_of E) ->
    forall e, In e E -> fst e = snd e.
Proof.
  intros E Hpw e He.
  destruct (point_eq_dec (fst e) (snd e)) as [Hd | Hnd].
  - exact Hd.
  - exfalso. exact (darts_of_nondeg_not_pairwise E e He Hnd Hpw).
Qed.

(* The bridge to slice 3g's ACTUAL hypothesis: `extract_faces_valid`'s
   `pairwise_no_proper_cross (result_darts op g)` is false the moment any
   op-surviving edge is non-degenerate -- i.e. always, for a non-trivial
   arrangement.  H1 is therefore vacuously-satisfiable only in the
   all-degenerate regime, and the deferred `extract_rings_valid` cannot be
   re-pointed onto `extract_faces_valid` by discharging H1. *)
Lemma result_darts_nondeg_not_pairwise :
  forall op g e,
    In e (result_edges op g) -> fst e <> snd e ->
    ~ pairwise_no_proper_cross (result_darts op g).
Proof.
  intros op g e He Hnd.
  unfold result_darts.
  exact (darts_of_nondeg_not_pairwise (result_edges op g) e He Hnd).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  `fully_intersected` does not deliver H1 (concrete witnesses).           *)
(* -------------------------------------------------------------------------- *)

(* Twin route: a singleton arrangement is vacuously `fully_intersected`, yet
   its `darts_of` -- the edge plus its reversal -- breaks `pairwise_no_proper_
   cross`.  This is exactly the shape `result_darts` takes on a one-edge
   result. *)
Lemma fully_intersected_darts_of_not_pairwise :
  exists S : list (Point * Point),
    fully_intersected S /\
    (exists e, In e S /\ fst e <> snd e) /\
    ~ pairwise_no_proper_cross (darts_of S).
Proof.
  exists [(mkPoint 0 0, mkPoint 1 0)].
  split; [ | split ].
  - (* fully_intersected: vacuous on a singleton *)
    intros s1 s2 H1 H2 Hne.
    cbn in H1, H2. destruct H1 as [<- | []]. destruct H2 as [<- | []].
    exfalso. apply Hne. reflexivity.
  - exists (mkPoint 0 0, mkPoint 1 0). split; [ left; reflexivity | ].
    cbn [fst snd]. intro Hpq.
    assert (px (mkPoint 0 0) = px (mkPoint 1 0)) by (rewrite Hpq; reflexivity).
    cbn in *. lra.
  - apply (darts_of_nondeg_not_pairwise _ (mkPoint 0 0, mkPoint 1 0)).
    + left; reflexivity.
    + cbn [fst snd]. intro Hpq.
      assert (px (mkPoint 0 0) = px (mkPoint 1 0)) by (rewrite Hpq; reflexivity).
      cbn in *. lra.
Qed.

(* Collinear route (refutes the prompt's R3): two DISTINCT collinear edges
   sharing an endpoint satisfy `fully_intersected` (the shared-endpoint
   disjunct) but properly cross at an interior point -- so
   `fully_intersected -> pairwise_no_proper_cross` fails on the EDGE set,
   before `darts_of` is even applied.  The shared-endpoint disjunct of
   `fully_intersected` is therefore NOT a "meet only at endpoints" guarantee;
   collinear overlaps slip through it. *)
Lemma fully_intersected_not_pairwise_collinear :
  exists S : list (Point * Point),
    fully_intersected S /\ ~ pairwise_no_proper_cross S.
Proof.
  pose (a := (mkPoint 0 0, mkPoint 2 0)).
  pose (b := (mkPoint 0 0, mkPoint 1 0)).
  exists [a; b].
  split.
  - (* fully_intersected: the only distinct pairs are (a,b) and (b,a),
       both sharing the endpoint (0,0). *)
    intros s1 s2 H1 H2 Hne.
    cbn in H1, H2.
    destruct H1 as [<- | [<- | []]]; destruct H2 as [<- | [<- | []]];
      try (exfalso; apply Hne; reflexivity);
      unfold a, b, segments_intersect_only_at_endpoints;
      right; left; reflexivity.
  - (* not pairwise: a and b are distinct and properly cross *)
    intro Hpw.
    apply (Hpw a b); [ left; reflexivity | right; left; reflexivity | | ].
    + (* a <> b *)
      intro Heq. unfold a, b in Heq.
      assert (px (snd (mkPoint 0 0, mkPoint 2 0)) =
              px (snd (mkPoint 0 0, mkPoint 1 0))) by (rewrite Heq; reflexivity).
      cbn in *. lra.
    + unfold a, b. cbn [fst snd]. exact collinear_overlap_properly_crosses.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The honest re-point: the obligation, relocated -- NOT discharged.        *)
(*                                                                            *)
(* `extract_faces_valid` instantiated at the noded labelled graph is the      *)
(* face-extractor analogue of the deferred `extract_rings_valid` (over the    *)
(* CORRECT extractor, not the refuted flatten).  We can state it -- but its    *)
(* hypothesis H1 is provably unsatisfiable for any non-degenerate noded        *)
(* output (§2-§3), so this is a RELOCATION of the obligation onto the          *)
(* corrected API, not a discharge.  Closing the bridge needs H1 reformulated   *)
(* to a twin-aware predicate; see the outcome doc.                             *)
(* -------------------------------------------------------------------------- *)

Theorem extract_rings_valid_faces_named :
  forall (op : BooleanOp) (A B : Geometry),
    (forall v, fan_ok (outgoing v (result_darts op (noded_labeled_graph A B)))) ->
    pairwise_no_proper_cross (result_darts op (noded_labeled_graph A B)) ->
    no_short_faces (result_darts op (noded_labeled_graph A B)) ->
    forall poly,
      In poly (extract_faces op (noded_labeled_graph A B)) ->
      valid_polygon poly.
Proof.
  intros op A B Hfan Hpw Hmin poly Hin.
  exact (extract_faces_valid op (noded_labeled_graph A B) Hfan Hpw Hmin poly Hin).
Qed.

(* The with-holes extractor (slice 3h) shares the SAME H1 hypothesis
   `pairwise_no_proper_cross (result_darts op g)`, so the relocation -- and its
   block -- carry over verbatim.  `extract_rings_valid_faces_holes_named`
   restates `ExtractFaces Holes.extract_faces_holes_valid` at the noded labelled
   graph (the with-holes obligation, over the correct extractor); its H1 is the
   same predicate §2 proves unsatisfiable for non-degenerate output, so the
   with-holes re-point is blocked on exactly the same twin-pair obstruction. *)
Theorem extract_rings_valid_faces_holes_named :
  forall (hassign : Dart -> list Dart) (op : BooleanOp) (A B : Geometry),
    (forall v, fan_ok (outgoing v (result_darts op (noded_labeled_graph A B)))) ->
    pairwise_no_proper_cross (result_darts op (noded_labeled_graph A B)) ->
    no_short_faces (result_darts op (noded_labeled_graph A B)) ->
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
  intros hassign op A B Hfan Hpw Hshort Hwf Hinside poly Hin.
  exact (extract_faces_holes_valid hassign op (noded_labeled_graph A B)
           Hfan Hpw Hshort Hwf Hinside poly Hin).
Qed.

(* Audit footprint. *)
Print Assumptions seg_properly_crosses_reversal.
Print Assumptions darts_of_nondeg_not_pairwise.
Print Assumptions result_darts_nondeg_not_pairwise.
Print Assumptions fully_intersected_darts_of_not_pairwise.
Print Assumptions fully_intersected_not_pairwise_collinear.
Print Assumptions extract_rings_valid_faces_named.
Print Assumptions extract_rings_valid_faces_holes_named.
