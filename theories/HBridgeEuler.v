(* ==========================================================================
   HBridgeEuler.v

   Discharge of the planar-bridge premise `EdgeFaceBridge.H_bridge_premise` from
   the planar Euler identity.

   `EdgeFaceBridge` (build position before the Euler stack) carries the bridge
   fact as a NAMED premise `H_bridge_premise E` threaded through the
   same_face/cut-edge chain.  Here -- downstream of the whole Euler/splice stack
   (`MapCounts`, `NumFacesSplice`, `EulerArrangement`, `EulerBridge`) -- we
   DISCHARGE that premise from the named planar Euler hypotheses.  The two
   per-dart reachability conjuncts each follow from
   `EulerBridge.H_bridge_core_conclusion_from_euler` once its FACE delta is
   supplied by the now-proved `NumFacesSplice.num_faces_E_minus_splice`; the edge
   delta comes from `NoDup E` (simple edge list) via `num_edges_E_minus`, and the
   vertex invariance + the two `euler_characteristic` instances stay named
   hypotheses (the planar identity is carried, not axiomatized).

   The headline `extract_rings_valid` (OverlayBridge.v) supplies this lemma's
   hypotheses, so the corpus has NO `Admitted` -- the residual is exactly the
   named planar Euler identity.

   Pure combinatorial wiring; no `Admitted` / `Axiom` / `Parameter`; allowlist
   axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import List Arith Lia.
From NTS.Proofs Require Import Distance Overlay OverlayGraph Dart DartNextSpec
                               DartAngularOrder DartFace FaceOrbitSep NoShortFaces
                               ExtractFaces EdgeConnectivity EdgeFaceBridge
                               MapCounts EulerArrangement EulerBridge NumFacesSplice.

Import ListNotations.

(* The planar Euler identity (carried as named hypotheses) discharges the
   bridge premise: a same-face edge is a bridge. *)
Theorem H_bridge_premise_from_euler : forall (E : list Edge),
  (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
  no_spurs (darts_of E) ->
  NoDup E ->
  euler_characteristic E ->
  (forall e, In e E -> euler_characteristic (E_minus E e)) ->
  (forall e, In e E -> num_vertices (E_minus E e) = num_vertices E) ->
  H_bridge_premise E.
Proof.
  intros E Hfan Hns Hnodup HeulE HeulEm HvertEm.
  assert (Hao : arrangement_ok (darts_of E))
    by (split; [ apply darts_of_closed_under_twin | exact Hfan ]).
  intros d Hd Hsf Hde. split.
  - (* d in E: ~ reachable (E_minus E d) (dtip d) (dbase d) *)
    intros HdE Hntwin Hreach.
    assert (Hne : dbase d <> dtip d) by (apply dart_endpoints_neE; exact Hde).
    assert (Hcount : count_occ edge_eq_dec E d = 1%nat)
      by (apply count_occ_1_of_NoDup; assumption).
    assert (HEd : num_edges (E_minus E d) + 1 = num_edges E)
      by (apply num_edges_E_minus; exact Hcount).
    assert (HF : num_faces (E_minus E d) = (num_faces E + 1)%nat)
      by (apply num_faces_E_minus_splice; assumption).
    apply (H_bridge_core_conclusion_from_euler E d
             HeulE (HeulEm d HdE) (HvertEm d HdE) HEd HF).
    apply reach_sym. exact Hreach.
  - (* twin d in E: ~ reachable (E_minus E (twin d)) (dbase d) (dtip d) *)
    intros HtwinE Hnd Hreach.
    assert (Hsf' : same_face (darts_of E) (twin d) (twin (twin d))).
    { rewrite twin_involutive.
      exact (same_face_sym (darts_of E) Hao d (twin d) Hd Hsf). }
    assert (Hne' : dbase (twin d) <> dtip (twin d)).
    { rewrite dbase_twin, dtip_twin. intro Heq.
      apply (dart_endpoints_neE d Hde). symmetry. exact Heq. }
    assert (Hntwin' : ~ In (twin (twin d)) E) by (rewrite twin_involutive; exact Hnd).
    assert (Hcount : count_occ edge_eq_dec E (twin d) = 1%nat)
      by (apply count_occ_1_of_NoDup; assumption).
    assert (HEd : num_edges (E_minus E (twin d)) + 1 = num_edges E)
      by (apply num_edges_E_minus; exact Hcount).
    assert (HF : num_faces (E_minus E (twin d)) = (num_faces E + 1)%nat)
      by (apply num_faces_E_minus_splice with (d := twin d); assumption).
    apply (H_bridge_core_conclusion_from_euler E (twin d)
             HeulE (HeulEm (twin d) HtwinE) (HvertEm (twin d) HtwinE) HEd HF).
    apply reach_sym. exact Hreach.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Combinatorial wiring; allowlist axioms only.                  *)
(* -------------------------------------------------------------------------- *)

Print Assumptions H_bridge_premise_from_euler.
