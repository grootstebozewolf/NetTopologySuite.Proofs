(* ============================================================================
   NetTopologySuite.Proofs.EdgeFaceBridge
   ----------------------------------------------------------------------------
   extract_rings_valid R5, H_bridge rung: link graph cut edges to rotation-system
   face orbits.

   Target (forward implication only):

     edge_2_connected E -> twins_in_different_faces (darts_of E)

   Equivalently (contrapositive core): if a proper dart d shares an `fstep`
   orbit with its twin, the undirected edge is a cut edge (`same_face_twin_is_cut`
   in §3 — the open rung).

   Layers consumed:
     - EdgeConnectivity.v   (reachable / is_cut_edge / edge_2_connected)
     - FaceOrbitSep.v       (same_face / twins_in_different_faces)
     - FaceChain.v          (dart_walk / face_chain)
     - ExtractFaces.v       (face_period)
     - VertexGeneralPosition.v (well_noded_darts -> fan_ok)

   No Admitted / Axiom / Parameter; allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Lia.
From NTS.Proofs Require Import Distance Overlay OverlayGraph Vec Azimuth
                               Dart DartNextSpec DartAngularOrder OrbitCycle
                               DartFace FaceChain FaceRingSimple FaceOrbitSep
                               ExtractFaces EdgeConnectivity
                               VertexGeneralPosition NoShortFaces.

Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  Dart ↔ edge incidence (Edge = Dart in this corpus).                     *)
(* -------------------------------------------------------------------------- *)

Lemma dart_in_darts_of_cases :
  forall E d, In d (darts_of E) -> In d E \/ In (twin d) E.
Proof.
  intros E d H. unfold darts_of in H. apply in_app_or in H.
  destruct H as [H | H]; [ left; exact H | right ].
  apply in_map_iff in H. destruct H as [e [Heq Hin]]. rewrite <- Heq, twin_involutive.
  exact Hin.
Qed.

Lemma twin_in_darts_of_orig :
  forall E e, In e E -> In (twin e) (darts_of E).
Proof. intros E e H. apply in_darts_of_twin. exact H. Qed.

Lemma twin_edge_endpoints_swap :
  forall d, fst (twin d) = dtip d /\ snd (twin d) = dbase d.
Proof. intros d. rewrite dbase_twin, dtip_twin. split; reflexivity. Qed.

(* An edge of `E` carrying the same undirected segment as dart `d`. *)
Lemma dart_carrier_edge :
  forall E d, In d (darts_of E) ->
    exists e, In e E /\ (e = d \/ e = twin d).
Proof.
  intros E d H.
  destruct (dart_in_darts_of_cases E d H) as [Hd | Ht].
  - exists d. split; [ exact Hd | left; reflexivity ].
  - exists (twin d). split; [ exact Ht | right; reflexivity ].
Qed.

Lemma dart_carrier_proper :
  forall E d e,
    In d (darts_of E) -> dbase d <> dtip d ->
    In e E -> (e = d \/ e = twin d) ->
    fst e <> snd e.
Proof.
  intros E d e Hd Hne He [-> | ->].
  - cbn. exact Hne.
  - destruct (twin_edge_endpoints_swap d) as [Hfst Hsnd].
    rewrite Hfst, Hsnd. intro Heq. apply Hne. symmetry. exact Heq.
Qed.

(* Endpoints of a proper dart are adjacent in the edge graph. *)
Lemma dart_endpoints_adj :
  forall E d, In d (darts_of E) -> dbase d <> dtip d ->
    adj E (dbase d) (dtip d).
Proof.
  intros E d Hd Hne.
  destruct (dart_carrier_edge E d Hd) as [e [He Hcase]].
  destruct Hcase as [-> | Htwin].
  - apply adj_edge. exact He.
  - assert (He' : In (twin d) E) by (rewrite <- Htwin; exact He).
    unfold adj. exists (twin d). split; [ exact He' | ].
    right. split; [ apply dbase_twin | apply dtip_twin ].
Qed.

Lemma dart_endpoints_reachable :
  forall E d, In d (darts_of E) -> dbase d <> dtip d ->
    reachable E (dbase d) (dtip d).
Proof.
  intros E d Hd Hne. apply reach_one, dart_endpoints_adj; assumption.
Qed.

Lemma dart_endpoints_ne_of_proper :
  forall d, proper_dart d -> dbase d <> dtip d.
Proof.
  intros d Hpr Heq.
  apply Hpr. unfold ddir. rewrite Heq.
  unfold point_diff, vzero. apply Vec_eq; cbn [vx vy]; ring.
Qed.

Lemma dart_proper_of_fan :
  forall D d, In d D ->
    (forall v : Point, fan_ok (outgoing v D)) ->
    proper_dart d.
Proof.
  intros D d Hd Hfan.
  assert (Ho : In d (outgoing (dbase d) D)).
  { apply in_outgoing. split; [ exact Hd | reflexivity ]. }
  destruct (Hfan (dbase d)) as [Hprop _]. exact (Hprop d Ho).
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Face walk ↔ same_face linkage.                                          *)
(* -------------------------------------------------------------------------- *)

Lemma arrangement_ok_of_fan :
  forall E, (forall v, fan_ok (outgoing v (darts_of E))) ->
    arrangement_ok (darts_of E).
Proof. intros E H. apply arrangement_ok_darts_of. exact H. Qed.

Lemma same_face_in_period_walk :
  forall D a b,
    arrangement_ok D -> In a D ->
    same_face D a b ->
    In b (dart_walk D a (face_period D a)).
Proof.
  intros D a b Hok Ha Hsf.
  apply (walk_at_period_iff_same_face D Hok a Ha b). exact Hsf.
Qed.

Lemma same_face_twin_in_period_walk :
  forall E d,
    (forall v, fan_ok (outgoing v (darts_of E))) ->
    In d (darts_of E) ->
    same_face (darts_of E) d (twin d) ->
    In (twin d) (dart_walk (darts_of E) d (face_period (darts_of E) d)).
Proof.
  intros E d Hfan Hd Hsf.
  set (D := darts_of E).
  assert (Hok : arrangement_ok D) by (apply arrangement_ok_of_fan; exact Hfan).
  assert (Ha : In d D) by (subst D; exact Hd).
  apply (same_face_in_period_walk D d (twin d) Hok Ha Hsf).
Qed.

Lemma same_face_refl_on_period_walk :
  forall E d,
    (forall v, fan_ok (outgoing v (darts_of E))) ->
    In d (darts_of E) ->
    In d (dart_walk (darts_of E) d (face_period (darts_of E) d)).
Proof.
  intros E d Hfan Hd.
  set (D := darts_of E).
  assert (Hok : arrangement_ok D) by (apply arrangement_ok_of_fan; exact Hfan).
  assert (Ha : In d D) by (subst D; exact Hd).
  apply (same_face_in_period_walk D d d Hok Ha (same_face_refl D d)).
Qed.

Lemma same_face_twin_both_on_period_walk :
  forall E d,
    (forall v, fan_ok (outgoing v (darts_of E))) ->
    In d (darts_of E) ->
    same_face (darts_of E) d (twin d) ->
    In d (dart_walk (darts_of E) d (face_period (darts_of E) d)) /\
    In (twin d) (dart_walk (darts_of E) d (face_period (darts_of E) d)).
Proof.
  intros E d Hfan Hd Hsf. split.
  - apply same_face_refl_on_period_walk; assumption.
  - apply same_face_twin_in_period_walk; assumption.
Qed.

Lemma same_face_of_one_spur_step :
  forall D d, In d D -> fstep D d = twin d -> same_face D d (twin d).
Proof.
  intros D d Hd Hspur. exists 1%nat. cbn [iter]. exact Hspur.
Qed.

(* Every dart on a face walk is a carrier edge of `E` and joins its endpoints. *)
Lemma dart_on_walk_endpoints_adj :
  forall E d n x,
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    In d (darts_of E) ->
    In x (dart_walk (darts_of E) d n) ->
    adj E (dbase x) (dtip x).
Proof.
  intros E d n x Hfan Hd Hx.
  set (D := darts_of E).
  assert (Htw : forall z, In z D -> In (twin z) D)
    by (apply darts_of_closed_under_twin).
  assert (HxD : In x D) by (apply (dart_walk_subset D Htw n d Hd x Hx)).
  assert (Hne : dbase x <> dtip x).
  { apply dart_endpoints_ne_of_proper.
    apply dart_proper_of_fan with (D := D); assumption. }
  apply dart_endpoints_adj with (d := x); [ exact HxD | exact Hne ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The bridge lemma (rotation-system core) — OPEN.                         *)
(*                                                                            *)
(* Target (Rung 3):                                                            *)
(*                                                                            *)
(*   same_face_twin_is_cut :                                                   *)
(*     forall E d, fan_ok on darts_of E -> no_spurs (darts_of E) ->            *)
(*     In d (darts_of E) -> dbase d <> dtip d ->                               *)
(*     same_face (darts_of E) d (twin d) ->                                    *)
(*     exists e, In e E /\ is_cut_edge E e /\ (e = d \/ e = twin d).          *)
(*                                                                            *)
(* `no_spurs` is necessary: on a bigon (two opposite darts, `fstep d = twin d` *)
(* at both tips) `fan_ok` holds but neither edge is a cut edge.                *)
(*                                                                            *)
(* Packaging (Rung 4): contrapositive assembly once §3 is available.           *)
(* -------------------------------------------------------------------------- *)

Section BridgePackaging.
  Variable same_face_twin_is_cut :
    forall (E : list Edge) (d : Dart),
      (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
      no_spurs (darts_of E) ->
      In d (darts_of E) ->
      dbase d <> dtip d ->
      same_face (darts_of E) d (twin d) ->
      exists e : Edge,
        In e E /\ is_cut_edge E e /\ (e = d \/ e = twin d).

  Theorem edge_2_connected_twins_sep :
    forall (E : list Edge),
      (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
      no_spurs (darts_of E) ->
      edge_2_connected E ->
      twins_in_different_faces (darts_of E).
  Proof.
    intros E Hfan Hns H2. unfold twins_in_different_faces.
    intros d Hd Hsf.
    assert (Hne : dbase d <> dtip d).
    { apply dart_endpoints_ne_of_proper.
      apply dart_proper_of_fan with (D := darts_of E); assumption. }
    destruct (same_face_twin_is_cut E d Hfan Hns Hd Hne Hsf) as
      [e [He [Hcut Hcase]]].
    apply (H2 e He). exact Hcut.
  Qed.

  Theorem H_bridge_well_noded :
    forall (E : list Edge),
      well_noded_darts E ->
      no_spurs (darts_of E) ->
      edge_2_connected E ->
      twins_in_different_faces (darts_of E).
  Proof.
    intros E Hwn Hns H2.
    apply (edge_2_connected_twins_sep E).
    - intro v. apply well_noded_fan_ok. exact Hwn.
    - exact Hns.
    - exact H2.
  Qed.
End BridgePackaging.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions dart_carrier_edge.
Print Assumptions same_face_twin_in_period_walk.
Print Assumptions same_face_twin_both_on_period_walk.
Print Assumptions dart_on_walk_endpoints_adj.
Print Assumptions dart_endpoints_reachable.
Print Assumptions dart_endpoints_ne_of_proper.