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
                               VertexGeneralPosition NoShortFaces FaceTwinAware.

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

Lemma dart_carrier_endpoints :
  forall E d e,
    In d (darts_of E) -> dbase d <> dtip d ->
    In e E -> (e = d \/ e = twin d) ->
    (fst e = dbase d /\ snd e = dtip d) \/
    (fst e = dtip d /\ snd e = dbase d).
Proof.
  intros E d e Hd Hne He Hcase.
  destruct Hcase as [-> | Htwin].
  - left. split; reflexivity.
  - right. destruct (twin_edge_endpoints_swap d) as [Hfst Hsnd].
    subst e. split; [ exact Hfst | exact Hsnd ].
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

(* Walk-level reachability: `iter (fstep D) n d` is the last dart of a length-(S n)
   walk (`dart_walk_last`), so its tip is reachable from `dbase d` in `E`. *)
Lemma dart_walk_endpoints_reachable_iter :
  forall (E : list Edge) (D : list Dart) (d : Dart) (n : nat),
    D = darts_of E ->
    (forall v : Point, fan_ok (outgoing v D)) ->
    (forall x, In x D -> In (twin x) D) ->
    In d D ->
    reachable E (dbase d) (dtip (iter (fstep D) n d)).
Proof.
  intros E D d n HD Hfan Htw Hd.
  revert d Hd.
  induction n as [| n IHn]; intros d Hd.
  - cbn [iter].
    assert (HdE : In d (darts_of E)) by (rewrite <- HD; exact Hd).
    apply dart_endpoints_reachable with (d := d); [ exact HdE | ].
    apply dart_endpoints_ne_of_proper, dart_proper_of_fan with (D := D); assumption.
  - cbn [iter].
    assert (HdE : In d (darts_of E)) by (rewrite <- HD; exact Hd).
    assert (HfanE : forall v, fan_ok (outgoing v (darts_of E))).
    { intro v. rewrite <- HD. apply Hfan. }
    apply reach_trans with (dtip d).
    + apply reach_one, dart_on_walk_endpoints_adj with (d := d) (n := S n)
        (x := d); [ exact HfanE | exact HdE | left; reflexivity ].
    + rewrite <- (dbase_fstep D d Htw Hd).
      assert (Heq : fstep D (iter (fstep D) n d) = iter (fstep D) n (fstep D d))
        by (symmetry; apply iter_succ_inside).
      rewrite Heq. apply IHn. apply fstep_in; assumption.
Qed.

Lemma dart_walk_endpoints_reachable :
  forall E d n,
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    In d (darts_of E) ->
    (1 <= n)%nat ->
    reachable E (dbase d)
      (dtip (last (dart_walk (darts_of E) d n) d)).
Proof.
  intros E d n Hfan Hd Hle.
  set (D := darts_of E).
  assert (Htw : forall x, In x D -> In (twin x) D)
    by (apply darts_of_closed_under_twin).
  destruct n as [| n']; [ lia | ].
  assert (Hlast : last (dart_walk D d (S n')) d = iter (fstep D) n' d).
  { apply dart_walk_last. }
  rewrite Hlast.
  apply (dart_walk_endpoints_reachable_iter E D d n'); [ reflexivity | exact Hfan | exact Htw | exact Hd ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Toward same_face_twin_is_cut (Rung 3).                                   *)
(* -------------------------------------------------------------------------- *)

Lemma all_proper_darts_of_fan :
  forall D, (forall v : Point, fan_ok (outgoing v D)) -> all_proper_darts D.
Proof.
  intros D Hfan d Hd. apply dart_proper_of_fan with (D := D); assumption.
Qed.

Lemma face_period_ge3_of_fan_nospur :
  forall E d,
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    no_spurs (darts_of E) ->
    In d (darts_of E) ->
    (3 <= face_period (darts_of E) d)%nat.
Proof.
  intros E d Hfan Hns Hd.
  set (D := darts_of E).
  assert (Hok : arrangement_ok D) by (apply arrangement_ok_of_fan; exact Hfan).
  assert (Hshort : no_short_faces D).
  { apply no_short_faces_of_proper_nospur; [ exact Hok | | exact Hns ].
    apply all_proper_darts_of_fan. exact Hfan. }
  unfold no_short_faces in Hshort. exact (Hshort d Hd).
Qed.

Lemma same_face_twin_step_index :
  forall E d,
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    In d (darts_of E) ->
    same_face (darts_of E) d (twin d) ->
    exists k, (k < face_period (darts_of E) d)%nat /\
      iter (fstep (darts_of E)) k d = twin d.
Proof.
  intros E d Hfan Hd Hsf.
  set (D := darts_of E).
  assert (Hok : arrangement_ok D) by (apply arrangement_ok_of_fan; exact Hfan).
  assert (Htwin : In (twin d) (dart_walk D d (face_period D d))).
  { subst D; apply same_face_twin_in_period_walk; assumption. }
  apply dart_walk_iter_iff in Htwin.
  destruct Htwin as [k [Hk Hit]]. exists k. split; [ exact Hk | exact Hit ].
Qed.

Lemma same_face_twin_step_not_one :
  forall E d k,
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    no_spurs (darts_of E) ->
    In d (darts_of E) ->
    iter (fstep (darts_of E)) k d = twin d ->
    (2 <= k)%nat.
Proof.
  intros E d k Hfan Hns Hd Hit.
  assert (Hne : dbase d <> dtip d).
  { apply dart_endpoints_ne_of_proper.
    apply dart_proper_of_fan with (D := darts_of E) (d := d); [ exact Hd | exact Hfan ]. }
  destruct k as [| k']; cbn [iter] in Hit.
  - exfalso. apply (twin_neq_self d Hne). symmetry. exact Hit.
  - destruct k' as [| k'']; [ | lia ].
    exfalso. apply (Hns d Hd). exact Hit.
Qed.

Lemma is_cut_edge_of_disconnect :
  forall (E : list Edge) (e : Edge) (u v : Point),
    In e E -> fst e = u -> snd e = v -> u <> v ->
    reachable E u v ->
    ~ reachable (E_minus E e) u v ->
    is_cut_edge E e.
Proof.
  intros E e u v He Hfu Hsv Huv Hreach Hdis.
  unfold is_cut_edge. repeat split.
  - exact He.
  - rewrite Hfu, Hsv. exact Huv.
  - rewrite Hfu, Hsv. exact Hreach.
  - rewrite Hfu, Hsv. exact Hdis.
Qed.

Lemma dart_endpoints_adj_E_minus :
  forall E d e,
    In d (darts_of E) -> dbase d <> dtip d ->
    In e E -> e <> d -> e <> twin d ->
    adj (E_minus E e) (dbase d) (dtip d).
Proof.
  intros E d e Hd Hne He Hned Hntwin.
  destruct (dart_carrier_edge E d Hd) as [ec [Hec Hcase]].
  unfold adj. exists ec. split.
  - apply in_E_minus. split; [ exact Hec | ].
    intro Heq. destruct Hcase as [-> | Htwin].
    + apply Hned. symmetry. exact Heq.
    + apply Hntwin. rewrite <- Heq. exact Htwin.
  - destruct Hcase as [-> | Htwin].
    + left. split; reflexivity.
    + right. rewrite Htwin. split; [ apply dbase_twin | apply dtip_twin ].
Qed.

Lemma is_cut_edge_of_dart_disconnect :
  forall E d e,
    In d (darts_of E) -> dbase d <> dtip d ->
    In e E -> (e = d \/ e = twin d) ->
    ~ reachable (E_minus E e) (dbase d) (dtip d) ->
    is_cut_edge E e.
Proof.
  intros E d e Hd Hne He Hcase Hdis.
  assert (Hreach : reachable E (dbase d) (dtip d))
    by (apply dart_endpoints_reachable; assumption).
  assert (Hprop : fst e <> snd e).
  { apply dart_carrier_proper with (E := E) (d := d) (e := e); assumption. }
  destruct Hcase as [-> | Htwin].
  - apply is_cut_edge_of_disconnect with (u := dbase d) (v := dtip d);
      [ exact He | reflexivity | reflexivity | exact Hne | exact Hreach | exact Hdis ].
  - subst e.
    apply is_cut_edge_of_disconnect with (u := dtip d) (v := dbase d).
    + exact He.
    + apply dbase_twin.
    + apply dtip_twin.
    + exact Hprop.
    + apply reach_sym. exact Hreach.
    + intro Hr. apply Hdis. apply reach_sym in Hr. exact Hr.
Qed.

(* Easy direction: a bypass in `E_minus` refutes `is_cut_edge`. *)
Lemma reachable_E_minus_implies_not_cut :
  forall (E : list Edge) (e : Edge) (u v : Point),
    In e E -> fst e = u -> snd e = v -> u <> v ->
    reachable (E_minus E e) u v ->
    ~ is_cut_edge E e.
Proof.
  intros E e u v He Hfu Hsv Huv Hreach.
  intro Hcut. unfold is_cut_edge in Hcut.
  destruct Hcut as [_ [_ [_ Hdis]]].
  rewrite Hfu, Hsv in Hdis. exact (Hdis Hreach).
Qed.

(* `same_face` with `twin` places both orientations on the period walk, so the
   per-face twin-freeness hypothesis fails (the dumbbell obstruction). *)
Lemma same_face_twin_breaks_face_twin_free :
  forall E d,
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    In d (darts_of E) ->
    same_face (darts_of E) d (twin d) ->
    ~ face_twin_free (darts_of E) d (face_period (darts_of E) d).
Proof.
  intros E d Hfan Hd Hsf Htf.
  assert (Hdwalk : In d (dart_walk (darts_of E) d (face_period (darts_of E) d))).
  { apply same_face_refl_on_period_walk; assumption. }
  assert (Htwinwalk : In (twin d) (dart_walk (darts_of E) d (face_period (darts_of E) d))).
  { apply same_face_twin_in_period_walk; assumption. }
  apply (Htf d Hdwalk). exact Htwinwalk.
Qed.

(* Twin occurs at step `k >= 2`; the first `k` face-walk darts join `dbase d`
   to `dtip d` in the full edge graph. *)
Lemma same_face_twin_reachable_k :
  forall E d k,
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    In d (darts_of E) ->
    (2 <= k)%nat ->
    iter (fstep (darts_of E)) k d = twin d ->
    reachable E (dbase d) (dtip d).
Proof.
  intros E d k Hfan Hd Hk Hit.
  set (D := darts_of E).
  assert (Htw : forall z, In z D -> In (twin z) D)
    by (subst D; apply darts_of_closed_under_twin).
  assert (Hreach : reachable E (dbase d)
      (dtip (last (dart_walk D d k) d))).
  { subst D. apply (dart_walk_endpoints_reachable E d k); [ exact Hfan | exact Hd | lia ]. }
  assert (Hlast : last (dart_walk D d k) d = iter (fstep D) (pred k) d).
  { destruct k as [| k']; [ lia | destruct k' as [| k'']; [ lia | ]].
    apply dart_walk_last. }
  rewrite Hlast in Hreach.
  assert (Htip : dtip (iter (fstep D) (pred k) d) = dtip d).
  { destruct k as [| k']; [ lia | cbn [iter] ].
    assert (Hin : In (iter (fstep D) k' d) D).
    { apply (face_walk_in D Htw d k' Hd). }
    pose proof (dbase_fstep D (iter (fstep D) k' d) Htw Hin) as Hbs.
    assert (Heq : fstep D (iter (fstep D) k' d) = iter (fstep D) (S k') d)
      by (cbn [iter]; reflexivity).
    assert (Hit' : iter (fstep D) (S k') d = twin d) by (subst D; exact Hit).
    rewrite Heq in Hbs. rewrite Hit', dbase_twin in Hbs. symmetry. exact Hbs. }
  rewrite Htip in Hreach. exact Hreach.
Qed.

(* On the period walk, every dart except the carrier orientations stays
   adjacent after removing the carrier edge. *)
Lemma dart_on_walk_endpoints_adj_E_minus :
  forall E d0 e n x,
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    In d0 (darts_of E) ->
    In e E -> (e = d0 \/ e = twin d0) ->
    In x (dart_walk (darts_of E) d0 n) ->
    x <> d0 -> x <> twin d0 ->
    adj (E_minus E e) (dbase x) (dtip x).
Proof.
  intros E d0 e n x Hfan Hd0 He Hcase Hx Hxd Hxtwin.
  assert (HxD : In x (darts_of E)).
  { set (D := darts_of E) in *.
    assert (Htw : forall z, In z D -> In (twin z) D)
      by (subst D; apply darts_of_closed_under_twin).
    apply (dart_walk_subset D Htw n d0 Hd0 x Hx). }
  assert (Hne : dbase x <> dtip x).
  { apply dart_endpoints_ne_of_proper.
    apply dart_proper_of_fan with (D := darts_of E); assumption. }
  assert (Hnex : e <> x).
  { intro H. destruct Hcase as [-> | Ht].
    - apply Hxd. symmetry. exact H.
    - apply Hxtwin. transitivity e; [ symmetry; exact H | exact Ht ]. }
  assert (Hnetx : e <> twin x).
  { intro H. destruct Hcase as [-> | Ht].
    - apply Hxtwin. symmetry. apply twin_inj. rewrite twin_involutive. exact H.
    - apply Hxd. apply twin_inj. rewrite <- Ht, H. reflexivity. }
  apply dart_endpoints_adj_E_minus with (d := x); assumption.
Qed.

(* Open core (Rung 3b): the rotation-system disconnectivity fact.              *)
Section SameFaceTwinCutCore.
  Variable same_face_twin_disconnect :
    forall (E : list Edge) (d : Dart) (e : Edge),
      (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
      no_spurs (darts_of E) ->
      In d (darts_of E) ->
      dbase d <> dtip d ->
      same_face (darts_of E) d (twin d) ->
      In e E -> (e = d \/ e = twin d) ->
      ~ reachable (E_minus E e) (dbase d) (dtip d).

  Theorem same_face_twin_is_cut :
    forall (E : list Edge) (d : Dart),
      (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
      no_spurs (darts_of E) ->
      In d (darts_of E) ->
      dbase d <> dtip d ->
      same_face (darts_of E) d (twin d) ->
      exists e : Edge,
        In e E /\ is_cut_edge E e /\ (e = d \/ e = twin d).
  Proof.
    intros E d Hfan Hns Hd Hne Hsf.
    destruct (dart_carrier_edge E d Hd) as [e [He Hcase]].
    exists e. split; [ exact He | split ].
    - apply is_cut_edge_of_dart_disconnect with (d := d); [ exact Hd | exact Hne | exact He | exact Hcase | ].
      apply same_face_twin_disconnect with (E := E) (d := d) (e := e); assumption.
    - exact Hcase.
  Qed.
End SameFaceTwinCutCore.

(* -------------------------------------------------------------------------- *)
(* §4  Contrapositive packaging (modulo §3).                                   *)
(* -------------------------------------------------------------------------- *)

Section BridgePackaging.
  (* Abstract §3 conclusion; instantiate from `SameFaceTwinCutCore` once
     `same_face_twin_disconnect` is proved. *)
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
Print Assumptions dart_carrier_endpoints.
Print Assumptions same_face_twin_in_period_walk.
Print Assumptions same_face_twin_both_on_period_walk.
Print Assumptions dart_on_walk_endpoints_adj.
Print Assumptions dart_walk_endpoints_reachable_iter.
Print Assumptions dart_walk_endpoints_reachable.
Print Assumptions face_period_ge3_of_fan_nospur.
Print Assumptions same_face_twin_step_index.
Print Assumptions is_cut_edge_of_dart_disconnect.
Print Assumptions reachable_E_minus_implies_not_cut.
Print Assumptions same_face_twin_breaks_face_twin_free.
Print Assumptions same_face_twin_reachable_k.
Print Assumptions dart_on_walk_endpoints_adj_E_minus.
Print Assumptions dart_endpoints_reachable.
Print Assumptions dart_endpoints_ne_of_proper.