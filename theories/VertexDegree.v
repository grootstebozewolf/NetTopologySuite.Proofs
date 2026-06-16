(* ============================================================================
   NetTopologySuite.Proofs.VertexDegree
   ----------------------------------------------------------------------------
   extract_rings_valid R5, face_twin_free closure rung 1 (H7): discharge the
   vertex-invariance hypothesis

     forall e, In e E -> num_vertices (E_minus E e) = num_vertices E

   from `no_spurs (darts_of E)` + `well_noded_darts E`.

   `num_vertices_E_minus_le` (EulerArrangement.v) already gives the `<=`
   direction.  The reverse needs: removing one edge `e = (u, v)` strands no
   vertex, i.e. each of `u`, `v` survives on another edge -- minimum degree 2.
   `no_spurs` supplies exactly this: if the only outgoing dart at a vertex were
   the reversal `twin d` of a dart `d` ending there, the face step `fstep` would
   fold `d` onto `twin d` (a spur).  Concretely (`no_spur_fan_has_other`): the
   rotational successor `next (outgoing (dtip d) ..) (twin d)` stays in the fan
   (`next_in`); were every fan element equal to `twin d` it would return
   `twin d`, contradicting `no_spurs`.  So every vertex has an outgoing dart
   other than the reversal, and -- since the two darts carrying `e` sit at the
   two DISTINCT endpoints of the proper edge `e` -- that other dart carries a
   DIFFERENT edge, which keeps the endpoint in `verts (E_minus E e)`.

   This removes H7 from `HBridgeEuler.H_bridge_premise_from_euler` and from the
   `OverlayBridge` capstones, shrinking the carried hypothesis set.

   Pure dart + list combinatorics; no `Admitted` / `Axiom` / `Parameter`;
   allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import List Arith Lia.
From NTS.Proofs Require Import Distance Overlay OverlayGraph Dart DartAngularOrder
                               DartNext DartFace EdgeConnectivity ReachableDec
                               NodedGeneralPosition VertexGeneralPosition
                               NoShortFaces EulerArrangement EdgeFaceBridge.

Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  The fan reversal is outgoing at the tip.                                *)
(* -------------------------------------------------------------------------- *)

Lemma outgoing_tip_twin_In : forall E d,
  In d (darts_of E) -> In (twin d) (outgoing (dtip d) (darts_of E)).
Proof.
  intros E d Hd. apply in_outgoing. split.
  - apply darts_of_closed_under_twin. exact Hd.
  - apply dbase_twin.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  no_spurs gives a fan element other than the reversal (min-degree-2).    *)
(* -------------------------------------------------------------------------- *)

(* If the rotational successor of `twin d` in the tip fan returned `twin d`,
   that would be a spur (`fstep D d = twin d`); `no_spurs` forbids it, so the
   fan contains some dart distinct from `twin d`. *)
Lemma no_spur_fan_has_other : forall E d,
  no_spurs (darts_of E) ->
  In d (darts_of E) ->
  exists y, In y (outgoing (dtip d) (darts_of E)) /\ y <> twin d.
Proof.
  intros E d Hns Hd.
  assert (Htw : In (twin d) (outgoing (dtip d) (darts_of E)))
    by (apply outgoing_tip_twin_In; exact Hd).
  destruct (edge_eq_dec (next (outgoing (dtip d) (darts_of E)) (twin d)) (twin d))
    as [Heq | Hne].
  - exfalso. apply (Hns d Hd). unfold fstep. exact Heq.
  - exists (next (outgoing (dtip d) (darts_of E)) (twin d)).
    split; [ apply next_in; exact Htw | exact Hne ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Carrier uniqueness at a vertex.                                         *)
(*                                                                            *)
(* The two darts carrying a proper edge `e` are `e` (based at `fst e`) and      *)
(* `twin e` (based at `snd e`); since `fst e <> snd e`, at most one is based    *)
(* at any given vertex.                                                        *)
(* -------------------------------------------------------------------------- *)

Lemma at_most_one_carrier_at_vertex :
  forall (e x y : Dart) (w : Point),
    fst e <> snd e ->
    dbase x = w -> dbase y = w ->
    (x = e \/ x = twin e) -> (y = e \/ y = twin e) ->
    x = y.
Proof.
  intros e x y w Hproper Hx Hy Hxc Hyc.
  unfold dbase, twin in *.
  destruct Hxc as [-> | ->]; destruct Hyc as [-> | ->];
    cbn [fst snd] in Hx, Hy; try reflexivity;
    (exfalso; apply Hproper; rewrite Hx, Hy; reflexivity).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Vertex survival under single-edge deletion.                            *)
(* -------------------------------------------------------------------------- *)

Lemma vertex_survives_E_minus :
  forall E e w,
    no_spurs (darts_of E) -> well_noded_darts E ->
    In e E -> (fst e = w \/ snd e = w) ->
    In w (verts (E_minus E e)).
Proof.
  intros E e w Hns Hwn He Hor.
  assert (HeD : In e (darts_of E)) by (apply in_darts_of_orig; exact He).
  assert (Hproper : proper_dart e).
  { destruct Hwn as (_ & Hap & _). exact (Hap e HeD). }
  assert (Hne_e : dbase e <> dtip e) by (apply dart_endpoints_ne_of_proper; exact Hproper).
  assert (Hfst_snd : fst e <> snd e) by (unfold dbase, dtip in Hne_e; exact Hne_e).
  (* a dart d0 of e ending at w, so twin d0 is the carrier-of-e dart based at w *)
  assert (Hdin : exists d0, In d0 (darts_of E) /\ dtip d0 = w
                   /\ (twin d0 = e \/ twin d0 = twin e)).
  { destruct Hor as [Hf | Hs].
    - exists (twin e). repeat split.
      + apply in_darts_of_twin; exact He.
      + rewrite dtip_twin. unfold dbase in *; exact Hf.
      + left. apply twin_involutive.
    - exists e. repeat split.
      + exact HeD.
      + unfold dtip in *; exact Hs.
      + right. reflexivity. }
  destruct Hdin as [d0 [Hd0 [Htip0 Htwc]]].
  assert (Hbtw : dbase (twin d0) = w) by (rewrite dbase_twin; exact Htip0).
  (* min-degree-2: a fan dart y at w distinct from the carrier-of-e dart twin d0 *)
  destruct (no_spur_fan_has_other E d0 Hns Hd0) as [y [Hy Hyne]].
  rewrite Htip0 in Hy.
  assert (HyP : In y (darts_of E) /\ dbase y = w) by (apply in_outgoing; exact Hy).
  destruct HyP as [HyD Hyw].
  destruct (dart_carrier_edge E y HyD) as [e' [He' Hcar]].
  assert (Hne' : e' <> e).
  { intro Habs. subst e'.
    assert (Hyc : y = e \/ y = twin e).
    { destruct Hcar as [Heq | Heq].
      - left. symmetry. exact Heq.
      - right. assert (Ht : twin e = y) by (rewrite Heq, twin_involutive; reflexivity).
        symmetry; exact Ht. }
    assert (Hyeq : y = twin d0)
      by (apply (at_most_one_carrier_at_vertex e y (twin d0) w
                   Hfst_snd Hyw Hbtw Hyc Htwc)).
    apply Hyne. exact Hyeq. }
  apply in_verts. exists e'. split.
  - apply in_E_minus. split; [ exact He' | exact Hne' ].
  - destruct Hcar as [Heq | Heq].
    + left. rewrite Heq. unfold dbase in Hyw. exact Hyw.
    + right. rewrite Heq. unfold twin; cbn [fst snd]. unfold dbase in Hyw. exact Hyw.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Reverse inclusion and the vertex-count equality (H7).                   *)
(* -------------------------------------------------------------------------- *)

Lemma verts_incl_E_minus :
  forall E e,
    no_spurs (darts_of E) -> well_noded_darts E -> In e E ->
    incl (verts E) (verts (E_minus E e)).
Proof.
  intros E e Hns Hwn He p Hp.
  apply in_verts in Hp. destruct Hp as [e0 [He0 Hor]].
  destruct (edge_eq_dec e0 e) as [-> | Hdiff].
  - apply (vertex_survives_E_minus E e p Hns Hwn He Hor).
  - apply in_verts. exists e0. split.
    + apply in_E_minus. split; [ exact He0 | exact Hdiff ].
    + exact Hor.
Qed.

Theorem num_vertices_E_minus_eq :
  forall E e,
    no_spurs (darts_of E) -> well_noded_darts E -> In e E ->
    num_vertices (E_minus E e) = num_vertices E.
Proof.
  intros E e Hns Hwn He.
  apply Nat.le_antisymm.
  - apply num_vertices_E_minus_le.
  - unfold num_vertices. apply NoDup_incl_length; [ apply NoDup_nodup | ].
    intros p Hp. rewrite nodup_In in Hp. rewrite nodup_In.
    apply (verts_incl_E_minus E e Hns Hwn He). exact Hp.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure dart + list combinatorics; allowlist axioms only.        *)
(* -------------------------------------------------------------------------- *)

Print Assumptions no_spur_fan_has_other.
Print Assumptions vertex_survives_E_minus.
Print Assumptions num_vertices_E_minus_eq.
