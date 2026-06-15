(* ============================================================================
   NetTopologySuite.Proofs.MonotoneChainCoverage
   ----------------------------------------------------------------------------
   Convex-chain monotonicity campaign, RUNG 4: the edge-halfplane algebraic
   bridge and the general `interior_hits_one_chain` construction.

   The key algebraic identity: for an edge e = (a, b) and the canonical CCW
   inward half-plane `edge_inward_hp e`, the hp_slack equals the signed
   cross-product  (wx-vx)*(py q-vy) - (wy-vy)*(px q-vx), which is exactly the
   quantity that `edge_cross_sign` (GeneralTriangleParity.v) uses to
   characterise `edge_crosses_ray`.  The identity yields:

     * For inc edges (vy < wy):
         edge_crosses_ray q e  ↔  straddles q e  ∧  hp_slack(edge_inward_hp e) q > 0
     * For dec edges (wy < vy):
         edge_crosses_ray q e  ↔  straddles q e  ∧  hp_slack(edge_inward_hp e) q < 0

   A strictly-interior point has hp_slack > 0 for ALL half-planes →
   inc chain edges that straddle are crossed; dec chain edges that straddle are
   NOT crossed.  Together with a height-band coverage lemma (every y in the
   chain's y-span is straddled by some chain edge) this closes
   `interior_hits_one_chain` for any y-unimodal convex ring whose edge inward
   half-planes are supplied in `hps`.

   §1  `edge_inward_hp` and the hp_slack identity.
   §2  `edge_up_crosses_iff_hp` / `edge_dn_crosses_iff_hp` (algebraic bridge).
   §3  Chain height coverage: `chain_increasing_straddles_y` / dual.
   §4  `interior_hits_inc_chain` / `interior_not_hits_dec_chain`.
   §5  General `interior_hits_one_chain_of_edge_hps`.
   §6  Concrete validations: diamond + hexagon.

   Pure-R + three-axiom.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List Lra Lia.
From NTS.Proofs Require Import Distance Overlay ConvexField PointInRingCorrect
                               MonotoneChainParity MonotoneChainConstruction
                               ConvexChainSplit GeneralTriangleParity.

Import ListNotations.
Local Open Scope R_scope.

(* Default point (used as 'hd'/'last' default argument).  Exported (not Local)
   so downstream files reusing the straddle lemmas share the same constant. *)
Definition dpt : Point := mkPoint 0 0.

(* -------------------------------------------------------------------------- *)
(* §1  Canonical CCW inward half-plane of an edge.                            *)
(* -------------------------------------------------------------------------- *)

(* For CCW edge (a→b), the inward half-plane has positive slack iff q is
   strictly to the LEFT of the edge direction, i.e., strictly inside the
   CCW polygon.

   Convention: hp_slack (A,B,C) q = C - A*px q - B*py q.
   Here A = py b - py a, B = px a - px b, C = px a * py b - px b * py a.
   For an inc edge (py a < py b), A > 0 and hp_slack > 0 ↔ interior.
   For a dec edge (py a > py b), A < 0 and hp_slack > 0 ↔ also interior.  *)
Definition edge_inward_hp (e : Edge) : R * R * R :=
  let '(a, b) := e in
  (py b - py a, px a - px b, px a * py b - px b * py a).

(* -------------------------------------------------------------------------- *)
(* §2  Algebraic bridge: hp_slack = signed cross-product = edge_cross_sign.   *)
(* -------------------------------------------------------------------------- *)

(* hp_slack of the inward half-plane equals the signed cross-product used by
   edge_cross_sign; the proof is pure ring arithmetic. *)
Lemma hp_slack_edge_inward_cross_product : forall (vx vy wx wy : R) (q : Point),
  hp_slack (edge_inward_hp (mkPoint vx vy, mkPoint wx wy)) q =
  (wx - vx) * (py q - vy) - (wy - vy) * (px q - vx).
Proof.
  intros vx vy wx wy q.
  unfold edge_inward_hp, hp_slack. cbn [px py fst snd]. ring.
Qed.

(* For a strictly-upward edge: edge_crosses_ray ↔ y-straddles AND hp_slack > 0. *)
Lemma edge_up_crosses_iff_hp : forall (vx vy wx wy : R) (q : Point),
  vy < wy ->
  edge_crosses_ray q (mkPoint vx vy, mkPoint wx wy) <->
  (vy < py q < wy /\ 0 < hp_slack (edge_inward_hp (mkPoint vx vy, mkPoint wx wy)) q).
Proof.
  intros vx vy wx wy q Hup.
  rewrite (edge_cross_sign vx vy wx wy q).
  rewrite hp_slack_edge_inward_cross_product.
  split.
  - intros [[Hy Hc] | [Hy _]]; [ split; lra | lra ].
  - intros [Hy Hs]. left. lra.
Qed.

(* For a strictly-downward edge: edge_crosses_ray ↔ y-straddles AND hp_slack < 0. *)
Lemma edge_dn_crosses_iff_hp : forall (vx vy wx wy : R) (q : Point),
  wy < vy ->
  edge_crosses_ray q (mkPoint vx vy, mkPoint wx wy) <->
  (wy < py q < vy /\ hp_slack (edge_inward_hp (mkPoint vx vy, mkPoint wx wy)) q < 0).
Proof.
  intros vx vy wx wy q Hdn.
  rewrite (edge_cross_sign vx vy wx wy q).
  rewrite hp_slack_edge_inward_cross_product.
  split.
  - intros [[Hy _] | [Hy Hc]]; [ lra | split; lra ].
  - intros [Hy Hs]. right. lra.
Qed.

(* For an upward edge with hp_slack > 0 AND y-straddle: the ray IS crossed. *)
Lemma edge_up_straddle_hp_pos_crosses :
  forall (e : Edge) (q : Point),
    edge_up e ->
    straddles q e ->
    0 < hp_slack (edge_inward_hp e) q ->
    edge_crosses_ray q e.
Proof.
  intros [a b] q Hup Hstr Hpos.
  destruct a as [vx vy]. destruct b as [wx wy].
  unfold edge_up in Hup. cbn [fst snd px py] in *.
  apply (edge_up_crosses_iff_hp vx vy wx wy q Hup).
  split.
  - unfold straddles in Hstr. cbn [fst snd px py] in Hstr.
    destruct Hstr as [[H1 H2] | [H1 H2]]; lra.
  - exact Hpos.
Qed.

(* For a downward edge with hp_slack > 0: the ray is NOT crossed. *)
Lemma edge_dn_hp_pos_not_crosses :
  forall (e : Edge) (q : Point),
    edge_dn e ->
    0 < hp_slack (edge_inward_hp e) q ->
    ~ edge_crosses_ray q e.
Proof.
  intros [a b] q Hdn Hpos Hcr.
  destruct a as [vx vy]. destruct b as [wx wy].
  unfold edge_dn in Hdn. cbn [fst snd px py] in *.
  apply (edge_dn_crosses_iff_hp vx vy wx wy q Hdn) in Hcr.
  destruct Hcr as [_ Hneg].
  lra.
Qed.

(* Key: for an upward edge (a→b), hp_slack > 0 at height py b gives px q < px b.
   This is used to derive that interior-point height avoids vertex heights via
   `ray_avoids_vertices`. *)
Lemma edge_up_snd_hp_pos_x_bound :
  forall (vx vy wx wy : R) (hps : list (R*R*R)) (q : Point),
    vy < wy ->
    In (edge_inward_hp (mkPoint vx vy, mkPoint wx wy)) hps ->
    0 < conv_min hps q ->
    py q = wy ->
    px q < wx.
Proof.
  intros vx vy wx wy hps q Hup Hin Hpos Heq.
  apply conv_min_pos_iff in Hpos.
  rewrite Forall_forall in Hpos. specialize (Hpos _ Hin).
  rewrite hp_slack_edge_inward_cross_product in Hpos.
  rewrite Heq in Hpos. nra.
Qed.

(* For an upward edge (a→b) whose inward hp is in hps, an interior point q
   (conv_min > 0) satisfies py q ≠ py b whenever b is in outer and the ray
   avoids outer's vertices. *)
Lemma edge_up_snd_neq_py :
  forall (vx vy wx wy : R) (hps : list (R*R*R)) (outer : Ring) (q : Point),
    vy < wy ->
    In (edge_inward_hp (mkPoint vx vy, mkPoint wx wy)) hps ->
    0 < conv_min hps q ->
    In (mkPoint wx wy) outer ->
    ray_avoids_vertices q outer ->
    py q <> wy.
Proof.
  intros vx vy wx wy hps outer q Hup Hin Hpos Hv Hrav Heq.
  pose proof (edge_up_snd_hp_pos_x_bound vx vy wx wy hps q Hup Hin Hpos Heq) as Hx.
  apply (Hrav (mkPoint wx wy) Hv).
  split; [ cbn [py]; lra | cbn [px]; lra ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Chain height coverage.                                                  *)
(* -------------------------------------------------------------------------- *)

(* Every height strictly inside the y-span of a y-strictly-increasing vertex
   list is straddled by some edge of the chain, provided the height avoids all
   vertex y-values. *)
Lemma chain_increasing_straddles_y : forall (l : list Point) (q : Point),
  y_strict_incr l ->
  (2 <= length l)%nat ->
  py (hd dpt l) < py q ->
  py q < py (last l dpt) ->
  (forall v, In v l -> py v <> py q) ->
  exists e, In e (ring_edges l) /\ straddles q e.
Proof.
  induction l as [| a l' IH]; intros q Hinc Hlen Hlo Hhi Hav.
  - simpl in Hlen. lia.
  - destruct l' as [| b rest].
    + simpl in Hlen. lia.
    + destruct Hinc as [Hab Hrest].
      destruct rest as [| c rest'].
      * (* l = [a; b]: last = b, Hhi : py q < py b *)
        exists (a, b). split.
        -- rewrite ring_edges_cons2. simpl ring_edges. left. reflexivity.
        -- unfold straddles. cbn [fst snd]. left.
           split; [ exact Hlo | simpl in Hhi; exact Hhi ].
      * (* l = a :: b :: c :: rest' *)
        destruct (Rlt_dec (py q) (py b)) as [Hlt | Hge].
        -- (* straddles q (a,b) *)
           exists (a, b). split.
           ++ rewrite ring_edges_cons2. left. reflexivity.
           ++ unfold straddles. cbn [fst snd].
              left. split; [ exact Hlo | exact Hlt ].
        -- (* py q >= py b; use IH on (b :: c :: rest') *)
           assert (Hbq : py b < py q).
           { assert (Hne : py b <> py q) by (apply Hav; right; left; reflexivity).
             lra. }
           assert (Hlen2 : (2 <= length (b :: c :: rest'))%nat) by (simpl; lia).
           assert (Hav2 : forall v, In v (b :: c :: rest') -> py v <> py q).
           { intros v Hv. apply Hav. right; exact Hv. }
           destruct (IH q Hrest Hlen2 Hbq Hhi Hav2) as [e [Hin Hstr]].
           exists e. split.
           ++ rewrite ring_edges_cons2. right. exact Hin.
           ++ exact Hstr.
Qed.

(* Dual for decreasing chains. *)
Lemma chain_decreasing_straddles_y : forall (l : list Point) (q : Point),
  y_strict_decr l ->
  (2 <= length l)%nat ->
  py (last l dpt) < py q ->
  py q < py (hd dpt l) ->
  (forall v, In v l -> py v <> py q) ->
  exists e, In e (ring_edges l) /\ straddles q e.
Proof.
  induction l as [| a l' IH]; intros q Hdec Hlen Hlo Hhi Hav.
  - simpl in Hlen. lia.
  - destruct l' as [| b rest].
    + simpl in Hlen. lia.
    + destruct Hdec as [Hab Hrest].
      destruct rest as [| c rest'].
      * (* l = [a; b]: last = b, Hlo : py b < py q *)
        exists (a, b). split.
        -- rewrite ring_edges_cons2. simpl ring_edges. left. reflexivity.
        -- unfold straddles. cbn [fst snd]. right.
           split; [ simpl in Hlo; exact Hlo | exact Hhi ].
      * (* l = a :: b :: c :: rest' *)
        destruct (Rlt_dec (py b) (py q)) as [Hlt | Hge].
        -- (* straddles q (a,b) in dec case: py b < py q < py a *)
           exists (a, b). split.
           ++ rewrite ring_edges_cons2. left. reflexivity.
           ++ unfold straddles. cbn [fst snd].
              right. split; [ exact Hlt | exact Hhi ].
        -- (* py q <= py b; use IH on (b :: c :: rest') *)
           assert (Hbq : py q < py b).
           { assert (Hne : py b <> py q) by (apply Hav; right; left; reflexivity).
             lra. }
           assert (Hlen2 : (2 <= length (b :: c :: rest'))%nat) by (simpl; lia).
           assert (Hav2 : forall v, In v (b :: c :: rest') -> py v <> py q).
           { intros v Hv. apply Hav. right; exact Hv. }
           destruct (IH q Hrest Hlen2 Hlo Hbq Hav2) as [e [Hin Hstr]].
           exists e. split.
           ++ rewrite ring_edges_cons2. right. exact Hin.
           ++ exact Hstr.
Qed.

(* If v ∈ l then v is the snd-coordinate of some edge in ring_edges (a :: l).
   The induction quantifies over the head vertex a so the IH is strong enough. *)
Lemma in_tail_in_ring_edges_snd : forall (l : list Point) (a v : Point),
  In v l ->
  exists e, In e (ring_edges (a :: l)) /\ snd e = v.
Proof.
  induction l as [| b rest IH]; intros a v Hv.
  - inversion Hv.
  - simpl in Hv. destruct Hv as [<- | Hv'].
    + exists (a, b). split.
      * rewrite ring_edges_cons2. left. reflexivity.
      * reflexivity.
    + destruct rest as [| c rest'].
      * inversion Hv'.
      * destruct (IH b v Hv') as [e [HeIn HeSnd]].
        exists e. split.
        -- rewrite ring_edges_cons2. right. exact HeIn.
        -- exact HeSnd.
Qed.

(* For an inc chain (ring_edges l), every snd-vertex of each edge satisfies
   py ≠ py q, given the edge's hp is in hps, conv_min > 0, and ray_avoids. *)
Lemma inc_chain_snd_vertex_avoidance :
  forall (l : list Point) (hps : list (R*R*R)) (outer : Ring) (q : Point),
    y_strict_incr l ->
    Forall (fun e => In (edge_inward_hp e) hps) (ring_edges l) ->
    (forall v, In v l -> In v outer) ->
    0 < conv_min hps q ->
    ray_avoids_vertices q outer ->
    forall e, In e (ring_edges l) -> py (snd e) <> py q.
Proof.
  intros l hps outer q Hinc HF Hvout Hpos Hrav.
  induction l as [| a [| b rest] IH]; intros e Hin.
  - inversion Hin.
  - inversion Hin.
  - rewrite ring_edges_cons2 in Hin.
    rewrite ring_edges_cons2 in HF.
    rewrite Forall_cons_iff in HF. destruct HF as [Hhp HFrest].
    destruct Hin as [<- | Hin].
    + (* e = (a, b): snd e = b *)
      cbn [snd]. destruct b as [wx wy]. cbn [px py].
      destruct Hinc as [Hab Hrest].
      destruct a as [vx vy]. cbn [px py] in Hab.
      intro Heq. symmetry in Heq. revert Heq.
      apply (edge_up_snd_neq_py vx vy wx wy hps outer q Hab).
      * exact Hhp.
      * exact Hpos.
      * apply Hvout. right; left; reflexivity.
      * exact Hrav.
    + (* e in ring_edges (b :: rest) *)
      destruct Hinc as [_ Hrest].
      apply IH.
      * exact Hrest.
      * exact HFrest.
      * intros v Hv. apply Hvout. right; exact Hv.
      * exact Hin.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Interior hits inc chain; interior avoids dec chain.                    *)
(* -------------------------------------------------------------------------- *)

(* Helper: any hp in the list with a positive conv_min has positive hp_slack. *)
Lemma conv_min_in_pos : forall (hps : list (R*R*R)) (hp : R*R*R) (q : Point),
  In hp hps ->
  0 < conv_min hps q ->
  0 < hp_slack hp q.
Proof.
  intros hps hp q Hin Hpos.
  apply conv_min_pos_iff in Hpos.
  rewrite Forall_forall in Hpos.
  exact (Hpos hp Hin).
Qed.

(* An interior point hits the increasing chain: there exists an inc chain edge
   that its rightward ray crosses. *)
Lemma interior_hits_inc_chain :
  forall (l : list Point) (hps : list (R*R*R)) (outer : Ring) (q : Point),
    y_strict_incr l ->
    (2 <= length l)%nat ->
    py (hd dpt l) < py q ->
    py q < py (last l dpt) ->
    Forall (fun e => In (edge_inward_hp e) hps) (ring_edges l) ->
    (forall v, In v l -> In v outer) ->
    0 < conv_min hps q ->
    ray_avoids_vertices q outer ->
    chain_crossed q (ring_edges l).
Proof.
  intros l hps outer q Hinc Hlen Hlo Hhi HF Hvout Hpos Hrav.
  (* Step 1: vertex height avoidance for intermediate vertices (snd of edges). *)
  pose proof (inc_chain_snd_vertex_avoidance l hps outer q Hinc HF Hvout Hpos Hrav)
    as Hsnd_avoids.
  (* Step 2: derive full vertex avoidance for all elements of l. *)
  assert (Hav : forall v, In v l -> py v <> py q).
  { intros v Hv.
    destruct l as [| a l']. { inversion Hv. }
    simpl in Hv. destruct Hv as [<- | Hv'].
    - (* v = hd l: py (hd l) < py q from Hlo *)
      simpl in Hlo. lra.
    - (* v ∈ l': v is snd of some edge in ring_edges (a :: l') *)
      destruct (in_tail_in_ring_edges_snd l' a v Hv') as [e [HeIn HeSnd]].
      rewrite <- HeSnd.
      exact (Hsnd_avoids e HeIn). }
  (* Step 3: apply the coverage lemma. *)
  destruct (chain_increasing_straddles_y l q Hinc Hlen Hlo Hhi Hav) as [e [Hin Hstr]].
  (* Step 4: show the found edge crosses. *)
  exists e. split; [ exact Hin | ].
  pose proof (chain_increasing_of_y_strict_incr _ Hinc) as Hcinc.
  pose proof (chain_increasing_all_up _ Hcinc) as Hallup.
  rewrite Forall_forall in Hallup.
  pose proof (Hallup e Hin) as Hup.
  rewrite Forall_forall in HF.
  pose proof (HF e Hin) as HhpIn.
  pose proof (conv_min_in_pos hps (edge_inward_hp e) q HhpIn Hpos) as Hslack.
  exact (edge_up_straddle_hp_pos_crosses e q Hup Hstr Hslack).
Qed.

(* An interior point does NOT hit the decreasing chain. *)
Lemma interior_not_hits_dec_chain :
  forall (l : list Point) (hps : list (R*R*R)) (q : Point),
    y_strict_decr l ->
    Forall (fun e => In (edge_inward_hp e) hps) (ring_edges l) ->
    0 < conv_min hps q ->
    ~ chain_crossed q (ring_edges l).
Proof.
  intros l hps q Hdec HForall Hpos [e [Hin Hcr]].
  pose proof (chain_decreasing_of_y_strict_decr _ Hdec) as Hcdec.
  pose proof (chain_decreasing_all_dn _ Hcdec) as Halldn.
  rewrite Forall_forall in Halldn.
  pose proof (Halldn e Hin) as Hdn.
  rewrite Forall_forall in HForall.
  pose proof (HForall e Hin) as HhpIn.
  pose proof (conv_min_in_pos hps (edge_inward_hp e) q HhpIn Hpos) as Hslack.
  exact (edge_dn_hp_pos_not_crosses e q Hdn Hslack Hcr).
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  General `interior_hits_one_chain_of_edge_hps`.                         *)
(* -------------------------------------------------------------------------- *)

Theorem interior_hits_one_chain_of_edge_hps :
  forall (up down : list Point) (apex bottom : Point)
         (hps : list (R*R*R)) (q : Point) (outer : Ring),
    let inc := ring_edges (up ++ [apex]) in
    let dec := ring_edges (apex :: down) in
    y_strict_incr (up ++ [apex]) ->
    y_strict_decr (apex :: down) ->
    Forall (fun e => In (edge_inward_hp e) hps) inc ->
    Forall (fun e => In (edge_inward_hp e) hps) dec ->
    py (hd dpt (up ++ [apex])) = py bottom ->
    py bottom < py q < py apex ->
    last (up ++ [apex]) dpt = apex ->
    outer = up ++ apex :: down ->
    (forall v, In v (up ++ [apex]) -> In v outer) ->
    0 < conv_min hps q ->
    ray_avoids_vertices q outer ->
    (chain_crossed q inc /\ ~ chain_crossed q dec).
Proof.
  intros up down apex bottom hps q outer inc dec Hinc Hdec HFInc HFDec
         Hhd Hspan Hlast Houter Hvout Hpos Hrav.
  split.
  - (* chain_crossed q inc *)
    apply (interior_hits_inc_chain (up ++ [apex]) hps outer q Hinc).
    + (* length >= 2: need up non-empty, which follows from py bottom < py apex *)
      rewrite length_app. simpl.
      destruct up as [| x up'].
      * (* up = []: hd dpt [apex] = apex, so py bottom = py apex, contradicts Hspan *)
        simpl in Hhd. rewrite Hhd in Hspan. lra.
      * simpl. lia.
    + (* py (hd dpt (up ++ [apex])) < py q *)
      rewrite Hhd. lra.
    + (* py q < py (last (up ++ [apex]) dpt) = py apex *)
      rewrite Hlast. lra.
    + exact HFInc.
    + exact Hvout.
    + exact Hpos.
    + exact Hrav.
  - (* ~ chain_crossed q dec *)
    exact (interior_not_hits_dec_chain (apex :: down) hps q Hdec HFDec Hpos).
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Concrete validations: diamond + hexagon.                               *)
(* -------------------------------------------------------------------------- *)

(* §6a: Diamond — interior chain hit via the general theorem. *)

Definition diamond_edge_hps : list (R*R*R) :=
  [ edge_inward_hp (mkPoint 0 (-2), mkPoint 2 0)
  ; edge_inward_hp (mkPoint 2 0,    mkPoint 0 2)
  ; edge_inward_hp (mkPoint 0 2,    mkPoint (-2) 0)
  ; edge_inward_hp (mkPoint (-2) 0, mkPoint 0 (-2))
  ].

Lemma diamond_inc_hps_in :
  Forall (fun e => In (edge_inward_hp e) diamond_edge_hps) diamond_inc.
Proof.
  unfold diamond_inc, diamond_edge_hps.
  apply Forall_cons. { apply in_eq. }
  apply Forall_cons. { apply in_cons. apply in_eq. }
  apply Forall_nil.
Qed.

Lemma diamond_dec_hps_in :
  Forall (fun e => In (edge_inward_hp e) diamond_edge_hps) diamond_dec.
Proof.
  unfold diamond_dec, diamond_edge_hps.
  apply Forall_cons. { do 2 apply in_cons. apply in_eq. }
  apply Forall_cons. { do 3 apply in_cons. apply in_eq. }
  apply Forall_nil.
Qed.

Lemma diamond_interior_chain_hit :
  forall q : Point,
    0 < conv_min diamond_edge_hps q ->
    ray_avoids_vertices q diamond_ring ->
    -2 < py q < 2 ->
    chain_crossed q diamond_inc /\
    ~ chain_crossed q diamond_dec.
Proof.
  intros q Hpos Hrav Hspan.
  apply (interior_hits_one_chain_of_edge_hps
           [mkPoint 0 (-2); mkPoint 2 0]
           [mkPoint (-2) 0; mkPoint 0 (-2)]
           (mkPoint 0 2)
           (mkPoint 0 (-2))
           diamond_edge_hps
           q
           diamond_ring).
  - cbn [y_strict_incr app py]. repeat split; lra.
  - cbn [y_strict_decr py]. repeat split; lra.
  - apply diamond_inc_hps_in.
  - apply diamond_dec_hps_in.
  - reflexivity.
  - simpl. lra.
  - rewrite last_last. reflexivity.
  - reflexivity.
  - intros v Hv. unfold diamond_ring. cbn [app In].
    rewrite in_app_iff in Hv. cbn [In] in Hv.
    destruct Hv as [[<- | [<- | []]] | [<- | []]]; cbn [In]; auto.
  - exact Hpos.
  - exact Hrav.
Qed.

(* §6b: Hexagon — interior chain hit via the general theorem. *)

Definition hexagon_edge_hps : list (R*R*R) :=
  [ edge_inward_hp (mkPoint 0 (-3),   mkPoint 3 (-1))
  ; edge_inward_hp (mkPoint 3 (-1),   mkPoint 4 2)
  ; edge_inward_hp (mkPoint 4 2,      mkPoint 1 3)
  ; edge_inward_hp (mkPoint 1 3,      mkPoint (-2) 1)
  ; edge_inward_hp (mkPoint (-2) 1,   mkPoint (-3) (-2))
  ; edge_inward_hp (mkPoint (-3) (-2), mkPoint 0 (-3))
  ].

Lemma hexagon_inc_hps_in :
  Forall (fun e => In (edge_inward_hp e) hexagon_edge_hps) hexagon_inc.
Proof.
  unfold hexagon_inc, hexagon_edge_hps.
  repeat (rewrite ring_edges_cons2 || simpl ring_edges).
  apply Forall_cons. { apply in_eq. }
  apply Forall_cons. { do 1 apply in_cons; apply in_eq. }
  apply Forall_cons. { do 2 apply in_cons; apply in_eq. }
  apply Forall_nil.
Qed.

Lemma hexagon_dec_hps_in :
  Forall (fun e => In (edge_inward_hp e) hexagon_edge_hps) hexagon_dec.
Proof.
  unfold hexagon_dec, hexagon_edge_hps.
  repeat (rewrite ring_edges_cons2 || simpl ring_edges).
  apply Forall_cons. { do 3 apply in_cons; apply in_eq. }
  apply Forall_cons. { do 4 apply in_cons; apply in_eq. }
  apply Forall_cons. { do 5 apply in_cons; apply in_eq. }
  apply Forall_nil.
Qed.

Lemma hexagon_interior_chain_hit :
  forall q : Point,
    0 < conv_min hexagon_edge_hps q ->
    ray_avoids_vertices q hexagon_ring ->
    -3 < py q < 3 ->
    chain_crossed q hexagon_inc /\ ~ chain_crossed q hexagon_dec.
Proof.
  intros q Hpos Hrav Hspan.
  apply (interior_hits_one_chain_of_edge_hps
           [mkPoint 0 (-3); mkPoint 3 (-1); mkPoint 4 2]
           [mkPoint (-2) 1; mkPoint (-3) (-2); mkPoint 0 (-3)]
           (mkPoint 1 3)
           (mkPoint 0 (-3))
           hexagon_edge_hps
           q
           hexagon_ring).
  - cbn [y_strict_incr app py]. repeat split; lra.
  - cbn [y_strict_decr py]. repeat split; lra.
  - apply hexagon_inc_hps_in.
  - apply hexagon_dec_hps_in.
  - reflexivity.
  - simpl. lra.
  - rewrite last_last. reflexivity.
  - reflexivity.
  - intros v Hv. unfold hexagon_ring. cbn [app In].
    rewrite in_app_iff in Hv. cbn [In] in Hv.
    destruct Hv as [[<- | [<- | [<- | []]]] | [<- | []]]; cbn [In]; auto.
  - exact Hpos.
  - exact Hrav.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions hp_slack_edge_inward_cross_product.
Print Assumptions edge_up_crosses_iff_hp.
Print Assumptions edge_dn_crosses_iff_hp.
Print Assumptions interior_hits_one_chain_of_edge_hps.
Print Assumptions diamond_interior_chain_hit.
Print Assumptions hexagon_interior_chain_hit.
