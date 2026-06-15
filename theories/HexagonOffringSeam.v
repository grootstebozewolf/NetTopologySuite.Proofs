(* ==========================================================================
   HexagonOffringSeam.v

   The convex HEXAGON as the FIFTH total family of the polygonal Jordan-Curve
   off-ring seam -- and the FIRST convex polygon with more than four edges
   (n = 6).  After the rectangle, the general triangle, the right triangle,
   and the diamond (the first convex 4-gon), this is the first demonstration
   that the monotone-chain machinery (rungs 1-5) scales past four edges with
   only an arithmetic per-family check.

   `hexagon_ring` (MonotoneChainConstruction.v) is the CCW 6-gon
   (0,-3),(3,-1),(4,2),(1,3),(-2,1),(-3,-2).  We present it by its six edge
   inward half-planes `hexagon_edge_hps` (MonotoneChainCoverage.v) and
   discharge the six obligations of
   `ConvexOffringSeam.convex_parity_seam_offring_of`:

     1-4 (presentation): zero-set on skeleton, vertices in all half-planes,
         non-degeneracy, bounded positive region (radius 5);
     5 (interior-odd): a strict-interior point's rightward ray crosses the
         right (increasing) chain exactly once -- via RUNG 4
         (`MonotoneChainCoverage.hexagon_interior_chain_hit`) and the already-
         Qed monotone-chain split (`bimonotone_split_parity`);
     6 (exterior-even): an exterior point's ray crosses the two chains both-
         or-neither (even) -- the split again, by a per-band case analysis
         over the six edges, using the generic-position guards.

   The interior-odd obligation is now a near one-liner thanks to rung 4; the
   only family-specific work is the six-edge exterior-even band analysis and
   the arithmetic presentation facts.

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List Lra Lia.
From NTS.Proofs Require Import Distance Overlay ConvexField PointInRingTangents
                               PointInRingCorrect ConvexNesting MonotoneChainParity
                               MonotoneChainConstruction MonotoneChainCoverage
                               ConvexChainSplit ConvexOffringSeam GeneralTriangleParity
                               JordanCurveSeam JCT_OnEdgeCounterexample.

Import ListNotations.
Local Open Scope R_scope.

(* The six hexagon vertices, CCW, bottom vertex first. *)
Local Notation P0 := (mkPoint 0 (-3)).
Local Notation P1 := (mkPoint 3 (-1)).
Local Notation P2 := (mkPoint 4 2).
Local Notation P3 := (mkPoint 1 3).
Local Notation P4 := (mkPoint (-2) 1).
Local Notation P5 := (mkPoint (-3) (-2)).

(* The six edges. g1,g2,g3 are the increasing (right) chain; g4,g5,g6 the
   decreasing (left) chain. *)
Local Notation g1 := (P0, P1).
Local Notation g2 := (P1, P2).
Local Notation g3 := (P2, P3).
Local Notation g4 := (P3, P4).
Local Notation g5 := (P4, P5).
Local Notation g6 := (P5, P0).

(* The presentation: the six edge inward half-planes (from rung 4).  Reduced
   forms of the slacks (hp_slack (edge_inward_hp gK) q):
     slack1 = 9 - 2x + 3y     slack4 = 7 + 2x - 3y
     slack2 = 10 - 3x + y     slack5 = 7 + 3x - y
     slack3 = 10 - x - 3y     slack6 = 9 + x + 3y                          *)

Lemma ring_edges_hexagon :
  ring_edges hexagon_ring = [ g1 ; g2 ; g3 ; g4 ; g5 ; g6 ].
Proof. reflexivity. Qed.

Lemma hexagon_inc_edges : hexagon_inc = [ g1 ; g2 ; g3 ].
Proof. reflexivity. Qed.

Lemma hexagon_dec_edges : hexagon_dec = [ g4 ; g5 ; g6 ].
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Slack expansion tactic: turn `conv_min`/`hp_slack` facts over             *)
(* `hexagon_edge_hps` into linear (in)equalities the `lra`/`nra` engines      *)
(* understand.                                                                *)
(* -------------------------------------------------------------------------- *)

Ltac hex_expand H :=
  apply conv_min_pos_iff in H; unfold hexagon_edge_hps in H;
  repeat (apply Forall_cons_iff in H as [? H]);
  unfold edge_inward_hp, hp_slack in *; cbn [px py fst snd] in *.

(* All six slacks nonnegative => conv_min nonnegative (used as the exterior
   contradiction: an interior-side point cannot have a negative field). *)
Lemma conv_min_le_in : forall hps pt hp,
  In hp hps -> conv_min hps pt <= hp_slack hp pt.
Proof.
  induction hps as [| h rest IH]; intros pt hp Hin; [ contradiction | ].
  simpl. destruct Hin as [<- | Hin].
  - apply Rmin_l.
  - eapply Rle_trans; [ apply Rmin_r | apply IH; exact Hin ].
Qed.

Lemma conv_min_nonneg_Forall : forall hps pt,
  0 <= conv_min hps pt -> Forall (fun hp => 0 <= hp_slack hp pt) hps.
Proof.
  intros hps pt H. apply Forall_forall. intros hp Hin.
  eapply Rle_trans; [ exact H | apply conv_min_le_in; exact Hin ].
Qed.

Lemma conv_min_nonneg : forall hps pt,
  Forall (fun hp => 0 <= hp_slack hp pt) hps -> 0 <= conv_min hps pt.
Proof.
  induction hps as [| h rest IH]; intros pt H; simpl; [ lra | ].
  inversion H as [| ? ? Hh Hrest]; subst.
  pose proof (IH pt Hrest) as Hr.
  unfold Rmin; destruct (Rle_dec (hp_slack h pt) (conv_min rest pt)); lra.
Qed.

Lemma conv_min_zero_inv : forall hps pt,
  conv_min hps pt = 0 ->
  Forall (fun hp => 0 <= hp_slack hp pt) hps /\
  Exists (fun hp => hp_slack hp pt = 0) hps.
Proof.
  induction hps as [| h rest IH]; intros pt H.
  - simpl in H; lra.
  - simpl in H.
    assert (Ha : 0 <= hp_slack h pt) by (pose proof (Rmin_l (hp_slack h pt) (conv_min rest pt)); lra).
    assert (Hb : 0 <= conv_min rest pt) by (pose proof (Rmin_r (hp_slack h pt) (conv_min rest pt)); lra).
    split.
    + apply Forall_cons; [ exact Ha | apply conv_min_nonneg_Forall; exact Hb ].
    + destruct (Rle_lt_dec (hp_slack h pt) (conv_min rest pt)) as [Hle | Hlt].
      * rewrite (Rmin_left _ _ Hle) in H. apply Exists_cons_hd; exact H.
      * rewrite (Rmin_right _ _ (Rlt_le _ _ Hlt)) in H.
        apply Exists_cons_tl. apply (proj2 (IH pt H)).
Qed.

(* Tactic: the exterior contradiction.  Given enough slack-sign hypotheses in
   context to make all six slacks nonnegative, derive `0 <= conv_min` and
   contradict a `conv_min < 0` hypothesis. *)
Ltac hex_nonneg_contra Hext :=
  match type of Hext with
  | conv_min _ ?q < 0 =>
    exfalso;
    assert (Hge : 0 <= conv_min hexagon_edge_hps q) by
      (apply conv_min_nonneg; unfold hexagon_edge_hps;
       repeat (apply Forall_cons); try apply Forall_nil;
       unfold edge_inward_hp, hp_slack; cbn [px py fst snd]; lra);
    lra
  end.

(* -------------------------------------------------------------------------- *)
(* Obligations 2-3: presentation (vertices in half-planes, non-degeneracy).    *)
(* -------------------------------------------------------------------------- *)

Lemma hexagon_vertices_in_hps :
  Forall (vertices_in_halfplane hexagon_ring) hexagon_edge_hps.
Proof.
  unfold hexagon_edge_hps, hexagon_ring.
  repeat (apply Forall_cons); [ | | | | | | apply Forall_nil ];
    intros v Hv; cbn [In] in Hv;
    repeat (destruct Hv as [<- | Hv]); try contradiction;
    unfold edge_inward_hp, hp_slack; cbn [px py fst snd]; lra.
Qed.

Lemma hexagon_hps_nondeg :
  Forall (fun hp : R * R * R => let '(a, b, _) := hp in 0 < a * a + b * b)
         hexagon_edge_hps.
Proof.
  unfold hexagon_edge_hps. repeat (apply Forall_cons); try (apply Forall_nil);
    unfold edge_inward_hp; cbn [px py fst snd]; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Obligation 4: bounded positive region (radius 5).                           *)
(*   The six slacks pin the point into the box [-3,4] x [-3,3], whose corners  *)
(*   are within radius 5 of the origin.                                        *)
(* -------------------------------------------------------------------------- *)

Lemma hexagon_bounded : forall p,
  0 < conv_min hexagon_edge_hps p -> px p * px p + py p * py p <= 5 * 5.
Proof.
  intros p Hpos. hex_expand Hpos.
  (* box bounds: -3 < x < 4, -3 < y < 3 by linear combinations *)
  assert (Hx1 : -3 < px p) by lra.
  assert (Hx2 : px p < 4) by lra.
  assert (Hy1 : -3 < py p) by lra.
  assert (Hy2 : py p < 3) by lra.
  nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Obligation 1: the zero-set of conv_min lies on the hexagon skeleton.        *)
(* -------------------------------------------------------------------------- *)

Lemma hexagon_zero_on_skeleton : forall pt,
  conv_min hexagon_edge_hps pt = 0 -> ring_image hexagon_ring pt.
Proof.
  intros pt H. apply conv_min_zero_inv in H. destruct H as [Hall Hex].
  unfold hexagon_edge_hps in Hall, Hex.
  repeat (apply Forall_cons_iff in Hall as [? Hall]).
  unfold edge_inward_hp, hp_slack in *; cbn [px py fst snd] in *.
  unfold ring_image. rewrite ring_edges_hexagon.
  apply Exists_cons in Hex; destruct Hex as [Hz | Hex].
  { (* slack1 = 0 : edge g1 = (P0,P1) *)
    unfold edge_inward_hp, hp_slack in Hz; cbn [px py fst snd] in Hz.
    exists g1, ((py pt + 3) / 2); cbn [fst snd px py];
      repeat split; ((cbn [In]; tauto) || lra). }
  apply Exists_cons in Hex; destruct Hex as [Hz | Hex].
  { (* slack2 = 0 : edge g2 = (P1,P2) *)
    unfold edge_inward_hp, hp_slack in Hz; cbn [px py fst snd] in Hz.
    exists g2, ((py pt + 1) / 3); cbn [fst snd px py];
      repeat split; ((cbn [In]; tauto) || lra). }
  apply Exists_cons in Hex; destruct Hex as [Hz | Hex].
  { (* slack3 = 0 : edge g3 = (P2,P3) *)
    unfold edge_inward_hp, hp_slack in Hz; cbn [px py fst snd] in Hz.
    exists g3, (py pt - 2); cbn [fst snd px py];
      repeat split; ((cbn [In]; tauto) || lra). }
  apply Exists_cons in Hex; destruct Hex as [Hz | Hex].
  { (* slack4 = 0 : edge g4 = (P3,P4) *)
    unfold edge_inward_hp, hp_slack in Hz; cbn [px py fst snd] in Hz.
    exists g4, ((3 - py pt) / 2); cbn [fst snd px py];
      repeat split; ((cbn [In]; tauto) || lra). }
  apply Exists_cons in Hex; destruct Hex as [Hz | Hex].
  { (* slack5 = 0 : edge g5 = (P4,P5) *)
    unfold edge_inward_hp, hp_slack in Hz; cbn [px py fst snd] in Hz.
    exists g5, ((1 - py pt) / 3); cbn [fst snd px py];
      repeat split; ((cbn [In]; tauto) || lra). }
  apply Exists_cons in Hex; destruct Hex as [Hz | Hex].
  { (* slack6 = 0 : edge g6 = (P5,P0) *)
    unfold edge_inward_hp, hp_slack in Hz; cbn [px py fst snd] in Hz.
    exists g6, (- (py pt + 2)); cbn [fst snd px py];
      repeat split; ((cbn [In]; tauto) || lra). }
  apply Exists_nil in Hex; contradiction.
Qed.

(* -------------------------------------------------------------------------- *)
(* Per-edge crossing in clean (band, slack-sign) form (edge_cross_sign + lra). *)
(* -------------------------------------------------------------------------- *)

Lemma g1_cross_iff : forall p,
  edge_crosses_ray p g1 <-> (-3 < py p < -1 /\ 2 * px p < 3 * py p + 9).
Proof.
  intro p. rewrite (edge_cross_sign 0 (-3) 3 (-1) p). cbn [px py]. split.
  - intros [[Hy Hc] | [Hy Hc]]; lra.
  - intros [Hy Hx]. left. lra.
Qed.

Lemma g2_cross_iff : forall p,
  edge_crosses_ray p g2 <-> (-1 < py p < 2 /\ 3 * px p < py p + 10).
Proof.
  intro p. rewrite (edge_cross_sign 3 (-1) 4 2 p). cbn [px py]. split.
  - intros [[Hy Hc] | [Hy Hc]]; lra.
  - intros [Hy Hx]. left. lra.
Qed.

Lemma g3_cross_iff : forall p,
  edge_crosses_ray p g3 <-> (2 < py p < 3 /\ px p < 10 - 3 * py p).
Proof.
  intro p. rewrite (edge_cross_sign 4 2 1 3 p). cbn [px py]. split.
  - intros [[Hy Hc] | [Hy Hc]]; lra.
  - intros [Hy Hx]. left. lra.
Qed.

Lemma g4_cross_iff : forall p,
  edge_crosses_ray p g4 <-> (1 < py p < 3 /\ 7 + 2 * px p - 3 * py p < 0).
Proof.
  intro p. rewrite (edge_cross_sign 1 3 (-2) 1 p). cbn [px py]. split.
  - intros [[Hy Hc] | [Hy Hc]]; lra.
  - intros [Hy Hx]. right. lra.
Qed.

Lemma g5_cross_iff : forall p,
  edge_crosses_ray p g5 <-> (-2 < py p < 1 /\ 7 + 3 * px p - py p < 0).
Proof.
  intro p. rewrite (edge_cross_sign (-2) 1 (-3) (-2) p). cbn [px py]. split.
  - intros [[Hy Hc] | [Hy Hc]]; lra.
  - intros [Hy Hx]. right. lra.
Qed.

Lemma g6_cross_iff : forall p,
  edge_crosses_ray p g6 <-> (-3 < py p < -2 /\ 9 + px p + 3 * py p < 0).
Proof.
  intro p. rewrite (edge_cross_sign (-3) (-2) 0 (-3) p). cbn [px py]. split.
  - intros [[Hy Hc] | [Hy Hc]]; lra.
  - intros [Hy Hx]. right. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Obligation 5: interior-odd parity, via RUNG 4 + the split.                  *)
(* -------------------------------------------------------------------------- *)

Lemma hexagon_convex_interior_parity :
  convex_interior_parity hexagon_ring hexagon_edge_hps.
Proof.
  intros q Hpos Hrav Hnh.
  (* derive the y-span -3 < py q < 3 from conv_min > 0 *)
  assert (Hspan : -3 < py q < 3).
  { pose proof Hpos as Hpos'. hex_expand Hpos'. lra. }
  (* rung 4: q crosses the increasing chain once, misses the decreasing one *)
  pose proof (hexagon_interior_chain_hit q Hpos Hrav Hspan) as [Hinc Hdec].
  apply (bimonotone_split_parity hexagon_ring hexagon_inc hexagon_dec q
           hexagon_bimonotone).
  left. exact (conj Hinc Hdec).
Qed.

(* -------------------------------------------------------------------------- *)
(* Obligation 6: exterior-even parity, via the split + per-band analysis.      *)
(* -------------------------------------------------------------------------- *)

(* Helpers to membership in the explicit inc / dec edge lists. *)
Local Ltac in_inc := rewrite hexagon_inc_edges; cbn [In]; tauto.
Local Ltac in_dec := rewrite hexagon_dec_edges; cbn [In]; tauto.

Lemma hexagon_exterior_even : forall p,
  conv_min hexagon_edge_hps p < 0 ->
  ray_avoids_vertices p hexagon_ring ->
  no_horizontal_edge_at p hexagon_ring ->
  ~ point_in_ring p hexagon_ring.
Proof.
  intros q Hext Hrav Hnh Hpir.
  (* guard facts at the four span-interior vertex heights *)
  assert (GP1 : py q = -1 -> 3 < px q).
  { intro Hy. destruct (Rlt_le_dec 3 (px q)) as [|Hle]; [ assumption | exfalso ].
    apply (Hrav P1); [ unfold hexagon_ring; cbn [In]; tauto | cbn [px py]; lra ]. }
  assert (GP2 : py q = 2 -> 4 < px q).
  { intro Hy. destruct (Rlt_le_dec 4 (px q)) as [|Hle]; [ assumption | exfalso ].
    apply (Hrav P2); [ unfold hexagon_ring; cbn [In]; tauto | cbn [px py]; lra ]. }
  assert (GP4 : py q = 1 -> -2 < px q).
  { intro Hy. destruct (Rlt_le_dec (-2) (px q)) as [|Hle]; [ assumption | exfalso ].
    apply (Hrav P4); [ unfold hexagon_ring; cbn [In]; tauto | cbn [px py]; lra ]. }
  assert (GP5 : py q = -2 -> -3 < px q).
  { intro Hy. destruct (Rlt_le_dec (-3) (px q)) as [|Hle]; [ assumption | exfalso ].
    apply (Hrav P5); [ unfold hexagon_ring; cbn [In]; tauto | cbn [px py]; lra ]. }
  (* the XOR from the bimonotone split *)
  pose proof (proj1 (bimonotone_split_parity hexagon_ring hexagon_inc hexagon_dec q
                       hexagon_bimonotone) Hpir) as Hxor.
  destruct Hxor as [[Hinc Hdec] | [Hinc Hdec]].
  - (* inc crossed, ~dec : show the field is nonnegative, contradicting Hext *)
    destruct Hinc as [e [Hin Hcr]]. rewrite hexagon_inc_edges in Hin.
    cbn [In] in Hin. destruct Hin as [He | [He | [He | []]]]; subst e.
    + (* g1 crossed: band (-3,-1), slack1>0 *)
      apply g1_cross_iff in Hcr. destruct Hcr as [Hband Hs1].
      destruct (total_order_T (py q) (-2)) as [[Hlt | Heq] | Hgt].
      * (* y in (-3,-2): g6 straddles; ~dec gives slack6 >= 0 *)
        assert (Hs6 : 0 <= 9 + px q + 3 * py q).
        { destruct (Rle_lt_dec 0 (9 + px q + 3 * py q)) as [|Hb]; [ assumption | ].
          exfalso. apply Hdec. exists g6. split; [ in_dec | ].
          apply (proj2 (g6_cross_iff q)). split; lra. }
        hex_nonneg_contra Hext.
      * (* y = -2: vertex P5 height; guard gives px q > -3 *)
        pose proof (GP5 Heq) as Hpx. hex_nonneg_contra Hext.
      * (* y in (-2,-1): g5 straddles; ~dec gives slack5 >= 0 *)
        assert (Hs5 : 0 <= 7 + 3 * px q - py q).
        { destruct (Rle_lt_dec 0 (7 + 3 * px q - py q)) as [|Hb]; [ assumption | ].
          exfalso. apply Hdec. exists g5. split; [ in_dec | ].
          apply (proj2 (g5_cross_iff q)). split; lra. }
        hex_nonneg_contra Hext.
    + (* g2 crossed: band (-1,2), slack2>0 *)
      apply g2_cross_iff in Hcr. destruct Hcr as [Hband Hs2].
      destruct (total_order_T (py q) 1) as [[Hlt | Heq] | Hgt].
      * (* y in (-1,1): g5 straddles; ~dec gives slack5 >= 0 *)
        assert (Hs5 : 0 <= 7 + 3 * px q - py q).
        { destruct (Rle_lt_dec 0 (7 + 3 * px q - py q)) as [|Hb]; [ assumption | ].
          exfalso. apply Hdec. exists g5. split; [ in_dec | ].
          apply (proj2 (g5_cross_iff q)). split; lra. }
        hex_nonneg_contra Hext.
      * (* y = 1: vertex P4 height; guard gives px q > -2 *)
        pose proof (GP4 Heq) as Hpx. hex_nonneg_contra Hext.
      * (* y in (1,2): g4 straddles; ~dec gives slack4 >= 0 *)
        assert (Hs4 : 0 <= 7 + 2 * px q - 3 * py q).
        { destruct (Rle_lt_dec 0 (7 + 2 * px q - 3 * py q)) as [|Hb]; [ assumption | ].
          exfalso. apply Hdec. exists g4. split; [ in_dec | ].
          apply (proj2 (g4_cross_iff q)). split; lra. }
        hex_nonneg_contra Hext.
    + (* g3 crossed: band (2,3), slack3>0; g4 straddles all of (2,3) *)
      apply g3_cross_iff in Hcr. destruct Hcr as [Hband Hs3].
      assert (Hs4 : 0 <= 7 + 2 * px q - 3 * py q).
      { destruct (Rle_lt_dec 0 (7 + 2 * px q - 3 * py q)) as [|Hb]; [ assumption | ].
        exfalso. apply Hdec. exists g4. split; [ in_dec | ].
        apply (proj2 (g4_cross_iff q)). split; lra. }
      hex_nonneg_contra Hext.
  - (* ~inc, dec crossed : the straddling inc edge has slack <= 0, which with
       the crossed dec edge's slack < 0 is geometrically impossible (lra). *)
    destruct Hdec as [e [Hin Hcr]]. rewrite hexagon_dec_edges in Hin.
    cbn [In] in Hin. destruct Hin as [He | [He | [He | []]]]; subst e.
    + (* g4 crossed: band (1,3), slack4<0 *)
      apply g4_cross_iff in Hcr. destruct Hcr as [Hband Hs4].
      destruct (total_order_T (py q) 2) as [[Hlt | Heq] | Hgt].
      * (* y in (1,2): g2 straddles; ~inc gives slack2 <= 0 *)
        assert (Hs2 : py q + 10 <= 3 * px q).
        { destruct (Rle_lt_dec (3 * px q) (py q + 10)) as [Hb | ]; [ | lra ].
          exfalso. apply Hinc. exists g2. split; [ in_inc | ].
          apply (proj2 (g2_cross_iff q)). split; lra. }
        lra.
      * (* y = 2: vertex P2 height; guard gives px q > 4 *)
        pose proof (GP2 Heq) as Hpx. lra.
      * (* y in (2,3): g3 straddles; ~inc gives slack3 <= 0 *)
        assert (Hs3 : 10 - 3 * py q <= px q).
        { destruct (Rle_lt_dec (px q) (10 - 3 * py q)) as [Hb | ]; [ | lra ].
          exfalso. apply Hinc. exists g3. split; [ in_inc | ].
          apply (proj2 (g3_cross_iff q)). split; lra. }
        lra.
    + (* g5 crossed: band (-2,1), slack5<0 *)
      apply g5_cross_iff in Hcr. destruct Hcr as [Hband Hs5].
      destruct (total_order_T (py q) (-1)) as [[Hlt | Heq] | Hgt].
      * (* y in (-2,-1): g1 straddles; ~inc gives slack1 <= 0 *)
        assert (Hs1 : 3 * py q + 9 <= 2 * px q).
        { destruct (Rle_lt_dec (2 * px q) (3 * py q + 9)) as [Hb | ]; [ | lra ].
          exfalso. apply Hinc. exists g1. split; [ in_inc | ].
          apply (proj2 (g1_cross_iff q)). split; lra. }
        lra.
      * (* y = -1: vertex P1 height; guard gives px q > 3 *)
        pose proof (GP1 Heq) as Hpx. lra.
      * (* y in (-1,1): g2 straddles; ~inc gives slack2 <= 0 *)
        assert (Hs2 : py q + 10 <= 3 * px q).
        { destruct (Rle_lt_dec (3 * px q) (py q + 10)) as [Hb | ]; [ | lra ].
          exfalso. apply Hinc. exists g2. split; [ in_inc | ].
          apply (proj2 (g2_cross_iff q)). split; lra. }
        lra.
    + (* g6 crossed: band (-3,-2), slack6<0; g1 straddles all of (-3,-2) *)
      apply g6_cross_iff in Hcr. destruct Hcr as [Hband Hs6].
      assert (Hs1 : 3 * py q + 9 <= 2 * px q).
      { destruct (Rle_lt_dec (2 * px q) (3 * py q + 9)) as [Hb | ]; [ | lra ].
        exfalso. apply Hinc. exists g1. split; [ in_inc | ].
        apply (proj2 (g1_cross_iff q)). split; lra. }
      lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* HEADLINE: the hexagon is the fifth total off-ring JCT family.               *)
(* -------------------------------------------------------------------------- *)

Theorem hexagon_parity_seam_offring : forall p,
  parity_characterises_interior_cont_offring p hexagon_ring.
Proof.
  intro p.
  apply (convex_parity_seam_offring_of hexagon_ring hexagon_edge_hps p 5).
  - exact hexagon_zero_on_skeleton.
  - exact hexagon_vertices_in_hps.
  - exact hexagon_hps_nondeg.
  - lra.
  - exact hexagon_bounded.
  - intros Hpos Hrav Hnh. exact (hexagon_convex_interior_parity p Hpos Hrav Hnh).
  - intros Hneg Hrav Hnh. exact (hexagon_exterior_even p Hneg Hrav Hnh).
Qed.

(* -------------------------------------------------------------------------- *)
(* Structural facts + the off-ring biconditional corollary.                    *)
(* -------------------------------------------------------------------------- *)

Lemma hexagon_ring_closed : ring_closed hexagon_ring.
Proof.
  exists P0, [ P1 ; P2 ; P3 ; P4 ; P5 ].
  reflexivity.
Qed.

Lemma hexagon_ring_min_points : ring_has_minimum_points hexagon_ring.
Proof. unfold ring_has_minimum_points, hexagon_ring; cbn [length]; lia. Qed.

Lemma hexagon_ring_simple : ring_simple hexagon_ring.
Proof.
  unfold ring_simple. rewrite ring_edges_hexagon.
  intros e1 e2 H1 H2 Hne. cbn [In] in H1, H2.
  destruct H1 as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
  destruct H2 as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
    first
      [ exfalso; apply Hne; reflexivity
      | intros (t & s & Ht & Hs & Hx & Hy); cbn [fst snd px py] in *; nra ].
Qed.

Corollary hexagon_point_in_ring_iff_geometric : forall p,
  ring_complement hexagon_ring p ->
  no_horizontal_edge_at p hexagon_ring ->
  ray_avoids_vertices p hexagon_ring ->
  (point_in_ring p hexagon_ring <-> geometric_interior_cont p hexagon_ring).
Proof.
  intros p Hc Hnh Hrav.
  pose proof (hexagon_parity_seam_offring p hexagon_ring_simple hexagon_ring_closed
                hexagon_ring_min_points Hc Hnh Hrav) as H.
  split; [ apply (proj2 H) | apply (proj1 H) ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions hexagon_parity_seam_offring.
Print Assumptions hexagon_point_in_ring_iff_geometric.
