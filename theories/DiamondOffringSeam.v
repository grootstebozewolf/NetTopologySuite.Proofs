(* ==========================================================================
   DiamondOffringSeam.v

   The DIAMOND as the FOURTH total family of the polygonal Jordan-Curve
   off-ring seam, after the rectangle, the general triangle, and the right
   triangle -- and the FIRST convex polygon with four edges, and the FIRST
   instantiation of the generic convex assembly
   `ConvexOffringSeam.convex_parity_seam_offring_of`.

   `diamond_ring` (ConvexChainSplit.v) is the CCW 4-gon (0,-2),(2,0),(0,2),
   (-2,0) -- the region |x|+|y| <= 2.  We present it by its four edge
   half-planes `diamond_hps` and discharge the six obligations of
   `convex_parity_seam_offring_of`:

     1-4 (presentation): zero-set on skeleton, vertices in all half-planes,
         non-degeneracy, bounded positive region;
     5 (interior-odd): a strict-interior point's rightward ray crosses the
         right (increasing) chain exactly once -- via the already-Qed
         monotone-chain split (`bimonotone_split_parity`) and
         `interior_hits_one_chain`;
     6 (exterior-even): an exterior point's ray crosses the two chains both-
         or-neither (even) -- the split again, by a y-band case analysis.

   The two geometric obligations both route through the Qed monotone-chain
   machinery + `edge_cross_sign`; no new escape/parity machinery is built.
   The guards `ray_avoids_vertices` + `no_horizontal_edge_at` are exactly
   those the assembly demands (and are provably necessary, per the
   vertex-grazing / horizontal-edge counterexamples).

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List Lra Lia.
From NTS.Proofs Require Import Distance Overlay ConvexField PointInRingTangents
                               PointInRingCorrect ConvexNesting MonotoneChainParity
                               ConvexChainSplit ConvexOffringSeam GeneralTriangleParity
                               JordanCurveSeam JCT_OnEdgeCounterexample.

Import ListNotations.
Local Open Scope R_scope.

(* The four inward edge half-planes (a,b,c) with hp_slack = c - (a x + b y). *)
Definition diamond_hps : list (R * R * R) :=
  [ (1, -1, 2)      (* edge (0,-2)->(2,0):  x - y <= 2 *)
  ; (1,  1, 2)      (* edge (2,0)->(0,2):   x + y <= 2 *)
  ; (-1, 1, 2)      (* edge (0,2)->(-2,0): -x + y <= 2 *)
  ; (-1,-1, 2) ].   (* edge (-2,0)->(0,-2):-x - y <= 2 *)

Local Notation ea := (mkPoint 0 (-2), mkPoint 2 0).
Local Notation eb := (mkPoint 2 0,    mkPoint 0 2).
Local Notation ec := (mkPoint 0 2,    mkPoint (-2) 0).
Local Notation ed := (mkPoint (-2) 0, mkPoint 0 (-2)).

Lemma ring_edges_diamond : ring_edges diamond_ring = [ ea ; eb ; ec ; ed ].
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Obligations 2-3: presentation (vertices in half-planes, non-degeneracy).    *)
(* -------------------------------------------------------------------------- *)

Lemma diamond_vertices_in_hps : Forall (vertices_in_halfplane diamond_ring) diamond_hps.
Proof.
  unfold diamond_hps, diamond_ring.
  repeat (apply Forall_cons); [ | | | | apply Forall_nil ];
    intros v Hv; cbn [In] in Hv;
    repeat (destruct Hv as [<- | Hv]); try contradiction;
    unfold hp_slack; cbn [px py]; lra.
Qed.

Lemma diamond_hps_nondeg :
  Forall (fun hp : R * R * R => let '(a, b, _) := hp in 0 < a * a + b * b) diamond_hps.
Proof.
  unfold diamond_hps. repeat (apply Forall_cons); try (apply Forall_nil); lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Small reusable conv_min facts: the min is below each slack; nonneg lifts to  *)
(* every slack; a zero value forces all-nonneg + one-zero.                      *)
(* -------------------------------------------------------------------------- *)

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

(* -------------------------------------------------------------------------- *)
(* Obligation 4: bounded positive region (radius 2).                           *)
(* -------------------------------------------------------------------------- *)

Lemma diamond_bounded : forall p,
  0 < conv_min diamond_hps p -> px p * px p + py p * py p <= 2 * 2.
Proof.
  intros p Hpos. apply conv_min_pos_iff in Hpos. unfold diamond_hps in Hpos.
  repeat (apply Forall_cons_iff in Hpos as [? Hpos]).
  unfold hp_slack in *; cbn [px py] in *. nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Obligation 1: the zero-set of conv_min lies on the diamond skeleton.        *)
(* -------------------------------------------------------------------------- *)

Lemma diamond_zero_on_skeleton : forall pt,
  conv_min diamond_hps pt = 0 -> ring_image diamond_ring pt.
Proof.
  intros pt H. apply conv_min_zero_inv in H. destruct H as [Hall Hex].
  unfold diamond_hps in Hall, Hex.
  (* the four slack-nonneg facts, in context *)
  repeat (apply Forall_cons_iff in Hall as [? Hall]).
  unfold hp_slack in *; cbn [px py] in *.
  unfold ring_image. rewrite ring_edges_diamond.
  apply Exists_cons in Hex; destruct Hex as [Hz | Hex].
  { (* x - y = 2 : edge ea = ((0,-2),(2,0)) *)
    unfold hp_slack in Hz; cbn [px py] in Hz.
    exists ea, ((py pt + 2) / 2); cbn [fst snd px py];
      repeat split; ((cbn [In]; tauto) || lra). }
  apply Exists_cons in Hex; destruct Hex as [Hz | Hex].
  { (* x + y = 2 : edge eb = ((2,0),(0,2)) *)
    unfold hp_slack in Hz; cbn [px py] in Hz.
    exists eb, (py pt / 2); cbn [fst snd px py];
      repeat split; ((cbn [In]; tauto) || lra). }
  apply Exists_cons in Hex; destruct Hex as [Hz | Hex].
  { (* -x + y = 2 : edge ec = ((0,2),(-2,0)) *)
    unfold hp_slack in Hz; cbn [px py] in Hz.
    exists ec, ((2 - py pt) / 2); cbn [fst snd px py];
      repeat split; ((cbn [In]; tauto) || lra). }
  apply Exists_cons in Hex; destruct Hex as [Hz | Hex].
  { (* -x - y = 2 : edge ed = ((-2,0),(0,-2)) *)
    unfold hp_slack in Hz; cbn [px py] in Hz.
    exists ed, ((- py pt) / 2); cbn [fst snd px py];
      repeat split; ((cbn [In]; tauto) || lra). }
  apply Exists_nil in Hex; contradiction.
Qed.

(* -------------------------------------------------------------------------- *)
(* Per-edge crossing in clean x-bound form (edge_cross_sign + lra).            *)
(*   The four edges, with slack abbreviations:                                 *)
(*     ea up   (0,-2)->(2,0):   crosses iff -2<y<0 /\ x < y+2  (slack_a>0)     *)
(*     eb up   (2,0)->(0,2):    crosses iff  0<y<2 /\ x < 2-y  (slack_b>0)     *)
(*     ec down (0,2)->(-2,0):   crosses iff  0<y<2 /\ x < y-2  (slack_c<0)     *)
(*     ed down (-2,0)->(0,-2):  crosses iff -2<y<0 /\ x < -2-y (slack_d<0)     *)
(* -------------------------------------------------------------------------- *)

Lemma ea_cross_iff : forall p,
  edge_crosses_ray p ea <-> (-2 < py p < 0 /\ px p < py p + 2).
Proof.
  intro p. rewrite (edge_cross_sign 0 (-2) 2 0 p). cbn [px py]. split.
  - intros [[Hy Hc] | [Hy Hc]]; lra.
  - intros [Hy Hx]. left. lra.
Qed.

Lemma eb_cross_iff : forall p,
  edge_crosses_ray p eb <-> (0 < py p < 2 /\ px p < 2 - py p).
Proof.
  intro p. rewrite (edge_cross_sign 2 0 0 2 p). cbn [px py]. split.
  - intros [[Hy Hc] | [Hy Hc]]; lra.
  - intros [Hy Hx]. left. lra.
Qed.

Lemma ec_cross_iff : forall p,
  edge_crosses_ray p ec <-> (0 < py p < 2 /\ px p < py p - 2).
Proof.
  intro p. rewrite (edge_cross_sign 0 2 (-2) 0 p). cbn [px py]. split.
  - intros [[Hy Hc] | [Hy Hc]]; lra.
  - intros [Hy Hx]. right. lra.
Qed.

Lemma ed_cross_iff : forall p,
  edge_crosses_ray p ed <-> (-2 < py p < 0 /\ px p < -2 - py p).
Proof.
  intro p. rewrite (edge_cross_sign (-2) 0 0 (-2) p). cbn [px py]. split.
  - intros [[Hy Hc] | [Hy Hc]]; lra.
  - intros [Hy Hx]. right. lra.
Qed.

(* conv_min lower bound: all slacks nonneg => the min is nonneg. *)
Lemma conv_min_nonneg : forall hps pt,
  Forall (fun hp => 0 <= hp_slack hp pt) hps -> 0 <= conv_min hps pt.
Proof.
  induction hps as [| h rest IH]; intros pt H; simpl; [ lra | ].
  inversion H as [| ? ? Hh Hrest]; subst.
  pose proof (IH pt Hrest) as Hr.
  unfold Rmin; destruct (Rle_dec (hp_slack h pt) (conv_min rest pt)); lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Obligation 5: interior-odd parity, via the monotone-chain split.            *)
(*   A strict-interior point's rightward ray crosses the right (increasing)    *)
(*   chain exactly once and the left (decreasing) chain not at all.            *)
(* -------------------------------------------------------------------------- *)

Lemma diamond_interior_one_chain :
  interior_hits_one_chain diamond_ring diamond_hps diamond_inc diamond_dec.
Proof.
  intros q Hpos Hrav Hnh.
  apply conv_min_pos_iff in Hpos. unfold diamond_hps in Hpos.
  repeat (apply Forall_cons_iff in Hpos as [? Hpos]).
  unfold hp_slack in *; cbn [px py] in *.
  (* the four slacks are strictly positive: interior of |x|+|y| < 2 *)
  (* the guard excludes the vertex height y = 0 *)
  assert (Hy0 : py q <> 0).
  { intro Hy. apply (Hrav (mkPoint 2 0)).
    - unfold diamond_ring; right; left; reflexivity.
    - cbn [px py]. split; lra. }
  left. split.
  - (* chain_crossed q diamond_inc *)
    destruct (Rlt_le_dec (py q) 0) as [Hneg | Hnn].
    + exists ea. split; [ unfold diamond_inc; left; reflexivity | ].
      apply (proj2 (ea_cross_iff q)); lra.
    + exists eb. split; [ unfold diamond_inc; right; left; reflexivity | ].
      apply (proj2 (eb_cross_iff q)); lra.
  - (* ~ chain_crossed q diamond_dec *)
    intros [e [Hin Hcr]]. unfold diamond_dec in Hin; cbn [In] in Hin.
    destruct Hin as [He | [He | []]]; subst e.
    + apply ec_cross_iff in Hcr; lra.
    + apply ed_cross_iff in Hcr; lra.
Qed.

Lemma diamond_convex_interior_parity :
  convex_interior_parity diamond_ring diamond_hps.
Proof.
  exact (convex_interior_parity_from_split diamond_ring diamond_hps
           diamond_inc diamond_dec diamond_bimonotone diamond_interior_one_chain).
Qed.

(* -------------------------------------------------------------------------- *)
(* Obligation 6: exterior-even parity, via the split.                          *)
(*   An exterior point's ray crosses the two chains both-or-neither.           *)
(*   (B) dec crossed => inc crossed needs no exterior hypothesis;              *)
(*   (A) inc crossed => dec crossed uses conv_min < 0 to force the opposite    *)
(*       slack negative (else all slacks >= 0 and conv_min >= 0).              *)
(* -------------------------------------------------------------------------- *)

Lemma diamond_exterior_even : forall p,
  conv_min diamond_hps p < 0 ->
  ray_avoids_vertices p diamond_ring ->
  no_horizontal_edge_at p diamond_ring ->
  ~ point_in_ring p diamond_ring.
Proof.
  intros q Hext Hrav Hnh Hpir.
  pose proof (proj1 (bimonotone_split_parity diamond_ring diamond_inc diamond_dec q
                       diamond_bimonotone) Hpir) as Hxor.
  destruct Hxor as [[Hinc Hdec] | [Hinc Hdec]].
  - (* inc crossed, ~dec : show dec crossed, contradiction *)
    destruct Hinc as [e [Hin Hcr]]. unfold diamond_inc in Hin; cbn [In] in Hin.
    destruct Hin as [He | [He | []]]; subst e.
    + (* ea crossed -> ed crossed *)
      apply ea_cross_iff in Hcr.
      apply Hdec. exists ed. split; [ unfold diamond_dec; right; left; reflexivity | ].
      apply (proj2 (ed_cross_iff q)). split; [ lra | ].
      destruct (Rlt_le_dec (2 + px q + py q) 0) as [Hsd | Hsd]; [ lra | ].
      exfalso.
      assert (Hge : 0 <= conv_min diamond_hps q).
      { apply conv_min_nonneg. unfold diamond_hps.
        repeat (apply Forall_cons); try apply Forall_nil;
          unfold hp_slack; cbn [px py]; lra. }
      lra.
    + (* eb crossed -> ec crossed *)
      apply eb_cross_iff in Hcr.
      apply Hdec. exists ec. split; [ unfold diamond_dec; left; reflexivity | ].
      apply (proj2 (ec_cross_iff q)). split; [ lra | ].
      destruct (Rlt_le_dec (2 + px q - py q) 0) as [Hsc | Hsc]; [ lra | ].
      exfalso.
      assert (Hge : 0 <= conv_min diamond_hps q).
      { apply conv_min_nonneg. unfold diamond_hps.
        repeat (apply Forall_cons); try apply Forall_nil;
          unfold hp_slack; cbn [px py]; lra. }
      lra.
  - (* ~inc, dec crossed : show inc crossed, contradiction (no exterior needed) *)
    destruct Hdec as [e [Hin Hcr]]. unfold diamond_dec in Hin; cbn [In] in Hin.
    destruct Hin as [He | [He | []]]; subst e.
    + (* ec crossed -> eb crossed *)
      apply ec_cross_iff in Hcr.
      apply Hinc. exists eb. split; [ unfold diamond_inc; right; left; reflexivity | ].
      apply (proj2 (eb_cross_iff q)); lra.
    + (* ed crossed -> ea crossed *)
      apply ed_cross_iff in Hcr.
      apply Hinc. exists ea. split; [ unfold diamond_inc; left; reflexivity | ].
      apply (proj2 (ea_cross_iff q)); lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* HEADLINE: the diamond is the fourth total off-ring JCT family.              *)
(* -------------------------------------------------------------------------- *)

Theorem diamond_parity_seam_offring : forall p,
  parity_characterises_interior_cont_offring p diamond_ring.
Proof.
  intro p.
  apply (convex_parity_seam_offring_of diamond_ring diamond_hps p 2).
  - exact diamond_zero_on_skeleton.
  - exact diamond_vertices_in_hps.
  - exact diamond_hps_nondeg.
  - lra.
  - exact diamond_bounded.
  - intros Hpos Hrav Hnh. exact (diamond_convex_interior_parity p Hpos Hrav Hnh).
  - intros Hneg Hrav Hnh. exact (diamond_exterior_even p Hneg Hrav Hnh).
Qed.

(* -------------------------------------------------------------------------- *)
(* Structural facts + the off-ring biconditional corollary.                    *)
(* -------------------------------------------------------------------------- *)

Lemma diamond_ring_closed : ring_closed diamond_ring.
Proof.
  exists (mkPoint 0 (-2)), [ mkPoint 2 0 ; mkPoint 0 2 ; mkPoint (-2) 0 ].
  reflexivity.
Qed.

Lemma diamond_ring_min_points : ring_has_minimum_points diamond_ring.
Proof. unfold ring_has_minimum_points, diamond_ring; cbn [length]; lia. Qed.

Lemma diamond_ring_simple : ring_simple diamond_ring.
Proof.
  unfold ring_simple. rewrite ring_edges_diamond.
  intros e1 e2 H1 H2 Hne. cbn [In] in H1, H2.
  destruct H1 as [<- | [<- | [<- | [<- | []]]]];
  destruct H2 as [<- | [<- | [<- | [<- | []]]]];
    first
      [ exfalso; apply Hne; reflexivity
      | intros (t & s & Ht & Hs & Hx & Hy); cbn [fst snd px py] in *; nra ].
Qed.

Corollary diamond_point_in_ring_iff_geometric : forall p,
  ring_complement diamond_ring p ->
  no_horizontal_edge_at p diamond_ring ->
  ray_avoids_vertices p diamond_ring ->
  (point_in_ring p diamond_ring <-> geometric_interior_cont p diamond_ring).
Proof.
  intros p Hc Hnh Hrav.
  pose proof (diamond_parity_seam_offring p diamond_ring_simple diamond_ring_closed
                diamond_ring_min_points Hc Hnh Hrav) as H.
  split; [ apply (proj2 H) | apply (proj1 H) ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions diamond_parity_seam_offring.
Print Assumptions diamond_point_in_ring_iff_geometric.
