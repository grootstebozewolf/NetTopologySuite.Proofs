(* ============================================================================
   NetTopologySuite.Proofs.ConvexChainSplit
   ----------------------------------------------------------------------------
   Convex-chain monotonicity campaign, RUNG 3: conditional closure of
   `convex_interior_parity` over a bimonotone split.

   This file assembles the campaign: given the two structural residuals (a) the
   ring's edges split into a y-increasing chain followed by a y-decreasing chain
   (`bimonotone_split`), and (b) a strictly-interior point hits exactly one of the
   two chains (`interior_hits_one_chain`), `convex_interior_parity` follows
   immediately from `MonotoneChainParity.bimonotone_split_parity` (rung 2).

   Both residuals are named predicates, not Admitteds.  Concrete convex families
   can discharge them by ring-specific case analysis; the general-n-gon case
   (connecting `conv_min > 0` / `vertices_in_halfplane` to vertex ordering) is the
   sole remaining open lemma, isolated exactly here.

   §4 adds a concrete diamond witness (`diamond_ring`, split into two 2-edge
   chains, test point (0, 1/2)) that exercises the full pipeline end-to-end:
   `bimonotone_split` + `chain_crossed` + `bimonotone_split_parity` ⟹
   `point_in_ring` in 3 steps with no `Admitted`.

   Pure-R + three-axiom.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List Lra.
From NTS.Proofs Require Import Distance Overlay ConvexField PointInRingCorrect
                               ConvexNesting MonotoneChainParity.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The remaining structural residual.                                      *)
(* -------------------------------------------------------------------------- *)

(* `interior_hits_one_chain outer hps inc dec`: for every strictly-interior
   point (positive in every half-plane), in general position w.r.t. `outer`,
   exactly one of the two chains is crossed by the rightward ray.  This is the
   conjunction of two geometric facts: (a) the interior point's y is strictly
   between the ring's min-y and max-y, so the ray hits at least one chain; and
   (b) the ring's convex geometry ensures the ray hits only the right-side
   (increasing) chain, not the left-side (decreasing) one.  Establishing this
   for a general convex ring (from `vertices_in_halfplane`/`conv_min`) is the
   last open lemma of the campaign; concrete families discharge it by explicit
   crossing arithmetic. *)
Definition interior_hits_one_chain
    (outer : Ring) (hps : list (R * R * R)) (inc dec : list Edge) : Prop :=
  forall q : Point,
    0 < conv_min hps q ->
    ray_avoids_vertices q outer ->
    no_horizontal_edge_at q outer ->
    (chain_crossed q inc /\ ~ chain_crossed q dec) \/
    (~ chain_crossed q inc /\ chain_crossed q dec).

(* -------------------------------------------------------------------------- *)
(* §2  RUNG 3 — conditional closure of `convex_interior_parity`.              *)
(* -------------------------------------------------------------------------- *)

(* Given the bimonotone split and the one-chain property, `convex_interior_parity`
   holds.  The proof is a one-step composition: `bimonotone_split_parity` (rung 2)
   turns the XOR into `point_in_ring`; `interior_hits_one_chain` supplies the XOR.
   The two named predicates are the ONLY residuals for the general convex case. *)
Theorem convex_interior_parity_from_split :
  forall (outer : Ring) (hps : list (R * R * R)) (inc dec : list Edge),
    bimonotone_split outer inc dec ->
    interior_hits_one_chain outer hps inc dec ->
    convex_interior_parity outer hps.
Proof.
  intros outer hps inc dec Hsplit Hone.
  unfold convex_interior_parity.
  intros q Hpos Hrav Hnh.
  apply (bimonotone_split_parity outer inc dec q Hsplit).
  exact (Hone q Hpos Hrav Hnh).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Corollary: guarded general convex hole_inside_outer via the split.     *)
(* -------------------------------------------------------------------------- *)

Theorem hole_inside_outer_convex_via_split :
  forall (outer hole : Ring) (hps : list (R * R * R)) (inc dec : list Edge) (p : Point),
    bimonotone_split outer inc dec ->
    interior_hits_one_chain outer hps inc dec ->
    In p hole ->
    0 < conv_min hps p ->
    ray_avoids_vertices p outer ->
    no_horizontal_edge_at p outer ->
    hole_inside_outer outer hole.
Proof.
  intros outer hole hps inc dec p Hsplit Hone Hin Hpos Hrav Hnh.
  apply (hole_inside_outer_convex_guarded outer hole hps p
    (convex_interior_parity_from_split outer hps inc dec Hsplit Hone)
    Hin Hpos Hrav Hnh).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Concrete diamond witness: the full pipeline exercised end-to-end.      *)
(*   A convex 4-gon with integer (/2) coordinates, split into two 2-edge      *)
(*   chains, with test point (0, 1/2) crossing exactly the increasing chain.   *)
(* -------------------------------------------------------------------------- *)

(* CCW diamond (0,-2), (2,0), (0,2), (-2,0). *)
Definition diamond_ring : Ring :=
  [ mkPoint 0 (-2) ; mkPoint 2 0 ; mkPoint 0 2 ; mkPoint (-2) 0 ; mkPoint 0 (-2) ].

(* Right (increasing) side: two up-edges going (0,-2)→(2,0)→(0,2). *)
Definition diamond_inc : list Edge :=
  [ (mkPoint 0 (-2), mkPoint 2 0) ; (mkPoint 2 0, mkPoint 0 2) ].

(* Left (decreasing) side: two down-edges going (0,2)→(-2,0)→(0,-2). *)
Definition diamond_dec : list Edge :=
  [ (mkPoint 0 2, mkPoint (-2) 0) ; (mkPoint (-2) 0, mkPoint 0 (-2)) ].

Lemma diamond_bimonotone : bimonotone_split diamond_ring diamond_inc diamond_dec.
Proof.
  unfold bimonotone_split, diamond_ring, diamond_inc, diamond_dec.
  refine (conj _ (conj _ _)).
  - (* ring_edges diamond_ring = diamond_inc ++ diamond_dec *)
    reflexivity.
  - (* chain_increasing diamond_inc *)
    simpl chain_increasing.
    refine (conj _ (conj _ (conj _ I))).
    + unfold edge_up. cbn [py fst snd]. lra.
    + reflexivity.
    + unfold edge_up. cbn [py fst snd]. lra.
  - (* chain_decreasing diamond_dec *)
    simpl chain_decreasing.
    refine (conj _ (conj _ (conj _ I))).
    + unfold edge_dn. cbn [py fst snd]. lra.
    + reflexivity.
    + unfold edge_dn. cbn [py fst snd]. lra.
Qed.

(* Test point at height 1/2 (avoids all vertex heights -2, 0, 2). *)
Definition diamond_pt : Point := mkPoint 0 (1/2).

(* The increasing chain IS crossed: (2,0)→(0,2) straddles y=1/2 with intercept 1.5 > 0. *)
Lemma diamond_inc_crossed : chain_crossed diamond_pt diamond_inc.
Proof.
  unfold chain_crossed, diamond_pt, diamond_inc.
  exists (mkPoint 2 0, mkPoint 0 2). split.
  - right. left. reflexivity.
  - unfold edge_crosses_ray. cbn [fst snd px py]. left. split; lra.
Qed.

(* The decreasing chain is NOT crossed: left-side intercepts are at x = -1.5, and
   the lower edge's y-band misses height 1/2 entirely. *)
Lemma diamond_dec_not_crossed : ~ chain_crossed diamond_pt diamond_dec.
Proof.
  unfold chain_crossed. intros [e [Hin Hx]].
  unfold diamond_dec in Hin. cbn [In] in Hin.
  destruct Hin as [<- | [<- | []]];
    unfold edge_crosses_ray, diamond_pt in Hx;
    cbn [fst snd px py] in Hx;
    destruct Hx as [[Hy Hx] | [Hy Hx]]; lra.
Qed.

(* Full pipeline: bimonotone_split_parity + XOR ⟹ point_in_ring. *)
Theorem diamond_point_in_ring_via_split : point_in_ring diamond_pt diamond_ring.
Proof.
  apply (bimonotone_split_parity diamond_ring diamond_inc diamond_dec _ diamond_bimonotone).
  left. exact (conj diamond_inc_crossed diamond_dec_not_crossed).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions convex_interior_parity_from_split.
Print Assumptions hole_inside_outer_convex_via_split.
Print Assumptions diamond_point_in_ring_via_split.
