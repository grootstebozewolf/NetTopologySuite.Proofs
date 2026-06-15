(* ============================================================================
   NetTopologySuite.Proofs.ConvexExteriorEven
   ----------------------------------------------------------------------------
   Convex-chain monotonicity campaign: the GENERAL exterior-even, factoring the
   parity plumbing out of every family.

   `ConvexOffringSeam.convex_parity_seam_offring_of` assembles the total off-ring
   seam for a half-plane-presented ring from two guarded-parity obligations:
   interior-odd (`0 < conv_min ⟹ point_in_ring`) — which is GENERAL
   (`MonotoneChainCoverage.interior_hits_one_chain_of_edge_hps`) — and
   exterior-even (`conv_min < 0 ⟹ ~ point_in_ring`), which has so far been
   supplied PER FAMILY (e.g. `HexagonOffringSeam.hexagon_exterior_even`, a
   six-edge per-band analysis).

   This file isolates the GEOMETRIC heart of exterior-even as one named predicate
   — `convex_exterior_balanced`: an exterior point's rightward ray crosses the two
   monotone chains BOTH-or-NEITHER — and proves, once and for all, that this
   predicate yields `~ point_in_ring` for any `bimonotone_split` ring (via the
   parity bridge `MonotoneChainParity.bimonotone_split_parity`).  The converse
   shows the predicate is exactly the per-family obligation, repackaged through
   the bridge; so every family now only owes the geometric balance, not the
   parity reduction.  Validated on the diamond and hexagon (recovered from their
   existing exterior-even lemmas), and composed into a general convex off-ring
   seam (`convex_offring_seam_of_balanced`).

   The genuinely-hard geometric discharge of `convex_exterior_balanced` for an
   ARBITRARY convex ring (the convex "horizontal slice = inter-chain interval"
   fact) remains the open content — but note the exterior straddle-extraction
   lever the interior proof uses (`conv_min > 0` forcing vertex-height avoidance)
   is unavailable for exterior points, so it is a genuine multi-session lemma; it
   is carried here as the named predicate, never `Admitted`.

   Pure-R + three-axiom.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List Lra Lia.
From NTS.Proofs Require Import Distance Overlay MonotoneChainParity
                               MonotoneChainConstruction ConvexChainSplit
                               MonotoneChainCoverage
                               ConvexField PointInRingTangents PointInRingCorrect
                               JCT_OnEdgeCounterexample ConvexOffringSeam
                               DiamondOffringSeam HexagonOffringSeam.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  `chain_crossed` is decidable (via the crossing count), so "not XOR"      *)
(*     collapses to the iff.                                                    *)
(* -------------------------------------------------------------------------- *)

Lemma chain_crossed_dec : forall p es, chain_crossed p es \/ ~ chain_crossed p es.
Proof.
  intros p es. destruct (Nat.eq_dec (cross_count p es) 0) as [H | H].
  - right. rewrite chain_crossed_iff_count. lia.
  - left. apply chain_crossed_iff_count. exact H.
Qed.

Lemma not_xor_iff : forall A B : Prop,
  (A \/ ~ A) -> (B \/ ~ B) ->
  ~ ((A /\ ~ B) \/ (~ A /\ B)) -> (A <-> B).
Proof. intros A B HA HB H. tauto. Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The named geometric residual: exterior ⟹ both-or-neither chain crossed. *)
(* -------------------------------------------------------------------------- *)

Definition convex_exterior_balanced
    (r : Ring) (hps : list (R*R*R)) (inc dec : list Edge) : Prop :=
  forall p : Point,
    conv_min hps p < 0 ->
    ray_avoids_vertices p r ->
    no_horizontal_edge_at p r ->
    (chain_crossed p inc <-> chain_crossed p dec).

(* -------------------------------------------------------------------------- *)
(* §3  The general exterior-even: balance ⟹ ~ point_in_ring, for any split.    *)
(* -------------------------------------------------------------------------- *)

(* The parity plumbing, factored out of every family: a `bimonotone_split` ring
   whose exterior crossings are balanced has even ray-parity outside, i.e. is not
   `point_in_ring`.  (`bimonotone_split_parity` makes `point_in_ring` the XOR of
   the two chain crossings; balance negates the XOR.) *)
Theorem convex_exterior_even_of_balanced : forall r inc dec hps p,
  bimonotone_split r inc dec ->
  convex_exterior_balanced r hps inc dec ->
  conv_min hps p < 0 ->
  ray_avoids_vertices p r ->
  no_horizontal_edge_at p r ->
  ~ point_in_ring p r.
Proof.
  intros r inc dec hps p Hbs Hbal Hext Hrav Hnh Hpir.
  apply (proj1 (bimonotone_split_parity r inc dec p Hbs)) in Hpir.
  destruct (Hbal p Hext Hrav Hnh) as [Hid Hdi].
  destruct Hpir as [[Hi Hnd] | [Hni Hd]].
  - exact (Hnd (Hid Hi)).
  - exact (Hni (Hdi Hd)).
Qed.

(* The converse: the named predicate is EXACTLY the per-family exterior-even
   obligation, viewed through the parity bridge.  So generalising via
   `convex_exterior_balanced` loses nothing — it factors the bridge step out. *)
Theorem balanced_of_exterior_even : forall r inc dec hps,
  bimonotone_split r inc dec ->
  (forall p, conv_min hps p < 0 -> ray_avoids_vertices p r ->
             no_horizontal_edge_at p r -> ~ point_in_ring p r) ->
  convex_exterior_balanced r hps inc dec.
Proof.
  intros r inc dec hps Hbs Hext p Hcm Hrav Hnh.
  pose proof (Hext p Hcm Hrav Hnh) as Hn.
  rewrite (bimonotone_split_parity r inc dec p Hbs) in Hn.
  apply not_xor_iff; [ apply chain_crossed_dec | apply chain_crossed_dec | exact Hn ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The capstone: a general convex off-ring seam from the balance predicate. *)
(* -------------------------------------------------------------------------- *)

(* Feeding the general exterior-even into `convex_parity_seam_offring_of`: any
   half-plane-presented `bimonotone_split` ring with the balance predicate (and
   the general interior-odd obligation + the presentation facts) gets the TOTAL
   off-ring parity seam.  Exterior-even is now supplied generically; only the
   interior obligation and presentation remain per-instance. *)
Theorem convex_offring_seam_of_balanced : forall r hps inc dec p M,
  bimonotone_split r inc dec ->
  (forall pt, conv_min hps pt = 0 -> ring_image r pt) ->
  Forall (vertices_in_halfplane r) hps ->
  Forall (fun hp : R * R * R => let '(a, b, _) := hp in 0 < a * a + b * b) hps ->
  0 < M ->
  (forall pt, 0 < conv_min hps pt -> px pt * px pt + py pt * py pt <= M * M) ->
  convex_exterior_balanced r hps inc dec ->
  (0 < conv_min hps p -> ray_avoids_vertices p r ->
     no_horizontal_edge_at p r -> point_in_ring p r) ->
  parity_characterises_interior_cont_offring p r.
Proof.
  intros r hps inc dec p M Hbs Hzero Hverts Hnd HM Hbound Hbal Hint.
  apply (convex_parity_seam_offring_of r hps p M Hzero Hverts Hnd HM Hbound Hint).
  intros Hext Hrav Hnh.
  exact (convex_exterior_even_of_balanced r inc dec hps p Hbs Hbal Hext Hrav Hnh).
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Validation: the diamond and hexagon discharge the balance predicate.    *)
(* -------------------------------------------------------------------------- *)

Lemma diamond_exterior_balanced :
  convex_exterior_balanced diamond_ring diamond_hps diamond_inc diamond_dec.
Proof.
  apply balanced_of_exterior_even.
  - exact diamond_bimonotone.
  - exact diamond_exterior_even.
Qed.

Lemma hexagon_exterior_balanced :
  convex_exterior_balanced hexagon_ring hexagon_edge_hps hexagon_inc hexagon_dec.
Proof.
  apply balanced_of_exterior_even.
  - exact hexagon_bimonotone.
  - exact hexagon_exterior_even.
Qed.

(* Round-trip sanity: the general theorem recovers each family's exterior-even. *)
Corollary diamond_exterior_even_via_balanced : forall p,
  conv_min diamond_hps p < 0 ->
  ray_avoids_vertices p diamond_ring ->
  no_horizontal_edge_at p diamond_ring ->
  ~ point_in_ring p diamond_ring.
Proof.
  intros p. apply (convex_exterior_even_of_balanced diamond_ring diamond_inc diamond_dec
                     diamond_hps p diamond_bimonotone diamond_exterior_balanced).
Qed.

Corollary hexagon_exterior_even_via_balanced : forall p,
  conv_min hexagon_edge_hps p < 0 ->
  ray_avoids_vertices p hexagon_ring ->
  no_horizontal_edge_at p hexagon_ring ->
  ~ point_in_ring p hexagon_ring.
Proof.
  intros p. apply (convex_exterior_even_of_balanced hexagon_ring hexagon_inc hexagon_dec
                     hexagon_edge_hps p hexagon_bimonotone hexagon_exterior_balanced).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions convex_exterior_even_of_balanced.
Print Assumptions balanced_of_exterior_even.
Print Assumptions convex_offring_seam_of_balanced.
Print Assumptions diamond_exterior_balanced.
Print Assumptions hexagon_exterior_balanced.
