(* ============================================================================
   NetTopologySuite.Proofs.ConvexRayCrossing
   ----------------------------------------------------------------------------
   Convex-chain monotonicity campaign, the y-modulator (crossing bound): a
   convex / y-unimodal ring (one presented as a `bimonotone_split`) is crossed
   AT MOST TWICE by any rightward ray, hence a point is inside iff the ray
   crosses it EXACTLY ONCE — the crisp discrete Jordan characterization for the
   convex case.

   `ConvexYUnimodal.v` showed half-plane convexity is the all-CCW-left-turns
   orientation form and named the residual "convexity ⟹ y-unimodal vertex order"
   (which feeds `bimonotone_split` generally).  This file takes a `bimonotone_split`
   as the structural hypothesis (supplied generally by the y-modulator once the
   residual is closed, and concretely by every family) and proves the crossing
   bound that the split buys:

     §1  `inc_cross_count_le_one` / `dec_cross_count_le_one` — each monotone chain
         is crossed at most once (count form, from `*_chain_le_one_cross`).
     §2  `convex_ray_crosses_le_two` — the whole ring is crossed at most twice.
     §3  `convex_in_ring_iff_one_crossing` — HEADLINE: for a convex ring, a point
         is `point_in_ring` iff `cross_count = 1` (odd + `<= 2` pins it to one).
     §4  Validation on the diamond and hexagon (both already `bimonotone_split`).

   This is the convexity-strengthened companion to the bare parity seam: in
   general a `point_in_ring` only fixes the crossing parity; here convexity fixes
   the exact count.  The remaining geometric residual (convexity ⟹ the vertex
   order is y-unimodal, hence a `bimonotone_split` exists) is unchanged and lives
   in `ConvexYUnimodal.v`.

   Pure-R + three-axiom.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List Lra Lia.
From NTS.Proofs Require Import Distance Overlay MonotoneChainParity
                               MonotoneChainConstruction ConvexChainSplit.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Each monotone chain is crossed at most once (count form).               *)
(* -------------------------------------------------------------------------- *)

Lemma inc_cross_count_le_one : forall p es,
  chain_increasing es -> (cross_count p es <= 1)%nat.
Proof.
  induction es as [| e rest IH]; intros Hc.
  - unfold cross_count; simpl; lia.
  - destruct (edge_crosses_ray_dec p e) as [Hx | Hnx].
    + (* head crosses: the tail cannot cross again (distinct y-intervals) *)
      rewrite (cross_count_cons_cross p e rest Hx).
      assert (Hrest0 : cross_count p rest = 0%nat).
      { apply cross_count_zero_of_no_cross.
        rewrite Forall_forall. intros f Hf Hxf.
        assert (Hef : e = f).
        { apply (inc_chain_le_one_cross (e :: rest) p e f Hc);
            [ left; reflexivity | right; exact Hf | exact Hx | exact Hxf ]. }
        subst f.
        pose proof (chain_increasing_above e rest Hc) as Hab.
        rewrite Forall_forall in Hab. specialize (Hab e Hf).
        pose proof (chain_increasing_all_up (e :: rest) Hc) as Hup.
        rewrite Forall_forall in Hup. specialize (Hup e (or_introl eq_refl)).
        unfold edge_up in Hup. lra. }
      rewrite Hrest0. lia.
    + rewrite (cross_count_cons_nocross p e rest Hnx).
      apply IH.
      destruct rest as [| e2 rest']; [ exact I | ].
      simpl in Hc. destruct Hc as [_ [_ Hcr]]. exact Hcr.
Qed.

Lemma dec_cross_count_le_one : forall p es,
  chain_decreasing es -> (cross_count p es <= 1)%nat.
Proof.
  induction es as [| e rest IH]; intros Hc.
  - unfold cross_count; simpl; lia.
  - destruct (edge_crosses_ray_dec p e) as [Hx | Hnx].
    + rewrite (cross_count_cons_cross p e rest Hx).
      assert (Hrest0 : cross_count p rest = 0%nat).
      { apply cross_count_zero_of_no_cross.
        rewrite Forall_forall. intros f Hf Hxf.
        assert (Hef : e = f).
        { apply (dec_chain_le_one_cross (e :: rest) p e f Hc);
            [ left; reflexivity | right; exact Hf | exact Hx | exact Hxf ]. }
        subst f.
        pose proof (chain_decreasing_below e rest Hc) as Hbe.
        rewrite Forall_forall in Hbe. specialize (Hbe e Hf).
        pose proof (chain_decreasing_all_dn (e :: rest) Hc) as Hdn.
        rewrite Forall_forall in Hdn. specialize (Hdn e (or_introl eq_refl)).
        unfold edge_dn in Hdn. lra. }
      rewrite Hrest0. lia.
    + rewrite (cross_count_cons_nocross p e rest Hnx).
      apply IH.
      destruct rest as [| e2 rest']; [ exact I | ].
      simpl in Hc. destruct Hc as [_ [_ Hcr]]. exact Hcr.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  A convex / y-unimodal ring is crossed at most twice.                    *)
(* -------------------------------------------------------------------------- *)

Theorem convex_ray_crosses_le_two : forall p r inc dec,
  bimonotone_split r inc dec ->
  (cross_count p (ring_edges r) <= 2)%nat.
Proof.
  intros p r inc dec Hbs.
  unfold bimonotone_split in Hbs. destruct Hbs as [Hsplit [Hinc Hdec]].
  rewrite Hsplit, cross_count_app.
  pose proof (inc_cross_count_le_one p inc Hinc) as Hi.
  pose proof (dec_cross_count_le_one p dec Hdec) as Hd.
  lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  HEADLINE: inside iff exactly one crossing.                              *)
(* -------------------------------------------------------------------------- *)

Theorem convex_in_ring_iff_one_crossing : forall p r inc dec,
  bimonotone_split r inc dec ->
  (point_in_ring p r <-> cross_count p (ring_edges r) = 1%nat).
Proof.
  intros p r inc dec Hbs.
  pose proof (convex_ray_crosses_le_two p r inc dec Hbs) as Hle.
  unfold point_in_ring.
  destruct (ray_parity_count p (ring_edges r)) as [Hodd _].
  split.
  - intro Hpir. apply Hodd in Hpir.
    destruct (cross_count p (ring_edges r)) as [| [| [| n]]]; cbn in Hpir;
      solve [ discriminate | reflexivity | lia ].
  - intro Hcc. apply Hodd. rewrite Hcc. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Validation: diamond and hexagon (already bimonotone).                   *)
(* -------------------------------------------------------------------------- *)

Corollary diamond_ray_crosses_le_two : forall p,
  (cross_count p (ring_edges diamond_ring) <= 2)%nat.
Proof.
  intro p. exact (convex_ray_crosses_le_two p diamond_ring diamond_inc diamond_dec
                    diamond_bimonotone).
Qed.

Corollary diamond_in_ring_iff_one_crossing : forall p,
  point_in_ring p diamond_ring <-> cross_count p (ring_edges diamond_ring) = 1%nat.
Proof.
  intro p. exact (convex_in_ring_iff_one_crossing p diamond_ring diamond_inc diamond_dec
                    diamond_bimonotone).
Qed.

Corollary hexagon_ray_crosses_le_two : forall p,
  (cross_count p (ring_edges hexagon_ring) <= 2)%nat.
Proof.
  intro p. exact (convex_ray_crosses_le_two p hexagon_ring hexagon_inc hexagon_dec
                    hexagon_bimonotone).
Qed.

Corollary hexagon_in_ring_iff_one_crossing : forall p,
  point_in_ring p hexagon_ring <-> cross_count p (ring_edges hexagon_ring) = 1%nat.
Proof.
  intro p. exact (convex_in_ring_iff_one_crossing p hexagon_ring hexagon_inc hexagon_dec
                    hexagon_bimonotone).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions convex_ray_crosses_le_two.
Print Assumptions convex_in_ring_iff_one_crossing.
Print Assumptions diamond_in_ring_iff_one_crossing.
Print Assumptions hexagon_in_ring_iff_one_crossing.
