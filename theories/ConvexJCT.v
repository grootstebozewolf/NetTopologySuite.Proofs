(* ============================================================================
   NetTopologySuite.Proofs.ConvexJCT
   ----------------------------------------------------------------------------
   The convex Jordan-curve characterization, GEOMETRIC form: for a y-unimodal
   convex ring, ray-parity `point_in_ring` agrees with the convex field
   `conv_min` — a point is inside (odd crossings) exactly when it strictly
   satisfies every edge half-plane (`0 < conv_min`).  This composes the two
   halves the campaign proved separately:

     - interior-odd  : `MonotoneChainCoverage.interior_hits_one_chain_of_edge_hps`
                       (a strict interior point crosses the increasing chain and
                       not the decreasing one), and
     - exterior-even : `ConvexExteriorEven.convex_exterior_balanced_of_unimodal`
                       (an exterior point crosses both chains or neither),

   glued through `MonotoneChainParity.bimonotone_split_parity` (`point_in_ring`
   is the XOR of the two chain crossings).  The §11.5o discharge of the
   convex⟹y-unimodal residual (`ConvexYUnimodal`) is what makes the structural
   `bimonotone_split` hypothesis available; the crossing-count companion
   (`ConvexRayCrossing.convex_strict_in_ring_iff_one_crossing`) is now also
   unconditional.

   There is NO open mathematical residual here: both halves are `Qed`.  The
   honest hypotheses are exactly the general-position inputs the two halves
   demand — a y-unimodal decomposition, the half-plane data, the interior
   y-range `py bottom < py q < py apex`, and FULL vertex avoidance
   (`forall v, In v outer -> py v <> py q`).  The latter is genuinely stronger
   than the seam's `ray_avoids_vertices` (a vertex at the query height but to its
   LEFT is allowed by the ray guard yet must be excluded for the interior
   straddle), and no bridge between them exists or is possible — so full
   avoidance is the correct guard, not a convenience.

   This file targets `conv_min` directly; lifting to the topological
   `geometric_interior_cont` form (via `ConvexOffringSeam`) needs additional
   per-presentation facts (zero-set on the skeleton, a bounded positive region,
   `ring_simple`/`ring_closed`/`ring_has_minimum_points`) that are not derivable
   from convexity and are supplied per-family (`DiamondOffringSeam`,
   `HexagonOffringSeam`); that lift is out of scope here.

   Pure-R + three-axiom.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List Lra Lia.
From NTS.Proofs Require Import Distance Overlay MonotoneChainParity
                               MonotoneChainConstruction ConvexChainSplit
                               MonotoneChainCoverage ConvexField
                               PointInRingCorrect ConvexOffringSeam ConvexSlice
                               ConvexExteriorEven ConvexYUnimodal.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The composition capstone: point_in_ring iff convex-field interior.      *)
(* -------------------------------------------------------------------------- *)

(* For a y-unimodal convex ring `outer = up ++ apex :: down` (with the half-plane
   list `hps` containing every edge's inward half-plane), a query point off the
   skeleton (`conv_min hps q <> 0`) in full general position is `point_in_ring`
   exactly when it is a strict interior point of the convex field.  The interior
   direction uses the interior-odd coverage theorem; the exterior direction uses
   exterior-even; both are XOR-glued by `bimonotone_split_parity`. *)
Theorem convex_unimodal_point_in_ring_iff_interior :
  forall (up down : list Point) (apex bottom : Point)
         (hps : list (R*R*R)) (q : Point) (outer : Ring),
    y_strict_incr (up ++ [apex]) ->
    y_strict_decr (apex :: down) ->
    (2 <= length (up ++ [apex]))%nat ->
    (2 <= length (apex :: down))%nat ->
    Forall (vertices_in_halfplane outer) hps ->
    Forall (fun e => In (edge_inward_hp e) hps) (ring_edges (up ++ [apex])) ->
    Forall (fun e => In (edge_inward_hp e) hps) (ring_edges (apex :: down)) ->
    py (hd dpt (up ++ [apex])) = py bottom ->
    py (last (apex :: down) dpt) = py bottom ->
    last (up ++ [apex]) dpt = apex ->
    outer = up ++ apex :: down ->
    py bottom < py q < py apex ->
    (forall v, In v outer -> py v <> py q) ->
    conv_min hps q <> 0 ->
    (point_in_ring q outer <-> 0 < conv_min hps q).
Proof.
  intros up down apex bottom hps q outer
         Hinc Hdec Hleni Hlend Hverts HincHps HdecHps Hhd Hlastd Hlasti Houter Hyr Hav Hcm0.
  assert (Hbs : bimonotone_split outer (ring_edges (up ++ [apex])) (ring_edges (apex :: down))).
  { rewrite Houter. apply bimonotone_split_unimodal; assumption. }
  assert (Hrav : ray_avoids_vertices q outer).
  { intros v Hv [Heq _]. exact (Hav v Hv Heq). }
  assert (HinInc : forall v, In v (up ++ [apex]) -> In v outer).
  { intros v Hv. rewrite Houter, in_app_iff. rewrite in_app_iff in Hv.
    destruct Hv as [Hup | Hap]; [ left; exact Hup | ].
    destruct Hap as [<- | []]. right; left; reflexivity. }
  pose proof (bimonotone_split_parity outer (ring_edges (up ++ [apex]))
                (ring_edges (apex :: down)) q Hbs) as Hpar.
  destruct (Rdichotomy (conv_min hps q) 0 Hcm0) as [Hneg | Hpos].
  - (* exterior: balanced crossings negate the XOR, so ~point_in_ring *)
    pose proof (convex_exterior_balanced_of_unimodal up down apex bottom hps q outer
                  Hinc Hdec Hleni Hlend Hverts HincHps Hhd Hlastd Hlasti Houter Hneg Hav)
      as Hbal.
    split.
    + intro Hpir. exfalso.
      destruct (proj1 Hpar Hpir) as [[Hi Hnd] | [Hni Hd]].
      * apply Hnd. exact (proj1 Hbal Hi).
      * apply Hni. exact (proj2 Hbal Hd).
    + intro Hp. lra.
  - (* interior: inc crossed, dec not, so the XOR holds and point_in_ring *)
    destruct Hyr as [Hyr1 Hyr2].
    pose proof (interior_hits_one_chain_of_edge_hps up down apex bottom hps q outer
                  Hinc Hdec HincHps HdecHps Hhd (conj Hyr1 Hyr2) Hlasti Houter HinInc Hpos Hrav)
      as [Hcrinc Hncrdec].
    split.
    + intros _. exact Hpos.
    + intros _. apply (proj2 Hpar). left. split; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Canonical specialization: hps := the ring's own edge half-planes.       *)
(* -------------------------------------------------------------------------- *)

(* When the half-plane list is exactly `map edge_inward_hp (ring_edges outer)`,
   the two `In (edge_inward_hp e) hps` obligations are automatic (every chain
   edge is a ring edge, via the bimonotone split). *)
Theorem convex_unimodal_jct_canonical :
  forall (up down : list Point) (apex bottom : Point) (q : Point) (outer : Ring),
    let hps := map edge_inward_hp (ring_edges outer) in
    y_strict_incr (up ++ [apex]) ->
    y_strict_decr (apex :: down) ->
    (2 <= length (up ++ [apex]))%nat ->
    (2 <= length (apex :: down))%nat ->
    Forall (vertices_in_halfplane outer) hps ->
    py (hd dpt (up ++ [apex])) = py bottom ->
    py (last (apex :: down) dpt) = py bottom ->
    last (up ++ [apex]) dpt = apex ->
    outer = up ++ apex :: down ->
    py bottom < py q < py apex ->
    (forall v, In v outer -> py v <> py q) ->
    conv_min hps q <> 0 ->
    (point_in_ring q outer <-> 0 < conv_min hps q).
Proof.
  intros up down apex bottom q outer hps
         Hinc Hdec Hleni Hlend Hverts Hhd Hlastd Hlasti Houter Hyr Hav Hcm0.
  assert (Hsplit : ring_edges outer
                   = ring_edges (up ++ [apex]) ++ ring_edges (apex :: down)).
  { rewrite Houter.
    destruct (bimonotone_split_unimodal up down apex Hinc Hdec) as [Hs _]. exact Hs. }
  assert (HincHps : Forall (fun e => In (edge_inward_hp e) hps) (ring_edges (up ++ [apex]))).
  { apply Forall_forall. intros e He. unfold hps. apply in_map.
    rewrite Hsplit. apply in_or_app. left. exact He. }
  assert (HdecHps : Forall (fun e => In (edge_inward_hp e) hps) (ring_edges (apex :: down))).
  { apply Forall_forall. intros e He. unfold hps. apply in_map.
    rewrite Hsplit. apply in_or_app. right. exact He. }
  apply (convex_unimodal_point_in_ring_iff_interior up down apex bottom hps q outer);
    assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Validation: the diamond and hexagon, end-to-end through the geometric   *)
(*     convex JCT (ray parity = convex-field membership).                      *)
(* -------------------------------------------------------------------------- *)

Theorem diamond_point_in_ring_iff_interior : forall q,
  py (mkPoint 0 (-2)) < py q < py (mkPoint 0 2) ->
  (forall v, In v diamond_ring -> py v <> py q) ->
  conv_min (map edge_inward_hp (ring_edges diamond_ring)) q <> 0 ->
  (point_in_ring q diamond_ring
   <-> 0 < conv_min (map edge_inward_hp (ring_edges diamond_ring)) q).
Proof.
  intros q Hyr Hav Hcm0.
  apply (convex_unimodal_jct_canonical
           [mkPoint 0 (-2); mkPoint 2 0] [mkPoint (-2) 0; mkPoint 0 (-2)]
           (mkPoint 0 2) (mkPoint 0 (-2)) q diamond_ring).
  - cbn; repeat split; lra.
  - cbn; repeat split; lra.
  - cbn; lia.
  - cbn; lia.
  - exact diamond_convex_inward.
  - cbn; reflexivity.
  - cbn; reflexivity.
  - cbn; reflexivity.
  - unfold diamond_ring; reflexivity.
  - exact Hyr.
  - exact Hav.
  - exact Hcm0.
Qed.

Theorem hexagon_point_in_ring_iff_interior : forall q,
  py (mkPoint 0 (-3)) < py q < py (mkPoint 1 3) ->
  (forall v, In v hexagon_ring -> py v <> py q) ->
  conv_min (map edge_inward_hp (ring_edges hexagon_ring)) q <> 0 ->
  (point_in_ring q hexagon_ring
   <-> 0 < conv_min (map edge_inward_hp (ring_edges hexagon_ring)) q).
Proof.
  intros q Hyr Hav Hcm0.
  apply (convex_unimodal_jct_canonical
           [mkPoint 0 (-3); mkPoint 3 (-1); mkPoint 4 2]
           [mkPoint (-2) 1; mkPoint (-3) (-2); mkPoint 0 (-3)]
           (mkPoint 1 3) (mkPoint 0 (-3)) q hexagon_ring).
  - cbn; repeat split; lra.
  - cbn; repeat split; lra.
  - cbn; lia.
  - cbn; lia.
  - exact hexagon_convex_inward.
  - cbn; reflexivity.
  - cbn; reflexivity.
  - cbn; reflexivity.
  - unfold hexagon_ring; reflexivity.
  - exact Hyr.
  - exact Hav.
  - exact Hcm0.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions convex_unimodal_point_in_ring_iff_interior.
Print Assumptions convex_unimodal_jct_canonical.
Print Assumptions diamond_point_in_ring_iff_interior.
Print Assumptions hexagon_point_in_ring_iff_interior.
