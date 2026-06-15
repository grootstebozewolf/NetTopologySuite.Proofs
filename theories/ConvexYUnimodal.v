(* ============================================================================
   NetTopologySuite.Proofs.ConvexYUnimodal
   ----------------------------------------------------------------------------
   Convex-chain monotonicity campaign, the y-modulator (first step): the bridge
   from HALF-PLANE convexity to ORIENTATION (all CCW left-turns), the y-unimodal
   decomposition predicate and its wiring to `bimonotone_split`, supporting
   extremum infrastructure, and the isolation of the remaining geometric residual.

   Rung 3.5 (`MonotoneChainConstruction.bimonotone_split_unimodal`) reduces the
   bimonotone split to a purely combinatorial y-unimodality hypothesis; Rung 4
   (`MonotoneChainCoverage.interior_hits_one_chain_of_edge_hps`) closes interior-
   odd for any y-unimodal ring.  What still gates a *fully general* convex n-gon
   is the geometric implication "convexity ⟹ the vertex order is y-unimodal".

   This file lays the first stones:

   §1  `hp_slack_edge_inward_is_cross` / `convex_left_turns` — the half-plane
       convexity hypothesis `vertices_in_halfplane` (every vertex in every edge's
       inward half-plane) is EXACTLY "every vertex is left-of-or-on every edge"
       (`0 <= cross a b c`), i.e. all boundary turns are CCW.  This is the
       orientation form of convexity, and the global form correctly rules out the
       star/pentagram (which has all *local* left-turns but a vertex outside a
       non-adjacent edge's half-plane).

   §2  `y_unimodal_decomposition` — the named structural predicate: the ring is
       `up ++ apex :: down` with `y_strict_incr (up ++ [apex])` and
       `y_strict_decr (apex :: down)`.  `y_unimodal_bimonotone` wires it to
       `bimonotone_split` via Rung 3.5.

   §3  `exists_max_y_vertex` / `exists_min_y_vertex` — extremum infrastructure a
       future closing rung needs (a nonempty ring has a maximal-/minimal-height
       vertex).  Pure list induction.

   §4  Validation — `diamond_ring` and `hexagon_ring` satisfy
       `y_unimodal_decomposition` directly (their CCW order already starts at the
       bottom vertex), recovering their bimonotone splits through the modulator.

   The remaining residual (the genuine convex content) is the IMPLICATION
   `convex_left_turns`-form ⟹ `y_unimodal_decomposition` for a general convex
   ring under the right general-position guard — isolated here, to be closed by a
   follow-up rung.  This file introduces no `Admitted`: it proves the bridge and
   the wiring, and validates the witnesses.

   Pure-R + three-axiom.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List Lra.
From NTS.Proofs Require Import Distance Overlay Orientation ConvexField
                               MonotoneChainParity MonotoneChainConstruction
                               MonotoneChainCoverage ConvexChainSplit
                               ConvexOffringSeam.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Half-plane convexity is the all-left-turns (CCW) orientation form.      *)
(* -------------------------------------------------------------------------- *)

(* The inward-half-plane slack of edge (a,b) evaluated at c is exactly the
   signed twice-area `cross a b c`.  (`edge_inward_hp` and the cross-product
   identity live in `MonotoneChainCoverage`.) *)
Lemma hp_slack_edge_inward_is_cross : forall a b c : Point,
  hp_slack (edge_inward_hp (a, b)) c = cross a b c.
Proof.
  intros [ax ay] [bx by_] [cx cy].
  rewrite hp_slack_edge_inward_cross_product. unfold cross. cbn [px py]. ring.
Qed.

(* Convexity, half-plane form: every vertex lies in every edge's inward
   half-plane.  Equivalently (this lemma): every vertex is left-of-or-on every
   directed edge — all boundary turns are counter-clockwise.  Crucially the
   hypothesis is GLOBAL (all vertices vs. all edges), so it rules out the
   pentagram, whose local turns are all left but which has vertices outside the
   half-planes of non-adjacent edges. *)
Lemma convex_left_turns : forall (r : Ring) (a b c : Point),
  Forall (vertices_in_halfplane r) (map edge_inward_hp (ring_edges r)) ->
  In (a, b) (ring_edges r) ->
  In c r ->
  0 <= cross a b c.
Proof.
  intros r a b c HF Hab Hc.
  rewrite <- hp_slack_edge_inward_is_cross.
  rewrite Forall_forall in HF.
  apply (HF (edge_inward_hp (a, b))).
  - apply in_map. exact Hab.
  - exact Hc.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The y-unimodal decomposition predicate and its wiring.                  *)
(* -------------------------------------------------------------------------- *)

(* A ring is y-unimodal when its vertex list rises strictly to a single apex
   then falls strictly: `up ++ apex :: down` with the two strict-monotone runs.
   This is exactly the hypothesis `bimonotone_split_unimodal` (Rung 3.5)
   consumes. *)
Definition y_unimodal_decomposition (r : Ring) : Prop :=
  exists (up down : list Point) (apex : Point),
    r = up ++ apex :: down /\
    y_strict_incr (up ++ [apex]) /\
    y_strict_decr (apex :: down).

(* The wiring: a y-unimodal ring has a bimonotone split (the increasing chain is
   the rising prefix's skeleton, the decreasing chain the falling suffix's). *)
Theorem y_unimodal_bimonotone : forall r,
  y_unimodal_decomposition r ->
  exists inc dec, bimonotone_split r inc dec.
Proof.
  intros r [up [down [apex [Hr [Hi Hd]]]]].
  subst r.
  exists (ring_edges (up ++ [apex])), (ring_edges (apex :: down)).
  apply bimonotone_split_unimodal; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Extremum infrastructure: a nonempty ring has max-/min-height vertices.  *)
(* -------------------------------------------------------------------------- *)

Lemma exists_max_y_vertex : forall (r : list Point),
  r <> [] ->
  exists v, In v r /\ forall w, In w r -> py w <= py v.
Proof.
  induction r as [| a r' IH]; intro Hne.
  - exfalso; apply Hne; reflexivity.
  - destruct r' as [| b r''].
    + (* singleton *)
      exists a. split; [ left; reflexivity | ].
      intros w [Hw | []]. subst w. lra.
    + (* a :: b :: r'' : recurse on the tail, then compare with a *)
      destruct (IH ltac:(discriminate)) as [m [Hm Hmax]].
      destruct (Rle_lt_dec (py a) (py m)) as [Hle | Hlt].
      * (* m dominates a *)
        exists m. split; [ right; exact Hm | ].
        intros w [Hw | Hw].
        -- subst w. exact Hle.
        -- apply Hmax. exact Hw.
      * (* a dominates m (hence the whole tail) *)
        exists a. split; [ left; reflexivity | ].
        intros w [Hw | Hw].
        -- subst w. lra.
        -- pose proof (Hmax w Hw) as Hwm. lra.
Qed.

Lemma exists_min_y_vertex : forall (r : list Point),
  r <> [] ->
  exists v, In v r /\ forall w, In w r -> py v <= py w.
Proof.
  induction r as [| a r' IH]; intro Hne.
  - exfalso; apply Hne; reflexivity.
  - destruct r' as [| b r''].
    + exists a. split; [ left; reflexivity | ].
      intros w [Hw | []]. subst w. lra.
    + destruct (IH ltac:(discriminate)) as [m [Hm Hmin]].
      destruct (Rle_lt_dec (py m) (py a)) as [Hle | Hlt].
      * exists m. split; [ right; exact Hm | ].
        intros w [Hw | Hw].
        -- subst w. exact Hle.
        -- apply Hmin. exact Hw.
      * exists a. split; [ left; reflexivity | ].
        intros w [Hw | Hw].
        -- subst w. lra.
        -- pose proof (Hmin w Hw) as Hwm. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Validation: diamond and hexagon are y-unimodal, recovering their splits.*)
(* -------------------------------------------------------------------------- *)

(* `diamond_ring`'s CCW order already starts at the bottom vertex (0,-2), so it
   IS literally `up ++ apex :: down` (the closing duplicate sits at the tail of
   `down`).  Note the diamond is NOT y-injective — (2,0) and (-2,0) share height
   0 — yet it is y-unimodal, because the tie lands on OPPOSITE chains; each chain
   is individually strict.  This is why the eventual residual's general-position
   guard is "no two ADJACENT-on-a-chain vertices share y", not full y-injectivity. *)
Theorem diamond_y_unimodal : y_unimodal_decomposition diamond_ring.
Proof.
  exists [mkPoint 0 (-2); mkPoint 2 0], [mkPoint (-2) 0; mkPoint 0 (-2)],
         (mkPoint 0 2).
  split; [ reflexivity | split ].
  - cbn [y_strict_incr app py]. repeat split; lra.
  - cbn [y_strict_decr py]. repeat split; lra.
Qed.

Theorem hexagon_y_unimodal : y_unimodal_decomposition hexagon_ring.
Proof.
  exists [mkPoint 0 (-3); mkPoint 3 (-1); mkPoint 4 2],
         [mkPoint (-2) 1; mkPoint (-3) (-2); mkPoint 0 (-3)],
         (mkPoint 1 3).
  split; [ reflexivity | split ].
  - cbn [y_strict_incr app py]. repeat split; lra.
  - cbn [y_strict_decr py]. repeat split; lra.
Qed.

(* And the splits drop out through the modulator wiring. *)
Theorem diamond_bimonotone_via_y_unimodal :
  exists inc dec, bimonotone_split diamond_ring inc dec.
Proof. apply y_unimodal_bimonotone, diamond_y_unimodal. Qed.

Theorem hexagon_bimonotone_via_y_unimodal :
  exists inc dec, bimonotone_split hexagon_ring inc dec.
Proof. apply y_unimodal_bimonotone, hexagon_y_unimodal. Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions convex_left_turns.
Print Assumptions y_unimodal_bimonotone.
Print Assumptions exists_max_y_vertex.
Print Assumptions diamond_y_unimodal.
Print Assumptions hexagon_y_unimodal.
