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

   §8–§11 (added 2026-06-16) CLOSE the genuine convex content.  §8 proves the
   geometric keystone — `convex_valley_is_global_min`: a vertex sitting strictly
   below its two neighbours at a STRICT convex corner is the ring's global
   y-minimum (via the one-line cross-product lever `valley_min`).  §9 records the
   honesty caveat that the bare residual `convex_no_interior_ymin` (§6) is FALSE
   in degenerate position (`collinear_spike_not_convex_no_interior_ymin` — a
   collinear spike), which is exactly why a strict-convexity guard is needed.
   §10 then discharges the residual under that guard: `convex_strict_start_y_unimodal`
   proves a strictly-convex ring presented from its unique bottom vertex IS
   y-unimodal — UNCONDITIONALLY, no named residual — and §11 validates the
   diamond and hexagon end-to-end through it.

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
(* §5  The no-interior-y-min reduction: the combinatorial heart of the close.  *)
(* -------------------------------------------------------------------------- *)

(* The genuine convex content of "convexity ⟹ y-unimodal" splits cleanly in
   two.  The LIST-COMBINATORIAL half — proved here, in full — says: a ring whose
   consecutive heights are distinct and which has NO strict interior y-local-
   minimum is y-unimodal.  ("No interior dip": you cannot descend then re-ascend,
   so the height profile is a single ascent to one apex followed by a single
   descent.)  The GEOMETRIC half — that global half-plane convexity, read from
   the bottom vertex, actually forbids every interior y-local-minimum — is the
   single residual, isolated below as the named predicate
   `convex_no_interior_ymin` (never `Admitted`). *)

(* General-position guard: consecutive vertices have distinct heights (i.e. no
   horizontal edge).  The only legal y-tie is the closing duplicate head = last,
   which is non-consecutive (opposite chains; cf. the diamond's (2,0)/(-2,0)). *)
Fixpoint chain_y_distinct (l : list Point) : Prop :=
  match l with
  | a :: ((b :: _) as l') => py a <> py b /\ chain_y_distinct l'
  | _ => True
  end.

(* No strict interior y-local-minimum: no consecutive triple a,b,c has b strictly
   below both neighbours.  A "W dip" anywhere is forbidden. *)
Fixpoint no_interior_strict_ymin (l : list Point) : Prop :=
  match l with
  | a :: ((b :: c :: _) as l') => ~ (py b < py a /\ py b < py c)
                                  /\ no_interior_strict_ymin l'
  | _ => True
  end.

(* The head vertex attains the minimal height over the whole ring. *)
Definition starts_at_min (r : Ring) : Prop :=
  match r with
  | [] => True
  | a :: _ => forall w, In w r -> py a <= py w
  end.

(* Dropping the head preserves the no-interior-min property (the dropped triple
   only constrained the old head). *)
Lemma no_interior_strict_ymin_tail : forall a l,
  no_interior_strict_ymin (a :: l) -> no_interior_strict_ymin l.
Proof.
  intros a l H. destruct l as [| b l']; [ exact I | ].
  destruct l' as [| c l'']; [ exact I | exact (proj2 H) ].
Qed.

(* A small prepend lemma for the increasing chain. *)
Lemma y_strict_incr_cons : forall a l,
  match l with [] => True | b :: _ => py a < py b end ->
  y_strict_incr l ->
  y_strict_incr (a :: l).
Proof. intros a l Hhd Hl. destruct l as [| b l']; cbn; [ exact I | split; assumption ]. Qed.

(* Once a no-interior-min, chain-distinct list starts descending, it descends all
   the way: a re-ascent would create a strict interior minimum. *)
Lemma descending_of_no_interior_min : forall l a b,
  chain_y_distinct (a :: b :: l) ->
  no_interior_strict_ymin (a :: b :: l) ->
  py b < py a ->
  y_strict_decr (a :: b :: l).
Proof.
  induction l as [| c l' IH]; intros a b Hcd Hnim Hba.
  - cbn. split; [ exact Hba | exact I ].
  - cbn. split; [ exact Hba | ].
    apply IH.
    + exact (proj2 Hcd).
    + exact (proj2 Hnim).
    + (* py c < py b: ~(py b < py c) [from the triple] + py b <> py c [distinct] *)
      destruct Hnim as [Htriple _].
      assert (Hnlt : ~ (py b < py c)) by (intro H; apply Htriple; split; assumption).
      assert (Hbc : py b <> py c) by exact (proj1 (proj2 Hcd)).
      apply Rnot_lt_le in Hnlt.
      destruct (Rle_lt_or_eq_dec (py c) (py b) Hnlt) as [Hlt | Heq].
      * exact Hlt.
      * exfalso. apply Hbc. symmetry. exact Heq.
Qed.

(* THE LOAD-BEARING RUNG: no interior strict y-minimum + chain-distinct heights
   ⟹ y-unimodal.  Pure list induction: at each step the list either keeps
   ascending (extend the rising prefix via the IH) or turns down (and then, by
   `descending_of_no_interior_min`, descends to the end — apex is the head). *)
Lemma no_interior_ymin_unimodal : forall l : Ring,
  l <> [] ->
  chain_y_distinct l ->
  no_interior_strict_ymin l ->
  y_unimodal_decomposition l.
Proof.
  induction l as [| a l' IH]; intros Hne Hcd Hnim.
  - exfalso. apply Hne. reflexivity.
  - destruct l' as [| b tl'].
    + (* singleton [a]: up = [], apex = a, down = [] *)
      exists [], [], a. cbn. repeat split.
    + (* l = a :: b :: tl' *)
      destruct (Rlt_le_dec (py a) (py b)) as [Hab | Hba].
      * (* ascending: extend the IH's decomposition of the tail by a *)
        assert (Hcd' : chain_y_distinct (b :: tl')) by exact (proj2 Hcd).
        assert (Hnim' : no_interior_strict_ymin (b :: tl'))
          by exact (no_interior_strict_ymin_tail a (b :: tl') Hnim).
        destruct (IH ltac:(discriminate) Hcd' Hnim')
          as [up' [down' [apex [Hr [Hi Hd]]]]].
        exists (a :: up'), down', apex.
        split.
        { (* (a::up') ++ apex::down' = a :: (up' ++ apex::down') = a :: (b::tl') *)
          cbn. rewrite <- Hr. reflexivity. }
        split.
        { (* y_strict_incr ((a::up') ++ [apex]) *)
          apply y_strict_incr_cons; [ | exact Hi ].
          destruct up' as [| u0 up''].
          - (* up' = [] ⟹ apex = b *)
            cbn in Hr |- *. injection Hr as Hapex _. rewrite <- Hapex. exact Hab.
          - (* up' = u0 :: _ ⟹ u0 = b *)
            cbn in Hr |- *. injection Hr as Hu0 _. rewrite <- Hu0. exact Hab. }
        { exact Hd. }
      * (* descending: apex = a, the whole tail strictly decreases *)
        assert (Hlt : py b < py a).
        { assert (Hab_ne : py a <> py b) by exact (proj1 Hcd). lra. }
        exists [], (b :: tl'), a.
        split; [ reflexivity | ].
        split; [ cbn; exact I | ].
        apply descending_of_no_interior_min; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  The conditional headline + the isolated geometric residual.             *)
(* -------------------------------------------------------------------------- *)

(* The single remaining geometric gap, as a NAMED predicate (not `Admitted`):
   GLOBAL half-plane convexity (the pentagram-ruling form), read from the
   bottom (min-y) vertex, has no strict interior y-local-minimum.  This is the
   genuine convex content the close still needs — it composes the local
   convex-vertex fact over the whole boundary, and genuinely needs either the
   canonical-start rotation invariance or the horizontal-line-meets-convex-
   region-in-an-interval argument (the same global-vs-local distinction that
   rules out the star, per §11.5h). *)
Definition convex_no_interior_ymin (r : Ring) : Prop :=
  Forall (vertices_in_halfplane r) (map edge_inward_hp (ring_edges r)) ->
  starts_at_min r ->
  no_interior_strict_ymin r.

(* The conditional close: under the named residual, a convex ring presented from
   its bottom vertex (with distinct consecutive heights) is y-unimodal — and
   hence has a bimonotone split via the modulator wiring.  The half-plane
   convexity hypothesis is genuinely consumed (it feeds the residual). *)
Theorem convex_canonical_start_y_unimodal : forall r : Ring,
  r <> [] ->
  convex_no_interior_ymin r ->
  Forall (vertices_in_halfplane r) (map edge_inward_hp (ring_edges r)) ->
  starts_at_min r ->
  chain_y_distinct r ->
  y_unimodal_decomposition r.
Proof.
  intros r Hne Hres Hconv Hmin Hcd.
  apply no_interior_ymin_unimodal; [ exact Hne | exact Hcd | ].
  apply Hres; assumption.
Qed.

Corollary convex_canonical_start_bimonotone : forall r : Ring,
  r <> [] ->
  convex_no_interior_ymin r ->
  Forall (vertices_in_halfplane r) (map edge_inward_hp (ring_edges r)) ->
  starts_at_min r ->
  chain_y_distinct r ->
  exists inc dec, bimonotone_split r inc dec.
Proof.
  intros r Hne Hres Hconv Hmin Hcd.
  apply y_unimodal_bimonotone.
  apply convex_canonical_start_y_unimodal; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §7  Validation: the diamond and hexagon go through the NEW rung end-to-end. *)
(* -------------------------------------------------------------------------- *)

(* Both witnesses satisfy the general-position + no-interior-min hypotheses
   directly (by `cbn`/`lra`), so they reach `y_unimodal_decomposition` through
   `no_interior_ymin_unimodal` — exercising the combinatorial rung itself, not
   just the hand-built split of §4. *)
Theorem diamond_y_unimodal_via_rung : y_unimodal_decomposition diamond_ring.
Proof.
  apply no_interior_ymin_unimodal.
  - discriminate.
  - cbn. repeat split; lra.
  - cbn. repeat split; intros [H1 H2]; lra.
Qed.

Theorem hexagon_y_unimodal_via_rung : y_unimodal_decomposition hexagon_ring.
Proof.
  apply no_interior_ymin_unimodal.
  - discriminate.
  - cbn. repeat split; lra.
  - cbn. repeat split; intros [H1 H2]; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §8  The valley lever: a strict-turn local-y-minimum vertex of a convex ring *)
(*     is a GLOBAL minimum — the genuine geometric content, proved.            *)
(* -------------------------------------------------------------------------- *)

(* THE ALGEBRAIC KEYSTONE.  A pure cross-product identity (closed by `ring`):

     (py c - py b) * cross a b w + (py a - py b) * cross b c w
       = (py w - py b) * cross a b c.

   When `b` is strictly below both `a` and `c` (so the two height coefficients
   `py c - py b` and `py a - py b` are positive) and `w` is left-of-or-on both
   directed edges `a→b` and `b→c` (`0 <= cross a b w`, `0 <= cross b c w`), the
   left-hand side is `>= 0`.  A STRICT turn at `b` (`0 < cross a b c`) then forces
   `py b <= py w`.  No supporting-line monotonicity, no induction — just the
   orientation sign of three triangles, fed to `nra`. *)
Lemma valley_min : forall a b c w : Point,
  0 < cross a b c ->
  0 <= cross a b w ->
  0 <= cross b c w ->
  py b < py a ->
  py b < py c ->
  py b <= py w.
Proof.
  intros a b c w Habc Habw Hbcw Hba Hbc.
  assert (Hid : (py c - py b) * cross a b w + (py a - py b) * cross b c w
                = (py w - py b) * cross a b c).
  { destruct a as [ax ay], b as [bx by_], c as [cx cy], w as [wx wy].
    unfold cross; cbn [px py]; ring. }
  assert (H1 : 0 <= (py c - py b) * cross a b w) by (apply Rmult_le_pos; lra).
  assert (H2 : 0 <= (py a - py b) * cross b c w) by (apply Rmult_le_pos; lra).
  nra.
Qed.

(* The convex reading of the lever: in a (half-plane) convex ring, a vertex `b`
   sitting strictly below its two boundary neighbours `a`, `c` — provided the
   turn at `b` is a STRICT left turn (`b` is a genuine convex corner, not a
   collinear/spike degeneracy) — is the GLOBAL minimum: it is `<=` every vertex.
   `convex_left_turns` supplies `0 <= cross a b w` and `0 <= cross b c w` for
   every vertex `w`; the rest is `valley_min`. *)
Lemma convex_valley_is_global_min : forall (r : Ring) (a b c : Point),
  Forall (vertices_in_halfplane r) (map edge_inward_hp (ring_edges r)) ->
  In (a, b) (ring_edges r) ->
  In (b, c) (ring_edges r) ->
  0 < cross a b c ->
  py b < py a ->
  py b < py c ->
  forall w, In w r -> py b <= py w.
Proof.
  intros r a b c Hconv Hab Hbc Hturn Hba Hbc' w Hw.
  apply (valley_min a b c w Hturn).
  - exact (convex_left_turns r a b w Hconv Hab Hw).
  - exact (convex_left_turns r b c w Hconv Hbc Hw).
  - exact Hba.
  - exact Hbc'.
Qed.

(* -------------------------------------------------------------------------- *)
(* §9  The bare residual `convex_no_interior_ymin` is FALSE as stated.         *)
(* -------------------------------------------------------------------------- *)

(* HONESTY NOTE.  The residual predicate `convex_no_interior_ymin` (§6) is NOT
   provable as literally stated: a DEGENERATE convex ring can have an interior
   strict y-local-minimum.  Witness: a fully collinear (zero-area) vertical
   "ring".  Every edge is vertical, so `edge_inward_hp` has x-coefficient ≠ 0 but
   zero constant and y-coefficient, and the slack of every edge at every vertex
   (all on the line `x = 0`) is exactly `0` — global half-plane convexity holds
   vacuously.  Its head `(0,0)` is a (non-strict) global minimum, so
   `starts_at_min` holds.  Yet the consecutive triple `(0,2),(0,1),(0,3)` is a
   strict interior y-minimum.  This is precisely the case the §8 lever cannot
   touch — the turn at the valley is `cross = 0` (collinear), not a STRICT left
   turn — which is exactly why the closing rung needs a strict-convexity
   general-position guard.  The bare predicate's premises hold while its
   conclusion fails, so it is false. *)
Definition collinear_spike_ring : Ring :=
  [ mkPoint 0 0 ; mkPoint 0 2 ; mkPoint 0 1 ; mkPoint 0 3 ; mkPoint 0 0 ].

Lemma collinear_spike_not_convex_no_interior_ymin :
  ~ convex_no_interior_ymin collinear_spike_ring.
Proof.
  unfold convex_no_interior_ymin. intro H.
  assert (Hno : no_interior_strict_ymin collinear_spike_ring).
  { apply H.
    - unfold collinear_spike_ring.
      cbn [ring_edges map edge_inward_hp].
      repeat (apply Forall_cons); try apply Forall_nil;
        intros v Hv; cbn [In] in Hv;
        repeat (destruct Hv as [<- | Hv]); try contradiction;
        unfold hp_slack; cbn [px py fst snd]; lra.
    - cbn [collinear_spike_ring starts_at_min]. intros w Hw.
      cbn [In] in Hw.
      repeat (destruct Hw as [<- | Hw]); try contradiction; cbn [py]; lra. }
  cbn in Hno.
  destruct Hno as [_ [Hbad _]].
  apply Hbad. split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §10  The corrected, UNCONDITIONAL close under the strict-convexity guard.   *)
(* -------------------------------------------------------------------------- *)

(* General position guard (the honest minimum, per §9): every consecutive triple
   is a STRICT left turn (no three consecutive vertices collinear). *)
Fixpoint strict_ccw_turns (l : list Point) : Prop :=
  match l with
  | a :: ((b :: c :: _) as l') => 0 < cross a b c /\ strict_ccw_turns l'
  | _ => True
  end.

(* Every element of `l` strictly above height `h0`, EXCEPT possibly the last (the
   closing duplicate of a ring is permitted to tie the bottom). *)
Fixpoint all_above (h0 : R) (l : list Point) : Prop :=
  match l with
  | [] => True
  | x :: rest => match rest with
                 | [] => True
                 | _ => h0 < py x /\ all_above h0 rest
                 end
  end.

(* The bottom vertex (head) is strictly lower than every other vertex, save the
   closing duplicate.  Equivalent to: the global minimum is attained uniquely, at
   the head — the elementary fact the §8 lever reduces the geometry to. *)
Definition unique_bottom (r : Ring) : Prop :=
  match r with
  | [] => True
  | h :: t => all_above (py h) t
  end.

(* Consecutive list members are ring edges. *)
Lemma ring_edges_adjacent : forall pre a b suf,
  In (a, b) (ring_edges (pre ++ a :: b :: suf)).
Proof.
  induction pre as [| x pre IH]; intros a b suf.
  - cbn. left. reflexivity.
  - cbn [app].
    destruct (pre ++ a :: b :: suf) as [| y l] eqn:E.
    + destruct pre; cbn [app] in E; discriminate.
    + change (In (a, b) ((x, y) :: ring_edges (y :: l))).
      right. rewrite <- E. apply IH.
Qed.

(* A consecutive triple anywhere in a `strict_ccw_turns` list is a strict turn. *)
Lemma strict_ccw_turns_app : forall pre a b c suf,
  strict_ccw_turns (pre ++ a :: b :: c :: suf) -> 0 < cross a b c.
Proof.
  induction pre as [| p pre IH]; intros a b c suf H.
  - cbn [app] in H. exact (proj1 H).
  - cbn [app] in H.
    apply (IH a b c suf).
    remember (pre ++ a :: b :: c :: suf) as m eqn:E.
    destruct m as [| x [| y l]].
    + exact I.
    + exact I.
    + cbn [strict_ccw_turns] in H. exact (proj2 H).
Qed.

(* A non-last element of an `all_above h0` list is strictly above `h0`. *)
Lemma all_above_not_last : forall (h0 : R) (mid : list Point) (x : Point) (rest : list Point),
  all_above h0 (mid ++ x :: rest) ->
  rest <> [] ->
  h0 < py x.
Proof.
  induction mid as [| m mid IH]; intros x rest Hall Hrest.
  - destruct rest as [| r0 rest']; [ contradiction | ].
    cbn [app all_above] in Hall. exact (proj1 Hall).
  - cbn [app] in Hall.
    remember (mid ++ x :: rest) as m0 eqn:E.
    destruct m0 as [| y l].
    + exfalso. destruct mid; cbn [app] in E; discriminate.
    + cbn [all_above] in Hall.
      apply (IH x rest); [ rewrite <- E; exact (proj2 Hall) | exact Hrest ].
Qed.

(* `no_interior_strict_ymin` from a per-triple obligation (pure list induction). *)
Lemma no_interior_strict_ymin_of_triples : forall l : list Point,
  (forall pre a b c suf, l = pre ++ a :: b :: c :: suf -> ~ (py b < py a /\ py b < py c)) ->
  no_interior_strict_ymin l.
Proof.
  induction l as [| a0 l IH]; intros Htri.
  - exact I.
  - destruct l as [| b0 l']; [ exact I | ].
    destruct l' as [| c0 l'']; [ exact I | ].
    change (~ (py b0 < py a0 /\ py b0 < py c0)
            /\ no_interior_strict_ymin (b0 :: c0 :: l'')).
    split.
    + exact (Htri [] a0 b0 c0 l'' eq_refl).
    + apply IH. intros pre a b c suf Heq.
      apply (Htri (a0 :: pre) a b c suf).
      cbn [app]. rewrite Heq. reflexivity.
Qed.

(* THE CLOSE (formerly the geometric residual).  A half-plane-convex ring in
   strict general position (`strict_ccw_turns`) presented from a UNIQUE bottom
   vertex (`unique_bottom`) has NO interior strict y-local-minimum.  Each candidate
   valley triple is refuted: §8's lever makes the valley a global minimum
   (`py b <= py h` for the head `h`), while `unique_bottom` forces `py h < py b`
   (the valley is a non-last interior vertex) — contradiction.  No hypothesis is
   left dangling; this discharges `convex_no_interior_ymin`'s content under the
   honest general-position guard §9 shows is necessary. *)
Theorem convex_strict_no_interior_ymin : forall r : Ring,
  Forall (vertices_in_halfplane r) (map edge_inward_hp (ring_edges r)) ->
  strict_ccw_turns r ->
  unique_bottom r ->
  no_interior_strict_ymin r.
Proof.
  intros r Hconv Hstrict Huniq.
  apply no_interior_strict_ymin_of_triples.
  intros pre a b c suf Hr [Hba Hbc].
  assert (Hab_e : In (a, b) (ring_edges r)).
  { rewrite Hr. apply (ring_edges_adjacent pre a b (c :: suf)). }
  assert (Hbc_e : In (b, c) (ring_edges r)).
  { assert (Heq : ring_edges r = ring_edges ((pre ++ [a]) ++ b :: c :: suf)).
    { rewrite Hr. rewrite <- app_assoc. reflexivity. }
    rewrite Heq. apply (ring_edges_adjacent (pre ++ [a]) b c suf). }
  assert (Hturn : 0 < cross a b c).
  { apply (strict_ccw_turns_app pre a b c suf). rewrite <- Hr. exact Hstrict. }
  destruct r as [| h t].
  { exfalso. destruct pre; cbn [app] in Hr; discriminate. }
  cbn [unique_bottom] in Huniq.
  assert (Hbh : py b <= py h).
  { apply (convex_valley_is_global_min (h :: t) a b c); try assumption.
    left; reflexivity. }
  assert (Hhb : py h < py b).
  { destruct pre as [| p pre'].
    - cbn [app] in Hr. injection Hr as Hh Ht. subst t.
      apply (all_above_not_last (py h) [] b (c :: suf)); [ exact Huniq | discriminate ].
    - cbn [app] in Hr. injection Hr as Hh Ht. subst t.
      apply (all_above_not_last (py h) (pre' ++ [a]) b (c :: suf)).
      + rewrite <- (app_assoc pre' [a] (b :: c :: suf)). cbn [app]. exact Huniq.
      + discriminate. }
  lra.
Qed.

(* The unconditional headline: a strictly-convex ring presented from its unique
   bottom vertex (distinct consecutive heights) IS y-unimodal — no named residual.
   This is the §11.5k conditional headline with the residual discharged. *)
Theorem convex_strict_start_y_unimodal : forall r : Ring,
  r <> [] ->
  Forall (vertices_in_halfplane r) (map edge_inward_hp (ring_edges r)) ->
  strict_ccw_turns r ->
  unique_bottom r ->
  chain_y_distinct r ->
  y_unimodal_decomposition r.
Proof.
  intros r Hne Hconv Hstrict Huniq Hcd.
  apply no_interior_ymin_unimodal; [ exact Hne | exact Hcd | ].
  apply convex_strict_no_interior_ymin; assumption.
Qed.

(* And the bimonotone split drops out through the modulator wiring — the whole
   convex ladder, unconditional under strict general position. *)
Corollary convex_strict_start_bimonotone : forall r : Ring,
  r <> [] ->
  Forall (vertices_in_halfplane r) (map edge_inward_hp (ring_edges r)) ->
  strict_ccw_turns r ->
  unique_bottom r ->
  chain_y_distinct r ->
  exists inc dec, bimonotone_split r inc dec.
Proof.
  intros r Hne Hconv Hstrict Huniq Hcd.
  apply y_unimodal_bimonotone.
  apply convex_strict_start_y_unimodal; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §11  Validation: the diamond and hexagon go through the UNCONDITIONAL close. *)
(* -------------------------------------------------------------------------- *)

(* Half-plane convexity in the `edge_inward_hp` form (the shape the close wants). *)
Lemma diamond_convex_inward :
  Forall (vertices_in_halfplane diamond_ring) (map edge_inward_hp (ring_edges diamond_ring)).
Proof.
  unfold diamond_ring.
  cbn [ring_edges map edge_inward_hp].
  repeat (apply Forall_cons); try apply Forall_nil;
    intros v Hv; cbn [In] in Hv;
    repeat (destruct Hv as [<- | Hv]); try contradiction;
    unfold hp_slack; cbn [px py fst snd]; lra.
Qed.

Theorem diamond_y_unimodal_via_strict : y_unimodal_decomposition diamond_ring.
Proof.
  apply convex_strict_start_y_unimodal.
  - discriminate.
  - exact diamond_convex_inward.
  - cbn [diamond_ring strict_ccw_turns]; repeat split; unfold cross; cbn [px py]; lra.
  - cbn [diamond_ring unique_bottom all_above py]; repeat split; lra.
  - cbn [diamond_ring chain_y_distinct py]; repeat split; lra.
Qed.

Lemma hexagon_convex_inward :
  Forall (vertices_in_halfplane hexagon_ring) (map edge_inward_hp (ring_edges hexagon_ring)).
Proof.
  unfold hexagon_ring.
  cbn [ring_edges map edge_inward_hp].
  repeat (apply Forall_cons); try apply Forall_nil;
    intros v Hv; cbn [In] in Hv;
    repeat (destruct Hv as [<- | Hv]); try contradiction;
    unfold hp_slack; cbn [px py fst snd]; lra.
Qed.

Theorem hexagon_y_unimodal_via_strict : y_unimodal_decomposition hexagon_ring.
Proof.
  apply convex_strict_start_y_unimodal.
  - discriminate.
  - exact hexagon_convex_inward.
  - cbn [hexagon_ring strict_ccw_turns]; repeat split; unfold cross; cbn [px py]; lra.
  - cbn [hexagon_ring unique_bottom all_above py]; repeat split; lra.
  - cbn [hexagon_ring chain_y_distinct py]; repeat split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions convex_left_turns.
Print Assumptions y_unimodal_bimonotone.
Print Assumptions exists_max_y_vertex.
Print Assumptions diamond_y_unimodal.
Print Assumptions hexagon_y_unimodal.
Print Assumptions descending_of_no_interior_min.
Print Assumptions no_interior_ymin_unimodal.
Print Assumptions convex_canonical_start_y_unimodal.
Print Assumptions convex_canonical_start_bimonotone.
Print Assumptions diamond_y_unimodal_via_rung.
Print Assumptions hexagon_y_unimodal_via_rung.
Print Assumptions valley_min.
Print Assumptions convex_valley_is_global_min.
Print Assumptions collinear_spike_not_convex_no_interior_ymin.
Print Assumptions convex_strict_no_interior_ymin.
Print Assumptions convex_strict_start_y_unimodal.
Print Assumptions convex_strict_start_bimonotone.
Print Assumptions diamond_y_unimodal_via_strict.
Print Assumptions hexagon_y_unimodal_via_strict.
