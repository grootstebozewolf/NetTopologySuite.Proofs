(* ==========================================================================
   EulerFormula.v

   Toward an UNCONDITIONAL discharge of the planar Euler identity
   `euler_characteristic E` that `extract_rings_valid` (OverlayBridge.v §8)
   and `HBridgeEuler.H_bridge_premise_from_euler` currently carry as a NAMED
   HYPOTHESIS.

   --------------------------------------------------------------------------
   WHY IT IS STILL A HYPOTHESIS (the obstruction, precisely).

   `euler_characteristic E := V + F = E + 2*C` (EulerArrangement §2) is the
   genus-0 relation for the combinatorial MAP induced by the geometric angular
   order (DartAngularOrder).  It is NOT derivable from the rotation-system data
   alone: an abstract rotation system can have any genus, and V-E+F = 2-2g.
   Establishing g = 0 is exactly a discrete planar-embedding fact.

   The current corpus proves the bridge property (a same-face edge is a cut
   edge) FROM the Euler identity:

       EulerBridge.H_bridge_core_conclusion_from_euler :
         euler_characteristic E -> euler_characteristic (E_minus E d) -> ...
         -> ~ reachable (E_minus E d) (fst d) (snd d)

   So Euler is used to prove "bridge".  A standalone inductive proof of Euler
   (delete edges one at a time) needs the CONVERSE deltas -- and in particular
   needs to know, per edge, whether it is a bridge -- which is currently only
   available *via* Euler.  That circularity is the crux; breaking it needs an
   independent genus-0 / planar-embedding argument.

   --------------------------------------------------------------------------
   THE INDUCTION PLAN (what an unconditional proof needs).

   Induct on E, deleting one once-occurring edge d at a time.  Euler is
   INVARIANT under each deletion, so `euler_characteristic E` reduces to
   `euler_characteristic []` (the base case, PROVED below):

     bridge edge d (same_face):   Delta V = 0, Delta E = -1, Delta F = +1, Delta C = +1
       (V+F) -> (V+F+1) ;  (E+2C) -> (E-1) + 2(C+1) = E+2C+1     -- preserved.
     cycle edge d (not same_face):Delta V = 0, Delta E = -1, Delta F = -1, Delta C = 0
       (V+F) -> (V+F-1) ;  (E+2C) -> (E-1) + 2C     = E+2C-1     -- preserved.

   MISSING LEMMAS (each unconditional, i.e. NOT assuming euler_characteristic):

     [EF-1] bridge components split:  same_face-edge d (equivalently: d a cut
            edge) => num_components (E_minus E d) = num_components E + 1.
            *** DONE below, UNCONDITIONALLY, as `bridge_components_split` ***
            (reachability form, mirroring [EF-3]: `~ reachable (E_minus E d)
             (fst d) (snd d)` plus both endpoints surviving as vertices via
             some other edge; Euler-free, 2-axiom.  Proved via the semantic
             bridge `reachable_add_edge_iff` -- E-reachability is exactly
             (E minus d)-reachability plus whatever crossing `d` once newly
             connects -- composed with the existing generic "+1 splice" engine
             `ClassCount.count_classes_filter_split` / `count_classes_eq_1`
             (previously used only for the face-orbit splice) applied to the
             reachability relation: the endpoints' single E-class becomes
             exactly two (E minus d)-classes, every other class is untouched.)
     [EF-2] cycle face merge:  ~ same_face-edge d =>
            num_faces (E_minus E d) = num_faces E - 1.
            *** DONE, UNCONDITIONALLY, as `NumFacesMerge.num_faces_E_minus_merge` ***
            (theories/PermCycleMerge.v + theories/NumFacesMerge.v.  The mirror
             image of `PermCycleSplice.cycle_count_surgery`: `d` and `twin d`
             sit on two DISTINCT fstep-orbits (periods per1, per2); the SAME
             cross-wiring redirect `FaceStepRemove.fstep_E_minus_splice`
             (already proved WITHOUT any same-face hypothesis) STITCHES them
             into one orbit of length per1+per2-2, via the SAME generic "+1"
             splice engine EF-1 reused (`ClassCount.count_classes_filter_split`
             / `count_classes_eq_1`), run in the opposite direction.
             `PermCycleMerge.cycle_count_merge` is fully axiom-free (0 axioms:
             pure permutation/list/nat combinatorics); the Dart-layer
             instantiation carries the corpus's standard 2-axiom footprint.)
     [EF-3] cycle connectivity: bypass (d not a cut edge) =>
            num_components (E_minus E d) = num_components E.
            *** DONE below, UNCONDITIONALLY, as `cycle_components_eq` ***
            (reachability form: `reachable (E_minus E d) (fst d) (snd d)` with
             distinct endpoints; Euler-free, 2-axiom.  This is the correct
             graph-theoretic framing -- the delta is classified by REACHABILITY,
             not same_face; the same_face<->cut-edge link is the residual crux.)
     [EF-4] vertex delta over the induction: `num_vertices_E_minus_eq` needs
            min-degree-2; peeling edges eventually breaks that, so the
            induction must either track the exact Delta V or induct over a
            degree->=2 core (the standard Euler proof deletes degree-1 vertices
            first).  Base case then generalises from [] to a forest.
            *** PARTIAL: the missing permutation-surgery case is now proved,
             UNCONDITIONALLY and AXIOM-FREE, as `PermCycleShrink.cycle_count_shrink`.
             ***  A degree-1 (leaf) vertex's unique dart `d0` forces a SPUR at
             its twin (`fstep D (twin d0) = d0`), so `no_spurs` -- the standing
             hypothesis of EVERY [EF-1]/[EF-2]/[EF-3] lemma above -- fails
             exactly there; none of the split/merge machinery applies to
             leaf-peeling.  This is precisely the `k = 1` boundary case
             `PermCycleSplice.v`'s SPLIT excludes outright
             (`Hk_range : 2 <= k <= per-2`).  `PermCycleShrink.v` supplies that
             missing third permutation surgery: when `f d = td` directly and
             the shared orbit has period `>= 3` (excluding the further
             degenerate sub-case where `{d, td}` is an isolated 2-cycle, i.e. an
             edge whose BOTH endpoints are degree-1 -- a lone K2 component,
             genuinely simpler and not attempted here), the same same_face-
             agnostic redirect leaves the orbit count UNCHANGED -- the correct
             face-count delta (0) for peeling a leaf edge.  Still OPEN: the
             Dart-layer instantiation (a `NumFacesShrink.v` analogous to
             `NumFacesSplice.v`/`NumFacesMerge.v`) needs a fresh hypothesis this
             corpus does not yet supply -- that the far endpoint `b` of the leaf
             edge is not ITSELF degree-1 (i.e. `per >= 3` rather than `per = 2`)
             -- plus the companion Delta V = -1 / Delta C = 0 facts for a
             vertex vanishing from the carrier.  Assembling those and wiring
             the standalone "peeling a degree-1 vertex's edge preserves
             `euler_characteristic`" theorem is the next well-scoped step.

   The genuinely hard, planar-content lemma is the equivalence
   `same_face E d  <->  d is a cut edge of E` proven WITHOUT Euler -- i.e. the
   combinatorial Jordan step.  [EF-1], [EF-2], and [EF-3] are now ALL
   Euler-free and unconditional -- every arithmetic DELTA the induction step
   needs (component split, component no-change, face merge; the face SPLIT
   delta was already banked pre-existing as `NumFacesSplice`) is proved.  What
   remains is exclusively the same_face<->cut-edge equivalence itself: with it
   the induction could dispatch on `same_face` alone (a decidable, purely
   combinatorial test) instead of needing the correct delta supplied
   externally per edge, and [EF-4]'s vertex-delta/degree-2-core bookkeeping
   for the induction's base case.  This is the sole surviving combinatorial
   Jordan step; the corpus already knows every OTHER piece of the arithmetic.

   Until then `euler_characteristic` stays the single, clearly-named planar
   hypothesis, SHARED unchanged by the linear and curve extractors (the curve
   case adds no new Euler obligation -- it reuses the same arrangement counts).

   This file banks the base case and the plan; it introduces NO `Admitted`,
   `Axiom`, or `Parameter` (the corpus invariant is preserved).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import List Arith Lia Bool.
From NTS.Proofs Require Import Distance Overlay OverlayGraph EdgeConnectivity
                               EulerArrangement MapCounts ReachableDec EulerBridge
                               ClassCount.

Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* Base case of the induction: the empty arrangement satisfies Euler.          *)
(*                                                                            *)
(* V = F = E = C = 0 on the empty edge list (no vertices, no fstep orbits, no  *)
(* edges, no components), so V + F = E + 2*C is 0 = 0.                          *)
(* -------------------------------------------------------------------------- *)

Lemma num_vertices_nil : num_vertices [] = 0%nat.
Proof. reflexivity. Qed.

Lemma num_edges_nil : num_edges [] = 0%nat.
Proof. reflexivity. Qed.

Lemma euler_characteristic_nil : euler_characteristic [].
Proof.
  unfold euler_characteristic.
  rewrite num_vertices_nil, num_edges_nil.
  (* num_faces [] = 0 and num_components [] = 0 both compute. *)
  cbn. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* Deletion invariance, arithmetic core (UNCONDITIONAL in the counts).         *)
(*                                                                            *)
(* Given the four per-edge deltas as hypotheses, Euler transfers across one    *)
(* edge deletion in BOTH directions.  This is the arithmetic skeleton of the   *)
(* induction step; the OPEN work is supplying the deltas ([EF-1..4]) without   *)
(* assuming Euler.  Stated here so the eventual proof only has to discharge    *)
(* the geometric deltas, not re-derive the bookkeeping.                        *)
(* -------------------------------------------------------------------------- *)

Lemma euler_transfer_bridge : forall E d,
  num_vertices (E_minus E d) = num_vertices E ->
  num_edges (E_minus E d) + 1 = num_edges E ->
  num_faces (E_minus E d) = (num_faces E + 1)%nat ->
  num_components (E_minus E d) = (num_components E + 1)%nat ->
  (euler_characteristic E <-> euler_characteristic (E_minus E d)).
Proof.
  intros E d HV HE HF HC. unfold euler_characteristic.
  rewrite HV, HF, HC. lia.
Qed.

Lemma euler_transfer_cycle : forall E d,
  num_vertices (E_minus E d) = num_vertices E ->
  num_edges (E_minus E d) + 1 = num_edges E ->
  num_faces (E_minus E d) + 1 = num_faces E ->
  num_components (E_minus E d) = num_components E ->
  (euler_characteristic E <-> euler_characteristic (E_minus E d)).
Proof.
  intros E d HV HE HF HC. unfold euler_characteristic.
  rewrite HV, HC. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* [EF-3] Cycle component delta, UNCONDITIONAL (Euler-free graph theory).       *)
(*                                                                            *)
(* If deleting a (non-loop) edge d leaves its endpoints connected -- a bypass  *)
(* exists, i.e. d is NOT a cut edge -- then the component count is unchanged.   *)
(* This is one of the two component-side deltas the Euler induction needs, and *)
(* it needs NO Euler hypothesis (contrast euler_component_increase, which does).*)
(* -------------------------------------------------------------------------- *)

(* A non-trivial walk starts at a genuine vertex: the first adjacency step is
   an incident edge. *)
Lemma reachable_ne_in_verts : forall E u v,
  reachable E u v -> u <> v -> In u (verts E).
Proof.
  intros E u v Hr Hne. destruct Hr as [u | u v' w Hadj Hrec].
  - contradiction.
  - destruct Hadj as [e [He Hor]]. apply in_verts. exists e. split; [ exact He | ].
    destruct Hor as [[Hf _] | [_ Hs]]; [ left | right ]; assumption.
Qed.

(* Under a bypass (with distinct endpoints) no vertex is dropped, so the vertex
   sets of E and E_minus E d coincide. *)
Lemma verts_incl_E_of_bypass : forall E d,
  fst d <> snd d ->
  reachable (E_minus E d) (fst d) (snd d) ->
  incl (verts E) (verts (E_minus E d)).
Proof.
  intros E d Hne Hby p Hp.
  apply in_verts in Hp. destruct Hp as [e [He Hend]].
  destruct (edge_eq_dec e d) as [-> | Hedne].
  - (* p is an endpoint of d itself; both endpoints survive via the bypass. *)
    destruct Hend as [Hf | Hs].
    + rewrite <- Hf. apply (reachable_ne_in_verts (E_minus E d) (fst d) (snd d) Hby Hne).
    + rewrite <- Hs.
      apply (reachable_ne_in_verts (E_minus E d) (snd d) (fst d)
               (reach_sym _ _ _ Hby) (fun h => Hne (eq_sym h))).
  - (* p is an endpoint of a surviving edge e <> d. *)
    apply in_verts. exists e. split; [ apply in_E_minus; split; assumption | exact Hend ].
Qed.

Lemma cycle_components_eq : forall E d,
  fst d <> snd d ->
  reachable (E_minus E d) (fst d) (snd d) ->
  num_components (E_minus E d) = num_components E.
Proof.
  intros E d Hne Hby.
  (* reachability agrees on E and E_minus E d (bypass reroutes every use of d). *)
  assert (Hrel : forall u v, reachable E u v <-> reachable (E_minus E d) u v)
    by (intros u v; apply bypass_reachable_iff; exact Hby).
  assert (Hb : forall u v, reachable_b (E_minus E d) u v = reachable_b E u v).
  { intros u v.
    destruct (reachable_b (E_minus E d) u v) eqn:H1;
      destruct (reachable_b E u v) eqn:H2; try reflexivity; exfalso.
    - apply reachable_b_true_iff in H1. apply (proj2 (Hrel u v)) in H1.
      apply reachable_b_true_iff in H1. congruence.
    - apply reachable_b_true_iff in H2. apply (proj1 (Hrel u v)) in H2.
      apply reachable_b_true_iff in H2. congruence. }
  (* vertex sets coincide (bypass, distinct endpoints). *)
  assert (Hincl1 : incl (verts (E_minus E d)) (verts E)) by (apply verts_E_minus_incl).
  assert (Hincl2 : incl (verts E) (verts (E_minus E d)))
    by (apply verts_incl_E_of_bypass; assumption).
  (* num_components on each, rewritten to a common relation via comp_reps_ext. *)
  unfold num_components.
  rewrite (comp_reps_ext (E_minus E d) E
             (nodup point_eq_dec (verts (E_minus E d))) Hb).
  apply Nat.le_antisymm.
  - apply comp_reps_length_mono. intros x Hx. rewrite nodup_In in Hx. rewrite nodup_In.
    apply Hincl1; exact Hx.
  - apply comp_reps_length_mono. intros x Hx. rewrite nodup_In in Hx. rewrite nodup_In.
    apply Hincl2; exact Hx.
Qed.

(* -------------------------------------------------------------------------- *)
(* [EF-1] Bridge component delta, UNCONDITIONAL (Euler-free graph theory).      *)
(*                                                                            *)
(* If `d` is a cut edge (its endpoints become unreachable once `d` is deleted) *)
(* and both endpoints survive as vertices via some OTHER edge, then deleting   *)
(* `d` increases the component count by EXACTLY one: the single component      *)
(* containing both endpoints splits into exactly two.  This is the other of    *)
(* the two component-side deltas the Euler induction needs ([EF-3] being the   *)
(* bypass/no-change case); together they are Euler-free.  The both-endpoints-  *)
(* survive side condition is the same min-degree bookkeeping flagged at        *)
(* [EF-4] -- an isolated endpoint is a genuinely different (vertex-count)      *)
(* delta, not attempted here.                                                 *)
(* -------------------------------------------------------------------------- *)

(* The semantic engine: `E`-reachability is exactly `(E minus d)`-reachability, *)
(* PLUS whatever a single crossing of `d` newly connects.  Proved by structural *)
(* induction on the `reachable E u v` derivation (via `reach_refl`/`reach_step`), *)
(* not on path length, so it is robust to `d` being crossed any number of       *)
(* times in a longer `E`-walk: each individual step through `d` collapses into  *)
(* the SAME two extra disjuncts via `(E minus d)`'s own transitivity/symmetry.  *)
Lemma reachable_add_edge_iff : forall E d u v,
  In d E ->
  reachable E u v <->
    ( reachable (E_minus E d) u v
      \/ (reachable (E_minus E d) u (fst d) /\ reachable (E_minus E d) (snd d) v)
      \/ (reachable (E_minus E d) u (snd d) /\ reachable (E_minus E d) (fst d) v) ).
Proof.
  intros E d u v Hd. split.
  - intro Hr. induction Hr as [u | u v0 w Hadj Hrec IH].
    + left. apply reach_refl.
    + destruct Hadj as [e0 [He0 Hends]].
      destruct (edge_eq_dec e0 d) as [-> | Hne].
      * (* the very first step IS d: u,v0 = fst d,snd d in some order. *)
        destruct Hends as [[Hfu Hsv0] | [Hfv0 Hsu]].
        -- (* u = fst d, v0 = snd d *)
           subst u v0. destruct IH as [IH1 | [[IH2a IH2b] | [IH3a IH3b]]].
           ++ right; left. split; [ apply reach_refl | exact IH1 ].
           ++ left. apply (reach_trans (E_minus E d) (fst d) (snd d) w);
                [ apply reach_sym; exact IH2a | exact IH2b ].
           ++ left. exact IH3b.
        -- (* u = snd d, v0 = fst d *)
           subst u v0. destruct IH as [IH1 | [[IH2a IH2b] | [IH3a IH3b]]].
           ++ right; right. split; [ apply reach_refl | exact IH1 ].
           ++ left. exact IH2b.
           ++ left. apply (reach_trans (E_minus E d) (snd d) (fst d) w);
                [ apply reach_sym; exact IH3a | exact IH3b ].
      * (* the first step survives in E minus d. *)
        assert (Hadj' : adj (E_minus E d) u v0)
          by (exists e0; split; [ apply in_E_minus; split; assumption | exact Hends ]).
        destruct IH as [IH1 | [[IH2a IH2b] | [IH3a IH3b]]].
        -- left. apply (reach_step _ _ v0); [ exact Hadj' | exact IH1 ].
        -- right; left.
           split; [ apply (reach_step _ _ v0); [ exact Hadj' | exact IH2a ] | exact IH2b ].
        -- right; right.
           split; [ apply (reach_step _ _ v0); [ exact Hadj' | exact IH3a ] | exact IH3b ].
  - intros [H1 | [[H2a H2b] | [H3a H3b]]].
    + apply (reach_incl (E_minus E d) E); [ apply E_minus_incl | exact H1 ].
    + apply (reach_trans E u (fst d) v).
      * apply (reach_incl (E_minus E d) E); [ apply E_minus_incl | exact H2a ].
      * apply (reach_trans E (fst d) (snd d) v).
        -- apply reach_one, adj_edge; exact Hd.
        -- apply (reach_incl (E_minus E d) E); [ apply E_minus_incl | exact H2b ].
    + apply (reach_trans E u (snd d) v).
      * apply (reach_incl (E_minus E d) E); [ apply E_minus_incl | exact H3a ].
      * apply (reach_trans E (snd d) (fst d) v).
        -- apply reach_sym, reach_one, adj_edge; exact Hd.
        -- apply (reach_incl (E_minus E d) E); [ apply E_minus_incl | exact H3b ].
Qed.

(* Vertex-set inclusion given both endpoints of `d` survive via some other
   edge: mirrors `verts_incl_E_of_bypass`, but the hypothesis is the endpoints'
   own survival (a genuine side condition here -- there is no bypass) rather
   than derived from one. *)
Lemma verts_incl_E_of_survivors : forall E d,
  In (fst d) (verts (E_minus E d)) ->
  In (snd d) (verts (E_minus E d)) ->
  incl (verts E) (verts (E_minus E d)).
Proof.
  intros E d Ha Hb p Hp.
  apply in_verts in Hp. destruct Hp as [e [He Hend]].
  destruct (edge_eq_dec e d) as [-> | Hedne].
  - destruct Hend as [Hf | Hs]; [ rewrite <- Hf; exact Ha | rewrite <- Hs; exact Hb ].
  - apply in_verts. exists e. split; [ apply in_E_minus; split; assumption | exact Hend ].
Qed.

Lemma bridge_components_split : forall E d,
  In d E ->
  fst d <> snd d ->
  In (fst d) (verts (E_minus E d)) ->
  In (snd d) (verts (E_minus E d)) ->
  ~ reachable (E_minus E d) (fst d) (snd d) ->
  num_components (E_minus E d) = (num_components E + 1)%nat.
Proof.
  intros E d Hd Hne Ha Hb Hcut.
  set (Ed := E_minus E d).
  set (a := fst d). set (b := snd d).
  set (V := nodup point_eq_dec (verts Ed)).
  (* Both edge lists share the same vertex SET, so `num_components E` may be
     recomputed over `V` instead of `nodup (verts E)` (mirrors the double
     `comp_reps_length_mono` + antisymmetry step of `cycle_components_eq`). *)
  assert (HinclEEd : incl (verts E) (verts Ed)) by (apply verts_incl_E_of_survivors; assumption).
  assert (HinclEdE : incl (verts Ed) (verts E)) by (apply verts_E_minus_incl).
  assert (HnumE : num_components E = count_classes (reachable_b E) V).
  { unfold num_components, comp_reps, count_classes, V.
    apply Nat.le_antisymm.
    - apply comp_reps_length_mono. intros x Hx. rewrite nodup_In in Hx |- *.
      apply HinclEEd; exact Hx.
    - apply comp_reps_length_mono. intros x Hx. rewrite nodup_In in Hx |- *.
      apply HinclEdE; exact Hx. }
  assert (HnumEd : num_components Ed = count_classes (reachable_b Ed) V)
    by reflexivity.
  (* `a` and `b` are directly `E`-adjacent, hence `E`-reachable, always. *)
  assert (Hab : reachable E a b) by (apply reach_one, adj_edge, Hd).
  assert (Hba : reachable E b a) by (apply reach_sym; exact Hab).
  (* The splitting predicate: "reachable to `a` in E". *)
  set (inO := fun x => reachable_b E x a).
  assert (HccE : forall x y, In x V -> In y V -> reachable_b E x y = true -> inO x = inO y).
  { intros x y _ _ Hxy. unfold inO.
    destruct (reachable_b E x a) eqn:Hxa; destruct (reachable_b E y a) eqn:Hya;
      try reflexivity; exfalso.
    - apply reachable_b_true_iff in Hxy, Hxa.
      assert (reachable_b E y a = true)
        by (apply reachable_b_true_iff, (reach_trans E y x a);
              [ apply reach_sym; exact Hxy | exact Hxa ]).
      congruence.
    - apply reachable_b_true_iff in Hxy, Hya.
      assert (reachable_b E x a = true)
        by (apply reachable_b_true_iff, (reach_trans E x y a); [ exact Hxy | exact Hya ]).
      congruence. }
  assert (HccEd : forall x y, In x V -> In y V -> reachable_b Ed x y = true -> inO x = inO y).
  { intros x y Hx Hy Hxy. apply (HccE x y Hx Hy).
    apply reachable_b_true_iff. apply reachable_b_true_iff in Hxy.
    apply (reach_incl Ed E); [ apply E_minus_incl | exact Hxy ]. }
  (* Split both counts along `inO`. *)
  rewrite (count_classes_filter_split (reachable_b E) (reachable_b_refl E) inO V HccE
             (fun x y z _ _ _ => reachable_b_trans E x y z)) in HnumE.
  rewrite (count_classes_filter_split (reachable_b Ed) (reachable_b_refl Ed) inO V HccEd
             (fun x y z _ _ _ => reachable_b_trans Ed x y z)) in HnumEd.
  (* The `inO`-block is exactly one `E`-class (everything reachable to `a`). *)
  assert (HblockE1 : count_classes (reachable_b E) (filter inO V) = 1%nat).
  { apply (count_classes_eq_1 (reachable_b E) (reachable_b_refl E)).
    - intro Hnil.
      assert (Hain : In a (filter inO V)).
      { apply filter_In. split.
        - apply nodup_In. exact Ha.
        - unfold inO. apply reachable_b_refl. }
      rewrite Hnil in Hain. destruct Hain.
    - intros x y Hx Hy. apply filter_In in Hx. apply filter_In in Hy.
      unfold inO in Hx, Hy. destruct Hx as [_ Hxa]. destruct Hy as [_ Hya].
      apply reachable_b_true_iff in Hxa, Hya. apply reachable_b_true_iff.
      apply (reach_trans E x a y); [ exact Hxa | apply reach_sym; exact Hya ]. }
  (* Outside the `inO`-block, `E` and `Ed` reachability agree exactly: reaching
     `a` in `E` (but not `Ed`) would require crossing `d`, but `Ed`-reaching
     `b` already forces `Ed`-reaching `a` too (contra the cut-edge hypothesis)
     via the direct `a-b` edge on the `E` side, so no such crossing survives
     outside the block either way. *)
  assert (HccOd : forall x, negb (inO x) = true -> ~ reachable_b Ed x a = true /\ ~ reachable_b Ed x b = true).
  { intros x Hx. unfold inO in Hx. apply negb_true_iff in Hx. split.
    - intro Hc. apply reachable_b_true_iff in Hc.
      assert (reachable_b E x a = true) by (apply reachable_b_true_iff, (reach_incl Ed E); [ apply E_minus_incl | exact Hc ]).
      congruence.
    - intro Hc. apply reachable_b_true_iff in Hc.
      assert (Hxb : reachable E x b) by (apply (reach_incl Ed E); [ apply E_minus_incl | exact Hc ]).
      assert (reachable_b E x a = true) by (apply reachable_b_true_iff, (reach_trans E x b a); [ exact Hxb | exact Hba ]).
      congruence. }
  assert (Hb_ext : forall x y, In x (filter (fun x => negb (inO x)) V) ->
                    In y (filter (fun x => negb (inO x)) V) ->
                    reachable_b Ed x y = reachable_b E x y).
  { intros x y Hx Hy.
    apply filter_In in Hx. apply filter_In in Hy.
    destruct Hx as [_ Hxn]. destruct Hy as [_ Hyn].
    destruct (HccOd x Hxn) as [Hxna Hxnb]. destruct (HccOd y Hyn) as [Hyna Hynb].
    destruct (reachable_b Ed x y) eqn:H1; destruct (reachable_b E x y) eqn:H2;
      try reflexivity; exfalso.
    - assert (reachable_b E x y = true)
        by (apply reachable_b_true_iff, (reach_incl Ed E); [ apply E_minus_incl | apply reachable_b_true_iff; exact H1 ]).
      congruence.
    - apply reachable_b_true_iff in H2.
      apply (reachable_add_edge_iff E d x y Hd) in H2.
      destruct H2 as [H2 | [[H2a H2b] | [H3a H3b]]].
      + apply reachable_b_true_iff in H2. fold Ed in H2. congruence.
      + fold a in H2a. fold Ed in H2a. apply reachable_b_true_iff in H2a. congruence.
      + fold b in H3a. fold Ed in H3a. apply reachable_b_true_iff in H3a. congruence. }
  assert (Hcompl : count_classes (reachable_b E) (filter (fun x => negb (inO x)) V)
                  = count_classes (reachable_b Ed) (filter (fun x => negb (inO x)) V)).
  { unfold count_classes. f_equal. apply class_reps_ext_on. intros x y Hx Hy. symmetry.
    apply Hb_ext; assumption. }
  (* The `inO`-block splits, on the `Ed` side, into exactly two classes: `a`'s
     and `b`'s. *)
  assert (Hdich : forall x, In x V -> (inO x = true <-> (reachable_b Ed x a = true \/ reachable_b Ed x b = true))).
  { intros x Hx. unfold inO. split.
    - intro Hxa. apply reachable_b_true_iff in Hxa.
      apply (reachable_add_edge_iff E d x a Hd) in Hxa.
      destruct Hxa as [H1 | [[H2a H2b] | [H3a H3b]]].
      + left. apply reachable_b_true_iff. fold Ed in H1. exact H1.
      + left. apply reachable_b_true_iff. fold a in H2a. fold Ed in H2a. exact H2a.
      + right. apply reachable_b_true_iff. fold b in H3a. fold Ed in H3a. exact H3a.
    - intros [H | H].
      + apply reachable_b_true_iff. apply reachable_b_true_iff in H.
        apply (reach_incl Ed E); [ apply E_minus_incl | exact H ].
      + apply reachable_b_true_iff. apply reachable_b_true_iff in H.
        apply reachable_b_true_iff.
        assert (Hxb : reachable E x b) by (apply (reach_incl Ed E); [ apply E_minus_incl | exact H ]).
        apply reachable_b_true_iff, (reach_trans E x b a); [ exact Hxb | exact Hba ]. }
  set (inA := fun x => reachable_b Ed x a).
  assert (HccOfA : forall x y, In x (filter inO V) -> In y (filter inO V) ->
                     reachable_b Ed x y = true -> inA x = inA y).
  { intros x y Hx Hy Hxy. unfold inA.
    destruct (reachable_b Ed x a) eqn:Hxa; destruct (reachable_b Ed y a) eqn:Hya;
      try reflexivity; exfalso.
    - apply reachable_b_true_iff in Hxy, Hxa.
      assert (reachable_b Ed y a = true)
        by (apply reachable_b_true_iff, (reach_trans Ed y x a); [ apply reach_sym; exact Hxy | exact Hxa ]).
      congruence.
    - apply reachable_b_true_iff in Hxy, Hya.
      assert (reachable_b Ed x a = true)
        by (apply reachable_b_true_iff, (reach_trans Ed x y a); [ exact Hxy | exact Hya ]).
      congruence. }
  rewrite (count_classes_filter_split (reachable_b Ed) (reachable_b_refl Ed) inA (filter inO V) HccOfA
             (fun x y z _ _ _ => reachable_b_trans Ed x y z)) in HnumEd.
  assert (HblockA : count_classes (reachable_b Ed) (filter inA (filter inO V)) = 1%nat).
  { apply (count_classes_eq_1 (reachable_b Ed) (reachable_b_refl Ed)).
    - intro Hnil.
      assert (Hain : In a (filter inA (filter inO V))).
      { apply filter_In. split.
        - apply filter_In. split; [ apply nodup_In; exact Ha | unfold inO; apply reachable_b_refl ].
        - unfold inA; apply reachable_b_refl. }
      rewrite Hnil in Hain. destruct Hain.
    - intros x y Hx Hy. apply filter_In in Hx. apply filter_In in Hy.
      unfold inA in Hx, Hy. destruct Hx as [_ Hxa]. destruct Hy as [_ Hya].
      apply reachable_b_true_iff in Hxa, Hya. apply reachable_b_true_iff.
      apply (reach_trans Ed x a y); [ exact Hxa | apply reach_sym; exact Hya ]. }
  assert (HblockNA : count_classes (reachable_b Ed) (filter (fun x => negb (inA x)) (filter inO V)) = 1%nat).
  { apply (count_classes_eq_1 (reachable_b Ed) (reachable_b_refl Ed)).
    - intro Hnil.
      assert (Hbin : In b (filter (fun x => negb (inA x)) (filter inO V))).
      { apply filter_In. split.
        - apply filter_In. split.
          + apply nodup_In; exact Hb.
          + apply (proj2 (Hdich b (proj2 (nodup_In point_eq_dec (verts Ed) b) Hb))).
            right; apply reachable_b_refl.
        - unfold inA. apply negb_true_iff.
          destruct (reachable_b Ed b a) eqn:Hba' ; [ exfalso | reflexivity ].
          apply Hcut, reach_sym, reachable_b_true_iff. exact Hba'. }
      rewrite Hnil in Hbin. destruct Hbin.
    - intros x y Hx Hy. apply filter_In in Hx. apply filter_In in Hy.
      destruct Hx as [HxO Hxna]. destruct Hy as [HyO Hyna].
      unfold inA in Hxna, Hyna. apply negb_true_iff in Hxna, Hyna.
      apply filter_In in HxO. apply filter_In in HyO.
      destruct HxO as [HxV HxinO]. destruct HyO as [HyV HyinO].
      assert (Hxb : reachable_b Ed x b = true).
      { destruct (proj1 (Hdich x HxV) HxinO) as [Hcontra | Hgood];
          [ congruence | exact Hgood ]. }
      assert (Hyb : reachable_b Ed y b = true).
      { destruct (proj1 (Hdich y HyV) HyinO) as [Hcontra | Hgood];
          [ congruence | exact Hgood ]. }
      apply reachable_b_true_iff in Hxb, Hyb. apply reachable_b_true_iff.
      apply (reach_trans Ed x b y); [ exact Hxb | apply reach_sym; exact Hyb ]. }
  lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit: base case + transfer skeleton + [EF-1] + [EF-3], no       *)
(* Admitted/Axiom.                                                            *)
(* -------------------------------------------------------------------------- *)
Print Assumptions euler_characteristic_nil.
Print Assumptions cycle_components_eq.
Print Assumptions euler_transfer_bridge.
Print Assumptions euler_transfer_cycle.
Print Assumptions reachable_add_edge_iff.
Print Assumptions verts_incl_E_of_survivors.
Print Assumptions bridge_components_split.
