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
            (Today only `euler_component_increase` gives this, and it ASSUMES
             euler at both E and E_minus -- must be replaced by a reachability
             /connectivity argument: removing a cut edge separates its
             endpoints' component into two.)
     [EF-2] cycle face merge:  ~ same_face-edge d =>
            num_faces (E_minus E d) = num_faces E - 1.
            (Today NumFacesSplice only covers the same_face F+1 case; the
             fstep-orbit MERGE for a non-bridge deletion is unproved.)
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

   The genuinely hard, planar-content lemma is the equivalence
   `same_face E d  <->  d is a cut edge of E` proven WITHOUT Euler -- i.e. the
   combinatorial Jordan step.  With it, [EF-1]/[EF-3] follow from connectivity
   and the induction closes.

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

From Stdlib Require Import List Arith Lia.
From NTS.Proofs Require Import Distance Overlay OverlayGraph EdgeConnectivity
                               EulerArrangement MapCounts ReachableDec EulerBridge.

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
(* Assumption audit: base case + transfer skeleton, no Admitted/Axiom.         *)
(* -------------------------------------------------------------------------- *)
Print Assumptions euler_characteristic_nil.
Print Assumptions cycle_components_eq.
Print Assumptions euler_transfer_bridge.
Print Assumptions euler_transfer_cycle.
