(* ============================================================================
   NetTopologySuite.Proofs.EulerWitness
   ----------------------------------------------------------------------------
   extract_rings_valid R5, face_twin_free closure: NON-VACUITY witnesses for the
   carried planar-Euler premise `EulerArrangement.euler_characteristic`.

   `euler_characteristic E := num_vertices E + num_faces E = num_edges E +
   2 * num_components E` is an irreducible genus-0 input, carried by design
   (see docs/face-twin-free-closure-plan.md §H5/H6).  This file does NOT
   discharge the general hypothesis; it proves it holds on concrete witnesses --
   the analogue of `EdgeConnectivity.single_edge_is_cut` /
   `triangle_2_connected` for `is_cut_edge` / `edge_2_connected` -- confirming
   the premise is correct and satisfiable.

   W1 (LANDED): single edge   V=2, F=1, E=1, C=1   (2+1 = 1+2*1).
   W2 (deferred): two disjoint edges -- would validate the `2*C` form (C=2).
   W3 (deferred): triangle    -- the canonical genus-0 face.
   See the §3 comment block at the end for the W2/W3 deferral rationale.

   W1 has SINGLETON outgoing fans, so `fstep` is determined without any
   coordinate arithmetic (the only sub-`lra` fact is the dart-order
   self-irreflexivity `dart_ltb d d = false`).  `num_faces`/`num_components` are
   driven through the high-level `ClassCount.count_classes_eq_1` (all darts /
   vertices in a single class) rather than raw `class_reps` unfolding.

   Pure dart + list + class-count combinatorics; no `Admitted` / `Axiom` /
   `Parameter`; allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import List Reals Lra Arith Lia.
From NTS.Proofs Require Import Distance Overlay OverlayGraph Dart DartAngularOrder
                               DartNext DartNextSpec DartFace EdgeConnectivity
                               ReachableDec PermCycleCount ClassCount MapCounts
                               EulerArrangement OrbitCycle.

Import ListNotations.
Local Open Scope nat_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Singleton-fan reduction: a degree-1 vertex forces `fstep d = twin d`.   *)
(* -------------------------------------------------------------------------- *)

Lemma dart_ltb_irrefl : forall x : Dart, dart_ltb x x = false.
Proof.
  intro x. destruct (dart_ltb x x) eqn:H; [ | reflexivity ].
  apply dart_ltb_spec in H. exfalso. exact (dart_lt_irrefl x H).
Qed.

Lemma next_self_singleton : forall x : Dart, next [x] x = x.
Proof.
  intro x. unfold next.
  assert (Hf : filter (fun e => dart_ltb x e) [x] = []).
  { cbn [filter]. rewrite dart_ltb_irrefl. reflexivity. }
  rewrite Hf. cbn [list_min fold_left]. reflexivity.
Qed.

Lemma fstep_of_singleton_fan : forall E d,
  outgoing (dtip d) (darts_of E) = [twin d] -> fstep (darts_of E) d = twin d.
Proof.
  intros E d H. unfold fstep. rewrite H. apply next_self_singleton.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  W1: a single edge `[(a,b)]`.                                            *)
(* -------------------------------------------------------------------------- *)

Section W1.
  Variables a b : Point.
  Hypothesis Hab : a <> b.

  Lemma w1_verts_nodup : nodup point_eq_dec (verts [(a, b)]) = [a; b].
  Proof.
    unfold verts. cbn [flat_map app fst snd].
    cbn [nodup]. destruct (in_dec point_eq_dec a [b]) as [Hin | _].
    - exfalso. cbn in Hin. destruct Hin as [H | H]; [ apply Hab; symmetry; exact H | destruct H ].
    - reflexivity.
  Qed.

  Lemma w1_num_vertices : num_vertices [(a, b)] = 2.
  Proof. unfold num_vertices. rewrite w1_verts_nodup. reflexivity. Qed.

  Lemma w1_num_edges : num_edges [(a, b)] = 1.
  Proof. reflexivity. Qed.

  (* Both endpoints are reachable in the single-edge graph (either order). *)
  Lemma w1_reachable : forall x y, In x [a; b] -> In y [a; b] -> reachable [(a, b)] x y.
  Proof.
    assert (Hab_r : reachable [(a, b)] a b).
    { apply reach_one. exists (a, b). split; [ left; reflexivity | left; split; reflexivity ]. }
    intros x y Hx Hy. cbn in Hx, Hy.
    destruct Hx as [<- | [<- | []]]; destruct Hy as [<- | [<- | []]].
    - apply reach_refl.
    - exact Hab_r.
    - apply reach_sym. exact Hab_r.
    - apply reach_refl.
  Qed.

  Lemma w1_num_components : num_components [(a, b)] = 1.
  Proof.
    unfold num_components, comp_reps. rewrite w1_verts_nodup.
    change (count_classes (reachable_b [(a, b)]) [a; b] = 1).
    apply count_classes_eq_1.
    - intro x. apply reachable_b_refl.
    - discriminate.
    - intros x y Hx Hy. apply reachable_b_true_iff. apply w1_reachable; assumption.
  Qed.

  (* The two darts of the edge swap under `fstep` (singleton fans). *)
  Lemma w1_darts : darts_of [(a, b)] = [(a, b); (b, a)].
  Proof. reflexivity. Qed.

  Lemma w1_outgoing_b : outgoing b (darts_of [(a, b)]) = [(b, a)].
  Proof.
    rewrite w1_darts. unfold outgoing. cbn [filter dbase fst snd].
    destruct (point_eq_dec a b) as [Heq | _]; [ exfalso; apply Hab; exact Heq | ].
    destruct (point_eq_dec b b) as [_ | Hne]; [ reflexivity | exfalso; apply Hne; reflexivity ].
  Qed.

  Lemma w1_outgoing_a : outgoing a (darts_of [(a, b)]) = [(a, b)].
  Proof.
    rewrite w1_darts. unfold outgoing. cbn [filter dbase fst snd].
    destruct (point_eq_dec a a) as [_ | Hne]; [ | exfalso; apply Hne; reflexivity ].
    destruct (point_eq_dec b a) as [Heq | _]; [ exfalso; apply Hab; symmetry; exact Heq | reflexivity ].
  Qed.

  Lemma w1_fstep_ab : fstep (darts_of [(a, b)]) (a, b) = (b, a).
  Proof.
    apply (fstep_of_singleton_fan [(a, b)] (a, b)).
    cbn [dtip twin fst snd]. exact w1_outgoing_b.
  Qed.

  Lemma w1_fstep_ba : fstep (darts_of [(a, b)]) (b, a) = (a, b).
  Proof.
    apply (fstep_of_singleton_fan [(a, b)] (b, a)).
    cbn [dtip twin fst snd]. exact w1_outgoing_a.
  Qed.

  (* All darts lie in a single `fstep`-orbit; proved directly via `existsb`
     (the small finite case), avoiding the closure/injectivity hypotheses of
     `same_orbit_b_complete`. *)
  Lemma w1_same_orbit_b : forall x y,
    In x (darts_of [(a, b)]) -> In y (darts_of [(a, b)]) ->
    same_orbit_b dart_eq_dec (fstep (darts_of [(a, b)])) (darts_of [(a, b)]) x y = true.
  Proof.
    intros x y Hx Hy. rewrite w1_darts in Hx, Hy. cbn in Hx, Hy.
    unfold same_orbit_b. apply existsb_exists.
    destruct Hx as [<- | [<- | []]]; destruct Hy as [<- | [<- | []]].
    - exists 0%nat. split; [ apply in_seq; cbn; lia | ].
      cbn [iter]. destruct (dart_eq_dec (a, b) (a, b)) as [_ | Hn]; [ reflexivity | exfalso; apply Hn; reflexivity ].
    - exists 1%nat. split; [ apply in_seq; cbn; lia | ].
      cbn [iter]. rewrite w1_fstep_ab.
      destruct (dart_eq_dec (b, a) (b, a)) as [_ | Hn]; [ reflexivity | exfalso; apply Hn; reflexivity ].
    - exists 1%nat. split; [ apply in_seq; cbn; lia | ].
      cbn [iter]. rewrite w1_fstep_ba.
      destruct (dart_eq_dec (a, b) (a, b)) as [_ | Hn]; [ reflexivity | exfalso; apply Hn; reflexivity ].
    - exists 0%nat. split; [ apply in_seq; cbn; lia | ].
      cbn [iter]. destruct (dart_eq_dec (b, a) (b, a)) as [_ | Hn]; [ reflexivity | exfalso; apply Hn; reflexivity ].
  Qed.

  Lemma w1_num_faces : num_faces [(a, b)] = 1.
  Proof.
    unfold num_faces, cycle_count, orbit_reps.
    change (count_classes (same_orbit_b dart_eq_dec (fstep (darts_of [(a, b)])) (darts_of [(a, b)]))
                          (darts_of [(a, b)]) = 1).
    apply count_classes_eq_1.
    - intro x. apply same_orbit_b_refl.
    - rewrite w1_darts. discriminate.
    - exact w1_same_orbit_b.
  Qed.

  Theorem w1_euler : euler_characteristic [(a, b)].
  Proof.
    unfold euler_characteristic.
    rewrite w1_num_vertices, w1_num_edges, w1_num_faces, w1_num_components.
    reflexivity.
  Qed.

End W1.

(* -------------------------------------------------------------------------- *)
(* §3  W2 (two disjoint edges) and W3 (triangle): DEFERRED.                    *)
(*                                                                            *)
(* W2 `[(a,b);(c,d)]` (V=4,E=2,F=2,C=2) would additionally validate the `2*C`  *)
(* coefficient (C=2).  Its structural facts are clean and singleton-fan based  *)
(* (the `fstep` swaps, the per-edge orbit/reachability blocks), and            *)
(* `num_components=2` is reachable via `ClassCount.count_classes_filter_split`  *)
(* (split [a;b;c;d] into the two edge blocks).  The blocker is `num_faces=2`:  *)
(* driving `cycle_count` past the nested `class_reps` needs `same_orbit_b`      *)
(* transitivity on the 4 darts, which routes through `same_orbit_b_complete`'s  *)
(* `fstep` closure + injectivity hypotheses -- a disproportionate amount of     *)
(* finite case-work for a non-vacuity witness.                                 *)
(*                                                                            *)
(* W3 `[(A,B);(B,C);(C,A)]` (V=3,E=3,F=2,C=1, the canonical genus-0 face) has   *)
(* DEGREE-2 vertices, so each `fstep` value needs a concrete `lra`/`nra`        *)
(* discharge on a `vcross`, and `num_faces=2` then needs the two 3-cycle face   *)
(* orbits hand-chained through the six `fstep` equations.                      *)
(*                                                                            *)
(* W1 above already establishes that `euler_characteristic` is correct and     *)
(* satisfiable on a concrete arrangement (the connected C=1 case).  W2/W3 are   *)
(* left as documented follow-ups; see docs/face-twin-free-closure-plan.md.     *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions w1_euler.
