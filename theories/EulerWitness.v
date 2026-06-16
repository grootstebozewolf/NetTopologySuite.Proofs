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

   W1 (LANDED): single edge        V=2, F=1, E=1, C=1   (2+1 = 1+2*1).
   W2 (LANDED): two disjoint edges  V=4, F=2, E=2, C=2   (4+2 = 2+2*2) --
       validates the `2*C` coefficient (C=2), not `1+C`.
   W3 (deferred): triangle -- the canonical genus-0 face; see §4.

   W1/W2 have SINGLETON outgoing fans, so `fstep` is determined without any
   coordinate arithmetic (the only sub-`lra` fact is the dart-order
   self-irreflexivity `dart_ltb d d = false`).  `num_faces`/`num_components` are
   driven either through `ClassCount.count_classes_eq_1` (W1, single class) or
   bottom-up via `class_reps_cons` (W2), rewriting each `existsb`/relation guard
   by its proved value -- never by raw `class_reps`/`Rlt_dec` computation.

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

(* One-step unfold of `class_reps` -- lets us drive a concrete count bottom-up
   (rewriting each `existsb`/relation guard by its proved value) without the
   transitivity/closure premises of `count_classes_filter_split`. *)
Lemma class_reps_cons :
  forall (A : Type) (rb : A -> A -> bool) (x : A) (l : list A),
    class_reps rb (x :: l) =
      (if existsb (fun z => rb z x) (class_reps rb l)
       then class_reps rb l else x :: class_reps rb l).
Proof. reflexivity. Qed.

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
(* §3  W2: two disjoint edges `[(a,b);(c,d)]` -- validates the `2*C` form (C=2). *)
(* -------------------------------------------------------------------------- *)

Section W2.
  Variables a b c d : Point.
  Hypotheses (Hab : a <> b) (Hcd : c <> d)
             (Hac : a <> c) (Had : a <> d) (Hbc : b <> c) (Hbd : b <> d).

  Local Notation E2 := [(a, b); (c, d)] (only parsing).
  Local Notation D2 := [(a, b); (c, d); (b, a); (d, c)] (only parsing).

  Lemma w2_darts : darts_of E2 = [(a, b); (c, d); (b, a); (d, c)].
  Proof. reflexivity. Qed.

  Lemma w2_outgoing_b : outgoing b (darts_of E2) = [(b, a)].
  Proof.
    rewrite w2_darts. unfold outgoing. cbn [filter dbase fst snd].
    destruct (point_eq_dec a b) as [H|_]; [ exfalso; apply Hab; exact H | ].
    destruct (point_eq_dec c b) as [H|_]; [ exfalso; apply Hbc; symmetry; exact H | ].
    destruct (point_eq_dec b b) as [_|H]; [ | exfalso; apply H; reflexivity ].
    destruct (point_eq_dec d b) as [H|_]; [ exfalso; apply Hbd; symmetry; exact H | ].
    reflexivity.
  Qed.

  Lemma w2_outgoing_a : outgoing a (darts_of E2) = [(a, b)].
  Proof.
    rewrite w2_darts. unfold outgoing. cbn [filter dbase fst snd].
    destruct (point_eq_dec a a) as [_|H]; [ | exfalso; apply H; reflexivity ].
    destruct (point_eq_dec c a) as [H|_]; [ exfalso; apply Hac; symmetry; exact H | ].
    destruct (point_eq_dec b a) as [H|_]; [ exfalso; apply Hab; symmetry; exact H | ].
    destruct (point_eq_dec d a) as [H|_]; [ exfalso; apply Had; symmetry; exact H | ].
    reflexivity.
  Qed.

  Lemma w2_outgoing_d : outgoing d (darts_of E2) = [(d, c)].
  Proof.
    rewrite w2_darts. unfold outgoing. cbn [filter dbase fst snd].
    destruct (point_eq_dec a d) as [H|_]; [ exfalso; apply Had; exact H | ].
    destruct (point_eq_dec c d) as [H|_]; [ exfalso; apply Hcd; exact H | ].
    destruct (point_eq_dec b d) as [H|_]; [ exfalso; apply Hbd; exact H | ].
    destruct (point_eq_dec d d) as [_|H]; [ | exfalso; apply H; reflexivity ].
    reflexivity.
  Qed.

  Lemma w2_outgoing_c : outgoing c (darts_of E2) = [(c, d)].
  Proof.
    rewrite w2_darts. unfold outgoing. cbn [filter dbase fst snd].
    destruct (point_eq_dec a c) as [H|_]; [ exfalso; apply Hac; exact H | ].
    destruct (point_eq_dec c c) as [_|H]; [ | exfalso; apply H; reflexivity ].
    destruct (point_eq_dec b c) as [H|_]; [ exfalso; apply Hbc; exact H | ].
    destruct (point_eq_dec d c) as [H|_]; [ exfalso; apply Hcd; symmetry; exact H | ].
    reflexivity.
  Qed.

  Lemma w2_fstep_ab : fstep (darts_of E2) (a, b) = (b, a).
  Proof. apply (fstep_of_singleton_fan E2 (a, b)). cbn [dtip twin fst snd]. exact w2_outgoing_b. Qed.
  Lemma w2_fstep_ba : fstep (darts_of E2) (b, a) = (a, b).
  Proof. apply (fstep_of_singleton_fan E2 (b, a)). cbn [dtip twin fst snd]. exact w2_outgoing_a. Qed.
  Lemma w2_fstep_cd : fstep (darts_of E2) (c, d) = (d, c).
  Proof. apply (fstep_of_singleton_fan E2 (c, d)). cbn [dtip twin fst snd]. exact w2_outgoing_d. Qed.
  Lemma w2_fstep_dc : fstep (darts_of E2) (d, c) = (c, d).
  Proof. apply (fstep_of_singleton_fan E2 (d, c)). cbn [dtip twin fst snd]. exact w2_outgoing_c. Qed.

  Lemma w2_orbit_block1 : forall n x,
    In x [(a, b); (b, a)] -> In (iter (fstep (darts_of E2)) n x) [(a, b); (b, a)].
  Proof.
    induction n as [| n IH]; intros x Hx; [ exact Hx | ].
    cbn [iter]. specialize (IH x Hx).
    cbn [In] in IH. destruct IH as [<- | [<- | []]].
    - rewrite w2_fstep_ab. right; left; reflexivity.
    - rewrite w2_fstep_ba. left; reflexivity.
  Qed.

  Lemma w2_orbit_block2 : forall n x,
    In x [(c, d); (d, c)] -> In (iter (fstep (darts_of E2)) n x) [(c, d); (d, c)].
  Proof.
    induction n as [| n IH]; intros x Hx; [ exact Hx | ].
    cbn [iter]. specialize (IH x Hx).
    cbn [In] in IH. destruct IH as [<- | [<- | []]].
    - rewrite w2_fstep_cd. right; left; reflexivity.
    - rewrite w2_fstep_dc. left; reflexivity.
  Qed.

  Lemma w2_num_edges : num_edges E2 = 2.
  Proof. reflexivity. Qed.

  Lemma w2_verts_nodup : nodup point_eq_dec (verts E2) = [a; b; c; d].
  Proof.
    unfold verts. cbn [flat_map app fst snd]. cbn [nodup].
    destruct (in_dec point_eq_dec a [b; c; d]) as [H|_].
    { exfalso. cbn in H. destruct H as [H|[H|[H|[]]]]; congruence. }
    destruct (in_dec point_eq_dec b [c; d]) as [H|_].
    { exfalso. cbn in H. destruct H as [H|[H|[]]]; congruence. }
    destruct (in_dec point_eq_dec c [d]) as [H|_].
    { exfalso. cbn in H. destruct H as [H|[]]; congruence. }
    reflexivity.
  Qed.

  Lemma w2_num_vertices : num_vertices E2 = 4.
  Proof. unfold num_vertices. rewrite w2_verts_nodup. reflexivity. Qed.

  (* Reachability blocks: the two edges are disconnected. *)
  Lemma w2_block_inv : forall x y, reachable E2 x y -> (In x [a; b] <-> In y [a; b]).
  Proof.
    intros x y H. induction H as [u | u v w Hadj Hr IH]; [ reflexivity | ].
    rewrite <- IH. clear IH Hr w.
    destruct Hadj as [e [He Hor]]. cbn [In] in He.
    destruct He as [<- | [<- | []]]; cbn [fst snd] in Hor.
    - destruct Hor as [[<- <-] | [<- <-]]; cbn; tauto.
    - destruct Hor as [[<- <-] | [<- <-]]; cbn;
        (split; intro HH; destruct HH as [HH|[HH|[]]];
         exfalso; congruence).
  Qed.

  Lemma w2_reach_ab : reachable E2 a b.
  Proof. apply reach_one. exists (a, b). split; [ left; reflexivity | left; split; reflexivity ]. Qed.
  Lemma w2_reach_cd : reachable E2 c d.
  Proof. apply reach_one. exists (c, d). split; [ right; left; reflexivity | left; split; reflexivity ]. Qed.

  (* num_components = 2, driven bottom-up via class_reps_cons. *)
  Lemma w2_num_components : num_components E2 = 2.
  Proof.
    assert (Hdc : reachable_b E2 d c = true)
      by (apply reachable_b_true_iff; apply reach_sym; exact w2_reach_cd).
    assert (Hba : reachable_b E2 b a = true)
      by (apply reachable_b_true_iff; apply reach_sym; exact w2_reach_ab).
    assert (Hdb : reachable_b E2 d b = false).
    { destruct (reachable_b E2 d b) eqn:Hr; [ exfalso | reflexivity ].
      apply reachable_b_true_iff in Hr. apply w2_block_inv in Hr.
      destruct Hr as [_ Hbwd].
      assert (Hb : In b [a; b]) by (cbn; right; left; reflexivity).
      specialize (Hbwd Hb). cbn in Hbwd. destruct Hbwd as [Hd|[Hd|[]]]; congruence. }
    unfold num_components, comp_reps. rewrite w2_verts_nodup.
    assert (C1 : class_reps (reachable_b E2) [d] = [d]) by reflexivity.
    assert (C2 : class_reps (reachable_b E2) [c; d] = [d]).
    { rewrite class_reps_cons, C1. cbn [existsb]. rewrite Hdc. reflexivity. }
    assert (C3 : class_reps (reachable_b E2) [b; c; d] = [b; d]).
    { rewrite class_reps_cons, C2. cbn [existsb]. rewrite Hdb. reflexivity. }
    rewrite class_reps_cons, C3. cbn [existsb]. rewrite Hba. reflexivity.
  Qed.

  (* Orbit (face) relation values. *)
  Lemma w2_same_orbit_true : forall x y,
    fstep (darts_of E2) x = y ->
    same_orbit_b dart_eq_dec (fstep (darts_of E2)) (darts_of E2) x y = true.
  Proof.
    intros x y Hxy. unfold same_orbit_b. apply existsb_exists.
    exists 1%nat. split; [ apply in_seq; rewrite w2_darts; cbn; lia | ].
    cbn [iter]. rewrite Hxy.
    destruct (dart_eq_dec y y) as [_|Hn]; [ reflexivity | exfalso; apply Hn; reflexivity ].
  Qed.

  Lemma w2_same_orbit_false_12 : forall x y,
    In x [(a, b); (b, a)] -> In y [(c, d); (d, c)] ->
    same_orbit_b dart_eq_dec (fstep (darts_of E2)) (darts_of E2) x y = false.
  Proof.
    intros x y Hx Hy.
    destruct (same_orbit_b dart_eq_dec (fstep (darts_of E2)) (darts_of E2) x y) eqn:Hc;
      [ exfalso | reflexivity ].
    unfold same_orbit_b in Hc. apply existsb_exists in Hc.
    destruct Hc as [n [_ Hp]]. cbn beta in Hp.
    destruct (dart_eq_dec (iter (fstep (darts_of E2)) n x) y) as [Heq | _]; [ | discriminate Hp ].
    pose proof (w2_orbit_block1 n x Hx) as Ho. rewrite Heq in Ho.
    cbn [In] in Hy, Ho. destruct Hy as [Hy|[Hy|[]]]; destruct Ho as [Ho|[Ho|[]]]; congruence.
  Qed.

  Lemma w2_same_orbit_false_21 : forall x y,
    In x [(c, d); (d, c)] -> In y [(a, b); (b, a)] ->
    same_orbit_b dart_eq_dec (fstep (darts_of E2)) (darts_of E2) x y = false.
  Proof.
    intros x y Hx Hy.
    destruct (same_orbit_b dart_eq_dec (fstep (darts_of E2)) (darts_of E2) x y) eqn:Hc;
      [ exfalso | reflexivity ].
    unfold same_orbit_b in Hc. apply existsb_exists in Hc.
    destruct Hc as [n [_ Hp]]. cbn beta in Hp.
    destruct (dart_eq_dec (iter (fstep (darts_of E2)) n x) y) as [Heq | _]; [ | discriminate Hp ].
    pose proof (w2_orbit_block2 n x Hx) as Ho. rewrite Heq in Ho.
    cbn [In] in Hy, Ho. destruct Hy as [Hy|[Hy|[]]]; destruct Ho as [Ho|[Ho|[]]]; congruence.
  Qed.

  (* num_faces = 2, driven bottom-up via class_reps_cons. *)
  Lemma w2_num_faces : num_faces E2 = 2.
  Proof.
    assert (Hdcba : same_orbit_b dart_eq_dec (fstep D2) D2 (d, c) (b, a) = false)
      by (apply w2_same_orbit_false_21; cbn; tauto).
    assert (Hbacd : same_orbit_b dart_eq_dec (fstep D2) D2 (b, a) (c, d) = false)
      by (apply w2_same_orbit_false_12; cbn; tauto).
    assert (Hdccd : same_orbit_b dart_eq_dec (fstep D2) D2 (d, c) (c, d) = true)
      by (apply w2_same_orbit_true; apply w2_fstep_dc).
    assert (Hbaab : same_orbit_b dart_eq_dec (fstep D2) D2 (b, a) (a, b) = true)
      by (apply w2_same_orbit_true; apply w2_fstep_ba).
    unfold num_faces, cycle_count, orbit_reps.
    assert (HD : darts_of E2 = D2) by reflexivity. rewrite HD.
    (* drive class_reps innermost-out: rewrite each orbit guard then cbn the
       now-concrete inner list so the next existsb can reduce. *)
    cbn [class_reps existsb orb].
    rewrite Hdcba. cbn [existsb orb].
    rewrite Hbacd, Hdccd. cbn [existsb orb].
    rewrite Hbaab. reflexivity.
  Qed.

  Theorem w2_euler : euler_characteristic E2.
  Proof.
    unfold euler_characteristic.
    rewrite w2_num_vertices, w2_num_edges, w2_num_faces, w2_num_components.
    reflexivity.
  Qed.

End W2.

(* -------------------------------------------------------------------------- *)
(* §4  W3 (triangle): DEFERRED.                                                *)
(*                                                                            *)
(* The canonical genus-0 witness `[(A,B);(B,C);(C,A)]` (e.g. A=(0,0),B=(1,0),  *)
(* C=(0,1)) has V=3,E=3,F=2,C=1.  Unlike W1/W2 its vertices have DEGREE 2, so  *)
(* `next` must order two distinct darts by angle: each `fstep` value needs a   *)
(* concrete `lra`/`nra` discharge on a `vcross`, and `num_faces=2` then needs  *)
(* the two 3-cycle face orbits chained by hand through the six `fstep`         *)
(* equations.  Feasible but disproportionate for a non-vacuity witness; W1     *)
(* (C=1) and W2 (C=2) already validate the identity and the `2*C` coefficient. *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions w1_euler.
Print Assumptions w2_euler.
