(* ============================================================================
   NetTopologySuite.Proofs.ExtractFaces
   ----------------------------------------------------------------------------
   extract_rings_valid R5 / general assembler, slice 3g: the EXTRACT REWIRE --
   a face-walk extractor over the labelled graph's op-surviving edges
   (docs/extract-rings-proof-structure.md §5 step 4 "extract re-defined";
   docs/extract-faces.md).

   `OverlayGraph.extract` filters `tg_edges g` by `edge_in_result op` and then
   FLATTENS the survivors into one pseudo-ring -- refuted as a valid_polygon
   source by `ExtractFlattenCounterexample.extract_unordered_not_valid`.  The
   DCEL machinery (slices 1-3c) built the correct alternative: turn the
   surviving edges into darts, walk `fstep` orbits, and emit one face polygon
   per orbit.  This slice performs that rewire and proves the resulting
   extractor satisfies the OBLIGATION SHAPE of the registered deferred proof
   `extract_rings_valid` (`forall poly, In poly (extract ...) ->
   valid_polygon poly`), hole-free, with no Jordan-curve residual:

     - `result_edges op g`   : the op-surviving edges of the labelled graph
                               (exactly `extract`'s filter, minus the flatten);
     - `result_darts op g`   : their half-edge (dart) view, `darts_of`;
     - `face_period D d`     : the first return time of the face step `fstep`
                               from `d` -- computed by bounded search, justified
                               by a BOUNDED orbit return (`orbit_returns_bounded`,
                               the pigeonhole bound `n <= length D` that
                               `OrbitCycle.orbit_returns` proves but does not
                               export);
     - `extract_faces op g`  : one hole-free face polygon per surviving dart;
     - `extract_faces_valid` : every polygon `extract_faces` emits is
                               `Overlay.valid_polygon` -- under the three named
                               structural hypotheses the noded pipeline supplies
                               (per-vertex `fan_ok` general position, pairwise
                               non-crossing of the survivors, faces of >= 3
                               darts i.e. no spurs/bigons);
     - `extract_faces_label_fidelity` : every edge of every emitted polygon is
                               (an orientation of) an edge the labelling kept --
                               the extractor invents no geometry.

   Each face is emitted once per boundary dart (deduplication is cosmetic for
   the validity obligation), and the unbounded outer face's traversal is also
   emitted -- selecting bounded/CCW faces is the orientation-classification
   refinement (slice 3e), orthogonal to validity.  Faces WITH holes remain on
   the analytic `hole_inside_outer` residual (§4).

   Pure dart + orbit + list combinatorics; no `Admitted` / `Axiom` /
   `Parameter`.  Axioms: the allowlisted classical-reals pair (via
   `dart_eq_dec` and the slice 2a-2d order machinery).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import List Arith Lia.
From NTS.Proofs Require Import Distance Overlay OverlayGraph BufferAssembly
                               RingExtract RingSimple Vec Direction Azimuth
                               Dart DartAngularOrder DartNext DartNextSpec
                               DartNextInjective OrbitCycle DartFace FaceChain
                               FaceRingSimple FacePolygon.

Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  The op-surviving edges and their dart view.                             *)
(* -------------------------------------------------------------------------- *)

(* The edges the labelling keeps for `op` -- the same filter as
   `OverlayGraph.extract`, WITHOUT the refuted flatten. *)
Definition result_edges (op : BooleanOp) (g : TopologyGraph) : list Edge :=
  map fst (filter (fun e => edge_in_result op (snd e)) (tg_edges g)).

(* Their half-edge view: both orientations of every surviving edge. *)
Definition result_darts (op : BooleanOp) (g : TopologyGraph) : list Dart :=
  darts_of (result_edges op g).

(* H4 (face_twin_free closure): the survivor edge list inherits distinctness from
   the underlying labelled-edge KEYS.  `result_edges` is `map fst` of a filtered
   sublist of `tg_edges g`, so once those keys are duplicate-free the survivors
   are too.  No-blast-radius: it observes the existing structure, changing no
   definitions. *)
Lemma NoDup_map_fst_filter :
  forall (A B : Type) (f : A -> B) (p : A -> bool) (l : list A),
    NoDup (map f l) -> NoDup (map f (filter p l)).
Proof.
  intros A B f p l. induction l as [| a l IH]; intro Hnd.
  - simpl. constructor.
  - cbn [map] in Hnd. inversion Hnd as [| x xs Hnotin Hnd' Heq]. subst.
    cbn [filter]. destruct (p a) eqn:Hpa.
    + cbn [map]. constructor.
      * intro Hin. apply Hnotin.
        rewrite in_map_iff in Hin. destruct Hin as [x [Hfx Hxin]].
        apply filter_In in Hxin. destruct Hxin as [Hxl _].
        rewrite in_map_iff. exists x. split; [ exact Hfx | exact Hxl ].
      * apply IH. exact Hnd'.
    + apply IH. exact Hnd'.
Qed.

Lemma NoDup_result_edges_of_keys :
  forall op g, NoDup (map fst (tg_edges g)) -> NoDup (result_edges op g).
Proof.
  intros op g H. unfold result_edges. apply NoDup_map_fst_filter. exact H.
Qed.

(* Membership unfolding: an edge survives iff some kept label carries it. *)
Lemma in_result_edges_iff :
  forall op g e,
    In e (result_edges op g) <->
    exists l, In (e, l) (tg_edges g) /\ edge_in_result op l = true.
Proof.
  intros op g e. unfold result_edges. rewrite in_map_iff. split.
  - intros [[e' l] [Hfst Hin]]. apply filter_In in Hin.
    destruct Hin as [Hin Hlab]. cbn in Hfst, Hlab. subst e'.
    exists l. split; assumption.
  - intros [l [Hin Hlab]]. exists (e, l). split; [ reflexivity | ].
    apply filter_In. split; [ exact Hin | exact Hlab ].
Qed.

(* A dart of the result is one of the two orientations of a surviving edge. *)
Lemma in_result_darts_iff :
  forall op g d,
    In d (result_darts op g) <->
    In d (result_edges op g) \/ In (twin d) (result_edges op g).
Proof.
  intros op g d. unfold result_darts, darts_of.
  rewrite in_app_iff, in_map_iff. split.
  - intros [H | [e [Heq He]]].
    + left. exact H.
    + right. rewrite <- Heq, twin_involutive. exact He.
  - intros [H | H].
    + left. exact H.
    + right. exists (twin d). split; [ apply twin_involutive | exact H ].
Qed.

(* The result dart set is a `darts_of`, so twin-closure is free: a per-vertex
   `fan_ok` hypothesis is all that `arrangement_ok` still needs. *)
Lemma result_darts_arrangement_ok :
  forall op g,
    (forall v, fan_ok (outgoing v (result_darts op g))) ->
    arrangement_ok (result_darts op g).
Proof.
  intros op g Hfan. unfold result_darts in *.
  apply arrangement_ok_darts_of. exact Hfan.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Bounded orbit return.                                                   *)
(*                                                                            *)
(* `OrbitCycle.orbit_returns` proves the return time is at most `length S`    *)
(* (the pigeonhole collides within the first |S|+1 iterates) but exports only *)
(* the existence.  The bounded form is what a COMPUTABLE period search needs,  *)
(* so we restate it here from the same exported ingredients.                   *)
(* -------------------------------------------------------------------------- *)

Lemma orbit_returns_bounded :
  forall (A : Type) (eqdec : forall a b : A, {a = b} + {a <> b})
         (f : A -> A) (L : list A),
    (forall x, In x L -> In (f x) L) ->
    (forall a b, In a L -> In b L -> f a = f b -> a = b) ->
    forall d, In d L ->
      exists n, (1 <= n)%nat /\ (n <= length L)%nat /\ iter f n d = d.
Proof.
  intros A eqdec f L Hclos Hinj d Hd.
  (* pigeonhole among the first |L|+1 iterates, keeping the bound *)
  assert (Hdup : exists i j,
             (i < j < Datatypes.S (length L))%nat /\ iter f i d = iter f j d).
  { apply (seq_map_dup eqdec (fun k => iter f k d) (Datatypes.S (length L))).
    intro Hnd.
    assert (Hincl : incl (map (fun k => iter f k d)
                              (seq 0 (Datatypes.S (length L)))) L).
    { intros y Hy. apply in_map_iff in Hy. destruct Hy as [k [Hk _]].
      subst y. apply (iter_in f L Hclos). exact Hd. }
    pose proof (NoDup_incl_length Hnd Hincl) as Hle.
    rewrite length_map, length_seq in Hle. lia. }
  destruct Hdup as [i [j [[Hij Hjlt] Heq]]].
  exists (j - i)%nat. split; [ lia | split; [ lia | ] ].
  (* peel the common prefix of i steps via injectivity of iterates *)
  assert (Hgoal : d = iter f (j - i) d).
  { apply (iter_inj_on f L Hclos Hinj i d (iter f (j - i) d)).
    - exact Hd.
    - apply (iter_in f L Hclos). exact Hd.
    - rewrite <- (iter_comp f i (j - i) d).
      replace (i + (j - i))%nat with j by lia. exact Heq. }
  symmetry. exact Hgoal.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The face period: first return time of the face step.                    *)
(* -------------------------------------------------------------------------- *)

(* First `k` in `l` with `iter (fstep D) k d = d`, else 0. *)
Fixpoint first_return (D : list Dart) (d : Dart) (l : list nat) : nat :=
  match l with
  | [] => O
  | k :: rest => if dart_eq_dec (iter (fstep D) k d) d
                 then k
                 else first_return D d rest
  end.

(* The face period: search return times `1 .. length D` -- enough by the
   pigeonhole bound of §2. *)
Definition face_period (D : list Dart) (d : Dart) : nat :=
  first_return D d (seq 1 (length D)).

(* If some candidate in `l` is a return time, `first_return` lands on a
   candidate in `l` that IS a return time (the first such). *)
Lemma first_return_finds :
  forall D d l,
    (exists k, In k l /\ iter (fstep D) k d = d) ->
    In (first_return D d l) l /\
    iter (fstep D) (first_return D d l) d = d.
Proof.
  intros D d l. induction l as [| k0 rest IH]; intros [k [Hk Hret]].
  - destruct Hk.
  - cbn [first_return].
    destruct (dart_eq_dec (iter (fstep D) k0 d) d) as [E | E].
    + split; [ left; reflexivity | exact E ].
    + destruct Hk as [-> | Hk].
      * contradiction.
      * destruct (IH (ex_intro _ k (conj Hk Hret))) as [Hin Hr].
        split; [ right; exact Hin | exact Hr ].
Qed.

(* Scan `m..n` for the least return time (matches `first_return` on `seq 1 n`). *)
Fixpoint min_return_scan (D : list Dart) (d : Dart) (rem m : nat) {struct rem} : nat :=
  match rem with
  | O => O
  | S rem' =>
      if dart_eq_dec (iter (fstep D) m d) d
      then m
      else min_return_scan D d rem' (S m)
  end.

Definition min_return (D : list Dart) (d : Dart) (m n : nat) : nat :=
  if Nat.leb m n then min_return_scan D d (S (n - m)) m else O.

Lemma min_return_scan_le :
  forall D d rem m k,
    (m <= k < m + rem)%nat ->
    iter (fstep D) k d = d ->
    (min_return_scan D d rem m <= k)%nat.
Proof.
  intros D d rem m k Hrange Hret.
  revert D m Hrange Hret.
  induction rem as [| rem' IHrem']; intros D m [Hm Hk] Hret.
  - lia.
  - cbn [min_return_scan].
    destruct (dart_eq_dec (iter (fstep D) m d) d) as [Em | Em].
    + subst. exact Hm.
    + assert (Hm' : (S m <= k < S m + rem')%nat).
      { split.
        - destruct (Nat.eq_dec m k) as [-> | Hneq]; [ exfalso; apply Em; exact Hret | lia ].
        - lia. }
      apply (IHrem' D (S m) Hm' Hret).
Qed.

Lemma min_return_le :
  forall D d m n k,
    (m <= k <= n)%nat ->
    iter (fstep D) k d = d ->
    (min_return D d m n <= k)%nat.
Proof.
  intros D d m n k Hrange Hret.
  unfold min_return.
  destruct (Nat.leb m n) eqn:Hleb; [| lia].
  apply Nat.leb_le in Hleb.
  apply (min_return_scan_le D d (S (n - m)) m k).
  - destruct Hrange. lia.
  - exact Hret.
Qed.

Lemma first_return_min_return_scan :
  forall D d m n,
    first_return D d (seq m n) = min_return_scan D d n m.
Proof.
  intros D d m n.
  revert D m. induction n as [| n' IHn']; intros D m.
  - reflexivity.
  - cbn [first_return seq min_return_scan].
    destruct (dart_eq_dec (iter (fstep D) m d) d) as [E | E].
    + reflexivity.
    + rewrite IHn'. reflexivity.
Qed.

Lemma first_return_min_return :
  forall D d n, (1 <= n)%nat -> first_return D d (seq 1 n) = min_return D d 1 n.
Proof.
  intros D d n Hn.
  unfold min_return.
  assert (Hleb : Nat.leb 1 n = true) by (apply Nat.leb_le; exact Hn).
  rewrite Hleb.
  rewrite first_return_min_return_scan.
  destruct n as [| n']; [ lia | destruct n' as [| n'']; reflexivity ].
Qed.

(* On a well-formed arrangement the period is a genuine positive return time:
   `face_orbit_finite`'s return happens within `length D` steps (§2), so the
   bounded search cannot miss. *)
Lemma face_period_spec :
  forall D, arrangement_ok D -> forall d, In d D ->
    (1 <= face_period D d)%nat /\
    iter (fstep D) (face_period D d) d = d.
Proof.
  intros D Hok d Hd.
  destruct (orbit_returns_bounded Dart dart_eq_dec (fstep D) D
              (fun x Hx => fstep_in D x (proj1 Hok) Hx)
              (fstep_inj D Hok) d Hd) as [n [Hn1 [Hn2 Hret]]].
  assert (Hfind : In (face_period D d) (seq 1 (length D)) /\
                  iter (fstep D) (face_period D d) d = d).
  { apply first_return_finds. exists n.
    split; [ apply in_seq; lia | exact Hret ]. }
  destruct Hfind as [Hin Hr]. split; [ | exact Hr ].
  apply in_seq in Hin. lia.
Qed.

Lemma face_period_bounded :
  forall D d,
    arrangement_ok D ->
    In d D ->
    (face_period D d <= length D)%nat.
Proof.
  intros D d Hok Hd.
  destruct (orbit_returns_bounded Dart dart_eq_dec (fstep D) D
              (fun x Hx => fstep_in D x (proj1 Hok) Hx)
              (fstep_inj D Hok) d Hd) as [n [Hn1 [Hn2 Hret]]].
  assert (Hfind : In (face_period D d) (seq 1 (length D)) /\
                  iter (fstep D) (face_period D d) d = d).
  { apply first_return_finds. exists n.
    split; [ apply in_seq; lia | exact Hret ]. }
  destruct Hfind as [Hin _]. apply in_seq in Hin. lia.
Qed.

Lemma face_period_no_early_return :
  forall D d j,
    arrangement_ok D ->
    In d D ->
    (1 <= j < face_period D d)%nat ->
    iter (fstep D) j d <> d.
Proof.
  intros D d j Hok Hd [H1 Hj] contra.
  assert (Hfpl := face_period_bounded D d Hok Hd).
  assert (Hjn : (1 <= j <= length D)%nat) by lia.
  assert (Hlen : (1 <= length D)%nat) by lia.
  assert (Hle := min_return_le D d 1 (length D) j Hjn contra).
  rewrite <- first_return_min_return in Hle by exact Hlen.
  unfold face_period in Hj, Hle. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The face extractor.                                                     *)
(* -------------------------------------------------------------------------- *)

(* The hole-free face polygon spawned by a dart: walk its face orbit for one
   period and package the traced ring (slice 3c). *)
Definition face_polygon_at (D : list Dart) (d : Dart) : Polygon :=
  face_polygon D d (face_period D d).

(* THE REWIRE: filter the labelled edges by `edge_in_result op` (as
   `OverlayGraph.extract` does), then emit one face polygon per surviving dart
   -- tracing face walks instead of the flatten that
   `ExtractFlattenCounterexample.extract_unordered_not_valid` refutes (that
   counterexample remains the RED witness against `OverlayGraph.extract`,
   which this definition supersedes as the `valid_polygon` source). *)
Definition extract_faces (op : BooleanOp) (g : TopologyGraph) : Geometry :=
  map (face_polygon_at (result_darts op g)) (result_darts op g).

(* Sanity: the empty graph extracts to the empty geometry. *)
Lemma extract_faces_empty_graph :
  forall op, extract_faces op empty_graph = [].
Proof. intros op. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Headline: every extracted polygon is valid.                             *)
(* -------------------------------------------------------------------------- *)

(* The no-spur condition of the fully-noded arrangement: every face has at
   least three darts (no isolated dangling edge walks of period 1 or 2). *)
Definition no_short_faces (D : list Dart) : Prop :=
  forall d, In d D -> (3 <= face_period D d)%nat.

(* The obligation shape of the registered deferred `extract_rings_valid`
   (`theories-flocq/OverlayBridge.v`), discharged for the face extractor in
   the hole-free regime: under the three structural hypotheses the noded
   pipeline supplies -- per-vertex general position (`fan_ok`), pairwise
   non-crossing survivors (`fully_intersected`'s noding guarantee), and no
   spurs -- EVERY polygon `extract_faces` emits is `valid_polygon`, with no
   Jordan-curve residual. *)
Theorem extract_faces_valid :
  forall op g,
    (forall v, fan_ok (outgoing v (result_darts op g))) ->
    pairwise_no_proper_cross (result_darts op g) ->
    no_short_faces (result_darts op g) ->
    forall poly, In poly (extract_faces op g) -> valid_polygon poly.
Proof.
  intros op g Hfan Hpw Hmin poly Hin.
  assert (Hok : arrangement_ok (result_darts op g))
    by (apply result_darts_arrangement_ok; exact Hfan).
  unfold extract_faces in Hin. apply in_map_iff in Hin.
  destruct Hin as [d [Hpoly Hd]]. subst poly.
  destruct (face_period_spec (result_darts op g) Hok d Hd) as [_ Hret].
  unfold face_polygon_at.
  apply (face_polygon_valid (result_darts op g) Hok Hpw d Hd
           (face_period (result_darts op g) d)).
  - apply Hmin. exact Hd.
  - exact Hret.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Label fidelity: the extractor invents no geometry.                      *)
(* -------------------------------------------------------------------------- *)

(* Every edge of every emitted polygon is a surviving dart. *)
Theorem extract_faces_edges_subset :
  forall op g,
    (forall v, fan_ok (outgoing v (result_darts op g))) ->
    forall poly, In poly (extract_faces op g) ->
      forall e, In e (ring_edges (outer_ring poly)) ->
        In e (result_darts op g).
Proof.
  intros op g Hfan poly Hin e He.
  assert (Hok : arrangement_ok (result_darts op g))
    by (apply result_darts_arrangement_ok; exact Hfan).
  unfold extract_faces in Hin. apply in_map_iff in Hin.
  destruct Hin as [d [Hpoly Hd]]. subst poly.
  unfold face_polygon_at, face_polygon in He. cbn [outer_ring] in He.
  destruct (face_period_spec (result_darts op g) Hok d Hd) as [Hge1 Hret].
  rewrite (ring_edges_of_closed_chain _
             (face_chain_closed_chain (result_darts op g) Hok d Hd
                (face_period (result_darts op g) d) Hge1 Hret)) in He.
  exact (face_chain_subset (result_darts op g) (proj1 Hok)
           (face_period (result_darts op g) d) d Hd e He).
Qed.

(* ... and hence (an orientation of) an edge the labelling kept for `op`:
   the assembled rings trace ONLY result edges -- the semantic bridge from
   the face extractor back to `edge_in_result`. *)
Corollary extract_faces_label_fidelity :
  forall op g,
    (forall v, fan_ok (outgoing v (result_darts op g))) ->
    forall poly, In poly (extract_faces op g) ->
      forall e, In e (ring_edges (outer_ring poly)) ->
        exists l, (In (e, l) (tg_edges g) \/ In (twin e, l) (tg_edges g)) /\
                  edge_in_result op l = true.
Proof.
  intros op g Hfan poly Hp e He.
  pose proof (extract_faces_edges_subset op g Hfan poly Hp e He) as Hd.
  apply in_result_darts_iff in Hd.
  destruct Hd as [Hd | Hd]; apply in_result_edges_iff in Hd;
    destruct Hd as [l [Hin Hlab]]; exists l.
  - split; [ left; exact Hin | exact Hlab ].
  - split; [ right; exact Hin | exact Hlab ].
Qed.
