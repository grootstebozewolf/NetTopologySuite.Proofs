(* ============================================================================
   NetTopologySuite.Proofs.DartNextInjective
   ----------------------------------------------------------------------------
   extract_rings_valid R5 / general assembler, slice 2d: INJECTIVITY of the
   cyclic `next` on the outgoing dart fan (docs/extract-rings-proof-structure.md
   §5 step 1; docs/dart-next-injective.md).

   Slice 2c (theories/DartNextSpec.v) pinned `next` down as the rotational
   successor: the minimal strictly-greater dart, or the global minimum on wrap.
   This slice proves the companion fact that makes `next` a CYCLIC PERMUTATION
   of the fan rather than an arbitrary self-map: it is INJECTIVE.

   The geometric content: in a cyclic angular order each dart has a UNIQUE
   PREDECESSOR.  If `m` is not the global minimum, its predecessor is the maximal
   dart below it (reached in the non-wrap branch); if `m` IS the global minimum,
   its predecessor is the (unique) global maximum (reached on wrap).  Either way
   at most one dart maps to `m`.  Formally we show two distinct fan darts cannot
   share a `next`-image, by cases on the strict order between them and on whether
   each has a successor (decided by emptiness of the strictly-greater filter, so
   no `classic` axiom is needed):

     - `next_no_collision` : `d1 < d2` -> `next d1 <> next d2`;
     - `next_injective`    : `next` is injective on a `fan_ok` fan.

   Injectivity is exactly what an orbit argument needs to know the `face_of` walk
   (`next o twin`) is a genuine CYCLE (every dart on a closed loop) rather than a
   "rho" shape with a tail.

   DELIBERATELY DEFERRED (the §9 crux): packaging injective-endo-on-a-finite-fan
   as a surjection / permutation, the `face_of` orbit of `next o twin` and its
   FINITENESS, then face orbit ⇒ `closed_chain` ⇒ `RingExtract.ring_of_chain`.

   Pure list + order combinatorics; no `Admitted` / `Axiom` / `Parameter`.
   Axioms: the allowlisted classical-reals pair (inherited from slices 2a–2c).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List.
From NTS.Proofs Require Import Vec Distance Direction Azimuth Dart
                               DartAngularOrder DartNext DartNextSpec.

Import ListNotations.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Deciding "d has a strictly-greater dart" by filter emptiness.           *)
(* -------------------------------------------------------------------------- *)

(* Empty strictly-greater filter  <=>  d is the fan maximum. *)
Lemma filter_succ_empty :
  forall F d, filter (fun e => dart_ltb d e) F = [] ->
    forall e, In e F -> ~ dart_lt d e.
Proof.
  intros F d Hf e He Hlt.
  assert (Hin : In e (filter (fun x => dart_ltb d x) F)).
  { apply filter_In. split; [ exact He | apply dart_ltb_spec; exact Hlt ]. }
  rewrite Hf in Hin. inversion Hin.
Qed.

(* A nonempty strictly-greater filter exhibits a successor. *)
Lemma filter_succ_ex :
  forall F d y ys, filter (fun e => dart_ltb d e) F = y :: ys ->
    exists e, In e F /\ dart_lt d e.
Proof.
  intros F d y ys Hf. exists y.
  assert (Hin : In y (filter (fun e => dart_ltb d e) F)) by (rewrite Hf; left; reflexivity).
  apply filter_In in Hin. destruct Hin as [HyF Hyb].
  split; [ exact HyF | apply dart_ltb_spec; exact Hyb ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Two distinct darts never share a `next`-image.                          *)
(* -------------------------------------------------------------------------- *)

(* The directed core of injectivity: if `d1 < d2`, they have different
   successors.  `d1` certainly has a successor (`d2` itself), so `next d1` is its
   minimal successor; we then split on whether `d2` has a successor and derive a
   contradiction from `next d1 = next d2` using irreflexivity / asymmetry. *)
Lemma next_no_collision :
  forall F, fan_ok F ->
    forall d1 d2, In d1 F -> In d2 F -> dart_lt d1 d2 -> next F d1 = next F d2 -> False.
Proof.
  intros F HF d1 d2 H1 H2 Hlt Heq.
  destruct (next_min_successor F d1 HF (ex_intro _ d2 (conj H2 Hlt)))
    as [_ [Hgt1 Hmin1]].
  destruct (Hmin1 d2 H2 Hlt) as [Em1 | Hlt1].
  - (* next d1 = d2 *)
    destruct (filter (fun e => dart_ltb d2 e) F) as [| y ys] eqn:Hf2.
    + (* d2 is the fan maximum: next d2 is the global minimum *)
      pose proof (filter_succ_empty F d2 Hf2) as Hmax2.
      destruct (next_wrap_least F d2 HF H2 Hmax2 d1 H1) as [Ew | Hw].
      * rewrite Em1 in Heq. rewrite Ew in Heq. rewrite <- Heq in Hlt.
        exact (dart_lt_irrefl d2 Hlt).
      * rewrite <- Heq in Hw. rewrite Em1 in Hw. exact (dart_lt_asym d1 d2 Hlt Hw).
    + (* d2 has a successor *)
      destruct (next_min_successor F d2 HF (filter_succ_ex F d2 y ys Hf2))
        as [_ [Hgt2 _]].
      rewrite <- Heq in Hgt2. rewrite Em1 in Hgt2. exact (dart_lt_irrefl d2 Hgt2).
  - (* dart_lt (next d1) d2 *)
    destruct (filter (fun e => dart_ltb d2 e) F) as [| y ys] eqn:Hf2.
    + pose proof (filter_succ_empty F d2 Hf2) as Hmax2.
      destruct (next_wrap_least F d2 HF H2 Hmax2 d1 H1) as [Ew | Hw].
      * rewrite Heq in Hgt1. rewrite Ew in Hgt1. exact (dart_lt_irrefl d1 Hgt1).
      * rewrite Heq in Hgt1. exact (dart_lt_asym d1 (next F d2) Hgt1 Hw).
    + destruct (next_min_successor F d2 HF (filter_succ_ex F d2 y ys Hf2))
        as [_ [Hgt2 _]].
      rewrite Heq in Hlt1. exact (dart_lt_asym d2 (next F d2) Hgt2 Hlt1).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Injectivity of `next` on the fan.                                       *)
(* -------------------------------------------------------------------------- *)

(* The payoff for the `face_of` walk: because `next` is injective on the fan,
   the orbit of `next o twin` cannot run a tail into a cycle (a "rho") -- the
   only shape an injective self-map of a finite set admits is disjoint cycles.
   So every dart lies on a closed loop and `face_of d` is a genuine face
   boundary returning to `d`.  (Closure/finiteness of that orbit is the next
   slice; this injectivity is the structural guarantee it rests on.) *)
Lemma next_injective :
  forall F, fan_ok F ->
    forall d1 d2, In d1 F -> In d2 F -> next F d1 = next F d2 -> d1 = d2.
Proof.
  intros F HF d1 d2 H1 H2 Heq.
  destruct (dart_eq_dec d1 d2) as [E | E]; [ exact E | exfalso ].
  destruct (dart_ltb_total_on F HF d1 d2 H1 H2) as [E' | [Hlt | Hgt]].
  - contradiction.
  - apply dart_ltb_spec in Hlt.
    exact (next_no_collision F HF d1 d2 H1 H2 Hlt Heq).
  - apply dart_ltb_spec in Hgt.
    apply (next_no_collision F HF d2 d1 H2 H1 Hgt). symmetry. exact Heq.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Surjectivity: `next` is a permutation of the (NoDup) fan.               *)
(* -------------------------------------------------------------------------- *)

(* `NoDup` is preserved by a map that is injective ON the list's elements. *)
Lemma NoDup_map_inj_on :
  forall (f : Dart -> Dart) (l : list Dart),
    NoDup l ->
    (forall a b, In a l -> In b l -> f a = f b -> a = b) ->
    NoDup (map f l).
Proof.
  induction l as [| x l IH]; intros Hnd Hinj; cbn; [ constructor | ].
  inversion Hnd as [| ? ? Hx Hnd' Heql]; subst.
  constructor.
  - (* f x is not already in map f l *)
    intros Hin. apply in_map_iff in Hin. destruct Hin as [y [Hfy Hy]].
    assert (x = y) by (apply Hinj; [ left; reflexivity | right; exact Hy | symmetry; exact Hfy ]).
    subst y. exact (Hx Hy).
  - apply IH; [ exact Hnd' | ]. intros a b Ha Hb. apply Hinj; right; assumption.
Qed.

(* An injective self-map of a finite fan with no duplicates is onto: every dart
   has a (unique, by injectivity) `next`-predecessor.  This makes `next` a cyclic
   permutation of the fan -- the standing assumption of the face-orbit walk. *)
Lemma next_surjective :
  forall F, fan_ok F -> NoDup F ->
    forall m, In m F -> exists d, In d F /\ next F d = m.
Proof.
  intros F HF Hnd m Hm.
  (* G = image of the fan under next; incl G F by orbit closure (next_in) *)
  assert (HinclGF : incl (map (next F) F) F).
  { intros y Hy. apply in_map_iff in Hy. destruct Hy as [d [Hd Hdin]].
    subst y. apply next_in. exact Hdin. }
  assert (HndG : NoDup (map (next F) F)).
  { apply NoDup_map_inj_on; [ exact Hnd | ].
    intros a b Ha Hb Hab. exact (next_injective F HF a b Ha Hb Hab). }
  assert (Hlen : (length F <= length (map (next F) F))%nat) by (rewrite length_map; lia).
  (* NoDup image of size >= |F|, included in F  =>  F included in the image *)
  pose proof (NoDup_length_incl HndG Hlen HinclGF) as HinclFG.
  specialize (HinclFG m Hm). apply in_map_iff in HinclFG.
  destruct HinclFG as [d [Hd Hdin]]. exists d. split; [ exact Hdin | exact Hd ].
Qed.
