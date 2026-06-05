(* ============================================================================
   NetTopologySuite.Proofs.OrbitCycle
   ----------------------------------------------------------------------------
   extract_rings_valid R5 / general assembler, slice 2e: the FINITENESS /
   return crux for face orbits (docs/extract-rings-proof-structure.md §5 step 2;
   docs/orbit-cycle.md).

   The §9 crux of the DCEL route is `face_orbit_finite`: iterating the face step
   `next o twin` from a dart eventually returns to it, so the face boundary is a
   finite closed walk.  This slice isolates and proves the PURE-COMBINATORIAL
   heart of that fact, free of any geometry:

       an INJECTIVE self-map of a FINITE set, iterated, cycles back to start.

   Concretely, for `f : A -> A` that maps a finite list `S` into itself
   (`Hclos`) and is injective on `S` (`Hinj`), with decidable equality on `A`:

     - `iter_in`        : every iterate of a point of `S` stays in `S`
                          (the orbit is contained in `S`, hence FINITE);
     - `iter_inj_on`    : every iterate `iter n` is injective on `S`;
     - `iter_pigeon`    : among `iter 0 d .. iter |S| d` two coincide (pigeonhole
                          into `S`);
     - `orbit_returns`  : there is `n >= 1` with `iter n d = d` -- the orbit is a
                          genuine CYCLE through `d`.

   Slice 2d gave exactly the injective-self-map-of-a-finite-fan hypotheses this
   needs.  Instantiating `f` with the dart face step `next o twin` (with its
   twin-closure + per-vertex `fan_ok` plumbing) is the next slice (2f); this one
   keeps the result abstract and reusable.

   Pure list + arithmetic; no `Admitted` / `Axiom` / `Parameter`; AXIOM-FREE
   (no classical reals here -- decidable equality is a hypothesis).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import List Arith Lia.

Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §0  A general list duplicate lemma (no geometry, no order).                 *)
(* -------------------------------------------------------------------------- *)

(* Appending a fresh element preserves `NoDup`. *)
Lemma NoDup_app_singleton :
  forall {A : Type} (l : list A) (x : A),
    NoDup l -> ~ In x l -> NoDup (l ++ [x]).
Proof.
  intros A l x. induction l as [| y ys IHl]; intros Hnd Hni; cbn.
  - constructor; [ intros [] | constructor ].
  - inversion Hnd as [| ? ? Hy Hnd' Heql]; subst.
    constructor.
    + intro Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * exact (Hy Hin).
      * destruct Hin as [He | []]. apply Hni. left. symmetry. exact He.
    + apply IHl; [ exact Hnd' | intro Hin; apply Hni; right; exact Hin ].
Qed.

(* If a `seq`-indexed family has no duplicates among its first `m` values, two
   distinct indices below `m` map to the same value.  (Constructive: the fresh
   element either repeats an earlier value, or the prefix already collides.) *)
Lemma seq_map_dup :
  forall {A : Type} (eqdec : forall a b : A, {a = b} + {a <> b})
         (g : nat -> A) (m : nat),
    ~ NoDup (map g (seq 0 m)) ->
    exists i j, (i < j < m)%nat /\ g i = g j.
Proof.
  intros A eqdec g. induction m as [| m IHm]; intros Hnd.
  - exfalso. apply Hnd. cbn. constructor.
  - rewrite seq_S, map_app in Hnd. cbn in Hnd.
    destruct (in_dec eqdec (g m) (map g (seq 0 m))) as [Hin | Hni].
    + (* g m repeats an earlier value *)
      apply in_map_iff in Hin. destruct Hin as [k [Hgk Hk]].
      apply in_seq in Hk. destruct Hk as [_ Hk]. cbn in Hk.
      exists k, m. split; [ split; [ exact Hk | apply Nat.lt_succ_diag_r ] | exact Hgk ].
    + (* g m is fresh: the prefix must already collide *)
      destruct IHm as [i [j [[Hi Hj] Hgij]]].
      * intro Hnd'. apply Hnd. apply NoDup_app_singleton; [ exact Hnd' | exact Hni ].
      * exists i, j. split; [ split; [ exact Hi | apply Nat.lt_lt_succ_r; exact Hj ] | exact Hgij ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §1  Iterating an injective self-map of a finite set.                        *)
(* -------------------------------------------------------------------------- *)

Section OrbitCycle.

  Context {A : Type}.
  Variable eqdec : forall a b : A, {a = b} + {a <> b}.
  Variable f : A -> A.
  Variable S : list A.
  Hypothesis Hclos : forall x, In x S -> In (f x) S.
  Hypothesis Hinj  : forall a b, In a S -> In b S -> f a = f b -> a = b.

  Fixpoint iter (n : nat) (x : A) : A :=
    match n with
    | O => x
    | Datatypes.S k => f (iter k x)
    end.

  (* The orbit stays inside `S` -- hence it is a finite set. *)
  Lemma iter_in : forall n x, In x S -> In (iter n x) S.
  Proof.
    induction n as [| n IHn]; intros x Hx; cbn.
    - exact Hx.
    - apply Hclos. apply IHn. exact Hx.
  Qed.

  Lemma iter_comp : forall a b x, iter (a + b) x = iter a (iter b x).
  Proof.
    induction a as [| a IHa]; intros b x; cbn.
    - reflexivity.
    - rewrite IHa. reflexivity.
  Qed.

  (* Each iterate is injective on `S` (a composite of maps injective on `S`). *)
  Lemma iter_inj_on :
    forall n a b, In a S -> In b S -> iter n a = iter n b -> a = b.
  Proof.
    induction n as [| n IHn]; intros a b Ha Hb Heq; cbn in Heq.
    - exact Heq.
    - assert (Hf : iter n a = iter n b).
      { apply (Hinj (iter n a) (iter n b));
          [ apply iter_in; exact Ha | apply iter_in; exact Hb | exact Heq ]. }
      apply IHn; [ exact Ha | exact Hb | exact Hf ].
  Qed.

  (* Pigeonhole: |S|+1 iterates into the |S|-element set `S` must collide. *)
  Lemma iter_pigeon :
    forall d, In d S -> exists i j, (i < j)%nat /\ iter i d = iter j d.
  Proof.
    intros d Hd.
    assert (Hdup : exists i j, (i < j < Datatypes.S (length S))%nat /\ iter i d = iter j d).
    { apply (seq_map_dup eqdec (fun k => iter k d) (Datatypes.S (length S))).
      intro Hnd.
      assert (Hincl : incl (map (fun k => iter k d) (seq 0 (Datatypes.S (length S)))) S).
      { intros y Hy. apply in_map_iff in Hy. destruct Hy as [k [Hk _]].
        subst y. apply iter_in. exact Hd. }
      pose proof (NoDup_incl_length Hnd Hincl) as Hle.
      rewrite length_map, length_seq in Hle. lia. }
    destruct Hdup as [i [j [[Hij _] Heq]]]. exists i, j. split; [ exact Hij | exact Heq ].
  Qed.

  (* THE crux: the orbit returns -- some positive iterate is the identity at d. *)
  Theorem orbit_returns :
    forall d, In d S -> exists n, (1 <= n)%nat /\ iter n d = d.
  Proof.
    intros d Hd. destruct (iter_pigeon d Hd) as [i [j [Hij Heq]]].
    exists (j - i). split; [ lia | ].
    assert (Hgoal : d = iter (j - i) d).
    { apply (iter_inj_on i d (iter (j - i) d)).
      - exact Hd.
      - apply iter_in; exact Hd.
      - rewrite <- iter_comp. replace (i + (j - i))%nat with j by lia. exact Heq. }
    symmetry. exact Hgoal.
  Qed.

End OrbitCycle.
