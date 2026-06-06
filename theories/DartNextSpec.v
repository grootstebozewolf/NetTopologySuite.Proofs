(* ============================================================================
   NetTopologySuite.Proofs.DartNextSpec
   ----------------------------------------------------------------------------
   extract_rings_valid R5 / general assembler, slice 2c: the rotational-successor
   CORRECTNESS spec of `next` (docs/extract-rings-proof-structure.md §5 step 1;
   docs/dart-next-spec.md).

   Slice 2b (theories/DartNext.v) defined `next` and proved it WELL-DEFINED
   (`next_in` / `next_base` / `next_advances`) -- but left its defining property
   (that it picks the MINIMAL strictly-greater dart, and on wrap the global
   minimum) as a deferred obligation, because the `fold_left` minimum is only a
   true minimum when the comparator is a strict TOTAL order on the fan, which
   needs transitivity + totality threaded through the fold.

   This slice supplies exactly that, under a `fan_ok` hypothesis (the fan is
   PROPER -- every dart has a nonzero direction -- and in GENERAL POSITION --
   distinct darts have non-parallel directions, the noded-arrangement guarantee
   from slice 2a):

     - `dart_eq_dec`                      : decidable dart equality (classical R);
     - `dart_ltb_irrefl/_trans_on/_total_on` : the slice-2a order, on the fan,
       in boolean form;
     - `fold_min_lb` / `list_min_lb`      : `list_min` returns a genuine LOWER
       BOUND of the list (the fold-minimum is correct under a strict total order);
     - `next_min_successor`               : when `d` is not the fan maximum,
       `next F d` is THE minimal strictly-greater dart (a successor, and `<=`
       every successor);
     - `next_wrap_least`                  : when `d` IS the fan maximum, `next F d`
       is the global minimum (the wrap-around).

   Together these pin `next` down as the genuine rotational successor.

   DELIBERATELY DEFERRED (slice 2d / §9 crux): `next` INJECTIVITY / that it is a
   cyclic permutation of the fan, and the `face_of` orbit of `next o twin` + its
   FINITENESS.

   Pure list + order combinatorics; no `Admitted` / `Axiom` / `Parameter`.
   Axioms: the allowlisted classical-reals pair (via the real-order decisions and
   `Req_EM_T` reused here).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Vec Distance Direction Azimuth Dart DartAngularOrder DartNext.

Import ListNotations.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Decidable dart equality (light, from classical real-equality).          *)
(* -------------------------------------------------------------------------- *)

Definition pt_eq_dec (p q : Point) : {p = q} + {p <> q}.
Proof.
  destruct p as [px1 py1], q as [px2 py2].
  destruct (Req_EM_T px1 px2) as [Hx | Hx];
  destruct (Req_EM_T py1 py2) as [Hy | Hy].
  - left. subst. reflexivity.
  - right. intro E. inversion E. contradiction.
  - right. intro E. inversion E. contradiction.
  - right. intro E. inversion E. contradiction.
Defined.

Definition dart_eq_dec (d e : Dart) : {d = e} + {d <> e}.
Proof.
  destruct d as [d1 d2], e as [e1 e2].
  destruct (pt_eq_dec d1 e1) as [H1 | H1];
  destruct (pt_eq_dec d2 e2) as [H2 | H2].
  - left. subst. reflexivity.
  - right. intro E. inversion E. contradiction.
  - right. intro E. inversion E. contradiction.
  - right. intro E. inversion E. contradiction.
Defined.

(* -------------------------------------------------------------------------- *)
(* §2  The fan is well-formed: proper + general position.                      *)
(* -------------------------------------------------------------------------- *)

(* `fan_ok F`: every dart has a real direction, and distinct darts point in
   distinct directions.  A noded arrangement's outgoing fan satisfies this. *)
Definition fan_ok (F : list Dart) : Prop :=
  (forall d, In d F -> proper_dart d)
  /\ (forall d e, In d F -> In e F -> d <> e -> ~ parallel (ddir d) (ddir e)).

(* -------------------------------------------------------------------------- *)
(* §3  The boolean order, restricted to the fan, is a strict total order.      *)
(* -------------------------------------------------------------------------- *)

Lemma dart_ltb_irrefl : forall d, dart_ltb d d = false.
Proof.
  intros d. destruct (dart_ltb d d) eqn:E; [ | reflexivity ].
  apply dart_ltb_spec in E. exfalso. exact (dart_lt_irrefl d E).
Qed.

Lemma dart_ltb_trans_on :
  forall F, fan_ok F ->
    forall a b c, In a F -> In b F -> In c F ->
      dart_ltb a b = true -> dart_ltb b c = true -> dart_ltb a c = true.
Proof.
  intros F [Hprop Hgp] a b c Ha Hb Hc Hab Hbc.
  apply dart_ltb_spec in Hab. apply dart_ltb_spec in Hbc.
  apply dart_ltb_spec.
  assert (Hac : a <> c).
  { intro E. subst c. exact (dart_lt_asym a b Hab Hbc). }
  apply (dart_lt_trans a b c);
    [ apply Hprop | apply Hprop | apply Hprop | apply Hgp | | ]; auto.
Qed.

Lemma dart_ltb_total_on :
  forall F, fan_ok F ->
    forall a b, In a F -> In b F ->
      a = b \/ dart_ltb a b = true \/ dart_ltb b a = true.
Proof.
  intros F [Hprop Hgp] a b Ha Hb.
  destruct (dart_eq_dec a b) as [E | E]; [ left; exact E | right ].
  assert (Hnp : ~ parallel (ddir a) (ddir b)) by (apply Hgp; auto).
  destruct (dir_lt_total (ddir a) (ddir b) Hnp) as [H | H].
  - left. apply dart_ltb_spec. exact H.
  - right. apply dart_ltb_spec. exact H.
Qed.

(* The three properties bundled on the elements of a list (irreflexivity is
   unconditional, so it is not bundled). *)
Definition sto_on (L : list Dart) : Prop :=
  (forall a b c, In a L -> In b L -> In c L ->
     dart_ltb a b = true -> dart_ltb b c = true -> dart_ltb a c = true)
  /\ (forall a b, In a L -> In b L ->
     a = b \/ dart_ltb a b = true \/ dart_ltb b a = true).

Lemma fan_ok_sto : forall F, fan_ok F -> sto_on F.
Proof.
  intros F HF. split.
  - intros a b c. apply (dart_ltb_trans_on F HF).
  - intros a b. apply (dart_ltb_total_on F HF).
Qed.

Lemma sto_on_subset :
  forall F G, sto_on F -> (forall x, In x G -> In x F) -> sto_on G.
Proof.
  intros F G [Htr Hto] Hsub. split.
  - intros a b c Ha Hb Hc. apply Htr; auto.
  - intros a b Ha Hb. apply Hto; auto.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  `list_min` is a genuine lower bound under a strict total order.         *)
(* -------------------------------------------------------------------------- *)

(* The fold-minimum dominates every element it has seen.  Under transitivity +
   totality the discarded head can never sneak below the running minimum. *)
Lemma fold_min_lb :
  forall l d0,
    (forall a b c, In a (d0 :: l) -> In b (d0 :: l) -> In c (d0 :: l) ->
       dart_ltb a b = true -> dart_ltb b c = true -> dart_ltb a c = true) ->
    (forall a b, In a (d0 :: l) -> In b (d0 :: l) ->
       a = b \/ dart_ltb a b = true \/ dart_ltb b a = true) ->
    forall x, In x (d0 :: l) -> dart_ltb x (fold_left min_step l d0) = false.
Proof.
  induction l as [| a l IH]; intros d0 Htr Hto x Hx.
  - (* l = [] : the minimum is d0 itself *)
    destruct Hx as [<- | []]. cbn. apply dart_ltb_irrefl.
  - (* l = a :: l : recurse on seed d0' = min_step d0 a *)
    cbn [fold_left].
    remember (min_step d0 a) as d0' eqn:Hd0'.
    remember (fold_left min_step l d0') as m eqn:Hm.
    (* d0' is d0 or a, hence in the full list *)
    assert (Hd0'in : In d0' (d0 :: a :: l)).
    { rewrite Hd0'. unfold min_step.
      destruct (dart_ltb a d0); [ right; left; reflexivity | left; reflexivity ]. }
    (* membership weakening: d0' :: l  is contained in  d0 :: a :: l *)
    assert (Hsub : forall y, In y (d0' :: l) -> In y (d0 :: a :: l)).
    { intros y [Hy | Hy]; [ subst y; exact Hd0'in | right; right; exact Hy ]. }
    (* the hypotheses transport to the sublist d0' :: l *)
    assert (Htr' : forall p q r, In p (d0' :: l) -> In q (d0' :: l) -> In r (d0' :: l) ->
       dart_ltb p q = true -> dart_ltb q r = true -> dart_ltb p r = true).
    { intros p q r Hp Hq Hr Hpq Hqr.
      apply (Htr p q r); [ apply Hsub; exact Hp | apply Hsub; exact Hq
                         | apply Hsub; exact Hr | exact Hpq | exact Hqr ]. }
    assert (Hto' : forall p q, In p (d0' :: l) -> In q (d0' :: l) ->
       p = q \/ dart_ltb p q = true \/ dart_ltb q p = true).
    { intros p q Hp Hq. apply (Hto p q); [ apply Hsub; exact Hp | apply Hsub; exact Hq ]. }
    pose proof (IH d0' Htr' Hto') as IHm0.
    (* re-express the IH in terms of m *)
    assert (IHm : forall y, In y (d0' :: l) -> dart_ltb y m = false).
    { intros y Hy. rewrite Hm. apply IHm0. exact Hy. }
    (* m is itself in the full list *)
    assert (HmIn : In m (d0 :: a :: l)).
    { destruct (fold_min_in l d0') as [H | H]; rewrite <- Hm in H.
      - rewrite H. exact Hd0'in.
      - right; right; exact H. }
    (* show both candidate heads d0 and a are dominated, then conclude for x *)
    assert (Hd0 : dart_ltb d0 m = false).
    { destruct (dart_ltb a d0) eqn:Ead.
      - (* d0' = a : suppose d0 < m, then a < d0 < m contradicts IHm a *)
        destruct (dart_ltb d0 m) eqn:Edm; [ | reflexivity ].
        assert (Ham : dart_ltb a m = true).
        { apply (Htr a d0 m); [ right; left; reflexivity | left; reflexivity
                              | exact HmIn | exact Ead | exact Edm ]. }
        assert (Haf : dart_ltb a m = false).
        { apply IHm. left. rewrite Hd0'. unfold min_step. rewrite Ead. reflexivity. }
        rewrite Ham in Haf; discriminate.
      - (* d0' = d0 : IHm covers d0 directly *)
        apply IHm. left. rewrite Hd0'. unfold min_step. rewrite Ead. reflexivity. }
    assert (Ha : dart_ltb a m = false).
    { destruct (dart_ltb a d0) eqn:Ead.
      - (* d0' = a : IHm covers a directly *)
        apply IHm. left. rewrite Hd0'. unfold min_step. rewrite Ead. reflexivity.
      - (* d0' = d0 : use totality a vs d0 *)
        destruct (dart_ltb a m) eqn:Eam; [ | reflexivity ].
        destruct (Hto a d0 ltac:(right; left; reflexivity) ltac:(left; reflexivity))
          as [Eq | [Hlt | Hgt]].
        + (* a = d0 : then a < m = d0 < m, but Hd0 says false *)
          rewrite Eq in Eam. rewrite Eam in Hd0; discriminate.
        + (* a < d0 : contradicts Ead = false *)
          rewrite Hlt in Ead; discriminate.
        + (* d0 < a < m -> d0 < m, contradicts Hd0 *)
          assert (Hdm : dart_ltb d0 m = true).
          { apply (Htr d0 a m); [ left; reflexivity | right; left; reflexivity
                                | exact HmIn | exact Hgt | exact Eam ]. }
          rewrite Hdm in Hd0; discriminate. }
    (* conclude for x : it is d0, a, or in l (the last covered by IHm) *)
    destruct Hx as [<- | [<- | Hx]].
    + exact Hd0.
    + exact Ha.
    + apply IHm. right. exact Hx.
Qed.

Lemma list_min_lb :
  forall L m, sto_on L -> list_min L = Some m ->
    forall x, In x L -> dart_ltb x m = false.
Proof.
  intros [| d0 rest] m [Htr Hto] Hlm x Hx; cbn in Hlm; [ discriminate | ].
  injection Hlm as <-. apply (fold_min_lb rest d0 Htr Hto x Hx).
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  `next` is the rotational successor.                                     *)
(* -------------------------------------------------------------------------- *)

(* These pin down `DartNext.next` (the rotational successor on a `list Dart`)
   when that list is an outgoing fan `Dart.outgoing v D` satisfying `fan_ok`:
   the minimal strictly-greater dart around the vertex `v`, wrapping to the
   global minimum at the fan maximum.  Together with slice 2b's `next_in` /
   `next_base`, they are the angular semantics the `face_of` walk (`next o twin`)
   and its finiteness -- the next slice's target -- will iterate. *)

(* Non-wrap case: when a strictly-greater dart exists, `next F d` is one of them
   and is `<=` every strictly-greater dart -- i.e. THE minimal successor. *)
Lemma next_min_successor :
  forall F d, fan_ok F ->
    (exists e, In e F /\ dart_lt d e) ->
    In (next F d) F
    /\ dart_lt d (next F d)
    /\ (forall e, In e F -> dart_lt d e -> next F d = e \/ dart_lt (next F d) e).
Proof.
  intros F d HF [e0 [He0 He0lt]].
  set (S := filter (fun x => dart_ltb d x) F).
  assert (HinS0 : In e0 S).
  { apply filter_In. split; [ exact He0 | apply dart_ltb_spec; exact He0lt ]. }
  (* S is nonempty, so its minimum exists and is `next F d` *)
  assert (Hns : list_min S <> None).
  { intro Hn. apply list_min_none_iff in Hn. rewrite Hn in HinS0. exact HinS0. }
  destruct (list_min S) as [m |] eqn:Hm; [ | exfalso; apply Hns; reflexivity ].
  assert (Hnext : next F d = m).
  { unfold next. fold S. rewrite Hm. reflexivity. }
  assert (HmS : In m S) by (apply (list_min_in S m Hm)).
  assert (HmF : In m F) by (apply filter_In in HmS; apply HmS).
  assert (Hmlt : dart_lt d m).
  { apply filter_In in HmS. apply dart_ltb_spec. apply HmS. }
  (* S is in general position (subset of F), so list_min S is a lower bound *)
  assert (HstoS : sto_on S).
  { apply (sto_on_subset F S (fan_ok_sto F HF)).
    intros y Hy. apply filter_In in Hy. apply Hy. }
  split; [ rewrite Hnext; exact HmF | split; [ rewrite Hnext; exact Hmlt | ] ].
  intros e HeF Helt.
  assert (HeS : In e S).
  { apply filter_In. split; [ exact HeF | apply dart_ltb_spec; exact Helt ]. }
  pose proof (list_min_lb S m HstoS Hm e HeS) as Hem.  (* dart_ltb e m = false *)
  destruct HstoS as [_ HtoS].
  destruct (HtoS e m HeS HmS) as [Eq | [Hlt | Hgt]].
  - left. rewrite Hnext. symmetry. exact Eq.
  - rewrite Hlt in Hem; discriminate.
  - right. rewrite Hnext. apply dart_ltb_spec. exact Hgt.
Qed.

(* Wrap case: when `d` is the fan maximum (no strictly-greater dart), `next F d`
   is the global minimum of the fan. *)
Lemma next_wrap_least :
  forall F d, fan_ok F -> In d F ->
    (forall e, In e F -> ~ dart_lt d e) ->
    forall x, In x F -> next F d = x \/ dart_lt (next F d) x.
Proof.
  intros F d HF Hd Hmax x Hx.
  (* the successor set is empty *)
  assert (Hempty : filter (fun e => dart_ltb d e) F = []).
  { destruct (filter (fun e => dart_ltb d e) F) as [| y ys] eqn:Hf; [ reflexivity | ].
    exfalso.
    assert (Hy : In y (filter (fun e => dart_ltb d e) F)) by (rewrite Hf; left; reflexivity).
    apply filter_In in Hy. destruct Hy as [HyF Hylt].
    apply dart_ltb_spec in Hylt. exact (Hmax y HyF Hylt). }
  (* so `next` takes the global-minimum branch *)
  assert (Hns : list_min F <> None).
  { intro Hn. apply list_min_none_iff in Hn. rewrite Hn in Hd. exact Hd. }
  destruct (list_min F) as [m |] eqn:Hm; [ | exfalso; apply Hns; reflexivity ].
  assert (Hnext : next F d = m).
  { unfold next. rewrite Hempty. cbn. rewrite Hm. reflexivity. }
  pose proof (list_min_lb F m (fan_ok_sto F HF) Hm x Hx) as Hxm.  (* dart_ltb x m = false *)
  assert (HmF : In m F) by (apply (list_min_in F m Hm)).
  destruct (fan_ok_sto F HF) as [_ Hto].
  destruct (Hto x m Hx HmF) as [Eq | [Hlt | Hgt]].
  - left. rewrite Hnext. symmetry. exact Eq.
  - rewrite Hlt in Hxm; discriminate.
  - right. rewrite Hnext. apply dart_ltb_spec. exact Hgt.
Qed.
