(* ==========================================================================
   PermCycleSplice.v

   H_bridge Euler route, Rung 3b-xvii (stage 1 of the cycle-count SPLICE):
   the orbit-transversal lemmas, as thin INSTANCES of the shared
   `ClassCount` core (Rung 3b-vii).

   Since `PermCycleCount.orbit_reps eqdec f S = ClassCount.class_reps
   (same_orbit_b eqdec f S)` (the orbit counter IS the generic class counter
   specialised to the same-orbit relation), the transversal facts
   (`orbit_reps_NoDup`, `orbit_reps_indep`, `orbit_rep_in`,
   `orbit_reps_length_mono`) are direct instantiations of
   `ClassCount.class_reps_{NoDup,indep,...}` with `rb := same_orbit_b`.  The
   only orbit-specific glue is converting between the `same_orbit` (Prop) and
   `same_orbit_b` (bool) views and supplying the on-`S` symmetry/transitivity
   (`PermCycleCount.same_orbit_b_sym_on` / `_trans_on`).

   Pure list/orbit combinatorics; no `Admitted` / `Axiom` / `Parameter`;
   allowlist axioms only (in fact axiom-free).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import List Arith Lia.
From NTS.Proofs Require Import OrbitCycle ClassCount PermCycleCount.

Import ListNotations.

Section OrbitTransversal.
  Context {A : Type}.
  Variable eqdec : forall a b : A, {a = b} + {a <> b}.
  Variable f : A -> A.
  Variable S : list A.
  Hypothesis Hclos : forall x, In x S -> In (f x) S.
  Hypothesis Hinj : forall a b, In a S -> In b S -> f a = f b -> a = b.

  (* The kept representatives are NoDup. *)
  Lemma orbit_reps_NoDup : forall l, NoDup (orbit_reps eqdec f S l).
  Proof.
    intro l. unfold orbit_reps.
    apply (class_reps_NoDup (same_orbit_b eqdec f S) (same_orbit_b_refl eqdec f S)).
  Qed.

  (* Distinct reps lie in distinct orbits.  `incl l S` lets the on-S symmetry of
     `same_orbit_b` feed the generic `class_reps_indep`. *)
  Lemma orbit_reps_indep : forall l,
    (forall x, In x l -> In x S) ->
    forall r1 r2, In r1 (orbit_reps eqdec f S l) -> In r2 (orbit_reps eqdec f S l) ->
    same_orbit f r1 r2 -> r1 = r2.
  Proof.
    intros l Hsub r1 r2 H1 H2 Hr. unfold orbit_reps in H1, H2.
    apply (class_reps_indep (same_orbit_b eqdec f S) l
             (fun x y Hx Hy Hxy =>
                same_orbit_b_sym_on eqdec f S Hclos Hinj x y (Hsub x Hx) (Hsub y Hy) Hxy)
             r1 r2 H1 H2).
    apply (same_orbit_b_complete eqdec f S Hclos Hinj r1
             (Hsub r1 (class_reps_incl (same_orbit_b eqdec f S) l r1 H1)) r2 Hr).
  Qed.

  (* Class-representative chooser, as the ClassCount one. *)
  Definition orbit_rep_in (l : list A) (r : A) : A :=
    class_rep_in (same_orbit_b eqdec f S) l r.

  Lemma orbit_rep_in_spec : forall l r, In r l ->
    In (orbit_rep_in l r) (orbit_reps eqdec f S l) /\
    same_orbit_b eqdec f S (orbit_rep_in l r) r = true.
  Proof.
    intros l r Hr. unfold orbit_rep_in, orbit_reps.
    apply (class_rep_in_spec (same_orbit_b eqdec f S) (same_orbit_b_refl eqdec f S) l r Hr).
  Qed.

  (* Class count is monotone in the carrier (same f). *)
  Lemma orbit_reps_length_mono : forall l l',
    (forall x, In x l -> In x S) -> (forall x, In x l' -> In x S) ->
    (forall x, In x l -> In x l') ->
    (length (orbit_reps eqdec f S l) <= length (orbit_reps eqdec f S l'))%nat.
  Proof.
    intros l l' HlS Hl'S Hincl. unfold orbit_reps.
    apply (class_reps_length_mono (same_orbit_b eqdec f S) (same_orbit_b_refl eqdec f S) l l').
    - intros x y Hx Hy Hxy.
      apply (same_orbit_b_sym_on eqdec f S Hclos Hinj x y (Hl'S x Hx) (Hl'S y Hy) Hxy).
    - intros x y z Hx Hy Hz Hxy Hyz.
      apply (same_orbit_b_trans_on eqdec f S Hclos Hinj x y z
               (Hl'S x Hx) (Hl'S y Hy) (Hl'S z Hz) Hxy Hyz).
    - exact Hincl.
  Qed.

End OrbitTransversal.

(* -------------------------------------------------------------------------- *)
(* CYCLE-COUNT SPLICE, stage 3a: the arc STRUCTURE of an orbit cut at two       *)
(* points.  Generic permutation surgery (no Dart imports): a permutation `f` of *)
(* `S` with one orbit O of period `per` containing `d` (position 0) and `td`    *)
(* (position k, 2 <= k <= per-2).  Deleting d, td and CROSS-CONNECTING their    *)
(* predecessors (the `fstep_E_minus_splice` shape) splits O into two `f'`-cycles:*)
(* arc1 = positions 1..k-1, arc2 = positions k+1..per-1.  This rung proves each  *)
(* arc closes into a single f'-orbit and that an on-orbit S'-element is indexed  *)
(* in one of the two ranges.  The NOT-same-orbit invariant (3b) and the `+1`    *)
(* count (stage 4, via ClassCount.count_classes_filter_split) build on these.    *)
(* -------------------------------------------------------------------------- *)

(* iter at `n+1` peels one application on the left (generic; `n+1` reduces to    *)
(* `S n` only after commuting). *)
Lemma iter_add1 : forall {A : Type} (g : A -> A) (n : nat) (x : A),
  OrbitCycle.iter g (n + 1) x = g (OrbitCycle.iter g n x).
Proof. intros A g n x. replace (n + 1)%nat with (1 + n)%nat by lia. reflexivity. Qed.

Section CycleSplice.
  Context {A : Type}.
  Variable eqdec : forall a b : A, {a = b} + {a <> b}.
  Variable f : A -> A.
  Variable S : list A.
  Hypothesis Hclos : forall x, In x S -> In (f x) S.
  Hypothesis Hinj : forall a b, In a S -> In b S -> f a = f b -> a = b.

  Variable d td : A.
  Hypothesis HdS : In d S.
  Hypothesis HtdS : In td S.
  Hypothesis Hdtd : d <> td.

  (* The orbit of d is a genuine cycle of minimal period `per`. *)
  Variable per : nat.
  Hypothesis Hper_return : OrbitCycle.iter f per d = d.
  Hypothesis Hper_pos : (1 <= per)%nat.
  Hypothesis Hper_min : forall j, (1 <= j < per)%nat -> OrbitCycle.iter f j d <> d.

  (* td is first reached at index k, strictly inside the cycle (no spur at either
     end: 2 <= k from `no_spurs` on d, k <= per-2 from `no_spurs` on td). *)
  Variable k : nat.
  Hypothesis Hk_td : OrbitCycle.iter f k d = td.
  Hypothesis Hk_range : (2 <= k <= per - 2)%nat.
  Hypothesis Hk_first : forall j, (1 <= j < k)%nat -> OrbitCycle.iter f j d <> td.

  (* The surgered map/carrier (specified ON S' only, as `fstep_E_minus_splice`
     produces; CROSSED redirect: `=d => f td`, `=td => f d`). *)
  Variable f' : A -> A.
  Variable S' : list A.
  Hypothesis Hcarrier : forall x, In x S' <-> (In x S /\ x <> d /\ x <> td).
  Hypothesis Hclos' : forall x, In x S' -> In (f' x) S'.
  Hypothesis Hinj' : forall a b, In a S' -> In b S' -> f' a = f' b -> a = b.
  Hypothesis Hf'spec : forall x, In x S' ->
    f' x = (if eqdec (f x) d then f td
            else if eqdec (f x) td then f d
            else f x).

  Local Notation it := (OrbitCycle.iter f).
  Local Notation it' := (OrbitCycle.iter f').

  (* The whole orbit of d sits inside S. *)
  Lemma orbit_in_S : forall i, In (it i d) S.
  Proof. intro i. apply OrbitCycle.iter_in; [ exact Hclos | exact HdS ]. Qed.

  (* Positions 0..per-1 are distinct (minimal period). The workhorse. *)
  Lemma splice_period_orbit_distinct :
    forall i j, (i < per)%nat -> (j < per)%nat -> it i d = it j d -> i = j.
  Proof.
    assert (Haux : forall i j, (i < j)%nat -> (j < per)%nat -> it i d = it j d -> False).
    { intros i j Hij Hjper Heq.
      assert (Hreturn : it (j - i) d = d).
      { apply (OrbitCycle.iter_inj_on f S Hclos Hinj i (it (j - i) d) d).
        - apply orbit_in_S.
        - exact HdS.
        - rewrite <- OrbitCycle.iter_comp.
          replace (i + (j - i))%nat with j by lia.
          symmetry. exact Heq. }
      apply (Hper_min (j - i)); [ lia | exact Hreturn ]. }
    intros i j Hi Hj Heq.
    destruct (lt_eq_lt_dec i j) as [[Hlt | Heqij] | Hgt].
    - exfalso. apply (Haux i j Hlt Hj Heq).
    - exact Heqij.
    - exfalso. apply (Haux j i Hgt Hi). symmetry. exact Heq.
  Qed.

  (* Past k, the orbit never revisits td before wrapping. *)
  Lemma it_not_td_after_k : forall i, (k < i < per)%nat -> it i d <> td.
  Proof.
    intros i [Hki Hip] Heq.
    assert (Hik : it i d = it k d) by (rewrite Heq, Hk_td; reflexivity).
    assert (i = k) by (apply splice_period_orbit_distinct; [ exact Hip | lia | exact Hik ]).
    lia.
  Qed.

  (* Arc members live in the surgered carrier S'. *)
  Lemma arc1_mem : forall i, (1 <= i <= k - 1)%nat -> In (it i d) S'.
  Proof.
    intros i Hi. apply (proj2 (Hcarrier (it i d))).
    split; [ apply orbit_in_S | split ].
    - apply Hper_min. lia.
    - apply Hk_first. lia.
  Qed.

  Lemma arc2_mem : forall i, (k + 1 <= i <= per - 1)%nat -> In (it i d) S'.
  Proof.
    intros i Hi. apply (proj2 (Hcarrier (it i d))).
    split; [ apply orbit_in_S | split ].
    - apply Hper_min. lia.
    - apply it_not_td_after_k. lia.
  Qed.

  (* f' tracks f along each arc's interior, and wraps the last element back to
     the arc's first (CROSSED redirect, hence arc1 wraps via `=td`, arc2 via `=d`). *)
  Lemma f'_arc1_interior : forall i, (1 <= i <= k - 2)%nat -> f' (it i d) = it (i + 1) d.
  Proof.
    intros i Hi.
    rewrite (Hf'spec (it i d) (arc1_mem i ltac:(lia))).
    assert (Hf : f (it i d) = it (i + 1) d) by (rewrite iter_add1; reflexivity).
    rewrite Hf.
    destruct (eqdec (it (i + 1) d) d) as [Hc | _].
    - exfalso. apply (Hper_min (i + 1)); [ lia | exact Hc ].
    - destruct (eqdec (it (i + 1) d) td) as [Hc | _].
      + exfalso. apply (Hk_first (i + 1)); [ lia | exact Hc ].
      + reflexivity.
  Qed.

  Lemma f'_arc1_wrap : f' (it (k - 1) d) = it 1 d.
  Proof.
    rewrite (Hf'spec (it (k - 1) d) (arc1_mem (k - 1) ltac:(lia))).
    assert (Hf : f (it (k - 1) d) = td)
      by (rewrite <- iter_add1; replace (k - 1 + 1)%nat with k by lia; exact Hk_td).
    rewrite Hf.
    destruct (eqdec td d) as [Hc | _]; [ exfalso; apply Hdtd; symmetry; exact Hc | ].
    destruct (eqdec td td) as [_ | Hc]; [ reflexivity | exfalso; apply Hc; reflexivity ].
  Qed.

  Lemma f'_arc2_interior : forall i, (k + 1 <= i <= per - 2)%nat -> f' (it i d) = it (i + 1) d.
  Proof.
    intros i Hi.
    rewrite (Hf'spec (it i d) (arc2_mem i ltac:(lia))).
    assert (Hf : f (it i d) = it (i + 1) d) by (rewrite iter_add1; reflexivity).
    rewrite Hf.
    destruct (eqdec (it (i + 1) d) d) as [Hc | _].
    - exfalso. apply (Hper_min (i + 1)); [ lia | exact Hc ].
    - destruct (eqdec (it (i + 1) d) td) as [Hc | _].
      + exfalso. apply (it_not_td_after_k (i + 1)); [ lia | exact Hc ].
      + reflexivity.
  Qed.

  Lemma f'_arc2_wrap : f' (it (per - 1) d) = it (k + 1) d.
  Proof.
    rewrite (Hf'spec (it (per - 1) d) (arc2_mem (per - 1) ltac:(lia))).
    assert (Hf : f (it (per - 1) d) = d)
      by (rewrite <- iter_add1; replace (per - 1 + 1)%nat with per by lia; exact Hper_return).
    rewrite Hf.
    destruct (eqdec d d) as [_ | Hc]; [ | exfalso; apply Hc; reflexivity ].
    rewrite <- Hk_td. rewrite <- iter_add1. reflexivity.
  Qed.

  (* Iterating f' inside an arc tracks f along the index. *)
  Lemma iter_f'_arc1 : forall m, (1 + m <= k - 1)%nat -> it' m (it 1 d) = it (1 + m) d.
  Proof.
    induction m as [| m IH]; intro Hm.
    - reflexivity.
    - replace (Datatypes.S m) with (m + 1)%nat by lia.
      rewrite iter_add1, IH by lia.
      rewrite (f'_arc1_interior (1 + m)) by lia.
      f_equal; lia.
  Qed.

  Lemma iter_f'_arc2 :
    forall m, (k + 1 + m <= per - 1)%nat -> it' m (it (k + 1) d) = it (k + 1 + m) d.
  Proof.
    induction m as [| m IH]; intro Hm.
    - replace (k + 1 + 0)%nat with (k + 1)%nat by lia. reflexivity.
    - replace (Datatypes.S m) with (m + 1)%nat by lia.
      rewrite iter_add1, IH by lia.
      rewrite (f'_arc2_interior (k + 1 + m)) by lia.
      f_equal; lia.
  Qed.

  (* Each arc closes into a SINGLE f'-orbit (all its elements are same_orbit f'
     to the arc's first element). *)
  Lemma splice_arc1_is_orbit : forall i, (1 <= i <= k - 1)%nat ->
    same_orbit_b eqdec f' S' (it 1 d) (it i d) = true.
  Proof.
    intros i Hi.
    apply (same_orbit_b_complete eqdec f' S' Hclos' Hinj' (it 1 d));
      [ apply arc1_mem; lia | ].
    exists (i - 1)%nat. rewrite iter_f'_arc1 by lia. f_equal. lia.
  Qed.

  Lemma splice_arc2_is_orbit : forall i, (k + 1 <= i <= per - 1)%nat ->
    same_orbit_b eqdec f' S' (it (k + 1) d) (it i d) = true.
  Proof.
    intros i Hi.
    apply (same_orbit_b_complete eqdec f' S' Hclos' Hinj' (it (k + 1) d));
      [ apply arc2_mem; lia | ].
    exists (i - (k + 1))%nat. rewrite iter_f'_arc2 by lia. f_equal. lia.
  Qed.

  (* Modular reduction of the orbit index by the period. *)
  Lemma it_mod_per : forall n, it n d = it (n mod per) d.
  Proof.
    intro n.
    rewrite (Nat.div_mod_eq n per) at 1.
    rewrite Nat.add_comm, OrbitCycle.iter_comp, (Nat.mul_comm per (n / per)).
    rewrite (PermCycleCount.iter_period_mult f per d Hper_return (n / per)).
    reflexivity.
  Qed.

  (* DECOMPOSE direction: an S'-element on d's f-orbit is indexed in one of the
     two arc ranges (the complement of {0 (=d), k (=td)} mod per). *)
  Lemma splice_on_orbit_index : forall x, In x S' -> same_orbit f d x ->
    exists i, ((1 <= i <= k - 1)%nat \/ (k + 1 <= i <= per - 1)%nat) /\ x = it i d.
  Proof.
    intros x HxS' Hso. destruct Hso as [n Hn].
    apply (proj1 (Hcarrier x)) in HxS'. destruct HxS' as [_ [Hxd Hxtd]].
    set (i := (n mod per)%nat).
    assert (Hilt : (i < per)%nat) by (apply Nat.mod_upper_bound; lia).
    assert (Hxi : x = it i d)
      by (subst i; rewrite <- it_mod_per; symmetry; exact Hn).
    exists i. split; [ | exact Hxi ].
    assert (Hi0 : i <> 0%nat) by (intro H0; apply Hxd; rewrite Hxi, H0; reflexivity).
    assert (Hik : i <> k) by (intro He; apply Hxtd; rewrite Hxi, He; exact Hk_td).
    lia.
  Qed.

  (* ---- Stage 3b: the not-same-orbit / class-constancy invariant ---------- *)

  (* The three regions of S' under the surgery. `Outside` is membership-based
     (in S', not on d's f-orbit) -- the form that feeds the f'=f closure step;
     `arc_or_outside` reconciles it with the index view. *)
  Definition InArc1 (z : A) : Prop := exists i, (1 <= i <= k - 1)%nat /\ z = it i d.
  Definition InArc2 (z : A) : Prop := exists i, (k + 1 <= i <= per - 1)%nat /\ z = it i d.
  Definition Outside (z : A) : Prop := In z S' /\ ~ same_orbit f d z.

  Lemma inO_d_td : same_orbit f d td.
  Proof. exists k. exact Hk_td. Qed.

  Lemma arc_or_outside : forall z, In z S' -> InArc1 z \/ InArc2 z \/ Outside z.
  Proof.
    intros z Hz.
    destruct (same_orbit_dec eqdec f S Hclos Hinj d HdS z) as [Hso | Hnso].
    - destruct (splice_on_orbit_index z Hz Hso) as [i [[Hr1 | Hr2] Hzi]].
      + left. exists i. split; [ exact Hr1 | exact Hzi ].
      + right; left. exists i. split; [ exact Hr2 | exact Hzi ].
    - right; right. split; [ exact Hz | exact Hnso ].
  Qed.

  (* On Outside points the surgered map is the original: neither redirect guard
     fires, else `x` would be a one-step predecessor of `d`/`td`, hence on d's
     orbit (`same_orbit_sym`/`_trans`), contradicting Outside. *)
  Lemma f'_eq_f_outside : forall z, Outside z -> f' z = f z.
  Proof.
    intros z [HzS' Hznoso].
    destruct (proj1 (Hcarrier z) HzS') as [HzS _].
    rewrite (Hf'spec z HzS').
    destruct (eqdec (f z) d) as [Hfd | _].
    - exfalso. apply Hznoso.
      apply (same_orbit_sym eqdec f S Hclos Hinj z HzS d).
      exists 1%nat. cbn [OrbitCycle.iter]. exact Hfd.
    - destruct (eqdec (f z) td) as [Hftd | _].
      + exfalso. apply Hznoso.
        apply (same_orbit_trans f d td z inO_d_td).
        apply (same_orbit_sym eqdec f S Hclos Hinj z HzS td).
        exists 1%nat. cbn [OrbitCycle.iter]. exact Hftd.
      + reflexivity.
  Qed.

  (* Each region is f'-closed (the wraps stay in-arc; Outside stays Outside). *)
  Lemma f'_closes_arc1 : forall z, InArc1 z -> InArc1 (f' z).
  Proof.
    intros z [i [Hi Hz]]. subst z.
    destruct (Nat.eq_dec i (k - 1)) as [Hwrap | Hint].
    - subst i. rewrite f'_arc1_wrap. exists 1%nat. split; [ lia | reflexivity ].
    - rewrite (f'_arc1_interior i ltac:(lia)).
      exists (i + 1)%nat. split; [ lia | reflexivity ].
  Qed.

  Lemma f'_closes_arc2 : forall z, InArc2 z -> InArc2 (f' z).
  Proof.
    intros z [i [Hi Hz]]. subst z.
    destruct (Nat.eq_dec i (per - 1)) as [Hwrap | Hint].
    - subst i. rewrite f'_arc2_wrap. exists (k + 1)%nat. split; [ lia | reflexivity ].
    - rewrite (f'_arc2_interior i ltac:(lia)).
      exists (i + 1)%nat. split; [ lia | reflexivity ].
  Qed.

  Lemma f'_closes_outside : forall z, Outside z -> Outside (f' z).
  Proof.
    intros z Hz. destruct Hz as [HzS' Hznoso].
    destruct (proj1 (Hcarrier z) HzS') as [HzS _].
    split.
    - apply Hclos'. exact HzS'.
    - rewrite (f'_eq_f_outside z (conj HzS' Hznoso)). intro Hso.
      apply Hznoso.
      apply (same_orbit_trans f d (f z) z Hso).
      apply (same_orbit_sym eqdec f S Hclos Hinj z HzS (f z)).
      exists 1%nat. cbn [OrbitCycle.iter]. reflexivity.
  Qed.

  (* f'-orbits preserve region membership (induction on the step count). *)
  Lemma f'_orbit_preserves_arc1 : forall n z, InArc1 z -> InArc1 (it' n z).
  Proof.
    intros n. induction n as [| n IH]; intros z Hz.
    - exact Hz.
    - cbn [OrbitCycle.iter]. apply f'_closes_arc1. apply IH. exact Hz.
  Qed.

  Lemma f'_orbit_preserves_arc2 : forall n z, InArc2 z -> InArc2 (it' n z).
  Proof.
    intros n. induction n as [| n IH]; intros z Hz.
    - exact Hz.
    - cbn [OrbitCycle.iter]. apply f'_closes_arc2. apply IH. exact Hz.
  Qed.

  Lemma f'_orbit_preserves_outside : forall n z, Outside z -> Outside (it' n z).
  Proof.
    intros n. induction n as [| n IH]; intros z Hz.
    - exact Hz.
    - cbn [OrbitCycle.iter]. apply f'_closes_outside. apply IH. exact Hz.
  Qed.

  (* CLASS-CONSTANCY of "in O" along f'-orbits (Prop core). *)
  Lemma splice_inO_f'_class_constant_prop : forall x y,
    In x S' -> In y S' -> same_orbit f' x y ->
    (same_orbit f d x <-> same_orbit f d y).
  Proof.
    intros x y HxS' HyS' Hxy.
    assert (Hfwd : forall a b, In a S' -> same_orbit f' a b ->
                     same_orbit f d a -> same_orbit f d b).
    { intros a b HaS' [n Hn] Hda. subst b.
      destruct (arc_or_outside a HaS') as [Ha | [Ha | Ha]].
      - destruct (f'_orbit_preserves_arc1 n a Ha) as [j [_ Hj']].
        exists j. symmetry. exact Hj'.
      - destruct (f'_orbit_preserves_arc2 n a Ha) as [j [_ Hj']].
        exists j. symmetry. exact Hj'.
      - exfalso. destruct Ha as [_ Hna]. exact (Hna Hda). }
    split.
    - intro Hdx. exact (Hfwd x y HxS' Hxy Hdx).
    - intro Hdy.
      assert (Hyx : same_orbit f' y x)
        by (exact (same_orbit_sym eqdec f' S' Hclos' Hinj' x HxS' y Hxy)).
      exact (Hfwd y x HyS' Hyx Hdy).
  Qed.

  (* Boolean corollary -- the exact shape stage 4's count_classes_filter_split
     consumes on the (f',S') side. *)
  Lemma splice_inO_f'_class_constant : forall x y,
    In x S' -> In y S' ->
    same_orbit_b eqdec f' S' x y = true ->
    same_orbit_b eqdec f S d x = same_orbit_b eqdec f S d y.
  Proof.
    intros x y HxS' HyS' Hb. apply same_orbit_b_sound in Hb.
    destruct (proj1 (Hcarrier x) HxS') as [HxS _].
    destruct (proj1 (Hcarrier y) HyS') as [HyS _].
    destruct (splice_inO_f'_class_constant_prop x y HxS' HyS' Hb) as [Hfwd Hbwd].
    destruct (same_orbit_b eqdec f S d x) eqn:Ex;
      destruct (same_orbit_b eqdec f S d y) eqn:Ey; try reflexivity; exfalso.
    - assert (same_orbit f d x) by (apply (same_orbit_b_sound eqdec f S d x); exact Ex).
      assert (same_orbit f d y) by (apply Hfwd; assumption).
      assert (same_orbit_b eqdec f S d y = true)
        by (apply (same_orbit_b_complete eqdec f S Hclos Hinj d HdS y); assumption).
      congruence.
    - assert (same_orbit f d y) by (apply (same_orbit_b_sound eqdec f S d y); exact Ey).
      assert (same_orbit f d x) by (apply Hbwd; assumption).
      assert (same_orbit_b eqdec f S d x = true)
        by (apply (same_orbit_b_complete eqdec f S Hclos Hinj d HdS x); assumption).
      congruence.
  Qed.

  (* arc1 and arc2 are DISTINCT f'-orbits. *)
  Lemma splice_arcs_distinct : forall a b, InArc1 a -> InArc2 b -> ~ same_orbit f' a b.
  Proof.
    intros a b Ha Hb [n Hn].
    assert (Hb1 : InArc1 b)
      by (rewrite <- Hn; apply f'_orbit_preserves_arc1; exact Ha).
    destruct Hb1 as [i1 [Hi1 Hbi1]]. destruct Hb as [i2 [Hi2 Hbi2]].
    assert (it i1 d = it i2 d) by (rewrite <- Hbi1, <- Hbi2; reflexivity).
    assert (i1 = i2) by (apply splice_period_orbit_distinct; [ lia | lia | assumption ]).
    lia.
  Qed.

  Lemma splice_arcs_distinct_b : forall a b,
    InArc1 a -> InArc2 b -> same_orbit_b eqdec f' S' a b = false.
  Proof.
    intros a b Ha Hb.
    destruct (same_orbit_b eqdec f' S' a b) eqn:E; [ exfalso | reflexivity ].
    apply same_orbit_b_sound in E. exact (splice_arcs_distinct a b Ha Hb E).
  Qed.

  (* OUTSIDE BRIDGE: f' and f agree along an Outside orbit, so the two
     same_orbit_b's (different carriers!) agree there -- stage 4's complement. *)
  Lemma iter_f'_eq_iter_f_outside : forall n z, Outside z -> it' n z = it n z.
  Proof.
    intros n. induction n as [| n IH]; intros z Hz.
    - reflexivity.
    - cbn [OrbitCycle.iter]. rewrite (IH z Hz).
      apply f'_eq_f_outside. rewrite <- (IH z Hz).
      apply f'_orbit_preserves_outside. exact Hz.
  Qed.

  Lemma outside_orbit_iff : forall x y,
    Outside x -> Outside y -> (same_orbit f' x y <-> same_orbit f x y).
  Proof.
    intros x y Hx Hy. split.
    - intros [n Hn]. exists n. rewrite <- (iter_f'_eq_iter_f_outside n x Hx). exact Hn.
    - intros [n Hn]. exists n. rewrite (iter_f'_eq_iter_f_outside n x Hx). exact Hn.
  Qed.

  Lemma outside_orbit_b_eq : forall x y,
    Outside x -> Outside y ->
    same_orbit_b eqdec f' S' x y = same_orbit_b eqdec f S x y.
  Proof.
    intros x y Hx Hy.
    pose proof Hx as HxC. destruct HxC as [HxS' _].
    pose proof Hy as HyC. destruct HyC as [HyS' _].
    destruct (proj1 (Hcarrier x) HxS') as [HxS _].
    destruct (proj1 (Hcarrier y) HyS') as [HyS _].
    destruct (same_orbit_b eqdec f' S' x y) eqn:E';
      destruct (same_orbit_b eqdec f S x y) eqn:E; try reflexivity; exfalso.
    - apply same_orbit_b_sound in E'.
      assert (same_orbit f x y)
        by (apply (proj1 (outside_orbit_iff x y Hx Hy)); exact E').
      assert (same_orbit_b eqdec f S x y = true)
        by (apply (same_orbit_b_complete eqdec f S Hclos Hinj x HxS y); assumption).
      congruence.
    - apply same_orbit_b_sound in E.
      assert (same_orbit f' x y)
        by (apply (proj2 (outside_orbit_iff x y Hx Hy)); exact E).
      assert (same_orbit_b eqdec f' S' x y = true)
        by (apply (same_orbit_b_complete eqdec f' S' Hclos' Hinj' x HxS' y); assumption).
      congruence.
  Qed.

End CycleSplice.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Thin instances of ClassCount; allowlist axioms only.          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions orbit_reps_NoDup.
Print Assumptions orbit_reps_indep.
Print Assumptions orbit_reps_length_mono.
Print Assumptions splice_arc1_is_orbit.
Print Assumptions splice_arc2_is_orbit.
Print Assumptions splice_on_orbit_index.
Print Assumptions splice_inO_f'_class_constant.
Print Assumptions splice_arcs_distinct_b.
Print Assumptions outside_orbit_b_eq.
