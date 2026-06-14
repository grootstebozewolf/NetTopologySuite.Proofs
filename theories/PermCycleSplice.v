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
