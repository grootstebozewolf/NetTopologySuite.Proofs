(* ==========================================================================
   PermCycleMerge.v

   Cycle-count MERGE: the mirror image of `PermCycleSplice.cycle_count_surgery`.

   `PermCycleSplice.v` proves the SPLIT direction: deleting two points `d`,
   `td` that share ONE `f`-orbit (with `td` first reached at an interior
   index `k`) and cross-wiring their neighbours (`f'`'s redirect: whoever's
   successor was `d` now goes to `f td`; whoever's successor was `td` now goes
   to `f d`) splits that orbit into TWO `f'`-orbits.

   This file proves the opposite composition: `d` and `td` sit on TWO
   DISTINCT `f`-orbits (periods `per1`, `per2`); the SAME cross-wiring
   redirect STITCHES them into a SINGLE `f'`-orbit of length `per1+per2-2`,
   so the orbit count DROPS by one.  The redirect formula
   (`FaceStepRemove.fstep_E_minus_splice`) is already proved without any
   same-face hypothesis, so no new semantic bridge is needed -- only the
   mirror-image generic permutation combinatorics, built the same way as
   `PermCycleSplice.v`'s `CycleSplice` section (arc bookkeeping via
   `ClassCount.count_classes_filter_split` / `count_classes_eq_1`).

   The disjoint-orbit hypothesis `~ same_orbit f d td` REPLACES the split
   case's index bookkeeping (`k`, `Hk_range`, `Hk_first`) outright -- there is
   no "first reached at index k" question when the two points are not on the
   same orbit to begin with, so this section's premise list is actually
   SHORTER than `CycleSplice`'s.

   Intuition by example: a 3-cycle containing `d` and a 4-cycle containing
   `td`, stitched by the redirect, become ONE 5-cycle (`per1+per2-2 = 3+4-2`)
   -- the orbit count drops from 2 to 1, exactly the `-1` `cycle_count_merge`
   proves in general, and exactly the `-1` `[EF-2]` needs for `num_faces`.

   Pure combinatorial wiring; no `Admitted` / `Axiom` / `Parameter`; allowlist
   axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import List Arith Lia Bool.
From NTS.Proofs Require Import OrbitCycle ClassCount PermCycleCount PermCycleSplice.

Import ListNotations.

Section CycleMerge.
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
  Hypothesis Hnso : ~ same_orbit f d td.

  Variable per1 : nat.
  Hypothesis Hper1_return : OrbitCycle.iter f per1 d = d.
  Hypothesis Hper1_ge2 : (2 <= per1)%nat.
  Hypothesis Hper1_min : forall j, (1 <= j < per1)%nat -> OrbitCycle.iter f j d <> d.

  Variable per2 : nat.
  Hypothesis Hper2_return : OrbitCycle.iter f per2 td = td.
  Hypothesis Hper2_ge2 : (2 <= per2)%nat.
  Hypothesis Hper2_min : forall j, (1 <= j < per2)%nat -> OrbitCycle.iter f j td <> td.

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

  (* -------------------------------------------------------------------------- *)
  (* Stage 1: the two orbits, disjoint, each a genuine period.                    *)
  (* -------------------------------------------------------------------------- *)

  Lemma orbit_in_S_d : forall i, In (it i d) S.
  Proof. intro i. apply OrbitCycle.iter_in; [ exact Hclos | exact HdS ]. Qed.

  Lemma orbit_in_S_td : forall i, In (it i td) S.
  Proof. intro i. apply OrbitCycle.iter_in; [ exact Hclos | exact HtdS ]. Qed.

  Lemma period_d_distinct : forall i j, (i < per1)%nat -> (j < per1)%nat -> it i d = it j d -> i = j.
  Proof.
    assert (Haux : forall i j, (i < j)%nat -> (j < per1)%nat -> it i d = it j d -> False).
    { intros i j Hij Hjper Heq.
      assert (Hreturn : it (j - i) d = d).
      { apply (OrbitCycle.iter_inj_on f S Hclos Hinj i (it (j - i) d) d).
        - apply orbit_in_S_d.
        - exact HdS.
        - rewrite <- OrbitCycle.iter_comp.
          replace (i + (j - i))%nat with j by lia.
          symmetry. exact Heq. }
      apply (Hper1_min (j - i)); [ lia | exact Hreturn ]. }
    intros i j Hi Hj Heq.
    destruct (lt_eq_lt_dec i j) as [[Hlt | Heqij] | Hgt].
    - exfalso. apply (Haux i j Hlt Hj Heq).
    - exact Heqij.
    - exfalso. apply (Haux j i Hgt Hi). symmetry. exact Heq.
  Qed.

  Lemma period_td_distinct : forall i j, (i < per2)%nat -> (j < per2)%nat -> it i td = it j td -> i = j.
  Proof.
    assert (Haux : forall i j, (i < j)%nat -> (j < per2)%nat -> it i td = it j td -> False).
    { intros i j Hij Hjper Heq.
      assert (Hreturn : it (j - i) td = td).
      { apply (OrbitCycle.iter_inj_on f S Hclos Hinj i (it (j - i) td) td).
        - apply orbit_in_S_td.
        - exact HtdS.
        - rewrite <- OrbitCycle.iter_comp.
          replace (i + (j - i))%nat with j by lia.
          symmetry. exact Heq. }
      apply (Hper2_min (j - i)); [ lia | exact Hreturn ]. }
    intros i j Hi Hj Heq.
    destruct (lt_eq_lt_dec i j) as [[Hlt | Heqij] | Hgt].
    - exfalso. apply (Haux i j Hlt Hj Heq).
    - exact Heqij.
    - exfalso. apply (Haux j i Hgt Hi). symmetry. exact Heq.
  Qed.

  Lemma it_mod_per1 : forall n, it n d = it (n mod per1) d.
  Proof.
    intro n.
    rewrite (Nat.div_mod_eq n per1) at 1.
    rewrite Nat.add_comm, OrbitCycle.iter_comp, (Nat.mul_comm per1 (n / per1)).
    rewrite (PermCycleCount.iter_period_mult f per1 d Hper1_return (n / per1)).
    reflexivity.
  Qed.

  Lemma it_mod_per2 : forall n, it n td = it (n mod per2) td.
  Proof.
    intro n.
    rewrite (Nat.div_mod_eq n per2) at 1.
    rewrite Nat.add_comm, OrbitCycle.iter_comp, (Nat.mul_comm per2 (n / per2)).
    rewrite (PermCycleCount.iter_period_mult f per2 td Hper2_return (n / per2)).
    reflexivity.
  Qed.

  (* No index of d's orbit ever equals an index of td's orbit: they would
     otherwise be `same_orbit`, contradicting `Hnso`. *)
  Lemma d_orbit_ne_td_orbit : forall i j, it i d <> it j td.
  Proof.
    intros i j Heq.
    apply Hnso. exists (per2 - j mod per2 + i)%nat.
    rewrite OrbitCycle.iter_comp, Heq, <- OrbitCycle.iter_comp.
    assert (Hjlt : (j mod per2 < per2)%nat) by (apply Nat.mod_upper_bound; lia).
    replace (per2 - j mod per2 + j)%nat with ((Datatypes.S (j / per2)) * per2)%nat.
    - apply (PermCycleCount.iter_period_mult f per2 td Hper2_return).
    - pose proof (Nat.div_mod_eq j per2) as Hdm. nia.
  Qed.

  (* -------------------------------------------------------------------------- *)
  (* Stage 2: the two arcs (each orbit minus its own marked point) and their     *)
  (* membership in the surgered carrier.                                        *)
  (* -------------------------------------------------------------------------- *)

  Definition InArcD (z : A) : Prop := exists i, (1 <= i <= per1 - 1)%nat /\ z = it i d.
  Definition InArcT (z : A) : Prop := exists i, (1 <= i <= per2 - 1)%nat /\ z = it i td.

  Lemma arcD_mem : forall i, (1 <= i <= per1 - 1)%nat -> In (it i d) S'.
  Proof.
    intros i Hi. apply (proj2 (Hcarrier (it i d))).
    split; [ apply orbit_in_S_d | split ].
    - apply Hper1_min. lia.
    - exact (d_orbit_ne_td_orbit i 0).
  Qed.

  Lemma arcT_mem : forall i, (1 <= i <= per2 - 1)%nat -> In (it i td) S'.
  Proof.
    intros i Hi. apply (proj2 (Hcarrier (it i td))).
    split; [ apply orbit_in_S_td | split ].
    - intro Heq. exact (d_orbit_ne_td_orbit 0 i (eq_sym Heq)).
    - apply Hper2_min. lia.
  Qed.

  (* -------------------------------------------------------------------------- *)
  (* Stage 3: f' along each arc tracks f, and the two WRAP points cross-connect  *)
  (* the arcs instead of closing back on themselves.                            *)
  (* -------------------------------------------------------------------------- *)

  Lemma f'_arcD_interior : forall i, (1 <= i <= per1 - 2)%nat -> f' (it i d) = it (i + 1) d.
  Proof.
    intros i Hi.
    rewrite (Hf'spec (it i d) (arcD_mem i ltac:(lia))).
    assert (Hf : f (it i d) = it (i + 1) d) by (rewrite PermCycleSplice.iter_add1; reflexivity).
    rewrite Hf.
    destruct (eqdec (it (i + 1) d) d) as [Hc | _].
    - exfalso. apply (Hper1_min (i + 1)); [ lia | exact Hc ].
    - destruct (eqdec (it (i + 1) d) td) as [Hc | _].
      + exfalso. exact (d_orbit_ne_td_orbit (i + 1) 0 Hc).
      + reflexivity.
  Qed.

  Lemma f'_arcD_wrap : f' (it (per1 - 1) d) = it 1 td.
  Proof.
    rewrite (Hf'spec (it (per1 - 1) d) (arcD_mem (per1 - 1) ltac:(lia))).
    assert (Hf : f (it (per1 - 1) d) = d)
      by (rewrite <- PermCycleSplice.iter_add1;
          replace (per1 - 1 + 1)%nat with per1 by lia; exact Hper1_return).
    rewrite Hf.
    destruct (eqdec d d) as [_ | Hc]; [ reflexivity | exfalso; apply Hc; reflexivity ].
  Qed.

  Lemma f'_arcT_interior : forall i, (1 <= i <= per2 - 2)%nat -> f' (it i td) = it (i + 1) td.
  Proof.
    intros i Hi.
    rewrite (Hf'spec (it i td) (arcT_mem i ltac:(lia))).
    assert (Hf : f (it i td) = it (i + 1) td) by (rewrite PermCycleSplice.iter_add1; reflexivity).
    rewrite Hf.
    destruct (eqdec (it (i + 1) td) d) as [Hc | _].
    - exfalso. exact (d_orbit_ne_td_orbit 0 (i + 1) (eq_sym Hc)).
    - destruct (eqdec (it (i + 1) td) td) as [Hc | _].
      + exfalso. apply (Hper2_min (i + 1)); [ lia | exact Hc ].
      + reflexivity.
  Qed.

  Lemma f'_arcT_wrap : f' (it (per2 - 1) td) = it 1 d.
  Proof.
    rewrite (Hf'spec (it (per2 - 1) td) (arcT_mem (per2 - 1) ltac:(lia))).
    assert (Hf : f (it (per2 - 1) td) = td)
      by (rewrite <- PermCycleSplice.iter_add1;
          replace (per2 - 1 + 1)%nat with per2 by lia; exact Hper2_return).
    rewrite Hf.
    destruct (eqdec td d) as [Hc | _]; [ exfalso; apply Hdtd; symmetry; exact Hc | ].
    destruct (eqdec td td) as [_ | Hc]; [ reflexivity | exfalso; apply Hc; reflexivity ].
  Qed.

  (* -------------------------------------------------------------------------- *)
  (* Stage 4: iterating f' walks along d's arc, crosses into td's arc, walks     *)
  (* it, ready to cross back (closing the merged orbit).                        *)
  (* -------------------------------------------------------------------------- *)

  Lemma iter_f'_arcD : forall m, (1 + m <= per1 - 1)%nat -> it' m (it 1 d) = it (1 + m) d.
  Proof.
    induction m as [| m IH]; intro Hm.
    - reflexivity.
    - replace (Datatypes.S m) with (m + 1)%nat by lia.
      rewrite PermCycleSplice.iter_add1, IH by lia.
      rewrite (f'_arcD_interior (1 + m)) by lia.
      f_equal; lia.
  Qed.

  Lemma iter_f'_arcT : forall m, (1 + m <= per2 - 1)%nat -> it' m (it 1 td) = it (1 + m) td.
  Proof.
    induction m as [| m IH]; intro Hm.
    - reflexivity.
    - replace (Datatypes.S m) with (m + 1)%nat by lia.
      rewrite PermCycleSplice.iter_add1, IH by lia.
      rewrite (f'_arcT_interior (1 + m)) by lia.
      f_equal; lia.
  Qed.

  Lemma iter_f'_cross : it' (per1 - 1) (it 1 d) = it 1 td.
  Proof.
    replace (per1 - 1)%nat with ((per1 - 2) + 1)%nat by lia.
    rewrite PermCycleSplice.iter_add1.
    rewrite (iter_f'_arcD (per1 - 2) ltac:(lia)).
    replace (1 + (per1 - 2))%nat with (per1 - 1)%nat by lia.
    exact f'_arcD_wrap.
  Qed.

  Lemma iter_f'_arcD_then_T : forall m, (1 <= m <= per2 - 1)%nat ->
    it' (per1 - 1 + (m - 1)) (it 1 d) = it m td.
  Proof.
    intros m Hm.
    replace (per1 - 1 + (m - 1))%nat with ((m - 1) + (per1 - 1))%nat by lia.
    rewrite OrbitCycle.iter_comp.
    rewrite iter_f'_cross.
    rewrite (iter_f'_arcT (m - 1) ltac:(lia)).
    f_equal. lia.
  Qed.

  (* Every merged-carrier element reached from `it 1 d` closes into ONE `f'`-orbit. *)
  Lemma merged_is_orbit_of_d1 : forall z,
    InArcD z \/ InArcT z -> same_orbit_b eqdec f' S' (it 1 d) z = true.
  Proof.
    intros z [[i [Hi Hz]] | [i [Hi Hz]]]; subst z.
    - apply (same_orbit_b_complete eqdec f' S' Hclos' Hinj' (it 1 d)); [ apply arcD_mem; lia | ].
      exists (i - 1)%nat. rewrite iter_f'_arcD by lia. f_equal. lia.
    - apply (same_orbit_b_complete eqdec f' S' Hclos' Hinj' (it 1 d)); [ apply arcD_mem; lia | ].
      exists (per1 - 1 + (i - 1))%nat. rewrite iter_f'_arcD_then_T by lia. reflexivity.
  Qed.

  (* -------------------------------------------------------------------------- *)
  (* Stage 5: the region dichotomy -- every S'-element is in one of the two      *)
  (* arcs or is Outside both original orbits entirely.                          *)
  (* -------------------------------------------------------------------------- *)

  (* Boolean "on d's or td's ORIGINAL (f,S) orbit" predicate. *)
  Definition inMO (x : A) : bool := orb (same_orbit_b eqdec f S d x) (same_orbit_b eqdec f S td x).

  Lemma merged_iff_inMO : forall x, In x S' -> ((InArcD x \/ InArcT x) <-> inMO x = true).
  Proof.
    intros x Hx. unfold inMO. rewrite Bool.orb_true_iff. split.
    - intros [[i [Hi Heq]] | [i [Hi Heq]]]; subst x.
      + left. apply (same_orbit_b_complete eqdec f S Hclos Hinj d HdS). exists i; reflexivity.
      + right. apply (same_orbit_b_complete eqdec f S Hclos Hinj td HtdS). exists i; reflexivity.
    - intros [Hd | Htd].
      + left. apply same_orbit_b_sound in Hd. destruct Hd as [n Hn].
        exists (n mod per1)%nat.
        assert (Hxi : x = it (n mod per1) d) by (rewrite <- it_mod_per1; symmetry; exact Hn).
        assert (Hlt : (n mod per1 < per1)%nat) by (apply Nat.mod_upper_bound; lia).
        destruct (proj1 (Hcarrier x) Hx) as [_ [Hxd _]].
        assert (Hne0 : (n mod per1) <> 0%nat) by (intro H0; apply Hxd; rewrite Hxi, H0; reflexivity).
        split; [ lia | exact Hxi ].
      + right. apply same_orbit_b_sound in Htd. destruct Htd as [n Hn].
        exists (n mod per2)%nat.
        assert (Hxi : x = it (n mod per2) td) by (rewrite <- it_mod_per2; symmetry; exact Hn).
        assert (Hlt : (n mod per2 < per2)%nat) by (apply Nat.mod_upper_bound; lia).
        destruct (proj1 (Hcarrier x) Hx) as [_ [_ Hxtd]].
        assert (Hne0 : (n mod per2) <> 0%nat) by (intro H0; apply Hxtd; rewrite Hxi, H0; reflexivity).
        split; [ lia | exact Hxi ].
  Qed.

  Definition Outside (z : A) : Prop := In z S' /\ ~ same_orbit f d z /\ ~ same_orbit f td z.

  Lemma arc_or_outside : forall z, In z S' -> InArcD z \/ InArcT z \/ Outside z.
  Proof.
    intros z Hz.
    destruct (inMO z) eqn:Hm.
    - destruct (proj2 (merged_iff_inMO z Hz) Hm) as [H | H]; [ left; exact H | right; left; exact H ].
    - right; right. split; [ exact Hz | ].
      split; intro Hso.
      + assert (inMO z = true)
          by (unfold inMO; apply Bool.orb_true_iff; left;
              apply (same_orbit_b_complete eqdec f S Hclos Hinj d HdS z); exact Hso).
        congruence.
      + assert (inMO z = true)
          by (unfold inMO; apply Bool.orb_true_iff; right;
              apply (same_orbit_b_complete eqdec f S Hclos Hinj td HtdS z); exact Hso).
        congruence.
  Qed.

  (* -------------------------------------------------------------------------- *)
  (* Stage 6: closure of the three regions under f', and the class-constancy of  *)
  (* `inMO` on BOTH sides -- the shape `count_classes_filter_split` needs.       *)
  (* -------------------------------------------------------------------------- *)

  Lemma f'_closes_arcD : forall z, InArcD z -> InArcD (f' z) \/ InArcT (f' z).
  Proof.
    intros z [i [Hi Hz]]. subst z.
    destruct (Nat.eq_dec i (per1 - 1)) as [Hwrap | Hint].
    - subst i. right. rewrite f'_arcD_wrap. exists 1%nat. split; [ lia | reflexivity ].
    - left. rewrite (f'_arcD_interior i ltac:(lia)). exists (i + 1)%nat. split; [ lia | reflexivity ].
  Qed.

  Lemma f'_closes_arcT : forall z, InArcT z -> InArcT (f' z) \/ InArcD (f' z).
  Proof.
    intros z [i [Hi Hz]]. subst z.
    destruct (Nat.eq_dec i (per2 - 1)) as [Hwrap | Hint].
    - subst i. right. rewrite f'_arcT_wrap. exists 1%nat. split; [ lia | reflexivity ].
    - left. rewrite (f'_arcT_interior i ltac:(lia)). exists (i + 1)%nat. split; [ lia | reflexivity ].
  Qed.

  Lemma f'_closes_merged : forall z, InArcD z \/ InArcT z -> InArcD (f' z) \/ InArcT (f' z).
  Proof.
    intros z [H | H].
    - exact (f'_closes_arcD z H).
    - destruct (f'_closes_arcT z H) as [H' | H']; [ right | left ]; exact H'.
  Qed.

  Lemma f'_eq_f_outside : forall z, Outside z -> f' z = f z.
  Proof.
    intros z [HzS' [Hnod Hnotd]].
    destruct (proj1 (Hcarrier z) HzS') as [HzS _].
    rewrite (Hf'spec z HzS').
    destruct (eqdec (f z) d) as [Hfd | _].
    - exfalso. apply Hnod.
      apply (same_orbit_sym eqdec f S Hclos Hinj z HzS d).
      exists 1%nat. cbn [OrbitCycle.iter]. exact Hfd.
    - destruct (eqdec (f z) td) as [Hftd | _].
      + exfalso. apply Hnotd.
        apply (same_orbit_sym eqdec f S Hclos Hinj z HzS td).
        exists 1%nat. cbn [OrbitCycle.iter]. exact Hftd.
      + reflexivity.
  Qed.

  Lemma f'_closes_outside : forall z, Outside z -> Outside (f' z).
  Proof.
    intros z Hz. pose proof Hz as [HzS' [Hnod Hnotd]].
    destruct (proj1 (Hcarrier z) HzS') as [HzS _].
    split; [ apply Hclos'; exact HzS' | split ].
    - rewrite (f'_eq_f_outside z Hz). intro Hso.
      apply Hnod. apply (same_orbit_trans f d (f z) z Hso).
      apply (same_orbit_sym eqdec f S Hclos Hinj z HzS (f z)).
      exists 1%nat. cbn [OrbitCycle.iter]. reflexivity.
    - rewrite (f'_eq_f_outside z Hz). intro Hso.
      apply Hnotd. apply (same_orbit_trans f td (f z) z Hso).
      apply (same_orbit_sym eqdec f S Hclos Hinj z HzS (f z)).
      exists 1%nat. cbn [OrbitCycle.iter]. reflexivity.
  Qed.

  Lemma f'_orbit_preserves_merged : forall n z,
    (InArcD z \/ InArcT z) -> (InArcD (it' n z) \/ InArcT (it' n z)).
  Proof.
    intros n. induction n as [| n IH]; intros z Hz.
    - exact Hz.
    - cbn [OrbitCycle.iter]. apply f'_closes_merged. apply IH. exact Hz.
  Qed.

  Lemma f'_orbit_preserves_outside : forall n z, Outside z -> Outside (it' n z).
  Proof.
    intros n. induction n as [| n IH]; intros z Hz.
    - exact Hz.
    - cbn [OrbitCycle.iter]. apply f'_closes_outside. apply IH. exact Hz.
  Qed.

  (* OUTSIDE BRIDGE: f' and f agree along an Outside orbit, so the two
     same_orbit_b's (different carriers!) agree there. *)
  Lemma iter_f'_eq_iter_f_outside : forall n z, Outside z -> it' n z = it n z.
  Proof.
    intros n. induction n as [| n IH]; intros z Hz.
    - reflexivity.
    - cbn [OrbitCycle.iter]. rewrite (IH z Hz).
      apply f'_eq_f_outside. rewrite <- (IH z Hz).
      apply f'_orbit_preserves_outside. exact Hz.
  Qed.

  Lemma merged_or_outside_f'_class_constant_prop : forall x y,
    In x S' -> In y S' -> same_orbit f' x y ->
    ((InArcD x \/ InArcT x) <-> (InArcD y \/ InArcT y)).
  Proof.
    intros x y HxS' HyS' Hxy.
    assert (Hfwd : forall a b, In a S' -> same_orbit f' a b ->
                     (InArcD a \/ InArcT a) -> (InArcD b \/ InArcT b)).
    { intros a b HaS' [n Hn] Ha. subst b. apply f'_orbit_preserves_merged. exact Ha. }
    split.
    - intro Hdx. exact (Hfwd x y HxS' Hxy Hdx).
    - intro Hdy.
      assert (Hyx : same_orbit f' y x)
        by (exact (same_orbit_sym eqdec f' S' Hclos' Hinj' x HxS' y Hxy)).
      exact (Hfwd y x HyS' Hyx Hdy).
  Qed.

  Lemma merged_f'_class_constant : forall x y,
    In x S' -> In y S' -> same_orbit_b eqdec f' S' x y = true -> inMO x = inMO y.
  Proof.
    intros x y Hx Hy Hb. apply same_orbit_b_sound in Hb.
    destruct (merged_or_outside_f'_class_constant_prop x y Hx Hy Hb) as [Hfwd Hbwd].
    destruct (inMO x) eqn:Ex; destruct (inMO y) eqn:Ey; try reflexivity; exfalso.
    - assert (InArcD x \/ InArcT x) by (apply (merged_iff_inMO x Hx); exact Ex).
      assert (InArcD y \/ InArcT y) by (apply Hfwd; assumption).
      assert (inMO y = true) by (apply (merged_iff_inMO y Hy); assumption).
      congruence.
    - assert (InArcD y \/ InArcT y) by (apply (merged_iff_inMO y Hy); exact Ey).
      assert (InArcD x \/ InArcT x) by (apply Hbwd; assumption).
      assert (inMO x = true) by (apply (merged_iff_inMO x Hx); assumption).
      congruence.
  Qed.

  Lemma same_orbit_b_base_class_constant : forall (base x y : A),
    In base S -> In x S -> In y S ->
    same_orbit_b eqdec f S x y = true -> same_orbit_b eqdec f S base x = same_orbit_b eqdec f S base y.
  Proof.
    intros base x y Hbase Hx Hy Hxy.
    destruct (same_orbit_b eqdec f S base x) eqn:Ex;
      destruct (same_orbit_b eqdec f S base y) eqn:Ey; try reflexivity; exfalso.
    - assert (same_orbit_b eqdec f S base y = true)
        by (apply (same_orbit_b_trans_on eqdec f S Hclos Hinj base x y Hbase Hx Hy Ex Hxy));
        congruence.
    - assert (same_orbit_b eqdec f S y x = true)
        by (apply (same_orbit_b_sym_on eqdec f S Hclos Hinj x y Hx Hy Hxy)).
      assert (same_orbit_b eqdec f S base x = true)
        by (apply (same_orbit_b_trans_on eqdec f S Hclos Hinj base y x Hbase Hy Hx Ey H));
        congruence.
  Qed.

  Lemma inMO_fS_class_constant : forall x y, In x S -> In y S ->
    same_orbit_b eqdec f S x y = true -> inMO x = inMO y.
  Proof.
    intros x y Hx Hy Hxy. unfold inMO.
    rewrite (same_orbit_b_base_class_constant d x y HdS Hx Hy Hxy).
    rewrite (same_orbit_b_base_class_constant td x y HtdS Hx Hy Hxy).
    reflexivity.
  Qed.

  (* -------------------------------------------------------------------------- *)
  (* Stage 7: the counts.  On (f,S), the `inMO` block is TWO classes (d's orbit  *)
  (* and td's orbit, disjoint).  On (f',S'), it is exactly ONE (the merge).      *)
  (* -------------------------------------------------------------------------- *)

  Lemma inMO_block_fS_eq_2 : count_classes (same_orbit_b eqdec f S) (filter inMO S) = 2%nat.
  Proof.
    set (isD := fun x => same_orbit_b eqdec f S d x).
    assert (Hmem : forall x, In x (filter inMO S) -> In x S)
      by (intros x Hx; apply filter_In in Hx; tauto).
    assert (HccD : forall x y, In x (filter inMO S) -> In y (filter inMO S) ->
              same_orbit_b eqdec f S x y = true -> isD x = isD y).
    { intros x y Hx Hy Hxy. unfold isD.
      exact (same_orbit_b_base_class_constant d x y HdS (Hmem x Hx) (Hmem y Hy) Hxy). }
    assert (Htr : forall x y z, In x (filter inMO S) -> In y (filter inMO S) -> In z (filter inMO S) ->
              same_orbit_b eqdec f S x y = true -> same_orbit_b eqdec f S y z = true ->
              same_orbit_b eqdec f S x z = true).
    { intros x y z Hx Hy Hz Hxy Hyz.
      exact (same_orbit_b_trans_on eqdec f S Hclos Hinj x y z (Hmem x Hx) (Hmem y Hy) (Hmem z Hz) Hxy Hyz). }
    rewrite (count_classes_filter_split (same_orbit_b eqdec f S) (same_orbit_b_refl eqdec f S)
               isD (filter inMO S) HccD Htr).
    assert (HdinMO : In d (filter inMO S)).
    { apply filter_In. split; [ exact HdS | unfold inMO ].
      apply Bool.orb_true_iff. left. apply same_orbit_b_refl. }
    assert (HtdinMO : In td (filter inMO S)).
    { apply filter_In. split; [ exact HtdS | unfold inMO ].
      apply Bool.orb_true_iff. right. apply same_orbit_b_refl. }
    assert (HblockD : count_classes (same_orbit_b eqdec f S) (filter isD (filter inMO S)) = 1%nat).
    { apply (count_classes_eq_1 (same_orbit_b eqdec f S) (same_orbit_b_refl eqdec f S)).
      - intro Hnil.
        assert (Hdin : In d (filter isD (filter inMO S)))
          by (apply filter_In; split; [ exact HdinMO | unfold isD; apply same_orbit_b_refl ]).
        rewrite Hnil in Hdin. destruct Hdin.
      - intros x y Hx Hy. apply filter_In in Hx. apply filter_In in Hy.
        destruct Hx as [HxM Hxd]. destruct Hy as [HyM Hyd]. unfold isD in Hxd, Hyd.
        assert (Hxd' : same_orbit_b eqdec f S x d = true)
          by (apply (same_orbit_b_sym_on eqdec f S Hclos Hinj d x HdS (Hmem x HxM) Hxd)).
        exact (same_orbit_b_trans_on eqdec f S Hclos Hinj x d y (Hmem x HxM) HdS (Hmem y HyM) Hxd' Hyd). }
    assert (HblockNotD : count_classes (same_orbit_b eqdec f S)
              (filter (fun x => negb (isD x)) (filter inMO S)) = 1%nat).
    { apply (count_classes_eq_1 (same_orbit_b eqdec f S) (same_orbit_b_refl eqdec f S)).
      - intro Hnil.
        assert (HtdnD : negb (isD td) = true).
        { unfold isD. destruct (same_orbit_b eqdec f S d td) eqn:E; [ exfalso | reflexivity ].
          apply Hnso. apply same_orbit_b_sound in E. exact E. }
        assert (Htdin : In td (filter (fun x => negb (isD x)) (filter inMO S)))
          by (apply filter_In; split; [ exact HtdinMO | exact HtdnD ]).
        rewrite Hnil in Htdin. destruct Htdin.
      - intros x y Hx Hy. apply filter_In in Hx. apply filter_In in Hy.
        destruct Hx as [HxM HxnD]. destruct Hy as [HyM HynD].
        unfold isD in HxnD, HynD. apply Bool.negb_true_iff in HxnD, HynD.
        pose proof HxM as HxM0. pose proof HyM as HyM0.
        apply filter_In in HxM0. apply filter_In in HyM0.
        destruct HxM0 as [HxS HxMO]. destruct HyM0 as [HyS HyMO].
        unfold inMO in HxMO, HyMO. apply Bool.orb_true_iff in HxMO, HyMO.
        assert (HxT : same_orbit_b eqdec f S td x = true)
          by (destruct HxMO as [Hc | Hc]; [ congruence | exact Hc ]).
        assert (HyT : same_orbit_b eqdec f S td y = true)
          by (destruct HyMO as [Hc | Hc]; [ congruence | exact Hc ]).
        assert (Hxtd : same_orbit_b eqdec f S x td = true)
          by (apply (same_orbit_b_sym_on eqdec f S Hclos Hinj td x HtdS HxS HxT)).
        exact (same_orbit_b_trans_on eqdec f S Hclos Hinj x td y HxS HtdS HyS Hxtd HyT). }
    rewrite HblockD, HblockNotD. reflexivity.
  Qed.

  (* On (f',S'), the `inMO` block is a SINGLE class: every member is `same_orbit
     f'`-related to `it 1 d` (`merged_is_orbit_of_d1`, via `merged_iff_inMO`). *)
  Lemma inMO_block_f'S'_eq_1 : count_classes (same_orbit_b eqdec f' S') (filter inMO S') = 1%nat.
  Proof.
    apply (count_classes_eq_1 (same_orbit_b eqdec f' S') (same_orbit_b_refl eqdec f' S')).
    - intro Hnil.
      assert (H1S' : In (it 1 d) S') by (apply arcD_mem; lia).
      assert (Hin : In (it 1 d) (filter inMO S')).
      { apply filter_In. split; [ exact H1S' | ].
        apply (proj1 (merged_iff_inMO (it 1 d) H1S')).
        left. exists 1%nat. split; [ lia | reflexivity ]. }
      rewrite Hnil in Hin. destruct Hin.
    - intros x y Hx Hy. apply filter_In in Hx. apply filter_In in Hy.
      destruct Hx as [HxS' HxMO]. destruct Hy as [HyS' HyMO].
      assert (Hxm : InArcD x \/ InArcT x) by (apply (merged_iff_inMO x HxS'); exact HxMO).
      assert (Hym : InArcD y \/ InArcT y) by (apply (merged_iff_inMO y HyS'); exact HyMO).
      assert (Hx1 : same_orbit_b eqdec f' S' (it 1 d) x = true) by (apply merged_is_orbit_of_d1; exact Hxm).
      assert (Hy1 : same_orbit_b eqdec f' S' (it 1 d) y = true) by (apply merged_is_orbit_of_d1; exact Hym).
      assert (H1S' : In (it 1 d) S') by (apply arcD_mem; lia).
      assert (Hx1' : same_orbit_b eqdec f' S' x (it 1 d) = true)
        by (apply (same_orbit_b_sym_on eqdec f' S' Hclos' Hinj' (it 1 d) x H1S' HxS' Hx1)).
      exact (same_orbit_b_trans_on eqdec f' S' Hclos' Hinj' x (it 1 d) y HxS' H1S' HyS' Hx1' Hy1).
  Qed.

  (* The complement (Outside both original orbits) is untouched by the surgery. *)
  Lemma inMO_complement_eq :
    count_classes (same_orbit_b eqdec f' S') (filter (fun x => negb (inMO x)) S')
    = count_classes (same_orbit_b eqdec f S) (filter (fun x => negb (inMO x)) S).
  Proof.
    assert (HinMO_d : inMO d = true) by (unfold inMO; apply Bool.orb_true_iff; left; apply same_orbit_b_refl).
    assert (HinMO_td : inMO td = true) by (unfold inMO; apply Bool.orb_true_iff; right; apply same_orbit_b_refl).
    assert (HmemS : forall z, In z (filter (fun x => negb (inMO x)) S) -> In z S)
      by (intros z Hz; apply filter_In in Hz; tauto).
    assert (Hmem' : forall z, In z (filter (fun x => negb (inMO x)) S') -> In z S)
      by (intros z Hz; apply filter_In in Hz; destruct Hz as [HzS' _];
          destruct (proj1 (Hcarrier z) HzS') as [HzS _]; exact HzS).
    assert (Hiff : forall z, In z (filter (fun x => negb (inMO x)) S')
                          <-> In z (filter (fun x => negb (inMO x)) S)).
    { intro z. split.
      - intro Hz. pose proof Hz as Hz0. apply filter_In in Hz. destruct Hz as [HzS' HznMO].
        apply filter_In. split; [ exact (Hmem' z Hz0) | exact HznMO ].
      - intro Hz. apply filter_In in Hz. destruct Hz as [HzS HznMO].
        apply filter_In. split; [ | exact HznMO ].
        apply (proj2 (Hcarrier z)). split; [ exact HzS | split ].
        + intro He. subst z. cbv beta in HznMO. rewrite HinMO_d in HznMO. discriminate HznMO.
        + intro He. subst z. cbv beta in HznMO. rewrite HinMO_td in HznMO. discriminate HznMO. }
    assert (Hswitch : count_classes (same_orbit_b eqdec f' S') (filter (fun x => negb (inMO x)) S')
                    = count_classes (same_orbit_b eqdec f S) (filter (fun x => negb (inMO x)) S')).
    { unfold count_classes. f_equal. apply class_reps_ext_on.
      intros x y Hx Hy.
      pose proof Hx as Hx0. pose proof Hy as Hy0.
      apply filter_In in Hx. destruct Hx as [HxS' HxnMO].
      apply filter_In in Hy. destruct Hy as [HyS' HynMO].
      cbv beta in HxnMO, HynMO.
      apply Bool.negb_true_iff in HxnMO, HynMO.
      assert (HOx : Outside x) by (split; [ exact HxS' | ];
        split; intro Hso;
          [ assert (inMO x = true) by (unfold inMO; apply Bool.orb_true_iff; left;
              apply (same_orbit_b_complete eqdec f S Hclos Hinj d HdS x); exact Hso); congruence
          | assert (inMO x = true) by (unfold inMO; apply Bool.orb_true_iff; right;
              apply (same_orbit_b_complete eqdec f S Hclos Hinj td HtdS x); exact Hso); congruence ]).
      assert (HOy : Outside y) by (split; [ exact HyS' | ];
        split; intro Hso;
          [ assert (inMO y = true) by (unfold inMO; apply Bool.orb_true_iff; left;
              apply (same_orbit_b_complete eqdec f S Hclos Hinj d HdS y); exact Hso); congruence
          | assert (inMO y = true) by (unfold inMO; apply Bool.orb_true_iff; right;
              apply (same_orbit_b_complete eqdec f S Hclos Hinj td HtdS y); exact Hso); congruence ]).
      destruct (same_orbit_b eqdec f' S' x y) eqn:E'; destruct (same_orbit_b eqdec f S x y) eqn:E;
        try reflexivity; exfalso.
      - apply same_orbit_b_sound in E'.
        assert (Hxy : same_orbit f x y)
          by (destruct E' as [n Hn]; exists n;
              rewrite <- (iter_f'_eq_iter_f_outside n x HOx); exact Hn).
        assert (HxS : In x S) by (exact (proj1 (proj1 (Hcarrier x) HxS'))).
        assert (same_orbit_b eqdec f S x y = true)
          by (apply (same_orbit_b_complete eqdec f S Hclos Hinj x HxS y); exact Hxy).
        congruence.
      - apply same_orbit_b_sound in E.
        assert (Hxy : same_orbit f' x y)
          by (destruct E as [n Hn]; exists n;
              rewrite (iter_f'_eq_iter_f_outside n x HOx); exact Hn).
        assert (same_orbit_b eqdec f' S' x y = true)
          by (apply (same_orbit_b_complete eqdec f' S' Hclos' Hinj' x HxS' y); exact Hxy).
        congruence. }
    rewrite Hswitch.
    apply Nat.le_antisymm.
    - apply (class_reps_length_mono (same_orbit_b eqdec f S) (same_orbit_b_refl eqdec f S)
               (filter (fun x => negb (inMO x)) S') (filter (fun x => negb (inMO x)) S)).
      + intros x y Hx Hy. apply (same_orbit_b_sym_on eqdec f S Hclos Hinj x y (HmemS x Hx) (HmemS y Hy)).
      + intros x y z Hx Hy Hz.
        apply (same_orbit_b_trans_on eqdec f S Hclos Hinj x y z (HmemS x Hx) (HmemS y Hy) (HmemS z Hz)).
      + intros z Hz. exact (proj1 (Hiff z) Hz).
    - apply (class_reps_length_mono (same_orbit_b eqdec f S) (same_orbit_b_refl eqdec f S)
               (filter (fun x => negb (inMO x)) S) (filter (fun x => negb (inMO x)) S')).
      + intros x y Hx Hy. apply (same_orbit_b_sym_on eqdec f S Hclos Hinj x y (Hmem' x Hx) (Hmem' y Hy)).
      + intros x y z Hx Hy Hz.
        apply (same_orbit_b_trans_on eqdec f S Hclos Hinj x y z (Hmem' x Hx) (Hmem' y Hy) (Hmem' z Hz)).
      + intros z Hz. exact (proj2 (Hiff z) Hz).
  Qed.

  (* `cycle_count` is the `ClassCount` class count of the same-orbit relation
     (mirrors `PermCycleSplice.cycle_count_as_count_classes`, restated locally
     since that one is scoped to the `CycleSplice` section's own hypotheses). *)
  Lemma cycle_count_as_count_classes : forall (g : A -> A) (T : list A),
    cycle_count eqdec g T = count_classes (same_orbit_b eqdec g T) T.
  Proof. intros g T. unfold cycle_count, orbit_reps, count_classes. reflexivity. Qed.

  (* THE -1: the merge surgery lowers the orbit count by exactly one. *)
  Theorem cycle_count_merge :
    cycle_count eqdec f' S' = (cycle_count eqdec f S - 1)%nat.
  Proof.
    assert (Hcc_fS : forall x y, In x S -> In y S ->
              same_orbit_b eqdec f S x y = true -> inMO x = inMO y)
      by (exact inMO_fS_class_constant).
    assert (Htr_fS : forall x y z, In x S -> In y S -> In z S ->
              same_orbit_b eqdec f S x y = true -> same_orbit_b eqdec f S y z = true ->
              same_orbit_b eqdec f S x z = true)
      by (intros x y z Hx Hy Hz; apply (same_orbit_b_trans_on eqdec f S Hclos Hinj x y z Hx Hy Hz)).
    assert (Hcc_f'S' : forall x y, In x S' -> In y S' ->
              same_orbit_b eqdec f' S' x y = true -> inMO x = inMO y)
      by (exact merged_f'_class_constant).
    assert (Htr_f'S' : forall x y z, In x S' -> In y S' -> In z S' ->
              same_orbit_b eqdec f' S' x y = true -> same_orbit_b eqdec f' S' y z = true ->
              same_orbit_b eqdec f' S' x z = true)
      by (intros x y z Hx Hy Hz; apply (same_orbit_b_trans_on eqdec f' S' Hclos' Hinj' x y z Hx Hy Hz)).
    rewrite (cycle_count_as_count_classes f' S'), (cycle_count_as_count_classes f S).
    rewrite (count_classes_filter_split (same_orbit_b eqdec f' S')
               (same_orbit_b_refl eqdec f' S') inMO S' Hcc_f'S' Htr_f'S').
    rewrite (count_classes_filter_split (same_orbit_b eqdec f S)
               (same_orbit_b_refl eqdec f S) inMO S Hcc_fS Htr_fS).
    rewrite inMO_block_f'S'_eq_1, inMO_block_fS_eq_2, inMO_complement_eq.
    lia.
  Qed.

End CycleMerge.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Thin instances of ClassCount; allowlist axioms only.          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions cycle_count_merge.
