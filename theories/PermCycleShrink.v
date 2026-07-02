(* ==========================================================================
   PermCycleShrink.v

   Cycle-count SHRINK: the k=1 boundary case `PermCycleSplice.v`'s SPLIT
   excludes outright (`Hk_range : 2 <= k <= per - 2`).

   When `td` is reached from `d` in exactly ONE step (`f d = td`, i.e. `d`'s
   predecessor role and `td`'s successor role COLLIDE: `d`'s only predecessor
   IS `td` itself, which is also being deleted), the same cross-wiring
   redirect (`FaceStepRemove.fstep_E_minus_splice`, same_face-agnostic) does
   NOT split the orbit into two -- there is no room for a first arc (indices
   `1..k-1 = 1..0`, empty) -- it just SHORTENS the SAME orbit by the two
   deleted points, leaving the orbit COUNT UNCHANGED.

   This is exactly the DART-LAYER situation at a degree-1 (leaf) vertex: its
   unique outgoing dart `d0` and the arriving twin `td0 := twin d0` form a
   spur (`fstep D td0 = d0`, `NoShortFaces.v`'s excluded configuration) --
   [EF-1]/[EF-2]/[EF-3] all implicitly assume `no_spurs`, so NONE of them
   apply to this case; this file is the missing companion for [EF-4]'s
   degree-1 peeling step.  The `per >= 3` hypothesis excludes the further
   degenerate sub-case where `{d, td}` is an ISOLATED 2-cycle (an edge with
   BOTH endpoints degree 1, i.e. a lone K2 component) -- there the whole
   orbit vanishes with the deletion, a genuinely different (simpler) delta,
   not attempted here.

   Pure combinatorial wiring; no `Admitted` / `Axiom` / `Parameter`; allowlist
   axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import List Arith Lia Bool.
From NTS.Proofs Require Import OrbitCycle ClassCount PermCycleCount PermCycleSplice.

Import ListNotations.

Section CycleShrink.
  Context {A : Type}.
  Variable eqdec : forall a b : A, {a = b} + {a <> b}.
  Variable f : A -> A.
  Variable S : list A.
  Hypothesis Hclos : forall x, In x S -> In (f x) S.
  Hypothesis Hinj : forall a b, In a S -> In b S -> f a = f b -> a = b.

  Variable d td : A.
  Hypothesis HdS : In d S.
  Hypothesis Hdtd : d <> td.
  Hypothesis Hf_d_td : f d = td.

  Variable per : nat.
  Hypothesis Hper_return : OrbitCycle.iter f per d = d.
  Hypothesis Hper_ge3 : (3 <= per)%nat.
  Hypothesis Hper_min : forall j, (1 <= j < per)%nat -> OrbitCycle.iter f j d <> d.

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

  Lemma td_is_it1 : td = it 1 d.
  Proof. cbn [OrbitCycle.iter]. symmetry. exact Hf_d_td. Qed.

  Lemma orbit_in_S : forall i, In (it i d) S.
  Proof. intro i. apply OrbitCycle.iter_in; [ exact Hclos | exact HdS ]. Qed.

  Lemma period_orbit_distinct :
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

  Lemma it_mod_per : forall n, it n d = it (n mod per) d.
  Proof.
    intro n.
    rewrite (Nat.div_mod_eq n per) at 1.
    rewrite Nat.add_comm, OrbitCycle.iter_comp, (Nat.mul_comm per (n / per)).
    rewrite (PermCycleCount.iter_period_mult f per d Hper_return (n / per)).
    reflexivity.
  Qed.

  (* The single surviving arc: everything on `d`'s orbit except `d` and `td`
     itself (indices 2..per-1 -- index 1 IS `td`, excluded). *)
  Definition InArc (z : A) : Prop := exists i, (2 <= i <= per - 1)%nat /\ z = it i d.

  Lemma arc_mem : forall i, (2 <= i <= per - 1)%nat -> In (it i d) S'.
  Proof.
    intros i Hi. apply (proj2 (Hcarrier (it i d))).
    split; [ apply orbit_in_S | split ].
    - apply Hper_min. lia.
    - intro Heq. rewrite td_is_it1 in Heq.
      assert (i = 1%nat) by (apply (period_orbit_distinct i 1); [ lia | lia | exact Heq ]). lia.
  Qed.

  Lemma f'_arc_interior : forall i, (2 <= i <= per - 2)%nat -> f' (it i d) = it (i + 1) d.
  Proof.
    intros i Hi.
    rewrite (Hf'spec (it i d) (arc_mem i ltac:(lia))).
    assert (Hf : f (it i d) = it (i + 1) d) by (rewrite PermCycleSplice.iter_add1; reflexivity).
    rewrite Hf.
    destruct (eqdec (it (i + 1) d) d) as [Hc | _].
    - exfalso. apply (Hper_min (i + 1)); [ lia | exact Hc ].
    - destruct (eqdec (it (i + 1) d) td) as [Hc | _].
      + exfalso. rewrite td_is_it1 in Hc.
        assert (i + 1 = 1)%nat by (apply (period_orbit_distinct (i+1) 1); [ lia | lia | exact Hc ]). lia.
      + reflexivity.
  Qed.

  (* The wrap: the arc's last element goes back to the arc's first (index 2),
     skipping over `td` and `d` (which sit at indices 1 and 0/per). *)
  Lemma f'_arc_wrap : f' (it (per - 1) d) = it 2 d.
  Proof.
    rewrite (Hf'spec (it (per - 1) d) (arc_mem (per - 1) ltac:(lia))).
    assert (Hf : f (it (per - 1) d) = d)
      by (rewrite <- PermCycleSplice.iter_add1;
          replace (per - 1 + 1)%nat with per by lia; exact Hper_return).
    rewrite Hf.
    destruct (eqdec d d) as [_ | Hc]; [ | exfalso; apply Hc; reflexivity ].
    rewrite td_is_it1. rewrite <- PermCycleSplice.iter_add1. reflexivity.
  Qed.

  Lemma iter_f'_arc : forall m, (2 + m <= per - 1)%nat -> it' m (it 2 d) = it (2 + m) d.
  Proof.
    induction m as [| m IH]; intro Hm.
    - reflexivity.
    - replace (Datatypes.S m) with (m + 1)%nat by lia.
      rewrite PermCycleSplice.iter_add1, IH by lia.
      rewrite (f'_arc_interior (2 + m)) by lia.
      f_equal; lia.
  Qed.

  Lemma arc_is_orbit_of_2 : forall i, (2 <= i <= per - 1)%nat ->
    same_orbit_b eqdec f' S' (it 2 d) (it i d) = true.
  Proof.
    intros i Hi.
    apply (same_orbit_b_complete eqdec f' S' Hclos' Hinj' (it 2 d)); [ apply arc_mem; lia | ].
    exists (i - 2)%nat. rewrite iter_f'_arc by lia. f_equal. lia.
  Qed.

  (* Boolean "on d's ORIGINAL (f,S) orbit" predicate. *)
  Definition inO (x : A) : bool := same_orbit_b eqdec f S d x.

  Lemma inO_iff_arc : forall x, In x S' -> (InArc x <-> inO x = true).
  Proof.
    intros x Hx. unfold inO. split.
    - intros [i [Hi Heq]]; subst x.
      apply (same_orbit_b_complete eqdec f S Hclos Hinj d HdS). exists i; reflexivity.
    - intro Hd. apply same_orbit_b_sound in Hd. destruct Hd as [n Hn].
      exists (n mod per)%nat.
      assert (Hxi : x = it (n mod per) d) by (rewrite <- it_mod_per; symmetry; exact Hn).
      assert (Hlt : (n mod per < per)%nat) by (apply Nat.mod_upper_bound; lia).
      destruct (proj1 (Hcarrier x) Hx) as [_ [Hxd Hxtd]].
      assert (Hne0 : (n mod per) <> 0%nat) by (intro H0; apply Hxd; rewrite Hxi, H0; reflexivity).
      assert (Hne1 : (n mod per) <> 1%nat)
        by (intro H1; apply Hxtd; rewrite Hxi, H1, <- td_is_it1; reflexivity).
      split; [ lia | exact Hxi ].
  Qed.

  Lemma f'_closes_arc : forall z, InArc z -> InArc (f' z).
  Proof.
    intros z [i [Hi Hz]]. subst z.
    destruct (Nat.eq_dec i (per - 1)) as [Hwrap | Hint].
    - subst i. rewrite f'_arc_wrap. exists 2%nat. split; [ lia | reflexivity ].
    - rewrite (f'_arc_interior i ltac:(lia)). exists (i + 1)%nat. split; [ lia | reflexivity ].
  Qed.

  Definition Outside (z : A) : Prop := In z S' /\ ~ same_orbit f d z.

  Lemma arc_or_outside : forall z, In z S' -> InArc z \/ Outside z.
  Proof.
    intros z Hz.
    destruct (inO z) eqn:Hm.
    - left. apply (inO_iff_arc z Hz). exact Hm.
    - right. split; [ exact Hz | ].
      intro Hso. assert (inO z = true) by (unfold inO; apply (same_orbit_b_complete eqdec f S Hclos Hinj d HdS z); exact Hso).
      congruence.
  Qed.

  Lemma f'_eq_f_outside : forall z, Outside z -> f' z = f z.
  Proof.
    intros z [HzS' Hnod].
    destruct (proj1 (Hcarrier z) HzS') as [HzS _].
    rewrite (Hf'spec z HzS').
    destruct (eqdec (f z) d) as [Hfd | _].
    - exfalso. apply Hnod.
      apply (same_orbit_sym eqdec f S Hclos Hinj z HzS d).
      exists 1%nat. cbn [OrbitCycle.iter]. exact Hfd.
    - destruct (eqdec (f z) td) as [Hftd | _].
      + exfalso. apply Hnod.
        assert (Hdtd_orbit : same_orbit f d td)
          by (exists 1%nat; cbn [OrbitCycle.iter]; exact Hf_d_td).
        apply (same_orbit_trans f d td z Hdtd_orbit).
        apply (same_orbit_sym eqdec f S Hclos Hinj z HzS td).
        exists 1%nat. cbn [OrbitCycle.iter]. exact Hftd.
      + reflexivity.
  Qed.

  Lemma f'_closes_outside : forall z, Outside z -> Outside (f' z).
  Proof.
    intros z Hz. pose proof Hz as [HzS' Hnod].
    destruct (proj1 (Hcarrier z) HzS') as [HzS _].
    split; [ apply Hclos'; exact HzS' | ].
    rewrite (f'_eq_f_outside z Hz). intro Hso.
    apply Hnod. apply (same_orbit_trans f d (f z) z Hso).
    apply (same_orbit_sym eqdec f S Hclos Hinj z HzS (f z)).
    exists 1%nat. cbn [OrbitCycle.iter]. reflexivity.
  Qed.

  Lemma f'_orbit_preserves_outside : forall n z, Outside z -> Outside (it' n z).
  Proof.
    intros n. induction n as [| n IH]; intros z Hz.
    - exact Hz.
    - cbn [OrbitCycle.iter]. apply f'_closes_outside. apply IH. exact Hz.
  Qed.

  Lemma iter_f'_eq_iter_f_outside : forall n z, Outside z -> it' n z = it n z.
  Proof.
    intros n. induction n as [| n IH]; intros z Hz.
    - reflexivity.
    - cbn [OrbitCycle.iter]. rewrite (IH z Hz).
      apply f'_eq_f_outside. rewrite <- (IH z Hz).
      apply f'_orbit_preserves_outside. exact Hz.
  Qed.

  Lemma inO_fS_class_constant : forall x y, In x S -> In y S ->
    same_orbit_b eqdec f S x y = true -> inO x = inO y.
  Proof.
    intros x y Hx Hy Hxy. unfold inO.
    destruct (same_orbit_b eqdec f S d x) eqn:Ex;
      destruct (same_orbit_b eqdec f S d y) eqn:Ey; try reflexivity; exfalso.
    - assert (same_orbit_b eqdec f S d y = true)
        by (apply (same_orbit_b_trans_on eqdec f S Hclos Hinj d x y HdS Hx Hy Ex Hxy)); congruence.
    - assert (same_orbit_b eqdec f S y x = true)
        by (apply (same_orbit_b_sym_on eqdec f S Hclos Hinj x y Hx Hy Hxy)).
      assert (same_orbit_b eqdec f S d x = true)
        by (apply (same_orbit_b_trans_on eqdec f S Hclos Hinj d y x HdS Hy Hx Ey H)); congruence.
  Qed.

  Lemma f'_orbit_preserves_arc : forall n z, InArc z -> InArc (it' n z).
  Proof.
    intros n. induction n as [| n IH]; intros z Hz.
    - exact Hz.
    - cbn [OrbitCycle.iter]. apply f'_closes_arc. apply IH. exact Hz.
  Qed.

  (* CLASS-CONSTANCY of "in O" along f'-orbits (Prop core), mirroring
     PermCycleSplice.splice_inO_f'_class_constant_prop exactly. *)
  Lemma inO_f'S'_class_constant_prop : forall x y,
    In x S' -> In y S' -> same_orbit f' x y ->
    (same_orbit f d x <-> same_orbit f d y).
  Proof.
    intros x y HxS' HyS' Hxy.
    assert (Hfwd : forall a b, In a S' -> same_orbit f' a b ->
                     same_orbit f d a -> same_orbit f d b).
    { intros a b HaS' [n Hn] Hda. subst b.
      destruct (arc_or_outside a HaS') as [Ha | Ha].
      - destruct (f'_orbit_preserves_arc n a Ha) as [j [_ Hj']].
        exists j. symmetry. exact Hj'.
      - exfalso. destruct Ha as [_ Hna]. exact (Hna Hda). }
    split.
    - intro Hdx. exact (Hfwd x y HxS' Hxy Hdx).
    - intro Hdy.
      assert (Hyx : same_orbit f' y x)
        by (exact (same_orbit_sym eqdec f' S' Hclos' Hinj' x HxS' y Hxy)).
      exact (Hfwd y x HyS' Hyx Hdy).
  Qed.

  Lemma inO_f'S'_class_constant : forall x y, In x S' -> In y S' ->
    same_orbit_b eqdec f' S' x y = true -> inO x = inO y.
  Proof.
    intros x y Hx Hy Hb. apply same_orbit_b_sound in Hb.
    destruct (inO_f'S'_class_constant_prop x y Hx Hy Hb) as [Hfwd Hbwd].
    unfold inO.
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

  Lemma inO_block_fS_eq_1 : count_classes (same_orbit_b eqdec f S) (filter inO S) = 1%nat.
  Proof.
    apply (count_classes_eq_1 (same_orbit_b eqdec f S) (same_orbit_b_refl eqdec f S)).
    - intro Hnil.
      assert (Hd : In d (filter inO S))
        by (apply filter_In; split; [ exact HdS | unfold inO; apply same_orbit_b_refl ]).
      rewrite Hnil in Hd. exact Hd.
    - intros x y Hx Hy.
      apply filter_In in Hx. destruct Hx as [HxS Hxo].
      apply filter_In in Hy. destruct Hy as [HyS Hyo].
      unfold inO in Hxo, Hyo.
      assert (Hxd : same_orbit_b eqdec f S x d = true)
        by (apply (same_orbit_b_sym_on eqdec f S Hclos Hinj d x HdS HxS Hxo)).
      exact (same_orbit_b_trans_on eqdec f S Hclos Hinj x d y HxS HdS HyS Hxd Hyo).
  Qed.

  Lemma inO_block_f'S'_eq_1 : count_classes (same_orbit_b eqdec f' S') (filter inO S') = 1%nat.
  Proof.
    apply (count_classes_eq_1 (same_orbit_b eqdec f' S') (same_orbit_b_refl eqdec f' S')).
    - intro Hnil.
      assert (H2S' : In (it 2 d) S') by (apply arc_mem; lia).
      assert (Hin : In (it 2 d) (filter inO S')).
      { apply filter_In. split; [ exact H2S' | ].
        apply (proj1 (inO_iff_arc (it 2 d) H2S')). exists 2%nat. split; [ lia | reflexivity ]. }
      rewrite Hnil in Hin. destruct Hin.
    - intros x y Hx Hy. apply filter_In in Hx. apply filter_In in Hy.
      destruct Hx as [HxS' HxO]. destruct Hy as [HyS' HyO].
      assert (Hxa : InArc x) by (apply (inO_iff_arc x HxS'); exact HxO).
      assert (Hya : InArc y) by (apply (inO_iff_arc y HyS'); exact HyO).
      destruct Hxa as [i [Hi Hxi]]. destruct Hya as [j [Hj Hyj]]. subst x y.
      assert (H2S' : In (it 2 d) S') by (apply arc_mem; lia).
      assert (Hx2 : same_orbit_b eqdec f' S' (it 2 d) (it i d) = true) by (apply arc_is_orbit_of_2; lia).
      assert (Hy2 : same_orbit_b eqdec f' S' (it 2 d) (it j d) = true) by (apply arc_is_orbit_of_2; lia).
      assert (Hx2' : same_orbit_b eqdec f' S' (it i d) (it 2 d) = true)
        by (apply (same_orbit_b_sym_on eqdec f' S' Hclos' Hinj' (it 2 d) (it i d) H2S' (arc_mem i ltac:(lia)) Hx2)).
      exact (same_orbit_b_trans_on eqdec f' S' Hclos' Hinj' (it i d) (it 2 d) (it j d)
               (arc_mem i ltac:(lia)) H2S' (arc_mem j ltac:(lia)) Hx2' Hy2).
  Qed.

  Lemma inO_complement_eq :
    count_classes (same_orbit_b eqdec f' S') (filter (fun x => negb (inO x)) S')
    = count_classes (same_orbit_b eqdec f S) (filter (fun x => negb (inO x)) S).
  Proof.
    assert (HinO_d : inO d = true) by (unfold inO; apply same_orbit_b_refl).
    assert (HinO_td : inO td = true)
      by (unfold inO; apply (same_orbit_b_complete eqdec f S Hclos Hinj d HdS td);
          rewrite td_is_it1; exists 1%nat; reflexivity).
    assert (HmemS : forall z, In z (filter (fun x => negb (inO x)) S) -> In z S)
      by (intros z Hz; apply filter_In in Hz; tauto).
    assert (Hmem' : forall z, In z (filter (fun x => negb (inO x)) S') -> In z S)
      by (intros z Hz; apply filter_In in Hz; destruct Hz as [HzS' _];
          destruct (proj1 (Hcarrier z) HzS') as [HzS _]; exact HzS).
    assert (Hiff : forall z, In z (filter (fun x => negb (inO x)) S')
                          <-> In z (filter (fun x => negb (inO x)) S)).
    { intro z. split.
      - intro Hz. pose proof Hz as Hz0. apply filter_In in Hz. destruct Hz as [HzS' HznO].
        apply filter_In. split; [ exact (Hmem' z Hz0) | exact HznO ].
      - intro Hz. apply filter_In in Hz. destruct Hz as [HzS HznO].
        apply filter_In. split; [ | exact HznO ].
        apply (proj2 (Hcarrier z)). split; [ exact HzS | split ].
        + intro He. subst z. cbv beta in HznO. rewrite HinO_d in HznO. discriminate HznO.
        + intro He. subst z. cbv beta in HznO. rewrite HinO_td in HznO. discriminate HznO. }
    assert (Hswitch : count_classes (same_orbit_b eqdec f' S') (filter (fun x => negb (inO x)) S')
                    = count_classes (same_orbit_b eqdec f S) (filter (fun x => negb (inO x)) S')).
    { unfold count_classes. f_equal. apply class_reps_ext_on.
      intros x y Hx Hy.
      pose proof Hx as Hx0. pose proof Hy as Hy0.
      apply filter_In in Hx. destruct Hx as [HxS' HxnO].
      apply filter_In in Hy. destruct Hy as [HyS' HynO].
      cbv beta in HxnO, HynO. apply Bool.negb_true_iff in HxnO, HynO.
      assert (HOx : Outside x)
        by (split; [ exact HxS' | intro Hso; assert (inO x = true)
              by (unfold inO; apply (same_orbit_b_complete eqdec f S Hclos Hinj d HdS x); exact Hso);
              congruence ]).
      assert (HOy : Outside y)
        by (split; [ exact HyS' | intro Hso; assert (inO y = true)
              by (unfold inO; apply (same_orbit_b_complete eqdec f S Hclos Hinj d HdS y); exact Hso);
              congruence ]).
      destruct (same_orbit_b eqdec f' S' x y) eqn:E'; destruct (same_orbit_b eqdec f S x y) eqn:E;
        try reflexivity; exfalso.
      - apply same_orbit_b_sound in E'.
        assert (Hxy : same_orbit f x y)
          by (destruct E' as [n Hn]; exists n; rewrite <- (iter_f'_eq_iter_f_outside n x HOx); exact Hn).
        assert (HxS : In x S) by (exact (proj1 (proj1 (Hcarrier x) HxS'))).
        assert (same_orbit_b eqdec f S x y = true)
          by (apply (same_orbit_b_complete eqdec f S Hclos Hinj x HxS y); exact Hxy).
        congruence.
      - apply same_orbit_b_sound in E.
        assert (Hxy : same_orbit f' x y)
          by (destruct E as [n Hn]; exists n; rewrite (iter_f'_eq_iter_f_outside n x HOx); exact Hn).
        assert (same_orbit_b eqdec f' S' x y = true)
          by (apply (same_orbit_b_complete eqdec f' S' Hclos' Hinj' x HxS' y); exact Hxy).
        congruence. }
    rewrite Hswitch.
    apply Nat.le_antisymm.
    - apply (class_reps_length_mono (same_orbit_b eqdec f S) (same_orbit_b_refl eqdec f S)
               (filter (fun x => negb (inO x)) S') (filter (fun x => negb (inO x)) S)).
      + intros x y Hx Hy. apply (same_orbit_b_sym_on eqdec f S Hclos Hinj x y (HmemS x Hx) (HmemS y Hy)).
      + intros x y z Hx Hy Hz.
        apply (same_orbit_b_trans_on eqdec f S Hclos Hinj x y z (HmemS x Hx) (HmemS y Hy) (HmemS z Hz)).
      + intros z Hz. exact (proj1 (Hiff z) Hz).
    - apply (class_reps_length_mono (same_orbit_b eqdec f S) (same_orbit_b_refl eqdec f S)
               (filter (fun x => negb (inO x)) S) (filter (fun x => negb (inO x)) S')).
      + intros x y Hx Hy. apply (same_orbit_b_sym_on eqdec f S Hclos Hinj x y (Hmem' x Hx) (Hmem' y Hy)).
      + intros x y z Hx Hy Hz.
        apply (same_orbit_b_trans_on eqdec f S Hclos Hinj x y z (Hmem' x Hx) (Hmem' y Hy) (Hmem' z Hz)).
      + intros z Hz. exact (proj2 (Hiff z) Hz).
  Qed.

  Lemma cycle_count_as_count_classes : forall (g : A -> A) (T : list A),
    cycle_count eqdec g T = count_classes (same_orbit_b eqdec g T) T.
  Proof. intros g T. unfold cycle_count, orbit_reps, count_classes. reflexivity. Qed.

  (* THE SHRINK: removing the spur pair leaves the orbit count UNCHANGED. *)
  Theorem cycle_count_shrink : cycle_count eqdec f' S' = cycle_count eqdec f S.
  Proof.
    assert (Htr_fS : forall x y z, In x S -> In y S -> In z S ->
              same_orbit_b eqdec f S x y = true -> same_orbit_b eqdec f S y z = true ->
              same_orbit_b eqdec f S x z = true)
      by (intros x y z Hx Hy Hz; apply (same_orbit_b_trans_on eqdec f S Hclos Hinj x y z Hx Hy Hz)).
    assert (Htr_f'S' : forall x y z, In x S' -> In y S' -> In z S' ->
              same_orbit_b eqdec f' S' x y = true -> same_orbit_b eqdec f' S' y z = true ->
              same_orbit_b eqdec f' S' x z = true)
      by (intros x y z Hx Hy Hz; apply (same_orbit_b_trans_on eqdec f' S' Hclos' Hinj' x y z Hx Hy Hz)).
    rewrite (cycle_count_as_count_classes f' S'), (cycle_count_as_count_classes f S).
    rewrite (count_classes_filter_split (same_orbit_b eqdec f' S')
               (same_orbit_b_refl eqdec f' S') inO S' inO_f'S'_class_constant Htr_f'S').
    rewrite (count_classes_filter_split (same_orbit_b eqdec f S)
               (same_orbit_b_refl eqdec f S) inO S inO_fS_class_constant Htr_fS).
    rewrite inO_block_f'S'_eq_1, inO_block_fS_eq_1, inO_complement_eq.
    reflexivity.
  Qed.

End CycleShrink.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Thin instances of ClassCount; allowlist axioms only.          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions cycle_count_shrink.
