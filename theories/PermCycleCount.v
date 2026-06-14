(* ==========================================================================
   PermCycleCount.v

   Phase C-1 of the H_bridge Euler route (Rung 3b-iv).

   Cycle/orbit counting for a permutation given as an injective self-map `f` of
   a finite carrier `S` (decidable equality).  This is the combinatorial
   substrate for the Euler-characteristic argument: the number of faces of the
   arrangement is the number of `fstep`-orbits, and the bridge accounting tracks
   how that count changes under edge deletion.

   Foundation established here: the same-orbit relation is an equivalence on `S`
   (symmetry from orbit periodicity), it is decidable (orbit covered within |S|
   steps), and `cycle_count` (one representative kept per orbit) is well defined.
   Reuses the finite-orbit machinery of OrbitCycle.v (`iter`, `iter_comp`,
   `iter_in`, `iter_inj_on`, `seq_map_dup`).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import List Arith Lia.
From NTS.Proofs Require Import OrbitCycle.

Import ListNotations.

Section CycleCount.
  Context {A : Type}.
  Variable eqdec : forall a b : A, {a = b} + {a <> b}.
  Variable f : A -> A.
  Variable S : list A.
  Hypothesis Hclos : forall x, In x S -> In (f x) S.
  Hypothesis Hinj : forall a b, In a S -> In b S -> f a = f b -> a = b.

  Notation it := (OrbitCycle.iter f).

  (* A period iterated any whole number of times is still the identity. *)
  Lemma iter_period_mult : forall p x,
    it p x = x -> forall k, it (k * p) x = x.
  Proof.
    intros p x Hp. induction k as [| k IH]; [ reflexivity | ].
    replace (Datatypes.S k * p)%nat with (k * p + p)%nat by lia.
    rewrite OrbitCycle.iter_comp, Hp. exact IH.
  Qed.

  (* The orbit returns within |S| steps (bounded pigeonhole + injectivity). *)
  Lemma return_le_length : forall x, In x S ->
    exists r, (1 <= r <= length S)%nat /\ it r x = x.
  Proof.
    intros x Hx.
    assert (Hnd : ~ NoDup (map (fun k => it k x) (seq 0 (Datatypes.S (length S))))).
    { intro HND.
      apply NoDup_incl_length with (l' := S) in HND.
      - rewrite length_map, length_seq in HND. lia.
      - intros y Hy. apply in_map_iff in Hy. destruct Hy as [k [Hk _]].
        subst y. apply OrbitCycle.iter_in; assumption. }
    destruct (OrbitCycle.seq_map_dup eqdec (fun k => it k x)
                (Datatypes.S (length S)) Hnd) as [i [j [Hij Heq]]].
    cbn in Heq.
    exists (j - i)%nat. split; [ lia | ].
    assert (Hb : In (it (j - i) x) S) by (apply OrbitCycle.iter_in; assumption).
    symmetry.
    apply (OrbitCycle.iter_inj_on f S Hclos Hinj i x (it (j - i) x) Hx Hb).
    rewrite <- OrbitCycle.iter_comp.
    replace (i + (j - i))%nat with j by lia. exact Heq.
  Qed.

  (* `x` and `y` are on the same orbit: some iterate of `x` lands on `y`. *)
  Definition same_orbit (x y : A) : Prop := exists n, it n x = y.

  Lemma same_orbit_refl : forall x, same_orbit x x.
  Proof. intros x. exists 0%nat. reflexivity. Qed.

  Lemma same_orbit_trans : forall x y z,
    same_orbit x y -> same_orbit y z -> same_orbit x z.
  Proof.
    intros x y z [m Hm] [n Hn]. exists (n + m)%nat.
    rewrite OrbitCycle.iter_comp, Hm. exact Hn.
  Qed.

  Lemma same_orbit_sym : forall x, In x S ->
    forall y, same_orbit x y -> same_orbit y x.
  Proof.
    intros x Hx y [n Hn].
    destruct (return_le_length x Hx) as [r [[Hr1 _] Hrx]].
    exists (n * r - n)%nat.
    rewrite <- Hn, <- OrbitCycle.iter_comp.
    replace (n * r - n + n)%nat with (n * r)%nat by nia.
    apply iter_period_mult. exact Hrx.
  Qed.

  (* Decidable boolean form: search the first |S|+1 iterates. *)
  Definition same_orbit_b (x y : A) : bool :=
    existsb (fun n => if eqdec (it n x) y then true else false)
            (seq 0 (Datatypes.S (length S))).

  Lemma same_orbit_b_sound : forall x y,
    same_orbit_b x y = true -> same_orbit x y.
  Proof.
    intros x y H. apply existsb_exists in H. destruct H as [n [_ Hn]].
    destruct (eqdec (it n x) y) as [Heq | _]; [ | discriminate ].
    exists n. exact Heq.
  Qed.

  Lemma same_orbit_b_complete : forall x, In x S ->
    forall y, same_orbit x y -> same_orbit_b x y = true.
  Proof.
    intros x Hx y [n Hn].
    destruct (return_le_length x Hx) as [r [[Hr1 Hr2] Hrx]].
    apply existsb_exists. exists (n mod r)%nat.
    assert (Hmodlt : (n mod r < r)%nat) by (apply Nat.mod_upper_bound; lia).
    split.
    - apply in_seq. lia.
    - pose proof (Nat.div_mod_eq n r) as Hdm.
      assert (Heq_n : (n = n mod r + (n / r) * r)%nat).
      { rewrite (Nat.mul_comm (n / r) r). lia. }
      assert (Hmod : it n x = it (n mod r) x).
      { rewrite Heq_n at 1. rewrite OrbitCycle.iter_comp.
        rewrite (iter_period_mult r x Hrx (n / r)). reflexivity. }
      destruct (eqdec (it (n mod r) x) y) as [_ | Hne]; [ reflexivity | ].
      exfalso. apply Hne. rewrite <- Hmod. exact Hn.
  Qed.

  Lemma same_orbit_dec : forall x, In x S ->
    forall y, {same_orbit x y} + {~ same_orbit x y}.
  Proof.
    intros x Hx y. destruct (same_orbit_b x y) eqn:Hb.
    - left. apply same_orbit_b_sound. exact Hb.
    - right. intro Hso. rewrite (same_orbit_b_complete x Hx y Hso) in Hb. discriminate.
  Qed.

  (* One representative kept per orbit (first occurrence in the list). *)
  Fixpoint orbit_reps (l : list A) : list A :=
    match l with
    | [] => []
    | x :: l' =>
        let rs := orbit_reps l' in
        if existsb (fun z => same_orbit_b z x) rs then rs else x :: rs
    end.

  (* The number of distinct orbits met by S. *)
  Definition cycle_count : nat := length (orbit_reps S).

End CycleCount.
