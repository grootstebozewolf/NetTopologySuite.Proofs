(* ==========================================================================
   PermCycleSplice.v

   H_bridge Euler route, Rung 3b-xvii (stage 1 of the cycle-count SPLICE):
   the generic ORBIT-TRANSVERSAL substrate.

   `cycle_count eqdec f S := length (orbit_reps eqdec f S S)` (PermCycleCount.v)
   counts `same_orbit`-CLASSES (`orbit_reps` keeps one representative per class;
   it tolerates duplicates in `S`, which matters because `darts_of E` is not
   NoDup).  To eventually prove the `+1` of the same-face face split we first need
   the transversal facts: the reps are pairwise non-orbit-equivalent
   (`orbit_reps_indep`), `NoDup` (`orbit_reps_NoDup`), a class-representative
   chooser (`orbit_rep_in`), and the injection-length comparison
   (`orbit_reps_length_mono`).

   These port the proven `ReachableDec` §9 pattern from reachability-classes to
   `same_orbit`-classes, with one extra subtlety: `same_orbit` is symmetric only
   ON `S` (`PermCycleCount.same_orbit_sym` needs `In x S`), so the relevant lists
   must be `incl ... S` -- threaded explicitly.

   Pure list/orbit combinatorics over PermCycleCount; no `Admitted` / `Axiom` /
   `Parameter`; allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import List Arith Lia.
From NTS.Proofs Require Import OrbitCycle PermCycleCount.

Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  Generic injection-bounds-length (carrier-agnostic, reusable).           *)
(* -------------------------------------------------------------------------- *)

Lemma nodup_map_inj : forall {A B : Type} (g : A -> B) (l : list A),
  NoDup l ->
  (forall x y, In x l -> In y l -> g x = g y -> x = y) ->
  NoDup (map g l).
Proof.
  intros A B g l. induction l as [| a l IH]; intros Hnd Hinj; [ constructor | ].
  cbn [map]. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hna HndA].
  constructor.
  - intro Hin. apply in_map_iff in Hin. destruct Hin as [x [Hgx Hx]]. apply Hna.
    assert (a = x)
      by (apply Hinj; [ left; reflexivity | right; exact Hx | symmetry; exact Hgx ]).
    subst x. exact Hx.
  - apply IH; [ exact HndA | ].
    intros x y Hx Hy Hgxy. apply Hinj; [ right; exact Hx | right; exact Hy | exact Hgxy ].
Qed.

Lemma nodup_inj_length : forall {A B : Type} (l1 : list A) (l2 : list B) (g : A -> B),
  NoDup l1 ->
  (forall x, In x l1 -> In (g x) l2) ->
  (forall x y, In x l1 -> In y l1 -> g x = g y -> x = y) ->
  (length l1 <= length l2)%nat.
Proof.
  intros A B l1 l2 g Hnd Hmap Hinj.
  rewrite <- (length_map g l1).
  apply NoDup_incl_length.
  - apply nodup_map_inj; assumption.
  - intros y Hy. apply in_map_iff in Hy. destruct Hy as [x [<- Hx]]. apply Hmap; exact Hx.
Qed.

Lemma existsb_false_forall : forall {A : Type} (p : A -> bool) (l : list A),
  existsb p l = false -> forall z, In z l -> p z = false.
Proof.
  intros A p l H z Hz. destruct (p z) eqn:Hpz; [ | reflexivity ].
  exfalso. assert (existsb p l = true) by (apply existsb_exists; exists z; auto).
  congruence.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Orbit-transversal facts (in the PermCycleCount section context).        *)
(* -------------------------------------------------------------------------- *)

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
    induction l as [| a l IH]; [ constructor | ].
    cbn [orbit_reps].
    destruct (existsb (fun z => same_orbit_b eqdec f S z a) (orbit_reps eqdec f S l)) eqn:He.
    - exact IH.
    - constructor; [ | exact IH ].
      intro Hin.
      assert (existsb (fun z => same_orbit_b eqdec f S z a) (orbit_reps eqdec f S l) = true)
        by (apply existsb_exists; exists a;
            split; [ exact Hin | apply (same_orbit_b_refl eqdec f S a) ]).
      congruence.
  Qed.

  (* Distinct reps are in distinct orbits (the transversal property).
     Needs `incl l S` so `same_orbit` symmetry (on S) applies to the reps. *)
  Lemma orbit_reps_indep : forall l,
    (forall x, In x l -> In x S) ->
    forall r1 r2, In r1 (orbit_reps eqdec f S l) -> In r2 (orbit_reps eqdec f S l) ->
    same_orbit f r1 r2 -> r1 = r2.
  Proof.
    induction l as [| a l' IH]; intros Hsub r1 r2 H1 H2 Hr; [ destruct H1 | ].
    assert (HaS : In a S) by (apply Hsub; left; reflexivity).
    assert (Hsub' : forall x, In x l' -> In x S) by (intros x Hx; apply Hsub; right; exact Hx).
    cbn [orbit_reps] in H1, H2.
    destruct (existsb (fun z => same_orbit_b eqdec f S z a) (orbit_reps eqdec f S l')) eqn:He.
    - apply (IH Hsub' r1 r2 H1 H2 Hr).
    - assert (Hfall : forall z, In z (orbit_reps eqdec f S l') ->
                      same_orbit_b eqdec f S z a = false)
        by (apply existsb_false_forall; exact He).
      destruct H1 as [<- | H1]; destruct H2 as [<- | H2].
      + reflexivity.
      + exfalso.
        assert (Hr2S : In r2 S) by (apply Hsub'; apply (orbit_reps_incl eqdec f S l' r2 H2)).
        assert (Hsym : same_orbit f r2 a)
          by (apply (same_orbit_sym eqdec f S Hclos Hinj a HaS r2 Hr)).
        assert (Hb : same_orbit_b eqdec f S r2 a = true)
          by (apply (same_orbit_b_complete eqdec f S Hclos Hinj r2 Hr2S a Hsym)).
        rewrite (Hfall r2 H2) in Hb. discriminate.
      + exfalso.
        assert (Hr1S : In r1 S) by (apply Hsub'; apply (orbit_reps_incl eqdec f S l' r1 H1)).
        assert (Hb : same_orbit_b eqdec f S r1 a = true)
          by (apply (same_orbit_b_complete eqdec f S Hclos Hinj r1 Hr1S a Hr)).
        rewrite (Hfall r1 H1) in Hb. discriminate.
      + apply (IH Hsub' r1 r2 H1 H2 Hr).
  Qed.

  (* A class-representative chooser inside `orbit_reps eqdec f S l`. *)
  Definition orbit_rep_in (l : list A) (r : A) : A :=
    match find (fun z => same_orbit_b eqdec f S z r) (orbit_reps eqdec f S l) with
    | Some z => z
    | None => r
    end.

  Lemma orbit_rep_in_spec : forall l r, In r l ->
    In (orbit_rep_in l r) (orbit_reps eqdec f S l) /\
    same_orbit_b eqdec f S (orbit_rep_in l r) r = true.
  Proof.
    intros l r Hr. unfold orbit_rep_in.
    destruct (orbit_reps_cover eqdec f S l r Hr) as [z [Hz Hzr]].
    destruct (find (fun w => same_orbit_b eqdec f S w r) (orbit_reps eqdec f S l)) eqn:Hf.
    - apply find_some in Hf. exact Hf.
    - exfalso.
      assert (same_orbit_b eqdec f S z r = false)
        by (exact (find_none (fun w => same_orbit_b eqdec f S w r)
                     (orbit_reps eqdec f S l) Hf z Hz)).
      congruence.
  Qed.

  (* Monotonicity of the class count in the carrier list (same `f`): more
     elements, at least as many classes.  The injection sends each rep of `l` to
     the class-rep in `l'`; injectivity is `orbit_reps_indep`. *)
  Lemma orbit_reps_length_mono : forall l l',
    (forall x, In x l -> In x S) -> (forall x, In x l' -> In x S) ->
    (forall x, In x l -> In x l') ->
    (length (orbit_reps eqdec f S l) <= length (orbit_reps eqdec f S l'))%nat.
  Proof.
    intros l l' HlS Hl'S Hincl.
    apply (nodup_inj_length (orbit_reps eqdec f S l) (orbit_reps eqdec f S l')
                            (orbit_rep_in l')).
    - apply orbit_reps_NoDup.
    - intros r Hr.
      exact (proj1 (orbit_rep_in_spec l' r (Hincl r (orbit_reps_incl eqdec f S l r Hr)))).
    - intros r1 r2 Hr1 Hr2 Hfeq.
      pose proof (orbit_rep_in_spec l' r1 (Hincl r1 (orbit_reps_incl eqdec f S l r1 Hr1)))
        as [Hin1 H1].
      pose proof (orbit_rep_in_spec l' r2 (Hincl r2 (orbit_reps_incl eqdec f S l r2 Hr2)))
        as [Hin2 H2].
      rewrite Hfeq in H1, Hin1.
      (* both reps' chosen class-rep is `orbit_rep_in l' r2`, call it w *)
      assert (HwS : In (orbit_rep_in l' r2) S)
        by (apply Hl'S; apply (orbit_reps_incl eqdec f S l' (orbit_rep_in l' r2) Hin2)).
      apply (same_orbit_b_sound eqdec f S (orbit_rep_in l' r2) r1) in H1.
      apply (same_orbit_b_sound eqdec f S (orbit_rep_in l' r2) r2) in H2.
      apply (orbit_reps_indep l HlS r1 r2 Hr1 Hr2).
      apply (same_orbit_trans f r1 (orbit_rep_in l' r2) r2).
      + apply (same_orbit_sym eqdec f S Hclos Hinj (orbit_rep_in l' r2) HwS r1 H1).
      + exact H2.
  Qed.

End OrbitTransversal.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure list/orbit combinatorics; allowlist axioms only.         *)
(* -------------------------------------------------------------------------- *)

Print Assumptions nodup_inj_length.
Print Assumptions orbit_reps_NoDup.
Print Assumptions orbit_reps_indep.
Print Assumptions orbit_reps_length_mono.
