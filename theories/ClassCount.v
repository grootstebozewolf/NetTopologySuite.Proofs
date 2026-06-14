(* ==========================================================================
   ClassCount.v

   Rung 3b-vii of the H_bridge Euler route.

   Generic class counting for a decidable (boolean) "same class" relation on a
   finite list: keep one representative per class, count them.  This is the
   shared tool behind the Euler accounting -- `num_faces` (the orbit relation,
   already landed via cycle_count) and the pending `num_components` (the
   reachability relation, once `reachable_dec` provides a boolean form) are both
   instances.  `cycle_count` is exactly this counter specialised to the
   same-orbit relation, so this file factors out the order-independent counting
   core from the permutation-specific PermCycleCount.v.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import List Arith Lia FunctionalExtensionality.

Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* Generic list helpers (carrier-agnostic) used by the transversal lemmas.     *)
(* -------------------------------------------------------------------------- *)

Lemma existsb_false_forall : forall {A : Type} (p : A -> bool) (l : list A),
  existsb p l = false -> forall z, In z l -> p z = false.
Proof.
  intros A p l H z Hz. destruct (p z) eqn:Hpz; [ | reflexivity ].
  exfalso. assert (existsb p l = true) by (apply existsb_exists; exists z; auto).
  congruence.
Qed.

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

Section ClassCount.
  Context {A : Type}.
  (* A boolean "same class" relation.  Reflexivity is the only property the
     counting well-definedness needs (symmetry/transitivity are not required for
     the cover/incl/positivity facts below). *)
  Variable rb : A -> A -> bool.

  (* One representative kept per class (first occurrence in the list). *)
  Fixpoint class_reps (l : list A) : list A :=
    match l with
    | [] => []
    | x :: l' =>
        let rs := class_reps l' in
        if existsb (fun z => rb z x) rs then rs else x :: rs
    end.

  Definition count_classes (l : list A) : nat := length (class_reps l).

  (* Representatives are drawn from the list. *)
  Lemma class_reps_incl : forall l r, In r (class_reps l) -> In r l.
  Proof.
    induction l as [| a l IH]; intros r Hr; [ exact Hr | ].
    cbn [class_reps] in Hr.
    destruct (existsb (fun z => rb z a) (class_reps l)).
    - right. apply IH. exact Hr.
    - destruct Hr as [Hr | Hr]; [ left; exact Hr | right; apply IH; exact Hr ].
  Qed.

  Hypothesis rb_refl : forall x, rb x x = true.

  (* Every element is covered by some representative's class. *)
  Lemma class_reps_cover : forall l x, In x l ->
    exists r, In r (class_reps l) /\ rb r x = true.
  Proof.
    induction l as [| a l IH]; intros x Hx; [ destruct Hx | ].
    cbn [class_reps].
    destruct (existsb (fun z => rb z a) (class_reps l)) eqn:He.
    - destruct Hx as [Hxa | Hxl].
      + subst x. apply existsb_exists in He. destruct He as [z [Hz Hzb]].
        exists z. split; [ exact Hz | exact Hzb ].
      + destruct (IH x Hxl) as [r [Hr Hrb]]. exists r. split; [ exact Hr | exact Hrb ].
    - destruct Hx as [Hxa | Hxl].
      + subst x. exists a. split; [ left; reflexivity | apply rb_refl ].
      + destruct (IH x Hxl) as [r [Hr Hrb]].
        exists r. split; [ right; exact Hr | exact Hrb ].
  Qed.

  (* A nonempty list has at least one class. *)
  Lemma count_classes_pos : forall l, l <> [] -> (1 <= count_classes l)%nat.
  Proof.
    intros l Hne. unfold count_classes.
    destruct l as [| a l']; [ contradiction | ].
    destruct (class_reps_cover (a :: l') a (or_introl eq_refl)) as [r [Hr _]].
    destruct (class_reps (a :: l')) as [| ? ?];
      [ destruct Hr | cbn [length]; lia ].
  Qed.

  (* An explicit upper bound: never more classes than elements. *)
  Lemma count_classes_le : forall l, (count_classes l <= length l)%nat.
  Proof.
    unfold count_classes.
    induction l as [| a l IH]; [ cbn; lia | ].
    cbn [class_reps length].
    destruct (existsb (fun z => rb z a) (class_reps l)).
    - lia.
    - cbn [length]. lia.
  Qed.

  (* --- Transversal facts (the shared core for orbit / reachability counts) --- *)

  (* The kept representatives are NoDup. *)
  Lemma class_reps_NoDup : forall l, NoDup (class_reps l).
  Proof.
    induction l as [| a l IH]; [ constructor | ].
    cbn [class_reps].
    destruct (existsb (fun z => rb z a) (class_reps l)) eqn:He.
    - exact IH.
    - constructor; [ | exact IH ].
      intro Hin.
      assert (existsb (fun z => rb z a) (class_reps l) = true)
        by (apply existsb_exists; exists a; split; [ exact Hin | apply rb_refl ]).
      congruence.
  Qed.

  (* Distinct reps are in distinct classes (the transversal property), given the
     class relation is symmetric on the list. *)
  Lemma class_reps_indep : forall l,
    (forall x y, In x l -> In y l -> rb x y = true -> rb y x = true) ->
    forall r1 r2, In r1 (class_reps l) -> In r2 (class_reps l) -> rb r1 r2 = true -> r1 = r2.
  Proof.
    induction l as [| a l' IH]; intros Hsym r1 r2 H1 H2 Hr; [ destruct H1 | ].
    assert (Hsym' : forall x y, In x l' -> In y l' -> rb x y = true -> rb y x = true)
      by (intros x y Hx Hy; apply Hsym; right; assumption).
    cbn [class_reps] in H1, H2.
    destruct (existsb (fun z => rb z a) (class_reps l')) eqn:He.
    - apply (IH Hsym' r1 r2 H1 H2 Hr).
    - assert (Hfall : forall z, In z (class_reps l') -> rb z a = false)
        by (apply existsb_false_forall; exact He).
      destruct H1 as [<- | H1]; destruct H2 as [<- | H2].
      + reflexivity.
      + exfalso.
        assert (Hr2l' : In r2 l') by (apply (class_reps_incl l' r2 H2)).
        assert (Hba : rb r2 a = true)
          by (apply (Hsym a r2); [ left; reflexivity | right; exact Hr2l' | exact Hr ]).
        rewrite (Hfall r2 H2) in Hba. discriminate.
      + exfalso. rewrite (Hfall r1 H1) in Hr. discriminate.
      + apply (IH Hsym' r1 r2 H1 H2 Hr).
  Qed.

  (* A class-representative chooser inside `class_reps l`. *)
  Definition class_rep_in (l : list A) (r : A) : A :=
    match find (fun z => rb z r) (class_reps l) with
    | Some z => z
    | None => r
    end.

  Lemma class_rep_in_spec : forall l r, In r l ->
    In (class_rep_in l r) (class_reps l) /\ rb (class_rep_in l r) r = true.
  Proof.
    intros l r Hr. unfold class_rep_in.
    destruct (class_reps_cover l r Hr) as [z [Hz Hzr]].
    destruct (find (fun w => rb w r) (class_reps l)) eqn:Hf.
    - apply find_some in Hf. exact Hf.
    - exfalso.
      assert (rb z r = false)
        by (exact (find_none (fun w => rb w r) (class_reps l) Hf z Hz)).
      congruence.
  Qed.

  (* Monotonicity of the class count in the carrier list, given the class
     relation is symmetric and transitive on the (larger) list. *)
  Lemma class_reps_length_mono : forall l l',
    (forall x y, In x l' -> In y l' -> rb x y = true -> rb y x = true) ->
    (forall x y z, In x l' -> In y l' -> In z l' ->
       rb x y = true -> rb y z = true -> rb x z = true) ->
    (forall x, In x l -> In x l') ->
    (count_classes l <= count_classes l')%nat.
  Proof.
    intros l l' Hsym Htrans Hincl. unfold count_classes.
    apply (nodup_inj_length (class_reps l) (class_reps l') (class_rep_in l')).
    - apply class_reps_NoDup.
    - intros r Hr.
      exact (proj1 (class_rep_in_spec l' r (Hincl r (class_reps_incl l r Hr)))).
    - intros r1 r2 Hr1 Hr2 Hfeq.
      pose proof (class_rep_in_spec l' r1 (Hincl r1 (class_reps_incl l r1 Hr1))) as [Hin1 H1].
      pose proof (class_rep_in_spec l' r2 (Hincl r2 (class_reps_incl l r2 Hr2))) as [Hin2 H2].
      rewrite Hfeq in H1, Hin1.
      assert (Hwl' : In (class_rep_in l' r2) l') by (apply (class_reps_incl l' _ Hin2)).
      assert (Hr1l' : In r1 l') by (apply Hincl; apply (class_reps_incl l r1 Hr1)).
      assert (Hr2l' : In r2 l') by (apply Hincl; apply (class_reps_incl l r2 Hr2)).
      apply (class_reps_indep l (fun x y Hx Hy Hxy =>
               Hsym x y (Hincl x Hx) (Hincl y Hy) Hxy) r1 r2 Hr1 Hr2).
      assert (Hr1w : rb r1 (class_rep_in l' r2) = true)
        by (apply (Hsym (class_rep_in l' r2) r1 Hwl' Hr1l' H1)).
      apply (Htrans r1 (class_rep_in l' r2) r2 Hr1l' Hwl' Hr2l' Hr1w H2).
  Qed.

End ClassCount.

(* `class_reps` depends only on the pointwise behaviour of the class relation,
   so two extensionally-equal relations yield the same representatives.  This
   lets a concrete counter (e.g. `comp_reps E := class_reps (reachable_b E)`)
   rewrite the relation under `class_reps` when needed. *)
Lemma class_reps_ext : forall {A : Type} (rb1 rb2 : A -> A -> bool) (l : list A),
  (forall x y, rb1 x y = rb2 x y) -> class_reps rb1 l = class_reps rb2 l.
Proof.
  intros A rb1 rb2 l Hb. induction l as [| a l IH]; [ reflexivity | ].
  cbn [class_reps]. rewrite IH.
  replace (fun z => rb1 z a) with (fun z => rb2 z a).
  - reflexivity.
  - apply functional_extensionality. intro z. symmetry. apply Hb.
Qed.
