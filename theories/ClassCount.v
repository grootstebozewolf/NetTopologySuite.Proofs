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

From Stdlib Require Import List Arith Lia.

Import ListNotations.

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

End ClassCount.
