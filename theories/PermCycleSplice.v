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
(* Axiom audit.  Thin instances of ClassCount; allowlist axioms only.          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions orbit_reps_NoDup.
Print Assumptions orbit_reps_indep.
Print Assumptions orbit_reps_length_mono.
