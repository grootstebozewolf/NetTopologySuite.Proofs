(* ============================================================================
   NetTopologySuite.Proofs.BoundedComponent
   ----------------------------------------------------------------------------
   extract_rings_valid, slice R3 (see docs/extract-rings-proof-structure.md):
   the BOUNDED-COMPONENT STRUCTURE underlying the hole-count heuristic.

   `theories/PointInRingTangents.v` defines, off the ring's edge skeleton:
       connected_in_complement r p q  -- a (not necessarily continuous) path
                                         from p to q staying in the complement
       in_bounded_component r p       -- every point reachable from p stays
                                         within some finite radius M.
   `oracle/buffer_hole_count.py` is the computable grid oracle for exactly
   this: flood-fill computes the connectivity classes, and "touches the
   border" refutes boundedness.

   This file proves the RIGOROUS FOUNDATION the heuristic rests on, all
   JCT-free (the path relation carries no continuity obligation, so the
   classes are built with explicit reparametrisations):

     - `connected_in_complement` is an equivalence relation on the
       complement (`_refl`, `_sym`, `_trans`);
     - `in_bounded_component` is a COMPONENT INVARIANT -- constant on a
       connectivity class (`in_bounded_component_invariant` / `_iff`);
     - a sufficient refutation: unbounded reachability rules out membership
       in a bounded component (`not_in_bounded_component_intro`) -- the tool
       for showing the OUTER face is unbounded.

   So "bounded component" is a well-defined notion (equivalence classes;
   boundedness a class invariant), which is what the heuristic counts.

   What is NOT here (the analytic crux, plan §9).  That a point strictly
   inside an assembled face lies in a BOUNDED class -- i.e. the ring
   separates the plane into a bounded inside and an unbounded outside -- is
   the Jordan-curve content (the same gap as `overlay_ng_correct_conditional`'s
   H1 / `point_in_ring` <-> `geometric_interior_stdlib`).  It is carried as a
   named hypothesis downstream (R6), NOT admitted here.

   Pure-R; no atan / Flocq.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.8)
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  connected_in_complement is an equivalence relation on the complement.  *)
(* -------------------------------------------------------------------------- *)

(* Reflexive on complement points (constant path). *)
Lemma connected_in_complement_refl : forall r p,
  ring_complement r p -> connected_in_complement r p p.
Proof.
  intros r p Hp. exists (fun _ => p).
  split; [ reflexivity | split; [ reflexivity | ] ].
  intros t _. exact Hp.
Qed.

(* Symmetric (reverse the parametrisation t |-> 1 - t). *)
Lemma connected_in_complement_sym : forall r p q,
  connected_in_complement r p q -> connected_in_complement r q p.
Proof.
  intros r p q [path [H0 [H1 Hc]]].
  exists (fun t => path (1 - t)).
  split; [ | split ].
  - replace (1 - 0) with 1 by lra. exact H1.
  - replace (1 - 1) with 0 by lra. exact H0.
  - intros t Ht. apply Hc. lra.
Qed.

(* Transitive (concatenate at the midpoint). *)
Lemma connected_in_complement_trans : forall r p q s,
  connected_in_complement r p q ->
  connected_in_complement r q s ->
  connected_in_complement r p s.
Proof.
  intros r p q s [p1 [H10 [H11 Hc1]]] [p2 [H20 [H21 Hc2]]].
  exists (fun t => if Rle_dec t (1/2) then p1 (2 * t) else p2 (2 * t - 1)).
  split; [ | split ].
  - destruct (Rle_dec 0 (1/2)) as [_|Hn]; [ | exfalso; lra ].
    replace (2 * 0) with 0 by lra. exact H10.
  - destruct (Rle_dec 1 (1/2)) as [Hle|_]; [ exfalso; lra | ].
    replace (2 * 1 - 1) with 1 by lra. exact H21.
  - intros t Ht. destruct (Rle_dec t (1/2)) as [Hle|Hgt].
    + apply Hc1. lra.
    + apply Hc2. lra.
Qed.

(* The endpoints of any complement path are themselves in the complement. *)
Lemma connected_in_complement_left : forall r p q,
  connected_in_complement r p q -> ring_complement r p.
Proof.
  intros r p q [path [H0 [_ Hc]]]. rewrite <- H0. apply Hc. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  in_bounded_component is a component invariant.                         *)
(* -------------------------------------------------------------------------- *)

(* If p and q are in the same component, p bounded implies q bounded
   (the same radius M works, by transitivity of reachability). *)
Lemma in_bounded_component_invariant : forall r p q,
  connected_in_complement r p q ->
  in_bounded_component r p ->
  in_bounded_component r q.
Proof.
  intros r p q Hpq [M [HM Hbound]].
  exists M. split; [ exact HM | ].
  intros s Hqs. apply Hbound.
  apply (connected_in_complement_trans r p q s Hpq Hqs).
Qed.

(* Hence boundedness is constant on a connectivity class. *)
Theorem in_bounded_component_iff : forall r p q,
  connected_in_complement r p q ->
  (in_bounded_component r p <-> in_bounded_component r q).
Proof.
  intros r p q Hpq. split.
  - apply in_bounded_component_invariant; exact Hpq.
  - apply in_bounded_component_invariant.
    apply connected_in_complement_sym; exact Hpq.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Refutation: unbounded reachability rules out a bounded component.      *)
(*     (The tool for proving the OUTER face is unbounded.)                    *)
(* -------------------------------------------------------------------------- *)

Theorem not_in_bounded_component_intro : forall r p,
  (forall M, M > 0 ->
     exists q, connected_in_complement r p q /\
               px q * px q + py q * py q > M * M) ->
  ~ in_bounded_component r p.
Proof.
  intros r p Hunb [M [HM Hbound]].
  destruct (Hunb M HM) as [q [Hpq Hbig]].
  specialize (Hbound q Hpq). lra.
Qed.
