(* ==========================================================================
   MapCounts.v

   Phase C / Rung 3b-vi of the H_bridge Euler route.

   The first concrete Euler quantity: `num_faces E`, the number of `fstep`-orbits
   (faces) of the arrangement `darts_of E`, obtained by instantiating the generic
   `cycle_count` (PermCycleCount.v) at the face-step permutation.  Under general
   position, `fstep` is a closed, injective self-map of `darts_of E` -- a genuine
   permutation -- so `darts_of E` really is partitioned into faces, and the count
   is a well-defined positive natural for any nonempty arrangement.

   The companion count `num_components` (number of `reachable`-classes of the
   vertex graph) now lives in `ReachableDec.v` (Rung 3b-vii): `reachable_dec`
   decides undirected reachability over a finite edge list (bounded BFS closure
   + NoDup-length saturation), `reachable_b` reflects it, and `num_components`
   counts the reachability classes of `verts E` with `num_components_pos` for the
   nonempty case -- the class-counting analogue of `num_faces` here.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import List.
From NTS.Proofs Require Import Distance Overlay Dart DartAngularOrder
                               DartNextSpec DartFace PermCycleCount.

Import ListNotations.

(* Face count: the number of fstep-orbits of the arrangement. *)
Definition num_faces (E : list Edge) : nat :=
  cycle_count dart_eq_dec (fstep (darts_of E)) (darts_of E).

(* `fstep` keeps darts inside the arrangement (twin-closure of darts_of). *)
Lemma fstep_closed_darts_of : forall (E : list Edge) d,
  In d (darts_of E) -> In (fstep (darts_of E) d) (darts_of E).
Proof.
  intros E d Hd. apply fstep_in; [ apply darts_of_closed_under_twin | exact Hd ].
Qed.

(* A nonempty arrangement has at least one face. *)
Lemma num_faces_pos : forall (E : list Edge),
  (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
  darts_of E <> [] ->
  (1 <= num_faces E)%nat.
Proof.
  intros E Hfan Hne. unfold num_faces.
  (* cycle_count_pos now needs only nonemptiness (the migrated wrapper over
     ClassCount.count_classes_pos no longer destructs S, so closure/injectivity
     are not required). *)
  apply cycle_count_pos. exact Hne.
Qed.

(* Every dart lies in the face of some representative -- the face partition is
   complete (instantiating the generic `orbit_reps_cover`). *)
Lemma num_faces_cover : forall (E : list Edge) d,
  In d (darts_of E) ->
  exists r, In r (darts_of E) /\
            same_orbit (fstep (darts_of E)) r d.
Proof.
  intros E d Hd.
  destruct (orbit_reps_cover dart_eq_dec (fstep (darts_of E)) (darts_of E)
              (darts_of E) d Hd) as [r [Hr Hrb]].
  exists r. split.
  - apply (orbit_reps_incl dart_eq_dec (fstep (darts_of E)) (darts_of E)).
    exact Hr.
  - exact (same_orbit_b_sound dart_eq_dec (fstep (darts_of E)) (darts_of E) r d Hrb).
Qed.
