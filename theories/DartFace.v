(* ============================================================================
   NetTopologySuite.Proofs.DartFace
   ----------------------------------------------------------------------------
   extract_rings_valid R5 / general assembler, slice 2f: the face step
   `next o twin` and FACE ORBIT FINITENESS (docs/extract-rings-proof-structure.md
   §5 step 2; docs/dart-face.md).

   This is where the whole `next` programme converges.  The face boundary walk
   advances a dart by `fstep D d = next (outgoing (dtip d) D) (twin d)`: cross the
   edge to the head vertex (`twin`), then turn to the rotationally adjacent
   outgoing dart (`next`).  We prove `fstep` is a CLOSED self-map of the dart set
   and INJECTIVE, then feed slice 2e's `orbit_returns` to obtain

       face_orbit_finite : iterating `fstep` from any dart returns to it,

   so every face boundary is a finite closed walk -- the §9 crux, discharged.

   Hypothesis: `arrangement_ok D` -- `D` is closed under `twin` and every vertex
   fan `outgoing v D` is `fan_ok` (proper + general position).  A noded
   arrangement's `darts_of` satisfies the twin-closure for free
   (`arrangement_ok_darts_of`).

     - `fstep_in`            : `fstep` keeps darts in `D` (orbit closure);
     - `fstep_inj`           : `fstep` is injective on `D` (distinct head vertices
                               separate the images; same vertex reduces to slice
                               2d's `next_injective` + `twin_inj`);
     - `face_orbit_finite`   : `exists n >= 1, iter (fstep D) n d = d`;
     - `face_walk_in`        : every face-walk vertex stays in `D` (finiteness).

   DELIBERATELY DEFERRED (the assembly): reading the closed `fstep`-orbit off as a
   `closed_chain` / `ring_closed` ring feeding `RingExtract.ring_of_chain`, and
   the hole-nesting tree -- the remaining combinatorial core of `valid_polygon`.

   Pure dart + order + orbit combinatorics; no `Admitted` / `Axiom` /
   `Parameter`.  Axioms: the allowlisted classical-reals pair (via `dart_eq_dec`
   and the slice 2a-2d order machinery).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import List Arith Lia.
From NTS.Proofs Require Import Vec Distance Direction Azimuth Dart
                               DartAngularOrder DartNext DartNextSpec
                               DartNextInjective OrbitCycle.

Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  The face step and the well-formed dart set.                             *)
(* -------------------------------------------------------------------------- *)

(* Advance a dart around a face: cross to the head vertex via `twin`, then take
   the rotational successor in that vertex's fan. *)
Definition fstep (D : list Dart) (d : Dart) : Dart :=
  next (outgoing (dtip d) D) (twin d).

(* `D` is closed under `twin`, and every vertex fan is well-formed. *)
Definition arrangement_ok (D : list Dart) : Prop :=
  (forall d, In d D -> In (twin d) D)
  /\ (forall v, fan_ok (outgoing v D)).

(* The twin-closure is automatic for a `darts_of` dart set. *)
Lemma arrangement_ok_darts_of :
  forall E, (forall v, fan_ok (outgoing v (darts_of E))) ->
            arrangement_ok (darts_of E).
Proof.
  intros E Hfan. split; [ apply darts_of_closed_under_twin | exact Hfan ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  `fstep` is a closed, injective self-map of the dart set.                *)
(* -------------------------------------------------------------------------- *)

(* Orbit closure: `fstep` keeps darts in `D`. *)
Lemma fstep_in :
  forall D d, (forall x, In x D -> In (twin x) D) -> In d D -> In (fstep D d) D.
Proof.
  intros D d Htw Hd. unfold fstep.
  assert (Htwd : In (twin d) (outgoing (dtip d) D)).
  { apply in_outgoing. split; [ apply Htw; exact Hd | exact (dbase_twin d) ]. }
  pose proof (next_in (outgoing (dtip d) D) (twin d) Htwd) as Hnext.
  apply in_outgoing in Hnext. exact (proj1 Hnext).
Qed.

(* Injectivity: in a cyclic permutation per vertex, the face step has no
   collisions.  Equal images share a base vertex (so the same fan), and there
   `next` is injective. *)
Lemma fstep_inj :
  forall D, arrangement_ok D ->
    forall d1 d2, In d1 D -> In d2 D -> fstep D d1 = fstep D d2 -> d1 = d2.
Proof.
  intros D [Htw Hfan] d1 d2 Hd1 Hd2 Heq.
  assert (Ht1 : In (twin d1) (outgoing (dtip d1) D)).
  { apply in_outgoing. split; [ apply Htw; exact Hd1 | exact (dbase_twin d1) ]. }
  assert (Ht2 : In (twin d2) (outgoing (dtip d2) D)).
  { apply in_outgoing. split; [ apply Htw; exact Hd2 | exact (dbase_twin d2) ]. }
  (* both images are based at the respective head vertices *)
  assert (Hb1 : dbase (fstep D d1) = dtip d1) by (unfold fstep; apply next_base; exact Ht1).
  assert (Hb2 : dbase (fstep D d2) = dtip d2) by (unfold fstep; apply next_base; exact Ht2).
  assert (Hv : dtip d1 = dtip d2).
  { rewrite <- Hb1, <- Hb2. rewrite Heq. reflexivity. }
  (* same fan; reduce to next-injectivity there *)
  rewrite <- Hv in Ht2.
  unfold fstep in Heq. rewrite <- Hv in Heq.
  assert (Htweq : twin d1 = twin d2).
  { apply (next_injective (outgoing (dtip d1) D));
      [ apply Hfan | exact Ht1 | exact Ht2 | exact Heq ]. }
  apply twin_inj. exact Htweq.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Face orbit finiteness -- the §9 crux.                                   *)
(* -------------------------------------------------------------------------- *)

(* Iterating the face step from any dart returns to it: every face boundary is a
   finite closed walk.  Direct instantiation of slice 2e's `orbit_returns` with
   `f := fstep D`, `S := D`. *)
Theorem face_orbit_finite :
  forall D, arrangement_ok D ->
    forall d, In d D -> exists n, (1 <= n)%nat /\ iter (fstep D) n d = d.
Proof.
  intros D Hok d Hd.
  apply (orbit_returns dart_eq_dec (fstep D) D).
  - intros x Hx. apply fstep_in; [ exact (proj1 Hok) | exact Hx ].
  - apply fstep_inj; exact Hok.
  - exact Hd.
Qed.

(* The orbit is contained in `D` -- the face walk never leaves the arrangement
   (finiteness of the vertex set it visits). *)
Corollary face_walk_in :
  forall D, (forall d, In d D -> In (twin d) D) ->
    forall d n, In d D -> In (iter (fstep D) n d) D.
Proof.
  intros D Htw d n Hd.
  apply (iter_in (fstep D) D); [ | exact Hd ].
  intros x Hx. apply fstep_in; [ exact Htw | exact Hx ].
Qed.
