(* ============================================================================
   NetTopologySuite.Proofs.Dart
   ----------------------------------------------------------------------------
   extract_rings_valid R5 / general assembler, slice 1: the half-edge (dart)
   foundation (docs/extract-rings-proof-structure.md §5 step 1).

   The combinatorial core of ring extraction (R1/R2, theories/RingExtract.v)
   sidestepped the half-edge layer by taking a face walk as a PRE-ORDERED
   `closed_chain` (which the buffer assembler supplies directly).  The doc's own
   note marks the still-open piece for the GENERAL overlay case:

       "ordering an *unordered* overlay edge set into chains
        (the dart / next / turn_sign assembly)".

   This file lays the dart layer that ordering will run on: each undirected edge
   becomes two opposite DARTS (directed half-edges), `twin` reverses a dart, and
   `outgoing v` selects the darts based at a vertex (the fan a cyclic `next` will
   later rotate through).  Everything here is the pure dart ALGEBRA -- the
   involutive twin, base/tip incidence, the two-orientation dart set and its
   closure under twin, and the outgoing fan.  No geometry, no ordering yet.

   DELIBERATELY DEFERRED to later slices (the hard, higher-risk parts):
     - the cyclic `next` = rotational successor in `outgoing` by `Azimuth.turn_sign`
       (angular order, general-position dependent);
     - `face_of` = the orbit of `next` o `twin`, and its FINITENESS
       (the `face_orbit_finite` crux of §9);
     - that a face orbit is a `closed_chain` (feeding RingExtract.ring_of_chain).

   Pure combinatorics over `Point`; the only axioms are the allowlisted
   classical-reals decidability pair, inherited via `point_eq_dec`.
   No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import List Lia.
From NTS.Proofs Require Import Distance Overlay OverlayGraph.

Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  Darts (directed half-edges) and twin.                                   *)
(* -------------------------------------------------------------------------- *)

(* A dart is a directed edge: it goes from its base to its tip.  Each
   undirected edge of the arrangement yields two darts (see `darts_of`). *)
Definition Dart : Type := (Point * Point)%type.

Definition dbase (d : Dart) : Point := fst d.
Definition dtip  (d : Dart) : Point := snd d.

(* Reverse a dart: swap base and tip. *)
Definition twin (d : Dart) : Dart := (snd d, fst d).

Lemma twin_involutive : forall d : Dart, twin (twin d) = d.
Proof. intros [a b]. reflexivity. Qed.

Lemma dbase_twin : forall d : Dart, dbase (twin d) = dtip d.
Proof. intros [a b]. reflexivity. Qed.

Lemma dtip_twin : forall d : Dart, dtip (twin d) = dbase d.
Proof. intros [a b]. reflexivity. Qed.

(* twin is injective (it is its own inverse). *)
Lemma twin_inj : forall d e : Dart, twin d = twin e -> d = e.
Proof.
  intros d e H.
  rewrite <- (twin_involutive d), <- (twin_involutive e), H. reflexivity.
Qed.

(* A non-degenerate dart (distinct base and tip) is not its own twin -- so the
   two orientations of a proper edge are genuinely distinct half-edges. *)
Lemma twin_neq_self : forall d : Dart, dbase d <> dtip d -> twin d <> d.
Proof.
  intros [a b] Hne Heq. cbn in Hne.
  (* twin (a,b) = (b,a) = (a,b)  forces a = b *)
  injection Heq as Hba Hab. apply Hne. cbn. symmetry. exact Hba.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The dart set of an edge list (both orientations).                       *)
(* -------------------------------------------------------------------------- *)

(* Every undirected edge contributes both of its darts. *)
Definition darts_of (E : list Edge) : list Dart := E ++ map twin E.

Lemma darts_of_length : forall E, length (darts_of E) = (2 * length E)%nat.
Proof.
  intros E. unfold darts_of. rewrite length_app, length_map.
  (* `length (map twin E)` rewrites to `@length Dart E`, which is only
     CONVERTIBLE (not syntactically equal) to the statement's `@length Edge E`;
     settle the arithmetic on the statement's atom, then close by conversion. *)
  replace (2 * length E)%nat with (length E + length E)%nat by lia.
  reflexivity.
Qed.

Lemma in_darts_of_orig : forall E e, In e E -> In e (darts_of E).
Proof. intros E e H. unfold darts_of. apply in_or_app. left. exact H. Qed.

Lemma in_darts_of_twin : forall E e, In e E -> In (twin e) (darts_of E).
Proof.
  intros E e H. unfold darts_of. apply in_or_app. right.
  apply in_map. exact H.
Qed.

(* The dart set is closed under twin: reversing any present dart stays in the
   set.  (This is the half-edge invariant the face-walk `next o twin` relies
   on -- twin never leaves the arrangement.) *)
Lemma darts_of_closed_under_twin :
  forall E d, In d (darts_of E) -> In (twin d) (darts_of E).
Proof.
  intros E d H. unfold darts_of in *.
  apply in_app_or in H. destruct H as [H | H].
  - (* d is an original edge: its twin is in the mapped part *)
    apply in_or_app. right. apply in_map. exact H.
  - (* d = twin e for some original e: twin d = e is in the original part *)
    apply in_map_iff in H. destruct H as [e [Heq Hin]].
    apply in_or_app. left.
    rewrite <- Heq, twin_involutive. exact Hin.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The outgoing fan at a vertex.                                           *)
(* -------------------------------------------------------------------------- *)

(* The darts based at a given vertex -- the rotational fan that a cyclic
   `next` (a later slice) will order by angle. *)
Definition outgoing (v : Point) (D : list Dart) : list Dart :=
  filter (fun d => if point_eq_dec (dbase d) v then true else false) D.

Lemma in_outgoing :
  forall v D d, In d (outgoing v D) <-> (In d D /\ dbase d = v).
Proof.
  intros v D d. unfold outgoing. rewrite filter_In.
  split.
  - intros [Hin Hb]. split; [ exact Hin | ].
    destruct (point_eq_dec (dbase d) v) as [He | He].
    + exact He.
    + discriminate Hb.
  - intros [Hin Hb]. split; [ exact Hin | ].
    destruct (point_eq_dec (dbase d) v) as [He | He].
    + reflexivity.
    + exfalso. apply He. exact Hb.
Qed.

(* Every outgoing dart is indeed based at the vertex. *)
Lemma outgoing_base : forall v D d, In d (outgoing v D) -> dbase d = v.
Proof. intros v D d H. exact (proj2 (proj1 (in_outgoing v D d) H)). Qed.

(* The vertex degree in the dart graph = the size of its outgoing fan. *)
Definition vdeg (v : Point) (D : list Dart) : nat := length (outgoing v D).
