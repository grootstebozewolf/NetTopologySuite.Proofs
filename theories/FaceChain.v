(* ============================================================================
   NetTopologySuite.Proofs.FaceChain
   ----------------------------------------------------------------------------
   extract_rings_valid R5 / general assembler, slice 3a: reading a face orbit
   off as a CLOSED CHAIN, and thence a valid-shape ring
   (docs/extract-rings-proof-structure.md §5 step 2; docs/face-chain.md).

   Slice 2f (theories/DartFace.v) proved `face_orbit_finite`: iterating the face
   step `fstep` from a dart returns to it.  `RingExtract` already turns a
   `BufferAssembly.closed_chain` (a list of connected `Point*Point` segments that
   loops shut) into a `ring_closed` / `ring_has_minimum_points` ring whose edges
   are exactly the chain (`face_walk_core`).  This slice supplies the MISSING
   LINK between them: the face walk, as a list of dart segments, IS a closed
   chain.

     - `dart_walk D d n`    : the n darts `d, fstep d, .., fstep^(n-1) d`;
     - `face_chain D d n`   : their segments `(dbase, dtip)`;
     - `face_chain_ok`      : consecutive segments connect (`dbase (fstep e) =
                              dtip e`, i.e. `next_base`);
     - `face_chain_closed_chain` : with the orbit's return `iter fstep n d = d`,
                              the chain loops shut -> `closed_chain`;
     - `face_closed_chain_exists` : combine with `face_orbit_finite` -- every
                              dart of a well-formed arrangement spawns a closed
                              chain;
     - `face_ring_valid_shape`    : a face of `>= 3` darts yields a ring that is
                              `ring_closed`, `ring_has_minimum_points`, and whose
                              edges are exactly the face segments.

   This delivers the combinatorial core of `valid_polygon`'s outer ring for a
   GENERAL overlay arrangement (not just the buffer beachhead): closure +
   min-points + edge fidelity, by construction of the face walk.  The hole
   nesting and the analytic `hole_inside_outer` residual remain (§4).

   Pure dart + chain + orbit combinatorics; no `Admitted` / `Axiom` /
   `Parameter`.  Axioms: the allowlisted classical-reals pair.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import List Arith Lia.
From NTS.Proofs Require Import Distance Overlay BufferAssembly RingExtract
                               Vec Direction Azimuth Dart DartAngularOrder
                               DartNext DartNextSpec DartNextInjective
                               OrbitCycle DartFace.

Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §0  Small reusable lemmas.                                                  *)
(* -------------------------------------------------------------------------- *)

(* One-step unfolding of chain_ok on a two-or-more list. *)
Lemma chain_ok_cons2 : forall (a b : Point * Point) (l : list (Point * Point)),
  chain_ok (a :: b :: l) = (snd a = fst b /\ chain_ok (b :: l)).
Proof. reflexivity. Qed.

(* Polymorphic `last` of a cons with a nonempty tail (BufferAssembly's is fixed
   to `Point*Point`; the face walk is a `Dart` list). *)
Lemma last_cons_ne_gen : forall {A} (a : A) (m : list A) d0,
  m <> [] -> last (a :: m) d0 = last m d0.
Proof. intros A a m d0 Hne. destruct m; [ contradiction | reflexivity ]. Qed.

(* `iter f n (f x) = iter f (S n) x` -- pushing a step inside the iteration. *)
Lemma iter_succ_inside :
  forall (f : Dart -> Dart) n x, iter f n (f x) = iter f (Datatypes.S n) x.
Proof.
  intros f. induction n as [| n IHn]; intros x; cbn [iter]; [ reflexivity | ].
  rewrite IHn. reflexivity.
Qed.

(* The base vertex of the next face dart is the tip of the current one. *)
Lemma fstep_base :
  forall D d, (forall x, In x D -> In (twin x) D) -> In d D ->
    dbase (fstep D d) = dtip d.
Proof.
  intros D d Htw Hd. unfold fstep. apply next_base.
  apply in_outgoing. split; [ apply Htw; exact Hd | exact (dbase_twin d) ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §1  The face walk and its segment chain.                                    *)
(* -------------------------------------------------------------------------- *)

(* The n darts visited from `d`: d, fstep d, fstep^2 d, .., fstep^(n-1) d. *)
Fixpoint dart_walk (D : list Dart) (d : Dart) (n : nat) : list Dart :=
  match n with
  | O => []
  | Datatypes.S k => d :: dart_walk D (fstep D d) k
  end.

Definition seg_of (d : Dart) : Point * Point := (dbase d, dtip d).

(* The face chain: the segment of each dart on the walk. *)
Definition face_chain (D : list Dart) (d : Dart) (n : nat) : list (Point * Point) :=
  map seg_of (dart_walk D d n).

Lemma dart_walk_length : forall D n d, length (dart_walk D d n) = n.
Proof.
  intros D. induction n as [| n IHn]; intros d; cbn [dart_walk length];
    [ reflexivity | rewrite IHn; reflexivity ].
Qed.

Lemma face_chain_length : forall D d n, length (face_chain D d n) = n.
Proof. intros D d n. unfold face_chain. rewrite length_map. apply dart_walk_length. Qed.

(* The last dart visited is `fstep^(n) d` (for a walk of `S n` darts). *)
Lemma dart_walk_last :
  forall D n d def, last (dart_walk D d (Datatypes.S n)) def = iter (fstep D) n d.
Proof.
  intros D. induction n as [| n IHn]; intros d def.
  - reflexivity.
  - change (dart_walk D d (Datatypes.S (Datatypes.S n)))
      with (d :: fstep D d :: dart_walk D (fstep D (fstep D d)) n).
    rewrite (last_cons_ne_gen d (fstep D d :: dart_walk D (fstep D (fstep D d)) n) def)
      by discriminate.
    change (fstep D d :: dart_walk D (fstep D (fstep D d)) n)
      with (dart_walk D (fstep D d) (Datatypes.S n)).
    rewrite IHn. apply iter_succ_inside.
Qed.

(* `last` commutes with `map seg_of` on a nonempty list. *)
Lemma last_map_seg :
  forall (L : list Dart) pdef ddef,
    L <> [] -> last (map seg_of L) pdef = seg_of (last L ddef).
Proof.
  induction L as [| x L IHL]; intros pdef ddef Hne; [ contradiction | ].
  destruct L as [| y L'].
  - reflexivity.
  - change (map seg_of (x :: y :: L')) with (seg_of x :: map seg_of (y :: L')).
    rewrite (last_cons_ne_gen (seg_of x) (map seg_of (y :: L')) pdef)
      by (change (map seg_of (y :: L')) with (seg_of y :: map seg_of L'); discriminate).
    rewrite (last_cons_ne_gen x (y :: L') ddef) by discriminate.
    apply IHL. discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The face chain is connected (chain_ok).                                 *)
(* -------------------------------------------------------------------------- *)

Lemma face_chain_ok :
  forall D, (forall x, In x D -> In (twin x) D) ->
    forall n d, In d D -> chain_ok (face_chain D d n).
Proof.
  intros D Htw. unfold face_chain. induction n as [| n IHn]; intros d Hd.
  - exact I.
  - cbn [dart_walk map].
    destruct n as [| n'].
    + exact I.
    + cbn [dart_walk map].
      rewrite chain_ok_cons2. split.
      * unfold seg_of; cbn [fst snd]. symmetry. apply fstep_base; [ exact Htw | exact Hd ].
      * change (seg_of (fstep D d) :: map seg_of (dart_walk D (fstep D (fstep D d)) n'))
          with (map seg_of (dart_walk D (fstep D d) (Datatypes.S n'))).
        apply IHn. apply fstep_in; [ exact Htw | exact Hd ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The face chain loops shut (closed_chain).                               *)
(* -------------------------------------------------------------------------- *)

Lemma face_chain_loop :
  forall D, (forall x, In x D -> In (twin x) D) ->
    forall n d, In d D -> (1 <= n)%nat -> iter (fstep D) n d = d ->
    forall d0, face_chain D d n <> [] ->
      snd (last (face_chain D d n) d0) = fst (hd d0 (face_chain D d n)).
Proof.
  intros D Htw n d Hd Hn Hret d0 _.
  destruct n as [| m]; [ lia | ]. unfold face_chain.
  (* head segment is seg_of d *)
  assert (Hhd : hd d0 (map seg_of (dart_walk D d (Datatypes.S m))) = seg_of d)
    by reflexivity.
  rewrite Hhd.
  (* last segment is seg_of (fstep^m d) *)
  rewrite (last_map_seg (dart_walk D d (Datatypes.S m)) d0 d) by (cbn [dart_walk]; discriminate).
  rewrite (dart_walk_last D m d d).
  unfold seg_of; cbn [fst snd].
  (* goal: dtip (iter (fstep D) m d) = dbase d *)
  assert (Hin : In (iter (fstep D) m d) D) by (apply (face_walk_in D Htw d m Hd)).
  rewrite <- (fstep_base D (iter (fstep D) m d) Htw Hin).
  change (fstep D (iter (fstep D) m d)) with (iter (fstep D) (Datatypes.S m) d).
  rewrite Hret. reflexivity.
Qed.

Theorem face_chain_closed_chain :
  forall D, arrangement_ok D ->
    forall d, In d D -> forall n, (1 <= n)%nat -> iter (fstep D) n d = d ->
    closed_chain (face_chain D d n).
Proof.
  intros D Hok d Hd n Hn Hret. split.
  - apply face_chain_ok; [ exact (proj1 Hok) | exact Hd ].
  - intros d0 Hne. apply (face_chain_loop D (proj1 Hok) n d Hd Hn Hret d0 Hne).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Capstones: face orbit -> closed chain -> valid-shape ring.              *)
(* -------------------------------------------------------------------------- *)

(* Every dart of a well-formed arrangement spawns a closed face chain. *)
Corollary face_closed_chain_exists :
  forall D, arrangement_ok D -> forall d, In d D ->
    exists n, (1 <= n)%nat /\ closed_chain (face_chain D d n).
Proof.
  intros D Hok d Hd. destruct (face_orbit_finite D Hok d Hd) as [n [Hn Hret]].
  exists n. split; [ exact Hn | apply face_chain_closed_chain; assumption ].
Qed.

(* A face of >= 3 darts yields a closed, min-vertex ring whose edges are exactly
   the face segments -- the combinatorial core of `valid_polygon`'s outer ring,
   now for a general arrangement. *)
Theorem face_ring_valid_shape :
  forall D, arrangement_ok D ->
    forall d, In d D -> forall n, (3 <= n)%nat -> iter (fstep D) n d = d ->
    ring_closed (ring_of_chain (face_chain D d n)) /\
    ring_has_minimum_points (ring_of_chain (face_chain D d n)) /\
    ring_edges (ring_of_chain (face_chain D d n)) = face_chain D d n.
Proof.
  intros D Hok d Hd n Hn Hret. apply face_walk_core.
  - apply face_chain_closed_chain; [ exact Hok | exact Hd | lia | exact Hret ].
  - rewrite face_chain_length. exact Hn.
Qed.
