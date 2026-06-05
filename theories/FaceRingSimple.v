(* ============================================================================
   NetTopologySuite.Proofs.FaceRingSimple
   ----------------------------------------------------------------------------
   extract_rings_valid R5 / general assembler, slice 3b: a noded arrangement's
   face ring is `ring_simple`, completing THREE of the four `valid_polygon`
   conditions (docs/extract-rings-proof-structure.md §4; docs/face-ring-simple.md).

   Slice 3a (theories/FaceChain.v) showed a face orbit yields a ring that is
   `ring_closed`, `ring_has_minimum_points`, with edges exactly the face
   segments.  `RingSimple.ring_simple_of_subset` says: a ring whose edges all lie
   in a `pairwise_no_proper_cross` (i.e. NODED) arrangement is `ring_simple`.

   The key observation: a face segment `(dbase d, dtip d)` of a dart `d` IS the
   dart itself (`Dart = Edge = Point*Point`, so `seg_of d = d`).  So a face
   ring's edges are exactly arrangement darts -- and if the dart set `D` is
   noded, every face ring is `ring_simple`.

     - `dart_walk_subset` / `face_chain_subset` : every face segment is a dart
       of `D`;
     - `face_ring_simple`            : `pairwise_no_proper_cross D` ->
       the face ring is `ring_simple`;
     - `face_ring_combinatorial_valid` : a `>= 3`-dart face of a noded,
       well-formed arrangement yields a ring that is `ring_closed`,
       `ring_has_minimum_points`, AND `ring_simple` -- three of the four OGC
       `valid_polygon` conditions, by construction.

   Only `hole_inside_outer` (the analytic / JCT-adjacent residual, §4) then
   remains for `valid_polygon`.

   Pure dart + ring combinatorics; no `Admitted` / `Axiom` / `Parameter`.
   Axioms: the allowlisted classical-reals pair.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import List Arith Lia.
From NTS.Proofs Require Import Distance Overlay BufferAssembly RingExtract
                               RingSimple Vec Direction Azimuth Dart
                               DartAngularOrder DartNext DartNextSpec
                               DartNextInjective OrbitCycle DartFace FaceChain.

Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  Face segments are arrangement darts.                                    *)
(* -------------------------------------------------------------------------- *)

(* Every dart on the walk lies in the dart set. *)
Lemma dart_walk_subset :
  forall D, (forall x, In x D -> In (twin x) D) ->
    forall n d, In d D -> forall x, In x (dart_walk D d n) -> In x D.
Proof.
  intros D Htw. induction n as [| n IHn]; intros d Hd x Hx.
  - cbn in Hx. contradiction.
  - cbn [dart_walk] in Hx. destruct Hx as [<- | Hx].
    + exact Hd.
    + apply (IHn (fstep D d)); [ apply fstep_in; [ exact Htw | exact Hd ] | exact Hx ].
Qed.

(* A face segment `(dbase d, dtip d)` is the dart `d` itself, hence in `D`. *)
Lemma face_chain_subset :
  forall D, (forall x, In x D -> In (twin x) D) ->
    forall n d, In d D -> forall e, In e (face_chain D d n) -> In e D.
Proof.
  intros D Htw n d Hd e He. unfold face_chain in He.
  apply in_map_iff in He. destruct He as [x [Hseg Hx]].
  assert (Hxe : x = e).
  { unfold seg_of, dbase, dtip in Hseg. rewrite <- surjective_pairing in Hseg. exact Hseg. }
  rewrite <- Hxe. apply (dart_walk_subset D Htw n d Hd). exact Hx.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  A noded arrangement's face ring is simple.                              *)
(* -------------------------------------------------------------------------- *)

Theorem face_ring_simple :
  forall D, arrangement_ok D -> pairwise_no_proper_cross D ->
    forall d, In d D -> forall n, (1 <= n)%nat -> iter (fstep D) n d = d ->
    ring_simple (ring_of_chain (face_chain D d n)).
Proof.
  intros D Hok Hpw d Hd n Hn Hret.
  assert (Hcc : closed_chain (face_chain D d n))
    by (apply face_chain_closed_chain; assumption).
  apply (ring_simple_of_subset D).
  - exact Hpw.
  - intros e He.
    rewrite (ring_edges_of_closed_chain (face_chain D d n) Hcc) in He.
    apply (face_chain_subset D (proj1 Hok) n d Hd). exact He.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Three of the four valid_polygon conditions, by construction.            *)
(* -------------------------------------------------------------------------- *)

Theorem face_ring_combinatorial_valid :
  forall D, arrangement_ok D -> pairwise_no_proper_cross D ->
    forall d, In d D -> forall n, (3 <= n)%nat -> iter (fstep D) n d = d ->
    ring_closed (ring_of_chain (face_chain D d n)) /\
    ring_has_minimum_points (ring_of_chain (face_chain D d n)) /\
    ring_simple (ring_of_chain (face_chain D d n)).
Proof.
  intros D Hok Hpw d Hd n Hn Hret.
  destruct (face_ring_valid_shape D Hok d Hd n Hn Hret) as [Hcl [Hmin _]].
  repeat split.
  - exact Hcl.
  - exact Hmin.
  - apply face_ring_simple; [ exact Hok | exact Hpw | exact Hd | lia | exact Hret ].
Qed.
