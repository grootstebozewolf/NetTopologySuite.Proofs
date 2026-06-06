(* ============================================================================
   NetTopologySuite.Proofs.FacePolygon
   ----------------------------------------------------------------------------
   extract_rings_valid R5 / general assembler, slice 3c: a hole-free face yields
   a `valid_polygon` -- the FIRST full `valid_polygon` produced by the DCEL
   machinery (docs/extract-rings-proof-structure.md §5 step 4; docs/face-polygon.md).

   `Overlay.valid_polygon` is
       ring_closed (outer) /\ ring_simple (outer) /\ ring_has_minimum_points (outer)
       /\ (forall h, In h (hole_rings) -> ... /\ hole_inside_outer (outer) h).
   For a polygon with NO holes (`hole_rings = []`) the last conjunct is VACUOUS,
   so the analytic `hole_inside_outer` residual does not arise -- and slice 3b's
   `face_ring_combinatorial_valid` already gives the three outer-ring conditions.

   Therefore a `>= 3`-dart face of a noded, well-formed arrangement, packaged as a
   hole-free polygon, IS a `valid_polygon`, fully `Qed`:

     - `face_polygon D d n`     : `mkPolygon (ring_of_chain (face_chain D d n)) []`;
     - `face_polygon_valid`     : it satisfies `Overlay.valid_polygon`.

   This is the combinatorial core of `extract_rings_valid` discharged for the
   hole-free case, end to end from the dart set.  Faces WITH holes need the hole
   nesting tree and the analytic `hole_inside_outer` (§4) -- the genuinely
   JCT-adjacent residual that remains.

   Pure assembly; no `Admitted` / `Axiom` / `Parameter`.  Axioms: the allowlisted
   classical-reals pair.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import List Arith Lia.
From NTS.Proofs Require Import Distance Overlay BufferAssembly RingExtract
                               RingSimple Vec Direction Azimuth Dart
                               DartAngularOrder DartNext DartNextSpec
                               DartNextInjective OrbitCycle DartFace FaceChain
                               FaceRingSimple.

Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  The hole-free face polygon.                                             *)
(* -------------------------------------------------------------------------- *)

(* The polygon whose outer ring is the face ring and which has no holes. *)
Definition face_polygon (D : list Dart) (d : Dart) (n : nat) : Polygon :=
  mkPolygon (ring_of_chain (face_chain D d n)) [].

(* -------------------------------------------------------------------------- *)
(* §2  It is a valid_polygon.                                                  *)
(* -------------------------------------------------------------------------- *)

(* This is the hole-free instance of the `extract_rings_valid` headline
   (`theories-flocq/OverlayBridge.v`): `extract_rings_valid` requires every
   extracted polygon to be `valid_polygon`; for a face with no holes that is
   exactly `face_polygon_valid`.  Closing the headline in general then reduces to
   (a) emitting these face polygons from `extract`, and (b) the WITH-holes case
   -- hole nesting + the analytic `hole_inside_outer` residual (§4). *)
Theorem face_polygon_valid :
  forall D, arrangement_ok D -> pairwise_no_proper_cross D ->
    forall d, In d D -> forall n, (3 <= n)%nat -> iter (fstep D) n d = d ->
    valid_polygon (face_polygon D d n).
Proof.
  intros D Hok Hpw d Hd n Hn Hret.
  destruct (face_ring_combinatorial_valid D Hok Hpw d Hd n Hn Hret)
    as [Hcl [Hmin Hsimp]].
  unfold face_polygon, valid_polygon. cbn [outer_ring hole_rings].
  split; [ exact Hcl | ].
  split; [ exact Hsimp | ].
  split; [ exact Hmin | ].
  intros hr Hin. destruct Hin.   (* In hr [] is False *)
Qed.

(* Existence form: every dart of a noded, well-formed arrangement whose face has
   at least three darts spawns a valid (hole-free) polygon.  (The `>= 3`
   premise is the no-spur guarantee of the fully-noded arrangement; the orbit's
   return period `n` itself comes from `face_orbit_finite`.) *)
Corollary face_polygon_valid_exists :
  forall D, arrangement_ok D -> pairwise_no_proper_cross D ->
    forall d, In d D -> forall n, (3 <= n)%nat -> iter (fstep D) n d = d ->
    exists poly, valid_polygon poly.
Proof.
  intros D Hok Hpw d Hd n Hn Hret.
  exists (face_polygon D d n).
  apply (face_polygon_valid D Hok Hpw d Hd n Hn Hret).
Qed.
