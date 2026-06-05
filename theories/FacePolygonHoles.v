(* ============================================================================
   NetTopologySuite.Proofs.FacePolygonHoles
   ----------------------------------------------------------------------------
   extract_rings_valid R5 / general assembler, slice 3f: assembling a
   `valid_polygon` WITH holes, modulo the single analytic seam
   (docs/extract-rings-proof-structure.md §4 / §5 step 4; docs/face-polygon-holes.md).

   Slice 3c handled the hole-free case.  This slice closes the COMBINATORIAL
   assembly for the general (with-holes) case, isolating the residual to exactly
   one analytic predicate -- the §4 goal of "shrink the residual to a single
   analytic hypothesis".

     - `polygon_valid_of_rings` : a polygon is `valid_polygon` as soon as its
       outer ring is closed/simple/min-points and each hole is closed/simple/
       min-points AND `hole_inside_outer` -- this is just `valid_polygon`'s
       structure, made into an assembly lemma;
     - `face_outer_polygon_valid` : when the OUTER ring is a face ring, its three
       combinatorial conditions are automatic (slice 3b), so the polygon is valid
       given only that each hole is a valid-shape ring INSIDE it;
     - `face_polygon_holes_valid` : when the holes are ALSO face rings, their
       three conditions are automatic too -- leaving `hole_inside_outer` as the
       SOLE remaining input.

   So the combinatorial core of `extract_rings_valid` is fully assembled: every
   `valid_polygon` condition except `hole_inside_outer` holds by construction of
   the face walks.  The lone remaining analytic seam is the point-set containment
   `hole_inside_outer` (§4, the JCT-adjacent residual, shared with R3's H1 gap),
   plus rewiring `extract` itself.

   Pure assembly; no `Admitted` / `Axiom` / `Parameter`.  Axioms: the standard
   three-axiom classical-reals base, introduces none of its own.

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
(* §1  The generic assembly bridge.                                            *)
(* -------------------------------------------------------------------------- *)

(* A polygon is valid exactly when its outer ring has the three combinatorial
   conditions and each hole has them too and lies inside the outer.  (This is
   `valid_polygon` repackaged as a constructor -- the explicit statement of what
   ring assembly must supply.) *)
Theorem polygon_valid_of_rings :
  forall (outer : Ring) (holes : list Ring),
    ring_closed outer -> ring_simple outer -> ring_has_minimum_points outer ->
    (forall h, In h holes ->
        ring_closed h /\ ring_simple h /\ ring_has_minimum_points h
        /\ hole_inside_outer outer h) ->
    valid_polygon (mkPolygon outer holes).
Proof.
  intros outer holes Hcl Hsi Hmin Hholes.
  unfold valid_polygon. cbn [outer_ring hole_rings].
  split; [ exact Hcl | ].
  split; [ exact Hsi | ].
  split; [ exact Hmin | ].
  exact Hholes.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Face outer ring: its three conditions are automatic.                    *)
(* -------------------------------------------------------------------------- *)

(* When the outer ring is a face ring (slice 3b gives closed/simple/min-points),
   the polygon is valid given only that each hole is a valid-shape ring inside
   the outer. *)
Corollary face_outer_polygon_valid :
  forall D, arrangement_ok D -> pairwise_no_proper_cross D ->
    forall d, In d D -> forall n, (3 <= n)%nat -> iter (fstep D) n d = d ->
    forall holes : list Ring,
      (forall h, In h holes ->
          ring_closed h /\ ring_simple h /\ ring_has_minimum_points h
          /\ hole_inside_outer (ring_of_chain (face_chain D d n)) h) ->
      valid_polygon (mkPolygon (ring_of_chain (face_chain D d n)) holes).
Proof.
  intros D Hok Hpw d Hd n Hn Hret holes Hholes.
  destruct (face_ring_combinatorial_valid D Hok Hpw d Hd n Hn Hret) as [Hcl [Hmin Hsi]].
  apply polygon_valid_of_rings; [ exact Hcl | exact Hsi | exact Hmin | exact Hholes ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Holes that are face rings too: only hole_inside_outer remains.          *)
(* -------------------------------------------------------------------------- *)

(* A face polygon whose holes are themselves face rings (each from some dart of
   the arrangement, with a >= 3-dart returning face).  The hole list is built
   from a list of (dart, period) specs; every combinatorial condition on the
   outer ring AND on each hole is discharged by the face machinery, so the SOLE
   remaining hypothesis is the analytic `hole_inside_outer` for each hole.

   That remaining seam is JCT-adjacent: `hole_inside_outer outer h`
   (`Overlay.v`) is the point-set claim that a vertex of `h` is `point_in_ring`
   the outer ring -- the same ray-parity / point-in-region machinery as
   `Overlay.ray_parity_odd` / `point_in_ring` and `PointInRingTangents`'s
   bounded-complement predicates, and the same gap as H1 in
   `overlay_ng_correct_conditional` / R3.  Slice 3e's orientation classifier is
   the COMBINATORIAL half of deciding which faces are holes; this analytic half
   is what is deferred (§4). *)
Definition hole_ring_of (D : list Dart) (spec : Dart * nat) : Ring :=
  ring_of_chain (face_chain D (fst spec) (snd spec)).

Theorem face_polygon_holes_valid :
  forall D, arrangement_ok D -> pairwise_no_proper_cross D ->
    forall d, In d D -> forall n, (3 <= n)%nat -> iter (fstep D) n d = d ->
    forall (hspecs : list (Dart * nat)),
      (forall s, In s hspecs ->
          In (fst s) D /\ (3 <= snd s)%nat /\ iter (fstep D) (snd s) (fst s) = fst s) ->
      (forall s, In s hspecs ->
          hole_inside_outer (ring_of_chain (face_chain D d n)) (hole_ring_of D s)) ->
      valid_polygon (mkPolygon (ring_of_chain (face_chain D d n))
                               (map (hole_ring_of D) hspecs)).
Proof.
  intros D Hok Hpw d Hd n Hn Hret hspecs Hspec Hinside.
  apply face_outer_polygon_valid; try assumption.
  intros h Hh. apply in_map_iff in Hh. destruct Hh as [s [Hs Hin]]. subst h.
  destruct (Hspec s Hin) as [HsD [Hsn Hsret]].
  destruct (face_ring_combinatorial_valid D Hok Hpw (fst s) HsD (snd s) Hsn Hsret)
    as [Hcl [Hmin Hsi]].
  split; [ exact Hcl | ]. split; [ exact Hsi | ]. split; [ exact Hmin | ].
  apply Hinside. exact Hin.
Qed.
