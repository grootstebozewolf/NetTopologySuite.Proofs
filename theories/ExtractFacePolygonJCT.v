(* ============================================================================
   NetTopologySuite.Proofs.ExtractFacePolygonJCT
   ----------------------------------------------------------------------------
   extract_rings_valid R5 / general assembler, analytic seam -- Stage A
   (conditional headline): a face polygon with holes is `valid_polygon` modulo a
   NAMED JCT hypothesis, in geometric (point-set) terms
   (docs/extract-rings-proof-structure.md §4; docs/hole-inside-outer-plan.md
   Stage A).

   Slice 3f reduced the residual to `hole_inside_outer` (a ray-parity predicate).
   This slice expresses that residual in its natural GEOMETRIC form and bundles
   it with the corpus's named JCT predicate
   (`JCT.parity_characterises_interior_cont_strict`, which packages the
   parity <-> geometric-interior bridge and its technical side conditions).  The
   result is a conditional `valid_polygon` headline matching the established
   `overlay_ng_correct_conditional` / `point_in_ring_correct_jct` pattern -- the
   JCT itself appears only as a named hypothesis.

     - `hole_jct_witness outer h` : a hole vertex of `h` is geometrically inside
       `outer`, with the named JCT bridge holding there;
     - `hole_inside_outer_of_witness` : that witness discharges `hole_inside_outer`
       (the parity predicate) via the JCT bridge;
     - `face_polygon_valid_via_jct` : a face outer ring + holes, each with a
       `hole_jct_witness`, is a `valid_polygon`.

   So `extract_rings_valid` for a face polygon now holds outright EXCEPT for the
   named JCT predicate -- and Stage B (`HoleInsideOuterRect`) discharges that
   predicate unconditionally for the rectangular case.  The general
   simple-polygon JCT (Stage E) is the registered residual.

   Pure composition; no new geometry, no `Admitted` / `Axiom` / `Parameter`.
   Standard three-axiom classical-reals base.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import List Arith Lia.
From NTS.Proofs Require Import Distance Overlay BufferAssembly RingExtract
                               RingSimple PointInRingCorrect JordanCurveSeam JCT
                               Vec Direction Azimuth Dart DartAngularOrder
                               DartNext DartNextSpec DartNextInjective OrbitCycle
                               DartFace FaceChain FaceRingSimple FacePolygonHoles.

Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  The named geometric/JCT witness for a hole.                             *)
(* -------------------------------------------------------------------------- *)

(* A hole `h` has a vertex `p` that is geometrically inside `outer`, with the
   named JCT bridge (`parity_characterises_interior_cont_strict`) and its
   technical side conditions holding at `p`.  This is the "thesis-shaped"
   hypothesis -- the JCT content appears only here, as a named assumption. *)
Definition hole_jct_witness (outer h : Ring) : Prop :=
  exists p,
    In p h /\
    no_horizontal_edge_at p outer /\
    ray_avoids_vertices p outer /\
    parity_characterises_interior_cont_strict p outer /\
    geometric_interior_cont p outer.

(* The witness discharges `hole_inside_outer` (the parity predicate) through the
   JCT bridge -- given the outer ring's three combinatorial conditions. *)
Lemma hole_inside_outer_of_witness :
  forall outer h,
    ring_simple outer -> ring_closed outer -> ring_has_minimum_points outer ->
    hole_jct_witness outer h ->
    hole_inside_outer outer h.
Proof.
  intros outer h Hs Hc Hm [p [Hin [Hnh [Hrav [Hjct Hgi]]]]].
  exists p. split; [ exact Hin | ].
  (* parity_characterises_interior_cont_strict gives geometric <-> point_in_ring *)
  apply (proj1 (Hjct Hs Hc Hm Hnh Hrav)). exact Hgi.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Conditional headline: face polygon with holes is valid_polygon.         *)
(* -------------------------------------------------------------------------- *)

(* A face outer ring (its three combinatorial conditions automatic, slice 3b)
   together with holes that are valid-shape rings each carrying a
   `hole_jct_witness`, assembles into a `valid_polygon` -- modulo only the named
   JCT predicate inside the witness.  This is Stage A of the multi-beachhead plan
   (docs/hole-inside-outer-plan.md): the conditional `extract_rings_valid`
   headline for a face polygon, in the corpus's named-hypothesis form. *)
Theorem face_polygon_valid_via_jct :
  forall D, arrangement_ok D -> pairwise_no_proper_cross D ->
    forall d, In d D -> forall n, (3 <= n)%nat -> iter (fstep D) n d = d ->
    forall holes : list Ring,
      (forall h, In h holes -> ring_closed h /\ ring_simple h /\ ring_has_minimum_points h) ->
      (forall h, In h holes -> hole_jct_witness (ring_of_chain (face_chain D d n)) h) ->
      valid_polygon (mkPolygon (ring_of_chain (face_chain D d n)) holes).
Proof.
  intros D Hok Hpw d Hd n Hn Hret holes Hshape Hwit.
  destruct (face_ring_combinatorial_valid D Hok Hpw d Hd n Hn Hret)
    as [Hocl [Homin Hosi]].
  apply face_outer_polygon_valid; try assumption.
  intros h Hh.
  destruct (Hshape h Hh) as [Hcl [Hsi Hmin]].
  split; [ exact Hcl | ]. split; [ exact Hsi | ]. split; [ exact Hmin | ].
  apply (hole_inside_outer_of_witness (ring_of_chain (face_chain D d n)) h);
    [ exact Hosi | exact Hocl | exact Homin | apply Hwit; exact Hh ].
Qed.
