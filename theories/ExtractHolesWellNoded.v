(* ============================================================================
   NetTopologySuite.Proofs.ExtractHolesWellNoded
   ----------------------------------------------------------------------------
   extract_rings_valid R5, bridge follow-up: the WITH-HOLES capstone, mirror
   of NoShortFaces.extract_faces_valid_well_noded.

   `extract_faces_valid_well_noded` (NoShortFaces.v) discharged the three
   structural hypotheses of the hole-free twin-aware extractor from
   `well_noded_darts` + `no_spurs`, leaving only per-face `face_twin_free`.
   This file does the same for the WITH-HOLES extractor
   (`FaceTwinAware.extract_faces_holes_valid_twin_aware`): H1 (twin-aware
   non-crossing), H2 (`fan_ok`) and H3 (`no_short_faces`) all come from the
   well-noded + no-spur condition, and the only structural residual is the
   per-face `face_twin_free` -- the SAME single gap as the hole-free case.
   The oracle clauses (hole well-formedness + `hole_inside_outer` nesting)
   pass through unchanged, exactly as in slice 3h.

   So both extractors now reduce to the identical residual: the bridge is
   "well-noded + no-spurs => valid faces, modulo face_twin_free", uniformly.

   Pure composition; no `Admitted` / `Axiom` / `Parameter`; allowlist axioms
   only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Arith Lia.
From NTS.Proofs Require Import Distance Overlay OverlayGraph BufferAssembly
                               RingExtract RingSimple Vec Direction Azimuth
                               Dart DartAngularOrder DartNext DartNextSpec
                               DartNextInjective OrbitCycle DartFace FaceChain
                               FaceRingSimple FacePolygon FacePolygonHoles
                               ExtractFaces ExtractFacesHoles FaceTwinAware
                               NodedGeneralPosition VertexGeneralPosition
                               NoShortFaces.

Import ListNotations.
Local Open Scope R_scope.

Theorem extract_faces_holes_valid_well_noded :
  forall (hassign : Dart -> list Dart) (op : BooleanOp) (g : TopologyGraph),
    well_noded_darts (result_edges op g) ->
    no_spurs (result_darts op g) ->
    (forall d, In d (result_darts op g) ->
       face_twin_free (result_darts op g) d (face_period (result_darts op g) d)) ->
    (* oracle spec (i): well-formedness *)
    (forall d, In d (result_darts op g) ->
       forall h, In h (hassign d) -> In h (result_darts op g)) ->
    (* oracle spec (ii): nesting -- the sole analytic input *)
    (forall d, In d (result_darts op g) ->
       forall h, In h (hassign d) ->
       hole_inside_outer
         (ring_of_chain (face_chain (result_darts op g) d
                           (face_period (result_darts op g) d)))
         (hole_ring_of (result_darts op g)
            (h, face_period (result_darts op g) h))) ->
    forall poly, In poly (extract_faces_holes hassign op g) -> valid_polygon poly.
Proof.
  intros hassign op g Hwn Hns Htf Hwf Hinside.
  assert (Hfan : forall v, fan_ok (outgoing v (result_darts op g)))
    by (intro v; apply well_noded_fan_ok; exact Hwn).
  apply (extract_faces_holes_valid_twin_aware hassign op g).
  - exact Hfan.
  - apply well_noded_twin_aware. exact Hwn.
  - apply no_short_faces_of_proper_nospur.
    + apply arrangement_ok_of_fan_ok. exact Hfan.
    + destruct Hwn as (_ & Hp & _). exact Hp.
    + exact Hns.
  - exact Htf.
  - exact Hwf.
  - exact Hinside.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure composition; allowlist axioms only.                      *)
(* -------------------------------------------------------------------------- *)

Print Assumptions extract_faces_holes_valid_well_noded.
