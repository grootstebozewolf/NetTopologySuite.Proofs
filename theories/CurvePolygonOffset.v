(* ============================================================================
   NetTopologySuite.Proofs.CurvePolygonOffset
   ----------------------------------------------------------------------------
   Buffer/noder pipeline, Stage 2-CURVE seam, rung 9: the SQL/MM
   HIERARCHY LIFT (issue #65 BUF-*, forward pointer P1 of
   `audit-rgr-comparison.md` §8) -- lift the total ring-level assembly
   of `CurveOffsetAssemblyTotal.v` through `CurvePolygon` to
   `CurveGeometry`:

     - `curve_polygon_offset`: offset the outer ring and every hole
       ring with the total assembly (offset segments + three-way join
       connectors, closing joins included).  ONE signed `d` serves all
       rings: as in JTS's OffsetCurveBuilder, the side an offset lands
       on is encoded by each ring's traversal orientation through the
       normal field (holes are stored opposite-oriented, so the same
       `d` that dilates the shell erodes the holes).  Consumers wanting
       asymmetric treatment instantiate the (parametric) `d` per call.

     - `curve_polygon_offset_valid` / `curve_geometry_offset_valid`
       (HEADLINES): validity is preserved at every level of the SQL/MM
       hierarchy -- ring (rung 8), polygon, geometry -- under the
       per-ring hypotheses bundled as `polygon_offsetable`
       (non-degenerate chords + per-arc safety bound, outer and holes)
       and `d <> 0`.  With rung 8 carrying no join exclusions, neither
       does any level above it.

     - `curve_polygon_offset_holes_length` /
       `curve_geometry_offset_length`: hole and polygon counts are
       preserved -- the structural facts a CurvePolygon emitter and the
       JTS#979 hole-count oracle family consume.

   HONEST SCOPE.  `CurveGeometry.valid_curve_polygon` deliberately
   contains NO hole-inside-outer or hole-disjointness constraints (its
   §4 comment punts them to the analytic `hole_inside_outer` layer,
   mirroring Phase 3).  This lift is therefore COMPLETE with respect to
   the corpus's validity layer; whether offsetting preserves the
   ANALYTIC hole/shell relations is part of the Minkowski point-set
   lane (forward pointer P2), not a gap in this file.

   Pure-R; THREE-AXIOM THROUGHOUT (classical-reals trio).  No
   `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Bool.
From NTS.Proofs Require Import Distance Vec CurveGeometry ArcChordApprox.
From NTS.Proofs Require Import ArcOffsetThreePoint CurveRingOffset CurveRoundJoin.
From NTS.Proofs Require Import CurveOffsetAssembly CurveSemicircle.
From NTS.Proofs Require Import CurveOffsetAssemblyTotal BufferOffset.

Import ListNotations.

Local Open Scope R_scope.

Section PolygonOffset.

  Variable d : R.

  Variable g1dec : CurveSegment -> CurveSegment -> bool.
  Hypothesis g1dec_spec : forall s1 s2,
    g1dec s1 s2 = true <-> segment_norm_end s1 = segment_norm_start s2.

  Variable uturndec : CurveSegment -> CurveSegment -> bool.
  Hypothesis uturndec_spec : forall s1 s2,
    uturndec s1 s2 = true <->
    segment_norm_start s2 = vneg (segment_norm_end s1).

  Variable tsel : CurveSegment -> CurveSegment -> Vec.
  Hypothesis tsel_spec : forall s1 s2,
    segment_arc_valid s1 -> segment_nondeg s1 ->
    vdot (tsel s1 s2) (tsel s1 s2) = 1 /\
    vdot (segment_norm_end s1) (tsel s1 s2) = 0.

  (* Shorthand for the rung-8 total ring assembly at these parameters.       *)
  Let ring_offset (r : CurveRing) : CurveRing :=
    curve_ring_offset_total d g1dec uturndec tsel r.

  Lemma ring_offset_valid : forall r,
    valid_curve_ring r ->
    Forall segment_nondeg r ->
    ring_offset_safe r d ->
    d <> 0 ->
    valid_curve_ring (ring_offset r).
  Proof.
    intros r Hv Hn Hs Hd.
    unfold ring_offset.
    apply curve_ring_offset_total_valid; assumption.
  Qed.

  (* -------------------------------------------------------------------- *)
  (* §1  Polygon level.                                                    *)
  (* -------------------------------------------------------------------- *)

  Definition curve_polygon_offset (cp : CurvePolygon) : CurvePolygon :=
    mkCurvePolygon (ring_offset (curve_outer cp))
                   (map ring_offset (curve_holes cp)).

  (* The per-ring side conditions, bundled per polygon.                    *)
  Definition polygon_offsetable (cp : CurvePolygon) : Prop :=
    Forall segment_nondeg (curve_outer cp) /\
    ring_offset_safe (curve_outer cp) d /\
    Forall (fun h => Forall segment_nondeg h) (curve_holes cp) /\
    Forall (fun h => ring_offset_safe h d) (curve_holes cp).

  Lemma rings_offset_valid_forall : forall hs,
    Forall valid_curve_ring hs ->
    Forall (fun h => Forall segment_nondeg h) hs ->
    Forall (fun h => ring_offset_safe h d) hs ->
    d <> 0 ->
    Forall valid_curve_ring (map ring_offset hs).
  Proof.
    induction hs as [| h hs' IH]; intros Hv Hn Hs Hd.
    - constructor.
    - simpl. constructor.
      + apply ring_offset_valid;
          [ exact (Forall_inv Hv) | exact (Forall_inv Hn)
          | exact (Forall_inv Hs) | exact Hd ].
      + apply IH;
          [ exact (Forall_inv_tail Hv) | exact (Forall_inv_tail Hn)
          | exact (Forall_inv_tail Hs) | exact Hd ].
  Qed.

  Theorem curve_polygon_offset_valid : forall cp,
    valid_curve_polygon cp ->
    polygon_offsetable cp ->
    d <> 0 ->
    valid_curve_polygon (curve_polygon_offset cp).
  Proof.
    intros cp [Hvo Hvh] [Hno [Hso [Hnh Hsh]]] Hd.
    split.
    - apply ring_offset_valid; assumption.
    - apply rings_offset_valid_forall; assumption.
  Qed.

  Lemma curve_polygon_offset_holes_length : forall cp,
    length (curve_holes (curve_polygon_offset cp)) =
    length (curve_holes cp).
  Proof.
    intros cp. unfold curve_polygon_offset. simpl. apply length_map.
  Qed.

  (* -------------------------------------------------------------------- *)
  (* §2  Geometry level.                                                   *)
  (* -------------------------------------------------------------------- *)

  Definition curve_geometry_offset (cg : CurveGeometry) : CurveGeometry :=
    map curve_polygon_offset cg.

  Theorem curve_geometry_offset_valid : forall cg,
    valid_curve_geometry cg ->
    Forall polygon_offsetable cg ->
    d <> 0 ->
    valid_curve_geometry (curve_geometry_offset cg).
  Proof.
    induction cg as [| cp cg' IH]; intros Hv Ho Hd.
    - constructor.
    - simpl. constructor.
      + apply curve_polygon_offset_valid;
          [ exact (Forall_inv Hv) | exact (Forall_inv Ho) | exact Hd ].
      + apply IH;
          [ exact (Forall_inv_tail Hv) | exact (Forall_inv_tail Ho)
          | exact Hd ].
  Qed.

  Lemma curve_geometry_offset_length : forall cg,
    length (curve_geometry_offset cg) = length cg.
  Proof.
    intros cg. unfold curve_geometry_offset. apply length_map.
  Qed.

End PolygonOffset.

(* ========================================================================== *)
(* Axiom audit.  ALL headlines below are 3-axiom (classical-reals trio:      *)
(* sig_not_dec, sig_forall_dec, functional_extensionality_dep).              *)
(* ========================================================================== *)

Print Assumptions curve_polygon_offset_valid.
Print Assumptions curve_geometry_offset_valid.
Print Assumptions curve_polygon_offset_holes_length.
Print Assumptions curve_geometry_offset_length.
