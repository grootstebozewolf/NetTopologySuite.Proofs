(* ============================================================================
   NetTopologySuite.Proofs.CurveRingOffset
   ----------------------------------------------------------------------------
   Buffer/noder pipeline, Stage 2a-CURVE seam, rung 3: OFFSETTING A
   COMPOUND CURVE SEGMENT-WISE (issue #65 BUF-*; follows `ArcOffset.v`
   (rung 1, center/angle soundness) and `ArcOffsetThreePoint.v` (rung 2,
   SQL/MM closure `arc_offset_preserves_arc`)).

   A SQL/MM COMPOUNDCURVE ring (`CurveGeometry.CurveRing := list
   CurveSegment`, `CSChord | CSArc`) is offset segment-wise: chords via
   the linear pipeline's `BufferOffset.offset_point` (normal
   translation), arcs via rung 2's `arc_offset_arc` (radial homothety).
   This file wires that map and proves what survives it -- and, just as
   importantly, what provably does NOT:

     1. STRUCTURE SURVIVES (`curve_ring_offset_arcs_valid`).  Under the
        per-arc safety bound `ring_offset_safe` (`-r < d` for every arc
        in the ring), every arc of the offset ring is again a valid
        three-point arc.  With `curve_ring_offset_length`, the offset
        ring has the same segment count -- the structural prerequisites
        for emitting CurvePolygon boundaries in SQL/MM form.

     2. G1 JOINS WITH CONSISTENT NORMALS SURVIVE
        (`arc_join_offset_continuous`).  If two consecutive arcs share
        their join point AND their unit outward normals there agree
        (stated division-free: `r2*(P - C1) = r1*(P - C2)`
        componentwise), then the offset arcs still share the join
        point: smooth compound curves offset WITHOUT join edges.

     3. TANGENT-LINE CONTINUITY ALONE DOES NOT SURVIVE
        (`tangent_continuity_insufficient_for_offset`, honest negative).
        Concrete witness: two unit arcs meeting at (1,0) in an S-curve
        (inflection) -- centers (0,0) and (2,0), tangent LINES at the
        join identical, but normals ANTI-parallel.  Offsetting at d = 1
        sends the shared point to (2,0) along the first arc and to
        (0,0) along the second: the offset curve TEARS at an inflection
        even though the source curve is tangent-continuous.  This is
        the arc-side reason stage 2b join edges (or normal-consistency
        re-orientation) remain necessary for compound curves -- the
        curve analogue of the corner gap in the linear pipeline, and a
        quality class behind JTS#1147 / OffsetCurve artifacts.

   Adjacency/closedness preservation for an ALL-G1-consistent ring is
   deliberately deferred to the assembly rung (it is the per-join lemma
   2 lifted by list induction, pending the join-edge emission design
   for the non-G1 case that lemma 3 forces).

   Pure-R; THREE-AXIOM THROUGHOUT (classical-reals trio).  No
   `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance CurveGeometry ArcChordApprox.
From NTS.Proofs Require Import ArcOffsetThreePoint BufferOffset.

Import ListNotations.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Segment-wise offset of a compound curve.                               *)
(* -------------------------------------------------------------------------- *)

Definition curve_segment_offset (s : CurveSegment) (d : R) : CurveSegment :=
  match s with
  | CSChord p q => CSChord (offset_point p q p d) (offset_point p q q d)
  | CSArc a => CSArc (arc_offset_arc a d)
  end.

Definition curve_ring_offset (r : CurveRing) (d : R) : CurveRing :=
  map (fun s => curve_segment_offset s d) r.

Lemma curve_ring_offset_length : forall r d,
  length (curve_ring_offset r d) = length r.
Proof.
  intros r d. unfold curve_ring_offset. apply length_map.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Arc validity survives the offset (under the per-arc safety bound).    *)
(* -------------------------------------------------------------------------- *)

(* d stays strictly above every arc's inner singularity -r.                  *)
Definition ring_offset_safe (r : CurveRing) (d : R) : Prop :=
  Forall (fun s => match s with
                   | CSChord _ _ => True
                   | CSArc a => - arc_radius a < d
                   end) r.

Theorem curve_ring_offset_arcs_valid : forall r d,
  curve_ring_arcs_valid r -> ring_offset_safe r d ->
  curve_ring_arcs_valid (curve_ring_offset r d).
Proof.
  intros r d Hv Hs.
  unfold curve_ring_arcs_valid, ring_offset_safe, curve_ring_offset in *.
  induction r as [| s rest IH].
  - constructor.
  - inversion Hv as [| ? ? Hv1 Hvrest]; subst.
    inversion Hs as [| ? ? Hs1 Hsrest]; subst.
    simpl. constructor.
    + destruct s as [p q | a]; simpl.
      * exact I.
      * apply arc_offset_arc_valid; assumption.
    + apply IH; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  G1 joins with consistent normals offset continuously.                  *)
(*                                                                            *)
(* At a shared join point P, the radial offset moves P along each arc's      *)
(* outward unit normal (P - C)/r.  If the two normals AGREE, both arcs       *)
(* move P to the same place.  Stated division-free.                          *)
(* -------------------------------------------------------------------------- *)

Definition join_normals_consistent (a1 a2 : CircularArc) : Prop :=
  let P := arc_end a1 in
  (px P - px (arc_center a1)) / arc_radius a1 =
  (px P - px (arc_center a2)) / arc_radius a2 /\
  (py P - py (arc_center a1)) / arc_radius a1 =
  (py P - py (arc_center a2)) / arc_radius a2.

Theorem arc_join_offset_continuous : forall a1 a2 d,
  valid_arc a1 -> valid_arc a2 ->
  arc_end a1 = arc_start a2 ->
  join_normals_consistent a1 a2 ->
  arc_end (arc_offset_arc a1 d) = arc_start (arc_offset_arc a2 d).
Proof.
  intros a1 a2 d Hv1 Hv2 HP [Hx Hy].
  pose proof (arc_radius_pos a1 Hv1) as Hr1.
  pose proof (arc_radius_pos a2 Hv2) as Hr2.
  set (r1 := arc_radius a1) in *.
  set (r2 := arc_radius a2) in *.
  set (P := arc_end a1) in *.
  unfold arc_offset_arc. cbn [arc_start arc_end].
  fold r1 r2. rewrite <- HP. fold P.
  unfold radial_offset, homothety.
  (* Both offsets move P by d along their unit normal; the normals agree.
     (cbn restricted to the projections: a bare simpl would unfold
     arc_center into the full circumcenter formula.) *)
  apply point_eq; cbn [px py].
  - transitivity (px P + d * ((px P - px (arc_center a1)) / r1)).
    { field; lra. }
    rewrite Hx. field; lra.
  - transitivity (py P + d * ((py P - py (arc_center a1)) / r1)).
    { field; lra. }
    rewrite Hy. field; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Honest negative: tangent-line continuity is NOT enough.                *)
(*                                                                            *)
(* The S-curve (inflection) witness: two unit arcs meeting at (1,0) with     *)
(* the same tangent line but anti-parallel normals.  The offset tears.       *)
(* -------------------------------------------------------------------------- *)

Definition scurve_a1 : CircularArc :=
  mkCircularArc (mkPoint (-1) 0) (mkPoint 0 1) (mkPoint 1 0).

Definition scurve_a2 : CircularArc :=
  mkCircularArc (mkPoint 1 0) (mkPoint 2 1) (mkPoint 3 0).

Lemma scurve_a1_valid : valid_arc scurve_a1.
Proof. unfold valid_arc, scurve_a1. simpl. lra. Qed.

Lemma scurve_a2_valid : valid_arc scurve_a2.
Proof. unfold valid_arc, scurve_a2. simpl. lra. Qed.

Lemma scurve_a1_center : arc_center scurve_a1 = mkPoint 0 0.
Proof.
  unfold arc_center, scurve_a1. simpl.
  apply point_eq; simpl; field_simplify_eq; lra.
Qed.

Lemma scurve_a2_center : arc_center scurve_a2 = mkPoint 2 0.
Proof.
  unfold arc_center, scurve_a2. simpl.
  apply point_eq; simpl; field_simplify_eq; lra.
Qed.

Lemma scurve_a1_radius : arc_radius scurve_a1 = 1.
Proof.
  unfold arc_radius. rewrite scurve_a1_center.
  unfold dist, dist_sq, scurve_a1. simpl.
  replace ((0 - -1) * (0 - -1) + (0 - 0) * (0 - 0)) with 1 by ring.
  exact sqrt_1.
Qed.

Lemma scurve_a2_radius : arc_radius scurve_a2 = 1.
Proof.
  unfold arc_radius. rewrite scurve_a2_center.
  unfold dist, dist_sq, scurve_a2. simpl.
  replace ((2 - 1) * (2 - 1) + (0 - 0) * (0 - 0)) with 1 by ring.
  exact sqrt_1.
Qed.

Theorem tangent_continuity_insufficient_for_offset :
  exists (a1 a2 : CircularArc) (d : R),
    valid_arc a1 /\ valid_arc a2 /\
    arc_end a1 = arc_start a2 /\
    (* the tangent LINES at the join agree: the unit normals are ANTI-parallel *)
    (let P := arc_end a1 in
     (px P - px (arc_center a1)) / arc_radius a1 =
       - ((px P - px (arc_center a2)) / arc_radius a2) /\
     (py P - py (arc_center a1)) / arc_radius a1 =
       - ((py P - py (arc_center a2)) / arc_radius a2)) /\
    arc_end (arc_offset_arc a1 d) <> arc_start (arc_offset_arc a2 d).
Proof.
  exists scurve_a1, scurve_a2, 1.
  split; [ exact scurve_a1_valid | ].
  split; [ exact scurve_a2_valid | ].
  split; [ reflexivity | ].
  split.
  - (* anti-parallel normals at P = (1,0) *)
    rewrite scurve_a1_center, scurve_a2_center,
            scurve_a1_radius, scurve_a2_radius.
    unfold scurve_a1. simpl. split; lra.
  - (* the offsets tear: (2,0) <> (0,0) *)
    intros Heq.
    assert (Hpx : px (arc_end (arc_offset_arc scurve_a1 1)) =
                  px (arc_start (arc_offset_arc scurve_a2 1)))
      by (rewrite Heq; reflexivity).
    revert Hpx.
    unfold arc_offset_arc. cbn [arc_start arc_end].
    rewrite scurve_a1_center, scurve_a2_center,
            scurve_a1_radius, scurve_a2_radius.
    unfold radial_offset, homothety, scurve_a1, scurve_a2. simpl.
    lra.
Qed.

(* ========================================================================== *)
(* Axiom audit.  ALL headlines below are 3-axiom (classical-reals trio:      *)
(* sig_not_dec, sig_forall_dec, functional_extensionality_dep).              *)
(* ========================================================================== *)

Print Assumptions curve_ring_offset_arcs_valid.
Print Assumptions arc_join_offset_continuous.
Print Assumptions tangent_continuity_insufficient_for_offset.
