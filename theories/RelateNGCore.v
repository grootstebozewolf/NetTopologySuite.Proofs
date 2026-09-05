(* ============================================================================
   NetTopologySuite.Proofs.RelateNGCore
   ----------------------------------------------------------------------------
   Issue #67 S13: RelateNG pipeline — dispatch core.

   Split (2026-08) from the former monolithic RelateNG.v; RelateNG.v remains
   as the re-export umbrella, so existing `Require Import RelateNG` clients
   (RelatePrepared.v) are unaffected.  Original section banners preserved.

   Strata over general Geometry; the rect lane (bounds extractor,
   `rect_pair_regime`, `rects_relate` selection wrapper); the triangle lane
   (ring/polygon/geometry representation, decidable boolean detectors,
   `triangle_pair_regime`, `tris_relate`); and the top-level `relate`
   dispatch with its fidelity lemmas and the line-geometry fallback.

   Layout note (meso-audit B6, executed at the split): the monolith
   interleaved the two lanes (`rect_pair_regime` sat inside the triangle
   block); here the rect lane precedes the triangle lane, and the shared
   `relate` dispatch closes the file.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List Lia Lra Ranalysis Bool Btauto.
From NTS.Proofs Require Import Real.
From NTS.Proofs Require Import DE9IM Distance Overlay Segment RelateBoundary
  RelateLineLine RelateAreaPoint RelateAreaLine RelateAreaArea
  RelateMatrixLineLine RelateMatrixAreaLine RelateMatrixRect RelateMatrixTriangle
  RelateCurveMatrix RectangleJCT Intersect Orientation.  (* cross for between collinear *)
From NTS.Proofs Require Import GeneralTriangleSeparation GeneralTriangleParity.  (* gtri / JCT planar covering for triangle interiors & exterior signs *)
From NTS.Proofs Require Import GeneralTriangleJCT GeneralTriangleExterior
  TriangleValidPolygon JCTSeamAssembly PointInRingCorrect PointInRingTangents
  JordanCurveSeam.  (* assembled in-house JCT converse: point_in_ring -> 0 < gtri *)
From NTS.Proofs Require Import TriangleContainmentConvex.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Strata (reuse/extend from RelateCurveMatrix style for general Geometry).   *)
(* -------------------------------------------------------------------------- *)

Inductive Stratum : Type := SInt | SBnd | SExt.

Definition point_in_interior (g : Geometry) (p : Point) : Prop :=
  point_set g p.

Definition point_on_boundary (g : Geometry) (p : Point) : Prop :=
  exists poly, In poly g /\
    exists r, In r (outer_ring poly :: hole_rings poly) /\
    exists e, In e (ring_edges r) /\ between (fst e) (snd e) p.

Definition point_in_exterior (g : Geometry) (p : Point) : Prop :=
  ~ point_set g p.

Definition in_stratum (s : Stratum) (g : Geometry) (p : Point) : Prop :=
  match s with
  | SInt => point_in_interior g p
  | SBnd => point_on_boundary g p
  | SExt => point_in_exterior g p
  end.

(* -------------------------------------------------------------------------- *)
(* Core relate (delegating for base cases; general stub).                     *)
(* -------------------------------------------------------------------------- *)

(* relate is defined below with rect dispatch (and stub fallback). *)

(* The point-set specification link lives in RelateCurveMatrix
   (`geom_de9im_pointset`); per-regime satisfaction lemmas below target it
   directly, so no marker predicate is kept here. *)

(* -------------------------------------------------------------------------- *)
(* Delegation / agreement examples (smoke for rect + line cases).             *)
(* -------------------------------------------------------------------------- *)

(* Delegation lemma moved after relate definition for scoping. *)

(* -------------------------------------------------------------------------- *)
(* Rect lane: bounds extractor, regime decision, selection wrapper.           *)
(* -------------------------------------------------------------------------- *)

(* Real dispatch for rect geometries. *)
Definition rect_geometry_bounds (g : Geometry) : option (R * R * R * R) :=
  match g with
  | [poly] =>
      match hole_rings poly with
      | [] =>
          match outer_ring poly with
          | mkPoint x0 y0 :: mkPoint x1 _ :: mkPoint _ y1 :: mkPoint _ _ :: _ :: nil =>
              Some (x0, y0, x1, y1)
          | _ => None
          end
      | _ => None
      end
  | _ => None
  end.

(* bool dec helpers removed... (kept comment for style) *)

Definition rect_pair_regime (ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 : R) : RectPairRegime :=
  (* Full rect family decision (horizontal expansion + all four regimes).
     Detects vertical/horizontal touch (using the symmetric guards), contains
     (either dir), partial overlap, else disjoint. Mirrors the S6 predicates.
     Transpose for reverse-contains is handled in `relate`. *)
  match Req_dec_T ax1 bx0 with
  | left _ =>
      match Rlt_dec (Rmax ay0 by0) (Rmin ay1 by1) with
      | left _ => RPR_TouchVert
      | right _ => RPR_Disjoint
      end
  | right _ =>
      match Req_dec_T ay1 by0 with
      | left _ =>
          match Rlt_dec (Rmax ax0 bx0) (Rmin ax1 bx1) with
          | left _ => RPR_TouchHoriz
          | right _ => RPR_Disjoint
          end
      | right _ =>
          (* contains A supset B *)
          match Rlt_dec ax0 bx0 with
          | left _ =>
              match Rlt_dec bx1 ax1 with
              | left _ =>
                  match Rlt_dec ay0 by0 with
                  | left _ =>
                      match Rlt_dec by1 ay1 with
                      | left _ => RPR_Contains
                      | right _ => RPR_Disjoint
                      end
                  | right _ => RPR_Disjoint
                  end
              | right _ => RPR_Disjoint
              end
          | right _ =>
              (* contains B supset A (or overlap/disjoint) *)
              match Rlt_dec bx0 ax0 with
              | left _ =>
                  match Rlt_dec ax1 bx1 with
                  | left _ =>
                      match Rlt_dec by0 ay0 with
                      | left _ =>
                          match Rlt_dec ay1 by1 with
                          | left _ => RPR_Contains
                          | right _ => RPR_Disjoint
                          end
                      | right _ => RPR_Disjoint
                      end
                  | right _ => RPR_Disjoint
                  end
              | right _ =>
                  (* overlap heuristic using the partial_overlap guard structure *)
                  match Rlt_dec ax0 bx0 with
                  | left _ =>
                      match Rlt_dec bx0 ax1 with
                      | left _ =>
                          match Rlt_dec ay0 by0 with
                          | left _ =>
                              match Rlt_dec by0 ay1 with
                              | left _ =>
                                  match Rlt_dec bx1 ax1 with
                                  | left _ => RPR_Disjoint
                                  | right _ => RPR_Overlap
                                  end
                              | right _ => RPR_Disjoint
                              end
                          | right _ => RPR_Disjoint
                          end
                      | right _ => RPR_Disjoint
                      end
                  | right _ => RPR_Disjoint
                  end
              end
          end
      end
  end.

(* rects_relate wrapper (defined before use) *)
Definition rects_relate (ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 : R)
    (r : RectPairRegime) : IntersectionMatrix :=
  (* `rect_pair_regime` maps BOTH A⊃B and B⊃A to RPR_Contains; the latter
     (strict B-within-A: bx0<ax0 ∧ ax1<bx1 ∧ by0<ay0 ∧ ay1<by1) is the
     "within" case, whose matrix is the transpose of contains. Folding that
     here keeps `relate` = `rects_relate … regime` definitionally. *)
  match r with
  | RPR_Contains =>
      match Rlt_dec bx0 ax0, Rlt_dec ax1 bx1, Rlt_dec by0 ay0, Rlt_dec ay1 by1 with
      | left _, left _, left _, left _ => matrix_transpose (rect_pair_fill r)
      | _, _, _, _ => rect_pair_fill r
      end
  | _ => rect_pair_fill r
  end.

Lemma rects_relate_touch_eq :
  forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
    rects_relate ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 RPR_TouchVert =
    aa_matrix_touch_vertical.
Proof.
  intros. unfold rects_relate. apply rect_pair_fill_touch_eq.
Qed.

(* -------------------------------------------------------------------------- *)
(* Triangle lane: representation, decidable detectors, regime classifier.     *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Triangle representation (using gtri_ring style for consistency with JCT). *)
(* -------------------------------------------------------------------------- *)

Definition triangle_ring (ax ay bx by_ cx cy : R) : Ring :=
  [ mkPoint ax ay ; mkPoint bx by_ ; mkPoint cx cy ; mkPoint ax ay ].

Definition triangle_polygon (ax ay bx by_ cx cy : R) : Polygon :=
  {| outer_ring := triangle_ring ax ay bx by_ cx cy; hole_rings := [] |}.

Definition triangle_geometry (ax ay bx by_ cx cy : R) : Geometry :=
  [ triangle_polygon ax ay bx by_ cx cy ].

(* Extract the 6 coordinates for dispatch (mirrors rect_geometry_bounds). *)
Definition triangle_geometry_points (g : Geometry) : option (R * R * R * R * R * R) :=
  match g with
  | [poly] =>
      match hole_rings poly with
      | [] =>
          match outer_ring poly with
          | mkPoint ax ay :: mkPoint bx by_ :: mkPoint cx cy :: _ :: nil =>
              Some (ax, ay, bx, by_, cx, cy)
          | _ => None
          end
      | _ => None
      end
  | _ => None
  end.

(* Basic point-in-triangle (reuse point_in_ring on the ring; gtri for strict int later). *)
Definition point_in_triangle (ax ay bx by_ cx cy : R) (p : Point) : Prop :=
  point_in_ring p (triangle_ring ax ay bx by_ cx cy).

(* -------------------------------------------------------------------------- *)
(* Triangle regime decision (parallel to rect_pair_regime).                  *)
(* Uses cross for orientation, between for edge/vertex sharing.               *)
(* For now, a simple structural decision; full geometry predicates in classify. *)
(* -------------------------------------------------------------------------- *)

(* Decidable detectors for the shared-edge touch regime (boolean mirrors of the
   `shares_edge` / `opposite_sides` Props defined below; kept standalone so the
   classifier can use them).  Point equality and the strict cross-product sign
   are decidable over R via Req_dec_T / Rlt_dec (as in rect_pair_regime). *)
Definition point_eqb (p q : Point) : bool :=
  if Req_dec_T (px p) (px q)
  then if Req_dec_T (py p) (py q) then true else false
  else false.

Definition shares_edge_b (p1 p2 q1 q2 : Point) : bool :=
  orb (andb (point_eqb p1 q1) (point_eqb p2 q2))
      (andb (point_eqb p1 q2) (point_eqb p2 q1)).

Definition opposite_sides_b (p1 p2 p q : Point) : bool :=
  if Rlt_dec (cross p1 p2 p * cross p1 p2 q) 0 then true else false.

(* True iff some edge of triangle A coincides with some edge of triangle B and
   the two apex vertices lie on opposite sides of that shared edge -- the nine
   (edge-of-A x edge-of-B) cases of `triangles_touch_on_shared_edge`. *)
Definition touch_edge_b (a1 a2 a3 b1 b2 b3 : Point) : bool :=
  (shares_edge_b a1 a2 b1 b2 && opposite_sides_b a1 a2 a3 b3) ||
  (shares_edge_b a1 a2 b2 b3 && opposite_sides_b a1 a2 a3 b1) ||
  (shares_edge_b a1 a2 b3 b1 && opposite_sides_b a1 a2 a3 b2) ||
  (shares_edge_b a2 a3 b1 b2 && opposite_sides_b a2 a3 a1 b3) ||
  (shares_edge_b a2 a3 b2 b3 && opposite_sides_b a2 a3 a1 b1) ||
  (shares_edge_b a2 a3 b3 b1 && opposite_sides_b a2 a3 a1 b2) ||
  (shares_edge_b a3 a1 b1 b2 && opposite_sides_b a3 a1 a2 b3) ||
  (shares_edge_b a3 a1 b2 b3 && opposite_sides_b a3 a1 a2 b1) ||
  (shares_edge_b a3 a1 b3 b1 && opposite_sides_b a3 a1 a2 b2).

(* Decidable detector for the containment regime: A is CCW (0 < gdbl A) and
   all three of B's vertices are strictly interior to A (0 < gtri A _).
   `triangle_pair_regime_contains` below shows this is sound: it entails
   `touch_edge_b` is false (a vertex strictly interior to A cannot equal any
   of A's own vertices, so no shared-edge endpoint match is possible), and
   `contains_b_ring_inside` shows it is geometrically meaningful: every
   point on any of B's three edges -- not merely its vertices -- lies in
   A's closed region (via TriangleContainmentConvex.gtri_region_contains_segment). *)
Definition contains_b (ax ay bx by_ cx cy dx dy ex ey fx fy : R) : bool :=
  if Rlt_dec 0 (gdbl ax ay bx by_ cx cy) then
  if Rlt_dec 0 (gtri ax ay bx by_ cx cy (mkPoint dx dy)) then
  if Rlt_dec 0 (gtri ax ay bx by_ cx cy (mkPoint ex ey)) then
  if Rlt_dec 0 (gtri ax ay bx by_ cx cy (mkPoint fx fy)) then true
  else false else false else false else false.

(* Strict gtri-sign probes used by the overlap certificate.  Pure `Rlt_dec`. *)
Definition gtri_strict_pos_b (ax ay bx by_ cx cy : R) (p : Point) : bool :=
  if Rlt_dec 0 (gtri ax ay bx by_ cx cy p) then true else false.

Definition gtri_strict_neg_b (ax ay bx by_ cx cy : R) (p : Point) : bool :=
  if Rlt_dec (gtri ax ay bx by_ cx cy p) 0 then true else false.

Definition some_vertex_strict_pos (ax ay bx by_ cx cy : R)
    (p q r : Point) : bool :=
  gtri_strict_pos_b ax ay bx by_ cx cy p
  || gtri_strict_pos_b ax ay bx by_ cx cy q
  || gtri_strict_pos_b ax ay bx by_ cx cy r.

Definition some_vertex_strict_neg (ax ay bx by_ cx cy : R)
    (p q r : Point) : bool :=
  gtri_strict_neg_b ax ay bx by_ cx cy p
  || gtri_strict_neg_b ax ay bx by_ cx cy q
  || gtri_strict_neg_b ax ay bx by_ cx cy r.

(* Sound-but-partial overlap certificate (#570 / claimId 522-b).
   Both triangles CCW, a vertex of B strictly interior to A, a vertex of B
   strictly exterior to A, and a vertex of A strictly exterior to B.
   `triangle_pair_regime_overlap` (RelateNGOverlap) derives the earlier
   branches false and lifts the flag to `triangles_partial_overlap` via a
   convexity nudge toward B's centroid.  Lens pairs whose interiors meet
   without a B-vertex in A still decline -- completeness is later #522. *)
Definition overlap_b (ax ay bx by_ cx cy dx dy ex ey fx fy : R) : bool :=
  if Rlt_dec 0 (gdbl ax ay bx by_ cx cy) then
  if Rlt_dec 0 (gdbl dx dy ex ey fx fy) then
    some_vertex_strict_pos ax ay bx by_ cx cy
      (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)
    && some_vertex_strict_neg ax ay bx by_ cx cy
      (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)
    && some_vertex_strict_neg dx dy ex ey fx fy
      (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
  else false else false.

(* Separating-edge certificate (#571 / claimId 522-c).  An oriented edge of
   one triangle is a strict supporting line: the owner's remaining vertex
   and the other triangle's three vertices have opposite `cross` signs
   (pure `Rlt_dec`).  Six candidates — three edges of A, three of B.
   Sound-but-partial: pairs whose closures miss each other without a
   vertex-strict supporting edge (partial-edge kiss) still decline.
   Vertex-touch is #572.  Completeness of leftover declines is #577. *)
Definition edge_separates_b (p1 p2 apex q1 q2 q3 : Point) : bool :=
  opposite_sides_b p1 p2 apex q1
  && opposite_sides_b p1 p2 apex q2
  && opposite_sides_b p1 p2 apex q3.

Definition some_edge_separates_b (a1 a2 a3 b1 b2 b3 : Point) : bool :=
  edge_separates_b a1 a2 a3 b1 b2 b3 ||
  edge_separates_b a2 a3 a1 b1 b2 b3 ||
  edge_separates_b a3 a1 a2 b1 b2 b3 ||
  edge_separates_b b1 b2 b3 a1 a2 a3 ||
  edge_separates_b b2 b3 b1 a1 a2 a3 ||
  edge_separates_b b3 b1 b2 a1 a2 a3.

Definition separated_b (ax ay bx by_ cx cy dx dy ex ey fx fy : R) : bool :=
  if Rlt_dec 0 (gdbl ax ay bx by_ cx cy) then
  if Rlt_dec 0 (gdbl dx dy ex ey fx fy) then
    some_edge_separates_b
      (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
      (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)
  else false else false.

(* Vertex-touch certificate (#572 / claimId 522-i).  A shared vertex `v`
   plus a separating line through `v`: the normal is the sum of one
   triangle's remaining legs (`(a2-v)+(a3-v)`), both of that triangle's
   remaining vertices are strictly on the positive side, and both of the
   other triangle's remaining vertices are strictly on the negative
   side (pure `Rlt_dec` on the same affine side function the disjoint
   certificate uses).  Exactly one A-vertex is a B-vertex, so a shared
   edge stays on `touch_edge_b`.  Sound-but-partial: obtuse-at-`v` pairs
   and slivers that also overlap are rejected.  Completeness of leftover
   declines (obtuse-at-`v`, T-junction / partial-edge kiss) is #577. *)
Definition is_vertex_b (v p q r : Point) : bool :=
  point_eqb v p || point_eqb v q || point_eqb v r.

Definition others_fst (v p q r : Point) : Point :=
  if point_eqb v p then q else if point_eqb v q then p else p.

Definition others_snd (v p q r : Point) : Point :=
  if point_eqb v p then r else if point_eqb v q then r else q.

Definition side_dot (v n q : Point) : R :=
  (px q - px v) * px n + (py q - py v) * py n.

Definition vec_sum_from (v a b : Point) : Point :=
  mkPoint (px a + px b - 2 * px v) (py a + py b - 2 * py v).

Definition both_strict_pos_b (v n p q : Point) : bool :=
  (if Rlt_dec 0 (side_dot v n p) then true else false)
  && (if Rlt_dec 0 (side_dot v n q) then true else false).

Definition both_strict_neg_b (v n p q : Point) : bool :=
  (if Rlt_dec (side_dot v n p) 0 then true else false)
  && (if Rlt_dec (side_dot v n q) 0 then true else false).

Definition cone_separates_b (v a1 a2 b1 b2 : Point) : bool :=
  let nA := vec_sum_from v a1 a2 in
  let nB := vec_sum_from v b1 b2 in
  (both_strict_pos_b v nA a1 a2 && both_strict_neg_b v nA b1 b2)
  || (both_strict_pos_b v nB b1 b2 && both_strict_neg_b v nB a1 a2).

Definition exactly_one_shared_from_a (a1 a2 a3 b1 b2 b3 : Point) : bool :=
  let s1 := is_vertex_b a1 b1 b2 b3 in
  let s2 := is_vertex_b a2 b1 b2 b3 in
  let s3 := is_vertex_b a3 b1 b2 b3 in
  (s1 && negb s2 && negb s3)
  || (negb s1 && s2 && negb s3)
  || (negb s1 && negb s2 && s3).

Definition touch_vertex_from_v (v a1 a2 a3 b1 b2 b3 : Point) : bool :=
  is_vertex_b v a1 a2 a3
  && is_vertex_b v b1 b2 b3
  && cone_separates_b v
       (others_fst v a1 a2 a3) (others_snd v a1 a2 a3)
       (others_fst v b1 b2 b3) (others_snd v b1 b2 b3).

Definition touch_vertex_b (ax ay bx by_ cx cy dx dy ex ey fx fy : R) : bool :=
  if Rlt_dec 0 (gdbl ax ay bx by_ cx cy) then
  if Rlt_dec 0 (gdbl dx dy ex ey fx fy) then
    exactly_one_shared_from_a
      (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
      (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)
    && (touch_vertex_from_v (mkPoint ax ay)
          (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
          (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)
        || touch_vertex_from_v (mkPoint bx by_)
          (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
          (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)
        || touch_vertex_from_v (mkPoint cx cy)
          (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
          (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy))
  else false else false.

(* Leftover Ⅰ: a vertex of one triangle sits in the OPEN interior of an
   edge of the other (collinear, strictly between endpoints). Mutual —
   some B-vertex on an open A-edge AND some A-vertex on an open B-edge —
   so a one-sided dim-0 T is not this leftover. Do not widen
   `shares_edge_b` (frozen TouchEdge leftover). Pure `Req_dec_T` /
   `Rlt_dec`. *)
Definition on_open_seg_b (p q r : Point) : bool :=
  if Req_dec_T (cross p q r) 0 then
    if Rlt_dec 0 ((px r - px p) * (px q - px p) + (py r - py p) * (py q - py p))
    then
    if Rlt_dec 0 ((px r - px q) * (px p - px q) + (py r - py q) * (py p - py q))
    then true else false else false
  else false.

Definition vertex_on_open_edges (a1 a2 a3 v : Point) : bool :=
  on_open_seg_b a1 a2 v || on_open_seg_b a2 a3 v || on_open_seg_b a3 a1 v.

Definition some_vertex_on_open_edges (a1 a2 a3 b1 b2 b3 : Point) : bool :=
  vertex_on_open_edges a1 a2 a3 b1
  || vertex_on_open_edges a1 a2 a3 b2
  || vertex_on_open_edges a1 a2 a3 b3.

Definition touch_partial_edge_b (a1 a2 a3 b1 b2 b3 : Point) : bool :=
  some_vertex_on_open_edges a1 a2 a3 b1 b2 b3
  && some_vertex_on_open_edges b1 b2 b3 a1 a2 a3.

(* Leftover Ⅲ / leftover Ⅳ: exactly one direction of
   vertex-in-open-edge. Not leftover Ⅰ (mutual). The xor is a
   Ⅲ∨Ⅳ configuration class (exterior-side leftover Ⅲ;
   interior-side leftover Ⅳ). Do not widen
   `touch_partial_edge_b`. Pure `Req_dec_T` / `Rlt_dec` via the
   existing open-edge helpers. *)
Definition touch_onesided_t_b (a1 a2 a3 b1 b2 b3 : Point) : bool :=
  xorb (some_vertex_on_open_edges a1 a2 a3 b1 b2 b3)
       (some_vertex_on_open_edges b1 b2 b3 a1 a2 a3).

(* Leftover Ⅱ: closed cone at a shared vertex that misses the
   *strict* cone (`cone_separates_b` / #572). Allow `side_dot = 0`
   on a remaining B-vertex. Do not remint `cone_separates_b` or
   `touch_vertex_b` — that vocab is the #572 / `522-i` certificate.
   `negb cone_separates_b` keeps the boolean false on the wired
   TouchVertex pair. Pure `Rlt_dec`. *)
Definition both_closed_pos_b (v n p q : Point) : bool :=
  (if Rlt_dec (side_dot v n p) 0 then false else true)
  && (if Rlt_dec (side_dot v n q) 0 then false else true).

Definition both_closed_neg_b (v n p q : Point) : bool :=
  (if Rlt_dec 0 (side_dot v n p) then false else true)
  && (if Rlt_dec 0 (side_dot v n q) then false else true).

Definition closed_cone_separates_b (v a1 a2 b1 b2 : Point) : bool :=
  let nA := vec_sum_from v a1 a2 in
  let nB := vec_sum_from v b1 b2 in
  (both_closed_pos_b v nA a1 a2 && both_closed_neg_b v nA b1 b2)
  || (both_closed_pos_b v nB b1 b2 && both_closed_neg_b v nB a1 a2).

Definition touch_obtuse_from_v (v a1 a2 a3 b1 b2 b3 : Point) : bool :=
  is_vertex_b v a1 a2 a3
  && is_vertex_b v b1 b2 b3
  && closed_cone_separates_b v
       (others_fst v a1 a2 a3) (others_snd v a1 a2 a3)
       (others_fst v b1 b2 b3) (others_snd v b1 b2 b3)
  && negb (cone_separates_b v
       (others_fst v a1 a2 a3) (others_snd v a1 a2 a3)
       (others_fst v b1 b2 b3) (others_snd v b1 b2 b3)).

Definition touch_obtuse_vertex_b (ax ay bx by_ cx cy dx dy ex ey fx fy : R) : bool :=
  if Rlt_dec 0 (gdbl ax ay bx by_ cx cy) then
  if Rlt_dec 0 (gdbl dx dy ex ey fx fy) then
    exactly_one_shared_from_a
      (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
      (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)
    && (touch_obtuse_from_v (mkPoint ax ay)
          (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
          (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)
        || touch_obtuse_from_v (mkPoint bx by_)
          (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
          (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)
        || touch_obtuse_from_v (mkPoint cx cy)
          (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
          (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy))
  else false else false.

(* Leftover Ⅴ: remaining vertices of one triangle sit on *opposite*
   sides of the other's cone normal at a shared vertex. Product of
   `side_dot`s is strictly negative. Not a remint of
   `cone_separates_b` / `touch_vertex_b` (#572) or
   `closed_cone_separates_b` / `touch_obtuse_vertex_b` (leftover Ⅱ).
   `negb` of both cones keeps #572 and leftover Ⅱ false
   (belt-and-suspenders: leftover Ⅱ product is 0 so `opp` is
   already false; #572 same-sign). Pure `Rlt_dec`. *)
Definition opposite_side_dot_b (v n p q : Point) : bool :=
  if Rlt_dec (side_dot v n p * side_dot v n q) 0 then true else false.

Definition mixed_cone_from_v (v a1 a2 a3 b1 b2 b3 : Point) : bool :=
  is_vertex_b v a1 a2 a3
  && is_vertex_b v b1 b2 b3
  && (opposite_side_dot_b v
        (vec_sum_from v (others_fst v a1 a2 a3) (others_snd v a1 a2 a3))
        (others_fst v b1 b2 b3) (others_snd v b1 b2 b3)
      || opposite_side_dot_b v
        (vec_sum_from v (others_fst v b1 b2 b3) (others_snd v b1 b2 b3))
        (others_fst v a1 a2 a3) (others_snd v a1 a2 a3))
  && negb (cone_separates_b v
       (others_fst v a1 a2 a3) (others_snd v a1 a2 a3)
       (others_fst v b1 b2 b3) (others_snd v b1 b2 b3))
  && negb (closed_cone_separates_b v
       (others_fst v a1 a2 a3) (others_snd v a1 a2 a3)
       (others_fst v b1 b2 b3) (others_snd v b1 b2 b3)).

Definition mixed_cone_vertex_b (ax ay bx by_ cx cy dx dy ex ey fx fy : R) : bool :=
  if Rlt_dec 0 (gdbl ax ay bx by_ cx cy) then
  if Rlt_dec 0 (gdbl dx dy ex ey fx fy) then
    exactly_one_shared_from_a
      (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
      (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)
    && (mixed_cone_from_v (mkPoint ax ay)
          (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
          (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)
        || mixed_cone_from_v (mkPoint bx by_)
          (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
          (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)
        || mixed_cone_from_v (mkPoint cx cy)
          (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
          (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy))
  else false else false.

(* Leftover Ⅵ: remaining vertices of both triangles sit on the
   *same* (strictly positive) side of the other's cone normal at a
   shared vertex. Not a remint of `cone_separates_b` / `touch_vertex_b`
   (#572; that pin is same-sign *opposite* cone — both-neg vs nA),
   leftover Ⅱ (product 0), or leftover Ⅴ (opposite signs).
   `negb` of both cones and of `mixed_cone_from_v` keeps those
   families false (belt-and-suspenders: leftover Ⅴ `opp` is
   already exclusive of `both_strict_pos`). Pure `Rlt_dec`. *)
Definition same_cone_from_v (v a1 a2 a3 b1 b2 b3 : Point) : bool :=
  is_vertex_b v a1 a2 a3
  && is_vertex_b v b1 b2 b3
  && both_strict_pos_b v
       (vec_sum_from v (others_fst v a1 a2 a3) (others_snd v a1 a2 a3))
       (others_fst v b1 b2 b3) (others_snd v b1 b2 b3)
  && both_strict_pos_b v
       (vec_sum_from v (others_fst v b1 b2 b3) (others_snd v b1 b2 b3))
       (others_fst v a1 a2 a3) (others_snd v a1 a2 a3)
  && negb (cone_separates_b v
       (others_fst v a1 a2 a3) (others_snd v a1 a2 a3)
       (others_fst v b1 b2 b3) (others_snd v b1 b2 b3))
  && negb (closed_cone_separates_b v
       (others_fst v a1 a2 a3) (others_snd v a1 a2 a3)
       (others_fst v b1 b2 b3) (others_snd v b1 b2 b3))
  && negb (mixed_cone_from_v v a1 a2 a3 b1 b2 b3).

Definition same_cone_vertex_b (ax ay bx by_ cx cy dx dy ex ey fx fy : R) : bool :=
  if Rlt_dec 0 (gdbl ax ay bx by_ cx cy) then
  if Rlt_dec 0 (gdbl dx dy ex ey fx fy) then
    exactly_one_shared_from_a
      (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
      (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)
    && (same_cone_from_v (mkPoint ax ay)
          (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
          (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)
        || same_cone_from_v (mkPoint bx by_)
          (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
          (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)
        || same_cone_from_v (mkPoint cx cy)
          (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
          (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy))
  else false else false.

(* Triangle regime classifier.  DETECTS shared-edge touch, containment,
   the vertex-stab overlap certificate, a separating-edge disjoint
   certificate, a vertex-touch certificate, leftover Ⅰ's collinear
   partial-edge kiss (`touch_partial_edge_b`, after `touch_edge_b` so a
   full shared edge still wins), leftover Ⅲ∨Ⅳ (`touch_onesided_t_b`),
   leftover Ⅱ (`touch_obtuse_vertex_b`, after `touch_vertex_b` so
   the strict cone still wins), leftover Ⅴ
   (`mixed_cone_vertex_b`, after leftover Ⅱ so a closed cone still
   wins), and leftover Ⅵ (`same_cone_vertex_b`, after leftover Ⅴ
   so opposite-sign still wins).  DECLINES on everything else.

   The default used to be TPR_Disjoint, which was unsound: failing the
   shared-edge and containment tests does not establish disjointness, so
   two genuinely overlapping triangles -- a supported input pair -- were
   classified disjoint and filled with `aa_matrix_disjoint`.  The default is
   TPR_Unsupported.  Overlap is reachable when `overlap_b` fires (#570);
   disjoint is reachable when `separated_b` fires (#571); vertex-touch is
   reachable when `touch_vertex_b` fires (#572); leftover Ⅰ is reachable
   when `touch_partial_edge_b` fires.  Leftover Ⅲ∨Ⅳ is reachable
   when `touch_onesided_t_b` fires (after leftover Ⅰ). Leftover Ⅱ
   is reachable when `touch_obtuse_vertex_b` fires. Leftover Ⅴ is
   reachable when `mixed_cone_vertex_b` fires. Leftover Ⅵ is
   reachable when `same_cone_vertex_b` fires. Completeness stays
   false on an unnamed lens pair (not leftover `Ⅶ`).
   Do not reorder the four wired certificates. Do not remint
   `cone_separates_b`. *)
Definition triangle_pair_regime (ax ay bx by_ cx cy dx dy ex ey fx fy : R) : TrianglePairRegime :=
  if touch_edge_b (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
                  (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)
  then TPR_TouchEdge
  else if contains_b ax ay bx by_ cx cy dx dy ex ey fx fy
  then TPR_Contains
  else if overlap_b ax ay bx by_ cx cy dx dy ex ey fx fy
  then TPR_Overlap
  else if separated_b ax ay bx by_ cx cy dx dy ex ey fx fy
  then TPR_Disjoint
  else if touch_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy
  then TPR_TouchVertex
  else if touch_partial_edge_b
            (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
            (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)
  then TPR_TouchPartialEdge
  else if touch_onesided_t_b
            (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
            (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)
  then TPR_TouchOnesided
  else if touch_obtuse_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy
  then TPR_TouchObtuse
  else if mixed_cone_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy
  then TPR_MixedCone
  else if same_cone_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy
  then TPR_SameCone
  else TPR_Unsupported.

(* Decidable equality on the classifier's result type -- consistent with the
   Req_dec_T / Rlt_dec approach used throughout the boolean detectors above,
   and available for any future case dispatch on `triangle_pair_regime`
   (mirroring the rectangle regime's decidability). *)
Lemma triangle_pair_regime_eq_dec :
  forall r1 r2 : TrianglePairRegime, {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Qed.

(* tris_relate wrapper (parallel to rects_relate) *)
Definition tris_relate (ax ay bx by_ cx cy ax' ay' bx' by'' cx' cy' : R)
    (r : TrianglePairRegime) : IntersectionMatrix :=
  triangle_pair_fill r.

(* -------------------------------------------------------------------------- *)
(* Top-level relate dispatch (rect pair, then triangle pair, line fallback).  *)
(* -------------------------------------------------------------------------- *)

Definition relate (A B : Geometry) : IntersectionMatrix :=
  match rect_geometry_bounds A, rect_geometry_bounds B with
  | Some (ax0, ay0, ax1, ay1), Some (bx0, by0, bx1, by1) =>
      rects_relate ax0 ay0 ax1 ay1 bx0 by0 bx1 by1
        (rect_pair_regime ax0 ay0 ax1 ay1 bx0 by0 bx1 by1)
  | _, _ =>
      match triangle_geometry_points A, triangle_geometry_points B with
      | Some (ax, ay, bx, by_, cx, cy),
        Some (dx, dy, ex, ey, fx, fy) =>
          tris_relate ax ay bx by_ cx cy dx dy ex ey fx fy
            (triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy)
      (* Outside the supported domain.  This MUST NOT be a disjointness
         matrix: `FFFFFFFFF` asserts the two geometries do not interact, and
         nothing here has established that.  `DE9IM.im_unsupported` is the
         sentinel: it fails `matrix_ok` and supports no standard predicate
         (`im_unsupported_no_predicate`), so it cannot be read as any verdict.
         The general case (the RelateNG noding pipeline) is still to come;
         until it lands the dispatch declines instead of guessing.

         KNOWN GAP: the empty/empty pair lands here too, and that one input
         does have an uncontroversial answer (`FFFFFFFF2`, disjoint).  The
         dispatch declines on it rather than special-casing; recovering it is
         a completeness item, not an honesty one. *)
      | _, _ => im_unsupported
      end
  end.

Lemma relate_on_triangles_dispatches :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    relate (triangle_geometry ax ay bx by_ cx cy)
           (triangle_geometry dx dy ex ey fx fy) =
    tris_relate ax ay bx by_ cx cy dx dy ex ey fx fy
      (triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy).
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy.
  unfold relate, triangle_geometry_points, triangle_geometry, triangle_polygon.
  simpl.
  (* Dispatch reduces directly once the triangle points are extracted. *)
  reflexivity.
Qed.

(* Basic example of triangle dispatch reducing.  These two triangles share no
   edge, neither contains the other, and A's hypotenuse (1,0)--(0,1) is a
   strict supporting line for B, so the classifier now answers TPR_Disjoint
   (#571).  The pair is the #530 sentinel that used to decline. *)
Example relate_triangle_dispatch_ex :
  relate (triangle_geometry 0 0 1 0 0 1) (triangle_geometry 2 0 3 0 2 1) =
  tris_relate 0 0 1 0 0 1 2 0 3 0 2 1 TPR_Disjoint.
Proof.
  rewrite relate_on_triangles_dispatches.
  assert (Hreg : triangle_pair_regime 0 0 1 0 0 1 2 0 3 0 2 1 = TPR_Disjoint).
  { unfold triangle_pair_regime, touch_edge_b, shares_edge_b, point_eqb.
    cbn [px py].
    repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
    unfold contains_b.
    assert (Hcb : gtri 0 0 1 0 0 1 (mkPoint 2 0) <= 0).
    { unfold gtri.
      assert (H : gsA 0 0 1 0 (mkPoint 2 0) = 0) by (unfold gsA; simpl; ring).
      rewrite H. eapply Rle_trans; [ apply Rmin_l_le | apply Rmin_l_le ]. }
    destruct (Rlt_dec 0 (gdbl 0 0 1 0 0 1)) as [_ | Hn];
      [ | exfalso; apply Hn; unfold gdbl; lra ].
    destruct (Rlt_dec 0 (gtri 0 0 1 0 0 1 (mkPoint 2 0))) as [Hlt | _];
      [ exfalso; lra | ].
    unfold overlap_b, some_vertex_strict_pos, gtri_strict_pos_b.
    destruct (Rlt_dec 0 (gdbl 0 0 1 0 0 1)) as [_ | Hn];
      [ | exfalso; apply Hn; unfold gdbl; lra ].
    destruct (Rlt_dec 0 (gdbl 2 0 3 0 2 1)) as [_ | Hn];
      [ | exfalso; apply Hn; unfold gdbl; lra ].
    destruct (Rlt_dec 0 (gtri 0 0 1 0 0 1 (mkPoint 2 0))) as [H2 | _];
      [ exfalso; lra | ].
    assert (H3 : gtri 0 0 1 0 0 1 (mkPoint 3 0) <= 0).
    { unfold gtri.
      assert (H : gsA 0 0 1 0 (mkPoint 3 0) = 0) by (unfold gsA; simpl; ring).
      rewrite H. eapply Rle_trans; [ apply Rmin_l_le | apply Rmin_l_le ]. }
    destruct (Rlt_dec 0 (gtri 0 0 1 0 0 1 (mkPoint 3 0))) as [H3lt | _];
      [ exfalso; lra | ].
    assert (H21 : gtri 0 0 1 0 0 1 (mkPoint 2 1) < 0).
    { eapply Rle_lt_trans; [ apply (gtri_le_gsB 0 0 1 0 0 1 (mkPoint 2 1)) | ].
      unfold gsB; cbn [px py]; lra. }
    destruct (Rlt_dec 0 (gtri 0 0 1 0 0 1 (mkPoint 2 1))) as [H21lt | _];
      [ exfalso; lra | ].
    (* separated_b: both CCW; A's hypotenuse (1,0)--(0,1) strictly separates. *)
    unfold separated_b, some_edge_separates_b, edge_separates_b, opposite_sides_b.
    destruct (Rlt_dec 0 (gdbl 0 0 1 0 0 1)) as [_ | Hn];
      [ | exfalso; apply Hn; unfold gdbl; lra ].
    destruct (Rlt_dec 0 (gdbl 2 0 3 0 2 1)) as [_ | Hn];
      [ | exfalso; apply Hn; unfold gdbl; lra ].
    cbn [px py].
    (* First candidate (bottom edge) is not strict: B's (2,0) is collinear. *)
    destruct (Rlt_dec (cross (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
                      * cross (mkPoint 0 0) (mkPoint 1 0) (mkPoint 2 0)) 0)
      as [Hbot | _];
      [ exfalso; unfold cross in Hbot; cbn [px py] in Hbot; lra | ].
    (* Second candidate: hypotenuse (1,0)--(0,1), apex (0,0). *)
    destruct (Rlt_dec (cross (mkPoint 1 0) (mkPoint 0 1) (mkPoint 0 0)
                      * cross (mkPoint 1 0) (mkPoint 0 1) (mkPoint 2 0)) 0)
      as [_ | Hn];
      [ | exfalso; apply Hn; unfold cross; cbn [px py]; lra ].
    destruct (Rlt_dec (cross (mkPoint 1 0) (mkPoint 0 1) (mkPoint 0 0)
                      * cross (mkPoint 1 0) (mkPoint 0 1) (mkPoint 3 0)) 0)
      as [_ | Hn];
      [ | exfalso; apply Hn; unfold cross; cbn [px py]; lra ].
    destruct (Rlt_dec (cross (mkPoint 1 0) (mkPoint 0 1) (mkPoint 0 0)
                      * cross (mkPoint 1 0) (mkPoint 0 1) (mkPoint 2 1)) 0)
      as [_ | Hn];
      [ | exfalso; apply Hn; unfold cross; cbn [px py]; lra ].
    reflexivity. }
  rewrite Hreg. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Unsupported input declines rather than guessing.                           *)
(*                                                                            *)
(* Previously this dispatch answered `ll_matrix_disjoint` for every pair it    *)
(* could not classify -- a positive claim of disjointness, indistinguishable  *)
(* to the caller from a computed one.  It now returns the sentinel, and the    *)
(* two lemmas below are the honesty properties that make the difference       *)
(* checkable rather than a comment.                                           *)
(* -------------------------------------------------------------------------- *)

Lemma relate_unsupported_pair :
  relate [] [] = im_unsupported.
Proof.
  unfold relate. reflexivity.
Qed.

(* The sentinel is not a well-formed matrix, so a caller validating its input
   catches the unsupported case. *)
Lemma relate_unsupported_not_ok :
  ~ matrix_ok (relate [] []).
Proof.
  rewrite relate_unsupported_pair. exact im_unsupported_not_ok.
Qed.

(* Stronger, and the property that matters: the declined result supports NO
   standard predicate -- not the disjointness it replaced, and not the
   intersection an everywhere-non-empty sentinel would have asserted. *)
Lemma relate_unsupported_no_predicate :
  forall r : RelatePredicate, ~ predicate_holds r (relate [] []).
Proof.
  intros r. rewrite relate_unsupported_pair. exact (im_unsupported_no_predicate r).
Qed.

Lemma relate_unsupported_not_disjoint :
  ~ im_disjoint (relate [] []).
Proof. exact (relate_unsupported_no_predicate RDisjoint). Qed.

(* The #530 sentinel pair now classifies disjoint (#571): the designated
   fill is `aa_matrix_disjoint`, which satisfies `im_disjoint`.  Bar 1 is
   the geometric verdict plus this designated witness.  The nine gtri
   cells of OGC FF2FF1212 live in RelateNGDisjointCells (#573 / 522-d);
   the classifier pointer stays on FFFFFFFFF because `pat_disjoint`
   rejects EI=2.  Rewiring the pointer is later; #575 / 522-f is the
   oracle `UNSUPPORTED` token, not this remint. *)
Lemma relate_dispatch_pair_disjoint :
  im_disjoint (relate (triangle_geometry 0 0 1 0 0 1)
                      (triangle_geometry 2 0 3 0 2 1)).
Proof.
  rewrite relate_triangle_dispatch_ex.
  unfold tris_relate. rewrite triangle_pair_fill_disjoint_eq.
  exact aa_matrix_disjoint_witness.
Qed.

Lemma relate_dispatch_pair_predicate_disjoint :
  predicate_holds RDisjoint
    (relate (triangle_geometry 0 0 1 0 0 1)
            (triangle_geometry 2 0 3 0 2 1)).
Proof.
  unfold predicate_holds. exact relate_dispatch_pair_disjoint.
Qed.


(* Prepared integration note: see RelatePrepared.prepared_evaluate_agrees.
   The public entry `relate` is the uncached path; evaluate is the cached one. *)

(* -------------------------------------------------------------------------- *)
(* Audit.                                                                     *)
(* -------------------------------------------------------------------------- *)

Print Assumptions relate_unsupported_not_disjoint.
