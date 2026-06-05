(* ============================================================================
   NetTopologySuite.Proofs.CurveGeometry
   ----------------------------------------------------------------------------
   Phase 4 Session 2: foundational types for chord-approximation curve
   geometry.  SQL/MM Spatial (ISO/IEC 13249-3) `CIRCULARSTRING` and
   `COMPOUNDCURVE` representations, plus the Option B bridge
   `to_geometry` to Phase 3's `Geometry` carrier.

   This file defines types and validity predicates only.  No proofs of
   approximation correctness (S6 lands those); no orientation /
   intersection predicates (S3-S5 land those).  Same role as Phase 3
   Milestone 1's `Overlay.v`: get the types right before predicate work.

   See `docs/audit-phase4-chord-overfitting.md` for the full Phase 4
   classification and `docs/audit-phase4-curves.md` for the strategic
   framing (Option B confirmed 2026-05-29).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import List.

From NTS.Proofs Require Import Distance.
From NTS.Proofs Require Import Overlay.

Import ListNotations.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  CircularArc.                                                           *)
(*                                                                            *)
(* SQL/MM Spatial three-point convention: an arc is defined by its start,    *)
(* an interior point on the arc, and its end.  The three points (assumed     *)
(* non-collinear via `valid_arc`) uniquely determine the circumscribed       *)
(* circle and the minor arc through them.                                     *)
(* -------------------------------------------------------------------------- *)

Record CircularArc : Type := mkCircularArc {
  arc_start : Point;
  arc_mid   : Point;
  arc_end   : Point;
}.

(* Non-collinearity of the three control points.  Equivalent to: the signed
   triangle area (twice it = cross product of the start->mid and start->end
   vectors) is non-zero.  When this fails, no unique circle exists. *)
Definition valid_arc (a : CircularArc) : Prop :=
  let v1x := px (arc_mid a) - px (arc_start a) in
  let v1y := py (arc_mid a) - py (arc_start a) in
  let v2x := px (arc_end a) - px (arc_start a) in
  let v2y := py (arc_end a) - py (arc_start a) in
  v1x * v2y - v1y * v2x <> 0.

(* -------------------------------------------------------------------------- *)
(* §2  Circumscribed circle: arc_center, arc_radius.                          *)
(*                                                                            *)
(* Explicit circumcenter formula for a triangle with vertices A, B, C:        *)
(*                                                                            *)
(*   D  := 2 (Ax (By - Cy) + Bx (Cy - Ay) + Cx (Ay - By))                    *)
(*       (= 2 * signed area; non-zero iff non-collinear)                     *)
(*   Ux := ((Ax^2 + Ay^2)(By - Cy) + (Bx^2 + By^2)(Cy - Ay)                  *)
(*           + (Cx^2 + Cy^2)(Ay - By)) / D                                    *)
(*   Uy := ((Ax^2 + Ay^2)(Cx - Bx) + (Bx^2 + By^2)(Ax - Cx)                  *)
(*           + (Cx^2 + Cy^2)(Bx - Ax)) / D                                    *)
(*                                                                            *)
(* When `valid_arc a` holds, D /= 0 and `arc_center` is the unique point     *)
(* equidistant from the three control points.  The equidistance lemma is    *)
(* deferred to Session 5 (arc-in-hot-pixel) where it actually feeds into a  *)
(* downstream proof.                                                          *)
(* -------------------------------------------------------------------------- *)

Definition arc_center (a : CircularArc) : Point :=
  let ax := px (arc_start a) in let ay := py (arc_start a) in
  let bx := px (arc_mid   a) in let by_ := py (arc_mid   a) in
  let cx := px (arc_end   a) in let cy := py (arc_end   a) in
  let d := 2 * (ax * (by_ - cy) + bx * (cy - ay) + cx * (ay - by_)) in
  let na := ax * ax + ay * ay in
  let nb := bx * bx + by_ * by_ in
  let nc := cx * cx + cy * cy in
  let ux := (na * (by_ - cy) + nb * (cy - ay) + nc * (ay - by_)) / d in
  let uy := (na * (cx - bx) + nb * (ax - cx) + nc * (bx - ax)) / d in
  mkPoint ux uy.

Definition arc_radius (a : CircularArc) : R :=
  dist (arc_center a) (arc_start a).

(* -------------------------------------------------------------------------- *)
(* §3  CurveSegment, CurveRing, CurvePolygon, CurveGeometry.                  *)
(*                                                                            *)
(* SQL/MM COMPOUNDCURVE mixes chord and arc segments.  CurveSegment is the    *)
(* sum type.  The remaining levels mirror Phase 3's Overlay.v exactly:        *)
(*   CurveRing     := list CurveSegment   (parallel of Ring := list Point)   *)
(*   CurvePolygon  := { outer; holes }    (parallel of Polygon)              *)
(*   CurveGeometry := list CurvePolygon   (parallel of Geometry)             *)
(* -------------------------------------------------------------------------- *)

Inductive CurveSegment : Type :=
  | CSChord (s e : Point)
  | CSArc   (a : CircularArc).

(* Endpoint accessors -- straight chords expose their endpoints directly;
   arcs expose the start/end of the underlying CircularArc. *)
Definition curve_segment_start (s : CurveSegment) : Point :=
  match s with
  | CSChord p _ => p
  | CSArc a => arc_start a
  end.

Definition curve_segment_end (s : CurveSegment) : Point :=
  match s with
  | CSChord _ q => q
  | CSArc a => arc_end a
  end.

Definition CurveRing : Type := list CurveSegment.

Record CurvePolygon : Type := mkCurvePolygon {
  curve_outer : CurveRing;
  curve_holes : list CurveRing
}.

Definition CurveGeometry : Type := list CurvePolygon.

(* -------------------------------------------------------------------------- *)
(* §4  Validity predicates.                                                   *)
(*                                                                            *)
(* Mirroring Phase 3's `valid_polygon` / `valid_geometry` shape:              *)
(*   - All arc segments must satisfy `valid_arc` (non-collinear).            *)
(*   - Consecutive segments must connect at endpoints.                       *)
(*   - The ring must be closed (last segment's end = first segment's start). *)
(*                                                                            *)
(* Per audit doc §3 TRANSFER: these mirror Phase 3 directly, with the only   *)
(* novelty being the arc validity per-segment.                                *)
(* -------------------------------------------------------------------------- *)

(* All arc segments in a ring have non-collinear control points. *)
Definition curve_ring_arcs_valid (r : CurveRing) : Prop :=
  Forall (fun s => match s with
                   | CSChord _ _ => True
                   | CSArc a => valid_arc a
                   end) r.

(* Consecutive segments connect: end of one = start of next.  Stated
   inductively to avoid pattern-matching gymnastics in lemmas. *)
Fixpoint curve_ring_adjacent (r : CurveRing) : Prop :=
  match r with
  | [] => True
  | s1 :: rest =>
      match rest with
      | [] => True
      | s2 :: _ =>
          curve_segment_end s1 = curve_segment_start s2 /\
          curve_ring_adjacent rest
      end
  end.

(* Closed: end of last segment = start of first segment.  A ring with zero
   segments is not closed; a ring with one segment is closed iff its start
   equals its end (degenerate but admissible at the type level). *)
Definition curve_ring_closed (r : CurveRing) : Prop :=
  match r with
  | [] => False
  | s :: _ =>
      curve_segment_end (List.last r s) = curve_segment_start s
  end.

(* A CurveRing is valid if all three structural conditions hold. *)
Definition valid_curve_ring (r : CurveRing) : Prop :=
  curve_ring_arcs_valid r /\
  curve_ring_adjacent r /\
  curve_ring_closed r.

(* A CurvePolygon is valid if its outer ring is valid and every hole is
   a valid ring.  No hole-inside-outer or hole-disjoint constraints here
   (Phase 3 punts these to `hole_inside_outer` at the validity layer; we
   mirror the choice). *)
Definition valid_curve_polygon (cp : CurvePolygon) : Prop :=
  valid_curve_ring (curve_outer cp) /\
  Forall valid_curve_ring (curve_holes cp).

Definition valid_curve_geometry (cg : CurveGeometry) : Prop :=
  Forall valid_curve_polygon cg.

(* -------------------------------------------------------------------------- *)
(* §5  Chord approximation.                                                   *)
(*                                                                            *)
(* `chord_approx_arc a n` returns a list of points along `a` (the chord       *)
(* endpoints of an n-chord polyline approximation).  The `n` parameter        *)
(* controls the approximation tolerance: larger `n` => smaller sagitta.       *)
(*                                                                            *)
(* THIS SESSION (S2) lands the *degenerate* 3-point approximation             *)
(* `[arc_start a; arc_mid a; arc_end a]` which ignores `n`.  This is an       *)
(* honest valid Option B approximation (tolerance = sagitta of each half-arc) *)
(* and proves the structural shape works.  The refined n-chord trigonometric  *)
(* version + sagitta-bound proof lands in S6                                  *)
(* (`chord_approx_error_bound`).                                              *)
(* -------------------------------------------------------------------------- *)

Definition chord_approx_arc (a : CircularArc) (_n : nat) : list Point :=
  [arc_start a; arc_mid a; arc_end a].

Definition chord_approx_segment (s : CurveSegment) (n : nat) : list Point :=
  match s with
  | CSChord p q => [p; q]
  | CSArc a     => chord_approx_arc a n
  end.

(* Flatten a CurveRing's segment-by-segment chord approximation into a flat
   Ring.  Adjacent segments share their connection point under
   `curve_ring_adjacent`, so the flat_map introduces no duplication of
   meaning -- though some boundary points may appear twice in the list.
   Phase 3's `point_in_ring` (ray-crossing parity on `ring_edges`) is robust
   to duplicated vertices via its pairwise-edge construction. *)
Definition chord_approx_ring (r : CurveRing) (n : nat) : Ring :=
  flat_map (fun s => chord_approx_segment s n) r.

(* The Option B bridge: approximate every CurvePolygon's outer ring and
   holes as Phase 3 Rings, then package as a Geometry.  This is the
   compositional entry point that S3-S7 will refine. *)
Definition to_geometry (cg : CurveGeometry) (n : nat) : Geometry :=
  map (fun cp => mkPolygon
                   (chord_approx_ring (curve_outer cp) n)
                   (map (fun h => chord_approx_ring h n) (curve_holes cp)))
      cg.

(* -------------------------------------------------------------------------- *)
(* §6  Structural lemmas.                                                     *)
(*                                                                            *)
(* Five Qed-closed structural lemmas covering the nil / cons / chord cases.   *)
(* All are purely structural -- no real arithmetic, no Classical_Prop.classic *)
(* pulls.  Same role as Phase 3 Overlay.v's `valid_geometry_nil` /            *)
(* `valid_geometry_cons` family.                                              *)
(* -------------------------------------------------------------------------- *)

Lemma valid_curve_geometry_nil : valid_curve_geometry [].
Proof. unfold valid_curve_geometry. constructor. Qed.

Lemma valid_curve_geometry_cons :
  forall cp cg,
    valid_curve_polygon cp ->
    valid_curve_geometry cg ->
    valid_curve_geometry (cp :: cg).
Proof.
  intros cp cg Hcp Hcg.
  unfold valid_curve_geometry in *.
  constructor; assumption.
Qed.

Lemma to_geometry_nil : forall n, to_geometry [] n = [].
Proof. intros n. reflexivity. Qed.

(* Chord segments approximate to their two endpoints exactly, regardless of
   the approximation parameter -- chords are already exact. *)
Lemma chord_approx_segment_chord :
  forall p q n,
    chord_approx_segment (CSChord p q) n = [p; q].
Proof. intros p q n. reflexivity. Qed.

(* Arc segments approximate to the three control points (under the S2
   degenerate stub).  S6 will refine this to an n-chord polyline. *)
Lemma chord_approx_segment_arc_degenerate :
  forall a n,
    chord_approx_segment (CSArc a) n
      = [arc_start a; arc_mid a; arc_end a].
Proof. intros a n. reflexivity. Qed.

(* Empty CurveRing approximates to an empty Ring. *)
Lemma chord_approx_ring_nil :
  forall n, chord_approx_ring [] n = [].
Proof. intros n. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* §7  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions valid_curve_geometry_nil.
Print Assumptions valid_curve_geometry_cons.
Print Assumptions to_geometry_nil.
Print Assumptions chord_approx_segment_chord.
Print Assumptions chord_approx_segment_arc_degenerate.
Print Assumptions chord_approx_ring_nil.
