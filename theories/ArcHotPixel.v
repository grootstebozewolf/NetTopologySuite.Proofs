(* ============================================================================
   NetTopologySuite.Proofs.ArcHotPixel
   ----------------------------------------------------------------------------
   Phase 4 Session 5: arc-in-hot-pixel predicate.

   The arc analog of Phase 2's `segment_touches_hot_pixel`.  A circular arc
   passes through a hot pixel iff at least one of:

     - The arc crosses one of the four pixel edges (four arc-chord tests).
     - Either arc endpoint (arc_start or arc_end) lies inside the pixel.

   Six-way disjunction.  Inherits S4's Option S limitation
   (arcs < pi via `arc_span_contains`).  Same pixel parameterisation as
   Phase 2 (`C : Point`, `scale : R`, half-extent `/ (2 * scale)`) and the
   same half-open `<=, <` boundary convention from `in_hot_pixel`.

   DESIGN DECISIONS

   1. Disjunction definition (per the session prompt §6-tangent rule):
      cleaner to reason about than an existential over arc points + pixel.
      The existential "there exists a point on the arc in the pixel" is
      the SPEC; the disjunction is the DECISION PROCEDURE.  This file
      lands the decision procedure + structural lemmas relating each
      disjunct back to the predicate.

   2. Soundness (disjunction => point-on-arc-in-pixel) and completeness
      (point-on-arc-in-pixel => disjunction) DEFERRED to a follow-up.
      Soundness depends on S4's `arc_chord_intersect_sound`
      (Admitted, IVT-blocked).  Completeness requires geometric
      continuity reasoning that this session does not provide.  The
      endpoint-disjunct half of soundness IS structural (arc_start /
      arc_end in pixel => point on arc in pixel = arc_start / arc_end)
      and lands here.

   3. Parameterised by `scale`, mirroring Phase 2 exactly.  Hard-coding
      1/2 (scale = 1) would diverge from the established pattern.

   See `docs/audit-phase4-chord-overfitting.md` §3 (NEW PROOF row,
   `arc_in_hot_pixel`).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.

From NTS.Proofs Require Import Distance.
From NTS.Proofs Require Import HotPixel.
From NTS.Proofs Require Import CurveGeometry.
From NTS.Proofs Require Import ArcOrient.
From NTS.Proofs Require Import ArcIntersect.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Pixel corner helpers.                                                  *)
(*                                                                            *)
(* Parameterised by `C : Point` and `scale : R`.  Half-extent is              *)
(* `hot_pixel_radius scale` = `/ (2 * scale)` -- inherited from Phase 2's     *)
(* `theories/HotPixel.v`.                                                     *)
(*                                                                            *)
(* Half-open boundary convention (Phase 2): bottom + left edges are CLOSED,   *)
(* top + right edges are OPEN.  The corner names match the geometric          *)
(* placement; the open/closed distinction is in `in_hot_pixel`'s definition   *)
(* (lower bound `<=`, upper bound `<`).                                       *)
(* -------------------------------------------------------------------------- *)

Definition pixel_bottom_left (C : Point) (scale : R) : Point :=
  mkPoint (px C - hot_pixel_radius scale) (py C - hot_pixel_radius scale).

Definition pixel_bottom_right (C : Point) (scale : R) : Point :=
  mkPoint (px C + hot_pixel_radius scale) (py C - hot_pixel_radius scale).

Definition pixel_top_right (C : Point) (scale : R) : Point :=
  mkPoint (px C + hot_pixel_radius scale) (py C + hot_pixel_radius scale).

Definition pixel_top_left (C : Point) (scale : R) : Point :=
  mkPoint (px C - hot_pixel_radius scale) (py C + hot_pixel_radius scale).

(* -------------------------------------------------------------------------- *)
(* §2  arc_passes_through_hot_pixel.                                          *)
(*                                                                            *)
(* Six-way disjunction: four pixel-edge arc-chord crossings + two endpoint    *)
(* containment tests.                                                         *)
(*                                                                            *)
(* For arcs with subtended angle < pi (the Option S regime from S4), this    *)
(* is a sufficient condition for the arc to geometrically pass through the   *)
(* pixel.  Necessity (completeness) for the full geometric notion is         *)
(* deferred -- see §3 below.                                                  *)
(* -------------------------------------------------------------------------- *)

Definition arc_passes_through_hot_pixel
    (a : CircularArc) (C : Point) (scale : R) : Prop :=
  arc_chord_intersects a
    (pixel_bottom_left C scale) (pixel_bottom_right C scale) \/
  arc_chord_intersects a
    (pixel_bottom_right C scale) (pixel_top_right C scale) \/
  arc_chord_intersects a
    (pixel_top_right C scale) (pixel_top_left C scale) \/
  arc_chord_intersects a
    (pixel_top_left C scale) (pixel_bottom_left C scale) \/
  in_hot_pixel (arc_start a) C scale \/
  in_hot_pixel (arc_end a) C scale.

(* -------------------------------------------------------------------------- *)
(* §3  arc_touches_hot_pixel -- the SPEC predicate.                           *)
(*                                                                            *)
(* The existential form that captures the geometric intuition: there is a    *)
(* point on the arc that is in the pixel.  Direct arc analog of              *)
(* `segment_touches_hot_pixel` from Phase 2.                                  *)
(*                                                                            *)
(* The relationship to `arc_passes_through_hot_pixel`:                       *)
(*   - `arc_passes_through_hot_pixel` => `arc_touches_hot_pixel` is          *)
(*     SOUNDNESS.  Endpoint disjuncts close directly (the endpoint IS the    *)
(*     witness).  Edge-crossing disjuncts depend on `arc_chord_intersect_-   *)
(*     sound` (S4 Admitted, IVT-blocked).                                    *)
(*   - `arc_touches_hot_pixel` => `arc_passes_through_hot_pixel` is          *)
(*     COMPLETENESS.  Requires geometric continuity reasoning; deferred.     *)
(* -------------------------------------------------------------------------- *)

Definition arc_touches_hot_pixel
    (a : CircularArc) (C : Point) (scale : R) : Prop :=
  exists X : Point,
    in_hot_pixel X C scale /\
    inCircle_R (arc_start a) (arc_mid a) (arc_end a) X = 0 /\
    arc_span_contains a X.

(* -------------------------------------------------------------------------- *)
(* §4  Structural lemmas.                                                     *)
(* -------------------------------------------------------------------------- *)

(* Six per-disjunct introduction lemmas: each disjunct of arc_passes_through *)
(* implies the predicate.                                                     *)

Lemma arc_passes_through_hot_pixel_bottom :
  forall a C scale,
    arc_chord_intersects a
      (pixel_bottom_left C scale) (pixel_bottom_right C scale) ->
    arc_passes_through_hot_pixel a C scale.
Proof. intros. unfold arc_passes_through_hot_pixel. tauto. Qed.

Lemma arc_passes_through_hot_pixel_right :
  forall a C scale,
    arc_chord_intersects a
      (pixel_bottom_right C scale) (pixel_top_right C scale) ->
    arc_passes_through_hot_pixel a C scale.
Proof. intros. unfold arc_passes_through_hot_pixel. tauto. Qed.

Lemma arc_passes_through_hot_pixel_top :
  forall a C scale,
    arc_chord_intersects a
      (pixel_top_right C scale) (pixel_top_left C scale) ->
    arc_passes_through_hot_pixel a C scale.
Proof. intros. unfold arc_passes_through_hot_pixel. tauto. Qed.

Lemma arc_passes_through_hot_pixel_left :
  forall a C scale,
    arc_chord_intersects a
      (pixel_top_left C scale) (pixel_bottom_left C scale) ->
    arc_passes_through_hot_pixel a C scale.
Proof. intros. unfold arc_passes_through_hot_pixel. tauto. Qed.

Lemma arc_passes_through_hot_pixel_start :
  forall a C scale,
    in_hot_pixel (arc_start a) C scale ->
    arc_passes_through_hot_pixel a C scale.
Proof. intros. unfold arc_passes_through_hot_pixel. tauto. Qed.

Lemma arc_passes_through_hot_pixel_end :
  forall a C scale,
    in_hot_pixel (arc_end a) C scale ->
    arc_passes_through_hot_pixel a C scale.
Proof. intros. unfold arc_passes_through_hot_pixel. tauto. Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Endpoint soundness: partial close of `_passes_through => _touches`.    *)
(*                                                                            *)
(* For the endpoint disjuncts the soundness witness is the endpoint itself.  *)
(* arc_start is in its own arc span (proved via arc_span_contains_start in   *)
(* S4), is on its own circumcircle (inCircle_R_at_A from S3 -- a defining    *)
(* point of the determinant), and is in the pixel by hypothesis.             *)
(* Symmetric for arc_end.                                                    *)
(* -------------------------------------------------------------------------- *)

Lemma arc_passes_through_hot_pixel_start_touches :
  forall a C scale,
    in_hot_pixel (arc_start a) C scale ->
    arc_touches_hot_pixel a C scale.
Proof.
  intros a C scale Hin.
  unfold arc_touches_hot_pixel.
  exists (arc_start a).
  split; [|split].
  - exact Hin.
  - apply inCircle_R_at_A.
  - apply arc_span_contains_start.
Qed.

Lemma arc_passes_through_hot_pixel_end_touches :
  forall a C scale,
    in_hot_pixel (arc_end a) C scale ->
    arc_touches_hot_pixel a C scale.
Proof.
  intros a C scale Hin.
  unfold arc_touches_hot_pixel.
  exists (arc_end a).
  split; [|split].
  - exact Hin.
  - apply inCircle_R_at_C.
  - apply arc_span_contains_end.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Edge-crossing soundness (partial: structural part only).               *)
(*                                                                            *)
(* For an edge-crossing disjunct, the soundness witness is the chord-arc     *)
(* intersection point X (from `arc_chord_intersects`).  X is on the arc       *)
(* (on circumcircle + in span) by the intersection predicate.  What remains  *)
(* is showing X is in the pixel.                                              *)
(*                                                                            *)
(* X lies on the pixel edge chord, which is on the pixel boundary.  The      *)
(* half-open convention (bottom/left CLOSED, top/right OPEN) determines      *)
(* whether X-on-boundary satisfies `in_hot_pixel` exactly:                   *)
(*                                                                            *)
(*   - bottom edge: X has py(X) = py(C) - r.  in_hot_pixel needs              *)
(*     py(C) - r <= py(X) < py(C) + r -- the lower bound is CLOSED, so X    *)
(*     in_hot_pixel iff also px-range satisfied.  CLOSES STRUCTURALLY.       *)
(*                                                                            *)
(*   - top edge: X has py(X) = py(C) + r.  Upper bound is OPEN -- X NOT in   *)
(*     in_hot_pixel.  Requires IVT to slide along the arc to a strictly      *)
(*     interior point.                                                        *)
(*                                                                            *)
(*   - left / right edges: symmetric.                                         *)
(*                                                                            *)
(* The bottom + left edge cases are structurally closeable; top + right      *)
(* depend on IVT machinery (the same dependency as S4's                       *)
(* arc_chord_intersect_sound).  Deferred end-to-end to a follow-up session   *)
(* that handles the IVT piece.                                                *)
(*                                                                            *)
(* This file lands the endpoint half (above) and stops; the edge half is the *)
(* IVT-dependent piece.                                                       *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* §7  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions arc_passes_through_hot_pixel_bottom.
Print Assumptions arc_passes_through_hot_pixel_right.
Print Assumptions arc_passes_through_hot_pixel_top.
Print Assumptions arc_passes_through_hot_pixel_left.
Print Assumptions arc_passes_through_hot_pixel_start.
Print Assumptions arc_passes_through_hot_pixel_end.
Print Assumptions arc_passes_through_hot_pixel_start_touches.
Print Assumptions arc_passes_through_hot_pixel_end_touches.
