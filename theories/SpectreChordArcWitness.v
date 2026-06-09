(* ============================================================================
   NetTopologySuite.Proofs.SpectreChordArcWitness
   ----------------------------------------------------------------------------
   CHORD-vs-ARC clip divergence -- the "rounded edge" companion to
   theories/SpectreExample.v.

   The canonical SPECTRE monotile is the aperiodic tile drawn with CURVED
   (arc) edges; SpectreExample.v uses the polygonal Tile(1,1) skeleton (straight
   chords).  This file answers a sharp question that distinction raises:

       is there a hot pixel that a Spectre edge's straight CHORD clips, but the
       actual ARC misses?

   YES -- and it is exhibited here, unconditionally and `Qed`.  This is the
   concrete hot-pixel form of the chord-overfitting / linearisation-instability
   theme (cf. Linearise.regime3_counterexample, the sagitta bound in
   ArcChordApprox.v, docs/audit-phase4-chord-overfitting.md): a *false positive*
   of chord approximation against the passes-through predicate.

   THE WITNESS.  Take a Spectre foot edge replaced by a shallow downward arc:
     arc_start = (-1, 1),  arc_mid = (0, 1/2),  arc_end = (1, 1).
   These lie on the circle centred (0, 7/4) of radius 5/4 (sagitta 1/2 below the
   chord).  The straight chord is the segment (-1,1)-(1,1) at height y = 1.
   Put a hot pixel at the chord midpoint C = (0,1), scale = 2 (half-extent 1/4),
   i.e. the box [-1/4,1/4) x [3/4,5/4).

     - The CHORD clips it: its midpoint (0,1) (parameter t = 1/2) is in the box.
     - The ARC misses it: the box lies strictly INSIDE the circle, so no point of
       the box is on the arc.  The in-circle value is the circle power
       `inCircle_R = 25/16 - x^2 - (y - 7/4)^2`, which is >= 1/2 > 0 (hence never
       0) for every (x,y) in the box.

   Pure `R`; no Admitted / Axiom / Parameter.  Standard three-axiom
   classical-reals base (lra / nra / ring only).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance HotPixel CurveGeometry ArcOrient
                               ArcIntersect ArcHotPixel.

Local Open Scope R_scope.

(* A shallow downward arc on a Spectre foot edge: chord (-1,1)-(1,1), bulging
   down to (0,1/2).  Circle: centre (0,7/4), radius 5/4, sagitta 1/2. *)
Definition spectre_arc : CircularArc :=
  mkCircularArc (mkPoint (-1) 1) (mkPoint 0 (1/2)) (mkPoint 1 1).

(* Hot-pixel centre at the chord midpoint; scale 2 => half-extent 1/4. *)
Definition spectre_pix_C : Point := mkPoint 0 1.
Definition spectre_scale : R := 2.

(* The three control points are non-collinear, so the circle is well-defined. *)
Lemma spectre_arc_valid : valid_arc spectre_arc.
Proof. unfold valid_arc, spectre_arc; cbn [arc_start arc_mid arc_end px py]. lra. Qed.

(* The circle-power identity: inCircle_R of the three control points at any X is
   `25/16 - x^2 - (y - 7/4)^2`, the (scaled) power of X wrt the circle. *)
Lemma spectre_inCircle_power :
  forall X : Point,
    inCircle_R (arc_start spectre_arc) (arc_mid spectre_arc) (arc_end spectre_arc) X
      = 25/16 - px X * px X - (py X - 7/4) * (py X - 7/4).
Proof.
  intros X.
  unfold spectre_arc, inCircle_R; cbn [arc_start arc_mid arc_end px py]. field.
Qed.

(* Every point of the hot pixel is strictly inside the circle: inCircle_R >= 1/2. *)
Lemma spectre_pixel_inside_circle :
  forall X : Point,
    in_hot_pixel X spectre_pix_C spectre_scale ->
    inCircle_R (arc_start spectre_arc) (arc_mid spectre_arc) (arc_end spectre_arc) X
      >= 1/2.
Proof.
  intros X Hin.
  unfold in_hot_pixel, spectre_pix_C, spectre_scale, hot_pixel_radius in Hin.
  cbn [px py] in Hin.
  destruct Hin as [[Hxlo Hxhi] [Hylo Hyhi]].
  rewrite spectre_inCircle_power.
  (* -1/4 <= px X < 1/4 and 3/4 <= py X < 5/4 give x^2 <= 1/16, (y-7/4)^2 <= 1 *)
  nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* THE WITNESS: the chord clips the pixel; the arc does not.                   *)
(* -------------------------------------------------------------------------- *)
Theorem spectre_chord_clips_arc_misses :
  (* the straight CHORD (arc_start -- arc_end) passes through the pixel ... *)
  segment_touches_hot_pixel
    (arc_start spectre_arc) (arc_end spectre_arc) spectre_pix_C spectre_scale
  (* ... but the ARC does not. *)
  /\ ~ arc_touches_hot_pixel spectre_arc spectre_pix_C spectre_scale.
Proof.
  split.
  - (* chord: the midpoint (t = 1/2) is (0,1), the pixel centre, in the box. *)
    exists (1/2). split; [ lra | ].
    unfold spectre_arc, in_hot_pixel, segment_point, spectre_pix_C,
           spectre_scale, hot_pixel_radius;
      cbn [arc_start arc_end px py].
    split; lra.
  - (* arc: any in-pixel point X would need inCircle_R X = 0, but it is >= 1/2. *)
    intros [X [Hin [Hcirc _]]].
    pose proof (spectre_pixel_inside_circle X Hin) as Hpow.
    lra.
Qed.

(* The same divergence against the DECISION-PROCEDURE predicate
   `arc_passes_through_hot_pixel` (the six-way disjunction).  Every disjunct
   fails: each edge-crossing would put a circle point on a pixel edge (between
   two corners), but the whole closed box is inside the circle
   (`inCircle_R >= 1/2 > 0` there); and both arc endpoints (x = +/-1) are outside
   the box (x in [-1/4,1/4)). *)

(* No point of the CLOSED pixel box lies on the circle. *)
Lemma spectre_closed_box_off_circle :
  forall X : Point,
    -(1/4) <= px X <= 1/4 ->
    3/4 <= py X <= 5/4 ->
    inCircle_R (arc_start spectre_arc) (arc_mid spectre_arc)
               (arc_end spectre_arc) X >= 1/2.
Proof. intros X Hx Hy. rewrite spectre_inCircle_power. nra. Qed.

(* A `between` of two pixel corners stays in the closed box (per axis bounds). *)
Ltac edge_off_circle H :=
  unfold arc_chord_intersects in H;
  destruct H as [X [Hbetween [Hcirc _]]];
  destruct Hbetween as [t [Ht0 [Ht1 [HpxX HpyX]]]];
  unfold pixel_bottom_left, pixel_bottom_right, pixel_top_right,
         pixel_top_left, spectre_pix_C, spectre_scale, hot_pixel_radius
    in HpxX, HpyX;
  cbn [px py] in HpxX, HpyX;
  pose proof (spectre_closed_box_off_circle X ltac:(nra) ltac:(nra)) as HB;
  lra.

Ltac endpoint_off_box H :=
  unfold in_hot_pixel, spectre_arc, spectre_pix_C, spectre_scale,
         hot_pixel_radius in H;
  cbn [arc_start arc_end px py] in H; lra.

Theorem spectre_chord_clips_arc_passes_misses :
  ~ arc_passes_through_hot_pixel spectre_arc spectre_pix_C spectre_scale.
Proof.
  unfold arc_passes_through_hot_pixel.
  intros Hdisj.
  destruct Hdisj as [He | [He | [He | [He | [He | He]]]]].
  - edge_off_circle He.
  - edge_off_circle He.
  - edge_off_circle He.
  - edge_off_circle He.
  - endpoint_off_box He.   (* arc_start: x = -1 not in [-1/4, 1/4) *)
  - endpoint_off_box He.   (* arc_end:   x =  1 not in [-1/4, 1/4) *)
Qed.
