(* ============================================================================
   NetTopologySuite.Proofs.ArcChordSound
   ----------------------------------------------------------------------------
   Issue #64 ask #3c/#4c: ARC-CHORD SOUNDNESS — promoting "the chord crosses the
   circumcircle" (the Qed IVT terminal `chord_crosses_arc_circle_implies_
   circle_intersection`, ArcIntersectIVT.v) to "the chord crosses the arc SPAN"
   (`arc_chord_intersects`, ArcIntersect.v).

   THE GAP.  The IVT gives a point X on the *circle* with `between P Q X`, but
   `arc_chord_intersects` additionally needs `arc_span_contains a X` (X on
   `arc_mid`'s side of the chord line).  A circle-crossing can land on the
   *major* arc, so `chord_crosses_arc_circle -> arc_chord_intersects` is FALSE
   in general.  Every sound terminal must pin the crossing to the minor side.

   THE ARGUMENT (pure sign-algebra, no atan2 / angle / PI — stays 3-axiom).
   `arc_side_chord a (·) = cross_R_pt (arc_start a) (arc_end a) (·)` is AFFINE in
   its point argument, so along the chord
       arc_side_chord a X = (1-t)·arc_side_chord a P + t·arc_side_chord a Q
   for the convex parameter t of `between P Q X`.  If both chord endpoints are
   strictly on `arc_mid`'s side (`0 < s_mid·s_P` and `0 < s_mid·s_Q`), the
   convex combination keeps X strictly on that side for every t ∈ [0,1] — so the
   IVT crossing is in-span.  The minor-arc semantics is captured implicitly by
   the strict-side hypotheses; for arcs ≥ π they simply rarely hold (vacuously
   sound, no false claim, no angle dependency).

   WHAT THIS FILE LANDS
     - `arc_side_chord_of_between` — the affine identity along the chord.
     - `chord_crosses_arc_circle_span_sound` — (a) the honest conditional floor
       (names the missing span hypothesis in the signature; not an Admitted).
     - `chord_crosses_arc_circle_minor_side_sound` — (b) both chord endpoints
       strictly on the minor side ⇒ in-span crossing (the geometric advance).
     - `chord_crosses_arc_circle_{start,end}_anchored_sound` — (c) one chord
       endpoint IS a control point (the common arc-self-intersection / V-CP
       case); removes one side hypothesis via the boundary disjunct.

   STILL OPEN (deliberately quarantined, NOT Admitted): the unconditional
   minor-guard promotion (sweep ≤ π ALONE ⇒ soundness, without a side/endpoint
   hypothesis).  It is false without such a hypothesis (a crossing can hit the
   major arc); see docs/issue-64-arc-primitives-triage.md rows #3c/#4c.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.

From NTS.Proofs Require Import Distance.
From NTS.Proofs Require Import Segment.
From NTS.Proofs Require Import CurveGeometry.
From NTS.Proofs Require Import ArcOrient.
From NTS.Proofs Require Import ArcIntersect.
From NTS.Proofs Require Import ArcIntersectIVT.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Affine algebra of the chord-side function.                             *)
(* -------------------------------------------------------------------------- *)

(* Point extensionality (Point := mkPoint { px; py } in Distance.v). *)
Lemma point_ext :
  forall p q : Point, px p = px q -> py p = py q -> p = q.
Proof.
  intros [a1 b1] [a2 b2] Hx Hy. simpl in Hx, Hy. subst. reflexivity.
Qed.

(* `arc_side_chord` is affine along the chord: a convex combination of the
   endpoint sides.  Derived directly from the `between` witness coordinates,
   so it does not depend on recovering the IVT parameter.  Pure `ring`. *)
Lemma arc_side_chord_of_between :
  forall (a : CircularArc) (P Q X : Point) (t : R),
    px X = (1 - t) * px P + t * px Q ->
    py X = (1 - t) * py P + t * py Q ->
    arc_side_chord a X
    = (1 - t) * arc_side_chord a P + t * arc_side_chord a Q.
Proof.
  intros a P Q X t Hx Hy.
  unfold arc_side_chord, cross_R_pt.
  rewrite Hx, Hy. ring.
Qed.

(* A convex combination of two strictly-positive reals is strictly positive. *)
Lemma convex_combo_pos :
  forall t A B : R,
    0 <= t -> t <= 1 -> 0 < A -> 0 < B ->
    0 < (1 - t) * A + t * B.
Proof.
  intros t A B Ht0 Ht1 HA HB.
  destruct (Rle_lt_dec t (/2)) as [Hle|Hgt]; nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  (a) Conditional floor: the missing span hypothesis, named honestly.    *)
(* -------------------------------------------------------------------------- *)

Theorem chord_crosses_arc_circle_span_sound :
  forall (a : CircularArc) (P Q : Point),
    chord_crosses_arc_circle a P Q ->
    (forall X : Point,
       between P Q X ->
       inCircle_R (arc_start a) (arc_mid a) (arc_end a) X = 0 ->
       arc_span_contains a X) ->
    arc_chord_intersects a P Q.
Proof.
  intros a P Q Hcross Hspan.
  destruct (chord_crosses_arc_circle_implies_circle_intersection a P Q Hcross)
    as [X [Hbtw Hcirc]].
  exists X. split; [exact Hbtw | split; [exact Hcirc | ]].
  apply Hspan; [exact Hbtw | exact Hcirc].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  (b) Both chord endpoints strictly on the minor side ⇒ in-span crossing.*)
(* -------------------------------------------------------------------------- *)

Theorem chord_crosses_arc_circle_minor_side_sound :
  forall (a : CircularArc) (P Q : Point),
    valid_arc a ->
    0 < arc_side_chord a (arc_mid a) * arc_side_chord a P ->
    0 < arc_side_chord a (arc_mid a) * arc_side_chord a Q ->
    chord_crosses_arc_circle a P Q ->
    arc_chord_intersects a P Q.
Proof.
  intros a P Q Hva HsP HsQ Hcross.
  destruct (chord_crosses_arc_circle_implies_circle_intersection a P Q Hcross)
    as [X [Hbtw Hcirc]].
  exists X. split; [exact Hbtw | split; [exact Hcirc | ]].
  destruct Hbtw as [t [Ht0 [Ht1 [Hx Hy]]]].
  left. unfold arc_interior_side.
  rewrite (arc_side_chord_of_between a P Q X t Hx Hy).
  replace (arc_side_chord a (arc_mid a)
           * ((1 - t) * arc_side_chord a P + t * arc_side_chord a Q))
    with ((1 - t) * (arc_side_chord a (arc_mid a) * arc_side_chord a P)
          + t * (arc_side_chord a (arc_mid a) * arc_side_chord a Q)) by ring.
  apply convex_combo_pos; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  (c) Endpoint-anchored: one chord endpoint is a control point.          *)
(*                                                                            *)
(* The common arc-self-intersection / V-CP case: a chord emanating from a     *)
(* control point.  `arc_side_chord a (arc_start a) = 0` (the chord line passes *)
(* through its own endpoint), so only the OTHER endpoint's side is needed;    *)
(* the t = 0 boundary hit lands on `arc_start a`, in-span by the boundary     *)
(* disjunct.                                                                   *)
(* -------------------------------------------------------------------------- *)

Theorem chord_crosses_arc_circle_start_anchored_sound :
  forall (a : CircularArc) (P Q : Point),
    valid_arc a ->
    P = arc_start a ->
    0 < arc_side_chord a (arc_mid a) * arc_side_chord a Q ->
    chord_crosses_arc_circle a P Q ->
    arc_chord_intersects a P Q.
Proof.
  intros a P Q Hva HP HsQ Hcross.
  destruct (chord_crosses_arc_circle_implies_circle_intersection a P Q Hcross)
    as [X [Hbtw Hcirc]].
  exists X. split; [exact Hbtw | split; [exact Hcirc | ]].
  destruct Hbtw as [t [Ht0 [Ht1 [Hx Hy]]]].
  assert (HsP0 : arc_side_chord a P = 0).
  { rewrite HP. unfold arc_side_chord, cross_R_pt. ring. }
  destruct (Rle_lt_dec t 0) as [Hle|Hgt].
  - (* t = 0: X = P = arc_start a, in-span by the boundary disjunct. *)
    assert (Ht00 : t = 0) by lra.
    assert (HXs : X = arc_start a).
    { apply point_ext.
      - rewrite Hx, Ht00, HP. ring.
      - rewrite Hy, Ht00, HP. ring. }
    rewrite HXs. apply arc_span_contains_start.
  - (* 0 < t: strict interior side. *)
    left. unfold arc_interior_side.
    rewrite (arc_side_chord_of_between a P Q X t Hx Hy), HsP0.
    replace (arc_side_chord a (arc_mid a)
             * ((1 - t) * 0 + t * arc_side_chord a Q))
      with (t * (arc_side_chord a (arc_mid a) * arc_side_chord a Q)) by ring.
    nra.
Qed.

Theorem chord_crosses_arc_circle_end_anchored_sound :
  forall (a : CircularArc) (P Q : Point),
    valid_arc a ->
    Q = arc_end a ->
    0 < arc_side_chord a (arc_mid a) * arc_side_chord a P ->
    chord_crosses_arc_circle a P Q ->
    arc_chord_intersects a P Q.
Proof.
  intros a P Q Hva HQ HsP Hcross.
  destruct (chord_crosses_arc_circle_implies_circle_intersection a P Q Hcross)
    as [X [Hbtw Hcirc]].
  exists X. split; [exact Hbtw | split; [exact Hcirc | ]].
  destruct Hbtw as [t [Ht0 [Ht1 [Hx Hy]]]].
  assert (HsQ0 : arc_side_chord a Q = 0).
  { rewrite HQ. unfold arc_side_chord, cross_R_pt. ring. }
  destruct (Rle_lt_dec 1 t) as [Hge|Hlt].
  - (* t = 1: X = Q = arc_end a, in-span by the boundary disjunct. *)
    assert (Ht11 : t = 1) by lra.
    assert (HXe : X = arc_end a).
    { apply point_ext.
      - rewrite Hx, Ht11, HQ. ring.
      - rewrite Hy, Ht11, HQ. ring. }
    rewrite HXe. apply arc_span_contains_end.
  - (* t < 1: strict interior side. *)
    left. unfold arc_interior_side.
    rewrite (arc_side_chord_of_between a P Q X t Hx Hy), HsQ0.
    replace (arc_side_chord a (arc_mid a)
             * ((1 - t) * arc_side_chord a P + t * 0))
      with ((1 - t) * (arc_side_chord a (arc_mid a) * arc_side_chord a P)) by ring.
    nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions arc_side_chord_of_between.
Print Assumptions chord_crosses_arc_circle_span_sound.
Print Assumptions chord_crosses_arc_circle_minor_side_sound.
Print Assumptions chord_crosses_arc_circle_start_anchored_sound.
Print Assumptions chord_crosses_arc_circle_end_anchored_sound.
