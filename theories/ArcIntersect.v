(* ============================================================================
   NetTopologySuite.Proofs.ArcIntersect
   ----------------------------------------------------------------------------
   Phase 4 Session 4: arc-chord and arc-arc intersection predicates (R-side).

   Two existence-Prop predicates plus the arc-span containment primitive
   they depend on.  Built on Session 3's `inCircle_R` + `arc_interior_side`.

   DESIGN DECISIONS

   1. R-SIDE PREDICATES ONLY.  This file defines `Prop`-valued intersection
      predicates over Stdlib `Reals`.  No binary64 / Flocq.  The b64
      computational layer (`HasArcIntersect` parallel typeclass per the
      §6 dovetail in `Intersect_b64_exact.v`) is a separate session that
      lands when arc-intersection COORDINATE COMPUTATION machinery is
      available.  Note: `HasIntersect` in `Intersect_b64_exact.v:2153`
      has signature `T -> T -> T -> T -> binary64` (returns intersection
      coordinates in b64) -- this is structurally not feasible for arcs
      without quadratic root-finding machinery.  Hence the parallel-
      typeclass design (per §6).

   2. ARC SPAN CONTAINMENT: Option S (chord cross product sign).
      `arc_span_contains a P := arc_interior_side a P \/ P = arc_start a
                                \/ P = arc_end a`.
      Correct for arcs with subtended angle < pi (the typical case).
      Reflex arcs (> pi) are not characterised correctly; that's a known
      limitation of the chord-sign test.  Option F (atan2-based angular
      ordering) is structurally heavier and not justified for Option B's
      chord-approximation thesis direction.

   3. SOUNDNESS PROOF: deferred.  An IVT-based proof showing the
      sign-change condition on `inCircle_R` along the chord parametrisation
      implies the existence of an intersection point requires `Ranalysis`
      machinery (continuity_pt + IVT_cor).  Per the prompt's tangent
      rule, soundness lands in a follow-up session.

   WHAT THIS FILE LANDS

     - `arc_span_contains` predicate.
     - `arc_chord_intersects` (existence: a point on chord segment that
       is also on the arc).
     - `arc_arc_intersects` (existence: a point on both arc circumcircles
       within both spans).
     - Six Qed-closed structural lemmas (boundary membership, symmetry).

   See `docs/audit-phase4-chord-overfitting.md` §3 (NEW PROOF row).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.

From NTS.Proofs Require Import Distance.
From NTS.Proofs Require Import CurveGeometry.
From NTS.Proofs Require Import ArcOrient.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Arc span containment (Option S).                                       *)
(*                                                                            *)
(* A point P lies "within" the arc span when either:                          *)
(*   - P is on the interior side of the chord (same side as arc_mid), or     *)
(*   - P equals arc_start or arc_end (boundary).                              *)
(*                                                                            *)
(* For arcs with subtended angle < pi this characterises arc membership      *)
(* exactly (assuming P is also on the circumscribed circle, which the         *)
(* intersection predicates below enforce).  Reflex arcs (> pi) fail this     *)
(* characterisation -- documented as a known limitation.                      *)
(* -------------------------------------------------------------------------- *)

Definition arc_span_contains (a : CircularArc) (P : Point) : Prop :=
  arc_interior_side a P \/
  P = arc_start a \/
  P = arc_end a.

(* -------------------------------------------------------------------------- *)
(* §2  Arc-chord intersection.                                                *)
(*                                                                            *)
(* Existence form: there is a point X on the chord segment PQ that is also   *)
(* on the arc (on the circle AND within the arc span).  The chord is        *)
(* parametrised by t in [0,1]; X is the convex combination.                  *)
(* -------------------------------------------------------------------------- *)

Definition arc_chord_intersects
    (a : CircularArc) (P Q : Point) : Prop :=
  exists (X : Point) (t : R),
    0 <= t <= 1 /\
    px X = (1 - t) * px P + t * px Q /\
    py X = (1 - t) * py P + t * py Q /\
    inCircle_R (arc_start a) (arc_mid a) (arc_end a) X = 0 /\
    arc_span_contains a X.

(* -------------------------------------------------------------------------- *)
(* §3  Arc-arc intersection.                                                  *)
(*                                                                            *)
(* Existence form: there is a point X that lies on both arcs (on both         *)
(* circumcircles AND within both spans).                                      *)
(* -------------------------------------------------------------------------- *)

Definition arc_arc_intersects
    (a1 a2 : CircularArc) : Prop :=
  exists X : Point,
    inCircle_R (arc_start a1) (arc_mid a1) (arc_end a1) X = 0 /\
    inCircle_R (arc_start a2) (arc_mid a2) (arc_end a2) X = 0 /\
    arc_span_contains a1 X /\
    arc_span_contains a2 X.

(* -------------------------------------------------------------------------- *)
(* §4  Necessary-condition predicate: chord crosses circumcircle.             *)
(*                                                                            *)
(* `chord_crosses_arc_circle a P Q`: the inCircle_R signs at P and Q differ. *)
(* This is the sign-change condition that an IVT argument would use to show  *)
(* existence of a circle-crossing point along the chord.  Computable from   *)
(* point coordinates alone (no existential).  Useful as a fast filter        *)
(* before the more expensive `arc_chord_intersects` test.                    *)
(* -------------------------------------------------------------------------- *)

Definition chord_crosses_arc_circle
    (a : CircularArc) (P Q : Point) : Prop :=
  let sP := inCircle_R (arc_start a) (arc_mid a) (arc_end a) P in
  let sQ := inCircle_R (arc_start a) (arc_mid a) (arc_end a) Q in
  sP * sQ < 0.

(* -------------------------------------------------------------------------- *)
(* §5  Structural lemmas.                                                     *)
(* -------------------------------------------------------------------------- *)

(* arc_start is in its own arc span (the second disjunct of arc_span_contains). *)
Lemma arc_span_contains_start :
  forall a : CircularArc,
    arc_span_contains a (arc_start a).
Proof.
  intros a. unfold arc_span_contains. right. left. reflexivity.
Qed.

(* arc_end is in its own arc span (the third disjunct). *)
Lemma arc_span_contains_end :
  forall a : CircularArc,
    arc_span_contains a (arc_end a).
Proof.
  intros a. unfold arc_span_contains. right. right. reflexivity.
Qed.

(* arc_mid is in its own arc span under valid_arc -- via arc_interior_side. *)
Lemma arc_span_contains_mid :
  forall a : CircularArc,
    valid_arc a -> arc_span_contains a (arc_mid a).
Proof.
  intros a Hva. unfold arc_span_contains. left.
  apply arc_interior_side_mid. exact Hva.
Qed.

(* Arc-chord intersection is symmetric in the chord direction. *)
Lemma arc_chord_intersects_sym :
  forall (a : CircularArc) (P Q : Point),
    arc_chord_intersects a P Q <->
    arc_chord_intersects a Q P.
Proof.
  intros a P Q.
  split; intros [X [t [Ht [Hpx [Hpy [Hcirc Hspan]]]]]];
    exists X, (1 - t);
    repeat split.
  - lra.
  - lra.
  - rewrite Hpx. ring.
  - rewrite Hpy. ring.
  - exact Hcirc.
  - exact Hspan.
  - lra.
  - lra.
  - rewrite Hpx. ring.
  - rewrite Hpy. ring.
  - exact Hcirc.
  - exact Hspan.
Qed.

(* Arc-arc intersection is symmetric in arc order. *)
Lemma arc_arc_intersects_sym :
  forall a1 a2 : CircularArc,
    arc_arc_intersects a1 a2 <->
    arc_arc_intersects a2 a1.
Proof.
  intros a1 a2.
  split; intros [X [Hc1 [Hc2 [Hs1 Hs2]]]]; exists X;
    repeat split; assumption.
Qed.

(* chord_crosses_arc_circle is symmetric (product is commutative). *)
Lemma chord_crosses_arc_circle_sym :
  forall (a : CircularArc) (P Q : Point),
    chord_crosses_arc_circle a P Q <->
    chord_crosses_arc_circle a Q P.
Proof.
  intros a P Q.
  unfold chord_crosses_arc_circle.
  split; intros Hpq; nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions arc_span_contains_start.
Print Assumptions arc_span_contains_end.
Print Assumptions arc_span_contains_mid.
Print Assumptions arc_chord_intersects_sym.
Print Assumptions arc_arc_intersects_sym.
Print Assumptions chord_crosses_arc_circle_sym.
