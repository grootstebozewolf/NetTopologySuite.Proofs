(* ============================================================================
   NetTopologySuite.Proofs.ArcArcSound
   ----------------------------------------------------------------------------
   Issue #64 ask #5b / JTS curve-awareness N-AA: ARC-ARC INTERSECTION SOUNDNESS,
   first bounded slice.

   `ArcIntersect.arc_arc_intersects a1 a2` is an EXISTENCE predicate: some point
   X lies on BOTH circumcircles (`inCircle_R = 0` for each) AND in BOTH arc spans
   (`arc_span_contains`).  Until now only structural symmetry lemmas existed; no
   constructive soundness.  This file lands the cheapest honest terminals,
   reusing the already-Qed arc-CHORD IVT result and the affine span algebra:

     - `inCircle_R_arc_{start,end}_self` : an arc's own chord endpoints lie on
       its circumcircle (the trivial but load-bearing membership facts).
     - `arc_arc_intersects_shared_vertex` (HEADLINE, unconditional): if two arcs
       share an endpoint (`arc_end a1 = arc_start a2`), that shared point is a
       genuine arc-arc intersection.  No IVT, no side hypothesis.  This is
       exactly the configuration of `CurveGeometry.curve_ring_adjacent` arc
       chains (consecutive segments meet), so it is non-vacuous on real
       CompoundCurve/CircularString rings.
     - `arc_arc_intersects_of_chord_cross_cond` (conditional floor): when a2's
       CHORD crosses a1's circumcircle (strict opposite `inCircle_R` signs), the
       IVT (`ArcIntersectIVT.chord_crosses_arc_circle_implies_circle_intersection`)
       produces a point on a1's circle; promoting it to a full arc-arc
       intersection needs the missing facts (that point also on a2's circle, and
       in both spans), named honestly as one bundled hypothesis -- the arc-arc
       analogue of `ArcChordSound.chord_crosses_arc_circle_span_sound`.

   Pure structural / sign reasoning; THREE-AXIOM (the classical-reals trio).  The
   IVT route via Stdlib `IVT_cor`/`Ranalysis_reg` pulls no `Classical_Prop.classic`
   (that enters only via `atan`/`sin_lt_x`), so no `docs/audit-exceptions.txt`
   entry is needed.  No `Admitted`/`Axiom`/`Parameter`.

   DEFERRED (honest scope): the UNCONDITIONAL both-circles existence for two arcs
   that cross at interior points (the radical-line / sqrt-discriminant coordinate
   story -- still the genuinely hard #5b frontier); explicit intersection
   coordinates and a binary64 layer; interior (non-endpoint) span membership for
   a2-chord crossings; and reflex/sweep >= pi arcs (the chord-side `arc_span`
   characterisation is exact only for sweep < pi -- quarantined, not Admitted).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (claude-opus-4-8)
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import Distance Segment CurveGeometry ArcOrient
  ArcIntersect ArcIntersectIVT.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  An arc's chord endpoints lie on its own circumcircle.                   *)
(* -------------------------------------------------------------------------- *)

Lemma inCircle_R_arc_start_self :
  forall a : CircularArc,
    inCircle_R (arc_start a) (arc_mid a) (arc_end a) (arc_start a) = 0.
Proof. intro a. apply inCircle_R_at_A. Qed.

Lemma inCircle_R_arc_end_self :
  forall a : CircularArc,
    inCircle_R (arc_start a) (arc_mid a) (arc_end a) (arc_end a) = 0.
Proof. intro a. apply inCircle_R_at_C. Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Headline (unconditional): a shared endpoint IS an arc-arc intersection. *)
(*                                                                            *)
(* The shared point lies on both circumcircles (§1) and is an endpoint of each *)
(* arc, hence in each span (`arc_span_contains_{end,start}`).  Covers          *)
(* consecutive arcs of a CompoundCurve / CircularString ring                   *)
(* (`curve_ring_adjacent`: end of one segment = start of the next).            *)
(* -------------------------------------------------------------------------- *)

Theorem arc_arc_intersects_shared_vertex :
  forall a1 a2 : CircularArc,
    arc_end a1 = arc_start a2 ->
    arc_arc_intersects a1 a2.
Proof.
  intros a1 a2 Hshare.
  exists (arc_end a1). split; [| split; [| split]].
  - apply inCircle_R_arc_end_self.
  - rewrite Hshare. apply inCircle_R_arc_start_self.
  - apply arc_span_contains_end.
  - rewrite Hshare. apply arc_span_contains_start.
Qed.

(* Variant: arcs sharing the other endpoint pairing (start of a1 = end of a2). *)
Corollary arc_arc_intersects_shared_vertex_rev :
  forall a1 a2 : CircularArc,
    arc_start a1 = arc_end a2 ->
    arc_arc_intersects a1 a2.
Proof.
  intros a1 a2 Hshare.
  apply (proj1 (arc_arc_intersects_sym a2 a1)).
  apply arc_arc_intersects_shared_vertex. symmetry. exact Hshare.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Conditional floor: a2's chord crossing a1's circle, promoted via IVT.   *)
(*                                                                            *)
(* The IVT gives a point X on a1's circle between a2's endpoints; X is on a2's *)
(* CHORD (generally strictly inside a2's circle), so the remaining facts (X on *)
(* a2's circle and in both spans) are bundled as one named hypothesis -- the   *)
(* honest conditional, mirroring ArcChordSound.chord_crosses_arc_circle_span_  *)
(* sound.  (The hypothesis is itself the deferred unconditional content.)      *)
(* -------------------------------------------------------------------------- *)

Theorem arc_arc_intersects_of_chord_cross_cond :
  forall a1 a2 : CircularArc,
    chord_crosses_arc_circle a1 (arc_start a2) (arc_end a2) ->
    (forall X : Point,
       between (arc_start a2) (arc_end a2) X ->
       inCircle_R (arc_start a1) (arc_mid a1) (arc_end a1) X = 0 ->
       inCircle_R (arc_start a2) (arc_mid a2) (arc_end a2) X = 0
       /\ arc_span_contains a1 X
       /\ arc_span_contains a2 X) ->
    arc_arc_intersects a1 a2.
Proof.
  intros a1 a2 Hcross Hbridge.
  destruct (chord_crosses_arc_circle_implies_circle_intersection
              a1 (arc_start a2) (arc_end a2) Hcross) as [X [Hbtw Hc1]].
  destruct (Hbridge X Hbtw Hc1) as [Hc2 [Hs1 Hs2]].
  exists X. split; [exact Hc1 | split; [exact Hc2 | split; [exact Hs1 | exact Hs2]]].
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions inCircle_R_arc_end_self.
Print Assumptions arc_arc_intersects_shared_vertex.
Print Assumptions arc_arc_intersects_of_chord_cross_cond.
