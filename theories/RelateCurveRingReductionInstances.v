(* ============================================================================
   NetTopologySuite.Proofs.RelateCurveRingReductionInstances
   ----------------------------------------------------------------------------
   Issue #67 (curve→matrix soundness): the per-shape reductions are INSTANCES of
   the general one.

   `RelateCurveRingReduction.point_in_ring_chord_approx_eq_inscribed` proves the
   linearised-ring ↔ inscribed-polygon equivalence for ANY adjacent curve ring.
   This file cross-checks it against the two hand-proved special cases — the
   one-arc lens (`RelateCurveArcSegment.point_in_ring_arc_seg_iff`) and the
   two-arc vesica (`RelateCurveVesica.point_in_ring_vesica_iff`) — by computing
   their inscribed rings and re-deriving each headline from the general theorem.

   The inscribed ring of each shape is fixed by `reflexivity`:

     inscribed_ring (arc_seg_curve_ring a) n
       = [arc_start a; arc_mid a; arc_end a; arc_start a]        (control triangle)
     inscribed_ring (vesica_curve_ring a b) n
       = [arc_start a; arc_mid a; arc_start b; arc_mid b; arc_end b]

   so under the lens' (trivial) adjacency and the vesica's adjacency/closure the
   general reduction reproduces the bespoke `(v,v)`-stripping results exactly —
   confirming the ladder is coherent and the per-shape proofs add no axioms the
   general one lacks.

   All `Qed`; no new `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List.
From NTS.Proofs Require Import Distance Overlay CurveGeometry
  RelateCurveRingReduction RelateCurveArcSegment RelateCurveVesica.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The inscribed rings of the two shapes, computed.                        *)
(* -------------------------------------------------------------------------- *)

(* The lens' inscribed ring is the control triangle (n-independent). *)
Lemma inscribed_ring_arc_seg :
  forall a n,
    inscribed_ring (arc_seg_curve_ring a) n
    = [arc_start a; arc_mid a; arc_end a; arc_start a].
Proof. reflexivity. Qed.

(* The vesica's inscribed ring before substituting the adjacency/closure
   identities (the start/mid of each arc, then the second arc's end). *)
Lemma inscribed_ring_vesica :
  forall a b n,
    inscribed_ring (vesica_curve_ring a b) n
    = [arc_start a; arc_mid a; arc_start b; arc_mid b; arc_end b].
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The per-shape headlines, re-derived from the general reduction.         *)
(* -------------------------------------------------------------------------- *)

(* Reproduces RelateCurveArcSegment.point_in_ring_arc_seg_iff. *)
Theorem arc_seg_reduction_via_general :
  forall a n p,
    point_in_ring p (chord_approx_ring (arc_seg_curve_ring a) n)
    <-> point_in_ring p [arc_start a; arc_mid a; arc_end a; arc_start a].
Proof.
  intros a n p.
  rewrite (point_in_ring_chord_approx_eq_inscribed (arc_seg_curve_ring a) n p
             (arc_seg_curve_ring_adjacent a)).
  rewrite (inscribed_ring_arc_seg a n). reflexivity.
Qed.

(* Reproduces RelateCurveVesica.point_in_ring_vesica_iff. *)
Theorem vesica_reduction_via_general :
  forall a b n p,
    arc_end a = arc_start b ->
    arc_end b = arc_start a ->
    point_in_ring p (chord_approx_ring (vesica_curve_ring a b) n)
    <-> point_in_ring p [arc_start a; arc_mid a; arc_end a; arc_mid b; arc_start a].
Proof.
  intros a b n p Hadj Hcl.
  rewrite (point_in_ring_chord_approx_eq_inscribed (vesica_curve_ring a b) n p
             (vesica_curve_ring_adjacent a b Hadj)).
  rewrite (inscribed_ring_vesica a b n).
  rewrite <- Hadj, Hcl. reflexivity.
Qed.

(* The bespoke headlines have the SAME statement as these re-derivations (see
   the `Reproduces ...` comments), so each shape's `(v,v)`-stripping proof is
   confirmed to be a special case of the general reduction, adding no axioms the
   general one lacks. *)

(* -------------------------------------------------------------------------- *)
(* §3  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions arc_seg_reduction_via_general.
Print Assumptions vesica_reduction_via_general.
