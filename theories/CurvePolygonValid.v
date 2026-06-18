(* ============================================================================
   NetTopologySuite.Proofs.CurvePolygonValid
   ----------------------------------------------------------------------------
   Issue #64 / JTS #1195 §7 V-CP (CP_VALID): the HOLES-INSIDE-SHELL component of
   CurvePolygon validity -- the second V-CP slice (after the ring-simplicity
   layer of CurvePolygonSimple.v).

   `CurveGeometry.valid_curve_polygon` is structural only; CP_VALID adds
   ring-simplicity (DONE, simple_curve_polygon), HOLES-INSIDE-SHELL (here),
   holes-disjoint, and sector orientation (the next slices).

   This file reduces curve-polygon containment to the Phase-3 LINEAR machinery
   through the merged densification bridge `CurveGeometry.chord_approx_ring`
   (a CurveRing -> Overlay.Ring).  Because `chord_approx_arc` currently returns
   the three control points `[start; mid; end]`, the bridge is the EXACT rational
   INSCRIBED CONTROL POLYGON -- so `Overlay.point_in_ring` (ray-parity) and
   `Overlay.hole_inside_outer` on it are exact, no trig.

   IMPORTANT (oracle vs proof): the inscribed control polygon is a sound
   UNDER-approximation of the true curved region (it omits the arc bulges):
   `point_in_inscribed_ring p r n  =>  p is in the true region`, but NOT
   conversely (a point in a bulge reads false).  The POINT_IN_CURVE_RING oracle
   computes the TRUE region by ARC-AWARE ray casting (interface-boundary float,
   allowlisted), whose Jordan soundness is the deferred frontier (pinned by the
   adversarial test).  This file proves the EXACT inscribed floor -- the
   sound-but-conservative containment.

   Defined here (all THREE-AXIOM, exact):
     §1  `point_in_inscribed_ring p r n` := p inside the inscribed densified
         ring (`point_in_ring p (chord_approx_ring r n)`).
     §2  `curve_polygon_holes_inside_shell cp n` := every hole's densified ring
         sits inside the densified outer (`hole_inside_outer`).
         `valid_curve_polygon_cp cp n` := `simple_curve_polygon cp` (merged) AND
         holes-inside-shell (the conservative, sound containment).
     §3  Projections: a CP-valid polygon is simple and, for each hole, has a
         hole vertex inside the inscribed outer ring
         (`valid_curve_polygon_cp_hole_witness`).

   DEFERRED (honest scope): TRUE-region containment (the arc-aware oracle, Jordan
   soundness); the refined n-chord densification; the "every hole point inside"
   Jordan strengthening of `hole_inside_outer`.  Sector orientation and holes
   mutually disjoint are the remaining CP_VALID slices.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (claude-opus-4-8)
   ========================================================================== *)

From Stdlib Require Import List.
From NTS.Proofs Require Import Distance CurveGeometry Overlay CurvePolygonSimple.
Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  Point inside the INSCRIBED curve ring (densified control polygon).      *)
(*     Sound under-approximation of the true region (omits the arc bulges).    *)
(* -------------------------------------------------------------------------- *)

Definition point_in_inscribed_ring (p : Point) (r : CurveRing) (n : nat) : Prop :=
  point_in_ring p (chord_approx_ring r n).

(* -------------------------------------------------------------------------- *)
(* §2  Holes-inside-shell and the composite CP-validity predicate.             *)
(* -------------------------------------------------------------------------- *)

Definition curve_polygon_holes_inside_shell (cp : CurvePolygon) (n : nat) : Prop :=
  Forall (fun h => hole_inside_outer (chord_approx_ring (curve_outer cp) n)
                                     (chord_approx_ring h n))
         (curve_holes cp).

Definition valid_curve_polygon_cp (cp : CurvePolygon) (n : nat) : Prop :=
  simple_curve_polygon cp /\ curve_polygon_holes_inside_shell cp n.

(* -------------------------------------------------------------------------- *)
(* §3  Projections -- the per-ring / per-hole facts the oracle pins.           *)
(* -------------------------------------------------------------------------- *)

Lemma valid_curve_polygon_cp_simple :
  forall (cp : CurvePolygon) (n : nat),
    valid_curve_polygon_cp cp n -> simple_curve_polygon cp.
Proof. intros cp n [H _]. exact H. Qed.

Lemma valid_curve_polygon_cp_hole_inside :
  forall (cp : CurvePolygon) (n : nat) (h : CurveRing),
    valid_curve_polygon_cp cp n -> In h (curve_holes cp) ->
    hole_inside_outer (chord_approx_ring (curve_outer cp) n) (chord_approx_ring h n).
Proof.
  intros cp n h [_ Hholes] Hin.
  unfold curve_polygon_holes_inside_shell in Hholes.
  rewrite Forall_forall in Hholes. exact (Hholes h Hin).
Qed.

(* The per-hole containment witness the POINT_IN_CURVE_RING oracle pins: every
   hole has a vertex of its densified ring that is inside the densified outer
   ring (i.e. point_in_curve_ring against the shell holds for that vertex). *)
Theorem valid_curve_polygon_cp_hole_witness :
  forall (cp : CurvePolygon) (n : nat) (h : CurveRing),
    valid_curve_polygon_cp cp n -> In h (curve_holes cp) ->
    exists p : Point,
      In p (chord_approx_ring h n) /\ point_in_inscribed_ring p (curve_outer cp) n.
Proof.
  intros cp n h Hv Hin.
  destruct (valid_curve_polygon_cp_hole_inside cp n h Hv Hin) as [p [Hp Hpir]].
  exists p. split; [ exact Hp | exact Hpir ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions valid_curve_polygon_cp_simple.
Print Assumptions valid_curve_polygon_cp_hole_witness.
