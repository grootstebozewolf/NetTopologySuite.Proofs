(* ============================================================================
   NetTopologySuite.Proofs.BufferDepthHorizontalEdgeCounterexample
   ----------------------------------------------------------------------------
   `depth_region`'s closed-boundary guard (#91) is necessary but NOT sufficient:
   a CLOSED kept boundary with a horizontal edge still misclassifies (RED+GREEN).

   `BufferDepthEnclosureCounterexample.v` (#91) showed `depth_region` needs the
   kept edges to form a CLOSED boundary.  This file shows that closure alone is
   not enough -- `depth_region` needs the SAME generic-position guards as
   `point_in_ring` (cf. the JCT parity seam, #86): a closed kept boundary with a
   horizontal edge at the ray height is misclassified.

   The witness reuses the merged #86 "notch" (a valid simple polygon with a
   horizontal edge at y = 1) as the kept boundary of a graph `G_notch`.  Because
   `edges_of (kept_edges G_notch) = ring_edges notch`, `depth_region G_notch`
   coincides with `point_in_ring (- ) notch`, so the #86 verdicts transfer
   verbatim:

     - `depth_region G_notch pext` is TRUE for the exterior point pext=(-1,1)
       (the ray runs along the horizontal kept edge (2,1)->(0,1)), yet
     - pext is in the UNBOUNDED component -- `~ geometric_interior_cont pext
       notch` -- so the kept boundary does not enclose it.

   So `depth_region` disagrees with the geometric interior for a CLOSED kept
   boundary, purely because of the horizontal edge.

   WHAT IS PROVED HERE (all Qed-closed, no `Admitted`/`Axiom`/`Parameter`):

     - `Gnotch_kept_is_notch`: the kept boundary of `G_notch` is `ring_edges
       notch` (a closed boundary -- so this is NOT the open-spur gap of #91).
     - `Gnotch_depth_is_point_in_ring`: `depth_region G_notch` = `point_in_ring
       ( ) notch`.
     - `depth_region_horizontal_refutes` (RED): `depth_region G_notch pext` is
       true while pext is not enclosed.
     - `depth_region_generic_guarded` + `Gnotch_excluded_by_no_horizontal_guard`
       (GREEN): a `depth_region` additionally guarded by `no_horizontal_edge_at`
       on its kept boundary excludes the witness vacuously.

   Together with #91: `depth_region` is a sound enclosure test only under
   BOTH a closed-boundary guard (#91) AND the generic-position guards
   (`no_horizontal_edge_at`, and -- by the same argument as #85 --
   `ray_avoids_vertices`).

   Pure-R; no atan / Flocq / `Classical_Prop.classic`.  No `Admitted`,
   no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import List.

From NTS.Proofs Require Import Distance.
From NTS.Proofs Require Import Overlay.
From NTS.Proofs Require Import OverlayGraph.
From NTS.Proofs Require Import BufferCorrectness.
From NTS.Proofs Require Import BufferDepth.
From NTS.Proofs Require Import PointInRingCorrect.
From NTS.Proofs Require Import PointInRingTangents.
From NTS.Proofs Require Import JordanCurveSeam.
From NTS.Proofs Require Import JCT_HorizontalEdgeCounterexample.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  A graph whose (closed) kept boundary is the #86 notch.                  *)
(* -------------------------------------------------------------------------- *)

(* A label kept by the depth rule: xor in_left in_right = xor true false. *)
Definition keep_lbl : EdgeLabel := {| in_left := true; in_right := false |}.

(* The kept edges, listed in the notch's consecutive-vertex order, so that
   `edges_of (kept_edges G_notch)` is exactly `ring_edges notch`. *)
Definition G_notch : TopologyGraph :=
  {| tg_vertices :=
       [mkPoint 0 0; mkPoint 4 0; mkPoint 4 2; mkPoint 2 2; mkPoint 2 1; mkPoint 0 1];
     tg_edges :=
       [ (mkPoint 0 0, mkPoint 4 0, keep_lbl);
         (mkPoint 4 0, mkPoint 4 2, keep_lbl);
         (mkPoint 4 2, mkPoint 2 2, keep_lbl);
         (mkPoint 2 2, mkPoint 2 1, keep_lbl);
         (mkPoint 2 1, mkPoint 0 1, keep_lbl);
         (mkPoint 0 1, mkPoint 0 0, keep_lbl) ] |}.

(* The kept boundary is the notch's closed edge loop. *)
Lemma Gnotch_kept_is_notch :
  edges_of (kept_edges G_notch) = ring_edges notch.
Proof. reflexivity. Qed.

Lemma Gnotch_depth_is_point_in_ring :
  forall p, depth_region G_notch p <-> point_in_ring p notch.
Proof.
  intro p. unfold depth_region, point_in_ring.
  rewrite Gnotch_kept_is_notch. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  RED: the closed kept boundary still misclassifies the exterior point.   *)
(* -------------------------------------------------------------------------- *)

Lemma Gnotch_depth_pext : depth_region G_notch pext.
Proof. apply Gnotch_depth_is_point_in_ring. exact notch_point_in_ring_pext. Qed.

(* `depth_region G_notch` calls pext "inside", but pext is in the unbounded
   component of the kept-boundary complement (the kept boundary is `ring_edges
   notch`, so its complement is the notch's complement) -- not enclosed. *)
Theorem depth_region_horizontal_refutes :
  depth_region G_notch pext /\ ~ geometric_interior_cont pext notch.
Proof.
  split; [ exact Gnotch_depth_pext | exact notch_pext_not_interior ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  GREEN: a no-horizontal-edge guard on the kept boundary excludes it.     *)
(* -------------------------------------------------------------------------- *)

(* A depth predicate additionally guarded by `no_horizontal_edge_at` on its
   kept boundary (mirroring the JCT parity seam's guard, #86).  Combined with
   the closure guard of #91 this is the generic-position strengthening
   `depth_region` needs to be a sound enclosure test. *)
Definition depth_region_generic_guarded
    (G : TopologyGraph) (r : Ring) (p : Point) : Prop :=
  edges_of (kept_edges G) = ring_edges r ->
  no_horizontal_edge_at p r ->
  depth_region G p.

(* GREEN.  The notch kept boundary HAS a horizontal edge ((2,1)->(0,1) at
   y = 1 = py pext), so `no_horizontal_edge_at pext notch` is false and the
   guarded predicate excludes the witness vacuously. *)
Theorem Gnotch_excluded_by_no_horizontal_guard :
  depth_region_generic_guarded G_notch notch pext.
Proof.
  intros _ Hnh. exfalso. exact (notch_violates_no_horizontal Hnh).
Qed.

(* RED and GREEN in one statement. *)
Theorem no_horizontal_guard_is_necessary_for_depth_region :
  (depth_region G_notch pext /\ ~ geometric_interior_cont pext notch)  (* RED   *)
  /\ depth_region_generic_guarded G_notch notch pext.                  (* GREEN *)
Proof.
  split.
  - exact depth_region_horizontal_refutes.
  - exact Gnotch_excluded_by_no_horizontal_guard.
Qed.
