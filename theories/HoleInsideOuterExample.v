(* ============================================================================
   NetTopologySuite.Proofs.HoleInsideOuterExample
   ----------------------------------------------------------------------------
   extract_rings_valid R5 / general assembler: a CONCRETE, unconditional witness
   that the analytic predicate `hole_inside_outer` is reachable
   (docs/extract-rings-proof-structure.md §4; docs/hole-inside-outer.md).

   `hole_inside_outer outer hole := exists p, In p hole /\ point_in_ring p outer`,
   and `point_in_ring p r := ray_parity_odd p (ring_edges r)` -- the (inductive,
   real-arithmetic) crossing-parity predicate of `Overlay`.  The GENERAL
   discharge of `hole_inside_outer` for arbitrary extracted faces is the
   registered JCT / H1 analytic residual (parity <-> geometric interior), and is
   NOT attempted here -- the corpus already carries the conditional bridge
   `PointInRingTangents.point_in_ring_correct_jct` (Qed, with the JCT step as a
   named hypothesis), and slice 3f (`FacePolygonHoles.face_polygon_holes_valid`)
   already takes `hole_inside_outer` as its sole remaining hypothesis.

   This file instead pins down a CONCRETE instance, fully unconditional and
   axiom-disciplined: a square `outer` ring and a smaller square `hole` strictly
   inside it, with `hole_inside_outer outer hole` proved by walking the
   `ray_parity_odd` constructors and discharging each `edge_crosses_ray`
   real-inequality by `lra`.  It is a regression anchor (the predicate is
   satisfiable / the parity definition behaves) and the concrete seed the general
   JCT generalises -- nothing more is claimed.

   Pure `R`; no `Admitted` / `Axiom` / `Parameter`.  Standard three-axiom
   classical-reals base.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List Lra.
From NTS.Proofs Require Import Distance Overlay.

Import ListNotations.
Open Scope R_scope.

(* A 4x4 axis-aligned square (closed ring), and its centre point. *)
Definition o00 : Point := mkPoint 0 0.
Definition o40 : Point := mkPoint 4 0.
Definition o44 : Point := mkPoint 4 4.
Definition o04 : Point := mkPoint 0 4.
Definition outer_sq : Ring := [o00; o40; o44; o04; o00].
Definition ctr : Point := mkPoint 2 2.

(* Helper: the term (px b - px a) * (...) / (py b - py a) collapses to 0 when the
   edge is vertical (px a = px b), keeping `lra` clear of division. *)
Lemma vert_intercept_zero : forall t d, (4 - 4) * t / d = 0.
Proof. intros t d. replace (4 - 4) with 0 by lra. rewrite Rmult_0_l. unfold Rdiv. apply Rmult_0_l. Qed.

Lemma left_intercept_zero : forall t d, (0 - 0) * t / d = 0.
Proof. intros t d. replace (0 - 0) with 0 by lra. rewrite Rmult_0_l. unfold Rdiv. apply Rmult_0_l. Qed.

(* The centre of the square has odd ray-parity against the square's edges: the
   rightward ray from (2,2) crosses exactly the right edge.  Hence it is
   `point_in_ring`. *)
Lemma ctr_in_outer : point_in_ring ctr outer_sq.
Proof.
  unfold point_in_ring, outer_sq, ctr. cbn [ring_edges].
  (* bottom edge (0,0)-(4,0): horizontal, not crossed *)
  apply rpo_skip.
  { unfold edge_crosses_ray, o00, o40. cbn [px py]. intros [[H _] | [H _]]; lra. }
  (* right edge (4,0)-(4,4): crossed *)
  apply rpo_cross.
  { unfold edge_crosses_ray, o40, o44. cbn [px py]. left. split.
    - lra.
    - rewrite vert_intercept_zero. lra. }
  (* top edge (4,4)-(0,4): horizontal, not crossed *)
  apply rpe_skip.
  { unfold edge_crosses_ray, o44, o04. cbn [px py]. intros [[H _] | [H _]]; lra. }
  (* left edge (0,4)-(0,0): vertical at x=0, ray going right does not reach it *)
  apply rpe_skip.
  { unfold edge_crosses_ray, o04, o00. cbn [px py]. intros [[H _] | [_ Hx]].
    - lra.
    - revert Hx. rewrite left_intercept_zero. lra. }
  apply rpe_nil.
Qed.

(* A smaller square hole, sharing the centre as a vertex. *)
Definition h22 : Point := mkPoint 2 2.
Definition h32 : Point := mkPoint 3 2.
Definition h33 : Point := mkPoint 3 3.
Definition h23 : Point := mkPoint 2 3.
Definition hole_sq : Ring := [h22; h32; h33; h23; h22].

(* The concrete witness: a square hole lies inside the square outer ring.

   This is the hole-bearing instance of the `extract_rings_valid` headline: that
   theorem requires every extracted polygon to be `valid_polygon`, whose last
   conjunct is `hole_inside_outer` for each hole.  Slice 3f
   (`FacePolygonHoles.face_polygon_holes_valid`) discharges all the OTHER
   conjuncts by construction and takes exactly this predicate as its sole
   hypothesis; here we exhibit it concretely.  The general (any-face) discharge
   is the registered JCT residual -- and `docs/hole-inside-outer-plan.md` lays out
   the route that turns this fixed-square witness into an UNCONDITIONAL theorem
   for all rectangles (via `RectangleSeparation.rect_confines_of_interior`). *)
Theorem hole_inside_outer_example : hole_inside_outer outer_sq hole_sq.
Proof.
  exists ctr. split.
  - unfold hole_sq, ctr, h22. cbn [In]. left. reflexivity.
  - exact ctr_in_outer.
Qed.
