(* ============================================================================
   NetTopologySuite.Proofs.GeneralTriangleParity
   ----------------------------------------------------------------------------
   Special-case JCT: foundation for the ray-parity half of an arbitrary triangle.

   The companion `GeneralTriangleSeparation.v` discharged the bounded-component
   (geometric-interior) half for an arbitrary CCW triangle.  This file builds
   the reusable foundation for the ray-parity half: a clean characterisation of
   when a polygon edge crosses the rightward horizontal ray, with the
   division-by-edge-height cleared once and the crossing expressed via the
   edge's SIGNED AREA (the same cross product that defines the triangle's
   inward slacks).

   `edge_cross_sign`:
     edge (V,W) crosses the ray from p  <->
       (vy < py p < wy  /\  0 < cross(W-V, p-V))      (* upward edge, p to its left *)
    \/ (wy < py p < vy  /\  cross(W-V, p-V) < 0)       (* downward edge, p to its left *)

   so an edge crosses iff p's height is strictly between the edge's endpoints
   AND p lies on the interior side of the edge line (matching the edge's
   up/down orientation).  This is the bridge between `Overlay.edge_crosses_ray`
   (a division formula) and the signed-area slacks `gsA/gsB/gsC`, and is what
   the full parity assembly (a case analysis over the vertices' height ordering)
   will consume.

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (claude-opus-4-8)
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam GeneralTriangleSeparation.
Import ListNotations.

Local Open Scope R_scope.
(* Part of the special-case JCT programme (issue #65): rectangle -> right
   triangle -> arbitrary triangle, plus the hat & Spectre monotile showcases. *)

(* Clearing the linear-interpolation division: a < N/d  <->  0 < N - a*d. *)
Lemma lt_div_iff : forall a N d, 0 < d -> (a < N / d <-> 0 < N - a * d).
Proof.
  intros a N d Hd. split; intro H.
  - assert (Hq : a * d < N / d * d) by (apply Rmult_lt_compat_r; lra).
    replace (N / d * d) with N in Hq by (field; lra). lra.
  - apply (Rmult_lt_reg_r d); [ lra | ].
    replace (N / d * d) with N by (field; lra). lra.
Qed.

(* The edge-crossing characterisation via the signed area of the edge.         *)
Lemma edge_cross_sign : forall vx vy wx wy (p : Point),
  edge_crosses_ray p (mkPoint vx vy, mkPoint wx wy) <->
    ( (vy < py p < wy /\ 0 < (wx - vx) * (py p - vy) - (wy - vy) * (px p - vx))
   \/ (wy < py p < vy /\ (wx - vx) * (py p - vy) - (wy - vy) * (px p - vx) < 0) ).
Proof.
  intros vx vy wx wy p. unfold edge_crosses_ray; cbn [px py fst snd]. split.
  - intros [[Hy Hx] | [Hy Hx]].
    + (* vy < py < wy : wy - vy > 0 *)
      left. split; [ exact Hy | ].
      assert (Hd : 0 < wy - vy) by lra.
      pose proof (proj1 (lt_div_iff (px p - vx) ((wx - vx) * (py p - vy)) (wy - vy) Hd)) as Himp.
      assert (Hx' : px p - vx < (wx - vx) * (py p - vy) / (wy - vy)).
      { apply (Rplus_lt_reg_l vx). replace (vx + (px p - vx)) with (px p) by ring.
        replace (vx + (wx - vx) * (py p - vy) / (wy - vy))
          with (vx + (wx - vx) * (py p - vy) / (wy - vy)) by ring.
        exact Hx. }
      pose proof (Himp Hx') as Hs. lra.
    + (* wy < py < vy : vy - wy > 0 *)
      right. split; [ exact Hy | ].
      assert (Hd : 0 < vy - wy) by lra.
      assert (Hx' : px p - wx < (vx - wx) * (py p - wy) / (vy - wy)).
      { apply (Rplus_lt_reg_l wx). replace (wx + (px p - wx)) with (px p) by ring.
        exact Hx. }
      pose proof (proj1 (lt_div_iff (px p - wx) ((vx - wx) * (py p - wy)) (vy - wy) Hd) Hx') as Hs.
      nra.
  - intros [[Hy Hs] | [Hy Hs]].
    + left. split; [ exact Hy | ].
      assert (Hd : 0 < wy - vy) by lra.
      assert (Hx' : px p - vx < (wx - vx) * (py p - vy) / (wy - vy))
        by (apply (lt_div_iff (px p - vx) ((wx - vx) * (py p - vy)) (wy - vy) Hd); lra).
      apply (Rplus_lt_reg_l (- vx)).
      replace (- vx + px p) with (px p - vx) by ring.
      replace (- vx + (vx + (wx - vx) * (py p - vy) / (wy - vy)))
        with ((wx - vx) * (py p - vy) / (wy - vy)) by ring.
      exact Hx'.
    + right. split; [ exact Hy | ].
      assert (Hd : 0 < vy - wy) by lra.
      assert (Hx' : px p - wx < (vx - wx) * (py p - wy) / (vy - wy))
        by (apply (lt_div_iff (px p - wx) ((vx - wx) * (py p - wy)) (vy - wy) Hd); nra).
      apply (Rplus_lt_reg_l (- wx)).
      replace (- wx + px p) with (px p - wx) by ring.
      replace (- wx + (wx + (vx - wx) * (py p - wy) / (vy - wy)))
        with ((vx - wx) * (py p - wy) / (vy - wy)) by ring.
      exact Hx'.
Qed.

(* -------------------------------------------------------------------------- *)
(* The single minimal hypothesis for the arbitrary-triangle parity, and the     *)
(* conditional headline it unlocks.                                            *)
(*                                                                            *)
(* Rather than discharge the full ray-parity case analysis in one shot, we      *)
(* isolate the one irreducible geometric fact as a named Prop: the rightward-    *)
(* ray parity test decides EXACTLY the algebraic interior (all three inward      *)
(* signed areas positive).  This is the genuine Jordan "ray-parity = inside"     *)
(* content -- everything mechanical is already in place: `edge_cross_sign`       *)
(* reduces each edge crossing to a slack sign, and `GeneralTriangleSeparation`   *)
(* already turns the algebraic interior into the geometric one.  Discharging     *)
(* `gtri_parity_spec` (the vertex height-ordering case analysis, under the       *)
(* `ray_avoids_vertices` / `no_horizontal_edge_at` guards) is the remaining,     *)
(* multi-step work.                                                            *)
(* -------------------------------------------------------------------------- *)

Section TriangleParitySpec.

Variables ax ay bx by_ cx cy : R.
Hypothesis Hccw : 0 < gdbl ax ay bx by_ cx cy.

(* Minimal hypothesis (one universally-quantified biconditional). *)
Definition gtri_parity_spec : Prop :=
  forall p : Point,
    point_in_ring p (gtri_ring ax ay bx by_ cx cy)
      <-> 0 < gtri ax ay bx by_ cx cy p.

(* Conditional headline: under the parity spec, the ray-parity test's "inside"
   verdict is a genuine geometric-interior point (the spec composed with the
   separation result, GeneralTriangleSeparation.gtri_interior_is_geometric). *)
Theorem gtri_in_ring_imp_geometric :
  gtri_parity_spec ->
  forall p,
    point_in_ring p (gtri_ring ax ay bx by_ cx cy) ->
    geometric_interior_cont p (gtri_ring ax ay bx by_ cx cy).
Proof.
  intros Hspec p Hpir.
  apply (gtri_interior_is_geometric ax ay bx by_ cx cy Hccw).
  apply (proj1 (Hspec p)). exact Hpir.
Qed.

End TriangleParitySpec.

(* -------------------------------------------------------------------------- *)
(* RED non-vacuity check on the engine.                                        *)
(*                                                                            *)
(* The corpus's prior interior predicate `geometric_interior_stdlib` was       *)
(* refuted as VACUOUSLY FALSE (`JordanCurveSeam.geometric_interior_stdlib_      *)
(* vacuous`).  Before investing in discharging `gtri_parity_spec` we confirm    *)
(* the continuous predicate the separation engine produces is genuinely         *)
(* INHABITED: a concrete CCW triangle A=(0,0), B=(4,0), C=(0,4) and its         *)
(* centroid (4/3,4/3) -- with 0 < gtri there -- yields a real                  *)
(* `geometric_interior_cont` point via the engine.  So the engine is not       *)
(* vacuous and is genuinely load-bearing for the conditional headline.         *)
(* -------------------------------------------------------------------------- *)

Example engine_produces_inhabited_interior :
  geometric_interior_cont (mkPoint (4 / 3) (4 / 3)) (gtri_ring 0 0 4 0 0 4).
Proof.
  apply (gtri_interior_is_geometric 0 0 4 0 0 4).
  - unfold gdbl; lra.
  - apply (proj2 (gtri_pos_iff 0 0 4 0 0 4 (mkPoint (4 / 3) (4 / 3)))).
    unfold gsA, gsB, gsC; cbn [px py]; repeat split; lra.
Qed.

(* And the engine's output is a strict refinement of "off the skeleton": the
   centroid is in the ring complement too (sanity: the interior witness is a
   genuine off-edge point, not a boundary artefact). *)
Example centroid_in_complement :
  ring_complement (gtri_ring 0 0 4 0 0 4) (mkPoint (4 / 3) (4 / 3)).
Proof.
  apply (gtri_interior_complement 0 0 4 0 0 4).
  apply (proj2 (gtri_pos_iff 0 0 4 0 0 4 (mkPoint (4 / 3) (4 / 3)))).
  unfold gsA, gsB, gsC; cbn [px py]; repeat split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions edge_cross_sign.
Print Assumptions gtri_in_ring_imp_geometric.
Print Assumptions engine_produces_inhabited_interior.
