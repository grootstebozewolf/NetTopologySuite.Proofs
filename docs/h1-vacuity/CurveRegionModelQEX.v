(* ============================================================================
   docs/h1-vacuity/CurveRegionModelQEX.v  --  hunt probe (QEX), not a product module
   ----------------------------------------------------------------------------
   The first `curve_region` of ArcOverlayRegion.v was a global model: the
   chord geometry's point set, flipped by parity over the FULL circular
   segment of every arc of the geometry.  Its stated side condition was
   "segments pairwise disjoint, each wholly inside or outside the chord
   polygon".  Two findings:

   1. Validity does not give that condition.  `valid_curve_geometry` checks
      arcs non-degenerate and rings connected and closed -- no simplicity, no
      polygon disjointness.  `qgeom ++ qgeom` is valid and its two arc entries
      share their whole segment (`validity_allows_overlapping_segments`).

   2. The old model is wrong even on ONE valid simple polygon.  The chord
      approximation runs S -> M -> E through the arc midpoint, so the triangle
      S M E is already in the chord polygon; flipping the whole segment flips
      that triangle OUT.  At (1, -1/2), inside the bulge of qgeom's corner arc
      and inside triangle S M E, the old model says "outside"
      (`old_model_wrong_in_triangle`); the corrected per-ring model, which
      flips only segment-minus-triangle, says "inside"
      (`new_model_right_in_triangle`).

   The corrected model (ArcOverlayRegion.v §2) is per ring / per polygon /
   union, so it needs no disjointness at all.

   SUMMARY: bug — old curve_region model refuted on a valid input; condition not implied by validity (Qed).
   AI assistance disclosure: AI-drafted; human review pending.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay CurveGeometry ArcOrient
  ArcIntersect ArcHotPixel ArcChordApprox ArcDistance ArcOverlay
  ArcControlTriangleInSegment ArcOverlayRegion.
From NTS.Proofs.Probes Require Import ArcOverlayBridgeQEX.
Import ListNotations.
Local Open Scope R_scope.

Definition tpt : Point := mkPoint 1 (-1/2).

(* -------------------------------------------------------------------------- *)
(* §1  Validity does not give disjoint segments.                              *)
(* -------------------------------------------------------------------------- *)

Lemma tpt_in_segment : in_circular_segment qa tpt.
Proof.
  split.
  - unfold arc_interior_side, arc_side_chord, cross_R_pt, qa, tpt. cbn. lra.
  - unfold dist_sq, arc_center, qa, tpt. cbn. field_simplify; lra.
Qed.

Theorem validity_allows_overlapping_segments :
  valid_curve_geometry (qgeom ++ qgeom) /\
  arcs_of (qgeom ++ qgeom) = [qa; qa] /\
  in_circular_segment qa tpt.
Proof.
  split; [| split].
  - unfold valid_curve_geometry. apply Forall_app.
    split; exact arc_bridge_witness_valid.
  - reflexivity.
  - exact tpt_in_segment.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The old global model is wrong inside triangle S M E.                   *)
(* -------------------------------------------------------------------------- *)

Inductive old_odd (p : Point) : list CircularArc -> Prop :=
| oo_in : forall a l,
    in_circular_segment a p -> old_even p l -> old_odd p (a :: l)
| oo_out : forall a l,
    ~ in_circular_segment a p -> old_odd p l -> old_odd p (a :: l)
with old_even (p : Point) : list CircularArc -> Prop :=
| oe_nil : old_even p []
| oe_in : forall a l,
    in_circular_segment a p -> old_odd p l -> old_even p (a :: l)
| oe_out : forall a l,
    ~ in_circular_segment a p -> old_even p l -> old_even p (a :: l).

Definition old_curve_region (A : CurveGeometry) (n : nat) (p : Point) : Prop :=
  (point_set (to_geometry A n) p /\ old_even p (arcs_of A)) \/
  (~ point_set (to_geometry A n) p /\ old_odd p (arcs_of A)).

Ltac no_cross :=
  unfold edge_crosses_ray; cbn [px py fst snd];
  intros [[H1 H2] | [H1 H2]];
  [ try lra | try lra ];
  unfold Rdiv in H2;
  first
    [ match type of H2 with
      | context [ (?u - ?u) * ?w ] =>
          replace ((u - u) * w) with 0 in H2 by ring; lra
      end
    | field_simplify in H2; lra ].

Lemma tpt_in_chord_ring : forall n,
  point_in_ring tpt (chord_approx_ring qring n).
Proof.
  intro n.
  unfold point_in_ring, tpt, qring, qa.
  cbn [chord_approx_ring flat_map chord_approx_segment chord_approx_arc
       arc_start arc_mid arc_end app ring_edges].
  apply rpo_skip; [ no_cross |].   (* (0,0)   -> (1,-1): crosses at x = 1/2 < 1 *)
  apply rpo_cross.                 (* (1,-1)  -> (2,0): crosses at x = 3/2 *)
  { unfold edge_crosses_ray. cbn [px py fst snd]. left. split; [lra|].
    replace (1 + (2 - 1) * (-1/2 - -1) / (0 - -1)) with (3/2) by field. lra. }
  apply rpe_skip; [ no_cross |].
  apply rpe_skip; [ no_cross |].
  apply rpe_skip; [ no_cross |].
  apply rpe_skip; [ no_cross |].
  apply rpe_skip; [ no_cross |].
  apply rpe_skip; [ no_cross |].
  apply rpe_skip; [ no_cross |].
  apply rpe_skip; [ no_cross |].
  apply rpe_nil.
Qed.

Lemma tpt_in_point_set : forall n, point_set (to_geometry qgeom n) tpt.
Proof.
  intro n. exists (mkPolygon (chord_approx_ring qring n) []).
  split; [ left; reflexivity |].
  split; [ exact (tpt_in_chord_ring n) | intros h [] ].
Qed.

Theorem old_model_wrong_in_triangle : forall n,
  point_set (to_geometry qgeom n) tpt /\
  in_circular_segment qa tpt /\
  ~ old_curve_region qgeom n tpt.
Proof.
  intro n. split; [ exact (tpt_in_point_set n) |].
  split; [ exact tpt_in_segment |].
  unfold old_curve_region.
  replace (arcs_of qgeom) with [qa] by reflexivity.
  intros [[_ He] | [Hn _]].
  - inversion He as [| a l Hs Ho | a l Hs Hr]; subst.
    + inversion Ho.
    + exact (Hs tpt_in_segment).
  - exact (Hn (tpt_in_point_set n)).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The corrected per-ring model gets it right.                            *)
(* -------------------------------------------------------------------------- *)

Lemma tpt_in_triangle : point_in_ring tpt (arc_triangle qa).
Proof.
  unfold point_in_ring, arc_triangle, tpt, qa.
  cbn [arc_start arc_mid arc_end ring_edges].
  apply rpo_skip; [ no_cross |].   (* (0,0) -> (1,-1) *)
  apply rpo_cross.                 (* (1,-1) -> (2,0) *)
  { unfold edge_crosses_ray. cbn [px py fst snd]. left. split; [lra|].
    replace (1 + (2 - 1) * (-1/2 - -1) / (0 - -1)) with (3/2) by field. lra. }
  apply rpe_skip; [ no_cross |].   (* (2,0) -> (0,0) *)
  apply rpe_nil.
Qed.

Theorem new_model_right_in_triangle : forall n,
  curve_region qgeom n tpt /\ curve_region (qgeom ++ qgeom) n tpt.
Proof.
  intro n.
  assert (Hreg : polygon_region (mkCurvePolygon qring []) n tpt).
  { split; [| intros h []].
    left. split; [ exact (tpt_in_chord_ring n) |].
    replace (arcs_of_ring qring) with [qa] by reflexivity.
    apply se_out; [| constructor].
    intros [_ Hnot]. exact (Hnot tpt_in_triangle). }
  split; exists (mkCurvePolygon qring []); split; try exact Hreg;
    left; reflexivity.
Qed.

Print Assumptions old_model_wrong_in_triangle.
Print Assumptions new_model_right_in_triangle.
