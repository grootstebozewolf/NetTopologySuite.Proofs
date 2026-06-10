(* ============================================================================
   NetTopologySuite.Proofs.TriangleValidPolygon
   ----------------------------------------------------------------------------
   A concrete `Overlay.valid_polygon` WITH A HOLE, discharged UNCONDITIONALLY
   (no Jordan-curve hypothesis) -- the culmination of the arbitrary-triangle
   hole-nesting slice (GeneralTriangleHoleNesting.v).

   `valid_polygon` requires, for the outer ring and every hole, the four OGC
   conditions: `ring_closed`, `ring_simple`, `ring_has_minimum_points`, and (for
   holes) `hole_inside_outer`.  Three of these are combinatorial; the only
   analytic one -- `hole_inside_outer` -- is the polygonal-JCT residual that
   gated the general / with-holes case of `extract_rings_valid`.  For a
   triangular outer ring that residual is now UNCONDITIONAL
   (`hole_inside_outer_triangle`), so a triangle-with-triangular-hole polygon is
   fully `valid_polygon` with NO named hypothesis.

   Contributions:
   - `gtri_ring_simple`: a non-degenerate triangle ring (`cross A B C <> 0`) is
     `ring_simple` -- every edge pair shares a vertex, and two segments from a
     common vertex with nonzero cross never cross properly
     (`KakeyaOverlay.sip_shared_no_cross`).  The general `gtri_ring` analogue of
     `KakeyaOverlay.perron_tri_ring_simple`.
   - `triangle_with_hole_valid`: the polygon with outer triangle (0,0),(6,0),(0,6)
     and hole triangle (1,1),(3,1),(1,3) is `valid_polygon`, unconditionally.

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List.
From NTS.Proofs Require Import Distance Overlay Orientation.
From NTS.Proofs Require Import GeneralTriangleSeparation GeneralTriangleHoleNesting KakeyaOverlay.
Import ListNotations.

Local Open Scope R_scope.

(* A non-degenerate triangle ring is simple. *)
Theorem gtri_ring_simple : forall ax ay bx by_ cx cy,
  cross (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy) <> 0 ->
  ring_simple (gtri_ring ax ay bx by_ cx cy).
Proof.
  intros ax ay bx by_ cx cy Hcr.
  pose proof (cross_nonzero_perms (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy) Hcr)
    as [HABC [HBCA [HCAB [HACB [HCBA HBAC]]]]].
  intros e1 e2 H1 H2 Hne.
  rewrite ring_edges_gtri in H1, H2. cbn [In] in H1, H2.
  destruct H1 as [H1 | [H1 | [H1 | []]]]; destruct H2 as [H2 | [H2 | [H2 | []]]];
    subst e1 e2; cbn [fst snd];
    try (exfalso; apply Hne; reflexivity);
    intro Hsip;
    first
      [ refine (sip_shared_no_cross _ _ _ _ Hsip); assumption
      | apply sip_rev1 in Hsip;
        refine (sip_shared_no_cross _ _ _ _ Hsip); assumption
      | apply sip_rev2 in Hsip;
        refine (sip_shared_no_cross _ _ _ _ Hsip); assumption
      | apply sip_rev1 in Hsip; apply sip_rev2 in Hsip;
        refine (sip_shared_no_cross _ _ _ _ Hsip); assumption ].
Qed.

(* Cheap structural facts for a triangle ring. *)
Lemma gtri_ring_closed : forall ax ay bx by_ cx cy,
  ring_closed (gtri_ring ax ay bx by_ cx cy).
Proof.
  intros. exists (mkPoint ax ay), [ mkPoint bx by_ ; mkPoint cx cy ]. reflexivity.
Qed.

Lemma gtri_ring_min_points : forall ax ay bx by_ cx cy,
  ring_has_minimum_points (gtri_ring ax ay bx by_ cx cy).
Proof.
  intros. unfold ring_has_minimum_points, gtri_ring; cbn [length]; lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* The concrete with-holes polygon.                                            *)
(* -------------------------------------------------------------------------- *)

Definition tri_outer : Ring := gtri_ring 0 0 6 0 0 6.   (* (0,0),(6,0),(0,6) *)
Definition tri_hole  : Ring := gtri_ring 1 1 3 1 1 3.   (* (1,1),(3,1),(1,3) *)
Definition tri_poly  : Polygon := mkPolygon tri_outer [ tri_hole ].

Theorem triangle_with_hole_valid : valid_polygon tri_poly.
Proof.
  unfold valid_polygon, tri_poly; cbn [outer_ring hole_rings].
  split; [ apply gtri_ring_closed | ].
  split; [ apply gtri_ring_simple; unfold cross; cbn [px py]; intro Hc; nra | ].
  split; [ apply gtri_ring_min_points | ].
  intros h Hin. cbn [In] in Hin. destruct Hin as [Hh | []]; subst h.
  unfold tri_hole, tri_outer.
  split; [ apply gtri_ring_closed | ].
  split; [ apply gtri_ring_simple; unfold cross; cbn [px py]; intro Hc; nra | ].
  split; [ apply gtri_ring_min_points | ].
  (* hole_inside_outer: vertex (1,1) of the hole is inside the big triangle *)
  apply (hole_inside_outer_triangle 0 0 6 0 0 6 _ (mkPoint 1 1)).
  { unfold gtri_ring; apply in_eq. }
  { apply (proj2 (gtri_pos_iff 0 0 6 0 0 6 (mkPoint 1 1))).
    unfold gsA, gsB, gsC; cbn [px py]; repeat split; nra. }
  { (* py = 1 lies in the band 0 < py < 6 (the live band of (0,0),(6,0),(0,6)) *)
    right; left; cbn [px py]; split; lra. }
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions gtri_ring_simple.
Print Assumptions triangle_with_hole_valid.
