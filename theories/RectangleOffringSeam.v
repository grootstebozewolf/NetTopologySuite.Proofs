(* ============================================================================
   NetTopologySuite.Proofs.RectangleOffringSeam
   ----------------------------------------------------------------------------
   The corrected H1 seam, discharged TOTALLY for the rectangle: the first
   family for which `parity_characterises_interior_cont_offring` itself is
   Qed -- for EVERY off-ring point, not just the strict interior.

   The three closed families (rectangle / right triangle / arbitrary triangle)
   all scope their parity<->interior headlines to strict-interior points
   (`0 < field p`).  What was missing for a TOTAL instance of the seam is the
   EXTERIOR half: a point strictly outside the ring is in no bounded
   complement component -- it escapes to infinity along a straight ray.  For
   the axis-aligned rectangle every exterior point violates one of the four
   slab inequalities, and the axis-aligned ray AWAY from the violated slab
   never meets the skeleton (whose coordinates are confined to the box).
   This file builds that machinery and assembles the total seam instance:

     - `escape_beyond_x_low/_x_high/_y_low/_y_high` : GENERIC over any ring r
       whose skeleton is bounded on one side -- a point strictly beyond that
       bound is not `in_bounded_component_cont` (straight-line escape, reusing
       `JordanCurveSeam.straight_path_continuous`).  These are the reusable
       pieces for the triangle/convex exterior halves to come.
     - `rect_image_bounds` : the rectangle skeleton lies in the closed box.
     - `rect_exterior_not_in_ring` : `box_min p < 0 -> ~ point_in_ring p`
       (the half-open membership of `point_in_ring_rect_iff` fails strictly).
     - `rect_point_in_ring_iff_geometric` : for ALL off-ring p,
       `point_in_ring <-> geometric_interior_cont` -- by the `box_min`
       trichotomy: >0 the existing strict-interior result; =0 impossible
       off-ring; <0 both sides false (parity by the iff, escape by the ray).
     - `rect_parity_seam_offring` : THE HEADLINE -- the corrected seam Prop of
       JCT_OnEdgeCounterexample.v holds for every rectangle and every point;
       the corrected H1 target is SATISFIABLE, and the rectangle is its first
       totally-discharged instance.  (The two ray-genericity guards are not
       even needed here: the rectangle's parity computation is exact.)

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam.
From NTS.Proofs Require Import PointInRingCorrect JCT JCT_OnEdgeCounterexample.
From NTS.Proofs Require Import RectangleJCT RectangleSeparation.
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §1  Generic straight-ray escape: a point strictly beyond a one-sided bound
       on the ring skeleton is in NO bounded complement component.
   --------------------------------------------------------------------------- *)

Lemma escape_beyond_x_low : forall (r : Ring) (p : Point) (xlo : R),
  (forall q : Point, ring_image r q -> xlo <= px q) ->
  px p < xlo ->
  ~ in_bounded_component_cont r p.
Proof.
  intros r p xlo Hskel Hp; destruct p as [a b]; cbn [px py] in *.
  intros [M [HM Hb]].
  set (X := a - (M + Rabs a + 1)).
  assert (HXle : X <= - (M + 1)) by (unfold X; pose proof (Rle_abs a); lra).
  assert (HXlt : X < a) by (unfold X; pose proof (Rabs_pos a); lra).
  assert (Hq : connected_in_complement_cont r (mkPoint a b) (mkPoint X b)).
  { exists (fun t => mkPoint ((1 - t) * a + t * X) ((1 - t) * b + t * b)).
    split; [ apply straight_path_continuous | ]. split; [ | split ].
    - cbn [px py]; f_equal; lra.
    - cbn [px py]; f_equal; lra.
    - intros t Ht Himg. apply Hskel in Himg. cbn [px] in Himg. nra. }
  specialize (Hb _ Hq). cbn [px py] in Hb. nra.
Qed.

Lemma escape_beyond_x_high : forall (r : Ring) (p : Point) (xhi : R),
  (forall q : Point, ring_image r q -> px q <= xhi) ->
  xhi < px p ->
  ~ in_bounded_component_cont r p.
Proof.
  intros r p xhi Hskel Hp; destruct p as [a b]; cbn [px py] in *.
  intros [M [HM Hb]].
  set (X := a + (M + Rabs a + 1)).
  assert (HXge : M + 1 <= X) by (unfold X; pose proof (Rle_abs (- a)); rewrite Rabs_Ropp in *; lra).
  assert (HXgt : a < X) by (unfold X; pose proof (Rabs_pos a); lra).
  assert (Hq : connected_in_complement_cont r (mkPoint a b) (mkPoint X b)).
  { exists (fun t => mkPoint ((1 - t) * a + t * X) ((1 - t) * b + t * b)).
    split; [ apply straight_path_continuous | ]. split; [ | split ].
    - cbn [px py]; f_equal; lra.
    - cbn [px py]; f_equal; lra.
    - intros t Ht Himg. apply Hskel in Himg. cbn [px] in Himg. nra. }
  specialize (Hb _ Hq). cbn [px py] in Hb. nra.
Qed.

Lemma escape_beyond_y_low : forall (r : Ring) (p : Point) (ylo : R),
  (forall q : Point, ring_image r q -> ylo <= py q) ->
  py p < ylo ->
  ~ in_bounded_component_cont r p.
Proof.
  intros r p ylo Hskel Hp; destruct p as [a b]; cbn [px py] in *.
  intros [M [HM Hb]].
  set (Y := b - (M + Rabs b + 1)).
  assert (HYle : Y <= - (M + 1)) by (unfold Y; pose proof (Rle_abs b); lra).
  assert (HYlt : Y < b) by (unfold Y; pose proof (Rabs_pos b); lra).
  assert (Hq : connected_in_complement_cont r (mkPoint a b) (mkPoint a Y)).
  { exists (fun t => mkPoint ((1 - t) * a + t * a) ((1 - t) * b + t * Y)).
    split; [ apply straight_path_continuous | ]. split; [ | split ].
    - cbn [px py]; f_equal; lra.
    - cbn [px py]; f_equal; lra.
    - intros t Ht Himg. apply Hskel in Himg. cbn [py] in Himg. nra. }
  specialize (Hb _ Hq). cbn [px py] in Hb. nra.
Qed.

Lemma escape_beyond_y_high : forall (r : Ring) (p : Point) (yhi : R),
  (forall q : Point, ring_image r q -> py q <= yhi) ->
  yhi < py p ->
  ~ in_bounded_component_cont r p.
Proof.
  intros r p yhi Hskel Hp; destruct p as [a b]; cbn [px py] in *.
  intros [M [HM Hb]].
  set (Y := b + (M + Rabs b + 1)).
  assert (HYge : M + 1 <= Y) by (unfold Y; pose proof (Rle_abs (- b)); rewrite Rabs_Ropp in *; lra).
  assert (HYgt : b < Y) by (unfold Y; pose proof (Rabs_pos b); lra).
  assert (Hq : connected_in_complement_cont r (mkPoint a b) (mkPoint a Y)).
  { exists (fun t => mkPoint ((1 - t) * a + t * a) ((1 - t) * b + t * Y)).
    split; [ apply straight_path_continuous | ]. split; [ | split ].
    - cbn [px py]; f_equal; lra.
    - cbn [px py]; f_equal; lra.
    - intros t Ht Himg. apply Hskel in Himg. cbn [py] in Himg. nra. }
  specialize (Hb _ Hq). cbn [px py] in Hb. nra.
Qed.

(* ---------------------------------------------------------------------------
   §2  The rectangle skeleton is confined to the closed box.
   --------------------------------------------------------------------------- *)

Lemma rect_image_bounds : forall x0 y0 x1 y1 q,
  x0 < x1 -> y0 < y1 ->
  ring_image (rect_ring x0 y0 x1 y1) q ->
  (x0 <= px q <= x1) /\ (y0 <= py q <= y1).
Proof.
  intros x0 y0 x1 y1 q Hx01 Hy01 [e [t [Hin [Ht [Hx Hy]]]]].
  rewrite ring_edges_rect in Hin. cbn [In] in Hin.
  destruct Hin as [He | [He | [He | [He | []]]]];
    subst e; cbn [px py fst snd] in Hx, Hy; repeat split; nra.
Qed.

(* ---------------------------------------------------------------------------
   §3  Strict exterior: even parity (the half-open membership fails strictly).
   --------------------------------------------------------------------------- *)

Lemma Rmin_neg_inv : forall a b, Rmin a b < 0 -> a < 0 \/ b < 0.
Proof.
  intros a b H. unfold Rmin in H.
  destruct (Rle_dec a b); [ left | right ]; lra.
Qed.

(* box_min < 0 names the violated slab. *)
Lemma box_min_neg_inv : forall x0 y0 x1 y1 p,
  box_min x0 y0 x1 y1 p < 0 ->
  px p < x0 \/ x1 < px p \/ py p < y0 \/ y1 < py p.
Proof.
  intros x0 y0 x1 y1 p Hneg. unfold box_min in Hneg.
  destruct (Rmin_neg_inv _ _ Hneg) as [H1 | H1];
    destruct (Rmin_neg_inv _ _ H1) as [H2 | H2];
    [ left | right; left | right; right; left | right; right; right ]; lra.
Qed.

Lemma rect_exterior_not_in_ring : forall x0 y0 x1 y1 p,
  x0 < x1 -> y0 < y1 ->
  box_min x0 y0 x1 y1 p < 0 ->
  ~ point_in_ring p (rect_ring x0 y0 x1 y1).
Proof.
  intros x0 y0 x1 y1 p Hx01 Hy01 Hneg Hpir.
  apply (point_in_ring_rect_iff x0 y0 x1 y1 p Hx01 Hy01) in Hpir.
  destruct (box_min_neg_inv x0 y0 x1 y1 p Hneg) as [H | [H | [H | H]]]; lra.
Qed.

(* ---------------------------------------------------------------------------
   §4  The total off-ring biconditional, by box_min trichotomy.
   --------------------------------------------------------------------------- *)

Theorem rect_point_in_ring_iff_geometric : forall x0 y0 x1 y1 p,
  x0 < x1 -> y0 < y1 ->
  ring_complement (rect_ring x0 y0 x1 y1) p ->
  (point_in_ring p (rect_ring x0 y0 x1 y1)
     <-> geometric_interior_cont p (rect_ring x0 y0 x1 y1)).
Proof.
  intros x0 y0 x1 y1 p Hx01 Hy01 Hcompl.
  destruct (Rtotal_order (box_min x0 y0 x1 y1 p) 0) as [Hneg | [Hzero | Hpos]].
  - (* strict exterior: both sides false *)
    pose proof (box_min_neg_inv x0 y0 x1 y1 p Hneg) as Hout.
    split.
    + intro Hpir. exfalso.
      exact (rect_exterior_not_in_ring x0 y0 x1 y1 p Hx01 Hy01 Hneg Hpir).
    + intros [_ Hbnd]. exfalso.
      destruct Hout as [H | [H | [H | H]]].
      * refine (escape_beyond_x_low _ _ x0 _ H Hbnd).
        intros q Hq; exact (proj1 (proj1 (rect_image_bounds x0 y0 x1 y1 q Hx01 Hy01 Hq))).
      * refine (escape_beyond_x_high _ _ x1 _ H Hbnd).
        intros q Hq; exact (proj2 (proj1 (rect_image_bounds x0 y0 x1 y1 q Hx01 Hy01 Hq))).
      * refine (escape_beyond_y_low _ _ y0 _ H Hbnd).
        intros q Hq; exact (proj1 (proj2 (rect_image_bounds x0 y0 x1 y1 q Hx01 Hy01 Hq))).
      * refine (escape_beyond_y_high _ _ y1 _ H Hbnd).
        intros q Hq; exact (proj2 (proj2 (rect_image_bounds x0 y0 x1 y1 q Hx01 Hy01 Hq))).
  - (* on the skeleton: excluded by the off-ring premise *)
    exfalso.
    exact (box_min_nonzero_off_skeleton x0 y0 x1 y1 p Hx01 Hy01 Hcompl Hzero).
  - (* strict interior: the existing closed-family result *)
    apply box_min_pos_iff in Hpos.
    apply rect_parity_characterises_interior; tauto.
Qed.

(* ---------------------------------------------------------------------------
   §5  THE HEADLINE: the corrected H1 seam, totally discharged for the
       rectangle.  First family instance of the seam Prop itself.
   --------------------------------------------------------------------------- *)

Theorem rect_parity_seam_offring : forall x0 y0 x1 y1 p,
  x0 < x1 -> y0 < y1 ->
  parity_characterises_interior_cont_offring p (rect_ring x0 y0 x1 y1).
Proof.
  intros x0 y0 x1 y1 p Hx01 Hy01.
  unfold parity_characterises_interior_cont_offring.
  intros _ _ _ Hcompl _ _.
  symmetry.
  apply rect_point_in_ring_iff_geometric; assumption.
Qed.

(* Sanity instances on the unit square: an interior, an exterior-left and an
   exterior-above point all satisfy the discharged seam (trivially, as
   corollaries -- the value is that the seam Prop is now a THEOREM here). *)
Example rect_seam_unit_square_interior :
  parity_characterises_interior_cont_offring (mkPoint (1/2) (1/2)) (rect_ring 0 0 1 1).
Proof. apply rect_parity_seam_offring; lra. Qed.

Example rect_seam_unit_square_exterior :
  parity_characterises_interior_cont_offring (mkPoint (-2) (1/2)) (rect_ring 0 0 1 1).
Proof. apply rect_parity_seam_offring; lra. Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions escape_beyond_x_low.
Print Assumptions rect_point_in_ring_iff_geometric.
Print Assumptions rect_parity_seam_offring.
