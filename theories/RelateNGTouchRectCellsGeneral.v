(* ============================================================================
   NetTopologySuite.Proofs.RelateNGTouchRectCellsGeneral
   ----------------------------------------------------------------------------
   NTS: NetTopologySuite.Operation.Relate.RelateNG
   JTS: org.locationtech.jts.operation.relateng.RelateNG
        (IntersectionMatrix, axis-aligned rectangle touch)
   claimId: 0003-touch-rect-cells-general

   Issue #847 / ADR-0003 specification tier (open interior).

   Forall-quantified IB/BI/IE/EI/BE/EB cells of a vertical or horizontal
   shared-edge rectangle touch.  II and EE stay the cell_ok facts in
   RelateNGRect (touch_rect_pair_ii_cell, touch_rect_pair_ee_cell).  BB's
   geometric cell_ok is the separate vertical-touch target (#848); this
   module does not remint rect_pair_fill / aa_matrix_touch_vertical.

   IB, IE, EI, BE, EB are interval arithmetic on point_set and
   geom_boundary.  BI is NOT stated against point_set: the shared edge
   sits in B's half-open parity region (point_in_ring_rect_iff) and in
   A's boundary, so that cell is inhabited.  BI is empty against
   rect_interior (the open box), the rect analogue of tri_interior.

   No ring_complement / ray_avoids_vertices guard.

   WITNESS topic: relate · claimId: 0003-touch-rect-cells-general
   witness: 0003-touch-rect-cells-general
   board: ADR-0003
   issue: #847 (parent map #822; classification #824, not reopened)

   No Axiom, no Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Segment Overlay RectangleJCT
  RelateAreaPoint RelateAreaArea RelateCurveMatrix.

Import ListNotations.
Local Open Scope R_scope.

(* Same cell-dimension predicates as RelateNGTouchEdgeCellsGeneral. *)
Definition rect_cell_empty (P : Point -> Prop) : Prop :=
  forall p, ~ P p.

Definition rect_cell_dim1 (P : Point -> Prop) : Prop :=
  exists q r, P q /\ P r /\ q <> r.

Definition rect_cell_dim2 (P : Point -> Prop) : Prop :=
  exists c rad, 0 < rad /\ forall q, dist c q < rad -> P q.

(* Open box.  Same predicate as point_strictly_in_open_rect; named here
   as the rect analogue of tri_interior.  Pure interval arithmetic. *)
Definition rect_interior (x0 y0 x1 y1 : R) (p : Point) : Prop :=
  x0 < px p < x1 /\ y0 < py p < y1.

Lemma rect_interior_iff_open_rect :
  forall x0 y0 x1 y1 p,
    rect_interior x0 y0 x1 y1 p <->
    point_strictly_in_open_rect x0 y0 x1 y1 p.
Proof.
  intros x0 y0 x1 y1 p.
  unfold rect_interior, point_strictly_in_open_rect. tauto.
Qed.

Definition rect_center (x0 y0 x1 y1 : R) : Point :=
  mkPoint ((x0 + x1) / 2) ((y0 + y1) / 2).

Definition rect_inradius (x0 y0 x1 y1 : R) : R :=
  Rmin ((x1 - x0) / 2) ((y1 - y0) / 2).

Lemma rect_inradius_pos :
  forall x0 y0 x1 y1,
    x0 < x1 -> y0 < y1 -> 0 < rect_inradius x0 y0 x1 y1.
Proof.
  intros x0 y0 x1 y1 Hx Hy.
  unfold rect_inradius, Rmin.
  destruct (Rle_dec ((x1 - x0) / 2) ((y1 - y0) / 2)); lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Coordinate bounds: half-open point_set, closed-box geom_boundary.          *)
(* -------------------------------------------------------------------------- *)

Lemma rect_point_set_half_open :
  forall x0 y0 x1 y1 p,
    x0 < x1 -> y0 < y1 ->
    point_set (rect_geometry x0 y0 x1 y1) p ->
    y0 < py p < y1 /\ x0 <= px p < x1.
Proof.
  intros x0 y0 x1 y1 p Hx Hy Hin.
  destruct Hin as [poly [Hpoly Hpin]].
  unfold rect_geometry in Hpoly. simpl in Hpoly.
  destruct Hpoly as [Heq | []]. subst poly.
  apply rect_polygon_no_holes in Hpin.
  apply (point_in_ring_rect_iff x0 y0 x1 y1 p Hx Hy) in Hpin.
  exact Hpin.
Qed.

Lemma rect_interior_point_set :
  forall x0 y0 x1 y1 p,
    x0 < x1 -> y0 < y1 ->
    rect_interior x0 y0 x1 y1 p ->
    point_set (rect_geometry x0 y0 x1 y1) p.
Proof.
  intros x0 y0 x1 y1 p Hx Hy Hi.
  apply strict_interior_in_rect_geometry; [ exact Hx | exact Hy | ].
  apply rect_interior_iff_open_rect. exact Hi.
Qed.

Lemma rect_px_lt_lo_exterior :
  forall x0 y0 x1 y1 p,
    x0 < x1 -> y0 < y1 -> px p < x0 ->
    ~ point_set (rect_geometry x0 y0 x1 y1) p.
Proof.
  intros x0 y0 x1 y1 p Hx Hy Hlt Hin.
  apply rect_point_set_half_open in Hin; try assumption. lra.
Qed.

Lemma rect_px_ge_hi_exterior :
  forall x0 y0 x1 y1 p,
    x0 < x1 -> y0 < y1 -> x1 <= px p ->
    ~ point_set (rect_geometry x0 y0 x1 y1) p.
Proof.
  intros x0 y0 x1 y1 p Hx Hy Hge Hin.
  apply rect_point_set_half_open in Hin; try assumption. lra.
Qed.

Lemma rect_py_lt_lo_exterior :
  forall x0 y0 x1 y1 p,
    x0 < x1 -> y0 < y1 -> py p < y0 ->
    ~ point_set (rect_geometry x0 y0 x1 y1) p.
Proof.
  intros x0 y0 x1 y1 p Hx Hy Hlt Hin.
  apply rect_point_set_half_open in Hin; try assumption. lra.
Qed.

Lemma rect_py_ge_hi_exterior :
  forall x0 y0 x1 y1 p,
    x0 < x1 -> y0 < y1 -> y1 <= py p ->
    ~ point_set (rect_geometry x0 y0 x1 y1) p.
Proof.
  intros x0 y0 x1 y1 p Hx Hy Hge Hin.
  apply rect_point_set_half_open in Hin; try assumption. lra.
Qed.

Lemma rect_boundary_closed_box :
  forall x0 y0 x1 y1 p,
    x0 < x1 -> y0 < y1 ->
    geom_boundary (rect_geometry x0 y0 x1 y1) p ->
    x0 <= px p <= x1 /\ y0 <= py p <= y1.
Proof.
  intros x0 y0 x1 y1 p Hx Hy Hb.
  destruct Hb as [poly [Hpoly [e [He Hon]]]].
  unfold rect_geometry in Hpoly. simpl in Hpoly.
  destruct Hpoly as [Heq | []]. subst poly.
  unfold poly_edges, rect_polygon in He. simpl in He.
  unfold on_edge in Hon.
  destruct He as [<- | [<- | [<- | [<- | []]]]]; simpl in Hon.
  - pose proof (between_in_coord_range (mkPoint x0 y0) (mkPoint x1 y0) p Hon)
      as [Hpx Hpy].
    cbn [px py] in Hpx, Hpy.
    rewrite (Rmin_left x0 x1) in Hpx by lra.
    rewrite (Rmax_right x0 x1) in Hpx by lra.
    rewrite (Rmin_left y0 y0) in Hpy by lra.
    rewrite (Rmax_left y0 y0) in Hpy by lra.
    lra.
  - pose proof (between_in_coord_range (mkPoint x1 y0) (mkPoint x1 y1) p Hon)
      as [Hpx Hpy].
    cbn [px py] in Hpx, Hpy.
    rewrite (Rmin_left x1 x1) in Hpx by lra.
    rewrite (Rmax_left x1 x1) in Hpx by lra.
    rewrite (Rmin_left y0 y1) in Hpy by lra.
    rewrite (Rmax_right y0 y1) in Hpy by lra.
    lra.
  - pose proof (between_in_coord_range (mkPoint x1 y1) (mkPoint x0 y1) p Hon)
      as [Hpx Hpy].
    cbn [px py] in Hpx, Hpy.
    rewrite (Rmin_right x1 x0) in Hpx by lra.
    rewrite (Rmax_left x1 x0) in Hpx by lra.
    rewrite (Rmin_left y1 y1) in Hpy by lra.
    rewrite (Rmax_left y1 y1) in Hpy by lra.
    lra.
  - pose proof (between_in_coord_range (mkPoint x0 y1) (mkPoint x0 y0) p Hon)
      as [Hpx Hpy].
    cbn [px py] in Hpx, Hpy.
    rewrite (Rmin_left x0 x0) in Hpx by lra.
    rewrite (Rmax_left x0 x0) in Hpx by lra.
    rewrite (Rmin_right y1 y0) in Hpy by lra.
    rewrite (Rmax_left y1 y0) in Hpy by lra.
    lra.
Qed.

Lemma rect_bl_boundary : forall x0 y0 x1 y1,
  geom_boundary (rect_geometry x0 y0 x1 y1) (mkPoint x0 y0).
Proof.
  intros x0 y0 x1 y1.
  unfold geom_boundary.
  exists (rect_polygon x0 y0 x1 y1). split.
  - unfold rect_geometry. simpl. left. reflexivity.
  - exists (mkPoint x0 y0, mkPoint x1 y0). split.
    + unfold poly_edges, rect_polygon. simpl. left. reflexivity.
    + unfold on_edge. simpl. apply between_P0.
Qed.

Lemma rect_br_boundary : forall x0 y0 x1 y1,
  geom_boundary (rect_geometry x0 y0 x1 y1) (mkPoint x1 y0).
Proof.
  intros x0 y0 x1 y1.
  unfold geom_boundary.
  exists (rect_polygon x0 y0 x1 y1). split.
  - unfold rect_geometry. simpl. left. reflexivity.
  - exists (mkPoint x1 y0, mkPoint x1 y1). split.
    + unfold poly_edges, rect_polygon. simpl. right. left. reflexivity.
    + unfold on_edge. simpl. apply between_P0.
Qed.

Lemma rect_tr_boundary : forall x0 y0 x1 y1,
  geom_boundary (rect_geometry x0 y0 x1 y1) (mkPoint x1 y1).
Proof.
  intros x0 y0 x1 y1.
  unfold geom_boundary.
  exists (rect_polygon x0 y0 x1 y1). split.
  - unfold rect_geometry. simpl. left. reflexivity.
  - exists (mkPoint x1 y0, mkPoint x1 y1). split.
    + unfold poly_edges, rect_polygon. simpl. right. left. reflexivity.
    + unfold on_edge. simpl. apply between_P1.
Qed.

Lemma rect_tl_boundary : forall x0 y0 x1 y1,
  geom_boundary (rect_geometry x0 y0 x1 y1) (mkPoint x0 y1).
Proof.
  intros x0 y0 x1 y1.
  unfold geom_boundary.
  exists (rect_polygon x0 y0 x1 y1). split.
  - unfold rect_geometry. simpl. left. reflexivity.
  - exists (mkPoint x0 y1, mkPoint x0 y0). split.
    + unfold poly_edges, rect_polygon. simpl.
      right. right. right. left. reflexivity.
    + unfold on_edge. simpl. apply between_P0.
Qed.

(* -------------------------------------------------------------------------- *)
(* Open disk inside the open box (dim-2 witness).                             *)
(* -------------------------------------------------------------------------- *)

Lemma Rabs_lt_between : forall x r, Rabs x < r -> - r < x < r.
Proof.
  intros x r H.
  destruct (Rle_or_lt 0 x) as [Hx | Hx].
  - rewrite (Rabs_pos_eq x Hx) in H. split; lra.
  - rewrite (Rabs_left x Hx) in H. split; lra.
Qed.

Lemma Rabs_mul_self : forall x, Rabs x * Rabs x = x * x.
Proof.
  intros x. rewrite <- Rabs_mult. apply Rabs_pos_eq. apply Rle_0_sqr.
Qed.

Lemma abs_coord_le_dist_x : forall p q, Rabs (px p - px q) <= dist p q.
Proof.
  intros p q.
  pose proof (dist_sq_nonneg p q) as Hnn.
  unfold dist.
  apply (proj2 (sq_monotone_nonneg (Rabs (px p - px q))
                   (sqrt (dist_sq p q)) (Rabs_pos _) (sqrt_pos _))).
  rewrite sqrt_sqrt by exact Hnn.
  rewrite Rabs_mul_self.
  unfold dist_sq. pose proof (Rle_0_sqr (py p - py q)). unfold Rsqr in *. lra.
Qed.

Lemma abs_coord_le_dist_y : forall p q, Rabs (py p - py q) <= dist p q.
Proof.
  intros p q.
  pose proof (dist_sq_nonneg p q) as Hnn.
  unfold dist.
  apply (proj2 (sq_monotone_nonneg (Rabs (py p - py q))
                   (sqrt (dist_sq p q)) (Rabs_pos _) (sqrt_pos _))).
  rewrite sqrt_sqrt by exact Hnn.
  rewrite Rabs_mul_self.
  unfold dist_sq. pose proof (Rle_0_sqr (px p - px q)). unfold Rsqr in *. lra.
Qed.

Lemma rect_open_disk_interior :
  forall x0 y0 x1 y1 q,
    x0 < x1 -> y0 < y1 ->
    dist (rect_center x0 y0 x1 y1) q < rect_inradius x0 y0 x1 y1 ->
    rect_interior x0 y0 x1 y1 q.
Proof.
  intros x0 y0 x1 y1 q Hx Hy Hd.
  set (c := rect_center x0 y0 x1 y1).
  set (r := rect_inradius x0 y0 x1 y1).
  assert (Hrx : Rabs (px c - px q) < r).
  { apply Rle_lt_trans with (dist c q); [ apply abs_coord_le_dist_x | exact Hd ]. }
  assert (Hry : Rabs (py c - py q) < r).
  { apply Rle_lt_trans with (dist c q); [ apply abs_coord_le_dist_y | exact Hd ]. }
  apply Rabs_lt_between in Hrx. apply Rabs_lt_between in Hry.
  destruct Hrx as [Hrx1 Hrx2]. destruct Hry as [Hry1 Hry2].
  assert (Hrb : r <= (x1 - x0) / 2 /\ r <= (y1 - y0) / 2).
  { unfold r, rect_inradius. split; [ apply Rmin_l | apply Rmin_r ]. }
  unfold rect_interior, c, rect_center in *.
  cbn [px py] in *.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Vertical touch: A left of B, shared edge x = ax1 = bx0.                    *)
(* -------------------------------------------------------------------------- *)

Lemma touch_rect_vert_ib_empty :
  forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
    rects_touch_vertical_edge ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 ->
    rect_cell_empty (fun p =>
      point_set (rect_geometry ax0 ay0 ax1 ay1) p /\
      geom_boundary (rect_geometry bx0 by0 bx1 by1) p).
Proof.
  intros ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 Htouch p [HA HB].
  destruct Htouch as (Hax & Hay & Hbx & Hby & Heq & _ & _).
  apply rect_point_set_half_open in HA; try assumption.
  apply rect_boundary_closed_box in HB; try assumption.
  subst bx0. lra.
Qed.

Lemma touch_rect_vert_bi_empty :
  forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
    rects_touch_vertical_edge ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 ->
    rect_cell_empty (fun p =>
      geom_boundary (rect_geometry ax0 ay0 ax1 ay1) p /\
      rect_interior bx0 by0 bx1 by1 p).
Proof.
  intros ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 Htouch p [HA HB].
  destruct Htouch as (Hax & Hay & _ & _ & Heq & _ & _).
  apply rect_boundary_closed_box in HA; try assumption.
  unfold rect_interior in HB. subst bx0. lra.
Qed.

Lemma touch_rect_vert_ie_dim2 :
  forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
    rects_touch_vertical_edge ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 ->
    rect_cell_dim2 (fun p =>
      point_set (rect_geometry ax0 ay0 ax1 ay1) p /\
      ~ point_set (rect_geometry bx0 by0 bx1 by1) p).
Proof.
  intros ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 Htouch.
  destruct Htouch as (Hax & Hay & Hbx & Hby & Heq & _ & _).
  exists (rect_center ax0 ay0 ax1 ay1), (rect_inradius ax0 ay0 ax1 ay1).
  split.
  - apply rect_inradius_pos; assumption.
  - intros q Hq.
    pose proof (rect_open_disk_interior ax0 ay0 ax1 ay1 q Hax Hay Hq) as Hi.
    split.
    + apply rect_interior_point_set; assumption.
    + apply (rect_px_lt_lo_exterior bx0 by0 bx1 by1 q Hbx Hby).
      unfold rect_interior in Hi. subst bx0. lra.
Qed.

Lemma touch_rect_vert_ei_dim2 :
  forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
    rects_touch_vertical_edge ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 ->
    rect_cell_dim2 (fun p =>
      ~ point_set (rect_geometry ax0 ay0 ax1 ay1) p /\
      point_set (rect_geometry bx0 by0 bx1 by1) p).
Proof.
  intros ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 Htouch.
  destruct Htouch as (Hax & Hay & Hbx & Hby & Heq & _ & _).
  exists (rect_center bx0 by0 bx1 by1), (rect_inradius bx0 by0 bx1 by1).
  split.
  - apply rect_inradius_pos; assumption.
  - intros q Hq.
    pose proof (rect_open_disk_interior bx0 by0 bx1 by1 q Hbx Hby Hq) as Hi.
    split.
    + apply (rect_px_ge_hi_exterior ax0 ay0 ax1 ay1 q Hax Hay).
      unfold rect_interior in Hi. subst bx0. lra.
    + apply rect_interior_point_set; assumption.
Qed.

Lemma touch_rect_vert_be_dim1 :
  forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
    rects_touch_vertical_edge ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 ->
    rect_cell_dim1 (fun p =>
      geom_boundary (rect_geometry ax0 ay0 ax1 ay1) p /\
      ~ point_set (rect_geometry bx0 by0 bx1 by1) p).
Proof.
  intros ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 Htouch.
  destruct Htouch as (Hax & Hay & Hbx & Hby & Heq & _ & _).
  exists (mkPoint ax0 ay0), (mkPoint ax0 ay1).
  repeat split.
  - apply rect_bl_boundary.
  - apply rect_px_lt_lo_exterior; try assumption. simpl. subst bx0. lra.
  - apply rect_tl_boundary.
  - apply rect_px_lt_lo_exterior; try assumption. simpl. subst bx0. lra.
  - intros Heqpt. apply (f_equal py) in Heqpt. simpl in Heqpt. lra.
Qed.

Lemma touch_rect_vert_eb_dim1 :
  forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
    rects_touch_vertical_edge ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 ->
    rect_cell_dim1 (fun p =>
      ~ point_set (rect_geometry ax0 ay0 ax1 ay1) p /\
      geom_boundary (rect_geometry bx0 by0 bx1 by1) p).
Proof.
  intros ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 Htouch.
  destruct Htouch as (Hax & Hay & Hbx & Hby & Heq & _ & _).
  exists (mkPoint bx1 by0), (mkPoint bx1 by1).
  repeat split.
  - apply rect_px_ge_hi_exterior; try assumption. simpl. subst bx0. lra.
  - apply rect_br_boundary.
  - apply rect_px_ge_hi_exterior; try assumption. simpl. subst bx0. lra.
  - apply rect_tr_boundary.
  - intros Heqpt. apply (f_equal py) in Heqpt. simpl in Heqpt. lra.
Qed.

Lemma touch_rect_vert_six_cells :
  forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
    rects_touch_vertical_edge ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 ->
    rect_cell_empty (fun p =>
      point_set (rect_geometry ax0 ay0 ax1 ay1) p /\
      geom_boundary (rect_geometry bx0 by0 bx1 by1) p) /\
    rect_cell_empty (fun p =>
      geom_boundary (rect_geometry ax0 ay0 ax1 ay1) p /\
      rect_interior bx0 by0 bx1 by1 p) /\
    rect_cell_dim2 (fun p =>
      point_set (rect_geometry ax0 ay0 ax1 ay1) p /\
      ~ point_set (rect_geometry bx0 by0 bx1 by1) p) /\
    rect_cell_dim2 (fun p =>
      ~ point_set (rect_geometry ax0 ay0 ax1 ay1) p /\
      point_set (rect_geometry bx0 by0 bx1 by1) p) /\
    rect_cell_dim1 (fun p =>
      geom_boundary (rect_geometry ax0 ay0 ax1 ay1) p /\
      ~ point_set (rect_geometry bx0 by0 bx1 by1) p) /\
    rect_cell_dim1 (fun p =>
      ~ point_set (rect_geometry ax0 ay0 ax1 ay1) p /\
      geom_boundary (rect_geometry bx0 by0 bx1 by1) p).
Proof.
  intros ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 Htouch.
  split; [| split; [| split; [| split; [| split]]]].
  - apply touch_rect_vert_ib_empty. exact Htouch.
  - apply touch_rect_vert_bi_empty. exact Htouch.
  - apply touch_rect_vert_ie_dim2. exact Htouch.
  - apply touch_rect_vert_ei_dim2. exact Htouch.
  - apply touch_rect_vert_be_dim1. exact Htouch.
  - apply touch_rect_vert_eb_dim1. exact Htouch.
Qed.

(* -------------------------------------------------------------------------- *)
(* Horizontal touch: A below B, shared edge y = ay1 = by0.                    *)
(* -------------------------------------------------------------------------- *)

Lemma touch_rect_horiz_ib_empty :
  forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
    rects_touch_horizontal_edge ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 ->
    rect_cell_empty (fun p =>
      point_set (rect_geometry ax0 ay0 ax1 ay1) p /\
      geom_boundary (rect_geometry bx0 by0 bx1 by1) p).
Proof.
  intros ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 Htouch p [HA HB].
  destruct Htouch as (Hax & Hay & Hbx & Hby & Heq & _ & _).
  apply rect_point_set_half_open in HA; try assumption.
  apply rect_boundary_closed_box in HB; try assumption.
  subst by0. lra.
Qed.

Lemma touch_rect_horiz_bi_empty :
  forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
    rects_touch_horizontal_edge ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 ->
    rect_cell_empty (fun p =>
      geom_boundary (rect_geometry ax0 ay0 ax1 ay1) p /\
      rect_interior bx0 by0 bx1 by1 p).
Proof.
  intros ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 Htouch p [HA HB].
  destruct Htouch as (Hax & Hay & _ & _ & Heq & _ & _).
  apply rect_boundary_closed_box in HA; try assumption.
  unfold rect_interior in HB. subst by0. lra.
Qed.

Lemma touch_rect_horiz_ie_dim2 :
  forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
    rects_touch_horizontal_edge ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 ->
    rect_cell_dim2 (fun p =>
      point_set (rect_geometry ax0 ay0 ax1 ay1) p /\
      ~ point_set (rect_geometry bx0 by0 bx1 by1) p).
Proof.
  intros ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 Htouch.
  destruct Htouch as (Hax & Hay & Hbx & Hby & Heq & _ & _).
  exists (rect_center ax0 ay0 ax1 ay1), (rect_inradius ax0 ay0 ax1 ay1).
  split.
  - apply rect_inradius_pos; assumption.
  - intros q Hq.
    pose proof (rect_open_disk_interior ax0 ay0 ax1 ay1 q Hax Hay Hq) as Hi.
    split.
    + apply rect_interior_point_set; assumption.
    + apply (rect_py_lt_lo_exterior bx0 by0 bx1 by1 q Hbx Hby).
      unfold rect_interior in Hi. subst by0. lra.
Qed.

Lemma touch_rect_horiz_ei_dim2 :
  forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
    rects_touch_horizontal_edge ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 ->
    rect_cell_dim2 (fun p =>
      ~ point_set (rect_geometry ax0 ay0 ax1 ay1) p /\
      point_set (rect_geometry bx0 by0 bx1 by1) p).
Proof.
  intros ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 Htouch.
  destruct Htouch as (Hax & Hay & Hbx & Hby & Heq & _ & _).
  exists (rect_center bx0 by0 bx1 by1), (rect_inradius bx0 by0 bx1 by1).
  split.
  - apply rect_inradius_pos; assumption.
  - intros q Hq.
    pose proof (rect_open_disk_interior bx0 by0 bx1 by1 q Hbx Hby Hq) as Hi.
    split.
    + apply (rect_py_ge_hi_exterior ax0 ay0 ax1 ay1 q Hax Hay).
      unfold rect_interior in Hi. subst by0. lra.
    + apply rect_interior_point_set; assumption.
Qed.

Lemma touch_rect_horiz_be_dim1 :
  forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
    rects_touch_horizontal_edge ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 ->
    rect_cell_dim1 (fun p =>
      geom_boundary (rect_geometry ax0 ay0 ax1 ay1) p /\
      ~ point_set (rect_geometry bx0 by0 bx1 by1) p).
Proof.
  intros ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 Htouch.
  destruct Htouch as (Hax & Hay & Hbx & Hby & Heq & _ & _).
  exists (mkPoint ax0 ay0), (mkPoint ax1 ay0).
  repeat split.
  - apply rect_bl_boundary.
  - apply rect_py_lt_lo_exterior; try assumption. simpl. subst by0. lra.
  - apply rect_br_boundary.
  - apply rect_py_lt_lo_exterior; try assumption. simpl. subst by0. lra.
  - intros Heqpt. apply (f_equal px) in Heqpt. simpl in Heqpt. lra.
Qed.

Lemma touch_rect_horiz_eb_dim1 :
  forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
    rects_touch_horizontal_edge ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 ->
    rect_cell_dim1 (fun p =>
      ~ point_set (rect_geometry ax0 ay0 ax1 ay1) p /\
      geom_boundary (rect_geometry bx0 by0 bx1 by1) p).
Proof.
  intros ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 Htouch.
  destruct Htouch as (Hax & Hay & Hbx & Hby & Heq & _ & _).
  exists (mkPoint bx0 by1), (mkPoint bx1 by1).
  repeat split.
  - apply rect_py_ge_hi_exterior; try assumption. simpl. subst by0. lra.
  - apply rect_tl_boundary.
  - apply rect_py_ge_hi_exterior; try assumption. simpl. subst by0. lra.
  - apply rect_tr_boundary.
  - intros Heqpt. apply (f_equal px) in Heqpt. simpl in Heqpt. lra.
Qed.

Lemma touch_rect_horiz_six_cells :
  forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
    rects_touch_horizontal_edge ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 ->
    rect_cell_empty (fun p =>
      point_set (rect_geometry ax0 ay0 ax1 ay1) p /\
      geom_boundary (rect_geometry bx0 by0 bx1 by1) p) /\
    rect_cell_empty (fun p =>
      geom_boundary (rect_geometry ax0 ay0 ax1 ay1) p /\
      rect_interior bx0 by0 bx1 by1 p) /\
    rect_cell_dim2 (fun p =>
      point_set (rect_geometry ax0 ay0 ax1 ay1) p /\
      ~ point_set (rect_geometry bx0 by0 bx1 by1) p) /\
    rect_cell_dim2 (fun p =>
      ~ point_set (rect_geometry ax0 ay0 ax1 ay1) p /\
      point_set (rect_geometry bx0 by0 bx1 by1) p) /\
    rect_cell_dim1 (fun p =>
      geom_boundary (rect_geometry ax0 ay0 ax1 ay1) p /\
      ~ point_set (rect_geometry bx0 by0 bx1 by1) p) /\
    rect_cell_dim1 (fun p =>
      ~ point_set (rect_geometry ax0 ay0 ax1 ay1) p /\
      geom_boundary (rect_geometry bx0 by0 bx1 by1) p).
Proof.
  intros ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 Htouch.
  split; [| split; [| split; [| split; [| split]]]].
  - apply touch_rect_horiz_ib_empty. exact Htouch.
  - apply touch_rect_horiz_bi_empty. exact Htouch.
  - apply touch_rect_horiz_ie_dim2. exact Htouch.
  - apply touch_rect_horiz_ei_dim2. exact Htouch.
  - apply touch_rect_horiz_be_dim1. exact Htouch.
  - apply touch_rect_horiz_eb_dim1. exact Htouch.
Qed.

(* -------------------------------------------------------------------------- *)
(* Concrete pairs are instances, not the claim.                               *)
(* -------------------------------------------------------------------------- *)

Lemma touch_rect_vert_witness_touch :
  rects_touch_vertical_edge 0 0 1 1 1 0 2 1.
Proof.
  unfold rects_touch_vertical_edge. repeat split; lra.
Qed.

Lemma touch_rect_horiz_witness_touch :
  rects_touch_horizontal_edge 0 0 1 1 0 1 1 2.
Proof.
  unfold rects_touch_horizontal_edge. repeat split; lra.
Qed.

Lemma touch_rect_vert_witness_six_cells :
  rect_cell_empty (fun p =>
    point_set (rect_geometry 0 0 1 1) p /\
    geom_boundary (rect_geometry 1 0 2 1) p) /\
  rect_cell_empty (fun p =>
    geom_boundary (rect_geometry 0 0 1 1) p /\
    rect_interior 1 0 2 1 p) /\
  rect_cell_dim2 (fun p =>
    point_set (rect_geometry 0 0 1 1) p /\
    ~ point_set (rect_geometry 1 0 2 1) p) /\
  rect_cell_dim2 (fun p =>
    ~ point_set (rect_geometry 0 0 1 1) p /\
    point_set (rect_geometry 1 0 2 1) p) /\
  rect_cell_dim1 (fun p =>
    geom_boundary (rect_geometry 0 0 1 1) p /\
    ~ point_set (rect_geometry 1 0 2 1) p) /\
  rect_cell_dim1 (fun p =>
    ~ point_set (rect_geometry 0 0 1 1) p /\
    geom_boundary (rect_geometry 1 0 2 1) p).
Proof.
  apply (touch_rect_vert_six_cells 0 0 1 1 1 0 2 1).
  exact touch_rect_vert_witness_touch.
Qed.

Lemma touch_rect_horiz_witness_six_cells :
  rect_cell_empty (fun p =>
    point_set (rect_geometry 0 0 1 1) p /\
    geom_boundary (rect_geometry 0 1 1 2) p) /\
  rect_cell_empty (fun p =>
    geom_boundary (rect_geometry 0 0 1 1) p /\
    rect_interior 0 1 1 2 p) /\
  rect_cell_dim2 (fun p =>
    point_set (rect_geometry 0 0 1 1) p /\
    ~ point_set (rect_geometry 0 1 1 2) p) /\
  rect_cell_dim2 (fun p =>
    ~ point_set (rect_geometry 0 0 1 1) p /\
    point_set (rect_geometry 0 1 1 2) p) /\
  rect_cell_dim1 (fun p =>
    geom_boundary (rect_geometry 0 0 1 1) p /\
    ~ point_set (rect_geometry 0 1 1 2) p) /\
  rect_cell_dim1 (fun p =>
    ~ point_set (rect_geometry 0 0 1 1) p /\
    geom_boundary (rect_geometry 0 1 1 2) p).
Proof.
  apply (touch_rect_horiz_six_cells 0 0 1 1 0 1 1 2).
  exact touch_rect_horiz_witness_touch.
Qed.

(* Coded-tier BI is inhabited: the shared-edge midpoint is on A's boundary
   and in B's half-open point_set, and it is not in the open box. *)
Lemma touch_vert_bi_point_set_inhabited :
  let p := mkPoint 1 (1 / 2) in
  rects_touch_vertical_edge 0 0 1 1 1 0 2 1 /\
  geom_boundary (rect_geometry 0 0 1 1) p /\
  point_set (rect_geometry 1 0 2 1) p /\
  ~ rect_interior 1 0 2 1 p.
Proof.
  split; [ exact touch_rect_vert_witness_touch |].
  set (p := mkPoint 1 (1 / 2)).
  split; [| split].
  - unfold geom_boundary.
    exists (rect_polygon 0 0 1 1). split.
    + unfold rect_geometry. simpl. left. reflexivity.
    + exists (mkPoint 1 0, mkPoint 1 1). split.
      * unfold poly_edges, rect_polygon. simpl. right. left. reflexivity.
      * unfold on_edge. simpl. exists (1 / 2). repeat split; simpl; lra.
  - unfold point_set, rect_geometry.
    exists (rect_polygon 1 0 2 1). split.
    + simpl. left. reflexivity.
    + apply rect_polygon_no_holes.
      apply point_in_ring_rect_iff; try lra.
      unfold p. simpl. split; lra.
  - unfold rect_interior, p. simpl. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stop.  LEFT is the six forall cells, vertical and   *)
(* horizontal.  RIGHT would be a vertical-touch pair whose open interior of   *)
(* A meets B's point_set (the IE interval fact failing).                       *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0003-touch-rect-cells-general","topic":"relate","lemma":"ticket_0003_touch_rect_cells_general_qed_or_qex","title":"ADR-0003 rect shared-edge touch: forall vertical and horizontal pair, IB empty on point_set/boundary, BI empty on rect_interior, IE=EI dim2, BE=EB dim1 (QED) or an open-interior point of A meets B point_set (QEX); discharged QED; no ring_complement guard","file":"theories/RelateNGTouchRectCellsGeneral.v","witness":"0003-touch-rect-cells-general","board":"ADR-0003"} *)

Theorem ticket_0003_touch_rect_cells_general_qed_or_qex :
  (
    (forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
       rects_touch_vertical_edge ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 ->
       rect_cell_empty (fun p =>
         point_set (rect_geometry ax0 ay0 ax1 ay1) p /\
         geom_boundary (rect_geometry bx0 by0 bx1 by1) p) /\
       rect_cell_empty (fun p =>
         geom_boundary (rect_geometry ax0 ay0 ax1 ay1) p /\
         rect_interior bx0 by0 bx1 by1 p) /\
       rect_cell_dim2 (fun p =>
         point_set (rect_geometry ax0 ay0 ax1 ay1) p /\
         ~ point_set (rect_geometry bx0 by0 bx1 by1) p) /\
       rect_cell_dim2 (fun p =>
         ~ point_set (rect_geometry ax0 ay0 ax1 ay1) p /\
         point_set (rect_geometry bx0 by0 bx1 by1) p) /\
       rect_cell_dim1 (fun p =>
         geom_boundary (rect_geometry ax0 ay0 ax1 ay1) p /\
         ~ point_set (rect_geometry bx0 by0 bx1 by1) p) /\
       rect_cell_dim1 (fun p =>
         ~ point_set (rect_geometry ax0 ay0 ax1 ay1) p /\
         geom_boundary (rect_geometry bx0 by0 bx1 by1) p))
    /\
    (forall ax0 ay0 ax1 ay1 bx0 by0 bx1 by1,
       rects_touch_horizontal_edge ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 ->
       rect_cell_empty (fun p =>
         point_set (rect_geometry ax0 ay0 ax1 ay1) p /\
         geom_boundary (rect_geometry bx0 by0 bx1 by1) p) /\
       rect_cell_empty (fun p =>
         geom_boundary (rect_geometry ax0 ay0 ax1 ay1) p /\
         rect_interior bx0 by0 bx1 by1 p) /\
       rect_cell_dim2 (fun p =>
         point_set (rect_geometry ax0 ay0 ax1 ay1) p /\
         ~ point_set (rect_geometry bx0 by0 bx1 by1) p) /\
       rect_cell_dim2 (fun p =>
         ~ point_set (rect_geometry ax0 ay0 ax1 ay1) p /\
         point_set (rect_geometry bx0 by0 bx1 by1) p) /\
       rect_cell_dim1 (fun p =>
         geom_boundary (rect_geometry ax0 ay0 ax1 ay1) p /\
         ~ point_set (rect_geometry bx0 by0 bx1 by1) p) /\
       rect_cell_dim1 (fun p =>
         ~ point_set (rect_geometry ax0 ay0 ax1 ay1) p /\
         geom_boundary (rect_geometry bx0 by0 bx1 by1) p))
  )
  \/
  (exists ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 p,
     rects_touch_vertical_edge ax0 ay0 ax1 ay1 bx0 by0 bx1 by1 /\
     rect_interior ax0 ay0 ax1 ay1 p /\
     point_set (rect_geometry bx0 by0 bx1 by1) p).
Proof.
  left. split.
  - exact touch_rect_vert_six_cells.
  - exact touch_rect_horiz_six_cells.
Qed.

Print Assumptions rect_boundary_closed_box.
Print Assumptions rect_open_disk_interior.
Print Assumptions touch_rect_vert_ib_empty.
Print Assumptions touch_rect_vert_bi_empty.
Print Assumptions touch_rect_vert_ie_dim2.
Print Assumptions touch_rect_vert_ei_dim2.
Print Assumptions touch_rect_vert_be_dim1.
Print Assumptions touch_rect_vert_eb_dim1.
Print Assumptions touch_rect_horiz_ib_empty.
Print Assumptions touch_rect_horiz_bi_empty.
Print Assumptions touch_rect_horiz_ie_dim2.
Print Assumptions touch_rect_horiz_ei_dim2.
Print Assumptions touch_rect_horiz_be_dim1.
Print Assumptions touch_rect_horiz_eb_dim1.
Print Assumptions touch_rect_vert_six_cells.
Print Assumptions touch_rect_horiz_six_cells.
Print Assumptions touch_rect_vert_witness_six_cells.
Print Assumptions touch_rect_horiz_witness_six_cells.
Print Assumptions touch_vert_bi_point_set_inhabited.
Print Assumptions ticket_0003_touch_rect_cells_general_qed_or_qex.
