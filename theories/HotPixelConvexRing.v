(* ============================================================================
   NetTopologySuite.Proofs.HotPixelConvexRing
   ----------------------------------------------------------------------------
   Snap-rounding meets ray-parity: the HOT PIXEL as a convex ring.

   The hot pixel of `HotPixel.in_hot_pixel` is the half-open axis-aligned square
   `[cx-r, cx+r) x [cy-r, cy+r)` with `r = hot_pixel_radius scale`.  This file
   presents that square as a CCW `Ring` (`pixel_ring`) and connects it to the
   crossing-number predicate `Overlay.point_in_ring`, bridging the Phase-2
   snap-rounding stack to the JCT / convex-chain campaign
   (`docs/extract-rings-proof-structure.md` 11.5j).

   The pixel is a convex 4-gon with HORIZONTAL top/bottom edges, so it is NOT a
   strict `bimonotone_split` (the chain predicates `edge_up`/`edge_dn` are
   strict).  But `edge_crosses_ray` needs a strict y-straddle, so a horizontal
   edge is never crossed by a rightward ray -- only the two VERTICAL edges count.
   That makes the crossing count directly tractable, so the convex
   characterisation (`ConvexRayCrossing.convex_in_ring_iff_one_crossing`) is
   reproved here DIRECTLY for the flat-edged square, via `cross_count_cons_*`
   plus `ray_parity_count`, rather than through a `bimonotone_split`.

     1  `pixel_ring`, `pixel_ring_edges` -- the CCW 4-gon and its
        `[bottom; right; top; left]` edge list.
     2  `pixel_bottom_no_cross` / `pixel_top_no_cross` -- horizontal edges never
        cross the ray; `pixel_right_crosses_iff` / `pixel_left_crosses_iff` --
        each vertical edge crosses iff the ray height straddles the pixel and the
        origin is left of that edge's x.
     3  `pixel_ray_crosses_le_two` -- the ring is crossed at most twice;
        `pixel_in_ring_iff_one_crossing` -- inside iff crossed exactly once.
     4  `pixel_point_in_ring_iff_box` -- HEADLINE: `point_in_ring` iff a
        half-open-x / open-y box.
     5  Bridge to `in_hot_pixel`, with the grazing edge:
        `pixel_point_in_ring_implies_in_hot_pixel` (total inclusion),
        `in_hot_pixel_off_bottom_implies_point_in_ring` (the converse off the
        bottom edge), and `pixel_grazing_bottom_edge` (a concrete point on the
        included bottom edge that is `in_hot_pixel` yet not `point_in_ring` --
        the hot-pixel incarnation of `JCT_VertexGrazingCounterexample`).
     6  Validation on the unit pixel (`unit_pixel_centre_in_ring`,
        `unit_pixel_centre_one_crossing`).

   Pure-R + three-axiom.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List Lra Lia Setoid.
From NTS.Proofs Require Import Distance Overlay MonotoneChainParity HotPixel.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* 1  The hot pixel as a CCW ring.                                             *)
(* -------------------------------------------------------------------------- *)

(* The four corners of the half-open square `[cx-r, cx+r) x [cy-r, cy+r)`,
   r = hot_pixel_radius s, taken counter-clockwise from the bottom-left. *)
Definition pixel_bl (C : Point) (s : R) : Point :=
  mkPoint (px C - hot_pixel_radius s) (py C - hot_pixel_radius s).
Definition pixel_br (C : Point) (s : R) : Point :=
  mkPoint (px C + hot_pixel_radius s) (py C - hot_pixel_radius s).
Definition pixel_tr (C : Point) (s : R) : Point :=
  mkPoint (px C + hot_pixel_radius s) (py C + hot_pixel_radius s).
Definition pixel_tl (C : Point) (s : R) : Point :=
  mkPoint (px C - hot_pixel_radius s) (py C + hot_pixel_radius s).

(* CCW ring: bottom-left -> bottom-right -> top-right -> top-left -> close. *)
Definition pixel_ring (C : Point) (s : R) : Ring :=
  [ pixel_bl C s ; pixel_br C s ; pixel_tr C s ; pixel_tl C s ; pixel_bl C s ].

(* Its edge list, [bottom; right; top; left]. *)
Lemma pixel_ring_edges : forall C s,
  ring_edges (pixel_ring C s) =
    [ (pixel_bl C s, pixel_br C s)    (* bottom (horizontal) *)
    ; (pixel_br C s, pixel_tr C s)    (* right  (vertical, up)   *)
    ; (pixel_tr C s, pixel_tl C s)    (* top    (horizontal) *)
    ; (pixel_tl C s, pixel_bl C s) ]. (* left   (vertical, down) *)
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* 2  Per-edge crossing analysis.                                              *)
(* -------------------------------------------------------------------------- *)

(* A vertical edge has px a = px b, so the linear-interpolation intercept
   collapses to that shared x (the `(px b - px a) * _ / _` term vanishes). *)
Lemma intercept_collapse : forall a t d : R, a + (a - a) * t / d = a.
Proof. intros a t d. unfold Rdiv. ring. Qed.

(* A vertical edge `(mkPoint xv ya, mkPoint xv yb)` is crossed by the rightward
   ray from p iff the ray height strictly straddles the edge's y-span and p lies
   strictly left of the edge's x. *)
Lemma vertical_edge_crosses : forall (p : Point) (xv ya yb : R),
  edge_crosses_ray p (mkPoint xv ya, mkPoint xv yb) <->
  ((ya < py p < yb \/ yb < py p < ya) /\ px p < xv).
Proof.
  intros p xv ya yb.
  unfold edge_crosses_ray. simpl.
  rewrite !intercept_collapse.
  tauto.
Qed.

(* A horizontal edge `(mkPoint xa yh, mkPoint xb yh)` is never crossed: the
   strict y-straddle `py a < py p < py b` is unsatisfiable when py a = py b. *)
Lemma horizontal_edge_no_cross : forall (p : Point) (xa xb yh : R),
  ~ edge_crosses_ray p (mkPoint xa yh, mkPoint xb yh).
Proof.
  intros p xa xb yh H. unfold edge_crosses_ray in H. simpl in H.
  destruct H as [[[? ?] _] | [[? ?] _]]; lra.
Qed.

(* The bottom edge (horizontal, y = cy - r) is never crossed. *)
Lemma pixel_bottom_no_cross : forall C s p,
  ~ edge_crosses_ray p (pixel_bl C s, pixel_br C s).
Proof.
  intros C s p. unfold pixel_bl, pixel_br.
  apply (horizontal_edge_no_cross p
           (px C - hot_pixel_radius s) (px C + hot_pixel_radius s)
           (py C - hot_pixel_radius s)).
Qed.

(* The top edge (horizontal, y = cy + r) is never crossed. *)
Lemma pixel_top_no_cross : forall C s p,
  ~ edge_crosses_ray p (pixel_tr C s, pixel_tl C s).
Proof.
  intros C s p. unfold pixel_tr, pixel_tl.
  apply (horizontal_edge_no_cross p
           (px C + hot_pixel_radius s) (px C - hot_pixel_radius s)
           (py C + hot_pixel_radius s)).
Qed.

(* The right edge crosses iff the ray height straddles the pixel and p is left
   of cx + r. *)
Lemma pixel_right_crosses_iff : forall C s p, 0 < s ->
  edge_crosses_ray p (pixel_br C s, pixel_tr C s) <->
  (py C - hot_pixel_radius s < py p < py C + hot_pixel_radius s) /\
  px p < px C + hot_pixel_radius s.
Proof.
  intros C s p Hs.
  pose proof (hot_pixel_radius_pos s Hs) as Hr.
  unfold pixel_br, pixel_tr.
  rewrite vertical_edge_crosses.
  split.
  - intros [Hdisj Hx]. split; [ | exact Hx ].
    destruct Hdisj as [H | H]; [ exact H | lra ].
  - intros [Hy Hx]. split; [ left; exact Hy | exact Hx ].
Qed.

(* The left edge crosses iff the ray height straddles the pixel and p is left
   of cx - r. *)
Lemma pixel_left_crosses_iff : forall C s p, 0 < s ->
  edge_crosses_ray p (pixel_tl C s, pixel_bl C s) <->
  (py C - hot_pixel_radius s < py p < py C + hot_pixel_radius s) /\
  px p < px C - hot_pixel_radius s.
Proof.
  intros C s p Hs.
  pose proof (hot_pixel_radius_pos s Hs) as Hr.
  unfold pixel_tl, pixel_bl.
  rewrite vertical_edge_crosses.
  split.
  - intros [Hdisj Hx]. split; [ | exact Hx ].
    destruct Hdisj as [H | H]; [ lra | exact H ].
  - intros [Hy Hx]. split; [ right; exact Hy | exact Hx ].
Qed.

(* -------------------------------------------------------------------------- *)
(* 3  At most two crossings; inside iff exactly one.                           *)
(* -------------------------------------------------------------------------- *)

(* Only the two vertical edges can be crossed, so the count is at most two. *)
Lemma pixel_ray_crosses_le_two : forall C s p,
  (cross_count p (ring_edges (pixel_ring C s)) <= 2)%nat.
Proof.
  intros C s p. rewrite pixel_ring_edges.
  rewrite (cross_count_cons_nocross p _ _ (pixel_bottom_no_cross C s p)).
  destruct (edge_crosses_ray_dec p (pixel_br C s, pixel_tr C s)) as [Hrt|Hrt];
    [ rewrite (cross_count_cons_cross p _ _ Hrt)
    | rewrite (cross_count_cons_nocross p _ _ Hrt) ];
    rewrite (cross_count_cons_nocross p _ _ (pixel_top_no_cross C s p));
    (destruct (edge_crosses_ray_dec p (pixel_tl C s, pixel_bl C s)) as [Hlb|Hlb];
      [ rewrite (cross_count_cons_cross p _ _ Hlb)
      | rewrite (cross_count_cons_nocross p _ _ Hlb) ]);
    unfold cross_count; simpl; lia.
Qed.

(* The convex characterisation, reproved directly for the flat-edged square:
   odd parity (`point_in_ring`) plus the `<= 2` bound pins the count to one. *)
Lemma pixel_in_ring_iff_one_crossing : forall C s p,
  point_in_ring p (pixel_ring C s) <->
  cross_count p (ring_edges (pixel_ring C s)) = 1%nat.
Proof.
  intros C s p.
  pose proof (pixel_ray_crosses_le_two C s p) as Hle.
  unfold point_in_ring.
  destruct (ray_parity_count p (ring_edges (pixel_ring C s))) as [Hodd _].
  split.
  - intro Hpir. apply Hodd in Hpir.
    destruct (cross_count p (ring_edges (pixel_ring C s))) as [| [| [| n]]];
      cbn in Hpir; solve [ discriminate | reflexivity | lia ].
  - intro Hcc. apply Hodd. rewrite Hcc. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* 4  HEADLINE: point_in_ring iff a half-open-x / open-y box.                  *)
(* -------------------------------------------------------------------------- *)

(* `point_in_ring p (pixel_ring C s)` holds exactly on the half-open-x /
   open-y box: x in `[cx-r, cx+r)`, y in `(cy-r, cy+r)`.  The open bottom (y
   strict) is where the rightward ray grazes the bottom vertices and parity
   diverges from the closed half-open pixel (see `pixel_grazing_bottom_edge`). *)
Lemma pixel_point_in_ring_iff_box : forall C s p, 0 < s ->
  point_in_ring p (pixel_ring C s) <->
  (px C - hot_pixel_radius s <= px p < px C + hot_pixel_radius s) /\
  (py C - hot_pixel_radius s < py p < py C + hot_pixel_radius s).
Proof.
  intros C s p Hs.
  pose proof (hot_pixel_radius_pos s Hs) as Hr.
  pose proof (pixel_right_crosses_iff C s p Hs) as HR.
  pose proof (pixel_left_crosses_iff C s p Hs) as HL.
  rewrite pixel_in_ring_iff_one_crossing, pixel_ring_edges.
  rewrite (cross_count_cons_nocross p _ _ (pixel_bottom_no_cross C s p)).
  destruct (edge_crosses_ray_dec p (pixel_br C s, pixel_tr C s)) as [Hrt|Hrt].
  - rewrite (cross_count_cons_cross p _ _ Hrt).
    rewrite (cross_count_cons_nocross p _ _ (pixel_top_no_cross C s p)).
    destruct (edge_crosses_ray_dec p (pixel_tl C s, pixel_bl C s)) as [Hlb|Hlb].
    + (* both vertical edges cross: count 2, and p is left of cx - r *)
      rewrite (cross_count_cons_cross p _ _ Hlb).
      destruct (proj1 HR Hrt) as [Hstr Hxr].
      destruct (proj1 HL Hlb) as [_ Hxl].
      split.
      * intro Hc; discriminate.
      * intros [[Hxlo _] _]; exfalso; lra.
    + (* only the right edge crosses: count 1, p in the half-open box *)
      rewrite (cross_count_cons_nocross p _ _ Hlb).
      destruct (proj1 HR Hrt) as [Hstr Hxr].
      assert (Hxlo : px C - hot_pixel_radius s <= px p).
      { destruct (Rle_or_lt (px C - hot_pixel_radius s) (px p)) as [Hle|Hlt];
          [ exact Hle
          | exfalso; apply Hlb; apply (proj2 HL); split; [ exact Hstr | exact Hlt ] ]. }
      split.
      * intros _. split; [ split; [ exact Hxlo | exact Hxr ] | exact Hstr ].
      * intros _. reflexivity.
  - rewrite (cross_count_cons_nocross p _ _ Hrt).
    rewrite (cross_count_cons_nocross p _ _ (pixel_top_no_cross C s p)).
    destruct (edge_crosses_ray_dec p (pixel_tl C s, pixel_bl C s)) as [Hlb|Hlb].
    + (* left crosses but right doesn't: impossible (cx-r < cx+r) *)
      rewrite (cross_count_cons_cross p _ _ Hlb).
      destruct (proj1 HL Hlb) as [Hstr Hxl].
      exfalso. apply Hrt. apply (proj2 HR). split; [ exact Hstr | lra ].
    + (* neither crosses: count 0, p outside the box *)
      rewrite (cross_count_cons_nocross p _ _ Hlb).
      split.
      * intro Hc; discriminate.
      * intros [[_ Hxhi] Hstr]. exfalso. apply Hrt. apply (proj2 HR).
        split; [ exact Hstr | exact Hxhi ].
Qed.

(* -------------------------------------------------------------------------- *)
(* 5  Bridge to `in_hot_pixel`, with the grazing edge.                         *)
(* -------------------------------------------------------------------------- *)

(* Total inclusion: the ray-parity interior sits inside the half-open pixel.
   The open-y interior (cy - r < py p) implies the half-open lower bound. *)
Lemma pixel_point_in_ring_implies_in_hot_pixel : forall C s p, 0 < s ->
  point_in_ring p (pixel_ring C s) -> in_hot_pixel p C s.
Proof.
  intros C s p Hs Hpir.
  apply (proj1 (pixel_point_in_ring_iff_box C s p Hs)) in Hpir.
  destruct Hpir as [[Hxlo Hxhi] [Hylo Hyhi]].
  unfold in_hot_pixel. repeat split; lra.
Qed.

(* The converse, OFF the bottom edge: an `in_hot_pixel` point strictly above the
   bottom (cy - r < py p) is `point_in_ring`. *)
Lemma in_hot_pixel_off_bottom_implies_point_in_ring : forall C s p, 0 < s ->
  in_hot_pixel p C s ->
  py C - hot_pixel_radius s < py p ->
  point_in_ring p (pixel_ring C s).
Proof.
  intros C s p Hs Hin Hoff.
  apply (proj2 (pixel_point_in_ring_iff_box C s p Hs)).
  destruct Hin as [[Hxlo Hxhi] [Hylo Hyhi]].
  split; split; lra.
Qed.

(* The grazing point: the midpoint of the included bottom edge (py = cy - r). *)
Definition pixel_grazing_point (C : Point) (s : R) : Point :=
  mkPoint (px C) (py C - hot_pixel_radius s).

(* The hot-pixel incarnation of the documented vertex-grazing caveat
   (`JCT_VertexGrazingCounterexample`): a concrete point on the half-open
   pixel's INCLUDED bottom edge that is `in_hot_pixel` yet NOT `point_in_ring`.
   The rightward ray at height cy - r grazes the two bottom vertices, so the
   strict y-straddle counts neither, and the parity reads "outside". *)
Lemma pixel_grazing_bottom_edge : forall C s, 0 < s ->
  in_hot_pixel (pixel_grazing_point C s) C s /\
  ~ point_in_ring (pixel_grazing_point C s) (pixel_ring C s).
Proof.
  intros C s Hs.
  pose proof (hot_pixel_radius_pos s Hs) as Hr.
  unfold pixel_grazing_point.
  split.
  - unfold in_hot_pixel. cbn [px py]. repeat split; lra.
  - intro Hpir.
    apply (proj1 (pixel_point_in_ring_iff_box C s _ Hs)) in Hpir.
    destruct Hpir as [_ [Hylo _]]. cbn [px py] in Hylo. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* 6  Validation on the unit pixel (scale = 1, centre at the origin).          *)
(* -------------------------------------------------------------------------- *)

Lemma unit_pixel_centre_in_ring :
  point_in_ring (mkPoint 0 0) (pixel_ring (mkPoint 0 0) 1).
Proof.
  pose proof (hot_pixel_radius_pos 1 Rlt_0_1) as Hr.
  apply (proj2 (pixel_point_in_ring_iff_box (mkPoint 0 0) 1 (mkPoint 0 0) Rlt_0_1)).
  cbn [px py]. split; split; lra.
Qed.

Lemma unit_pixel_centre_one_crossing :
  cross_count (mkPoint 0 0) (ring_edges (pixel_ring (mkPoint 0 0) 1)) = 1%nat.
Proof.
  apply (proj1 (pixel_in_ring_iff_one_crossing (mkPoint 0 0) 1 (mkPoint 0 0))).
  exact unit_pixel_centre_in_ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions pixel_ray_crosses_le_two.
Print Assumptions pixel_in_ring_iff_one_crossing.
Print Assumptions pixel_point_in_ring_iff_box.
Print Assumptions pixel_point_in_ring_implies_in_hot_pixel.
Print Assumptions in_hot_pixel_off_bottom_implies_point_in_ring.
Print Assumptions pixel_grazing_bottom_edge.
