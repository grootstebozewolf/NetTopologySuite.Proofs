(* ============================================================================
   NetTopologySuite.Proofs.RightTriangleJCT
   ----------------------------------------------------------------------------
   Special-case JCT, first SLOPED-edge family: the axis-aligned right triangle.

   Generalises the rectangle ray-parity computation (RectangleJCT.v) to a ring
   with a sloped edge.  Vertices A=(x0,y0), B=(x1,y0), C=(x0,y1) (legs along the
   bottom y=y0 and left x=x0, hypotenuse B--C), x0<x1, y0<y1.  Edges:
     e1 bottom  ((x0,y0),(x1,y0))  -- horizontal, ray-parallel, never crosses
     e2 hyp     ((x1,y0),(x0,y1))  -- SLOPED
     e3 left    ((x0,y1),(x0,y0))  -- vertical

   Headline (`point_in_ring_right_triangle_iff`): the rightward-ray crossing
   parity test equals membership in the (half-open) triangle interior

     point_in_ring p T  <->  (y0<py<y1  /\  x0 <= px < hyp_x py)

   where  hyp_x py = x1 + (x0-x1)*(py-y0)/(y1-y0)  is the hypotenuse's x at
   height py.  The horizontal leg never crosses; the left leg crosses iff px<x0;
   the hypotenuse crosses iff y0<py<y1 /\ px<hyp_x py.  Since x0<hyp_x py<x1 for
   interior heights, parity = {hyp crosses} xor {left crosses} = the box.

   The reusable ray-parity reduction lemmas and the two axis-aligned edge
   characterisations are imported from RectangleJCT; only the sloped-edge
   crossing (`e_hyp_cross_iff`) and the interior x-bounds (`hyp_x_bounds`) are new.

   Pure-R, three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (claude-opus-4-8)
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List.
From NTS.Proofs Require Import Distance Overlay RectangleJCT.
Import ListNotations.

Local Open Scope R_scope.

(* The hypotenuse's x-coordinate at height py (linear interpolation B--C). *)
Definition hyp_x (x0 y0 x1 y1 py : R) : R :=
  x1 + (x0 - x1) * (py - y0) / (y1 - y0).

(* For an interior height, the hypotenuse sits strictly between the legs. *)
Lemma hyp_x_bounds : forall x0 y0 x1 y1 py,
  x0 < x1 -> y0 < y1 -> y0 < py < y1 ->
  x0 < hyp_x x0 y0 x1 y1 py < x1.
Proof.
  intros x0 y0 x1 y1 py Hx01 Hy01 Hy. unfold hyp_x.
  set (w := (x0 - x1) * (py - y0) / (y1 - y0)).
  assert (Hw : w * (y1 - y0) = (x0 - x1) * (py - y0)) by (unfold w; field; lra).
  nra.
Qed.

(* The right-triangle ring and its three edges. *)
Definition rtri_ring (x0 y0 x1 y1 : R) : Ring :=
  [ mkPoint x0 y0 ; mkPoint x1 y0 ; mkPoint x0 y1 ; mkPoint x0 y0 ].

Lemma ring_edges_rtri : forall x0 y0 x1 y1,
  ring_edges (rtri_ring x0 y0 x1 y1) =
    [ (mkPoint x0 y0, mkPoint x1 y0)     (* e1 bottom, horizontal *)
    ; (mkPoint x1 y0, mkPoint x0 y1)     (* e2 hypotenuse, sloped *)
    ; (mkPoint x0 y1, mkPoint x0 y0) ].  (* e3 left, vertical     *)
Proof. reflexivity. Qed.

(* The new (sloped) edge-crossing characterisation. *)
Lemma e_hyp_cross_iff : forall (x0 y0 x1 y1 : R) (p : Point),
  y0 < y1 ->
  (edge_crosses_ray p (mkPoint x1 y0, mkPoint x0 y1)
     <-> (y0 < py p < y1 /\ px p < hyp_x x0 y0 x1 y1 (py p))).
Proof.
  intros x0 y0 x1 y1 p Hy01. unfold edge_crosses_ray, hyp_x; cbn [px py fst snd].
  split.
  - intros [[Hy Hx] | [Hy _]]; [ split; [ exact Hy | exact Hx ] | lra ].
  - intros [Hy Hx]. left; split; [ exact Hy | exact Hx ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Headline: ray-parity in-ring test = membership in the (half-open) triangle. *)
(* -------------------------------------------------------------------------- *)

Theorem point_in_ring_right_triangle_iff : forall x0 y0 x1 y1 p,
  x0 < x1 -> y0 < y1 ->
  (point_in_ring p (rtri_ring x0 y0 x1 y1)
     <-> (y0 < py p < y1 /\ x0 <= px p < hyp_x x0 y0 x1 y1 (py p))).
Proof.
  intros x0 y0 x1 y1 p Hx01 Hy01.
  unfold point_in_ring. rewrite ring_edges_rtri.
  pose proof (e_bottom_no_cross x0 y0 x1 y1 p) as Hb.
  (* drop the bottom (horizontal) edge *)
  rewrite (rpo_skip_iff _ _ _ Hb).
  (* case on the interior height band first *)
  destruct (Rlt_le_dec y0 (py p)) as [Hyb | Hyb];
  destruct (Rlt_le_dec (py p) y1) as [Hyt | Hyt].
  - (* y0 < py p < y1 : the live band *)
    pose proof (hyp_x_bounds x0 y0 x1 y1 (py p) Hx01 Hy01 (conj Hyb Hyt)) as [Hlo Hhi].
    destruct (Rlt_le_dec (px p) (hyp_x x0 y0 x1 y1 (py p))) as [HxH | HxH].
    + (* hypotenuse crosses *)
      assert (Hc2 : edge_crosses_ray p (mkPoint x1 y0, mkPoint x0 y1))
        by (apply (proj2 (e_hyp_cross_iff x0 y0 x1 y1 p Hy01)); split; [ lra | exact HxH ]).
      rewrite (rpo_cross_iff _ _ _ Hc2).
      destruct (Rlt_le_dec (px p) x0) as [Hx0 | Hx0].
      * (* also left crosses -> even -> not in ring; RHS x0<=px fails *)
        assert (Hc3 : edge_crosses_ray p (mkPoint x0 y1, mkPoint x0 y0))
          by (apply (proj2 (e_left_cross_iff x0 y0 x1 y1 p Hy01)); split; [ lra | exact Hx0 ]).
        rewrite (rpe_cross_iff _ _ _ Hc3).
        split; [ intro K; exfalso; eapply ray_parity_odd_nil_false; exact K
               | intros [_ [Hge _]]; lra ].
      * (* left does not cross -> odd -> in ring; RHS holds *)
        assert (Hnc3 : ~ edge_crosses_ray p (mkPoint x0 y1, mkPoint x0 y0))
          by (rewrite (e_left_cross_iff x0 y0 x1 y1 p Hy01); intros [_ Hlt]; lra).
        rewrite (rpe_skip_iff _ _ _ Hnc3).
        split; [ intros _; repeat split; lra | intros _; constructor ].
    + (* hypotenuse does not cross : px >= hyp_x > x0, so left does not either *)
      assert (Hnc2 : ~ edge_crosses_ray p (mkPoint x1 y0, mkPoint x0 y1))
        by (rewrite (e_hyp_cross_iff x0 y0 x1 y1 p Hy01); intros [_ Hlt]; lra).
      rewrite (rpo_skip_iff _ _ _ Hnc2).
      rewrite ray_parity_odd_single.
      rewrite (e_left_cross_iff x0 y0 x1 y1 p Hy01).
      split; intros [HY HX]; exfalso; lra.
  - (* py p <= y0 and py p < y1 : below the band -> nothing crosses *)
    assert (Hnc2 : ~ edge_crosses_ray p (mkPoint x1 y0, mkPoint x0 y1))
      by (rewrite (e_hyp_cross_iff x0 y0 x1 y1 p Hy01); intros [[? ?] _]; lra).
    rewrite (rpo_skip_iff _ _ _ Hnc2).
    rewrite ray_parity_odd_single.
    rewrite (e_left_cross_iff x0 y0 x1 y1 p Hy01).
    split; intros [HY _]; exfalso; lra.
  - (* y1 <= py p and y0 < py p : above the band -> nothing crosses *)
    assert (Hnc2 : ~ edge_crosses_ray p (mkPoint x1 y0, mkPoint x0 y1))
      by (rewrite (e_hyp_cross_iff x0 y0 x1 y1 p Hy01); intros [[? ?] _]; lra).
    rewrite (rpo_skip_iff _ _ _ Hnc2).
    rewrite ray_parity_odd_single.
    rewrite (e_left_cross_iff x0 y0 x1 y1 p Hy01).
    split; intros [HY _]; exfalso; lra.
  - (* py p <= y0 and y1 <= py p : impossible (y0<y1) *)
    exfalso; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Cheap structural facts (premises that ARE satisfied).                       *)
(* -------------------------------------------------------------------------- *)

Lemma rtri_ring_closed : forall x0 y0 x1 y1,
  ring_closed (rtri_ring x0 y0 x1 y1).
Proof.
  intros x0 y0 x1 y1.
  exists (mkPoint x0 y0), [ mkPoint x1 y0 ; mkPoint x0 y1 ].
  reflexivity.
Qed.

Lemma rtri_ring_min_points : forall x0 y0 x1 y1,
  ring_has_minimum_points (rtri_ring x0 y0 x1 y1).
Proof. intros; unfold ring_has_minimum_points, rtri_ring; cbn [length]; lia. Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions point_in_ring_right_triangle_iff.
