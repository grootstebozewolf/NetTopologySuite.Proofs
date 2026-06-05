(* ============================================================================
   NetTopologySuite.Proofs.RectangleJCT
   ----------------------------------------------------------------------------
   Special-case JCT, slice 1: the ray-parity COMPUTATION for an axis-aligned
   rectangle.  Part of the programme to discharge `parity_characterises_
   interior_cont` (theories/JCT.v) for tractable ring families instead of the
   full thesis-scale polygonal Jordan Curve Theorem.

   This file closes the *combinatorial / computational half* of the rectangle
   case, with NO Jordan-curve content:

     point_in_ring p (rect_ring x0 y0 x1 y1)
        <->  (y0 < py p < y1  /\  x0 <= px p < x1)         (for x0<x1, y0<y1)

   i.e. the horizontal-ray crossing-parity test `Overlay.point_in_ring`
   evaluates EXACTLY to membership in the (half-open) box.  The proof is a
   finite evaluation of the inductive `ray_parity_odd` over the rectangle's
   four edges:
     - the two horizontal edges (bottom y0, top y1) are PARALLEL to the ray
       and never cross it (their endpoints share a y-coordinate, so the strict
       y-straddle is impossible);
     - the two vertical edges (x1, x0) cross iff the ray height is strictly
       inside (y0,y1) and the edge is strictly to the right of p.
   Parity of {right-edge crosses} XOR {left-edge crosses} is exactly the box.

   The left boundary `px p = x0` is included by the standard half-open
   ray-cast convention (it lies on the left edge, hence in `ring_image`); once
   composed with `ring_complement` it agrees with the OPEN box.

   Scope note.  A strictly axis-aligned rectangle has horizontal edges, so it
   sits just outside the conservative `no_horizontal_edge_at` generic-position
   guard of `parity_characterises_interior_cont` -- but those edges are
   ray-parallel and benign, so the parity is correct regardless, and we state
   the characterisation directly.  The ANALYTIC half (`geometric_interior_cont`
   <-> open box, via `in_bounded_component_cont` + a rectangle separation /
   IVT argument) is the next slice and is NOT addressed here.

   Pure-R, three-axiom.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (claude-opus-4-8)
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam.
Import ListNotations.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Generic ray-parity reduction lemmas (reusable; finite-list evaluation).*)
(* -------------------------------------------------------------------------- *)

Lemma ray_parity_odd_nil_false : forall p, ~ ray_parity_odd p [].
Proof. intros p H; inversion H. Qed.

Lemma rpo_skip_iff : forall p e es,
  ~ edge_crosses_ray p e ->
  (ray_parity_odd p (e :: es) <-> ray_parity_odd p es).
Proof.
  intros p e es Hnc; split.
  - intros H; inversion H; subst; [ contradiction | assumption ].
  - intros H; apply rpo_skip; assumption.
Qed.

Lemma rpe_skip_iff : forall p e es,
  ~ edge_crosses_ray p e ->
  (ray_parity_even p (e :: es) <-> ray_parity_even p es).
Proof.
  intros p e es Hnc; split.
  - intros H; inversion H; subst; [ contradiction | assumption ].
  - intros H; apply rpe_skip; assumption.
Qed.

Lemma rpo_cross_iff : forall p e es,
  edge_crosses_ray p e ->
  (ray_parity_odd p (e :: es) <-> ray_parity_even p es).
Proof.
  intros p e es Hc; split.
  - intros H; inversion H; subst; [ assumption | contradiction ].
  - intros H; apply rpo_cross; assumption.
Qed.

Lemma rpe_cross_iff : forall p e es,
  edge_crosses_ray p e ->
  (ray_parity_even p (e :: es) <-> ray_parity_odd p es).
Proof.
  intros p e es Hc; split.
  - intros H; inversion H; subst; [ assumption | contradiction ].
  - intros H; apply rpe_cross; assumption.
Qed.

Lemma ray_parity_odd_single : forall p e,
  ray_parity_odd p [e] <-> edge_crosses_ray p e.
Proof.
  intros p e; split.
  - intros H; inversion H; subst.
    + assumption.
    + exfalso; eapply ray_parity_odd_nil_false; eauto.
  - intros Hc; apply rpo_cross; [ assumption | constructor ].
Qed.

Lemma ray_parity_even_single : forall p e,
  ray_parity_even p [e] <-> ~ edge_crosses_ray p e.
Proof.
  intros p e; split.
  - intros H; inversion H; subst.
    + exfalso; eapply ray_parity_odd_nil_false; eauto.
    + assumption.
  - intros Hnc; apply rpe_skip; [ assumption | constructor ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The axis-aligned rectangle ring and its four edges.                    *)
(* -------------------------------------------------------------------------- *)

(* Counter-clockwise from the bottom-left corner:
   (x0,y0) -> (x1,y0) -> (x1,y1) -> (x0,y1) -> close. *)
Definition rect_ring (x0 y0 x1 y1 : R) : Ring :=
  [ mkPoint x0 y0 ; mkPoint x1 y0 ; mkPoint x1 y1 ; mkPoint x0 y1 ; mkPoint x0 y0 ].

Lemma ring_edges_rect : forall x0 y0 x1 y1,
  ring_edges (rect_ring x0 y0 x1 y1) =
    [ (mkPoint x0 y0, mkPoint x1 y0)     (* e1 bottom, horizontal *)
    ; (mkPoint x1 y0, mkPoint x1 y1)     (* e2 right,  vertical   *)
    ; (mkPoint x1 y1, mkPoint x0 y1)     (* e3 top,    horizontal *)
    ; (mkPoint x0 y1, mkPoint x0 y0) ].  (* e4 left,   vertical   *)
Proof. reflexivity. Qed.

(* §2.1  Per-edge crossing characterisations. *)

Lemma e_bottom_no_cross : forall (x0 y0 x1 y1 : R) (p : Point),
  ~ edge_crosses_ray p (mkPoint x0 y0, mkPoint x1 y0).
Proof.
  intros x0 y0 x1 y1 p H.
  unfold edge_crosses_ray in H; cbn [px py fst snd] in H.
  destruct H as [[Hy _] | [Hy _]]; lra.
Qed.

Lemma e_top_no_cross : forall (x0 y0 x1 y1 : R) (p : Point),
  ~ edge_crosses_ray p (mkPoint x1 y1, mkPoint x0 y1).
Proof.
  intros x0 y0 x1 y1 p H.
  unfold edge_crosses_ray in H; cbn [px py fst snd] in H.
  destruct H as [[Hy _] | [Hy _]]; lra.
Qed.

Lemma e_right_cross_iff : forall (x0 y0 x1 y1 : R) (p : Point),
  y0 < y1 ->
  (edge_crosses_ray p (mkPoint x1 y0, mkPoint x1 y1)
     <-> (y0 < py p < y1 /\ px p < x1)).
Proof.
  intros x0 y0 x1 y1 p Hy01.
  assert (Hb : x1 + (x1 - x1) * (py p - y0) / (y1 - y0) = x1) by (unfold Rdiv; ring).
  unfold edge_crosses_ray; cbn [px py fst snd]; split.
  - intros [[Hy Hx] | [Hy _]].
    + rewrite Hb in Hx. split; [ exact Hy | exact Hx ].
    + lra.
  - intros [Hy Hx]. left. split; [ exact Hy | rewrite Hb; exact Hx ].
Qed.

Lemma e_left_cross_iff : forall (x0 y0 x1 y1 : R) (p : Point),
  y0 < y1 ->
  (edge_crosses_ray p (mkPoint x0 y1, mkPoint x0 y0)
     <-> (y0 < py p < y1 /\ px p < x0)).
Proof.
  intros x0 y0 x1 y1 p Hy01.
  assert (Hb : x0 + (x0 - x0) * (py p - y0) / (y1 - y0) = x0) by (unfold Rdiv; ring).
  unfold edge_crosses_ray; cbn [px py fst snd]; split.
  - intros [[Hy _] | [Hy Hx]].
    + lra.
    + rewrite Hb in Hx. split; [ exact Hy | exact Hx ].
  - intros [Hy Hx]. right. split; [ exact Hy | rewrite Hb; exact Hx ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Main: ray-parity in-ring test = membership in the (half-open) box.     *)
(* -------------------------------------------------------------------------- *)

Theorem point_in_ring_rect_iff : forall x0 y0 x1 y1 p,
  x0 < x1 -> y0 < y1 ->
  (point_in_ring p (rect_ring x0 y0 x1 y1)
     <-> (y0 < py p < y1 /\ x0 <= px p < x1)).
Proof.
  intros x0 y0 x1 y1 p Hx01 Hy01.
  unfold point_in_ring. rewrite ring_edges_rect.
  pose proof (e_bottom_no_cross x0 y0 x1 y1 p) as Hb.
  pose proof (e_top_no_cross    x0 y0 x1 y1 p) as Ht.
  pose proof (e_right_cross_iff x0 y0 x1 y1 p Hy01) as HR.
  pose proof (e_left_cross_iff  x0 y0 x1 y1 p Hy01) as HL.
  (* drop the bottom (horizontal, never crosses) *)
  rewrite (rpo_skip_iff _ _ _ Hb).
  (* split on whether the right edge crosses *)
  destruct (Rlt_dec (px p) x1) as [HxR | HxR];
  destruct (Rlt_le_dec (py p) y1) as [Hyt | Hyt];
  destruct (Rlt_le_dec y0 (py p)) as [Hyb | Hyb].
  all: try (
    (* cases where the RIGHT edge crosses: y0<py<y1 /\ px<x1 *)
    assert (HcR : edge_crosses_ray p (mkPoint x1 y0, mkPoint x1 y1))
      by (apply HR; split; [ split; lra | lra ]);
    rewrite (rpo_cross_iff _ _ _ HcR);
    rewrite (rpe_skip_iff _ _ _ Ht);
    rewrite ray_parity_even_single;
    (* now goal: ~ left-cross <-> box *)
    rewrite HL; split; intros; try (split; lra); lra).
  all: try (
    (* cases where the RIGHT edge does NOT cross *)
    assert (HncR : ~ edge_crosses_ray p (mkPoint x1 y0, mkPoint x1 y1))
      by (rewrite HR; intros [[? ?] ?]; lra);
    rewrite (rpo_skip_iff _ _ _ HncR);
    rewrite (rpo_skip_iff _ _ _ Ht);
    rewrite ray_parity_odd_single;
    rewrite HL; split; intros; try (split; lra); lra).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The rectangle is a closed ring with enough vertices (premises of the   *)
(*     headline that ARE satisfied; cheap structural facts).                  *)
(* -------------------------------------------------------------------------- *)

Lemma rect_ring_closed : forall x0 y0 x1 y1,
  ring_closed (rect_ring x0 y0 x1 y1).
Proof.
  intros x0 y0 x1 y1.
  exists (mkPoint x0 y0), [ mkPoint x1 y0 ; mkPoint x1 y1 ; mkPoint x0 y1 ].
  reflexivity.
Qed.

Lemma rect_ring_min_points : forall x0 y0 x1 y1,
  ring_has_minimum_points (rect_ring x0 y0 x1 y1).
Proof. intros; unfold ring_has_minimum_points, rect_ring; cbn [length]; lia. Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Slice 2a (analytic, JCT-free): open-box points are off the edge          *)
(*     skeleton, reducing the interior equivalence to the bounded-component     *)
(*     separation alone.                                                        *)
(* -------------------------------------------------------------------------- *)

(* A strict-interior point lies in `ring_complement` (is not on any of the four
   edges): each edge pins one coordinate to a boundary value (py=y0, px=x1,
   py=y1, px=x0), contradicting the strict box inequalities.  No Jordan content
   -- pure interval arithmetic over the four lerp parametrisations. *)
Theorem rect_open_box_complement : forall x0 y0 x1 y1 p,
  x0 < px p < x1 -> y0 < py p < y1 ->
  ring_complement (rect_ring x0 y0 x1 y1) p.
Proof.
  intros x0 y0 x1 y1 p Hx Hy.
  intros [e [t [Hin [Ht [Hpx Hpy]]]]].
  rewrite ring_edges_rect in Hin.
  cbn [In] in Hin.
  destruct Hin as [He | [He | [He | [He | []]]]];
    subst e; cbn [px py fst snd] in Hpx, Hpy; nra.
Qed.

(* Consequently, for a strict-interior point the `ring_complement` half of
   `geometric_interior_cont` is automatic, so "geometric interior" collapses to
   exactly "in a bounded complement component" -- the single remaining analytic
   rung (the rectangle separation / IVT argument), isolated. *)
Theorem rect_open_box_interior_iff_bounded : forall x0 y0 x1 y1 p,
  x0 < px p < x1 -> y0 < py p < y1 ->
  (geometric_interior_cont p (rect_ring x0 y0 x1 y1)
     <-> in_bounded_component_cont (rect_ring x0 y0 x1 y1) p).
Proof.
  intros x0 y0 x1 y1 p Hx Hy.
  unfold geometric_interior_cont; split.
  - intros [_ Hb]; exact Hb.
  - intros Hb; split; [ apply rect_open_box_complement; assumption | exact Hb ].
Qed.

(* The combined slice-1+2a picture for a strict-interior point: the ray-parity
   test fires AND the point is off the skeleton AND "interior = bounded
   component".  Everything except the bounded-component separation is now Qed. *)
Theorem rect_open_box_characterisation : forall x0 y0 x1 y1 p,
  x0 < x1 -> y0 < y1 ->
  x0 < px p < x1 -> y0 < py p < y1 ->
  point_in_ring p (rect_ring x0 y0 x1 y1) /\
  ring_complement (rect_ring x0 y0 x1 y1) p /\
  (geometric_interior_cont p (rect_ring x0 y0 x1 y1)
     <-> in_bounded_component_cont (rect_ring x0 y0 x1 y1) p).
Proof.
  intros x0 y0 x1 y1 p Hx01 Hy01 Hx Hy.
  split; [| split].
  - apply point_in_ring_rect_iff; [ exact Hx01 | exact Hy01 | ].
    split; [ exact Hy | split; lra ].
  - apply rect_open_box_complement; assumption.
  - apply rect_open_box_interior_iff_bounded; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions point_in_ring_rect_iff.
Print Assumptions rect_open_box_complement.
Print Assumptions rect_open_box_characterisation.
