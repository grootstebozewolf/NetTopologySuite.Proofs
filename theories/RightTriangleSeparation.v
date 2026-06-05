(* ============================================================================
   NetTopologySuite.Proofs.RightTriangleSeparation
   ----------------------------------------------------------------------------
   Special-case JCT: the right-triangle separation, UNCONDITIONALLY, via the
   reusable engine (SeparationField.separation_via_field).

   Completes the right-triangle instance begun in RightTriangleJCT.v: combining
   the ray-parity computation there with the separation here gives the
   unconditional

     right_triangle_parity_characterises_interior :
       point_in_ring p T  <->  geometric_interior_cont p T

   for strict-interior points of the axis-aligned right triangle.

   The separating field is `tri_min = Rmin (Rmin (px-x0) (py-y0)) s_hyp`, where
     s_hyp pt = (y1-y0)*(x1 - px pt) + (x1-x0)*(y0 - py pt)
   is the AFFINE inward signed distance to the hypotenuse line B--C (no division,
   so continuity is immediate).  `tri_min` is >0 strictly inside, =0 exactly on
   the three edges (ring_image), <0 outside; plug it into the engine.

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (claude-opus-4-8)
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From Stdlib Require Import Ranalysis.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam.
From NTS.Proofs Require Import RectangleJCT RectangleSeparation SeparationField RightTriangleJCT.
Import ListNotations.

Local Open Scope R_scope.

(* Affine inward signed distance to the hypotenuse line through (x1,y0),(x0,y1):
   = 0 on the line, > 0 on the interior (A=(x0,y0)) side. *)
Definition s_hyp (x0 y0 x1 y1 : R) (pt : Point) : R :=
  (y1 - y0) * (x1 - px pt) + (x1 - x0) * (y0 - py pt).

Definition tri_min (x0 y0 x1 y1 : R) (pt : Point) : R :=
  Rmin (Rmin (px pt - x0) (py pt - y0)) (s_hyp x0 y0 x1 y1 pt).

(* s_hyp > 0 is exactly "left of the hypotenuse" px < hyp_x py. *)
Lemma s_hyp_pos_iff_hyp_x : forall x0 y0 x1 y1 pt,
  y0 < y1 ->
  (0 < s_hyp x0 y0 x1 y1 pt <-> px pt < hyp_x x0 y0 x1 y1 (py pt)).
Proof.
  intros x0 y0 x1 y1 pt Hy01. unfold s_hyp, hyp_x.
  set (w := (x0 - x1) * (py pt - y0) / (y1 - y0)).
  assert (Hw : w * (y1 - y0) = (x0 - x1) * (py pt - y0)) by (unfold w; field; lra).
  split; intro H; nra.
Qed.

Lemma tri_min_pos_iff : forall x0 y0 x1 y1 pt,
  0 < tri_min x0 y0 x1 y1 pt
  <-> (x0 < px pt /\ y0 < py pt /\ 0 < s_hyp x0 y0 x1 y1 pt).
Proof.
  intros x0 y0 x1 y1 pt. unfold tri_min. rewrite !Rmin_pos_iff. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* tri_min = 0 lands on one of the three edges (ring_image).                   *)
(* -------------------------------------------------------------------------- *)

Definition on_tri_boundary (x0 y0 x1 y1 : R) (pt : Point) : Prop :=
  (px pt = x0 /\ y0 <= py pt <= y1) \/
  (py pt = y0 /\ x0 <= px pt <= x1) \/
  (s_hyp x0 y0 x1 y1 pt = 0 /\ x0 <= px pt <= x1 /\ y0 <= py pt <= y1).

Lemma tri_min_zero_imp_boundary : forall x0 y0 x1 y1 pt,
  x0 < x1 -> y0 < y1 ->
  tri_min x0 y0 x1 y1 pt = 0 -> on_tri_boundary x0 y0 x1 y1 pt.
Proof.
  intros x0 y0 x1 y1 pt Hx01 Hy01 H. unfold tri_min in H.
  destruct (Rmin_eq_0_inv _ _ H) as [HA [HB Hor]].
  assert (Hxx : 0 <= px pt - x0)
    by (pose proof (Rmin_l (px pt - x0) (py pt - y0)); lra).
  assert (Hyy : 0 <= py pt - y0)
    by (pose proof (Rmin_r (px pt - x0) (py pt - y0)); lra).
  (* HB : 0 <= s_hyp; Hor : Rmin (px-x0)(py-y0) = 0 \/ s_hyp = 0 *)
  destruct Hor as [Hinner | Hhyp].
  - destruct (Rmin_eq_0_inv _ _ Hinner) as [_ [_ [Hl | Hb]]].
    + (* px = x0 *) left. unfold s_hyp in HB. split; [ lra | nra ].
    + (* py = y0 *) right; left. unfold s_hyp in HB. split; [ lra | nra ].
  - (* s_hyp = 0 *) right; right.
    unfold s_hyp in *. split; [ exact Hhyp | nra ].
Qed.

Lemma tri_boundary_in_ring_image : forall x0 y0 x1 y1 pt,
  x0 < x1 -> y0 < y1 ->
  on_tri_boundary x0 y0 x1 y1 pt ->
  ring_image (rtri_ring x0 y0 x1 y1) pt.
Proof.
  intros x0 y0 x1 y1 pt Hx01 Hy01 Hb.
  unfold ring_image; rewrite ring_edges_rtri.
  destruct Hb as [[Hpx Hpy] | [[Hpy Hpx] | [Hs [Hpx Hpy]]]].
  - (* left edge e3 = ((x0,y1),(x0,y0)) *)
    exists (mkPoint x0 y1, mkPoint x0 y0), ((y1 - py pt) / (y1 - y0)).
    pose proof (div_in_01 (y1 - py pt) (y1 - y0) ltac:(lra) ltac:(lra) ltac:(lra)) as Ht.
    repeat split; [ cbn [In]; auto | lra | lra
                  | cbn [px py fst snd]; rewrite Hpx; field; lra
                  | cbn [px py fst snd]; field; lra ].
  - (* bottom edge e1 = ((x0,y0),(x1,y0)) *)
    exists (mkPoint x0 y0, mkPoint x1 y0), ((px pt - x0) / (x1 - x0)).
    pose proof (div_in_01 (px pt - x0) (x1 - x0) ltac:(lra) ltac:(lra) ltac:(lra)) as Ht.
    repeat split; [ cbn [In]; auto | lra | lra
                  | cbn [px py fst snd]; field; lra
                  | cbn [px py fst snd]; rewrite Hpy; field; lra ].
  - (* hypotenuse edge e2 = ((x1,y0),(x0,y1)) *)
    exists (mkPoint x1 y0, mkPoint x0 y1), ((py pt - y0) / (y1 - y0)).
    pose proof (div_in_01 (py pt - y0) (y1 - y0) ltac:(lra) ltac:(lra) ltac:(lra)) as Ht.
    repeat split; [ cbn [In]; auto | lra | lra | | ].
    + (* px eq: needs s_hyp = 0 *)
      cbn [px py fst snd]. unfold s_hyp in Hs.
      apply (Rmult_eq_reg_r (y1 - y0)); [ | lra ].
      field_simplify; [ nra | lra ].
    + cbn [px py fst snd]; field; lra.
Qed.

Lemma tri_min_nonzero_off_skeleton : forall x0 y0 x1 y1 pt,
  x0 < x1 -> y0 < y1 ->
  ring_complement (rtri_ring x0 y0 x1 y1) pt ->
  tri_min x0 y0 x1 y1 pt <> 0.
Proof.
  intros x0 y0 x1 y1 pt Hx01 Hy01 Hcomp Hz.
  apply Hcomp. apply tri_boundary_in_ring_image; [ exact Hx01 | exact Hy01 | ].
  apply tri_min_zero_imp_boundary; [ exact Hx01 | exact Hy01 | exact Hz ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Continuity of tri_min along a path.                                         *)
(* -------------------------------------------------------------------------- *)

Lemma continuity_pt_s_hyp_path : forall x0 y0 x1 y1 (g : R -> Point) t,
  continuity_pt (fun s => px (g s)) t ->
  continuity_pt (fun s => py (g s)) t ->
  continuity_pt (fun s => s_hyp x0 y0 x1 y1 (g s)) t.
Proof.
  intros x0 y0 x1 y1 g t Hu Hv. unfold s_hyp.
  apply continuity_pt_plus.
  - apply continuity_pt_scal. apply continuity_pt_minus;
      [ apply continuity_pt_const; intros ? ?; reflexivity | exact Hu ].
  - apply continuity_pt_scal. apply continuity_pt_minus;
      [ apply continuity_pt_const; intros ? ?; reflexivity | exact Hv ].
Qed.

Lemma continuity_pt_tri_min_path : forall x0 y0 x1 y1 (g : R -> Point) t,
  continuity_pt (fun s => px (g s)) t ->
  continuity_pt (fun s => py (g s)) t ->
  continuity_pt (fun s => tri_min x0 y0 x1 y1 (g s)) t.
Proof.
  intros x0 y0 x1 y1 g t Hu Hv. unfold tri_min.
  apply continuity_pt_Rmin.
  - apply continuity_pt_Rmin.
    + apply continuity_pt_minus; [ exact Hu | apply continuity_pt_const; intros ? ?; reflexivity ].
    + apply continuity_pt_minus; [ exact Hv | apply continuity_pt_const; intros ? ?; reflexivity ].
  - apply continuity_pt_s_hyp_path; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Separation: a strict-interior point is in a bounded complement component.   *)
(* -------------------------------------------------------------------------- *)

Theorem tri_interior_in_bounded_component : forall x0 y0 x1 y1 p,
  x0 < x1 -> y0 < y1 ->
  0 < tri_min x0 y0 x1 y1 p ->
  in_bounded_component_cont (rtri_ring x0 y0 x1 y1) p.
Proof.
  intros x0 y0 x1 y1 p Hx01 Hy01 Hp.
  assert (Hx2 : 0 <= Rmax (x0 * x0) (x1 * x1))
    by (apply Rle_trans with (x0 * x0); [ nra | apply Rmax_l ]).
  assert (Hy2 : 0 <= Rmax (y0 * y0) (y1 * y1))
    by (apply Rle_trans with (y0 * y0); [ nra | apply Rmax_l ]).
  apply (separation_via_field (rtri_ring x0 y0 x1 y1) (tri_min x0 y0 x1 y1) p
           (sqrt (Rmax (x0 * x0) (x1 * x1) + Rmax (y0 * y0) (y1 * y1) + 1))).
  - intros g Hcx Hcy t. apply continuity_pt_tri_min_path; [ apply Hcx | apply Hcy ].
  - intros pt Hc. apply tri_min_nonzero_off_skeleton; [ exact Hx01 | exact Hy01 | exact Hc ].
  - exact Hp.
  - apply sqrt_lt_R0; lra.
  - intros pt Hpos. apply tri_min_pos_iff in Hpos.
    destruct Hpos as [Hax [Hay Hsh]].
    (* s_hyp > 0 + interior gives px < x1 and py < y1 *)
    assert (Hbx : px pt < x1) by (unfold s_hyp in Hsh; nra).
    assert (Hby : py pt < y1) by (unfold s_hyp in Hsh; nra).
    assert (HMM : sqrt (Rmax (x0 * x0) (x1 * x1) + Rmax (y0 * y0) (y1 * y1) + 1)
                * sqrt (Rmax (x0 * x0) (x1 * x1) + Rmax (y0 * y0) (y1 * y1) + 1)
                = Rmax (x0 * x0) (x1 * x1) + Rmax (y0 * y0) (y1 * y1) + 1)
      by (apply sqrt_sqrt; lra).
    rewrite HMM.
    pose proof (sq_le_max_endpoints (px pt) x0 x1 ltac:(lra)) as Hpx2.
    pose proof (sq_le_max_endpoints (py pt) y0 y1 ltac:(lra)) as Hpy2.
    lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* A strict-interior point is off the edge skeleton.                           *)
(* -------------------------------------------------------------------------- *)

Theorem tri_interior_complement : forall x0 y0 x1 y1 p,
  x0 < x1 -> y0 < y1 ->
  0 < tri_min x0 y0 x1 y1 p ->
  ring_complement (rtri_ring x0 y0 x1 y1) p.
Proof.
  intros x0 y0 x1 y1 p Hx01 Hy01 Hp.
  apply tri_min_pos_iff in Hp. destruct Hp as [Hax [Hay Hsh]].
  intros [e [t [Hin [Ht [Hpx Hpy]]]]].
  rewrite ring_edges_rtri in Hin. cbn [In] in Hin.
  destruct Hin as [He | [He | [He | []]]];
    subst e; cbn [px py fst snd] in Hpx, Hpy; unfold s_hyp in Hsh; nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Headline: unconditional rectangle... triangle instance.                     *)
(* -------------------------------------------------------------------------- *)

Theorem right_triangle_interior_is_geometric : forall x0 y0 x1 y1 p,
  x0 < x1 -> y0 < y1 ->
  0 < tri_min x0 y0 x1 y1 p ->
  geometric_interior_cont p (rtri_ring x0 y0 x1 y1).
Proof.
  intros x0 y0 x1 y1 p Hx01 Hy01 Hp; split.
  - apply tri_interior_complement; assumption.
  - apply tri_interior_in_bounded_component; assumption.
Qed.

Theorem right_triangle_parity_characterises_interior : forall x0 y0 x1 y1 p,
  x0 < x1 -> y0 < y1 ->
  0 < tri_min x0 y0 x1 y1 p ->
  (point_in_ring p (rtri_ring x0 y0 x1 y1)
     <-> geometric_interior_cont p (rtri_ring x0 y0 x1 y1)).
Proof.
  intros x0 y0 x1 y1 p Hx01 Hy01 Hp.
  pose proof Hp as Hp'. apply tri_min_pos_iff in Hp'.
  destruct Hp' as [Hax [Hay Hsh]].
  pose proof (proj1 (s_hyp_pos_iff_hyp_x x0 y0 x1 y1 p Hy01) Hsh) as Hhx.
  (* px < hyp_x and x0 < px give py < y1 (hyp_x > x0) *)
  assert (Hby : py p < y1).
  { unfold hyp_x in Hhx.
    set (w := (x0 - x1) * (py p - y0) / (y1 - y0)) in *.
    assert (Hw : w * (y1 - y0) = (x0 - x1) * (py p - y0)) by (unfold w; field; lra).
    nra. }
  split; intros _.
  - apply right_triangle_interior_is_geometric; assumption.
  - apply (proj2 (point_in_ring_right_triangle_iff x0 y0 x1 y1 p Hx01 Hy01)).
    split; [ lra | split; [ lra | exact Hhx ] ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions tri_interior_in_bounded_component.
Print Assumptions right_triangle_parity_characterises_interior.
