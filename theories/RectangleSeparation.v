(* ============================================================================
   NetTopologySuite.Proofs.RectangleSeparation
   ----------------------------------------------------------------------------
   Special-case JCT, slice 2d: the rectangle separation, UNCONDITIONALLY.

   Discharges `RectangleJCT.rect_confines` for strict-interior points, hence
   the FULL unconditional rectangle instance of `parity_characterises_
   interior_cont`:

     point_in_ring p (rect_ring x0 y0 x1 y1)  <->  geometric_interior_cont p ...
       for x0<x1, y0<y1 and a strict-interior point p.

   Method (IVT, not a 2D sup/clopen argument).  Encode box membership by ONE
   continuous scalar field

     box_min pt := Rmin (Rmin (px pt - x0) (x1 - px pt))
                        (Rmin (py pt - y0) (y1 - py pt))

   which is  > 0 strictly inside the open box,  = 0 exactly on the box boundary
   (= the edge skeleton `ring_image`, by RectangleJCT's characterisation), and
   < 0 strictly outside.  A complement-connecting path avoids the boundary, so
   `box_min` along it is never 0; by the intermediate value theorem a
   continuous function that starts positive and never vanishes stays positive.
   Hence the path's endpoint is strictly inside -- the rectangle "separates" the
   plane.  The 2D "go-around" difficulty dissolves because `box_min < 0`
   captures EVERY exterior point (some slab is negative) and `= 0` captures
   EXACTLY the boundary.

   Pure-R; three-axiom (uses `functional_extensionality` only to rewrite Rmin to
   its closed form -- already in the allowlist).  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (claude-opus-4-8)
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From Stdlib Require Import Ranalysis Ranalysis5.
From Stdlib Require Import FunctionalExtensionality.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam.
From NTS.Proofs Require Import RectangleJCT.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Rmin arithmetic.                                                        *)
(* -------------------------------------------------------------------------- *)

Lemma Rmin_pos_iff : forall a b, 0 < Rmin a b <-> 0 < a /\ 0 < b.
Proof.
  intros a b. unfold Rmin. destruct (Rle_dec a b) as [r | r].
  - split; [ intro H; split; lra | intros [? ?]; lra ].
  - apply Rnot_le_lt in r. split; [ intro H; split; lra | intros [? ?]; lra ].
Qed.

Lemma Rmin_eq_0_inv : forall a b,
  Rmin a b = 0 -> 0 <= a /\ 0 <= b /\ (a = 0 \/ b = 0).
Proof.
  intros a b H. unfold Rmin in H. destruct (Rle_dec a b) as [r | r].
  - split; [ lra | split; [ lra | left; exact H ] ].
  - apply Rnot_le_lt in r. split; [ lra | split; [ lra | right; exact H ] ].
Qed.

Lemma Rmin_eq_formula : forall a b, Rmin a b = / 2 * (a + b - Rabs (a - b)).
Proof.
  intros a b. unfold Rmin. destruct (Rle_dec a b) as [r | r].
  - rewrite Rabs_left1 by lra. lra.
  - apply Rnot_le_lt in r. rewrite Rabs_right by lra. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The scalar box field and its sign characterisation.                     *)
(* -------------------------------------------------------------------------- *)

Definition box_min (x0 y0 x1 y1 : R) (pt : Point) : R :=
  Rmin (Rmin (px pt - x0) (x1 - px pt)) (Rmin (py pt - y0) (y1 - py pt)).

Lemma box_min_pos_iff : forall x0 y0 x1 y1 pt,
  0 < box_min x0 y0 x1 y1 pt <-> (x0 < px pt < x1 /\ y0 < py pt < y1).
Proof.
  intros x0 y0 x1 y1 pt. unfold box_min.
  rewrite !Rmin_pos_iff. lra.
Qed.

Lemma box_min_zero_imp_boundary : forall x0 y0 x1 y1 pt,
  box_min x0 y0 x1 y1 pt = 0 -> on_box_boundary x0 y0 x1 y1 pt.
Proof.
  intros x0 y0 x1 y1 pt H. unfold box_min in H.
  destruct (Rmin_eq_0_inv _ _ H) as [HA [HB Hor]].
  assert (Hx0 : x0 <= px pt) by (pose proof (Rmin_l (px pt - x0) (x1 - px pt)); lra).
  assert (Hx1 : px pt <= x1) by (pose proof (Rmin_r (px pt - x0) (x1 - px pt)); lra).
  assert (Hy0 : y0 <= py pt) by (pose proof (Rmin_l (py pt - y0) (y1 - py pt)); lra).
  assert (Hy1 : py pt <= y1) by (pose proof (Rmin_r (py pt - y0) (y1 - py pt)); lra).
  destruct Hor as [Hxz | Hyz].
  - destruct (Rmin_eq_0_inv _ _ Hxz) as [_ [_ [Hs1 | Hs2]]].
    + right; split; [ left; lra | lra ].
    + right; split; [ right; lra | lra ].
  - destruct (Rmin_eq_0_inv _ _ Hyz) as [_ [_ [Hs3 | Hs4]]].
    + left; split; [ left; lra | lra ].
    + left; split; [ right; lra | lra ].
Qed.

(* Off the edge skeleton, box_min is nonzero. *)
Lemma box_min_nonzero_off_skeleton : forall x0 y0 x1 y1 pt,
  x0 < x1 -> y0 < y1 ->
  ring_complement (rect_ring x0 y0 x1 y1) pt ->
  box_min x0 y0 x1 y1 pt <> 0.
Proof.
  intros x0 y0 x1 y1 pt Hx01 Hy01 Hcomp Hz.
  apply Hcomp. apply box_boundary_in_ring_image; [ exact Hx01 | exact Hy01 | ].
  apply box_min_zero_imp_boundary; exact Hz.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Continuity of Rmin and of box_min along a continuous path.              *)
(* -------------------------------------------------------------------------- *)

Lemma continuity_pt_Rmin : forall (u v : R -> R) t,
  continuity_pt u t -> continuity_pt v t ->
  continuity_pt (fun x => Rmin (u x) (v x)) t.
Proof.
  intros u v t Hu Hv.
  assert (Hext : (fun x => Rmin (u x) (v x))
               = (fun x => / 2 * (u x + v x - Rabs (u x - v x)))).
  { apply functional_extensionality; intro x. apply Rmin_eq_formula. }
  rewrite Hext.
  apply continuity_pt_scal.
  apply continuity_pt_minus.
  - apply continuity_pt_plus; assumption.
  - apply (continuity_pt_comp (fun x => u x - v x) Rabs).
    + apply continuity_pt_minus; assumption.
    + apply Rcontinuity_abs.
Qed.

Lemma continuity_pt_box_min_path : forall x0 y0 x1 y1 (g : R -> Point) t,
  continuity_pt (fun s => px (g s)) t ->
  continuity_pt (fun s => py (g s)) t ->
  continuity_pt (fun s => box_min x0 y0 x1 y1 (g s)) t.
Proof.
  intros x0 y0 x1 y1 g t Hu Hv. unfold box_min.
  apply continuity_pt_Rmin.
  - apply continuity_pt_Rmin.
    + apply continuity_pt_minus; [ exact Hu | apply continuity_pt_const; intros ? ?; reflexivity ].
    + apply continuity_pt_minus; [ apply continuity_pt_const; intros ? ?; reflexivity | exact Hu ].
  - apply continuity_pt_Rmin.
    + apply continuity_pt_minus; [ exact Hv | apply continuity_pt_const; intros ? ?; reflexivity ].
    + apply continuity_pt_minus; [ apply continuity_pt_const; intros ? ?; reflexivity | exact Hv ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The separation: a complement-connected point stays in the closed box.   *)
(* -------------------------------------------------------------------------- *)

Theorem rect_confines_of_interior : forall x0 y0 x1 y1 p,
  x0 < x1 -> y0 < y1 ->
  x0 < px p < x1 -> y0 < py p < y1 ->
  rect_confines x0 y0 x1 y1 p.
Proof.
  intros x0 y0 x1 y1 p Hx01 Hy01 Hxp Hyp q Hconn.
  destruct Hconn as [g [[Hcx Hcy] [Hg0 [Hg1 Hcompl]]]].
  set (F := fun t => box_min x0 y0 x1 y1 (g t)).
  assert (HcontF : forall a, continuity_pt F a)
    by (intro a; apply continuity_pt_box_min_path; [ apply Hcx | apply Hcy ]).
  (* F is positive at 0 (the interior start point) *)
  assert (HF0 : 0 < F 0).
  { unfold F. rewrite Hg0. apply box_min_pos_iff. split; assumption. }
  (* F never vanishes on [0,1] (the path avoids the skeleton) *)
  assert (Hnz : forall t, 0 <= t <= 1 -> F t <> 0)
    by (intros t Ht; apply box_min_nonzero_off_skeleton;
        [ exact Hx01 | exact Hy01 | apply Hcompl; exact Ht ]).
  (* Hence F 1 > 0: no sign change is possible without a zero (IVT). *)
  assert (HF1 : 0 < F 1).
  { destruct (Rtotal_order (F 1) 0) as [Hlt | [Heq | Hgt]].
    - (* F 1 < 0: IVT on -F gives a zero in [0,1], contradiction *)
      assert (Hc' : forall a, 0 <= a <= 1 -> continuity_pt (fun t => - F t) a)
        by (intros a _; apply continuity_pt_opp; apply HcontF).
      destruct (IVT_interv (fun t => - F t) 0 1 Hc' Rlt_0_1) as [z [Hz Hzeq]].
      + simpl; lra.
      + simpl; lra.
      + exfalso. apply (Hnz z Hz). lra.
    - exfalso. apply (Hnz 1 ltac:(lra)). exact Heq.
    - exact Hgt. }
  (* F 1 > 0 means q = g 1 is strictly inside; weaken to the closed box. *)
  assert (Hopen : x0 < px (g 1) < x1 /\ y0 < py (g 1) < y1)
    by (apply box_min_pos_iff; exact HF1).
  rewrite Hg1 in Hopen. destruct Hopen as [[? ?] [? ?]].
  split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Unconditional rectangle instance of parity_characterises_interior_cont. *)
(* -------------------------------------------------------------------------- *)

Theorem rect_interior_is_geometric : forall x0 y0 x1 y1 p,
  x0 < x1 -> y0 < y1 ->
  x0 < px p < x1 -> y0 < py p < y1 ->
  geometric_interior_cont p (rect_ring x0 y0 x1 y1).
Proof.
  intros x0 y0 x1 y1 p Hx01 Hy01 Hxp Hyp.
  apply rect_open_box_geometric_interior_of_confines; try assumption.
  apply rect_confines_of_interior; assumption.
Qed.

Theorem rect_parity_characterises_interior : forall x0 y0 x1 y1 p,
  x0 < x1 -> y0 < y1 ->
  x0 < px p < x1 -> y0 < py p < y1 ->
  (point_in_ring p (rect_ring x0 y0 x1 y1)
     <-> geometric_interior_cont p (rect_ring x0 y0 x1 y1)).
Proof.
  intros x0 y0 x1 y1 p Hx01 Hy01 Hxp Hyp.
  apply rect_parity_characterises_interior_open; try assumption.
  apply rect_confines_of_interior; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions rect_confines_of_interior.
Print Assumptions rect_parity_characterises_interior.
