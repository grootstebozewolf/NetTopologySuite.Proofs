(* ============================================================================
   NetTopologySuite.Proofs.RelateIntDetBound
   ----------------------------------------------------------------------------
   Integer-coordinate range bound for the orientation determinant, grounding
   the robust DE-9IM / relate approach of Romanschek, Clemen & Huhnt,
   "A Novel Robust Approach for Computing DE-9IM Matrices Based on Space
   Partition and Integer Coordinates", ISPRS Int. J. Geo-Inf. 2021, 10, 715
   (doi:10.3390/ijgi10110715), Section 3.2.

   That approach computes spatial relations exactly by carrying coordinates as
   integers and never rounding; the only arithmetic that can overflow is the
   3-point orientation determinant (their Equation (2))

       det(a,b,c) = (bx - ax)(cy - ay) - (cx - ax)(by - ay)

   which is signed twice the area of triangle a-b-c.  The paper's central
   feasibility argument (Section 3.2, Equations (4),(5),(8)) is: if every
   coordinate fits in a bounded integer window, the determinant fits in the
   next-wider native integer type, so the whole pipeline is overflow-free and
   therefore exact.  This module mechanises that argument.

   Two regimes are established:

     1. 32-bit coordinate regime (proven on the nose).  With non-negative
        coordinates in [0, 2^31 - 1] -- the regime after the paper's scale +
        translate-to-bounding-box-minimum step (Equation (6), which makes all
        coordinates >= 0) -- the determinant is representable in signed 64-bit:
        |det| <= 2^63 - 1.  This is the paper's "32 bit integers can be used
        for the coordinates" statement.

     2. 64-bit coordinate regime (paper's tight cmax, Equations (5),(8)).  The
        paper pushes the coordinate window to cmax = floor(sqrt(2^63 - 1)) =
        3,037,000,499 using the *geometric* bound |det| <= cmax^2 (the area of
        a triangle inside a cmax x cmax box is at most cmax^2 / 2, Equation (4),
        Figure 3).  The universal geometric bound `idet_abs_le_sq` licenses the
        full [0, cmax] window; `cmax` bracketing and +/- cmax^2 witnesses show
        the range [-cmax^2, cmax^2] is tight.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

(* -------------------------------------------------------------------------- *)
(* The orientation determinant on integer coordinates (paper Equation (2)).   *)
(* -------------------------------------------------------------------------- *)

Definition idet (ax ay bx by_ cx cy : Z) : Z :=
  (bx - ax) * (cy - ay) - (cx - ax) * (by_ - ay).

(* -------------------------------------------------------------------------- *)
(* Algebraic range bound.                                                     *)
(*                                                                            *)
(* For non-negative coordinates in [0,c], coordinate differences lie in       *)
(* [-c,c], each product in [-c^2,c^2], and the determinant (a difference of    *)
(* two such products) in [-2c^2, 2c^2].  The tighter geometric bound           *)
(* |det| <= c^2 (Equation (4)) is proved below as `idet_abs_le_sq`.             *)
(* -------------------------------------------------------------------------- *)

Lemma idet_abs_le_2sq :
  forall c ax ay bx by_ cx cy,
    0 <= ax <= c -> 0 <= ay <= c -> 0 <= bx <= c -> 0 <= by_ <= c ->
    0 <= cx <= c -> 0 <= cy <= c ->
    Z.abs (idet ax ay bx by_ cx cy) <= 2 * (c * c).
Proof.
  intros c ax ay bx by_ cx cy Hax Hay Hbx Hby Hcx Hcy.
  unfold idet. apply Z.abs_le. split; nia.
Qed.

(* -------------------------------------------------------------------------- *)
(* Geometric range bound (paper Equation (4): |det| <= c^2).                   *)
(*                                                                            *)
(* `idet` is affine in each coordinate on [0,c]; |.| therefore attains its    *)
(* maximum at a box corner.  Corner case analysis (64 vertices) closes the    *)
(* bound; six one-coordinate reductions transport it to the full box.           *)
(* -------------------------------------------------------------------------- *)

Lemma Zabs_in_interval_le_max_abs_endpoints :
  forall x a b, a <= x -> x <= b -> Z.abs x <= Z.max (Z.abs a) (Z.abs b).
Proof.
  intros x a b Ha Hb.
  destruct (Z.le_ge_cases 0 a) as [Ha0 | Ha0].
  - destruct (Z.le_ge_cases 0 b) as [Hb0 | Hb0]; apply Z.abs_le; split; lia.
  - destruct (Z.le_ge_cases 0 b) as [Hb0 | Hb0]; apply Z.abs_le; split; lia.
Qed.

Lemma Zabs_affine_le_endpoint_max :
  forall p q c x,
    0 <= c -> 0 <= x -> x <= c ->
    Z.abs (p * x + q) <= Z.max (Z.abs q) (Z.abs (p * c + q)).
Proof.
  intros p q c x Hc0 Hx0 Hxc.
  destruct (Z.le_ge_cases p 0) as [Hp | Hp].
  - assert (H1 : p * c + q <= p * x + q) by nia.
    assert (H2 : p * x + q <= q) by nia.
    assert (H := Zabs_in_interval_le_max_abs_endpoints (p * x + q) (p * c + q) q H1 H2).
    rewrite Z.max_comm in H. exact H.
  - assert (H1 : q <= p * x + q) by nia.
    assert (H2 : p * x + q <= p * c + q) by nia.
    exact (Zabs_in_interval_le_max_abs_endpoints (p * x + q) q (p * c + q) H1 H2).
Qed.

Lemma Zmax_le_both : forall a b m, a <= m -> b <= m -> Z.max a b <= m.
Proof. intros. lia. Qed.

Lemma idet_affine_ax : forall ax ay bx by_ cx cy,
  idet ax ay bx by_ cx cy =
    (by_ - cy) * ax + (bx * cy - bx * ay - cx * by_ + cx * ay).
Proof. intros. unfold idet. ring. Qed.

Lemma idet_affine_ay : forall ax ay bx by_ cx cy,
  idet ax ay bx by_ cx cy =
    (cx - bx) * ay + (bx * cy - ax * cy - cx * by_ + ax * by_).
Proof. intros. unfold idet. ring. Qed.

Lemma idet_affine_bx : forall ax ay bx by_ cx cy,
  idet ax ay bx by_ cx cy =
    (cy - ay) * bx + (- ax * cy - cx * by_ + cx * ay + ax * by_).
Proof. intros. unfold idet. ring. Qed.

Lemma idet_affine_by : forall ax ay bx by_ cx cy,
  idet ax ay bx by_ cx cy =
    (ax - cx) * by_ + (bx * cy - bx * ay - ax * cy + cx * ay).
Proof. intros. unfold idet. ring. Qed.

Lemma idet_affine_cx : forall ax ay bx by_ cx cy,
  idet ax ay bx by_ cx cy =
    (ay - by_) * cx + (bx * cy - bx * ay - ax * cy + ax * by_).
Proof. intros. unfold idet. ring. Qed.

Lemma idet_affine_cy : forall ax ay bx by_ cx cy,
  idet ax ay bx by_ cx cy =
    (bx - ax) * cy + (- bx * ay - cx * by_ + cx * ay + ax * by_).
Proof. intros. unfold idet. ring. Qed.

Lemma idet_abs_affine_reduce :
  forall c x p q lo hi,
    0 <= c -> 0 <= x -> x <= c ->
    lo = q -> hi = p * c + q ->
    Z.abs (p * x + q) <= Z.max (Z.abs lo) (Z.abs hi).
Proof.
  intros c x p q lo hi Hc0 Hx0 Hxc Hlo Hhi. subst lo hi.
  apply Zabs_affine_le_endpoint_max; lia.
Qed.

Lemma idet_abs_reduce_ax :
  forall c ax ay bx by_ cx cy,
    0 <= c ->
    0 <= ax <= c -> 0 <= ay <= c -> 0 <= bx <= c -> 0 <= by_ <= c ->
    0 <= cx <= c -> 0 <= cy <= c ->
    Z.abs (idet ax ay bx by_ cx cy) <=
      Z.max (Z.abs (idet 0 ay bx by_ cx cy)) (Z.abs (idet c ay bx by_ cx cy)).
Proof.
  intros c ax ay bx by_ cx cy Hc0 Hax Hay Hbx Hby Hcx Hcy.
  pose (p := by_ - cy).
  pose (q := bx * cy - bx * ay - cx * by_ + cx * ay).
  rewrite idet_affine_ax.
  replace (idet 0 ay bx by_ cx cy) with q by (unfold idet, p, q; ring).
  replace (idet c ay bx by_ cx cy) with (p * c + q) by (unfold idet, p, q; ring).
  eapply idet_abs_affine_reduce; eauto; lia.
Qed.

Lemma idet_abs_reduce_ay :
  forall c ax ay bx by_ cx cy,
    0 <= c ->
    0 <= ax <= c -> 0 <= ay <= c -> 0 <= bx <= c -> 0 <= by_ <= c ->
    0 <= cx <= c -> 0 <= cy <= c ->
    Z.abs (idet ax ay bx by_ cx cy) <=
      Z.max (Z.abs (idet ax 0 bx by_ cx cy)) (Z.abs (idet ax c bx by_ cx cy)).
Proof.
  intros c ax ay bx by_ cx cy Hc0 Hax Hay Hbx Hby Hcx Hcy.
  pose (p := cx - bx).
  pose (q := bx * cy - ax * cy - cx * by_ + ax * by_).
  rewrite idet_affine_ay.
  replace (idet ax 0 bx by_ cx cy) with q by (unfold idet, p, q; ring).
  replace (idet ax c bx by_ cx cy) with (p * c + q) by (unfold idet, p, q; ring).
  eapply idet_abs_affine_reduce; eauto; lia.
Qed.

Lemma idet_abs_reduce_bx :
  forall c ax ay bx by_ cx cy,
    0 <= c ->
    0 <= ax <= c -> 0 <= ay <= c -> 0 <= bx <= c -> 0 <= by_ <= c ->
    0 <= cx <= c -> 0 <= cy <= c ->
    Z.abs (idet ax ay bx by_ cx cy) <=
      Z.max (Z.abs (idet ax ay 0 by_ cx cy)) (Z.abs (idet ax ay c by_ cx cy)).
Proof.
  intros c ax ay bx by_ cx cy Hc0 Hax Hay Hbx Hby Hcx Hcy.
  pose (p := cy - ay).
  pose (q := - ax * cy - cx * by_ + cx * ay + ax * by_).
  rewrite idet_affine_bx.
  replace (idet ax ay 0 by_ cx cy) with q by (unfold idet, p, q; ring).
  replace (idet ax ay c by_ cx cy) with (p * c + q) by (unfold idet, p, q; ring).
  eapply idet_abs_affine_reduce; eauto; lia.
Qed.

Lemma idet_abs_reduce_by :
  forall c ax ay bx by_ cx cy,
    0 <= c ->
    0 <= ax <= c -> 0 <= ay <= c -> 0 <= bx <= c -> 0 <= by_ <= c ->
    0 <= cx <= c -> 0 <= cy <= c ->
    Z.abs (idet ax ay bx by_ cx cy) <=
      Z.max (Z.abs (idet ax ay bx 0 cx cy)) (Z.abs (idet ax ay bx c cx cy)).
Proof.
  intros c ax ay bx by_ cx cy Hc0 Hax Hay Hbx Hby Hcx Hcy.
  pose (p := ax - cx).
  pose (q := bx * cy - bx * ay - ax * cy + cx * ay).
  rewrite idet_affine_by.
  replace (idet ax ay bx 0 cx cy) with q by (unfold idet, p, q; ring).
  replace (idet ax ay bx c cx cy) with (p * c + q) by (unfold idet, p, q; ring).
  eapply idet_abs_affine_reduce; eauto; lia.
Qed.

Lemma idet_abs_reduce_cx :
  forall c ax ay bx by_ cx cy,
    0 <= c ->
    0 <= ax <= c -> 0 <= ay <= c -> 0 <= bx <= c -> 0 <= by_ <= c ->
    0 <= cx <= c -> 0 <= cy <= c ->
    Z.abs (idet ax ay bx by_ cx cy) <=
      Z.max (Z.abs (idet ax ay bx by_ 0 cy)) (Z.abs (idet ax ay bx by_ c cy)).
Proof.
  intros c ax ay bx by_ cx cy Hc0 Hax Hay Hbx Hby Hcx Hcy.
  pose (p := ay - by_).
  pose (q := bx * cy - bx * ay - ax * cy + ax * by_).
  rewrite idet_affine_cx.
  replace (idet ax ay bx by_ 0 cy) with q by (unfold idet, p, q; ring).
  replace (idet ax ay bx by_ c cy) with (p * c + q) by (unfold idet, p, q; ring).
  eapply idet_abs_affine_reduce; eauto; lia.
Qed.

Lemma idet_abs_reduce_cy :
  forall c ax ay bx by_ cx cy,
    0 <= c ->
    0 <= ax <= c -> 0 <= ay <= c -> 0 <= bx <= c -> 0 <= by_ <= c ->
    0 <= cx <= c -> 0 <= cy <= c ->
    Z.abs (idet ax ay bx by_ cx cy) <=
      Z.max (Z.abs (idet ax ay bx by_ cx 0)) (Z.abs (idet ax ay bx by_ cx c)).
Proof.
  intros c ax ay bx by_ cx cy Hc0 Hax Hay Hbx Hby Hcx Hcy.
  pose (p := bx - ax).
  pose (q := - bx * ay - cx * by_ + cx * ay + ax * by_).
  rewrite idet_affine_cy.
  replace (idet ax ay bx by_ cx 0) with q by (unfold idet, p, q; ring).
  replace (idet ax ay bx by_ cx c) with (p * c + q) by (unfold idet, p, q; ring).
  eapply idet_abs_affine_reduce; eauto; lia.
Qed.

Lemma coord0_le_c : forall c, 0 <= c -> 0 <= 0 <= c.
Proof. intros. split; [reflexivity | lia]. Qed.

Lemma coordc_le_c : forall c, 0 <= c -> 0 <= c <= c.
Proof. intros. split; [lia | reflexivity]. Qed.

Lemma idet_abs_le_sq_corners :
  forall c ax ay bx by_ cx cy,
    0 <= c ->
    (ax = 0 \/ ax = c) -> (ay = 0 \/ ay = c) -> (bx = 0 \/ bx = c) ->
    (by_ = 0 \/ by_ = c) -> (cx = 0 \/ cx = c) -> (cy = 0 \/ cy = c) ->
    Z.abs (idet ax ay bx by_ cx cy) <= c * c.
Proof.
  intros c ax ay bx by_ cx cy Hc0.
  intros Hax Hay Hbx Hby Hcx Hcy.
  unfold idet.
  repeat (destruct Hax as [-> | ->]);
  repeat (destruct Hay as [-> | ->]);
  repeat (destruct Hbx as [-> | ->]);
  repeat (destruct Hby as [-> | ->]);
  repeat (destruct Hcx as [-> | ->]);
  repeat (destruct Hcy as [-> | ->]);
  apply Z.abs_le; split; nia.
Qed.
(* Corner transport: one affine reduction per axis, then max over endpoints. *)
Ltac idet_corner_side kind :=
  match eval cbv in kind with
  | 1 => left; reflexivity
  | _ => right; reflexivity
  end.

Ltac idet_corners6 kax kay kbx kby kcx kcy :=
  match goal with
  | Hc0 : ?Hc0T |- _ =>
      apply idet_abs_le_sq_corners;
        [ exact Hc0
        | idet_corner_side kax
        | idet_corner_side kay
        | idet_corner_side kbx
        | idet_corner_side kby
        | idet_corner_side kcx
        | idet_corner_side kcy
        ]
  end.

Lemma idet_abs_le_sq :
  forall c ax ay bx by_ cx cy,
    0 <= c ->
    0 <= ax <= c -> 0 <= ay <= c -> 0 <= bx <= c -> 0 <= by_ <= c ->
    0 <= cx <= c -> 0 <= cy <= c ->
    Z.abs (idet ax ay bx by_ cx cy) <= c * c.
Proof.
  intros c ax ay bx by_ cx cy Hc0 Hax Hay Hbx Hby Hcx Hcy.
  pose proof (coord0_le_c c Hc0) as Hax0.
  pose proof (coordc_le_c c Hc0) as Haxc.
  pose proof (coord0_le_c c Hc0) as Hay0.
  pose proof (coordc_le_c c Hc0) as Hayc.
  pose proof (coord0_le_c c Hc0) as Hbx0.
  pose proof (coordc_le_c c Hc0) as Hbxc.
  pose proof (coord0_le_c c Hc0) as Hby0.
  pose proof (coordc_le_c c Hc0) as Hbyc.
  pose proof (coord0_le_c c Hc0) as Hcx0.
  pose proof (coordc_le_c c Hc0) as Hcxc.
  pose proof (coord0_le_c c Hc0) as Hcy0.
  pose proof (coordc_le_c c Hc0) as Hcyc.
  eapply Z.le_trans.
  { exact (idet_abs_reduce_ax c ax ay bx by_ cx cy Hc0 Hax Hay Hbx Hby Hcx Hcy). }
  { apply Zmax_le_both.
    eapply Z.le_trans.
    { exact (idet_abs_reduce_ay c 0 ay bx by_ cx cy Hc0 Hax0 Hay Hbx Hby Hcx Hcy). }
    { apply Zmax_le_both.
      eapply Z.le_trans.
      { exact (idet_abs_reduce_bx c 0 0 bx by_ cx cy Hc0 Hax0 Hay0 Hbx Hby Hcx Hcy). }
      { apply Zmax_le_both.
        eapply Z.le_trans.
        { exact (idet_abs_reduce_by c 0 0 0 by_ cx cy Hc0 Hax0 Hay0 Hbx0 Hby Hcx Hcy). }
        { apply Zmax_le_both.
          eapply Z.le_trans.
          { exact (idet_abs_reduce_cx c 0 0 0 0 cx cy Hc0 Hax0 Hay0 Hbx0 Hby0 Hcx Hcy). }
          { apply Zmax_le_both.
            eapply Z.le_trans.
            { exact (idet_abs_reduce_cy c 0 0 0 0 0 cy Hc0 Hax0 Hay0 Hbx0 Hby0 Hcx0 Hcy). }
            { apply Zmax_le_both.
              idet_corners6 1 1 1 1 1 1.
              idet_corners6 1 1 1 1 1 2.
            }
            eapply Z.le_trans.
            { exact (idet_abs_reduce_cy c 0 0 0 0 c cy Hc0 Hax0 Hay0 Hbx0 Hby0 Hcxc Hcy). }
            { apply Zmax_le_both.
              idet_corners6 1 1 1 1 2 1.
              idet_corners6 1 1 1 1 2 2.
            }
          }
          eapply Z.le_trans.
          { exact (idet_abs_reduce_cx c 0 0 0 c cx cy Hc0 Hax0 Hay0 Hbx0 Hbyc Hcx Hcy). }
          { apply Zmax_le_both.
            eapply Z.le_trans.
            { exact (idet_abs_reduce_cy c 0 0 0 c 0 cy Hc0 Hax0 Hay0 Hbx0 Hbyc Hcx0 Hcy). }
            { apply Zmax_le_both.
              idet_corners6 1 1 1 2 1 1.
              idet_corners6 1 1 1 2 1 2.
            }
            eapply Z.le_trans.
            { exact (idet_abs_reduce_cy c 0 0 0 c c cy Hc0 Hax0 Hay0 Hbx0 Hbyc Hcxc Hcy). }
            { apply Zmax_le_both.
              idet_corners6 1 1 1 2 2 1.
              idet_corners6 1 1 1 2 2 2.
            }
          }
        }
        eapply Z.le_trans.
        { exact (idet_abs_reduce_by c 0 0 c by_ cx cy Hc0 Hax0 Hay0 Hbxc Hby Hcx Hcy). }
        { apply Zmax_le_both.
          eapply Z.le_trans.
          { exact (idet_abs_reduce_cx c 0 0 c 0 cx cy Hc0 Hax0 Hay0 Hbxc Hby0 Hcx Hcy). }
          { apply Zmax_le_both.
            eapply Z.le_trans.
            { exact (idet_abs_reduce_cy c 0 0 c 0 0 cy Hc0 Hax0 Hay0 Hbxc Hby0 Hcx0 Hcy). }
            { apply Zmax_le_both.
              idet_corners6 1 1 2 1 1 1.
              idet_corners6 1 1 2 1 1 2.
            }
            eapply Z.le_trans.
            { exact (idet_abs_reduce_cy c 0 0 c 0 c cy Hc0 Hax0 Hay0 Hbxc Hby0 Hcxc Hcy). }
            { apply Zmax_le_both.
              idet_corners6 1 1 2 1 2 1.
              idet_corners6 1 1 2 1 2 2.
            }
          }
          eapply Z.le_trans.
          { exact (idet_abs_reduce_cx c 0 0 c c cx cy Hc0 Hax0 Hay0 Hbxc Hbyc Hcx Hcy). }
          { apply Zmax_le_both.
            eapply Z.le_trans.
            { exact (idet_abs_reduce_cy c 0 0 c c 0 cy Hc0 Hax0 Hay0 Hbxc Hbyc Hcx0 Hcy). }
            { apply Zmax_le_both.
              idet_corners6 1 1 2 2 1 1.
              idet_corners6 1 1 2 2 1 2.
            }
            eapply Z.le_trans.
            { exact (idet_abs_reduce_cy c 0 0 c c c cy Hc0 Hax0 Hay0 Hbxc Hbyc Hcxc Hcy). }
            { apply Zmax_le_both.
              idet_corners6 1 1 2 2 2 1.
              idet_corners6 1 1 2 2 2 2.
            }
          }
        }
      }
      eapply Z.le_trans.
      { exact (idet_abs_reduce_bx c 0 c bx by_ cx cy Hc0 Hax0 Hayc Hbx Hby Hcx Hcy). }
      { apply Zmax_le_both.
        eapply Z.le_trans.
        { exact (idet_abs_reduce_by c 0 c 0 by_ cx cy Hc0 Hax0 Hayc Hbx0 Hby Hcx Hcy). }
        { apply Zmax_le_both.
          eapply Z.le_trans.
          { exact (idet_abs_reduce_cx c 0 c 0 0 cx cy Hc0 Hax0 Hayc Hbx0 Hby0 Hcx Hcy). }
          { apply Zmax_le_both.
            eapply Z.le_trans.
            { exact (idet_abs_reduce_cy c 0 c 0 0 0 cy Hc0 Hax0 Hayc Hbx0 Hby0 Hcx0 Hcy). }
            { apply Zmax_le_both.
              idet_corners6 1 2 1 1 1 1.
              idet_corners6 1 2 1 1 1 2.
            }
            eapply Z.le_trans.
            { exact (idet_abs_reduce_cy c 0 c 0 0 c cy Hc0 Hax0 Hayc Hbx0 Hby0 Hcxc Hcy). }
            { apply Zmax_le_both.
              idet_corners6 1 2 1 1 2 1.
              idet_corners6 1 2 1 1 2 2.
            }
          }
          eapply Z.le_trans.
          { exact (idet_abs_reduce_cx c 0 c 0 c cx cy Hc0 Hax0 Hayc Hbx0 Hbyc Hcx Hcy). }
          { apply Zmax_le_both.
            eapply Z.le_trans.
            { exact (idet_abs_reduce_cy c 0 c 0 c 0 cy Hc0 Hax0 Hayc Hbx0 Hbyc Hcx0 Hcy). }
            { apply Zmax_le_both.
              idet_corners6 1 2 1 2 1 1.
              idet_corners6 1 2 1 2 1 2.
            }
            eapply Z.le_trans.
            { exact (idet_abs_reduce_cy c 0 c 0 c c cy Hc0 Hax0 Hayc Hbx0 Hbyc Hcxc Hcy). }
            { apply Zmax_le_both.
              idet_corners6 1 2 1 2 2 1.
              idet_corners6 1 2 1 2 2 2.
            }
          }
        }
        eapply Z.le_trans.
        { exact (idet_abs_reduce_by c 0 c c by_ cx cy Hc0 Hax0 Hayc Hbxc Hby Hcx Hcy). }
        { apply Zmax_le_both.
          eapply Z.le_trans.
          { exact (idet_abs_reduce_cx c 0 c c 0 cx cy Hc0 Hax0 Hayc Hbxc Hby0 Hcx Hcy). }
          { apply Zmax_le_both.
            eapply Z.le_trans.
            { exact (idet_abs_reduce_cy c 0 c c 0 0 cy Hc0 Hax0 Hayc Hbxc Hby0 Hcx0 Hcy). }
            { apply Zmax_le_both.
              idet_corners6 1 2 2 1 1 1.
              idet_corners6 1 2 2 1 1 2.
            }
            eapply Z.le_trans.
            { exact (idet_abs_reduce_cy c 0 c c 0 c cy Hc0 Hax0 Hayc Hbxc Hby0 Hcxc Hcy). }
            { apply Zmax_le_both.
              idet_corners6 1 2 2 1 2 1.
              idet_corners6 1 2 2 1 2 2.
            }
          }
          eapply Z.le_trans.
          { exact (idet_abs_reduce_cx c 0 c c c cx cy Hc0 Hax0 Hayc Hbxc Hbyc Hcx Hcy). }
          { apply Zmax_le_both.
            eapply Z.le_trans.
            { exact (idet_abs_reduce_cy c 0 c c c 0 cy Hc0 Hax0 Hayc Hbxc Hbyc Hcx0 Hcy). }
            { apply Zmax_le_both.
              idet_corners6 1 2 2 2 1 1.
              idet_corners6 1 2 2 2 1 2.
            }
            eapply Z.le_trans.
            { exact (idet_abs_reduce_cy c 0 c c c c cy Hc0 Hax0 Hayc Hbxc Hbyc Hcxc Hcy). }
            { apply Zmax_le_both.
              idet_corners6 1 2 2 2 2 1.
              idet_corners6 1 2 2 2 2 2.
            }
          }
        }
      }
    }
    eapply Z.le_trans.
    { exact (idet_abs_reduce_ay c c ay bx by_ cx cy Hc0 Haxc Hay Hbx Hby Hcx Hcy). }
    { apply Zmax_le_both.
      eapply Z.le_trans.
      { exact (idet_abs_reduce_bx c c 0 bx by_ cx cy Hc0 Haxc Hay0 Hbx Hby Hcx Hcy). }
      { apply Zmax_le_both.
        eapply Z.le_trans.
        { exact (idet_abs_reduce_by c c 0 0 by_ cx cy Hc0 Haxc Hay0 Hbx0 Hby Hcx Hcy). }
        { apply Zmax_le_both.
          eapply Z.le_trans.
          { exact (idet_abs_reduce_cx c c 0 0 0 cx cy Hc0 Haxc Hay0 Hbx0 Hby0 Hcx Hcy). }
          { apply Zmax_le_both.
            eapply Z.le_trans.
            { exact (idet_abs_reduce_cy c c 0 0 0 0 cy Hc0 Haxc Hay0 Hbx0 Hby0 Hcx0 Hcy). }
            { apply Zmax_le_both.
              idet_corners6 2 1 1 1 1 1.
              idet_corners6 2 1 1 1 1 2.
            }
            eapply Z.le_trans.
            { exact (idet_abs_reduce_cy c c 0 0 0 c cy Hc0 Haxc Hay0 Hbx0 Hby0 Hcxc Hcy). }
            { apply Zmax_le_both.
              idet_corners6 2 1 1 1 2 1.
              idet_corners6 2 1 1 1 2 2.
            }
          }
          eapply Z.le_trans.
          { exact (idet_abs_reduce_cx c c 0 0 c cx cy Hc0 Haxc Hay0 Hbx0 Hbyc Hcx Hcy). }
          { apply Zmax_le_both.
            eapply Z.le_trans.
            { exact (idet_abs_reduce_cy c c 0 0 c 0 cy Hc0 Haxc Hay0 Hbx0 Hbyc Hcx0 Hcy). }
            { apply Zmax_le_both.
              idet_corners6 2 1 1 2 1 1.
              idet_corners6 2 1 1 2 1 2.
            }
            eapply Z.le_trans.
            { exact (idet_abs_reduce_cy c c 0 0 c c cy Hc0 Haxc Hay0 Hbx0 Hbyc Hcxc Hcy). }
            { apply Zmax_le_both.
              idet_corners6 2 1 1 2 2 1.
              idet_corners6 2 1 1 2 2 2.
            }
          }
        }
        eapply Z.le_trans.
        { exact (idet_abs_reduce_by c c 0 c by_ cx cy Hc0 Haxc Hay0 Hbxc Hby Hcx Hcy). }
        { apply Zmax_le_both.
          eapply Z.le_trans.
          { exact (idet_abs_reduce_cx c c 0 c 0 cx cy Hc0 Haxc Hay0 Hbxc Hby0 Hcx Hcy). }
          { apply Zmax_le_both.
            eapply Z.le_trans.
            { exact (idet_abs_reduce_cy c c 0 c 0 0 cy Hc0 Haxc Hay0 Hbxc Hby0 Hcx0 Hcy). }
            { apply Zmax_le_both.
              idet_corners6 2 1 2 1 1 1.
              idet_corners6 2 1 2 1 1 2.
            }
            eapply Z.le_trans.
            { exact (idet_abs_reduce_cy c c 0 c 0 c cy Hc0 Haxc Hay0 Hbxc Hby0 Hcxc Hcy). }
            { apply Zmax_le_both.
              idet_corners6 2 1 2 1 2 1.
              idet_corners6 2 1 2 1 2 2.
            }
          }
          eapply Z.le_trans.
          { exact (idet_abs_reduce_cx c c 0 c c cx cy Hc0 Haxc Hay0 Hbxc Hbyc Hcx Hcy). }
          { apply Zmax_le_both.
            eapply Z.le_trans.
            { exact (idet_abs_reduce_cy c c 0 c c 0 cy Hc0 Haxc Hay0 Hbxc Hbyc Hcx0 Hcy). }
            { apply Zmax_le_both.
              idet_corners6 2 1 2 2 1 1.
              idet_corners6 2 1 2 2 1 2.
            }
            eapply Z.le_trans.
            { exact (idet_abs_reduce_cy c c 0 c c c cy Hc0 Haxc Hay0 Hbxc Hbyc Hcxc Hcy). }
            { apply Zmax_le_both.
              idet_corners6 2 1 2 2 2 1.
              idet_corners6 2 1 2 2 2 2.
            }
          }
        }
      }
      eapply Z.le_trans.
      { exact (idet_abs_reduce_bx c c c bx by_ cx cy Hc0 Haxc Hayc Hbx Hby Hcx Hcy). }
      { apply Zmax_le_both.
        eapply Z.le_trans.
        { exact (idet_abs_reduce_by c c c 0 by_ cx cy Hc0 Haxc Hayc Hbx0 Hby Hcx Hcy). }
        { apply Zmax_le_both.
          eapply Z.le_trans.
          { exact (idet_abs_reduce_cx c c c 0 0 cx cy Hc0 Haxc Hayc Hbx0 Hby0 Hcx Hcy). }
          { apply Zmax_le_both.
            eapply Z.le_trans.
            { exact (idet_abs_reduce_cy c c c 0 0 0 cy Hc0 Haxc Hayc Hbx0 Hby0 Hcx0 Hcy). }
            { apply Zmax_le_both.
              idet_corners6 2 2 1 1 1 1.
              idet_corners6 2 2 1 1 1 2.
            }
            eapply Z.le_trans.
            { exact (idet_abs_reduce_cy c c c 0 0 c cy Hc0 Haxc Hayc Hbx0 Hby0 Hcxc Hcy). }
            { apply Zmax_le_both.
              idet_corners6 2 2 1 1 2 1.
              idet_corners6 2 2 1 1 2 2.
            }
          }
          eapply Z.le_trans.
          { exact (idet_abs_reduce_cx c c c 0 c cx cy Hc0 Haxc Hayc Hbx0 Hbyc Hcx Hcy). }
          { apply Zmax_le_both.
            eapply Z.le_trans.
            { exact (idet_abs_reduce_cy c c c 0 c 0 cy Hc0 Haxc Hayc Hbx0 Hbyc Hcx0 Hcy). }
            { apply Zmax_le_both.
              idet_corners6 2 2 1 2 1 1.
              idet_corners6 2 2 1 2 1 2.
            }
            eapply Z.le_trans.
            { exact (idet_abs_reduce_cy c c c 0 c c cy Hc0 Haxc Hayc Hbx0 Hbyc Hcxc Hcy). }
            { apply Zmax_le_both.
              idet_corners6 2 2 1 2 2 1.
              idet_corners6 2 2 1 2 2 2.
            }
          }
        }
        eapply Z.le_trans.
        { exact (idet_abs_reduce_by c c c c by_ cx cy Hc0 Haxc Hayc Hbxc Hby Hcx Hcy). }
        { apply Zmax_le_both.
          eapply Z.le_trans.
          { exact (idet_abs_reduce_cx c c c c 0 cx cy Hc0 Haxc Hayc Hbxc Hby0 Hcx Hcy). }
          { apply Zmax_le_both.
            eapply Z.le_trans.
            { exact (idet_abs_reduce_cy c c c c 0 0 cy Hc0 Haxc Hayc Hbxc Hby0 Hcx0 Hcy). }
            { apply Zmax_le_both.
              idet_corners6 2 2 2 1 1 1.
              idet_corners6 2 2 2 1 1 2.
            }
            eapply Z.le_trans.
            { exact (idet_abs_reduce_cy c c c c 0 c cy Hc0 Haxc Hayc Hbxc Hby0 Hcxc Hcy). }
            { apply Zmax_le_both.
              idet_corners6 2 2 2 1 2 1.
              idet_corners6 2 2 2 1 2 2.
            }
          }
          eapply Z.le_trans.
          { exact (idet_abs_reduce_cx c c c c c cx cy Hc0 Haxc Hayc Hbxc Hbyc Hcx Hcy). }
          { apply Zmax_le_both.
            eapply Z.le_trans.
            { exact (idet_abs_reduce_cy c c c c c 0 cy Hc0 Haxc Hayc Hbxc Hbyc Hcx0 Hcy). }
            { apply Zmax_le_both.
              idet_corners6 2 2 2 2 1 1.
              idet_corners6 2 2 2 2 1 2.
            }
            eapply Z.le_trans.
            { exact (idet_abs_reduce_cy c c c c c c cy Hc0 Haxc Hayc Hbxc Hbyc Hcxc Hcy). }
            { apply Zmax_le_both.
              idet_corners6 2 2 2 2 2 1.
              idet_corners6 2 2 2 2 2 2.
            }
          }
        }
      }
    }
  }
Qed.

(* Regime 1: 32-bit coordinates => 64-bit determinant is overflow-free.        *)
(* -------------------------------------------------------------------------- *)

Definition i32max : Z := 2 ^ 31 - 1.

Theorem idet_fits_int64_for_int32_coords :
  forall ax ay bx by_ cx cy,
    0 <= ax <= i32max -> 0 <= ay <= i32max -> 0 <= bx <= i32max ->
    0 <= by_ <= i32max -> 0 <= cx <= i32max -> 0 <= cy <= i32max ->
    - (2 ^ 63 - 1) <= idet ax ay bx by_ cx cy <= 2 ^ 63 - 1.
Proof.
  intros ax ay bx by_ cx cy Hax Hay Hbx Hby Hcx Hcy.
  assert (H := idet_abs_le_2sq i32max ax ay bx by_ cx cy
                 Hax Hay Hbx Hby Hcx Hcy).
  apply Z.abs_le in H. unfold i32max in H. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* Regime 2: the paper's tight cmax (Equations (5),(8)).                       *)
(* -------------------------------------------------------------------------- *)

Definition cmax : Z := 3037000499.

Theorem cmax_sq_le_int64 : cmax * cmax <= 2 ^ 63 - 1.
Proof. unfold cmax. lia. Qed.

Theorem cmax_succ_sq_gt_int64 : (cmax + 1) * (cmax + 1) > 2 ^ 63 - 1.
Proof. unfold cmax. lia. Qed.

Theorem idet_max_witness : idet 0 0 cmax 0 0 cmax = cmax * cmax.
Proof. unfold idet, cmax. ring. Qed.

Theorem idet_min_witness : idet 0 0 0 cmax cmax 0 = - (cmax * cmax).
Proof. unfold idet, cmax. ring. Qed.

Corollary idet_range_tight_at_int64_edge :
  idet 0 0 cmax 0 0 cmax = cmax * cmax /\
  cmax * cmax <= 2 ^ 63 - 1 /\
  (cmax + 1) * (cmax + 1) > 2 ^ 63 - 1.
Proof.
  split; [exact idet_max_witness | ].
  split; [exact cmax_sq_le_int64 | exact cmax_succ_sq_gt_int64].
Qed.

Theorem idet_fits_int64_for_cmax_coords :
  forall ax ay bx by_ cx cy,
    0 <= ax <= cmax -> 0 <= ay <= cmax -> 0 <= bx <= cmax ->
    0 <= by_ <= cmax -> 0 <= cx <= cmax -> 0 <= cy <= cmax ->
    - (2 ^ 63 - 1) <= idet ax ay bx by_ cx cy <= 2 ^ 63 - 1.
Proof.
  intros ax ay bx by_ cx cy Hax Hay Hbx Hby Hcx Hcy.
  assert (Hc0 : 0 <= cmax) by (unfold cmax; lia).
  assert (H := idet_abs_le_sq cmax ax ay bx by_ cx cy Hc0 Hax Hay Hbx Hby Hcx Hcy).
  apply Z.abs_le in H. unfold cmax in H. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                               *)
(* -------------------------------------------------------------------------- *)

Print Assumptions idet_abs_le_sq.
Print Assumptions idet_fits_int64_for_int32_coords.
Print Assumptions idet_fits_int64_for_cmax_coords.
Print Assumptions cmax_sq_le_int64.
Print Assumptions cmax_succ_sq_gt_int64.
Print Assumptions idet_range_tight_at_int64_edge.
