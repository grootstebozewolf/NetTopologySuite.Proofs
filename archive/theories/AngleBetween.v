(* ============================================================================
   NetTopologySuite.Proofs.AngleBetween
   ----------------------------------------------------------------------------
   Option-A arc primitives, foundation 2/N: the SIGNED angle between two planar
   vectors, built on `atan2` (theories/Atan2.v).  This is the robust "central
   angle / sweep" primitive issue #64 asks for (ask #2): the JTS-faithful
   atan2-of-(cross, dot) formula, whose sign encodes the orientation (CCW
   positive) -- exactly what disambiguates the short vs long arc once the
   mid-point fixes the traversal direction.

     angle_between u v := atan2 (cross u v) (dot u v),
       cross u v = ux*vy - uy*vx,   dot u v = ux*vx + uy*vy.

   Headlines (for nonzero u, v):
     cos (angle_between u v) = dot / (|u| * |v|),
     sin (angle_between u v) = cross / (|u| * |v|),
   i.e. angle_between is the signed angle theta with the usual
   dot = |u||v|cos theta, cross = |u||v|sin theta.  Proof is immediate from the
   `cos_atan2`/`sin_atan2` characterisations plus the Lagrange identity
   dot^2 + cross^2 = |u|^2 |v|^2 (a pure `ring` fact) -- no angle wrap-around
   reasoning.  Also: `atan2_range` (principal range (-PI, PI]) and the derived
   `angle_between_range`.  Refs #64.

   Inherits `Classical_Prop.classic` from `atan` (see docs/audit-exceptions.txt
   entry for theories/Atan2.v).  No Admitted.
   ========================================================================== *)

Require Import Reals.
Require Import Lra.
From NTS.Proofs Require Import Atan2.
Local Open Scope R_scope.

(* Sum of two squares is strictly positive unless both terms vanish. *)
Lemma sum_sq_pos : forall a b : R, ~ (a = 0 /\ b = 0) -> 0 < a * a + b * b.
Proof.
  intros a b H. destruct (Req_dec a 0) as [Ha|Ha].
  - subst a. assert (Hb : b <> 0) by (intro Hb0; apply H; split; [ reflexivity | exact Hb0 ]).
    destruct (Rdichotomy b 0 Hb); nra.
  - destruct (Rdichotomy a 0 Ha); nra.
Qed.

(* Sign of a quotient with negative denominator (for the atan2 range branches). *)
Lemma div_nonpos_of_neg_denom : forall x y : R, x < 0 -> 0 <= y -> y / x <= 0.
Proof.
  intros x y Hx Hy. unfold Rdiv.
  assert (/ x < 0) by (apply Rinv_lt_0_compat; exact Hx). nra.
Qed.
Lemma div_pos_of_neg_neg : forall x y : R, x < 0 -> y < 0 -> 0 < y / x.
Proof.
  intros x y Hx Hy. unfold Rdiv.
  assert (/ x < 0) by (apply Rinv_lt_0_compat; exact Hx). nra.
Qed.

(* atan is monotone through 0. *)
Lemma atan_le_0 : forall t : R, t <= 0 -> atan t <= 0.
Proof.
  intros t Ht. destruct (Req_dec t 0) as [E|E].
  - subst; rewrite atan_0; lra.
  - rewrite <- atan_0. apply Rlt_le, atan_increasing. lra.
Qed.
Lemma atan_gt_0 : forall t : R, 0 < t -> 0 < atan t.
Proof.
  intros t Ht. rewrite <- atan_0. apply atan_increasing. lra.
Qed.

(* ---- atan2 lands in the principal range (-PI, PI]. --------------------- *)
Theorem atan2_range : forall x y : R, ~ (x = 0 /\ y = 0) ->
  - PI < atan2 y x <= PI.
Proof.
  intros x y H. pose proof PI_RGT_0 as HPI. unfold atan2.
  destruct (Rlt_dec 0 x) as [Hx|Hx].
  - pose proof (atan_bound (y / x)); lra.
  - destruct (Rlt_dec x 0) as [Hx2|Hx2].
    + destruct (Rle_dec 0 y) as [Hy|Hy].
      * pose proof (atan_bound (y / x)).
        assert (atan (y / x) <= 0) by (apply atan_le_0, div_nonpos_of_neg_denom; lra).
        lra.
      * pose proof (atan_bound (y / x)).
        assert (0 < atan (y / x)) by (apply atan_gt_0, div_pos_of_neg_neg; lra).
        lra.
    + assert (x = 0) by lra. subst x.
      destruct (Rlt_dec 0 y) as [Hy|Hy].
      * lra.
      * destruct (Rlt_dec y 0) as [Hy2|Hy2].
        -- lra.
        -- exfalso. apply H. split; [ reflexivity | lra ].
Qed.

(* ---- The signed angle between two planar vectors. ---------------------- *)
Definition angle_between (ux uy vx vy : R) : R :=
  atan2 (ux * vy - uy * vx) (ux * vx + uy * vy).

(* The (dot, cross) pair is away from the origin when both vectors are. *)
Lemma dotcross_nonzero : forall ux uy vx vy : R,
  ~ (ux = 0 /\ uy = 0) -> ~ (vx = 0 /\ vy = 0) ->
  ~ (ux * vx + uy * vy = 0 /\ ux * vy - uy * vx = 0).
Proof.
  intros ux uy vx vy Hu Hv.
  assert (Hu' : 0 < ux * ux + uy * uy) by (apply sum_sq_pos; exact Hu).
  assert (Hv' : 0 < vx * vx + vy * vy) by (apply sum_sq_pos; exact Hv).
  intros [Hd Hc].
  assert (Lag : (ux * vx + uy * vy) * (ux * vx + uy * vy)
              + (ux * vy - uy * vx) * (ux * vy - uy * vx)
              = (ux * ux + uy * uy) * (vx * vx + vy * vy)) by ring.
  rewrite Hd, Hc in Lag. nra.
Qed.

(* ---- Headline 1: cosine of the signed angle = dot / (|u||v|). ---------- *)
Theorem cos_angle_between : forall ux uy vx vy : R,
  ~ (ux = 0 /\ uy = 0) -> ~ (vx = 0 /\ vy = 0) ->
  cos (angle_between ux uy vx vy)
    = (ux * vx + uy * vy)
      / (sqrt (ux * ux + uy * uy) * sqrt (vx * vx + vy * vy)).
Proof.
  intros ux uy vx vy Hu Hv. unfold angle_between.
  assert (Hu' : 0 < ux * ux + uy * uy) by (apply sum_sq_pos; exact Hu).
  assert (Hv' : 0 < vx * vx + vy * vy) by (apply sum_sq_pos; exact Hv).
  rewrite cos_atan2 by (apply dotcross_nonzero; assumption).
  assert (E : (ux * vx + uy * vy) * (ux * vx + uy * vy)
            + (ux * vy - uy * vx) * (ux * vy - uy * vx)
            = (ux * ux + uy * uy) * (vx * vx + vy * vy)) by ring.
  rewrite E, sqrt_mult by lra. reflexivity.
Qed.

(* ---- Headline 2: sine of the signed angle = cross / (|u||v|). ---------- *)
Theorem sin_angle_between : forall ux uy vx vy : R,
  ~ (ux = 0 /\ uy = 0) -> ~ (vx = 0 /\ vy = 0) ->
  sin (angle_between ux uy vx vy)
    = (ux * vy - uy * vx)
      / (sqrt (ux * ux + uy * uy) * sqrt (vx * vx + vy * vy)).
Proof.
  intros ux uy vx vy Hu Hv. unfold angle_between.
  assert (Hu' : 0 < ux * ux + uy * uy) by (apply sum_sq_pos; exact Hu).
  assert (Hv' : 0 < vx * vx + vy * vy) by (apply sum_sq_pos; exact Hv).
  rewrite sin_atan2 by (apply dotcross_nonzero; assumption).
  assert (E : (ux * vx + uy * vy) * (ux * vx + uy * vy)
            + (ux * vy - uy * vx) * (ux * vy - uy * vx)
            = (ux * ux + uy * uy) * (vx * vx + vy * vy)) by ring.
  rewrite E, sqrt_mult by lra. reflexivity.
Qed.

(* ---- The signed angle is a principal angle in (-PI, PI]. --------------- *)
Corollary angle_between_range : forall ux uy vx vy : R,
  ~ (ux = 0 /\ uy = 0) -> ~ (vx = 0 /\ vy = 0) ->
  - PI < angle_between ux uy vx vy <= PI.
Proof.
  intros ux uy vx vy Hu Hv. unfold angle_between.
  apply atan2_range. apply dotcross_nonzero; assumption.
Qed.

Print Assumptions cos_angle_between.
Print Assumptions sin_angle_between.
