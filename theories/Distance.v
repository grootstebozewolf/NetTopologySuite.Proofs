(* ============================================================================
   NetTopologySuite.Proofs.Distance
   ----------------------------------------------------------------------------
   Foundational properties of Euclidean distance on the 2D plane.

   The optimisation tracked in JTS PR #1111 (and the gap noted in NTS epic #828
   for LineStringSnapper) replaces `distance(p, q) < tol` with
   `distance_sq(p, q) < tol * tol`, saving the square root call.

   The justification rests on a small theorem: on the non-negative reals,
   x ≤ y  iff  x² ≤ y².  Since Euclidean distance is non-negative, the squared
   form of any distance comparison against a non-negative threshold is
   equivalent.  This file proves it cleanly.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* A 2-D point is a pair of reals.                                            *)
(* -------------------------------------------------------------------------- *)

Record Point : Type := mkPoint { px : R; py : R }.

Definition dist_sq (p q : Point) : R :=
  (px p - px q) * (px p - px q) + (py p - py q) * (py p - py q).

Definition dist (p q : Point) : R := sqrt (dist_sq p q).

(* -------------------------------------------------------------------------- *)
(* Foundational properties of squared distance.                               *)
(* -------------------------------------------------------------------------- *)

Lemma sqr_nonneg : forall x : R, 0 <= x * x.
Proof.
  intros x. pose proof (Rle_0_sqr x) as H. unfold Rsqr in H. exact H.
Qed.

Lemma sqr_eq_zero : forall x : R, x * x = 0 -> x = 0.
Proof.
  intros x H. apply Rsqr_0_uniq. unfold Rsqr. exact H.
Qed.

Lemma dist_sq_nonneg : forall p q, 0 <= dist_sq p q.
Proof.
  intros p q. unfold dist_sq.
  pose proof (sqr_nonneg (px p - px q)) as Hx.
  pose proof (sqr_nonneg (py p - py q)) as Hy.
  lra.
Qed.

Lemma dist_sq_sym : forall p q, dist_sq p q = dist_sq q p.
Proof.
  intros p q. unfold dist_sq.
  ring.
Qed.

Lemma dist_sq_zero_iff_eq : forall p q,
  dist_sq p q = 0 <-> (px p = px q /\ py p = py q).
Proof.
  intros p q. unfold dist_sq. split.
  - intros H.
    pose proof (sqr_nonneg (px p - px q)) as Hx.
    pose proof (sqr_nonneg (py p - py q)) as Hy.
    assert (Hxz : (px p - px q) * (px p - px q) = 0) by lra.
    assert (Hyz : (py p - py q) * (py p - py q) = 0) by lra.
    apply sqr_eq_zero in Hxz.
    apply sqr_eq_zero in Hyz.
    split; lra.
  - intros [Hx Hy]. rewrite Hx, Hy. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* The headline theorem: on non-negative reals, the square is monotone.       *)
(* This is the formal justification for replacing distance comparisons with   *)
(* squared-distance comparisons.                                              *)
(* -------------------------------------------------------------------------- *)

Lemma sq_monotone_nonneg : forall x y, 0 <= x -> 0 <= y ->
  (x <= y <-> x * x <= y * y).
Proof.
  intros x y Hx Hy.
  split; intros H.
  - apply Rmult_le_compat; lra.
  - destruct (Rle_or_lt x y) as [Hle | Hlt].
    + exact Hle.
    + exfalso.
      assert (y * y < x * x).
      { apply Rmult_le_0_lt_compat; lra. }
      lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* The result NTS would cite: comparing a distance to a non-negative          *)
(* threshold is equivalent to comparing squared distance to the squared       *)
(* threshold.                                                                 *)
(*                                                                            *)
(*   For all points p q and threshold t with t >= 0,                          *)
(*     dist(p, q) <= t   iff   dist_sq(p, q) <= t * t.                        *)
(*                                                                            *)
(* This is the formal "no, the optimisation cannot lie" guarantee.            *)
(* -------------------------------------------------------------------------- *)

Theorem dist_le_iff_dist_sq_le : forall p q t,
  0 <= t -> (dist p q <= t <-> dist_sq p q <= t * t).
Proof.
  intros p q t Ht.
  unfold dist.
  pose proof (dist_sq_nonneg p q) as Hd.
  pose proof (sqrt_pos (dist_sq p q)) as Hsd.
  rewrite (sq_monotone_nonneg (sqrt (dist_sq p q)) t Hsd Ht).
  rewrite sqrt_sqrt by exact Hd.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Distance (with sqrt) properties.                                           *)
(* -------------------------------------------------------------------------- *)

Lemma dist_nonneg : forall p q, 0 <= dist p q.
Proof.
  intros p q. unfold dist. apply sqrt_pos.
Qed.

Lemma dist_refl : forall p, dist p p = 0.
Proof.
  intros p. unfold dist.
  replace (dist_sq p p) with 0.
  - apply sqrt_0.
  - unfold dist_sq. ring.
Qed.

Lemma dist_sym : forall p q, dist p q = dist q p.
Proof.
  intros p q. unfold dist. rewrite (dist_sq_sym p q). reflexivity.
Qed.

Theorem dist_eq_zero_iff : forall p q,
  dist p q = 0 <-> (px p = px q /\ py p = py q).
Proof.
  intros p q. unfold dist. split.
  - intros H.
    apply sqrt_eq_0 in H; [| apply dist_sq_nonneg].
    apply dist_sq_zero_iff_eq. exact H.
  - intros Hxy.
    replace (dist_sq p q) with 0.
    + apply sqrt_0.
    + symmetry. apply dist_sq_zero_iff_eq. exact Hxy.
Qed.

(* -------------------------------------------------------------------------- *)
(* Squared-distance properties (translation invariance, scaling, strictness). *)
(* -------------------------------------------------------------------------- *)

Definition pt_translate (p : Point) (vx vy : R) : Point :=
  mkPoint (px p + vx) (py p + vy).

Lemma dist_sq_translation_invariant : forall p q vx vy,
  dist_sq (pt_translate p vx vy) (pt_translate q vx vy) = dist_sq p q.
Proof.
  intros p q vx vy. unfold dist_sq, pt_translate. simpl. ring.
Qed.

Definition pt_scale (c : R) (p : Point) : Point :=
  mkPoint (c * px p) (c * py p).

Lemma dist_sq_scale : forall c p q,
  dist_sq (pt_scale c p) (pt_scale c q) = c * c * dist_sq p q.
Proof.
  intros c p q. unfold dist_sq, pt_scale. simpl. ring.
Qed.

Lemma dist_sq_pos_iff_distinct : forall p q,
  0 < dist_sq p q <-> ~ (px p = px q /\ py p = py q).
Proof.
  intros p q. split.
  - intros H Hxy. apply dist_sq_zero_iff_eq in Hxy. lra.
  - intros H.
    pose proof (dist_sq_nonneg p q) as Hnn.
    destruct (Req_dec (dist_sq p q) 0) as [Heq | Hne].
    + exfalso. apply H. apply dist_sq_zero_iff_eq. exact Heq.
    + lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit. The proofs above rely only on the constructions of the   *)
(* standard library's classical real arithmetic.  Run with `make` or          *)
(* `rocq compile theories/Distance.v` and inspect the `Print Assumptions`     *)
(* output: any axiom not part of the classical Reals stdlib is a red flag.    *)
(* -------------------------------------------------------------------------- *)

Print Assumptions dist_le_iff_dist_sq_le.
