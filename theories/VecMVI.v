(* ============================================================================
   NetTopologySuite.Proofs.VecMVI
   ----------------------------------------------------------------------------
   Vector mean-value inequality in the plane: if (fx, fy) has derivative
   (gx, gy) on [p, q] with |(gx, gy)| <= d, then
     |(fx, fy)(q)| <= |(fx, fy)(p)| + d (q - p).
   Project onto the unit direction of (fx, fy)(q) and apply
   RealMonotone.deriv_nonneg_incr: no MVT, no Rolle, no classic.
   First consumer: ClothoidArcSpline.v (arc spline vs clothoid).
   claimId: none.  3-axiom host.  No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra.
From Stdlib Require Import Ranalysis1.
From NTS.Proofs Require Import RealMonotone MetricSpeed DerivAlgebra.
Local Open Scope R_scope.

Lemma vec_unit_dot_le : forall wx wy x y,
  wx * wx + wy * wy = 1 ->
  wx * x + wy * y <= sqrt (x * x + y * y).
Proof.
  intros wx wy x y Hw.
  pose proof (dot_le_norms wx wy x y) as H.
  rewrite Hw, sqrt_1, Rmult_1_l in H. exact H.
Qed.

Lemma vec_mvi : forall (fx fy gx gy : R -> R) p q d,
  p <= q -> 0 <= d ->
  (forall t, p <= t <= q -> derivable_pt_lim fx t (gx t)) ->
  (forall t, p <= t <= q -> derivable_pt_lim fy t (gy t)) ->
  (forall t, p <= t <= q -> gx t * gx t + gy t * gy t <= d * d) ->
  sqrt (fx q * fx q + fy q * fy q)
    <= sqrt (fx p * fx p + fy p * fy p) + d * (q - p).
Proof.
  intros fx fy gx gy p q d Hpq Hd Hdx Hdy Hg.
  set (S := fx q * fx q + fy q * fy q).
  assert (HS : 0 <= S) by (unfold S; nra).
  set (Nq := sqrt S).
  destruct (Req_EM_T Nq 0) as [Hz|Hnz].
  - rewrite Hz. pose proof (sqrt_pos (fx p * fx p + fy p * fy p)). nra.
  - assert (HN0 : 0 <= Nq) by apply sqrt_pos.
    assert (HN : 0 < Nq) by lra.
    assert (HNN : Nq * Nq = S) by (unfold Nq; apply sqrt_sqrt; exact HS).
    set (wx := fx q / Nq). set (wy := fy q / Nq).
    assert (Hw : wx * wx + wy * wy = 1).
    { unfold wx, wy.
      replace (fx q / Nq * (fx q / Nq) + fy q / Nq * (fy q / Nq))
        with (S / (Nq * Nq)) by (unfold S; field; exact Hnz).
      rewrite HNN. unfold Rdiv. apply Rinv_r.
      rewrite <- HNN. apply Rgt_not_eq. nra. }
    set (g := fun t => d * t - (wx * fx t + wy * fy t)).
    set (g' := fun t => d - (wx * gx t + wy * gy t)).
    assert (Hgd : forall t, p <= t <= q -> derivable_pt_lim g t (g' t)).
    { intros t Ht. unfold g, g'.
      replace (d - (wx * gx t + wy * gy t))
        with (d * 1 - (wx * gx t + wy * gy t)) by ring.
      apply (d_minus (fun t => d * t)).
      - apply d_scal. apply derivable_pt_lim_id.
      - apply (d_plus (fun t => wx * fx t) (fun t => wy * fy t));
          apply d_scal.
        + apply Hdx. exact Ht.
        + apply Hdy. exact Ht. }
    assert (Hgn : forall t, p <= t <= q -> 0 <= g' t).
    { intros t Ht. unfold g'.
      pose proof (vec_unit_dot_le wx wy (gx t) (gy t) Hw) as Hc.
      assert (Hsq : sqrt (gx t * gx t + gy t * gy t) <= d).
      { rewrite <- (sqrt_square d) by exact Hd.
        apply sqrt_le_1_alt. apply Hg. exact Ht. }
      lra. }
    pose proof (deriv_nonneg_incr g g' p q p q Hgd Hgn
                  (Rle_refl p) Hpq (Rle_refl q)) as Hinc.
    unfold g in Hinc.
    assert (Hq : wx * fx q + wy * fy q = Nq).
    { unfold wx, wy.
      replace (fx q / Nq * fx q + fy q / Nq * fy q) with (S / Nq)
        by (unfold S; field; exact Hnz).
      rewrite <- HNN. field. exact Hnz. }
    pose proof (vec_unit_dot_le wx wy (fx p) (fy p) Hw) as Hp.
    fold S Nq. lra.
Qed.

Print Assumptions vec_unit_dot_le.
Print Assumptions vec_mvi.
