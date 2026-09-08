(* ============================================================================
   NetTopologySuite.Proofs.AtanDoubleAngle
   ----------------------------------------------------------------------------
   Shared one-argument atan identities used by the 508-a golden quarter
   (NurbsConicExact.v) and available to later Weierstrass / half-angle
   consumers.

   This is NOT atan2 (that is Atan2.v) and NOT golden-specific.  The
   load-bearing facts are the double-angle evaluations

     cos (2 · atan x) = (1 − x²) / (1 + x²)
     sin (2 · atan x) = (2 · x) / (1 + x²)

   plus the monotone/range lemmas needed for an explicit tan preimage
   on [0, π/4] (the reparam contract forbids IVT).

   Stdlib `atan` pulls Classical_Prop.classic; this file is Category C
   in docs/audit-exceptions.txt, same atan lineage as ArcParamBridge.v.
   No golden weights, no CurveSegment growth, no ADR-0004 remint.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra Ratan.
Local Open Scope R_scope.

Lemma atan_le : forall x y, x <= y -> atan x <= atan y.
Proof.
  intros x y [Hlt | Heq].
  - apply Rlt_le, atan_increasing. exact Hlt.
  - subst. apply Rle_refl.
Qed.

Lemma tan_PI4 : tan (PI / 4) = 1.
Proof. rewrite <- atan_1. apply tan_atan. Qed.

Lemma cos_atan_pos : forall x, 0 < cos (atan x).
Proof.
  intro x. rewrite cos_atan.
  apply Rdiv_lt_0_compat; [lra |].
  apply sqrt_lt_R0.
  apply Rplus_lt_le_0_compat; [lra | apply Rle_0_sqr].
Qed.

Lemma one_plus_sq_pos : forall x, 0 < 1 + x * x.
Proof.
  intro x. apply Rplus_lt_le_0_compat; [lra | apply Rle_0_sqr].
Qed.

Lemma one_plus_sq_neq : forall x, 1 + x * x <> 0.
Proof. intro x. apply Rgt_not_eq, one_plus_sq_pos. Qed.

Lemma one_plus_tan2 : forall a,
  cos a <> 0 ->
  1 + tan a * tan a = / (cos a * cos a).
Proof.
  intros a Hc.
  unfold tan, Rdiv.
  assert (Hc2 : cos a * cos a <> 0)
    by (apply Rmult_integral_contrapositive_currified; exact Hc).
  replace ((sin a * / cos a) * (sin a * / cos a))
    with (sin a * sin a * / (cos a * cos a))
    by (field; exact Hc).
  rewrite <- (Rinv_r (cos a * cos a) Hc2) at 1.
  rewrite <- Rmult_plus_distr_r.
  replace (cos a * cos a + sin a * sin a) with 1.
  2: { pose proof (sin2_cos2 a) as Hsc. unfold Rsqr in Hsc. lra. }
  rewrite Rmult_1_l. reflexivity.
Qed.

Lemma cos2_of_atan : forall x,
  cos (atan x) * cos (atan x) = / (1 + x * x).
Proof.
  intro x.
  assert (Hc : cos (atan x) <> 0) by (apply Rgt_not_eq, cos_atan_pos).
  pose proof (one_plus_tan2 (atan x) Hc) as Hsec.
  rewrite tan_atan in Hsec.
  apply (f_equal Rinv) in Hsec.
  rewrite Rinv_inv in Hsec.
  symmetry. exact Hsec.
Qed.

Lemma cos_2_atan : forall x,
  cos (2 * atan x) = (1 - x * x) / (1 + x * x).
Proof.
  intro x.
  set (a := atan x).
  assert (Htan : tan a = x) by (unfold a; apply tan_atan).
  assert (Hcos : 0 < cos a) by (unfold a; apply cos_atan_pos).
  assert (Hcos0 : cos a <> 0) by lra.
  rewrite cos_2a.
  replace (cos a * cos a - sin a * sin a)
    with (cos a * cos a * (1 - tan a * tan a))
    by (unfold tan; field; exact Hcos0).
  rewrite Htan.
  unfold a. rewrite cos2_of_atan.
  unfold Rdiv. ring.
Qed.

Lemma sin_2_atan : forall x,
  sin (2 * atan x) = (2 * x) / (1 + x * x).
Proof.
  intro x.
  set (a := atan x).
  assert (Htan : tan a = x) by (unfold a; apply tan_atan).
  assert (Hcos : 0 < cos a) by (unfold a; apply cos_atan_pos).
  assert (Hcos0 : cos a <> 0) by lra.
  rewrite sin_2a.
  replace (2 * sin a * cos a)
    with (2 * tan a * (cos a * cos a))
    by (unfold tan; field; exact Hcos0).
  rewrite Htan.
  unfold a. rewrite cos2_of_atan.
  unfold Rdiv. ring.
Qed.

Lemma tan_ge_0_on_0_PI4 : forall x,
  0 <= x -> x <= PI / 4 -> 0 <= tan x.
Proof.
  intros x Hx0 Hx1.
  destruct Hx0 as [Hlt | Heq].
  - rewrite <- tan_0. apply Rlt_le.
    pose proof PI_RGT_0.
    apply tan_increasing_1; lra.
  - subst. rewrite tan_0. lra.
Qed.

Lemma tan_le_1_on_0_PI4 : forall x,
  0 <= x -> x <= PI / 4 -> tan x <= 1.
Proof.
  intros x Hx0 Hx1.
  rewrite <- tan_PI4.
  destruct Hx1 as [Hlt | Heq].
  - apply Rlt_le.
    pose proof PI_RGT_0.
    apply tan_increasing_1; lra.
  - subst. apply Rle_refl.
Qed.

Print Assumptions cos_2_atan.
Print Assumptions sin_2_atan.
