(* ============================================================================
   NetTopologySuite.Proofs.ClothoidShearLaw
   ----------------------------------------------------------------------------
   Proof half of claimId `cloth-linear-law-iff-similarity` (statements
   pinned in ClothoidShearLawStmt.v).  A placed clothoid M c (det M <> 0)
   has curvature linear in placed arc length on a window of positive
   length iff M is a similarity (M^T M = lam^2 I).

   Notation along the host arc length s: v = (x, y) the unit tangent,
   v' = k J v with k = k0 + g s (g <> 0), Q = |M v|^2, P = M v . M J v,
   W = |M J v|^2, T = |M|_F^2, D = det M.  Then Q' = 2 k P,
   P' = k (W - Q), Q + W = T and Q W - P^2 = D^2 (qf_wf_tf, qf_lagrange).
   The placed curvature is D k / Q^(3/2).

   Only if (shear_core).  From kappa_P = a + b sg, sg' = sqrt Q:
     E   : D g Q - 3 D k^2 P - b Q^3 = 0        (one derivative, law_E)
     E'  : k Y = 0,  Y = -4 D g P - 3 D k^2 (W - Q) - 6 b Q^2 P
                                             (E is locally 0, law_dE)
   Eliminating k^2 with P Y - (W - Q) E leaves a quartic in Q alone,
     zq Q = 4 b Q^4 - 5 b T Q^3 + 6 (g D + b D^2) Q^2 - 5 g D T Q + 4 g D^3,
   whose constant term 4 g D^3 is nonzero (zq_of_EY).  On a subwindow with
   k <> 0, Q is continuous; if it took two values it would take five
   (IVT), all roots of zq, so zq = 0 (poly4_zero), which it is not.  So Q
   is constant there, Q' = 2 k P = 0 gives P = 0, Y = 0 gives W = Q, and
   P = 0, W = Q at one unit vector force M^T M = lam^2 I (conformal_of_PW).
   No integral, no analytic continuation: derivatives of explicit
   functions, IVT and a five-root count.

   If (conformal_law).  Q = lam^2 is constant, sg = lam s, and the law is
   (D k0 / lam^3, D g / lam^4).

   claimId: cloth-linear-law-iff-similarity.
   3-axiom host. No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
   ========================================================================== *)

From Stdlib Require Import Reals Lra Ranalysis1 Rsqrt_def Sqrt_reg.
From NTS.Proofs Require Import Distance SignedCurvature SheetHenClothoidCore
  ClothoidNorm2 ClothoidTraversal ClothoidPlacement ClothoidShearLawStmt.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Derivative rules in the shape used below.                              *)
(* -------------------------------------------------------------------------- *)

Lemma dpl_eq : forall f s l1 l2,
  derivable_pt_lim f s l1 -> l1 = l2 -> derivable_pt_lim f s l2.
Proof. intros f s l1 l2 H E. subst. exact H. Qed.

Lemma d_const : forall a s, derivable_pt_lim (fun _ => a) s 0.
Proof. intros. apply derivable_pt_lim_const. Qed.

Lemma d_plus : forall f g s df dg,
  derivable_pt_lim f s df -> derivable_pt_lim g s dg ->
  derivable_pt_lim (fun u => f u + g u) s (df + dg).
Proof.
  intros. apply derivable_pt_lim_ext with (f := plus_fct f g);
    [intro; reflexivity | apply derivable_pt_lim_plus; assumption].
Qed.

Lemma d_minus : forall f g s df dg,
  derivable_pt_lim f s df -> derivable_pt_lim g s dg ->
  derivable_pt_lim (fun u => f u - g u) s (df - dg).
Proof.
  intros. apply derivable_pt_lim_ext with (f := minus_fct f g);
    [intro; reflexivity | apply derivable_pt_lim_minus; assumption].
Qed.

Lemma d_mul : forall f g s df dg,
  derivable_pt_lim f s df -> derivable_pt_lim g s dg ->
  derivable_pt_lim (fun u => f u * g u) s (df * g s + f s * dg).
Proof.
  intros. apply derivable_pt_lim_ext with (f := mult_fct f g);
    [intro; reflexivity | apply derivable_pt_lim_mult; assumption].
Qed.

Lemma d_scal : forall a f s df,
  derivable_pt_lim f s df -> derivable_pt_lim (fun u => a * f u) s (a * df).
Proof.
  intros. apply derivable_pt_lim_ext with (f := mult_real_fct a f);
    [intro; reflexivity | apply derivable_pt_lim_scal; assumption].
Qed.

Lemma d_lin2 : forall a b f g s df dg,
  derivable_pt_lim f s df -> derivable_pt_lim g s dg ->
  derivable_pt_lim (fun u => a * f u + b * g u) s (a * df + b * dg).
Proof. intros. apply d_plus; apply d_scal; assumption. Qed.

Lemma dpl_locally_zero : forall f s s1 s2 l,
  s1 < s < s2 -> (forall z, s1 < z < s2 -> f z = 0) ->
  derivable_pt_lim f s l -> l = 0.
Proof.
  intros f s s1 s2 l Hs Hz Hd.
  apply (uniqueness_limite f s); [exact Hd|].
  apply (derivable_pt_lim_locally_ext (fun _ => 0) f s s1 s2 0 Hs).
  - intros z Hz'. symmetry. apply Hz. exact Hz'.
  - apply d_const.
Qed.

Lemma dpl_locally_const : forall f s s1 s2 C l,
  s1 < s < s2 -> (forall z, s1 < z < s2 -> f z = C) ->
  derivable_pt_lim f s l -> l = 0.
Proof.
  intros f s s1 s2 C l Hs Hz Hd.
  apply (dpl_locally_zero (fun u => f u - C) s s1 s2 l Hs).
  - intros z Hz'. rewrite (Hz z Hz'). ring.
  - apply (dpl_eq _ _ (l - 0)); [apply d_minus; [exact Hd | apply d_const] | ring].
Qed.

Lemma mul_nz_zero : forall a b, a <> 0 -> a * b = 0 -> b = 0.
Proof.
  intros a b Ha H. destruct (Rmult_integral a b H) as [E|E]; [contradiction | exact E].
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  A quartic with five distinct roots is zero.                            *)
(* -------------------------------------------------------------------------- *)

Lemma poly1_zero : forall c1 c0 r1 r2, r1 <> r2 ->
  c1 * r1 + c0 = 0 -> c1 * r2 + c0 = 0 -> c1 = 0 /\ c0 = 0.
Proof.
  intros c1 c0 r1 r2 H12 E1 E2.
  assert (H : (r1 - r2) * c1 = 0) by lra.
  apply mul_nz_zero in H; [|lra].
  subst. split; [reflexivity | lra].
Qed.

Lemma poly2_zero : forall c2 c1 c0 r1 r2 r3,
  r1 <> r2 -> r1 <> r3 -> r2 <> r3 ->
  c2 * (r1 * r1) + c1 * r1 + c0 = 0 ->
  c2 * (r2 * r2) + c1 * r2 + c0 = 0 ->
  c2 * (r3 * r3) + c1 * r3 + c0 = 0 ->
  c2 = 0 /\ c1 = 0 /\ c0 = 0.
Proof.
  intros c2 c1 c0 r1 r2 r3 H12 H13 H23 E1 E2 E3.
  assert (Q2 : c2 * r2 + (c2 * r1 + c1) = 0).
  { apply (mul_nz_zero (r2 - r1)); [lra|].
    replace ((r2 - r1) * (c2 * r2 + (c2 * r1 + c1)))
      with ((c2 * (r2 * r2) + c1 * r2 + c0) - (c2 * (r1 * r1) + c1 * r1 + c0)) by ring.
    lra. }
  assert (Q3 : c2 * r3 + (c2 * r1 + c1) = 0).
  { apply (mul_nz_zero (r3 - r1)); [lra|].
    replace ((r3 - r1) * (c2 * r3 + (c2 * r1 + c1)))
      with ((c2 * (r3 * r3) + c1 * r3 + c0) - (c2 * (r1 * r1) + c1 * r1 + c0)) by ring.
    lra. }
  destruct (poly1_zero c2 (c2 * r1 + c1) r2 r3 H23 Q2 Q3) as [Z2 Z1].
  subst c2. split; [reflexivity|]. split; [lra|].
  assert (c1 = 0) by lra. subst c1. lra.
Qed.

Lemma poly3_zero : forall c3 c2 c1 c0 r1 r2 r3 r4,
  r1 <> r2 -> r1 <> r3 -> r1 <> r4 -> r2 <> r3 -> r2 <> r4 -> r3 <> r4 ->
  (forall r, r = r1 \/ r = r2 \/ r = r3 \/ r = r4 ->
     c3 * (r * r * r) + c2 * (r * r) + c1 * r + c0 = 0) ->
  c3 = 0 /\ c2 = 0 /\ c1 = 0 /\ c0 = 0.
Proof.
  intros c3 c2 c1 c0 r1 r2 r3 r4 H12 H13 H14 H23 H24 H34 E.
  assert (Q : forall r, r <> r1 -> c3 * (r * r * r) + c2 * (r * r) + c1 * r + c0 = 0 ->
            (c3) * (r * r) + (c3 * r1 + c2) * r + (c3 * (r1 * r1) + c2 * r1 + c1) = 0).
  { intros r Hr Er. apply (mul_nz_zero (r - r1)); [lra|].
    pose proof (E r1 (or_introl eq_refl)) as E1.
    replace ((r - r1) * (c3 * (r * r) + (c3 * r1 + c2) * r
                          + (c3 * (r1 * r1) + c2 * r1 + c1)))
      with ((c3 * (r * r * r) + c2 * (r * r) + c1 * r + c0)
            - (c3 * (r1 * r1 * r1) + c2 * (r1 * r1) + c1 * r1 + c0)) by ring.
    lra. }
  destruct (poly2_zero c3 (c3 * r1 + c2) (c3 * (r1 * r1) + c2 * r1 + c1) r2 r3 r4
              H23 H24 H34
              (Q r2 (not_eq_sym H12) (E r2 (or_intror (or_introl eq_refl))))
              (Q r3 (not_eq_sym H13) (E r3 (or_intror (or_intror (or_introl eq_refl)))))
              (Q r4 (not_eq_sym H14) (E r4 (or_intror (or_intror (or_intror eq_refl))))))
    as (Z3 & Z2 & Z1).
  subst c3. assert (c2 = 0) by lra. subst c2. assert (c1 = 0) by lra. subst c1.
  pose proof (E r1 (or_introl eq_refl)) as E1.
  repeat split; lra.
Qed.

Definition pl4 (c4 c3 c2 c1 c0 r : R) : R :=
  c4 * (r * r * r * r) + c3 * (r * r * r) + c2 * (r * r) + c1 * r + c0.

Lemma poly4_zero : forall c4 c3 c2 c1 c0 r1 r2 r3 r4 r5,
  r1 <> r2 -> r1 <> r3 -> r1 <> r4 -> r1 <> r5 ->
  r2 <> r3 -> r2 <> r4 -> r2 <> r5 -> r3 <> r4 -> r3 <> r5 -> r4 <> r5 ->
  pl4 c4 c3 c2 c1 c0 r1 = 0 -> pl4 c4 c3 c2 c1 c0 r2 = 0 ->
  pl4 c4 c3 c2 c1 c0 r3 = 0 -> pl4 c4 c3 c2 c1 c0 r4 = 0 ->
  pl4 c4 c3 c2 c1 c0 r5 = 0 ->
  c0 = 0.
Proof.
  intros c4 c3 c2 c1 c0 r1 r2 r3 r4 r5 H12 H13 H14 H15 H23 H24 H25 H34 H35 H45
    E1 E2 E3 E4 E5.
  unfold pl4 in *.
  assert (Q : forall r, r <> r1 ->
            c4 * (r * r * r * r) + c3 * (r * r * r) + c2 * (r * r) + c1 * r + c0 = 0 ->
            c4 * (r * r * r) + (c4 * r1 + c3) * (r * r)
              + (c4 * (r1 * r1) + c3 * r1 + c2) * r
              + (c4 * (r1 * r1 * r1) + c3 * (r1 * r1) + c2 * r1 + c1) = 0).
  { intros r Hr Er. apply (mul_nz_zero (r - r1)); [lra|].
    replace ((r - r1) * (c4 * (r * r * r) + (c4 * r1 + c3) * (r * r)
              + (c4 * (r1 * r1) + c3 * r1 + c2) * r
              + (c4 * (r1 * r1 * r1) + c3 * (r1 * r1) + c2 * r1 + c1)))
      with ((c4 * (r * r * r * r) + c3 * (r * r * r) + c2 * (r * r) + c1 * r + c0)
            - (c4 * (r1 * r1 * r1 * r1) + c3 * (r1 * r1 * r1) + c2 * (r1 * r1)
               + c1 * r1 + c0)) by ring.
    lra. }
  assert (Hall : forall r, r = r2 \/ r = r3 \/ r = r4 \/ r = r5 ->
            c4 * (r * r * r) + (c4 * r1 + c3) * (r * r)
              + (c4 * (r1 * r1) + c3 * r1 + c2) * r
              + (c4 * (r1 * r1 * r1) + c3 * (r1 * r1) + c2 * r1 + c1) = 0).
  { intros r [ -> | [ -> | [ -> | -> ]]].
    - exact (Q r2 (not_eq_sym H12) E2).
    - exact (Q r3 (not_eq_sym H13) E3).
    - exact (Q r4 (not_eq_sym H14) E4).
    - exact (Q r5 (not_eq_sym H15) E5). }
  destruct (poly3_zero c4 (c4 * r1 + c3) (c4 * (r1 * r1) + c3 * r1 + c2)
              (c4 * (r1 * r1 * r1) + c3 * (r1 * r1) + c2 * r1 + c1) r2 r3 r4 r5
              H23 H24 H25 H34 H35 H45 Hall) as (Z4 & Z3 & Z2 & Z1).
  subst c4. assert (c3 = 0) by lra. subst c3. assert (c2 = 0) by lra. subst c2.
  assert (c1 = 0) by lra. subst c1. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The quadratic forms of a placement at a unit vector.                   *)
(* -------------------------------------------------------------------------- *)

Definition qf (M : Lin2) (x y : R) : R :=
  (l11 M * x + l12 M * y) * (l11 M * x + l12 M * y)
  + (l21 M * x + l22 M * y) * (l21 M * x + l22 M * y).

Definition pf (M : Lin2) (x y : R) : R :=
  (l11 M * x + l12 M * y) * (- l11 M * y + l12 M * x)
  + (l21 M * x + l22 M * y) * (- l21 M * y + l22 M * x).

Definition wf (M : Lin2) (x y : R) : R := qf M (- y) x.

Definition tf (M : Lin2) : R :=
  l11 M * l11 M + l12 M * l12 M + l21 M * l21 M + l22 M * l22 M.

Lemma point_eta_sl : forall p, mkPoint (px p) (py p) = p.
Proof. intros [x y]. reflexivity. Qed.

Lemma qf_speed2 : forall M x y,
  curv_speed2 (lin_ap M (mkPoint x y)) = qf M x y.
Proof. intros. unfold curv_speed2, lin_ap, qf. cbn. reflexivity. Qed.

Lemma qf_wf_tf : forall M x y, x * x + y * y = 1 ->
  qf M x y + wf M x y = tf M.
Proof.
  intros M x y H.
  transitivity (tf M * (x * x + y * y)); [unfold wf, qf, tf; ring | rewrite H; ring].
Qed.

Lemma qf_lagrange : forall M x y, x * x + y * y = 1 ->
  qf M x y * wf M x y - pf M x y * pf M x y = lin_det M * lin_det M.
Proof.
  intros M x y H.
  transitivity (lin_det M * lin_det M * ((x * x + y * y) * (x * x + y * y)));
    [unfold wf, qf, pf, lin_det; ring | rewrite H; ring].
Qed.

Lemma qf_pos : forall M x y, lin_det M <> 0 -> x * x + y * y = 1 -> 0 < qf M x y.
Proof.
  intros M x y HD H.
  pose proof (qf_lagrange M x y H) as L.
  assert (Hq : 0 <= qf M x y) by
    (unfold qf; apply Rplus_le_le_0_compat; apply Rle_0_sqr).
  assert (HD2 : 0 < lin_det M * lin_det M) by (apply Rsqr_pos_lt; exact HD).
  assert (Hp : 0 <= pf M x y * pf M x y) by apply Rle_0_sqr.
  destruct (Rle_lt_or_eq_dec 0 (qf M x y) Hq) as [Hlt|Heq]; [exact Hlt|].
  rewrite <- Heq in L. lra.
Qed.

(* The pointwise rigidity step: P = 0 and W = Q at one unit vector. *)
Theorem conformal_of_PW : forall M x y, x * x + y * y = 1 ->
  pf M x y = 0 -> wf M x y = qf M x y -> lin_conformal M.
Proof.
  intros M x y H HP HW.
  set (al := l11 M * l11 M + l21 M * l21 M - (l12 M * l12 M + l22 M * l22 M)).
  set (q := l11 M * l12 M + l21 M * l22 M).
  set (C := x * x - y * y). set (S := 2 * x * y).
  assert (HCS : C * C + S * S = 1).
  { transitivity ((x * x + y * y) * (x * x + y * y)); [unfold C, S; ring|].
    rewrite H. ring. }
  assert (Hal : al = - C * (wf M x y - qf M x y) - 2 * S * pf M x y).
  { transitivity (al * (C * C + S * S)); [rewrite HCS; ring|].
    unfold al, C, S, wf, qf, pf. ring. }
  assert (Hq : 2 * q = - S * (wf M x y - qf M x y) + 2 * C * pf M x y).
  { transitivity (2 * q * (C * C + S * S)); [rewrite HCS; ring|].
    unfold q, C, S, wf, qf, pf. ring. }
  rewrite HP, HW in Hal, Hq.
  unfold lin_conformal. fold q. split; [unfold al in Hal|]; lra.
Qed.

Theorem cloth_shear_law_supporting : ClothoidShearLawStmt.supporting.
Proof.
  intros M x y H HP HW. apply (conformal_of_PW M x y H).
  - unfold pf. exact HP.
  - unfold wf. rewrite <- !qf_speed2. exact HW.
Qed.

Lemma conformal_qf : forall M x y, lin_conformal M -> x * x + y * y = 1 ->
  qf M x y = l11 M * l11 M + l21 M * l21 M.
Proof.
  intros M x y [E O] H.
  transitivity ((l11 M * l11 M + l21 M * l21 M) * (x * x)
                + (l12 M * l12 M + l22 M * l22 M) * (y * y)
                + 2 * (l11 M * l12 M + l21 M * l22 M) * (x * y));
    [unfold qf; ring|].
  rewrite <- E, O. transitivity ((l11 M * l11 M + l21 M * l21 M) * (x * x + y * y));
    [ring | rewrite H; ring].
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Along a unit-speed curve with v' = k J v.                              *)
(* -------------------------------------------------------------------------- *)

Definition Qf (M : Lin2) (x y : R -> R) (u : R) : R := qf M (x u) (y u).
Definition Pf (M : Lin2) (x y : R -> R) (u : R) : R := pf M (x u) (y u).
Definition Wf (M : Lin2) (x y : R -> R) (u : R) : R := wf M (x u) (y u).

Lemma d_A : forall a b (x y k : R -> R) s,
  derivable_pt_lim x s (- k s * y s) -> derivable_pt_lim y s (k s * x s) ->
  derivable_pt_lim (fun u => a * x u + b * y u) s (k s * (- a * y s + b * x s)).
Proof.
  intros a b x y k s Hx Hy.
  eapply dpl_eq; [apply d_lin2; [exact Hx | exact Hy] | ring].
Qed.

Lemma d_B : forall a b (x y k : R -> R) s,
  derivable_pt_lim x s (- k s * y s) -> derivable_pt_lim y s (k s * x s) ->
  derivable_pt_lim (fun u => - a * y u + b * x u) s (- k s * (a * x s + b * y s)).
Proof.
  intros a b x y k s Hx Hy.
  eapply dpl_eq; [apply d_lin2; [exact Hy | exact Hx] | ring].
Qed.

Lemma d_Qf : forall M (x y k : R -> R) s,
  derivable_pt_lim x s (- k s * y s) -> derivable_pt_lim y s (k s * x s) ->
  derivable_pt_lim (Qf M x y) s (2 * k s * Pf M x y s).
Proof.
  intros M x y k s Hx Hy. unfold Qf, qf, Pf, pf.
  eapply dpl_eq.
  - apply d_plus; apply d_mul; apply (d_A _ _ x y k s Hx Hy).
  - cbv beta. ring.
Qed.

Lemma d_Pf : forall M (x y k : R -> R) s,
  derivable_pt_lim x s (- k s * y s) -> derivable_pt_lim y s (k s * x s) ->
  derivable_pt_lim (Pf M x y) s (k s * (Wf M x y s - Qf M x y s)).
Proof.
  intros M x y k s Hx Hy. unfold Pf, pf, Wf, wf, Qf, qf.
  eapply dpl_eq.
  - apply d_plus; apply d_mul;
      first [apply (d_A _ _ x y k s Hx Hy) | apply (d_B _ _ x y k s Hx Hy)].
  - cbv beta. ring.
Qed.

Lemma d_Rf : forall M (x y k : R -> R) s,
  lin_det M <> 0 -> (forall u, x u * x u + y u * y u = 1) ->
  derivable_pt_lim x s (- k s * y s) -> derivable_pt_lim y s (k s * x s) ->
  derivable_pt_lim (fun u => sqrt (Qf M x y u)) s
    (k s * Pf M x y s / sqrt (Qf M x y s)).
Proof.
  intros M x y k s HD Hu Hx Hy.
  pose proof (qf_pos M (x s) (y s) HD (Hu s)) as Hq. fold (Qf M x y s) in Hq.
  pose proof (sqrt_lt_R0 _ Hq) as Hr.
  apply derivable_pt_lim_ext with (f := comp sqrt (Qf M x y)); [intro; reflexivity|].
  eapply dpl_eq.
  - apply derivable_pt_lim_comp; [apply (d_Qf M x y k s Hx Hy) |].
    apply derivable_pt_lim_sqrt. exact Hq.
  - field. lra.
Qed.

Definition Evf (M : Lin2) (x y k : R -> R) (g b : R) (u : R) : R :=
  lin_det M * g * Qf M x y u - 3 * lin_det M * (k u * k u) * Pf M x y u
  - b * (Qf M x y u * Qf M x y u * Qf M x y u).

Definition Yf (M : Lin2) (x y k : R -> R) (g b : R) (u : R) : R :=
  - 4 * lin_det M * g * Pf M x y u
  - 3 * lin_det M * (k u * k u) * (Wf M x y u - Qf M x y u)
  - 6 * b * (Qf M x y u * Qf M x y u) * Pf M x y u.

Lemma d_Evf : forall M (x y k : R -> R) g b s,
  derivable_pt_lim x s (- k s * y s) -> derivable_pt_lim y s (k s * x s) ->
  derivable_pt_lim k s g ->
  derivable_pt_lim (Evf M x y k g b) s (k s * Yf M x y k g b s).
Proof.
  intros M x y k g b s Hx Hy Hk.
  pose proof (d_Qf M x y k s Hx Hy) as HQ.
  pose proof (d_Pf M x y k s Hx Hy) as HP.
  unfold Evf, Yf.
  eapply dpl_eq.
  - apply d_minus; [apply d_minus|].
    + apply d_scal. exact HQ.
    + apply d_mul; [apply d_scal; apply d_mul; exact Hk | exact HP].
    + apply d_scal. apply d_mul; [apply d_mul|]; exact HQ.
  - cbv beta. ring.
Qed.

Definition zq (D g b T q : R) : R :=
  pl4 (4 * b) (- 5 * b * T) (6 * (g * D + b * (D * D))) (- 5 * g * D * T)
      (4 * g * (D * D * D)) q.

(* Eliminating k^2: P Y - (W - Q) E is a quartic in Q alone. *)
Lemma zq_of_EY : forall D g b T q p w kk,
  q + w = T -> q * w - p * p = D * D ->
  D * g * q - 3 * D * kk * p - b * (q * q * q) = 0 ->
  - 4 * D * g * p - 3 * D * kk * (w - q) - 6 * b * (q * q) * p = 0 ->
  zq D g b T q = 0.
Proof.
  intros D g b T q p w kk HT HL HE HY. subst T.
  transitivity (p * (- 4 * D * g * p - 3 * D * kk * (w - q) - 6 * b * (q * q) * p)
                - (w - q) * (D * g * q - 3 * D * kk * p - b * (q * q * q))
                + (4 * g * D + 6 * b * (q * q)) * (p * p - (q * w - D * D))).
  - unfold zq, pl4. ring.
  - rewrite HE, HY. replace (p * p) with (q * w - D * D) by lra. ring.
Qed.

Lemma ivt_hit : forall f p q v, continuity f -> p <= q ->
  (f p - v) * (f q - v) <= 0 -> exists z, p <= z <= q /\ f z = v.
Proof.
  intros f p q v Hc Hpq H.
  destruct (IVT_cor (fun u => f u - v) p q) as [z [Hz Ez]].
  - apply continuity_minus with (f2 := fct_cte v); [exact Hc|].
    apply continuity_const. intros a b'. reflexivity.
  - exact Hpq.
  - exact H.
  - exists z. split; [exact Hz | lra].
Qed.

Lemma frac_hit_sign : forall a d c, 0 < c < 1 ->
  (a - (a + c * d)) * ((a + d) - (a + c * d)) <= 0.
Proof.
  intros a d c Hc.
  replace ((a - (a + c * d)) * ((a + d) - (a + c * d)))
    with (- ((c * (1 - c)) * (d * d))) by ring.
  assert (0 <= c * (1 - c) * (d * d)).
  { apply Rmult_le_pos; [apply Rmult_le_pos; lra | apply Rle_0_sqr]. }
  lra.
Qed.

(* A continuous function whose values on [p, q] are all roots of a quartic
   with nonzero constant term is constant there. *)
Lemma roots_const : forall (F : R -> R) c4 c3 c2 c1 c0 p q,
  continuity F -> p <= q -> c0 <> 0 ->
  (forall z, p <= z <= q -> pl4 c4 c3 c2 c1 c0 (F z) = 0) ->
  F p = F q.
Proof.
  intros F c4 c3 c2 c1 c0 p q Hc Hpq H0 Hr.
  destruct (Req_dec (F p) (F q)) as [E|Ne]; [exact E | exfalso].
  set (d := F q - F p).
  assert (Hd : d <> 0) by (unfold d; lra).
  assert (Hit : forall c, 0 < c < 1 -> pl4 c4 c3 c2 c1 c0 (F p + c * d) = 0).
  { intros c Hc'.
    destruct (ivt_hit F p q (F p + c * d) Hc Hpq) as [z [Hz Ez]].
    - replace (F q) with (F p + d) by (unfold d; ring). apply frac_hit_sign. exact Hc'.
    - rewrite <- Ez. apply Hr. exact Hz. }
  assert (Dst : forall i j, 0 < i < 1 -> 0 < j < 1 -> i <> j ->
            F p + i * d <> F p + j * d).
  { intros i j _ _ Hij E. apply Hij. apply (Rmult_eq_reg_r d); [lra | exact Hd]. }
  apply H0.
  apply (poly4_zero c4 c3 c2 c1 c0 (F p + 1/6 * d) (F p + 2/6 * d) (F p + 3/6 * d)
           (F p + 4/6 * d) (F p + 5/6 * d));
    try (apply Dst; lra); apply Hit; lra.
Qed.

Lemma Qf_continuity : forall M (x y k : R -> R),
  (forall u, derivable_pt_lim x u (- k u * y u)) ->
  (forall u, derivable_pt_lim y u (k u * x u)) ->
  continuity (Qf M x y).
Proof.
  intros M x y k Hx Hy u. apply derivable_continuous_pt.
  exists (2 * k u * Pf M x y u). apply d_Qf; [apply Hx | apply Hy].
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  The analytic core.                                                     *)
(* -------------------------------------------------------------------------- *)

Lemma law_E : forall M (x y k sg : R -> R) g a b s1 s2 s,
  lin_det M <> 0 ->
  (forall u, x u * x u + y u * y u = 1) ->
  (forall u, derivable_pt_lim x u (- k u * y u)) ->
  (forall u, derivable_pt_lim y u (k u * x u)) ->
  (forall u, derivable_pt_lim k u g) ->
  (forall u, s1 < u < s2 ->
     derivable_pt_lim sg u (sqrt (Qf M x y u)) /\
     lin_det M * k u / (sqrt (Qf M x y u) * sqrt (Qf M x y u) * sqrt (Qf M x y u))
       = a + b * sg u) ->
  s1 < s < s2 -> Evf M x y k g b s = 0.
Proof.
  intros M x y k sg g a b s1 s2 s HD Hu Hx Hy Hk Hlaw Hs.
  set (D := lin_det M) in *.
  set (Rf := fun u => sqrt (Qf M x y u)).
  assert (HQ : forall u, 0 < Qf M x y u) by (intro u; apply qf_pos; [exact HD | apply Hu]).
  assert (HR : forall u, 0 < Rf u) by (intro u; apply sqrt_lt_R0, HQ).
  assert (HRR : forall u, Rf u * Rf u = Qf M x y u)
    by (intro u; apply sqrt_sqrt; left; apply HQ).
  set (K := fun u => D * k u / (Rf u * Rf u * Rf u)).
  assert (dK : derivable_pt_lim K s (b * Rf s)).
  { apply (derivable_pt_lim_locally_ext (fun u => a + b * sg u) K s s1 s2 _ Hs).
    - intros z Hz. symmetry. apply (Hlaw z Hz).
    - eapply dpl_eq; [apply d_plus; [apply d_const | apply d_scal; apply (Hlaw s Hs)]|].
      unfold Rf. ring. }
  assert (dR : derivable_pt_lim Rf s (k s * Pf M x y s / Rf s))
    by (apply d_Rf; [exact HD | exact Hu | apply Hx | apply Hy]).
  pose proof (d_mul K (fun u => Rf u * Rf u * Rf u) s _ _ dK
               (d_mul _ _ s _ _ (d_mul _ _ s _ _ dR dR) dR)) as dF.
  assert (dF' : derivable_pt_lim (fun u => D * k u) s
                  (b * Rf s * (Rf s * Rf s * Rf s)
                   + K s * ((k s * Pf M x y s / Rf s * Rf s
                             + Rf s * (k s * Pf M x y s / Rf s)) * Rf s
                            + Rf s * Rf s * (k s * Pf M x y s / Rf s)))).
  { apply derivable_pt_lim_ext with (f := fun u => K u * (Rf u * Rf u * Rf u)); [|exact dF].
    intro z. unfold K. field. apply Rgt_not_eq, HR. }
  pose proof (uniqueness_limite _ s _ _ dF' (d_scal D k s g (Hk s))) as Eq.
  unfold Evf. fold D.
  rewrite <- Eq, <- (HRR s). unfold K.
  field. apply Rgt_not_eq, HR.
Qed.

Lemma law_kY : forall M (x y k sg : R -> R) g a b s1 s2 s,
  lin_det M <> 0 ->
  (forall u, x u * x u + y u * y u = 1) ->
  (forall u, derivable_pt_lim x u (- k u * y u)) ->
  (forall u, derivable_pt_lim y u (k u * x u)) ->
  (forall u, derivable_pt_lim k u g) ->
  (forall u, s1 < u < s2 ->
     derivable_pt_lim sg u (sqrt (Qf M x y u)) /\
     lin_det M * k u / (sqrt (Qf M x y u) * sqrt (Qf M x y u) * sqrt (Qf M x y u))
       = a + b * sg u) ->
  s1 < s < s2 -> k s * Yf M x y k g b s = 0.
Proof.
  intros M x y k sg g a b s1 s2 s HD Hu Hx Hy Hk Hlaw Hs.
  apply (dpl_locally_zero (Evf M x y k g b) s s1 s2 _ Hs).
  - intros z Hz. apply (law_E M x y k sg g a b s1 s2 z HD Hu Hx Hy Hk Hlaw Hz).
  - apply d_Evf; [apply Hx | apply Hy | apply Hk].
Qed.

Theorem shear_core : forall M (x y sg : R -> R) k0 g a b s1 s2,
  lin_det M <> 0 -> g <> 0 -> s1 < s2 ->
  (forall u, x u * x u + y u * y u = 1) ->
  (forall u, derivable_pt_lim x u (- (k0 + g * u) * y u)) ->
  (forall u, derivable_pt_lim y u ((k0 + g * u) * x u)) ->
  (forall u, s1 < u < s2 ->
     derivable_pt_lim sg u (sqrt (Qf M x y u)) /\
     lin_det M * (k0 + g * u)
       / (sqrt (Qf M x y u) * sqrt (Qf M x y u) * sqrt (Qf M x y u))
       = a + b * sg u) ->
  lin_conformal M.
Proof.
  intros M x y sg k0 g a b s1 s2 HD Hg H12 Hu Hx Hy Hlaw.
  set (k := fun u => k0 + g * u).
  assert (Hk : forall u, derivable_pt_lim k u g).
  { intro u. unfold k. eapply dpl_eq; [apply d_plus; [apply d_const | apply d_scal];
      apply derivable_pt_lim_id | ring]. }
  set (D := lin_det M) in *.
  (* a subwindow (u1, u2) of (s1, s2) on which k has no zero *)
  set (z0 := - k0 / g). set (m := (s1 + s2) / 2).
  assert (Hz0 : forall u, k u = 0 -> u = z0).
  { intros u Hu0. unfold k in Hu0. unfold z0. field_simplify; [|exact Hg].
    apply (Rmult_eq_reg_l g); [|exact Hg]. field_simplify; [lra | exact Hg]. }
  assert (Hm : s1 < m < s2) by (unfold m; lra).
  destruct (Rle_lt_dec z0 m) as [Hzm|Hzm];
  [ set (u1 := m); set (u2 := s2) | set (u1 := s1); set (u2 := m) ];
  (assert (H12' : u1 < u2) by (unfold u1, u2; lra));
  (assert (Hsub : forall u, u1 < u < u2 -> s1 < u < s2) by
     (intros u Hu'; unfold u1, u2 in Hu'; lra));
  (assert (Hknz : forall u, u1 < u < u2 -> k u <> 0) by
     (intros u Hu' E; apply Hz0 in E; unfold u1, u2 in Hu'; lra));
  clear Hzm.
  all: assert (Hlaw' : forall u, s1 < u < s2 ->
               derivable_pt_lim sg u (sqrt (Qf M x y u)) /\
               lin_det M * k u
                 / (sqrt (Qf M x y u) * sqrt (Qf M x y u) * sqrt (Qf M x y u))
                 = a + b * sg u) by exact Hlaw.
  all: assert (HEv : forall u, u1 < u < u2 -> Evf M x y k g b u = 0) by
         (intros u Hu'; apply (law_E M x y k sg g a b s1 s2 u HD Hu Hx Hy Hk Hlaw' (Hsub u Hu'))).
  all: assert (HY : forall u, u1 < u < u2 -> Yf M x y k g b u = 0) by
         (intros u Hu'; apply (mul_nz_zero (k u)); [apply Hknz; exact Hu'|];
          apply (law_kY M x y k sg g a b s1 s2 u HD Hu Hx Hy Hk Hlaw' (Hsub u Hu'))).
  all: assert (HZ : forall u, u1 < u < u2 ->
                 zq D g b (tf M) (Qf M x y u) = 0) by
         (intros u Hu';
          apply (zq_of_EY D g b (tf M) (Qf M x y u) (Pf M x y u) (Wf M x y u) (k u * k u));
          [ apply qf_wf_tf, Hu | apply qf_lagrange, Hu
          | pose proof (HEv u Hu') as E; unfold Evf in E; fold D in E; lra
          | pose proof (HY u Hu') as E; unfold Yf in E; fold D in E; lra ]).
  all: assert (Hc0 : 4 * g * (D * D * D) <> 0) by
         (apply Rmult_integral_contrapositive_currified;
          [apply Rmult_integral_contrapositive_currified; lra |];
          apply Rmult_integral_contrapositive_currified;
          [apply Rmult_integral_contrapositive_currified|]; exact HD).
  all: set (w1 := u1 + (u2 - u1) / 4); set (w2 := u2 - (u2 - u1) / 4).
  all: assert (HQc : forall u, w1 <= u <= w2 -> Qf M x y u = Qf M x y w1).
  all: try (intros u Hu'; symmetry;
            apply (roots_const (Qf M x y) (4 * b) (- 5 * b * tf M)
                     (6 * (g * D + b * (D * D))) (- 5 * g * D * tf M)
                     (4 * g * (D * D * D)) w1 u);
            [ apply (Qf_continuity M x y k Hx Hy) | lra | exact Hc0
            | intros z Hz; apply HZ; unfold w1, w2 in *; lra ]).
  all: set (s := (w1 + w2) / 2).
  all: assert (Hs : u1 < s < u2) by (unfold s, w1, w2; lra).
  all: assert (Hw : w1 < s < w2) by (unfold s, w1, w2; lra).
  all: assert (HP : Pf M x y s = 0) by
         (apply (mul_nz_zero (2 * k s));
          [ apply Rmult_integral_contrapositive_currified;
            [lra | apply Hknz; exact Hs]
          | apply (dpl_locally_const (Qf M x y) s w1 w2 (Qf M x y w1));
            [ exact Hw | intros z Hz; apply HQc; lra
            | apply d_Qf; [apply Hx | apply Hy] ] ]).
  all: apply (conformal_of_PW M (x s) (y s) (Hu s)); [exact HP|].
  all: pose proof (HY s Hs) as E; unfold Yf in E; fold D in E;
       change (Pf M x y s) with (pf M (x s) (y s)) in HP;
       change (Wf M x y s) with (wf M (x s) (y s)) in E;
       change (Qf M x y s) with (qf M (x s) (y s)) in E;
       change (Pf M x y s) with (pf M (x s) (y s)) in E;
       rewrite HP in E.
  all: assert (Hks : k s * k s <> 0) by
         (apply Rmult_integral_contrapositive_currified; apply Hknz; exact Hs).
  all: assert (E' : (3 * D * (k s * k s)) * (wf M (x s) (y s) - qf M (x s) (y s)) = 0) by lra.
  all: apply mul_nz_zero in E';
       [ lra
       | apply Rmult_integral_contrapositive_currified;
         [apply Rmult_integral_contrapositive_currified; [lra | exact HD] | exact Hks] ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  The host clothoid supplies (x, y, k).                                  *)
(* -------------------------------------------------------------------------- *)

Definition cl_x (c : ClothoidEgg) (u : R) : R := px (cloth_arc_v c u).
Definition cl_y (c : ClothoidEgg) (u : R) : R := py (cloth_arc_v c u).
Definition cl_g (c : ClothoidEgg) : R := (cloth_tk1 c - cloth_tk0 c) / cloth_tlen c.

Lemma cl_kap : forall c u, cloth_d c <> 0 ->
  cloth_tk0 c + (cloth_tk1 c - cloth_tk0 c) * u / cloth_tlen c
    = cloth_tk0 c + cl_g c * u.
Proof.
  intros c u Hd. pose proof (cloth_tlen_pos c Hd). unfold cl_g. field. lra.
Qed.

Lemma cl_unit : forall c u, cloth_h2 c <> 0 -> cl_x c u * cl_x c u + cl_y c u * cl_y c u = 1.
Proof. intros c u Hh. unfold cl_x, cl_y. apply (cloth_arc_speed2 c u Hh). Qed.

Lemma cl_a : forall c u, cloth_d c <> 0 ->
  px (cloth_arc_a c u) = - (cloth_tk0 c + cl_g c * u) * cl_y c u /\
  py (cloth_arc_a c u) = (cloth_tk0 c + cl_g c * u) * cl_x c u.
Proof.
  intros c u Hd. rewrite <- cl_kap by exact Hd.
  rewrite <- cloth_kappa_traversal_linear by exact Hd.
  pose proof (cloth_dir_sq c) as H2.
  unfold cl_x, cl_y, cloth_arc_a, cloth_arc_v. cbn [px py].
  split.
  - transitivity (- ((cloth_dir c * cloth_dir c) * cloth_kappa c (cloth_station c u))
                    * cloth_vy c (cloth_station c u)); [rewrite H2; ring | ring].
  - transitivity (((cloth_dir c * cloth_dir c) * cloth_kappa c (cloth_station c u))
                    * cloth_vx c (cloth_station c u)); [rewrite H2; ring | ring].
Qed.

Lemma cl_g_nz : forall c, cloth_A c <> 0 -> cloth_d c <> 0 -> cl_g c <> 0.
Proof.
  intros c HA Hd. pose proof (cloth_tlen_pos c Hd) as HL.
  assert (Hs : cloth_sigma c <> 0) by (unfold cloth_sigma; destruct (Rle_dec 0 (cloth_cross c)); lra).
  pose proof (cloth_dir_nz c) as Hdir.
  unfold cl_g, cloth_tk1, cloth_tk0, cloth_kappa.
  replace ((cloth_dir c * (cloth_sigma c * cloth_ed c / (cloth_A c * cloth_A c))
            - cloth_dir c * (cloth_sigma c * cloth_sd c / (cloth_A c * cloth_A c)))
           / cloth_tlen c)
    with (cloth_dir c * cloth_sigma c * cloth_d c / (cloth_A c * cloth_A c * cloth_tlen c))
    by (unfold cloth_d; field; split; [exact HA | lra]).
  unfold Rdiv. repeat apply Rmult_integral_contrapositive_currified; try assumption.
  apply Rinv_neq_0_compat. repeat apply Rmult_integral_contrapositive_currified; try assumption; lra.
Qed.

Lemma cl_placed_curv : forall c M u, cloth_h2 c <> 0 -> cloth_d c <> 0 ->
  placed_curv c M u
    = lin_det M * (cloth_tk0 c + cl_g c * u)
      / (sqrt (Qf M (cl_x c) (cl_y c) u) * sqrt (Qf M (cl_x c) (cl_y c) u)
         * sqrt (Qf M (cl_x c) (cl_y c) u)).
Proof.
  intros c M u Hh Hd. unfold placed_curv.
  rewrite signed_curv_lin, cloth_arc_cross, cl_kap by assumption.
  unfold Qf. rewrite <- qf_speed2. unfold cl_x, cl_y. rewrite point_eta_sl. reflexivity.
Qed.

Lemma cl_speed : forall c M u,
  curv_speed2 (lin_ap M (cloth_arc_v c u)) = Qf M (cl_x c) (cl_y c) u.
Proof.
  intros. unfold Qf, cl_x, cl_y. rewrite <- qf_speed2, point_eta_sl. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §7  The claim, its supporting step and the GEOS witness.                   *)
(* -------------------------------------------------------------------------- *)

Theorem conformal_law : forall c M s1 s2,
  cloth_h2 c <> 0 -> cloth_d c <> 0 -> lin_det M <> 0 ->
  lin_conformal M -> linear_law_on c M s1 s2.
Proof.
  intros c M s1 s2 Hh Hd HD Hc.
  set (p := l11 M * l11 M + l21 M * l21 M).
  assert (HQ : forall u, Qf M (cl_x c) (cl_y c) u = p)
    by (intro u; apply conformal_qf; [exact Hc | apply cl_unit; exact Hh]).
  assert (Hp : 0 < p) by (rewrite <- (HQ 0); apply qf_pos; [exact HD | apply cl_unit; exact Hh]).
  set (R := sqrt p).
  assert (HR : 0 < R) by (apply sqrt_lt_R0; exact Hp).
  exists (fun u => R * u), (lin_det M * cloth_tk0 c / (R * R * R)),
         (lin_det M * cl_g c / (R * R * R * R)).
  intros u _. split.
  - unfold placed_speed. rewrite cl_speed, HQ. fold R.
    eapply dpl_eq; [apply d_scal; apply derivable_pt_lim_id | ring].
  - rewrite cl_placed_curv by assumption. rewrite HQ. fold R. field. lra.
Qed.

Theorem cloth_shear_law_claim : ClothoidShearLawStmt.claim.
Proof.
  intros c M s1 s2 HA Hh Hd HD H12. split.
  - intros (sg & a & b & Hlaw).
    apply (shear_core M (cl_x c) (cl_y c) sg (cloth_tk0 c) (cl_g c) a b s1 s2
             HD (cl_g_nz c HA Hd) H12).
    + intro u. apply cl_unit. exact Hh.
    + intro u. destruct (cl_a c u Hd) as [Ea _]. rewrite <- Ea.
      unfold cl_x. apply cloth_arc_vx_deriv. exact HA.
    + intro u. destruct (cl_a c u Hd) as [_ Ea]. rewrite <- Ea.
      unfold cl_y. apply cloth_arc_vy_deriv. exact HA.
    + intros u Hu. destruct (Hlaw u Hu) as [Hs Hk]. split.
      * unfold placed_speed in Hs. rewrite cl_speed in Hs. exact Hs.
      * rewrite <- cl_placed_curv by assumption. exact Hk.
  - intro Hc. apply conformal_law; assumption.
Qed.

Theorem cloth_shear_law_witness : ClothoidShearLawStmt.witness.
Proof.
  intros s1 s2 H12 Hlaw.
  destruct geos_shear_nondeg as (HA & Hh & Hd).
  apply (cloth_shear_law_claim geos_shear_egg geos_shear s1 s2 HA Hh Hd) in Hlaw;
    [| rewrite geos_shear_det; lra | exact H12].
  destruct Hlaw as [E _]. unfold geos_shear in E. cbn in E. lra.
Qed.

Print Assumptions poly4_zero.
Print Assumptions qf_lagrange.
Print Assumptions qf_pos.
Print Assumptions conformal_of_PW.
Print Assumptions cloth_shear_law_supporting.
Print Assumptions d_Qf.
Print Assumptions d_Pf.
Print Assumptions d_Evf.
Print Assumptions zq_of_EY.
Print Assumptions roots_const.
Print Assumptions law_E.
Print Assumptions law_kY.
Print Assumptions shear_core.
Print Assumptions cl_a.
Print Assumptions cl_g_nz.
Print Assumptions cl_placed_curv.
Print Assumptions conformal_law.
Print Assumptions cloth_shear_law_claim.
Print Assumptions cloth_shear_law_witness.
