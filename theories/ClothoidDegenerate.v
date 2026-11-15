(* ============================================================================
   NetTopologySuite.Proofs.ClothoidDegenerate
   ----------------------------------------------------------------------------
   The degenerate straight-chord regime of the clothoid chord-length residual
   -- the one EXACT sub-regime, and a non-vacuity witness for the conditional
   interface of theories/ClothoidResidual.v.  Route (A) of
   docs/clothoid-open-questions-triage.md.

   Context.  ClothoidResidual.v defines
   f(L) = L^2 * (P(L)^2 + Q(L)^2) - d^2, with f' a definition
   (clothoid_f_deriv) and f' > 0 on |clothoid_kappa * L| <= 1/2.
   In the degenerate regime k0 = k1 = 0 the turning vanishes, so

       P(L) = 1,  Q(L) = 0,  f(L) = L^2 - d^2,  f'(L) = 2L

   (clothoid_f_flat, clothoid_fprime_flat).  The quadratic MVT witness
   is the midpoint; Stdlib MVT is not used.

   This file delivers two things:

   1. The exact-root headline: L = d is the unique positive root
      (degenerate_root_exact, degenerate_unique_positive_root).

   2. The same facts through the residual
      (degenerate_H_deriv, degenerate_H_fprime_pos,
      degenerate_unique_root_via_interface).  Strict increase comes from
      RealMonotone.  degenerate_H_mvt remains a midpoint identity; it is
      not a premise.

   Queued (NOT this file): the binary64 mirror -- for integer-valued d the
   root L = d is exactly representable and the residual evaluation is exact
   in the 2^26 window, mirroring the `_small_int` headline pattern of
   theories-flocq/Orient_b64_exact.v.  See the triage doc, route (A).

   NTS mapping: the straight-chord fast path of a clothoid G^1 Hermite
   solver (clothoid-halley-coq, public EUPL-1.2 repro), consumed through the
   RelateClothoid.v chord carrier on the NetTopologySuite.Curve side.

   3. The other degenerate inputs of the residual, at spec level (the
      "degenerate cases" part at the end of the file).  They test the
      real-number statement, not an implementation:
        - L = 0: f = - d^2 and f' = 0 (clothoid_f_at_zero,
          clothoid_fprime_at_zero); the sign of f' is only claimed for
          0 < L.
        - symmetries: f is unchanged under L -> - L (clothoid_f_even),
          under the mirror image (k0, k1) -> (- k0, - k1)
          (clothoid_f_mirror) and under reversal of the arc,
          (k0, k1) -> (- k1, - k0) (clothoid_f_reverse).  The branch
          condition |clothoid_kappa * L| is NOT invariant under reversal;
          the residual is.
        - circular arc k0 = k1 = k <> 0: closed forms
          f = (2 - 2 cos (k L)) / k^2 - d^2 and f' = 2 sin (k L) / k
          (clothoid_f_arc, clothoid_fprime_arc).
        - edge of the branch: for the circle f' = 0 at
          |clothoid_kappa * L| = PI and f' < 0 for PI < |k L| < 2 PI
          (clothoid_fprime_arc_zero_at_pi,
          clothoid_fprime_arc_neg_past_pi).  So the open bound of
          ClothoidResidual.clothoid_fprime_pos_branch cannot be widened.
        - k1 = - k0, symmetric about the inflection: f' > 0 for
          |k0 L| <= PI (clothoid_fprime_pos_symmetric), twice the reach
          of the branch condition there.

   No Admitted, no Axiom (except the classical real axioms inherited from the
   corpus's Real.v).  No MVT, Rolle, RiemannInt.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Psatz.
From Stdlib Require Import Ranalysis1.   (* derivable_pt_lim *)
From NTS.Proofs Require Import Real.
From NTS.Proofs Require Import LipInt LipIntLeibniz LipIntUnit ClothoidFPrimeCore.
From NTS.Proofs Require Import ClothoidResidual.
From Stdlib Require Import List.

Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* The degenerate residual and its derivative.                                *)
(* -------------------------------------------------------------------------- *)

Definition degenerate_residual (d : R) (L : R) : R := L * L - d * d.

Definition degenerate_residual' (d : R) (L : R) : R := 2 * L.

(* -------------------------------------------------------------------------- *)
(* Part 1 -- the exact-root headline, proved directly.                        *)
(* -------------------------------------------------------------------------- *)

(* The chord length d itself is a root: f_deg(d) = d^2 - d^2 = 0.  On the
   nose -- no approximation enters at any point. *)
Lemma degenerate_root_exact :
  forall d : R, degenerate_residual d d = 0.
Proof.
  intro d. unfold degenerate_residual. ring.
Qed.

(* Strict monotonicity on L > 0, directly (no MVT): L1^2 < L2^2. *)
Lemma degenerate_strictly_increasing :
  forall d L1 L2 : R,
    0 < L1 -> L1 < L2 ->
    degenerate_residual d L1 < degenerate_residual d L2.
Proof.
  intros d L1 L2 HL1 HL12. unfold degenerate_residual. nra.
Qed.

(* The unique positive root is L = d (for a positive chord).  This is the
   exact answer the Halley iteration would converge to: in the degenerate
   regime the solver's fixpoint is available in closed form. *)
Theorem degenerate_unique_positive_root :
  forall d L : R,
    0 < d -> 0 < L ->
    degenerate_residual d L = 0 ->
    L = d.
Proof.
  intros d L Hd HL Hroot. unfold degenerate_residual in Hroot. nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Part 2 -- discharging the ClothoidResidual.v interface concretely.         *)
(*                                                                            *)
(* kappa = 0: the branch precondition |kappa * L| <= pi is trivially true     *)
(* everywhere, so the degenerate regime lies entirely on the monotone branch. *)
(* -------------------------------------------------------------------------- *)

(* H_deriv, concretely: the derivative of L*L - d*d at L is 2*L.  Assembled
   from Stdlib's derivability algebra (id * id, minus a constant). *)
Lemma degenerate_H_deriv :
  forall d L : R,
    derivable_pt_lim (degenerate_residual d) L (degenerate_residual' d L).
Proof.
  intros d L.
  unfold degenerate_residual, degenerate_residual'.
  replace (2 * L) with (1 * L + L * 1 - 0) by ring.
  apply (derivable_pt_lim_minus (fun x => x * x) (fun _ => d * d)).
  - apply (derivable_pt_lim_mult (fun x => x) (fun x => x)).
    + apply derivable_pt_lim_id.
    + apply derivable_pt_lim_id.
  - apply derivable_pt_lim_const.
Qed.

(* H_fprime_pos, concretely (with kappa = 0): 2L > 0 for L > 0. *)
Lemma degenerate_H_fprime_pos :
  forall d L : R,
    0 < L -> Rabs (0 * L) <= PI ->
    0 < degenerate_residual' d L.
Proof.
  intros d L HL _. unfold degenerate_residual'. lra.
Qed.

(* The branch precondition itself is trivial at kappa = 0 -- every L > 0 is
   on the monotone branch, so the interface's guard never bites here. *)
Lemma degenerate_branch_trivial :
  forall L : R, Rabs (0 * L) <= PI.
Proof.
  intro L.
  rewrite Rmult_0_l, Rabs_R0.
  pose proof PI_RGT_0. lra.
Qed.

(* H_mvt, concretely -- and CONSTRUCTIVELY.  For the quadratic residual the
   mean value witness on [a, b] is the midpoint c = (a+b)/2:

       f b - f a = b^2 - a^2 = (a+b)(b-a) = (2 * (a+b)/2) * (b - a).

   Stdlib's MVT_cor2 would pull Classical_Prop.classic (see the
   ClothoidResidual.v header); exhibiting the midpoint keeps this file on
   the corpus's three-axiom allowlist. *)
Lemma degenerate_H_mvt :
  forall d a b : R,
    a < b ->
    (forall c : R, a <= c <= b ->
       derivable_pt_lim (degenerate_residual d) c (degenerate_residual' d c)) ->
    exists c : R,
      degenerate_residual d b - degenerate_residual d a
        = degenerate_residual' d c * (b - a)
      /\ a < c < b.
Proof.
  intros d a b Hab _.
  exists ((a + b) / 2).
  split.
  - unfold degenerate_residual, degenerate_residual'. field.
  - lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* The degenerate residual through ClothoidResidual's half-branch theorems.   *)
(* -------------------------------------------------------------------------- *)

Theorem degenerate_strictly_increasing_via_interface :
  forall d L1 L2 : R,
    0 < L1 -> L1 < L2 ->
    Rabs (0 * L2) <= PI ->
    degenerate_residual d L1 < degenerate_residual d L2.
Proof.
  intros d L1 L2 HL1 HL12 _.
  unfold degenerate_residual.
  rewrite <- (clothoid_f_flat d L1), <- (clothoid_f_flat d L2).
  apply (clothoid_residual_strictly_increasing 0 0 d L1 L2 HL1 HL12).
  assert (Hk0 : clothoid_kappa 0 0 = 0).
  { unfold clothoid_kappa. rewrite Rabs_R0.
    replace (0 - 0) with 0 by ring. rewrite Rabs_R0. field. }
  rewrite Hk0, Rmult_0_l, Rabs_R0. lra.
Qed.

Theorem degenerate_unique_root_via_interface :
  forall d L1 L2 : R,
    0 < L1 -> 0 < L2 ->
    degenerate_residual d L1 = 0 ->
    degenerate_residual d L2 = 0 ->
    L1 = L2.
Proof.
  intros d L1 L2 HL1 HL2 Hf1 Hf2.
  apply (clothoid_residual_unique_root_half 0 0 d L1 L2 HL1 HL2).
  - assert (Hk0 : clothoid_kappa 0 0 = 0).
    { unfold clothoid_kappa. rewrite Rabs_R0.
      replace (0 - 0) with 0 by ring. rewrite Rabs_R0. field. }
    rewrite Hk0, Rmult_0_l, Rabs_R0. lra.
  - assert (Hk0 : clothoid_kappa 0 0 = 0).
    { unfold clothoid_kappa. rewrite Rabs_R0.
      replace (0 - 0) with 0 by ring. rewrite Rabs_R0. field. }
    rewrite Hk0, Rmult_0_l, Rabs_R0. lra.
  - unfold degenerate_residual in Hf1. rewrite <- (clothoid_f_flat d L1) in Hf1. exact Hf1.
  - unfold degenerate_residual in Hf2. rewrite <- (clothoid_f_flat d L2) in Hf2. exact Hf2.
Qed.

(* Consistency: the interface route and the direct route agree on the
   closed-form answer. *)
Corollary degenerate_root_is_chord_length :
  forall d L : R,
    0 < d -> 0 < L ->
    degenerate_residual d L = 0 ->
    L = d.
Proof.
  intros d L Hd HL Hroot.
  apply (degenerate_unique_root_via_interface d L d HL Hd Hroot
           (degenerate_root_exact d)).
Qed.

(* ========================================================================== *)
(* Degenerate cases of the residual, at spec level.                           *)
(* ========================================================================== *)

(* ---- L = 0, and the two sign symmetries ---------------------------------- *)

Lemma clothoid_f_at_zero : forall k0 k1 d, clothoid_f k0 k1 d 0 = - (d * d).
Proof. intros. unfold clothoid_f. ring. Qed.

Lemma clothoid_fprime_at_zero : forall k0 k1, clothoid_f' k0 k1 0 = 0.
Proof. intros. unfold clothoid_f'. ring. Qed.

Lemma clothoid_P_uint : forall k0 k1 L (H : ULip (fun t => g_cos k0 k1 t L)),
  clothoid_P k0 k1 L = uint _ H.
Proof. intros. unfold clothoid_P. apply pint_uint. Qed.

Lemma clothoid_Q_uint : forall k0 k1 L (H : ULip (fun t => g_sin k0 k1 t L)),
  clothoid_Q k0 k1 L = uint _ H.
Proof. intros. unfold clothoid_Q. apply pint_uint. Qed.

Lemma clothoid_R_uint : forall k0 k1 L (H : ULip (fun t => unit_cos k0 k1 t L)),
  clothoid_R k0 k1 L = uint _ H.
Proof. intros. unfold clothoid_R. apply pint_uint. Qed.

Lemma clothoid_T_uint : forall k0 k1 L (H : ULip (fun t => unit_sin k0 k1 t L)),
  clothoid_T k0 k1 L = uint _ H.
Proof. intros. unfold clothoid_T. apply pint_uint. Qed.

Lemma g_cos_lip : forall k0 k1 L, ULip (fun t => g_cos k0 k1 t L).
Proof. intros. unfold g_cos, clothoid_psi. ulip. Qed.

Lemma g_sin_lip : forall k0 k1 L, ULip (fun t => g_sin k0 k1 t L).
Proof. intros. unfold g_sin, clothoid_psi. ulip. Qed.

(* P is even and Q odd under an odd change of the heading: used for
   L -> - L and for the mirror image (k0, k1) -> (- k0, - k1). *)
Lemma clothoid_PQ_odd_heading :
  forall k0 k1 L k0' k1' L',
    (forall t, L' * clothoid_psi k0' k1' t = - (L * clothoid_psi k0 k1 t)) ->
    clothoid_P k0' k1' L' = clothoid_P k0 k1 L /\
    clothoid_Q k0' k1' L' = - clothoid_Q k0 k1 L.
Proof.
  intros k0 k1 L k0' k1' L' Hodd. split.
  - rewrite (clothoid_P_uint k0' k1' L' (g_cos_lip _ _ _)).
    rewrite (clothoid_P_uint k0 k1 L (g_cos_lip _ _ _)).
    apply uint_ext. intros t _. unfold g_cos. rewrite Hodd. apply cos_neg.
  - rewrite (clothoid_Q_uint k0' k1' L' (g_sin_lip _ _ _)).
    rewrite (clothoid_Q_uint k0 k1 L (g_sin_lip _ _ _)).
    assert (Hl : ULip (fun t => -1 * g_sin k0 k1 t L))
      by (unfold g_sin, clothoid_psi; ulip).
    replace (- uint _ (g_sin_lip k0 k1 L)) with (-1 * uint _ (g_sin_lip k0 k1 L))
      by ring.
    rewrite <- (uint_scal (-1) _ (g_sin_lip k0 k1 L) Hl).
    apply uint_ext. intros t _. unfold g_sin. rewrite Hodd, sin_neg. ring.
Qed.

Lemma clothoid_f_even :
  forall k0 k1 d L, clothoid_f k0 k1 d (- L) = clothoid_f k0 k1 d L.
Proof.
  intros k0 k1 d L.
  destruct (clothoid_PQ_odd_heading k0 k1 L k0 k1 (- L)) as [HP HQ].
  { intro t. ring. }
  unfold clothoid_f, clothoid_S. rewrite HP, HQ. ring.
Qed.

Lemma clothoid_f_mirror :
  forall k0 k1 d L, clothoid_f (- k0) (- k1) d L = clothoid_f k0 k1 d L.
Proof.
  intros k0 k1 d L.
  destruct (clothoid_PQ_odd_heading k0 k1 L (- k0) (- k1) L) as [HP HQ].
  { intro t. unfold clothoid_psi. field. }
  unfold clothoid_f, clothoid_S. rewrite HP, HQ. ring.
Qed.

(* ---- reversal: the residual does not depend on the direction ------------- *)

Lemma clothoid_psi_reverse :
  forall k0 k1 t,
    clothoid_psi (- k1) (- k0) t
    = clothoid_psi k0 k1 (1 - t) - clothoid_psi k0 k1 1.
Proof. intros. unfold clothoid_psi. field. Qed.

Lemma clothoid_S_reverse :
  forall k0 k1 L, clothoid_S (- k1) (- k0) L = clothoid_S k0 k1 L.
Proof.
  intros k0 k1 L.
  set (th := L * clothoid_psi k0 k1 1).
  pose (Hc := g_cos_lip k0 k1 L). pose (Hs := g_sin_lip k0 k1 L).
  pose (Hcr := ulip_refl _ Hc). pose (Hsr := ulip_refl _ Hs).
  assert (HP : clothoid_P (- k1) (- k0) L
               = cos th * clothoid_P k0 k1 L + sin th * clothoid_Q k0 k1 L).
  { rewrite (clothoid_P_uint (- k1) (- k0) L (g_cos_lip _ _ _)).
    rewrite (uint_lincomb (ut (cos th) _ Hcr :: ut (sin th) _ Hsr :: nil)).
    - cbn [lc_int ut]. unfold Hcr, Hsr.
      rewrite (uint_refl _ Hc), (uint_refl _ Hs).
      rewrite <- (clothoid_P_uint k0 k1 L Hc), <- (clothoid_Q_uint k0 k1 L Hs).
      ring.
    - intros t _. cbn [lc_fun ut]. unfold g_cos, g_sin.
      rewrite clothoid_psi_reverse.
      replace (L * (clothoid_psi k0 k1 (1 - t) - clothoid_psi k0 k1 1))
        with (L * clothoid_psi k0 k1 (1 - t) - th) by (unfold th; ring).
      rewrite cos_minus. ring. }
  assert (HQ : clothoid_Q (- k1) (- k0) L
               = cos th * clothoid_Q k0 k1 L - sin th * clothoid_P k0 k1 L).
  { rewrite (clothoid_Q_uint (- k1) (- k0) L (g_sin_lip _ _ _)).
    rewrite (uint_lincomb (ut (cos th) _ Hsr :: ut (- sin th) _ Hcr :: nil)).
    - cbn [lc_int ut]. unfold Hcr, Hsr.
      rewrite (uint_refl _ Hc), (uint_refl _ Hs).
      rewrite <- (clothoid_P_uint k0 k1 L Hc), <- (clothoid_Q_uint k0 k1 L Hs).
      ring.
    - intros t _. cbn [lc_fun ut]. unfold g_cos, g_sin.
      rewrite clothoid_psi_reverse.
      replace (L * (clothoid_psi k0 k1 (1 - t) - clothoid_psi k0 k1 1))
        with (L * clothoid_psi k0 k1 (1 - t) - th) by (unfold th; ring).
      rewrite sin_minus. ring. }
  unfold clothoid_S. rewrite HP, HQ.
  pose proof (sin2_cos2 th) as H1. unfold Rsqr in H1.
  replace (clothoid_P k0 k1 L * clothoid_P k0 k1 L
           + clothoid_Q k0 k1 L * clothoid_Q k0 k1 L)
    with ((sin th * sin th + cos th * cos th)
          * (clothoid_P k0 k1 L * clothoid_P k0 k1 L
             + clothoid_Q k0 k1 L * clothoid_Q k0 k1 L))
    by (rewrite H1; ring).
  ring.
Qed.

Theorem clothoid_f_reverse :
  forall k0 k1 d L, clothoid_f (- k1) (- k0) d L = clothoid_f k0 k1 d L.
Proof.
  intros. unfold clothoid_f. rewrite clothoid_S_reverse. reflexivity.
Qed.

(* ---- the circular arc k0 = k1 = k <> 0 ----------------------------------- *)

Lemma deriv_trig_affine :
  forall al be ga de c t,
    derivable_pt_lim
      (fun t => (al + be * t) * sin (c * t) + (ga + de * t) * cos (c * t)) t
      (be * sin (c * t) + (al + be * t) * (cos (c * t) * c)
       + (de * cos (c * t) + (ga + de * t) * (- sin (c * t) * c))).
Proof.
  intros al be ga de c t.
  assert (Hlin : forall a b, derivable_pt_lim (fun t => a + b * t) t b).
  { intros a b.
    pose proof (derivable_pt_lim_plus (fun _ => a) (fun t => b * t) t 0 (b * 1)
                  (derivable_pt_lim_const a t)
                  (derivable_pt_lim_scal (fun t => t) b t 1
                     (derivable_pt_lim_id t))) as H.
    replace (0 + b * 1) with b in H by ring. exact H. }
  assert (Hct : derivable_pt_lim (fun t => c * t) t c).
  { pose proof (derivable_pt_lim_scal (fun t => t) c t 1
                  (derivable_pt_lim_id t)) as H.
    replace (c * 1) with c in H by ring. exact H. }
  apply (derivable_pt_lim_plus
           (fun t => (al + be * t) * sin (c * t))
           (fun t => (ga + de * t) * cos (c * t))).
  - apply (derivable_pt_lim_mult (fun t => al + be * t) (fun t => sin (c * t))).
    + apply Hlin.
    + apply (derivable_pt_lim_comp (fun t => c * t) sin t c (cos (c * t)) Hct).
      apply derivable_pt_lim_sin.
  - apply (derivable_pt_lim_mult (fun t => ga + de * t) (fun t => cos (c * t))).
    + apply Hlin.
    + apply (derivable_pt_lim_comp (fun t => c * t) cos t c (- sin (c * t)) Hct).
      apply derivable_pt_lim_cos.
Qed.

(* ∫_0^1 of an integrand whose primitive is trig-affine. *)
Lemma uint_trig_affine :
  forall al be ga de c f (H : ULip f),
    (forall t, 0 <= t <= 1 ->
       f t = be * sin (c * t) + (al + be * t) * (cos (c * t) * c)
             + (de * cos (c * t) + (ga + de * t) * (- sin (c * t) * c))) ->
    uint f H = (al + be) * sin c + (ga + de) * cos c - ga.
Proof.
  intros al be ga de c f H Hf.
  rewrite (uint_ftc f H
             (fun t => (al + be * t) * sin (c * t) + (ga + de * t) * cos (c * t))).
  - rewrite !Rmult_1_r, !Rmult_0_r, sin_0, cos_0. ring.
  - intros t Ht. rewrite (Hf t Ht). apply deriv_trig_affine.
Qed.

Lemma clothoid_arc_moments :
  forall k L, k * L <> 0 ->
    clothoid_P k k L = sin (k * L) / (k * L) /\
    clothoid_Q k k L = (1 - cos (k * L)) / (k * L) /\
    clothoid_R k k L
    = k * (k * L * sin (k * L) + cos (k * L) - 1) / ((k * L) * (k * L)) /\
    clothoid_T k k L
    = k * (sin (k * L) - k * L * cos (k * L)) / ((k * L) * (k * L)).
Proof.
  intros k L Hc. set (c := k * L) in *.
  assert (Hpsi : forall t, L * clothoid_psi k k t = c * t)
    by (intro t; unfold clothoid_psi, c; field).
  assert (Hpsi' : forall t, clothoid_psi k k t = k * t)
    by (intro t; unfold clothoid_psi; field).
  assert (HR : ULip (fun t => unit_cos k k t L))
    by (unfold unit_cos, clothoid_psi; ulip).
  assert (HT : ULip (fun t => unit_sin k k t L))
    by (unfold unit_sin, clothoid_psi; ulip).
  repeat split.
  - rewrite (clothoid_P_uint k k L (g_cos_lip _ _ _)).
    rewrite (uint_trig_affine (/ c) 0 0 0 c).
    + field. exact Hc.
    + intros t _. unfold g_cos. rewrite Hpsi. field. exact Hc.
  - rewrite (clothoid_Q_uint k k L (g_sin_lip _ _ _)).
    rewrite (uint_trig_affine 0 0 (- / c) 0 c).
    + field. exact Hc.
    + intros t _. unfold g_sin. rewrite Hpsi. field. exact Hc.
  - rewrite (clothoid_R_uint k k L HR).
    rewrite (uint_trig_affine 0 (k / c) (k / (c * c)) 0 c).
    + field. exact Hc.
    + intros t _. unfold unit_cos. rewrite Hpsi, Hpsi'. field. exact Hc.
  - rewrite (clothoid_T_uint k k L HT).
    rewrite (uint_trig_affine (k / (c * c)) 0 0 (- (k / c)) c).
    + field. exact Hc.
    + intros t _. unfold unit_sin. rewrite Hpsi, Hpsi'. field. exact Hc.
Qed.

(* Squared chord of an arc of curvature k and length L: (2 sin (kL/2) / k)^2,
   written without the half angle. *)
Theorem clothoid_f_arc :
  forall k d L, k <> 0 -> L <> 0 ->
    clothoid_f k k d L = (2 - 2 * cos (k * L)) / (k * k) - d * d.
Proof.
  intros k d L Hk HL.
  assert (Hc : k * L <> 0) by (apply Rmult_integral_contrapositive; split; assumption).
  destruct (clothoid_arc_moments k L Hc) as [HP [HQ _]].
  unfold clothoid_f, clothoid_S. rewrite HP, HQ.
  pose proof (sin2_cos2 (k * L)) as H1. unfold Rsqr in H1.
  set (s := sin (k * L)) in *. set (co := cos (k * L)) in *.
  replace (2 - 2 * co) with (s * s + (1 - co) * (1 - co))
    by (replace (s * s) with (1 - co * co) by lra; ring).
  field. split; assumption.
Qed.

Theorem clothoid_fprime_arc :
  forall k L, k <> 0 -> L <> 0 ->
    clothoid_f' k k L = 2 * sin (k * L) / k.
Proof.
  intros k L Hk HL.
  assert (Hc : k * L <> 0) by (apply Rmult_integral_contrapositive; split; assumption).
  destruct (clothoid_arc_moments k L Hc) as [HP [HQ [HR HT]]].
  unfold clothoid_f', clothoid_S. rewrite HP, HQ, HR, HT.
  field. split; assumption.
Qed.

(* Sharpness of the open branch: for the circle the derivative vanishes at
   total turning PI and is negative just beyond it. *)
Corollary clothoid_fprime_arc_zero_at_pi :
  forall k L, k <> 0 -> 0 < L ->
    Rabs (clothoid_kappa k k * L) = PI ->
    clothoid_f' k k L = 0.
Proof.
  intros k L Hk HL Hpi.
  rewrite (clothoid_fprime_arc k L Hk) by lra.
  unfold clothoid_kappa in Hpi.
  replace (k - k) with 0 in Hpi by ring. rewrite Rabs_R0 in Hpi.
  replace ((Rabs k + 0 / 2) * L) with (Rabs k * L) in Hpi by field.
  rewrite Rabs_mult, Rabs_Rabsolu, <- Rabs_mult in Hpi.
  assert (Hs : sin (k * L) = 0).
  { unfold Rabs in Hpi. destruct (Rcase_abs (k * L)) as [Hn|Hp].
    - replace (k * L) with (- PI) by lra. rewrite sin_neg, sin_PI. ring.
    - rewrite Hpi. apply sin_PI. }
  rewrite Hs. field. exact Hk.
Qed.

Corollary clothoid_fprime_arc_neg_past_pi :
  forall k L, k <> 0 -> 0 < L ->
    PI < Rabs (k * L) < 2 * PI ->
    clothoid_f' k k L < 0.
Proof.
  intros k L Hk HL Hr.
  rewrite (clothoid_fprime_arc k L Hk) by lra.
  unfold Rabs in Hr. destruct (Rcase_abs (k * L)) as [Hn|Hp].
  - assert (Hkn : k < 0) by nra.
    assert (Hs : sin (- (k * L)) < 0) by (apply sin_lt_0; lra).
    rewrite sin_neg in Hs.
    assert (0 < 2 * sin (k * L) * / - k)
      by (apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat; lra]).
    replace (2 * sin (k * L) / k) with (- (2 * sin (k * L) * / - k))
      by (field; exact Hk).
    lra.
  - assert (Hkp : 0 < k) by nra.
    assert (Hs : sin (k * L) < 0) by (apply sin_lt_0; lra).
    assert (0 < - (2 * sin (k * L)) * / k)
      by (apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat; lra]).
    unfold Rdiv. lra.
Qed.

(* ---- k1 = - k0: symmetric about the inflection --------------------------- *)

(* The total turning is 0, so the turning form gives the sign for
   |k0 L| <= PI.  The branch condition |kappa L| < PI only reaches
   |k0 L| < PI / 2 here. *)
Corollary clothoid_fprime_pos_symmetric :
  forall k0 L, 0 < L -> Rabs (k0 * L) <= PI ->
    0 < clothoid_f' k0 (- k0) L.
Proof.
  intros k0 L HL Hb. pose proof PI_RGT_0 as Hpi.
  apply clothoid_fprime_pos_turning; [exact HL | |].
  - replace (L * (k0 + - k0) / 2) with 0 by field. rewrite Rabs_R0. exact Hpi.
  - replace (L * (- k0 - k0)) with (- (2 * (k0 * L))) by ring.
    rewrite Rabs_Ropp, Rabs_mult, (Rabs_pos_eq 2) by lra. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Everything above must show a SUBSET of the three             *)
(* classical-reals axioms (docs/axiom-allowlist.txt).  In particular          *)
(* degenerate_H_mvt and the two _via_interface theorems must NOT show         *)
(* Classical_Prop.classic: the MVT witness is exhibited, not deduced.         *)
(* -------------------------------------------------------------------------- *)

Print Assumptions degenerate_root_exact.
Print Assumptions degenerate_strictly_increasing.
Print Assumptions degenerate_unique_positive_root.
Print Assumptions degenerate_H_deriv.
Print Assumptions degenerate_H_fprime_pos.
Print Assumptions degenerate_branch_trivial.
Print Assumptions degenerate_H_mvt.
Print Assumptions degenerate_strictly_increasing_via_interface.
Print Assumptions degenerate_unique_root_via_interface.
Print Assumptions degenerate_root_is_chord_length.
Print Assumptions clothoid_f_at_zero.
Print Assumptions clothoid_fprime_at_zero.
Print Assumptions clothoid_P_uint.
Print Assumptions clothoid_Q_uint.
Print Assumptions clothoid_R_uint.
Print Assumptions clothoid_T_uint.
Print Assumptions g_cos_lip.
Print Assumptions g_sin_lip.
Print Assumptions clothoid_PQ_odd_heading.
Print Assumptions clothoid_f_even.
Print Assumptions clothoid_f_mirror.
Print Assumptions clothoid_psi_reverse.
Print Assumptions clothoid_S_reverse.
Print Assumptions clothoid_f_reverse.
Print Assumptions deriv_trig_affine.
Print Assumptions uint_trig_affine.
Print Assumptions clothoid_arc_moments.
Print Assumptions clothoid_f_arc.
Print Assumptions clothoid_fprime_arc.
Print Assumptions clothoid_fprime_arc_zero_at_pi.
Print Assumptions clothoid_fprime_arc_neg_past_pi.
Print Assumptions clothoid_fprime_pos_symmetric.
