(* ============================================================================
   NetTopologySuite.Proofs.FresnelSeries
   ----------------------------------------------------------------------------
   S6 of the transcendental programme: the Fresnel power series as a
   specification, kept separate from any evaluator, and proved equal to the
   existing clothoid integrals (SheetHenClothoidCore.cloth_Icos / cloth_Isin,
   the 3-axiom LipInt.int_seg primitives).

   S6A (pure series).  For psi(u) = a u^2 the partial sums
     fz_C n a s = sum_{k<=n} (-1)^k a^(2k)   s^(4k+1) / ((2k)!   (4k+1))
     fz_S n a s = sum_{k<=n} (-1)^k a^(2k+1) s^(4k+3) / ((2k+1)! (4k+3))
   are the term-wise primitives of the Taylor polynomials of cos(a s^2),
   sin(a s^2).  fz_taylor gives the Taylor remainders of cos / sin for ALL
   real x (Stdlib cos_bound / sin_bound stop at pi/2 / pi), and fz_C_rem /
   fz_S_rem bound any primitive F (F 0 = 0, F' = cos(a s^2) resp.
   sin(a s^2)) against the partial sum with an explicit remainder:
     |F s - fz_C n a s| <= |a|^(2n+2) |s|^(4n+5) / ((2n+2)! (4n+5))
     |F s - fz_S n a s| <= |a|^(2n+3) |s|^(4n+7) / ((2n+3)! (4n+7)).
   S6B (equivalence).  With a = cloth_a c (cloth_psi c s = a s^2):
     fresnel_C_series_rem / fresnel_S_series_rem   the remainder lines
     fresnel_C_series / fresnel_S_series           Un_cv of the partial
                                                   sums to cloth_Icos /
                                                   cloth_Isin, every c, s.
   No series is differentiated: the only analysis is the classic-free
   RealMonotone.deriv_nonneg_incr and ClothoidTangent.cloth_I*_deriv; the
   axiom spike (Print Assumptions below) is the 3-axiom base.
   claimId: s6-fresnel-series.  witness: fresnel_C_series.
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia.
From Stdlib Require Import Ranalysis1 Factorial.
From NTS.Proofs Require Import RealMonotone LipInt SheetHenClothoidCore ClothoidTangent.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Value bounds from derivative bounds (classic-free).                    *)
(* -------------------------------------------------------------------------- *)

Lemma fz_abs_le_inv : forall x y, Rabs x <= y -> - y <= x <= y.
Proof. intros x y H. unfold Rabs in H. destruct (Rcase_abs x); lra. Qed.

Lemma fz_mono_bound : forall (f f' g g' : R -> R) x,
  0 <= x -> f 0 = 0 -> g 0 = 0 ->
  (forall t, 0 <= t <= x -> derivable_pt_lim f t (f' t)) ->
  (forall t, 0 <= t <= x -> derivable_pt_lim g t (g' t)) ->
  (forall t, 0 <= t <= x -> Rabs (f' t) <= g' t) ->
  Rabs (f x) <= g x.
Proof.
  intros f f' g g' x Hx F0 G0 Df Dg Hb.
  assert (A : g 0 - f 0 <= g x - f x).
  { apply (deriv_nonneg_incr (fun t => g t - f t) (fun t => g' t - f' t) 0 x 0 x).
    - intros t Ht. apply derivable_pt_lim_minus with (f1 := g) (f2 := f); auto.
    - intros t Ht. specialize (Hb t Ht). apply fz_abs_le_inv in Hb. lra.
    - lra. - lra. - lra. }
  assert (B : g 0 + f 0 <= g x + f x).
  { apply (deriv_nonneg_incr (fun t => g t + f t) (fun t => g' t + f' t) 0 x 0 x).
    - intros t Ht. apply derivable_pt_lim_plus with (f1 := g) (f2 := f); auto.
    - intros t Ht. specialize (Hb t Ht). apply fz_abs_le_inv in Hb. lra.
    - lra. - lra. - lra. }
  rewrite F0, G0 in *. apply Rabs_le. split; lra.
Qed.

Lemma fz_opp_deriv : forall t, derivable_pt_lim (fun y => - y) t (-1).
Proof.
  intro t. eapply derivable_pt_lim_ext;
    [| exact (derivable_pt_lim_opp id t 1 (derivable_pt_lim_id t))].
  intro z. unfold opp_fct, id. reflexivity.
Qed.

(* Both signs of x, for a bound depending on |t| only. *)
Lemma fz_mono_bound_abs : forall (f f' G G' : R -> R),
  f 0 = 0 -> G 0 = 0 ->
  (forall t, derivable_pt_lim f t (f' t)) ->
  (forall t, 0 <= t -> derivable_pt_lim G t (G' t)) ->
  (forall t, Rabs (f' t) <= G' (Rabs t)) ->
  forall x, Rabs (f x) <= G (Rabs x).
Proof.
  intros f f' G G' F0 G0 Df DG Hb x.
  destruct (Rle_lt_dec 0 x) as [Hx|Hx].
  - rewrite (Rabs_pos_eq x) by exact Hx.
    apply (fz_mono_bound f f' G G' x Hx F0 G0).
    + intros t _. apply Df.
    + intros t Ht. apply DG. lra.
    + intros t Ht. specialize (Hb t). rewrite (Rabs_pos_eq t) in Hb by lra. exact Hb.
  - rewrite (Rabs_left x) by exact Hx.
    replace (f x) with ((fun t => f (- t)) (- x)) by (cbn beta; rewrite Ropp_involutive; reflexivity).
    apply (fz_mono_bound (fun t => f (- t)) (fun t => - f' (- t)) G G' (- x));
      [lra | cbn beta; rewrite Ropp_0; exact F0 | exact G0 | | |].
    + intros t _.
      assert (Hc := derivable_pt_lim_comp (fun y => - y) f t (-1) (f' (- t))
                      (fz_opp_deriv t) (Df (- t))).
      replace (- f' (- t)) with (f' (- t) * -1) by ring.
      eapply derivable_pt_lim_ext; [| exact Hc]. intro z. unfold comp. reflexivity.
    + intros t Ht. apply DG. lra.
    + intros t Ht. rewrite Rabs_Ropp. specialize (Hb (- t)).
      rewrite Rabs_Ropp, (Rabs_pos_eq t) in Hb by lra. exact Hb.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Derivatives of the Taylor polynomials.                                 *)
(* -------------------------------------------------------------------------- *)

Lemma fz_INR_fact_S : forall n, INR (fact (S n)) = INR (S n) * INR (fact n).
Proof. intro n. rewrite fact_simpl, mult_INR. reflexivity. Qed.

Lemma fz_fact_nz : forall n, INR (fact n) <> 0.
Proof. intro n. apply Rgt_not_eq, INR_fact_lt_0. Qed.

Lemma fz_S_nz : forall n, INR (S n) <> 0.
Proof. intro n. apply not_0_INR. lia. Qed.

Lemma fz_pow_deriv : forall (K : R) (m : nat) t,
  derivable_pt_lim (fun y => K * y ^ S m) t (K * INR (S m) * t ^ m).
Proof.
  intros K m t.
  assert (H := derivable_pt_lim_scal (fun y => y ^ S m) K t _ (derivable_pt_lim_pow t (S m))).
  cbn [pred] in H.
  replace (K * INR (S m) * t ^ m) with (K * (INR (S m) * t ^ m)) by ring.
  eapply derivable_pt_lim_ext; [| exact H]. intro z. unfold mult_real_fct. reflexivity.
Qed.

Lemma fz_sin_term_deriv : forall i t,
  derivable_pt_lim (fun x => sin_term x i) t (cos_term t i).
Proof.
  intros i t. unfold sin_term, cos_term.
  replace (2 * i + 1)%nat with (S (2 * i)) by lia.
  pose proof (fz_pow_deriv ((-1) ^ i / INR (fact (S (2 * i)))) (2 * i) t) as H.
  pose proof (fz_fact_nz (2 * i)). pose proof (fz_S_nz (2 * i)).
  replace ((-1) ^ i * (t ^ (2 * i) / INR (fact (2 * i))))
    with ((-1) ^ i / INR (fact (S (2 * i))) * INR (S (2 * i)) * t ^ (2 * i))
    by (rewrite fz_INR_fact_S; field; split; assumption).
  eapply derivable_pt_lim_ext; [| exact H]. intro z. unfold Rdiv. ring.
Qed.

Lemma fz_cos_term_deriv : forall i t,
  derivable_pt_lim (fun x => cos_term x (S i)) t (- sin_term t i).
Proof.
  intros i t. unfold sin_term, cos_term.
  replace (2 * S i)%nat with (S (2 * i + 1)) by lia.
  pose proof (fz_pow_deriv ((-1) ^ S i / INR (fact (S (2 * i + 1)))) (2 * i + 1) t) as H.
  pose proof (fz_fact_nz (2 * i + 1)). pose proof (fz_S_nz (2 * i + 1)).
  replace (- ((-1) ^ i * (t ^ (2 * i + 1) / INR (fact (2 * i + 1)))))
    with ((-1) ^ S i / INR (fact (S (2 * i + 1))) * INR (S (2 * i + 1)) * t ^ (2 * i + 1))
    by (rewrite fz_INR_fact_S; change ((-1) ^ S i) with (-1 * (-1) ^ i);
        field; split; assumption).
  eapply derivable_pt_lim_ext; [| exact H]. intro z. unfold Rdiv. ring.
Qed.

Lemma fz_sin_approx_deriv : forall n t,
  derivable_pt_lim (fun x => sin_approx x n) t (cos_approx t n).
Proof.
  induction n as [|n IH]; intro t.
  - eapply derivable_pt_lim_ext; [| exact (fz_sin_term_deriv 0 t)].
    intro z. unfold sin_approx. reflexivity.
  - eapply derivable_pt_lim_ext;
      [| exact (derivable_pt_lim_plus _ _ t _ _ (IH t) (fz_sin_term_deriv (S n) t))].
    intro z. unfold plus_fct, sin_approx. reflexivity.
Qed.

Lemma fz_cos_term0_deriv : forall t, derivable_pt_lim (fun x => cos_term x 0) t 0.
Proof.
  intro t. eapply derivable_pt_lim_ext; [| exact (derivable_pt_lim_const 1 t)].
  intro z. unfold fct_cte, cos_term. cbn. field.
Qed.

Lemma fz_cos_approx_deriv : forall n t,
  derivable_pt_lim (fun x => cos_approx x (S n)) t (- sin_approx t n).
Proof.
  induction n as [|n IH]; intro t.
  - assert (H := derivable_pt_lim_plus _ _ t _ _ (fz_cos_term0_deriv t) (fz_cos_term_deriv 0 t)).
    replace (- sin_approx t 0) with (0 + - sin_term t 0) by (unfold sin_approx; cbn [sum_f_R0]; ring).
    eapply derivable_pt_lim_ext; [| exact H].
    intro z. unfold plus_fct, cos_approx. reflexivity.
  - assert (H := derivable_pt_lim_plus _ _ t _ _ (IH t) (fz_cos_term_deriv (S n) t)).
    replace (- sin_approx t (S n)) with (- sin_approx t n + - sin_term t (S n))
      by (unfold sin_approx; cbn [sum_f_R0]; ring).
    eapply derivable_pt_lim_ext; [| exact H].
    intro z. unfold plus_fct, cos_approx. reflexivity.
Qed.

Lemma fz_cos_approx0_deriv : forall t, derivable_pt_lim (fun x => cos_approx x 0) t 0.
Proof.
  intro t. eapply derivable_pt_lim_ext; [| exact (fz_cos_term0_deriv t)].
  intro z. unfold cos_approx. reflexivity.
Qed.

Lemma fz_cos_approx_at0 : forall n, cos_approx 0 n = 1.
Proof.
  induction n as [|n IH].
  - unfold cos_approx, cos_term. cbn. field.
  - unfold cos_approx in *. cbn [sum_f_R0]. rewrite IH. unfold cos_term.
    rewrite pow_i by lia. unfold Rdiv. ring.
Qed.

Lemma fz_sin_approx_at0 : forall n, sin_approx 0 n = 0.
Proof.
  induction n as [|n IH]; unfold sin_approx in *; cbn [sum_f_R0];
    [|rewrite IH]; unfold sin_term; rewrite pow_i by lia; unfold Rdiv; ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Taylor remainders of cos and sin on all of R.                          *)
(* -------------------------------------------------------------------------- *)

Lemma fz_G_deriv : forall k t,
  derivable_pt_lim (fun y => y ^ S k / INR (fact (S k))) t (t ^ k / INR (fact k)).
Proof.
  intros k t.
  pose proof (fz_pow_deriv (/ INR (fact (S k))) k t) as H.
  pose proof (fz_fact_nz k). pose proof (fz_S_nz k).
  replace (t ^ k / INR (fact k)) with (/ INR (fact (S k)) * INR (S k) * t ^ k)
    by (rewrite fz_INR_fact_S; field; split; assumption).
  eapply derivable_pt_lim_ext; [| exact H]. intro z. unfold Rdiv. ring.
Qed.

Lemma fz_step : forall (f f' : R -> R) k,
  f 0 = 0 -> (forall t, derivable_pt_lim f t (f' t)) ->
  (forall t, Rabs (f' t) <= Rabs t ^ k / INR (fact k)) ->
  forall x, Rabs (f x) <= Rabs x ^ S k / INR (fact (S k)).
Proof.
  intros f f' k F0 Df Hb x.
  apply (fz_mono_bound_abs f f' (fun y => y ^ S k / INR (fact (S k)))
           (fun y => y ^ k / INR (fact k)) F0).
  - cbn [pow]. unfold Rdiv. ring.
  - exact Df.
  - intros t _. apply fz_G_deriv.
  - exact Hb.
Qed.

Lemma fz_sin_le : forall x, Rabs (sin x) <= Rabs x.
Proof.
  intro x.
  assert (Hb : forall t, Rabs (cos t) <= Rabs t ^ 0 / INR (fact 0)).
  { intro t. replace (Rabs t ^ 0 / INR (fact 0)) with 1 by (cbn; field).
    apply Rabs_le. apply COS_bound. }
  pose proof (fz_step sin cos 0 sin_0 derivable_pt_lim_sin Hb x) as H.
  replace (Rabs x ^ 1 / INR (fact 1)) with (Rabs x) in H by (cbn; field).
  exact H.
Qed.

(* Taylor remainders, all real x: orders 2n+2 (cos) and 2n+3 (sin). *)
Theorem fz_taylor : forall n x,
  Rabs (cos x - cos_approx x n) <= Rabs x ^ (2 * n + 2) / INR (fact (2 * n + 2)) /\
  Rabs (sin x - sin_approx x n) <= Rabs x ^ (2 * n + 3) / INR (fact (2 * n + 3)).
Proof.
  induction n as [|n IH]; intro x.
  - assert (Hc : forall y, Rabs (cos y - cos_approx y 0) <= Rabs y ^ 2 / INR (fact 2)).
    { intro y.
      apply (fz_step (fun z => cos z - cos_approx z 0) (fun t => - sin t - 0) 1).
      - cbn beta. rewrite cos_0, fz_cos_approx_at0. ring.
      - intro t. apply derivable_pt_lim_minus with (f1 := cos) (f2 := fun z => cos_approx z 0);
          [apply derivable_pt_lim_cos | apply fz_cos_approx0_deriv].
      - intro t. replace (- sin t - 0) with (- sin t) by ring. rewrite Rabs_Ropp.
        replace (Rabs t ^ 1 / INR (fact 1)) with (Rabs t) by (cbn; field).
        apply fz_sin_le. }
    split; [exact (Hc x)|].
    apply (fz_step (fun z => sin z - sin_approx z 0) (fun t => cos t - cos_approx t 0) 2).
    + cbn beta. rewrite sin_0, fz_sin_approx_at0. ring.
    + intro t. apply derivable_pt_lim_minus with (f1 := sin) (f2 := fun z => sin_approx z 0);
        [apply derivable_pt_lim_sin | apply fz_sin_approx_deriv].
    + exact Hc.
  - assert (Hc : forall y, Rabs (cos y - cos_approx y (S n))
                           <= Rabs y ^ (2 * S n + 2) / INR (fact (2 * S n + 2))).
    { intro y. replace (2 * S n + 2)%nat with (S (2 * n + 3)) by lia.
      apply (fz_step (fun z => cos z - cos_approx z (S n))
               (fun t => - sin t - - sin_approx t n) (2 * n + 3)).
      - cbn beta. rewrite cos_0, fz_cos_approx_at0. ring.
      - intro t. apply derivable_pt_lim_minus with (f1 := cos) (f2 := fun z => cos_approx z (S n));
          [apply derivable_pt_lim_cos | apply fz_cos_approx_deriv].
      - intro t. replace (- sin t - - sin_approx t n) with (- (sin t - sin_approx t n)) by ring.
        rewrite Rabs_Ropp. apply (IH t). }
    split; [exact (Hc x)|].
    replace (2 * S n + 3)%nat with (S (2 * S n + 2)) by lia.
    apply (fz_step (fun z => sin z - sin_approx z (S n))
             (fun t => cos t - cos_approx t (S n)) (2 * S n + 2)).
    + cbn beta. rewrite sin_0, fz_sin_approx_at0. ring.
    + intro t. apply derivable_pt_lim_minus with (f1 := sin) (f2 := fun z => sin_approx z (S n));
        [apply derivable_pt_lim_sin | apply fz_sin_approx_deriv].
    + exact Hc.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The Fresnel partial sums (S6A).                                        *)
(* -------------------------------------------------------------------------- *)

Definition fz_Cterm (a s : R) (k : nat) : R :=
  (-1) ^ k * a ^ (2 * k) * s ^ (4 * k + 1) / (INR (fact (2 * k)) * INR (4 * k + 1)).
Definition fz_Sterm (a s : R) (k : nat) : R :=
  (-1) ^ k * a ^ (2 * k + 1) * s ^ (4 * k + 3) / (INR (fact (2 * k + 1)) * INR (4 * k + 3)).

Definition fz_C (n : nat) (a s : R) : R := sum_f_R0 (fz_Cterm a s) n.
Definition fz_S (n : nat) (a s : R) : R := sum_f_R0 (fz_Sterm a s) n.

Lemma fz_pow_C : forall a s k, (a * s * s) ^ (2 * k) = a ^ (2 * k) * s ^ (4 * k).
Proof.
  intros. rewrite !Rpow_mult_distr.
  replace (4 * k)%nat with (2 * k + 2 * k)%nat by lia. rewrite pow_add. ring.
Qed.

Lemma fz_pow_S : forall a s k, (a * s * s) ^ (2 * k + 1) = a ^ (2 * k + 1) * s ^ (4 * k + 2).
Proof.
  intros. rewrite !Rpow_mult_distr.
  replace (4 * k + 2)%nat with ((2 * k + 1) + (2 * k + 1))%nat by lia.
  rewrite (pow_add s (2 * k + 1) (2 * k + 1)). ring.
Qed.

Lemma fz_Cterm_deriv : forall a k t,
  derivable_pt_lim (fun s => fz_Cterm a s k) t (cos_term (a * t * t) k).
Proof.
  intros a k t. unfold fz_Cterm, cos_term. rewrite fz_pow_C.
  replace (4 * k + 1)%nat with (S (4 * k)) by lia.
  pose proof (fz_pow_deriv ((-1) ^ k * a ^ (2 * k) / (INR (fact (2 * k)) * INR (S (4 * k))))
                (4 * k) t) as H.
  pose proof (fz_fact_nz (2 * k)). pose proof (fz_S_nz (4 * k)).
  replace ((-1) ^ k * (a ^ (2 * k) * t ^ (4 * k) / INR (fact (2 * k))))
    with ((-1) ^ k * a ^ (2 * k) / (INR (fact (2 * k)) * INR (S (4 * k)))
          * INR (S (4 * k)) * t ^ (4 * k)) by (field; split; assumption).
  eapply derivable_pt_lim_ext; [| exact H]. intro z. unfold Rdiv. ring.
Qed.

Lemma fz_Sterm_deriv : forall a k t,
  derivable_pt_lim (fun s => fz_Sterm a s k) t (sin_term (a * t * t) k).
Proof.
  intros a k t. unfold fz_Sterm, sin_term. rewrite fz_pow_S.
  replace (4 * k + 3)%nat with (S (4 * k + 2)) by lia.
  pose proof (fz_pow_deriv ((-1) ^ k * a ^ (2 * k + 1)
                            / (INR (fact (2 * k + 1)) * INR (S (4 * k + 2))))
                (4 * k + 2) t) as H.
  pose proof (fz_fact_nz (2 * k + 1)). pose proof (fz_S_nz (4 * k + 2)).
  replace ((-1) ^ k * (a ^ (2 * k + 1) * t ^ (4 * k + 2) / INR (fact (2 * k + 1))))
    with ((-1) ^ k * a ^ (2 * k + 1) / (INR (fact (2 * k + 1)) * INR (S (4 * k + 2)))
          * INR (S (4 * k + 2)) * t ^ (4 * k + 2)) by (field; split; assumption).
  eapply derivable_pt_lim_ext; [| exact H]. intro z. unfold Rdiv. ring.
Qed.

Lemma fz_C_deriv : forall n a t,
  derivable_pt_lim (fun s => fz_C n a s) t (cos_approx (a * t * t) n).
Proof.
  induction n as [|n IH]; intros a t.
  - eapply derivable_pt_lim_ext; [| exact (fz_Cterm_deriv a 0 t)].
    intro z. unfold fz_C. reflexivity.
  - eapply derivable_pt_lim_ext;
      [| exact (derivable_pt_lim_plus _ _ t _ _ (IH a t) (fz_Cterm_deriv a (S n) t))].
    intro z. unfold plus_fct, fz_C. reflexivity.
Qed.

Lemma fz_S_deriv : forall n a t,
  derivable_pt_lim (fun s => fz_S n a s) t (sin_approx (a * t * t) n).
Proof.
  induction n as [|n IH]; intros a t.
  - eapply derivable_pt_lim_ext; [| exact (fz_Sterm_deriv a 0 t)].
    intro z. unfold fz_S. reflexivity.
  - eapply derivable_pt_lim_ext;
      [| exact (derivable_pt_lim_plus _ _ t _ _ (IH a t) (fz_Sterm_deriv a (S n) t))].
    intro z. unfold plus_fct, fz_S. reflexivity.
Qed.

Lemma fz_C_at0 : forall n a, fz_C n a 0 = 0.
Proof.
  induction n as [|n IH]; intro a; unfold fz_C in *; cbn [sum_f_R0];
    [|rewrite IH]; unfold fz_Cterm; rewrite pow_i by lia; unfold Rdiv; ring.
Qed.

Lemma fz_S_at0 : forall n a, fz_S n a 0 = 0.
Proof.
  induction n as [|n IH]; intro a; unfold fz_S in *; cbn [sum_f_R0];
    [|rewrite IH]; unfold fz_Sterm; rewrite pow_i by lia; unfold Rdiv; ring.
Qed.

Lemma fz_abs_pow : forall a t m,
  Rabs (a * t * t) ^ m = Rabs a ^ m * Rabs t ^ (m + m).
Proof. intros. rewrite !Rabs_mult, !Rpow_mult_distr, pow_add. ring. Qed.

(* Remainder against any primitive of cos(a s^2). *)
Theorem fz_C_rem : forall (F : R -> R) (a : R) (n : nat),
  F 0 = 0 -> (forall s, derivable_pt_lim F s (cos (a * s * s))) ->
  forall s, Rabs (F s - fz_C n a s)
    <= Rabs a ^ (2 * n + 2) * Rabs s ^ (4 * n + 5)
       / (INR (fact (2 * n + 2)) * INR (4 * n + 5)).
Proof.
  intros F a n F0 DF s.
  set (K := Rabs a ^ (2 * n + 2) / (INR (fact (2 * n + 2)) * INR (S (4 * n + 4)))).
  replace (Rabs a ^ (2 * n + 2) * Rabs s ^ (4 * n + 5)
           / (INR (fact (2 * n + 2)) * INR (4 * n + 5)))
    with (K * Rabs s ^ S (4 * n + 4))
    by (unfold K; replace (4 * n + 5)%nat with (S (4 * n + 4)) by lia; unfold Rdiv; ring).
  apply (fz_mono_bound_abs (fun z => F z - fz_C n a z)
           (fun t => cos (a * t * t) - cos_approx (a * t * t) n)
           (fun y => K * y ^ S (4 * n + 4))
           (fun y => K * INR (S (4 * n + 4)) * y ^ (4 * n + 4))).
  - cbn beta. rewrite F0, fz_C_at0. ring.
  - cbn [pow]. ring.
  - intro t. apply derivable_pt_lim_minus with (f1 := F) (f2 := fun z => fz_C n a z);
      [apply DF | apply fz_C_deriv].
  - intros t _. apply fz_pow_deriv.
  - intro t. destruct (fz_taylor n (a * t * t)) as [Hc _].
    eapply Rle_trans; [exact Hc|].
    rewrite fz_abs_pow. replace (2 * n + 2 + (2 * n + 2))%nat with (4 * n + 4)%nat by lia.
    pose proof (fz_fact_nz (2 * n + 2)). pose proof (fz_S_nz (4 * n + 4)).
    unfold K. right. field. split; assumption.
Qed.

(* Remainder against any primitive of sin(a s^2). *)
Theorem fz_S_rem : forall (F : R -> R) (a : R) (n : nat),
  F 0 = 0 -> (forall s, derivable_pt_lim F s (sin (a * s * s))) ->
  forall s, Rabs (F s - fz_S n a s)
    <= Rabs a ^ (2 * n + 3) * Rabs s ^ (4 * n + 7)
       / (INR (fact (2 * n + 3)) * INR (4 * n + 7)).
Proof.
  intros F a n F0 DF s.
  set (K := Rabs a ^ (2 * n + 3) / (INR (fact (2 * n + 3)) * INR (S (4 * n + 6)))).
  replace (Rabs a ^ (2 * n + 3) * Rabs s ^ (4 * n + 7)
           / (INR (fact (2 * n + 3)) * INR (4 * n + 7)))
    with (K * Rabs s ^ S (4 * n + 6))
    by (unfold K; replace (4 * n + 7)%nat with (S (4 * n + 6)) by lia; unfold Rdiv; ring).
  apply (fz_mono_bound_abs (fun z => F z - fz_S n a z)
           (fun t => sin (a * t * t) - sin_approx (a * t * t) n)
           (fun y => K * y ^ S (4 * n + 6))
           (fun y => K * INR (S (4 * n + 6)) * y ^ (4 * n + 6))).
  - cbn beta. rewrite F0, fz_S_at0. ring.
  - cbn [pow]. ring.
  - intro t. apply derivable_pt_lim_minus with (f1 := F) (f2 := fun z => fz_S n a z);
      [apply DF | apply fz_S_deriv].
  - intros t _. apply fz_pow_deriv.
  - intro t. destruct (fz_taylor n (a * t * t)) as [_ Hs].
    eapply Rle_trans; [exact Hs|].
    rewrite fz_abs_pow. replace (2 * n + 3 + (2 * n + 3))%nat with (4 * n + 6)%nat by lia.
    pose proof (fz_fact_nz (2 * n + 3)). pose proof (fz_S_nz (4 * n + 6)).
    unfold K. right. field. split; assumption.
Qed.

(* The remainder tends to 0: |s| X^m / m! with X = |a| s^2, m = 2n + j. *)
Lemma fz_rem_cv : forall (A Sv : R) (j : nat) (d : nat -> nat),
  0 <= A -> 0 <= Sv -> (forall n, (1 <= INR (d n))) ->
  forall eps, 0 < eps -> exists N, forall n, (n >= N)%nat ->
    A ^ (2 * n + j) * Sv ^ (2 * (2 * n + j) + 1)
      / (INR (fact (2 * n + j)) * INR (d n)) < eps.
Proof.
  intros A Sv j d HA HS Hd eps He.
  set (X := A * (Sv * Sv)).
  assert (HX : 0 <= X) by (unfold X; apply Rmult_le_pos; [lra | apply Rmult_le_pos; lra]).
  destruct (cv_speed_pow_fact X (eps / (Sv + 1)) ltac:(apply Rdiv_lt_0_compat; lra)) as [N HN].
  exists N. intros n Hn.
  assert (Hm : (2 * n + j >= N)%nat) by lia.
  specialize (HN _ Hm). unfold R_dist in HN. rewrite Rminus_0_r in HN.
  set (m := (2 * n + j)%nat) in *.
  pose proof (INR_fact_lt_0 m) as Hf. specialize (Hd n).
  assert (Hpos : 0 <= X ^ m / INR (fact m))
    by (apply Rmult_le_pos; [apply pow_le; exact HX | left; apply Rinv_0_lt_compat; exact Hf]).
  rewrite Rabs_pos_eq in HN by exact Hpos.
  replace (A ^ m * Sv ^ (2 * m + 1) / (INR (fact m) * INR (d n)))
    with (Sv * (X ^ m / INR (fact m)) * / INR (d n)).
  2:{ unfold X. rewrite !Rpow_mult_distr.
      replace (2 * m + 1)%nat with (S (m + m)) by lia. cbn [pow]. rewrite pow_add.
      field. split; lra. }
  assert (Sv * (X ^ m / INR (fact m)) <= Sv * (eps / (Sv + 1)))
    by (apply Rmult_le_compat_l; lra).
  assert (Sv * (eps / (Sv + 1)) < eps).
  { assert (Sv / (Sv + 1) < 1).
    { apply (Rmult_lt_reg_r (Sv + 1)); [lra|].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
    replace (Sv * (eps / (Sv + 1))) with (eps * (Sv / (Sv + 1))) by (field; lra).
    nra. }
  assert (0 < / INR (d n) <= 1).
  { split; [apply Rinv_0_lt_compat; lra|].
    rewrite <- Rinv_1. apply Rinv_le_contravar; lra. }
  assert (0 <= Sv * (X ^ m / INR (fact m))) by (apply Rmult_le_pos; lra).
  assert (Sv * (X ^ m / INR (fact m)) * / INR (d n) <= Sv * (X ^ m / INR (fact m)) * 1)
    by (apply Rmult_le_compat_l; lra).
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Equivalence with the clothoid integrals (S6B).                         *)
(* -------------------------------------------------------------------------- *)

Definition cloth_a (c : ClothoidEgg) : R := cloth_sigma c / (2 * cloth_A c * cloth_A c).

Lemma cloth_psi_a : forall c s, cloth_psi c s = cloth_a c * s * s.
Proof. intros c s. unfold cloth_psi, cloth_a. unfold Rdiv. ring. Qed.

Lemma cloth_Icos_at0 : forall c, cloth_Icos c 0 = 0.
Proof. intro c. unfold cloth_Icos. apply int_seg_point. Qed.

Lemma cloth_Isin_at0 : forall c, cloth_Isin c 0 = 0.
Proof. intro c. unfold cloth_Isin. apply int_seg_point. Qed.

Theorem fresnel_C_series_rem : forall c n s,
  Rabs (cloth_Icos c s - fz_C n (cloth_a c) s)
    <= Rabs (cloth_a c) ^ (2 * n + 2) * Rabs s ^ (4 * n + 5)
       / (INR (fact (2 * n + 2)) * INR (4 * n + 5)).
Proof.
  intros c n s. apply fz_C_rem; [apply cloth_Icos_at0|].
  intro t. rewrite <- cloth_psi_a. apply cloth_Icos_deriv.
Qed.

Theorem fresnel_S_series_rem : forall c n s,
  Rabs (cloth_Isin c s - fz_S n (cloth_a c) s)
    <= Rabs (cloth_a c) ^ (2 * n + 3) * Rabs s ^ (4 * n + 7)
       / (INR (fact (2 * n + 3)) * INR (4 * n + 7)).
Proof.
  intros c n s. apply fz_S_rem; [apply cloth_Isin_at0|].
  intro t. rewrite <- cloth_psi_a. apply cloth_Isin_deriv.
Qed.

(* WITNESS {"claimId":"s6-fresnel-series","topic":"numerics","lemma":"fresnel_C_series","title":"Fresnel series = clothoid integral: for every clothoid c and station s the partial sums fz_C n (cloth_a c) s converge to cloth_Icos c s (and fz_S to cloth_Isin), with explicit remainder |a|^(2n+2)|s|^(4n+5)/((2n+2)!(4n+5)); 3-axiom","file":"theories/FresnelSeries.v","witness":"fresnel_C_series","board":"ADR-0006"} *)
Theorem fresnel_C_series : forall c s,
  Un_cv (fun n => fz_C n (cloth_a c) s) (cloth_Icos c s).
Proof.
  intros c s eps He.
  destruct (fz_rem_cv (Rabs (cloth_a c)) (Rabs s) 2 (fun n => (4 * n + 5)%nat)
              (Rabs_pos _) (Rabs_pos _)
              ltac:(intro n; replace 1 with (INR 1) by reflexivity; apply le_INR; lia)
              eps He) as [N HN].
  exists N. intros n Hn. unfold R_dist. rewrite Rabs_minus_sym.
  eapply Rle_lt_trans; [apply fresnel_C_series_rem|].
  replace (4 * n + 5)%nat with (2 * (2 * n + 2) + 1)%nat at 1 by lia.
  exact (HN n Hn).
Qed.

Theorem fresnel_S_series : forall c s,
  Un_cv (fun n => fz_S n (cloth_a c) s) (cloth_Isin c s).
Proof.
  intros c s eps He.
  destruct (fz_rem_cv (Rabs (cloth_a c)) (Rabs s) 3 (fun n => (4 * n + 7)%nat)
              (Rabs_pos _) (Rabs_pos _)
              ltac:(intro n; replace 1 with (INR 1) by reflexivity; apply le_INR; lia)
              eps He) as [N HN].
  exists N. intros n Hn. unfold R_dist. rewrite Rabs_minus_sym.
  eapply Rle_lt_trans; [apply fresnel_S_series_rem|].
  replace (4 * n + 7)%nat with (2 * (2 * n + 3) + 1)%nat at 1 by lia.
  exact (HN n Hn).
Qed.

Print Assumptions fz_taylor.
Print Assumptions fz_C_rem.
Print Assumptions fz_S_rem.
Print Assumptions fresnel_C_series_rem.
Print Assumptions fresnel_S_series_rem.
Print Assumptions fresnel_C_series.
Print Assumptions fresnel_S_series.
