(* AlpogeIntegralQED.v -- allowlist-clean integration facts, and the
   refined main-line lemma windowHyp_of_rpow of the claimed RH/GRH Lean
   development (CocoSgt/riemann-hypothesis-lean @ 7cbf7a0) proved over R.

   Stdlib's continuity_implies_RiemannInt / RiemannInt_P6 reach
   Classical_Prop.classic through Heine_cor2 and the equidistant
   subdivision SubEqui (via maxN); MVT and Rolle carry it too
   (docs/attacks/2026-11-22-alpoge-integral-slice.md).  Here, within the
   three-axiom allowlist (docs/axiom-allowlist.txt):

   - RI_lipschitz: a Lipschitz function on [a, b] is Riemann_integrable
     (Stdlib's definition), via an equidistant subdivision built directly
     (StepFun_P38, StepFun_P4, StepFun_P18 are allowlist-clean);
   - rsum_inv_cv: the uniform Riemann sums of 1/y on [a, b] (0 < a <= b)
     converge to Lc b - Lc a, by bracketing with
     (x'-x)/x' <= Lc x' - Lc x <= (x'-x)/x  (no mean value theorem);
   - windowHyp_of_rpow (WindowHypOfRpow.lean): WindowHyp from the rpow
     window bound, with the window integral int R y^(-theta-1) proved to
     be |C| delta Lc Y.

   NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import Reals Lra Psatz List ZArith Lia RList RiemannInt_SF RiemannInt.
From NTS.Proofs.Probes Require Import AlpogeRealsQED AlpogeRealsQED2 AlpogeDeepStatements AlpogeRealsQED3.
Import ListNotations.
Local Open Scope R_scope.

(* ===================================================================== *)
(* Part A: an allowlist-clean equidistant subdivision and RI_lipschitz    *)
(* ===================================================================== *)
Definition eq_pt (a b : R) (N : nat) (i : nat) : R := a + INR i * (b - a) / INR N.
Definition eqlist (a b : R) (N : nat) : list R := map (eq_pt a b N) (seq 0 (S N)).

Lemma pos_Rl_map_seq : forall (f : nat -> R) len s i, (i < len)%nat -> pos_Rl (map f (seq s len)) i = f (s + i)%nat.
Proof.
  intros f len. induction len as [|len IH]; intros s i Hi; [lia|].
  simpl. destruct i as [|i]; [rewrite Nat.add_0_r; reflexivity|].
  rewrite IH by lia. f_equal. lia.
Qed.

Lemma eqlist_len : forall a b N, length (eqlist a b N) = S N.
Proof. intros. unfold eqlist. rewrite length_map, length_seq. reflexivity. Qed.

Lemma eqlist_pos : forall a b N i, (i <= N)%nat -> pos_Rl (eqlist a b N) i = eq_pt a b N i.
Proof. intros a b N i Hi. unfold eqlist. rewrite pos_Rl_map_seq by lia. reflexivity. Qed.

Lemma eqlist_ordered : forall a b N, a <= b -> (1 <= N)%nat -> ordered_Rlist (eqlist a b N).
Proof.
  intros a b N Hab HN i Hi. rewrite eqlist_len in Hi. simpl in Hi.
  rewrite !eqlist_pos by lia. unfold eq_pt.
  assert (HNr : 0 < INR N) by (apply lt_0_INR; lia).
  rewrite S_INR. unfold Rdiv.
  assert (0 <= (b - a) * / INR N) by (apply Rmult_le_pos; [lra|left; apply Rinv_0_lt_compat; lra]). nra.
Qed.

Lemma eqlist_first : forall a b N, pos_Rl (eqlist a b N) 0 = a.
Proof. intros. rewrite eqlist_pos by lia. unfold eq_pt. simpl. unfold Rdiv. ring. Qed.

Lemma eqlist_last : forall a b N, (1 <= N)%nat -> pos_Rl (eqlist a b N) (pred (length (eqlist a b N))) = b.
Proof.
  intros a b N HN. rewrite eqlist_len. cbn [pred]. rewrite eqlist_pos by lia. unfold eq_pt.
  assert (0 < INR N) by (apply lt_0_INR; lia). field. lra.
Qed.

(* index of the cell containing t in [a, b): k with x_k <= t < x_(k+1) *)
Lemma cell_index : forall a b (N : nat) t, a < b -> (1 <= N)%nat -> a <= t < b ->
  exists k, (k < N)%nat /\ eq_pt a b N k <= t < eq_pt a b N (S k).
Proof.
  intros a b N t Hab HN [Ht1 Ht2].
  assert (HNr : 0 < INR N) by (apply lt_0_INR; lia).
  set (r := (t - a) * INR N / (b - a)).
  assert (Hr0 : 0 <= r) by (unfold r; apply Rmult_le_pos; [nra|left; apply Rinv_0_lt_compat; lra]).
  assert (HrN : r < INR N).
  { unfold r. apply (Rmult_lt_reg_r (b - a)); [lra|]. replace ((t - a) * INR N / (b - a) * (b - a)) with ((t - a) * INR N) by (field; lra). nra. }
  destruct (archimed r) as [Hu1 Hu2].
  assert (Hz0 : (0 < up r)%Z) by (apply lt_IZR; lra).
  assert (Hz : (1 <= up r)%Z) by lia.
  exists (Z.to_nat (up r - 1)).
  assert (Hk : INR (Z.to_nat (up r - 1)) = IZR (up r) - 1).
  { rewrite INR_IZR_INZ, Z2Nat.id by lia. rewrite minus_IZR. reflexivity. }
  assert (Hkr : INR (Z.to_nat (up r - 1)) <= r) by lra.
  assert (Hrk : r < INR (Z.to_nat (up r - 1)) + 1) by lra.
  split.
  - apply INR_lt. lra.
  - unfold eq_pt. rewrite S_INR. split.
    + apply (Rplus_le_reg_r (- a)). replace (a + INR (Z.to_nat (up r - 1)) * (b - a) / INR N + - a) with (INR (Z.to_nat (up r - 1)) * ((b - a) / INR N)) by (field; lra).
      replace (t + - a) with (r * ((b - a) / INR N)) by (unfold r; field; lra).
      apply Rmult_le_compat_r; [left; apply Rdiv_lt_0_compat; lra|exact Hkr].
    + apply (Rplus_lt_reg_r (- a)). replace (a + (INR (Z.to_nat (up r - 1)) + 1) * (b - a) / INR N + - a) with ((INR (Z.to_nat (up r - 1)) + 1) * ((b - a) / INR N)) by (field; lra).
      replace (t + - a) with (r * ((b - a) / INR N)) by (unfold r; field; lra).
      apply Rmult_lt_compat_r; [apply Rdiv_lt_0_compat; lra|exact Hrk].
Qed.

(* the mesh can be made small *)
Definition meshN (a b d : R) : nat := S (Z.to_nat (up ((b - a) / d))).

Lemma meshN_spec : forall a b d, a < b -> 0 < d -> (b - a) / INR (meshN a b d) < d.
Proof.
  intros a b d Hab Hd. unfold meshN. destruct (archimed ((b - a) / d)) as [H1 _].
  assert (Hq : 0 < (b - a) / d) by (apply Rdiv_lt_0_compat; lra).
  assert (Hz : (0 <= up ((b - a) / d))%Z) by (apply le_IZR; lra).
  rewrite S_INR, INR_IZR_INZ, Z2Nat.id by exact Hz.
  assert (HN : 0 < IZR (up ((b - a) / d)) + 1) by lra.
  apply (Rmult_lt_reg_r (IZR (up ((b - a) / d)) + 1)); [exact HN|].
  replace ((b - a) / (IZR (up ((b - a) / d)) + 1) * (IZR (up ((b - a) / d)) + 1)) with (b - a) by (field; lra).
  apply (Rmult_lt_reg_r (/ d)); [apply Rinv_0_lt_compat; lra|].
  replace (d * (IZR (up ((b - a) / d)) + 1) * / d) with (IZR (up ((b - a) / d)) + 1) by (field; lra).
  unfold Rdiv in H1. lra.
Qed.

(* Riemann integrability of a Lipschitz function, within the allowlist *)
Theorem RI_lipschitz : forall (f : R -> R) (a b L : R), a < b -> 0 <= L ->
  (forall x y, a <= x <= b -> a <= y <= b -> Rabs (f x - f y) <= L * Rabs (x - y)) ->
  Riemann_integrable f a b.
Proof.
  intros f a b L Hab HL Hlip eps.
  set (e1 := eps / (2 * (b - a))).
  assert (He1 : 0 < e1) by (unfold e1; apply Rdiv_lt_0_compat; [apply cond_pos|lra]).
  set (d := e1 / (L + 1)).
  assert (Hd : 0 < d) by (unfold d; apply Rdiv_lt_0_compat; lra).
  set (N := meshN a b d).
  assert (HN : (1 <= N)%nat) by (unfold N, meshN; lia).
  assert (Hmesh : (b - a) / INR N < d) by (apply meshN_spec; lra).
  destruct (@StepFun_P38 (eqlist a b N) a b f (eqlist_ordered a b N ltac:(lra) HN) (eqlist_first a b N) (eqlist_last a b N HN))
    as [g [Hgb Hgc]].
  exists g. exists (mkStepFun (StepFun_P4 a b e1)). split.
  - intros t Ht. rewrite Rmin_left in Ht by lra. rewrite Rmax_right in Ht by lra.
    simpl. unfold fct_cte.
    destruct (Req_dec t b) as [Htb|Htb].
    + subst t. rewrite Hgb, Rminus_diag, Rabs_R0. lra.
    + destruct (cell_index a b N t Hab HN ltac:(lra)) as [k [Hk [Hk1 Hk2]]].
      assert (Hgt : g t = f (eq_pt a b N k)).
      { rewrite eqlist_len in Hgc. specialize (Hgc k ltac:(simpl; lia)). unfold constant_D_eq in Hgc.
        rewrite !eqlist_pos in Hgc by lia. apply Hgc. unfold co_interval. lra. }
      rewrite Hgt.
      assert (Hxk : a <= eq_pt a b N k <= b).
      { unfold eq_pt. assert (0 < INR N) by (apply lt_0_INR; lia). assert (0 <= INR k) by apply pos_INR.
        assert (INR k <= INR N) by (apply le_INR; lia). split.
        - assert (0 <= INR k * (b - a) / INR N) by (apply Rmult_le_pos; [nra|left; apply Rinv_0_lt_compat; lra]). lra.
        - apply (Rplus_le_reg_r (- a)). replace (a + INR k * (b - a) / INR N + - a) with (INR k * ((b - a) / INR N)) by (field; lra).
          replace (b + - a) with (INR N * ((b - a) / INR N)) by (field; lra).
          apply Rmult_le_compat_r; [left; apply Rdiv_lt_0_compat; lra|lra]. }
      assert (Hstep : eq_pt a b N (S k) - eq_pt a b N k = (b - a) / INR N).
      { unfold eq_pt. rewrite S_INR. assert (0 < INR N) by (apply lt_0_INR; lia). field. lra. }
      assert (Hdist : Rabs (t - eq_pt a b N k) < d) by (rewrite Rabs_pos_eq by lra; lra).
      eapply Rle_trans; [apply (Hlip t _ ltac:(lra) Hxk)|].
      apply Rle_trans with (L * d); [apply Rmult_le_compat_l; lra|].
      unfold d. assert (L * (e1 / (L + 1)) <= e1).
      { replace (L * (e1 / (L + 1))) with (e1 * (L / (L + 1))) by (field; lra).
        assert (L / (L + 1) <= 1) by (apply (Rmult_le_reg_r (L + 1)); [lra|]; replace (L / (L + 1) * (L + 1)) with L by (field; lra); lra).
        nra. }
      lra.
  - rewrite StepFun_P18. unfold e1. rewrite Rabs_pos_eq.
    + replace (eps / (2 * (b - a)) * (b - a)) with (eps / 2) by (field; lra). pose proof (cond_pos eps). lra.
    + apply Rmult_le_pos; [left; exact He1|lra].
Qed.

Print Assumptions RI_lipschitz.

(* ===================================================================== *)
(* Part B: the integral of 1/y, by bracketing                             *)
(* ===================================================================== *)
Lemma Lc_mult : forall x y, 0 < x -> 0 < y -> Lc (x * y) = Lc x + Lc y.
Proof.
  intros x y Hx Hy. apply exp_inj. rewrite exp_plus, !exp_Lc; [reflexivity|lra|lra|apply Rmult_lt_0_compat; lra].
Qed.

Lemma Lc_inv : forall x, 0 < x -> Lc (/ x) = - Lc x.
Proof.
  intros x Hx. assert (H : Lc (x * / x) = Lc x + Lc (/ x)) by (apply Lc_mult; [lra|apply Rinv_0_lt_compat; lra]).
  rewrite Rinv_r in H by lra. rewrite Lc_1 in H. lra.
Qed.

(* (x'-x)/x' <= Lc x' - Lc x <= (x'-x)/x *)
Lemma Lc_bracket : forall x x', 0 < x -> x <= x' ->
  (x' - x) / x' <= Lc x' - Lc x <= (x' - x) / x.
Proof.
  intros x x' Hx Hxx.
  assert (Hx' : 0 < x') by lra.
  assert (Ht : Lc x' - Lc x = Lc (x' / x)).
  { unfold Rdiv. rewrite Lc_mult, Lc_inv by (try apply Rinv_0_lt_compat; lra). ring. }
  assert (Hxx0 : 0 < x' / x) by (apply Rdiv_lt_0_compat; lra).
  split.
  - pose proof (Lc_le_sub1 (/ (x' / x)) ltac:(apply Rinv_0_lt_compat; lra)) as H.
    rewrite Lc_inv in H by lra. rewrite Ht.
    replace ((x' - x) / x') with (1 - / (x' / x)) by (field; lra). lra.
  - pose proof (Lc_le_sub1 (x' / x) Hxx0) as H. rewrite Ht.
    replace ((x' - x) / x) with (x' / x - 1) by (field; lra). exact H.
Qed.

Lemma sum_telescope : forall (F : nat -> R) (n : nat),
  sum_f_R0 (fun j => F (S j) - F j) n = F (S n) - F O.
Proof. intros F n. induction n as [|n IH]; simpl; [reflexivity|rewrite IH; ring]. Qed.

Lemma sum_le_pt : forall (A B : nat -> R) (n : nat), (forall j, (j <= n)%nat -> A j <= B j) ->
  sum_f_R0 A n <= sum_f_R0 B n.
Proof. intros A B n H. apply sum_Rle. intros j Hj. apply H. exact Hj. Qed.

Theorem rsum_inv_cv : forall a b, 0 < a -> a <= b -> Un_cv (RSum (fun y => / y) a b) (Lc b - Lc a).
Proof.
  intros a b Ha Hab.
  assert (Hbnd : forall n, 0 <= RSum (fun y => / y) a b n - (Lc b - Lc a) <= (b - a) * (/ a - / b) / INR (S n)).
  { intro n. unfold RSum.
    set (h := (b - a) / INR (S n)).
    assert (HSn : 0 < INR (S n)) by (apply lt_0_INR; lia).
    assert (Hh : 0 <= h) by (unfold h; apply Rmult_le_pos; [lra|left; apply Rinv_0_lt_compat; lra]).
    set (x := fun j : nat => a + INR j * h).
    assert (Hxpt : forall j, a + INR j * (b - a) / INR (S n) = x j) by (intro j; unfold x, h; field; lra).
    assert (Hxpos : forall j, a <= x j) by (intro j; unfold x; assert (0 <= INR j) by apply pos_INR; nra).
    assert (HxS : forall j, x (S j) = x j + h) by (intro j; unfold x; rewrite S_INR; ring).
    assert (Hxend : x (S n) = b) by (unfold x, h; field; lra).
    assert (Hx0 : x O = a) by (unfold x; simpl; ring).
    assert (Hsum : h * sum_f_R0 (fun j => / (a + INR j * (b - a) / INR (S n))) n
                   = sum_f_R0 (fun j => h * / x j) n).
    { rewrite <- sum_scal_l. apply sum_eq. intros j _. rewrite Hxpt. reflexivity. }
    rewrite Hsum.
    assert (Htel : Lc b - Lc a = sum_f_R0 (fun j => Lc (x (S j)) - Lc (x j)) n)
      by (rewrite (sum_telescope (fun k => Lc (x k))); cbv beta; rewrite Hxend, Hx0; reflexivity).
    rewrite Htel. split.
    - (* h / x_j >= Lc x_(j+1) - Lc x_j *)
      assert (sum_f_R0 (fun j => Lc (x (S j)) - Lc (x j)) n <= sum_f_R0 (fun j => h * / x j) n).
      { apply sum_le_pt. intros j _. pose proof (Hxpos j).
        destruct (Lc_bracket (x j) (x (S j)) ltac:(lra) ltac:(rewrite HxS; lra)) as [_ H2].
        rewrite HxS in H2 |- *. replace (x j + h - x j) with h in H2 by ring. unfold Rdiv in H2. lra. }
      lra.
    - (* h / x_j - (Lc x_(j+1) - Lc x_j) <= h / x_j - h / x_(j+1), which telescopes *)
      assert (H1 : sum_f_R0 (fun j => h * / x j) n - sum_f_R0 (fun j => Lc (x (S j)) - Lc (x j)) n
                   <= sum_f_R0 (fun j => h * / x j - h * / x (S j)) n).
      { rewrite <- minus_sum. apply sum_le_pt. intros j _. pose proof (Hxpos j).
        destruct (Lc_bracket (x j) (x (S j)) ltac:(lra) ltac:(rewrite HxS; lra)) as [H1 _].
        replace (x (S j) - x j) with h in H1 by (rewrite HxS; ring). unfold Rdiv in H1. lra. }
      assert (H2 : sum_f_R0 (fun j => h * / x j - h * / x (S j)) n = h * / a - h * / b).
      { transitivity (sum_f_R0 (fun j => (fun k => - (h * / x k)) (S j) - (fun k => - (h * / x k)) j) n).
        - apply sum_eq. intros j _. cbv beta. ring.
        - rewrite (sum_telescope (fun k => - (h * / x k))). cbv beta. rewrite Hxend, Hx0. ring. }
      assert (H3 : h * / a - h * / b = (b - a) * (/ a - / b) / INR (S n)) by (unfold h; field; lra).
      lra. }
  intros eps He.
  destruct (inv_Sn_cv ((b - a) * (/ a - / b)) eps He) as [N HN].
  exists N. intros n Hn. specialize (HN n Hn). unfold R_dist in *. rewrite Rminus_0_r in HN.
  destruct (Hbnd n) as [H1 H2].
  rewrite Rabs_pos_eq by lra. rewrite Rabs_pos_eq in HN.
  - lra.
  - lra.
Qed.

Print Assumptions rsum_inv_cv.

(* ===================================================================== *)
(* Part C: windowHyp_of_rpow                                              *)
(* ===================================================================== *)
Lemma rpc_neg1 : forall y, 0 < y -> rpc y (-1) = / y.
Proof. intros y Hy. unfold rpc. replace (-1 * Lc y) with (- Lc y) by ring. rewrite exp_Ropp, exp_Lc by exact Hy. reflexivity. Qed.

(* WindowHyp F theta delta (CharFamily.lean l.41), over R, with the window
   integral as an IntVal (Riemann_integrable + limit of uniform Riemann sums) *)
Definition WindowHypR (GmF : R -> R) (theta delta : R) : Prop :=
  forall eta, 0 < eta -> forall Y0, exists Y, Y0 <= Y /\ exists Rf : R -> R,
    (exists I, IntVal (fun y => Rf y * rpc y (- theta - 1)) Y (rpc Y (1 + delta)) I /\ I <= rpc Y eta) /\
    (forall y, Y <= y -> y <= rpc Y (1 + delta) -> 0 <= Rf y /\ GmF y <= Rf y).

Theorem windowHyp_of_rpow : forall (GmF : R -> R) theta delta C, 0 < delta ->
  (forall Y0, exists Y, Y0 <= Y /\ forall y, Y <= y -> y <= rpc Y (1 + delta) -> GmF y <= C * rpc y theta) ->
  WindowHypR GmF theta delta.
Proof.
  intros GmF theta delta C Hd h eta Heta Y0.
  destruct (windowHyp_of_rpow_eventually (Rabs C * delta) eta ltac:(pose proof (Rabs_pos C); nra) Heta) as [Y1 HY1].
  destruct (h (Rmax Y0 (Rmax Y1 2))) as [Y [HY Hwin]].
  assert (HY0 : Y0 <= Y) by (eapply Rle_trans; [apply Rmax_l|exact HY]).
  assert (HYY1 : Y1 <= Y) by (eapply Rle_trans; [|exact HY]; eapply Rle_trans; [apply Rmax_l|apply Rmax_r]).
  assert (HY2 : 2 <= Y) by (eapply Rle_trans; [|exact HY]; eapply Rle_trans; [apply Rmax_r|apply Rmax_r]).
  destruct (HY1 Y HYY1) as [_ HK].
  exists Y. split; [exact HY0|].
  set (b := rpc Y (1 + delta)).
  assert (HLc : 0 < Lc Y) by (apply exp_lt_inv'; rewrite exp_Lc, exp_0 by lra; lra).
  assert (Hb : Y < b).
  { unfold b. rewrite <- (rpc_one Y) at 1 by lra. unfold rpc. apply exp_lt_mono. nra. }
  exists (fun y => Rabs C * rpc y theta). split.
  - exists (Rabs C * (Lc b - Lc Y)). split; [split|].
    + (* integrability: the integrand is |C|/y on [Y, b], Lipschitz with constant |C|/Y^2 *)
      assert (RI : Riemann_integrable (fun y => Rabs C * rpc y theta * rpc y (- theta - 1)) Y b).
      { apply (@Riemann_integrable_ext (fun y => Rabs C * / y) (fun y => Rabs C * rpc y theta * rpc y (- theta - 1)) Y b).
      * intros y Hy. rewrite Rmin_left in Hy by lra. rewrite Rmax_right in Hy by lra.
        rewrite Rmult_assoc, <- rpc_add. replace (theta + (- theta - 1)) with (-1) by ring.
        rewrite rpc_neg1 by lra. reflexivity.
      * apply (RI_lipschitz _ Y b (Rabs C / (Y * Y))); [exact Hb|apply Rmult_le_pos; [apply Rabs_pos|left; apply Rinv_0_lt_compat; nra]|].
        intros x y Hx Hy.
        replace (Rabs C * / x - Rabs C * / y) with (Rabs C * ((y - x) / (x * y))) by (field; lra).
        rewrite Rabs_mult, (Rabs_pos_eq (Rabs C)) by apply Rabs_pos.
        unfold Rdiv. rewrite Rabs_mult, (Rabs_pos_eq (/ (x * y))) by (left; apply Rinv_0_lt_compat; nra).
        rewrite (Rabs_minus_sym y x).
        assert (Hxy : / (x * y) <= / (Y * Y)) by (apply Rinv_le_contravar; nra).
        pose proof (Rabs_pos C). pose proof (Rabs_pos (x - y)).
        assert (Rabs (x - y) * / (x * y) <= Rabs (x - y) * / (Y * Y)) by (apply Rmult_le_compat_l; lra).
        replace (Rabs C * / (Y * Y) * Rabs (x - y)) with (Rabs C * (Rabs (x - y) * / (Y * Y))) by ring.
        apply Rmult_le_compat_l; lra. }
      exact (ex_intro _ RI I).
    + (* the value: uniform sums of |C|/y converge to |C| (Lc b - Lc Y) *)
      assert (Hext : forall n, RSum (fun y => Rabs C * rpc y theta * rpc y (- theta - 1)) Y b n
                               = Rabs C * RSum (fun y => / y) Y b n).
      { intro n. unfold RSum. rewrite <- Rmult_assoc, (Rmult_comm (Rabs C)), Rmult_assoc. f_equal.
        rewrite <- sum_scal_l. apply sum_eq. intros j Hj.
        assert (HSn : 0 < INR (S n)) by (apply lt_0_INR; lia).
        assert (Hy : 0 < Y + INR j * (b - Y) / INR (S n)).
        { assert (0 <= INR j) by apply pos_INR. assert (0 <= INR j * (b - Y) / INR (S n)) by (apply Rmult_le_pos; [nra|left; apply Rinv_0_lt_compat; lra]). lra. }
        rewrite Rmult_assoc, <- rpc_add. replace (theta + (- theta - 1)) with (-1) by ring. rewrite rpc_neg1 by exact Hy. reflexivity. }
      intros eps He. destruct (Rle_lt_dec (Rabs C) 0) as [HC0|HC0].
      * exists O. intros n _. rewrite Hext. assert (Rabs C = 0) by (pose proof (Rabs_pos C); lra).
        rewrite H. unfold R_dist. rewrite !Rmult_0_l, Rminus_0_r, Rabs_R0. exact He.
      * destruct (rsum_inv_cv Y b ltac:(lra) ltac:(lra) (eps / Rabs C) ltac:(apply Rdiv_lt_0_compat; lra)) as [N HN].
        exists N. intros n Hn. rewrite Hext. specialize (HN n Hn). unfold R_dist in *.
        replace (Rabs C * RSum (fun y => / y) Y b n - Rabs C * (Lc b - Lc Y))
          with (Rabs C * (RSum (fun y => / y) Y b n - (Lc b - Lc Y))) by ring.
        rewrite Rabs_mult, Rabs_Rabsolu. apply (Rmult_lt_reg_l (/ Rabs C)); [apply Rinv_0_lt_compat; lra|].
        rewrite <- Rmult_assoc, Rinv_l, Rmult_1_l by lra. unfold Rdiv in HN. lra.
    + (* the bound: |C| (Lc b - Lc Y) = |C| delta Lc Y <= Y^eta *)
      unfold b. rewrite Lc_rpc. replace (Rabs C * ((1 + delta) * Lc Y - Lc Y)) with (Rabs C * delta * Lc Y) by ring. exact HK.
  - intros y Hy1 Hy2. split.
    + apply Rmult_le_pos; [apply Rabs_pos|left; apply rpc_pos].
    + eapply Rle_trans; [apply (Hwin y Hy1 Hy2)|]. apply Rmult_le_compat_r; [left; apply rpc_pos|apply Rle_abs].
Qed.

Print Assumptions windowHyp_of_rpow.
