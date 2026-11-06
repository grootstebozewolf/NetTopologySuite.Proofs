(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_DeCasteljau
   ----------------------------------------------------------------------------
   Binary64 forward error bound for de Casteljau evaluation of a Bezier /
   Bernstein-basis curve component (the scalar kernel behind GEOS/NTS NURBS
   and Bezier point evaluation; one call per coordinate).

   Evaluator (triangular scheme, one RNE product per weight and one RNE sum
   per node):
       node(x, y)  = fl( fl(s x) + fl(t y) )
       row_{k+1}   = [node(row_k[i], row_k[i+1])]_i,   n rounds,  value = row_n[0]
   with t a binary64 in [0,1] and s a binary64 standing for 1 - t.

   Reference: the SAME control values (after B2R) run through de Casteljau in
   R with the exact weights (1 - t, t) -- the Bernstein-basis value
   sum_i b_i B_i^n(t) (`dcR_bern`, correctness over R).

   Theorem `b64_decasteljau_err`: every control value finite with |b_i| <= M,
   |s - (1 - t)| <= eta (eta = 0 when s = 1 - t exactly, e.g. t in [1/2,1] by
   Sterbenz; eta = u + 2^-1075 for s = fl(1 - t), `b64_decasteljau_err_fl`)
   and the overflow guard  ==>  finite and
       |fl value - exact value|  <=  dc_iter eta M n 0
                                 <=  gamma_n(kappa) M + 2^-1075 (3+2u) n (1+kappa)^n
   with kappa = eta + (1+eta)(2u + u^2)  (= 2u + u^2 when eta = 0).
   The bound is in the max-norm of the control values; no cancellation
   factor, no dependence on the monomial-basis coefficients.  Normal and
   subnormal results are both covered (u|x| + 2^-1075 per op).

   claimId: s1-b64-decasteljau.  witness: b64_decasteljau_err.
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia Psatz ZArith List.
From Flocq Require Import Core IEEE754.Binary IEEE754.BinarySingleNaN.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib B64_AbsErr
  B64_Horner B64_HornerGamma.
Import ListNotations.
Local Open Scope R_scope.

Local Notation B2R := (Binary.B2R prec emax).
Local Notation fin := (Binary.is_finite prec emax).

Lemma dc_ab : forall x a, Rabs x <= a <-> (-a <= x /\ x <= a).
Proof.
  intros x a. split.
  - unfold Rabs. destruct (Rcase_abs x); intro H; lra.
  - intros [H1 H2]. apply Rabs_le. split; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §1  Evaluators.                                                            *)
(* -------------------------------------------------------------------------- *)

Definition dc_node (s t x y : binary64) : binary64 :=
  b64_plus (b64_mult s x) (b64_mult t y).

Fixpoint dcF_step (s t : binary64) (row : list binary64) : list binary64 :=
  match row with
  | x :: ((y :: _) as rest) => dc_node s t x y :: dcF_step s t rest
  | _ => []
  end.

Fixpoint dcR_step (s t : R) (row : list R) : list R :=
  match row with
  | x :: ((y :: _) as rest) => (s * x + t * y) :: dcR_step s t rest
  | _ => []
  end.

(* n rounds; for a row of length n+1 the value is the single survivor. *)
Fixpoint dcF (s t : binary64) (n : nat) (row : list binary64) : binary64 :=
  match n with
  | O => hd hz_zero row
  | S n' => dcF s t n' (dcF_step s t row)
  end.

Fixpoint dcR (s t : R) (n : nat) (row : list R) : R :=
  match n with
  | O => hd 0 row
  | S n' => dcR s t n' (dcR_step s t row)
  end.

Lemma dcR_step_length : forall s t row,
  length (dcR_step s t row) = Nat.pred (length row).
Proof.
  intros s t. induction row as [|x row IH]; [reflexivity|].
  destruct row as [|y row]; [reflexivity|].
  cbn [dcR_step length] in *. rewrite IH. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Error recursion.                                                       *)
(* -------------------------------------------------------------------------- *)

Definition dc_kappa (eta : R) : R := eta + (1 + eta) * (2 * b64ae_u + b64ae_u * b64ae_u).
Definition dc_rho : R := (3 + 2 * b64ae_u) * b64ae_e0.

Definition dc_next (eta M E : R) : R := E + dc_kappa eta * (M + E) + dc_rho.

Fixpoint dc_iter (eta M : R) (n : nat) (E : R) : R :=
  match n with
  | O => E
  | S n' => dc_iter eta M n' (dc_next eta M E)
  end.

Lemma dc_kappa_nonneg : forall eta, 0 <= eta -> 0 <= dc_kappa eta.
Proof.
  intros eta H. pose proof b64ae_u_small as [Hu _]. unfold dc_kappa.
  assert (0 <= (1 + eta) * (2 * b64ae_u + b64ae_u * b64ae_u)) by nra. lra.
Qed.

Lemma dc_rho_nonneg : 0 <= dc_rho.
Proof.
  pose proof b64ae_u_small as [Hu _]. pose proof b64ae_e0_small as [He _].
  unfold dc_rho. apply Rmult_le_pos; lra.
Qed.

Lemma dc_next_ge : forall eta M E, 0 <= eta -> 0 <= M -> 0 <= E -> E <= dc_next eta M E.
Proof.
  intros. unfold dc_next. pose proof (dc_kappa_nonneg eta H). pose proof dc_rho_nonneg.
  assert (0 <= dc_kappa eta * (M + E)) by (apply Rmult_le_pos; lra). lra.
Qed.

Lemma dc_iter_ge : forall eta M n E, 0 <= eta -> 0 <= M -> 0 <= E -> E <= dc_iter eta M n E.
Proof.
  intros eta M n. induction n as [|n IH]; intros E He Hm HE; [cbn; lra|].
  cbn [dc_iter]. pose proof (dc_next_ge eta M E He Hm HE).
  assert (0 <= dc_next eta M E) by lra.
  specialize (IH (dc_next eta M E) He Hm H0). lra.
Qed.

Lemma dc_next_nonneg : forall eta M E, 0 <= eta -> 0 <= M -> 0 <= E -> 0 <= dc_next eta M E.
Proof. intros. pose proof (dc_next_ge eta M E H H0 H1). lra. Qed.

(* -------------------------------------------------------------------------- *)
(* §3  One node.                                                              *)
(* -------------------------------------------------------------------------- *)

Lemma dc_scalar : forall (s t x y : binary64) (X Y M E eta : R),
  fin s = true -> fin t = true -> fin x = true -> fin y = true ->
  0 <= B2R t -> B2R t <= 1 -> Rabs (B2R s - (1 - B2R t)) <= eta ->
  0 <= eta -> eta <= 1 ->
  Rabs (B2R x - X) <= E -> Rabs X <= M ->
  Rabs (B2R y - Y) <= E -> Rabs Y <= M ->
  0 <= E -> 0 <= M ->
  (M + E) * 4 + 1 <= bpow radix2 1000 ->
  fin (dc_node s t x y) = true /\
  Rabs (B2R (dc_node s t x y) - ((1 - B2R t) * X + B2R t * Y)) <= dc_next eta M E /\
  Rabs ((1 - B2R t) * X + B2R t * Y) <= M.
Proof.
  intros s t x y X Y M E eta Fs Ft Fx Fy Ht0 Ht1 Hs He0 He1 Hx HX Hy HY HE HM Hg.
  pose proof b64ae_u_small as [Hu0 Hu1]. pose proof b64ae_e0_small as [He00 He01].
  set (N := M + E) in *.
  assert (HN : 0 <= N) by (unfold N; lra).
  set (bs := B2R s) in *. set (bt := B2R t) in *.
  set (bx := B2R x) in *. set (by_ := B2R y) in *.
  (* magnitudes of the computed inputs *)
  assert (Hbx : Rabs bx <= N).
  { replace bx with ((bx - X) + X) by ring.
    eapply Rle_trans; [apply Rabs_triang|]. unfold N. lra. }
  assert (Hby : Rabs by_ <= N).
  { replace by_ with ((by_ - Y) + Y) by ring.
    eapply Rle_trans; [apply Rabs_triang|]. unfold N. lra. }
  assert (Hbs : Rabs bs <= 1 - bt + eta).
  { apply dc_ab in Hs. apply Rabs_le. split; lra. }
  assert (Hbt : Rabs bt <= bt) by (rewrite Rabs_right; [lra | lra]).
  (* products *)
  assert (Psx : Rabs (bs * bx) <= (1 - bt + eta) * N)
    by (apply b64ae_abs_mult_le; assumption).
  assert (Pty : Rabs (bt * by_) <= bt * N)
    by (apply b64ae_abs_mult_le; assumption).
  set (sxa := Rabs (bs * bx)) in *. set (tya := Rabs (bt * by_)) in *.
  assert (Hsum : sxa + tya <= (1 + eta) * N) by lra.
  assert (Hsx0 : 0 <= sxa) by apply Rabs_pos.
  assert (Hty0 : 0 <= tya) by apply Rabs_pos.
  assert (HsN : (1 - bt + eta) * N <= 2 * N) by (apply Rmult_le_compat_r; lra).
  assert (HtN : bt * N <= 1 * N) by (apply Rmult_le_compat_r; lra).
  assert (Gsx : sxa <= bpow radix2 1000) by lra.
  assert (Gty : tya <= bpow radix2 1000) by lra.
  destruct (b64ae_mult_err s x Fs Fx Gsx) as [Fa Ea].
  destruct (b64ae_mult_err t y Ft Fy Gty) as [Fc Ec].
  set (a := b64_mult s x) in *. set (c := b64_mult t y) in *.
  fold bs bx in Ea. fold bt by_ in Ec. fold sxa in Ea. fold tya in Ec.
  (* |a + c| *)
  assert (Huu : b64ae_u * (sxa + tya) <= b64ae_u * ((1 + eta) * N))
    by (apply Rmult_le_compat_l; lra).
  assert (Hac_eq : B2R a + B2R c
                   = (B2R a - bs * bx) + (B2R c - bt * by_) + (bs * bx + bt * by_)) by ring.
  assert (Hsxty : Rabs (bs * bx + bt * by_) <= sxa + tya).
  { eapply Rle_trans; [apply Rabs_triang|]. unfold sxa, tya. lra. }
  apply dc_ab in Ea. apply dc_ab in Ec. apply dc_ab in Hsxty.
  assert (Hac : Rabs (B2R a + B2R c) <= (1 + eta) * (1 + b64ae_u) * N + 2 * b64ae_e0).
  { apply dc_ab. split; lra. }
  assert (Hc3 : (1 + eta) * (1 + b64ae_u) <= 3) by nra.
  assert (Hc3N : (1 + eta) * (1 + b64ae_u) * N <= 3 * N) by (apply Rmult_le_compat_r; lra).
  assert (Gac : Rabs (B2R a + B2R c) <= bpow radix2 1000).
  { eapply Rle_trans; [exact Hac|]. lra. }
  destruct (b64ae_plus_err a c Fa Fc Gac) as [Fr Er].
  split; [exact Fr|].
  assert (Hu2 : b64ae_u * Rabs (B2R a + B2R c) <= b64ae_u * ((1 + eta) * (1 + b64ae_u) * N + 2 * b64ae_e0))
    by (apply Rmult_le_compat_l; lra).
  unfold dc_node. fold a c bs bx bt by_ sxa tya.
  (* exact-vs-weighted error *)
  assert (Hdiff : Rabs (bs * bx + bt * by_ - ((1 - bt) * X + bt * Y))
                  <= (1 + eta) * E + eta * M).
  { replace (bs * bx + bt * by_ - ((1 - bt) * X + bt * Y))
      with (bs * (bx - X) + bt * (by_ - Y) + (bs - (1 - bt)) * X) by ring.
    assert (D1 : Rabs (bs * (bx - X)) <= (1 - bt + eta) * E)
      by (apply b64ae_abs_mult_le; assumption).
    assert (D2 : Rabs (bt * (by_ - Y)) <= bt * E)
      by (apply b64ae_abs_mult_le; assumption).
    assert (D3 : Rabs ((bs - (1 - bt)) * X) <= eta * M)
      by (apply b64ae_abs_mult_le; assumption).
    apply dc_ab in D1. apply dc_ab in D2. apply dc_ab in D3.
    apply dc_ab. split; lra. }
  split.
  - assert (Hr_eq : B2R (b64_plus a c) - ((1 - bt) * X + bt * Y)
          = (B2R (b64_plus a c) - (B2R a + B2R c)) + (B2R a - bs * bx) + (B2R c - bt * by_)
            + (bs * bx + bt * by_ - ((1 - bt) * X + bt * Y))) by ring.
    rewrite Hr_eq.
    apply dc_ab in Er. apply dc_ab in Hdiff.
    unfold dc_next, dc_kappa, dc_rho. unfold N in *.
    apply dc_ab. split; lra.
  - assert (Z1 : Rabs ((1 - bt) * X) <= (1 - bt) * M).
    { apply b64ae_abs_mult_le; [|assumption]. rewrite Rabs_right; lra. }
    assert (Z2 : Rabs (bt * Y) <= bt * M)
      by (apply b64ae_abs_mult_le; assumption).
    eapply Rle_trans; [apply Rabs_triang|]. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Rows and the n-round iteration.                                        *)
(* -------------------------------------------------------------------------- *)

Definition dc_inv (E M : R) (rf : list binary64) (rr : list R) : Prop :=
  Forall2 (fun xf xr => fin xf = true /\ Rabs (B2R xf - xr) <= E /\ Rabs xr <= M) rf rr.

Section Iter.
Variables (s t : binary64) (eta M : R).
Hypothesis Fs : fin s = true.
Hypothesis Ft : fin t = true.
Hypothesis Ht0 : 0 <= B2R t.
Hypothesis Ht1 : B2R t <= 1.
Hypothesis Hs : Rabs (B2R s - (1 - B2R t)) <= eta.
Hypothesis He0 : 0 <= eta.
Hypothesis He1 : eta <= 1.
Hypothesis HM : 0 <= M.

Lemma dc_step_inv : forall E rf rr,
  0 <= E -> (M + E) * 4 + 1 <= bpow radix2 1000 ->
  dc_inv E M rf rr ->
  dc_inv (dc_next eta M E) M (dcF_step s t rf) (dcR_step (1 - B2R t) (B2R t) rr).
Proof.
  intros E rf. induction rf as [|x rf IH]; intros rr HE Hg H.
  - inversion H; subst. constructor.
  - inversion H as [|x' xr rf0 rr' Hx Hrest]; subst.
    destruct rf as [|y rf'].
    + inversion Hrest; subst. constructor.
    + inversion Hrest as [|y' yr rf1 rr'' Hy Hrest']; subst.
      destruct Hx as [Fx [Ex Bx]]. destruct Hy as [Fy [Ey By]].
      destruct (dc_scalar s t x y xr yr M E eta Fs Ft Fx Fy Ht0 Ht1 Hs He0 He1
                  Ex Bx Ey By HE HM Hg) as [F1 [E1 B1]].
      cbn [dcF_step dcR_step].
      constructor.
      * repeat split; assumption.
      * apply (IH (yr :: rr'') HE Hg Hrest).
Qed.

Lemma dc_iter_inv : forall n rf rr E,
  length rr = S n -> dc_inv E M rf rr -> 0 <= E ->
  (M + dc_iter eta M n E) * 4 + 1 <= bpow radix2 1000 ->
  fin (dcF s t n rf) = true /\
  Rabs (B2R (dcF s t n rf) - dcR (1 - B2R t) (B2R t) n rr) <= dc_iter eta M n E.
Proof.
  induction n as [|n IH]; intros rf rr E Hlen Hinv HE Hg.
  - destruct rr as [|xr [|yr rr]]; cbn in Hlen; try discriminate.
    inversion Hinv as [|xf xr0 rf0 rr0 [Fx [Ex Bx]] Hrest]; subst.
    inversion Hrest; subst.
    cbn. split; assumption.
  - assert (Hge := dc_iter_ge eta M (S n) E He0 HM HE).
    assert (Hg0 : (M + E) * 4 + 1 <= bpow radix2 1000) by lra.
    pose proof (dc_step_inv E rf rr HE Hg0 Hinv) as Hstep.
    cbn [dcF dcR dc_iter] in *.
    assert (Hl : length (dcR_step (1 - B2R t) (B2R t) rr) = S n)
      by (rewrite dcR_step_length, Hlen; reflexivity).
    apply (IH _ _ _ Hl Hstep (dc_next_nonneg eta M E He0 HM HE) Hg).
Qed.

End Iter.

(* -------------------------------------------------------------------------- *)
(* §5  Closed form: gamma_n(kappa) M + underflow floor.                       *)
(* -------------------------------------------------------------------------- *)

Lemma dc_iter_closed : forall eta M n E, 0 <= eta -> 0 <= M ->
  dc_iter eta M n E
  <= (1 + dc_kappa eta) ^ n * E + ((1 + dc_kappa eta) ^ n - 1) * M
     + dc_rho * INR n * (1 + dc_kappa eta) ^ n.
Proof.
  intros eta M n. induction n as [|n IH]; intros E He Hm.
  - cbn. lra.
  - cbn [dc_iter]. specialize (IH (dc_next eta M E) He Hm).
    rewrite hg_pow_S, S_INR.
    pose proof (dc_kappa_nonneg eta He) as Hk. pose proof dc_rho_nonneg as Hr.
    set (k := dc_kappa eta) in *. set (P := (1 + k) ^ n) in *.
    assert (HP : 1 <= P).
    { unfold P. clear IH. induction n as [|n IHn]; [simpl; lra|].
      rewrite hg_pow_S. nra. }
    assert (Hn : 0 <= INR n) by apply pos_INR.
    assert (Hx : 0 <= dc_rho * (INR n + 1) * P * k).
    { repeat (apply Rmult_le_pos; try lra). }
    assert (HX : P * dc_next eta M E = P * (E + k * (M + E) + dc_rho))
      by (unfold dc_next; fold k; ring).
    lra.
Qed.

Lemma dc_pow_gamma : forall k n, 0 <= k -> k <= 1 -> INR n * k < 1 ->
  (1 + k) ^ n - 1 <= (INR n * k) / (1 - INR n * k).
Proof.
  intros k n H0 H1 Hn.
  assert (Ha : 0 <= (1 + k) * (1 - k) <= 1) by (split; nra).
  assert (Hp := hg_pow_le_one n _ Ha).
  rewrite Rpow_mult_distr in Hp.
  assert (Hb := hg_bernoulli n k (conj H0 H1)).
  assert (HP0 : 0 <= (1 + k) ^ n) by (apply pow_le; lra).
  assert (Hm : (1 + k) ^ n * (1 - INR n * k) <= (1 + k) ^ n * (1 - k) ^ n)
    by (apply Rmult_le_compat_l; lra).
  set (D := 1 - INR n * k) in *.
  assert (HD : 0 < D) by (unfold D; lra).
  apply (Rmult_le_reg_r D); [exact HD|].
  unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra.
  assert (INR n * k = 1 - D) by (unfold D; ring).
  nra.
Qed.

Lemma dc_inv_init : forall M cs,
  Forall (fun c => fin c = true /\ Rabs (B2R c) <= M) cs ->
  dc_inv 0 M cs (map B2R cs).
Proof.
  intros M cs H. induction H as [|c cs [Fc Bc] _ IH]; cbn; constructor.
  - repeat split; [exact Fc | | exact Bc]. rewrite Rminus_diag, Rabs_R0. lra.
  - exact IH.
Qed.

(* WITNESS {"claimId":"s1-b64-decasteljau","topic":"numerics","lemma":"b64_decasteljau_err","title":"Binary64 de Casteljau evaluation (RNE fl(fl(s x)+fl(t y)) per node, n rounds, t in [0,1], |s-(1-t)| <= eta) is finite and within dc_iter eta M n 0 <= ((1+kappa)^n - 1) M + 2^-1075 (3+2u) n (1+kappa)^n of the exact de Casteljau value of the same control values, where M bounds the control magnitudes (max-norm), kappa = eta + (1+eta)(2u+u^2); no cancellation factor in the monomial basis","file":"theories-flocq/B64_DeCasteljau.v","witness":"b64_decasteljau_err","board":"ADR-0006"} *)
Theorem b64_decasteljau_err : forall n (cs : list binary64) (s t : binary64) (M eta : R),
  length cs = S n ->
  Forall (fun c => fin c = true /\ Rabs (B2R c) <= M) cs ->
  fin s = true -> fin t = true -> 0 <= B2R t -> B2R t <= 1 ->
  Rabs (B2R s - (1 - B2R t)) <= eta -> 0 <= eta -> eta <= 1 / 100 -> 0 <= M ->
  (M + dc_iter eta M n 0) * 4 + 1 <= bpow radix2 1000 ->
  fin (dcF s t n cs) = true /\
  Rabs (B2R (dcF s t n cs) - dcR (1 - B2R t) (B2R t) n (map B2R cs))
    <= dc_iter eta M n 0 /\
  dc_iter eta M n 0
    <= ((1 + dc_kappa eta) ^ n - 1) * M
       + dc_rho * INR n * (1 + dc_kappa eta) ^ n.
Proof.
  intros n cs s t M eta Hlen Hcs Fs Ft Ht0 Ht1 Hs He0 He1 HM Hg.
  assert (He1' : eta <= 1) by lra.
  assert (Hlen' : length (map B2R cs) = S n) by (rewrite length_map; exact Hlen).
  destruct (dc_iter_inv s t eta M Fs Ft Ht0 Ht1 Hs He0 He1' HM n cs (map B2R cs) 0
              Hlen' (dc_inv_init M cs Hcs) (Rle_refl 0) Hg) as [F E].
  repeat split; try assumption.
  pose proof (dc_iter_closed eta M n 0 He0 HM). lra.
Qed.

(* gamma form: n kappa < 1. *)
Theorem b64_decasteljau_gamma : forall n (cs : list binary64) (s t : binary64) (M eta : R),
  length cs = S n ->
  Forall (fun c => fin c = true /\ Rabs (B2R c) <= M) cs ->
  fin s = true -> fin t = true -> 0 <= B2R t -> B2R t <= 1 ->
  Rabs (B2R s - (1 - B2R t)) <= eta -> 0 <= eta -> eta <= 1 / 100 -> 0 <= M ->
  (M + dc_iter eta M n 0) * 4 + 1 <= bpow radix2 1000 ->
  INR n * dc_kappa eta < 1 ->
  fin (dcF s t n cs) = true /\
  Rabs (B2R (dcF s t n cs) - dcR (1 - B2R t) (B2R t) n (map B2R cs))
    <= (INR n * dc_kappa eta / (1 - INR n * dc_kappa eta)) * M
       + dc_rho * INR n * (1 + dc_kappa eta) ^ n.
Proof.
  intros n cs s t M eta Hlen Hcs Fs Ft Ht0 Ht1 Hs He0 He1 HM Hg Hn.
  destruct (b64_decasteljau_err n cs s t M eta Hlen Hcs Fs Ft Ht0 Ht1 Hs He0 He1 HM Hg)
    as [F [E C]].
  split; [exact F|].
  pose proof b64ae_u_small as [Hu0 Hu1].
  assert (Hk0 := dc_kappa_nonneg eta He0).
  assert (Hk1 : dc_kappa eta <= 1).
  { unfold dc_kappa.
    assert ((1 + eta) * (2 * b64ae_u + b64ae_u * b64ae_u) <= (1 + 1/100) * (2 * (1/1000) + (1/1000) * (1/1000)))
      by (apply Rmult_le_compat; try lra; nra).
    lra. }
  assert (Hg2 := dc_pow_gamma (dc_kappa eta) n Hk0 Hk1 Hn).
  assert ((((1 + dc_kappa eta) ^ n - 1)) * M
          <= (INR n * dc_kappa eta / (1 - INR n * dc_kappa eta)) * M)
    by (apply Rmult_le_compat_r; assumption).
  lra.
Qed.

(* s = fl(1 - t): eta = u + 2^-1075. *)
Theorem b64_decasteljau_err_fl : forall n (cs : list binary64) (one t : binary64) (M : R),
  fin one = true -> B2R one = 1 ->
  length cs = S n ->
  Forall (fun c => fin c = true /\ Rabs (B2R c) <= M) cs ->
  fin t = true -> 0 <= B2R t -> B2R t <= 1 -> 0 <= M ->
  (M + dc_iter (b64ae_u + b64ae_e0) M n 0) * 4 + 1 <= bpow radix2 1000 ->
  fin (dcF (b64_minus one t) t n cs) = true /\
  Rabs (B2R (dcF (b64_minus one t) t n cs)
        - dcR (1 - B2R t) (B2R t) n (map B2R cs))
    <= ((1 + dc_kappa (b64ae_u + b64ae_e0)) ^ n - 1) * M
       + dc_rho * INR n * (1 + dc_kappa (b64ae_u + b64ae_e0)) ^ n.
Proof.
  intros n cs one t M Fo Bo Hlen Hcs Ft Ht0 Ht1 HM Hg.
  pose proof b64ae_u_small as [Hu0 Hu1]. pose proof b64ae_e0_small as [He0 He1].
  assert (H1 : 1 <= bpow radix2 1000).
  { replace 1 with (bpow radix2 0) by reflexivity. apply bpow_le. lia. }
  assert (Hm : Rabs (B2R one - B2R t) <= bpow radix2 1000).
  { rewrite Bo. apply Rabs_le. split; lra. }
  destruct (b64ae_minus_err one t Fo Ft Hm) as [Fs Es].
  rewrite Bo in Es.
  assert (Hab : Rabs (1 - B2R t) <= 1) by (apply Rabs_le; split; lra).
  assert (Hu : b64ae_u * Rabs (1 - B2R t) <= b64ae_u * 1)
    by (apply Rmult_le_compat_l; lra).
  assert (Heta : Rabs (B2R (b64_minus one t) - (1 - B2R t)) <= b64ae_u + b64ae_e0) by lra.
  destruct (b64_decasteljau_err n cs (b64_minus one t) t M (b64ae_u + b64ae_e0)
              Hlen Hcs Fs Ft Ht0 Ht1 Heta ltac:(lra) ltac:(lra) HM Hg) as [F [_ C]].
  split; [exact F|].
  (* reuse the closed form *)
  destruct (b64_decasteljau_err n cs (b64_minus one t) t M (b64ae_u + b64ae_e0)
              Hlen Hcs Fs Ft Ht0 Ht1 Heta ltac:(lra) ltac:(lra) HM Hg) as [_ [E _]].
  lra.
Qed.

Print Assumptions dc_scalar.
Print Assumptions dc_iter_inv.
Print Assumptions b64_decasteljau_err.
Print Assumptions b64_decasteljau_gamma.
Print Assumptions b64_decasteljau_err_fl.
