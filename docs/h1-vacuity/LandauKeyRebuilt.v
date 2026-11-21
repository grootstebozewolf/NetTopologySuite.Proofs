(* LandauKeyRebuilt.v -- the KEY seam of landau_window in the claimed RH/GRH
   Lean development (CocoSgt/riemann-hypothesis-lean @ 7cbf7a0):

     LandauTheorems/landauTails.lean : landau_tails, landau_tails_chernoff,
                                       landau_tails_pow
     LandauTheorems/landauWindow.lean: landau_window_key
     LandauTheorems/LandauCoeff.lean : landau_coeff

   landau_window_key turns the window hypothesis WindowHypU into the
   coefficient bound KEY consumed by LandauWindowRebuilt.v.  It combines
     landau_window_ineq  (norm + Re <= 2 (sigma-theta)^-k int R e^-theta u
                           + 2 C0 * tail integral;  core = window_ineq_discrete),
     landau_coeff        (Taylor coefficients = Laplace moments; translation),
     landau_tails        (tail integral <= C / sigma^k for some k >= U).

   Rocq (here, over Q):
   - tails_params (QED): the parameter arithmetic of landau_tails.  With
     l = 2 + 6/delta, M = l(1+delta), sigma = M(2+l), a = sigma-2-l,
     b = sigma-2+l and k in [(1+delta/2) sigma U, (1+delta/2) sigma U + 1]:
     U <= k, and both Chernoff exponents are bounded (by 1 and by 0).
   - tails_pow_core (QED): landau_tails_pow, with exp abstract (additive,
     monotone, 1 + t <= e^t).
   - tails_rebuilt (QED, conditional): landau_tails from the Chernoff split
     (landau_tails_chernoff: kernel_integral + pointwise comparison).
   - key_rebuilt (QED, conditional): KEY from the window inequality, the
     window bound int R e^-theta u <= e^(eta U), and the tails bound.
   - landau_window_from_windows (QED, conditional): landau_window_rebuilt
     with KEY discharged by key_rebuilt.

   Evidence for docs/attacks/2026-11-21-alpoge-landau-key-seam.md.
   NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import QArith Qabs Qminmax Qround Lqa ZArith Lia List.
From NTS.Proofs.Probes Require Import LandauWindowCore LandauDichotomyQED LandauWindowRebuilt FormBRebuilt.
Local Open Scope Q_scope.

(* ===================================================================== *)
(* Part 1: landau_tails parameter arithmetic                              *)
(* ===================================================================== *)

Theorem tails_params : forall delta U kq, 0 < delta -> 1 <= U ->
  let l := 2 + 6 / delta in
  let M := l * (1 + delta) in
  let sigma := M * (2 + l) in
  (1 + delta * (1 # 2)) * sigma * U <= kq ->
  kq <= (1 + delta * (1 # 2)) * sigma * U + 1 ->
  2 < sigma /\ 0 < sigma - 2 - l /\ 0 < sigma - 2 + l /\ U <= kq /\
  kq * (2 + l) <= (sigma - 2 - l) * (1 + l * (1 + delta) * U) /\
  l * U * (sigma - 2 + l) <= kq * (l - 2).
Proof.
  intros delta U kq Hd HU l M sigma Hk1 Hk2.
  assert (Hl : l * delta == 6 + 2 * delta) by (unfold l; field; lra).
  assert (H6 : 0 < 6 / delta) by (apply Qlt_shift_div_l; lra).
  assert (Hl2 : 2 < l) by (unfold l; lra).
  assert (EM : M == l + (6 + 2 * delta)) by (unfold M; rewrite <- Hl; ring).
  assert (HM : l < M) by lra.
  assert (HM1 : 2 <= M - 1) by lra.
  assert (Hs : l * (2 + l) < sigma) by (unfold sigma; nra).
  (* identities e1, e2, e3 of the Lean proof *)
  assert (E1 : (2 + l) * (M - 1) == sigma - 2 - l) by (unfold sigma; ring).
  assert (E2 : (1 + delta * (1 # 2)) * (2 + l) == M - 1).
  { unfold M. assert (Hr : (1 + delta * (1 # 2)) * (2 + l) - (l * (1 + delta) - 1)
                         == (1 # 2) * (6 + 2 * delta - l * delta)) by ring. lra. }
  assert (E3 : (1 + delta * (1 # 2)) * (l - 2) == l + 1).
  { assert (Hr : (1 + delta * (1 # 2)) * (l - 2) - (l + 1)
               == (1 # 2) * (l * delta - 6 - 2 * delta)) by ring. lra. }
  assert (Ha : 0 < sigma - 2 - l) by nra.
  assert (Hsig2 : 2 < sigma) by nra.
  assert (HUs : 0 <= sigma * U) by nra.
  assert (Hf : (1 + delta * (1 # 2)) * sigma == M * (M - 1)).
  { unfold sigma. rewrite <- E2. ring. }
  split; [exact Hsig2|]. split; [exact Ha|]. split; [lra|]. split.
  - (* U <= k *)
    assert (U <= sigma * U) by nra.
    assert (sigma * U <= (1 + delta * (1 # 2)) * sigma * U) by nra.
    lra.
  - split.
    + (* T1: k (2+l) <= a (1 + M U) *)
      assert (Hk : kq <= M * (M - 1) * U + 1).
      { assert (E : (1 + delta * (1 # 2)) * sigma * U == M * (M - 1) * U) by (rewrite Hf; ring). lra. }
      assert (Hl0 : 0 < 2 + l) by lra.
      assert (H1 : kq * (2 + l) <= (M * (M - 1) * U + 1) * (2 + l)) by (apply Qmult_le_compat_r; lra).
      assert (E4 : (M * (M - 1) * U + 1) * (2 + l) == (sigma - 2 - l) * (M * U) + (2 + l)).
      { rewrite <- E1. ring. }
      assert (H2 : 2 + l <= sigma - 2 - l) by (rewrite <- E1; nra).
      assert (E5 : (sigma - 2 - l) * (1 + l * (1 + delta) * U) == (sigma - 2 - l) + (sigma - 2 - l) * (M * U))
        by (unfold M; ring).
      lra.
    + (* T2: l U b <= k (l - 2) *)
      assert (H1 : (1 + delta * (1 # 2)) * sigma * U * (l - 2) <= kq * (l - 2))
        by (apply Qmult_le_compat_r; lra).
      assert (E6 : (1 + delta * (1 # 2)) * sigma * U * (l - 2) == (l + 1) * sigma * U).
      { rewrite <- E3. ring. }
      assert (H3 : l * (sigma - 2 + l) <= (l + 1) * sigma) by nra.
      assert (H4 : l * (sigma - 2 + l) * U <= (l + 1) * sigma * U) by (apply Qmult_le_compat_r; lra).
      assert (E7 : l * U * (sigma - 2 + l) == l * (sigma - 2 + l) * U) by ring.
      lra.
Qed.

Print Assumptions tails_params.

(* The integer k of the Lean proof: k = ceil((1 + delta/2) sigma U). *)
Lemma ceil_nat : forall X, 0 <= X -> exists k : nat, X <= nq k /\ nq k <= X + 1.
Proof.
  intros X HX. exists (Z.to_nat (Qceiling X)).
  pose proof (Qle_ceiling X) as H1. pose proof (Qceiling_lt X) as H2.
  assert (Hz : (0 <= Qceiling X)%Z).
  { assert (H : inject_Z 0 <= inject_Z (Qceiling X)) by (change (inject_Z 0) with 0; lra).
    rewrite <- Zle_Qle in H. exact H. }
  unfold nq. rewrite Z2Nat.id by exact Hz.
  split; [exact H1|].
  pose proof (inject_Z_plus (Qceiling X - 1) 1) as E.
  replace (Qceiling X - 1 + 1)%Z with (Qceiling X) in E by ring.
  change (inject_Z 1) with 1 in E. rewrite E. lra.
Qed.

(* ===================================================================== *)
(* Part 2: landau_tails_pow, exp abstract                                 *)
(* ===================================================================== *)

Section TailsPow.
Variable E : Q -> Q.                           (* Real.exp *)
Hypothesis E_pos : forall t, 0 < E t.
Hypothesis E_add : forall p q, E (p + q) == E p * E q.
Hypothesis E_mono : forall p q, p <= q -> E p <= E q.
Hypothesis E_ge : forall t, 1 + t <= E t.      (* Real.add_one_le_exp *)
Hypothesis E_wd : forall p q, p == q -> E p == E q.

Lemma E_pow : forall t k, qpow (E t) k == E (nq k * t).
Proof.
  intros t k. induction k as [|k IH]; cbn [qpow].
  - assert (E0 : E 0 == 1).
    { pose proof (E_add 0 0) as H. assert (E (0 + 0) == E 0) by (apply E_wd; ring).
      pose proof (E_pos 0). assert (E 0 * E 0 == E 0 * 1) by lra.
      apply (Qmult_inj_l _ _ (E 0)); [lra|]. exact H2. }
    assert (E (nq 0 * t) == E 0) by (apply E_wd; unfold nq; simpl; ring). lra.
  - rewrite IH, <- E_add. apply E_wd. rewrite nq_succ. ring.
Qed.

(* landau_tails_pow:  x + k (sigma - a)/a <= c  ==>
   e^x a^-(k+1) <= e^c / a / sigma^k,  here multiplied out:
   e^x sigma^k <= e^c a^k. *)
Theorem tails_pow_core : forall k sigma a x c, 0 < sigma -> 0 < a ->
  x + nq k * ((sigma - a) / a) <= c -> E x * qpow sigma k <= E c * qpow a k.
Proof.
  intros k sigma a x c Hs Ha Hc.
  set (t := (sigma - a) / a).
  assert (Ht : sigma / a <= E t).
  { pose proof (E_ge t) as H. assert (E1 : 1 + t == sigma / a) by (unfold t; field; lra). lra. }
  assert (Hsa : 0 <= sigma / a) by (apply Qle_shift_div_l; lra).
  assert (H1 : qpow (sigma / a) k <= E (nq k * t)).
  { rewrite <- E_pow. apply qpow_mono; assumption. }
  assert (H2 : E x * E (nq k * t) <= E c).
  { rewrite <- E_add. apply E_mono. exact Hc. }
  assert (Esig : qpow sigma k == qpow (sigma / a) k * qpow a k).
  { rewrite <- qpow_mul. apply qpow_wd. field. lra. }
  rewrite Esig.
  assert (Hak : 0 < qpow a k) by (apply qpow_pos; exact Ha).
  assert (Hex : 0 < E x) by apply E_pos.
  assert (H3 : E x * qpow (sigma / a) k <= E x * E (nq k * t)).
  { rewrite !(Qmult_comm (E x)). apply Qmult_le_compat_r; [exact H1|lra]. }
  assert (H4 : E x * qpow (sigma / a) k * qpow a k <= E c * qpow a k).
  { apply Qmult_le_compat_r; [lra|lra]. }
  setoid_replace (E x * (qpow (sigma / a) k * qpow a k)) with (E x * qpow (sigma / a) k * qpow a k) by ring.
  exact H4.
Qed.

(* landau_tails, from the Chernoff split.  T U k is the tail integral
   int_{(0,oo) \ [U, (1+delta)U]} u^k e^((2-sigma)u)/k! du.  CHER is
   landau_tails_chernoff (kernel_integral + the pointwise comparison
   e^-su <= e^(-su + l(u-V)) + e^(-su + l(U-u)) off [U, V]). *)
Variable delta : Q.
Hypothesis Hdelta : 0 < delta.
Definition tl := 2 + 6 / delta.
Definition tM := tl * (1 + delta).
Definition tsig := tM * (2 + tl).
Variable T : Q -> nat -> Q.
Hypothesis CHER : forall U k, 1 <= U ->
  T U k <= E (- (tl * ((1 + delta) * U))) / qpow (tsig - 2 - tl) (S k)
         + E (tl * U) / qpow (tsig - 2 + tl) (S k).

Lemma div_mul_bound : forall A S c a Pk, 0 < a -> 0 < Pk -> A * S <= c * Pk ->
  A / (a * Pk) * S <= c / a.
Proof.
  intros A S c a Pk Ha HP H.
  assert (HaP : 0 < a * Pk) by (apply Qmult_lt_0_compat; assumption).
  apply Qmult_le_r with (a * Pk); [exact HaP|].
  setoid_replace (A / (a * Pk) * S * (a * Pk)) with (A * S) by (field; split; lra).
  setoid_replace (c / a * (a * Pk)) with (c * Pk) by (field; lra).
  exact H.
Qed.

Theorem tails_rebuilt : 2 < tsig /\ forall U, 1 <= U -> exists k, U <= nq k /\
  T U k * qpow tsig k <= E 1 / (tsig - 2 - tl) + E 0 / (tsig - 2 + tl).
Proof.
  assert (Hs : 2 < tsig /\ 0 < tsig - 2 - tl /\ 0 < tsig - 2 + tl).
  { destruct (ceil_nat ((1 + delta * (1 # 2)) * tsig * 1)) as [k [Hk1 Hk2]].
    - unfold tsig, tM, tl. assert (0 < 6 / delta) by (apply Qlt_shift_div_l; lra). nra.
    - pose proof (tails_params delta 1 (nq k) Hdelta (Qle_refl 1) Hk1 Hk2) as P. cbv zeta in P.
      fold tl tM tsig in P. tauto. }
  destruct Hs as [Hs2 [Ha Hb]].
  split; [exact Hs2|]. intros U HU.
  assert (HX : 0 <= (1 + delta * (1 # 2)) * tsig * U).
  { assert (0 <= tsig * U) by nra. assert (0 <= 1 + delta * (1 # 2)) by lra. nra. }
  destruct (ceil_nat _ HX) as [k [Hk1 Hk2]].
  pose proof (tails_params delta U (nq k) Hdelta HU Hk1 Hk2) as P. cbv zeta in P.
  fold tl tM tsig in P. destruct P as [_ [_ [_ [HUk [T1 T2]]]]].
  exists k. split; [exact HUk|].
  set (a := tsig - 2 - tl) in *. set (b := tsig - 2 + tl) in *.
  pose proof (CHER U k HU) as HC. cbn [qpow] in HC. fold a b in HC.
  assert (Hsk : 0 <= qpow tsig k) by (apply qpow_nonneg; lra).
  assert (Hl2 : 2 < tl) by (unfold tl; assert (0 < 6 / delta) by (apply Qlt_shift_div_l; lra); lra).
  (* first Chernoff term: x = -(l V), c = 1 *)
  assert (P1 : E (- (tl * ((1 + delta) * U))) * qpow tsig k <= E 1 * qpow a k).
  { apply tails_pow_core; [lra|exact Ha|].
    assert (Ea : (tsig - a) / a == (2 + tl) / a) by (unfold a; apply Qdiv_comp; [ring|reflexivity]).
    rewrite Ea.
    assert (Hq : nq k * ((2 + tl) / a) <= 1 + tl * (1 + delta) * U).
    { apply Qmult_le_r with a; [exact Ha|].
      setoid_replace (nq k * ((2 + tl) / a) * a) with (nq k * (2 + tl)) by (field; lra).
      assert (Ec : (1 + tl * (1 + delta) * U) * a == a * (1 + tM * U)) by (unfold tM; ring).
      lra. }
    lra. }
  (* second Chernoff term: x = l U, c = 0 *)
  assert (P2 : E (tl * U) * qpow tsig k <= E 0 * qpow b k).
  { apply tails_pow_core; [lra|exact Hb|].
    assert (Eb : (tsig - b) / b == - ((tl - 2) / b)) by (unfold b; field; lra).
    rewrite Eb.
    assert (Hq : tl * U <= nq k * ((tl - 2) / b)).
    { apply Qmult_le_r with b; [exact Hb|].
      setoid_replace (nq k * ((tl - 2) / b) * b) with (nq k * (tl - 2)) by (field; lra).
      lra. }
    lra. }
  assert (Hak : 0 < qpow a k) by (apply qpow_pos; exact Ha).
  assert (Hbk : 0 < qpow b k) by (apply qpow_pos; exact Hb).
  pose proof (div_mul_bound _ _ _ _ _ Ha Hak P1) as D1.
  pose proof (div_mul_bound _ _ _ _ _ Hb Hbk P2) as D2.
  assert (H : T U k * qpow tsig k <=
              (E (- (tl * ((1 + delta) * U))) / (a * qpow a k)
               + E (tl * U) / (b * qpow b k)) * qpow tsig k)
    by (apply Qmult_le_compat_r; assumption).
  lra.
Qed.

End TailsPow.

Print Assumptions tails_pow_core.
Print Assumptions tails_rebuilt.

(* ===================================================================== *)
(* Part 3: landau_window_key, and landau_window with KEY discharged       *)
(* ===================================================================== *)

Section Key.
(* LandauWindowRebuilt.v's Assembly inputs, minus KEY *)
Variable Z : Q * Q -> Prop.
Variables sigma theta : Q.
Hypothesis Htheta : 0 < theta.
Hypothesis Hts : theta < sigma.
Hypothesis Hle : forall w, Z w -> fst w < sigma.
Hypothesis LF : forall lo y0 R, 0 < lo -> exists F : list (Q * Q),
  (forall w, In w F -> Z w) /\
  (forall w, Z w -> lo <= fst w -> - R <= snd w - y0 <= R -> In w F).
Variables (A : nat -> Q -> Q) (B : nat -> Q).
Hypothesis HA : forall k g, 0 <= A k g.
Hypothesis CAUCHY : forall D2 e, (forall w, Z w -> ~ d2 sigma 0 w < D2) ->
  0 < e -> e * e < D2 -> exists M, forall k, - M <= B k * qpow e k.
Hypothesis POLE1 : forall g rho r2 d e, Z rho ->
  (forall w, Z w -> d2 sigma g w < r2 -> peq w rho) ->
  0 < d -> d2 sigma g rho < d * d -> d < e -> e * e < r2 ->
  exists cn M, 0 < cn /\ forall k, cn * qpow e k <= (A k g * qpow e k + M) * qpow d k.
Hypothesis POLE2 : forall beta r2 e, Z beta -> snd beta == 0 ->
  (forall w, Z w -> d2 sigma 0 w < r2 -> peq w beta) ->
  sigma - fst beta < e -> e * e < r2 ->
  exists cr M, 0 < cr /\ forall k, cr * qpow e k <= (B k * qpow e k + M) * qpow (sigma - fst beta) k.

(* landau_window_key's inputs *)
Variable Xe : Q -> Q -> Q.                     (* Xe eta U = e^(eta U) *)
Hypothesis XS : forall s, 1 < s -> exists eta, 0 < eta /\
  forall U k, 0 <= U -> U <= nq k -> Xe eta U <= qpow s k.   (* eta = log s *)
Variable T : Q -> nat -> Q.                    (* tail integral *)
Hypothesis T_nonneg : forall U k, 0 <= T U k.
Variable C0 : Q.                               (* PoleData.growth *)
Hypothesis C0_nonneg : 0 <= C0.
(* WindowHypU + landau_coeff + landau_window_ineq: for every eta, arbitrarily
   large windows U with majorant integral Iw <= e^(eta U), and for all k, g
     norm + Re  <=  2 (sigma-theta)^-k Iw + 2 C0 T U k. *)
Hypothesis WI : forall eta, 0 < eta -> forall U0, exists U, U0 <= U /\ 1 <= U /\
  exists Iw, Iw <= Xe eta U /\ forall k g,
    (A k g + B k) * qpow (sigma - theta) k <= 2 * Iw + 2 * C0 * T U k * qpow (sigma - theta) k.
(* landau_tails (tails_rebuilt above) *)
Hypothesis TAILS : exists Ct, forall U, 1 <= U -> exists k, U <= nq k /\ T U k * qpow sigma k <= Ct.

Lemma nq_le_inv : forall m n, nq m <= nq n -> (m <= n)%nat.
Proof. intros m n H. unfold nq in H. rewrite <- Zle_Qle in H. lia. Qed.

Lemma qpow_ge1 : forall s k, 1 < s -> 1 <= qpow s k.
Proof.
  intros s k Hs. pose proof (bernoulli s k (Qlt_le_weak _ _ Hs)).
  assert (0 <= nq k * (s - 1)) by (pose proof (nq_nonneg k); nra). unfold nq in *. lra.
Qed.

Theorem key_rebuilt : exists C, forall s, 1 < s -> forall K, exists k, (K <= k)%nat /\
  forall g, (A k g + B k) * qpow (sigma - theta) k <= C * qpow s k.
Proof.
  destruct TAILS as [Ct HT].
  exists (2 + 2 * C0 * Qabs Ct). intros s Hs K.
  destruct (XS s Hs) as [eta [Heta HX]].
  destruct (WI eta Heta (Qmax (nq K) 1)) as [U [HU0 [HU1 [Iw [HI Hb]]]]].
  destruct (HT U HU1) as [k [Hk HTk]].
  exists k. split.
  { apply nq_le_inv. eapply Qle_trans; [|exact Hk]. eapply Qle_trans; [apply Q.le_max_l|exact HU0]. }
  intro g. specialize (Hb k g).
  assert (HIs : Iw <= qpow s k) by (eapply Qle_trans; [exact HI|apply HX; lra]).
  assert (Hsk : 1 <= qpow s k) by (apply qpow_ge1; exact Hs).
  assert (HEk : qpow (sigma - theta) k <= qpow sigma k) by (apply qpow_mono; lra).
  assert (HT0 := T_nonneg U k).
  assert (H1 : T U k * qpow (sigma - theta) k <= T U k * qpow sigma k).
  { rewrite !(Qmult_comm (T U k)). apply Qmult_le_compat_r; assumption. }
  assert (H2 : T U k * qpow sigma k <= Qabs Ct * qpow s k).
  { pose proof (Qle_Qabs Ct). pose proof (Qabs_nonneg Ct).
    assert (Qabs Ct <= Qabs Ct * qpow s k) by nra. lra. }
  assert (H3 : 2 * C0 * (T U k * qpow (sigma - theta) k) <= 2 * C0 * (Qabs Ct * qpow s k)).
  { rewrite !(Qmult_comm (2 * C0)). apply Qmult_le_compat_r; lra. }
  assert (E1 : 2 * C0 * T U k * qpow (sigma - theta) k == 2 * C0 * (T U k * qpow (sigma - theta) k)) by ring.
  assert (E2 : (2 + 2 * C0 * Qabs Ct) * qpow s k == 2 * qpow s k + 2 * C0 * (Qabs Ct * qpow s k)) by ring.
  lra.
Qed.

Theorem landau_window_from_windows : forall rho0, Z rho0 -> fst rho0 <= theta.
Proof.
  exact (landau_window_rebuilt Z sigma theta Htheta Hts Hle LF A B HA key_rebuilt CAUCHY POLE1 POLE2).
Qed.

End Key.

Print Assumptions key_rebuilt.
Print Assumptions landau_window_from_windows.

(* The tails input discharged: landau_window with sigma = tsig delta, the
   value landau_tails chooses, from WindowHypU's consequences (WI), the
   Chernoff split (CHER) and abstract exp. *)
Section Full.
Variable E : Q -> Q.
Hypothesis E_pos : forall t, 0 < E t.
Hypothesis E_add : forall p q, E (p + q) == E p * E q.
Hypothesis E_mono : forall p q, p <= q -> E p <= E q.
Hypothesis E_ge : forall t, 1 + t <= E t.
Hypothesis E_wd : forall p q, p == q -> E p == E q.
Variable delta : Q.
Hypothesis Hdelta : 0 < delta.
Variable T : Q -> nat -> Q.
Hypothesis T_nonneg : forall U k, 0 <= T U k.
Hypothesis CHER : forall U k, 1 <= U ->
  T U k <= E (- (tl delta * ((1 + delta) * U))) / qpow (tsig delta - 2 - tl delta) (S k)
         + E (tl delta * U) / qpow (tsig delta - 2 + tl delta) (S k).

Let sigma := tsig delta.
Variable Z : Q * Q -> Prop.
Variable theta : Q.
Hypothesis Htheta : 0 < theta.
Hypothesis Hts : theta < sigma.
Hypothesis Hle : forall w, Z w -> fst w < sigma.
Hypothesis LF : forall lo y0 R, 0 < lo -> exists F : list (Q * Q),
  (forall w, In w F -> Z w) /\
  (forall w, Z w -> lo <= fst w -> - R <= snd w - y0 <= R -> In w F).
Variables (A : nat -> Q -> Q) (B : nat -> Q).
Hypothesis HA : forall k g, 0 <= A k g.
Hypothesis CAUCHY : forall D2 e, (forall w, Z w -> ~ d2 sigma 0 w < D2) ->
  0 < e -> e * e < D2 -> exists M, forall k, - M <= B k * qpow e k.
Hypothesis POLE1 : forall g rho r2 d e, Z rho ->
  (forall w, Z w -> d2 sigma g w < r2 -> peq w rho) ->
  0 < d -> d2 sigma g rho < d * d -> d < e -> e * e < r2 ->
  exists cn M, 0 < cn /\ forall k, cn * qpow e k <= (A k g * qpow e k + M) * qpow d k.
Hypothesis POLE2 : forall beta r2 e, Z beta -> snd beta == 0 ->
  (forall w, Z w -> d2 sigma 0 w < r2 -> peq w beta) ->
  sigma - fst beta < e -> e * e < r2 ->
  exists cr M, 0 < cr /\ forall k, cr * qpow e k <= (B k * qpow e k + M) * qpow (sigma - fst beta) k.
Variable Xe : Q -> Q -> Q.
Hypothesis XS : forall s, 1 < s -> exists eta, 0 < eta /\
  forall U k, 0 <= U -> U <= nq k -> Xe eta U <= qpow s k.
Variable C0 : Q.
Hypothesis C0_nonneg : 0 <= C0.
Hypothesis WI : forall eta, 0 < eta -> forall U0, exists U, U0 <= U /\ 1 <= U /\
  exists Iw, Iw <= Xe eta U /\ forall k g,
    (A k g + B k) * qpow (sigma - theta) k <= 2 * Iw + 2 * C0 * T U k * qpow (sigma - theta) k.

Theorem landau_window_full : forall rho0, Z rho0 -> fst rho0 <= theta.
Proof.
  assert (TAILS : exists Ct, forall U, 1 <= U -> exists k, U <= nq k /\ T U k * qpow sigma k <= Ct).
  { destruct (tails_rebuilt E E_pos E_add E_mono E_ge E_wd delta Hdelta T CHER) as [_ HT].
    eexists. exact HT. }
  exact (landau_window_from_windows Z sigma theta Htheta Hts Hle LF A B HA CAUCHY POLE1 POLE2
           Xe XS T T_nonneg C0 C0_nonneg WI TAILS).
Qed.

End Full.

Print Assumptions landau_window_full.
