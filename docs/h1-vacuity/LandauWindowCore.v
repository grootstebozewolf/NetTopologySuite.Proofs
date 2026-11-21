(* LandauWindowCore.v -- elementary core of the main line's sign step in the
   claimed RH/GRH Lean development (CocoSgt/riemann-hypothesis-lean @ 7cbf7a0):

     Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/
       LandauGrowthContra.lean : landau_growth_contra
       landauWindow.lean       : landau_window_contra  (used by landau_window)

   The main line reaches zero-freeness through
     zeroFreeAll_of_topG -> zeroFreeOn_of_tiedWin_cyc -> level_of_tiedWin
       -> FormBAt (windowed) -> formB -> zeroFree_of_rpow_window -> lemmaL
       -> landau_window
   (NOT through Landau.lean's landau_family / zero_free_of_Chebyshev_growth,
   which have no callers on that path).  landau_window bounds the k-th Taylor
   coefficients of the Laplace transform Phi of g = Gm by C e^(eta U)/(sigma -
   theta)^k using a window majorant (g <= R, R >= 0); a pole at distance
   d < e = sigma - theta would force them >= c/d^k.  The contradiction is:

   Lean:  0 < c, 0 < d < e <= E, and for every eta > 0 arbitrarily large U with
          some k >= U and  c/d^k <= M/e^k + C e^(eta U)/E^k   ==>  False.

   Rocq (here, over Q): the slack factor e^(eta U) (with U <= k) is abstracted
   to X_k <= s^k for a rate s with 1 <= s and s*d < e -- the content of Lean's
   choice eta = log(e/d)/2.  Then  c <= (M + C s^k)(d/e)^k  fails for large k.
   Proved: Bernoulli growth of (e/(s d))^k, and the contradiction.
   Translation (not re-proved): e^(eta U) <= s^k for U <= k with s = e^eta,
   and eta small enough that s d < e.

   Evidence for docs/attacks/2026-11-21-alpoge-main-line-sign-correction.md.
   NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import QArith Qabs Lqa ZArith Lia.
Local Open Scope Q_scope.

Fixpoint qpow (q : Q) (n : nat) : Q := match n with O => 1 | S n' => q * qpow q n' end.

Lemma qpow_pos : forall q n, 0 < q -> 0 < qpow q n.
Proof. intros q n Hq. induction n as [|n IH]; cbn; [lra|]. apply Qmult_lt_0_compat; assumption. Qed.

(* Bernoulli: r >= 1 -> r^k >= 1 + k (r - 1) *)
Lemma bernoulli : forall r k, 1 <= r -> 1 + inject_Z (Z.of_nat k) * (r - 1) <= qpow r k.
Proof.
  intros r k Hr. induction k as [|k IH]; cbn [qpow].
  - setoid_replace (inject_Z (Z.of_nat 0)) with 0 by reflexivity. lra.
  - rewrite Nat2Z.inj_succ, <- Z.add_1_r, inject_Z_plus. change (inject_Z 1) with 1.
    assert (Hk : 0 <= inject_Z (Z.of_nat k)).
    { change 0 with (inject_Z 0). rewrite <- Zle_Qle. lia. }
    set (kq := inject_Z (Z.of_nat k)) in *.
    assert (H1 : r * (1 + kq * (r - 1)) <= r * qpow r k) by (apply Qmult_le_l; lra).
    assert (H2 : 0 <= kq * (r - 1) * (r - 1)) by (apply Qmult_le_0_compat; [apply Qmult_le_0_compat|]; lra).
    setoid_replace (r * (1 + kq * (r - 1))) with (1 + (kq + 1) * (r - 1) + kq * (r - 1) * (r - 1)) in H1 by ring.
    lra.
Qed.

Lemma qpow_wd : forall a b k, a == b -> qpow a k == qpow b k.
Proof.
  intros a b k H. induction k as [|k IH]; cbn [qpow]; [reflexivity|].
  apply Qmult_comp; assumption.
Qed.

Lemma qpow_mul : forall a b k, qpow (a * b) k == qpow a k * qpow b k.
Proof. intros a b k. induction k as [|k IH]; cbn [qpow]; [ring|]. rewrite IH. ring. Qed.

Section Contra.
Variables c d e M C s : Q.
Hypothesis Hc : 0 < c.
Hypothesis Hd : 0 < d.
Hypothesis Hs : 1 <= s.
Hypothesis Hsde : s * d < e.

(* For every k beyond any bound there is a violating instance... the Lean
   hypothesis H, specialised through X_k <= s^k:  c / d^k <= M / e^k + C s^k / e^k,
   i.e. c * e^k <= (M + C s^k) d^k, for arbitrarily large k. *)
Hypothesis H : forall K : nat, exists k : nat, (K <= k)%nat /\
  c * qpow e k <= (Qabs M + Qabs C * qpow s k) * qpow d k.

Theorem window_contra : False.
Proof.
  assert (He : 0 < e) by nra.
  set (r := e / (s * d)).
  assert (Hsd : 0 < s * d) by nra.
  assert (Hr : 1 < r).
  { unfold r. apply Qlt_shift_div_l; [exact Hsd | lra]. }
  set (A := Qabs M + Qabs C).
  assert (HA : 0 <= A) by (unfold A; pose proof (Qabs_nonneg M); pose proof (Qabs_nonneg C); lra).
  (* choose K with A < c * (1 + K (r - 1)) *)
  destruct (Qarchimedean (A / (c * (r - 1)))) as [p Hp].
  destruct (H (Pos.to_nat p)) as [k [Hk Hineq]].
  assert (Hkq : inject_Z (Z.pos p) <= inject_Z (Z.of_nat k)).
  { rewrite <- Zle_Qle. lia. }
  assert (Hcr : 0 < c * (r - 1)) by (apply Qmult_lt_0_compat; lra).
  assert (HAk : A < c * (inject_Z (Z.of_nat k) * (r - 1))).
  { assert (A / (c * (r - 1)) < inject_Z (Z.of_nat k)).
    { apply Qlt_le_trans with (Z.pos p # 1); [exact Hp|]. exact Hkq. }
    assert (Hcr' : ~ c * (r - 1) == 0) by (intro Z; rewrite Z in Hcr; discriminate Hcr).
    assert (EA : A == A / (c * (r - 1)) * (c * (r - 1))).
    { unfold Qdiv. rewrite <- Qmult_assoc, (Qmult_comm (/ _)), Qmult_inv_r by exact Hcr'. ring. }
    rewrite EA.
    setoid_replace (c * (inject_Z (Z.of_nat k) * (r - 1))) with (inject_Z (Z.of_nat k) * (c * (r - 1))) by ring.
    apply Qmult_lt_compat_r; [exact Hcr | exact H0]. }
  pose proof (bernoulli r k (Qlt_le_weak _ _ Hr)) as Hb.
  (* e^k = r^k (s d)^k = r^k s^k d^k *)
  assert (Ee : qpow e k == qpow r k * qpow s k * qpow d k).
  { assert (Hsd' : ~ s * d == 0) by (intro Z; rewrite Z in Hsd; discriminate Hsd).
    assert (Er : e == r * (s * d)).
    { unfold r, Qdiv. rewrite <- Qmult_assoc, (Qmult_comm (/ _)), Qmult_inv_r by exact Hsd'. ring. }
    rewrite (qpow_wd _ _ k Er), !qpow_mul. ring. }
  assert (Hsk : 1 <= qpow s k).
  { pose proof (bernoulli s k Hs). assert (0 <= inject_Z (Z.of_nat k) * (s - 1)).
    { apply Qmult_le_0_compat; [|lra]. change 0 with (inject_Z 0). rewrite <- Zle_Qle. lia. }
    lra. }
  assert (Hdk : 0 < qpow d k) by (apply qpow_pos; exact Hd).
  (* LHS = c r^k s^k d^k >= c (1 + k(r-1)) s^k d^k > A s^k d^k >= (|M| + |C| s^k) d^k *)
  assert (Hpos : 0 < qpow s k * qpow d k) by (apply Qmult_lt_0_compat; [lra | exact Hdk]).
  assert (Hlhs : c * (1 + inject_Z (Z.of_nat k) * (r - 1)) * (qpow s k * qpow d k)
                 <= c * qpow e k).
  { rewrite Ee. setoid_replace (c * (qpow r k * qpow s k * qpow d k))
      with (c * qpow r k * (qpow s k * qpow d k)) by ring.
    apply Qmult_le_compat_r; [|lra]. apply Qmult_le_l; lra. }
  assert (Hmid : A * (qpow s k * qpow d k) < c * (1 + inject_Z (Z.of_nat k) * (r - 1)) * (qpow s k * qpow d k)).
  { apply Qmult_lt_compat_r; [exact Hpos | lra]. }
  assert (Hrhs : (Qabs M + Qabs C * qpow s k) * qpow d k <= A * (qpow s k * qpow d k)).
  { unfold A. pose proof (Qabs_nonneg M). pose proof (Qabs_nonneg C).
    setoid_replace ((Qabs M + Qabs C) * (qpow s k * qpow d k))
      with ((Qabs M * qpow s k + Qabs C * qpow s k) * qpow d k) by ring.
    apply Qmult_le_compat_r; [|lra]. nra. }
  lra.
Qed.
End Contra.

Print Assumptions window_contra.
