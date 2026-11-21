(* LeanSkeletonRebuild.v -- Rocq rebuild of the LOGICAL SKELETON of the main line
   of the claimed RH/GRH Lean development (CocoSgt/riemann-hypothesis-lean @
   7cbf7a0), re-derived from the Lean TYPES (statements) without running Lean.

   Rule of the game: the deep analytic facts that the Lean development imports
   from Mathlib (completed L-functions, functional equation, Gamma-factor
   non-vanishing, Landau's theorem) or proves in its 17M lines (the growth
   bound) enter as SECTION HYPOTHESES, each paired with the Lean declaration it
   mirrors.  What is re-proved here is everything in between: the reflection
   argument and the epsilon bookkeeping.  Scalars are the rationals Q, which
   suffices for the order reasoning and keeps the file free of the Stdlib-Reals
   axioms.  Budget: at most Lean's three axioms (propext, Classical.choice,
   Quot.sound); the target is zero.

   Lean declarations mirrored:
     Formalism/GammaFactorNonvanishing/CritLine.lean
       Formalism.VW.critLine, Formalism.VW.rh_of_every
     Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/TopWin.lean
       exists_small_eps, level_of_tiedWin (shape)
     .../TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean
       ChebyshevGrowthImpliesZeroFree, ZeroFreeAbove

   Evidence for docs/attacks/2026-11-20-alpoge-grh-lean-audit.md, slice 8.
   NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import QArith Qabs Qminmax Lqa.
Local Open Scope Q_scope.

(* ============================================================================
   Part 1.  critLine / rh_of_every: the reflection s <-> 1-s.
   ========================================================================== *)
Section CritLine.

Variable C : Type.                      (* complex numbers *)
Variable re : C -> Q.                   (* real part *)
Variable onem : C -> C.                 (* s |-> 1 - s *)
Hypothesis re_onem : forall s, re (onem s) == 1 - re s.
Variable one_pt : C.                    (* the point s = 1 *)
Hypothesis re_one : re one_pt == 1.

Variable Ch : Type.                     (* Dirichlet characters, all levels *)
Variable inv : Ch -> Ch.                (* chi |-> chi^-1 *)
Variable trivial : Ch.                  (* the trivial character mod 1 *)
Variable prim : Ch -> Prop.             (* chi.IsPrimitive *)
Hypothesis prim_inv : forall chi, prim chi -> prim (inv chi).
                                        (* conductor_inv *)

Variable Lz : Ch -> C -> Prop.          (* LFunction chi s = 0 *)
Variable Cz : Ch -> C -> Prop.          (* completedLFunction chi s = 0 *)

(* LFunction_eq_completed_div_gammaFactor + gammaFactor_ne_zero (Re s > 0):
   L = Lambda / Gamma with Gamma <> 0 on Re s > 0. *)
Hypothesis L_to_C : forall chi s, 0 < re s -> Lz chi s -> Cz chi s.
(* same identity, other direction: 0 / Gamma = 0 (needs s <> 0) *)
Hypothesis C_to_L : forall chi s, 0 < re s -> Cz chi s -> Lz chi s.
(* IsPrimitive.completedLFunction_one_sub: Lambda(chi,1-s) = eps * Lambda(chi^-1, s);
   used as: Lambda(chi,s) = 0 -> Lambda(chi^-1, 1-s) = 0. *)
Hypothesis FE : forall chi s, prim chi -> Cz chi s -> Cz (inv chi) (onem s).

(* UpperTheory.EveryCharacter (the 17M-line output), restricted to the
   instances used: no zero with Re s > 1/2, unless chi = 1 and s = 1. *)
Hypothesis every : forall chi s, 1 # 2 < re s -> (chi <> trivial \/ s <> one_pt) -> ~ Lz chi s.

Theorem critLine : forall chi s, prim chi ->
  0 < re s -> re s < 1 -> Lz chi s -> re s == 1 # 2.
Proof.
  intros chi s Hp H0 H1 Hz.
  destruct (Q_dec (re s) (1 # 2)) as [[Hlt|Hgt]|Heq]; [| |exact Heq]; exfalso.
  - (* Re s < 1/2: reflect *)
    pose proof (re_onem s) as Ho.
    apply (every (inv chi) (onem s)).
    + lra.
    + right. intros E. rewrite E in Ho. lra.
    + apply C_to_L; [lra|]. apply FE; [exact Hp | now apply L_to_C].
  - (* Re s > 1/2: directly *)
    apply (every chi s); auto.
    right. intros E. rewrite E in H1. lra.
Qed.

(* rh_of_every, strip form: the zeta case is chi = trivial (mod 1). *)
Theorem rh_strip_of_every : prim trivial -> forall s,
  0 < re s -> re s < 1 -> Lz trivial s -> re s == 1 # 2.
Proof. intros Hp s; now apply critLine. Qed.


(* rh_of_every, FULL Mathlib shape (the rh_of_right half the strip form lacked):
     RiemannHypothesis : ∀ s, ζ s = 0 → ¬ (∃ n, s = -2(n+1)) → s ≠ 1 → s.re = 1/2.
   Extra trusted inputs, each a Mathlib fact used by Lean's `rh_of_right`:
     zf1   : riemannZeta_ne_zero_of_one_le_re  (no zero on Re s >= 1)
     FE0   : riemannZeta_one_sub + Gamma/cos non-vanishing off the trivial zeros:
             a non-trivial zero with Re s <= 0 reflects to a zero at 1 - s. *)
Variable triv : C -> Prop.               (* s = -2(n+1) for some n *)
Hypothesis zf1 : forall s, 1 <= re s -> ~ Lz trivial s.
Hypothesis FE0 : forall s, Lz trivial s -> ~ triv s -> s <> one_pt -> re s <= 0 ->
  Lz trivial (onem s).

Theorem rh_of_every_full : prim trivial -> forall s,
  Lz trivial s -> ~ triv s -> s <> one_pt -> re s == 1 # 2.
Proof.
  intros Hp s Hz Ht H1.
  destruct (Qlt_le_dec 0 (re s)) as [Hpos|Hnpos].
  - destruct (Qlt_le_dec (re s) 1) as [Hlt1|Hge1].
    + now apply (critLine trivial s Hp).
    + exfalso. exact (zf1 s Hge1 Hz).
  - exfalso. pose proof (re_onem s) as Ho.
    apply (zf1 (onem s)); [lra|]. now apply FE0.
Qed.
End CritLine.

Print Assumptions critLine.
Print Assumptions rh_of_every_full.

(* ============================================================================
   Part 2.  level_of_tiedWin: a growth bound with exponent 1/2 + K*eps for every
   small eps, plus "growth <= y^theta  =>  zero-free above theta", gives
   zero-free above 1/2.  The content is the epsilon selection (exists_small_eps).
   ========================================================================== *)
Section TiedWin.

Variable C : Type.
Variable re : C -> Q.
Variable nz : C -> Prop.                (* L(psi, s) <> 0 for the psi in the level *)

Definition ZeroFreeAbove (theta : Q) : Prop := forall s, theta < re s -> nz s.

Variable Growth : Q -> Prop.            (* exists y0, forall y >= y0, Gm y <= y^theta *)

(* Landau.zero_free_of_Chebyshev_growth : ChebyshevGrowthImpliesZeroFree *)
Hypothesis landau : forall theta, 0 < theta -> theta < 1 -> Growth theta -> ZeroFreeAbove theta.

(* ChebyshevInequalityOnWindows + ChebyshevInequalityAtWindowScale (the
   ch_core / core_gm output): exponent 1/2 + K*eps for all 0 < eps < eps1. *)
Variable K eps1 : Q.
Hypothesis K_nonneg : 0 <= K.
Hypothesis eps1_pos : 0 < eps1.
Hypothesis chain : forall eps, 0 < eps -> eps < eps1 -> Growth ((1 # 2) + K * eps).

(* exists_small_eps (TopWin.lean), for 0 <= K. *)
Lemma exists_small_eps : forall delta, 0 < delta ->
  exists eps, 0 < eps /\ eps < eps1 /\ K * eps <= delta.
Proof.
  intros delta Hd.
  set (e := Qmin (eps1 * (1 # 2)) (delta / (K + 1))).
  assert (HK1 : 0 < K + 1) by lra.
  assert (He1 : e <= eps1 * (1 # 2)) by apply Q.le_min_l.
  assert (He2 : e <= delta / (K + 1)) by apply Q.le_min_r.
  assert (Hpos : 0 < e).
  { unfold e. apply Q.min_glb_lt.
    - lra.
    - apply Qlt_shift_div_l; lra. }
  exists e. split; [exact Hpos|]. split; [lra|].
  (* K*e <= (K+1)*e <= (K+1)*(delta/(K+1)) = delta *)
  apply Qle_trans with ((K + 1) * e).
  - assert (0 <= e) by lra. nra.
  - apply Qle_trans with ((K + 1) * (delta / (K + 1))).
    + apply Qmult_le_l; [exact HK1 | exact He2].
    + rewrite Qmult_div_r; [lra|]. intros E. rewrite E in HK1. discriminate HK1.
Qed.

Theorem zero_free_half : ZeroFreeAbove (1 # 2).
Proof.
  intros s Hs.
  set (delta := Qmin (re s - (1 # 2)) (1 # 2)).
  assert (Hd0 : 0 < delta) by (unfold delta; apply Q.min_glb_lt; lra).
  assert (Hd1 : delta <= re s - (1 # 2)) by apply Q.le_min_l.
  assert (Hd2 : delta <= 1 # 2) by apply Q.le_min_r.
  destruct (exists_small_eps (delta * (1 # 2))) as [eps [He0 [He1 HKe']]].
  { lra. }
  assert (HKe0 : 0 <= K * eps) by (apply Qmult_le_0_compat; lra).
  apply (landau ((1 # 2) + K * eps)).
  - lra.
  - lra.
  - apply chain; auto.
  - lra.
Qed.

End TiedWin.

Print Assumptions zero_free_half.

(* ============================================================================
   Part 3.  The DEFINITE SIGN inside landau_entire / landau_family
   (Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Landau.lean).

   What is non-negative in the Lean proof is NOT a Dirichlet coefficient but
     H(x) := C * x^theta - (R*Gz(x) + sum_S Gchi(x))  >= 0      (hH; from the
   one-sided growth bound), and its Mellin transform satisfies (hM, PhiP)
     M(sigma) = (P'/P(sigma) - (a + b*sigma)) / (sigma*(sigma-1)) + C/(sigma-theta) >= 0
   for real sigma.  Closure of S under chi |-> chi^-1 only makes P'/P real on
   the real axis (`him`).  Near a real zero sigma0 in (theta,1) of P of order
   m >= 1, P'/P(sigma) = m/(sigma - sigma0) + r with r bounded; since
   sigma(sigma-1) < 0 there, M -> -infinity: contradiction.

   Rebuilt here: that contradiction, over Q, with the identity multiplied out
   by the positive quantities u = sigma - sigma0, sigma - theta,
   sigma(1 - sigma) (denominator clearing = translation; |a + b sigma| is
   absorbed in the bound B on r):
     M >= 0   <->   (m + r*u) * (sigma0 + u - theta) <= C * u * s * (1 - s),
                    s = sigma0 + u.
   ========================================================================== *)
Section DefiniteSign.

Variables theta sigma0 m B C Cabs delta : Q.
Hypothesis H_theta : 0 < theta.
Hypothesis H_order : theta < sigma0.
Hypothesis H_lt1 : sigma0 < 1.
Hypothesis H_m : 0 < m.                (* order of the zero, >= 1 *)
Hypothesis H_B : 0 <= B.
Hypothesis H_Cabs : Qabs C <= Cabs.
Hypothesis H_delta : 0 < delta.

(* M(sigma0 + u) >= 0 for all small u > 0, cleared of denominators *)
Hypothesis M_nonneg : forall u, 0 < u -> u < delta -> u < 1 - sigma0 ->
  exists r, - B <= r /\ r <= B /\
    (m + r * u) * (sigma0 + u - theta) <= C * u * ((sigma0 + u) * (1 - (sigma0 + u))).

Theorem no_real_zero_right_of_theta : False.
Proof.
  set (E := m * (sigma0 - theta)).
  set (K := B * (sigma0 - theta) + Cabs + 1).
  assert (HCa : 0 <= Cabs) by (eapply Qle_trans; [apply Qabs_nonneg | exact H_Cabs]).
  assert (HE : 0 < E) by (unfold E; apply Qmult_lt_0_compat; lra).
  assert (HK : 0 < K) by (unfold K; assert (0 <= B * (sigma0 - theta)) by (apply Qmult_le_0_compat; lra); lra).
  set (u := Qmin (Qmin (delta * (1 # 2)) ((1 - sigma0) * (1 # 2))) (E / (2 * K))).
  assert (Hu1 : u <= Qmin (delta * (1 # 2)) ((1 - sigma0) * (1 # 2))) by apply Q.le_min_l.
  assert (Hu2 : u <= delta * (1 # 2)) by (eapply Qle_trans; [exact Hu1 | apply Q.le_min_l]).
  assert (Hu3 : u <= (1 - sigma0) * (1 # 2)) by (eapply Qle_trans; [exact Hu1 | apply Q.le_min_r]).
  assert (Hu4 : u <= E / (2 * K)) by apply Q.le_min_r.
  assert (H2K : 0 < 2 * K) by lra.
  assert (Hdiv : 0 < E / (2 * K)) by (apply Qlt_shift_div_l; lra).
  assert (Hu0 : 0 < u).
  { unfold u. apply Q.min_glb_lt; [apply Q.min_glb_lt|]; lra. }
  (* 2K u <= E *)
  assert (HKu : 2 * K * u <= E).
  { apply Qle_trans with (2 * K * (E / (2 * K))).
    - apply Qmult_le_l; [exact H2K | exact Hu4].
    - rewrite Qmult_div_r; [lra|]. intros Z. rewrite Z in H2K. discriminate H2K. }
  destruct (M_nonneg u Hu0 ltac:(lra) ltac:(lra)) as [r [Hr1 [Hr2 Hineq]]].
  (* m + r u >= m/2:  B u <= m/2  because  B (sigma0-theta) u <= K u <= E/2 *)
  assert (HBu : B * u <= m * (1 # 2)).
  { assert (Hs : 0 < sigma0 - theta) by lra.
    assert (HBK : B * (sigma0 - theta) * u <= K * u).
    { apply Qmult_le_r; [exact Hu0|]. unfold K. lra. }
    assert (Hm2 : (sigma0 - theta) * (B * u) <= (sigma0 - theta) * (m * (1 # 2))).
    { unfold E in HKu. nra. }
    apply Qmult_le_l in Hm2; [exact Hm2 | exact Hs]. }
  assert (Hru : - (B * u) <= r * u) by nra.
  assert (HL : m * (1 # 2) <= m + r * u) by lra.
  (* LHS >= E/2 *)
  assert (HLHS : E * (1 # 2) <= (m + r * u) * (sigma0 + u - theta)).
  { unfold E. nra. }
  (* RHS <= Cabs * u, since 0 < s(1-s) <= 1 *)
  assert (Hs1 : 0 < (sigma0 + u) * (1 - (sigma0 + u))) by (apply Qmult_lt_0_compat; lra).
  assert (Hs2 : (sigma0 + u) * (1 - (sigma0 + u)) <= 1) by nra.
  assert (HCs : C * ((sigma0 + u) * (1 - (sigma0 + u))) <= Cabs).
  { destruct (Qlt_le_dec C 0) as [Cn|Cp].
    - assert (C * ((sigma0 + u) * (1 - (sigma0 + u))) < 0) by nra. lra.
    - rewrite Qabs_pos in H_Cabs by exact Cp. nra. }
  assert (HRHS : C * u * ((sigma0 + u) * (1 - (sigma0 + u))) <= Cabs * u).
  { setoid_replace (C * u * ((sigma0 + u) * (1 - (sigma0 + u))))
      with (u * (C * ((sigma0 + u) * (1 - (sigma0 + u))))) by ring.
    setoid_replace (Cabs * u) with (u * Cabs) by ring.
    apply Qmult_le_l; [exact Hu0 | exact HCs]. }
  (* E/2 <= Cabs u < K u <= E/2 *)
  assert (Cabs * u < K * u) by (apply Qmult_lt_r; [exact Hu0 | unfold K; assert (0 <= B * (sigma0 - theta)) by (apply Qmult_le_0_compat; lra); lra]).
  lra.
Qed.

End DefiniteSign.

Print Assumptions no_real_zero_right_of_theta.

(* ============================================================================
   Part 4.  The sqrt(X) BALANCE: GrowthSizeBound
   (Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean:119,
    proved in .../ChainSlopeWindows/LipschitzWeightAndMinimum.lean:507).

   Lean:  SizeWindows C ε x n nT nT2 m b k aE Err ->
          nT*m*b*((nT2/n)/2)*(Gx - 4 x^(1/2+ε)) <= Err + 2 nT m b / x ->
          Gx <= x^(1/2 + (C+3) ε)

   Translation to exponential atoms (x^(a+b) = x^a x^b; monotone since x >= 3):
     s = x^(1/2)   (x = s^2),  e = x^ε,  e2 = x^(ε/2) (e2^2 = e),  e8 = x^(ε/8),
     c = x^(Cε) >= 1,   target  x^(1/2+(C+3)ε) = e8^3 * (s c e^2 e2 e8).
   Divisions become named quotients: q1 = m^2/k, q2 = nT2 k b x^ε/(n (n x^-ε)),
   rho = nT2/n, w = 1/x.  SizeWindows' conjuncts become:
     aE <= 2 s^2 b;  n <= 2 e8 nT;  1 <= e rho;  s <= e m;  m <= s e2;
     s^2 m <= k;  e k <= n^2 s;  Err <= c (nT aE (1+q1) + m (2 n m b e + q2));
     26 <= e8^3.
   The two error terms that force m ~ sqrt x:
     aE-term   ~ x/m  -> needs m >= x^(1/2)    (s <= e m)
     2nmb-term ~ m    -> needs m <= x^(1/2)    (m <= s e2)
   ========================================================================== *)
Lemma ge1_mul : forall a b : Q, 1 <= a -> 1 <= b -> 1 <= a * b.
Proof. intros; nra. Qed.

Lemma le_mul_ge1 : forall x z : Q, 0 <= x -> 1 <= z -> x <= x * z.
Proof. intros; nra. Qed.

Lemma mul_le_l : forall x y z : Q, 0 <= z -> x <= y -> z * x <= z * y.
Proof.
  intros x y z Hz H. rewrite (Qmult_comm z x), (Qmult_comm z y).
  apply Qmult_le_compat_r; assumption.
Qed.

Section Balance.

Variables s e e2 e8 c b n nT nT2 m k aE Err Gx q1 q2 rho w : Q.
Hypothesis Hs : 1 <= s.
Hypothesis Hs3 : 3 <= s * s.
Hypothesis He : 1 <= e.
Hypothesis He2 : 1 <= e2.
Hypothesis He8 : 1 <= e8.
Hypothesis Hc : 1 <= c.
Hypothesis H26 : 26 <= e8 * e8 * e8.
Hypothesis Hb : 0 < b.
Hypothesis Hn : 0 < n.
Hypothesis HaE0 : 0 <= aE.
Hypothesis HaE : aE <= 2 * (s * s) * b.
Hypothesis HnT : n <= 2 * e8 * nT.
Hypothesis Hrho : rho * n == nT2.
Hypothesis Hrho1 : 1 <= e * rho.
Hypothesis Hm1 : s <= e * m.
Hypothesis Hm2 : m <= s * e2.
Hypothesis Hk1 : s * s * m <= k.
Hypothesis Hk2 : e * k <= n * n * s.
Hypothesis Hq1 : q1 * k == m * m.
Hypothesis Hq2 : q2 * (n * n) == nT2 * k * b * (e * e).
Hypothesis HErr : Err <= c * (nT * aE * (1 + q1) + m * (2 * n * m * b * e + q2)).
Hypothesis Hw : w * (s * s) == 1.
Hypothesis Hmain : nT * m * b * rho * (Gx - 4 * s * e) <= 2 * Err + 4 * nT * m * b * w.

Theorem growth_size_bound :
  Gx <= e8 * e8 * e8 * (s * c * (e * e) * e2 * e8).
Proof.
  (* positivity *)
  assert (Hrho0 : 0 < rho) by nra.
  assert (Hm0 : 0 < m) by nra.
  assert (HnT0 : 0 < nT) by nra.
  assert (Hk0 : 0 < k) by nra.
  assert (Hq10 : 0 <= q1) by nra.
  assert (Hw0 : 0 < w) by nra.
  assert (Hw3 : w <= 1 # 3) by nra.
  set (D := nT * m * b * rho).
  assert (HD : 0 < D) by (unfold D; repeat apply Qmult_lt_0_compat; lra).
  set (T := s * c * (e * e) * e2 * e8).
  assert (HT : 0 < T) by (unfold T; repeat apply Qmult_lt_0_compat; lra).
  (* (i) aE-term:  2 c nT aE (1+q1) <= D * (8 c e^2 s) *)
  assert (I1 : q1 * (s * s) <= m).
  { assert (q1 * (s * s * m) <= q1 * k) by nra.
    assert (q1 * (s * s) * m <= m * m) by nra. nra. }
  assert (I2 : aE * (1 + q1) <= 2 * b * (s * s + m)).
  { assert (aE * (1 + q1) <= 2 * (s * s) * b * (1 + q1)) by nra. nra. }
  assert (I3 : s * s + m <= 2 * e * m * s) by nra.
  assert (A1 : aE * (1 + q1) <= 2 * b * (2 * e * m * s)).
  { apply Qle_trans with (2 * b * (s * s + m)); [exact I2|]. apply mul_le_l; [lra|exact I3]. }
  assert (Hee : e <= e * e * rho) by nra.
  assert (Ti : 2 * c * (nT * aE * (1 + q1)) <= D * (8 * c * (e * e) * s)).
  { apply Qle_trans with ((2 * c * nT) * (2 * b * (2 * e * m * s))).
    - setoid_replace (2 * c * (nT * aE * (1 + q1))) with ((2 * c * nT) * (aE * (1 + q1))) by ring.
      apply mul_le_l; [nra | exact A1].
    - unfold D.
      setoid_replace ((2 * c * nT) * (2 * b * (2 * e * m * s))) with ((8 * c * nT * b * m * s) * e) by ring.
      setoid_replace (nT * m * b * rho * (8 * c * (e * e) * s)) with ((8 * c * nT * b * m * s) * (e * e * rho)) by ring.
      apply mul_le_l; [|exact Hee].
      assert (0 <= c * nT) by nra. assert (0 <= c * nT * b) by nra. assert (0 <= c * nT * b * m) by nra. nra. }
  (* (ii) 2nmb-term:  2 c m (2 n m b e) <= D * (8 c e8 e^2 s e2) *)
  assert (Tii : 2 * c * (m * (2 * n * m * b * e)) <= D * (8 * c * e8 * (e * e) * s * e2)).
  { assert (Z0 : 0 <= 4 * c * m * m * b * e) by (assert (0 <= c * m) by nra; assert (0 <= c * m * m) by nra; assert (0 <= c * m * m * b) by nra; nra).
    apply Qle_trans with ((4 * c * m * m * b * e) * (2 * e8 * nT)).
    - setoid_replace (2 * c * (m * (2 * n * m * b * e))) with ((4 * c * m * m * b * e) * n) by ring.
      apply mul_le_l; [exact Z0 | exact HnT].
    - assert (Z1 : 0 <= 8 * c * m * b * e * e8 * nT) by (assert (0 <= c * m) by nra; assert (0 <= c * m * b) by nra; assert (0 <= c * m * b * e) by nra; assert (0 <= c * m * b * e * e8) by nra; nra).
      apply Qle_trans with ((8 * c * m * b * e * e8 * nT) * (s * e2)).
      + setoid_replace ((4 * c * m * m * b * e) * (2 * e8 * nT)) with ((8 * c * m * b * e * e8 * nT) * m) by ring.
        apply mul_le_l; [exact Z1 | exact Hm2].
      + unfold D.
        setoid_replace ((8 * c * m * b * e * e8 * nT) * (s * e2)) with ((8 * c * m * b * e8 * nT * s * e2) * e) by ring.
        setoid_replace (nT * m * b * rho * (8 * c * e8 * (e * e) * s * e2)) with ((8 * c * m * b * e8 * nT * s * e2) * (e * e * rho)) by ring.
        apply mul_le_l; [|exact Hee].
        assert (0 <= c * m) by nra; assert (0 <= c * m * b) by nra; assert (0 <= c * m * b * e8) by nra;
        assert (0 <= c * m * b * e8 * nT) by nra; assert (0 <= c * m * b * e8 * nT * s) by nra; nra. }
  (* (iii) q2-term:  2 c m q2 <= D * (4 c e s e8) *)
  assert (Q1 : q2 * n == rho * k * b * (e * e)).
  { assert (q2 * n * n == rho * n * k * b * (e * e)) by (rewrite Hrho; nra). nra. }
  assert (Zrb : 0 <= rho * b * (e * e)) by (assert (0 <= rho * b) by nra; nra).
  assert (Q2 : q2 <= rho * b * e * n * s).
  { assert (E1 : q2 * n * e == rho * b * (e * e) * (e * k)).
    { rewrite Q1. ring. }
    assert (E2 : q2 * n * e <= rho * b * (e * e) * (n * n * s)).
    { rewrite E1. apply mul_le_l; [exact Zrb | exact Hk2]. }
    assert (Hne : 0 < n * e) by (apply Qmult_lt_0_compat; lra).
    apply Qmult_le_l with (n * e); [exact Hne|].
    setoid_replace (n * e * q2) with (q2 * n * e) by ring.
    setoid_replace (n * e * (rho * b * e * n * s)) with (rho * b * (e * e) * (n * n * s)) by ring.
    exact E2. }
  assert (Zcm : 0 <= 2 * c * m) by nra.
  assert (Tiii : 2 * c * (m * q2) <= D * (4 * c * e * s * e8)).
  { apply Qle_trans with ((2 * c * m) * (rho * b * e * n * s)).
    - setoid_replace (2 * c * (m * q2)) with ((2 * c * m) * q2) by ring.
      apply mul_le_l; [exact Zcm | exact Q2].
    - assert (Z2 : 0 <= 2 * c * m * rho * b * e * s).
      { assert (0 <= c * m) by nra. assert (0 <= c * m * rho) by nra.
        assert (0 <= c * m * rho * b) by nra. assert (0 <= c * m * rho * b * e) by nra. nra. }
      apply Qle_trans with ((2 * c * m * rho * b * e * s) * (2 * e8 * nT)).
      + setoid_replace ((2 * c * m) * (rho * b * e * n * s)) with ((2 * c * m * rho * b * e * s) * n) by ring.
        apply mul_le_l; [exact Z2 | exact HnT].
      + unfold D. apply Qle_lteq. right. ring. }
  (* (iv) 4 nT m b w <= D * (4/3) e *)
  assert (Znmb : 0 <= nT * m * b) by (assert (0 <= nT * m) by nra; nra).
  assert (Tiv : 4 * nT * m * b * w <= D * ((4 # 3) * e)).
  { unfold D.
    setoid_replace (4 * nT * m * b * w) with ((nT * m * b) * (4 * w)) by ring.
    setoid_replace (nT * m * b * rho * ((4 # 3) * e)) with ((nT * m * b) * ((4 # 3) * (e * rho))) by ring.
    apply mul_le_l; [exact Znmb | lra]. }
  (* assemble: D (Gx - 4se) <= D (X1 + X2 + X3 + X4) *)
  assert (HE2 : 2 * Err <= 2 * c * (nT * aE * (1 + q1)) + 2 * c * (m * (2 * n * m * b * e)) + 2 * c * (m * q2)).
  { assert (2 * Err <= 2 * (c * (nT * aE * (1 + q1) + m * (2 * n * m * b * e + q2)))) by lra.
    setoid_replace (2 * (c * (nT * aE * (1 + q1) + m * (2 * n * m * b * e + q2))))
      with (2 * c * (nT * aE * (1 + q1)) + 2 * c * (m * (2 * n * m * b * e)) + 2 * c * (m * q2)) in H by ring.
    exact H. }
  assert (Hsum : D * (Gx - 4 * s * e) <=
                 D * (8 * c * (e * e) * s + 8 * c * e8 * (e * e) * s * e2 + 4 * c * e * s * e8 + (4 # 3) * e)).
  { assert (HM : D * (Gx - 4 * s * e) <= 2 * Err + 4 * nT * m * b * w) by (unfold D; exact Hmain).
    setoid_replace (D * (8 * c * (e * e) * s + 8 * c * e8 * (e * e) * s * e2 + 4 * c * e * s * e8 + (4 # 3) * e))
      with (D * (8 * c * (e * e) * s) + D * (8 * c * e8 * (e * e) * s * e2) + D * (4 * c * e * s * e8) + D * ((4 # 3) * e))
      by ring.
    lra. }
  assert (Hcan : Gx - 4 * s * e <= 8 * c * (e * e) * s + 8 * c * e8 * (e * e) * s * e2 + 4 * c * e * s * e8 + (4 # 3) * e).
  { apply Qmult_le_l with D; [exact HD|]. exact Hsum. }
  (* each piece <= coefficient * T, total <= 26 T <= e8^3 T *)
  assert (Zs : 0 <= s) by lra. assert (Ze : 0 <= e) by lra. assert (Zc : 0 <= c) by lra.
  assert (P1 : s * e <= T).
  { unfold T. setoid_replace (s * c * (e * e) * e2 * e8) with ((s * e) * (c * e * e2 * e8)) by ring.
    apply le_mul_ge1; [nra|]. repeat apply ge1_mul; lra. }
  assert (P2 : c * (e * e) * s <= T).
  { unfold T. setoid_replace (s * c * (e * e) * e2 * e8) with ((c * (e * e) * s) * (e2 * e8)) by ring.
    apply le_mul_ge1; [|apply ge1_mul; lra].
    assert (0 <= c * (e * e)) by nra. nra. }
  assert (P3 : c * e8 * (e * e) * s * e2 == T) by (unfold T; ring).
  assert (P4 : c * e * s * e8 <= T).
  { unfold T. setoid_replace (s * c * (e * e) * e2 * e8) with ((c * e * s * e8) * (e * e2)) by ring.
    apply le_mul_ge1; [|apply ge1_mul; lra].
    assert (0 <= c * e) by nra. assert (0 <= c * e * s) by nra. nra. }
  assert (P5 : e <= T).
  { unfold T. setoid_replace (s * c * (e * e) * e2 * e8) with (e * (s * c * e * e2 * e8)) by ring.
    apply le_mul_ge1; [lra|]. repeat apply ge1_mul; lra. }
  assert (G26 : Gx <= 26 * T).
  { setoid_replace (8 * c * (e * e) * s) with (8 * (c * (e * e) * s)) in Hcan by ring.
    setoid_replace (8 * c * e8 * (e * e) * s * e2) with (8 * (c * e8 * (e * e) * s * e2)) in Hcan by ring.
    setoid_replace (4 * c * e * s * e8) with (4 * (c * e * s * e8)) in Hcan by ring.
    setoid_replace (4 * s * e) with (4 * (s * e)) in Hcan by ring.
    rewrite P3 in Hcan. lra. }
  assert (H26T : 26 * T <= e8 * e8 * e8 * T).
  { apply Qmult_le_compat_r; [exact H26 | lra]. }
  lra.
Qed.

End Balance.

Print Assumptions growth_size_bound.

(* ============================================================================
   Part 5.  Masullo's deduction (The Music of the Primes, draft 2026-11-20,
   §1.4.5 / Ch. 13), for comparison with Part 2 (zero_free_half) and Part 1.

   Masullo: for each a > 0 the Trace Formula on W_I, I = [-a, a], gives
     L'_f/L_f(s + 1/2, chi) holomorphic on Re s > a  (except s = 1/2 when chi
     is trivial on C_F^1);
   "since a > 0 is arbitrary" there are no zeros with Re > 1/2, and "by the
   functional equation" none with Re < 1/2.

   Trusted inputs (named hypotheses):
     TF    : the Trace Formula consequence, for every a > 0 -- a zero of L at
             w = s + 1/2 would be a pole of L'/L, so: Re w > 1/2 + a -> no zero
             (unless chi trivial and w = 1).  THIS carries the content
             (Theorem 12.5.1.1); here it is an assumption.
     FE    : as in Part 1 (completed L-function functional equation).
   Re-proved: the "a arbitrary" step and the reflection.
   Contrast with Part 2: no growth function, no Landau sign -- the exponent
   1/2 enters through the strip I = [-a, a] centred at the line, not through
   a bound Gm(x) <= x^(1/2 + K eps).
   ========================================================================== *)
Section Masullo.

Variable C : Type.
Variable re : C -> Q.
Variable onem : C -> C.
Hypothesis re_onem : forall s, re (onem s) == 1 - re s.
Variable one_pt : C.
Hypothesis re_one : re one_pt == 1.
Variable Ch : Type.
Variable inv : Ch -> Ch.
Variable trivial : Ch.
Variable prim : Ch -> Prop.
Hypothesis prim_inv : forall chi, prim chi -> prim (inv chi).
Variable Lz Cz : Ch -> C -> Prop.
Hypothesis L_to_C : forall chi s, 0 < re s -> Lz chi s -> Cz chi s.
Hypothesis C_to_L : forall chi s, 0 < re s -> Cz chi s -> Lz chi s.
Hypothesis FE : forall chi s, prim chi -> Cz chi s -> Cz (inv chi) (onem s).

(* Trace Formula consequence, one statement per strip half-width a > 0. *)
Hypothesis TF : forall a, 0 < a -> forall chi w,
  (1 # 2) + a < re w -> (chi <> trivial \/ w <> one_pt) -> ~ Lz chi w.

(* "since a > 0 is arbitrary": zero-free on Re w > 1/2 *)
Lemma masullo_right_of_half : forall chi w,
  1 # 2 < re w -> (chi <> trivial \/ w <> one_pt) -> ~ Lz chi w.
Proof.
  intros chi w Hw Hx. apply (TF ((re w - (1 # 2)) * (1 # 2))); [lra | lra | exact Hx].
Qed.

(* "by the functional equation": zeros in the strip lie on the line *)
Theorem masullo_critLine : forall chi s, prim chi ->
  0 < re s -> re s < 1 -> Lz chi s -> re s == 1 # 2.
Proof.
  intros chi s Hp H0 H1 Hz.
  destruct (Q_dec (re s) (1 # 2)) as [[Hlt|Hgt]|Heq]; [| |exact Heq]; exfalso.
  - pose proof (re_onem s) as Ho.
    apply (masullo_right_of_half (inv chi) (onem s)).
    + lra.
    + right. intros E. rewrite E in Ho. lra.
    + apply C_to_L; [lra|]. apply FE; [exact Hp | now apply L_to_C].
  - apply (masullo_right_of_half chi s); auto.
    right. intros E. rewrite E in H1. lra.
Qed.

End Masullo.

Print Assumptions masullo_critLine.

(* ============================================================================
   Part 6.  level_of_tiedWin with WINDOWS and FormBAt (closes the "shape only"
   caveat on zero_free_half; Formalism/.../TotientGaloisClasses/TopWin.lean :
   level_of_tiedWin, Window.lean : HasWindows, FormBAt).

   Lean:
     HasWindows S la := ∀ y, ∃ Y, y ≤ Y ∧ ∀ x, Y ≤ x → x ≤ Y^la → x ∈ S
     FormBAt la := ∀ θ ∈ (0,1), HasWindows {x | Gm x ≤ x^θ} la → ZeroFreeAbove θ
     level_of_tiedWin : ChebyshevInequalityOnWindows -> FormBAt la ->
                        ChebyshevInequalityAtWindowScale la -> ZeroFreeLevel
   Here the two Chebyshev hypotheses are combined into WIN (for small eps a
   window set Win with HasWindows Win la and Gm x <= x^(1/2 + K eps) on
   Win beyond x1), FormBAt is a hypothesis (it is landau_window's output), and
   x^a is an abstract pw x a, monotone in a for x >= 1 (translation).
   ========================================================================== *)
Section TiedWinWindows.

Variable C : Type.
Variable re : C -> Q.
Variable nz : C -> Prop.
Variable Gm : Q -> Q.
Variable pw : Q -> Q -> Q.                       (* pw x a = x^a *)
Hypothesis pw_mono : forall x a b, 1 <= x -> a <= b -> pw x a <= pw x b.
Variable la : Q.

Definition HasWindows (S : Q -> Prop) : Prop :=
  forall y, exists Y, y <= Y /\ forall x, Y <= x -> x <= pw Y la -> S x.

Definition ZFA (theta : Q) : Prop := forall s, theta < re s -> nz s.

Hypothesis FormBAt : forall theta, 0 < theta -> theta < 1 ->
  HasWindows (fun x => Gm x <= pw x theta) -> ZFA theta.

Variables K eps1 : Q.
Hypothesis K_nonneg : 0 <= K.
Hypothesis eps1_pos : 0 < eps1.
Hypothesis WIN : forall eps, 0 < eps -> eps < eps1 ->
  exists (Win : Q -> Prop) (x1 : Q), HasWindows Win /\
    forall x, x1 <= x -> Win x -> Gm x <= pw x ((1 # 2) + K * eps).

Lemma small_eps_w : forall delta, 0 < delta -> exists eps, 0 < eps /\ eps < eps1 /\ K * eps <= delta.
Proof.
  intros delta Hd.
  set (e := Qmin (eps1 * (1 # 2)) (delta / (K + 1))).
  assert (HK1 : 0 < K + 1) by lra.
  assert (He2 : e <= delta / (K + 1)) by apply Q.le_min_r.
  assert (He1 : e <= eps1 * (1 # 2)) by apply Q.le_min_l.
  assert (Hpos : 0 < e) by (unfold e; apply Q.min_glb_lt; [lra | apply Qlt_shift_div_l; lra]).
  exists e. repeat split; [exact Hpos | lra |].
  apply Qle_trans with ((K + 1) * e); [nra|].
  apply Qle_trans with ((K + 1) * (delta / (K + 1))).
  - apply Qmult_le_l; [exact HK1 | exact He2].
  - rewrite Qmult_div_r; [lra|]. intros Z. rewrite Z in HK1. discriminate HK1.
Qed.

Theorem level_of_tiedWin_rebuilt : ZFA (1 # 2).
Proof.
  intros s Hs.
  set (delta := Qmin (re s - (1 # 2)) (1 # 2)).
  assert (Hd0 : 0 < delta) by (unfold delta; apply Q.min_glb_lt; lra).
  assert (Hd1 : delta <= re s - (1 # 2)) by apply Q.le_min_l.
  assert (Hd2 : delta <= 1 # 2) by apply Q.le_min_r.
  destruct (small_eps_w (delta * (1 # 2)) ltac:(lra)) as [eps [He0 [He1 HKe]]].
  set (theta := (1 # 2) + delta * (1 # 2)).
  destruct (WIN eps He0 He1) as [Win [x1 [HW Hbound]]].
  apply (FormBAt theta); [unfold theta; lra | unfold theta; lra | | unfold theta; lra].
  (* windows for {Gm x <= x^theta}: those of Win, started beyond max(x1, 1) *)
  intros y.
  destruct (HW (Qmax y (Qmax x1 1))) as [Y [HY HYx]].
  exists Y. split; [eapply Qle_trans; [apply Q.le_max_l | exact HY]|].
  intros x Hx1 Hx2.
  assert (Hxx1 : x1 <= x).
  { apply Qle_trans with Y; [|exact Hx1].
    apply Qle_trans with (Qmax y (Qmax x1 1)); [|exact HY].
    apply Qle_trans with (Qmax x1 1); [apply Q.le_max_l | apply Q.le_max_r]. }
  assert (Hx1' : 1 <= x).
  { apply Qle_trans with Y; [|exact Hx1].
    apply Qle_trans with (Qmax y (Qmax x1 1)); [|exact HY].
    apply Qle_trans with (Qmax x1 1); [apply Q.le_max_r | apply Q.le_max_r]. }
  apply Qle_trans with (pw x ((1 # 2) + K * eps)).
  - apply Hbound; [exact Hxx1 | exact (HYx x Hx1 Hx2)].
  - apply pw_mono; [exact Hx1' | unfold theta; lra].
Qed.

End TiedWinWindows.

Print Assumptions level_of_tiedWin_rebuilt.

(* ============================================================================
   Part 7.  The CORE slice: ch_core = core (averaging) ∘ GrowthSizeBound.
   Development/.../LandauTheorems/ChCore.lean :
     core      (CharacterBalanceMoves, l.283): per-coset bound + orthogonality
               identity + lower bound Y  ==>  main inequality
       |TT| m b (delta2/2) Y <= Err + 2 |TT| m b / x
     ch_core   (l.343): core with Y = G - 4 x^(1/2+eps), then
               proposition_size_bound (= growth_size_bound, Part 4).
   Named hypotheses (the analytic inputs, not re-proved):
     per_u   : for each coset index u0 in A0,
               sum_t sum_j Re Th(u0,t) <= Err + 2 |TT| m b / x
               (th_le + ch_balance + gapA <= Err);
     ortho   : sum_{u0 in A0} (that sum) = |A0| * (m b (delta2/2)) * Tsum
               (sum_Th: orthogonality of the characters of H / A0);
     lowY    : |TT| * Y <= Tsum   (one_char, with Y = G - 4 x^(1/2+eps)).
   ========================================================================== *)
From Stdlib Require Import List ZArith Lia.
Import ListNotations.

Fixpoint lsum (l : list Q) : Q := match l with [] => 0 | v :: tl => v + lsum tl end.

Lemma lsum_le : forall (l : list Q) E, Forall (fun v => v <= E) l ->
  lsum l <= inject_Z (Z.of_nat (length l)) * E.
Proof.
  induction l as [|v tl IH]; intros E H; cbn [lsum length].
  - setoid_replace (inject_Z (Z.of_nat 0) * E) with 0 by (cbn; ring). lra.
  - inversion H as [|? ? Hv Htl]; subst. specialize (IH E Htl).
    rewrite Nat2Z.inj_succ, <- Z.add_1_r, inject_Z_plus. change (inject_Z 1) with 1. lra.
Qed.

Section Core.
Variables us : list Q.                          (* per-coset sums, one per u0 in A0 *)
Variables nTT m b delta2 x Err Y Tsum : Q.
Hypothesis HA0 : (1 <= length us)%nat.
Hypothesis Hfac : 0 <= m * b * (delta2 * (1 # 2)).
Hypothesis per_u : Forall (fun v => v <= Err + 2 * nTT * m * b / x) us.
Hypothesis ortho : lsum us == inject_Z (Z.of_nat (length us)) * (m * b * (delta2 * (1 # 2)) * Tsum).
Hypothesis lowY : nTT * Y <= Tsum.

Theorem core_rebuilt : nTT * m * b * (delta2 * (1 # 2)) * Y <= Err + 2 * nTT * m * b / x.
Proof.
  set (nA := inject_Z (Z.of_nat (length us))).
  assert (HnA : 0 < nA).
  { unfold nA. change 0 with (inject_Z 0). rewrite <- Zlt_Qlt. lia. }
  pose proof (lsum_le us _ per_u) as Hs. fold nA in Hs, ortho.
  rewrite ortho in Hs.
  (* cancel nA > 0 *)
  assert (Hc : m * b * (delta2 * (1 # 2)) * Tsum <= Err + 2 * nTT * m * b / x).
  { apply Qmult_le_l with nA; [exact HnA | exact Hs]. }
  assert (m * b * (delta2 * (1 # 2)) * (nTT * Y) <= m * b * (delta2 * (1 # 2)) * Tsum)
    by (apply mul_le_l; [exact Hfac | exact lowY]).
  setoid_replace (nTT * m * b * (delta2 * (1 # 2)) * Y)
    with (m * b * (delta2 * (1 # 2)) * (nTT * Y)) by ring.
  lra.
Qed.
End Core.

Print Assumptions core_rebuilt.

(* ch_core, composed: the averaging core feeds GrowthSizeBound's main inequality
   (delta2 = rho = nT2/n, Y = Gx - 4 x^(1/2+eps), w = 1/x, x = s^2). *)
Theorem ch_core_rebuilt :
  forall (us : list Q) (s e e2 e8 c b n nT nT2 m k aE Err Gx q1 q2 rho w Tsum : Q),
  (* core inputs *)
  (1 <= length us)%nat ->
  Forall (fun v => v <= Err + 2 * nT * m * b * w) us ->
  lsum us == inject_Z (Z.of_nat (length us)) * (m * b * (rho * (1 # 2)) * Tsum) ->
  nT * (Gx - 4 * s * e) <= Tsum ->
  (* SizeWindows, in exponential atoms (as in Part 4) *)
  1 <= s -> 3 <= s * s -> 1 <= e -> 1 <= e2 -> 1 <= e8 -> 1 <= c ->
  26 <= e8 * e8 * e8 -> 0 < b -> 0 < n -> 0 <= aE -> aE <= 2 * (s * s) * b ->
  n <= 2 * e8 * nT -> rho * n == nT2 -> 1 <= e * rho -> s <= e * m -> m <= s * e2 ->
  s * s * m <= k -> e * k <= n * n * s -> q1 * k == m * m ->
  q2 * (n * n) == nT2 * k * b * (e * e) ->
  Err <= c * (nT * aE * (1 + q1) + m * (2 * n * m * b * e + q2)) ->
  w * (s * s) == 1 ->
  Gx <= e8 * e8 * e8 * (s * c * (e * e) * e2 * e8).
Proof.
  intros us s e e2 e8 c b n nT nT2 m k aE Err Gx q1 q2 rho w Tsum
    HA0 Hper Hortho HlowY Hs Hs3 He He2 He8 Hc H26 Hb Hn HaE0 HaE HnT Hrho Hrho1 Hm1 Hm2 Hk1 Hk2 Hq1 Hq2 HErr Hw.
  assert (Hrho0 : 0 < rho) by nra.
  assert (Hm0 : 0 < m) by nra.
  assert (Hfac : 0 <= m * b * (rho * (1 # 2))).
  { assert (0 <= m * b) by nra. apply Qmult_le_0_compat; [lra | lra]. }
  (* x = s^2, so 2 nT m b / x = 2 nT m b w; restate per_u with /x *)
  assert (Hx0 : ~ s * s == 0) by (intro Z; rewrite Z in Hs3; lra).
  assert (Hwx : w == / (s * s)).
  { transitivity (w * ((s * s) * / (s * s))).
    - rewrite Qmult_inv_r by exact Hx0. ring.
    - rewrite Qmult_assoc, Hw. ring. }
  assert (Hper' : Forall (fun v => v <= Err + 2 * nT * m * b / (s * s)) us).
  { eapply Forall_impl; [|exact Hper]. intros v Hv. unfold Qdiv. rewrite <- Hwx. exact Hv. }
  pose proof (core_rebuilt us nT m b rho (s * s) Err (Gx - 4 * s * e) Tsum HA0 Hfac Hper' Hortho HlowY) as Hcore.
  (* main inequality of growth_size_bound *)
  assert (Hmain : nT * m * b * rho * (Gx - 4 * s * e) <= 2 * Err + 4 * nT * m * b * w).
  { unfold Qdiv in Hcore. rewrite <- Hwx in Hcore. nra. }
  exact (growth_size_bound s e e2 e8 c b n nT nT2 m k aE Err Gx q1 q2 rho w
           Hs Hs3 He He2 He8 Hc H26 Hb Hn HaE0 HaE HnT Hrho Hrho1 Hm1 Hm2 Hk1 Hk2 Hq1 Hq2 HErr Hw Hmain).
Qed.

Print Assumptions ch_core_rebuilt.

(* Non-vacuity of ch_core_rebuilt (h1-vacuity discipline): its hypotheses are
   jointly satisfiable.  Witness: x = 16 (s = 4), x^(eps/8) = 3, x^(eps/2) = 81,
   x^eps = 6561 (consistent: e2^2 = e, e8^4 = e2), c = 1, b = 1, n = 200,
   nT = 34, nT2 = 200, rho = 1, m = 1, k = 16, aE = 0, Err = 0, Gx = 0,
   q1 = 1/16, q2 = 16 * 6561^2 / 200, w = 1/16, Tsum = nT (Gx - 4 s e),
   one coset with per-coset sum v = m b (rho/2) Tsum. *)
Theorem ch_core_nonvacuous :
  let s := 4 in let e := 6561 in let e2 := 81 in let e8 := 3 in let c := 1 in
  let b := 1 in let n := 200 in let nT := 34 in let nT2 := 200 in let m := 1 in
  let k := 16 in let aE := 0 in let Err := 0 in let Gx := 0 in let q1 := 1 # 16 in
  let rho := 1 in let w := 1 # 16 in
  let q2 := 16 * (6561 * 6561) / 200 in
  let Tsum := nT * (Gx - 4 * s * e) in
  let us := [m * b * (rho * (1 # 2)) * Tsum] in
  (1 <= length us)%nat /\
  Forall (fun v => v <= Err + 2 * nT * m * b * w) us /\
  lsum us == inject_Z (Z.of_nat (length us)) * (m * b * (rho * (1 # 2)) * Tsum) /\
  nT * (Gx - 4 * s * e) <= Tsum /\
  1 <= s /\ 3 <= s * s /\ 1 <= e /\ 1 <= e2 /\ 1 <= e8 /\ 1 <= c /\
  26 <= e8 * e8 * e8 /\ 0 < b /\ 0 < n /\ 0 <= aE /\ aE <= 2 * (s * s) * b /\
  n <= 2 * e8 * nT /\ rho * n == nT2 /\ 1 <= e * rho /\ s <= e * m /\ m <= s * e2 /\
  s * s * m <= k /\ e * k <= n * n * s /\ q1 * k == m * m /\
  q2 * (n * n) == nT2 * k * b * (e * e) /\
  Err <= c * (nT * aE * (1 + q1) + m * (2 * n * m * b * e + q2)) /\
  w * (s * s) == 1 /\
  e2 * e2 == e /\ e8 * e8 * e8 * e8 == e2.
Proof.
  cbv zeta.
  repeat split; try (cbn; reflexivity); try (vm_compute; reflexivity);
    try (constructor; [vm_compute; discriminate|constructor]);
    try (vm_compute; discriminate); try lra.
Qed.
Print Assumptions ch_core_nonvacuous.
