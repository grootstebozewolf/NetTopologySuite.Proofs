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

End CritLine.

Print Assumptions critLine.

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
