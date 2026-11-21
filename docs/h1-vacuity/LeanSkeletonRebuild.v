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
