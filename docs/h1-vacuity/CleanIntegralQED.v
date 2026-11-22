(* CleanIntegralQED.v -- a small ALLOWLIST-CLEAN integration library over
   Stdlib's R, and the two Alpöge-audit integral lemmas it unblocks.

   Why.  The corpus allows exactly three axioms (docs/axiom-allowlist.txt).
   Stdlib's RiemannInt (the value), RiemannInt_P10 (linear combinations),
   ln and Rpower all carry Classical_Prop.classic; so do MVT, MVT_cor1/2,
   Rolle, Heine, compact_P3 and continuity_ab_maj (checked with Print
   Assumptions, Rocq 9.2 / rocq-stdlib 9.2).  Clean, and used here:
   derivable_pt_lim_{plus,minus,opp,mult,scal,id,const,pow,comp,exp},
   completeness, archimed_cor1, Rle_dec / Rlt_dec, sum_f_R0, plus the
   allowlist-clean logarithm Lc / power rpc of AlpogeRealsQED2.v.

   The library (Parts 1-6) imports nothing beyond Stdlib.

   Part 1  Tagged partitions as lists of (tag, right end) cells, tagged sums.
           RInt f a b I  :=  a <= b /\ every tagged partition of [a, b] with
           mesh < d has its tagged sum within eps of I (Riemann's definition
           with a mesh condition; no step functions, no RiemannInt).
   Part 2  Uniqueness, linearity (RInt_plus, RInt_scal: c * f is integrable
           WITHOUT RiemannInt_P10), constants, extensionality, monotonicity.
   Part 3  Chasles: RInt f a b I1 -> RInt f b c I2 -> RInt f a c (I1 + I2)
           for f bounded on [a, c] (partition splitting at b).
   Part 4  A one-sided mean value theorem by BISECTION (Stdlib's MVT is not
           clean): x < y and F' = f on [x, y] give c in [x, y] with
           (F y - F x)/(y - x) <= f c (mvt_ge), and dually (mvt_le).  The
           bisection keeps one decidable inequality per step (Rle_dec), the
           limit point comes from completeness.  Corollaries: mean value
           inequalities, Lipschitz bounds from derivative bounds.
   Part 5  tagged_ftc.  tagged_ftc_value: RInt f a b I and F' = f on [a, b] give
           I = F b - F a (any Riemann-integrable f).  tagged_ftc: F' = f with f
           uniformly continuous on [a, b] gives RInt f a b (F b - F a);
           tagged_ftc_lip / tagged_ftc_c1 for Lipschitz integrands and integrands with a
           bounded derivative.
   Part 6  Change of variables (RInt_change_var, RInt_change_var_FTC) and
           improper integrals over [a, oo) (RIntInf: uniqueness, linearity,
           monotonicity, Chasles = splitting off a finite interval).

   Checks (Parts 7-9), with the clean exp / Lc / rpc:
     Lc_deriv               Lc' = 1/y on (0, oo), elementary
     window_integral        int_Y^(Y^(1+delta)) dy/y = delta * Lc Y
     window_integral_rpow   the same integrand written y^theta * y^(-theta-1)
                            (the shape windowHyp_of_rpow needs)
     window_integral_by_cv  the same value through y = e^u
     windowU_change_var     the y = e^u identity of windowHypU_of_windowHyp
                            for majorants R with a y-antiderivative
     kernel_integral        int_0^oo u^k e^(-a u) / k! = a^(-(k+1))

   Evidence for docs/attacks/2026-11-22-clean-integral-library.md.
   NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import Reals Lra Psatz Lia List Factorial.
From NTS.Proofs.Probes Require Import AlpogeRealsQED AlpogeRealsQED2.
From NTS.Proofs Require Export TaggedIntegral TaggedIntegralApps.
Import ListNotations.
Local Open Scope R_scope.

(* Parts 0-9 live in theories/TaggedIntegral.v and theories/TaggedIntegralApps.v *)

(* ===================================================================== *)
(* Part 10: windowHyp_of_rpow over R                                      *)
(* ===================================================================== *)

(* WindowHyp F theta delta (CharFamily.lean), with the window integral an
   RInt (integrability = existence of the value):  for every eta > 0 there
   are arbitrarily large Y and a majorant R of Gm on [Y, Y^(1+delta)] with
   int_Y^(Y^(1+delta)) R y * y^(-theta-1) dy <= Y^eta. *)
Definition WindowHypR (Gm : R -> R) (theta delta : R) : Prop :=
  forall eta, 0 < eta -> forall Y0, exists Y, Y0 <= Y /\ exists (Rm : R -> R),
    (forall y, Y <= y -> y <= rpc Y (1 + delta) -> 0 <= Rm y /\ Gm y <= Rm y) /\
    exists I, RInt (fun y => Rm y * rpc y (- theta - 1)) Y (rpc Y (1 + delta)) I /\
      I <= rpc Y eta.

(* windowHyp_of_rpow (LandauTheorems/WindowHypOfRpow.lean): the majorant
   R y = |C| y^theta has window integral |C| delta log Y (window_integral_rpow),
   and |C| delta log Y <= Y^eta eventually (windowHyp_of_rpow_eventually,
   AlpogeRealsQED2.v).  This is the hypothesis WHR of AlpogeRealsQED2.v. *)
Theorem windowHyp_of_rpow_r : forall (Gm : R -> R) theta delta C, 0 < delta ->
  (forall Y0, exists Y, Y0 <= Y /\ forall y, Y <= y -> y <= rpc Y (1 + delta) -> Gm y <= C * rpc y theta) ->
  WindowHypR Gm theta delta.
Proof.
  intros Gm theta delta C Hd HW eta Heta Y0.
  destruct (windowHyp_of_rpow_eventually (Rabs C * delta) eta
              ltac:(apply Rmult_le_pos; [apply Rabs_pos|lra]) Heta) as [Y1 HY1].
  destruct (HW (Rmax Y0 Y1)) as [Y [HY Hwin]].
  assert (HYY1 : Y1 <= Y) by (eapply Rle_trans; [apply Rmax_r|exact HY]).
  destruct (HY1 Y HYY1) as [HY1' HK].
  exists Y. split; [eapply Rle_trans; [apply Rmax_l|exact HY]|].
  exists (fun y => Rabs C * rpc y theta). split.
  - intros y Hy1 Hy2. pose proof (rpc_pos y theta). pose proof (Rabs_pos C). split.
    + apply Rmult_le_pos; lra.
    + eapply Rle_trans; [apply Hwin; assumption|].
      apply Rmult_le_compat_r; [lra|apply Rle_abs].
  - exists (Rabs C * (delta * Lc Y)). split.
    + apply (RInt_ext (fun y => Rabs C * (rpc y theta * rpc y (- theta - 1)))); [intros; ring|].
      apply RInt_scal. apply window_integral_rpow; lra.
    + rewrite <- Rmult_assoc. exact HK.
Qed.

(* ===================================================================== *)
(* Axiom audit                                                            *)
(* ===================================================================== *)

Print Assumptions windowHyp_of_rpow_r.
