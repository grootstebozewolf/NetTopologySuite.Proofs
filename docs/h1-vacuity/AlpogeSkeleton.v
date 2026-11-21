(* AlpogeSkeleton.v -- a Rocq skeleton of the main line of the claimed RH/GRH
   Lean development (CocoSgt/riemann-hypothesis-lean @ 7cbf7a0), with a
   refinement ledger.

   Main line (read from source):
     plugWin / zeroFreeAll_of_topG
       -> zeroFreeOn_of_tiedWin_cyc -> level_of_tiedWin
            <- ChebyshevInequalityOnWindows = windowInequality_of_artinInputs
                 o tiedCore_of_chainTied o core_gm (ch_core, sigA_le, gmA_eq)
            <- ChebyshevInequalityAtWindowScale <- TopG, HostExW
            <- FormBAt <- formB = zeroFree_of_rpow_window
                 = lemmaL o windowHyp_of_rpow ; lemmaL = landau_window o
                   windowHypU_of_windowHyp o poleData
   The skeleton theorem is CoreSliceQED.v : main_line_from_core (Check below):
   ZeroFreeAbove (1/2) from named inputs.

   Inventory: 53 Lean lemmas on that main line.  Granularity: each lemma that
   was READ is one item; subtrees that were NOT expanded (TopG, HostExW,
   one_char, th_le, ch_balance, ch_top, gmA_eq, poleData, ...) count as ONE
   item each, although they hold most of the development's mathematics.

   "Refined": the Lean proof's own reasoning is rebuilt in Rocq with zero
   axioms, its remaining inputs being only standard Mathlib facts (named as
   hypotheses) or other inventory lemmas.  Instance checks (sum_A, sum_Th)
   do NOT count.  Each refined item names its Rocq witness, Checked below so
   that the ledger cannot cite a missing theorem.

   Stop condition (user): at least 2/3 of the lemmas refined.
   two_thirds_refined (QED): 39 of 53 (3 * 39 = 117 >= 106 = 2 * 53).

   Evidence for docs/attacks/2026-11-21-alpoge-skeleton-two-thirds.md.
   NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import String List Arith.
From NTS.Proofs.Probes Require Import LeanSkeletonRebuild LandauWindowCore LandauDichotomyQED
  LandauWindowRebuilt FormBRebuilt WinSeamRebuilt LandauKeyRebuilt CoreSliceQED AlpogeRefineBatch.
Import ListNotations.
Local Open Scope string_scope.

(* ---- the skeleton theorem ---- *)
Check main_line_from_core.

(* ---- witnesses of the refined items (compile-time existence) ---- *)
Check hypV_of_cls_r.               Check eFamC_of_cls_r.
Check level_of_tiedWin_rebuilt.    Check small_eps_w.
Check onWindows_rebuilt.           Check tiedCore_of_chainTied_r.
Check core_gm_rebuilt.             Check sigA_le_r.
Check sq_one_cases.                Check ch_core_CH.
Check core_rebuilt.                Check growth_size_bound.
Check formB_rebuilt.               Check level_family_sum.
Check level_family_zerofree.       Check windowHyp_of_rpow_rebuilt.
Check windowHyp_of_rpow_eventually_r.  Check poly_le_qpow.
Check windowHypU_of_windowHyp_r.   Check lemmaL_rebuilt.
Check charFamily_ne_zero_r.        Check landau_window_rebuilt.
Check key_rebuilt.                 Check window_ineq_discrete.
Check landau_kernel_max_r.         Check kernel_integral_r.
Check tails_rebuilt.               Check landau_tails_chernoff_r.
Check tails_pow_core.              Check landau_coeff_sign_r.
Check dichotomy_rebuilt.           Check nearest_rebuilt.
Check nearest_equi.                Check on_axis.
Check landau_cauchy_r.             Check landau_pole_re_le_r.
Check window_contra.               Check bernoulli.
Check landau_window_re_pos_r.      Check landau_pole_re_le_bound_r.
Check landau_window_full.          Check main_line_from_tiedWin.
(* partial evidence for unrefined items *)
Check sum_Th_instance.             Check sum_A_instance.
Check real_pole_residue_pos.

(* ---- the ledger: (Lean lemma, Rocq witness or "-", refined?) ---- *)
Definition ledger : list (string * string * bool) := [
  (* top *)
  ("zeroFreeAll_of_topG / plugWin (composition)", "main_line_from_core", true);
  ("TopG (shapeWin, from GLq.Green)", "-", false);
  ("HostExW (supplyChi, VWin)", "-", false);
  ("hypV_of_cls", "hypV_of_cls_r", true);
  ("eFamC_of_cls", "eFamC_of_cls_r", true);
  ("zeroFreeOn_of_tiedWin_cyc / level_of_tiedWin", "level_of_tiedWin_rebuilt", true);
  ("exists_small_eps", "small_eps_w", true);
  (* OnWindows *)
  ("windowInequality_of_artinInputs", "onWindows_rebuilt", true);
  ("tiedCore_of_chainTied", "tiedCore_of_chainTied_r", true);
  ("core_gm", "core_gm_rebuilt", true);
  ("large_x_eventually", "-", false);
  ("sigA_le (chr_bounded)", "sigA_le_r, sq_one_cases", true);
  ("gmA_eq", "-", false);
  ("ch_core", "ch_core_CH", true);
  ("CharacterBalanceMoves.core", "core_rebuilt", true);
  ("sum_Th", "- (instance: sum_Th_instance)", false);
  ("sum_A", "- (instance: sum_A_instance)", false);
  ("one_char", "-", false);
  ("th_le", "-", false);
  ("ch_balance", "-", false);
  ("ch_top", "-", false);
  ("proposition_size_bound (GrowthSizeBound)", "growth_size_bound", true);
  (* formB *)
  ("formB", "formB_rebuilt", true);
  ("level_family", "level_family_sum, level_family_zerofree", true);
  ("zeroFree_of_rpow_window", "formB_rebuilt (lemmaL o windowHyp_of_rpow)", true);
  ("windowHyp_of_rpow", "windowHyp_of_rpow_rebuilt", true);
  ("windowHyp_of_rpow_eventually", "windowHyp_of_rpow_eventually_r, poly_le_qpow", true);
  ("windowHypU_of_windowHyp", "windowHypU_of_windowHyp_r", true);
  ("lemmaL", "lemmaL_rebuilt", true);
  ("charFamily_LFunction_ne_zero_of_one_le_re", "charFamily_ne_zero_r", true);
  ("poleData", "- (core: real_pole_residue_pos)", false);
  (* landau_window *)
  ("landau_window", "landau_window_rebuilt, landau_window_full", true);
  ("landau_window_key", "key_rebuilt", true);
  ("landau_window_ineq", "window_ineq_discrete", true);
  ("landau_kernel_max", "landau_kernel_max_r", true);
  ("kernel_integral", "kernel_integral_r", true);
  ("landau_tails", "tails_rebuilt", true);
  ("landau_tails_chernoff", "landau_tails_chernoff_r", true);
  ("landau_tails_pow", "tails_pow_core", true);
  ("landau_coeff", "landau_coeff_sign_r", true);
  ("iteratedDeriv_laplace", "-", false);
  ("landau_dichotomy", "dichotomy_rebuilt", true);
  ("landau_nearest", "nearest_rebuilt", true);
  ("landau_nearest_equi", "nearest_equi", true);
  ("eq_ofReal_sub_of_dist_le_of_le_sub_re", "on_axis", true);
  ("landau_finite", "-", false);
  ("landau_cauchy", "landau_cauchy_r", true);
  ("landau_pole_asym", "-", false);
  ("landau_pole_re_le", "landau_pole_re_le_r", true);
  ("landau_window_contra", "window_contra", true);
  ("landau_growth_contra", "bernoulli (in window_contra)", true);
  ("landau_window_re_pos", "landau_window_re_pos_r", true);
  ("landau_pole_re_le_bound", "landau_pole_re_le_bound_r", true)
].

Definition total : nat := length ledger.
Definition refined : nat := length (filter (fun t => snd t) ledger).

Lemma counts : total = 53 /\ refined = 39.
Proof. vm_compute. split; reflexivity. Qed.

(* Stop condition: at least two thirds refined. *)
Theorem two_thirds_refined : 2 * total <= 3 * refined.
Proof. vm_compute. repeat constructor. Qed.

Print Assumptions two_thirds_refined.
Print Assumptions main_line_from_core.
