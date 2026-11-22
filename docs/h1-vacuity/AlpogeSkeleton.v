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
  LandauWindowRebuilt FormBRebuilt WinSeamRebuilt LandauKeyRebuilt CoreSliceQED AlpogeRefineBatch
  AlpogeRealsQED AlpogeRealsQED2 AlpogeDeepStatements AlpogeRealsQED3.
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

(* ---- twelve refined items PROVED over Stdlib's R (AlpogeRealsQED.v),
        within the three-axiom allowlist ---- *)
Check AlpogeRealsQED.landau_growth_contra.   Check AlpogeRealsQED.landau_window_contra.
Check AlpogeRealsQED.landau_kernel_max.      Check AlpogeRealsQED.landau_tails_pow.
Check AlpogeRealsQED.eFamC_of_cls.           Check AlpogeRealsQED.landau_window_re_pos.
Check AlpogeRealsQED.eq_ofReal_sub_of_dist_le_of_le_sub_re.
Check AlpogeRealsQED.landau_nearest_equi.    Check AlpogeRealsQED.exists_small_eps.
Check AlpogeRealsQED.level_family_sum.       Check AlpogeRealsQED.sigA_le.
Check AlpogeRealsQED.hypV_of_cls.

Definition reals12 : list string := [
  "landau_growth_contra"; "landau_window_contra"; "landau_kernel_max"; "landau_tails_pow";
  "eFamC_of_cls"; "landau_window_re_pos"; "eq_ofReal_sub_of_dist_le_of_le_sub_re";
  "landau_nearest_equi"; "exists_small_eps"; "level_family"; "sigA_le (chr_bounded)"; "hypV_of_cls" ].

(* each of the twelve is a refined ledger item, and they are distinct *)
Theorem twelve_proved_are_refined :
  @eq nat (length reals12) 12%nat /\
  @eq bool (forallb (fun nm => existsb (fun t => andb (String.eqb (fst (fst t)) nm) (snd t)) ledger) reals12) true /\
  NoDup reals12.
Proof.
  split; [reflexivity|]. split; [vm_compute; reflexivity|].
  repeat constructor; simpl; intuition discriminate.
Qed.
Print Assumptions twelve_proved_are_refined.
Print Assumptions main_line_from_core.

(* ---- the next twelve, PROVED over R with an allowlist-clean logarithm
        (AlpogeRealsQED2.v) ---- *)
Check AlpogeRealsQED2.level_of_tiedWin.        Check AlpogeRealsQED2.windowHyp_of_rpow_eventually.
Check AlpogeRealsQED2.windowInequality_of_artinInputs.  Check AlpogeRealsQED2.core_gm.
Check AlpogeRealsQED2.character_balance_core.  Check AlpogeRealsQED2.tiedCore_of_chainTied.
Check AlpogeRealsQED2.charFamily_LFunction_ne_zero_of_one_le_re.
Check AlpogeRealsQED2.lemmaL.                  Check AlpogeRealsQED2.zeroFree_of_rpow_window.
Check AlpogeRealsQED2.formB.                   Check AlpogeRealsQED2.landau_pole_re_le.
Check AlpogeRealsQED2.zeroFreeAll_of_topG.

Definition realsNext : list string := [
  "zeroFreeOn_of_tiedWin_cyc / level_of_tiedWin"; "windowHyp_of_rpow_eventually";
  "windowInequality_of_artinInputs"; "core_gm"; "CharacterBalanceMoves.core";
  "tiedCore_of_chainTied"; "charFamily_LFunction_ne_zero_of_one_le_re"; "lemmaL";
  "zeroFree_of_rpow_window"; "formB"; "landau_pole_re_le";
  "zeroFreeAll_of_topG / plugWin (composition)" ].

(* the next twelve are refined ledger items, and all 24 proved over R are distinct *)
Theorem next_twelve_proved_are_refined :
  @eq nat (length realsNext) 12%nat /\
  @eq bool (forallb (fun nm => existsb (fun t => andb (String.eqb (fst (fst t)) nm) (snd t)) ledger) realsNext) true /\
  NoDup (reals12 ++ realsNext).
Proof.
  split; [reflexivity|]. split; [vm_compute; reflexivity|].
  repeat constructor; simpl; intuition discriminate.
Qed.
Print Assumptions next_twelve_proved_are_refined.

(* ---- four UNREFINED items, now STATED in Rocq (no proofs;
        AlpogeDeepStatements.v), within the allowlist ---- *)
Check AlpogeDeepStatements.TopG.
Check AlpogeDeepStatements.HostExW.
Check AlpogeDeepStatements.poleData_statement.
Check AlpogeDeepStatements.landau_pole_asym_statement.

Definition stated4 : list string :=
  [ "TopG (shapeWin, from GLq.Green)"; "HostExW (supplyChi, VWin)"; "poleData"; "landau_pole_asym" ].

Theorem stated_four_are_unrefined_items :
  @eq bool (forallb (fun nm => existsb (fun t => andb (String.eqb (fst (fst t)) nm) (negb (snd t))) ledger) stated4) true.
Proof. vm_compute. reflexivity. Qed.
Print Assumptions stated_four_are_unrefined_items.

(* ---- the third batch, PROVED over R (AlpogeRealsQED3.v) ---- *)
Check AlpogeRealsQED3.landau_dichotomy.     Check AlpogeRealsQED3.landau_nearest.
Check AlpogeRealsQED3.landau_window.        Check AlpogeRealsQED3.landau_tails.
Check AlpogeRealsQED3.landau_window_key.    Check AlpogeRealsQED3.proposition_size_bound.
Check AlpogeRealsQED3.ch_core.              Check AlpogeRealsQED3.landau_pole_re_le_bound.

Definition realsThird : list string := [
  "landau_dichotomy"; "landau_nearest"; "landau_window"; "landau_tails"; "landau_window_key";
  "proposition_size_bound (GrowthSizeBound)"; "ch_core"; "landau_pole_re_le_bound" ].

(* the third batch are refined ledger items; all 32 proved over R are distinct *)
Theorem third_batch_proved_are_refined :
  @eq nat (length realsThird) 8%nat /\
  @eq bool (forallb (fun nm => existsb (fun t => andb (String.eqb (fst (fst t)) nm) (snd t)) ledger) realsThird) true /\
  NoDup (reals12 ++ realsNext ++ realsThird).
Proof.
  split; [reflexivity|]. split; [vm_compute; reflexivity|].
  repeat constructor; simpl; intuition discriminate.
Qed.
Print Assumptions third_batch_proved_are_refined.
