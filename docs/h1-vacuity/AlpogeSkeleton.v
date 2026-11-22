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
   two_thirds_refined (QED): 53 of 53 since the sixth batch (39 when first
   met; 3 * 53 = 159 >= 106 = 2 * 53).

   Evidence for docs/attacks/2026-11-21-alpoge-skeleton-two-thirds.md.
   NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human-reviewed by Jeroen Bloemscheer (2026-11-22).
     Assisted-by: Claude
*)
From Stdlib Require Import String List Arith.
From NTS.Proofs.Probes Require Import LeanSkeletonRebuild LandauWindowCore LandauDichotomyQED
  LandauWindowRebuilt FormBRebuilt WinSeamRebuilt LandauKeyRebuilt CoreSliceQED AlpogeRefineBatch
  AlpogeRealsQED AlpogeRealsQED2 AlpogeDeepStatements AlpogeRealsQED3 AlpogeIntegralQED CleanIntegralQED AlpogeFifthBatch AlpogeSixthBatch AlpogeSixthCH AlpogeSixthCHReals AlpogeSixthLandau.
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
  ("TopG (shapeWin, from GLq.Green)", "shapeWin_r, topG_of_hyps (AlpogeSixthBatch, refined)", true);
  ("HostExW (supplyChi, VWin)", "supplyChi_r, hostExW_main_r (AlpogeSixthBatch, refined)", true);
  ("hypV_of_cls", "hypV_of_cls_r", true);
  ("eFamC_of_cls", "eFamC_of_cls_r", true);
  ("zeroFreeOn_of_tiedWin_cyc / level_of_tiedWin", "level_of_tiedWin_rebuilt", true);
  ("exists_small_eps", "small_eps_w", true);
  (* OnWindows *)
  ("windowInequality_of_artinInputs", "onWindows_rebuilt", true);
  ("tiedCore_of_chainTied", "tiedCore_of_chainTied_r", true);
  ("core_gm", "core_gm_rebuilt", true);
  ("large_x_eventually", "large_x_eventually_r (AlpogeSixthCH, refined); over R: AlpogeSixthCHReals.large_x_eventually_R", true);
  ("sigA_le (chr_bounded)", "sigA_le_r, sq_one_cases", true);
  ("gmA_eq", "gmA_eq_r, gmA_eq_triv_r (AlpogeSixthCH, refined); over R: AlpogeSixthCHReals.gmA_eq_C", true);
  ("ch_core", "ch_core_CH", true);
  ("CharacterBalanceMoves.core", "core_rebuilt", true);
  ("sum_Th", "sum_Th (AlpogeFifthBatch, refined; instance: sum_Th_instance)", true);
  ("sum_A", "sum_A_trivial, sum_A_nontrivial (AlpogeFifthBatch, refined)", true);
  ("one_char", "one_char_r (AlpogeSixthCH, refined); over R: AlpogeSixthCHReals.one_char_C", true);
  ("th_le", "th_le_r (AlpogeSixthCH, refined); over R: AlpogeSixthCHReals.th_le_C", true);
  ("ch_balance", "ch_balance_r (AlpogeSixthCH, refined); over R: AlpogeSixthCHReals.ch_balance_C", true);
  ("ch_top", "ch_top_r (AlpogeSixthCH, refined); over R: AlpogeSixthCHReals.ch_top_C", true);
  ("proposition_size_bound (GrowthSizeBound)", "growth_size_bound", true);
  (* formB *)
  ("formB", "formB_rebuilt", true);
  ("level_family", "level_family_sum, level_family_zerofree", true);
  ("zeroFree_of_rpow_window", "formB_rebuilt (lemmaL o windowHyp_of_rpow)", true);
  ("windowHyp_of_rpow", "windowHyp_of_rpow_rebuilt; over R: AlpogeIntegralQED.windowHyp_of_rpow, CleanIntegralQED.windowHyp_of_rpow_r", true);
  ("windowHyp_of_rpow_eventually", "windowHyp_of_rpow_eventually_r, poly_le_qpow", true);
  ("windowHypU_of_windowHyp", "windowHypU_of_windowHyp_r", true);
  ("lemmaL", "lemmaL_rebuilt", true);
  ("charFamily_LFunction_ne_zero_of_one_le_re", "charFamily_ne_zero_r", true);
  ("poleData", "poleData_r (AlpogeSixthLandau, refined; poleData_char as inventory)", true);
  (* landau_window *)
  ("landau_window", "landau_window_rebuilt, landau_window_full", true);
  ("landau_window_key", "key_rebuilt", true);
  ("landau_window_ineq", "window_ineq_discrete", true);
  ("landau_kernel_max", "landau_kernel_max_r", true);
  ("kernel_integral", "kernel_integral_r; over R: CleanIntegralQED.kernel_integral", true);
  ("landau_tails", "tails_rebuilt", true);
  ("landau_tails_chernoff", "landau_tails_chernoff_r; over R: AlpogeFifthBatch.landau_tails_chernoff", true);
  ("landau_tails_pow", "tails_pow_core", true);
  ("landau_coeff", "landau_coeff_sign_r; over R: AlpogeFifthBatch.landau_coeff", true);
  ("iteratedDeriv_laplace", "iteratedDeriv_laplace_r, iteratedDeriv_laplace_ILAP (AlpogeSixthLandau, refined)", true);
  ("landau_dichotomy", "dichotomy_rebuilt", true);
  ("landau_nearest", "nearest_rebuilt", true);
  ("landau_nearest_equi", "nearest_equi", true);
  ("eq_ofReal_sub_of_dist_le_of_le_sub_re", "on_axis", true);
  ("landau_finite", "landau_finite_r (AlpogeSixthLandau, refined)", true);
  ("landau_cauchy", "landau_cauchy_r", true);
  ("landau_pole_asym", "landau_pole_asym_r, landau_pole_asym_deriv_r (AlpogeSixthLandau, refined)", true);
  ("landau_pole_re_le", "landau_pole_re_le_r", true);
  ("landau_window_contra", "window_contra", true);
  ("landau_growth_contra", "bernoulli (in window_contra)", true);
  ("landau_window_re_pos", "landau_window_re_pos_r", true);
  ("landau_pole_re_le_bound", "landau_pole_re_le_bound_r", true)
].

Definition total : nat := length ledger.
Definition refined : nat := length (filter (fun t => snd t) ledger).

Lemma counts : total = 53 /\ refined = 53.
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

(* ---- four items that were UNREFINED when STATED in Rocq (no proofs;
        AlpogeDeepStatements.v), within the allowlist; TopG and HostExW
        are refined since the sixth batch ---- *)
Check AlpogeDeepStatements.TopG.
Check AlpogeDeepStatements.HostExW.
Check AlpogeDeepStatements.poleData_statement.
Check AlpogeDeepStatements.landau_pole_asym_statement.

Definition stated4 : list string :=
  [ "TopG (shapeWin, from GLq.Green)"; "HostExW (supplyChi, VWin)"; "poleData"; "landau_pole_asym" ].

(* the name is kept: it anchors docs/attacks/2026-11-21-alpoge-deep-statements.md
   (immutable).  The four were unrefined at that finding's provenance; since
   the sixth batch TopG and HostExW are refined, so this now checks ledger
   membership only (the refined flags are checked in sixth_batch_counts). *)
Theorem stated_four_are_unrefined_items :
  @eq bool (forallb (fun nm => existsb (fun t => String.eqb (fst (fst t)) nm) ledger) stated4) true.
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

(* ---- the integral slice (AlpogeIntegralQED.v): allowlist-clean
        integrability (RI_lipschitz), the integral of 1/y, and
        windowHyp_of_rpow PROVED over R ---- *)
Check AlpogeIntegralQED.RI_lipschitz.
Check AlpogeIntegralQED.rsum_inv_cv.
Check AlpogeIntegralQED.windowHyp_of_rpow.

(* the clean integration library of #1047 (CleanIntegralQED.v) proves
   kernel_integral and, a second time and in its own integral formalism,
   windowHyp_of_rpow *)
Check CleanIntegralQED.kernel_integral.
Check CleanIntegralQED.windowHyp_of_rpow_r.

Definition realsFourth : list string := [ "windowHyp_of_rpow"; "kernel_integral" ].

Theorem integral_slice_proved_is_refined :
  @eq bool (forallb (fun nm => existsb (fun t => andb (String.eqb (fst (fst t)) nm) (snd t)) ledger) realsFourth) true /\
  NoDup (reals12 ++ realsNext ++ realsThird ++ realsFourth) /\
  @eq nat (length (reals12 ++ realsNext ++ realsThird ++ realsFourth)) 34%nat.
Proof.
  split; [vm_compute; reflexivity|]. split; [|reflexivity].
  repeat constructor; simpl; intuition discriminate.
Qed.
Print Assumptions integral_slice_proved_is_refined.

(* ---- the fifth batch (AlpogeFifthBatch.v): landau_tails_chernoff and
        landau_coeff PROVED over R with #1047's library; sum_A and sum_Th
        REFINED from the Lean proof (ledger entries flipped above) ---- *)
Check AlpogeFifthBatch.landau_tails_chernoff.  Check AlpogeFifthBatch.landau_coeff.
Check AlpogeFifthBatch.sum_A_trivial.          Check AlpogeFifthBatch.sum_A_nontrivial.
Check AlpogeFifthBatch.sum_Th.

Definition realsFifth : list string := [ "landau_tails_chernoff"; "landau_coeff" ].

Theorem fifth_batch_counts :
  @eq bool (forallb (fun nm => existsb (fun t => andb (String.eqb (fst (fst t)) nm) (snd t)) ledger) realsFifth) true /\
  NoDup (reals12 ++ realsNext ++ realsThird ++ realsFourth ++ realsFifth) /\
  @eq nat (length (reals12 ++ realsNext ++ realsThird ++ realsFourth ++ realsFifth)) 36%nat /\
  @eq bool (forallb (fun nm => existsb (fun t => andb (String.eqb (fst (fst t)) nm) (snd t)) ledger) ["sum_A"; "sum_Th"]) true.
Proof.
  split; [vm_compute; reflexivity|]. split; [|split; [reflexivity|vm_compute; reflexivity]].
  repeat constructor; simpl; intuition discriminate.
Qed.
Print Assumptions fifth_batch_counts.

(* where each post-#1047 over-R proof lives (review of #1046): the module
   of every witness below is Check-ed above by its qualified name *)
Definition overR_src : list (string * string) := [
  ("windowHyp_of_rpow", "AlpogeIntegralQED.windowHyp_of_rpow");
  ("kernel_integral", "CleanIntegralQED.kernel_integral");
  ("landau_tails_chernoff", "AlpogeFifthBatch.landau_tails_chernoff");
  ("landau_coeff", "AlpogeFifthBatch.landau_coeff") ].

Lemma overR_src_covers : @eq (list string) (map fst overR_src) (List.app realsFourth realsFifth).
Proof. reflexivity. Qed.

(* ---- the sixth batch (AlpogeSixthBatch.v): sum_A, sum_Th (over C = R x R),
        landau_window_ineq and windowHypU_of_windowHyp PROVED over R; TopG and
        HostExW REFINED (ledger entries flipped above) ---- *)
Check AlpogeSixthBatch.sum_A_trivial_C.        Check AlpogeSixthBatch.sum_A_nontrivial_C.
Check AlpogeSixthBatch.sum_Th_C.               Check AlpogeSixthBatch.landau_window_ineq_R.
Check AlpogeSixthBatch.windowHypU_of_windowHyp_R.
Check AlpogeSixthBatch.shapeWin_r.             Check AlpogeSixthBatch.supplyChi_r.

Definition realsSixth : list string :=
  [ "sum_A"; "sum_Th"; "landau_window_ineq"; "windowHypU_of_windowHyp" ].

Definition overR_src6 : list (string * string) := [
  ("sum_A", "AlpogeSixthBatch.sum_A_trivial_C, sum_A_nontrivial_C");
  ("sum_Th", "AlpogeSixthBatch.sum_Th_C");
  ("landau_window_ineq", "AlpogeSixthBatch.landau_window_ineq_R");
  ("windowHypU_of_windowHyp", "AlpogeSixthBatch.windowHypU_of_windowHyp_R") ].

Theorem sixth_batch_counts :
  @eq bool (forallb (fun nm => existsb (fun t => andb (String.eqb (fst (fst t)) nm) (snd t)) ledger) realsSixth) true /\
  @eq (list string) (map fst overR_src6) realsSixth /\
  NoDup (reals12 ++ realsNext ++ realsThird ++ realsFourth ++ realsFifth ++ realsSixth) /\
  @eq nat (length (reals12 ++ realsNext ++ realsThird ++ realsFourth ++ realsFifth ++ realsSixth)) 40%nat.
Proof.
  split; [vm_compute; reflexivity|]. split; [reflexivity|]. split; [|reflexivity].
  repeat constructor; simpl; intuition discriminate.
Qed.
Print Assumptions sixth_batch_counts.

(* ---- the sixth batch, character-sum side: one_char, th_le, ch_balance,
        ch_top, gmA_eq and large_x_eventually REFINED (AlpogeSixthCH.v,
        over an abstract C) and PROVED over R (AlpogeSixthCHReals.v: C = R x R
        as CcStr; large_x_eventually with no premises) ---- *)
Check AlpogeSixthCH.one_char_r.     Check AlpogeSixthCH.th_le_r.      Check AlpogeSixthCH.ch_balance_r.
Check AlpogeSixthCH.ch_top_r.       Check AlpogeSixthCH.gmA_eq_r.     Check AlpogeSixthCH.large_x_eventually_r.
Check AlpogeSixthCHReals.CcStr.
Check AlpogeSixthCHReals.one_char_C.  Check AlpogeSixthCHReals.th_le_C.  Check AlpogeSixthCHReals.ch_balance_C.
Check AlpogeSixthCHReals.ch_top_C.    Check AlpogeSixthCHReals.gmA_eq_C.
Check AlpogeSixthCHReals.large_x_eventually_R.

Definition realsSixthCH : list string :=
  [ "one_char"; "th_le"; "ch_balance"; "ch_top"; "gmA_eq"; "large_x_eventually" ].

Theorem sixth_batch_ch_counts :
  @eq bool (forallb (fun nm => existsb (fun t => andb (String.eqb (fst (fst t)) nm) (snd t)) ledger) realsSixthCH) true /\
  NoDup (reals12 ++ realsNext ++ realsThird ++ realsFourth ++ realsFifth ++ realsSixth ++ realsSixthCH) /\
  @eq nat (length (reals12 ++ realsNext ++ realsThird ++ realsFourth ++ realsFifth ++ realsSixth ++ realsSixthCH)) 46%nat.
Proof.
  split; [vm_compute; reflexivity|]. split; [|reflexivity].
  repeat constructor; simpl; intuition discriminate.
Qed.
Print Assumptions sixth_batch_ch_counts.

(* ---- the sixth batch, Landau side: iteratedDeriv_laplace, landau_finite,
        landau_pole_asym and poleData REFINED (AlpogeSixthLandau.v, over R
        with the cited Mathlib facts and inventory lemmas as hypotheses).
        iteratedDeriv_laplace_ILAP produces landau_coeff's ILAP premise. ---- *)
Check AlpogeSixthLandau.iteratedDeriv_laplace_r.   Check AlpogeSixthLandau.iteratedDeriv_laplace_ILAP.
Check AlpogeSixthLandau.landau_coeff_of_iteratedDeriv_laplace.
Check AlpogeSixthLandau.landau_finite_r.
Check AlpogeSixthLandau.landau_pole_asym_deriv_r.  Check AlpogeSixthLandau.landau_pole_asym_r.
Check AlpogeSixthLandau.poleData_r.

Definition refinedSixth : list string :=
  [ "TopG (shapeWin, from GLq.Green)"; "HostExW (supplyChi, VWin)";
    "one_char"; "th_le"; "ch_balance"; "ch_top"; "gmA_eq"; "large_x_eventually";
    "iteratedDeriv_laplace"; "landau_finite"; "landau_pole_asym"; "poleData" ].

(* all twelve previously unrefined items are refined; every ledger item is *)
Theorem sixth_batch_all_refined :
  @eq nat (length refinedSixth) 12%nat /\
  @eq bool (forallb (fun nm => existsb (fun t => andb (String.eqb (fst (fst t)) nm) (snd t)) ledger) refinedSixth) true /\
  @eq bool (forallb (fun t => snd t) ledger) true.
Proof. split; [reflexivity|]. split; vm_compute; reflexivity. Qed.
Print Assumptions sixth_batch_all_refined.
