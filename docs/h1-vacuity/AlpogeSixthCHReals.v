(* AlpogeSixthCHReals.v -- the six character-sum-side refinements of
   AlpogeSixthCH.v, PROVED over Stdlib's R.

   AlpogeSixthCH.v refines one_char, th_le, ch_balance, ch_top, gmA_eq and
   large_x_eventually over an abstract C (the record CStr, whose fields are
   the Mathlib laws of C the Lean proofs use).  Here:
   - CcStr : CStr is C = R x R (AlpogeDeepStatements' Cc, the field
     Cc_field of AlpogeSixthBatch), every CStr law PROVED (the triangle
     inequality by Cauchy-Schwarz, norm_mul by sqrt_mult);
   - the five C-valued refinements are instantiated at CcStr (one_char_C,
     th_le_C, ch_balance_C, ch_top_C, gmA_eq_C); their remaining premises
     are the inventory lemmas and Mathlib facts about characters, sums and
     the development's carriers named in AlpogeSixthCH.v;
   - large_x_eventually is proved outright over R with the allowlist-clean
     log Lc and rpow rpc: its three Mathlib premises (isLittleO_log_rpow_atTop,
     tendsto_rpow_atTop, rpow_nonneg) are proved here.

   Within docs/axiom-allowlist.txt.  Evidence for
   docs/attacks/2026-11-22-alpoge-sixth-batch.md.  NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import Reals Lra Psatz Ring Field.
From NTS.Proofs.Probes Require Import AlpogeRealsQED AlpogeRealsQED2 AlpogeDeepStatements CleanIntegralQED AlpogeSixthBatch.
From NTS.Proofs.Probes Require AlpogeSixthCH.
Local Open Scope R_scope.

(* x <= sqrt y  from  x^2 <= y *)
Lemma le_sqrt_of_sq : forall x y, 0 <= y -> x * x <= y -> x <= sqrt y.
Proof.
  intros x y Hy H. destruct (Rle_or_lt x 0) as [Hx|Hx].
  - pose proof (sqrt_pos y). lra.
  - rewrite <- (sqrt_square x) by lra. apply sqrt_le_1_alt. exact H.
Qed.

Lemma cnorm_nonneg : forall z, 0 <= cnorm z.
Proof. intro z. apply sqrt_pos. Qed.

Lemma cnorm_sq : forall z, cnorm z * cnorm z = cre z * cre z + cim z * cim z.
Proof. intro z. unfold cnorm. apply sqrt_sqrt. nra. Qed.

Lemma cnorm_add : forall a b, cnorm (cadd a b) <= cnorm a + cnorm b.
Proof.
  intros [ar ai] [br bi]. unfold cnorm, cadd; simpl.
  set (P := ar * ar + ai * ai). set (Q := br * br + bi * bi).
  assert (HP : 0 <= P) by (unfold P; nra). assert (HQ : 0 <= Q) by (unfold Q; nra).
  assert (CS : ar * br + ai * bi <= sqrt P * sqrt Q).
  { rewrite <- sqrt_mult by assumption. apply le_sqrt_of_sq; [nra|].
    unfold P, Q. pose proof (Rle_0_sqr (ar * bi - ai * br)). unfold Rsqr in *. nra. }
  rewrite <- (sqrt_square (sqrt P + sqrt Q)) by (pose proof (sqrt_pos P); pose proof (sqrt_pos Q); lra).
  apply sqrt_le_1_alt.
  replace ((sqrt P + sqrt Q) * (sqrt P + sqrt Q)) with (sqrt P * sqrt P + sqrt Q * sqrt Q + 2 * (sqrt P * sqrt Q)) by ring.
  rewrite !sqrt_sqrt by assumption. unfold P, Q in *. nra.
Qed.

Lemma cnorm_mul : forall a b, cnorm (cmul a b) = cnorm a * cnorm b.
Proof.
  intros [ar ai] [br bi]. unfold cnorm, cmul; simpl.
  rewrite <- sqrt_mult by nra. f_equal. ring.
Qed.

Lemma cnorm_ofR : forall r, cnorm (cofR r) = Rabs r.
Proof.
  intro r. unfold cnorm, cofR; simpl. replace (r * r + 0 * 0) with (Rsqr r) by (unfold Rsqr; ring).
  apply sqrt_Rsqr_abs.
Qed.

Lemma abs_cre_le : forall z, Rabs (cre z) <= cnorm z.
Proof.
  intros [a b]. unfold cnorm; simpl. rewrite <- sqrt_Rsqr_abs. apply sqrt_le_1_alt.
  unfold Rsqr. nra.
Qed.

(* C = R x R as a CStr: every Mathlib law of the record is a theorem here *)
Definition CcStr : AlpogeSixthCH.CStr.
Proof.
  refine (@AlpogeSixthCH.Build_CStr Cc c0 c1 cadd cmul csub cdiv copp cinv Cc_field
            cofR cre cnorm _ _ _ _ _ _ _ _ _ _ _).
  - intros r s. apply Cc_ext; unfold cofR, cadd; simpl; ring.
  - intros r s. apply Cc_ext; unfold cofR, cmul; simpl; ring.
  - reflexivity.
  - intros r E. unfold cofR, c0 in E. injection E. intros; assumption.
  - intros a b. reflexivity.
  - intros r z. unfold cmul, cofR; simpl. ring.
  - intro r. reflexivity.
  - exact abs_cre_le.
  - exact cnorm_add.
  - exact cnorm_mul.
  - exact cnorm_ofR.
Defined.

(* the five C-valued refinements, over R *)
Definition one_char_C := AlpogeSixthCH.one_char_r CcStr.
Definition th_le_C := AlpogeSixthCH.th_le_r CcStr.
Definition ch_balance_C := AlpogeSixthCH.ch_balance_r CcStr.
Definition ch_top_C := AlpogeSixthCH.ch_top_r CcStr.
Definition gmA_eq_C := AlpogeSixthCH.gmA_eq_r CcStr.

(* large_x_eventually over R: the three Mathlib premises, proved for Lc / rpc *)
Lemma exp_ge_1px : forall z, 0 <= z -> 1 + z <= exp z.
Proof.
  intros z Hz. pose proof (exp_ge_Pk 1 z Hz) as H. rewrite Pk_S, Pk_O in H. simpl in H. lra.
Qed.

(* tendsto_rpow_atTop *)
Lemma rpc_top : forall eps, 0 < eps -> forall M, exists x0, forall x, x0 <= x -> M <= rpc x eps.
Proof.
  intros eps Heps M. exists (exp (Rabs M / eps)). intros x Hx.
  pose proof (exp_pos (Rabs M / eps)) as He.
  assert (HL : Rabs M / eps <= Lc x).
  { rewrite <- (Lc_exp (Rabs M / eps)). apply Lc_le_mono; assumption. }
  unfold rpc. assert (Hz : Rabs M <= eps * Lc x).
  { apply (Rmult_le_compat_l eps) in HL; [|lra]. replace (eps * (Rabs M / eps)) with (Rabs M) in HL by (field; lra). exact HL. }
  pose proof (exp_ge_1px (eps * Lc x) ltac:(pose proof (Rabs_pos M); lra)).
  pose proof (Rle_abs M). lra.
Qed.

(* isLittleO_log_rpow_atTop, as the bound for every c > 0 *)
Lemma Lc_littleo : forall eps, 0 < eps -> forall c, 0 < c ->
  exists x0, forall x, x0 <= x -> Rabs (Lc x) <= c * Rabs (rpc x eps).
Proof.
  intros eps Heps c Hc.
  destruct (rpc_top (eps / 2) ltac:(lra) (2 / (eps * c))) as [x1 Hx1].
  exists (Rmax 1 x1). intros x Hx.
  assert (Hx1' : 1 <= x) by (eapply Rle_trans; [apply Rmax_l|exact Hx]).
  assert (Hxp : 0 < x) by lra.
  assert (HL0 : 0 <= Lc x) by (rewrite <- Lc_1; apply Lc_le_mono; lra).
  rewrite (Rabs_right (Lc x)) by lra. rewrite (Rabs_right (rpc x eps)) by (left; apply rpc_pos).
  pose proof (Lc_le_rpc_div x (eps / 2) Hxp ltac:(lra)) as H1.
  pose proof (Hx1 x (Rle_trans _ _ _ (Rmax_r _ _) Hx)) as H2.
  set (q := rpc x (eps / 2)) in *.
  assert (Hq : 0 < q) by apply rpc_pos.
  assert (Hsplit : rpc x eps = q * q).
  { unfold q, rpc. rewrite <- exp_plus. f_equal. field. }
  rewrite Hsplit.
  clearbody q.
  assert (Hd : q / (eps / 2) = 2 / eps * q) by (field; lra).
  rewrite Hd in H1.
  assert (2 / eps = c * (2 / (eps * c))) by (field; lra).
  assert (c * (2 / (eps * c)) * q <= c * q * q).
  {
    assert (0 <= c * q) by (apply Rmult_le_pos; lra).
    replace (c * (2 / (eps * c)) * q) with (c * q * (2 / (eps * c))) by ring.
    apply Rmult_le_compat_l; assumption. }
  rewrite H in H1. replace (c * (q * q)) with (c * q * q) by ring. lra.
Qed.

Theorem large_x_eventually_R : AlpogeSixthCH.LargeXEv Lc rpc.
Proof.
  apply AlpogeSixthCH.large_x_eventually_r.
  - exact Lc_littleo.
  - exact rpc_top.
  - intros x y _. left. apply rpc_pos.
Qed.

Print Assumptions CcStr.
Print Assumptions one_char_C.
Print Assumptions th_le_C.
Print Assumptions ch_balance_C.
Print Assumptions ch_top_C.
Print Assumptions gmA_eq_C.
Print Assumptions large_x_eventually_R.
