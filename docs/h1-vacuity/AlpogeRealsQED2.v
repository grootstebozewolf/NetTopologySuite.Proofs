(* AlpogeRealsQED2.v -- twelve more refined main-line lemmas of the claimed
   RH/GRH Lean development (CocoSgt/riemann-hypothesis-lean @ 7cbf7a0),
   proved over Stdlib's R within the three-axiom allowlist
   (docs/axiom-allowlist.txt).

   Infrastructure (Part 0): an ALLOWLIST-CLEAN logarithm.  Stdlib's ln and
   Rpower carry Classical_Prop.classic (AlpogeRealsQED.v).  Here
     Lc y   := the root of exp x - y on [-1/y, y] given by Stdlib's IVT
               (continuity_exp, IVT, Rlt_dec are allowlist-clean),
     rpc x a := exp (a * Lc x)            (x^a for x > 0),
   with exp (Lc y) = y (y > 0) and Lc (exp x) = x, so Lc is THE inverse of
   exp on (0, oo); rpc has the rpow laws used by the Lean proofs (add, mult,
   one, monotone in base and in exponent).  Statements below use Lc / rpc
   where Lean uses Real.log / rpow.

     1  level_of_tiedWin                 (TopWin.lean)
     2  windowHyp_of_rpow_eventually     (WindowHypOfRpow.lean)
     3  windowInequality_of_artinInputs  (WindowInequalityOfArtinInputs.lean)
     4  core_gm                          (CoreGm.lean)
     5  CharacterBalanceMoves.core       (ChCore.lean)
     6  tiedCore_of_chainTied            (LevelGmLeOnFamilyScales.lean)
     7  charFamily_LFunction_ne_zero_of_one_le_re
     8  lemmaL                           (lemmaL.lean)
     9  zeroFree_of_rpow_window          (ZeroFreeOfRpowWindow.lean)
    10  formB                            (PrimitiveCosets/Imports.lean)
    11  landau_pole_re_le                (LandauPoleReLe.lean)
    12  zeroFreeAll_of_topG (composition) (ZeroFreeAllOfTopG.lean)

   Premises are the Lean lemma's own premises plus, for composition lemmas,
   the OTHER inventory lemmas the Lean proof calls (named hypotheses, tagged
   [inventory]), exactly as the ledger treats them.  Items 3, 4, 9, 10 and 12
   chain the R theorems of this file and of AlpogeRealsQED.v wherever those
   exist.

   Evidence for docs/attacks/2026-11-21-alpoge-next-twelve-over-reals.md.
   NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import Reals Lra Psatz List Factorial.
From NTS.Proofs.Probes Require Import AlpogeRealsQED.
From NTS.Proofs Require Export LogRpowClean.
Import ListNotations.
Local Open Scope R_scope.

(* Part 0 (Lc, rpc) lives in theories/LogRpowClean.v *)

(* ===================================================================== *)
(* 1  level_of_tiedWin                                                    *)
(* ===================================================================== *)
Definition HasWindowsC (la : R) (S : R -> Prop) : Prop :=
  forall y, exists Y, y <= Y /\ forall x, Y <= x -> x <= rpc Y la -> S x.

Section TiedWin.
Variable Cx : Type.
Variable re : Cx -> R.
Variable nz : Cx -> Prop.
Variable Gm : R -> R.
Variable la : R.
Definition ZFA (theta : R) : Prop := forall s, theta < re s -> nz s.
Variable Fam : R -> Type.
Variable Win : forall eps, Fam eps -> R -> Prop.
Variable EF : forall eps, Fam eps -> Prop.
Variable TO : forall eps, Fam eps -> R -> R -> Prop.
Hypothesis h112 : forall eD eL eps, 0 < eps -> forall Fm : Fam eps, EF eps Fm -> TO eps Fm eD eL ->
  exists x1, forall x, x1 <= x -> Win eps Fm x -> Gm x <= rpc x (1 / 2 + (eD + eL + 7) * eps).
Hypothesis hB : forall theta, 0 < theta -> theta < 1 ->
  HasWindowsC la (fun x => Gm x <= rpc x theta) -> ZFA theta.
Hypothesis h : exists eD eL e1, 0 < e1 /\ forall eps, 0 < eps -> eps < e1 ->
  exists Fm : Fam eps, EF eps Fm /\ HasWindowsC la (Win eps Fm) /\ TO eps Fm eD eL.

Theorem level_of_tiedWin : ZFA (1 / 2).
Proof.
  destruct h as [eD [eL [e1 [He1 H]]]].
  intros s Hs.
  set (m := Rmin (re s - 1 / 2) (1 / 2)).
  assert (Hm1 : m <= re s - 1 / 2) by apply Rmin_l.
  assert (Hm2 : m <= 1 / 2) by apply Rmin_r.
  assert (Hm0 : 0 < m) by (unfold m; apply Rmin_glb_lt; lra).
  destruct (exists_small_eps (eD + eL + 7) (m / 2) e1 ltac:(lra) He1) as [eps [He0 [Hlt HCe]]].
  destruct (H eps He0 Hlt) as [Fm [HE [HW HT]]].
  destruct (h112 eD eL eps He0 Fm HE HT) as [x1 Hx].
  apply (hB (1 / 2 + m / 2)); [lra|lra| |lra].
  intro y. destruct (HW (Rmax y (Rmax x1 1))) as [Y [HY HYw]].
  exists Y. split; [eapply Rle_trans; [apply Rmax_l|exact HY]|].
  intros x Hx1 Hx2.
  assert (Hxx1 : x1 <= x).
  { eapply Rle_trans; [|exact Hx1]. eapply Rle_trans; [|exact HY].
    eapply Rle_trans; [apply Rmax_l|apply Rmax_r]. }
  assert (Hx1' : 1 <= x).
  { eapply Rle_trans; [|exact Hx1]. eapply Rle_trans; [|exact HY].
    eapply Rle_trans; [apply Rmax_r|apply Rmax_r]. }
  eapply Rle_trans; [apply (Hx x Hxx1 (HYw x Hx1 Hx2))|].
  apply rpc_mono_exp; [exact Hx1'|lra].
Qed.
End TiedWin.

(* ===================================================================== *)
(* 2  windowHyp_of_rpow_eventually                                        *)
(* ===================================================================== *)
Theorem windowHyp_of_rpow_eventually : forall K eta, 0 <= K -> 0 < eta ->
  exists Y1, forall Y, Y1 <= Y -> 1 <= Y /\ K * Lc Y <= rpc Y eta.
Proof.
  intros K eta HK Heta.
  set (hh := eta / 2). assert (Hh : 0 < hh) by (unfold hh; lra).
  set (B := K / hh + 1).
  assert (HKh : 0 <= K / hh) by (unfold Rdiv; apply Rmult_le_pos; [lra|left; apply Rinv_0_lt_compat; lra]).
  assert (HB : 0 < B) by (unfold B; lra).
  exists (Rmax 1 (rpc B (/ hh))). intros Y HY.
  assert (HY1 : 1 <= Y) by (eapply Rle_trans; [apply Rmax_l|exact HY]).
  assert (HYB : rpc B (/ hh) <= Y) by (eapply Rle_trans; [apply Rmax_r|exact HY]).
  split; [exact HY1|].
  set (P := rpc Y hh).
  assert (HP : B <= P).
  { unfold P. replace B with (rpc (rpc B (/ hh)) hh).
    - apply rpc_mono_base; [lra|apply rpc_pos|exact HYB].
    - rewrite rpc_mult, Rinv_l by lra. apply rpc_one. exact HB. }
  assert (HlnY : 0 <= Lc Y) by (apply Lc_nonneg; exact HY1).
  assert (Hl : Lc Y <= P / hh) by (apply Lc_le_rpc_div; lra).
  assert (HP0 : 0 <= P) by (left; apply rpc_pos).
  assert (Heq : rpc Y eta = P * P) by (unfold P; rewrite <- rpc_add; f_equal; unfold hh; field).
  rewrite Heq.
  assert (H1 : K * Lc Y <= K * (P / hh)) by (apply Rmult_le_compat_l; assumption).
  assert (H2 : K * (P / hh) = K / hh * P) by (field; lra).
  assert (H3 : K / hh * P <= P * P) by (apply Rmult_le_compat_r; [exact HP0|unfold B in HP; lra]).
  lra.
Qed.

(* ===================================================================== *)
(* 4  core_gm   (the eventual step 1 + 4o <= x^eps proved here)           *)
(* ===================================================================== *)
Lemma eventually_rpc_ge : forall A eps, 1 <= A -> 0 < eps ->
  exists x3, forall x, x3 <= x -> A <= rpc x eps.
Proof.
  intros A eps HA He. exists (Rmax 1 (rpc A (/ eps))). intros x Hx.
  assert (H1 : rpc A (/ eps) <= x) by (eapply Rle_trans; [apply Rmax_r|exact Hx]).
  replace A with (rpc (rpc A (/ eps)) eps) at 1.
  - apply rpc_mono_base; [lra|apply rpc_pos|exact H1].
  - rewrite rpc_mult, Rinv_l by lra. apply rpc_one. lra.
Qed.

Section CoreGm.
Variable Gm : R -> R.
Variable Hst KC : Type.
Variable EAt : Hst -> R -> R -> R -> Prop.
Variable CoreAt : Hst -> R -> R -> KC -> R -> R -> Prop.
Variable Sg : Hst -> R -> R.
Variable o : R.
Hypothesis o_nonneg : 0 <= o.
(* [inventory] ch_core (+ ch_top, gmA_eq), with C = max(eD+eL,0)+3 *)
Hypothesis CH : forall eD eL kc Cc eps, 0 < eps -> exists x1, forall x, x1 <= x ->
  1 <= x /\ forall h, EAt h x eps Cc -> CoreAt h eD eL kc eps x ->
    0 <= eD + eL /\ Gm x <= rpc x (1 / 2 + (eD + eL + 3 + 3) * eps) + Sg h x.
(* [inventory] sigA_le *)
Hypothesis SIG : forall h x eps Cc, EAt h x eps Cc -> 1 <= x ->
  Sg h x <= 4 * o * rpc x (1 / 2 + eps).

Theorem core_gm : forall eD eL kc Cc eps, 0 < eps -> exists x1, forall x, x1 <= x ->
  forall h, EAt h x eps Cc -> CoreAt h eD eL kc eps x ->
    Gm x <= rpc x (1 / 2 + (eD + eL + 7) * eps).
Proof.
  intros eD eL kc Cc eps He.
  destruct (CH eD eL kc Cc eps He) as [x1 Hx1].
  destruct (eventually_rpc_ge (1 + 4 * o) eps ltac:(lra) He) as [x3 Hx3].
  exists (Rmax x1 x3). intros x Hx h HE HC.
  assert (H1 : x1 <= x) by (eapply Rle_trans; [apply Rmax_l|exact Hx]).
  assert (H3 : x3 <= x) by (eapply Rle_trans; [apply Rmax_r|exact Hx]).
  destruct (Hx1 x H1) as [Hx1' Hb]. destruct (Hb h HE HC) as [HE0 HG].
  pose proof (SIG h x eps Cc HE Hx1') as HS.
  pose proof (Hx3 x H3) as HX.
  set (P := rpc x (1 / 2 + (eD + eL + 3 + 3) * eps)) in *.
  assert (HP0 : 0 <= P) by (left; apply rpc_pos).
  assert (HPe : rpc x (1 / 2 + eps) <= P) by (apply rpc_mono_exp; [exact Hx1'|nra]).
  assert (Ht : rpc x (1 / 2 + (eD + eL + 7) * eps) = rpc x eps * P).
  { unfold P. rewrite <- rpc_add. f_equal. ring. }
  rewrite Ht.
  assert (H4 : 4 * o * rpc x (1 / 2 + eps) <= 4 * o * P) by (apply Rmult_le_compat_l; lra).
  assert (H5 : (1 + 4 * o) * P <= rpc x eps * P) by (apply Rmult_le_compat_r; assumption).
  lra.
Qed.
End CoreGm.

(* ===================================================================== *)
(* 6  tiedCore_of_chainTied   and   3  windowInequality_of_artinInputs    *)
(* ===================================================================== *)
Theorem tiedCore_of_chainTied : forall (Ix El : Type) (TTh : Ix -> El -> Prop)
  (CoreAt : Ix -> (El -> Prop) -> Prop),
  (forall i (S S' : El -> Prop), (forall t, S t <-> S' t) -> CoreAt i S -> CoreAt i S') ->
  (exists i0 (TT : El -> Prop), (forall t, TT t <-> TTh i0 t) /\ CoreAt i0 TT) ->
  exists i0, CoreAt i0 (TTh i0).
Proof.
  intros Ix El TTh CoreAt Hext [i0 [TT [HTT HC]]]. exists i0. exact (Hext i0 TT (TTh i0) HTT HC).
Qed.

Section ArtinInputs.
Variable Gm : R -> R.
Variable Hst KC : Type.
Variable EAt : Hst -> R -> R -> R -> Prop.
Variable CoreAt : Hst -> R -> R -> KC -> R -> R -> Prop.
(* [inventory] core_gm (item 4 above) *)
Hypothesis COREGM : forall eD eL kc Cc eps, 0 < eps -> exists x1, forall x, x1 <= x ->
  forall h, EAt h x eps Cc -> CoreAt h eD eL kc eps x -> Gm x <= rpc x (1 / 2 + (eD + eL + 7) * eps).
Variable Fam : R -> Type.
Variable Win : forall eps, Fam eps -> R -> Prop.
Variable memF : forall eps, Fam eps -> R -> Hst -> Prop.
Variable Tied : forall eps, Fam eps -> R -> R -> KC -> R -> R -> Prop.
Definition EFamC {eps} (Fm : Fam eps) : Prop :=
  exists Cc xE, forall x, xE <= x -> forall h, memF eps Fm x h -> EAt h x eps Cc.
Definition TiedOn {eps} (Fm : Fam eps) (eD eL : R) : Prop :=
  exists kc CL x0, forall x, x0 <= x -> Win eps Fm x -> Tied eps Fm eD eL kc CL x.
(* the premise h of the Lean lemma (tiedCore_of_chainTied's output) *)
Hypothesis ARTIN : forall eps (Fm : Fam eps) eD eL kc CL x,
  Tied eps Fm eD eL kc CL x -> exists h, memF eps Fm x h /\ CoreAt h eD eL kc eps x.

Theorem windowInequality_of_artinInputs : forall eD eL eps, 0 < eps -> forall Fm : Fam eps,
  EFamC Fm -> TiedOn Fm eD eL ->
  exists x1, forall x, x1 <= x -> Win eps Fm x -> Gm x <= rpc x (1 / 2 + (eD + eL + 7) * eps).
Proof.
  intros eD eL eps He Fm [Cc [xE HE]] [kc [CL [x0 HT]]].
  destruct (COREGM eD eL kc Cc eps He) as [x1 Hx1].
  exists (Rmax x1 (Rmax x0 xE)). intros x Hx Hw.
  assert (H1 : x1 <= x) by (eapply Rle_trans; [apply Rmax_l|exact Hx]).
  assert (H0 : x0 <= x).
  { eapply Rle_trans; [|exact Hx]. eapply Rle_trans; [apply Rmax_l|apply Rmax_r]. }
  assert (HxE : xE <= x).
  { eapply Rle_trans; [|exact Hx]. eapply Rle_trans; [apply Rmax_r|apply Rmax_r]. }
  destruct (ARTIN eps Fm eD eL kc CL x (HT x H0 Hw)) as [h [Hm Hc]].
  exact (Hx1 x H1 h (HE x HxE h Hm) Hc).
Qed.
End ArtinInputs.

(* ===================================================================== *)
(* 5  CharacterBalanceMoves.core                                          *)
(* ===================================================================== *)
(* |TT| m b (delta2/2) Y <= Err + 2 |TT| m b / x, from
   [inventory] per-coset bounds (th_le + ch_balance + hTop) and the
   orthogonality identity (sum_Th), and the premise hY. *)
Theorem character_balance_core : forall (us : list R) nTT m b delta2 x Err Y Tsum,
  (1 <= length us)%nat -> 0 <= m * b * (delta2 / 2) ->
  Forall (fun v => v <= Err + 2 * nTT * m * b / x) us ->
  rsum us = INR (length us) * (m * b * (delta2 / 2) * Tsum) ->
  nTT * Y <= Tsum ->
  nTT * m * b * (delta2 / 2) * Y <= Err + 2 * nTT * m * b / x.
Proof.
  intros us nTT m b delta2 x Err Y Tsum HA0 Hfac Hper Hortho HlowY.
  set (E := Err + 2 * nTT * m * b / x) in *.
  assert (Hs : rsum us <= INR (length us) * E).
  { clear Hortho HA0. induction Hper as [|v l Hv _ IH]; simpl rsum; simpl length.
    - simpl. lra.
    - rewrite S_INR. lra. }
  assert (HnA : 0 < INR (length us)) by (apply lt_0_INR; lia).
  rewrite Hortho in Hs.
  assert (Hc : m * b * (delta2 / 2) * Tsum <= E) by (apply (Rmult_le_reg_l (INR (length us))); [exact HnA|lra]).
  assert (m * b * (delta2 / 2) * (nTT * Y) <= m * b * (delta2 / 2) * Tsum) by (apply Rmult_le_compat_l; assumption).
  replace (nTT * m * b * (delta2 / 2) * Y) with (m * b * (delta2 / 2) * (nTT * Y)) by ring.
  lra.
Qed.

(* ===================================================================== *)
(* 7  charFamily_LFunction_ne_zero_of_one_le_re                           *)
(* ===================================================================== *)
Theorem charFamily_LFunction_ne_zero_of_one_le_re : forall (Ix S : Type) (re : S -> R) (N : Ix -> nat)
  (triv : Ix -> Prop) (Lz : Ix -> S -> Prop) (zeta0 : S -> Prop),
  (forall i, N i = 1%nat \/ ~ triv i) ->                            (* F.adm *)
  (forall i s, N i = 1%nat -> (Lz i s <-> zeta0 s)) ->             (* LFunction_modOne_eq *)
  (forall s, 1 <= re s -> ~ zeta0 s) ->                            (* riemannZeta_ne_zero_of_one_le_re *)
  (forall i s, ~ triv i -> 1 <= re s -> ~ Lz i s) ->               (* LFunction_ne_zero_of_one_le_re *)
  forall i s, 1 <= re s -> ~ Lz i s.
Proof.
  intros Ix S re N triv Lz zeta0 Hadm Hmod Hz Hnt i s Hs.
  destruct (Hadm i) as [H1|H2].
  - intro HL. apply (Hz s Hs). apply (proj1 (Hmod i s H1)). exact HL.
  - exact (Hnt i s H2 Hs).
Qed.

(* ===================================================================== *)
(* 8  lemmaL   9  zeroFree_of_rpow_window   10  formB                     *)
(* ===================================================================== *)
Section FormB.
Variable Cx : Type.
Variable re : Cx -> R.
Variable conj : Cx -> Cx.
Variable I : Type.
Variable Lz : I -> Cx -> Prop.
Variable GmF : R -> R.                             (* Gm F *)
Variable WindowHyp : R -> R -> Prop.               (* WindowHyp F theta delta *)
Definition zeroSet (rho : Cx) : Prop := 0 < re rho /\ exists i, Lz i rho \/ Lz i (conj rho).
Definition ZeroFree (theta : R) : Prop := forall i s, theta < re s -> ~ Lz i s.
(* [inventory] landau_window o windowHypU_of_windowHyp o poleData *)
Hypothesis LW : forall theta delta, 0 < theta -> theta < 1 -> 0 < delta ->
  WindowHyp theta delta -> forall rho, zeroSet rho -> re rho <= theta.
(* [inventory] charFamily_LFunction_ne_zero_of_one_le_re (item 7) *)
Hypothesis NV1 : forall i s, 1 <= re s -> ~ Lz i s.

Theorem lemmaL : forall theta delta, 0 < theta -> theta < 1 -> 0 < delta ->
  WindowHyp theta delta -> ZeroFree theta.
Proof.
  intros theta delta H0 H1 Hd HW i s Hs Hz.
  destruct (Rlt_le_dec (re s) 1) as [Hlt|Hge].
  - assert (HZ : zeroSet s) by (split; [lra|exists i; left; exact Hz]).
    pose proof (LW theta delta H0 H1 Hd HW s HZ). lra.
  - exact (NV1 i s Hge Hz).
Qed.

(* [inventory] windowHyp_of_rpow (its window integral is calculus) *)
Hypothesis WHR : forall theta delta C, 0 < delta ->
  (forall Y0, exists Y, Y0 <= Y /\ forall y, Y <= y -> y <= rpc Y (1 + delta) -> GmF y <= C * rpc y theta) ->
  WindowHyp theta delta.

Theorem zeroFree_of_rpow_window : forall theta delta C, 0 < theta -> theta < 1 -> 0 < delta ->
  (forall Y0, exists Y, Y0 <= Y /\ forall y, Y <= y -> y <= rpc Y (1 + delta) -> GmF y <= C * rpc y theta) ->
  ZeroFree theta.
Proof.
  intros theta delta C H0 H1 Hd h. exact (lemmaL theta delta H0 H1 Hd (WHR theta delta C Hd h)).
Qed.

(* formB: for a level Λ, level_family supplies F with Gm F = Λ.Gm and
   ZeroFree F <-> Λ.ZeroFreeAbove; then zeroFree_of_rpow_window with
   delta = la - 1, C = 1. *)
Variable GmL : R -> R.                             (* Λ.Gm *)
Variable nz : Cx -> Prop.                          (* Λ.ZeroFreeAbove's predicate *)
Hypothesis hG : forall y, GmF y = GmL y.           (* [inventory] level_family *)
Hypothesis hZ : forall theta, ZeroFree theta -> forall s, theta < re s -> nz s.  (* [inventory] level_family *)

Theorem formB : forall la, 1 < la -> forall theta, 0 < theta -> theta < 1 ->
  HasWindowsC la (fun x => GmL x <= rpc x theta) -> forall s, theta < re s -> nz s.
Proof.
  intros la hla theta H0 H1 hW. apply hZ.
  apply (zeroFree_of_rpow_window theta (la - 1) 1 H0 H1 ltac:(lra)).
  intro Y0. destruct (hW Y0) as [Y [HY hx]]. exists Y. split; [exact HY|].
  intros y Hy1 Hy2. replace (1 + (la - 1)) with la in Hy2 by ring.
  rewrite hG, Rmult_1_l. exact (hx y Hy1 Hy2).
Qed.
End FormB.

(* ===================================================================== *)
(* 11 landau_pole_re_le                                                   *)
(* ===================================================================== *)
(* Near a pole rho with residue c <> 0, (s - rho) Phi s = c + (s - rho) h s.
   If Re rho > 2, Phi is bounded near rho ([inventory]
   landau_pole_re_le_bound) and h is bounded near rho (continuity), so
   |c| <= t (M + Hb) at every small distance t: c = 0, contradiction. *)
Lemma pole_residue_zero : forall nc M Hb t0, 0 < t0 -> 0 <= M -> 0 <= Hb ->
  (forall t, 0 < t -> t < t0 -> nc <= t * (M + Hb)) -> nc <= 0.
Proof.
  intros nc M Hb t0 Ht0 HM HH Hall.
  destruct (Rle_lt_dec nc 0) as [Hle|Hpos]; [exact Hle|exfalso].
  set (K := M + Hb + 1). assert (HK : 0 < K) by (unfold K; lra).
  set (t := Rmin (t0 / 2) (nc / (2 * K))).
  assert (Ht1 : t <= t0 / 2) by apply Rmin_l.
  assert (Ht2 : t <= nc / (2 * K)) by apply Rmin_r.
  assert (Htp : 0 < t) by (unfold t; apply Rmin_glb_lt; apply Rdiv_lt_0_compat; lra).
  pose proof (Hall t Htp ltac:(lra)) as H.
  assert (t * (M + Hb) <= t * K) by (apply Rmult_le_compat_l; unfold K; lra).
  assert (t * K <= nc / (2 * K) * K) by (apply Rmult_le_compat_r; lra).
  assert (E : nc / (2 * K) * K = nc / 2) by (field; lra).
  lra.
Qed.

Theorem landau_pole_re_le : forall (Pole : R -> Prop) (absres : R -> R),
  (forall rho, Pole rho -> 0 < absres rho) ->
  (forall rho, Pole rho -> 2 < rho -> exists M Hb t0, 0 < t0 /\ 0 <= M /\ 0 <= Hb /\
     forall t, 0 < t -> t < t0 -> absres rho <= t * (M + Hb)) ->
  forall rho, Pole rho -> rho <= 2.
Proof.
  intros Pole absres Hc Hb rho Hr.
  destruct (Rle_lt_dec rho 2) as [H|H]; [exact H|exfalso].
  destruct (Hb rho Hr H) as [M [Hh [t0 [Ht0 [HM [HH Hall]]]]]].
  pose proof (pole_residue_zero _ _ _ _ Ht0 HM HH Hall). pose proof (Hc rho Hr). lra.
Qed.

(* ===================================================================== *)
(* 12 zeroFreeAll_of_topG: the main line composed over R                  *)
(* ===================================================================== *)
(* level_of_tiedWin (1) with h112 = windowInequality_of_artinInputs (3)
   o core_gm (4), hB = formB (10) o zeroFree_of_rpow_window (9) o lemmaL (8),
   and h = AtWindowScale from TopG via eFamC_of_cls / hypV_of_cls. *)
Section MainLine.
Variable Cx : Type.
Variable re : Cx -> R.
Variable conj : Cx -> Cx.
Variable I : Type.
Variable Lz : I -> Cx -> Prop.
Variable nz : Cx -> Prop.
Variable GmF GmL : R -> R.
Variable WindowHyp : R -> R -> Prop.
Variable la : R.
Hypothesis hla : 1 < la.
Hypothesis LW : forall theta delta, 0 < theta -> theta < 1 -> 0 < delta ->
  WindowHyp theta delta -> forall rho, zeroSet Cx re conj I Lz rho -> re rho <= theta.     (* [inventory] *)
Hypothesis NV1 : forall i s, 1 <= re s -> ~ Lz i s.                                            (* item 7 *)
Hypothesis WHR : forall theta delta C, 0 < delta ->
  (forall Y0, exists Y, Y0 <= Y /\ forall y, Y <= y -> y <= rpc Y (1 + delta) -> GmF y <= C * rpc y theta) ->
  WindowHyp theta delta.                                                                        (* [inventory] *)
Hypothesis hG : forall y, GmF y = GmL y.                                                       (* [inventory] *)
Hypothesis hZ : forall theta, ZeroFree Cx re I Lz theta -> forall s, theta < re s -> nz s.    (* [inventory] *)
Variable Hst KC : Type.
Variable EAt : Hst -> R -> R -> R -> Prop.
Variable CoreAt : Hst -> R -> R -> KC -> R -> R -> Prop.
Variable Sg : Hst -> R -> R.
Variable o : R.
Hypothesis o_nonneg : 0 <= o.
Hypothesis CH : forall eD eL kc Cc eps, 0 < eps -> exists x1, forall x, x1 <= x ->
  1 <= x /\ forall h, EAt h x eps Cc -> CoreAt h eD eL kc eps x ->
    0 <= eD + eL /\ GmL x <= rpc x (1 / 2 + (eD + eL + 3 + 3) * eps) + Sg h x.                (* [inventory] ch_core *)
Hypothesis SIG : forall h x eps Cc, EAt h x eps Cc -> 1 <= x ->
  Sg h x <= 4 * o * rpc x (1 / 2 + eps).                                                       (* [inventory] sigA_le *)
Variable Fam : R -> Type.
Variable Win : forall eps, Fam eps -> R -> Prop.
Variable memF : forall eps, Fam eps -> R -> Hst -> Prop.
Variable Tied : forall eps, Fam eps -> R -> R -> KC -> R -> R -> Prop.
Hypothesis ARTIN : forall eps (Fm : Fam eps) eD eL kc CL x,
  Tied eps Fm eD eL kc CL x -> exists h, memF eps Fm x h /\ CoreAt h eD eL kc eps x.          (* item 6 *)
Hypothesis ATWS : exists eD eL e1, 0 < e1 /\ forall eps, 0 < eps -> eps < e1 ->
  exists Fm : Fam eps, EFamC Hst EAt Fam memF Fm /\ HasWindowsC la (Win eps Fm) /\
    TiedOn KC Fam Win Tied Fm eD eL.                                                            (* [inventory] TopG *)

Theorem zeroFreeAll_of_topG : ZFA Cx re nz (1 / 2).
Proof.
  apply (level_of_tiedWin Cx re nz GmL la Fam Win (fun eps Fm => EFamC Hst EAt Fam memF Fm)
           (fun eps Fm eD eL => TiedOn KC Fam Win Tied Fm eD eL)).
  - intros eD eL eps He Fm HE HT.
    exact (windowInequality_of_artinInputs GmL Hst KC EAt CoreAt
             (core_gm GmL Hst KC EAt CoreAt Sg o o_nonneg CH SIG) Fam Win memF Tied ARTIN eD eL eps He Fm HE HT).
  - intros theta H0 H1 HW s Hs.
    exact (formB Cx re conj I Lz GmF WindowHyp LW NV1 WHR GmL nz hG hZ la hla theta H0 H1 HW s Hs).
  - exact ATWS.
Qed.
End MainLine.

Print Assumptions exp_Lc.
Print Assumptions rpc_mult.
Print Assumptions level_of_tiedWin.
Print Assumptions windowHyp_of_rpow_eventually.
Print Assumptions windowInequality_of_artinInputs.
Print Assumptions core_gm.
Print Assumptions character_balance_core.
Print Assumptions tiedCore_of_chainTied.
Print Assumptions charFamily_LFunction_ne_zero_of_one_le_re.
Print Assumptions lemmaL.
Print Assumptions zeroFree_of_rpow_window.
Print Assumptions formB.
Print Assumptions landau_pole_re_le.
Print Assumptions zeroFreeAll_of_topG.
