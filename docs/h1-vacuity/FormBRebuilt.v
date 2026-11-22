(* FormBRebuilt.v -- the last unassembled link of the main line in the
   claimed RH/GRH Lean development (CocoSgt/riemann-hypothesis-lean @ 7cbf7a0):

     PrimitiveCosets/Imports.lean        : UpperTheory.Comparison₂.formB
     LandauTheorems/ZeroFreeOfRpowWindow : zeroFree_of_rpow_window
     LandauTheorems/WindowHypOfRpow      : windowHyp_of_rpow(_eventually)
     LandauTheorems/WindowHypUOfWindowHyp: windowHypU_of_windowHyp
     LandauTheorems/lemmaL               : lemmaL

   formB : forall Λ, Λ.FormB.  Given la > 1, 0 < theta < 1 and windows
   [Y, Y^la] on which Gm <= x^theta, it produces ZeroFreeAbove theta by:
     (a) windowHyp_of_rpow: the majorant R y = y^theta has window integral
         int_Y^(Y^la) y^theta y^(-theta-1) dy = (la - 1) log Y, and
         K log Y <= Y^eta eventually, for every eta > 0;
     (b) windowHypU_of_windowHyp: change of variables y = e^u;
     (c) lemmaL: landau_window gives Re rho <= theta on the zero set
         {rho | 0 < Re rho, exists i, L(chi_i, rho) = 0 or L(chi_i, conj rho) = 0};
         L(chi_i, s) <> 0 for Re s >= 1 handles the rest;
     (d) level_family: ZeroFree F theta is ZeroFreeAbove theta for the level.

   Rocq (here, over Q):
   - poly_le_qpow (QED): K (n + 1) <= s^n for all large n, whenever s > 1.
     This is the discrete core of windowHyp_of_rpow_eventually: for
     Y in [e^n, e^(n+1)), log Y <= n + 1 and Y^eta >= s^n with s = e^eta.
   - formB_rebuilt (QED): FormBAt la, in exactly the shape that
     LeanSkeletonRebuild.v : level_of_tiedWin_rebuilt consumes, from named
     inputs: the window integral of y^theta (calculus), the eventual
     log/rpow inequality (Mathlib's Real.log_le_rpow_div; core checked
     here), landau_window through the change of variables, nonvanishing on
     Re s >= 1, and level_family.
   - main_line_rebuilt (QED): ZeroFreeAbove (1/2), composing
     level_of_tiedWin_rebuilt with formB_rebuilt into ONE theorem.

   Evidence for docs/attacks/2026-11-21-alpoge-formb-main-line-composed.md.
   NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import QArith Qabs Qminmax Lqa ZArith Lia.
From NTS.Proofs.Probes Require Import LandauWindowCore LeanSkeletonRebuild.
Local Open Scope Q_scope.

(* ===================================================================== *)
(* Part 1: the eventual inequality, discrete core                         *)
(* ===================================================================== *)

Definition nq (n : nat) : Q := inject_Z (Z.of_nat n).

Lemma nq_succ : forall n, nq (S n) == nq n + 1.
Proof. intro n. unfold nq. rewrite Nat2Z.inj_succ, <- Z.add_1_r, inject_Z_plus. reflexivity. Qed.

Lemma nq_nonneg : forall n, 0 <= nq n.
Proof. intro n. unfold nq. change 0 with (inject_Z 0). rewrite <- Zle_Qle. lia. Qed.

Lemma nq_le : forall m n, (m <= n)%nat -> nq m <= nq n.
Proof. intros m n H. unfold nq. rewrite <- Zle_Qle. lia. Qed.

(* Second-order Bernoulli: (1+t)^n >= 1 + n t + n(n-1)/2 t^2 for t >= 0. *)
Lemma bernoulli2 : forall t n, 0 <= t ->
  1 + nq n * t + nq n * (nq n - 1) * (1 # 2) * (t * t) <= qpow (1 + t) n.
Proof.
  intros t n Ht. induction n as [|n IH]; cbn [qpow].
  - assert (E0 : 1 + nq 0 * t + nq 0 * (nq 0 - 1) * (1 # 2) * (t * t) == 1)
      by (unfold nq; simpl; ring).
    rewrite E0. apply Qle_refl.
  - rewrite nq_succ. pose proof (nq_nonneg n) as Hn.
    set (m := nq n) in *.
    assert (H1 : (1 + t) * (1 + m * t + m * (m - 1) * (1 # 2) * (t * t)) <= (1 + t) * qpow (1 + t) n)
      by (apply Qmult_le_l; lra).
    assert (Hm : 0 <= m * (m - 1) * (1 # 2) * (t * t) * t).
    { destruct (Qlt_le_dec m 1) as [Hlt|Hge].
      - (* m = 0 *)
        assert (Hm0 : m == 0).
        { unfold m, nq in *. destruct n; [reflexivity|].
          exfalso. assert (inject_Z 1 <= inject_Z (Z.of_nat (S n))) by (rewrite <- Zle_Qle; lia).
          change (inject_Z 1) with 1 in H. lra. }
        rewrite Hm0. lra.
      - assert (0 <= m * (m - 1)) by nra. assert (0 <= t * t * t) by nra. nra. }
    nra.
Qed.

Theorem poly_le_qpow : forall K s, 0 <= K -> 1 < s ->
  exists N, forall n, (N <= n)%nat -> K * (nq n + 1) <= qpow s n.
Proof.
  intros K s HK Hs. set (t := s - 1).
  assert (Ht : 0 < t) by (unfold t; lra).
  assert (Htt : 0 < t * t) by nra.
  destruct (Qarchimedean (4 * K / (t * t))) as [p Hp].
  exists (Nat.max 3 (Pos.to_nat p)). intros n Hn.
  assert (Hn3 : 3 <= nq n).
  { change 3 with (nq 3). apply nq_le. lia. }
  assert (Hnp : 4 * K / (t * t) < nq n).
  { apply Qlt_le_trans with (inject_Z (Z.pos p)); [exact Hp|].
    unfold nq. rewrite <- Zle_Qle. lia. }
  assert (H4K : 4 * K <= nq n * (t * t)).
  { assert (E : 4 * K / (t * t) * (t * t) == 4 * K) by (field; lra).
    assert (4 * K / (t * t) * (t * t) <= nq n * (t * t)) by (apply Qmult_le_compat_r; lra).
    lra. }
  pose proof (bernoulli2 t n (Qlt_le_weak _ _ Ht)) as Hb.
  assert (Es : qpow s n == qpow (1 + t) n) by (apply qpow_wd; unfold t; ring).
  rewrite Es.
  (* K (n+1) <= 2K (n-1) <= n(n-1)/2 t^2 *)
  assert (H1 : K * (nq n + 1) <= 2 * K * (nq n - 1)) by nra.
  assert (H2 : 2 * K * (nq n - 1) <= nq n * (nq n - 1) * (1 # 2) * (t * t)) by nra.
  assert (H3 : 0 <= nq n * t) by nra.
  lra.
Qed.

Print Assumptions poly_le_qpow.

(* ===================================================================== *)
(* Part 2: formB                                                          *)
(* ===================================================================== *)

Section FormB.
Variable C : Type.
Variable re : C -> Q.
Variable conj : C -> C.                       (* complex conjugation *)
Variable I : Type.
Variable Lz : I -> C -> Prop.                 (* Lz i s : L(chi_i, s) = 0 *)
Variable nz : C -> Prop.                      (* the level's ZeroFreeAbove predicate *)
Variable Gm : Q -> Q.
Variable pw : Q -> Q -> Q.                    (* pw x a = x^a *)
Variable lg : Q -> Q.                         (* log *)
Variable la : Q.
Hypothesis la_gt1 : 1 < la.
Hypothesis pw_nonneg : forall x a, 0 <= x -> 0 <= pw x a.
Hypothesis pw_wd : forall x a b, a == b -> pw x a == pw x b.   (* rpow is a function *)

(* Window integral  int_Y^(Y^(1+delta)) R y * y^(-theta-1) dy, abstract. *)
Variable INT : Q -> Q -> (Q -> Q) -> Q -> Q.  (* INT theta delta R Y *)

(* WindowHyp F theta delta (CharFamily.lean), integrability folded into INT. *)
Definition WH (theta delta : Q) : Prop :=
  forall eta, 0 < eta -> forall Y0, exists Y, Y0 <= Y /\ exists R : Q -> Q,
    (forall y, Y <= y -> y <= pw Y (1 + delta) -> 0 <= R y /\ Gm y <= R y) /\
    INT theta delta R Y <= pw Y eta.

(* Named inputs. *)
Hypothesis INT_rpow : forall theta delta Y, 1 <= Y ->   (* calculus: int y^-1 = delta log Y *)
  INT theta delta (fun y => pw y theta) Y == delta * lg Y.
Hypothesis EV : forall K eta, 0 <= K -> 0 < eta ->      (* windowHyp_of_rpow_eventually *)
  exists Y1, forall Y, Y1 <= Y -> 1 <= Y /\ K * lg Y <= pw Y eta.
Definition Zset (rho : C) : Prop :=
  0 < re rho /\ exists i, Lz i rho \/ Lz i (conj rho).
Hypothesis LW : forall theta delta, 0 < theta -> theta < 1 -> 0 < delta ->
  WH theta delta -> forall rho, Zset rho -> re rho <= theta.
                                   (* landau_window o windowHypU_of_windowHyp, poleData *)
Hypothesis NV1 : forall i s, 1 <= re s -> ~ Lz i s.
                                   (* charFamily_LFunction_ne_zero_of_one_le_re *)
Hypothesis LEVEL : forall theta, (forall i s, theta < re s -> ~ Lz i s) ->
  forall s, theta < re s -> nz s.  (* level_family: ZeroFree F = ZeroFreeAbove *)

(* windowHyp_of_rpow with C = 1, delta = la - 1. *)
Lemma windowHyp_of_rpow_rebuilt : forall theta,
  HasWindows pw la (fun x => Gm x <= pw x theta) -> WH theta (la - 1).
Proof.
  intros theta HW eta Heta Y0.
  destruct (EV (la - 1) eta ltac:(lra) Heta) as [Y1 HY1].
  destruct (HW (Qmax Y0 Y1)) as [Y [HY Hwin]].
  exists Y. split; [eapply Qle_trans; [apply Q.le_max_l|exact HY]|].
  assert (HYY1 : Y1 <= Y) by (eapply Qle_trans; [apply Q.le_max_r|exact HY]).
  destruct (HY1 Y HYY1) as [HY1' HK].
  exists (fun y => pw y theta). split.
  - intros y Hy1 Hy2. split.
    + apply pw_nonneg. lra.
    + apply Hwin; [exact Hy1|].
      assert (E : pw Y (1 + (la - 1)) == pw Y la) by (apply pw_wd; ring). lra.
  - rewrite (INT_rpow theta (la - 1) Y HY1'). exact HK.
Qed.

(* lemmaL *)
Lemma lemmaL_rebuilt : forall theta delta, 0 < theta -> theta < 1 -> 0 < delta ->
  WH theta delta -> forall i s, theta < re s -> ~ Lz i s.
Proof.
  intros theta delta H0 H1 Hd HW i s Hs Hz.
  destruct (Qlt_le_dec (re s) 1) as [Hlt|Hge].
  - assert (HZ : Zset s) by (split; [lra|exists i; left; exact Hz]).
    pose proof (LW theta delta H0 H1 Hd HW s HZ). lra.
  - exact (NV1 i s Hge Hz).
Qed.

(* formB: FormBAt la, in the shape level_of_tiedWin_rebuilt consumes. *)
Theorem formB_rebuilt : forall theta, 0 < theta -> theta < 1 ->
  HasWindows pw la (fun x => Gm x <= pw x theta) -> ZFA C re nz theta.
Proof.
  intros theta H0 H1 HW. unfold ZFA. apply LEVEL.
  apply (lemmaL_rebuilt theta (la - 1) H0 H1 ltac:(lra)).
  apply windowHyp_of_rpow_rebuilt. exact HW.
Qed.

(* The main line, composed: windows at exponent 1/2 + K eps (ch_core /
   GrowthSizeBound, as WIN) + formB  ==>  ZeroFreeAbove (1/2). *)
Hypothesis pw_mono : forall x a b, 1 <= x -> a <= b -> pw x a <= pw x b.
Variables K eps1 : Q.
Hypothesis K_nonneg : 0 <= K.
Hypothesis eps1_pos : 0 < eps1.
Hypothesis WIN : forall eps, 0 < eps -> eps < eps1 ->
  exists (Win : Q -> Prop) (x1 : Q), HasWindows pw la Win /\
    forall x, x1 <= x -> Win x -> Gm x <= pw x ((1 # 2) + K * eps).

Theorem main_line_rebuilt : ZFA C re nz (1 # 2).
Proof.
  apply (level_of_tiedWin_rebuilt C re nz Gm pw pw_mono la formB_rebuilt K eps1 K_nonneg eps1_pos WIN).
Qed.

End FormB.

Print Assumptions formB_rebuilt.
Print Assumptions main_line_rebuilt.
