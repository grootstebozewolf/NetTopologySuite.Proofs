(* AlpogeRefineBatch.v -- sixteen more main-line lemmas of the claimed RH/GRH
   Lean development (CocoSgt/riemann-hypothesis-lean @ 7cbf7a0), refined.

   "Refined" (the criterion of AlpogeSkeleton.v): the Lean proof's own
   reasoning is rebuilt in Rocq with zero axioms; its remaining inputs are
   only (a) standard Mathlib facts, named as hypotheses and tagged [Mathlib],
   or (b) other inventory lemmas.  Reals are modelled over Q with exp, log,
   rpow, norms and integrals as abstract operations satisfying exactly the
   Mathlib facts the Lean proof cites.

   Each section below names its Lean source (file : lemma).

   Evidence for docs/attacks/2026-11-21-alpoge-skeleton-two-thirds.md.
   NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import QArith Qabs Qminmax Lqa ZArith Lia List.
From NTS.Proofs.Probes Require Import LandauWindowCore.
Import ListNotations.
Local Open Scope Q_scope.

Fixpoint qsum (l : list Q) : Q := match l with [] => 0 | v :: tl => v + qsum tl end.

(* ===================================================================== *)
(* R1  CharacterBoxes/ZeroFreeAllOfTopG : hypV_of_cls                     *)
(* ===================================================================== *)
(* cls la Fm gives, beyond Fm.x1, a pair of bounds per index; HypV is the
   second one beyond some x0.  Lean: x0 = Fm.x1 + 1. *)
Theorem hypV_of_cls_r : forall (Ix : Type) (P Qb : Q -> Ix -> Prop) (x1 : Q),
  (forall x, x1 <= x -> forall i, P x i /\ Qb x i) ->
  exists x0, forall x, x0 <= x -> forall i, Qb x i.
Proof.
  intros Ix P Qb x1 H. exists (x1 + 1). intros x Hx i. apply (H x ltac:(lra) i).
Qed.

(* ===================================================================== *)
(* R2  CharacterBoxes/ZeroFreeAllOfTopG : eFamC_of_cls                    *)
(* ===================================================================== *)
(* The first bound is EAt at the family's own scale L x i and exponent
   L_eps x i; Fm.L_x and Fm.L_eps rewrite these to x and eps beyond x1.
   EFamC holds with C = 4. *)
Theorem eFamC_of_cls_r : forall (Ix : Type) (EAt : Q -> Q -> Q -> Ix -> Prop)
  (Lx Le : Q -> Ix -> Q) (Qb : Q -> Ix -> Prop) (x1 eps : Q),
  (forall x, x1 <= x -> forall i, EAt (Lx x i) (Le x i) 4 i /\ Qb x i) ->
  (forall x i, x1 <= x -> Lx x i = x) ->           (* Fm.L_x *)
  (forall x i, Le x i = eps) ->                    (* Fm.L_eps *)
  exists Cc xE, forall x, xE <= x -> forall i, EAt x eps Cc i.
Proof.
  intros Ix EAt Lx Le Qb x1 eps H HL HE. exists 4, (x1 + 1). intros x Hx i.
  destruct (H x ltac:(lra) i) as [H1 _]. rewrite (HL x i ltac:(lra)), HE in H1. exact H1.
Qed.

(* ===================================================================== *)
(* R3  PrimitiveCosets/LevelGmLeOnFamilyScales : tiedCore_of_chainTied    *)
(* ===================================================================== *)
(* ChainTied supplies an index i0, a set TT presented as an image (tT), the
   identification with the host's TT (TT_eq), and the Core data.  The only
   reasoning step is the extensional identification of the two TT's (hTT),
   after which the Core bounds are those of the host. *)
Theorem tiedCore_of_chainTied_r : forall (Ix El : Type) (TTh : Ix -> El -> Prop)
  (CoreAt : Ix -> (El -> Prop) -> Prop),
  (forall i (S S' : El -> Prop), (forall t, S t <-> S' t) -> CoreAt i S -> CoreAt i S') ->
  (exists i0 (TT : El -> Prop), (forall t, TT t <-> TTh i0 t) /\ CoreAt i0 TT) ->
  exists i0, CoreAt i0 (TTh i0).
Proof.
  intros Ix El TTh CoreAt Hext [i0 [TT [HTT HC]]]. exists i0. exact (Hext i0 TT (TTh i0) HTT HC).
Qed.

(* ===================================================================== *)
(* R4  PrimitiveCosets/SigALe : sigA_le (with chr_bounded)                *)
(* ===================================================================== *)
(* chr_bounded: a character value v at the order-2 element iod has v^2 = 1,
   hence v = 1 or v = -1 (Mathlib mul_self_eq_one_iff) -- the two
   "Bounded" cases. *)
Lemma sq_one_cases : forall v : Q, v * v == 1 -> v == 1 \/ v == -1.
Proof.
  intros v H.
  assert (H' : (v - 1) * (v + 1) == 0) by (setoid_replace ((v - 1) * (v + 1)) with (v * v - 1) by ring; lra).
  apply Qmult_integral in H'. destruct H' as [H1|H1]; [left|right]; lra.
Qed.

(* sigA_le: SigA = sum over PsiA \ kept of |GPsi| <= |PsiA| x^(1/2+eps)
   = 4 o x^(1/2+eps), each term bounded by EAtH.bdG. *)
Theorem sigA_le_r : forall (vals : list Q) (X o nPsi : Q),
  0 <= X ->
  Forall (fun v => v <= X) vals ->                       (* hE.bdG, per character *)
  inject_Z (Z.of_nat (length vals)) <= nPsi ->           (* card (PsiA \ kept) <= card PsiA *)
  nPsi == 4 * o ->                                       (* card_PsiA, hE.o_eq *)
  qsum vals <= 4 * o * X.
Proof.
  intros vals X o nPsi HX Hv Hc Ho.
  assert (H : qsum vals <= inject_Z (Z.of_nat (length vals)) * X).
  { clear Hc Ho. induction Hv as [|v l Hv _ IH]; cbn [qsum length].
    - setoid_replace (inject_Z (Z.of_nat 0) * X) with 0 by (cbn; ring). lra.
    - rewrite Nat2Z.inj_succ, <- Z.add_1_r, inject_Z_plus. change (inject_Z 1) with 1.
      assert (E : (inject_Z (Z.of_nat (length l)) + 1) * X == inject_Z (Z.of_nat (length l)) * X + X) by ring.
      cbv beta in Hv. lra. }
  assert (inject_Z (Z.of_nat (length vals)) * X <= nPsi * X) by (apply Qmult_le_compat_r; assumption).
  rewrite Ho in H0. lra.
Qed.

(* ===================================================================== *)
(* R5  PrimitiveCosets/LevelFamily : level_family                         *)
(* ===================================================================== *)
(* The CharFamily of a level: weights wt psi = 1 for the trivial character
   and Level.wt psi otherwise (all > 0); Gm F = Λ.Gm by splitting off the
   trivial character (Gchi one = Gz); ZeroFree F <-> ZeroFreeAbove is the
   subtype/membership repackaging. *)
Section LevelFamily.
Variable Ch : Type.
Variable one : Ch.
Variable eqb : Ch -> Ch -> bool.
Hypothesis eqb_spec : forall a b, eqb a b = true <-> a = b.
Variable lwt : Ch -> Q.
Hypothesis lwt_pos : forall c, c <> one -> 0 < lwt c.
Definition wt (c : Ch) : Q := if eqb c one then 1 else lwt c.

Lemma wt_pos : forall c, 0 < wt c.
Proof.
  intro c. unfold wt. destruct (eqb c one) eqn:E; [lra|].
  apply lwt_pos. intro Hc. apply eqb_spec in Hc. congruence.
Qed.

Variable Gchi : Ch -> Q.
Variable Gz : Q.
Hypothesis Gchi_one : Gchi one = Gz.                    (* gChi_eq, Gz_eq *)

Theorem level_family_sum : forall rest : list Ch, ~ In one rest ->
  qsum (map (fun c => wt c * Gchi c) (one :: rest)) == Gz + qsum (map (fun c => lwt c * Gchi c) rest).
Proof.
  intros rest Hn. simpl. unfold wt at 1.
  assert (Ho : eqb one one = true) by (apply eqb_spec; reflexivity). rewrite Ho, Gchi_one.
  assert (H : qsum (map (fun c => wt c * Gchi c) rest) == qsum (map (fun c => lwt c * Gchi c) rest)).
  { induction rest as [|a rest IH]; simpl; [reflexivity|].
    assert (Ha : eqb a one = false).
    { destruct (eqb a one) eqn:E; [|reflexivity]. apply eqb_spec in E. subst. exfalso. apply Hn. left. reflexivity. }
    unfold wt at 1. rewrite Ha. rewrite IH; [reflexivity|]. intro Hin. apply Hn. right. exact Hin. }
  rewrite H. ring.
Qed.

Variable C : Type.
Variable re : C -> Q.
Variable Lz : Ch -> C -> Prop.
Variable KEPT : Ch -> Prop.
Theorem level_family_zerofree : forall theta,
  (forall (i : {c | KEPT c}) s, theta < re s -> ~ Lz (proj1_sig i) s) <->
  (forall c, KEPT c -> forall s, theta < re s -> ~ Lz c s).
Proof.
  intro theta. split.
  - intros H c Hc s Hs. exact (H (exist _ c Hc) s Hs).
  - intros H [c Hc] s Hs. exact (H c Hc s Hs).
Qed.
End LevelFamily.

(* ===================================================================== *)
(* R6  LandauTheorems/WindowHypOfRpow : windowHyp_of_rpow_eventually      *)
(* ===================================================================== *)
(* Lean: log Y <= Y^(eta/2)/(eta/2)  [Mathlib Real.log_le_rpow_div],
   Y^eta = Y^(eta/2) Y^(eta/2)       [Mathlib Real.rpow_add],
   eventually Y^(eta/2) >= K/(eta/2) [Mathlib tendsto_rpow_atTop].
   Here L = log Y, P = Y^(eta/2). *)
Theorem windowHyp_of_rpow_eventually_r : forall K eta L P,
  0 <= K -> 0 < eta -> 0 <= P ->
  L <= P / (eta * (1 # 2)) ->
  K / (eta * (1 # 2)) <= P ->
  K * L <= P * P.
Proof.
  intros K eta L P HK He HP HL HKP.
  set (h := eta * (1 # 2)). assert (Hh : 0 < h) by (unfold h; lra).
  assert (H1 : K * L <= K * (P / h)).
  { rewrite !(Qmult_comm K). apply Qmult_le_compat_r; assumption. }
  assert (E : K * (P / h) == K / h * P) by (field; lra).
  assert (H2 : K / h * P <= P * P) by (apply Qmult_le_compat_r; assumption).
  lra.
Qed.

(* ===================================================================== *)
(* R7  LandauTheorems/WindowHypUOfWindowHyp : windowHypU_of_windowHyp     *)
(* ===================================================================== *)
(* Change of variables y = e^u.  Mathlib inputs: exp is strictly monotone,
   exp(log Y) = Y, x^a = exp(a log x) for x > 0 (rpow_def_of_pos),
   exp_add, and integral_image_eq_integral_abs_deriv_smul (CV, as an
   identity of the two abstract window integrals). *)
Section ChangeVar.
Variable E : Q -> Q.                                     (* Real.exp *)
Variable lg : Q -> Q.                                    (* Real.log *)
Variable pw : Q -> Q -> Q.                               (* rpow *)
Hypothesis E_mono : forall p q, p <= q <-> E p <= E q.  (* exp_le_exp *)
Hypothesis E_lg : forall Y, 0 < Y -> E (lg Y) == Y.     (* exp_log *)
Hypothesis pw_def : forall Y a, 0 < Y -> pw Y a == E (a * lg Y).   (* rpow_def_of_pos *)
Hypothesis E_add : forall p q, E (p + q) == E p * E q.
Hypothesis E_wd : forall p q, p == q -> E p == E q.
Variable Gm : Q -> Q.
Variable INTy : (Q -> Q) -> Q -> Q.                      (* int_[Y, Y^(1+d)] R y * y^(-theta-1) dy *)
Variable INTu : (Q -> Q) -> Q -> Q.                      (* int_[U, (1+d)U] R u * e^(-theta u) du *)
Variables theta delta : Q.
Hypothesis CV : forall R Y, 0 < Y -> INTy R Y == INTu (fun u => R (E u)) (lg Y).

(* the integrand identity |e^u| (R(e^u) (e^u)^(-theta-1)) = R(e^u) e^(-theta u) *)
Lemma integrand_identity : forall u, E u * E ((- theta - 1) * u) == E (- theta * u).
Proof. intro u. rewrite <- E_add. apply E_wd. ring. Qed.

(* window endpoints and membership *)
Lemma window_membership : forall Y u, 0 < Y ->
  (lg Y <= u /\ u <= (1 + delta) * lg Y) <-> (Y <= E u /\ E u <= pw Y (1 + delta)).
Proof.
  intros Y u HY. rewrite (pw_def Y (1 + delta) HY).
  pose proof (E_lg Y HY) as HEY.
  split; intros [H1 H2]; split.
  - pose proof (proj1 (E_mono _ _) H1). lra.
  - exact (proj1 (E_mono _ _) H2).
  - apply (proj2 (E_mono _ _)). lra.
  - exact (proj2 (E_mono _ _) H2).
Qed.

Theorem windowHypU_of_windowHyp_r : forall eta Y (R : Q -> Q), 0 < Y ->
  (forall y, Y <= y -> y <= pw Y (1 + delta) -> 0 <= R y /\ Gm y <= R y) ->
  INTy R Y <= pw Y eta ->
  (forall u, lg Y <= u -> u <= (1 + delta) * lg Y -> 0 <= R (E u) /\ Gm (E u) <= R (E u)) /\
  INTu (fun u => R (E u)) (lg Y) <= E (eta * lg Y).
Proof.
  intros eta Y R HY Hb HI. split.
  - intros u H1 H2. destruct (proj1 (window_membership Y u HY) (conj H1 H2)) as [G1 G2]. exact (Hb _ G1 G2).
  - rewrite <- (CV R Y HY), <- (pw_def Y eta HY). exact HI.
Qed.
End ChangeVar.

(* ===================================================================== *)
(* R8  LandauTheorems/CharFamilyLFunctionNeZeroOfOneLeRe                  *)
(* ===================================================================== *)
(* Case split on admissibility (N = 1 or chi <> 1): N = 1 gives zeta
   [Mathlib LFunction_modOne_eq, riemannZeta_ne_zero_of_one_le_re];
   chi <> 1 gives [Mathlib LFunction_ne_zero_of_one_le_re]. *)
Theorem charFamily_ne_zero_r : forall (Ix S : Type) (re : S -> Q) (N : Ix -> nat) (triv : Ix -> Prop)
  (Lz : Ix -> S -> Prop) (zeta0 : S -> Prop),
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
(* R9  LandauTheorems/LandauKernelMax : landau_kernel_max                 *)
(* ===================================================================== *)
(* Mathlib: (a u)^k / k! <= e^(a u)  [Real.pow_div_factorial_le_exp],
   e^(a u) e^(-a u) = 1             [Real.exp_add, exp_zero]. *)
Theorem landau_kernel_max_r : forall k a u fk Ep Em,
  0 < a -> 0 <= u -> 0 < fk -> 0 <= Em ->
  qpow (a * u) k / fk <= Ep ->            (* pow_div_factorial_le_exp *)
  Ep * Em == 1 ->                         (* exp_add *)
  qpow u k * Em / fk * qpow a k <= 1.
Proof.
  intros k a u fk Ep Em Ha Hu Hf HEm Hp HE.
  assert (E1 : qpow u k * Em / fk * qpow a k == qpow (a * u) k / fk * Em).
  { rewrite qpow_mul. field. lra. }
  rewrite E1.
  assert (qpow (a * u) k / fk * Em <= Ep * Em) by (apply Qmult_le_compat_r; assumption).
  lra.
Qed.

(* ===================================================================== *)
(* R10 LandauTheorems/kernelIntegral : kernel_integral                    *)
(* ===================================================================== *)
(* Mathlib: int_0^oo u^(s-1) e^(-a u) du = Gamma(s) / a^s
   [Real.integral_rpow_mul_exp_neg_mul_Ioi], Gamma(k+1) = k!
   [Real.Gamma_nat_eq_factorial], integral_div.  Here Ik is the integral
   of u^k e^(-a u). *)
Theorem kernel_integral_r : forall k a Ik fk,
  0 < a -> 0 < fk ->
  Ik == fk / qpow a (S k) ->              (* Gamma integral with Gamma(k+1) = k! *)
  Ik / fk == 1 / qpow a (S k).
Proof.
  intros k a Ik fk Ha Hf HI. rewrite HI.
  assert (Hp : 0 < qpow a (S k)) by (apply qpow_pos; exact Ha).
  field. split; lra.
Qed.

(* ===================================================================== *)
(* R11 LandauTheorems/landauTails : landau_tails_chernoff                 *)
(* ===================================================================== *)
(* The pointwise comparison off [U, V], then integral monotonicity and
   kernel_integral.  Mathlib: exp_le_exp, exp_add, exp_pos,
   setIntegral_mono_on, setIntegral_mono_set (integrals as finite
   nonnegative-weight sums here). *)
Lemma Qeq_dec' : forall x y : Q, {x = y} + {x <> y}.
Proof. decide equality; [apply Pos.eq_dec|apply Z.eq_dec]. Qed.

Section Chernoff.
Variable E : Q -> Q.
Hypothesis E_pos : forall t, 0 < E t.
Hypothesis E_mono : forall p q, p <= q -> E p <= E q.
Hypothesis E_add : forall p q, E (p + q) == E p * E q.
Hypothesis E_wd : forall p q, p == q -> E p == E q.

Lemma chernoff_pointwise : forall s l U V u, 0 <= l -> (u < U \/ V < u) ->
  E (- s * u) <= E (- (l * V)) * E (- (s - l) * u) + E (l * U) * E (- (s + l) * u).
Proof.
  intros s l U V u Hl Hu.
  assert (E1 : E (- (l * V)) * E (- (s - l) * u) == E (- s * u + l * (u - V))) by (rewrite <- E_add; apply E_wd; ring).
  assert (E2 : E (l * U) * E (- (s + l) * u) == E (- s * u + l * (U - u))) by (rewrite <- E_add; apply E_wd; ring).
  rewrite E1, E2.
  pose proof (E_pos (- s * u + l * (u - V))). pose proof (E_pos (- s * u + l * (U - u))).
  destruct Hu as [Hlt|Hgt].
  - assert (E (- s * u) <= E (- s * u + l * (U - u))) by (apply E_mono; nra). lra.
  - assert (E (- s * u) <= E (- s * u + l * (u - V))) by (apply E_mono; nra). lra.
Qed.

(* Integrals as sums over sample points u with weights c u = u^k/k! dx >= 0;
   off holds on the tail samples, all samples are in (0, oo). *)
Theorem landau_tails_chernoff_r : forall (pts : list Q) (c : Q -> Q) s l U V I1 I2,
  0 <= l ->
  (forall u, In u pts -> 0 <= c u) ->
  qsum (map (fun u => c u * E (- (s - l) * u)) pts) <= I1 ->     (* <= kernel_integral (s-l) *)
  qsum (map (fun u => c u * E (- (s + l) * u)) pts) <= I2 ->     (* <= kernel_integral (s+l) *)
  forall tail : list Q, (forall u, In u tail -> In u pts /\ (u < U \/ V < u)) -> NoDup tail ->
  qsum (map (fun u => c u * E (- s * u)) tail) <= E (- (l * V)) * I1 + E (l * U) * I2.
Proof.
  intros pts c s l U V I1 I2 Hl Hc H1 H2 tail Ht Hnd.
  set (g := fun u => E (- (l * V)) * (c u * E (- (s - l) * u)) + E (l * U) * (c u * E (- (s + l) * u))).
  assert (Hg0 : forall u, In u pts -> 0 <= g u).
  { intros u Hu. unfold g. pose proof (Hc u Hu).
    pose proof (E_pos (- (l * V))). pose proof (E_pos (- (s - l) * u)).
    pose proof (E_pos (l * U)). pose proof (E_pos (- (s + l) * u)).
    assert (0 <= c u * E (- (s - l) * u)) by nra. assert (0 <= c u * E (- (s + l) * u)) by nra. nra. }
  (* pointwise on the tail *)
  assert (Hpt : qsum (map (fun u => c u * E (- s * u)) tail) <= qsum (map g tail)).
  { clear Hnd. induction tail as [|a tl IH]; simpl; [lra|].
    destruct (Ht a (or_introl eq_refl)) as [Ha Hoff].
    assert (H : c a * E (- s * a) <= g a).
    { unfold g. pose proof (chernoff_pointwise s l U V a Hl Hoff) as P. pose proof (Hc a Ha).
      assert (c a * E (- s * a) <= c a * (E (- (l * V)) * E (- (s - l) * a) + E (l * U) * E (- (s + l) * a))).
      { rewrite !(Qmult_comm (c a)). apply Qmult_le_compat_r; assumption. }
      assert (Eq : c a * (E (- (l * V)) * E (- (s - l) * a) + E (l * U) * E (- (s + l) * a))
                   == E (- (l * V)) * (c a * E (- (s - l) * a)) + E (l * U) * (c a * E (- (s + l) * a))) by ring.
      lra. }
    assert (qsum (map (fun u => c u * E (- s * u)) tl) <= qsum (map g tl)).
    { apply IH. intros u Hu. apply Ht. right. exact Hu. }
    lra. }
  (* set monotonicity: tail sub-multiset of pts, g >= 0 *)
  assert (Hsub : qsum (map g tail) <= qsum (map g pts)).
  { assert (Hincl : incl tail pts) by (intros u Hu; apply (Ht u Hu)).
    clear Ht Hpt H1 H2 Hc.
    revert tail Hnd Hincl. induction pts as [|p pts IH]; intros tail Hnd Hincl.
    - destruct tail as [|a tl]; [simpl; lra|]. exfalso. apply (Hincl a). left. reflexivity.
    - simpl. pose proof (Hg0 p (or_introl eq_refl)) as Hp.
      destruct (in_dec Qeq_dec' p tail) as [Hin|Hnin].
      + destruct (in_split p tail Hin) as [l1 [l2 ->]].
        assert (Hs : qsum (map g (l1 ++ p :: l2)) == g p + qsum (map g (l1 ++ l2))).
        { clear. induction l1 as [|a l1 IH]; simpl; [ring|rewrite IH; ring]. }
        rewrite Hs.
        assert (qsum (map g (l1 ++ l2)) <= qsum (map g pts)).
        { apply IH.
          - intros u Hu. apply Hg0. right. exact Hu.
          - apply NoDup_remove_1 in Hnd. exact Hnd.
          - intros u Hu. assert (Hu' : In u (l1 ++ p :: l2)) by (apply in_app_or in Hu; apply in_or_app; destruct Hu; [left|right; right]; assumption).
            destruct (Hincl u Hu') as [Heq|Hm]; [|exact Hm].
            subst. exfalso. apply NoDup_remove_2 in Hnd. exact (Hnd Hu). }
        lra.
      + assert (qsum (map g tail) <= qsum (map g pts)).
        { apply IH.
          - intros u Hu. apply Hg0. right. exact Hu.
          - exact Hnd.
          - intros u Hu. destruct (Hincl u Hu) as [Heq|Hm]; [subst; contradiction|exact Hm]. }
        lra. }
  (* linearity and the kernel bounds *)
  assert (Hlin : qsum (map g pts) == E (- (l * V)) * qsum (map (fun u => c u * E (- (s - l) * u)) pts)
                                   + E (l * U) * qsum (map (fun u => c u * E (- (s + l) * u)) pts)).
  { unfold g. clear. induction pts as [|a pts IH]; simpl; [ring|rewrite IH; ring]. }
  pose proof (E_pos (- (l * V))). pose proof (E_pos (l * U)).
  assert (E (- (l * V)) * qsum (map (fun u => c u * E (- (s - l) * u)) pts) <= E (- (l * V)) * I1).
  { rewrite !(Qmult_comm (E (- (l * V)))). apply Qmult_le_compat_r; lra. }
  assert (E (l * U) * qsum (map (fun u => c u * E (- (s + l) * u)) pts) <= E (l * U) * I2).
  { rewrite !(Qmult_comm (E (l * U))). apply Qmult_le_compat_r; lra. }
  lra.
Qed.
End Chernoff.

(* ===================================================================== *)
(* R12 LandauTheorems/LandauCoeff : landau_coeff                          *)
(* ===================================================================== *)
(* Given iteratedDeriv_laplace (inventory lemma): the k-th derivative of
   the Laplace transform is the integral of g u (-u)^k e^(-s u); the
   sign algebra (-1)^k (-u)^k = u^k (the Lean `e`) turns the k-th
   Taylor coefficient (-1)^k Phi^(k)/k! into the integral of
   g u u^k e^(-s u)/k!.  Pointwise: *)
Theorem landau_coeff_sign_r : forall k u gu eu fk, 0 < fk ->
  qpow (-1) k * (gu * qpow (- u) k * eu) / fk == gu * qpow u k * eu / fk.
Proof.
  intros k u gu eu fk Hf.
  assert (H : qpow (-1) k * qpow (- u) k == qpow u k).
  { rewrite <- qpow_mul. apply qpow_wd. ring. }
  assert (E : qpow (-1) k * (gu * qpow (- u) k * eu) == gu * (qpow (-1) k * qpow (- u) k) * eu) by ring.
  rewrite E, H. reflexivity.
Qed.

(* ===================================================================== *)
(* R13 LandauTheorems/LandauCauchy : landau_cauchy                        *)
(* ===================================================================== *)
(* Mathlib: the k-th coefficient of the Cauchy power series is
   iteratedDeriv k Phi z / k!  [HasFPowerSeriesOnBall.factorial_smul],
   |p_k(1,..,1)| <= |p_k| prod |1| [le_opNorm],
   |p_k| <= M |r'|^-k               [norm_cauchyPowerSeries_le]. *)
Theorem landau_cauchy_r : forall k r' a pk M,
  0 < r' -> 0 <= M ->
  Qabs a <= pk * 1 ->                     (* le_opNorm, prod |1| = 1 *)
  pk <= M * / qpow (Qabs r') k ->         (* norm_cauchyPowerSeries_le *)
  Qabs a <= M / qpow r' k.
Proof.
  intros k r' a pk M Hr HM Ha Hp.
  assert (Eq : qpow (Qabs r') k == qpow r' k) by (apply qpow_wd; apply Qabs_pos; lra).
  rewrite Eq in Hp. unfold Qdiv. lra.
Qed.

(* ===================================================================== *)
(* R14 LandauTheorems/LandauPoleReLe : landau_pole_re_le_bound            *)
(* ===================================================================== *)
(* Pointwise: |g u| e^(-Re s u) <= C e^(2u) e^(-sigma u) = C e^(-(sigma-2)u)
   for u >= 0, Re s >= sigma; then Mathlib norm_integral_le_of_norm_le. *)
Theorem landau_pole_re_le_bound_r : forall (E : Q -> Q) (gu C u rs sigma : Q),
  (forall p q, p <= q -> E p <= E q) -> (forall t, 0 < E t) ->
  (forall p q, E (p + q) == E p * E q) -> (forall p q, p == q -> E p == E q) ->
  0 <= u -> sigma <= rs -> Qabs gu <= C * E (2 * u) ->
  Qabs gu * E (- rs * u) <= C * E (- (sigma - 2) * u).
Proof.
  intros E gu C u rs sigma Emono Epos Eadd Ewd Hu Hs Hg.
  assert (H2 : E (- rs * u) <= E (- sigma * u)) by (apply Emono; nra).
  assert (HC0 : 0 <= C * E (2 * u)) by (eapply Qle_trans; [apply Qabs_nonneg|exact Hg]).
  pose proof (Epos (- rs * u)) as P1. pose proof (Qabs_nonneg gu) as P0.
  assert (Qabs gu * E (- rs * u) <= C * E (2 * u) * E (- rs * u)) by (apply Qmult_le_compat_r; lra).
  assert (C * E (2 * u) * E (- rs * u) <= C * E (2 * u) * E (- sigma * u)).
  { rewrite !(Qmult_comm (C * E (2 * u))). apply Qmult_le_compat_r; lra. }
  assert (Eq : C * E (2 * u) * E (- sigma * u) == C * E (- (sigma - 2) * u)).
  { rewrite <- Qmult_assoc, <- Eadd. apply Qmult_comp; [reflexivity|]. apply Ewd. ring. }
  lra.
Qed.

(* ===================================================================== *)
(* R15 LandauTheorems/LandauPoleReLe : landau_pole_re_le                  *)
(* ===================================================================== *)
(* Near a pole rho with residue c: (s - rho) Phi s = c + (s - rho) h s.
   If Re rho > 2 then Phi is bounded (by M) near rho (R14), h is bounded
   (by Hb) near rho (continuity), so |c| <= t (M + Hb) for points at every
   small distance t > 0 -- forcing c = 0, against c <> 0.  Mathlib
   inputs (tendsto_nhds_unique, NormedField.tendsto_zero_smul...) become
   this Archimedean step. *)
Theorem pole_residue_zero_r : forall nc M Hb t0, 0 < t0 -> 0 <= M -> 0 <= Hb ->
  (forall t, 0 < t -> t < t0 -> nc <= t * (M + Hb)) -> nc <= 0.
Proof.
  intros nc M Hb t0 Ht0 HM HH Hall.
  destruct (Qlt_le_dec 0 nc) as [Hpos|Hle]; [exfalso|exact Hle].
  set (K := M + Hb + 1).
  assert (HK : 0 < K) by (unfold K; lra).
  set (t := Qmin (t0 * (1 # 2)) (nc / (2 * K))).
  assert (Ht1 : t <= t0 * (1 # 2)) by apply Q.le_min_l.
  assert (Ht2 : t <= nc / (2 * K)) by apply Q.le_min_r.
  assert (Htp : 0 < t) by (apply Q.min_glb_lt; [lra|apply Qlt_shift_div_l; lra]).
  pose proof (Hall t Htp ltac:(lra)) as H.
  assert (t * (M + Hb) <= t * K) by (rewrite !(Qmult_comm t); apply Qmult_le_compat_r; unfold K; lra).
  assert (t * K <= nc / (2 * K) * K) by (apply Qmult_le_compat_r; lra).
  assert (E : nc / (2 * K) * K == nc * (1 # 2)) by (field; lra).
  lra.
Qed.

Theorem landau_pole_re_le_r : forall (Pole : Q -> Prop) (resid : Q -> Q),
  (forall rho, Pole rho -> 0 < resid rho) ->                          (* |c| > 0 (c <> 0) *)
  (forall rho, Pole rho -> 2 < rho -> exists M Hb t0, 0 < t0 /\ 0 <= M /\ 0 <= Hb /\
     forall t, 0 < t -> t < t0 -> resid rho <= t * (M + Hb)) ->       (* R14 + residue expansion *)
  forall rho, Pole rho -> rho <= 2.
Proof.
  intros Pole resid Hc Hb rho Hr.
  destruct (Qlt_le_dec 2 rho) as [H|H]; [exfalso|exact H].
  destruct (Hb rho Hr H) as [M [Hh [t0 [Ht0 [HM [HH Hall]]]]]].
  pose proof (pole_residue_zero_r _ _ _ _ Ht0 HM HH Hall). pose proof (Hc rho Hr). lra.
Qed.

(* ===================================================================== *)
(* R16 landauWindow.lean : landau_window_re_pos                           *)
(* ===================================================================== *)
(* |w - z| < r <= Re z  ==>  0 < Re w, with |Re (w - z)| <= |w - z|
   [Mathlib Complex.abs_re_le_norm]; squared distances over Q. *)
Lemma sqnn : forall a : Q, 0 <= a * a.
Proof. intro a. nra. Qed.

Theorem landau_window_re_pos_r : forall zr zi wr wi r,
  0 <= r -> r <= zr ->
  (wr - zr) * (wr - zr) + (wi - zi) * (wi - zi) < r * r ->
  0 < wr.
Proof.
  intros zr zi wr wi r Hr Hrz Hd.
  pose proof (sqnn (wi - zi)) as Hi.
  assert (Hsq : (wr - zr) * (wr - zr) < r * r) by lra.
  destruct (Qlt_le_dec (- r) (wr - zr)) as [Hgt|Hle]; [lra|exfalso].
  set (a := - (wr - zr)).
  assert (Ha : r <= a) by (unfold a; lra).
  assert (H1 : r * r <= a * r) by (apply Qmult_le_compat_r; lra).
  assert (H2 : a * r <= a * a) by (rewrite !(Qmult_comm a); apply Qmult_le_compat_r; lra).
  assert (E : a * a == (wr - zr) * (wr - zr)) by (unfold a; ring).
  lra.
Qed.

Print Assumptions hypV_of_cls_r.
Print Assumptions eFamC_of_cls_r.
Print Assumptions tiedCore_of_chainTied_r.
Print Assumptions sigA_le_r.
Print Assumptions level_family_sum.
Print Assumptions level_family_zerofree.
Print Assumptions windowHyp_of_rpow_eventually_r.
Print Assumptions windowHypU_of_windowHyp_r.
Print Assumptions charFamily_ne_zero_r.
Print Assumptions landau_kernel_max_r.
Print Assumptions kernel_integral_r.
Print Assumptions landau_tails_chernoff_r.
Print Assumptions landau_coeff_sign_r.
Print Assumptions landau_cauchy_r.
Print Assumptions landau_pole_re_le_bound_r.
Print Assumptions landau_pole_re_le_r.
Print Assumptions landau_window_re_pos_r.
