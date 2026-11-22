(* CoreSliceQED.v -- the CORE slice of the Alpöge main line, re-derived:
   ch_core (CocoSgt/riemann-hypothesis-lean @ 7cbf7a0,
   Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean)
   and its use in core_gm (PrimitiveCosets/CoreGm.lean).

   ch_core = CharacterBalanceMoves.core  (per-coset bound + orthogonality sum_Th
             + lower bound from one_char)  ∘  proposition_size_bound.
   LeanSkeletonRebuild.v Part 7 rebuilt the averaging core and the size bound
   with the orthogonality identity as a HYPOTHESIS (ortho) and the exponent
   translation to x^(1/2 + (C+3) eps) left to the reader.  Here:

   Part A  sum_Th_instance (QED): the orthogonality identity sum_Th (l.56) and
           its lemma sum_A (l.28), computed in a concrete model: E0 × H =
           (Z/2)^4 (E0 = (Z/2)^2 as in ChCore's e1, H = (Z/2)^2), all 16
           characters (real, ±1), subgroups A0 = {0, (1,0)} and A0 = {0},
           T2 ⊆ A0, every t, and an ARBITRARY function GPsi (coefficient-wise
           proof).  The normalisation |A0| · b · delta2/2, with
           delta2 = |T2|/|H| and |PhiSet| = 2|H|, is confirmed.
           wrong_normalisation_fails (QEX control): |H|/|A0| in place of |A0|
           is refuted, so the check discriminates.
   Part B  ch_core_exponent (QED): with s = x^(1/2), e = x^eps,
           e2 = x^(eps/2), e8 = x^(eps/8), c = x^(C eps), the bound of
           growth_size_bound, e8^3 (s c e^2 e2 e8), IS x^(1/2 + (C+3) eps)
           (3/8 + 2 + 1/2 + 1/8 = 3).
   Part C  ch_core_CH (QED, conditional): the per-host statement CH that
           WinSeamRebuilt.v's core_gm_rebuilt consumes, derived from
           ch_core_rebuilt (C = eD + eL + 3, as core_gm instantiates ch_core
           with max(eD+eL,0) + 3) and Part B.
   Part D  ch_core_inputs_small_eps (QED): the inputs of ch_core_rebuilt are
           jointly satisfiable with EXPONENT-CONSISTENT atoms at a small eps:
           eps = 1/8, x = 2^128, C = 3 (s = 2^64, e = 2^16, e2 = 2^8, e8 = 4,
           c = 2^48 = e^3), host sizes n = 2^64 >= sqrt x, m = 2^48, k = 2^176.
           (LeanSkeletonRebuild.v's earlier witness had eps ~ 3.17.)

   Evidence for docs/attacks/2026-11-21-alpoge-core-slice-rederived.md.
   NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import QArith Qabs Lqa List Arith ZArith Lia.
From NTS.Proofs.Probes Require Import LeanSkeletonRebuild FormBRebuilt WinSeamRebuilt.
Import ListNotations.
Local Open Scope Q_scope.

(* ===================================================================== *)
(* Part A: orthogonality, concretely                                      *)
(* ===================================================================== *)
Fixpoint qsum (l : list Q) : Q := match l with [] => 0 | v :: tl => v + qsum tl end.

Lemma qsum_plus : forall {A} (f h : A -> Q) l, qsum (map (fun x => f x + h x) l) == qsum (map f l) + qsum (map h l).
Proof. intros A f h l. induction l as [|a l IH]; simpl; [ring|rewrite IH; ring]. Qed.
Lemma qsum_scal : forall {A} (k : Q) (f : A -> Q) l, qsum (map (fun x => k * f x) l) == k * qsum (map f l).
Proof. intros A k f l. induction l as [|a l IH]; simpl; [ring|rewrite IH; ring]. Qed.
Lemma qsum_ext : forall {A} (f h : A -> Q) l, (forall x, In x l -> f x == h x) -> qsum (map f l) == qsum (map h l).
Proof.
  intros A f h l H. induction l as [|a l IH]; simpl; [reflexivity|].
  rewrite (H a (or_introl eq_refl)), IH; [reflexivity|]. intros x Hx. apply H. right. exact Hx.
Qed.
(* sum interchange *)
Lemma qsum_swap : forall {A B} (f : A -> B -> Q) (la : list A) (lb : list B),
  qsum (map (fun x => qsum (map (fun y => f x y) lb)) la) == qsum (map (fun y => qsum (map (fun x => f x y) la)) lb).
Proof.
  intros A B f la lb. induction la as [|a la IH]; simpl.
  - induction lb as [|b lb IHb]; simpl; [reflexivity|rewrite <- IHb; ring].
  - rewrite IH. rewrite <- qsum_plus. reflexivity.
Qed.

Definition popc (n : nat) : nat :=
  (if Nat.testbit n 0 then 1 else 0) + (if Nat.testbit n 1 then 1 else 0) +
  (if Nat.testbit n 2 then 1 else 0) + (if Nat.testbit n 3 then 1 else 0).
Definition chi (c g : nat) : Q := if Nat.even (popc (Nat.land c g)) then 1 else -1.
Definition G16 := seq 0 16.
Definition e1 (t : nat) : nat := 1 + 4 * t.
Definition hadd (a b : nat) : nat := Nat.lxor a b.
Definition inPsiA (A0 : list nat) (c : nat) : bool := forallb (fun s => Qeq_bool (chi c (4 * s)) 1) A0.
Definition nq (n : nat) : Q := inject_Z (Z.of_nat n).

(* Th (ChCore.lean l.18): (1/|PhiSet|) sum_{s in T2} sum_psi psi(-e1(s+u0-t)) (b GPsi psi y),
   |PhiSet| = 2|H| = 8; in (Z/2)^4, -x = x and + is xor. *)
Definition Th (g : nat -> Q) (T2 : list nat) (b : Q) (u0 t : nat) : Q :=
  (1 # 8) * qsum (map (fun s => qsum (map (fun c => chi c (e1 (hadd (hadd s u0) t)) * (b * g c)) G16)) T2).

Definition lhs_coef (A0 T2 : list nat) (t c : nat) : Q :=
  qsum (map (fun u => (1 # 8) * qsum (map (fun s => chi c (e1 (hadd (hadd s u) t))) T2)) A0).
(* sum_Th's right side: |A0| * b * (delta2/2) * sum_{psi in PsiA} psi(e1 t) GPsi, delta2 = |T2|/|H| *)
Definition rhs_coef (A0 T2 : list nat) (t c : nat) : Q :=
  (nq (length A0) * ((nq (length T2) / 4) * (1 # 2))) * (if inPsiA A0 c then chi c (e1 t) else 0).

Lemma lhs_form : forall A0 T2 g b t,
  qsum (map (fun u => Th g T2 b u t) A0) == b * qsum (map (fun c => lhs_coef A0 T2 t c * g c) G16).
Proof.
  intros A0 T2 g b t. unfold Th, lhs_coef.
  rewrite <- qsum_scal.
  transitivity (qsum (map (fun u => qsum (map (fun c => (1 # 8) * qsum (map (fun s => chi c (e1 (hadd (hadd s u) t))) T2) * (b * g c)) G16)) A0)).
  - apply qsum_ext. intros u _.
    rewrite qsum_swap. rewrite <- qsum_scal. apply qsum_ext. intros c _.
    transitivity ((1 # 8) * (qsum (map (fun s => chi c (e1 (hadd (hadd s u) t))) T2) * (b * g c))); [|ring].
    f_equiv. induction T2 as [|a T2 IH]; simpl; [ring|rewrite IH; ring].
  - rewrite qsum_swap. apply qsum_ext. intros c _.
    transitivity (qsum (map (fun u => (1 # 8) * qsum (map (fun s => chi c (e1 (hadd (hadd s u) t))) T2)) A0) * (b * g c)).
    + induction A0 as [|a A0 IH]; simpl; [ring|rewrite IH; ring].
    + ring.
Qed.

Lemma rhs_form : forall A0 T2 g b t,
  (nq (length A0) * (b * ((nq (length T2) / 4) * (1 # 2)))) *
    qsum (map (fun c => if inPsiA A0 c then chi c (e1 t) * g c else 0) G16)
  == b * qsum (map (fun c => rhs_coef A0 T2 t c * g c) G16).
Proof.
  intros A0 T2 g b t. unfold rhs_coef.
  rewrite <- !qsum_scal. apply qsum_ext. intros c _. destruct (inPsiA A0 c); ring.
Qed.

Lemma qsum_coef_eq : forall (a a' g : nat -> Q) l,
  forallb (fun c => Qeq_bool (a c) (a' c)) l = true ->
  qsum (map (fun c => a c * g c) l) == qsum (map (fun c => a' c * g c) l).
Proof.
  intros a a' g l H. apply qsum_ext. intros c Hc.
  rewrite forallb_forall in H. specialize (H c Hc). apply Qeq_bool_iff in H. rewrite H. reflexivity.
Qed.

Definition H4 := [0;1;2;3]%nat.
(* the instances checked: A0 = {0,(1,0)} with T2 = A0 and T2 = {0}; A0 = {0} with T2 = {0} *)
Definition cases : list (list nat * list nat) := [([0;1]%nat, [0;1]%nat); ([0;1]%nat, [0%nat]); ([0%nat], [0%nat])].

Lemma coef_all : forallb (fun p => forallb (fun t => forallb (fun c =>
    Qeq_bool (lhs_coef (fst p) (snd p) t c) (rhs_coef (fst p) (snd p) t c)) G16) H4) cases = true.
Proof. vm_compute. reflexivity. Qed.

Theorem sum_Th_instance : forall A0 T2, In (A0, T2) cases -> forall t, In t H4 -> forall (g : nat -> Q) (b : Q),
  qsum (map (fun u => Th g T2 b u t) A0)
  == (nq (length A0) * (b * ((nq (length T2) / 4) * (1 # 2)))) *
     qsum (map (fun c => if inPsiA A0 c then chi c (e1 t) * g c else 0) G16).
Proof.
  intros A0 T2 Hp t Ht g b. rewrite lhs_form, rhs_form.
  pose proof coef_all as H. rewrite forallb_forall in H. specialize (H _ Hp). cbn [fst snd] in H.
  rewrite forallb_forall in H. specialize (H t Ht).
  rewrite (qsum_coef_eq _ _ g G16 H). reflexivity.
Qed.
Print Assumptions sum_Th_instance.

(* Control (QEX for a wrong normalisation): with |H|/|A0| in place of |A0| the
   identity fails at A0 = {0}, T2 = {0}, t = 0. *)
Definition rhs_coef_wrong (A0 T2 : list nat) (t c : nat) : Q :=
  ((4 / nq (length A0)) * ((nq (length T2) / 4) * (1 # 2))) * (if inPsiA A0 c then chi c (e1 t) else 0).
Lemma wrong_normalisation_fails :
  Qeq_bool (lhs_coef [0%nat] [0%nat] 0 0) (rhs_coef_wrong [0%nat] [0%nat] 0 0) = false.
Proof. vm_compute. reflexivity. Qed.
Print Assumptions wrong_normalisation_fails.

(* sum_A (l.28) for every character, s in A0 and t: the inner sum over A0
   is |A0| psi(e1 t) on PsiA A0 and 0 off it. *)
Lemma sum_A_instance : forallb (fun A0 => forallb (fun s => forallb (fun t => forallb (fun c =>
    Qeq_bool (qsum (map (fun u => chi c (e1 (hadd (hadd s u) t))) A0))
             (if inPsiA A0 c then nq (length A0) * chi c (e1 t) else 0)) G16) H4) A0)
    [[0;1]%nat; [0%nat]] = true.
Proof. vm_compute. reflexivity. Qed.
Print Assumptions sum_A_instance.

(* ===================================================================== *)
(* Part B: the exponent of ch_core                                        *)
(* ===================================================================== *)

Section Exponent.
Variable pw : Q -> Q -> Q.
Variable x : Q.
Hypothesis Hx : 1 <= x.
Hypothesis pw_add : forall a b, pw x (a + b) == pw x a * pw x b.
Hypothesis pw_wd : forall a b, a == b -> pw x a == pw x b.

Theorem ch_core_exponent : forall C eps,
  let s := pw x (1 # 2) in let e := pw x eps in let e2 := pw x (eps * (1 # 2)) in
  let e8 := pw x (eps * (1 # 8)) in let c := pw x (C * eps) in
  e8 * e8 * e8 * (s * c * (e * e) * e2 * e8) == pw x ((1 # 2) + (C + 3) * eps).
Proof.
  intros C eps s e e2 e8 c. unfold s, e, e2, e8, c.
  rewrite <- !pw_add. apply pw_wd. ring.
Qed.

(* the atom relations used by the witnesses *)
Lemma atom_relations : forall eps,
  pw x (eps * (1 # 2)) * pw x (eps * (1 # 2)) == pw x eps /\
  pw x (eps * (1 # 8)) * pw x (eps * (1 # 8)) * pw x (eps * (1 # 8)) * pw x (eps * (1 # 8))
    == pw x (eps * (1 # 2)).
Proof. intros eps. split; rewrite <- !pw_add; apply pw_wd; ring. Qed.
End Exponent.

Print Assumptions ch_core_exponent.

(* ===================================================================== *)
(* Part C: ch_core -> the per-host statement CH of core_gm                *)
(* ===================================================================== *)

(* The hypotheses of LeanSkeletonRebuild.v : ch_core_rebuilt, bundled. *)
Definition ChIn (us : list Q) (s e e2 e8 c b n nT nT2 m k aE Err Gx q1 q2 rho w Tsum : Q) : Prop :=
  (1 <= length us)%nat /\
  Forall (fun v => v <= Err + 2 * nT * m * b * w) us /\
  lsum us == inject_Z (Z.of_nat (length us)) * (m * b * (rho * (1 # 2)) * Tsum) /\
  nT * (Gx - 4 * s * e) <= Tsum /\
  1 <= s /\ 3 <= s * s /\ 1 <= e /\ 1 <= e2 /\ 1 <= e8 /\ 1 <= c /\
  26 <= e8 * e8 * e8 /\ 0 < b /\ 0 < n /\ 0 <= aE /\ aE <= 2 * (s * s) * b /\
  n <= 2 * e8 * nT /\ rho * n == nT2 /\ 1 <= e * rho /\ s <= e * m /\ m <= s * e2 /\
  s * s * m <= k /\ e * k <= n * n * s /\ q1 * k == m * m /\
  q2 * (n * n) == nT2 * k * b * (e * e) /\
  Err <= c * (nT * aE * (1 + q1) + m * (2 * n * m * b * e + q2)) /\
  w * (s * s) == 1.

Lemma ch_core_from_inputs : forall us s e e2 e8 c b n nT nT2 m k aE Err Gx q1 q2 rho w Tsum,
  ChIn us s e e2 e8 c b n nT nT2 m k aE Err Gx q1 q2 rho w Tsum ->
  Gx <= e8 * e8 * e8 * (s * c * (e * e) * e2 * e8).
Proof.
  intros us s e e2 e8 c b n nT nT2 m k aE Err Gx q1 q2 rho w Tsum
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26).
  exact (ch_core_rebuilt us s e e2 e8 c b n nT nT2 m k aE Err Gx q1 q2 rho w Tsum
           H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26).
Qed.

Section ToCH.
Variable Gm : Q -> Q.
Variable pw : Q -> Q -> Q.
Hypothesis pw_add : forall x a b, 1 <= x -> pw x (a + b) == pw x a * pw x b.
Hypothesis pw_wd : forall x a b, a == b -> pw x a == pw x b.
Variable Hst : Type.
Variable EAt : Hst -> Q -> Q -> Q -> Prop.
Variable KC : Type.
Variable CoreAt : Hst -> Q -> Q -> KC -> Q -> Q -> Prop.
Variable Sg : Hst -> Q -> Q.

(* What core_gm extracts from CoreAtH / EAtH (CoreGm.lean l.30-58: the
   destructuring of hCore, hostFactsS, charsA, ch_top per coset, gmA_eq):
   beyond a threshold depending only on the constants, each host supplies
   the inputs of ch_core with the atoms x^(1/2), x^eps, x^(eps/2), x^(eps/8),
   x^((eD+eL+3) eps), and G = Gm - Sig.  eD + eL >= 0 comes from the Core
   bounds (heD, heL). *)
Hypothesis CORE_IN : forall eD eL kc Cc eps, 0 < eps -> exists x1, forall x, x1 <= x ->
  1 <= x /\ forall h, EAt h x eps Cc -> CoreAt h eD eL kc eps x ->
    0 <= eD + eL /\
    exists us b n nT nT2 m k aE Err q1 q2 rho w Tsum,
      ChIn us (pw x (1 # 2)) (pw x eps) (pw x (eps * (1 # 2))) (pw x (eps * (1 # 8)))
           (pw x ((eD + eL + 3) * eps)) b n nT nT2 m k aE Err (Gm x - Sg h x) q1 q2 rho w Tsum.

Theorem ch_core_CH : forall eD eL kc Cc eps, 0 < eps -> exists x1, forall x, x1 <= x ->
  1 <= x /\ forall h, EAt h x eps Cc -> CoreAt h eD eL kc eps x ->
    0 <= eD + eL /\ Gm x <= pw x ((1 # 2) + (eD + eL + 3 + 3) * eps) + Sg h x.
Proof.
  intros eD eL kc Cc eps He.
  destruct (CORE_IN eD eL kc Cc eps He) as [x1 Hx1].
  exists x1. intros x Hx. destruct (Hx1 x Hx) as [Hx1' Hh]. split; [exact Hx1'|].
  intros h HE HC. destruct (Hh h HE HC) as [HE0 [us [b [n [nT [nT2 [m [k [aE [Err [q1 [q2 [rho [w [Tsum Hin]]]]]]]]]]]]]]].
  split; [exact HE0|].
  pose proof (ch_core_from_inputs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hin) as Hg.
  rewrite (ch_core_exponent pw x (fun a b0 => pw_add x a b0 Hx1') (pw_wd x) (eD + eL + 3) eps) in Hg.
  lra.
Qed.
End ToCH.

Print Assumptions ch_core_CH.

(* ===================================================================== *)
(* Part D: exponent-consistent witness at small eps                       *)
(* ===================================================================== *)

Definition p2 (j : nat) : Q := inject_Z (2 ^ Z.of_nat j).

Theorem ch_core_inputs_small_eps :
  (* eps = 1/8, x = 2^128, C = 3: s = x^(1/2), e = x^eps, e2 = x^(eps/2),
     e8 = x^(eps/8), c = x^(3 eps) *)
  let s := p2 64 in let e := p2 16 in let e2 := p2 8 in let e8 := p2 2 in let c := p2 48 in
  let b := 1 in let n := p2 64 in let nT := p2 61 in let nT2 := p2 48 in let rho := 1 / p2 16 in
  let m := p2 48 in let k := p2 176 in let aE := 0 in let Err := 0 in let Gx := 1 in
  let q1 := 1 / p2 80 in let q2 := p2 128 in let w := 1 / p2 128 in
  let Tsum := nT * (Gx - 4 * s * e) in
  let us := [m * b * (rho * (1 # 2)) * Tsum] in
  (* exponent consistency of the atoms *)
  s * s == p2 128 /\ e2 * e2 == e /\ e8 * e8 * e8 * e8 == e2 /\ c == e * e * e /\
  e * e * e * e * e * e * e * e == p2 128 /\
  ChIn us s e e2 e8 c b n nT nT2 m k aE Err Gx q1 q2 rho w Tsum.
Proof.
  cbv zeta. unfold ChIn.
  (* split conjunctions only: `split` would try eq_refl on Qeq goals *)
  repeat match goal with |- _ /\ _ => split end.
  all: try (apply Forall_cons; [|apply Forall_nil]).
  all: try (vm_compute; reflexivity).
  all: try (vm_compute; discriminate).
  all: try (cbn [length]; lia).
Qed.

Print Assumptions ch_core_inputs_small_eps.

(* ===================================================================== *)
(* Part E: the main line with CH discharged by ch_core                    *)
(* ===================================================================== *)

Section MainFromCore.
Variable C : Type.
Variable re : C -> Q.
Variable conj : C -> C.
Variable I : Type.
Variable Lz : I -> C -> Prop.
Variable nz : C -> Prop.
Variable Gm : Q -> Q.
Variable pw : Q -> Q -> Q.
Variable lg : Q -> Q.
Variable la : Q.
Hypothesis la_gt1 : 1 < la.
Hypothesis pw_nonneg : forall x a, 0 <= x -> 0 <= pw x a.
Hypothesis pw_wd : forall x a b, a == b -> pw x a == pw x b.
Variable INT : Q -> Q -> (Q -> Q) -> Q -> Q.
Hypothesis INT_rpow : forall theta delta Y, 1 <= Y ->
  INT theta delta (fun y => pw y theta) Y == delta * lg Y.
Hypothesis EV : forall K eta, 0 <= K -> 0 < eta ->
  exists Y1, forall Y, Y1 <= Y -> 1 <= Y /\ K * lg Y <= pw Y eta.
Hypothesis LW : forall theta delta, 0 < theta -> theta < 1 -> 0 < delta ->
  WH Gm pw INT theta delta -> forall rho, Zset C re conj I Lz rho -> re rho <= theta.
Hypothesis NV1 : forall i s, 1 <= re s -> ~ Lz i s.
Hypothesis LEVEL : forall theta, (forall i s, theta < re s -> ~ Lz i s) ->
  forall s, theta < re s -> nz s.
Hypothesis pw_mono : forall x a b, 1 <= x -> a <= b -> pw x a <= pw x b.
Hypothesis pw_add : forall x a b, 1 <= x -> pw x (a + b) == pw x a * pw x b.
Variable Hst : Type.
Variable EAt : Hst -> Q -> Q -> Q -> Prop.
Variable KC : Type.
Variable CoreAt : Hst -> Q -> Q -> KC -> Q -> Q -> Prop.
Variable Sg : Hst -> Q -> Q.
Variable o : Q.
Hypothesis o_nonneg : 0 <= o.
Hypothesis CORE_IN : forall eD eL kc Cc eps, 0 < eps -> exists x1, forall x, x1 <= x ->
  1 <= x /\ forall h, EAt h x eps Cc -> CoreAt h eD eL kc eps x ->
    0 <= eD + eL /\
    exists us b n nT nT2 m k aE Err q1 q2 rho w Tsum,
      ChIn us (pw x (1 # 2)) (pw x eps) (pw x (eps * (1 # 2))) (pw x (eps * (1 # 8)))
           (pw x ((eD + eL + 3) * eps)) b n nT nT2 m k aE Err (Gm x - Sg h x) q1 q2 rho w Tsum.
Hypothesis SIG : forall h x eps Cc, EAt h x eps Cc -> 1 <= x ->
  Sg h x <= 4 * o * pw x ((1 # 2) + eps).
Hypothesis EVX : forall eps, 0 < eps -> exists x3, forall x, x3 <= x -> 1 + 4 * o <= pw x eps.
Variable Fam : Q -> Type.
Variable Win : forall eps, Fam eps -> Q -> Prop.
Variable memF : forall eps, Fam eps -> Q -> Hst -> Prop.
Variable Tied : forall eps, Fam eps -> Q -> Q -> KC -> Q -> Q -> Prop.
Hypothesis ARTIN : forall eps (Fm : Fam eps) eD eL kc CL x,
  Tied eps Fm eD eL kc CL x -> exists h, memF eps Fm x h /\ CoreAt h eD eL kc eps x.
Hypothesis ATWS : exists eD eL e1, 0 < e1 /\ forall eps, 0 < eps -> eps < e1 ->
  exists Fm : Fam eps, EFamC Hst EAt Fam memF Fm /\ HasWindows pw la (Win eps Fm) /\
    TiedOn KC Fam Win Tied Fm eD eL.

Theorem main_line_from_core : ZFA C re nz (1 # 2).
Proof.
  exact (main_line_from_tiedWin C re conj I Lz nz Gm pw lg la la_gt1 pw_nonneg pw_wd INT INT_rpow EV LW NV1
           LEVEL pw_mono pw_add Hst EAt KC CoreAt Sg o o_nonneg
           (ch_core_CH Gm pw pw_add pw_wd Hst EAt KC CoreAt Sg CORE_IN)
           SIG EVX Fam Win memF Tied ARTIN ATWS).
Qed.
End MainFromCore.

Print Assumptions main_line_from_core.
