(* WinSeamRebuilt.v -- the WIN seam of the main line in the claimed RH/GRH
   Lean development (CocoSgt/riemann-hypothesis-lean @ 7cbf7a0):

     PrimitiveCosets/CoreGm.lean                     : core_gm
     PrimitiveCosets/WindowInequalityOfArtinInputs   : windowInequality_of_artinInputs
     PrimitiveCosets/LevelGmLeOnFamilyScales         : level_gm_le_on_family_scales
     CharacterBoxes/ZeroFreeAllOfTopG.lean           : zeroFreeAll_of_topG
     .../TotientGaloisClasses/TopWin.lean            : ChebyshevInequalityOnWindows,
                                                       ChebyshevInequalityAtWindowScale

   On the main line, level_of_tiedWin consumes two window hypotheses:
     OnWindows (h112) = level_gm_le_on_family_scales
                      = windowInequality_of_artinInputs (tiedCore_of_chainTied) o core_gm;
     AtWindowScale (h) is obtained from TopG (+ HostExW, eFamC_of_cls).
   LeanSkeletonRebuild.v / FormBRebuilt.v combined them into one hypothesis
   WIN.  Here WIN is DERIVED:

   - core_gm_rebuilt (QED, conditional): core_gm's exponent bookkeeping.
     ch_core (+ ch_top, gmA_eq) gives Gm <= x^(1/2 + (E+6) eps) + Sig with
     E = eD + eL >= 0; sigA_le gives Sig <= 4 o x^(1/2 + eps); eventually
     1 + 4 o <= x^eps; hence Gm <= x^(1/2 + (E+7) eps).
   - onWindows_rebuilt (QED): windowInequality_of_artinInputs; the threshold
     x1 of core_gm is chosen after the family constants (C from EFamC;
     K, cHH, eK from the Tied bounds) and before x, as in Lean.
   - win_rebuilt (QED): WIN from AtWindowScale + onWindows, with
     K = max(eD + eL + 7, 0).  Lean's exists_small_eps uses |C| + 1 and so
     accepts any sign; LeanSkeletonRebuild.v's level_of_tiedWin_rebuilt
     assumes K >= 0, so the max (plus x >= 1 and monotonicity of x^a)
     bridges the two.
   - main_line_from_tiedWin (QED, conditional): main_line_rebuilt with WIN
     discharged, i.e. ZeroFreeAbove (1/2) from AtWindowScale, the core_gm
     inputs, the Artin-input bridge, and FormBRebuilt.v's formB inputs.

   Evidence for docs/attacks/2026-11-21-alpoge-win-seam-closed.md.
   NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import QArith Qabs Qminmax Lqa.
From NTS.Proofs.Probes Require Import LeanSkeletonRebuild FormBRebuilt.
Local Open Scope Q_scope.

Section WinSeam.

(* --- shared with FormBRebuilt.v (main_line_rebuilt's inputs) --- *)
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

(* --- new: x^(a+b) = x^a x^b (Real.rpow_add) --- *)
Hypothesis pw_add : forall x a b, 1 <= x -> pw x (a + b) == pw x a * pw x b.

(* --- hosts and families (abstract) --- *)
Variable Hst : Type.                                  (* HostAx φ with its TT *)
Variable EAt : Hst -> Q -> Q -> Q -> Prop.            (* EAtH Λ H TT x eps C *)
Variable KC : Type.                                   (* the constants K, cHH, eK *)
Variable CoreAt : Hst -> Q -> Q -> KC -> Q -> Q -> Prop.  (* CoreAtH H TT eD eL (K,cHH,eK) eps x *)
Variable Sg : Hst -> Q -> Q.                          (* SigA at the host *)
Variable o : Q.                                       (* Λ.o *)
Hypothesis o_nonneg : 0 <= o.

(* ch_core + ch_top + gmA_eq, as consumed by core_gm (CoreGm.lean l.21-58):
   beyond a threshold depending only on the constants, every host with the
   E- and Core-bounds has  0 <= eD + eL  and
   Gm x <= x^(1/2 + (eD+eL+3+3) eps) + Sig. *)
Hypothesis CH : forall eD eL kc Cc eps, 0 < eps -> exists x1, forall x, x1 <= x ->
  1 <= x /\ forall h, EAt h x eps Cc -> CoreAt h eD eL kc eps x ->
    0 <= eD + eL /\ Gm x <= pw x ((1 # 2) + (eD + eL + 3 + 3) * eps) + Sg h x.
(* sigA_le *)
Hypothesis SIG : forall h x eps Cc, EAt h x eps Cc -> 1 <= x ->
  Sg h x <= 4 * o * pw x ((1 # 2) + eps).
(* tendsto_rpow_atTop: eventually 1 + 4 o <= x^eps *)
Hypothesis EVX : forall eps, 0 < eps -> exists x3, forall x, x3 <= x -> 1 + 4 * o <= pw x eps.

Theorem core_gm_rebuilt : forall eD eL kc Cc eps, 0 < eps -> exists x1, forall x, x1 <= x ->
  forall h, EAt h x eps Cc -> CoreAt h eD eL kc eps x ->
    Gm x <= pw x ((1 # 2) + (eD + eL + 7) * eps).
Proof.
  intros eD eL kc Cc eps He.
  destruct (CH eD eL kc Cc eps He) as [x1 Hx1].
  destruct (EVX eps He) as [x3 Hx3].
  exists (Qmax x1 x3). intros x Hx h HE Hc.
  assert (H1 : x1 <= x) by (eapply Qle_trans; [apply Q.le_max_l|exact Hx]).
  assert (H3 : x3 <= x) by (eapply Qle_trans; [apply Q.le_max_r|exact Hx]).
  destruct (Hx1 x H1) as [Hx1' Hb]. destruct (Hb h HE Hc) as [HE0 HG].
  pose proof (SIG h x eps Cc HE Hx1') as HS.
  pose proof (Hx3 x H3) as HX.
  set (P := pw x ((1 # 2) + (eD + eL + 3 + 3) * eps)) in *.
  assert (HP0 : 0 <= P) by (apply pw_nonneg; lra).
  assert (HPe : pw x ((1 # 2) + eps) <= P).
  { apply pw_mono; [exact Hx1'|]. nra. }
  assert (Ht : pw x ((1 # 2) + (eD + eL + 7) * eps) == pw x eps * P).
  { unfold P. rewrite <- pw_add by exact Hx1'. apply pw_wd. ring. }
  rewrite Ht.
  assert (H4 : 4 * o * pw x ((1 # 2) + eps) <= 4 * o * P).
  { rewrite !(Qmult_comm (4 * o)). apply Qmult_le_compat_r; [exact HPe|lra]. }
  assert (H5 : (1 + 4 * o) * P <= pw x eps * P) by (apply Qmult_le_compat_r; assumption).
  assert (E5 : (1 + 4 * o) * P == P + 4 * o * P) by ring.
  lra.
Qed.


(* --- families and the Artin-input bridge --- *)
Variable Fam : Q -> Type.
Variable Win : forall eps, Fam eps -> Q -> Prop.      (* (core Fm).Win *)
Variable memF : forall eps, Fam eps -> Q -> Hst -> Prop.  (* host (core Fm).D x i *)
Variable Tied : forall eps, Fam eps -> Q -> Q -> KC -> Q -> Q -> Prop.  (* ChainTied Fm eD eL K cHH eK CL x *)

Definition EFamC {eps} (Fm : Fam eps) : Prop :=
  exists Cc xE, forall x, xE <= x -> forall h, memF eps Fm x h -> EAt h x eps Cc.
Definition TiedOn {eps} (Fm : Fam eps) (eD eL : Q) : Prop :=   (* ChebyshevInequalityOnFamilyWindows *)
  exists kc CL x0, forall x, x0 <= x -> Win eps Fm x -> Tied eps Fm eD eL kc CL x.

(* tiedCore_of_chainTied *)
Hypothesis ARTIN : forall eps (Fm : Fam eps) eD eL kc CL x,
  Tied eps Fm eD eL kc CL x -> exists h, memF eps Fm x h /\ CoreAt h eD eL kc eps x.

(* windowInequality_of_artinInputs = level_gm_le_on_family_scales *)
Theorem onWindows_rebuilt : forall eD eL eps, 0 < eps -> forall Fm : Fam eps,
  EFamC Fm -> TiedOn Fm eD eL ->
  exists x1, forall x, x1 <= x -> Win eps Fm x -> Gm x <= pw x ((1 # 2) + (eD + eL + 7) * eps).
Proof.
  intros eD eL eps He Fm [Cc [xE HE]] [kc [CL [x0 HT]]].
  destruct (core_gm_rebuilt eD eL kc Cc eps He) as [x1 Hx1].
  exists (Qmax x1 (Qmax x0 xE)). intros x Hx Hw.
  assert (H1 : x1 <= x) by (eapply Qle_trans; [apply Q.le_max_l|exact Hx]).
  assert (H0 : x0 <= x).
  { eapply Qle_trans; [|exact Hx]. eapply Qle_trans; [apply Q.le_max_l|apply Q.le_max_r]. }
  assert (HxE : xE <= x).
  { eapply Qle_trans; [|exact Hx]. eapply Qle_trans; [apply Q.le_max_r|apply Q.le_max_r]. }
  destruct (ARTIN eps Fm eD eL kc CL x (HT x H0 Hw)) as [h [Hm Hc]].
  exact (Hx1 x H1 h (HE x HxE h Hm) Hc).
Qed.

(* ChebyshevInequalityAtWindowScale la Λ, as supplied by TopG on the main line. *)
Hypothesis ATWS : exists eD eL e1, 0 < e1 /\ forall eps, 0 < eps -> eps < e1 ->
  exists Fm : Fam eps, EFamC Fm /\ HasWindows pw la (Win eps Fm) /\ TiedOn Fm eD eL.

Theorem win_rebuilt : exists K eps1, 0 <= K /\ 0 < eps1 /\
  forall eps, 0 < eps -> eps < eps1 ->
  exists (W : Q -> Prop) (x1 : Q), HasWindows pw la W /\
    forall x, x1 <= x -> W x -> Gm x <= pw x ((1 # 2) + K * eps).
Proof.
  destruct ATWS as [eD [eL [e1 [He1 H]]]].
  exists (Qmax (eD + eL + 7) 0), e1. split; [apply Q.le_max_r|]. split; [exact He1|].
  intros eps He Hlt.
  destruct (H eps He Hlt) as [Fm [HE [HW HT]]].
  destruct (onWindows_rebuilt eD eL eps He Fm HE HT) as [x1 Hx1].
  exists (Win eps Fm), (Qmax x1 1). split; [exact HW|].
  intros x Hx Hw.
  assert (H1 : x1 <= x) by (eapply Qle_trans; [apply Q.le_max_l|exact Hx]).
  assert (H2 : 1 <= x) by (eapply Qle_trans; [apply Q.le_max_r|exact Hx]).
  eapply Qle_trans; [exact (Hx1 x H1 Hw)|].
  apply pw_mono; [exact H2|].
  pose proof (Q.le_max_l (eD + eL + 7) 0).
  assert ((eD + eL + 7) * eps <= Qmax (eD + eL + 7) 0 * eps) by (apply Qmult_le_compat_r; lra).
  lra.
Qed.


(* The main line with WIN discharged. *)
Theorem main_line_from_tiedWin : ZFA C re nz (1 # 2).
Proof.
  destruct win_rebuilt as [K [eps1 [HK [He1 HWIN]]]].
  exact (main_line_rebuilt C re conj I Lz nz Gm pw lg la la_gt1 pw_nonneg pw_wd INT INT_rpow EV LW NV1 LEVEL
           pw_mono K eps1 HK He1 HWIN).
Qed.

End WinSeam.

Print Assumptions core_gm_rebuilt.
Print Assumptions onWindows_rebuilt.
Print Assumptions win_rebuilt.

Print Assumptions main_line_from_tiedWin.
