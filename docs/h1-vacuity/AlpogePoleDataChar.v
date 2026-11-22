(* AlpogePoleDataChar.v -- poleData_char of the claimed RH/GRH Lean
   development (CocoSgt/riemann-hypothesis-lean @ 7cbf7a0,
   LandauTheorems/poleData.lean l.137), REFINED.

   AlpogeSixthLandau.v refines poleData (l.248) with the per-character
   statement poleData_char taken as an [inventory] hypothesis (CHAR1 /
   CHAR2, in the CharPole shape).  This file rebuilds poleData_char's own
   proof:

     poleData_abstract (l.22)   Phi s = -(dslope N 1 s) / s with
                                N s = g'(s)/g(s) - s c + k (1 - s), c = g'(1)/g(1):
                                the formula off s = 1, analyticity off the
                                zeros of g, the simple poles with residue
                                m * (-1/(rho (rho - 1))) at a zero of order m
                                (from logDeriv_local), isolated zeros.
     poleData_char, chi <> 1    g = L(chi, .), k = 0, with
                                mellin_Gchi_of_ne_one + poleData_change.
     poleData_char, chi = 1     g = (s - 1) zeta(s) patched to 1 at s = 1,
                                k = 1, with mellin_Gchi_modOne +
                                poleData_change; g /= 0 <-> zeta /= 0 proved.

   The conclusions are exactly AlpogeSixthLandau's CharPole, so they
   discharge poleData_r's CHAR1 / CHAR2 hypotheses.

   Carrier: C = R x R (AlpogeDeepStatements' Cc; Cc_field of
   AlpogeSixthBatch gives `field`).  CAnalyticAt and EvPunct are the
   concrete definitions of AlpogeDeepStatements.  The analytic-function
   facts the Lean proof cites (closure of AnalyticAt under + - * / and
   congruence, dslope, Differentiable.analyticAt, the identity theorem,
   isolated zeros), the zeta / L-function facts and the two Mellin
   identities are named hypotheses, tagged [Mathlib] or [inventory].
   Within docs/axiom-allowlist.txt.

   Evidence for docs/attacks/2026-11-22-alpoge-poledata-char.md.
   NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human-reviewed by Jeroen Bloemscheer (2026-11-22).
     Assisted-by: Claude
*)
From Stdlib Require Import Reals Lra Psatz Ring Field.
From NTS.Proofs.Probes Require Import AlpogeRealsQED2 AlpogeDeepStatements AlpogeSixthBatch AlpogeSixthLandau.
Local Open Scope R_scope.

Add Field Ccf : Cc_field.

(* ===================================================================== *)
(* C = R x R: small facts                                                 *)
(* ===================================================================== *)
Lemma cmul_c0_l : forall a, cmul c0 a = c0.
Proof. intros [a b]. apply Cc_ext; unfold cmul, c0, cofR; simpl; ring. Qed.
Lemma cadd_c0_l : forall a, cadd c0 a = a.
Proof. intros [a b]. apply Cc_ext; unfold cadd, c0, cofR; simpl; ring. Qed.
Lemma cadd_c0_r : forall a, cadd a c0 = a.
Proof. intros [a b]. apply Cc_ext; unfold cadd, c0, cofR; simpl; ring. Qed.
Lemma cdiv_c0_l : forall a, cdiv c0 a = c0.
Proof. intros [a b]. apply Cc_ext; unfold cdiv, cmul, cinv, c0, cofR; simpl; ring. Qed.
Lemma cdiv_by_c0 : forall a, cdiv a c0 = c0.
Proof. intros [a b]. apply Cc_ext; unfold cdiv, cmul, cinv, c0, cofR; simpl; unfold Rdiv; ring. Qed.
Lemma cofR_m1 : cofR (-1) = copp c1.
Proof. apply Cc_ext; unfold copp, c1, cofR; simpl; ring. Qed.

Lemma csub_nz : forall a b, a <> b -> csub a b <> c0.
Proof.
  intros [ar ai] [br bi] H E. apply H. unfold csub, c0, cofR in E. injection E. intros E2 E1.
  apply Cc_ext; simpl; lra.
Qed.

Lemma cmul_nz : forall a b, a <> c0 -> b <> c0 -> cmul a b <> c0.
Proof.
  intros a b Ha Hb E. apply Ha.
  assert (H : a = cdiv (cmul a b) b) by (field; exact Hb).
  rewrite H, E. field. exact Hb.
Qed.

Lemma cmul_c0_r : forall a, cmul a c0 = c0.
Proof. intros [a b]. apply Cc_ext; unfold cmul, c0, cofR; simpl; ring. Qed.

Lemma c1_nz : c1 <> c0.
Proof. unfold c1, c0, cofR. intro E. injection E. lra. Qed.

(* "eventually in a (full) neighbourhood" *)
Definition EvNear (z : Cc) (P : Cc -> Prop) : Prop :=
  exists d, 0 < d /\ forall w, cnorm (csub w z) < d -> P w.

Lemma avoid_near : forall c rho, c <> rho -> EvNear rho (fun s => s <> c).
Proof.
  intros c rho H. exists (cnorm (csub c rho)). split; [apply cnorm_pos_ne; exact H|].
  intros w Hw E. subst w. lra.
Qed.

Lemma near_punct : forall z P, EvNear z P -> EvPunct z P.
Proof. intros z P [d [Hd H]]. exists d. split; [exact Hd|]. intros s _ Hs. apply H; exact Hs. Qed.

Lemma punct_ne : forall z, EvPunct z (fun s => s <> z).
Proof.
  intro z. exists 1. split; [lra|]. intros s Hs _ E. subst s. rewrite cnorm_sub_self in Hs. lra.
Qed.

Lemma re_gt_ne : forall s c, cre c < cre s -> s <> c.
Proof. intros s c H E. subst. lra. Qed.

(* ===================================================================== *)
(* The analytic vocabulary the Lean proof cites, as [Mathlib] facts       *)
(* ===================================================================== *)
Section PoleDataChar.
Hypothesis AN_const : forall (c z : Cc), CAnalyticAt (fun _ => c) z.              (* [Mathlib] analyticAt_const *)
Hypothesis AN_id : forall z, CAnalyticAt (fun s => s) z.                          (* [Mathlib] analyticAt_id *)
Hypothesis AN_add : forall f h z, CAnalyticAt f z -> CAnalyticAt h z ->
  CAnalyticAt (fun s => cadd (f s) (h s)) z.                                       (* [Mathlib] AnalyticAt.add *)
Hypothesis AN_sub : forall f h z, CAnalyticAt f z -> CAnalyticAt h z ->
  CAnalyticAt (fun s => csub (f s) (h s)) z.                                       (* [Mathlib] AnalyticAt.sub *)
Hypothesis AN_mul : forall f h z, CAnalyticAt f z -> CAnalyticAt h z ->
  CAnalyticAt (fun s => cmul (f s) (h s)) z.                                       (* [Mathlib] AnalyticAt.mul *)
Hypothesis AN_neg : forall f z, CAnalyticAt f z -> CAnalyticAt (fun s => copp (f s)) z.   (* [Mathlib] AnalyticAt.neg *)
Hypothesis AN_div : forall f h z, CAnalyticAt f z -> CAnalyticAt h z -> h z <> c0 ->
  CAnalyticAt (fun s => cdiv (f s) (h s)) z.                                       (* [Mathlib] AnalyticAt.div *)
Hypothesis AN_congr : forall f h z, EvNear z (fun s => f s = h s) -> CAnalyticAt h z ->
  CAnalyticAt f z.                                                                 (* [Mathlib] AnalyticAt.congr *)
Variable dslope : (Cc -> Cc) -> Cc -> Cc -> Cc.                                    (* Mathlib dslope *)
Hypothesis dslope_ne : forall f a s, s <> a ->
  dslope f a s = cdiv (csub (f s) (f a)) (csub s a).                               (* [Mathlib] dslope_of_ne, slope_def_field *)
Hypothesis DSL_AN : forall f a, CAnalyticAt f a -> CAnalyticAt (dslope f a) a.    (* [Mathlib] HasFPowerSeriesAt.has_fpower_series_dslope_fslope (poleData_dslope) *)

(* ===================================================================== *)
(* poleData_abstract (poleData.lean l.22)                                 *)
(* ===================================================================== *)
Section Abstract.
Variables (g g' : Cc -> Cc) (k : Cc).                                              (* g, deriv g, k *)
Hypothesis GAN : forall z, CAnalyticAt g z.                                        (* [Mathlib] Differentiable.analyticAt (hg) *)
Hypothesis G'AN : forall z, CAnalyticAt g' z.                                      (* [Mathlib] AnalyticAt.deriv *)
Hypothesis g1 : g c1 <> c0.                                                        (* h1 *)
Hypothesis IDENT : forall z, EvNear z (fun w => g w = c0) -> forall w, g w = c0.  (* [Mathlib] AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero *)
Hypothesis ISO : forall z, EvNear z (fun w => g w = c0) \/ EvPunct z (fun w => g w <> c0).
                                                                                   (* [Mathlib] AnalyticAt.eventually_eq_zero_or_eventually_ne_zero *)
Hypothesis LOGD : forall rho, ~ EvNear rho (fun w => g w = c0) ->
  exists m : nat, (m = 0%nat <-> g rho <> c0) /\ exists h0, CAnalyticAt h0 rho /\
    EvPunct rho (fun s => cdiv (g' s) (g s) = cadd (cdiv (cofR (INR m)) (csub s rho)) (h0 s)).
                                                                                   (* [inventory] logDeriv_local *)

Definition cc : Cc := cdiv (g' c1) (g c1).
Definition NN (s : Cc) : Cc := cadd (csub (cdiv (g' s) (g s)) (cmul s cc)) (cmul k (csub c1 s)).
Definition PhiA (s : Cc) : Cc := cdiv (copp (dslope NN c1 s)) s.
Definition formula (s : Cc) : Cc :=
  cdiv (copp (cadd (csub (cdiv (g' s) (g s)) (cmul s (cdiv (g' c1) (g c1)))) (cmul k (csub c1 s))))
       (cmul s (csub s c1)).
(* the pole part of CharPole, verbatim *)
Definition PoleT (m : nat) (rho s : Cc) : Cc :=
  cdiv (cmul (cofR (INR m)) (cdiv (cofR (-1)) (cmul rho (csub rho (cofR 1))))) (csub s rho).

(* hnz: g is not eventually zero anywhere (identity theorem + g 1 /= 0) *)
Lemma hnz : forall z, ~ EvNear z (fun w => g w = c0).
Proof. intros z H. apply g1. exact (IDENT z H c1). Qed.

Lemma NN1 : NN c1 = c0.
Proof. unfold NN, cc. field. exact g1. Qed.

(* hPhi *)
Lemma hPhi : forall s, s <> c1 -> PhiA s = formula s.
Proof.
  intros s Hs. unfold PhiA. rewrite dslope_ne by exact Hs. rewrite NN1.
  destruct (Cc_eq_dec s c0) as [E|Hs0].
  - subst s. unfold formula. rewrite !cmul_c0_l, !cdiv_by_c0. reflexivity.
  - unfold formula, NN, cc. set (r := cdiv (g' s) (g s)). set (r1 := cdiv (g' c1) (g c1)).
    pose proof (csub_nz s c1 Hs). field. repeat split; auto.
Qed.

(* N is analytic off the zeros of g *)
Lemma NN_an : forall z, g z <> c0 -> CAnalyticAt NN z.
Proof.
  intros z Hz. unfold NN.
  apply (AN_add (fun s => csub (cdiv (g' s) (g s)) (cmul s cc)) (fun s => cmul k (csub c1 s))).
  - apply (AN_sub (fun s => cdiv (g' s) (g s)) (fun s => cmul s cc)).
    + apply (AN_div g' g); [apply G'AN|apply GAN|exact Hz].
    + apply (AN_mul (fun s => s) (fun _ => cc)); [apply AN_id|apply AN_const].
  - apply (AN_mul (fun _ => k) (fun s => csub c1 s)); [apply AN_const|].
    apply (AN_sub (fun _ => c1) (fun s => s)); [apply AN_const|apply AN_id].
Qed.

(* hPan *)
Lemma hPan : forall rho, rho <> c0 -> g rho <> c0 -> CAnalyticAt PhiA rho.
Proof.
  intros rho Hr Hg. unfold PhiA.
  assert (Hd : CAnalyticAt (dslope NN c1) rho).
  { destruct (Cc_eq_dec rho c1) as [E|Hne].
    - subst rho. apply DSL_AN. apply NN_an. exact g1.
    - apply (AN_congr _ (fun s => cdiv (csub (NN s) (NN c1)) (csub s c1))).
      + destruct (avoid_near c1 rho (fun E => Hne (eq_sym E))) as [d [Hd0 Hd1]].
        exists d. split; [exact Hd0|]. intros w Hw. apply dslope_ne. exact (Hd1 w Hw).
      + apply (AN_div (fun s => csub (NN s) (NN c1)) (fun s => csub s c1)).
        * apply (AN_sub NN (fun _ => NN c1)); [apply NN_an; exact Hg|apply AN_const].
        * apply (AN_sub (fun s => s) (fun _ => c1)); [apply AN_id|apply AN_const].
        * apply csub_nz. exact Hne. }
  apply (AN_div (fun s => copp (dslope NN c1 s)) (fun s => s)).
  - apply (AN_neg (dslope NN c1)). exact Hd.
  - apply AN_id.
  - exact Hr.
Qed.

Theorem poleData_abstract_r : exists Phi : Cc -> Cc,
  (forall s, s <> c1 -> Phi s = formula s) /\
  (forall rho, rho <> c0 -> g rho <> c0 -> CAnalyticAt Phi rho) /\
  (forall rho, rho <> c0 -> exists m : nat, (m = 0%nat <-> g rho <> c0) /\
     exists h, CAnalyticAt h rho /\ EvPunct rho (fun s => Phi s = cadd (PoleT m rho s) (h s))) /\
  (forall z, EvPunct z (fun w => g w <> c0)).
Proof.
  exists PhiA. split; [exact hPhi|]. split; [exact hPan|]. split.
  - intros rho Hr.
    destruct (Cc_eq_dec (g rho) c0) as [Hg0|Hg0].
    + (* a zero of g: logDeriv_local *)
      assert (Hr1 : rho <> c1) by (intro E; subst rho; exact (g1 Hg0)).
      destruct (LOGD rho (hnz rho)) as [m [Hm [h0 [Hh0 Hev]]]].
      exists m. split; [exact Hm|].
      set (q := fun s => cdiv c1 (cmul s (csub s c1))).
      assert (Hrr : cmul rho (csub rho c1) <> c0) by (apply cmul_nz; [exact Hr|apply csub_nz; exact Hr1]).
      assert (Hq : CAnalyticAt q rho).
      { unfold q. apply (AN_div (fun _ => c1) (fun s => cmul s (csub s c1))); [apply AN_const| |exact Hrr].
        apply (AN_mul (fun s => s) (fun s => csub s c1)); [apply AN_id|].
        apply (AN_sub (fun s => s) (fun _ => c1)); [apply AN_id|apply AN_const]. }
      exists (fun s => csub (copp (cmul (cofR (INR m)) (dslope q rho s)))
                            (cmul (cadd (csub (h0 s) (cmul s cc)) (cmul k (csub c1 s))) (q s))).
      split.
      * apply (AN_sub (fun s => copp (cmul (cofR (INR m)) (dslope q rho s)))
                      (fun s => cmul (cadd (csub (h0 s) (cmul s cc)) (cmul k (csub c1 s))) (q s))).
        -- apply (AN_neg (fun s => cmul (cofR (INR m)) (dslope q rho s))).
           apply (AN_mul (fun _ => cofR (INR m)) (dslope q rho)); [apply AN_const|apply DSL_AN; exact Hq].
        -- apply (AN_mul (fun s => cadd (csub (h0 s) (cmul s cc)) (cmul k (csub c1 s))) q); [|exact Hq].
           apply (AN_add (fun s => csub (h0 s) (cmul s cc)) (fun s => cmul k (csub c1 s))).
           ++ apply (AN_sub h0 (fun s => cmul s cc)); [exact Hh0|].
              apply (AN_mul (fun s => s) (fun _ => cc)); [apply AN_id|apply AN_const].
           ++ apply (AN_mul (fun _ => k) (fun s => csub c1 s)); [apply AN_const|].
              apply (AN_sub (fun _ => c1) (fun s => s)); [apply AN_const|apply AN_id].
      * pose proof (EvPunct_and _ _ _ Hev (near_punct _ _ (avoid_near c0 rho (fun E => Hr (eq_sym E))))) as H1.
        pose proof (EvPunct_and _ _ _ H1 (near_punct _ _ (avoid_near c1 rho (fun E => Hr1 (eq_sym E))))) as H2.
        pose proof (EvPunct_and _ _ _ H2 (punct_ne rho)) as H3.
        destruct H3 as [d [Hd H3]]. exists d. split; [exact Hd|]. intros s Hs1 Hs2.
        destruct (H3 s Hs1 Hs2) as [[[He Hs0] Hs1'] Hsr].
        rewrite (hPhi s Hs1'). unfold formula. rewrite He.
        rewrite (dslope_ne q rho s Hsr). unfold PoleT, q, cc. rewrite cofR_m1. change (cofR 1) with c1.
        set (r1 := cdiv (g' c1) (g c1)).
        pose proof (csub_nz s c1 Hs1'). pose proof (csub_nz s rho Hsr). pose proof (csub_nz rho c1 Hr1).
        field. repeat split; auto.
    + (* not a zero: m = 0, h = Phi *)
      exists 0%nat. split; [split; [intros _; exact Hg0|reflexivity]|].
      exists PhiA. split; [exact (hPan rho Hr Hg0)|].
      exists 1. split; [lra|]. intros s _ _. unfold PoleT. change (cofR (INR 0)) with c0.
      rewrite cmul_c0_l, cdiv_c0_l, cadd_c0_l. reflexivity.
  - intro z. destruct (ISO z) as [H|H]; [exfalso; exact (hnz z H)|exact H].
Qed.
End Abstract.

(* ===================================================================== *)
(* poleData_char, chi <> 1  (l.226): g = L(chi, .), k = 0                 *)
(* ===================================================================== *)
Section NonTrivial.
Variables (L L' : Cc -> Cc) (G : R -> Cc).          (* LFunction chi, its deriv, Gchi chi *)
Hypothesis LAN : forall z, CAnalyticAt L z.          (* [Mathlib] DirichletCharacter.differentiable_LFunction (chi <> 1), analyticAt *)
Hypothesis L'AN : forall z, CAnalyticAt L' z.        (* [Mathlib] AnalyticAt.deriv *)
Hypothesis L1 : L c1 <> c0.                          (* [Mathlib] DirichletCharacter.LFunction_apply_one_ne_zero *)
Hypothesis LIDENT : forall z, EvNear z (fun w => L w = c0) -> forall w, L w = c0.     (* [Mathlib] identity theorem *)
Hypothesis LISO : forall z, EvNear z (fun w => L w = c0) \/ EvPunct z (fun w => L w <> c0).   (* [Mathlib] isolated zeros *)
Hypothesis LLOGD : forall rho, ~ EvNear rho (fun w => L w = c0) ->
  exists m : nat, (m = 0%nat <-> L rho <> c0) /\ exists h0, CAnalyticAt h0 rho /\
    EvPunct rho (fun s => cdiv (L' s) (L s) = cadd (cdiv (cofR (INR m)) (csub s rho)) (h0 s)).   (* [inventory] logDeriv_local *)
(* [inventory] mellin_Gchi_of_ne_one composed with poleData_change *)
Hypothesis MELL : forall s, 1 < cre s ->
  LaplaceAtC (fun u => G (exp u)) s
    (cdiv (copp (csub (cdiv (L' s) (L s)) (cmul s (cdiv (L' c1) (L c1))))) (cmul s (csub s c1))).

Theorem poleData_char_nontriv_r : exists Phi, CharPole G (fun w => L w = c0) Phi.
Proof.
  destruct (poleData_abstract_r L L' c0 LAN L'AN L1 LIDENT LISO LLOGD) as [Phi [H1 [H2 [H3 H4]]]].
  exists Phi. split; [|split; [|split]].
  - intros s Hs. rewrite (H1 s (re_gt_ne s c1 ltac:(unfold c1, cofR; simpl; lra))).
    unfold formula. rewrite cmul_c0_l, cadd_c0_r. apply MELL. lra.
  - intros rho Hr HL. exact (H2 rho Hr HL).
  - intros rho Hr. destruct (H3 rho Hr) as [m [Hm [h [Hh Hev]]]].
    exists m. split; [exact Hm|]. exists h. split; [exact Hh|]. exact Hev.
  - exact H4.
Qed.
End NonTrivial.

(* ===================================================================== *)
(* poleData_char, chi = 1  (l.140): g = (s - 1) zeta(s) patched to 1 at   *)
(* s = 1, k = 1                                                           *)
(* ===================================================================== *)
Section Trivial.
Variables (Z Z' : Cc -> Cc) (gam : R) (G : R -> Cc).   (* riemannZeta, its deriv, eulerMascheroniConstant, Gchi 1 *)
(* g := Function.update (fun s => (s - 1) * riemannZeta s) 1 1 *)
Definition gT (w : Cc) : Cc := if Cc_eq_dec w c1 then c1 else cmul (csub w c1) (Z w).
Variable gT' : Cc -> Cc.                               (* deriv g *)
Hypothesis GTAN : forall z, CAnalyticAt gT z.
  (* [Mathlib] differentiableAt_riemannZeta, riemannZeta_residue_one,
     differentiableOn_compl_singleton_and_continuousAt_iff (hg), Differentiable.analyticAt *)
Hypothesis GT'AN : forall z, CAnalyticAt gT' z.        (* [Mathlib] AnalyticAt.deriv *)
Hypothesis GT'_ne1 : forall s, s <> c1 -> gT' s = cadd (Z s) (cmul (csub s c1) (Z' s)).
  (* hderiv: [Mathlib] HasDerivAt.mul, EventuallyEq.deriv_eq *)
Hypothesis GT'_1 : gT' c1 = cofR gam.                  (* hderiv1: [Mathlib] tendsto_riemannZeta_sub_one_div *)
Hypothesis Z1 : Z c1 <> c0.                            (* [Mathlib] riemannZeta_one_ne_zero *)
Hypothesis ZNZ : forall s, 1 <= cre s -> s <> c1 -> Z s <> c0.   (* [Mathlib] riemannZeta_ne_zero_of_one_le_re *)
Hypothesis GIDENT : forall z, EvNear z (fun w => gT w = c0) -> forall w, gT w = c0.   (* [Mathlib] identity theorem *)
Hypothesis GISO : forall z, EvNear z (fun w => gT w = c0) \/ EvPunct z (fun w => gT w <> c0).   (* [Mathlib] isolated zeros *)
Hypothesis GLOGD : forall rho, ~ EvNear rho (fun w => gT w = c0) ->
  exists m : nat, (m = 0%nat <-> gT rho <> c0) /\ exists h0, CAnalyticAt h0 rho /\
    EvPunct rho (fun s => cdiv (gT' s) (gT s) = cadd (cdiv (cofR (INR m)) (csub s rho)) (h0 s)).   (* [inventory] logDeriv_local *)
(* [inventory] mellin_Gchi_modOne composed with poleData_change *)
Hypothesis MELL1 : forall s, 1 < cre s ->
  LaplaceAtC (fun u => G (exp u)) s
    (cdiv (copp (csub (cadd (cadd (cdiv (Z' s) (Z s)) (cdiv c1 (csub s c1))) c1) (cmul (cadd c1 (cofR gam)) s)))
          (cmul s (csub s c1))).

Lemma gT_1 : gT c1 = c1.
Proof. unfold gT. destruct (Cc_eq_dec c1 c1) as [_|N]; [reflexivity|congruence]. Qed.
Lemma gT_ne1 : forall w, w <> c1 -> gT w = cmul (csub w c1) (Z w).
Proof. intros w Hw. unfold gT. destruct (Cc_eq_dec w c1) as [E|_]; [contradiction|reflexivity]. Qed.

(* hgz *)
Lemma hgz : forall w, gT w <> c0 <-> Z w <> c0.
Proof.
  intro w. destruct (Cc_eq_dec w c1) as [E|Hw].
  - subst w. rewrite gT_1. split; intros _; [exact Z1|exact c1_nz].
  - rewrite (gT_ne1 w Hw). split.
    + intros H HZ. apply H. rewrite HZ. apply cmul_c0_r.
    + intro HZ. apply cmul_nz; [apply csub_nz; exact Hw|exact HZ].
Qed.

Theorem poleData_char_triv_r : exists Phi, CharPole G (fun w => Z w = c0) Phi.
Proof.
  assert (Hg1 : gT c1 <> c0) by (rewrite gT_1; exact c1_nz).
  destruct (poleData_abstract_r gT gT' c1 GTAN GT'AN Hg1 GIDENT GISO GLOGD) as [Phi [H1 [H2 [H3 H4]]]].
  exists Phi. split; [|split; [|split]].
  - intros s Hs.
    assert (Hs1 : s <> c1) by (apply re_gt_ne; unfold c1, cofR; simpl; lra).
    assert (Hs0 : s <> c0) by (apply re_gt_ne; unfold c0, cofR; simpl; lra).
    assert (HZ : Z s <> c0) by (apply ZNZ; [lra|exact Hs1]).
    rewrite (H1 s Hs1). unfold formula.
    rewrite (GT'_ne1 s Hs1), (gT_ne1 s Hs1), gT_1, GT'_1.
    replace (cdiv (copp (cadd (csub (cdiv (cadd (Z s) (cmul (csub s c1) (Z' s))) (cmul (csub s c1) (Z s)))
                (cmul s (cdiv (cofR gam) c1))) (cmul c1 (csub c1 s)))) (cmul s (csub s c1)))
      with (cdiv (copp (csub (cadd (cadd (cdiv (Z' s) (Z s)) (cdiv c1 (csub s c1))) c1) (cmul (cadd c1 (cofR gam)) s)))
                 (cmul s (csub s c1))).
    + apply MELL1. lra.
    + pose proof (csub_nz s c1 Hs1). pose proof c1_nz. field. repeat split; auto.
  - intros rho Hr HZ. apply (H2 rho Hr). apply hgz. exact HZ.
  - intros rho Hr. destruct (H3 rho Hr) as [m [Hm [h [Hh Hev]]]].
    exists m. split; [rewrite Hm; apply hgz|]. exists h. split; [exact Hh|]. exact Hev.
  - intro z. destruct (H4 z) as [d [Hd Hz]]. exists d. split; [exact Hd|].
    intros w Hw1 Hw2. apply hgz. exact (Hz w Hw1 Hw2).
Qed.
End Trivial.
End PoleDataChar.

Print Assumptions poleData_abstract_r.
Print Assumptions poleData_char_nontriv_r.
Print Assumptions poleData_char_triv_r.
