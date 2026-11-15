(* ============================================================================
   NetTopologySuite.Proofs.LipIntUnit
   ----------------------------------------------------------------------------
   Calculus on the unit interval for the 3-axiom Lipschitz dyadic integral.

   lint carries its Lipschitz constant and proof as arguments, so every
   rewrite of an integrand has to rebuild them.  This file packages a
   function with a Lipschitz witness on the window [-1, 2] (ULip) and
   integrates it over [0, 1] (uint).  The window is wider than the range
   of integration so that LipIntFTC.lip_ftc gives a two-sided derivative
   at both endpoints.

     * lint_ftc_eval : second form of the fundamental theorem,
         lint f a b = F b - F a  when F' = f on [a, b].
       The difference F - lipF has zero derivative, so it is constant by
       RealMonotone.deriv_zero_const.  No MVT.
     * uint_ext / uint_plus / uint_scal / uint_const / uint_le, and
       uint_lincomb for a finite linear combination of integrands.
     * uint_ftc  : lint_ftc_eval on [0, 1].
     * uint_refl : the integral is invariant under x -> 1 - x.
       uint_odd  : an integrand odd about 1/2 integrates to 0.
     * ulip_* closure lemmas and the ulip tactic, which build the
       Lipschitz witness of a term made of +, -, *, / c, sin, cos.

   claimId: none.  Support for ClothoidFPrimeCore.
   No Admitted / Axiom / Parameter.  No MVT, Rolle, RiemannInt, Coquelicot.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude Code
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From Stdlib Require Import Ranalysis1.
From NTS.Proofs Require Import RealMonotone LipInt LipIntFTC.
Local Open Scope R_scope.

(* ---- second form of the fundamental theorem ------------------------------ *)

Lemma lipF_diff :
  forall (f : R -> R) (lo hi L : R) (HL : 0 <= L)
    (Hlip : forall x y, lo <= x <= hi -> lo <= y <= hi ->
              Rabs (f x - f y) <= L * Rabs (x - y))
    (a b : R) (Ha : lo <= a) (Hab : a <= b) (Hb : b <= hi),
    lipF f lo hi L HL Hlip b - lipF f lo hi L HL Hlip a
    = lint f lo hi L HL Hlip a b Ha Hab Hb.
Proof.
  intros f lo hi L HL Hlip a b Ha Hab Hb.
  assert (Hlob : lo <= b) by lra.
  assert (Hahi : a <= hi) by lra.
  rewrite (lipF_lint f lo hi L HL Hlip b Hlob Hb).
  rewrite (lipF_lint f lo hi L HL Hlip a Ha Hahi).
  rewrite (lint_add f lo hi L HL Hlip lo a b (Rle_refl lo) Ha Hahi Hlob Hb Hab).
  rewrite (lint_irrel f lo hi L L HL Hlip HL Hlip a b
             (Rle_trans lo lo a (Rle_refl lo) Ha) Hab Hb Ha Hab Hb).
  ring.
Qed.

Theorem lint_ftc_eval :
  forall (f F : R -> R) (lo hi L : R) (HL : 0 <= L)
    (Hlip : forall x y, lo <= x <= hi -> lo <= y <= hi ->
              Rabs (f x - f y) <= L * Rabs (x - y))
    (a b : R) (Ha : lo <= a) (Hab : a <= b) (Hb : b <= hi),
    lo < a -> b < hi ->
    (forall x, a <= x <= b -> derivable_pt_lim F x (f x)) ->
    lint f lo hi L HL Hlip a b Ha Hab Hb = F b - F a.
Proof.
  intros f F lo hi L HL Hlip a b Ha Hab Hb Hloa Hbhi HF.
  rewrite <- (lipF_diff f lo hi L HL Hlip a b Ha Hab Hb).
  assert (Hc : (F - lipF f lo hi L HL Hlip)%F a = (F - lipF f lo hi L HL Hlip)%F b).
  { apply (deriv_zero_const (F - lipF f lo hi L HL Hlip)%F
             (fun t => f t - f t) a b a b).
    - intros t Ht. apply derivable_pt_lim_minus.
      + apply HF. exact Ht.
      + apply lip_ftc. lra.
    - intros t _. ring.
    - lra.
    - lra. }
  unfold minus_fct in Hc. lra.
Qed.

(* ---- Lipschitz witnesses on the window [-1, 2] --------------------------- *)

Record ULip (f : R -> R) : Type := mkULip {
  ulip_k : R;
  ulip_k_nn : 0 <= ulip_k;
  ulip_k_ok : forall x y, -1 <= x <= 2 -> -1 <= y <= 2 ->
                Rabs (f x - f y) <= ulip_k * Rabs (x - y) }.

Arguments ulip_k {f} _.
Arguments ulip_k_nn {f} _.
Arguments ulip_k_ok {f} _.

Lemma uwin_lo : -1 <= 0.
Proof. lra. Qed.

Lemma uwin_hi : 1 <= 2.
Proof. lra. Qed.

Definition uint (f : R -> R) (H : ULip f) : R :=
  lint f (-1) 2 (ulip_k H) (ulip_k_nn H) (ulip_k_ok H) 0 1 uwin_lo Rle_0_1 uwin_hi.

Lemma ulip_bound :
  forall f (H : ULip f) x, -1 <= x <= 2 ->
    Rabs (f x) <= Rabs (f 0) + 2 * ulip_k H.
Proof.
  intros f H x Hx.
  assert (H0 : -1 <= 0 <= 2) by lra.
  pose proof (ulip_k_ok H x 0 Hx H0) as Hd.
  pose proof (ulip_k_nn H) as Hk.
  assert (Hx2 : Rabs (x - 0) <= 2).
  { apply Rabs_le. lra. }
  assert (Hm : ulip_k H * Rabs (x - 0) <= ulip_k H * 2).
  { apply Rmult_le_compat_l; assumption. }
  replace (f x) with ((f x - f 0) + f 0) by ring.
  eapply Rle_trans; [apply Rabs_triang|]. lra.
Qed.

Lemma ulip_const : forall c, ULip (fun _ => c).
Proof.
  intro c. refine (mkULip _ 0 (Rle_refl 0) _).
  intros x y _ _. replace (c - c) with 0 by ring.
  rewrite Rabs_R0. lra.
Qed.

Lemma ulip_id : ULip (fun x => x).
Proof.
  refine (mkULip _ 1 Rle_0_1 _). intros x y _ _. lra.
Qed.

Lemma ulip_plus :
  forall f g, ULip f -> ULip g -> ULip (fun x => f x + g x).
Proof.
  intros f g Hf Hg.
  refine (mkULip _ (ulip_k Hf + ulip_k Hg) _ _).
  - pose proof (ulip_k_nn Hf). pose proof (ulip_k_nn Hg). lra.
  - intros x y Hx Hy.
    pose proof (ulip_k_ok Hf x y Hx Hy). pose proof (ulip_k_ok Hg x y Hx Hy).
    replace (f x + g x - (f y + g y)) with ((f x - f y) + (g x - g y)) by ring.
    eapply Rle_trans; [apply Rabs_triang|]. lra.
Qed.

Lemma ulip_opp : forall f, ULip f -> ULip (fun x => - f x).
Proof.
  intros f Hf. refine (mkULip _ (ulip_k Hf) (ulip_k_nn Hf) _).
  intros x y Hx Hy.
  replace (- f x - - f y) with (- (f x - f y)) by ring.
  rewrite Rabs_Ropp. apply (ulip_k_ok Hf); assumption.
Qed.

Lemma ulip_minus :
  forall f g, ULip f -> ULip g -> ULip (fun x => f x - g x).
Proof.
  intros f g Hf Hg. unfold Rminus.
  apply (ulip_plus f (fun x => - g x)); [exact Hf | apply ulip_opp; exact Hg].
Qed.

Lemma ulip_mult :
  forall f g, ULip f -> ULip g -> ULip (fun x => f x * g x).
Proof.
  intros f g Hf Hg.
  set (Mf := Rabs (f 0) + 2 * ulip_k Hf).
  set (Mg := Rabs (g 0) + 2 * ulip_k Hg).
  pose proof (ulip_k_nn Hf) as Hkf. pose proof (ulip_k_nn Hg) as Hkg.
  assert (HMf : 0 <= Mf) by (unfold Mf; pose proof (Rabs_pos (f 0)); lra).
  assert (HMg : 0 <= Mg) by (unfold Mg; pose proof (Rabs_pos (g 0)); lra).
  refine (mkULip _ (Mf * ulip_k Hg + Mg * ulip_k Hf) _ _).
  - apply Rplus_le_le_0_compat; apply Rmult_le_pos; assumption.
  - intros x y Hx Hy.
    pose proof (ulip_k_ok Hf x y Hx Hy) as Hdf.
    pose proof (ulip_k_ok Hg x y Hx Hy) as Hdg.
    pose proof (ulip_bound f Hf x Hx) as Hbf. fold Mf in Hbf.
    pose proof (ulip_bound g Hg y Hy) as Hbg. fold Mg in Hbg.
    replace (f x * g x - f y * g y)
      with (f x * (g x - g y) + g y * (f x - f y)) by ring.
    eapply Rle_trans; [apply Rabs_triang|].
    rewrite !Rabs_mult.
    pose proof (Rabs_pos (x - y)) as Hxy.
    assert (H1 : Rabs (f x) * Rabs (g x - g y) <= Mf * (ulip_k Hg * Rabs (x - y))).
    { apply Rmult_le_compat; try apply Rabs_pos; assumption. }
    assert (H2 : Rabs (g y) * Rabs (f x - f y) <= Mg * (ulip_k Hf * Rabs (x - y))).
    { apply Rmult_le_compat; try apply Rabs_pos; assumption. }
    lra.
Qed.

Lemma ulip_div :
  forall f c, ULip f -> ULip (fun x => f x / c).
Proof.
  intros f c Hf. unfold Rdiv.
  apply (ulip_mult f (fun _ => / c)); [exact Hf | apply ulip_const].
Qed.

Lemma ulip_sin : forall f, ULip f -> ULip (fun x => sin (f x)).
Proof.
  intros f Hf. refine (mkULip _ (ulip_k Hf) (ulip_k_nn Hf) _).
  intros x y Hx Hy.
  eapply Rle_trans; [apply sin_lip|]. apply (ulip_k_ok Hf); assumption.
Qed.

Lemma ulip_cos : forall f, ULip f -> ULip (fun x => cos (f x)).
Proof.
  intros f Hf. refine (mkULip _ (ulip_k Hf) (ulip_k_nn Hf) _).
  intros x y Hx Hy.
  eapply Rle_trans; [apply cos_lip|]. apply (ulip_k_ok Hf); assumption.
Qed.

Lemma ulip_refl : forall f, ULip f -> ULip (fun x => f (1 - x)).
Proof.
  intros f Hf. refine (mkULip _ (ulip_k Hf) (ulip_k_nn Hf) _).
  intros x y Hx Hy.
  assert (Hx' : -1 <= 1 - x <= 2) by lra.
  assert (Hy' : -1 <= 1 - y <= 2) by lra.
  pose proof (ulip_k_ok Hf (1 - x) (1 - y) Hx' Hy') as Hd.
  replace (1 - x - (1 - y)) with (- (x - y)) in Hd by ring.
  rewrite Rabs_Ropp in Hd. exact Hd.
Qed.

Ltac ulip :=
  repeat first
    [ apply ulip_const | apply ulip_id | apply ulip_plus | apply ulip_minus
    | apply ulip_opp | apply ulip_mult | apply ulip_div
    | apply ulip_sin | apply ulip_cos ].

(* ---- the integral over [0, 1] -------------------------------------------- *)

Lemma ulip_k_weaken :
  forall f (H : ULip f) K, ulip_k H <= K ->
    forall x y, -1 <= x <= 2 -> -1 <= y <= 2 ->
      Rabs (f x - f y) <= K * Rabs (x - y).
Proof.
  intros f H K HK x y Hx Hy.
  eapply Rle_trans; [apply (ulip_k_ok H); assumption|].
  apply Rmult_le_compat_r; [apply Rabs_pos | exact HK].
Qed.

Lemma uint_ext :
  forall f g (Hf : ULip f) (Hg : ULip g),
    (forall x, 0 <= x <= 1 -> f x = g x) ->
    uint f Hf = uint g Hg.
Proof.
  intros f g Hf Hg Hfg. unfold uint.
  pose proof (ulip_k_nn Hf) as Hkf. pose proof (ulip_k_nn Hg) as Hkg.
  assert (HK : 0 <= ulip_k Hf + ulip_k Hg) by lra.
  assert (Hf' := ulip_k_weaken f Hf (ulip_k Hf + ulip_k Hg) ltac:(lra)).
  assert (Hg' := ulip_k_weaken g Hg (ulip_k Hf + ulip_k Hg) ltac:(lra)).
  rewrite (lint_irrel f (-1) 2 (ulip_k Hf) (ulip_k Hf + ulip_k Hg)
             (ulip_k_nn Hf) (ulip_k_ok Hf) HK Hf'
             0 1 uwin_lo Rle_0_1 uwin_hi uwin_lo Rle_0_1 uwin_hi).
  rewrite (lint_irrel g (-1) 2 (ulip_k Hg) (ulip_k Hf + ulip_k Hg)
             (ulip_k_nn Hg) (ulip_k_ok Hg) HK Hg'
             0 1 uwin_lo Rle_0_1 uwin_hi uwin_lo Rle_0_1 uwin_hi).
  apply lint_ext. exact Hfg.
Qed.

Lemma uint_plus :
  forall f g (Hf : ULip f) (Hg : ULip g) (H : ULip (fun x => f x + g x)),
    uint (fun x => f x + g x) H = uint f Hf + uint g Hg.
Proof. intros. unfold uint. apply lint_plus. Qed.

Lemma uint_scal :
  forall c f (Hf : ULip f) (H : ULip (fun x => c * f x)),
    uint (fun x => c * f x) H = c * uint f Hf.
Proof. intros. unfold uint. apply lint_scal. Qed.

Lemma uint_const :
  forall c (H : ULip (fun _ => c)), uint (fun _ => c) H = c.
Proof. intros. unfold uint. rewrite lint_const. ring. Qed.

Lemma uint_le :
  forall f g (Hf : ULip f) (Hg : ULip g),
    (forall x, 0 <= x <= 1 -> f x <= g x) ->
    uint f Hf <= uint g Hg.
Proof. intros f g Hf Hg Hfg. unfold uint. apply lint_mono. exact Hfg. Qed.

Lemma uint_ge_const :
  forall c f (Hf : ULip f),
    (forall x, 0 <= x <= 1 -> c <= f x) -> c <= uint f Hf.
Proof.
  intros c f Hf Hc.
  rewrite <- (uint_const c (ulip_const c)). apply uint_le. exact Hc.
Qed.

Lemma uint_le_const :
  forall c f (Hf : ULip f),
    (forall x, 0 <= x <= 1 -> f x <= c) -> uint f Hf <= c.
Proof.
  intros c f Hf Hc.
  rewrite <- (uint_const c (ulip_const c)). apply uint_le. exact Hc.
Qed.

(* A lint over [0, 1] taken in any window is the same number as uint. *)
Lemma uint_of_lint :
  forall f (H : ULip f) (lo hi L : R) (HL : 0 <= L)
    (Hlip : forall x y, lo <= x <= hi -> lo <= y <= hi ->
              Rabs (f x - f y) <= L * Rabs (x - y))
    (Ha : lo <= 0) (Hab : 0 <= 1) (Hb : 1 <= hi),
    lint f lo hi L HL Hlip 0 1 Ha Hab Hb = uint f H.
Proof. intros. unfold uint. apply lint_irrel_gen. Qed.

(* Finite linear combinations of integrands. *)

Definition uterm : Type := (R * {f : R -> R & ULip f})%type.

Definition ut (a : R) (f : R -> R) (H : ULip f) : uterm := (a, existT _ f H).

Fixpoint lc_fun (l : list uterm) (x : R) : R :=
  match l with
  | nil => 0
  | (a, existT _ f _) :: t => a * f x + lc_fun t x
  end.

Fixpoint lc_int (l : list uterm) : R :=
  match l with
  | nil => 0
  | (a, existT _ f H) :: t => a * uint f H + lc_int t
  end.

Lemma ulip_lc : forall l, ULip (lc_fun l).
Proof.
  induction l as [|[a [f H]] t IH].
  - exact (ulip_const 0).
  - exact (ulip_plus (fun x => a * f x) (lc_fun t)
             (ulip_mult (fun _ => a) f (ulip_const a) H) IH).
Qed.

Lemma uint_lc : forall l (H : ULip (lc_fun l)), uint (lc_fun l) H = lc_int l.
Proof.
  induction l as [|[a [f Hf]] t IH]; intro H.
  - apply (uint_const 0).
  - transitivity
      (uint (fun x => a * f x + lc_fun t x)
         (ulip_plus (fun x => a * f x) (lc_fun t)
            (ulip_mult (fun _ => a) f (ulip_const a) Hf) (ulip_lc t))).
    { apply uint_ext. intros; reflexivity. }
    rewrite (uint_plus (fun x => a * f x) (lc_fun t)
               (ulip_mult (fun _ => a) f (ulip_const a) Hf) (ulip_lc t)).
    simpl.
    rewrite (uint_scal a f Hf). rewrite IH. reflexivity.
Qed.

Lemma uint_lincomb :
  forall l g (Hg : ULip g),
    (forall x, 0 <= x <= 1 -> g x = lc_fun l x) ->
    uint g Hg = lc_int l.
Proof.
  intros l g Hg Hgl.
  rewrite (uint_ext g (lc_fun l) Hg (ulip_lc l) Hgl). apply uint_lc.
Qed.

(* ---- fundamental theorem and reflection on [0, 1] ------------------------ *)

Theorem uint_ftc :
  forall f (H : ULip f) F,
    (forall x, 0 <= x <= 1 -> derivable_pt_lim F x (f x)) ->
    uint f H = F 1 - F 0.
Proof.
  intros f H F HF. unfold uint. apply lint_ftc_eval; [lra | lra | exact HF].
Qed.

Theorem uint_refl :
  forall f (H : ULip f) (Hr : ULip (fun x => f (1 - x))),
    uint (fun x => f (1 - x)) Hr = uint f H.
Proof.
  intros f H Hr.
  set (G := lipF f (-1) 2 (ulip_k H) (ulip_k_nn H) (ulip_k_ok H)).
  rewrite (uint_ftc (fun x => f (1 - x)) Hr (fun x => - G (1 - x))).
  - replace (1 - 1) with 0 by ring. replace (1 - 0) with 1 by ring.
    unfold uint.
    rewrite <- (lipF_diff f (-1) 2 (ulip_k H) (ulip_k_nn H) (ulip_k_ok H)
                  0 1 uwin_lo Rle_0_1 uwin_hi).
    fold G. ring.
  - intros x Hx.
    replace (f (1 - x)) with (- (f (1 - x) * -1)) by ring.
    apply (derivable_pt_lim_opp (fun x => G (1 - x)) x (f (1 - x) * -1)).
    apply (derivable_pt_lim_comp (fun x => 1 - x) G x (-1) (f (1 - x))).
    + replace (-1) with (0 - 1) by ring.
      apply (derivable_pt_lim_minus (fun _ => 1) (fun x => x) x 0 1).
      * apply derivable_pt_lim_const.
      * apply derivable_pt_lim_id.
    + unfold G. apply lip_ftc. lra.
Qed.

Corollary uint_odd :
  forall f (H : ULip f),
    (forall x, 0 <= x <= 1 -> f (1 - x) = - f x) ->
    uint f H = 0.
Proof.
  intros f H Hodd.
  pose proof (uint_refl f H (ulip_refl f H)) as Hr.
  rewrite (uint_ext (fun x => f (1 - x)) (fun x => -1 * f x)
             (ulip_refl f H)
             (ulip_mult (fun _ => -1) f (ulip_const (-1)) H)) in Hr.
  - rewrite (uint_scal (-1) f H) in Hr. lra.
  - intros x Hx. rewrite (Hodd x Hx). ring.
Qed.

Print Assumptions lipF_diff.
Print Assumptions lint_ftc_eval.
Print Assumptions ulip_bound.
Print Assumptions ulip_const.
Print Assumptions ulip_id.
Print Assumptions ulip_plus.
Print Assumptions ulip_opp.
Print Assumptions ulip_minus.
Print Assumptions ulip_mult.
Print Assumptions ulip_div.
Print Assumptions ulip_sin.
Print Assumptions ulip_cos.
Print Assumptions ulip_refl.
Print Assumptions ulip_k_weaken.
Print Assumptions uint_ext.
Print Assumptions uint_plus.
Print Assumptions uint_scal.
Print Assumptions uint_const.
Print Assumptions uint_le.
Print Assumptions uint_ge_const.
Print Assumptions uint_le_const.
Print Assumptions uint_of_lint.
Print Assumptions ulip_lc.
Print Assumptions uint_lc.
Print Assumptions uint_lincomb.
Print Assumptions uint_ftc.
Print Assumptions uint_refl.
Print Assumptions uint_odd.
