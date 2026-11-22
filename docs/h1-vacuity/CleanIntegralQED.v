(* CleanIntegralQED.v -- a small ALLOWLIST-CLEAN integration library over
   Stdlib's R, and the two Alpöge-audit integral lemmas it unblocks.

   Why.  The corpus allows exactly three axioms (docs/axiom-allowlist.txt).
   Stdlib's RiemannInt (the value), RiemannInt_P10 (linear combinations),
   ln and Rpower all carry Classical_Prop.classic; so do MVT, MVT_cor1/2,
   Rolle, Heine, compact_P3 and continuity_ab_maj (checked with Print
   Assumptions, Rocq 9.2 / rocq-stdlib 9.2).  Clean, and used here:
   derivable_pt_lim_{plus,minus,opp,mult,scal,id,const,pow,comp,exp},
   completeness, archimed_cor1, Rle_dec / Rlt_dec, sum_f_R0, plus the
   allowlist-clean logarithm Lc / power rpc of AlpogeRealsQED2.v.

   The library (Parts 1-6) imports nothing beyond Stdlib.

   Part 1  Tagged partitions as lists of (tag, right end) cells, tagged sums.
           RInt f a b I  :=  a <= b /\ every tagged partition of [a, b] with
           mesh < d has its tagged sum within eps of I (Riemann's definition
           with a mesh condition; no step functions, no RiemannInt).
   Part 2  Uniqueness, linearity (RInt_plus, RInt_scal: c * f is integrable
           WITHOUT RiemannInt_P10), constants, extensionality, monotonicity.
   Part 3  Chasles: RInt f a b I1 -> RInt f b c I2 -> RInt f a c (I1 + I2)
           for f bounded on [a, c] (partition splitting at b).
   Part 4  A one-sided mean value theorem by BISECTION (Stdlib's MVT is not
           clean): x < y and F' = f on [x, y] give c in [x, y] with
           (F y - F x)/(y - x) <= f c (mvt_ge), and dually (mvt_le).  The
           bisection keeps one decidable inequality per step (Rle_dec), the
           limit point comes from completeness.  Corollaries: mean value
           inequalities, Lipschitz bounds from derivative bounds.
   Part 5  FTC.  FTC_value: RInt f a b I and F' = f on [a, b] give
           I = F b - F a (any Riemann-integrable f).  FTC: F' = f with f
           uniformly continuous on [a, b] gives RInt f a b (F b - F a);
           FTC_Lip / FTC_C1 for Lipschitz integrands and integrands with a
           bounded derivative.
   Part 6  Change of variables (RInt_change_var, RInt_change_var_FTC) and
           improper integrals over [a, oo) (RIntInf: uniqueness, linearity,
           monotonicity, Chasles = splitting off a finite interval).

   Checks (Parts 7-9), with the clean exp / Lc / rpc:
     Lc_deriv               Lc' = 1/y on (0, oo), elementary
     window_integral        int_Y^(Y^(1+delta)) dy/y = delta * Lc Y
     window_integral_rpow   the same integrand written y^theta * y^(-theta-1)
                            (the shape windowHyp_of_rpow needs)
     window_integral_by_cv  the same value through y = e^u
     windowU_change_var     the y = e^u identity of windowHypU_of_windowHyp
                            for majorants R with a y-antiderivative
     kernel_integral        int_0^oo u^k e^(-a u) / k! = a^(-(k+1))

   Evidence for docs/attacks/2026-11-22-clean-integral-library.md.
   NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import Reals Lra Psatz Lia List Factorial.
From NTS.Proofs.Probes Require Import AlpogeRealsQED AlpogeRealsQED2.
Import ListNotations.
Local Open Scope R_scope.

(* ===================================================================== *)
(* Part 0: small real-analysis helpers                                    *)
(* ===================================================================== *)

Lemma abs_lt_intro : forall x e, - e < x -> x < e -> Rabs x < e.
Proof. intros x e H1 H2. unfold Rabs. destruct (Rcase_abs x); lra. Qed.

Lemma abs_lt_elim : forall x e, Rabs x < e -> - e < x /\ x < e.
Proof. intros x e H. unfold Rabs in H. destruct (Rcase_abs x); split; lra. Qed.

Lemma abs_le_intro : forall x e, - e <= x -> x <= e -> Rabs x <= e.
Proof. intros x e H1 H2. unfold Rabs. destruct (Rcase_abs x); lra. Qed.

Lemma abs_le_elim : forall x e, Rabs x <= e -> - e <= x /\ x <= e.
Proof. intros x e H. unfold Rabs in H. destruct (Rcase_abs x); split; lra. Qed.

Lemma close_eq : forall x y, (forall e, 0 < e -> Rabs (x - y) < e) -> x = y.
Proof.
  intros x y H. destruct (Rtotal_order x y) as [Hl|[He|Hg]]; [|exact He|].
  - specialize (H (y - x) ltac:(lra)). apply abs_lt_elim in H. lra.
  - specialize (H (x - y) ltac:(lra)). apply abs_lt_elim in H. lra.
Qed.

Lemma close_le : forall x y, (forall e, 0 < e -> x <= y + e) -> x <= y.
Proof.
  intros x y H. destruct (Rle_lt_dec x y) as [Hl|Hg]; [exact Hl|].
  specialize (H ((x - y) / 2) ltac:(lra)). lra.
Qed.

(* derivative, transported along pointwise equal functions / equal values *)
Lemma dpl_ext : forall f g x l l', (forall y, f y = g y) -> l = l' ->
  derivable_pt_lim f x l -> derivable_pt_lim g x l'.
Proof.
  intros f g x l l' Hfg Hl H e He. destruct (H e He) as [d Hd]. exists d.
  intros h Hh Hhd. rewrite <- !Hfg, <- Hl. apply Hd; assumption.
Qed.

(* the linear-approximation form of a derivative at c *)
Lemma dpl_approx : forall F l c e (d : posreal) z,
  (forall h, h <> 0 -> Rabs h < d -> Rabs ((F (c + h) - F c) / h - l) < e) ->
  Rabs (z - c) < d -> Rabs (F z - F c - l * (z - c)) <= e * Rabs (z - c).
Proof.
  intros F l c e d z Hd Hz.
  destruct (Req_dec z c) as [Hzc|Hzc].
  - subst z. replace (F c - F c - l * (c - c)) with 0 by ring.
    replace (c - c) with 0 by ring. rewrite Rabs_R0. lra.
  - assert (Hh : z - c <> 0) by lra.
    specialize (Hd (z - c) Hh Hz). replace (c + (z - c)) with z in Hd by ring.
    replace (F z - F c - l * (z - c)) with ((z - c) * ((F z - F c) / (z - c) - l))
      by (field; exact Hh).
    rewrite Rabs_mult. rewrite (Rmult_comm e).
    apply Rmult_le_compat_l; [apply Rabs_pos|lra].
Qed.

Lemma INR_lt_pow2 : forall n, INR n < 2 ^ n.
Proof.
  induction n as [|n IH]; [simpl; lra|].
  rewrite S_INR. simpl. pose proof (pow_R1_Rle 2 n ltac:(lra)). lra.
Qed.

(* (y - x) / 2^n is eventually below any d > 0 *)
Lemma pow2_small : forall w d, 0 <= w -> 0 < d -> exists n, w / 2 ^ n < d.
Proof.
  intros w d Hw Hd.
  destruct (archimed_cor1 (d / (w + 1))) as [N [HN HN0]].
  { apply Rdiv_lt_0_compat; lra. }
  exists N.
  assert (HNp : 0 < INR N) by (apply lt_0_INR; exact HN0).
  pose proof (INR_lt_pow2 N) as Hp.
  assert (Hi : / 2 ^ N < / INR N) by (apply Rinv_lt_contravar; nra).
  assert (Hi0 : 0 < / 2 ^ N) by (apply Rinv_0_lt_compat; lra).
  assert (E : (w + 1) * (d / (w + 1)) = d) by (field; lra).
  unfold Rdiv. nra.
Qed.

(* ===================================================================== *)
(* Part 1: tagged partitions, tagged sums, the integral                   *)
(* ===================================================================== *)

(* A tagged partition of [a, b]: cells (t_i, x_(i+1)) read left to right,
   each with x_i <= t_i <= x_(i+1); the last right end is b. *)
Fixpoint tpart (a b : R) (l : list (R * R)) : Prop :=
  match l with
  | [] => a = b
  | (t, x) :: l' => a <= t /\ t <= x /\ tpart x b l'
  end.

(* the tagged (Riemann) sum  sum_i f(t_i) (x_(i+1) - x_i) *)
Fixpoint tsum (f : R -> R) (a : R) (l : list (R * R)) : R :=
  match l with
  | [] => 0
  | (t, x) :: l' => f t * (x - a) + tsum f x l'
  end.

(* mesh < d *)
Fixpoint fine (d a : R) (l : list (R * R)) : Prop :=
  match l with
  | [] => True
  | (t, x) :: l' => x - a < d /\ fine d x l'
  end.

(* THE INTEGRAL: I is the integral of f over [a, b]. *)
Definition RInt (f : R -> R) (a b I : R) : Prop :=
  a <= b /\ forall eps, 0 < eps -> exists d, 0 < d /\
    forall l, tpart a b l -> fine d a l -> Rabs (tsum f a l - I) < eps.

Lemma tpart_le : forall l a b, tpart a b l -> a <= b.
Proof.
  induction l as [|[t x] l IH]; simpl; intros a b H; [lra|].
  destruct H as [H1 [H2 H3]]. apply IH in H3. lra.
Qed.

Lemma fine_mono : forall l a d d', d <= d' -> fine d a l -> fine d' a l.
Proof.
  induction l as [|[t x] l IH]; simpl; intros a d d' Hd H; [trivial|].
  destruct H as [H1 H2]. split; [lra|]. eapply IH; eauto.
Qed.

(* uniform partitions, left tags *)
Fixpoint upart (a h : R) (n : nat) : list (R * R) :=
  match n with
  | O => []
  | S n' => (a, a + h) :: upart (a + h) h n'
  end.

Lemma upart_tpart : forall n a h, 0 <= h -> tpart a (a + INR n * h) (upart a h n).
Proof.
  induction n as [|n IH]; intros a h Hh; cbn [upart tpart].
  - simpl. ring.
  - split; [lra|]. split; [lra|].
    replace (a + INR (S n) * h) with ((a + h) + INR n * h) by (rewrite S_INR; ring).
    apply IH; exact Hh.
Qed.

Lemma upart_fine : forall n a h d, h < d -> fine d a (upart a h n).
Proof.
  induction n as [|n IH]; intros a h d Hd; cbn [upart fine]; [trivial|].
  split; [lra|]. apply IH; exact Hd.
Qed.

(* every interval has partitions of every mesh *)
Lemma exists_fine : forall a b d, a <= b -> 0 < d -> exists l, tpart a b l /\ fine d a l.
Proof.
  intros a b d Hab Hd.
  destruct (archimed_cor1 (d / (b - a + 1))) as [N [HN HN0]].
  { apply Rdiv_lt_0_compat; lra. }
  assert (HNp : 0 < INR N) by (apply lt_0_INR; exact HN0).
  set (h := (b - a) / INR N).
  assert (Hh0 : 0 <= h) by (unfold h; apply Rmult_le_pos; [lra|left; apply Rinv_0_lt_compat; lra]).
  exists (upart a h N). split.
  - assert (Hb : a + INR N * h = b) by (unfold h; field; lra).
    rewrite <- Hb at 1. apply upart_tpart. exact Hh0.
  - apply upart_fine.
    assert (Hi0 : 0 < / INR N) by (apply Rinv_0_lt_compat; lra).
    assert (E : (b - a + 1) * (d / (b - a + 1)) = d) by (field; lra).
    unfold h, Rdiv. unfold Rdiv in E, HN. nra.
Qed.

(* sums are linear, monotone and constant on constants *)
Lemma tsum_plus : forall f g l a, tsum (fun x => f x + g x) a l = tsum f a l + tsum g a l.
Proof. intros f g l. induction l as [|[t x] l IH]; intro a; simpl; [ring|]. rewrite IH. ring. Qed.

Lemma tsum_scal : forall c f l a, tsum (fun x => c * f x) a l = c * tsum f a l.
Proof. intros c f l. induction l as [|[t x] l IH]; intro a; simpl; [ring|]. rewrite IH. ring. Qed.

Lemma tsum_ext : forall f g l a b, tpart a b l ->
  (forall x, a <= x <= b -> f x = g x) -> tsum f a l = tsum g a l.
Proof.
  intros f g l. induction l as [|[t x] l IH]; intros a b Hl H; simpl; [reflexivity|].
  destruct Hl as [H1 [H2 H3]]. pose proof (tpart_le _ _ _ H3).
  rewrite (H t ltac:(lra)). rewrite (IH x b H3); [reflexivity|].
  intros y Hy. apply H. lra.
Qed.

Lemma tsum_le : forall f g l a b, tpart a b l ->
  (forall x, a <= x <= b -> f x <= g x) -> tsum f a l <= tsum g a l.
Proof.
  intros f g l. induction l as [|[t x] l IH]; intros a b Hl H; simpl; [lra|].
  destruct Hl as [H1 [H2 H3]]. pose proof (tpart_le _ _ _ H3).
  assert (Ht : f t * (x - a) <= g t * (x - a)) by (apply Rmult_le_compat_r; [lra|apply H; lra]).
  assert (Hr : tsum f x l <= tsum g x l) by (apply (IH x b H3); intros y Hy; apply H; lra).
  lra.
Qed.

Lemma tsum_const : forall c l a b, tpart a b l -> tsum (fun _ => c) a l = c * (b - a).
Proof.
  intros c l. induction l as [|[t x] l IH]; intros a b Hl; simpl in *.
  - subst. ring.
  - destruct Hl as [_ [_ H3]]. rewrite (IH x b H3). ring.
Qed.

(* ===================================================================== *)
(* Part 2: uniqueness, linearity, monotonicity                            *)
(* ===================================================================== *)

Lemma RInt_le_ab : forall f a b I, RInt f a b I -> a <= b.
Proof. intros f a b I [H _]. exact H. Qed.

(* two tolerances, one partition *)
Lemma common_fine : forall a b d1 d2, a <= b -> 0 < d1 -> 0 < d2 ->
  exists l, tpart a b l /\ fine d1 a l /\ fine d2 a l.
Proof.
  intros a b d1 d2 Hab H1 H2.
  destruct (exists_fine a b (Rmin d1 d2) Hab (Rmin_pos _ _ H1 H2)) as [l [Hl Hf]].
  exists l. split; [exact Hl|]. split.
  - eapply fine_mono; [apply Rmin_l|exact Hf].
  - eapply fine_mono; [apply Rmin_r|exact Hf].
Qed.

Theorem RInt_unique : forall f a b I J, RInt f a b I -> RInt f a b J -> I = J.
Proof.
  intros f a b I J [Hab HI] [_ HJ]. apply close_eq. intros e He.
  destruct (HI (e / 2) ltac:(lra)) as [d1 [Hd1 H1]].
  destruct (HJ (e / 2) ltac:(lra)) as [d2 [Hd2 H2]].
  destruct (common_fine a b d1 d2 Hab Hd1 Hd2) as [l [Hl [F1 F2]]].
  specialize (H1 l Hl F1). specialize (H2 l Hl F2).
  apply abs_lt_elim in H1, H2. apply abs_lt_intro; lra.
Qed.

Theorem RInt_ext : forall f g a b I, (forall x, a <= x <= b -> f x = g x) ->
  RInt f a b I -> RInt g a b I.
Proof.
  intros f g a b I Hfg [Hab HI]. split; [exact Hab|]. intros e He.
  destruct (HI e He) as [d [Hd H]]. exists d. split; [exact Hd|].
  intros l Hl Hf. rewrite <- (tsum_ext f g l a b Hl Hfg). apply H; assumption.
Qed.

Theorem RInt_const : forall c a b, a <= b -> RInt (fun _ => c) a b (c * (b - a)).
Proof.
  intros c a b Hab. split; [exact Hab|]. intros e He. exists 1. split; [lra|].
  intros l Hl _. rewrite (tsum_const c l a b Hl).
  replace (c * (b - a) - c * (b - a)) with 0 by ring. rewrite Rabs_R0. exact He.
Qed.

Theorem RInt_plus : forall f g a b I J, RInt f a b I -> RInt g a b J ->
  RInt (fun x => f x + g x) a b (I + J).
Proof.
  intros f g a b I J [Hab HI] [_ HJ]. split; [exact Hab|]. intros e He.
  destruct (HI (e / 2) ltac:(lra)) as [d1 [Hd1 H1]].
  destruct (HJ (e / 2) ltac:(lra)) as [d2 [Hd2 H2]].
  exists (Rmin d1 d2). split; [apply Rmin_pos; assumption|]. intros l Hl Hf.
  specialize (H1 l Hl (fine_mono _ _ _ _ (Rmin_l d1 d2) Hf)).
  specialize (H2 l Hl (fine_mono _ _ _ _ (Rmin_r d1 d2) Hf)).
  rewrite tsum_plus. apply abs_lt_elim in H1, H2. apply abs_lt_intro; lra.
Qed.

(* integrability of c * f, without RiemannInt_P10 *)
Theorem RInt_scal : forall c f a b I, RInt f a b I -> RInt (fun x => c * f x) a b (c * I).
Proof.
  intros c f a b I [Hab HI]. split; [exact Hab|]. intros e He.
  set (q := e / (Rabs c + 1)).
  assert (Hc : 0 <= Rabs c) by apply Rabs_pos.
  assert (Hq : 0 < q) by (unfold q; apply Rdiv_lt_0_compat; lra).
  assert (Eq : q * (Rabs c + 1) = e) by (unfold q; field; lra).
  destruct (HI q Hq) as [d [Hd H]]. exists d. split; [exact Hd|]. intros l Hl Hf.
  specialize (H l Hl Hf). rewrite tsum_scal.
  replace (c * tsum f a l - c * I) with (c * (tsum f a l - I)) by ring.
  rewrite Rabs_mult. pose proof (Rabs_pos (tsum f a l - I)). nra.
Qed.

Corollary RInt_opp : forall f a b I, RInt f a b I -> RInt (fun x => - f x) a b (- I).
Proof.
  intros f a b I H. replace (- I) with (-1 * I) by ring.
  apply (RInt_ext (fun x => -1 * f x)); [intros; ring|]. apply RInt_scal. exact H.
Qed.

Corollary RInt_minus : forall f g a b I J, RInt f a b I -> RInt g a b J ->
  RInt (fun x => f x - g x) a b (I - J).
Proof.
  intros f g a b I J Hf Hg. apply (RInt_ext (fun x => f x + - g x)); [intros; ring|].
  apply RInt_plus; [exact Hf|apply RInt_opp; exact Hg].
Qed.

Corollary RInt_lin : forall c1 c2 f g a b I J, RInt f a b I -> RInt g a b J ->
  RInt (fun x => c1 * f x + c2 * g x) a b (c1 * I + c2 * J).
Proof. intros. apply RInt_plus; apply RInt_scal; assumption. Qed.

(* monotonicity *)
Theorem RInt_le : forall f g a b I J, RInt f a b I -> RInt g a b J ->
  (forall x, a <= x <= b -> f x <= g x) -> I <= J.
Proof.
  intros f g a b I J [Hab HI] [_ HJ] Hfg. apply close_le. intros e He.
  destruct (HI (e / 2) ltac:(lra)) as [d1 [Hd1 H1]].
  destruct (HJ (e / 2) ltac:(lra)) as [d2 [Hd2 H2]].
  destruct (common_fine a b d1 d2 Hab Hd1 Hd2) as [l [Hl [F1 F2]]].
  specialize (H1 l Hl F1). specialize (H2 l Hl F2).
  pose proof (tsum_le f g l a b Hl Hfg).
  apply abs_lt_elim in H1, H2. lra.
Qed.

Corollary RInt_nonneg : forall f a b I, RInt f a b I ->
  (forall x, a <= x <= b -> 0 <= f x) -> 0 <= I.
Proof.
  intros f a b I H Hf. pose proof (RInt_le _ _ a b _ _ (RInt_const 0 a b (RInt_le_ab _ _ _ _ H)) H Hf).
  lra.
Qed.

Corollary RInt_abs_bound : forall f a b I M, RInt f a b I ->
  (forall x, a <= x <= b -> Rabs (f x) <= M) -> Rabs I <= M * (b - a).
Proof.
  intros f a b I M H HM. pose proof (RInt_le_ab _ _ _ _ H) as Hab.
  assert (H1 : I <= M * (b - a)).
  { apply (RInt_le f (fun _ => M) a b); [exact H|apply RInt_const; exact Hab|].
    intros x Hx. pose proof (abs_le_elim _ _ (HM x Hx)); lra. }
  assert (H2 : - M * (b - a) <= I).
  { apply (RInt_le (fun _ => - M) f a b); [apply RInt_const; exact Hab|exact H|].
    intros x Hx. pose proof (abs_le_elim _ _ (HM x Hx)); lra. }
  apply abs_le_intro; lra.
Qed.

(* ===================================================================== *)
(* Part 3: Chasles                                                        *)
(* ===================================================================== *)

Lemma diff_bound : forall u v w M d, Rabs u <= M -> Rabs v <= M -> 0 <= w -> w <= d ->
  Rabs ((u - v) * w) <= 2 * M * d.
Proof.
  intros u v w M d Hu Hv Hw Hwd. apply abs_le_elim in Hu, Hv. apply abs_le_intro; nra.
Qed.

(* split a fine partition of [x0, c] at b into fine partitions of [x0, b]
   and [b, c]; only the straddling cell changes the sum, by <= 2 M d *)
Lemma split_part : forall f a b c M d, b <= c -> 0 < d ->
  (forall x, a <= x <= c -> Rabs (f x) <= M) ->
  forall l x0, a <= x0 -> x0 <= b -> tpart x0 c l -> fine d x0 l ->
  exists l1 l2, tpart x0 b l1 /\ fine d x0 l1 /\ tpart b c l2 /\ fine d b l2 /\
    Rabs (tsum f x0 l - (tsum f x0 l1 + tsum f b l2)) <= 2 * M * d.
Proof.
  intros f a b c M d Hbc Hd HM l. induction l as [|[t x] l IH]; intros x0 Hax0 Hx0b Hl Hf.
  - simpl in Hl. subst x0. exists [], []. simpl. repeat split; try lra.
    replace (0 - (0 + 0)) with 0 by ring. rewrite Rabs_R0.
    pose proof (HM c ltac:(lra)). pose proof (Rabs_pos (f c)). nra.
  - destruct Hl as [H1 [H2 H3]]. destruct Hf as [Hf1 Hf2].
    pose proof (tpart_le _ _ _ H3) as Hxc.
    destruct (Rle_lt_dec x b) as [Hxb|Hxb].
    + destruct (IH x ltac:(lra) Hxb H3 Hf2) as [l1 [l2 [A1 [A2 [A3 [A4 A5]]]]]].
      exists ((t, x) :: l1), l2. simpl. repeat split; try lra; try assumption.
      match goal with |- Rabs ?e <= _ =>
        replace e with (tsum f x l - (tsum f x l1 + tsum f b l2)) by ring end.
      exact A5.
    + destruct (Rle_lt_dec t b) as [Htb|Htb].
      * exists [(t, b)], ((b, x) :: l). simpl. repeat split; try lra; try assumption.
        match goal with |- Rabs ?e <= _ => replace e with ((f t - f b) * (x - b)) by ring end.
        apply diff_bound; [apply HM; lra|apply HM; lra|lra|lra].
      * exists [(b, b)], ((t, x) :: l). simpl. repeat split; try lra; try assumption.
        match goal with |- Rabs ?e <= _ => replace e with ((f t - f b) * (b - x0)) by ring end.
        apply diff_bound; [apply HM; lra|apply HM; lra|lra|lra].
Qed.

Theorem RInt_chasles : forall f a b c M I1 I2,
  (forall x, a <= x <= c -> Rabs (f x) <= M) ->
  RInt f a b I1 -> RInt f b c I2 -> RInt f a c (I1 + I2).
Proof.
  intros f a b c M I1 I2 HM [Hab H1] [Hbc H2]. split; [lra|]. intros e He.
  assert (HM0 : 0 <= M) by (pose proof (HM a ltac:(lra)); pose proof (Rabs_pos (f a)); lra).
  destruct (H1 (e / 3) ltac:(lra)) as [d1 [Hd1 K1]].
  destruct (H2 (e / 3) ltac:(lra)) as [d2 [Hd2 K2]].
  set (d3 := e / (3 * (2 * M + 1))).
  assert (Hd3 : 0 < d3) by (unfold d3; apply Rdiv_lt_0_compat; lra).
  assert (E3 : d3 * (3 * (2 * M + 1)) = e) by (unfold d3; field; lra).
  set (d := Rmin d1 (Rmin d2 d3)).
  assert (Hd : 0 < d) by (unfold d; repeat apply Rmin_pos; assumption).
  assert (Hdd1 : d <= d1) by (unfold d; apply Rmin_l).
  assert (Hdd2 : d <= d2) by (unfold d; eapply Rle_trans; [apply Rmin_r|apply Rmin_l]).
  assert (Hdd3 : d <= d3) by (unfold d; eapply Rle_trans; [apply Rmin_r|apply Rmin_r]).
  exists d. split; [exact Hd|]. intros l Hl Hf.
  destruct (split_part f a b c M d Hbc Hd HM l a (Rle_refl a) Hab Hl Hf)
    as [l1 [l2 [A1 [A2 [A3 [A4 A5]]]]]].
  specialize (K1 l1 A1 (fine_mono _ _ _ _ Hdd1 A2)).
  specialize (K2 l2 A3 (fine_mono _ _ _ _ Hdd2 A4)).
  assert (HMd : 2 * M * d <= e / 3) by nra.
  apply abs_lt_elim in K1, K2. apply abs_le_elim in A5. apply abs_lt_intro; lra.
Qed.

(* ===================================================================== *)
(* Part 4: a one-sided mean value theorem by bisection                    *)
(* ===================================================================== *)

Section Bisect.
Variables (F : R -> R) (q : R).

(* keep the half on which the difference quotient stays >= q *)
Fixpoint bis (x y : R) (n : nat) : R * R :=
  match n with
  | O => (x, y)
  | S n' => let p := bis x y n' in
            let m := (fst p + snd p) / 2 in
            if Rle_dec (q * (m - fst p)) (F m - F (fst p)) then (fst p, m) else (m, snd p)
  end.

Lemma bis_S : forall x y n, bis x y (S n) =
  (let p := bis x y n in
   let m := (fst p + snd p) / 2 in
   if Rle_dec (q * (m - fst p)) (F m - F (fst p)) then (fst p, m) else (m, snd p)).
Proof. reflexivity. Qed.

Lemma bis_width : forall x y n, snd (bis x y n) - fst (bis x y n) = (y - x) / 2 ^ n.
Proof.
  intros x y n. induction n as [|n IH]; [simpl; field|].
  rewrite bis_S. destruct (bis x y n) as [u v]. cbn [fst snd] in IH |- *.
  assert (H2 : 0 < 2 ^ n) by (apply pow_lt; lra).
  replace (2 ^ S n) with (2 * 2 ^ n) by reflexivity.
  replace ((y - x) / (2 * 2 ^ n)) with ((y - x) / 2 ^ n / 2) by (field; lra).
  rewrite <- IH.
  destruct (Rle_dec _ _); cbn [fst snd]; field.
Qed.

Lemma bis_inv : forall x y n, q * (y - x) <= F y - F x ->
  q * (snd (bis x y n) - fst (bis x y n)) <= F (snd (bis x y n)) - F (fst (bis x y n)).
Proof.
  intros x y n H0. induction n as [|n IH]; [exact H0|].
  rewrite bis_S. destruct (bis x y n) as [u v]. cbn [fst snd] in IH |- *.
  destruct (Rle_dec _ _) as [Hc|Hc]; cbn [fst snd]; [exact Hc|].
  apply Rnot_le_lt in Hc.
  replace (q * (v - (u + v) / 2)) with (q * (v - u) - q * ((u + v) / 2 - u)) by field.
  lra.
Qed.

Lemma bis_step_mono : forall x y n,
  fst (bis x y n) <= fst (bis x y (S n)) /\ snd (bis x y (S n)) <= snd (bis x y n) /\
  fst (bis x y (S n)) <= snd (bis x y (S n)) \/ snd (bis x y n) < fst (bis x y n).
Proof.
  intros x y n. rewrite bis_S. destruct (bis x y n) as [u v]. cbn [fst snd].
  destruct (Rle_lt_dec u v) as [Huv|Huv]; [left|right; exact Huv].
  destruct (Rle_dec _ _); cbn [fst snd]; lra.
Qed.

Lemma bis_ordered : forall x y n, x <= y -> fst (bis x y n) <= snd (bis x y n).
Proof.
  intros x y n Hxy. pose proof (bis_width x y n).
  assert (0 <= (y - x) / 2 ^ n) by (apply Rmult_le_pos; [lra|left; apply Rinv_0_lt_compat, pow_lt; lra]).
  lra.
Qed.

Lemma bis_mono : forall x y, x <= y -> forall k n,
  fst (bis x y n) <= fst (bis x y (n + k)) /\ snd (bis x y (n + k)) <= snd (bis x y n).
Proof.
  intros x y Hxy k. induction k as [|k IH]; intro n.
  - rewrite Nat.add_0_r. lra.
  - destruct (IH n) as [A B]. replace (n + S k)%nat with (S (n + k)) by lia.
    destruct (bis_step_mono x y (n + k)) as [[C [D _]]|C].
    + split; lra.
    + pose proof (bis_ordered x y (n + k) Hxy). lra.
Qed.

Lemma bis_fst_le_snd : forall x y, x <= y -> forall m n, fst (bis x y m) <= snd (bis x y n).
Proof.
  intros x y Hxy m n. destruct (Compare_dec.le_lt_dec m n) as [Hmn|Hmn].
  - replace n with (m + (n - m))%nat by lia.
    destruct (bis_mono x y Hxy (n - m) m) as [A _].
    pose proof (bis_ordered x y (m + (n - m)) Hxy). lra.
  - replace m with (n + (m - n))%nat by lia.
    destruct (bis_mono x y Hxy (m - n) n) as [_ B].
    pose proof (bis_ordered x y (n + (m - n)) Hxy). lra.
Qed.

(* a point inside every bisection interval *)
Lemma bis_limit : forall x y, x <= y ->
  exists c, forall n, fst (bis x y n) <= c <= snd (bis x y n).
Proof.
  intros x y Hxy.
  set (E := fun z => exists n, z = fst (bis x y n)).
  destruct (completeness E) as [c [Hub Hlub]].
  - exists y. intros z [n Hz]. subst z.
    pose proof (bis_fst_le_snd x y Hxy n 0). simpl in H. exact H.
  - exists x. exists O. reflexivity.
  - exists c. intro n. split.
    + apply Hub. exists n. reflexivity.
    + apply Hlub. intros z [m Hz]. subst z. apply bis_fst_le_snd. exact Hxy.
Qed.

End Bisect.

(* The one-sided mean value theorem. *)
Theorem mvt_ge : forall F f x y, x < y ->
  (forall z, x <= z <= y -> derivable_pt_lim F z (f z)) ->
  exists c, x <= c <= y /\ (F y - F x) / (y - x) <= f c.
Proof.
  intros F f x y Hxy Hd.
  set (q := (F y - F x) / (y - x)).
  assert (H0 : q * (y - x) <= F y - F x) by (unfold q; right; field; lra).
  destruct (bis_limit F q x y ltac:(lra)) as [c Hc].
  assert (Hcxy : x <= c <= y) by (pose proof (Hc O); simpl in H; exact H).
  exists c. split; [exact Hcxy|]. fold q.
  apply close_le. intros e He.
  destruct (Hd c Hcxy e He) as [d Hdd].
  destruct (pow2_small (y - x) d ltac:(lra) (cond_pos d)) as [n Hn].
  set (u := fst (bis F q x y n)). set (v := snd (bis F q x y n)).
  assert (Huc : u <= c <= v) by exact (Hc n).
  assert (Hw : v - u = (y - x) / 2 ^ n) by exact (bis_width F q x y n).
  assert (Hwp : 0 < v - u) by (rewrite Hw; apply Rdiv_lt_0_compat; [lra|apply pow_lt; lra]).
  assert (Hinv : q * (v - u) <= F v - F u) by exact (bis_inv F q x y n H0).
  assert (Hv : Rabs (v - c) < d) by (apply abs_lt_intro; lra).
  assert (Hu : Rabs (u - c) < d) by (apply abs_lt_intro; lra).
  pose proof (dpl_approx F (f c) c e d v Hdd Hv) as Av.
  pose proof (dpl_approx F (f c) c e d u Hdd Hu) as Au.
  rewrite (Rabs_right (v - c)) in Av by lra. rewrite (Rabs_left1 (u - c)) in Au by lra.
  apply abs_le_elim in Av, Au.
  assert (Hsum : F v - F u <= (f c + e) * (v - u)) by nra.
  assert (Hq : q * (v - u) <= (f c + e) * (v - u)) by lra.
  apply Rmult_le_reg_r in Hq; [lra|exact Hwp].
Qed.

Theorem mvt_le : forall F f x y, x < y ->
  (forall z, x <= z <= y -> derivable_pt_lim F z (f z)) ->
  exists c, x <= c <= y /\ f c <= (F y - F x) / (y - x).
Proof.
  intros F f x y Hxy Hd.
  destruct (mvt_ge (fun z => - F z) (fun z => - f z) x y Hxy) as [c [Hc H]].
  - intros z Hz. apply (dpl_ext (opp_fct F) _ _ (- f z)); [reflexivity|reflexivity|].
    apply derivable_pt_lim_opp. apply Hd. exact Hz.
  - exists c. split; [exact Hc|].
    replace ((- F y - - F x) / (y - x)) with (- ((F y - F x) / (y - x))) in H by (field; lra).
    lra.
Qed.

(* mean value inequalities *)
Corollary mvi_upper : forall F f x y M, x <= y ->
  (forall z, x <= z <= y -> derivable_pt_lim F z (f z)) ->
  (forall z, x <= z <= y -> f z <= M) -> F y - F x <= M * (y - x).
Proof.
  intros F f x y M Hxy Hd HM. destruct Hxy as [Hlt|Heq].
  - destruct (mvt_ge F f x y Hlt Hd) as [c [Hc Hq]].
    pose proof (HM c Hc). assert (Hq' : (F y - F x) / (y - x) <= M) by lra.
    apply (Rmult_le_compat_r (y - x)) in Hq'; [|lra].
    unfold Rdiv in Hq'. rewrite Rmult_assoc, Rinv_l in Hq' by lra. lra.
  - subst y. lra.
Qed.

Corollary mvi_lower : forall F f x y m, x <= y ->
  (forall z, x <= z <= y -> derivable_pt_lim F z (f z)) ->
  (forall z, x <= z <= y -> m <= f z) -> m * (y - x) <= F y - F x.
Proof.
  intros F f x y m Hxy Hd Hm.
  assert (H : (- F y) - (- F x) <= (- m) * (y - x)).
  { apply (mvi_upper (fun z => - F z) (fun z => - f z) x y (- m) Hxy).
    - intros z Hz. apply (dpl_ext (opp_fct F) _ _ (- f z)); [reflexivity|reflexivity|].
      apply derivable_pt_lim_opp. apply Hd. exact Hz.
    - intros z Hz. pose proof (Hm z Hz). lra. }
  lra.
Qed.

Corollary mvi_abs : forall F f x y M, x <= y ->
  (forall z, x <= z <= y -> derivable_pt_lim F z (f z)) ->
  (forall z, x <= z <= y -> Rabs (f z) <= M) -> Rabs (F y - F x) <= M * (y - x).
Proof.
  intros F f x y M Hxy Hd HM. apply abs_le_intro.
  - assert (H : - M * (y - x) <= F y - F x).
    { apply (mvi_lower F f x y (- M) Hxy Hd). intros z Hz. pose proof (abs_le_elim _ _ (HM z Hz)); lra. }
    lra.
  - apply (mvi_upper F f x y M Hxy Hd). intros z Hz. pose proof (abs_le_elim _ _ (HM z Hz)); lra.
Qed.

(* a nonnegative derivative makes a function increasing *)
Corollary deriv_nonneg_incr : forall F f x y, x <= y ->
  (forall z, x <= z <= y -> derivable_pt_lim F z (f z)) ->
  (forall z, x <= z <= y -> 0 <= f z) -> F x <= F y.
Proof. intros. pose proof (mvi_lower F f x y 0 H H0 H1). lra. Qed.

(* regularity classes for integrands *)
Definition UC (f : R -> R) (a b : R) : Prop :=
  forall e, 0 < e -> exists d, 0 < d /\ forall x y, a <= x <= b -> a <= y <= b ->
    Rabs (x - y) < d -> Rabs (f x - f y) < e.

Definition Lip (f : R -> R) (a b L : R) : Prop :=
  forall x y, a <= x <= b -> a <= y <= b -> Rabs (f x - f y) <= L * Rabs (x - y).

Lemma Lip_UC : forall f a b L, Lip f a b L -> UC f a b.
Proof.
  intros f a b L HL e He.
  assert (HL0 : 0 <= Rabs L) by apply Rabs_pos.
  set (d := e / (Rabs L + 1)).
  assert (Hd : 0 < d) by (unfold d; apply Rdiv_lt_0_compat; lra).
  assert (Ed : d * (Rabs L + 1) = e) by (unfold d; field; lra).
  exists d. split; [exact Hd|]. intros x y Hx Hy Hxy.
  pose proof (HL x y Hx Hy) as H. pose proof (Rabs_pos (x - y)).
  pose proof (Rle_abs L). nra.
Qed.

(* Lipschitz from a derivative bound (mean value inequality) *)
Lemma Lip_of_deriv : forall f f' a b L,
  (forall z, a <= z <= b -> derivable_pt_lim f z (f' z)) ->
  (forall z, a <= z <= b -> Rabs (f' z) <= L) -> Lip f a b L.
Proof.
  intros f f' a b L Hd HL x y Hx Hy.
  destruct (Rle_lt_dec x y) as [Hxy|Hxy].
  - rewrite Rabs_minus_sym, (Rabs_minus_sym x y), (Rabs_right (y - x)) by lra.
    apply (mvi_abs f f' x y L Hxy); intros z Hz; [apply Hd|apply HL]; lra.
  - rewrite (Rabs_right (x - y)) by lra.
    apply (mvi_abs f f' y x L ltac:(lra)); intros z Hz; [apply Hd|apply HL]; lra.
Qed.

(* ===================================================================== *)
(* Part 5: the fundamental theorem of calculus                            *)
(* ===================================================================== *)

Lemma dpl_sub_lin : forall F l c z, derivable_pt_lim F z l ->
  derivable_pt_lim (fun y => F y - c * y) z (l - c).
Proof.
  intros F l c z H.
  apply (dpl_ext (minus_fct F (mult_real_fct c id)) _ _ (l - c * 1));
    [reflexivity|ring|].
  apply derivable_pt_lim_minus; [exact H|].
  apply derivable_pt_lim_scal. apply derivable_pt_lim_id.
Qed.

(* FTC, value form: for ANY integrable f with an antiderivative F. *)
Lemma retag_ge : forall F f a b d,
  (forall x, a <= x <= b -> derivable_pt_lim F x (f x)) ->
  forall l x0, a <= x0 -> tpart x0 b l -> fine d x0 l ->
  exists l', tpart x0 b l' /\ fine d x0 l' /\ F b - F x0 <= tsum f x0 l'.
Proof.
  intros F f a b d Hd l. induction l as [|[t x] l IH]; intros x0 Hax0 Hl Hf.
  - simpl in Hl. subst x0. exists []. simpl. repeat split. lra.
  - destruct Hl as [H1 [H2 H3]]. destruct Hf as [Hf1 Hf2].
    pose proof (tpart_le _ _ _ H3) as Hxb.
    destruct (IH x ltac:(lra) H3 Hf2) as [l' [A1 [A2 A3]]].
    destruct (Rle_lt_dec x x0) as [Hxx|Hxx].
    + exists ((x0, x) :: l'). simpl. repeat split; try lra; try assumption.
      assert (x = x0) by lra. subst x. lra.
    + destruct (mvt_ge F f x0 x Hxx) as [c [Hc Hq]].
      { intros z Hz. apply Hd. lra. }
      exists ((c, x) :: l'). simpl. repeat split; try lra; try assumption.
      apply (Rmult_le_compat_r (x - x0)) in Hq; [|lra].
      unfold Rdiv in Hq. rewrite Rmult_assoc, Rinv_l in Hq by lra. lra.
Qed.

Lemma retag_le : forall F f a b d,
  (forall x, a <= x <= b -> derivable_pt_lim F x (f x)) ->
  forall l x0, a <= x0 -> tpart x0 b l -> fine d x0 l ->
  exists l', tpart x0 b l' /\ fine d x0 l' /\ tsum f x0 l' <= F b - F x0.
Proof.
  intros F f a b d Hd l. induction l as [|[t x] l IH]; intros x0 Hax0 Hl Hf.
  - simpl in Hl. subst x0. exists []. simpl. repeat split. lra.
  - destruct Hl as [H1 [H2 H3]]. destruct Hf as [Hf1 Hf2].
    pose proof (tpart_le _ _ _ H3) as Hxb.
    destruct (IH x ltac:(lra) H3 Hf2) as [l' [A1 [A2 A3]]].
    destruct (Rle_lt_dec x x0) as [Hxx|Hxx].
    + exists ((x0, x) :: l'). simpl. repeat split; try lra; try assumption.
      assert (x = x0) by lra. subst x. lra.
    + destruct (mvt_le F f x0 x Hxx) as [c [Hc Hq]].
      { intros z Hz. apply Hd. lra. }
      exists ((c, x) :: l'). simpl. repeat split; try lra; try assumption.
      apply (Rmult_le_compat_r (x - x0)) in Hq; [|lra].
      unfold Rdiv in Hq. rewrite Rmult_assoc, Rinv_l in Hq by lra. lra.
Qed.

Theorem FTC_value : forall F f a b I, RInt f a b I ->
  (forall x, a <= x <= b -> derivable_pt_lim F x (f x)) -> I = F b - F a.
Proof.
  intros F f a b I [Hab HI] Hd. apply close_eq. intros e He.
  destruct (HI e He) as [d [Hdp H]].
  destruct (exists_fine a b d Hab Hdp) as [l [Hl Hf]].
  destruct (retag_ge F f a b d Hd l a (Rle_refl a) Hl Hf) as [l1 [A1 [A2 A3]]].
  destruct (retag_le F f a b d Hd l a (Rle_refl a) Hl Hf) as [l2 [B1 [B2 B3]]].
  pose proof (H l1 A1 A2) as K1. pose proof (H l2 B1 B2) as K2.
  apply abs_lt_elim in K1, K2. apply abs_lt_intro; lra.
Qed.

(* FTC, existence form: uniformly continuous integrands. *)
Lemma ftc_sum : forall F f a b e1 d,
  (forall x, a <= x <= b -> derivable_pt_lim F x (f x)) ->
  (forall x y, a <= x <= b -> a <= y <= b -> Rabs (x - y) < d -> Rabs (f x - f y) < e1) ->
  forall l x0, a <= x0 -> tpart x0 b l -> fine d x0 l ->
  Rabs (tsum f x0 l - (F b - F x0)) <= e1 * (b - x0).
Proof.
  intros F f a b e1 d Hd Huc l. induction l as [|[t x] l IH]; intros x0 Hax0 Hl Hf.
  - simpl in Hl. subst x0. simpl.
    replace (0 - (F b - F b)) with 0 by ring. replace (b - b) with 0 by ring.
    rewrite Rabs_R0. lra.
  - destruct Hl as [H1 [H2 H3]]. destruct Hf as [Hf1 Hf2].
    pose proof (tpart_le _ _ _ H3) as Hxb.
    specialize (IH x ltac:(lra) H3 Hf2).
    assert (Hcell : Rabs ((F x - f t * x) - (F x0 - f t * x0)) <= e1 * (x - x0)).
    { apply (mvi_abs (fun y => F y - f t * y) (fun y => f y - f t) x0 x e1 ltac:(lra)).
      - intros z Hz. apply dpl_sub_lin. apply Hd. lra.
      - intros z Hz. left. apply Huc; try lra. apply abs_lt_intro; lra. }
    simpl. apply abs_le_elim in IH, Hcell. apply abs_le_intro; nra.
Qed.

Theorem FTC : forall F f a b, a <= b ->
  (forall x, a <= x <= b -> derivable_pt_lim F x (f x)) -> UC f a b ->
  RInt f a b (F b - F a).
Proof.
  intros F f a b Hab Hd Huc. split; [exact Hab|]. intros e He.
  set (e1 := e / (b - a + 1)).
  assert (He1 : 0 < e1) by (unfold e1; apply Rdiv_lt_0_compat; lra).
  assert (E1 : e1 * (b - a + 1) = e) by (unfold e1; field; lra).
  destruct (Huc e1 He1) as [d [Hdp Hdd]].
  exists d. split; [exact Hdp|]. intros l Hl Hf.
  pose proof (ftc_sum F f a b e1 d Hd Hdd l a (Rle_refl a) Hl Hf). nra.
Qed.

Corollary FTC_Lip : forall F f a b L, a <= b ->
  (forall x, a <= x <= b -> derivable_pt_lim F x (f x)) -> Lip f a b L ->
  RInt f a b (F b - F a).
Proof. intros F f a b L Hab Hd HL. apply FTC; [exact Hab|exact Hd|]. eapply Lip_UC; exact HL. Qed.

(* "continuously differentiable" in the form used below: the integrand has
   a derivative bounded on [a, b] *)
Corollary FTC_C1 : forall F f f' a b L, a <= b ->
  (forall x, a <= x <= b -> derivable_pt_lim F x (f x)) ->
  (forall x, a <= x <= b -> derivable_pt_lim f x (f' x)) ->
  (forall x, a <= x <= b -> Rabs (f' x) <= L) ->
  RInt f a b (F b - F a).
Proof.
  intros F f f' a b L Hab HF Hf HL. apply (FTC_Lip F f a b L Hab HF).
  apply (Lip_of_deriv f f'); assumption.
Qed.

(* ===================================================================== *)
(* Part 6: change of variables; improper integrals over [a, oo)           *)
(* ===================================================================== *)

(* derivative combinators in lambda form *)
Lemma dpl_plus : forall f g x l1 l2, derivable_pt_lim f x l1 -> derivable_pt_lim g x l2 ->
  derivable_pt_lim (fun y => f y + g y) x (l1 + l2).
Proof. intros. exact (derivable_pt_lim_plus f g x l1 l2 H H0). Qed.

Lemma dpl_minus : forall f g x l1 l2, derivable_pt_lim f x l1 -> derivable_pt_lim g x l2 ->
  derivable_pt_lim (fun y => f y - g y) x (l1 - l2).
Proof. intros. exact (derivable_pt_lim_minus f g x l1 l2 H H0). Qed.

Lemma dpl_mult : forall f g x l1 l2, derivable_pt_lim f x l1 -> derivable_pt_lim g x l2 ->
  derivable_pt_lim (fun y => f y * g y) x (l1 * g x + f x * l2).
Proof. intros. exact (derivable_pt_lim_mult f g x l1 l2 H H0). Qed.

Lemma dpl_scal : forall c f x l, derivable_pt_lim f x l ->
  derivable_pt_lim (fun y => c * f y) x (c * l).
Proof. intros. exact (derivable_pt_lim_scal f c x l H). Qed.

Lemma dpl_opp : forall f x l, derivable_pt_lim f x l -> derivable_pt_lim (fun y => - f y) x (- l).
Proof. intros. exact (derivable_pt_lim_opp f x l H). Qed.

Lemma dpl_lin : forall c x, derivable_pt_lim (fun y => c * y) x c.
Proof.
  intros c x. apply (dpl_ext (fun y => c * id y) _ _ (c * 1)); [reflexivity|ring|].
  apply dpl_scal. apply derivable_pt_lim_id.
Qed.

Lemma dpl_comp' : forall f1 f2 x l1 l2, derivable_pt_lim f1 x l1 ->
  derivable_pt_lim f2 (f1 x) l2 -> derivable_pt_lim (fun y => f2 (f1 y)) x (l2 * l1).
Proof. intros. exact (derivable_pt_lim_comp f1 f2 x l1 l2 H H0). Qed.

(* change of variables: int_A^B f = int_a^b f(phi u) phi'(u) du, for f with
   an antiderivative on [A, B] = [phi a, phi b] *)
Theorem RInt_change_var : forall f F phi phi' a b A B I J,
  phi a = A -> phi b = B ->
  (forall u, a <= u <= b -> derivable_pt_lim phi u (phi' u)) ->
  (forall u, a <= u <= b -> A <= phi u <= B) ->
  (forall y, A <= y <= B -> derivable_pt_lim F y (f y)) ->
  RInt f A B I -> RInt (fun u => f (phi u) * phi' u) a b J -> I = J.
Proof.
  intros f F phi phi' a b A B I J HA HB Hphi Hmap HF HI HJ.
  rewrite (FTC_value F f A B I HI HF).
  rewrite (FTC_value (fun u => F (phi u)) _ a b J HJ).
  - rewrite <- HA, <- HB. reflexivity.
  - intros u Hu. apply dpl_comp'; [apply Hphi; exact Hu|apply HF, Hmap; exact Hu].
Qed.

(* ... and both sides exist when the two integrands are uniformly continuous *)
Theorem RInt_change_var_FTC : forall f F phi phi' a b A B,
  a <= b -> A <= B -> phi a = A -> phi b = B ->
  (forall u, a <= u <= b -> derivable_pt_lim phi u (phi' u)) ->
  (forall u, a <= u <= b -> A <= phi u <= B) ->
  (forall y, A <= y <= B -> derivable_pt_lim F y (f y)) ->
  UC f A B -> UC (fun u => f (phi u) * phi' u) a b ->
  RInt f A B (F B - F A) /\ RInt (fun u => f (phi u) * phi' u) a b (F B - F A).
Proof.
  intros f F phi phi' a b A B Hab HAB HA HB Hphi Hmap HF Uf Ug. split.
  - apply FTC; assumption.
  - rewrite <- HA, <- HB. apply (FTC (fun u => F (phi u))); [exact Hab| |exact Ug].
    intros u Hu. apply dpl_comp'; [apply Hphi; exact Hu|apply HF, Hmap; exact Hu].
Qed.

(* the improper integral over [a, oo): limit of int_a^T as T -> oo *)
Definition RIntInf (f : R -> R) (a I : R) : Prop :=
  forall eps, 0 < eps -> exists T0, a <= T0 /\ forall T, T0 <= T ->
    exists J, RInt f a T J /\ Rabs (J - I) < eps.

Theorem RIntInf_unique : forall f a I J, RIntInf f a I -> RIntInf f a J -> I = J.
Proof.
  intros f a I J HI HJ. apply close_eq. intros e He.
  destruct (HI (e / 2) ltac:(lra)) as [T1 [_ H1]].
  destruct (HJ (e / 2) ltac:(lra)) as [T2 [_ H2]].
  destruct (H1 (Rmax T1 T2) (Rmax_l _ _)) as [J1 [K1 L1]].
  destruct (H2 (Rmax T1 T2) (Rmax_r _ _)) as [J2 [K2 L2]].
  rewrite (RInt_unique _ _ _ _ _ K1 K2) in L1.
  apply abs_lt_elim in L1, L2. apply abs_lt_intro; lra.
Qed.

Theorem RIntInf_plus : forall f g a I J, RIntInf f a I -> RIntInf g a J ->
  RIntInf (fun x => f x + g x) a (I + J).
Proof.
  intros f g a I J HI HJ e He.
  destruct (HI (e / 2) ltac:(lra)) as [T1 [A1 H1]].
  destruct (HJ (e / 2) ltac:(lra)) as [T2 [A2 H2]].
  exists (Rmax T1 T2). split; [eapply Rle_trans; [exact A1|apply Rmax_l]|]. intros T HT.
  destruct (H1 T (Rle_trans _ _ _ (Rmax_l _ _) HT)) as [J1 [K1 L1]].
  destruct (H2 T (Rle_trans _ _ _ (Rmax_r _ _) HT)) as [J2 [K2 L2]].
  exists (J1 + J2). split; [apply RInt_plus; assumption|].
  apply abs_lt_elim in L1, L2. apply abs_lt_intro; lra.
Qed.

Theorem RIntInf_scal : forall c f a I, RIntInf f a I -> RIntInf (fun x => c * f x) a (c * I).
Proof.
  intros c f a I HI e He.
  set (q := e / (Rabs c + 1)).
  assert (Hc : 0 <= Rabs c) by apply Rabs_pos.
  assert (Hq : 0 < q) by (unfold q; apply Rdiv_lt_0_compat; lra).
  assert (Eq : q * (Rabs c + 1) = e) by (unfold q; field; lra).
  destruct (HI q Hq) as [T0 [A0 H0]]. exists T0. split; [exact A0|]. intros T HT.
  destruct (H0 T HT) as [J [K L]]. exists (c * J). split; [apply RInt_scal; exact K|].
  replace (c * J - c * I) with (c * (J - I)) by ring.
  rewrite Rabs_mult. pose proof (Rabs_pos (J - I)). nra.
Qed.

Theorem RIntInf_le : forall f g a I J, RIntInf f a I -> RIntInf g a J ->
  (forall x, a <= x -> f x <= g x) -> I <= J.
Proof.
  intros f g a I J HI HJ Hfg. apply close_le. intros e He.
  destruct (HI (e / 2) ltac:(lra)) as [T1 [_ H1]].
  destruct (HJ (e / 2) ltac:(lra)) as [T2 [_ H2]].
  destruct (H1 (Rmax T1 T2) (Rmax_l _ _)) as [J1 [K1 L1]].
  destruct (H2 (Rmax T1 T2) (Rmax_r _ _)) as [J2 [K2 L2]].
  pose proof (RInt_le f g a (Rmax T1 T2) J1 J2 K1 K2 (fun x Hx => Hfg x (proj1 Hx))).
  apply abs_lt_elim in L1, L2. lra.
Qed.

(* splitting off a finite interval:  int_a^oo = int_a^b + int_b^oo *)
Theorem RIntInf_chasles : forall f a b I1 I2,
  (forall T, b <= T -> exists M, forall x, a <= x <= T -> Rabs (f x) <= M) ->
  RInt f a b I1 -> RIntInf f b I2 -> RIntInf f a (I1 + I2).
Proof.
  intros f a b I1 I2 Hloc H1 H2 e He.
  pose proof (RInt_le_ab _ _ _ _ H1) as Hab.
  destruct (H2 e He) as [T0 [A0 K0]]. exists T0. split; [lra|]. intros T HT.
  destruct (K0 T HT) as [J [KJ LJ]]. destruct (Hloc T ltac:(lra)) as [M HM].
  exists (I1 + J). split; [apply (RInt_chasles f a b T M); assumption|].
  replace (I1 + J - (I1 + I2)) with (J - I2) by ring. exact LJ.
Qed.

(* an improper integral from an antiderivative with a limit at oo *)
Lemma RIntInf_of_antideriv : forall f G a L,
  (forall T, a <= T -> RInt f a T (G T - G a)) ->
  (forall e, 0 < e -> exists T0, a <= T0 /\ forall T, T0 <= T -> Rabs (G T - L) < e) ->
  RIntInf f a (L - G a).
Proof.
  intros f G a L HR HL e He. destruct (HL e He) as [T0 [A0 K0]].
  exists T0. split; [exact A0|]. intros T HT. exists (G T - G a). split; [apply HR; lra|].
  replace (G T - G a - (L - G a)) with (G T - L) by ring. apply K0. exact HT.
Qed.

(* ===================================================================== *)
(* Part 7: the clean logarithm is an antiderivative of 1/y                *)
(* ===================================================================== *)

Lemma Lc_mult : forall x y, 0 < x -> 0 < y -> Lc (x * y) = Lc x + Lc y.
Proof.
  intros x y Hx Hy. apply exp_inj. rewrite exp_plus, !exp_Lc; [reflexivity|exact Hy|exact Hx|].
  apply Rmult_lt_0_compat; assumption.
Qed.

(* Lc'(y) = 1/y, from  h/(y+h) <= Lc(y+h) - Lc y <= h/y  (Lc z <= z - 1) *)
Theorem Lc_deriv : forall y, 0 < y -> derivable_pt_lim Lc y (/ y).
Proof.
  intros y Hy e He.
  assert (Hyy : 0 < y * y) by nra.
  set (d := Rmin (y / 2) (e * (y * y) / 2)).
  assert (Hd : 0 < d).
  { unfold d. apply Rmin_pos; [lra|]. apply Rdiv_lt_0_compat; [nra|lra]. }
  exists (mkposreal d Hd). intros h Hh Hhd. simpl in Hhd.
  assert (Hh1 : Rabs h < y / 2) by (eapply Rlt_le_trans; [exact Hhd|apply Rmin_l]).
  assert (Hh2 : Rabs h < e * (y * y) / 2) by (eapply Rlt_le_trans; [exact Hhd|apply Rmin_r]).
  pose proof (abs_lt_elim _ _ Hh1) as [Hh1a Hh1b].
  assert (Hyh : 0 < y + h) by lra.
  assert (Up : Lc (y + h) - Lc y <= h / y).
  { assert (E : Lc (y + h) = Lc y + Lc ((y + h) / y)).
    { rewrite <- Lc_mult by (try apply Rdiv_lt_0_compat; lra). f_equal. field. lra. }
    pose proof (Lc_le_sub1 ((y + h) / y) ltac:(apply Rdiv_lt_0_compat; lra)) as H.
    replace ((y + h) / y - 1) with (h / y) in H by (field; lra). lra. }
  assert (Lo : h / (y + h) <= Lc (y + h) - Lc y).
  { assert (E : Lc y = Lc (y + h) + Lc (y / (y + h))).
    { rewrite <- Lc_mult by (try apply Rdiv_lt_0_compat; lra). f_equal. field. lra. }
    pose proof (Lc_le_sub1 (y / (y + h)) ltac:(apply Rdiv_lt_0_compat; lra)) as H.
    replace (y / (y + h) - 1) with (- (h / (y + h))) in H by (field; lra). lra. }
  set (D := Lc (y + h) - Lc y) in *.
  set (w := D - h / y).
  set (P := y * (y + h)).
  assert (HP : 0 < P) by (unfold P; nra).
  assert (Hw1 : w <= 0) by (unfold w; lra).
  assert (Hw2 : - (h * h) <= w * P).
  { assert (E : (h / (y + h) - h / y) * P = - (h * h)) by (unfold P; field; lra).
    rewrite <- E. apply Rmult_le_compat_r; [lra|unfold w; lra]. }
  assert (HhP : Rabs h < e * P).
  { unfold P. pose proof (Rabs_pos h). nra. }
  replace (D / h - / y) with (w / h) by (unfold w; field; lra).
  unfold Rdiv. rewrite Rabs_mult, Rabs_inv.
  assert (Hah : 0 < Rabs h) by (apply Rabs_pos_lt; exact Hh).
  rewrite (Rabs_left1 w) by exact Hw1.
  (* - w <= h^2 / P and h^2 = |h|^2 < e |h| P *)
  assert (Hsq : h * h = Rabs h * Rabs h) by (rewrite <- Rabs_mult; symmetry; apply Rabs_right; nra).
  apply (Rmult_lt_reg_r (Rabs h)); [exact Hah|].
  rewrite Rmult_assoc, Rinv_l by lra. rewrite Rmult_1_r.
  apply (Rmult_lt_reg_r P); [exact HP|]. nra.
Qed.

(* ===================================================================== *)
(* Part 8: the window integral of windowHyp_of_rpow                       *)
(* ===================================================================== *)

Lemma inv_Lip : forall Y B, 1 <= Y -> Lip (fun y => / y) Y B 1.
Proof.
  intros Y B HY x z Hx Hz.
  replace (/ x - / z) with ((z - x) * / (x * z)) by (field; lra).
  assert (Hxz : 1 <= x * z) by nra.
  assert (Hk : 0 < / (x * z)) by (apply Rinv_0_lt_compat; lra).
  assert (Ek : / (x * z) * (x * z) = 1) by (field; lra).
  rewrite Rabs_mult, (Rabs_right (/ (x * z))) by lra. rewrite (Rabs_minus_sym z x).
  pose proof (Rabs_pos (x - z)). nra.
Qed.

Lemma window_le : forall Y delta, 1 <= Y -> 0 <= delta -> Y <= rpc Y (1 + delta).
Proof.
  intros Y delta HY Hd. pose proof (rpc_mono_exp Y 1 (1 + delta) HY ltac:(lra)) as H.
  rewrite rpc_one in H by lra. exact H.
Qed.

(* int_Y^(Y^(1+delta)) dy / y = delta * log Y *)
Theorem window_integral : forall Y delta, 1 <= Y -> 0 <= delta ->
  RInt (fun y => / y) Y (rpc Y (1 + delta)) (delta * Lc Y).
Proof.
  intros Y delta HY Hd.
  replace (delta * Lc Y) with (Lc (rpc Y (1 + delta)) - Lc Y) by (rewrite Lc_rpc; ring).
  apply (FTC_Lip Lc (fun y => / y) Y (rpc Y (1 + delta)) 1 (window_le Y delta HY Hd)).
  - intros x Hx. apply Lc_deriv. lra.
  - apply inv_Lip. exact HY.
Qed.

(* the integrand of windowHyp_of_rpow:  R y * y^(-theta-1)  with  R y = y^theta *)
Theorem window_integral_rpow : forall Y theta delta, 1 <= Y -> 0 <= delta ->
  RInt (fun y => rpc y theta * rpc y (- theta - 1)) Y (rpc Y (1 + delta)) (delta * Lc Y).
Proof.
  intros Y theta delta HY Hd.
  apply (RInt_ext (fun y => / y)); [|apply window_integral; assumption].
  intros y Hy. rewrite <- rpc_add. replace (theta + (- theta - 1)) with (-1) by ring.
  unfold rpc. replace (-1 * Lc y) with (- Lc y) by ring.
  rewrite exp_Ropp, exp_Lc by lra. reflexivity.
Qed.

(* y = e^u maps [Lc Y, (1+delta) Lc Y] onto [Y, Y^(1+delta)] *)
Lemma exp_window_map : forall Y delta u, 1 <= Y ->
  Lc Y <= u <= (1 + delta) * Lc Y -> Y <= exp u <= rpc Y (1 + delta).
Proof.
  intros Y delta u HY [H1 H2]. split.
  - rewrite <- (exp_Lc Y) at 1 by lra. apply exp_le_mono. exact H1.
  - unfold rpc. apply exp_le_mono. exact H2.
Qed.

(* the same value through the change of variables y = e^u:
   int_Y^(Y^(1+delta)) dy/y = int_(Lc Y)^((1+delta) Lc Y) 1 du *)
Theorem window_integral_by_cv : forall Y delta I, 1 <= Y -> 0 <= delta ->
  RInt (fun y => / y) Y (rpc Y (1 + delta)) I -> I = delta * Lc Y.
Proof.
  intros Y delta I HY Hd HI.
  assert (HL : 0 <= Lc Y) by (apply Lc_nonneg; exact HY).
  assert (HJ : RInt (fun u => / exp u * exp u) (Lc Y) ((1 + delta) * Lc Y) (delta * Lc Y)).
  { apply (RInt_ext (fun _ => 1)).
    - intros u _. field. apply Rgt_not_eq, exp_pos.
    - replace (delta * Lc Y) with (1 * ((1 + delta) * Lc Y - Lc Y)) by ring.
      apply RInt_const. nra. }
  apply (RInt_change_var (fun y => / y) Lc exp exp (Lc Y) ((1 + delta) * Lc Y)
           Y (rpc Y (1 + delta)) I (delta * Lc Y)).
  - apply exp_Lc. lra.
  - reflexivity.
  - intros u _. apply derivable_pt_lim_exp.
  - intros u Hu. apply exp_window_map; assumption.
  - intros y Hy. apply Lc_deriv. lra.
  - exact HI.
  - exact HJ.
Qed.

(* the change-of-variables identity of windowHypU_of_windowHyp, for a
   majorant R whose y-integrand has an antiderivative on the window:
   int_Y^(Y^(1+delta)) R y y^(-theta-1) dy
     = int_(Lc Y)^((1+delta) Lc Y) R(e^u) e^(-theta u) du *)
Theorem windowU_change_var : forall (Rm Fm : R -> R) theta Y delta I J,
  1 <= Y ->
  (forall y, Y <= y <= rpc Y (1 + delta) -> derivable_pt_lim Fm y (Rm y * rpc y (- theta - 1))) ->
  RInt (fun y => Rm y * rpc y (- theta - 1)) Y (rpc Y (1 + delta)) I ->
  RInt (fun u => Rm (exp u) * exp (- theta * u)) (Lc Y) ((1 + delta) * Lc Y) J ->
  I = J.
Proof.
  intros Rm Fm theta Y delta I J HY HF HI HJ.
  apply (RInt_change_var (fun y => Rm y * rpc y (- theta - 1)) Fm exp exp (Lc Y) ((1 + delta) * Lc Y)
           Y (rpc Y (1 + delta)) I J).
  - apply exp_Lc. lra.
  - reflexivity.
  - intros u _. apply derivable_pt_lim_exp.
  - intros u Hu. apply exp_window_map; assumption.
  - exact HF.
  - exact HI.
  - apply (RInt_ext (fun u => Rm (exp u) * exp (- theta * u))); [|exact HJ].
    intros u _. unfold rpc. rewrite Lc_exp. rewrite Rmult_assoc, <- exp_plus.
    f_equal. f_equal. ring.
Qed.

(* ===================================================================== *)
(* Part 9: kernel_integral                                                *)
(* ===================================================================== *)

(* P_k x = sum_(j <= k) x^j / j! *)
Definition Pk (k : nat) (x : R) : R := sum_f_R0 (fun j => x ^ j / INR (fact j)) k.

Lemma Pk_S : forall k x, Pk (S k) x = Pk k x + x ^ S k / INR (fact (S k)).
Proof. reflexivity. Qed.

Lemma Pk_O : forall x, Pk 0 x = 1.
Proof. intro x. unfold Pk. simpl. field. Qed.

Lemma Pk_at0 : forall k, Pk k 0 = 1.
Proof.
  induction k as [|k IH]; [apply Pk_O|]. rewrite Pk_S, IH. simpl. unfold Rdiv. ring.
Qed.

Lemma fact_ge1 : forall n, 1 <= INR (fact n).
Proof.
  intro n. pose proof (lt_O_fact n) as H. apply le_INR in H. simpl in H. exact H.
Qed.

Lemma div_fact_le : forall z n, 0 <= z -> z / INR (fact n) <= z.
Proof.
  intros z n Hz. pose proof (fact_ge1 n) as H1.
  assert (Hq : 0 < / INR (fact n)) by (apply Rinv_0_lt_compat; lra).
  assert (Eq : / INR (fact n) * INR (fact n) = 1) by (field; lra).
  unfold Rdiv. nra.
Qed.

Lemma Pk_nonneg : forall k x, 0 <= x -> 0 <= Pk k x.
Proof.
  induction k as [|k IH]; intros x Hx; [rewrite Pk_O; lra|].
  rewrite Pk_S. pose proof (IH x Hx). pose proof (fact_ge1 (S k)).
  assert (0 <= x ^ S k / INR (fact (S k)))
    by (apply Rmult_le_pos; [apply pow_le; exact Hx|left; apply Rinv_0_lt_compat; lra]).
  lra.
Qed.

(* P_k' = P_k - x^k / k! *)
Lemma Pk_deriv : forall k x, derivable_pt_lim (Pk k) x (Pk k x - x ^ k / INR (fact k)).
Proof.
  induction k as [|k IH]; intro x.
  - apply (dpl_ext (fun _ => 1) _ _ 0).
    + intro y. symmetry. apply Pk_O.
    + rewrite Pk_O. simpl. field.
    + apply derivable_pt_lim_const.
  - apply (dpl_ext (fun y => Pk k y + / INR (fact (S k)) * y ^ S k) _ _
             ((Pk k x - x ^ k / INR (fact k)) + / INR (fact (S k)) * (INR (S k) * x ^ pred (S k)))).
    + intro y. rewrite Pk_S. unfold Rdiv. ring.
    + rewrite Pk_S. cbn [pred]. rewrite fact_simpl, mult_INR.
      pose proof (fact_ge1 k). assert (INR (S k) <> 0) by (apply not_0_INR; lia).
      field. split; lra.
    + apply dpl_plus; [apply IH|]. apply dpl_scal. apply derivable_pt_lim_pow.
Qed.

(* e^x >= P_k x on [0, oo) *)
Lemma exp_ge_Pk : forall k x, 0 <= x -> Pk k x <= exp x.
Proof.
  induction k as [|k IH]; intros x Hx.
  - assert (H : exp 0 - Pk 0 0 <= exp x - Pk 0 x).
    { apply (deriv_nonneg_incr (fun z => exp z - Pk 0 z)
               (fun z => exp z - (Pk 0 z - z ^ 0 / INR (fact 0))) 0 x Hx).
      - intros z _. apply dpl_minus; [apply derivable_pt_lim_exp|apply Pk_deriv].
      - intros z _. rewrite Pk_O. simpl. pose proof (exp_pos z).
        replace (1 - 1 / 1) with 0 by field. lra. }
    rewrite exp_0, Pk_at0 in H. lra.
  - assert (H : exp 0 - Pk (S k) 0 <= exp x - Pk (S k) x).
    { apply (deriv_nonneg_incr (fun z => exp z - Pk (S k) z)
               (fun z => exp z - (Pk (S k) z - z ^ S k / INR (fact (S k)))) 0 x Hx).
      - intros z _. apply dpl_minus; [apply derivable_pt_lim_exp|apply Pk_deriv].
      - intros z Hz. rewrite Pk_S. pose proof (IH z (proj1 Hz)). lra. }
    rewrite exp_0, Pk_at0 in H. lra.
Qed.

Lemma Pk_le_poly : forall k x, 1 <= x -> Pk k x <= INR (S k) * x ^ k.
Proof.
  induction k as [|k IH]; intros x Hx.
  - rewrite Pk_O. simpl. lra.
  - rewrite Pk_S. pose proof (IH x Hx).
    assert (Hk : 1 <= x ^ k) by (apply pow_R1_Rle; exact Hx).
    assert (HSk : x ^ S k = x * x ^ k) by reflexivity.
    pose proof (div_fact_le (x ^ S k) (S k) ltac:(rewrite HSk; nra)).
    rewrite (S_INR (S k)). rewrite HSk in *. pose proof (pos_INR (S k)).
    assert (INR (S k) * x ^ k <= INR (S k) * (x * x ^ k)) by (apply Rmult_le_compat_l; nra).
    lra.
Qed.

(* e^(-x) P_k x <= (k+1) (k+1)! / x  for x >= 1 *)
Lemma exp_Pk_decay : forall k x, 1 <= x ->
  exp (- x) * Pk k x <= INR (S k) * INR (fact (S k)) / x.
Proof.
  intros k x Hx.
  set (C := INR (S k) * INR (fact (S k))).
  assert (HE : 0 < exp x) by apply exp_pos.
  assert (HF : 1 <= INR (fact (S k))) by apply fact_ge1.
  assert (HS : 0 < INR (S k)) by (apply lt_0_INR; lia).
  assert (Hpow : x ^ S k <= INR (fact (S k)) * exp x).
  { pose proof (exp_ge_Pk (S k) x ltac:(lra)) as H. rewrite Pk_S in H.
    pose proof (Pk_nonneg k x ltac:(lra)).
    assert (E : x ^ S k = INR (fact (S k)) * (x ^ S k / INR (fact (S k)))) by (field; lra).
    rewrite E. apply Rmult_le_compat_l; lra. }
  assert (Key : Pk k x * x <= C * exp x).
  { pose proof (Pk_le_poly k x Hx).
    assert (E : x ^ S k = x * x ^ k) by reflexivity.
    assert (0 <= x ^ k) by (apply pow_le; lra).
    unfold C. nra. }
  replace (exp (- x) * Pk k x) with ((Pk k x * x) * (/ exp x * / x))
    by (rewrite exp_Ropp; field; split; lra).
  replace (C / x) with ((C * exp x) * (/ exp x * / x)) by (field; split; lra).
  apply Rmult_le_compat_r; [|exact Key].
  apply Rmult_le_pos; left; apply Rinv_0_lt_compat; lra.
Qed.

(* the kernel and its antiderivative *)
Definition gk (k : nat) (a u : R) : R := u ^ k * exp (- (a * u)) / INR (fact k).
Definition Gk (k : nat) (a u : R) : R := - / a ^ S k * (exp (- (a * u)) * Pk k (a * u)).

Lemma Gk_deriv : forall k a u, 0 < a -> derivable_pt_lim (Gk k a) u (gk k a u).
Proof.
  intros k a u Ha.
  assert (HE : derivable_pt_lim (fun v => exp (- (a * v))) u (exp (- (a * u)) * - a)).
  { apply (dpl_comp' (fun v => - (a * v)) exp u (- a) (exp (- (a * u)))).
    - apply dpl_opp. apply dpl_lin.
    - apply derivable_pt_lim_exp. }
  assert (HQ : derivable_pt_lim (fun v => Pk k (a * v)) u
                 ((Pk k (a * u) - (a * u) ^ k / INR (fact k)) * a)).
  { apply (dpl_comp' (fun v => a * v) (Pk k) u a). apply dpl_lin. apply Pk_deriv. }
  pose proof (dpl_scal (- / a ^ S k) _ u _ (dpl_mult _ _ u _ _ HE HQ)) as H.
  refine (dpl_ext _ _ u _ _ _ _ H); [intro y; reflexivity|].
  cbv beta. unfold gk. rewrite Rpow_mult_distr. replace (a ^ S k) with (a * a ^ k) by reflexivity.
  pose proof (fact_ge1 k). assert (a ^ k <> 0) by (apply pow_nonzero; lra).
  field. repeat split; lra.
Qed.

Lemma Gk_0 : forall k a, Gk k a 0 = - / a ^ S k.
Proof. intros k a. unfold Gk. rewrite Rmult_0_r, Ropp_0, exp_0, Pk_at0. ring. Qed.

(* the kernel has a bounded derivative on [0, T] *)
Lemma gk_deriv : forall k a u, derivable_pt_lim (gk k a) u
  ((INR k * u ^ pred k - a * u ^ k) * exp (- (a * u)) / INR (fact k)).
Proof.
  intros k a u.
  assert (HE : derivable_pt_lim (fun v => exp (- (a * v))) u (exp (- (a * u)) * - a)).
  { apply (dpl_comp' (fun v => - (a * v)) exp u (- a) (exp (- (a * u)))).
    - apply dpl_opp. apply dpl_lin.
    - apply derivable_pt_lim_exp. }
  pose proof (dpl_scal (/ INR (fact k)) _ u _ (dpl_mult _ _ u _ _ (derivable_pt_lim_pow u k) HE)) as H.
  pose proof (fact_ge1 k).
  refine (dpl_ext _ _ u _ _ _ _ H); [intro y; cbv beta; unfold gk; field; lra|].
  field. lra.
Qed.

Lemma gk_deriv_bound : forall k a T u, 0 < a -> 0 <= u <= T ->
  Rabs ((INR k * u ^ pred k - a * u ^ k) * exp (- (a * u)) / INR (fact k))
    <= INR k * T ^ pred k + a * T ^ k.
Proof.
  intros k a T u Ha Hu.
  pose proof (fact_ge1 k) as HK.
  assert (HA : 0 <= INR k * u ^ pred k <= INR k * T ^ pred k).
  { pose proof (pos_INR k). split; [apply Rmult_le_pos; [lra|apply pow_le; lra]|].
    apply Rmult_le_compat_l; [lra|apply pow_incr; lra]. }
  assert (HB : 0 <= a * u ^ k <= a * T ^ k).
  { split; [apply Rmult_le_pos; [lra|apply pow_le; lra]|].
    apply Rmult_le_compat_l; [lra|apply pow_incr; lra]. }
  assert (HE : 0 < exp (- (a * u)) <= 1).
  { split; [apply exp_pos|]. rewrite <- exp_0. apply exp_le_mono. nra. }
  set (X := exp (- (a * u)) / INR (fact k)).
  assert (HX : 0 < X <= 1).
  { unfold X. split; [apply Rdiv_lt_0_compat; lra|].
    apply (Rmult_le_reg_r (INR (fact k))); [lra|]. field_simplify; lra. }
  replace ((INR k * u ^ pred k - a * u ^ k) * exp (- (a * u)) / INR (fact k))
    with ((INR k * u ^ pred k - a * u ^ k) * X) by (unfold X, Rdiv; ring).
  apply abs_le_intro; nra.
Qed.

Lemma kernel_RInt : forall k a T, 0 < a -> 0 <= T ->
  RInt (gk k a) 0 T (Gk k a T - Gk k a 0).
Proof.
  intros k a T Ha HT.
  apply (FTC_C1 (Gk k a) (gk k a)
           (fun u => (INR k * u ^ pred k - a * u ^ k) * exp (- (a * u)) / INR (fact k))
           0 T (INR k * T ^ pred k + a * T ^ k) HT).
  - intros x _. apply Gk_deriv. exact Ha.
  - intros x _. apply gk_deriv.
  - intros x Hx. apply gk_deriv_bound; assumption.
Qed.

(* kernel_integral (LandauTheorems/kernelIntegral):
     int_0^oo u^k e^(-a u) / k! du = a^(-(k+1))   for a > 0 *)
Theorem kernel_integral : forall k a, 0 < a ->
  RIntInf (fun u => u ^ k * exp (- (a * u)) / INR (fact k)) 0 (/ a ^ S k).
Proof.
  intros k a Ha.
  assert (Hc : 0 < / a ^ S k) by (apply Rinv_0_lt_compat, pow_lt; exact Ha).
  replace (/ a ^ S k) with (0 - Gk k a 0) by (rewrite Gk_0; ring).
  apply (RIntInf_of_antideriv _ (Gk k a) 0 0).
  - intros T HT. exact (kernel_RInt k a T Ha HT).
  - intros e He.
    set (c := / a ^ S k) in *. set (C := INR (S k) * INR (fact (S k))).
    assert (HC : 0 < C).
    { unfold C. apply Rmult_lt_0_compat; [apply lt_0_INR; lia|pose proof (fact_ge1 (S k)); lra]. }
    assert (Hce : 0 <= c * C / e) by (apply Rmult_le_pos; [nra|left; apply Rinv_0_lt_compat; lra]).
    exists ((c * C / e + 1) / a). split; [apply Rmult_le_pos; [lra|left; apply Rinv_0_lt_compat; lra]|].
    intros T HT.
    assert (Hx : c * C / e + 1 <= a * T).
    { apply (Rmult_le_compat_l a) in HT; [|lra].
      replace (a * ((c * C / e + 1) / a)) with (c * C / e + 1) in HT by (field; lra). exact HT. }
    assert (Hx1 : 1 <= a * T) by lra.
    pose proof (exp_Pk_decay k (a * T) Hx1) as Hdec. fold C in Hdec.
    pose proof (Pk_nonneg k (a * T) ltac:(lra)) as HP. pose proof (exp_pos (- (a * T))) as HEp.
    unfold Gk. fold c. rewrite Rminus_0_r.
    rewrite Rabs_left1 by (assert (0 <= exp (- (a * T)) * Pk k (a * T)) by nra; nra).
    assert (HcC : c * C / (a * T) < e).
    { apply (Rmult_lt_reg_r (a * T)); [lra|]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra.
      replace (c * C) with (c * C / e * e) by (field; lra). nra. }
    assert (Hb : c * (exp (- (a * T)) * Pk k (a * T)) <= c * (C / (a * T)))
      by (apply Rmult_le_compat_l; lra).
    unfold Rdiv in HcC, Hb. nra.
Qed.

(* ===================================================================== *)
(* Part 10: windowHyp_of_rpow over R                                      *)
(* ===================================================================== *)

(* WindowHyp F theta delta (CharFamily.lean), with the window integral an
   RInt (integrability = existence of the value):  for every eta > 0 there
   are arbitrarily large Y and a majorant R of Gm on [Y, Y^(1+delta)] with
   int_Y^(Y^(1+delta)) R y * y^(-theta-1) dy <= Y^eta. *)
Definition WindowHypR (Gm : R -> R) (theta delta : R) : Prop :=
  forall eta, 0 < eta -> forall Y0, exists Y, Y0 <= Y /\ exists (Rm : R -> R),
    (forall y, Y <= y -> y <= rpc Y (1 + delta) -> 0 <= Rm y /\ Gm y <= Rm y) /\
    exists I, RInt (fun y => Rm y * rpc y (- theta - 1)) Y (rpc Y (1 + delta)) I /\
      I <= rpc Y eta.

(* windowHyp_of_rpow (LandauTheorems/WindowHypOfRpow.lean): the majorant
   R y = |C| y^theta has window integral |C| delta log Y (window_integral_rpow),
   and |C| delta log Y <= Y^eta eventually (windowHyp_of_rpow_eventually,
   AlpogeRealsQED2.v).  This is the hypothesis WHR of AlpogeRealsQED2.v. *)
Theorem windowHyp_of_rpow_r : forall (Gm : R -> R) theta delta C, 0 < delta ->
  (forall Y0, exists Y, Y0 <= Y /\ forall y, Y <= y -> y <= rpc Y (1 + delta) -> Gm y <= C * rpc y theta) ->
  WindowHypR Gm theta delta.
Proof.
  intros Gm theta delta C Hd HW eta Heta Y0.
  destruct (windowHyp_of_rpow_eventually (Rabs C * delta) eta
              ltac:(apply Rmult_le_pos; [apply Rabs_pos|lra]) Heta) as [Y1 HY1].
  destruct (HW (Rmax Y0 Y1)) as [Y [HY Hwin]].
  assert (HYY1 : Y1 <= Y) by (eapply Rle_trans; [apply Rmax_r|exact HY]).
  destruct (HY1 Y HYY1) as [HY1' HK].
  exists Y. split; [eapply Rle_trans; [apply Rmax_l|exact HY]|].
  exists (fun y => Rabs C * rpc y theta). split.
  - intros y Hy1 Hy2. pose proof (rpc_pos y theta). pose proof (Rabs_pos C). split.
    + apply Rmult_le_pos; lra.
    + eapply Rle_trans; [apply Hwin; assumption|].
      apply Rmult_le_compat_r; [lra|apply Rle_abs].
  - exists (Rabs C * (delta * Lc Y)). split.
    + apply (RInt_ext (fun y => Rabs C * (rpc y theta * rpc y (- theta - 1)))); [intros; ring|].
      apply RInt_scal. apply window_integral_rpow; lra.
    + rewrite <- Rmult_assoc. exact HK.
Qed.

(* ===================================================================== *)
(* Axiom audit                                                            *)
(* ===================================================================== *)

Print Assumptions RInt_unique.
Print Assumptions RInt_plus.
Print Assumptions RInt_scal.
Print Assumptions RInt_lin.
Print Assumptions RInt_le.
Print Assumptions RInt_abs_bound.
Print Assumptions RInt_chasles.
Print Assumptions mvt_ge.
Print Assumptions mvt_le.
Print Assumptions mvi_abs.
Print Assumptions Lip_of_deriv.
Print Assumptions FTC_value.
Print Assumptions FTC.
Print Assumptions FTC_Lip.
Print Assumptions FTC_C1.
Print Assumptions RInt_change_var.
Print Assumptions RInt_change_var_FTC.
Print Assumptions RIntInf_unique.
Print Assumptions RIntInf_plus.
Print Assumptions RIntInf_scal.
Print Assumptions RIntInf_le.
Print Assumptions RIntInf_chasles.
Print Assumptions Lc_deriv.
Print Assumptions window_integral.
Print Assumptions window_integral_rpow.
Print Assumptions window_integral_by_cv.
Print Assumptions windowU_change_var.
Print Assumptions exp_ge_Pk.
Print Assumptions kernel_integral.
Print Assumptions windowHyp_of_rpow_r.
