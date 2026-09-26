(* AtanIvt.v — 3-axiom atan via IVT (no Ratan / Classical_Prop.classic).
   atan3 u := IVT root of  sin t - u cos t  on [-PI/2, PI/2]; canonical by atan3_unique.
   R1 (#559) drop-in for NurbsConicExact 508-a / 508-g:
     atan_0, atan_1, atan_le, atan_tan, cos_2_atan, sin_2_atan  ->  atan3_*.
   Verified on Coq 8.18 with From Coq; re-run Print Assumptions on the corpus
   toolchain before peeling docs/audit-exceptions.txt. *)
From Stdlib Require Import Reals Lra.
Local Open Scope R_scope.

(* ---------- atan3 : IVT root of  sin t - u cos t  on [-PI/2, PI/2] ---------- *)

Definition atan3_g (u t : R) : R := sin t - u * cos t.

Lemma atan3_g_cont (u : R) : continuity (atan3_g u).
Proof.
  unfold atan3_g. apply continuity_minus; [apply continuity_sin|].
  apply continuity_mult; [apply continuity_const; intros ? ?; reflexivity | apply continuity_cos].
Qed.

Lemma atan3_g_lo (u : R) : atan3_g u (-(PI/2)) < 0.
Proof. unfold atan3_g. rewrite sin_neg, cos_neg, sin_PI2, cos_PI2. lra. Qed.

Lemma atan3_g_hi (u : R) : 0 < atan3_g u (PI/2).
Proof. unfold atan3_g. rewrite sin_PI2, cos_PI2. lra. Qed.

Local Lemma atan3_half_pi_lt : -(PI/2) < PI/2.
Proof. pose proof PI2_RGT_0. lra. Qed.

Definition atan3 (u : R) : R :=
  proj1_sig (IVT (atan3_g u) (-(PI/2)) (PI/2) (atan3_g_cont u) atan3_half_pi_lt (atan3_g_lo u) (atan3_g_hi u)).

Lemma atan3_spec (u : R) :
  -(PI/2) < atan3 u < PI/2 /\ sin (atan3 u) = u * cos (atan3 u).
Proof.
  unfold atan3. destruct (IVT _ _ _ _ _ _ _) as [z [Hz Hg]]; cbn.
  unfold atan3_g in Hg.
  assert (z <> -(PI/2)).
  { intro E. subst. pose proof (atan3_g_lo u). unfold atan3_g in H. lra. }
  assert (z <> PI/2).
  { intro E. subst. pose proof (atan3_g_hi u). unfold atan3_g in H0. lra. }
  repeat split; lra.
Qed.

(* ---------- sin d = 0 on (-PI, PI) forces d = 0 ---------- *)

Local Lemma atan3_sin_zero_unique (d : R) : -PI < d < PI -> sin d = 0 -> d = 0.
Proof.
  intros [Hl Hh] Hs.
  destruct (Rtotal_order d 0) as [Hn|[Hz|Hp]]; [|exact Hz|].
  - pose proof (sin_gt_0 (-d) ltac:(lra) ltac:(lra)). rewrite sin_neg in H. lra.
  - pose proof (sin_gt_0 d Hp Hh). lra.
Qed.

Lemma atan3_unique (u a : R) :
  -(PI/2) < a < PI/2 -> sin a = u * cos a -> a = atan3 u.
Proof.
  intros Ha Hs. destruct (atan3_spec u) as [Hb Hs'].
  set (b := atan3 u) in *.
  assert (sin (a - b) = 0) by (rewrite sin_minus, Hs, Hs'; ring).
  apply (Rplus_eq_reg_r (- b)). ring_simplify.
  replace (a - b) with (a + - b) in H by ring.
  apply atan3_sin_zero_unique; [lra | exact H].
Qed.

(* ---------- drop-in kit for AtanDoubleAngle / NurbsConicExact ---------- *)

Lemma atan3_0 : atan3 0 = 0.
Proof.
  symmetry. apply atan3_unique; [pose proof PI2_RGT_0; lra|]. rewrite sin_0. ring.
Qed.

Lemma atan3_1 : atan3 1 = PI / 4.
Proof.
  symmetry. apply atan3_unique.
  - pose proof PI_RGT_0. lra.
  - rewrite sin_PI4, cos_PI4. ring.
Qed.

Lemma atan3_tan : forall w, -(PI/2) < w < PI/2 -> atan3 (tan w) = w.
Proof.
  intros w Hw. symmetry. apply atan3_unique; [exact Hw|].
  assert (0 < cos w) by (apply cos_gt_0; lra).
  unfold tan. field. lra.
Qed.

Lemma atan3_le : forall x y, x <= y -> atan3 x <= atan3 y.
Proof.
  intros x y Hxy.
  destruct (atan3_spec x) as [Bx Sx]. destruct (atan3_spec y) as [By Sy].
  destruct (Rle_dec (atan3 x) (atan3 y)) as [H|H]; [exact H|]. exfalso.
  assert (Hd : 0 < sin (atan3 x - atan3 y)) by (apply sin_gt_0; lra).
  rewrite sin_minus, Sx, Sy in Hd.
  assert (0 < cos (atan3 x)) by (apply cos_gt_0; lra).
  assert (0 < cos (atan3 y)) by (apply cos_gt_0; lra).
  assert (E : x * cos (atan3 x) * cos (atan3 y) - cos (atan3 x) * (y * cos (atan3 y))
             = (x - y) * (cos (atan3 x) * cos (atan3 y))) by ring.
  rewrite E in Hd. assert (0 < cos (atan3 x) * cos (atan3 y)) by nra. nra.
Qed.

Lemma cos2_atan3 : forall x, cos (atan3 x) * cos (atan3 x) = 1 / (1 + x * x).
Proof.
  intro x. destruct (atan3_spec x) as [B S].
  pose proof (sin2_cos2 (atan3 x)) as K. unfold Rsqr in K. rewrite S in K.
  assert (Hp : 0 < 1 + x * x) by nra.
  assert (E : cos (atan3 x) * cos (atan3 x) * (1 + x * x) = 1) by lra.
  apply (Rmult_eq_reg_r (1 + x * x)); [|lra].
  rewrite E. field. lra.
Qed.

Lemma cos_2_atan3 : forall x, cos (2 * atan3 x) = (1 - x * x) / (1 + x * x).
Proof.
  intro x. destruct (atan3_spec x) as [B S]. pose proof (cos2_atan3 x) as C.
  assert (0 < 1 + x * x) by nra.
  rewrite cos_2a, S.
  replace ((x * cos (atan3 x)) * (x * cos (atan3 x))) with (x * x * (cos (atan3 x) * cos (atan3 x))) by ring.
  replace (cos (atan3 x) * cos (atan3 x) - x * x * (cos (atan3 x) * cos (atan3 x)))
    with ((1 - x * x) * (cos (atan3 x) * cos (atan3 x))) by ring.
  rewrite C. field. lra.
Qed.

Lemma sin_2_atan3 : forall x, sin (2 * atan3 x) = 2 * x / (1 + x * x).
Proof.
  intro x. destruct (atan3_spec x) as [B S]. pose proof (cos2_atan3 x) as C.
  assert (0 < 1 + x * x) by nra.
  rewrite sin_2a, S.
  replace (2 * (x * cos (atan3 x)) * cos (atan3 x)) with (2 * x * (cos (atan3 x) * cos (atan3 x))) by ring.
  rewrite C. field. lra.
Qed.

(* ---------- tan range on [0, PI/4] (split from AtanDoubleAngle; cites Stdlib Rtrigo_calc.tan_PI4) ---------- *)

Lemma tan_ge_0_on_0_PI4 : forall x, 0 <= x -> x <= PI / 4 -> 0 <= tan x.
Proof.
  intros x Hx0 Hx1. pose proof PI_RGT_0.
  destruct Hx0 as [Hlt | Heq].
  - rewrite <- tan_0. apply Rlt_le. apply tan_increasing_1; lra.
  - subst. rewrite tan_0. lra.
Qed.

Lemma tan_le_1_on_0_PI4 : forall x, 0 <= x -> x <= PI / 4 -> tan x <= 1.
Proof.
  intros x Hx0 Hx1. pose proof PI_RGT_0.
  rewrite <- Rtrigo_calc.tan_PI4.
  destruct Hx1 as [Hlt | Heq].
  - apply Rlt_le. apply tan_increasing_1; lra.
  - subst. apply Rle_refl.
Qed.

Print Assumptions atan3_0.
Print Assumptions atan3_1.
Print Assumptions atan3_tan.
Print Assumptions atan3_le.
Print Assumptions cos_2_atan3.
Print Assumptions sin_2_atan3.
Print Assumptions tan_ge_0_on_0_PI4.
Print Assumptions tan_le_1_on_0_PI4.
