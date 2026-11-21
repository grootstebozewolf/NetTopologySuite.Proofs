(* LandauWindowRebuilt.v -- landau_window itself, assembled from its
   machine-checked elementary pieces and named analytic inputs.  Subject:
   CocoSgt/riemann-hypothesis-lean @ 7cbf7a0,

     Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/
       landauWindow.lean : landau_window   (lines 83-168)

   Lean:  PoleData g Phi Z, 0 < theta < 1, 0 < delta, WindowHypU g theta delta
          ==>  forall rho in Z, Re rho <= theta.

   Rocq (here, over Q): the same conclusion, from
   - dichotomy_rebuilt, nearest_rebuilt   (LandauDichotomyQED.v),
   - window_contra                        (LandauWindowCore.v),
   - sqrt_gap (new, below): a rational strictly between two square roots.
     Lean's radii d = |z - rho| and r are real; window_contra needs rational
     radii d' < e with d <= d' and e < r.  This is what makes the squared-
     distance encoding of LandauDichotomyQED.v composable.
   The analytic inputs are hypotheses, each a named Lean lemma:
     A k g   = |(-1)^k Phi^(k)(sigma + i g)/k!|   (norm of a Taylor coefficient)
     B k     = Re((-1)^k Phi^(k)(sigma)/k!)
     KEY     = landau_window_key, with e^(eta U) <= s^k for k >= U (as in
               LandauWindowCore.v: any rate s >= 1 is available)
     CAUCHY  = landau_cauchy on a pole-free disc about sigma
     POLE1   = landau_pole_asym at an isolated pole rho of sigma + i g, with
               |c| / d^(k+1) >= (|c|/d') / d'^k for d <= d'  (residue c <> 0)
     POLE2   = landau_pole_asym at an isolated REAL pole beta, real part, with
               Re c > 0 (PoleData's real-pole clause; LandauWindowCore.v :
               real_pole_residue_pos is its elementary core)
     LF      = landau_finite: Z is finite on every box in Re s > 0.
   Only POLE2 carries a sign hypothesis on the residue (0 < cr); POLE1 needs
   only 0 < cn.

   Evidence for docs/attacks/2026-11-21-alpoge-landau-window-assembled.md.
   NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import QArith Qabs Qminmax Lqa ZArith Lia List.
From NTS.Proofs.Probes Require Import LandauWindowCore LandauDichotomyQED.
Import ListNotations.
Local Open Scope Q_scope.

(* ===================================================================== *)
(* Helpers                                                                *)
(* ===================================================================== *)

Lemma qpow_nonneg : forall q n, 0 <= q -> 0 <= qpow q n.
Proof. intros q n Hq. induction n as [|n IH]; cbn; [lra|]. apply Qmult_le_0_compat; assumption. Qed.

Lemma qpow_mono : forall a b n, 0 <= a -> a <= b -> qpow a n <= qpow b n.
Proof.
  intros a b n Ha Hab. induction n as [|n IH]; cbn; [lra|].
  pose proof (qpow_nonneg a n Ha). pose proof (qpow_nonneg b n (Qle_trans _ _ _ Ha Hab)). nra.
Qed.

Lemma first_true : forall (P : nat -> Prop), (forall n, {P n} + {~ P n}) ->
  forall m, P m -> ~ P 0%nat -> exists j, P (S j) /\ ~ P j.
Proof.
  intros P Pdec m. induction m as [|m IH]; intros Hm H0; [contradiction|].
  destruct (Pdec m) as [Hp|Hn].
  - exact (IH Hp H0).
  - exists m. split; assumption.
Qed.

Lemma nat_q_succ : forall j, inject_Z (Z.of_nat (S j)) == inject_Z (Z.of_nat j) + 1.
Proof. intro j. rewrite Nat2Z.inj_succ, <- Z.add_1_r, inject_Z_plus. reflexivity. Qed.

Lemma nat_q_nonneg' : forall j, 0 <= inject_Z (Z.of_nat j).
Proof. intro j. change 0 with (inject_Z 0). rewrite <- Zle_Qle. lia. Qed.

(* A rational strictly between sqrt a and sqrt b. *)
Theorem sqrt_gap : forall a b, 0 <= a -> a < b -> exists q, 0 < q /\ a < q * q /\ q * q < b.
Proof.
  intros a b Ha Hab.
  set (K := 2 * (2 * b + 3)).
  assert (HK : 0 < K) by (unfold K; lra).
  set (h := Qmin 1 ((b - a) / K)).
  assert (HbK : 0 < (b - a) / K) by (apply Qlt_shift_div_l; lra).
  assert (Hh0 : 0 < h) by (apply Q.min_glb_lt; lra).
  assert (Hh1 : h <= 1) by apply Q.le_min_l.
  assert (HhK : h * K <= b - a).
  { assert (E : (b - a) / K * K == b - a) by (field; lra).
    pose proof (Q.le_min_r 1 ((b - a) / K)) as Hm. fold h in Hm.
    assert (h * K <= (b - a) / K * K) by (apply Qmult_le_compat_r; lra). lra. }
  set (P := fun j : nat => a < (inject_Z (Z.of_nat j) * h) * (inject_Z (Z.of_nat j) * h)).
  assert (Pdec : forall n, {P n} + {~ P n}).
  { intro n. unfold P. destruct (Qlt_le_dec a ((inject_Z (Z.of_nat n) * h) * (inject_Z (Z.of_nat n) * h))) as [H|H];
      [left; exact H|right; lra]. }
  destruct (Qarchimedean ((b + 1) / h)) as [p Hp].
  assert (Hm : P (Pos.to_nat p)).
  { unfold P. rewrite positive_nat_Z.
    assert (Hph : b + 1 < inject_Z (Z.pos p) * h).
    { assert (E : (b + 1) / h * h == b + 1) by (field; lra).
      assert ((b + 1) / h * h < inject_Z (Z.pos p) * h) by (apply Qmult_lt_compat_r; [lra|exact Hp]).
      lra. }
    nra. }
  assert (H0 : ~ P 0%nat).
  { unfold P. intro Hc.
    assert (E0 : inject_Z (Z.of_nat 0) * h * (inject_Z (Z.of_nat 0) * h) == 0) by (simpl; ring).
    lra. }
  destruct (first_true P Pdec _ Hm H0) as [j [Hj1 Hj0]].
  unfold P in Hj1, Hj0. rewrite nat_q_succ in Hj1.
  set (x := inject_Z (Z.of_nat j) * h) in *.
  assert (Hx0 : 0 <= x) by (unfold x; pose proof (nat_q_nonneg' j); nra).
  assert (Hxa : x * x <= a) by lra.
  assert (Hxb : x <= b + 1) by nra.
  assert (Eq : (inject_Z (Z.of_nat j) + 1) * h == x + h) by (unfold x; ring).
  rewrite Eq in Hj1.
  exists (x + h). split; [lra|]. split; [exact Hj1|].
  assert (H2 : (x + h) * (x + h) <= a + h * (2 * b + 3)) by nra.
  unfold K in HhK. lra.
Qed.

Print Assumptions sqrt_gap.

(* The two final linear steps of landau_window, multiplied out. *)
Lemma glue_complex : forall cn A B P Qd Ek S C M1 M2,
  0 <= A -> 0 < P -> P <= Ek -> 0 < Qd -> 0 <= S ->
  cn * P <= (A * P + M1) * Qd -> - M2 <= B * P -> (A + B) * Ek <= C * S ->
  cn * P <= (Qabs (M1 + M2) + Qabs C * S) * Qd.
Proof.
  intros cn A B P Qd Ek S C M1 M2 HA HP HPE HQ HS H1 H2 H3.
  assert (HCS : C * S <= Qabs C * S) by (apply Qmult_le_compat_r; [apply Qle_Qabs|exact HS]).
  assert (HCS0 : 0 <= Qabs C * S) by (apply Qmult_le_0_compat; [apply Qabs_nonneg|exact HS]).
  assert (HAP : A * P <= Qabs C * S + M2).
  { destruct (Qlt_le_dec (A + B) 0) as [Hn|Hp].
    - assert ((A + B) * P <= 0) by nra. nra.
    - assert ((A + B) * P <= (A + B) * Ek) by nra. nra. }
  assert (HM : M1 + M2 <= Qabs (M1 + M2)) by apply Qle_Qabs.
  assert ((A * P + M1) * Qd <= (Qabs (M1 + M2) + Qabs C * S) * Qd)
    by (apply Qmult_le_compat_r; lra).
  lra.
Qed.

Lemma glue_real : forall cr A B P Qd Ek S C M,
  0 <= A -> 0 < P -> P <= Ek -> 0 < Qd -> 0 <= S ->
  cr * P <= (B * P + M) * Qd -> (A + B) * Ek <= C * S ->
  cr * P <= (Qabs M + Qabs C * S) * Qd.
Proof.
  intros cr A B P Qd Ek S C M HA HP HPE HQ HS H1 H3.
  assert (HCS : C * S <= Qabs C * S) by (apply Qmult_le_compat_r; [apply Qle_Qabs|exact HS]).
  assert (HCS0 : 0 <= Qabs C * S) by (apply Qmult_le_0_compat; [apply Qabs_nonneg|exact HS]).
  assert (HBP : B * P <= Qabs C * S).
  { destruct (Qlt_le_dec (A + B) 0) as [Hn|Hp].
    - assert ((A + B) * P <= 0) by nra. nra.
    - assert ((A + B) * P <= (A + B) * Ek) by nra. nra. }
  assert (HM : M <= Qabs M) by apply Qle_Qabs.
  assert ((B * P + M) * Qd <= (Qabs M + Qabs C * S) * Qd) by (apply Qmult_le_compat_r; lra).
  lra.
Qed.

(* A rate s >= 1 with s d < e, for 0 < d < e. *)
Lemma rate : forall d e, 0 < d -> d < e -> exists s, 1 <= s /\ s * d < e.
Proof.
  intros d e Hd Hde. exists ((1 # 2) * (1 + e / d)).
  assert (E : (1 # 2) * (1 + e / d) * d == (1 # 2) * (d + e)) by (field; lra).
  assert (H1 : 1 < e / d) by (apply Qlt_shift_div_l; lra).
  split; lra.
Qed.

Lemma sq_sum_nonneg : forall sigma g w, 0 <= d2 sigma g w.
Proof. intros. unfold d2. pose proof (sq_nonneg (sigma - fst w)). pose proof (sq_nonneg (g - snd w)). lra. Qed.

(* ===================================================================== *)
(* landau_window                                                          *)
(* ===================================================================== *)

Section Assembly.
Variable Z : Q * Q -> Prop.
Variables sigma theta : Q.
Hypothesis Htheta : 0 < theta.
Hypothesis Hts : theta < sigma.
Hypothesis Hle : forall w, Z w -> fst w < sigma.            (* landau_pole_re_le, 2 < sigma *)
Hypothesis LF : forall lo y0 R, 0 < lo -> exists F : list (Q * Q),
  (forall w, In w F -> Z w) /\
  (forall w, Z w -> lo <= fst w -> - R <= snd w - y0 <= R -> In w F).
Variables (A : nat -> Q -> Q) (B : nat -> Q).
Hypothesis HA : forall k g, 0 <= A k g.
Hypothesis KEY : exists C, forall s, 1 <= s -> forall K, exists k, (K <= k)%nat /\
  forall g, (A k g + B k) * qpow (sigma - theta) k <= C * qpow s k.
Hypothesis CAUCHY : forall D2 e, (forall w, Z w -> ~ d2 sigma 0 w < D2) ->
  0 < e -> e * e < D2 -> exists M, forall k, - M <= B k * qpow e k.
Hypothesis POLE1 : forall g rho r2 d e, Z rho ->
  (forall w, Z w -> d2 sigma g w < r2 -> peq w rho) ->
  0 < d -> d2 sigma g rho < d * d -> d < e -> e * e < r2 ->
  exists cn M, 0 < cn /\ forall k, cn * qpow e k <= (A k g * qpow e k + M) * qpow d k.
Hypothesis POLE2 : forall beta r2 e, Z beta -> snd beta == 0 ->
  (forall w, Z w -> d2 sigma 0 w < r2 -> peq w beta) ->
  sigma - fst beta < e -> e * e < r2 ->
  exists cr M, 0 < cr /\ forall k, cr * qpow e k <= (B k * qpow e k + M) * qpow (sigma - fst beta) k.

Theorem landau_window_rebuilt : forall rho0, Z rho0 -> fst rho0 <= theta.
Proof.
  intros rho0 H0. destruct (Qlt_le_dec theta (fst rho0)) as [Hx|Hx]; [exfalso|exact Hx].
  set (E := sigma - theta) in *.
  assert (HE : 0 < E) by (unfold E; lra).
  destruct KEY as [C HK].
  (* the finite set Z ∩ closedBall sigma E, via a box *)
  destruct (LF theta 0 E Htheta) as [F0 [HF0Z HF0]].
  set (F := filter (fun w => Qle_bool (d2 sigma 0 w) (E * E)) F0).
  assert (HF : forall w, Z w -> d2 sigma 0 w <= E * E -> In w F).
  { intros w Hw Hd. unfold F. apply filter_In. split; [|apply Qle_bool_iff; exact Hd].
    pose proof (Hle w Hw). unfold d2 in Hd.
    pose proof (sq_nonneg (sigma - fst w)). pose proof (sq_nonneg (0 - snd w)).
    apply HF0; [exact Hw| |].
    - assert (sigma - fst w <= E) by (apply sq_le_inv; lra). unfold E in *. lra.
    - assert (Hy : (0 - snd w) * (0 - snd w) <= E * E) by lra.
      split; nra. }
  assert (HFZ : forall w, In w F -> Z w /\ d2 sigma 0 w <= E * E).
  { intros w Hw. unfold F in Hw. apply filter_In in Hw. destruct Hw as [Hw Hb].
    split; [apply HF0Z; exact Hw|apply Qle_bool_iff; exact Hb]. }
  destruct (dichotomy_rebuilt Z F sigma theta rho0 Hts HF HFZ Hle H0 Hx)
    as [[D2 [HD2 [Hfree [rho1 [H1 Hr1]]]]]
       |[beta [HbZ [Hby [Hbt [r2 [Hbr [Hr2E Hiso]]]]]]]].
  - (* left branch: a non-real nearest pole, norm at sigma + i gamma *)
    fold E in HD2.
    pose proof (Hle rho1 H1) as Hx1.
    destruct (sqrt_gap _ _ (sq_nonneg (sigma - fst rho1)) Hr1) as [D' [HD'0 [HD'1 HD'2]]].
    assert (Hlt1 : sigma - fst rho1 < D') by (apply sq_lt_inv; lra).
    assert (HD'E : D' < E) by (apply sq_lt_inv; lra).
    destruct (LF (sigma - D') (snd rho1) (2 * D') ltac:(unfold E in HD'E; lra)) as [F1 [HF1Z HF1]].
    destruct (nearest_rebuilt Z F1 sigma D' rho1 Hle H1 Hlt1 HF1 HF1Z)
      as [g [rho [r2 [HrZ [Hdr [Hr2D Hiso]]]]]].
    destruct (sqrt_gap _ _ (sq_sum_nonneg sigma g rho) Hdr) as [q1 [Hq1 [Hq1a Hq1b]]].
    destruct (sqrt_gap _ _ (sq_nonneg q1) Hq1b) as [q2 [Hq2 [Hq2a Hq2b]]].
    assert (Hq12 : q1 < q2) by (apply sq_lt_inv; lra).
    assert (Hq2E : q2 < E) by (apply sq_lt_inv; lra).
    destruct (POLE1 g rho r2 q1 q2 HrZ Hiso Hq1 Hq1a Hq12 Hq2b) as [cn [M1 [Hcn HM1]]].
    destruct (CAUCHY D2 q2 Hfree Hq2 ltac:(lra)) as [M2 HM2].
    destruct (rate q1 q2 Hq1 Hq12) as [s [Hs1 Hsd]].
    apply (window_contra cn q1 q2 (M1 + M2) C s Hcn Hq1 Hs1 Hsd).
    intro K. destruct (HK s Hs1 K) as [k [Hk Hb]]. exists k. split; [exact Hk|].
    apply (glue_complex cn (A k g) (B k) (qpow q2 k) (qpow q1 k) (qpow E k) (qpow s k) C M1 M2).
    + apply HA.
    + apply qpow_pos; exact Hq2.
    + apply qpow_mono; lra.
    + apply qpow_pos; exact Hq1.
    + apply qpow_nonneg; lra.
    + apply HM1.
    + apply HM2.
    + apply Hb.
  - (* right branch: a real nearest pole beta, real part at sigma *)
    fold E in Hr2E.
    pose proof (Hle beta HbZ) as Hxb.
    set (d := sigma - fst beta) in *.
    assert (Hd : 0 < d) by (unfold d; lra).
    destruct (sqrt_gap _ _ (sq_nonneg d) Hbr) as [e [He [Hea Heb]]].
    assert (Hde : d < e) by (apply sq_lt_inv; lra).
    assert (HeE : e < E) by (apply sq_lt_inv; lra).
    destruct (POLE2 beta r2 e HbZ Hby Hiso Hde Heb) as [cr [M [Hcr HM]]].
    destruct (rate d e Hd Hde) as [s [Hs1 Hsd]].
    apply (window_contra cr d e M C s Hcr Hd Hs1 Hsd).
    intro K. destruct (HK s Hs1 K) as [k [Hk Hb]]. exists k. split; [exact Hk|].
    apply (glue_real cr (A k 0) (B k) (qpow e k) (qpow d k) (qpow E k) (qpow s k) C M).
    + apply HA.
    + apply qpow_pos; exact He.
    + apply qpow_mono; lra.
    + apply qpow_pos; exact Hd.
    + apply qpow_nonneg; lra.
    + apply HM.
    + apply Hb.
Qed.

End Assembly.

Print Assumptions landau_window_rebuilt.

(* Consistency check (the hypotheses are not contradictory): the empty zero set
   with zero coefficients satisfies Hle, LF, HA, KEY and CAUCHY; POLE1 and
   POLE2 hold vacuously because there are no zeros.  This is a consistency
   witness only, not evidence that the hypotheses hold for Phi = Laplace(Gm). *)
Theorem landau_window_hyps_consistent :
  let Z := fun _ : Q * Q => False in
  let A := fun (_ : nat) (_ : Q) => 0 in
  let B := fun _ : nat => 0 in
  forall sigma theta : Q, 0 < theta -> theta < sigma ->
  (forall w, Z w -> fst w < sigma) /\
  (forall lo y0 R, 0 < lo -> exists F : list (Q * Q),
     (forall w, In w F -> Z w) /\
     (forall w, Z w -> lo <= fst w -> - R <= snd w - y0 <= R -> In w F)) /\
  (forall k g, 0 <= A k g) /\
  (exists C, forall s, 1 <= s -> forall K, exists k, (K <= k)%nat /\
     forall g, (A k g + B k) * qpow (sigma - theta) k <= C * qpow s k) /\
  (forall D2 e, (forall w, Z w -> ~ d2 sigma 0 w < D2) ->
     0 < e -> e * e < D2 -> exists M, forall k, - M <= B k * qpow e k).
Proof.
  intros Z A B sigma theta _ _. unfold Z, A, B.
  split; [intros w []|]. split.
  { intros. exists []. split; [intros w []|intros w []]. }
  split; [intros; lra|]. split.
  - exists 0. intros s _ K. exists K. split; [lia|]. intro g. ring_simplify. lra.
  - intros. exists 0. intro k. ring_simplify. lra.
Qed.

Print Assumptions landau_window_hyps_consistent.
