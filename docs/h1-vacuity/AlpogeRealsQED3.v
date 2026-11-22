(* AlpogeRealsQED3.v -- the next refined main-line lemmas of the claimed
   RH/GRH Lean development (CocoSgt/riemann-hypothesis-lean @ 7cbf7a0),
   proved over Stdlib's R within the three-axiom allowlist.  See the
   finding docs/attacks/2026-11-21-alpoge-third-batch-over-reals.md.
   NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import Reals Lra Psatz List Factorial ZArith.
From NTS.Proofs.Probes Require Import AlpogeRealsQED AlpogeRealsQED2 AlpogeDeepStatements.
Import ListNotations.
Local Open Scope R_scope.

(* ===================================================================== *)
(* Part A: landau_dichotomy and landau_nearest (squared distances)        *)
(* ===================================================================== *)
Definition d2 (sigma gamma : R) (w : R * R) : R :=
  (sigma - fst w) * (sigma - fst w) + (gamma - snd w) * (gamma - snd w).
Definition peq (a b : R * R) : Prop := fst a = fst b /\ snd a = snd b.

Lemma sq_lt_inv : forall a b, 0 <= a -> 0 <= b -> a * a < b * b -> a < b.
Proof. intros. nra. Qed.
Lemma sq_le_inv : forall a b, 0 <= a -> 0 <= b -> a * a <= b * b -> a <= b.
Proof. intros. nra. Qed.
Lemma sq_nonneg : forall a, 0 <= a * a.
Proof. intros. nra. Qed.

(* eq_ofReal_sub_of_dist_le_of_le_sub_re: |w - sigma| <= D <= sigma - Re w
   forces w = sigma - D, on the real axis. *)
Theorem on_axis : forall sigma D w,
  0 <= D -> D <= sigma - fst w -> d2 sigma 0 w <= D * D ->
  snd w = 0 /\ fst w = sigma - D.
Proof.
  intros sigma D [x y] HD Hle Hd. unfold d2 in Hd; simpl in *.
  assert (Hx : D * D <= (sigma - x) * (sigma - x)) by nra.
  assert (Hy : y * y = 0) by nra.
  split.
  - destruct (Rlt_le_dec y 0); destruct (Rlt_le_dec 0 y); nra.
  - assert (sigma - x <= D) by (apply sq_le_inv; nra). lra.
Qed.

(* Finite minimum over a list, with default d. *)
Fixpoint minl (f : R * R -> R) (l : list (R * R)) (d : R) : R :=
  match l with [] => d | w :: l' => Rmin (f w) (minl f l' d) end.

Lemma minl_le_d : forall f l d, minl f l d <= d.
Proof.
  intros f l d. induction l as [|w l IH]; simpl; [lra|].
  pose proof (Rmin_r (f w) (minl f l d)). lra.
Qed.

Lemma minl_le_mem : forall f l d w, In w l -> minl f l d <= f w.
Proof.
  intros f l d w. induction l as [|a l IH]; simpl; [tauto|].
  intros [<-|H].
  - apply Rmin_l.
  - pose proof (Rmin_r (f a) (minl f l d)). specialize (IH H). lra.
Qed.

Lemma minl_cases : forall f l d, minl f l d = d \/ exists w, In w l /\ minl f l d = f w.
Proof.
  intros f l d. induction l as [|a l IH]; simpl; [left; reflexivity|].
  unfold Rmin. destruct (Rle_dec (f a) (minl f l d)) as [H|H].
  - right. exists a. split; [left; reflexivity|reflexivity].
  - destruct IH as [E|[w [Hw E]]]; [left; exact E|right; exists w; split; [right; exact Hw|exact E]].
Qed.

(* Attained when l is nonempty and every f w <= d. *)
Lemma minl_attained : forall f l d w0, In w0 l -> (forall w, In w l -> f w <= d) ->
  exists w, In w l /\ minl f l d = f w.
Proof.
  intros f l d w0 H0 Hd. destruct (minl_cases f l d) as [H|H]; [|exact H].
  exists w0. split; [exact H0|]. pose proof (minl_le_mem f l d w0 H0). specialize (Hd w0 H0). lra.
Qed.

(* The "second minimum": min over the entries strictly above m, capped at cap. *)
Definition above (f : R * R -> R) (m cap : R) (w : R * R) : R :=
  if Rle_dec (f w) m then cap else f w.

Lemma above_gt : forall f l m cap, m < cap -> m < minl (above f m cap) l cap.
Proof.
  intros f l m cap Hc. induction l as [|a l IH]; simpl; [exact Hc|].
  unfold above at 1. destruct (Rle_dec (f a) m) as [E|E].
  - apply Rmin_glb_lt; assumption.
  - apply Rmin_glb_lt; [lra|exact IH].
Qed.

Lemma above_sep : forall f l m cap w, In w l -> f w < minl (above f m cap) l cap -> f w <= m.
Proof.
  intros f l m cap w Hw Hlt. pose proof (minl_le_mem (above f m cap) l cap w Hw) as H.
  unfold above in H at 2. destruct (Rle_dec (f w) m) as [E|E]; [exact E|lra].
Qed.

(* Decide, over a finite list, whether some entry is nearer the line than m. *)
Lemma split_list : forall sigma m (l : list (R * R)),
  { w | In w l /\ (sigma - fst w) * (sigma - fst w) < m } +
  { forall w, In w l -> m <= (sigma - fst w) * (sigma - fst w) }.
Proof.
  intros sigma m l. induction l as [|a l IH].
  - right. intros w [].
  - destruct (Rlt_le_dec ((sigma - fst a) * (sigma - fst a)) m) as [H|H].
    + left. exists a. split; [left; reflexivity|exact H].
    + destruct IH as [[w [Hw Hlt]]|Hall].
      * left. exists w. split; [right; exact Hw|exact Hlt].
      * right. intros w [<-|Hw]; [exact H|exact (Hall w Hw)].
Qed.

(* landau_dichotomy.  E = sigma - theta.  F covers Z on the closed disc of
   radius E about sigma (Lean: Z ∩ closedBall sigma (sigma - theta), finite by
   landau_finite).  Left branch: a pole-free disc of squared radius D2 <= E^2
   and a pole nearer the line than its radius.  Right branch: a real pole beta
   in (theta, sigma), alone in a disc of squared radius r2 <= E^2. *)
Theorem landau_dichotomy :
  forall (Z : R * R -> Prop) (F : list (R * R)) (sigma theta : R) (rho0 : R * R),
  theta < sigma ->
  (forall w, Z w -> d2 sigma 0 w <= (sigma - theta) * (sigma - theta) -> In w F) ->
  (forall w, In w F -> Z w /\ d2 sigma 0 w <= (sigma - theta) * (sigma - theta)) ->
  (forall w, Z w -> fst w < sigma) ->
  Z rho0 -> theta < fst rho0 ->
  (exists D2, D2 <= (sigma - theta) * (sigma - theta)
     /\ (forall w, Z w -> ~ d2 sigma 0 w < D2)
     /\ exists rho1, Z rho1 /\ (sigma - fst rho1) * (sigma - fst rho1) < D2)
  \/
  (exists beta, Z beta /\ snd beta = 0 /\ theta < fst beta
     /\ exists r2, (sigma - fst beta) * (sigma - fst beta) < r2
          /\ r2 <= (sigma - theta) * (sigma - theta)
          /\ forall w, Z w -> d2 sigma 0 w < r2 -> peq w beta).
Proof.
  intros Z F sigma theta rho0 Hts HF HFZ Hle H0 Hx0.
  set (E2 := (sigma - theta) * (sigma - theta)).
  set (f := d2 sigma 0).
  pose proof (Hle rho0 H0) as Hx0s.
  assert (H0E : (sigma - fst rho0) * (sigma - fst rho0) < E2) by (unfold E2; nra).
  destruct F as [|p F'] eqn:EF.
  - (* no pole in the closed disc: D = sigma - theta, rho1 = rho0 *)
    left. exists E2. split; [unfold E2; lra|]. split.
    + intros w Hw Hlt. apply (HF w Hw). unfold f, E2 in *. lra.
    + exists rho0. split; assumption.
  - set (m := minl f F E2).
    assert (HmE : m <= E2) by apply minl_le_d.
    destruct (minl_attained f F E2 p) as [rs [Hrs Hm]].
    { rewrite EF. left. reflexivity. }
    { intros w Hw. rewrite <- EF in HFZ. apply (HFZ w Hw). }
    fold m in Hm. rewrite <- EF in HF, HFZ.
    assert (Hmin : forall w, Z w -> f w <= E2 -> m <= f w).
    { intros w Hw HwE. apply minl_le_mem. apply HF; assumption. }
    destruct (split_list sigma m (rho0 :: F)) as [[r1 [Hr1 Hlt]]|Hall].
    + (* left branch: D = dist rs sigma *)
      left. exists m. split; [exact HmE|]. split.
      * intros w Hw Hwm. assert (HwE : f w <= E2) by lra.
        pose proof (Hmin w Hw HwE). unfold f in *. lra.
      * exists r1. split; [|exact Hlt].
        destruct Hr1 as [<-|Hr1]; [exact H0|apply (HFZ r1 Hr1)].
    + (* right branch: the nearest pole rs is real *)
      right.
      assert (HmlE : m < E2).
      { pose proof (Hall rho0 (or_introl eq_refl)). lra. }
      assert (Hreal : forall w, In w F -> f w = m -> snd w = 0 /\ fst w = fst rs).
      { intros w Hw Hfw.
        destruct (HFZ w Hw) as [HwZ _].
        pose proof (Hall w (or_intror Hw)) as Hw2.
        pose proof (Hle w HwZ) as Hws.
        pose proof (Hall rs (or_intror Hrs)) as Hr2.
        destruct (HFZ rs Hrs) as [HrZ _]. pose proof (Hle rs HrZ) as Hrsl.
        unfold f, d2 in Hfw, Hm. simpl in Hfw, Hm.
        assert (E1 : (0 - snd w) * (0 - snd w) = snd w * snd w) by ring.
        assert (E2' : (0 - snd rs) * (0 - snd rs) = snd rs * snd rs) by ring.
        pose proof (sq_nonneg (snd w)). pose proof (sq_nonneg (snd rs)).
        assert (Hy : snd w * snd w = 0) by lra.
        assert (Hy' : snd rs * snd rs = 0) by lra.
        assert (snd w = 0) by (destruct (Rlt_le_dec (snd w) 0); destruct (Rlt_le_dec 0 (snd w)); nra).
        split; [assumption|].
        assert (Heq : (sigma - fst w) * (sigma - fst w) = (sigma - fst rs) * (sigma - fst rs)) by nra.
        assert (sigma - fst w <= sigma - fst rs) by (apply sq_le_inv; nra).
        assert (sigma - fst rs <= sigma - fst w) by (apply sq_le_inv; nra).
        lra. }
      destruct (Hreal rs Hrs (eq_sym Hm)) as [Hrsy _].
      destruct (HFZ rs Hrs) as [HrsZ _].
      pose proof (Hle rs HrsZ) as Hrsl.
      assert (Hfrs : f rs = (sigma - fst rs) * (sigma - fst rs)).
      { unfold f, d2. simpl. rewrite Hrsy. ring. }
      exists rs. split; [exact HrsZ|]. split; [exact Hrsy|]. split.
      { assert (sigma - fst rs < sigma - theta) by (apply sq_lt_inv; unfold E2 in HmlE; nra). lra. }
      exists (minl (above f m E2) F E2). split; [|split].
      * pose proof (above_gt f F m E2 HmlE). lra.
      * apply minl_le_d.
      * intros w HwZ Hw.
        pose proof (minl_le_d (above f m E2) F E2) as Hcap.
        assert (HwF : In w F) by (apply HF; [exact HwZ|change (f w <= E2); lra]).
        pose proof (above_sep f F m E2 w HwF Hw) as Hwm.
        pose proof (minl_le_mem f F E2 w HwF) as Hmw.
        destruct (Hreal w HwF ltac:(fold m in Hmw; lra)) as [Hy Hx].
        split; [exact Hx|]. rewrite Hy, Hrsy. reflexivity.
Qed.


(* =================================== *)
(* Part C: landau_nearest                                                 *)
(* =================================== *)

Definition nnum (sigma : R) (a b : R * R) : R :=
  (sigma - fst a) * (sigma - fst a) + snd a * snd a
  - (sigma - fst b) * (sigma - fst b) - snd b * snd b.

(* landau_nearest_equi: equidistance from sigma + i gamma forces a = b unless
   gamma is the one critical value of the pair (only when Im a <> Im b). *)
Theorem nearest_equi : forall sigma gamma a b,
  fst a < sigma -> fst b < sigma ->
  d2 sigma gamma a = d2 sigma gamma b ->
  (~ snd a = snd b -> ~ gamma * (2 * (snd a - snd b)) = nnum sigma a b) ->
  peq a b.
Proof.
  intros sigma gamma [xa ya] [xb yb] Ha Hb Hd Hg. unfold d2, nnum, peq in *; simpl in *.
  assert (Hy : ya = yb).
  { destruct (Req_dec ya yb) as [H|H]; [exact H|]. exfalso. apply (Hg H). nra. }
  split; [|exact Hy].
  rewrite Hy in Hd.
  assert (Heq : (sigma - xa) * (sigma - xa) = (sigma - xb) * (sigma - xb)) by nra.
  assert (sigma - xa <= sigma - xb) by (apply sq_le_inv; nra).
  assert (sigma - xb <= sigma - xa) by (apply sq_le_inv; nra).
  lra.
Qed.

(* Choose a shift avoiding a finite list of bad values, robustly. *)
Lemma avoid : forall (g0 eps : R) (L : list R), 0 < eps ->
  exists t, 0 < t /\ t <= eps /\ forall s, 0 < s -> s <= t -> forall b, In b L -> ~ g0 + s = b.
Proof.
  intros g0 eps L He. induction L as [|b L IH].
  - exists eps. split; [exact He|]. split; [lra|]. intros s _ _ b [].
  - destruct IH as [t [Ht [Hte Hav]]].
    destruct (Req_dec b g0) as [Hb|Hb].
    + exists t. split; [exact Ht|]. split; [exact Hte|].
      intros s Hs Hst c [<-|Hc]; [|exact (Hav s Hs Hst c Hc)]. intro E. rewrite Hb in E. lra.
    + set (q := Rabs (b - g0)).
      assert (Hq : 0 < q) by (unfold q; apply Rabs_pos_lt; lra).
      exists (Rmin t (q * / 2)).
      pose proof (Rmin_l t (q * / 2)). pose proof (Rmin_r t (q * / 2)).
      split; [apply Rmin_glb_lt; lra|].
      split; [lra|].
      intros s Hs Hst c [<-|Hc].
      * intro E. assert (Hq' : q = b - g0) by (unfold q; apply Rabs_pos_eq; lra). lra.
      * apply (Hav s Hs); [lra|exact Hc].
Qed.

Lemma abs_of_sq_lt : forall a D, 0 < D -> a * a < D * D -> - D < a /\ a < D.
Proof. intros. split; nra. Qed.

(* landau_nearest.  rho1 is a pole nearer the line Re s = sigma than D < sigma.
   F covers Z on the box [sigma - D, sigma] x [Im rho1 - 2D, Im rho1 + 2D],
   which contains Lean's closedBall (sigma + i Im rho1) (D + eps) and lies in
   Re s > 0 (Lean: landau_finite).  Conclusion: some sigma + i gamma has a
   unique nearest pole rho, alone in a disc of squared radius r2 <= D^2. *)
Theorem landau_nearest :
  forall (Z : R * R -> Prop) (F : list (R * R)) (sigma D : R) (rho1 : R * R),
  (forall w, Z w -> fst w < sigma) ->
  Z rho1 -> sigma - fst rho1 < D ->
  (forall w, Z w -> sigma - D <= fst w -> - (2 * D) <= snd w - snd rho1 <= 2 * D -> In w F) ->
  (forall w, In w F -> Z w) ->
  exists gamma rho r2, Z rho /\ d2 sigma gamma rho < r2 /\ r2 <= D * D
    /\ forall w, Z w -> d2 sigma gamma w < r2 -> peq w rho.
Proof.
  intros Z F sigma D rho1 Hle H1 Hx1 HF HFZ.
  pose proof (Hle rho1 H1) as Hx1s.
  set (a := sigma - fst rho1).
  assert (Ha : 0 < a) by (unfold a; lra).
  assert (HD : 0 < D) by (unfold a in Ha; lra).
  set (eps := (D - a) * (/ 2)).
  assert (He : 0 < eps) by (unfold eps, a in *; lra).
  set (crit := fun p q : R * R => nnum sigma p q / (2 * (snd p - snd q))).
  set (L := flat_map (fun p => map (crit p) F) F).
  destruct (avoid (snd rho1) eps L He) as [t [Ht [Hte Hav]]].
  set (gamma := snd rho1 + t).
  set (f := d2 sigma gamma).
  assert (Hf1 : f rho1 < D * D).
  { unfold f, d2, gamma. fold a.
    assert (Hg : snd rho1 + t - snd rho1 = t) by ring. rewrite Hg.
    unfold eps in Hte. unfold a in *. nra. }
  assert (H1F : In rho1 F).
  { apply HF; [exact H1|unfold a in Ha; lra|]. split; lra. }
  set (m := minl f F (f rho1)).
  assert (Hrho : exists rho, In rho F /\ m = f rho).
  { destruct (minl_cases f F (f rho1)) as [H|H]; [exists rho1; split; assumption|exact H]. }
  destruct Hrho as [rho [HrF Hm]].
  assert (Hmle : m <= f rho1) by apply minl_le_d.
  assert (HmD : m < D * D) by lra.
  assert (Huniq : forall w, In w F -> f w = m -> peq w rho).
  { intros w Hw Hfw. apply (nearest_equi sigma gamma w rho).
    - apply Hle, HFZ, Hw.
    - apply Hle, HFZ, HrF.
    - unfold f in *. lra.
    - intros Hne Hc. apply (Hav t Ht (Rle_refl t) (crit w rho)).
      + unfold L. apply in_flat_map. exists w. split; [exact Hw|]. apply in_map. exact HrF.
      + assert (Hden : ~ 2 * (snd w - snd rho) = 0) by (intro; apply Hne; lra).
        fold gamma. unfold crit. rewrite <- Hc. field. intro Hz; apply Hne; lra. }
  set (r2 := minl (above f m (D * D)) F (D * D)).
  exists gamma, rho, r2. split; [apply HFZ, HrF|]. split; [|split].
  - change (f rho < r2). pose proof (above_gt f F m (D * D) HmD) as Hg. fold r2 in Hg. lra.
  - apply minl_le_d.
  - intros w HwZ Hw. change (f w < r2) in Hw.
    assert (HwD : f w < D * D) by (pose proof (minl_le_d (above f m (D * D)) F (D * D)); fold r2 in H; lra).
    pose proof (Hle w HwZ) as Hws.
    assert (HwF : In w F).
    { apply HF; [exact HwZ| |].
      - assert (sigma - fst w < D).
        { apply sq_lt_inv; [lra|lra|]. unfold f, d2 in HwD.
          pose proof (sq_nonneg (gamma - snd w)). lra. }
        lra.
      - assert (Hg : (gamma - snd w) * (gamma - snd w) < D * D).
        { unfold f, d2 in HwD. pose proof (sq_nonneg (sigma - fst w)). lra. }
        destruct (abs_of_sq_lt _ _ HD Hg) as [Hg1 Hg2].
        unfold gamma in Hg1, Hg2. unfold eps, a in Hte. split; lra. }
    pose proof (above_sep f F m (D * D) w HwF Hw) as Hwm.
    pose proof (minl_le_mem f F (f rho1) w HwF) as Hmw. fold m in Hmw.
    apply Huniq; [exact HwF|lra].
Qed.


(* ===================================================================== *)
(* Part B: landau_window                                                  *)
(* ===================================================================== *)
Lemma sqrt_lt_of_sq : forall a b, 0 <= a -> 0 <= b -> a * a < b -> a < sqrt b.
Proof.
  intros a b Ha Hb H. rewrite <- (sqrt_Rsqr a Ha). apply sqrt_lt_1_alt. unfold Rsqr. split; [nra|exact H].
Qed.

Lemma sq_lt_of_sqrt : forall a b, 0 <= a -> 0 <= b -> a < sqrt b -> a * a < b.
Proof.
  intros a b Ha Hb H. pose proof (sqrt_pos b). pose proof (sqrt_sqrt b Hb). nra.
Qed.

Lemma d2_nonneg : forall s g w, 0 <= d2 s g w.
Proof. intros. unfold d2. pose proof (sq_nonneg (s - fst w)). pose proof (sq_nonneg (g - snd w)). lra. Qed.

Lemma div_pow_succ : forall c d (k : nat), 0 < d -> c / d ^ (S k) = c / d / d ^ k.
Proof. intros c d k Hd. simpl. assert (d ^ k <> 0) by (apply pow_nonzero; lra). field. split; lra. Qed.

Section Assembly.
Variable Z : R * R -> Prop.
Variables sigma theta : R.
Hypothesis Htheta : 0 < theta.
Hypothesis Hts : theta < sigma.
Hypothesis Hle : forall w, Z w -> fst w < sigma.                    (* [inventory] landau_pole_re_le *)
Hypothesis LF : forall lo y0 Rr, 0 < lo -> exists F : list (R * R),  (* [inventory] landau_finite *)
  (forall w, In w F -> Z w) /\
  (forall w, Z w -> lo <= fst w -> - Rr <= snd w - y0 <= Rr -> In w F).
Variables (A : nat -> R -> R) (B : nat -> R).                      (* norm of coef at sigma+i g; Re of coef at sigma *)
Hypothesis HA : forall k g, 0 <= A k g.
(* [inventory] landau_window_key, in Lean's form *)
Hypothesis KEY : exists C, forall eta, 0 < eta -> forall U0, exists U, U0 <= U /\ exists k : nat, U <= INR k /\
  forall g, A k g + B k <= C * exp (eta * U) / (sigma - theta) ^ k.
(* [inventory] landau_cauchy on a pole-free disc about sigma *)
Hypothesis CAUCHY : forall D2 e, (forall w, Z w -> ~ d2 sigma 0 w < D2) ->
  0 < e -> e * e < D2 -> exists M, forall k, - (M / e ^ k) <= B k.
(* [inventory] landau_pole_asym at an isolated pole of sigma + i g *)
Hypothesis POLE1 : forall g rho r2 e, Z rho ->
  (forall w, Z w -> d2 sigma g w < r2 -> peq w rho) ->
  sqrt (d2 sigma g rho) < e -> e * e < r2 ->
  exists c M, 0 < c /\ forall k, c / sqrt (d2 sigma g rho) ^ (S k) - M / e ^ k <= A k g.
(* [inventory] landau_pole_asym at an isolated REAL pole, with Re c > 0 *)
Hypothesis POLE2 : forall beta r2 e, Z beta -> snd beta = 0 ->
  (forall w, Z w -> d2 sigma 0 w < r2 -> peq w beta) ->
  sigma - fst beta < e -> e * e < r2 ->
  exists cr M, 0 < cr /\ forall k, cr / (sigma - fst beta) ^ (S k) - M / e ^ k <= B k.

Theorem landau_window : forall rho0, Z rho0 -> fst rho0 <= theta.
Proof.
  intros rho0 H0. destruct (Rle_lt_dec (fst rho0) theta) as [Hx|Hx]; [exact Hx|exfalso].
  set (E := sigma - theta) in *.
  assert (HE : 0 < E) by (unfold E; lra).
  destruct KEY as [C HK].
  destruct (LF theta 0 E Htheta) as [F0 [HF0Z HF0]].
  set (F := filter (fun w => if Rle_dec (d2 sigma 0 w) (E * E) then true else false) F0).
  assert (HF : forall w, Z w -> d2 sigma 0 w <= E * E -> In w F).
  { intros w Hw Hd. unfold F. apply filter_In. split; [|destruct (Rle_dec (d2 sigma 0 w) (E * E)); [reflexivity|contradiction]].
    pose proof (Hle w Hw). unfold d2 in Hd.
    pose proof (sq_nonneg (sigma - fst w)). pose proof (sq_nonneg (0 - snd w)).
    apply HF0; [exact Hw| |].
    - assert (sigma - fst w <= E) by (apply sq_le_inv; lra). unfold E in *. lra.
    - assert (Hy : (0 - snd w) * (0 - snd w) <= E * E) by lra. split; nra. }
  assert (HFZ : forall w, In w F -> Z w /\ d2 sigma 0 w <= E * E).
  { intros w Hw. unfold F in Hw. apply filter_In in Hw. destruct Hw as [Hw Hb].
    split; [apply HF0Z; exact Hw|]. destruct (Rle_dec (d2 sigma 0 w) (E * E)); [assumption|discriminate]. }
  destruct (landau_dichotomy Z F sigma theta rho0 Hts HF HFZ Hle H0 Hx)
    as [[D2 [HD2 [Hfree [rho1 [H1 Hr1]]]]]
       |[beta [HbZ [Hby [Hbt [r2 [Hbr [Hr2E Hiso]]]]]]]].
  - (* non-real nearest pole: norm at sigma + i g *)
    fold E in HD2.
    pose proof (Hle rho1 H1) as Hx1.
    assert (HD20 : 0 <= D2) by (pose proof (sq_nonneg (sigma - fst rho1)); lra).
    set (D := sqrt D2).
    assert (HlD : sigma - fst rho1 < D) by (unfold D; apply sqrt_lt_of_sq; lra).
    assert (HDE : D <= E) by (unfold D; rewrite <- (sqrt_Rsqr E) by lra; apply sqrt_le_1_alt; unfold Rsqr; lra).
    assert (HD0 : 0 < D) by lra.
    destruct (LF (sigma - D) (snd rho1) (2 * D) ltac:(unfold E in HDE; lra)) as [F1 [HF1Z HF1]].
    destruct (landau_nearest Z F1 sigma D rho1 Hle H1 HlD HF1 HF1Z) as [g [rho [r2 [HrZ [Hdr [Hr2D Hiso]]]]]].
    set (d := sqrt (d2 sigma g rho)).
    assert (Hd0 : 0 <= d) by apply sqrt_pos.
    assert (Hr20 : 0 <= r2) by (pose proof (d2_nonneg sigma g rho); lra).
    set (r := sqrt r2).
    assert (Hdr' : d < r) by (unfold d, r; apply sqrt_lt_1_alt; split; [apply d2_nonneg|exact Hdr]).
    assert (Hd : 0 < d).
    { unfold d. apply sqrt_lt_R0. destruct (Rle_lt_dec (d2 sigma g rho) 0) as [Hz|Hz]; [|exact Hz]. exfalso.
      assert (Hz0 : d2 sigma g rho = 0) by (pose proof (d2_nonneg sigma g rho); lra).
      unfold d2 in Hz0. pose proof (sq_nonneg (sigma - fst rho)). pose proof (sq_nonneg (g - snd rho)).
      assert ((sigma - fst rho) * (sigma - fst rho) = 0) by lra. pose proof (Hle rho HrZ). nra. }
    assert (HDD : D * D = D2) by (unfold D; apply sqrt_sqrt; lra).
    assert (HrD : r <= D) by (unfold r, D; apply sqrt_le_1_alt; fold D; lra).
    set (e := (d + r) / 2).
    assert (Hde : d < e) by (unfold e; lra).
    assert (Her : e < r) by (unfold e; lra).
    assert (Hee : e * e < r2) by (apply sq_lt_of_sqrt; [lra|lra|fold r; lra]).
    assert (HeD2 : e * e < D2) by (apply sq_lt_of_sqrt; [lra|lra|fold D; lra]).
    destruct (POLE1 g rho r2 e HrZ Hiso Hde Hee) as [c [M1 [Hc HM1]]].
    destruct (CAUCHY D2 e Hfree ltac:(lra) HeD2) as [M2 HM2].
    apply (landau_window_contra (c / d) d e E (M1 + M2) C ltac:(apply Rdiv_lt_0_compat; lra) Hd Hde ltac:(lra)).
    intros eta Heta U0. destruct (HK eta Heta U0) as [U [HU [k [Hk Hb]]]].
    exists U. split; [exact HU|]. exists k. split; [exact Hk|].
    pose proof (Hb g) as H1'. pose proof (HM1 k) as H2'. pose proof (HM2 k) as H3'.
    fold d in H2'. rewrite div_pow_succ in H2' by exact Hd.
    assert (Hm : (M1 + M2) / e ^ k = M1 / e ^ k + M2 / e ^ k) by (field; apply pow_nonzero; lra).
    pose proof (HA k g). lra.
  - (* real nearest pole beta: real part at sigma *)
    fold E in Hr2E.
    pose proof (Hle beta HbZ) as Hxb.
    set (d := sigma - fst beta) in *.
    assert (Hd : 0 < d) by (unfold d; lra).
    assert (Hr20 : 0 <= r2) by (pose proof (sq_nonneg d); lra).
    set (r := sqrt r2).
    assert (Hdr' : d < r) by (unfold r; apply sqrt_lt_of_sq; lra).
    assert (HrE : r <= E) by (unfold r; rewrite <- (sqrt_Rsqr E) by lra; apply sqrt_le_1_alt; unfold Rsqr; lra).
    set (e := (d + r) / 2).
    assert (Hde : d < e) by (unfold e; lra).
    assert (Hee : e * e < r2) by (apply sq_lt_of_sqrt; [unfold e; lra|lra|fold r; unfold e; lra]).
    destruct (POLE2 beta r2 e HbZ Hby Hiso Hde Hee) as [cr [M [Hcr HM]]].
    apply (landau_window_contra (cr / d) d e E M C ltac:(apply Rdiv_lt_0_compat; lra) Hd Hde ltac:(unfold e; lra)).
    intros eta Heta U0. destruct (HK eta Heta U0) as [U [HU [k [Hk Hb]]]].
    exists U. split; [exact HU|]. exists k. split; [exact Hk|].
    pose proof (Hb 0) as H1'. pose proof (HM k) as H2'.
    fold d in H2'. rewrite div_pow_succ in H2' by exact Hd.
    pose proof (HA k 0). lra.
Qed.
End Assembly.

Print Assumptions landau_dichotomy.
Print Assumptions landau_nearest.
Print Assumptions landau_window.

(* ===================================================================== *)
(* Part C: landau_tails  (composed with landau_tails_chernoff)            *)
(* ===================================================================== *)
(* the parameter arithmetic of landau_tails over R *)
Lemma tails_params_R : forall delta U kq, 0 < delta -> 1 <= U ->
  let l := 2 + 6 / delta in let M := l * (1 + delta) in let sigma := M * (2 + l) in
  (1 + delta / 2) * sigma * U <= kq -> kq <= (1 + delta / 2) * sigma * U + 1 ->
  2 < sigma /\ 0 < sigma - 2 - l /\ 0 < sigma - 2 + l /\ U <= kq /\
  kq * (2 + l) <= (sigma - 2 - l) * (1 + l * (1 + delta) * U) /\
  l * U * (sigma - 2 + l) <= kq * (l - 2).
Proof.
  intros delta U kq Hd HU l M sigma Hk1 Hk2.
  assert (Hl : l * delta = 6 + 2 * delta) by (unfold l; field; lra).
  assert (H6 : 0 < 6 / delta) by (apply Rdiv_lt_0_compat; lra).
  assert (Hl2 : 2 < l) by (unfold l; lra).
  assert (EM : M = l + (6 + 2 * delta)) by (unfold M; rewrite <- Hl; ring).
  assert (HM : l < M) by lra.
  assert (Hs : l * (2 + l) < sigma) by (unfold sigma; nra).
  assert (E1 : (2 + l) * (M - 1) = sigma - 2 - l) by (unfold sigma; ring).
  assert (E2 : (1 + delta / 2) * (2 + l) = M - 1) by (rewrite EM; field_simplify; nra).
  assert (E3 : (1 + delta / 2) * (l - 2) = l + 1) by nra.
  assert (Ha : 0 < sigma - 2 - l) by nra.
  assert (Hf : (1 + delta / 2) * sigma = M * (M - 1)) by (unfold sigma; rewrite <- E2; ring).
  split; [nra|]. split; [exact Ha|]. split; [lra|]. split.
  - assert (U <= sigma * U) by nra. assert (sigma * U <= (1 + delta / 2) * sigma * U) by nra. lra.
  - split.
    + assert (Hk : kq <= M * (M - 1) * U + 1) by (rewrite <- Hf; lra).
      assert (H1 : kq * (2 + l) <= (M * (M - 1) * U + 1) * (2 + l)) by (apply Rmult_le_compat_r; lra).
      assert (E4 : (M * (M - 1) * U + 1) * (2 + l) = (sigma - 2 - l) * (M * U) + (2 + l)) by (rewrite <- E1; ring).
      assert (H2 : 2 + l <= sigma - 2 - l) by (rewrite <- E1; nra).
      assert (E5 : (sigma - 2 - l) * (1 + l * (1 + delta) * U) = (sigma - 2 - l) + (sigma - 2 - l) * (M * U)) by (unfold M; ring).
      lra.
    + assert (H1 : (1 + delta / 2) * sigma * U * (l - 2) <= kq * (l - 2)) by (apply Rmult_le_compat_r; lra).
      assert (E6 : (1 + delta / 2) * sigma * U * (l - 2) = (l + 1) * sigma * U) by (rewrite <- E3; ring).
      assert (H3 : l * (sigma - 2 + l) <= (l + 1) * sigma) by nra.
      assert (H4 : l * (sigma - 2 + l) * U <= (l + 1) * sigma * U) by (apply Rmult_le_compat_r; lra).
      lra.
Qed.

(* the integer k = ceil-like of X >= 0, via archimed *)
Lemma ceil_nat_R : forall X, 0 <= X -> exists k : nat, X <= INR k /\ INR k <= X + 1.
Proof.
  intros X HX. destruct (archimed X) as [H1 H2].
  assert (Hz : (0 <= up X)%Z) by (apply le_IZR; lra).
  exists (Z.to_nat (up X)). rewrite INR_IZR_INZ, Z2Nat.id by exact Hz. lra.
Qed.

Section Tails.
Variable delta : R.
Hypothesis Hdelta : 0 < delta.
(* T sigma U k = int over (0,oo) \ [U, (1+delta) U] of u^k e^((2-sigma) u) / k! *)
Variable T : R -> R -> nat -> R.
(* [inventory] landau_tails_chernoff, with s = sigma - 2 and V = (1+delta) U *)
Hypothesis CHER : forall sigma U (k : nat) l, 0 <= l -> l < sigma - 2 ->
  T sigma U k <= exp (- (l * ((1 + delta) * U))) * / (sigma - 2 - l) ^ (k + 1)
               + exp (l * U) * / (sigma - 2 + l) ^ (k + 1).

Theorem landau_tails : exists sigma, 2 < sigma /\ exists C, forall U, 1 <= U ->
  exists k : nat, U <= INR k /\ T sigma U k <= C / sigma ^ k.
Proof.
  set (l := 2 + 6 / delta). set (M := l * (1 + delta)). set (sigma := M * (2 + l)).
  assert (H6 : 0 < 6 / delta) by (apply Rdiv_lt_0_compat; lra).
  assert (Hl2 : 2 < l) by (unfold l; lra).
  destruct (ceil_nat_R ((1 + delta / 2) * sigma * 1)) as [k0 [Hk01 Hk02]].
  { unfold sigma, M. assert (0 < l * (1 + delta)) by nra. nra. }
  destruct (tails_params_R delta 1 (INR k0) Hdelta (Rle_refl 1) Hk01 Hk02) as [Hs2 [Ha [Hb _]]].
  fold l M sigma in Hs2, Ha, Hb.
  exists sigma. split; [exact Hs2|].
  exists (exp 1 / (sigma - 2 - l) + exp 0 / (sigma - 2 + l)).
  intros U HU.
  assert (HX : 0 <= (1 + delta / 2) * sigma * U) by (assert (0 <= sigma * U) by nra; nra).
  destruct (ceil_nat_R _ HX) as [k [Hk1 Hk2]].
  destruct (tails_params_R delta U (INR k) Hdelta HU Hk1 Hk2) as [_ [_ [_ [HUk [T1 T2]]]]].
  fold l M sigma in HUk, T1, T2.
  exists k. split; [exact HUk|].
  pose proof (CHER sigma U k l ltac:(lra) ltac:(lra)) as HC.
  set (a := sigma - 2 - l) in *. set (b := sigma - 2 + l) in *.
  assert (P1 : exp (- (l * ((1 + delta) * U))) * / a ^ (k + 1) <= exp 1 / a / sigma ^ k).
  { apply landau_tails_pow; [lra|exact Ha|].
    replace ((sigma - a) / a) with ((2 + l) / a) by (unfold Rdiv, a; ring).
    assert (Hq : INR k * ((2 + l) / a) <= 1 + l * (1 + delta) * U).
    { apply (Rmult_le_reg_r a); [exact Ha|].
      assert (Ha0 : a <> 0) by lra.
      replace (INR k * ((2 + l) / a) * a) with (INR k * (2 + l)) by (field; exact Ha0). rewrite (Rmult_comm (1 + _) a). exact T1. }
    lra. }
  assert (P2 : exp (l * U) * / b ^ (k + 1) <= exp 0 / b / sigma ^ k).
  { apply landau_tails_pow; [lra|exact Hb|].
    replace ((sigma - b) / b) with (- ((l - 2) / b)) by (unfold Rdiv, b; ring).
    assert (Hq : l * U <= INR k * ((l - 2) / b)).
    { apply (Rmult_le_reg_r b); [exact Hb|].
      assert (Hb0 : b <> 0) by lra.
      replace (INR k * ((l - 2) / b) * b) with (INR k * (l - 2)) by (field; exact Hb0). exact T2. }
    lra. }
  assert (Hsk : 0 < sigma ^ k) by (apply pow_lt; lra).
  assert (Ha0 : a <> 0) by lra. assert (Hb0 : b <> 0) by lra. assert (Hsk0 : sigma ^ k <> 0) by lra.
  assert (E : exp 1 / a / sigma ^ k + exp 0 / b / sigma ^ k = (exp 1 / a + exp 0 / b) / sigma ^ k)
    by (field; repeat split; assumption).
  lra.
Qed.
End Tails.

(* ===================================================================== *)
(* Part D: landau_window_key                                              *)
(* ===================================================================== *)
Section Key.
Variables theta : R.
Hypothesis Htheta : 0 < theta.
Hypothesis Htheta1 : theta < 1.
Variables (A : R -> nat -> R -> R) (B : R -> nat -> R).   (* coefficients at sigma (+ i g) *)
Variable T : R -> R -> nat -> R.                          (* tail integrals *)
Hypothesis T_nonneg : forall sigma U k, 0 <= T sigma U k.
Variable C0 : R.                                          (* PoleData.growth *)
Hypothesis C0_nonneg : 0 <= C0.
(* landau_tails (Part C) *)
Hypothesis TAILS : exists sigma, 2 < sigma /\ exists C, forall U, 1 <= U ->
  exists k : nat, U <= INR k /\ T sigma U k <= C / sigma ^ k.
(* [inventory] WindowHypU + landau_coeff + landau_window_ineq, at every sigma > 2 *)
Hypothesis WI : forall sigma, 2 < sigma -> forall eta, 0 < eta -> forall U0, exists U, U0 <= U /\ 1 <= U /\
  exists Iw, Iw <= exp (eta * U) /\ forall (k : nat) g,
    A sigma k g + B sigma k <= 2 * (1 / (sigma - theta) ^ k) * Iw + 2 * C0 * T sigma U k.

Theorem landau_window_key : exists sigma, 2 < sigma /\ exists C, forall eta, 0 < eta -> forall U0,
  exists U, U0 <= U /\ exists k : nat, U <= INR k /\
    forall g, A sigma k g + B sigma k <= C * exp (eta * U) / (sigma - theta) ^ k.
Proof.
  destruct TAILS as [sigma [Hs [Ct HT]]].
  exists sigma. split; [exact Hs|]. exists (2 + 2 * C0 * Rabs Ct). intros eta Heta U0.
  destruct (WI sigma Hs eta Heta U0) as [U [HU0 [HU1 [Iw [HI Hb]]]]].
  destruct (HT U HU1) as [k [Hk HTk]].
  exists U. split; [exact HU0|]. exists k. split; [exact Hk|]. intro g. specialize (Hb k g).
  set (E := sigma - theta).
  assert (HE : 0 < E) by (unfold E; lra).
  assert (HEk : 0 < E ^ k) by (apply pow_lt; exact HE).
  assert (Hsk : 0 < sigma ^ k) by (apply pow_lt; lra).
  assert (HEs : E ^ k <= sigma ^ k) by (apply pow_le_mono; unfold E; lra).
  set (X := exp (eta * U)).
  assert (HX : 1 <= X) by (unfold X; pose proof (add_one_le_exp (eta * U)); nra).
  assert (H1 : 2 * (1 / E ^ k) * Iw <= 2 * X / E ^ k).
  { replace (2 * X / E ^ k) with (2 * (1 / E ^ k) * X) by (field; lra).
    apply Rmult_le_compat_l; [apply Rmult_le_pos; [lra|left; apply Rdiv_lt_0_compat; lra]|exact HI]. }
  assert (H2 : T sigma U k <= Rabs Ct * X / E ^ k).
  { apply Rle_trans with (Ct / sigma ^ k); [exact HTk|].
    apply Rle_trans with (Rabs Ct / sigma ^ k).
    - unfold Rdiv. apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; exact Hsk|apply Rle_abs].
    - pose proof (Rabs_pos Ct).
      apply Rle_trans with (Rabs Ct / E ^ k).
      + unfold Rdiv. apply Rmult_le_compat_l; [lra|]. apply Rinv_le_contravar; lra.
      + unfold Rdiv. rewrite Rmult_assoc, (Rmult_comm X), <- Rmult_assoc.
        assert (0 <= Rabs Ct * / E ^ k) by (apply Rmult_le_pos; [lra|left; apply Rinv_0_lt_compat; lra]). nra. }
  assert (H3 : 2 * C0 * T sigma U k <= 2 * C0 * (Rabs Ct * X / E ^ k)) by (apply Rmult_le_compat_l; lra).
  assert (E4 : (2 + 2 * C0 * Rabs Ct) * X / E ^ k = 2 * X / E ^ k + 2 * C0 * (Rabs Ct * X / E ^ k)) by (field; lra).
  fold E X in Hb. lra.
Qed.
End Key.

Print Assumptions landau_tails.
Print Assumptions landau_window_key.

(* ===================================================================== *)
(* Part E: proposition_size_bound (GrowthSizeBound) and ch_core           *)
(* ===================================================================== *)
Lemma ge1_mul_R : forall a b : R, 1 <= a -> 1 <= b -> 1 <= a * b.
Proof. intros; nra. Qed.
Lemma le_mul_ge1_R : forall x z : R, 0 <= x -> 1 <= z -> x <= x * z.
Proof. intros; nra. Qed.
Lemma mul_le_l_R : forall x y z : R, 0 <= z -> x <= y -> z * x <= z * y.
Proof. intros. apply Rmult_le_compat_l; assumption. Qed.

Section BalanceR.

Variables s e e2 e8 c b n nT nT2 m k aE Err Gx q1 q2 rho w : R.
Hypothesis Hs : 1 <= s.
Hypothesis Hs3 : 3 <= s * s.
Hypothesis He : 1 <= e.
Hypothesis He2 : 1 <= e2.
Hypothesis He8 : 1 <= e8.
Hypothesis Hc : 1 <= c.
Hypothesis H26 : 26 <= e8 * e8 * e8.
Hypothesis Hb : 0 < b.
Hypothesis Hn : 0 < n.
Hypothesis HaE0 : 0 <= aE.
Hypothesis HaE : aE <= 2 * (s * s) * b.
Hypothesis HnT : n <= 2 * e8 * nT.
Hypothesis Hrho : rho * n = nT2.
Hypothesis Hrho1 : 1 <= e * rho.
Hypothesis Hm1 : s <= e * m.
Hypothesis Hm2 : m <= s * e2.
Hypothesis Hk1 : s * s * m <= k.
Hypothesis Hk2 : e * k <= n * n * s.
Hypothesis Hq1 : q1 * k = m * m.
Hypothesis Hq2 : q2 * (n * n) = nT2 * k * b * (e * e).
Hypothesis HErr : Err <= c * (nT * aE * (1 + q1) + m * (2 * n * m * b * e + q2)).
Hypothesis Hw : w * (s * s) = 1.
Hypothesis Hmain : nT * m * b * rho * (Gx - 4 * s * e) <= 2 * Err + 4 * nT * m * b * w.

Theorem growth_size_bound_R :
  Gx <= e8 * e8 * e8 * (s * c * (e * e) * e2 * e8).
Proof.
  (* positivity *)
  assert (Hrho0 : 0 < rho) by nra.
  assert (Hm0 : 0 < m) by nra.
  assert (HnT0 : 0 < nT) by nra.
  assert (Hk0 : 0 < k) by nra.
  assert (Hq10 : 0 <= q1) by nra.
  assert (Hw0 : 0 < w) by nra.
  assert (Hw3 : w <= / 3) by nra.
  set (D := nT * m * b * rho).
  assert (HD : 0 < D) by (unfold D; repeat apply Rmult_lt_0_compat; lra).
  set (T := s * c * (e * e) * e2 * e8).
  assert (HT : 0 < T) by (unfold T; repeat apply Rmult_lt_0_compat; lra).
  (* (i) aE-term:  2 c nT aE (1+q1) <= D * (8 c e^2 s) *)
  assert (I1 : q1 * (s * s) <= m).
  { assert (q1 * (s * s * m) <= q1 * k) by nra.
    assert (q1 * (s * s) * m <= m * m) by nra. nra. }
  assert (I2 : aE * (1 + q1) <= 2 * b * (s * s + m)).
  { assert (aE * (1 + q1) <= 2 * (s * s) * b * (1 + q1)) by nra. nra. }
  assert (I3 : s * s + m <= 2 * e * m * s) by nra.
  assert (A1 : aE * (1 + q1) <= 2 * b * (2 * e * m * s)).
  { apply Rle_trans with (2 * b * (s * s + m)); [exact I2|]. apply mul_le_l_R; [lra|exact I3]. }
  assert (Hee : e <= e * e * rho) by nra.
  assert (Ti : 2 * c * (nT * aE * (1 + q1)) <= D * (8 * c * (e * e) * s)).
  { apply Rle_trans with ((2 * c * nT) * (2 * b * (2 * e * m * s))).
    - replace (2 * c * (nT * aE * (1 + q1))) with ((2 * c * nT) * (aE * (1 + q1))) by ring.
      apply mul_le_l_R; [nra | exact A1].
    - unfold D.
      replace ((2 * c * nT) * (2 * b * (2 * e * m * s))) with ((8 * c * nT * b * m * s) * e) by ring.
      replace (nT * m * b * rho * (8 * c * (e * e) * s)) with ((8 * c * nT * b * m * s) * (e * e * rho)) by ring.
      apply mul_le_l_R; [|exact Hee].
      assert (0 <= c * nT) by nra. assert (0 <= c * nT * b) by nra. assert (0 <= c * nT * b * m) by nra. nra. }
  (* (ii) 2nmb-term:  2 c m (2 n m b e) <= D * (8 c e8 e^2 s e2) *)
  assert (Tii : 2 * c * (m * (2 * n * m * b * e)) <= D * (8 * c * e8 * (e * e) * s * e2)).
  { assert (Z0 : 0 <= 4 * c * m * m * b * e) by (assert (0 <= c * m) by nra; assert (0 <= c * m * m) by nra; assert (0 <= c * m * m * b) by nra; nra).
    apply Rle_trans with ((4 * c * m * m * b * e) * (2 * e8 * nT)).
    - replace (2 * c * (m * (2 * n * m * b * e))) with ((4 * c * m * m * b * e) * n) by ring.
      apply mul_le_l_R; [exact Z0 | exact HnT].
    - assert (Z1 : 0 <= 8 * c * m * b * e * e8 * nT) by (assert (0 <= c * m) by nra; assert (0 <= c * m * b) by nra; assert (0 <= c * m * b * e) by nra; assert (0 <= c * m * b * e * e8) by nra; nra).
      apply Rle_trans with ((8 * c * m * b * e * e8 * nT) * (s * e2)).
      + replace ((4 * c * m * m * b * e) * (2 * e8 * nT)) with ((8 * c * m * b * e * e8 * nT) * m) by ring.
        apply mul_le_l_R; [exact Z1 | exact Hm2].
      + unfold D.
        replace ((8 * c * m * b * e * e8 * nT) * (s * e2)) with ((8 * c * m * b * e8 * nT * s * e2) * e) by ring.
        replace (nT * m * b * rho * (8 * c * e8 * (e * e) * s * e2)) with ((8 * c * m * b * e8 * nT * s * e2) * (e * e * rho)) by ring.
        apply mul_le_l_R; [|exact Hee].
        assert (0 <= c * m) by nra; assert (0 <= c * m * b) by nra; assert (0 <= c * m * b * e8) by nra;
        assert (0 <= c * m * b * e8 * nT) by nra; assert (0 <= c * m * b * e8 * nT * s) by nra; nra. }
  (* (iii) q2-term:  2 c m q2 <= D * (4 c e s e8) *)
  assert (Q1 : q2 * n = rho * k * b * (e * e)).
  { assert (q2 * n * n = rho * n * k * b * (e * e)) by (rewrite Hrho; nra). nra. }
  assert (Zrb : 0 <= rho * b * (e * e)) by (assert (0 <= rho * b) by nra; nra).
  assert (Q2 : q2 <= rho * b * e * n * s).
  { assert (E1 : q2 * n * e = rho * b * (e * e) * (e * k)).
    { rewrite Q1. ring. }
    assert (E2 : q2 * n * e <= rho * b * (e * e) * (n * n * s)).
    { rewrite E1. apply mul_le_l_R; [exact Zrb | exact Hk2]. }
    assert (Hne : 0 < n * e) by (apply Rmult_lt_0_compat; lra).
    apply (Rmult_le_reg_l (n * e)); [exact Hne|].
    replace (n * e * q2) with (q2 * n * e) by ring.
    replace (n * e * (rho * b * e * n * s)) with (rho * b * (e * e) * (n * n * s)) by ring.
    exact E2. }
  assert (Zcm : 0 <= 2 * c * m) by nra.
  assert (Tiii : 2 * c * (m * q2) <= D * (4 * c * e * s * e8)).
  { apply Rle_trans with ((2 * c * m) * (rho * b * e * n * s)).
    - replace (2 * c * (m * q2)) with ((2 * c * m) * q2) by ring.
      apply mul_le_l_R; [exact Zcm | exact Q2].
    - assert (Z2 : 0 <= 2 * c * m * rho * b * e * s).
      { assert (0 <= c * m) by nra. assert (0 <= c * m * rho) by nra.
        assert (0 <= c * m * rho * b) by nra. assert (0 <= c * m * rho * b * e) by nra. nra. }
      apply Rle_trans with ((2 * c * m * rho * b * e * s) * (2 * e8 * nT)).
      + replace ((2 * c * m) * (rho * b * e * n * s)) with ((2 * c * m * rho * b * e * s) * n) by ring.
        apply mul_le_l_R; [exact Z2 | exact HnT].
      + unfold D. right. ring. }
  (* (iv) 4 nT m b w <= D * (4/3) e *)
  assert (Znmb : 0 <= nT * m * b) by (assert (0 <= nT * m) by nra; nra).
  assert (Tiv : 4 * nT * m * b * w <= D * ((4 / 3) * e)).
  { unfold D.
    replace (4 * nT * m * b * w) with ((nT * m * b) * (4 * w)) by ring.
    replace (nT * m * b * rho * ((4 / 3) * e)) with ((nT * m * b) * ((4 / 3) * (e * rho))) by ring.
    apply mul_le_l_R; [exact Znmb | lra]. }
  (* assemble: D (Gx - 4se) <= D (X1 + X2 + X3 + X4) *)
  assert (HE2 : 2 * Err <= 2 * c * (nT * aE * (1 + q1)) + 2 * c * (m * (2 * n * m * b * e)) + 2 * c * (m * q2)).
  { assert (2 * Err <= 2 * (c * (nT * aE * (1 + q1) + m * (2 * n * m * b * e + q2)))) by lra.
    replace (2 * (c * (nT * aE * (1 + q1) + m * (2 * n * m * b * e + q2))))
      with (2 * c * (nT * aE * (1 + q1)) + 2 * c * (m * (2 * n * m * b * e)) + 2 * c * (m * q2)) in H by ring.
    exact H. }
  assert (Hsum : D * (Gx - 4 * s * e) <=
                 D * (8 * c * (e * e) * s + 8 * c * e8 * (e * e) * s * e2 + 4 * c * e * s * e8 + (4 / 3) * e)).
  { assert (HM : D * (Gx - 4 * s * e) <= 2 * Err + 4 * nT * m * b * w) by (unfold D; exact Hmain).
    replace (D * (8 * c * (e * e) * s + 8 * c * e8 * (e * e) * s * e2 + 4 * c * e * s * e8 + (4 / 3) * e))
      with (D * (8 * c * (e * e) * s) + D * (8 * c * e8 * (e * e) * s * e2) + D * (4 * c * e * s * e8) + D * ((4 / 3) * e))
      by ring.
    lra. }
  assert (Hcan : Gx - 4 * s * e <= 8 * c * (e * e) * s + 8 * c * e8 * (e * e) * s * e2 + 4 * c * e * s * e8 + (4 / 3) * e).
  { apply (Rmult_le_reg_l D); [exact HD|]. exact Hsum. }
  (* each piece <= coefficient * T, total <= 26 T <= e8^3 T *)
  assert (Zs : 0 <= s) by lra. assert (Ze : 0 <= e) by lra. assert (Zc : 0 <= c) by lra.
  assert (P1 : s * e <= T).
  { unfold T. replace (s * c * (e * e) * e2 * e8) with ((s * e) * (c * e * e2 * e8)) by ring.
    apply le_mul_ge1_R; [nra|]. repeat apply ge1_mul_R; lra. }
  assert (P2 : c * (e * e) * s <= T).
  { unfold T. replace (s * c * (e * e) * e2 * e8) with ((c * (e * e) * s) * (e2 * e8)) by ring.
    apply le_mul_ge1_R; [|apply ge1_mul_R; lra].
    assert (0 <= c * (e * e)) by nra. nra. }
  assert (P3 : c * e8 * (e * e) * s * e2 = T) by (unfold T; ring).
  assert (P4 : c * e * s * e8 <= T).
  { unfold T. replace (s * c * (e * e) * e2 * e8) with ((c * e * s * e8) * (e * e2)) by ring.
    apply le_mul_ge1_R; [|apply ge1_mul_R; lra].
    assert (0 <= c * e) by nra. assert (0 <= c * e * s) by nra. nra. }
  assert (P5 : e <= T).
  { unfold T. replace (s * c * (e * e) * e2 * e8) with (e * (s * c * e * e2 * e8)) by ring.
    apply le_mul_ge1_R; [lra|]. repeat apply ge1_mul_R; lra. }
  assert (G26 : Gx <= 26 * T).
  { replace (8 * c * (e * e) * s) with (8 * (c * (e * e) * s)) in Hcan by ring.
    replace (8 * c * e8 * (e * e) * s * e2) with (8 * (c * e8 * (e * e) * s * e2)) in Hcan by ring.
    replace (4 * c * e * s * e8) with (4 * (c * e * s * e8)) in Hcan by ring.
    replace (4 * s * e) with (4 * (s * e)) in Hcan by ring.
    rewrite P3 in Hcan. lra. }
  assert (H26T : 26 * T <= e8 * e8 * e8 * T).
  { apply Rmult_le_compat_r; [lra | exact H26]. }
  lra.
Qed.

End BalanceR.

Lemma rpc_0 : forall x, rpc x 0 = 1.
Proof. intro x. unfold rpc. rewrite Rmult_0_l. apply exp_0. Qed.
Lemma rpc_ge1 : forall x a, 1 <= x -> 0 <= a -> 1 <= rpc x a.
Proof. intros x a Hx Ha. rewrite <- (rpc_0 x). apply rpc_mono_exp; assumption. Qed.
Lemma rpc_neg : forall x a, rpc x (- a) * rpc x a = 1.
Proof. intros. rewrite <- rpc_add. replace (- a + a) with 0 by ring. apply rpc_0. Qed.
Lemma rpc_sq_half : forall x, 0 < x -> rpc x (1 / 2) * rpc x (1 / 2) = x.
Proof. intros x Hx. rewrite <- rpc_add. replace (1 / 2 + 1 / 2) with 1 by field. apply rpc_one. exact Hx. Qed.

(* SizeWindows (GrowthBoundGivesRiemannHypothesis.lean l.109), over R *)
Definition SizeWindows (C eps x : R) (n nT nT2 m : nat) (b k aE Err : R) : Prop :=
  3 <= x /\ 0 < eps /\ 0 <= C /\ 0 < INR n /\ 0 < b /\ 0 <= aE /\ aE <= 2 * x * b /\
  rpc x (- (eps / 8)) * INR n / 2 <= INR nT /\
  rpc x (- eps) <= INR nT2 / INR n /\ (nT2 <= n)%nat /\
  rpc x (1 / 2 - eps) <= INR m /\ INR m <= rpc x (1 / 2 + eps / 2) /\
  x * INR m <= k /\ k <= INR n ^ 2 * rpc x (1 / 2 - eps) /\
  Err <= rpc x (C * eps) * (INR nT * aE * (1 + INR m ^ 2 / k)
    + INR m * ((2 * INR n) * INR m * b * rpc x eps + INR nT2 * k * b * rpc x eps / (INR n * (INR n * rpc x (- eps))))) /\
  26 <= rpc x (3 * eps / 8).

(* GrowthSizeBound = proposition_size_bound *)
Theorem proposition_size_bound : forall (C eps x : R) (n nT nT2 m : nat) (b k aE Err Gx : R),
  SizeWindows C eps x n nT nT2 m b k aE Err ->
  INR nT * INR m * b * ((INR nT2 / INR n) / 2) * (Gx - 4 * rpc x (1 / 2 + eps)) <= Err + 2 * INR nT * INR m * b / x ->
  Gx <= rpc x (1 / 2 + (C + 3) * eps).
Proof.
  intros C eps x n nT nT2 m b k aE Err Gx
    (Hx3 & He & HC & Hn & Hb & HaE0 & HaE & HnT & Hrho & _ & Hm1 & Hm2 & Hk1 & Hk2 & HErr & H26) Hmain.
  assert (Hx0 : 0 < x) by lra. assert (Hx1 : 1 <= x) by lra.
  set (s := rpc x (1 / 2)). set (e := rpc x eps). set (e2 := rpc x (eps / 2)).
  set (e8 := rpc x (eps / 8)). set (c := rpc x (C * eps)).
  assert (Hs : 1 <= s) by (apply rpc_ge1; lra). assert (He1 : 1 <= e) by (apply rpc_ge1; lra).
  assert (He2 : 1 <= e2) by (apply rpc_ge1; lra). assert (He8 : 1 <= e8) by (apply rpc_ge1; lra).
  assert (Hc : 1 <= c) by (apply rpc_ge1; [lra|nra]).
  assert (Hss : s * s = x) by (apply rpc_sq_half; exact Hx0).
  pose proof (rpc_neg x (eps / 8)) as N8. pose proof (rpc_neg x eps) as N1. fold e8 e in N8, N1.
  assert (He0 : 0 < e) by lra. assert (He80 : 0 < e8) by lra.
  set (nn := INR n) in *. set (nTr := INR nT) in *. set (nT2r := INR nT2) in *. set (mr := INR m) in *.
  set (rho := nT2r / nn) in *.
  assert (Hm0 : 0 < mr).
  { assert (0 < rpc x (1 / 2 - eps)) by apply rpc_pos. lra. }
  assert (Hk0 : 0 < k) by nra.
  (* the atom relations of growth_size_bound_R *)
  assert (H26' : 26 <= e8 * e8 * e8).
  { replace (e8 * e8 * e8) with (rpc x (3 * eps / 8)) by (unfold e8; rewrite <- !rpc_add; f_equal; field). exact H26. }
  assert (HaE' : aE <= 2 * (s * s) * b) by (rewrite Hss; lra).
  assert (HnT' : nn <= 2 * e8 * nTr).
  { assert (H : rpc x (- (eps / 8)) * nn / 2 * (2 * e8) <= nTr * (2 * e8)) by (apply Rmult_le_compat_r; lra).
    replace (rpc x (- (eps / 8)) * nn / 2 * (2 * e8)) with (nn * (rpc x (- (eps / 8)) * e8)) in H by field.
    rewrite N8 in H. lra. }
  assert (Hrho' : rho * nn = nT2r) by (unfold rho; field; lra).
  assert (Hrho1 : 1 <= e * rho).
  { assert (H : rpc x (- eps) * e <= rho * e) by (apply Rmult_le_compat_r; lra). rewrite N1 in H. lra. }
  assert (Hm1' : s <= e * mr).
  { assert (Es : s = rpc x (1 / 2 - eps) * e) by (unfold s, e; rewrite <- rpc_add; f_equal; ring).
    rewrite Es. rewrite Rmult_comm. apply Rmult_le_compat_l; lra. }
  assert (Hm2' : mr <= s * e2).
  { replace (s * e2) with (rpc x (1 / 2 + eps / 2)) by (unfold s, e2; rewrite <- rpc_add; reflexivity). exact Hm2. }
  assert (Hk1' : s * s * mr <= k) by (rewrite Hss; exact Hk1).
  assert (Hk2' : e * k <= nn * nn * s).
  { assert (Es : rpc x (1 / 2 - eps) * e = s) by (unfold s, e; rewrite <- rpc_add; f_equal; ring).
    assert (H : k * e <= nn ^ 2 * rpc x (1 / 2 - eps) * e) by (apply Rmult_le_compat_r; lra).
    replace (nn ^ 2 * rpc x (1 / 2 - eps) * e) with (nn * nn * (rpc x (1 / 2 - eps) * e)) in H by ring.
    rewrite Es in H. lra. }
  set (q1 := mr * mr / k). set (q2 := nT2r * k * b * (e * e) / (nn * nn)).
  assert (Hq1 : q1 * k = mr * mr) by (unfold q1; field; lra).
  assert (Hq2 : q2 * (nn * nn) = nT2r * k * b * (e * e)) by (unfold q2; field; lra).
  assert (HErr' : Err <= c * (nTr * aE * (1 + q1) + mr * (2 * nn * mr * b * e + q2))).
  { replace (nTr * aE * (1 + q1) + mr * (2 * nn * mr * b * e + q2))
      with (nTr * aE * (1 + mr ^ 2 / k) + mr * ((2 * nn) * mr * b * e + nT2r * k * b * e / (nn * (nn * rpc x (- eps))))).
    - exact HErr.
    - unfold q1, q2. assert (Hi : rpc x (- eps) = / e) by (apply (Rmult_eq_reg_r e); [rewrite N1; field|]; lra).
      rewrite Hi. field. repeat split; lra. }
  set (w := / x).
  assert (Hw : w * (s * s) = 1) by (unfold w; rewrite Hss; field; lra).
  assert (Hmain' : nTr * mr * b * rho * (Gx - 4 * s * e) <= 2 * Err + 4 * nTr * mr * b * w).
  { replace (rpc x (1 / 2 + eps)) with (s * e) in Hmain by (unfold s, e; rewrite <- rpc_add; reflexivity).
    unfold w. replace (2 * nTr * mr * b / x) with (2 * nTr * mr * b * / x) in Hmain by (unfold Rdiv; ring).
    unfold rho. unfold rho in Hmain. lra. }
  pose proof (growth_size_bound_R s e e2 e8 c b nn nTr nT2r mr k aE Err Gx q1 q2 rho w
    Hs ltac:(lra) He1 He2 He8 Hc H26' Hb Hn HaE0 HaE' HnT' Hrho' Hrho1 Hm1' Hm2' Hk1' Hk2' Hq1 Hq2 HErr' Hw Hmain') as G.
  replace (e8 * e8 * e8 * (s * c * (e * e) * e2 * e8)) with (rpc x (1 / 2 + (C + 3) * eps)) in G.
  - exact G.
  - unfold s, c, e, e2, e8. rewrite <- !rpc_add. f_equal. field.
Qed.

(* errorBracketSizeWindows (ErrorFormsWeakWindowsFalse.lean l.133), over R *)
Definition errorBracket (x eps : R) (n nT nT2 m : nat) (b k aE : R) : R :=
  INR nT * aE * (1 + INR m ^ 2 / k)
    + INR m * ((2 * INR n) * INR m * b * rpc x eps + INR nT2 * k * b * rpc x eps / (INR n * (INR n * rpc x (- eps)))).

(* ch_core (ChCore.lean l.343): beyond a threshold, the averaging core
   (character_balance_core, AlpogeRealsQED2.v) and proposition_size_bound
   give GmA <= x^(1/2 + (C+3) eps) + SigA.  Inputs: Lean's premises
   (RestSize, the gap bound through the error bracket, the size conditions),
   and the [inventory] per-coset bounds (th_le + ch_balance + ch_top),
   orthogonality (sum_Th) and the one_char lower bound. *)
Theorem ch_core : forall C eps, 0 <= C -> 0 < eps -> exists x1, forall x, x1 <= x ->
  forall (us : list R) (n nT nT2 m : nat) (b k aE GmA SigA Tsum : R),
  (1 <= length us)%nat ->
  Forall (fun v => v <= rpc x (C * eps) * errorBracket x eps n nT nT2 m b k aE + 2 * INR nT * INR m * b / x) us ->
  rsum us = INR (length us) * (INR m * b * ((INR nT2 / INR n) / 2) * Tsum) ->
  INR nT * (GmA - SigA - 4 * rpc x (1 / 2 + eps)) <= Tsum ->
  (* RestSize *)
  aE <= 2 * x * b -> rpc x (- (eps / 8)) * INR n / 2 <= INR nT -> rpc x (- eps) <= INR nT2 / INR n ->
  rpc x (1 / 2 - eps) <= INR m -> k <= INR n ^ 2 * rpc x (1 / 2 - eps) ->
  (* the remaining size conditions *)
  0 < INR n -> 0 < b -> 0 <= aE -> (nT2 <= n)%nat -> INR m <= rpc x (1 / 2 + eps / 2) -> x * INR m <= k ->
  GmA <= rpc x (1 / 2 + (C + 3) * eps) + SigA.
Proof.
  intros C eps HC He.
  destruct (eventually_rpc_ge 26 (3 * eps / 8) ltac:(lra) ltac:(lra)) as [x2 Hx2].
  exists (Rmax 3 x2). intros x Hx us n nT nT2 m b k aE GmA SigA Tsum
    HA0 Hper Hortho HY HaE HnT Hrho Hm1 Hk2 Hn Hb HaE0 Hn2 Hm2 Hk1.
  assert (Hx3 : 3 <= x) by (eapply Rle_trans; [apply Rmax_l|exact Hx]).
  assert (H26 : 26 <= rpc x (3 * eps / 8)) by (apply Hx2; eapply Rle_trans; [apply Rmax_r|exact Hx]).
  set (Err := rpc x (C * eps) * errorBracket x eps n nT nT2 m b k aE) in *.
  assert (Hfac : 0 <= INR m * b * ((INR nT2 / INR n) / 2)).
  { assert (0 <= INR m) by apply pos_INR. assert (0 <= INR nT2) by apply pos_INR.
    assert (0 <= INR nT2 / INR n) by (apply Rmult_le_pos; [lra|left; apply Rinv_0_lt_compat; lra]).
    assert (0 <= INR nT2 / INR n / 2) by lra.
    apply Rmult_le_pos; [apply Rmult_le_pos; lra|lra]. }
  pose proof (character_balance_core us (INR nT) (INR m) b (INR nT2 / INR n) x Err
                (GmA - SigA - 4 * rpc x (1 / 2 + eps)) Tsum HA0 Hfac Hper Hortho HY) as Hmain.
  assert (HSW : SizeWindows C eps x n nT nT2 m b k aE Err).
  { unfold SizeWindows. repeat split; try assumption; try lra. unfold Err, errorBracket. right. reflexivity. }
  assert (Hmain' : INR nT * INR m * b * ((INR nT2 / INR n) / 2) * (GmA - SigA - 4 * rpc x (1 / 2 + eps))
                   <= Err + 2 * INR nT * INR m * b / x) by exact Hmain.
  pose proof (proposition_size_bound C eps x n nT nT2 m b k aE Err (GmA - SigA) HSW
                ltac:(replace (GmA - SigA - 4 * rpc x (1 / 2 + eps)) with (GmA - SigA - 4 * rpc x (1 / 2 + eps)) in Hmain' by ring; exact Hmain')) as G.
  lra.
Qed.

Print Assumptions growth_size_bound_R.
Print Assumptions proposition_size_bound.
Print Assumptions ch_core.

(* ===================================================================== *)
(* Part F: landau_pole_re_le_bound                                        *)
(* ===================================================================== *)
(* With PoleData and the Laplace integral of AlpogeDeepStatements.v (limits
   of uniform Riemann sums), the bound is proved from the sums themselves:
   |sum_j h f(j h)| <= C0 h sum_j exp(-c h)^j <= C0 (1/c + h). *)

Lemma geom_le : forall q (n : nat), 0 <= q < 1 -> sum_f_R0 (fun j => q ^ j) n <= / (1 - q).
Proof.
  intros q n [H0 H1]. rewrite tech3 by lra.
  assert (0 <= q ^ (S n)) by (apply pow_le; lra).
  unfold Rdiv. assert (0 < / (1 - q)) by (apply Rinv_0_lt_compat; lra). nra.
Qed.

Lemma sum_scal_l : forall (a : nat -> R) c (n : nat), sum_f_R0 (fun j => c * a j) n = c * sum_f_R0 a n.
Proof. intros a c n. induction n as [|n IH]; simpl; [reflexivity|rewrite IH; ring]. Qed.

Lemma inv_Sn_cv : forall T, Un_cv (fun n => T / INR (S n)) 0.
Proof.
  intros T eps He. destruct (archimed (Rabs T / eps)) as [H1 _].
  assert (HTe : 0 <= Rabs T / eps) by (apply Rmult_le_pos; [apply Rabs_pos|left; apply Rinv_0_lt_compat; lra]).
  exists (Z.to_nat (up (Rabs T / eps))). intros n Hn. unfold R_dist. rewrite Rminus_0_r.
  assert (Hz : (0 <= up (Rabs T / eps))%Z) by (apply le_IZR; lra).
  assert (HN : Rabs T / eps < INR (S n)).
  { apply Rlt_le_trans with (IZR (up (Rabs T / eps))); [lra|].
    rewrite <- (Z2Nat.id _ Hz), <- INR_IZR_INZ. apply le_INR. lia. }
  assert (HSn : 0 < INR (S n)) by apply lt_0_INR, Nat.lt_0_succ.
  unfold Rdiv. rewrite Rabs_mult, Rabs_inv, (Rabs_pos_eq (INR (S n))) by lra.
  apply (Rmult_lt_reg_r (INR (S n))); [lra|]. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
  apply (Rmult_lt_reg_l (/ eps)); [apply Rinv_0_lt_compat; lra|].
  replace (/ eps * (eps * INR (S n))) with (INR (S n)) by (field; lra). unfold Rdiv in HN. lra.
Qed.

(* the Riemann-sum bound *)
Lemma rsum_bound : forall (f : R -> R) C0 c T (n : nat), 0 <= C0 -> 0 < c -> 0 < T ->
  (forall u, 0 <= u <= T -> Rabs (f u) <= C0 * exp (- c * u)) ->
  Rabs (RSum f 0 T n) <= C0 * (/ c + T / INR (S n)).
Proof.
  intros f C0 c T n HC Hc HT Hf. unfold RSum.
  set (h := (T - 0) / INR (S n)).
  assert (HSn : 0 < INR (S n)) by apply lt_0_INR, Nat.lt_0_succ.
  assert (Hh : 0 < h) by (unfold h; apply Rdiv_lt_0_compat; lra).
  set (q := exp (- c * h)).
  assert (Hq0 : 0 <= q) by (left; apply exp_pos).
  assert (Hq1 : q < 1) by (unfold q; rewrite <- exp_0; apply exp_lt_mono; nra).
  assert (Hpt : forall j, (j <= n)%nat -> Rabs (f (0 + INR j * (T - 0) / INR (S n))) <= C0 * q ^ j).
  { intros j Hj. assert (Hx : 0 <= 0 + INR j * (T - 0) / INR (S n) <= T).
    { assert (0 <= INR j) by apply pos_INR. assert (INR j <= INR n) by (apply le_INR; exact Hj).
      rewrite S_INR in *. split.
      - apply Rplus_le_le_0_compat; [lra|]. apply Rmult_le_pos; [nra|left; apply Rinv_0_lt_compat; lra].
      - apply (Rmult_le_reg_r (INR n + 1)); [lra|]. replace ((0 + INR j * (T - 0) / (INR n + 1)) * (INR n + 1)) with (INR j * T) by (field; lra). nra. }
    eapply Rle_trans; [apply (Hf _ Hx)|]. apply Rmult_le_compat_l; [exact HC|].
    unfold q. rewrite <- exp_INR_mult. apply exp_le_mono. unfold h. right. field. lra. }
  assert (Hsum : Rabs (sum_f_R0 (fun j => f (0 + INR j * (T - 0) / INR (S n))) n) <= C0 * / (1 - q)).
  { eapply Rle_trans; [apply sum_f_R0_triangle|].
    apply Rle_trans with (sum_f_R0 (fun j => C0 * q ^ j) n).
    - apply sum_Rle. intros j Hj. apply Hpt. exact Hj.
    - rewrite sum_scal_l. apply Rmult_le_compat_l; [exact HC|apply geom_le; lra]. }
  (* h / (1 - q) <= 1/c + h, from exp(c h) >= 1 + c h *)
  assert (Hq : q <= / (1 + c * h)).
  { unfold q. replace (- c * h) with (- (c * h)) by ring. rewrite exp_Ropp.
    apply Rinv_le_contravar; [nra|]. pose proof (add_one_le_exp (c * h)). lra. }
  assert (H1q : 0 < 1 - q) by lra.
  assert (Hhq : h * / (1 - q) <= / c + h).
  { assert (1 - q >= c * h / (1 + c * h)).
    { assert (/ (1 + c * h) = 1 - c * h / (1 + c * h)) by (field; nra). lra. }
    apply (Rmult_le_reg_r (1 - q)); [lra|]. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
    assert (Hch : (/ c + h) * (c * h / (1 + c * h)) = h) by (field; split; nra).
    assert ((/ c + h) * (c * h / (1 + c * h)) <= (/ c + h) * (1 - q)).
    { apply Rmult_le_compat_l; [assert (0 < / c) by (apply Rinv_0_lt_compat; lra); lra|lra]. }
    lra. }
  rewrite Rabs_mult, (Rabs_pos_eq h) by lra.
  apply Rle_trans with (h * (C0 * / (1 - q))); [apply Rmult_le_compat_l; [lra|exact Hsum]|].
  replace (h * (C0 * / (1 - q))) with (C0 * (h * / (1 - q))) by ring.
  replace (T / INR (S n)) with h by (unfold h; field; lra).
  apply Rmult_le_compat_l; [exact HC|exact Hhq].
Qed.

Lemma lim_bound : forall (f : R -> R) C0 c T I, 0 <= C0 -> 0 < c -> 0 < T ->
  (forall u, 0 <= u <= T -> Rabs (f u) <= C0 * exp (- c * u)) ->
  Un_cv (RSum f 0 T) I -> Rabs I <= C0 / c.
Proof.
  intros f C0 c T I HC Hc HT Hf Hcv.
  assert (HV : Un_cv (fun n => C0 * (/ c + T / INR (S n))) (C0 / c)).
  { replace (C0 / c) with (C0 * (/ c + 0)) by (field; lra).
    apply (CV_mult (fun _ => C0) (fun n => / c + T / INR (S n))); [apply Un_cv_const|].
    apply (CV_plus (fun _ => / c) (fun n => T / INR (S n))); [apply Un_cv_const|apply inv_Sn_cv]. }
  assert (Hup : I <= C0 / c).
  { apply (@Rle_cv_lim (RSum f 0 T) (fun n => C0 * (/ c + T / INR (S n))) I (C0 / c)); [|exact Hcv|exact HV].
    intro n. pose proof (rsum_bound f C0 c T n HC Hc HT Hf). pose proof (Rle_abs (RSum f 0 T n)). lra. }
  assert (Hlo : - I <= C0 / c).
  { apply (@Rle_cv_lim (fun n => - RSum f 0 T n) (fun n => C0 * (/ c + T / INR (S n))) (- I) (C0 / c)); [|apply CV_opp; exact Hcv|exact HV].
    intro n. pose proof (rsum_bound f C0 c T n HC Hc HT Hf). pose proof (Rle_abs (- RSum f 0 T n)).
    rewrite Rabs_Ropp in H0. lra. }
  apply Rabs_le. lra.
Qed.

Section PoleBound.
Variable g : R -> R.
Variable Phi : Cc -> Cc.
Variable Z : Cc -> Prop.
Hypothesis HP : PoleData g Phi Z.

Theorem landau_pole_re_le_bound : forall sigma, 2 < sigma ->
  exists M, forall s, sigma <= cre s -> cnorm (Phi s) <= M.
Proof.
  intros sigma Hs.
  destruct HP as [_ [[C0 HC] [Hlap _]]].
  assert (HC0 : 0 <= C0) by (pose proof (HC 0 (Rle_refl 0)) as H; rewrite Rmult_0_r, exp_0 in H; pose proof (Rabs_pos (g 0)); lra).
  set (c := sigma - 2). assert (Hc : 0 < c) by (unfold c; lra).
  set (Bd := C0 / c).
  assert (HBd : 0 <= Bd) by (unfold Bd; apply Rmult_le_pos; [lra|left; apply Rinv_0_lt_compat; lra]).
  exists (2 * Bd). intros s Hsre.
  assert (Hgb : forall u, 0 <= u -> Rabs (g u) * exp (- cre s * u) <= C0 * exp (- c * u)).
  { intros u Hu. pose proof (HC u Hu) as H1.
    assert (H2 : exp (- cre s * u) <= exp (- sigma * u)) by (apply exp_le_mono; nra).
    apply Rle_trans with (C0 * exp (2 * u) * exp (- sigma * u)).
    - apply Rmult_le_compat; [apply Rabs_pos|left; apply exp_pos|exact H1|exact H2].
    - rewrite Rmult_assoc, <- exp_plus. unfold c. right. f_equal. f_equal. ring. }
  (* |Re Phi s| <= Bd and |Im Phi s| <= Bd *)
  assert (Hcomp : Rabs (cre (Phi s)) <= Bd /\ Rabs (cim (Phi s)) <= Bd).
  { split; apply Rnot_lt_le; intro Hgt;
      [set (dlt := Rabs (cre (Phi s)) - Bd)|set (dlt := Rabs (cim (Phi s)) - Bd)];
      assert (Hdlt : 0 < dlt) by (unfold dlt; lra);
      destruct (Hlap s ltac:(lra) dlt Hdlt) as [T0 [HT0 HT]];
      destruct (HT (Rmax T0 1) (Rmax_l T0 1)) as [Ir [Ii [[_ HIr] [[_ HIi] [Er Ei]]]]];
      assert (HT1 : 0 < Rmax T0 1) by (pose proof (Rmax_r T0 1); lra).
    - assert (Hb : Rabs Ir <= C0 / c).
      { apply (lim_bound (fun u => g u * exp (- cre s * u) * cos (cim s * u)) C0 c (Rmax T0 1) Ir HC0 Hc HT1); [|exact HIr].
        intros u Hu. rewrite !Rabs_mult. pose proof (COS_bound (cim s * u)) as Hcos.
        assert (Rabs (cos (cim s * u)) <= 1) by (apply Rabs_le; lra).
        rewrite (Rabs_pos_eq (exp _)) by (left; apply exp_pos).
        pose proof (Hgb u ltac:(lra)). pose proof (Rabs_pos (g u)). pose proof (exp_pos (- cre s * u)).
        pose proof (Rabs_pos (cos (cim s * u))).
        assert (Hx0 : 0 <= Rabs (g u) * exp (- cre s * u)) by (apply Rmult_le_pos; lra).
        assert (Rabs (g u) * exp (- cre s * u) * Rabs (cos (cim s * u)) <= Rabs (g u) * exp (- cre s * u) * 1)
          by (apply Rmult_le_compat_l; lra).
        lra. }
      pose proof (Rabs_triang_inv (cre (Phi s)) Ir). rewrite Rabs_minus_sym in Er. fold Bd in Hb. unfold dlt in Er. lra.
    - assert (Hb : Rabs Ii <= C0 / c).
      { apply (lim_bound (fun u => - g u * exp (- cre s * u) * sin (cim s * u)) C0 c (Rmax T0 1) Ii HC0 Hc HT1); [|exact HIi].
        intros u Hu. rewrite Rabs_mult, Rabs_mult, Rabs_Ropp. pose proof (SIN_bound (cim s * u)) as Hsin.
        assert (Rabs (sin (cim s * u)) <= 1) by (apply Rabs_le; lra).
        rewrite (Rabs_pos_eq (exp _)) by (left; apply exp_pos).
        pose proof (Hgb u ltac:(lra)). pose proof (Rabs_pos (g u)). pose proof (exp_pos (- cre s * u)).
        pose proof (Rabs_pos (sin (cim s * u))).
        assert (Hx0 : 0 <= Rabs (g u) * exp (- cre s * u)) by (apply Rmult_le_pos; lra).
        assert (Rabs (g u) * exp (- cre s * u) * Rabs (sin (cim s * u)) <= Rabs (g u) * exp (- cre s * u) * 1)
          by (apply Rmult_le_compat_l; lra).
        lra. }
      pose proof (Rabs_triang_inv (cim (Phi s)) Ii). rewrite Rabs_minus_sym in Ei. fold Bd in Hb. unfold dlt in Ei. lra. }
  destruct Hcomp as [Hre Him].
  unfold cnorm. rewrite <- (sqrt_Rsqr (2 * Bd)) by lra. apply sqrt_le_1_alt.
  assert (Hr2 : cre (Phi s) * cre (Phi s) <= Bd * Bd).
  { replace (cre (Phi s) * cre (Phi s)) with (Rabs (cre (Phi s)) * Rabs (cre (Phi s)))
      by (rewrite <- Rabs_mult; apply Rabs_pos_eq; nra).
    apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  assert (Hi2 : cim (Phi s) * cim (Phi s) <= Bd * Bd).
  { replace (cim (Phi s) * cim (Phi s)) with (Rabs (cim (Phi s)) * Rabs (cim (Phi s)))
      by (rewrite <- Rabs_mult; apply Rabs_pos_eq; nra).
    apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  unfold Rsqr. nra.
Qed.
End PoleBound.

Print Assumptions landau_pole_re_le_bound.
