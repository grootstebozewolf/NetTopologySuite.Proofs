(* LandauDichotomyQED.v -- the case split and the majorant inequality inside
   landau_window, the main line's sign step in the claimed RH/GRH Lean
   development (CocoSgt/riemann-hypothesis-lean @ 7cbf7a0):

     Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/
       landauWindowIneq.lean : landau_window_ineq   (Part A)
       LandauDichotomy.lean  : eq_ofReal_sub_of_dist_le_of_le_sub_re,
                               landau_dichotomy     (Part B)
       LandauNearest.lean    : landau_nearest_equi,
                               landau_nearest       (Part C)

   landau_window assumes a pole rho0 with Re rho0 > theta and splits:
     (1) some pole is nearer to the line Re s = sigma than the pole-free disc
         around sigma is wide: then pick gamma so that sigma + i gamma has a
         UNIQUE nearest pole (landau_nearest), and contradict with the NORM of
         the k-th Taylor coefficient at sigma + i gamma;
     (2) otherwise the nearest pole to sigma is REAL, beta in (theta, sigma),
         isolated in a disc (landau_dichotomy, right branch), and contradict
         with the REAL PART of the k-th coefficient at sigma, which is where
         the positive real-pole residue is used.
   Both branches feed landau_window_contra (LandauWindowCore.v).  The window
   majorant enters only through landau_window_ineq, whose pointwise core is
   |g| + g <= 2R when g <= R and 0 <= R.

   Rocq (here, over Q):
   - Distances appear SQUARED: d2 sigma gamma w = (sigma - x)^2 + (gamma - y)^2
     for w = (x, y).  Lean's real radii D, r become squared radii D2, r2; every
     comparison used is between nonnegative quantities, so this is faithful.
   - Lean's local finiteness of Z (landau_finite, from isolated zeros) is a
     hypothesis: a list F covering Z on the relevant compact region.  For
     landau_nearest the region is a box containing Lean's closed ball, which
     avoids the triangle inequality for square roots.
   - Integrals are finite sums; the triangle inequality for the complex
     Laplace integral and the kernel bound landau_kernel_max are hypotheses.
   - Lean's landau_dichotomy uses classical by_cases on an existential over the
     infinite set Z.  Here the split is decided over the finite list rho0 :: F,
     which suffices: no excluded middle is needed.

   Evidence for docs/attacks/2026-11-21-alpoge-landau-dichotomy-qed.md.
   NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import QArith Qabs Qminmax Lqa List.
Import ListNotations.
Local Open Scope Q_scope.

(* ===================================================================== *)
(* Part A: landau_window_ineq, discretised                                *)
(* ===================================================================== *)

(* The pointwise sign: Lean's  h3 : |g u| + g u <= 2 * R u. *)
Lemma abs_add_le_twice : forall g R : Q, 0 <= R -> g <= R -> Qabs g + g <= 2 * R.
Proof.
  intros g R HR Hg. destruct (Qlt_le_dec g 0) as [H|H].
  - rewrite Qabs_neg by lra. lra.
  - rewrite Qabs_pos by lra. lra.
Qed.

(* Window entries (g, w, R, v): sample of g, kernel weight w = u^k e^(-sigma u)/k!,
   majorant R, and v = e^(-theta u); hypothesis w <= K v is landau_kernel_max
   with K = 1/(sigma - theta)^k.  Tail entries (g, w, h): |g| w <= C0 h. *)
Definition gw   (t : Q * Q * Q * Q) := let '(g, w, _, _) := t in (g, w).
Definition inOK (K : Q) (t : Q * Q * Q * Q) : Prop :=
  let '(g, w, R, v) := t in 0 <= w /\ 0 <= R /\ g <= R /\ w <= K * v.
Definition outOK (C0 : Q) (t : Q * Q * Q) : Prop :=
  let '(g, w, h) := t in 0 <= w /\ Qabs g * w <= C0 * h.

Fixpoint sumIn (f : Q * Q * Q * Q -> Q) (l : list (Q * Q * Q * Q)) : Q :=
  match l with [] => 0 | t :: l' => f t + sumIn f l' end.
Fixpoint sumOut (f : Q * Q * Q -> Q) (l : list (Q * Q * Q)) : Q :=
  match l with [] => 0 | t :: l' => f t + sumOut f l' end.

Definition aIn  (t : Q * Q * Q * Q) := let '(g, w, _, _) := t in Qabs g * w.
Definition gIn  (t : Q * Q * Q * Q) := let '(g, w, _, _) := t in g * w.
Definition rIn  (t : Q * Q * Q * Q) := let '(_, _, R, v) := t in R * v.
Definition aOut (t : Q * Q * Q) := let '(g, w, _) := t in Qabs g * w.
Definition gOut (t : Q * Q * Q) := let '(g, w, _) := t in g * w.
Definition hOut (t : Q * Q * Q) := let '(_, _, h) := t in h.

Lemma window_part : forall K l, 0 <= K -> Forall (inOK K) l ->
  sumIn aIn l + sumIn gIn l <= 2 * K * sumIn rIn l.
Proof.
  intros K l HK Hl. induction Hl as [|[[[g w] R] v] l' Ht _ IH]; simpl.
  - lra.
  - destruct Ht as (Hw & HR & Hg & Hk).
    assert (H1 : (Qabs g + g) * w <= (2 * R) * w).
    { apply Qmult_le_compat_r; [apply abs_add_le_twice|]; assumption. }
    assert (H2 : (2 * R) * w <= (2 * R) * (K * v)).
    { rewrite !(Qmult_comm (2 * R)). apply Qmult_le_compat_r; lra. }
    assert (H3 : Qabs g * w + g * w == (Qabs g + g) * w) by ring.
    assert (H4 : (2 * R) * (K * v) == 2 * K * (R * v)) by ring.
    lra.
Qed.

Lemma tail_part : forall C0 l, Forall (outOK C0) l ->
  sumOut aOut l + sumOut gOut l <= 2 * C0 * sumOut hOut l.
Proof.
  intros C0 l Hl. induction Hl as [|[[g w] h] l' Ht _ IH]; simpl.
  - lra.
  - destruct Ht as (Hw & Hb).
    assert (H1 : g * w <= Qabs g * w) by (apply Qmult_le_compat_r; [apply Qle_Qabs|lra]).
    lra.
Qed.

(* Mirror of landau_window_ineq's conclusion:
     sum |g| w  <=  2 K sum_win R v  -  sum g w  +  2 C0 sum_tail h,
   where the left side bounds the norm of the coefficient at sigma + i gamma
   (triangle inequality, a translation) and sum g w is its real part at sigma. *)
Theorem window_ineq_discrete : forall K C0 lin lout,
  0 <= K -> Forall (inOK K) lin -> Forall (outOK C0) lout ->
  sumIn aIn lin + sumOut aOut lout
    <= 2 * K * sumIn rIn lin - (sumIn gIn lin + sumOut gOut lout)
       + 2 * C0 * sumOut hOut lout.
Proof.
  intros K C0 lin lout HK Hin Hout.
  pose proof (window_part K lin HK Hin). pose proof (tail_part C0 lout Hout). lra.
Qed.

Print Assumptions window_ineq_discrete.

(* ===================================================================== *)
(* Part B: landau_dichotomy                                               *)
(* ===================================================================== *)

Definition d2 (sigma gamma : Q) (w : Q * Q) : Q :=
  (sigma - fst w) * (sigma - fst w) + (gamma - snd w) * (gamma - snd w).
Definition peq (a b : Q * Q) : Prop := fst a == fst b /\ snd a == snd b.

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
  snd w == 0 /\ fst w == sigma - D.
Proof.
  intros sigma D [x y] HD Hle Hd. unfold d2 in Hd; simpl in *.
  assert (Hx : D * D <= (sigma - x) * (sigma - x)) by nra.
  assert (Hy : y * y == 0) by nra.
  split.
  - destruct (Qlt_le_dec y 0); destruct (Qlt_le_dec 0 y); nra.
  - assert (sigma - x <= D) by (apply sq_le_inv; nra). lra.
Qed.

(* Finite minimum over a list, with default d. *)
Fixpoint minl (f : Q * Q -> Q) (l : list (Q * Q)) (d : Q) : Q :=
  match l with [] => d | w :: l' => Qmin (f w) (minl f l' d) end.

Lemma minl_le_d : forall f l d, minl f l d <= d.
Proof.
  intros f l d. induction l as [|w l IH]; simpl; [lra|].
  pose proof (Q.le_min_r (f w) (minl f l d)). lra.
Qed.

Lemma minl_le_mem : forall f l d w, In w l -> minl f l d <= f w.
Proof.
  intros f l d w. induction l as [|a l IH]; simpl; [tauto|].
  intros [<-|H].
  - apply Q.le_min_l.
  - pose proof (Q.le_min_r (f a) (minl f l d)). specialize (IH H). lra.
Qed.

Lemma minl_cases : forall f l d, minl f l d == d \/ exists w, In w l /\ minl f l d == f w.
Proof.
  intros f l d. induction l as [|a l IH]; simpl; [left; lra|].
  destruct (Q.min_spec (f a) (minl f l d)) as [[_ Hm]|[_ Hm]].
  - right. exists a. split; [left; reflexivity|exact Hm].
  - destruct IH as [H|[w [Hw H]]];
      [left; rewrite Hm; exact H|right; exists w; split; [right; exact Hw|rewrite Hm; exact H]].
Qed.

(* Attained when l is nonempty and every f w <= d. *)
Lemma minl_attained : forall f l d w0, In w0 l -> (forall w, In w l -> f w <= d) ->
  exists w, In w l /\ minl f l d == f w.
Proof.
  intros f l d w0 H0 Hd. destruct (minl_cases f l d) as [H|H]; [|exact H].
  exists w0. split; [exact H0|]. pose proof (minl_le_mem f l d w0 H0). specialize (Hd w0 H0). lra.
Qed.

(* The "second minimum": min over the entries strictly above m, capped at cap. *)
Definition above (f : Q * Q -> Q) (m cap : Q) (w : Q * Q) : Q :=
  if Qle_bool (f w) m then cap else f w.

Lemma above_gt : forall f l m cap, m < cap -> m < minl (above f m cap) l cap.
Proof.
  intros f l m cap Hc. induction l as [|a l IH]; simpl; [exact Hc|].
  unfold above at 1. destruct (Qle_bool (f a) m) eqn:E.
  - apply Q.min_glb_lt; assumption.
  - apply Q.min_glb_lt; [|exact IH]. apply Qnot_le_lt. intro H.
    apply Qle_bool_iff in H. congruence.
Qed.

Lemma above_sep : forall f l m cap w, In w l -> f w < minl (above f m cap) l cap -> f w <= m.
Proof.
  intros f l m cap w Hw Hlt. pose proof (minl_le_mem (above f m cap) l cap w Hw) as H.
  destruct (Qle_bool (f w) m) eqn:E.
  - apply Qle_bool_iff. exact E.
  - assert (Ha : above f m cap w = f w) by (unfold above; rewrite E; reflexivity).
    rewrite Ha in H. lra.
Qed.

(* Decide, over a finite list, whether some entry is nearer the line than m. *)
Lemma split_list : forall sigma m (l : list (Q * Q)),
  { w | In w l /\ (sigma - fst w) * (sigma - fst w) < m } +
  { forall w, In w l -> m <= (sigma - fst w) * (sigma - fst w) }.
Proof.
  intros sigma m l. induction l as [|a l IH].
  - right. intros w [].
  - destruct (Qlt_le_dec ((sigma - fst a) * (sigma - fst a)) m) as [H|H].
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
Theorem dichotomy_rebuilt :
  forall (Z : Q * Q -> Prop) (F : list (Q * Q)) (sigma theta : Q) (rho0 : Q * Q),
  theta < sigma ->
  (forall w, Z w -> d2 sigma 0 w <= (sigma - theta) * (sigma - theta) -> In w F) ->
  (forall w, In w F -> Z w /\ d2 sigma 0 w <= (sigma - theta) * (sigma - theta)) ->
  (forall w, Z w -> fst w < sigma) ->
  Z rho0 -> theta < fst rho0 ->
  (exists D2, D2 <= (sigma - theta) * (sigma - theta)
     /\ (forall w, Z w -> ~ d2 sigma 0 w < D2)
     /\ exists rho1, Z rho1 /\ (sigma - fst rho1) * (sigma - fst rho1) < D2)
  \/
  (exists beta, Z beta /\ snd beta == 0 /\ theta < fst beta
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
      assert (Hreal : forall w, In w F -> f w == m -> snd w == 0 /\ fst w == fst rs).
      { intros w Hw Hfw.
        destruct (HFZ w Hw) as [HwZ _].
        pose proof (Hall w (or_intror Hw)) as Hw2.
        pose proof (Hle w HwZ) as Hws.
        pose proof (Hall rs (or_intror Hrs)) as Hr2.
        destruct (HFZ rs Hrs) as [HrZ _]. pose proof (Hle rs HrZ) as Hrsl.
        unfold f, d2 in Hfw, Hm. simpl in Hfw, Hm.
        assert (E1 : (0 - snd w) * (0 - snd w) == snd w * snd w) by ring.
        assert (E2' : (0 - snd rs) * (0 - snd rs) == snd rs * snd rs) by ring.
        pose proof (sq_nonneg (snd w)). pose proof (sq_nonneg (snd rs)).
        assert (Hy : snd w * snd w == 0) by lra.
        assert (Hy' : snd rs * snd rs == 0) by lra.
        assert (snd w == 0) by (destruct (Qlt_le_dec (snd w) 0); destruct (Qlt_le_dec 0 (snd w)); nra).
        split; [assumption|].
        assert (Heq : (sigma - fst w) * (sigma - fst w) == (sigma - fst rs) * (sigma - fst rs)) by nra.
        assert (sigma - fst w <= sigma - fst rs) by (apply sq_le_inv; nra).
        assert (sigma - fst rs <= sigma - fst w) by (apply sq_le_inv; nra).
        lra. }
      destruct (Hreal rs Hrs (Qeq_sym _ _ Hm)) as [Hrsy _].
      destruct (HFZ rs Hrs) as [HrsZ _].
      pose proof (Hle rs HrsZ) as Hrsl.
      assert (Hfrs : f rs == (sigma - fst rs) * (sigma - fst rs)).
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

Print Assumptions dichotomy_rebuilt.

(* ===================================================================== *)
(* Part C: landau_nearest                                                 *)
(* ===================================================================== *)

Definition nnum (sigma : Q) (a b : Q * Q) : Q :=
  (sigma - fst a) * (sigma - fst a) + snd a * snd a
  - (sigma - fst b) * (sigma - fst b) - snd b * snd b.

(* landau_nearest_equi: equidistance from sigma + i gamma forces a = b unless
   gamma is the one critical value of the pair (only when Im a <> Im b). *)
Theorem nearest_equi : forall sigma gamma a b,
  fst a < sigma -> fst b < sigma ->
  d2 sigma gamma a == d2 sigma gamma b ->
  (~ snd a == snd b -> ~ gamma * (2 * (snd a - snd b)) == nnum sigma a b) ->
  peq a b.
Proof.
  intros sigma gamma [xa ya] [xb yb] Ha Hb Hd Hg. unfold d2, nnum, peq in *; simpl in *.
  assert (Hy : ya == yb).
  { destruct (Qeq_dec ya yb) as [H|H]; [exact H|]. exfalso. apply (Hg H). nra. }
  split; [|exact Hy].
  rewrite Hy in Hd.
  assert (Heq : (sigma - xa) * (sigma - xa) == (sigma - xb) * (sigma - xb)) by nra.
  assert (sigma - xa <= sigma - xb) by (apply sq_le_inv; nra).
  assert (sigma - xb <= sigma - xa) by (apply sq_le_inv; nra).
  lra.
Qed.

(* Choose a shift avoiding a finite list of bad values, robustly. *)
Lemma avoid : forall (g0 eps : Q) (L : list Q), 0 < eps ->
  exists t, 0 < t /\ t <= eps /\ forall s, 0 < s -> s <= t -> forall b, In b L -> ~ g0 + s == b.
Proof.
  intros g0 eps L He. induction L as [|b L IH].
  - exists eps. split; [exact He|]. split; [lra|]. intros s _ _ b [].
  - destruct IH as [t [Ht [Hte Hav]]].
    destruct (Qeq_dec b g0) as [Hb|Hb].
    + exists t. split; [exact Ht|]. split; [exact Hte|].
      intros s Hs Hst c [<-|Hc]; [|exact (Hav s Hs Hst c Hc)]. intro E. rewrite Hb in E. lra.
    + set (q := Qabs (b - g0)).
      assert (Hq : 0 < q).
      { unfold q. destruct (Qlt_le_dec (b - g0) 0) as [Hn|Hp].
        - rewrite Qabs_neg; lra.
        - rewrite Qabs_pos by lra. destruct (proj1 (Qle_lteq 0 (b - g0)) Hp) as [H'|H'];
            [exact H'|exfalso; apply Hb; lra]. }
      exists (Qmin t (q * (1 # 2))).
      pose proof (Q.le_min_l t (q * (1 # 2))). pose proof (Q.le_min_r t (q * (1 # 2))).
      split; [apply Q.min_glb_lt; lra|].
      split; [lra|].
      intros s Hs Hst c [<-|Hc].
      * intro E. assert (Hq' : q == b - g0) by (unfold q; apply Qabs_pos; lra). lra.
      * apply (Hav s Hs); [lra|exact Hc].
Qed.

Lemma abs_of_sq_lt : forall a D, 0 < D -> a * a < D * D -> - D < a /\ a < D.
Proof. intros. split; nra. Qed.

(* landau_nearest.  rho1 is a pole nearer the line Re s = sigma than D < sigma.
   F covers Z on the box [sigma - D, sigma] x [Im rho1 - 2D, Im rho1 + 2D],
   which contains Lean's closedBall (sigma + i Im rho1) (D + eps) and lies in
   Re s > 0 (Lean: landau_finite).  Conclusion: some sigma + i gamma has a
   unique nearest pole rho, alone in a disc of squared radius r2 <= D^2. *)
Theorem nearest_rebuilt :
  forall (Z : Q * Q -> Prop) (F : list (Q * Q)) (sigma D : Q) (rho1 : Q * Q),
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
  set (eps := (D - a) * (1 # 2)).
  assert (He : 0 < eps) by (unfold eps, a in *; lra).
  set (crit := fun p q : Q * Q => nnum sigma p q / (2 * (snd p - snd q))).
  set (L := flat_map (fun p => map (crit p) F) F).
  destruct (avoid (snd rho1) eps L He) as [t [Ht [Hte Hav]]].
  set (gamma := snd rho1 + t).
  set (f := d2 sigma gamma).
  assert (Hf1 : f rho1 < D * D).
  { unfold f, d2, gamma. fold a.
    assert (Hg : snd rho1 + t - snd rho1 == t) by ring. rewrite Hg.
    unfold eps in Hte. unfold a in *. nra. }
  assert (H1F : In rho1 F).
  { apply HF; [exact H1|unfold a in Ha; lra|]. split; lra. }
  set (m := minl f F (f rho1)).
  assert (Hrho : exists rho, In rho F /\ m == f rho).
  { destruct (minl_cases f F (f rho1)) as [H|H]; [exists rho1; split; assumption|exact H]. }
  destruct Hrho as [rho [HrF Hm]].
  assert (Hmle : m <= f rho1) by apply minl_le_d.
  assert (HmD : m < D * D) by lra.
  assert (Huniq : forall w, In w F -> f w == m -> peq w rho).
  { intros w Hw Hfw. apply (nearest_equi sigma gamma w rho).
    - apply Hle, HFZ, Hw.
    - apply Hle, HFZ, HrF.
    - unfold f in *. lra.
    - intros Hne Hc. apply (Hav t Ht (Qle_refl t) (crit w rho)).
      + unfold L. apply in_flat_map. exists w. split; [exact Hw|]. apply in_map. exact HrF.
      + assert (Hden : ~ 2 * (snd w - snd rho) == 0) by (intro; apply Hne; lra).
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

Print Assumptions nearest_rebuilt.
Print Assumptions on_axis.
Print Assumptions nearest_equi.
