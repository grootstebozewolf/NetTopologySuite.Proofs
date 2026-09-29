(* ============================================================================
   NetTopologySuite.Proofs.LineariseContract
   ----------------------------------------------------------------------------
   Generic linearisation contract, plus the circular-arc instance.

   One contract, three curve types, and the year-2 bridge.  Regime 2 of
   Linearise.v (a gap that survives an eps-approximation) stays as it is;
   this file does not restate those theorems.  What it adds is the
   obligation a densifier has to meet before that bridge applies:

     L1  every vertex lies on the curve
     L2  the endpoints are exact
     L3  the parameter is strictly monotone and covers the whole sweep
     L4  every curve point is within tol of the polyline
     L6  reversing the parameter reverses the polyline
     L7  at least two segments

   L5 (Z/M) is a separate predicate.  The corpus Point is planar, so the
   contract does not mention an ordinate.

   Arc instance.  Behavioural reference: GEOS circular-arc densify, not
   a copy of GEOS.  On a CircularEgg (the payload #890 certifies),

     n    = max (ceil (|Δθ| / step), 2)
     step = a positive angle no larger than the maximum segment angle,
            and small enough that the sagitta r·(1 − cos(step/2))
            is at most the maximum deviation.

   Samples are uniform in the parameter, which is the CCW-normalised
   absolute sweep |Δθ|/n along the egg (a negative sweep walks clockwise;
   reverse symmetry is L6).  The deviation bound is the sagitta, not an
   acos: Stdlib acos/atan leave the three-axiom allowlist through Ratan.

   chord_approx_arc here is that n-chord.  CurveGeometry.chord_approx_arc
   stays the 3-point stub; its consumers keep their equations.

   chord_approx_error_bound is the deferred Phase-4 headline, discharged
   for |Δθ| < 2π: every point of the arc is within
   r·(1 − cos(|Δθ| / (2n))) of the polyline.  The full circle
   (|Δθ| = 2π) is full_circle_linearise_followup and waits on #892.

   No NTS C#.  No GEOS source.  claimId: none.
   No Admitted, no Axiom, no Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Grok (Cursor cloud agent)
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List ZArith Zfloor.
Import ListNotations.
From NTS.Proofs Require Import Distance.
From NTS.Proofs Require Import Segment.
From NTS.Proofs Require Import SheetHenCircEgg.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The contract.  γ is any planar curve on a parameter interval.          *)
(* -------------------------------------------------------------------------- *)

Definition L1_on_curve (γ : R -> Point) (ts : list R) : Prop :=
  forall p, In p (map γ ts) -> exists t, In t ts /\ p = γ t.

Definition L2_endpoints (γ : R -> Point) (t0 t1 : R) (ts : list R) : Prop :=
  match ts with
  | [] => False
  | t :: _ =>
      t = t0 /\ last ts t = t1 /\ γ t = γ t0 /\ γ (last ts t) = γ t1
  end.

Fixpoint param_incr (ts : list R) : Prop :=
  match ts with
  | [] => True
  | a :: rest =>
      match rest with
      | [] => True
      | b :: _ => a < b /\ param_incr rest
      end
  end.

Definition L3_monotone_cover (t0 t1 : R) (ts : list R) : Prop :=
  param_incr ts /\
  match ts with
  | [] => False
  | t :: _ => t = t0 /\ last ts 0 = t1
  end.

Fixpoint on_polyline (vs : list Point) (q : Point) : Prop :=
  match vs with
  | [] => False
  | p1 :: rest =>
      match rest with
      | [] => False
      | p2 :: _ => between p1 p2 q \/ on_polyline rest q
      end
  end.

Definition L4_within (tol : R) (γ : R -> Point) (t0 t1 : R)
    (vs : list Point) : Prop :=
  forall t, t0 <= t <= t1 -> exists q, on_polyline vs q /\ dist (γ t) q <= tol.

(* Parameter reversal.  For an egg this is the reversed CircularEgg. *)
Definition L6_reverse (γ : R -> Point) (t0 t1 : R) (ts : list R) : Prop :=
  map (fun s => γ (t0 + t1 - s)) ts = rev (map γ ts).

Definition L7_two_segments (ts : list R) : Prop :=
  (3 <= length ts)%nat.

Definition linearizes (γ : R -> Point) (t0 t1 tol : R) (ts : list R) : Prop :=
  L1_on_curve γ ts /\
  L2_endpoints γ t0 t1 ts /\
  L3_monotone_cover t0 t1 ts /\
  L4_within tol γ t0 t1 (map γ ts) /\
  L6_reverse γ t0 t1 ts /\
  L7_two_segments ts.

(* L5.  Not a conjunct of linearizes: Point has no Z or M. *)
Definition L5_zm (zm : R -> R) (ts zs : list R) : Prop :=
  zs = map zm ts.

Lemma L1_samples : forall γ ts, L1_on_curve γ ts.
Proof.
  intros γ ts p Hp.
  apply in_map_iff in Hp. destruct Hp as [t [Heq Hin]].
  exists t. split; [exact Hin | symmetry; exact Heq].
Qed.

Lemma L6_from_grid : forall (γ : R -> Point) (ts : list R),
  map (fun s => 1 - s) ts = rev ts ->
  map (fun s => γ (1 - s)) ts = rev (map γ ts).
Proof.
  intros γ ts H.
  rewrite <- map_rev. rewrite <- H. rewrite map_map. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Uniform parameter grid  0, 1/n, …, 1.                                  *)
(* -------------------------------------------------------------------------- *)

Fixpoint nats_upto (n : nat) : list nat :=
  match n with
  | 0%nat => [0%nat]
  | S n' => nats_upto n' ++ [S n']
  end.

Lemma nats_upto_length : forall n, length (nats_upto n) = S n.
Proof.
  induction n as [|n IH]; simpl; [reflexivity|].
  rewrite length_app, IH. simpl. lia.
Qed.

Lemma nats_upto_nth : forall n i d,
  (i <= n)%nat -> nth i (nats_upto n) d = i.
Proof.
  induction n as [|n IH]; intros i d Hi.
  - assert (i = 0)%nat by lia. subst. reflexivity.
  - destruct (Nat.eq_dec i (S n)) as [E|E].
    + subst i. simpl. rewrite app_nth2 by (rewrite nats_upto_length; lia).
      rewrite nats_upto_length.
      replace (S n - S n)%nat with 0%nat by lia. reflexivity.
    + simpl. rewrite app_nth1 by (rewrite nats_upto_length; lia).
      apply IH. lia.
Qed.

Definition arc_params (n : nat) : list R :=
  map (fun k => INR k / INR n) (nats_upto n).

Lemma arc_params_length : forall n, length (arc_params n) = S n.
Proof.
  intros n. unfold arc_params. rewrite length_map. apply nats_upto_length.
Qed.

Lemma arc_params_nth : forall n i,
  (1 <= n)%nat -> (i <= n)%nat ->
  nth i (arc_params n) 0 = INR i / INR n.
Proof.
  intros n i Hn Hi.
  assert (Hi' : (i < length (arc_params n))%nat).
  { rewrite arc_params_length. lia. }
  pose proof (nth_error_nth' (arc_params n) 0 Hi') as Hnth.
  assert (Hne : nth_error (arc_params n) i = Some (INR i / INR n)).
  { unfold arc_params. rewrite nth_error_map.
    assert (Hnat : nth_error (nats_upto n) i = Some i).
    { assert (Hilen : (i < length (nats_upto n))%nat).
      { rewrite nats_upto_length. lia. }
      pose proof (nth_error_nth' (nats_upto n) 0%nat Hilen) as Hn0.
      rewrite nats_upto_nth in Hn0 by exact Hi. exact Hn0. }
    rewrite Hnat. simpl. reflexivity. }
  rewrite Hne in Hnth. inversion Hnth. reflexivity.
Qed.

Lemma arc_params_nonempty : forall n, arc_params n <> [].
Proof.
  intros n E. apply (f_equal (@length R)) in E.
  rewrite arc_params_length in E. simpl in E. lia.
Qed.

Lemma hd_eq_nth0 : forall l : list R, l <> [] -> hd 0 l = nth 0 l 0.
Proof.
  intros [|a l] H; [contradiction|]. reflexivity.
Qed.

Lemma last_eq_nth : forall l : list R,
  l <> [] -> last l 0 = nth (length l - 1) l 0.
Proof.
  induction l as [|a l IH]; intros H; [contradiction|].
  destruct l as [|b l].
  - reflexivity.
  - simpl last. simpl length.
    replace (S (S (length l)) - 1)%nat with (S (length (b :: l) - 1)) by (simpl; lia).
    simpl nth. apply IH. discriminate.
Qed.

Lemma arc_params_ends : forall n,
  (1 <= n)%nat ->
  hd 0 (arc_params n) = 0 /\ last (arc_params n) 0 = 1.
Proof.
  intros n Hn. split.
  - rewrite hd_eq_nth0 by apply arc_params_nonempty.
    rewrite arc_params_nth by lia.
    rewrite INR_0. unfold Rdiv. rewrite Rmult_0_l. reflexivity.
  - rewrite last_eq_nth by apply arc_params_nonempty.
    rewrite arc_params_length.
    replace (S n - 1)%nat with n by lia.
    rewrite arc_params_nth by lia.
    field. apply not_0_INR. lia.
Qed.

Lemma param_incr_from_nth : forall ts,
  ts <> [] ->
  (forall i, (S i < length ts)%nat -> nth i ts 0 < nth (S i) ts 0) ->
  param_incr ts.
Proof.
  induction ts as [|a ts IH]; intros Hne Hstep; [contradiction|].
  destruct ts as [|b rest]; [exact I|].
  split.
  - change a with (nth 0 (a :: b :: rest) 0).
    change b with (nth 1 (a :: b :: rest) 0).
    apply Hstep. simpl. lia.
  - apply IH; [discriminate|].
    intros i Hi. specialize (Hstep (S i)).
    simpl in Hi. simpl. apply Hstep. simpl. lia.
Qed.

Lemma arc_params_incr : forall n, (1 <= n)%nat -> param_incr (arc_params n).
Proof.
  intros n Hn.
  apply param_incr_from_nth.
  - apply arc_params_nonempty.
  - intros i Hi. rewrite arc_params_length in Hi.
    rewrite arc_params_nth by lia. rewrite arc_params_nth by lia.
    rewrite S_INR. unfold Rdiv.
    assert (Hn0 : INR n <> 0) by (apply not_0_INR; lia).
    apply Rmult_lt_compat_r.
    + apply Rinv_0_lt_compat. apply lt_0_INR. lia.
    + lra.
Qed.

Lemma arc_params_sym : forall n,
  (1 <= n)%nat ->
  map (fun s : R => 1 - s) (arc_params n) = rev (arc_params n).
Proof.
  intros n Hn.
  apply (nth_ext _ _ 0 0).
  - rewrite length_map, length_rev. reflexivity.
  - intros i Hi.
    pose proof Hi as Himap.
    assert (Hi2 : (i < length (arc_params n))%nat).
    { rewrite arc_params_length. rewrite length_map, arc_params_length in Hi.
      exact Hi. }
    pose proof (nth_error_nth'
                  (map (fun s : R => 1 - s) (arc_params n)) 0 Himap) as HL.
    assert (Hir : (i < length (rev (arc_params n)))%nat).
    { rewrite length_rev, arc_params_length.
      rewrite length_map, arc_params_length in Hi. exact Hi. }
    pose proof (nth_error_nth' (rev (arc_params n)) 0 Hir) as HR.
    assert (Hi_le : (i <= n)%nat).
    { rewrite length_map, arc_params_length in Hi. lia. }
    rewrite nth_error_map in HL.
    rewrite (nth_error_nth' (arc_params n) 0 Hi2) in HL. simpl in HL.
    rewrite (arc_params_nth n i Hn Hi_le) in HL.
    rewrite nth_error_rev in HR. rewrite arc_params_length in HR.
    assert (Hltb : Nat.ltb i (S n) = true).
    { apply Nat.ltb_lt. rewrite length_map, arc_params_length in Hi. exact Hi. }
    rewrite Hltb in HR. simpl in HR.
    rewrite (nth_error_nth' (arc_params n) 0) in HR
      by (rewrite arc_params_length; lia).
    simpl in HR.
    replace (S n - S i)%nat with (n - i)%nat in HR by lia.
    assert (Hni : (n - i <= n)%nat) by lia.
    rewrite (arc_params_nth n (n - i) Hn Hni) in HR.
    rewrite minus_INR in HR by lia.
    assert (Hval : 1 - INR i / INR n = INR (n - i) / INR n).
    { rewrite minus_INR by exact Hi_le. field. apply not_0_INR. lia. }
    rewrite Hval in HL.
    injection HL as HLnth. injection HR as HRnth.
    rewrite <- HLnth. rewrite <- HRnth.
    rewrite minus_INR by exact Hi_le. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Segment count.  n = max(ceil(|Δθ| / step), 2).                          *)
(* -------------------------------------------------------------------------- *)

Definition arc_n (sweep step : R) : nat :=
  Nat.max (Z.to_nat (Zceil (Rabs sweep / step))) 2.

Lemma arc_n_ge2 : forall sweep step, (2 <= arc_n sweep step)%nat.
Proof.
  intros. unfold arc_n. lia.
Qed.

Lemma arc_n_step : forall sweep step,
  0 < step ->
  Rabs sweep / INR (arc_n sweep step) <= step.
Proof.
  intros sweep step Hstep.
  set (s := Rabs sweep / step).
  set (z := Zceil s).
  pose proof (Zceil_bound s) as Hz.
  assert (Hs0 : 0 <= s).
  { unfold s. unfold Rdiv. apply Rmult_le_pos.
    - apply Rabs_pos.
    - apply Rlt_le. apply Rinv_0_lt_compat. exact Hstep. }
  assert (Hz0 : (0 <= z)%Z).
  { apply Z.nlt_ge. intros Hneg.
    apply IZR_lt in Hneg.
    destruct Hz as [_ Hsle].
    assert (s < 0) by (apply Rle_lt_trans with (r2 := IZR z); assumption).
    lra. }
  assert (Hm : INR (Z.to_nat z) = IZR z).
  { rewrite INR_IZR_INZ. rewrite Z2Nat.id by exact Hz0. reflexivity. }
  assert (Hs_n : s <= INR (arc_n sweep step)).
  { apply Rle_trans with (r2 := IZR z).
    - apply Hz.
    - rewrite <- Hm. apply le_INR. unfold arc_n, z, s. lia. }
  assert (Habs : Rabs sweep <= step * INR (arc_n sweep step)).
  { unfold s in Hs_n. unfold Rdiv in Hs_n.
    apply Rmult_le_compat_l with (r := step) in Hs_n; [|lra].
    replace (step * (Rabs sweep * / step)) with (Rabs sweep) in Hs_n.
    - exact Hs_n.
    - field. lra. }
  unfold Rdiv.
  apply Rmult_le_reg_r with (r := INR (arc_n sweep step)).
  - apply lt_0_INR. pose proof (arc_n_ge2 sweep step). lia.
  - rewrite Rmult_assoc. rewrite Rinv_l.
    + rewrite Rmult_1_r. exact Habs.
    + apply not_0_INR. pose proof (arc_n_ge2 sweep step). lia.
Qed.

Lemma subarc_lt_pi : forall sweep n,
  Rabs sweep < 2 * PI ->
  (2 <= n)%nat ->
  Rabs sweep / INR n < PI.
Proof.
  intros sweep n Hsw Hn.
  assert (Hnpos : 0 < INR n) by (apply lt_0_INR; lia).
  assert (H2 : 2 <= INR n).
  { change 2 with (INR 2). apply le_INR. exact Hn. }
  apply Rlt_le_trans with (r2 := 2 * PI / INR n).
  - unfold Rdiv. apply Rmult_lt_compat_r.
    + apply Rinv_0_lt_compat. exact Hnpos.
    + exact Hsw.
  - apply Rmult_le_reg_r with (r := INR n); [exact Hnpos|].
    unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l by (apply not_0_INR; lia).
    rewrite Rmult_1_r.
    pose proof PI_RGT_0 as Hpi.
    replace (PI * INR n) with (INR n * PI) by ring.
    apply Rmult_le_compat_r; lra.
Qed.

Lemma sagitta_of_step : forall r sweep step n,
  0 < r ->
  0 < step <= PI ->
  (2 <= n)%nat ->
  Rabs sweep / INR n <= step ->
  r * (1 - cos (Rabs sweep / (2 * INR n)))
    <= r * (1 - cos (step / 2)).
Proof.
  intros r sweep step n Hr Hstep Hn Hphi.
  assert (Hnpos : 0 < INR n) by (apply lt_0_INR; lia).
  assert (Hhalf : 0 <= Rabs sweep / (2 * INR n) <= step / 2).
  { split.
    - unfold Rdiv. apply Rmult_le_pos; [apply Rabs_pos|].
      apply Rlt_le. apply Rinv_0_lt_compat. lra.
    - unfold Rdiv.
      replace (Rabs sweep * / (2 * INR n)) with (Rabs sweep * / INR n * / 2).
      + apply Rmult_le_compat_r.
        * apply Rlt_le. apply Rinv_0_lt_compat. lra.
        * exact Hphi.
      + field. lra. }
  assert (Hpi : step / 2 <= PI).
  { pose proof PI_RGT_0. lra. }
  apply Rmult_le_compat_l; [lra|].
  apply Rplus_le_compat_l. apply Ropp_le_contravar.
  apply cos_decr_1; try lra; try apply Hhalf; try exact Hpi.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Sagitta of one sub-arc.  Distance to the chord, not only the line.     *)
(* -------------------------------------------------------------------------- *)

Lemma chord_mix : forall Nx Tx half delta t,
  sin half <> 0 ->
  t = (sin half + sin delta) / (2 * sin half) ->
  (1 - t) * (Nx * cos half - Tx * sin half)
    + t * (Nx * cos half + Tx * sin half)
  = Nx * cos half + Tx * sin delta.
Proof.
  intros Nx Tx half delta t Hnz Ht. subst t. field. exact Hnz.
Qed.

Lemma dist_offset : forall qx qy r d nx ny,
  nx * nx + ny * ny = 1 ->
  0 <= r * d ->
  dist (mkPoint (qx + r * d * nx) (qy + r * d * ny)) (mkPoint qx qy) = r * d.
Proof.
  intros qx qy r d nx ny Hn Hd.
  unfold dist, dist_sq. cbn [px py].
  replace ((qx + r * d * nx - qx) * (qx + r * d * nx - qx)
         + (qy + r * d * ny - qy) * (qy + r * d * ny - qy))
    with ((r * d) * (r * d) * (nx * nx + ny * ny)) by ring.
  rewrite Hn. rewrite Rmult_1_r. apply sqrt_square. exact Hd.
Qed.

Lemma arc_point_near_chord :
  forall (o : Point) (r a b psi : R),
    0 < r ->
    a <= psi <= b ->
    0 < b - a < PI ->
    exists q : Point,
      between
        (mkPoint (px o + r * cos a) (py o + r * sin a))
        (mkPoint (px o + r * cos b) (py o + r * sin b)) q /\
      dist (mkPoint (px o + r * cos psi) (py o + r * sin psi)) q
        <= r * (1 - cos ((b - a) / 2)).
Proof.
  intros o r a b psi Hr [Hlo Hhi] Hspan.
  set (half := (b - a) / 2).
  set (mid := (a + b) / 2).
  set (delta := psi - mid).
  assert (Hhalf_pos : 0 < half) by (unfold half; lra).
  assert (Hhalf_lt : half < PI / 2).
  { unfold half. pose proof PI_RGT_0. lra. }
  assert (Hdelta : - half <= delta <= half) by (unfold delta, mid, half; lra).
  assert (Hsin : 0 < sin half).
  { apply sin_gt_0; [exact Hhalf_pos|]. pose proof PI_RGT_0. lra. }
  assert (Hsin_abs : Rabs (sin delta) <= sin half).
  { apply Rabs_le. split.
    - replace (- sin half) with (sin (- half)) by (rewrite sin_neg; ring).
      apply sin_incr_1.
      + pose proof PI_RGT_0. unfold half. lra.
      + pose proof PI_RGT_0. lra.
      + pose proof PI_RGT_0. lra.
      + pose proof PI_RGT_0. lra.
      + lra.
    - apply sin_incr_1.
      + pose proof PI_RGT_0. lra.
      + pose proof PI_RGT_0. lra.
      + pose proof PI_RGT_0. lra.
      + pose proof PI_RGT_0. lra.
      + lra. }
  set (t := (sin half + sin delta) / (2 * sin half)).
  assert (Ht01 : 0 <= t <= 1).
  { assert (Hs : - sin half <= sin delta <= sin half).
    { destruct (Rle_or_lt (sin delta) 0) as [Hsd|Hsd].
      - split; [|lra].
        unfold Rabs in Hsin_abs.
        destruct (Rcase_abs (sin delta)) as [Hc|Hc]; lra.
      - split; [lra|].
        unfold Rabs in Hsin_abs.
        destruct (Rcase_abs (sin delta)) as [Hc|Hc]; lra. }
    split.
    - unfold t. unfold Rdiv. apply Rmult_le_pos.
      + lra.
      + apply Rlt_le. apply Rinv_0_lt_compat. lra.
    - unfold t. apply Rmult_le_reg_r with (r := 2 * sin half).
      + lra.
      + unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l by lra.
        rewrite Rmult_1_r. lra. }
  set (Nx := cos mid).
  set (Ny := sin mid).
  set (Tx := - sin mid).
  set (Ty := cos mid).
  set (dlt := cos delta - cos half).
  set (qx := px o + r * (Nx * cos half + Tx * sin delta)).
  set (qy := py o + r * (Ny * cos half + Ty * sin delta)).
  set (q := mkPoint qx qy).
  assert (Hcos_d : cos half <= cos delta).
  { assert (Habs : cos delta = cos (Rabs delta)).
    { unfold Rabs. destruct (Rcase_abs delta) as [Hd|Hd].
      - rewrite cos_neg. reflexivity.
      - reflexivity. }
    assert (Habs_le : Rabs delta <= half).
    { unfold Rabs. destruct (Rcase_abs delta); lra. }
    rewrite Habs. apply cos_decr_1.
    - apply Rabs_pos.
    - apply Rle_trans with half; [exact Habs_le|].
      pose proof PI_RGT_0. lra.
    - lra.
    - pose proof PI_RGT_0. lra.
    - exact Habs_le. }
  assert (Hdlt : 0 <= dlt) by (unfold dlt; lra).
  exists q. split.
  - exists t. split; [apply Ht01|]. split; [apply Ht01|].
    assert (Ha : cos a = Nx * cos half - Tx * sin half
              /\ sin a = Ny * cos half - Ty * sin half).
    { replace a with (mid - half) by (unfold mid, half; field).
      replace (mid - half) with (mid + - half) by ring.
      rewrite cos_plus, sin_plus, cos_neg, sin_neg.
      unfold Nx, Ny, Tx, Ty. split; ring. }
    assert (Hb : cos b = Nx * cos half + Tx * sin half
              /\ sin b = Ny * cos half + Ty * sin half).
    { replace b with (mid + half) by (unfold mid, half; field).
      rewrite cos_plus, sin_plus.
      unfold Nx, Ny, Tx, Ty. split; ring. }
    assert (Hmixx : (1 - t) * (Nx * cos half - Tx * sin half)
                  + t * (Nx * cos half + Tx * sin half)
                  = Nx * cos half + Tx * sin delta).
    { apply chord_mix; [lra | unfold t; reflexivity]. }
    assert (Hmixy : (1 - t) * (Ny * cos half - Ty * sin half)
                  + t * (Ny * cos half + Ty * sin half)
                  = Ny * cos half + Ty * sin delta).
    { apply chord_mix; [lra | unfold t; reflexivity]. }
    split.
    + simpl. unfold qx. rewrite <- Hmixx.
      rewrite <- (proj1 Ha). rewrite <- (proj1 Hb). ring.
    + simpl. unfold qy. rewrite <- Hmixy.
      rewrite <- (proj2 Ha). rewrite <- (proj2 Hb). ring.
  - assert (Hpx : px (mkPoint (px o + r * cos psi) (py o + r * sin psi))
                  = qx + r * dlt * Nx).
    { simpl. unfold qx, dlt, Nx, Tx.
      replace psi with (mid + delta) by (unfold delta; ring).
      rewrite cos_plus. ring. }
    assert (Hpy : py (mkPoint (px o + r * cos psi) (py o + r * sin psi))
                  = qy + r * dlt * Ny).
    { simpl. unfold qy, dlt, Ny, Ty.
      replace psi with (mid + delta) by (unfold delta; ring).
      rewrite sin_plus. ring. }
    replace (dist (mkPoint (px o + r * cos psi) (py o + r * sin psi)) q)
      with (r * dlt).
    + unfold dlt. apply Rmult_le_compat_l; [lra|].
      pose proof (COS_bound delta) as [Hclo Hchi]. lra.
    + assert (Hunit : Nx * Nx + Ny * Ny = 1).
      { unfold Nx, Ny. pose proof (sin2_cos2 mid) as Hsc.
        unfold Rsqr in Hsc. lra. }
      assert (Hp_eq : mkPoint (px o + r * cos psi) (py o + r * sin psi)
                      = mkPoint (qx + r * dlt * Nx) (qy + r * dlt * Ny)).
      { apply (f_equal2 mkPoint); [exact Hpx|exact Hpy]. }
      rewrite Hp_eq. unfold q. symmetry. apply dist_offset.
      -- exact Hunit.
      -- apply Rmult_le_pos; [lra|exact Hdlt].
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Which sub-arc a parameter falls in.                                    *)
(* -------------------------------------------------------------------------- *)

Fixpoint slot_aux (k n : nat) (t : R) : nat :=
  match k with
  | 0 => 0
  | S k' =>
      if Rle_dec (INR (S k') / INR n) t then S k' else slot_aux k' n t
  end.

Definition slot (n : nat) (t : R) : nat :=
  match n with
  | 0 => 0
  | S n' => slot_aux n' n t
  end.

Lemma slot_aux_spec : forall k n t,
  (1 <= n)%nat ->
  (k < n)%nat ->
  0 <= t ->
  t <= INR (S k) / INR n ->
  (slot_aux k n t <= k)%nat /\
  INR (slot_aux k n t) / INR n <= t /\
  t <= INR (S (slot_aux k n t)) / INR n.
Proof.
  induction k as [|k IH]; intros n t Hn Hk Ht0 Ht1.
  - simpl. split; [lia|]. split.
    + unfold Rdiv. rewrite Rmult_0_l. exact Ht0.
    + exact Ht1.
  - unfold slot_aux. destruct (Rle_dec (INR (S k) / INR n) t) as [Hle|Hgt].
    + fold slot_aux. split; [apply Nat.le_refl|]. split; [exact Hle|exact Ht1].
    + assert (Hlt : t < INR (S k) / INR n).
      { apply Rnot_le_lt. exact Hgt. }
      assert (Hk' : (k < n)%nat) by lia.
      destruct (IH n t Hn Hk' Ht0 (Rlt_le _ _ Hlt)) as [Hs [Hlo Hhi]].
      split; [|split; assumption].
      eapply Nat.le_trans; [exact Hs|]. apply Nat.le_succ_diag_r.
Qed.

Lemma slot_spec : forall n t,
  (1 <= n)%nat ->
  0 <= t <= 1 ->
  (slot n t < n)%nat /\
  INR (slot n t) / INR n <= t <= INR (S (slot n t)) / INR n.
Proof.
  intros n t Hn Ht.
  destruct n as [|n']; [lia|].
  unfold slot.
  assert (Hend : t <= INR (S n') / INR (S n')).
  { field_simplify; [|apply not_0_INR; lia]. lra. }
  destruct (slot_aux_spec n' (S n') t) as [Hs [Hlo Hhi]].
  - lia.
  - lia.
  - lra.
  - exact Hend.
  - split; [lia|]. split; assumption.
Qed.

Lemma on_polyline_skip : forall p vs q,
  on_polyline vs q -> on_polyline (p :: vs) q.
Proof.
  intros p vs q H.
  destruct vs as [|a rest]; [contradiction|].
  simpl. right. exact H.
Qed.

Lemma on_polyline_nth : forall (vs : list Point) i p1 p2 q,
  nth_error vs i = Some p1 ->
  nth_error vs (S i) = Some p2 ->
  between p1 p2 q ->
  on_polyline vs q.
Proof.
  intros vs i. revert vs.
  induction i as [|i IH]; intros vs p1 p2 q H1 H2 Hb.
  - destruct vs as [|a rest]; [discriminate|].
    simpl in H1. inversion H1. subst a. clear H1.
    destruct rest as [|b rest']; [discriminate|].
    simpl in H2. inversion H2. subst b. clear H2.
    simpl. left. exact Hb.
  - destruct vs as [|a rest]; [discriminate|].
    simpl in H1, H2. apply on_polyline_skip.
    eapply IH; eauto.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  The arc instance.                                                       *)
(* -------------------------------------------------------------------------- *)

Definition chord_approx_arc (c : CircularEgg) (n : nat) : list Point :=
  map (circ_eval c) (arc_params n).

Definition egg_rev (c : CircularEgg) : CircularEgg :=
  mkCircularEgg (circ_o c) (circ_r c)
    (circ_theta0 c + circ_sweep c) (- circ_sweep c).

Lemma egg_rev_eval : forall c t,
  circ_eval (egg_rev c) t = circ_eval c (1 - t).
Proof.
  intros c t. unfold circ_eval, egg_rev.
  cbn [circ_o circ_r circ_theta0 circ_sweep].
  replace (circ_theta0 c + circ_sweep c + t * (- circ_sweep c))
    with (circ_theta0 c + (1 - t) * circ_sweep c) by ring.
  reflexivity.
Qed.

Lemma chord_vertex : forall c n i,
  (1 <= n)%nat -> (i <= n)%nat ->
  nth_error (chord_approx_arc c n) i =
    Some (circ_eval c (INR i / INR n)).
Proof.
  intros c n i Hn Hi.
  unfold chord_approx_arc.
  rewrite nth_error_map.
  assert (Hnth : nth_error (arc_params n) i = Some (INR i / INR n)).
  { rewrite nth_error_nth' with (d := 0).
    - rewrite arc_params_nth by assumption. reflexivity.
    - rewrite arc_params_length. lia. }
  rewrite Hnth. reflexivity.
Qed.

Lemma arc_reverse_vertices : forall c n,
  (1 <= n)%nat ->
  chord_approx_arc (egg_rev c) n = rev (chord_approx_arc c n).
Proof.
  intros c n Hn.
  unfold chord_approx_arc.
  rewrite <- (L6_from_grid (circ_eval c)) by (apply arc_params_sym; exact Hn).
  apply map_ext. intros s. rewrite egg_rev_eval.
  replace (0 + 1 - s) with (1 - s) by ring.
  reflexivity.
Qed.

Lemma chord_approx_error_bound : forall c n t,
  0 < circ_r c ->
  0 < Rabs (circ_sweep c) < 2 * PI ->
  (2 <= n)%nat ->
  0 <= t <= 1 ->
  exists q,
    on_polyline (chord_approx_arc c n) q /\
    dist (circ_eval c t) q <=
      circ_r c * (1 - cos (Rabs (circ_sweep c) / (2 * INR n))).
Proof.
  intros c n t Hr [Hsw0 Hsw] Hn Ht.
  destruct (slot_spec n t) as [Hk [Hlo Hhi]]; [lia|exact Ht|].
  set (k := slot n t) in *.
  assert (Hphi : 0 < Rabs (circ_sweep c) / INR n < PI).
  { split.
    - unfold Rdiv. apply Rmult_lt_0_compat; [exact Hsw0|].
      apply Rinv_0_lt_compat. apply lt_0_INR. lia.
    - apply subarc_lt_pi; assumption. }
  set (u := INR k / INR n).
  set (v := INR (S k) / INR n).
  assert (Huv : u <= t <= v) by (unfold u, v; lra).
  assert (Hstep : v - u = 1 / INR n).
  { unfold u, v. rewrite S_INR. field. apply not_0_INR. lia. }
  pose (ang := fun s => circ_theta0 c + s * circ_sweep c).
  assert (Hpt : forall s,
            circ_eval c s =
            mkPoint (px (circ_o c) + circ_r c * cos (ang s))
                    (py (circ_o c) + circ_r c * sin (ang s))).
  { intros s. unfold circ_eval, ang. reflexivity. }
  destruct (Rle_dec 0 (circ_sweep c)) as [Hnn|Hneg].
  - assert (Hord : ang u <= ang t <= ang v).
    { unfold ang. split; apply Rplus_le_compat_l; apply Rmult_le_compat_r.
      - exact Hnn.
      - apply Huv.
      - exact Hnn.
      - apply Huv. }
    assert (Hwid : ang v - ang u = Rabs (circ_sweep c) / INR n).
    { unfold ang. replace (circ_theta0 c + v * circ_sweep c
                          - (circ_theta0 c + u * circ_sweep c))
        with ((v - u) * circ_sweep c) by ring.
      rewrite Hstep. rewrite Rabs_pos_eq by exact Hnn. field.
      apply not_0_INR. lia. }
    rewrite (Hpt t).
    destruct (arc_point_near_chord (circ_o c) (circ_r c) (ang u) (ang v) (ang t))
      as [q [Hb Hd]].
    + exact Hr.
    + exact Hord.
    + rewrite Hwid. exact Hphi.
    + exists q. split.
      * apply on_polyline_nth with (i := k)
            (p1 := circ_eval c u) (p2 := circ_eval c v).
        -- unfold u. apply chord_vertex; lia.
        -- unfold v. apply chord_vertex; lia.
        -- rewrite (Hpt u). rewrite (Hpt v). exact Hb.
      * eapply Rle_trans; [exact Hd|].
        rewrite Hwid.
        replace (Rabs (circ_sweep c) / INR n / 2)
          with (Rabs (circ_sweep c) / (2 * INR n)).
        -- apply Rle_refl.
        -- field. apply not_0_INR. lia.
  - assert (Hord : ang v <= ang t <= ang u).
    { unfold ang. split.
      - apply Rplus_le_compat_l.
        rewrite (Rmult_comm v), (Rmult_comm t).
        apply Rmult_le_compat_neg_l; [lra|].
        apply Huv.
      - apply Rplus_le_compat_l.
        rewrite (Rmult_comm t), (Rmult_comm u).
        apply Rmult_le_compat_neg_l; [lra|].
        apply Huv. }
    assert (Hwid : ang u - ang v = Rabs (circ_sweep c) / INR n).
    { unfold ang. replace (circ_theta0 c + u * circ_sweep c
                          - (circ_theta0 c + v * circ_sweep c))
        with ((u - v) * circ_sweep c) by ring.
      replace (u - v) with (- (v - u)) by ring.
      rewrite Hstep.
      assert (Habs : Rabs (circ_sweep c) = - circ_sweep c).
      { apply Rabs_left. lra. }
      rewrite Habs. field. apply not_0_INR. lia. }
    rewrite (Hpt t).
    destruct (arc_point_near_chord (circ_o c) (circ_r c) (ang v) (ang u) (ang t))
      as [q [Hb Hd]].
    + exact Hr.
    + exact Hord.
    + rewrite Hwid. exact Hphi.
    + exists q. split.
      * apply on_polyline_nth with (i := k)
            (p1 := circ_eval c u) (p2 := circ_eval c v).
        -- unfold u. apply chord_vertex; lia.
        -- unfold v. apply chord_vertex; lia.
        -- apply between_symmetric.
           rewrite (Hpt v). rewrite (Hpt u). exact Hb.
      * eapply Rle_trans; [exact Hd|].
        rewrite Hwid.
        replace (Rabs (circ_sweep c) / INR n / 2)
          with (Rabs (circ_sweep c) / (2 * INR n)).
        -- apply Rle_refl.
        -- field. apply not_0_INR. lia.
Qed.

Theorem arc_linearizes : forall c step max_angle tol,
  0 < circ_r c ->
  0 < Rabs (circ_sweep c) < 2 * PI ->
  0 < step /\ step <= max_angle /\ max_angle <= PI ->
  circ_r c * (1 - cos (step / 2)) <= tol ->
  linearizes (circ_eval c) 0 1 tol
    (arc_params (arc_n (circ_sweep c) step)).
Proof.
  intros c step max_angle tol Hr Hsw Hstep Htol.
  destruct Hstep as [Hstep0 [Hangle Hpi]].
  set (n := arc_n (circ_sweep c) step).
  assert (Hn : (2 <= n)%nat) by (unfold n; apply arc_n_ge2).
  assert (Hphi : Rabs (circ_sweep c) / INR n <= step).
  { unfold n. apply arc_n_step. lra. }
  assert (Hends : hd 0 (arc_params n) = 0 /\ last (arc_params n) 0 = 1).
  { apply arc_params_ends. lia. }
  destruct Hends as [Hhd Hlast].
  destruct (arc_params n) as [|h rest] eqn:E.
  - exfalso. apply (arc_params_nonempty n). exact E.
  - simpl in Hhd. subst h. simpl in Hlast.
    unfold linearizes. split; [|split; [|split; [|split; [|split]]]].
    + apply L1_samples.
    + unfold L2_endpoints. simpl.
      split; [reflexivity|]. split; [exact Hlast|].
      split; [|rewrite Hlast]; reflexivity.
    + unfold L3_monotone_cover. split.
      * rewrite <- E. apply arc_params_incr. lia.
      * simpl. split; [reflexivity|exact Hlast].
    + intros t Ht.
      destruct (chord_approx_error_bound c n t Hr Hsw Hn Ht) as [q [Hq Hd]].
      exists q. split.
      * unfold chord_approx_arc in Hq. rewrite E in Hq. exact Hq.
      * eapply Rle_trans; [exact Hd|]. eapply Rle_trans.
        -- assert (Hspi : 0 < step <= PI) by (split; [exact Hstep0|lra]).
           apply (sagitta_of_step (circ_r c) (circ_sweep c) step n
                    Hr Hspi Hn Hphi).
        -- exact Htol.
    + unfold L6_reverse. rewrite <- E.
      transitivity (map (fun s => circ_eval c (1 - s)) (arc_params n)).
      * apply map_ext. intros s. replace (0 + 1 - s) with (1 - s) by ring.
        reflexivity.
      * apply L6_from_grid. apply arc_params_sym. lia.
    + unfold L7_two_segments. rewrite <- E. rewrite arc_params_length. lia.
Qed.

(* Full circle.  arc_linearizes asks |Δθ| < 2π.  Closing the loop is the
   winding #892 has to supply; this name is the follow-up, not a proof. *)
Definition full_circle_linearise_followup (c : CircularEgg) : Prop :=
  Rabs (circ_sweep c) = 2 * PI.

Lemma arc_linearizes_excludes_full_circle : forall c,
  0 < Rabs (circ_sweep c) < 2 * PI ->
  ~ full_circle_linearise_followup c.
Proof.
  intros c [Hpos Hlt] Hfull.
  unfold full_circle_linearise_followup in Hfull. lra.
Qed.

Print Assumptions L1_samples.
Print Assumptions L6_from_grid.
Print Assumptions nats_upto_length.
Print Assumptions nats_upto_nth.
Print Assumptions arc_params_length.
Print Assumptions arc_params_nth.
Print Assumptions arc_params_nonempty.
Print Assumptions hd_eq_nth0.
Print Assumptions last_eq_nth.
Print Assumptions arc_params_ends.
Print Assumptions param_incr_from_nth.
Print Assumptions arc_params_incr.
Print Assumptions arc_params_sym.
Print Assumptions arc_n_ge2.
Print Assumptions arc_n_step.
Print Assumptions subarc_lt_pi.
Print Assumptions sagitta_of_step.
Print Assumptions chord_mix.
Print Assumptions dist_offset.
Print Assumptions arc_point_near_chord.
Print Assumptions slot_aux_spec.
Print Assumptions slot_spec.
Print Assumptions on_polyline_skip.
Print Assumptions on_polyline_nth.
Print Assumptions egg_rev_eval.
Print Assumptions chord_vertex.
Print Assumptions arc_reverse_vertices.
Print Assumptions chord_approx_error_bound.
Print Assumptions arc_linearizes.
Print Assumptions arc_linearizes_excludes_full_circle.
