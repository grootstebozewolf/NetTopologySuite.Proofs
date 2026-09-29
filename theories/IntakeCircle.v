(* ============================================================================
   NetTopologySuite.Proofs.IntakeCircle
   ----------------------------------------------------------------------------
   ISO/IEC 13249-3 CIRCLE (claimId 0007-intake-angles, not reminted).
   Three controls A,B,C name a full circle. θ₀ is the chart angle of A
   about the circumcentre (the same egg_of_points angle as
   CIRCULARSTRING, equal to atan2(A−O)). Sweep is +2π when (A,B,C)
   turns CCW and −2π when CW. γ(0)=γ(1)=A. Bag ends are [A; A].

   CIRCULARSTRING(A,B,A) is not this circle. That Decline is
   try_cs_closed_degenerate / ID_CsClosedDegenerate.

   NTS clean-room: γ(t) = O + r·(cos(θ₀+t·Δθ), sin(θ₀+t·Δθ))
   with θ₀ = atan2(Ay−Oy, Ax−Ox) and Δθ = sign(orient(A,B,C))·2π.
   GEOS is a behavioural reference only. No Admitted.

   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra Field List.
From NTS.Proofs Require Import Distance Segment SheetHenCook CircleChart Atan2
  IntakeAngles.
Import ListNotations.
Local Open Scope R_scope.
Local Open Scope list_scope.

Lemma orient_of_denom : forall a b c,
  circ_denom a b c <> 0 -> orient_pts a b c <> 0.
Proof.
  intros a b c Hd Ho.
  apply Hd. rewrite circ_denom_orient, Ho. ring.
Qed.

Lemma two_pi_neq0 : 2 * PI <> 0.
Proof.
  pose proof PI_RGT_0. lra.
Qed.

Lemma full_sweep_pos : forall a b c,
  0 < orient_pts a b c -> full_sweep a b c = 2 * PI.
Proof.
  intros a b c H. unfold full_sweep.
  destruct (Rle_dec 0 (orient_pts a b c)); [reflexivity|lra].
Qed.

Lemma full_sweep_neg : forall a b c,
  orient_pts a b c < 0 -> full_sweep a b c = - (2 * PI).
Proof.
  intros a b c H. unfold full_sweep.
  destruct (Rle_dec 0 (orient_pts a b c)); [lra|reflexivity].
Qed.

Lemma full_sweep_spec : forall a b c,
  orient_pts a b c <> 0 ->
  Rabs (full_sweep a b c) = 2 * PI /\
  full_sweep a b c * orient_pts a b c > 0.
Proof.
  intros a b c Ho.
  pose proof PI_RGT_0 as Hp.
  unfold full_sweep.
  destruct (Rle_dec 0 (orient_pts a b c)) as [Hle|Hlt].
  - assert (0 < orient_pts a b c) by lra.
    split.
    + rewrite Rabs_right by lra. reflexivity.
    + nra.
  - assert (orient_pts a b c < 0) by lra.
    split.
    + rewrite Rabs_left by lra.
      replace (- - (2 * PI)) with (2 * PI) by ring.
      reflexivity.
    + nra.
Qed.

Lemma div_pos : forall x y, y <> 0 -> x * y > 0 -> 0 < x / y.
Proof.
  intros x y Hy Hp. unfold Rdiv.
  destruct (Rle_dec 0 y) as [Hy0|Hy0].
  - assert (0 < y) by lra.
    assert (0 < x) by nra.
    apply Rmult_lt_0_compat; [exact H0|].
    apply Rinv_0_lt_compat. exact H.
  - assert (y < 0) by lra.
    assert (x < 0) by nra.
    assert (/ y < 0) by (apply Rinv_lt_0_compat; exact H).
    assert (0 < (- x) * (- / y)).
    { apply Rmult_lt_0_compat; lra. }
    replace ((- x) * (- / y)) with (x * / y) in H2 by ring.
    exact H2.
Qed.

Lemma abs_div_lt_1 : forall x y,
  y <> 0 -> Rabs x < Rabs y -> Rabs (x / y) < 1.
Proof.
  intros x y Hy Hlt.
  unfold Rdiv. rewrite Rabs_mult, Rabs_inv.
  apply Rmult_lt_reg_r with (r := Rabs y).
  - apply Rabs_pos_lt. exact Hy.
  - rewrite Rmult_assoc, Rinv_l.
    + rewrite Rmult_1_r, Rmult_1_l. exact Hlt.
    + pose proof (Rabs_pos_lt y Hy). lra.
Qed.

Lemma arc_ratio_open : forall a b c,
  dist_sq a b <> 0 ->
  dist_sq b c <> 0 ->
  dist_sq a c <> 0 ->
  circ_denom a b c <> 0 ->
  dist (circumcenter_of a b c) a <> 0 ->
  let s := circ_sweep (egg_of_points a b c) in
  let u := full_sweep a b c in
  u <> 0 /\ 0 < s / u /\ s / u < 1.
Proof.
  intros a b c Hab Hbc Hac Hd Hr s u.
  assert (Ho : orient_pts a b c <> 0) by (apply orient_of_denom; exact Hd).
  destruct (full_sweep_spec a b c Ho) as [Huabs Hsign].
  fold u in Huabs, Hsign.
  assert (Hu : u <> 0).
  { intros Z. rewrite Z, Rabs_R0 in Huabs.
    exact (two_pi_neq0 (eq_sym Huabs)). }
  pose proof (egg_sweep_sign a b c Hab Hbc Hac Hd Hr) as Hs.
  pose proof (egg_sweep_open a b c Hab Hbc Hac Hd Hr) as [_ Hslt].
  fold s in Hs, Hslt.
  assert (Hprod : s * u > 0) by nra.
  assert (Hpos : 0 < s / u) by (apply div_pos; assumption).
  assert (Habs : Rabs (s / u) < 1).
  { apply abs_div_lt_1; [exact Hu|]. rewrite Huabs. exact Hslt. }
  split; [exact Hu|].
  split; [exact Hpos|].
  rewrite (Rabs_right (s / u)) in Habs by lra. exact Habs.
Qed.

Lemma circle_eval0_arc : forall a b c,
  circ_eval (circle_of_egg (egg_of_points a b c) a b c) 0 =
  circ_eval (egg_of_points a b c) 0.
Proof.
  intros a b c.
  unfold circ_eval, circle_of_egg.
  cbn [px py circ_o circ_r circ_theta0 circ_sweep].
  replace (0 * full_sweep a b c)
    with (0 * circ_sweep (egg_of_points a b c)) by ring.
  reflexivity.
Qed.

Lemma circle_eval_at_arc : forall a b c t,
  full_sweep a b c <> 0 ->
  circ_eval (circle_of_egg (egg_of_points a b c) a b c)
    (t * circ_sweep (egg_of_points a b c) / full_sweep a b c) =
  circ_eval (egg_of_points a b c) t.
Proof.
  intros a b c t Hu.
  unfold circ_eval, circle_of_egg.
  cbn [px py circ_o circ_r circ_theta0 circ_sweep].
  replace ((t * circ_sweep (egg_of_points a b c) / full_sweep a b c) *
           full_sweep a b c)
    with (t * circ_sweep (egg_of_points a b c)) by (field; exact Hu).
  reflexivity.
Qed.

Lemma circle_eval1_eval0 : forall a b c,
  orient_pts a b c <> 0 ->
  circ_eval (circle_of_egg (egg_of_points a b c) a b c) 1 =
  circ_eval (circle_of_egg (egg_of_points a b c) a b c) 0.
Proof.
  intros a b c Ho.
  unfold circ_eval, circle_of_egg.
  cbn [px py circ_o circ_r circ_theta0 circ_sweep].
  set (th := circ_theta0 (egg_of_points a b c)) in *.
  replace (th + 0 * full_sweep a b c) with th by ring.
  replace (th + 1 * full_sweep a b c) with (th + full_sweep a b c) by ring.
  destruct (Rle_dec 0 (orient_pts a b c)) as [Hle|Hlt].
  - assert (Hgt : 0 < orient_pts a b c) by lra.
    rewrite (full_sweep_pos a b c Hgt).
    rewrite cos_shift_2pi, sin_shift_2pi. reflexivity.
  - assert (Hneg : orient_pts a b c < 0) by lra.
    rewrite (full_sweep_neg a b c Hneg).
    replace (th + - (2 * PI)) with (th - 2 * PI) by ring.
    rewrite cos_shift_m2pi, sin_shift_m2pi. reflexivity.
Qed.

Lemma circle_controls_on : forall a b c,
  circ_denom a b c <> 0 ->
  dist (circumcenter_of a b c) a <> 0 ->
  let o := circumcenter_of a b c in
  let r := dist o a in
  dist_sq o b = r * r /\ dist_sq o c = r * r.
Proof.
  intros a b c Hd Hr o r.
  destruct (circum_equidistant a b c Hd) as [Hb Hc].
  assert (Haa : dist_sq o a = r * r).
  { unfold r, dist. rewrite sqrt_sqrt; [reflexivity|].
    unfold dist_sq.
    pose proof (Rle_0_sqr (px o - px a)) as Hx.
    pose proof (Rle_0_sqr (py o - py a)) as Hy.
    unfold Rsqr in Hx, Hy. lra. }
  fold o in Hb, Hc.
  split; [rewrite Hb; exact Haa|rewrite Hc; exact Haa].
Qed.

Lemma angle_cos1_sin0 : forall th,
  - PI < th <= PI -> cos th = 1 -> sin th = 0 -> th = 0.
Proof.
  intros th Hr Hc Hs.
  apply (angle_eq_of_trig th 0).
  - rewrite cos_0. exact Hc.
  - rewrite sin_0. exact Hs.
  - pose proof PI_RGT_0. lra.
Qed.

Lemma angle_cosneg1_sin0 : forall th,
  - PI < th <= PI -> cos th = -1 -> sin th = 0 -> th = PI.
Proof.
  intros th Hr Hc Hs.
  apply (angle_eq_of_trig th PI).
  - rewrite cos_PI. exact Hc.
  - rewrite sin_PI. exact Hs.
  - pose proof PI_RGT_0. lra.
Qed.

(* WITNESS {"claimId":"0007-intake-angles","topic":"core","lemma":"circle_full_param","title":"ISO CIRCLE(A,B,C) is the full turn from A: theta0 is the chart angle of A, equal to atan2(A-O); sweep is +2pi CCW and -2pi CW; gamma(0)=gamma(1)=A; B then C lie on the circle with parameters in (0,1)","file":"theories/IntakeCircle.v","witness":"0007-intake-angles","board":"ADR-0007"} *)
Theorem circle_full_param : forall a b c,
  dist_sq a b <> 0 ->
  dist_sq b c <> 0 ->
  dist_sq a c <> 0 ->
  circ_denom a b c <> 0 ->
  dist (circumcenter_of a b c) a <> 0 ->
  let f := circle_of_egg (egg_of_points a b c) a b c in
  circ_eval f 0 = a /\
  circ_eval f 1 = a /\
  circ_theta0 f =
    atan2 (py a - py (circ_o f)) (px a - px (circ_o f)) /\
  - PI < circ_theta0 f <= PI /\
  Rabs (circ_sweep f) = 2 * PI /\
  circ_sweep f * orient_pts a b c > 0 /\
  (0 < orient_pts a b c -> circ_sweep f = 2 * PI) /\
  (orient_pts a b c < 0 -> circ_sweep f = - (2 * PI)) /\
  dist_sq (circ_o f) b = circ_r f * circ_r f /\
  dist_sq (circ_o f) c = circ_r f * circ_r f /\
  exists tb tc,
    0 < tb /\ tb < tc /\ tc < 1 /\
    circ_eval f tb = b /\
    circ_eval f tc = c.
Proof.
  intros a b c Hab Hbc Hac Hd Hr f.
  set (e := egg_of_points a b c).
  assert (Ho : orient_pts a b c <> 0) by (apply orient_of_denom; exact Hd).
  destruct (egg_on_controls a b c Hab Hbc Hac Hd Hr) as [H0 [H1 Hm]].
  fold e in H0, H1, Hm.
  assert (He0 : circ_eval f 0 = a).
  { unfold f. rewrite circle_eval0_arc. fold e. exact H0. }
  assert (He1 : circ_eval f 1 = a).
  { unfold f. rewrite (circle_eval1_eval0 a b c Ho).
    rewrite circle_eval0_arc. fold e. exact H0. }
  assert (Hth : - PI < circ_theta0 f <= PI).
  { unfold f, circle_of_egg. cbn. fold e.
    unfold e. apply egg_theta_range; assumption. }
  assert (Hatan : circ_theta0 f =
            atan2 (py a - py (circ_o f)) (px a - px (circ_o f))).
  { apply theta_is_atan2.
    - apply dist_pos_of_neq. unfold f, circle_of_egg. cbn. exact Hr.
    - exact He0.
    - exact Hth. }
  destruct (full_sweep_spec a b c Ho) as [Habs Hsign].
  assert (Hsw : circ_sweep f = full_sweep a b c).
  { unfold f, circle_of_egg. reflexivity. }
  assert (Hon : dist_sq (circ_o f) b = circ_r f * circ_r f /\
                dist_sq (circ_o f) c = circ_r f * circ_r f).
  { destruct (circle_controls_on a b c Hd Hr) as [Hb Hc].
    unfold f, circle_of_egg, e, egg_of_points. cbn.
    split; assumption. }
  destruct (arc_ratio_open a b c Hab Hbc Hac Hd Hr) as [Hu [Hpos Hlt1]].
  destruct Hm as [tm [Htm HM]].
  destruct Htm as [Htm0 Htm1].
  set (ratio := circ_sweep e / full_sweep a b c).
  assert (Hratio_pos : 0 < ratio).
  { unfold ratio. fold e. exact Hpos. }
  assert (Hratio_lt : ratio < 1).
  { unfold ratio. fold e. exact Hlt1. }
  set (tb := tm * ratio).
  assert (Htb0 : 0 < tb).
  { unfold tb. apply Rmult_lt_0_compat; assumption. }
  assert (Htb : tb < ratio).
  { unfold tb.
    assert (tm * ratio < 1 * ratio) by (apply Rmult_lt_compat_r; assumption).
    rewrite Rmult_1_l in H. exact H. }
  assert (HhitB : circ_eval f tb = b).
  { unfold tb, ratio, f.
    replace (tm * (circ_sweep e / full_sweep a b c))
      with (tm * circ_sweep e / full_sweep a b c) by (field; exact Hu).
    unfold e. rewrite (circle_eval_at_arc a b c tm Hu). fold e. exact HM. }
  assert (HhitC : circ_eval f ratio = c).
  { unfold ratio, f, e.
    replace (circ_sweep (egg_of_points a b c) / full_sweep a b c)
      with (1 * circ_sweep (egg_of_points a b c) / full_sweep a b c)
      by (field; exact Hu).
    rewrite (circle_eval_at_arc a b c 1 Hu). fold e. exact H1. }
  split; [exact He0|].
  split; [exact He1|].
  split; [exact Hatan|].
  split; [exact Hth|].
  split; [rewrite Hsw; exact Habs|].
  split; [rewrite Hsw; exact Hsign|].
  split; [intros Hp; rewrite Hsw; apply full_sweep_pos; exact Hp|].
  split; [intros Hn; rewrite Hsw; apply full_sweep_neg; exact Hn|].
  split; [exact (proj1 Hon)|].
  split; [exact (proj2 Hon)|].
  exists tb, ratio.
  split; [exact Htb0|].
  split; [exact Htb|].
  split; [exact Hratio_lt|].
  split; [exact HhitB|exact HhitC].
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked CCW fixture. A=(5,0), B=(0,5), C=(-5,0). Centre origin, θ₀=0.     *)
(* -------------------------------------------------------------------------- *)

Definition ccw_a : Point := mkPoint 5 0.
Definition ccw_b : Point := mkPoint 0 5.
Definition ccw_c : Point := mkPoint (-5) 0.

Lemma ccw_dab : dist_sq ccw_a ccw_b <> 0.
Proof. unfold dist_sq, ccw_a, ccw_b. cbn. lra. Qed.

Lemma ccw_dbc : dist_sq ccw_b ccw_c <> 0.
Proof. unfold dist_sq, ccw_b, ccw_c. cbn. lra. Qed.

Lemma ccw_dac : dist_sq ccw_a ccw_c <> 0.
Proof. unfold dist_sq, ccw_a, ccw_c. cbn. lra. Qed.

Lemma ccw_denom : circ_denom ccw_a ccw_b ccw_c = 100.
Proof. unfold circ_denom, ccw_a, ccw_b, ccw_c. cbn. ring. Qed.

Lemma ccw_denom_nz : circ_denom ccw_a ccw_b ccw_c <> 0.
Proof. rewrite ccw_denom. lra. Qed.

Lemma ccw_center : circumcenter_of ccw_a ccw_b ccw_c = mkPoint 0 0.
Proof.
  symmetry. apply center_unique.
  - exact ccw_denom_nz.
  - unfold dist_sq, ccw_a, ccw_b. cbn. ring.
  - unfold dist_sq, ccw_a, ccw_c. cbn. ring.
Qed.

Lemma ccw_radius : dist (circumcenter_of ccw_a ccw_b ccw_c) ccw_a = 5.
Proof.
  rewrite ccw_center. unfold dist, dist_sq, ccw_a. cbn.
  replace ((0 - 5) * (0 - 5) + (0 - 0) * (0 - 0)) with (5 * 5) by ring.
  apply sqrt_square. lra.
Qed.

Lemma ccw_r_nz : dist (circumcenter_of ccw_a ccw_b ccw_c) ccw_a <> 0.
Proof. rewrite ccw_radius. lra. Qed.

Lemma ccw_orient : 0 < orient_pts ccw_a ccw_b ccw_c.
Proof. unfold orient_pts, orient3, crs, ccw_a, ccw_b, ccw_c. cbn. lra. Qed.

Lemma ccw_theta0 : circ_theta0 (egg_of_points ccw_a ccw_b ccw_c) = 0.
Proof.
  set (e := egg_of_points ccw_a ccw_b ccw_c).
  assert (Hrng : - PI < circ_theta0 e <= PI).
  { unfold e. apply egg_theta_range; try assumption.
    exact ccw_dab. exact ccw_dbc. exact ccw_dac.
    exact ccw_denom_nz. exact ccw_r_nz. }
  destruct (egg_on_controls ccw_a ccw_b ccw_c ccw_dab ccw_dbc ccw_dac
              ccw_denom_nz ccw_r_nz) as [H0 _].
  fold e in H0.
  assert (Ho : circ_o e = mkPoint 0 0).
  { unfold e, egg_of_points. exact ccw_center. }
  assert (Hr : circ_r e = 5).
  { unfold e, egg_of_points. exact ccw_radius. }
  assert (Hx : px (circ_eval e 0) = px ccw_a) by (rewrite H0; reflexivity).
  assert (Hy : py (circ_eval e 0) = py ccw_a) by (rewrite H0; reflexivity).
  unfold circ_eval in Hx, Hy. rewrite Ho, Hr in Hx, Hy.
  cbn [px py] in Hx, Hy.
  replace (circ_theta0 e + 0 * circ_sweep e) with (circ_theta0 e) in Hx, Hy by ring.
  unfold ccw_a in Hx, Hy. cbn [px py] in Hx, Hy.
  assert (Hc : cos (circ_theta0 e) = 1).
  { apply (Rmult_eq_reg_l 5).
    - replace (5 * cos (circ_theta0 e)) with (0 + 5 * cos (circ_theta0 e)) by ring.
      replace (5 * 1) with 5 by ring. exact Hx.
    - lra. }
  assert (Hs : sin (circ_theta0 e) = 0).
  { apply (Rmult_eq_reg_l 5).
    - replace (5 * sin (circ_theta0 e)) with (0 + 5 * sin (circ_theta0 e)) by ring.
      replace (5 * 0) with 0 by ring. exact Hy.
    - lra. }
  apply angle_cos1_sin0; assumption.
Qed.

Lemma ccw_circle_concrete :
  circle_of_egg (egg_of_points ccw_a ccw_b ccw_c) ccw_a ccw_b ccw_c =
  mkCircularEgg (mkPoint 0 0) 5 0 (2 * PI).
Proof.
  unfold circle_of_egg.
  rewrite ccw_theta0.
  assert (Ho : circ_o (egg_of_points ccw_a ccw_b ccw_c) = mkPoint 0 0)
    by (unfold egg_of_points; exact ccw_center).
  assert (Hr : circ_r (egg_of_points ccw_a ccw_b ccw_c) = 5)
    by (unfold egg_of_points; exact ccw_radius).
  rewrite Ho, Hr, (full_sweep_pos _ _ _ ccw_orient).
  reflexivity.
Qed.

Lemma ccw_triple :
  try_triple ccw_a ccw_b ccw_c = inl (egg_of_points ccw_a ccw_b ccw_c).
Proof.
  unfold try_triple.
  destruct (Req_EM_T (dist_sq ccw_a ccw_b) 0) as [H|H];
    [exfalso; exact (ccw_dab H)|].
  destruct (Req_EM_T (dist_sq ccw_b ccw_c) 0) as [H2|H2];
    [exfalso; exact (ccw_dbc H2)|].
  destruct (Req_EM_T (dist_sq ccw_a ccw_c) 0) as [H3|H3];
    [exfalso; exact (ccw_dac H3)|].
  destruct (Req_EM_T (circ_denom ccw_a ccw_b ccw_c) 0) as [H4|H4];
    [exfalso; exact (ccw_denom_nz H4)|].
  destruct (Req_EM_T (dist (circumcenter_of ccw_a ccw_b ccw_c) ccw_a) 0)
    as [H5|H5];
    [exfalso; exact (ccw_r_nz H5)|].
  reflexivity.
Qed.

Lemma ccw_try_circle :
  try_circle_eggs [ccw_a; ccw_b; ccw_c] =
    inl ([mkCircularEgg (mkPoint 0 0) 5 0 (2 * PI)], [ccw_a; ccw_a]).
Proof.
  unfold try_circle_eggs. rewrite ccw_triple.
  rewrite ccw_circle_concrete. reflexivity.
Qed.

Theorem ccw_circle_fixture :
  let f := circle_of_egg (egg_of_points ccw_a ccw_b ccw_c) ccw_a ccw_b ccw_c in
  f = mkCircularEgg (mkPoint 0 0) 5 0 (2 * PI) /\
  circ_eval f 0 = ccw_a /\
  circ_eval f 1 = ccw_a /\
  circ_theta0 f = 0 /\
  circ_sweep f = 2 * PI /\
  circ_sweep f * orient_pts ccw_a ccw_b ccw_c > 0 /\
  exists tb tc,
    0 < tb /\ tb < tc /\ tc < 1 /\
    circ_eval f tb = ccw_b /\
    circ_eval f tc = ccw_c.
Proof.
  intros f.
  pose proof (circle_full_param ccw_a ccw_b ccw_c ccw_dab ccw_dbc ccw_dac
              ccw_denom_nz ccw_r_nz) as Hp.
  fold f in Hp.
  destruct Hp as [H0 [H1 [_ [_ [_ [Hsign [_ [_ [_ [_ Hord]]]]]]]]]].
  split; [unfold f; exact ccw_circle_concrete|].
  split; [exact H0|].
  split; [exact H1|].
  split; [unfold f, circle_of_egg; cbn; exact ccw_theta0|].
  split; [unfold f, circle_of_egg; cbn; apply full_sweep_pos; exact ccw_orient|].
  split; [exact Hsign|].
  exact Hord.
Qed.

(* -------------------------------------------------------------------------- *)
(* CW fixture. Same A and C, B=(0,-5). θ₀ stays 0; sweep = −2π.              *)
(* -------------------------------------------------------------------------- *)

Definition cw_a : Point := mkPoint 5 0.
Definition cw_b : Point := mkPoint 0 (-5).
Definition cw_c : Point := mkPoint (-5) 0.

Lemma cw_dab : dist_sq cw_a cw_b <> 0.
Proof. unfold dist_sq, cw_a, cw_b. cbn. lra. Qed.

Lemma cw_dbc : dist_sq cw_b cw_c <> 0.
Proof. unfold dist_sq, cw_b, cw_c. cbn. lra. Qed.

Lemma cw_dac : dist_sq cw_a cw_c <> 0.
Proof. unfold dist_sq, cw_a, cw_c. cbn. lra. Qed.

Lemma cw_denom_nz : circ_denom cw_a cw_b cw_c <> 0.
Proof. unfold circ_denom, cw_a, cw_b, cw_c. cbn. lra. Qed.

Lemma cw_center : circumcenter_of cw_a cw_b cw_c = mkPoint 0 0.
Proof.
  symmetry. apply center_unique.
  - exact cw_denom_nz.
  - unfold dist_sq, cw_a, cw_b. cbn. ring.
  - unfold dist_sq, cw_a, cw_c. cbn. ring.
Qed.

Lemma cw_radius : dist (circumcenter_of cw_a cw_b cw_c) cw_a = 5.
Proof.
  rewrite cw_center. unfold dist, dist_sq, cw_a. cbn.
  replace ((0 - 5) * (0 - 5) + (0 - 0) * (0 - 0)) with (5 * 5) by ring.
  apply sqrt_square. lra.
Qed.

Lemma cw_r_nz : dist (circumcenter_of cw_a cw_b cw_c) cw_a <> 0.
Proof. rewrite cw_radius. lra. Qed.

Lemma cw_orient : orient_pts cw_a cw_b cw_c < 0.
Proof. unfold orient_pts, orient3, crs, cw_a, cw_b, cw_c. cbn. lra. Qed.

Lemma cw_theta0 : circ_theta0 (egg_of_points cw_a cw_b cw_c) = 0.
Proof.
  set (e := egg_of_points cw_a cw_b cw_c).
  assert (Hrng : - PI < circ_theta0 e <= PI).
  { unfold e. apply egg_theta_range.
    exact cw_dab. exact cw_dbc. exact cw_dac. exact cw_denom_nz. exact cw_r_nz. }
  destruct (egg_on_controls cw_a cw_b cw_c cw_dab cw_dbc cw_dac
              cw_denom_nz cw_r_nz) as [H0 _].
  fold e in H0.
  assert (Ho : circ_o e = mkPoint 0 0).
  { unfold e, egg_of_points. exact cw_center. }
  assert (Hr : circ_r e = 5).
  { unfold e, egg_of_points. exact cw_radius. }
  assert (Hx : px (circ_eval e 0) = px cw_a) by (rewrite H0; reflexivity).
  assert (Hy : py (circ_eval e 0) = py cw_a) by (rewrite H0; reflexivity).
  unfold circ_eval in Hx, Hy. rewrite Ho, Hr in Hx, Hy.
  cbn [px py] in Hx, Hy.
  replace (circ_theta0 e + 0 * circ_sweep e) with (circ_theta0 e) in Hx, Hy by ring.
  unfold cw_a in Hx, Hy. cbn [px py] in Hx, Hy.
  assert (Hc : cos (circ_theta0 e) = 1).
  { apply (Rmult_eq_reg_l 5).
    - replace (5 * cos (circ_theta0 e)) with (0 + 5 * cos (circ_theta0 e)) by ring.
      replace (5 * 1) with 5 by ring. exact Hx.
    - lra. }
  assert (Hs : sin (circ_theta0 e) = 0).
  { apply (Rmult_eq_reg_l 5).
    - replace (5 * sin (circ_theta0 e)) with (0 + 5 * sin (circ_theta0 e)) by ring.
      replace (5 * 0) with 0 by ring. exact Hy.
    - lra. }
  apply angle_cos1_sin0; assumption.
Qed.

Theorem cw_circle_fixture :
  let f := circle_of_egg (egg_of_points cw_a cw_b cw_c) cw_a cw_b cw_c in
  circ_o f = mkPoint 0 0 /\
  circ_r f = 5 /\
  circ_theta0 f = 0 /\
  circ_sweep f = - (2 * PI) /\
  circ_eval f 0 = cw_a /\
  circ_eval f 1 = cw_a /\
  circ_sweep f * orient_pts cw_a cw_b cw_c > 0 /\
  exists tb tc,
    0 < tb /\ tb < tc /\ tc < 1 /\
    circ_eval f tb = cw_b /\
    circ_eval f tc = cw_c.
Proof.
  intros f.
  pose proof (circle_full_param cw_a cw_b cw_c cw_dab cw_dbc cw_dac
              cw_denom_nz cw_r_nz) as Hp.
  fold f in Hp.
  destruct Hp as [H0 [H1 [_ [_ [_ [Hsign [_ [Hneg [_ [_ Hord]]]]]]]]]].
  split; [unfold f, circle_of_egg, egg_of_points; exact cw_center|].
  split; [unfold f, circle_of_egg, egg_of_points; exact cw_radius|].
  split; [unfold f, circle_of_egg; cbn; exact cw_theta0|].
  split; [unfold f, circle_of_egg; cbn; apply full_sweep_neg; exact cw_orient|].
  split; [exact H0|].
  split; [exact H1|].
  split; [exact Hsign|].
  exact Hord.
Qed.

(* -------------------------------------------------------------------------- *)
(* Atan2 cut. A=(-1,0) sits on the negative x-axis, so θ₀ = π, not −π.       *)
(* B=(0,-1), C=(1,0) is the CCW order from that start.                       *)
(* -------------------------------------------------------------------------- *)

Definition cut_a : Point := mkPoint (-1) 0.
Definition cut_b : Point := mkPoint 0 (-1).
Definition cut_c : Point := mkPoint 1 0.

Lemma cut_dab : dist_sq cut_a cut_b <> 0.
Proof. unfold dist_sq, cut_a, cut_b. cbn. lra. Qed.

Lemma cut_dbc : dist_sq cut_b cut_c <> 0.
Proof. unfold dist_sq, cut_b, cut_c. cbn. lra. Qed.

Lemma cut_dac : dist_sq cut_a cut_c <> 0.
Proof. unfold dist_sq, cut_a, cut_c. cbn. lra. Qed.

Lemma cut_denom_nz : circ_denom cut_a cut_b cut_c <> 0.
Proof. unfold circ_denom, cut_a, cut_b, cut_c. cbn. lra. Qed.

Lemma cut_center : circumcenter_of cut_a cut_b cut_c = mkPoint 0 0.
Proof.
  symmetry. apply center_unique.
  - exact cut_denom_nz.
  - unfold dist_sq, cut_a, cut_b. cbn. ring.
  - unfold dist_sq, cut_a, cut_c. cbn. ring.
Qed.

Lemma cut_radius : dist (circumcenter_of cut_a cut_b cut_c) cut_a = 1.
Proof.
  rewrite cut_center. unfold dist, dist_sq, cut_a. cbn.
  replace ((0 - -1) * (0 - -1) + (0 - 0) * (0 - 0)) with 1 by ring.
  rewrite sqrt_1. reflexivity.
Qed.

Lemma cut_r_nz : dist (circumcenter_of cut_a cut_b cut_c) cut_a <> 0.
Proof. rewrite cut_radius. lra. Qed.

Lemma cut_orient : 0 < orient_pts cut_a cut_b cut_c.
Proof. unfold orient_pts, orient3, crs, cut_a, cut_b, cut_c. cbn. lra. Qed.

Lemma cut_theta0 : circ_theta0 (egg_of_points cut_a cut_b cut_c) = PI.
Proof.
  set (e := egg_of_points cut_a cut_b cut_c).
  assert (Hrng : - PI < circ_theta0 e <= PI).
  { unfold e. apply egg_theta_range.
    exact cut_dab. exact cut_dbc. exact cut_dac.
    exact cut_denom_nz. exact cut_r_nz. }
  destruct (egg_on_controls cut_a cut_b cut_c cut_dab cut_dbc cut_dac
              cut_denom_nz cut_r_nz) as [H0 _].
  fold e in H0.
  assert (Ho : circ_o e = mkPoint 0 0).
  { unfold e, egg_of_points. exact cut_center. }
  assert (Hr : circ_r e = 1).
  { unfold e, egg_of_points. exact cut_radius. }
  assert (Hx : px (circ_eval e 0) = px cut_a) by (rewrite H0; reflexivity).
  assert (Hy : py (circ_eval e 0) = py cut_a) by (rewrite H0; reflexivity).
  unfold circ_eval in Hx, Hy. rewrite Ho, Hr in Hx, Hy.
  cbn [px py] in Hx, Hy.
  replace (circ_theta0 e + 0 * circ_sweep e) with (circ_theta0 e) in Hx, Hy by ring.
  unfold cut_a in Hx, Hy. cbn [px py] in Hx, Hy.
  assert (Hc : cos (circ_theta0 e) = -1).
  { apply (Rmult_eq_reg_l 1).
    - replace (1 * cos (circ_theta0 e)) with (0 + 1 * cos (circ_theta0 e)) by ring.
      replace (1 * -1) with (-1) by ring. exact Hx.
    - lra. }
  assert (Hs : sin (circ_theta0 e) = 0).
  { apply (Rmult_eq_reg_l 1).
    - replace (1 * sin (circ_theta0 e)) with (0 + 1 * sin (circ_theta0 e)) by ring.
      replace (1 * 0) with 0 by ring. exact Hy.
    - lra. }
  apply angle_cosneg1_sin0; assumption.
Qed.

Theorem cut_circle_fixture :
  let f := circle_of_egg (egg_of_points cut_a cut_b cut_c) cut_a cut_b cut_c in
  circ_o f = mkPoint 0 0 /\
  circ_r f = 1 /\
  circ_theta0 f = PI /\
  circ_sweep f = 2 * PI /\
  circ_eval f 0 = cut_a /\
  circ_eval f 1 = cut_a /\
  circ_sweep f * orient_pts cut_a cut_b cut_c > 0 /\
  exists tb tc,
    0 < tb /\ tb < tc /\ tc < 1 /\
    circ_eval f tb = cut_b /\
    circ_eval f tc = cut_c.
Proof.
  intros f.
  pose proof (circle_full_param cut_a cut_b cut_c cut_dab cut_dbc cut_dac
              cut_denom_nz cut_r_nz) as Hp.
  fold f in Hp.
  destruct Hp as [H0 [H1 [_ [_ [_ [Hsign [Hpos [_ [_ [_ Hord]]]]]]]]]].
  split; [unfold f, circle_of_egg, egg_of_points; exact cut_center|].
  split; [unfold f, circle_of_egg, egg_of_points; exact cut_radius|].
  split; [unfold f, circle_of_egg; cbn; exact cut_theta0|].
  split; [unfold f, circle_of_egg; cbn; apply full_sweep_pos; exact cut_orient|].
  split; [exact H0|].
  split; [exact H1|].
  split; [exact Hsign|].
  exact Hord.
Qed.

Print Assumptions orient_of_denom.
Print Assumptions two_pi_neq0.
Print Assumptions full_sweep_pos.
Print Assumptions full_sweep_neg.
Print Assumptions full_sweep_spec.
Print Assumptions div_pos.
Print Assumptions abs_div_lt_1.
Print Assumptions arc_ratio_open.
Print Assumptions circle_eval0_arc.
Print Assumptions circle_eval_at_arc.
Print Assumptions circle_eval1_eval0.
Print Assumptions circle_controls_on.
Print Assumptions angle_cos1_sin0.
Print Assumptions angle_cosneg1_sin0.
Print Assumptions circle_full_param.
Print Assumptions ccw_dab.
Print Assumptions ccw_dbc.
Print Assumptions ccw_dac.
Print Assumptions ccw_denom.
Print Assumptions ccw_denom_nz.
Print Assumptions ccw_center.
Print Assumptions ccw_radius.
Print Assumptions ccw_r_nz.
Print Assumptions ccw_orient.
Print Assumptions ccw_theta0.
Print Assumptions ccw_circle_concrete.
Print Assumptions ccw_triple.
Print Assumptions ccw_try_circle.
Print Assumptions ccw_circle_fixture.
Print Assumptions cw_dab.
Print Assumptions cw_dbc.
Print Assumptions cw_dac.
Print Assumptions cw_denom_nz.
Print Assumptions cw_center.
Print Assumptions cw_radius.
Print Assumptions cw_r_nz.
Print Assumptions cw_orient.
Print Assumptions cw_theta0.
Print Assumptions cw_circle_fixture.
Print Assumptions cut_dab.
Print Assumptions cut_dbc.
Print Assumptions cut_dac.
Print Assumptions cut_denom_nz.
Print Assumptions cut_center.
Print Assumptions cut_radius.
Print Assumptions cut_r_nz.
Print Assumptions cut_orient.
Print Assumptions cut_theta0.
Print Assumptions cut_circle_fixture.
