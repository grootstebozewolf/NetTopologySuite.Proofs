(* ============================================================================
   NetTopologySuite.Proofs.IntakeAngles
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: intake angles-from-points
   (claimId 0007-intake-angles). Needle AFTER first-slice walker
   (#725 / claimId 0007-intake-walker). Not a CircGamma remint.

   Host constructs CircularEgg (O, r, theta0, sweep) from well-formed
   WKT circular control points. Definitions and chart evaluation live
   in IntakeAnglesCore / IntakeAnglesChart. This file is the letter:
   carry-and-check, agreement by atan2_unique, and the CCW / CW
   fixtures. Supersedes the +/-2*PI statement
   IntakeAngles.v : intake_angles_ctor_shape (theta0 = 0, sweep = +2*PI)
   for a proper arc. ISO CIRCLE is IntakeCircle: theta0 is this chart
   angle of A, sweep is ±2*PI. Host gamma is circ_eval. Sidecar Parks
   Gamma is not reminted.

   Fail closed: empty / bad count / duplicate control / collinear
   / zero-radius. No silent chord demote. Mapper consumers live in
   IntakeWalker.v.

   WITNESS topic: core · claimId: 0007-intake-angles
   witness: 0007-intake-angles
   board: ADR-0007
   3-axiom host. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra Field List.
From NTS.Proofs Require Import Distance Segment SheetHenCook CircleChart Atan2 AtanIvt
  CurveGeometry ArcChordApprox.
From NTS.Proofs Require Export IntakeAnglesChart.
Import ListNotations.
Local Open Scope R_scope.
Local Open Scope list_scope.

(* -------------------------------------------------------------------------- *)
(* Carry-and-check. Geometric, not syntactic equality with the computed egg.  *)
(* -------------------------------------------------------------------------- *)

Definition carry_check (c : CircularEgg) (a m b : Point) : Prop :=
  0 < circ_r c /\
  circ_eval c 0 = a /\
  circ_eval c 1 = b /\
  (exists t, 0 < t < 1 /\ circ_eval c t = m) /\
  0 < Rabs (circ_sweep c) < 2 * PI /\
  - PI < circ_theta0 c <= PI /\
  dist_sq a m <> 0 /\
  dist_sq m b <> 0 /\
  dist_sq a b <> 0.

(* θ₀ is principal, in (−π, π]. A carried start angle outside that
   range (GML ArcByCenterPoint startAngle 350°) names the same
   direction but fails this check. try_carried has no WKT consumer;
   a future carrier should reduce θ₀ by 2π before checking.
   Full-circle Δθ = ±2π is outside this predicate on purpose. *)

Lemma circum_radius_nz : forall a m b,
  dist_sq a m <> 0 ->
  circ_denom a m b <> 0 ->
  dist (circumcenter_of a m b) a <> 0.
Proof.
  intros a m b Ham Hd Z.
  destruct (circum_equidistant a m b Hd) as [Hm _].
  assert (H0 : dist_sq (circumcenter_of a m b) a = 0).
  { unfold dist in Z.
    apply (f_equal (fun z => z * z)) in Z.
    rewrite sqrt_sqrt in Z by apply dist_sq_nonneg.
    rewrite Rmult_0_l in Z. exact Z. }
  set (o := circumcenter_of a m b) in *.
  assert (Ho : o = a).
  { unfold dist_sq in H0.
    pose proof (Rle_0_sqr (px o - px a)) as Hx.
    pose proof (Rle_0_sqr (py o - py a)) as Hy.
    unfold Rsqr in Hx, Hy.
    destruct (Rplus_eq_R0 _ _ Hx Hy H0) as [Hx0 Hy0].
    apply Point_eq_of_coords.
    - assert (px o - px a = 0) by (apply Rsqr_0_uniq; unfold Rsqr; exact Hx0).
      lra.
    - assert (py o - py a = 0) by (apply Rsqr_0_uniq; unfold Rsqr; exact Hy0).
      lra. }
  assert (Hz : dist_sq a m = 0).
  { rewrite Ho in Hm. unfold dist_sq at 2 in Hm.
    replace ((px a - px a) * (px a - px a) + (py a - py a) * (py a - py a))
      with 0 in Hm by ring.
    exact Hm. }
  exact (Ham Hz).
Qed.

(* WITNESS {"claimId":"0007-intake-angles","topic":"core","lemma":"egg_of_points_certified","title":"Every nondegenerate WKT triple's computed egg satisfies carry_check: it is the arc through A, M, B","file":"theories/IntakeAngles.v","witness":"0007-intake-angles","board":"ADR-0007"} *)
Theorem egg_of_points_certified : forall a m b,
  dist_sq a m <> 0 ->
  dist_sq m b <> 0 ->
  dist_sq a b <> 0 ->
  circ_denom a m b <> 0 ->
  carry_check (egg_of_points a m b) a m b.
Proof.
  intros a m b Ham Hmb Hab Hd.
  pose proof (circum_radius_nz a m b Ham Hd) as Hr.
  set (e := egg_of_points a m b).
  pose proof (egg_on_controls a m b Ham Hmb Hab Hd Hr) as Hon.
  cbn zeta in Hon. fold e in Hon.
  destruct Hon as [H0 [H1 Hmid]].
  destruct (egg_fields a m b) as [_ [HrE _]].
  fold e in HrE.
  unfold carry_check. fold e.
  split. { rewrite HrE. apply dist_pos_of_neq. exact Hr. }
  split. { exact H0. }
  split. { exact H1. }
  split. { exact Hmid. }
  split. { apply egg_sweep_open; assumption. }
  split. { apply egg_theta_range; assumption. }
  split. { exact Ham. }
  split. { exact Hmb. }
  exact Hab.
Qed.

Lemma circ_eval_dist_sq : forall c t,
  dist_sq (circ_o c) (circ_eval c t) = circ_r c * circ_r c.
Proof.
  intros c t.
  unfold circ_eval, dist_sq. cbn.
  pose proof (sin2_cos2 (circ_theta0 c + t * circ_sweep c)) as Hs.
  unfold Rsqr in Hs. nra.
Qed.

Lemma circ_egg_eq : forall c1 c2,
  circ_o c1 = circ_o c2 ->
  circ_r c1 = circ_r c2 ->
  circ_theta0 c1 = circ_theta0 c2 ->
  circ_sweep c1 = circ_sweep c2 ->
  c1 = c2.
Proof.
  intros [o1 r1 t1 s1] [o2 r2 t2 s2]. cbn. intros. subst. reflexivity.
Qed.

Lemma no_equidistant_collinear : forall U a m b,
  dist_sq a m <> 0 ->
  dist_sq m b <> 0 ->
  dist_sq a b <> 0 ->
  circ_denom a m b = 0 ->
  ~ (dist_sq U a = dist_sq U m /\ dist_sq U a = dist_sq U b).
Proof.
  intros U a m b Ham Hmb Hab Hd [Hm Hb].
  rewrite circ_denom_orient in Hd.
  assert (Ho : orient_pts a m b = 0) by lra.
  unfold dist_sq in Hm, Hb.
  set (mx := px m - px a) in *.
  set (my := py m - py a) in *.
  set (bx := px b - px a) in *.
  set (by_ := py b - py a) in *.
  set (ux := px U - px a) in *.
  set (uy := py U - py a) in *.
  assert (Hcross : mx * by_ - my * bx = 0).
  { unfold orient_pts, orient3, crs in Ho. cbn in Ho.
    unfold mx, my, bx, by_ in *. exact Ho. }
  assert (Eqm : 2 * ux * mx + 2 * uy * my = mx * mx + my * my).
  { unfold ux, uy, mx, my in *. nra. }
  assert (Eqb : 2 * ux * bx + 2 * uy * by_ = bx * bx + by_ * by_).
  { unfold ux, uy, bx, by_ in *. nra. }
  assert (Hab2 : bx * bx + by_ * by_ <> 0).
  { unfold bx, by_.
    replace ((px b - px a) * (px b - px a) + (py b - py a) * (py b - py a))
      with ((px a - px b) * (px a - px b) + (py a - py b) * (py a - py b))
      by ring.
    exact Hab. }
  assert (Ham2 : mx * mx + my * my <> 0).
  { unfold mx, my, dist_sq in *. cbn in *. nra. }
  destruct (Req_dec bx 0) as [Hbx|Hbx].
  - destruct (Req_dec by_ 0) as [Hby|Hby].
    + apply Hab2. rewrite Hbx, Hby. ring.
    + assert (Hmx0 : mx = 0) by nra.
      assert (Hmy0 : my <> 0) by nra.
      assert (Huy : 2 * uy = my) by nra.
      assert (Huyb : 2 * uy = by_) by nra.
      assert (Em : m = b).
      { apply Point_eq_of_coords; unfold mx, my, bx, by_ in *; lra. }
      apply (dist_sq_neq_ne m b Hmb). exact Em.
  - set (lam := mx / bx).
    assert (Hmx : mx = lam * bx) by (unfold lam; field; exact Hbx).
    assert (Hmy : my = lam * by_).
    { assert (Hcb : mx * by_ = my * bx) by nra.
      unfold lam. apply Rmult_eq_reg_r with (r := bx); [| exact Hbx].
      replace ((mx / bx) * by_ * bx) with (mx * by_) by (field; exact Hbx).
      symmetry. exact Hcb. }
    assert (Hlam : lam * (bx * bx + by_ * by_)
                   = lam * lam * (bx * bx + by_ * by_)).
    { assert (E : 2 * ux * mx + 2 * uy * my
                  = lam * (2 * ux * bx + 2 * uy * by_)).
      { rewrite Hmx, Hmy. ring. }
      assert (R : mx * mx + my * my
                  = lam * lam * (bx * bx + by_ * by_)).
      { rewrite Hmx, Hmy. ring. }
      rewrite <- R, <- Eqm, E, Eqb. ring. }
    assert (W : lam * (1 - lam) * (bx * bx + by_ * by_) = 0) by nra.
    apply Rmult_integral in W. destruct W as [W|W].
    + apply Rmult_integral in W. destruct W as [Z|Z].
      * assert (Em : m = a).
        { assert (Hmx0 : mx = 0).
          { apply Rmult_eq_reg_r with (r := / bx);
              [| apply Rinv_neq_0_compat; exact Hbx].
            unfold lam in Z. rewrite Rmult_0_l.
            replace (mx * / bx) with (mx / bx) by (unfold Rdiv; ring).
            exact Z. }
          assert (Hmy0 : my = 0).
          { rewrite Hmy, Z. ring. }
          apply Point_eq_of_coords; unfold mx, my in *; lra. }
        apply (dist_sq_neq_ne a m Ham). symmetry. exact Em.
      * assert (El : lam = 1) by lra.
        assert (Em : m = b).
        { apply Point_eq_of_coords.
          - apply (Rplus_eq_reg_r (- px a)).
            replace (px m + - px a) with mx by (unfold mx; ring).
            replace (px b + - px a) with bx by (unfold bx; ring).
            rewrite Hmx, El. ring.
          - apply (Rplus_eq_reg_r (- py a)).
            replace (py m + - py a) with my by (unfold my; ring).
            replace (py b + - py a) with by_ by (unfold by_; ring).
            rewrite Hmy, El. ring. }
        apply (dist_sq_neq_ne m b Hmb). exact Em.
    + apply Hab2. exact W.
Qed.

Lemma cos_one_span4 : forall t,
  - (4 * PI) < t < 4 * PI ->
  cos t = 1 ->
  t = 0 \/ t = 2 * PI \/ t = - (2 * PI).
Proof.
  intros t Ht Hc.
  pose proof PI_RGT_0 as Hp.
  destruct (Rlt_dec t (2 * PI)) as [Hhi|Hhi].
  - destruct (Rlt_dec (- (2 * PI)) t) as [Hlo|Hlo].
    + left. apply cos_eq_1_two_pi; lra.
    + right. right.
      assert (Hspan : - (2 * PI) < t + 2 * PI < 2 * PI) by lra.
      assert (Hc2 : cos (t + 2 * PI) = 1).
      { rewrite cos_shift_2pi. exact Hc. }
      assert (E : t + 2 * PI = 0).
      { apply cos_eq_1_two_pi; assumption. }
      lra.
  - right. left.
    assert (Hspan : - (2 * PI) < t - 2 * PI < 2 * PI) by lra.
    assert (Hc2 : cos (t - 2 * PI) = 1).
    { rewrite cos_shift_m2pi. exact Hc. }
    assert (E : t - 2 * PI = 0).
    { apply cos_eq_1_two_pi; assumption. }
    lra.
Qed.

Lemma sweep_complement : forall x y,
  Rabs x < 2 * PI ->
  Rabs y < 2 * PI ->
  (y = x + 2 * PI \/ y = x - 2 * PI) ->
  x * y < 0 /\ Rabs x + Rabs y = 2 * PI.
Proof.
  intros x y Hx Hy [E|E].
  - apply Rabs_def2 in Hx. apply Rabs_def2 in Hy.
    assert (x < 0 /\ 0 < y) by (pose proof PI_RGT_0; lra).
    rewrite (Rabs_left x) by lra.
    rewrite (Rabs_right y) by lra.
    split; nra.
  - apply Rabs_def2 in Hx. apply Rabs_def2 in Hy.
    assert (0 < x /\ y < 0) by (pose proof PI_RGT_0; lra).
    rewrite (Rabs_right x) by lra.
    rewrite (Rabs_left y) by lra.
    split; nra.
Qed.

Lemma opp_abs_sum : forall x y,
  x * y < 0 ->
  Rabs (x - y) = Rabs x + Rabs y.
Proof.
  intros x y H.
  destruct (Rle_dec 0 x) as [Hx|Hx].
  - assert (y < 0) by nra.
    assert (0 < x) by nra.
    rewrite (Rabs_right x) by lra.
    rewrite (Rabs_left y) by lra.
    rewrite (Rabs_right (x - y)) by lra.
    lra.
  - assert (x < 0) by lra.
    assert (0 < y) by nra.
    rewrite (Rabs_left x) by lra.
    rewrite (Rabs_right y) by lra.
    rewrite (Rabs_left (x - y)) by lra.
    lra.
Qed.

Lemma theta_is_atan2 : forall c p,
  0 < circ_r c ->
  circ_eval c 0 = p ->
  - PI < circ_theta0 c <= PI ->
  circ_theta0 c =
    atan2 (py p - py (circ_o c)) (px p - px (circ_o c)).
Proof.
  intros c p Hr He Hrng.
  set (x := px p - px (circ_o c)).
  set (y := py p - py (circ_o c)).
  assert (Hsq : x * x + y * y = circ_r c * circ_r c).
  { unfold x, y.
    replace (px p) with (px (circ_eval c 0)) by (rewrite He; reflexivity).
    replace (py p) with (py (circ_eval c 0)) by (rewrite He; reflexivity).
    pose proof (circ_eval_dist_sq c 0) as E.
    unfold dist_sq in E.
    replace ((px (circ_eval c 0) - px (circ_o c)) *
             (px (circ_eval c 0) - px (circ_o c)) +
             (py (circ_eval c 0) - py (circ_o c)) *
             (py (circ_eval c 0) - py (circ_o c)))
      with ((px (circ_o c) - px (circ_eval c 0)) *
            (px (circ_o c) - px (circ_eval c 0)) +
            (py (circ_o c) - py (circ_eval c 0)) *
            (py (circ_o c) - py (circ_eval c 0))) by ring.
    exact E. }
  assert (Hs : sqrt (x * x + y * y) = circ_r c).
  { rewrite Hsq. apply sqrt_square. lra. }
  assert (Hne : ~ (x = 0 /\ y = 0)).
  { intros [Hx Hy]. assert (x * x + y * y = 0) by nra.
    rewrite Hsq in H. nra. }
  assert (Hex : px p = px (circ_o c) + circ_r c * cos (circ_theta0 c)).
  { apply (f_equal px) in He. unfold circ_eval in He. cbn in He.
    replace (0 * circ_sweep c) with 0 in He by ring.
    rewrite Rplus_0_r in He. symmetry. exact He. }
  assert (Hey : py p = py (circ_o c) + circ_r c * sin (circ_theta0 c)).
  { apply (f_equal py) in He. unfold circ_eval in He. cbn in He.
    replace (0 * circ_sweep c) with 0 in He by ring.
    rewrite Rplus_0_r in He. symmetry. exact He. }
  apply atan2_unique.
  - exact Hne.
  - exact Hrng.
  - rewrite Hs.
    replace x with (circ_r c * cos (circ_theta0 c)).
    + field. lra.
    + unfold x. rewrite Hex. ring.
  - rewrite Hs.
    replace y with (circ_r c * sin (circ_theta0 c)).
    + field. lra.
    + unfold y. rewrite Hey. ring.
Qed.

(* WITNESS {"claimId":"0007-intake-angles","topic":"core","lemma":"intake_angles_agree","title":"Computed chart angles equal carried angles whenever carry-and-check passes, by atan2_unique; opposite ±2π arc is excluded by the interior control","file":"theories/IntakeAngles.v","witness":"0007-intake-angles","board":"ADR-0007"} *)
Theorem intake_angles_agree : forall c a m b,
  carry_check c a m b ->
  circ_o c = circ_o (egg_of_points a m b) /\
  circ_r c = circ_r (egg_of_points a m b) /\
  circ_theta0 c = circ_theta0 (egg_of_points a m b) /\
  circ_sweep c = circ_sweep (egg_of_points a m b).
Proof.
  intros c a m b H.
  destruct H as [Hr [Ha [Hb [Hmid [Habs [Hth [Ham [Hmb Hab]]]]]]]].
  assert (Hsqa : dist_sq (circ_o c) a = circ_r c * circ_r c).
  { rewrite <- Ha. apply circ_eval_dist_sq. }
  assert (Hsqb : dist_sq (circ_o c) b = circ_r c * circ_r c).
  { rewrite <- Hb. apply circ_eval_dist_sq. }
  destruct Hmid as [tc [Htc Hm]].
  assert (Hsqm : dist_sq (circ_o c) m = circ_r c * circ_r c).
  { rewrite <- Hm. apply circ_eval_dist_sq. }
  assert (Hd : circ_denom a m b <> 0).
  { destruct (Req_dec (circ_denom a m b) 0) as [Z|N]; [| exact N].
    exfalso.
    apply (no_equidistant_collinear (circ_o c) a m b Ham Hmb Hab Z).
    split; [rewrite Hsqa, Hsqm; reflexivity | rewrite Hsqa, Hsqb; reflexivity]. }
  assert (Ho : circ_o c = circumcenter_of a m b).
  { apply center_unique; [exact Hd | rewrite Hsqa, Hsqm; reflexivity |
                          rewrite Hsqa, Hsqb; reflexivity]. }
  set (e := egg_of_points a m b).
  assert (HrE : dist (circumcenter_of a m b) a <> 0).
  { rewrite <- Ho. intros Z.
    assert (dist_sq (circ_o c) a = 0).
    { unfold dist in Z. apply (f_equal (fun z => z * z)) in Z.
      rewrite sqrt_sqrt in Z by apply dist_sq_nonneg.
      rewrite Rmult_0_l in Z.
      unfold dist_sq in *. exact Z. }
    rewrite Hsqa in H. nra. }
  assert (Hon : circ_eval e 0 = a /\ circ_eval e 1 = b /\
                (exists t, 0 < t < 1 /\ circ_eval e t = m)).
  { apply egg_on_controls; assumption. }
  assert (Hrange_e : - PI < circ_theta0 e <= PI).
  { apply egg_theta_range; assumption. }
  assert (Hr_e : 0 < circ_r e).
  { destruct (egg_fields a m b) as [_ [Hr' _]].
    fold e in Hr'. rewrite Hr'.
    apply dist_pos_of_neq. exact HrE. }
  assert (Hth_c : circ_theta0 c =
            atan2 (py a - py (circ_o c)) (px a - px (circ_o c))).
  { apply theta_is_atan2; assumption. }
  assert (Hth_e : circ_theta0 e =
            atan2 (py a - py (circ_o e)) (px a - px (circ_o e))).
  { apply theta_is_atan2; try assumption. exact (proj1 Hon). }
  assert (Hoe : circ_o e = circumcenter_of a m b).
  { destruct (egg_fields a m b) as [Ho' _]. fold e in Ho'. exact Ho'. }
  assert (Hre : circ_r e = dist (circumcenter_of a m b) a).
  { destruct (egg_fields a m b) as [_ [Hr' _]]. fold e in Hr'. exact Hr'. }
  assert (Hth_eq : circ_theta0 c = circ_theta0 e).
  { rewrite Hth_c, Hth_e, Ho, Hoe. reflexivity. }
  assert (Hr_eq : circ_r c = circ_r e).
  { rewrite Hre, <- Ho.
    unfold dist. rewrite Hsqa. symmetry. apply sqrt_square. lra. }
  assert (Habs_e : 0 < Rabs (circ_sweep e) < 2 * PI).
  { apply egg_sweep_open; assumption. }
  assert (Hend : cos (circ_theta0 c + circ_sweep c)
                 = cos (circ_theta0 e + circ_sweep e) /\
                 sin (circ_theta0 c + circ_sweep c)
                 = sin (circ_theta0 e + circ_sweep e)).
  { apply (f_equal px) in Hb as Hbx.
    apply (f_equal py) in Hb as Hby.
    destruct Hon as [_ [Heb _]].
    apply (f_equal px) in Heb as Hex.
    apply (f_equal py) in Heb as Hey.
    unfold circ_eval in Hbx, Hby, Hex, Hey.
    cbn [px py] in Hbx, Hby, Hex, Hey.
    replace (1 * circ_sweep c) with (circ_sweep c) in Hbx, Hby by ring.
    replace (1 * circ_sweep e) with (circ_sweep e) in Hex, Hey by ring.
    rewrite Hoe, <- Ho, <- Hr_eq in Hex, Hey.
    assert (Hcx : circ_r c * cos (circ_theta0 c + circ_sweep c)
                  = circ_r c * cos (circ_theta0 e + circ_sweep e)) by nra.
    assert (Hsx : circ_r c * sin (circ_theta0 c + circ_sweep c)
                  = circ_r c * sin (circ_theta0 e + circ_sweep e)) by nra.
    split.
    - apply (Rmult_eq_reg_l (circ_r c)); [exact Hcx | lra].
    - apply (Rmult_eq_reg_l (circ_r c)); [exact Hsx | lra]. }
  assert (Hdiff : circ_sweep c - circ_sweep e = 0 \/
                  circ_sweep c - circ_sweep e = 2 * PI \/
                  circ_sweep c - circ_sweep e = - (2 * PI)).
  { apply cos_one_span4.
    - pose proof PI_RGT_0.
      assert (Rabs (circ_sweep c - circ_sweep e) < 4 * PI).
      { replace (circ_sweep c - circ_sweep e)
          with (circ_sweep c + - circ_sweep e) by ring.
        eapply Rle_lt_trans; [apply Rabs_triang|].
        rewrite Rabs_Ropp.
        replace (4 * PI) with (2 * PI + 2 * PI) by ring.
        apply Rplus_lt_compat; [exact (proj2 Habs) | exact (proj2 Habs_e)]. }
      destruct (Rabs_def2 _ _ H0) as [Hhi Hlo]. split; assumption.
    - destruct Hend as [Hc Hs].
      replace (circ_sweep c - circ_sweep e)
        with ((circ_theta0 c + circ_sweep c) - (circ_theta0 e + circ_sweep e)).
      2: { rewrite Hth_eq. ring. }
      rewrite cos_minus, Hc, Hs.
      pose proof (sin2_cos2 (circ_theta0 e + circ_sweep e)) as Py.
      unfold Rsqr in Py. nra. }
  assert (Hsweep : circ_sweep c = circ_sweep e).
  { destruct Hdiff as [E0|[Ep|Em]].
    - lra.
    - exfalso.
      assert (Hcomp : circ_sweep e * circ_sweep c < 0 /\
                      Rabs (circ_sweep e) + Rabs (circ_sweep c) = 2 * PI).
      { assert (Eplus : circ_sweep c = circ_sweep e + 2 * PI) by lra.
        apply sweep_complement.
        - exact (proj2 Habs_e).
        - exact (proj2 Habs).
        - left. exact Eplus. }
      destruct Hon as [_ [_ [te [Hte HteM]]]].
      set (ae := te * circ_sweep e).
      set (ac := tc * circ_sweep c).
      assert (Hopp : ae * ac < 0).
      { unfold ae, ac.
        replace (te * circ_sweep e * (tc * circ_sweep c))
          with ((te * tc) * (circ_sweep e * circ_sweep c)) by ring.
        destruct Hcomp as [Hp _].
        assert (Hk : 0 < te * tc) by (apply Rmult_lt_0_compat; lra).
        assert (Hprod : (te * tc) * (circ_sweep e * circ_sweep c)
                        < (te * tc) * 0).
        { apply Rmult_lt_compat_l; assumption. }
        rewrite Rmult_0_r in Hprod. exact Hprod. }
      assert (Hae : Rabs ae < Rabs (circ_sweep e)).
      { unfold ae. rewrite Rabs_mult.
        rewrite (Rabs_right te) by lra.
        assert (0 < Rabs (circ_sweep e)) by (apply Habs_e).
        rewrite <- (Rmult_1_l (Rabs (circ_sweep e))) at 2.
        apply Rmult_lt_compat_r; lra. }
      assert (Hac : Rabs ac < Rabs (circ_sweep c)).
      { unfold ac. rewrite Rabs_mult.
        rewrite (Rabs_right tc) by lra.
        assert (0 < Rabs (circ_sweep c)) by (apply Habs).
        rewrite <- (Rmult_1_l (Rabs (circ_sweep c))) at 2.
        apply Rmult_lt_compat_r; lra. }
      assert (Hsum : Rabs (ae - ac) < 2 * PI).
      { rewrite (opp_abs_sum ae ac Hopp).
        destruct Hcomp as [_ Hs]. lra. }
      assert (Heqang : cos (ae - ac) = 1).
      { apply (f_equal px) in Hm as Hmx.
        apply (f_equal py) in Hm as Hmy.
        apply (f_equal px) in HteM as Hex.
        apply (f_equal py) in HteM as Hey.
        unfold circ_eval in Hmx, Hmy, Hex, Hey. cbn [px py] in *.
        rewrite Hoe, <- Ho, <- Hr_eq in Hex, Hey.
        rewrite Hth_eq in Hmx, Hmy.
        fold ae in Hex, Hey. fold ac in Hmx, Hmy.
        assert (cos (circ_theta0 e + ae) = cos (circ_theta0 e + ac)) by nra.
        assert (sin (circ_theta0 e + ae) = sin (circ_theta0 e + ac)) by nra.
        replace (ae - ac)
          with ((circ_theta0 e + ae) - (circ_theta0 e + ac)) by ring.
        rewrite cos_minus.
        pose proof (sin2_cos2 (circ_theta0 e + ac)) as Py.
        unfold Rsqr in Py. nra. }
      assert (Eac : ae = ac).
      { assert (E0 : ae - ac = 0).
        { apply cos_eq_1_two_pi.
          - apply Rabs_def2 in Hsum. lra.
          - exact Heqang. }
        lra. }
      unfold ae, ac in Eac. nra.
    - exfalso.
      assert (Hcomp : circ_sweep e * circ_sweep c < 0 /\
                      Rabs (circ_sweep e) + Rabs (circ_sweep c) = 2 * PI).
      { assert (Eminus : circ_sweep c = circ_sweep e - 2 * PI) by lra.
        apply sweep_complement.
        - exact (proj2 Habs_e).
        - exact (proj2 Habs).
        - right. exact Eminus. }
      destruct Hon as [_ [_ [te [Hte HteM]]]].
      set (ae := te * circ_sweep e).
      set (ac := tc * circ_sweep c).
      assert (Hopp : ae * ac < 0).
      { unfold ae, ac.
        replace (te * circ_sweep e * (tc * circ_sweep c))
          with ((te * tc) * (circ_sweep e * circ_sweep c)) by ring.
        destruct Hcomp as [Hp _].
        assert (Hk : 0 < te * tc) by (apply Rmult_lt_0_compat; lra).
        assert (Hprod : (te * tc) * (circ_sweep e * circ_sweep c)
                        < (te * tc) * 0).
        { apply Rmult_lt_compat_l; assumption. }
        rewrite Rmult_0_r in Hprod. exact Hprod. }
      assert (Hae : Rabs ae < Rabs (circ_sweep e)).
      { unfold ae. rewrite Rabs_mult. rewrite (Rabs_right te) by lra.
        rewrite <- (Rmult_1_l (Rabs (circ_sweep e))) at 2.
        apply Rmult_lt_compat_r.
        - apply Rabs_pos_lt. intros Z.
          assert (Rabs (circ_sweep e) = 0) by (rewrite Z; apply Rabs_R0).
          destruct Habs_e as [Hp _]. lra.
        - lra. }
      assert (Hac : Rabs ac < Rabs (circ_sweep c)).
      { unfold ac. rewrite Rabs_mult. rewrite (Rabs_right tc) by lra.
        rewrite <- (Rmult_1_l (Rabs (circ_sweep c))) at 2.
        apply Rmult_lt_compat_r.
        - apply Rabs_pos_lt. intros Z.
          destruct Habs as [Hp _].
          assert (Rabs (circ_sweep c) = 0) by (rewrite Z; apply Rabs_R0).
          lra.
        - lra. }
      assert (Hsum : Rabs (ae - ac) < 2 * PI).
      { rewrite (opp_abs_sum ae ac Hopp). destruct Hcomp as [_ Hs]. lra. }
      assert (Heqang : cos (ae - ac) = 1).
      { apply (f_equal px) in Hm as Hmx.
        apply (f_equal py) in Hm as Hmy.
        apply (f_equal px) in HteM as Hex.
        apply (f_equal py) in HteM as Hey.
        unfold circ_eval in Hmx, Hmy, Hex, Hey. cbn [px py] in *.
        rewrite Hoe, <- Ho, <- Hr_eq in Hex, Hey.
        rewrite Hth_eq in Hmx, Hmy.
        fold ae in Hex, Hey. fold ac in Hmx, Hmy.
        assert (cos (circ_theta0 e + ae) = cos (circ_theta0 e + ac)) by nra.
        assert (sin (circ_theta0 e + ae) = sin (circ_theta0 e + ac)) by nra.
        replace (ae - ac)
          with ((circ_theta0 e + ae) - (circ_theta0 e + ac)) by ring.
        rewrite cos_minus.
        pose proof (sin2_cos2 (circ_theta0 e + ac)) as Py.
        unfold Rsqr in Py. nra. }
      assert (ae = ac).
      { assert (E0 : ae - ac = 0).
        { apply cos_eq_1_two_pi.
          - apply Rabs_def2 in Hsum. lra.
          - exact Heqang. }
        lra. }
      unfold ae, ac in H. nra. }
  repeat split.
  - rewrite Ho, Hoe. reflexivity.
  - exact Hr_eq.
  - exact Hth_eq.
  - exact Hsweep.
Qed.

(* -------------------------------------------------------------------------- *)
(* Decidable carry. pt_eqb / span_ok use Req_EM_T, so this is classical       *)
(* decidability, not an executable real computation. The executable chart     *)
(* window is the SQLMM_WKT differential (tests/SqlMmWktAngleHunt). Rejects    *)
(* unless the chart witness and the endpoints land on the carried egg.        *)
(* Does not test angle equality with Req_EM_T.                                *)
(* -------------------------------------------------------------------------- *)

Definition pt_eqb (p q : Point) : bool :=
  if Req_EM_T (px p) (px q) then
    if Req_EM_T (py p) (py q) then true else false
  else false.

Lemma pt_eqb_true : forall p q, pt_eqb p q = true -> p = q.
Proof.
  intros p q. unfold pt_eqb.
  destruct (Req_EM_T (px p) (px q)) as [Hx|Hx]; [| discriminate].
  destruct (Req_EM_T (py p) (py q)) as [Hy|Hy]; [| discriminate].
  intros _. apply Point_eq_of_coords; assumption.
Qed.

Definition span_ok (th dth t : R) : bool :=
  if Rle_dec th (- PI) then false
  else if Rlt_dec PI th then false
  else if Rle_dec (Rabs dth) 0 then false
  else if Rle_dec (2 * PI) (Rabs dth) then false
  else if Rle_dec t 0 then false
  else if Rle_dec 1 t then false
  else true.

Lemma span_ok_bounds : forall th dth t,
  span_ok th dth t = true ->
  - PI < th <= PI /\ 0 < Rabs dth < 2 * PI /\ 0 < t < 1.
Proof.
  intros th dth t H.
  unfold span_ok in H.
  destruct (Rle_dec th (- PI)) as [H1|H1]; [discriminate|].
  destruct (Rlt_dec PI th) as [H2|H2]; [discriminate|].
  destruct (Rle_dec (Rabs dth) 0) as [H3|H3]; [discriminate|].
  destruct (Rle_dec (2 * PI) (Rabs dth)) as [H4|H4]; [discriminate|].
  destruct (Rle_dec t 0) as [H5|H5]; [discriminate|].
  destruct (Rle_dec 1 t) as [H6|H6]; [discriminate|].
  apply Rnot_le_lt in H1. apply Rnot_lt_le in H2.
  apply Rnot_le_lt in H3. apply Rnot_le_lt in H4.
  apply Rnot_le_lt in H5. apply Rnot_le_lt in H6.
  repeat split; assumption.
Qed.

Definition try_carried (a m b : Point) (th dth : R) : AngleResult CircularEgg :=
  match try_triple a m b with
  | inr f => inr f
  | inl _ =>
      let o := circumcenter_of a m b in
      let r := dist o a in
      let c := mkCircularEgg o r th dth in
      let q := pole_point o m (midpoint a b) in
      let za := zeta_of_pt o q a in
      let zb := zeta_of_pt o q b in
      let zm := zeta_of_pt o q m in
      let den := atan3 zb - atan3 za in
      let t := (atan3 zm - atan3 za) / den in
      if Req_EM_T den 0 then inr AF_SpanMismatch
      else if span_ok th dth t then
        if pt_eqb (circ_eval c 0) a then
          if pt_eqb (circ_eval c 1) b then
            if pt_eqb (circ_eval c t) m then inl c
            else inr AF_SpanMismatch
          else inr AF_SpanMismatch
        else inr AF_SpanMismatch
      else inr AF_SpanMismatch
  end.

Lemma try_triple_inl : forall a b c e,
  try_triple a b c = inl e ->
  dist_sq a b <> 0 /\
  dist_sq b c <> 0 /\
  dist_sq a c <> 0 /\
  circ_denom a b c <> 0 /\
  dist (circumcenter_of a b c) a <> 0 /\
  e = egg_of_points a b c.
Proof.
  intros a b c e H.
  unfold try_triple in H. cbn in H.
  destruct (Req_EM_T (dist_sq a b) 0) as [E|Hab]; [discriminate|].
  destruct (Req_EM_T (dist_sq b c) 0) as [E|Hbc]; [discriminate|].
  destruct (Req_EM_T (dist_sq a c) 0) as [E|Hac]; [discriminate|].
  destruct (Req_EM_T (circ_denom a b c) 0) as [E|Hd]; [discriminate|].
  destruct (Req_EM_T (dist (circumcenter_of a b c) a) 0) as [E|Hr];
    [discriminate|].
  injection H as H.
  repeat split.
  - exact Hab.
  - exact Hbc.
  - exact Hac.
  - exact Hd.
  - exact Hr.
  - symmetry. exact H.
Qed.

Lemma try_carried_check : forall a m b th dth c,
  try_carried a m b th dth = inl c ->
  carry_check c a m b /\
  c = mkCircularEgg (circumcenter_of a m b) (dist (circumcenter_of a m b) a) th dth.
Proof.
  intros a m b th dth c H.
  unfold try_carried in H.
  destruct (try_triple a m b) as [e|f] eqn:Ht; [| discriminate].
  destruct (try_triple_inl a m b e Ht)
    as [Ham [Hmb [Hab [Hd [Hr He]]]]].
  set (o := circumcenter_of a m b) in *.
  set (r := dist o a) in *.
  set (egg := mkCircularEgg o r th dth) in *.
  set (q := pole_point o m (midpoint a b)) in *.
  set (za := zeta_of_pt o q a) in *.
  set (zb := zeta_of_pt o q b) in *.
  set (zm := zeta_of_pt o q m) in *.
  set (den := atan3 zb - atan3 za) in *.
  set (t := (atan3 zm - atan3 za) / den) in *.
  destruct (Req_EM_T den 0); [discriminate|].
  destruct (span_ok th dth t) eqn:Hok; [| discriminate].
  destruct (pt_eqb (circ_eval egg 0) a) eqn:H0; [| discriminate].
  destruct (pt_eqb (circ_eval egg 1) b) eqn:H1; [| discriminate].
  destruct (pt_eqb (circ_eval egg t) m) eqn:Hm; [| discriminate].
  injection H as Hc.
  apply pt_eqb_true in H0. apply pt_eqb_true in H1. apply pt_eqb_true in Hm.
  destruct (span_ok_bounds th dth t Hok) as [Hth [Habs Htopen]].
  assert (Hrpos : 0 < r).
  { unfold r. apply dist_pos_of_neq. exact Hr. }
  split.
  - unfold carry_check. rewrite <- Hc. unfold egg. cbn.
    split; [exact Hrpos|].
    split; [exact H0|].
    split; [exact H1|].
    split; [exists t; split; [exact Htopen| exact Hm]|].
    split; [exact Habs|].
    split; [exact Hth|].
    split; [exact Ham|].
    split; [exact Hmb|].
    exact Hab.
  - rewrite <- Hc. unfold egg. reflexivity.
Qed.

Lemma try_carried_agrees : forall a m b th dth c,
  try_carried a m b th dth = inl c ->
  c = egg_of_points a m b.
Proof.
  intros a m b th dth c H.
  destruct (try_carried_check a m b th dth c H) as [Hc Heq].
  destruct (intake_angles_agree c a m b Hc) as [Ho [Hr [Hth Hs]]].
  apply circ_egg_eq.
  - rewrite Heq. cbn.
    destruct (egg_fields a m b) as [Ho' _]. symmetry. exact Ho'.
  - rewrite Heq. cbn.
    destruct (egg_fields a m b) as [_ [Hr' _]]. symmetry. exact Hr'.
  - exact Hth.
  - exact Hs.
Qed.

(* -------------------------------------------------------------------------- *)
(* Fixtures. CCW minor arc and CW major arc on the same circumcircle.         *)
(* Endpoint cross is ArcSweepCcw.radius_cross (strict arm of sweep_ccw).      *)
(* -------------------------------------------------------------------------- *)

Definition cw_b : Point := mkPoint (-1) 1.
Definition cw_egg : CircularEgg := egg_of_points ang_a cw_b ang_c.

Lemma cw_dab_nz : dist_sq ang_a cw_b <> 0.
Proof. unfold dist_sq, ang_a, cw_b. cbn. lra. Qed.

Lemma cw_dbc_nz : dist_sq cw_b ang_c <> 0.
Proof. unfold dist_sq, cw_b, ang_c. cbn. lra. Qed.

Lemma cw_denom : circ_denom ang_a cw_b ang_c = -8.
Proof. unfold circ_denom, ang_a, cw_b, ang_c. cbn. ring. Qed.

Lemma cw_denom_nz : circ_denom ang_a cw_b ang_c <> 0.
Proof. rewrite cw_denom. lra. Qed.

Lemma cw_center : circumcenter_of ang_a cw_b ang_c = mkPoint 1 2.
Proof.
  unfold circumcenter_of. rewrite cw_denom.
  unfold ang_a, cw_b, ang_c. cbn.
  apply (f_equal2 mkPoint); field; lra.
Qed.

Lemma cw_r_nz : dist (circumcenter_of ang_a cw_b ang_c) ang_a <> 0.
Proof.
  rewrite cw_center. unfold dist, dist_sq, ang_a. cbn.
  apply sqrt_pos_neq_0. lra.
Qed.

Lemma cw_orient : orient_pts ang_a cw_b ang_c < 0.
Proof. unfold orient_pts, orient3, crs, ang_a, cw_b, ang_c. cbn. lra. Qed.

Lemma ang_orient : orient_pts ang_a ang_b ang_c > 0.
Proof. unfold orient_pts, orient3, crs, ang_a, ang_b, ang_c. cbn. lra. Qed.

Lemma ang_sweep_bounds : 0 < circ_sweep ang_egg < 2 * PI.
Proof.
  pose proof (egg_sweep_open ang_a ang_b ang_c ang_dab_nz ang_dbc_nz ang_dac_nz
                ltac:(rewrite ang_denom; lra) ang_r_nz) as Habs.
  pose proof (egg_sweep_sign ang_a ang_b ang_c ang_dab_nz ang_dbc_nz ang_dac_nz
                ltac:(rewrite ang_denom; lra) ang_r_nz) as Hs.
  pose proof ang_orient as Ho.
  unfold ang_egg in Habs, Hs.
  assert (Hp : 0 < circ_sweep (egg_of_points ang_a ang_b ang_c)) by nra.
  destruct Habs as [_ Hlt].
  split; [exact Hp|].
  rewrite (Rabs_right (circ_sweep (egg_of_points ang_a ang_b ang_c))) in Hlt by lra.
  exact Hlt.
Qed.

Lemma cw_sweep_neg : circ_sweep cw_egg < 0.
Proof.
  pose proof (egg_sweep_sign ang_a cw_b ang_c cw_dab_nz cw_dbc_nz ang_dac_nz
                cw_denom_nz cw_r_nz) as Hs.
  pose proof cw_orient as Ho.
  unfold cw_egg.
  apply Rmult_lt_reg_r with (r := - orient_pts ang_a cw_b ang_c).
  - lra.
  - replace (circ_sweep (egg_of_points ang_a cw_b ang_c) *
             - orient_pts ang_a cw_b ang_c)
      with (- (circ_sweep (egg_of_points ang_a cw_b ang_c) *
               orient_pts ang_a cw_b ang_c)) by ring.
    rewrite Rmult_0_l. lra.
Qed.

Lemma cw_sweep_abs : Rabs (circ_sweep cw_egg) < 2 * PI.
Proof.
  pose proof (egg_sweep_open ang_a cw_b ang_c cw_dab_nz cw_dbc_nz ang_dac_nz
                cw_denom_nz cw_r_nz) as H.
  unfold cw_egg in H. apply (proj2 H).
Qed.

(* Strict left turn of the endpoint radii: the left disjunct of
   ArcSweepCcw.sweep_ccw. Holds for both fixtures; the CW egg still
   has Δθ < 0 (major arc). *)
Lemma ang_endpoint_cross_pos :
  0 < (px ang_a - px (circ_o ang_egg)) * (py ang_c - py (circ_o ang_egg))
    - (py ang_a - py (circ_o ang_egg)) * (px ang_c - px (circ_o ang_egg)).
Proof.
  rewrite ang_egg_center.
  unfold ang_a, ang_c. cbn. lra.
Qed.

Lemma cw_endpoint_cross_pos :
  0 < (px ang_a - px (circ_o cw_egg)) * (py ang_c - py (circ_o cw_egg))
    - (py ang_a - py (circ_o cw_egg)) * (px ang_c - px (circ_o cw_egg)).
Proof.
  unfold cw_egg, egg_of_points. rewrite cw_center.
  unfold ang_a, ang_c. cbn. lra.
Qed.

(* ArcSweepCcw.sweep_ccw reads only the endpoint radii (left disjunct:
   positive radius_cross). Both fixtures have that cross positive, so
   sweep_ccw accepts the CW major arc and the CCW minor arc alike.
   No host consumer of sweep_ccw infers circ_sweep from it (the name
   is used only inside ArcSweepCcw.v). Orientation of an intake egg
   is circ_sweep. *)
Theorem sweep_ccw_not_orientation :
  0 < (px ang_a - px (circ_o ang_egg)) * (py ang_c - py (circ_o ang_egg))
    - (py ang_a - py (circ_o ang_egg)) * (px ang_c - px (circ_o ang_egg)) /\
  0 < (px ang_a - px (circ_o cw_egg)) * (py ang_c - py (circ_o cw_egg))
    - (py ang_a - py (circ_o cw_egg)) * (px ang_c - px (circ_o cw_egg)) /\
  circ_sweep cw_egg < 0 /\
  0 < circ_sweep ang_egg.
Proof.
  split; [exact ang_endpoint_cross_pos|].
  split; [exact cw_endpoint_cross_pos|].
  split; [exact cw_sweep_neg|].
  exact (proj1 ang_sweep_bounds).
Qed.

(* WITNESS {"claimId":"0007-intake-angles","topic":"core","lemma":"intake_angles_ctor_shape","title":"Supersedes the old IntakeAngles.v intake_angles_ctor_shape conjuncts theta0=0 and sweep=+2pi: CCW fixture is the chart egg, theta0 principal, 0<sweep<2pi, endpoint cross positive","file":"theories/IntakeAngles.v","witness":"0007-intake-angles","board":"ADR-0007"} *)
Theorem intake_angles_ctor_shape :
  circ_o ang_egg = mkPoint 1 2 /\
  circ_r ang_egg = sqrt 5 /\
  - PI < circ_theta0 ang_egg <= PI /\
  0 < circ_sweep ang_egg < 2 * PI /\
  circ_eval ang_egg 0 = ang_a /\
  circ_eval ang_egg 1 = ang_c /\
  (exists t, 0 < t < 1 /\ circ_eval ang_egg t = ang_b) /\
  0 < (px ang_a - px (circ_o ang_egg)) * (py ang_c - py (circ_o ang_egg))
    - (py ang_a - py (circ_o ang_egg)) * (px ang_c - px (circ_o ang_egg)).
Proof.
  split; [exact ang_egg_center|].
  split; [exact ang_egg_radius|].
  split.
  - unfold ang_egg. apply egg_theta_range.
    + exact ang_dab_nz.
    + exact ang_dbc_nz.
    + exact ang_dac_nz.
    + rewrite ang_denom. lra.
    + exact ang_r_nz.
  - split; [exact ang_sweep_bounds|].
    destruct (egg_on_controls ang_a ang_b ang_c ang_dab_nz ang_dbc_nz ang_dac_nz
                ltac:(rewrite ang_denom; lra) ang_r_nz) as [H0 [H1 Hm]].
    unfold ang_egg in H0, H1, Hm.
    split; [exact H0|].
    split; [exact H1|].
    split; [exact Hm|].
    exact ang_endpoint_cross_pos.
Qed.

Lemma intake_angles_pm2pi_superseded :
  ~ (circ_theta0 ang_egg = 0 /\ circ_sweep ang_egg = 2 * PI).
Proof.
  intros [_ H].
  destruct ang_sweep_bounds as [_ Hlt].
  lra.
Qed.

Lemma ang_egg_not_full_span : Rabs (circ_sweep ang_egg) <> 2 * PI.
Proof.
  destruct ang_sweep_bounds as [Hp Hlt].
  rewrite (Rabs_right (circ_sweep ang_egg)) by lra.
  lra.
Qed.


(* Axiom audit. Headlines are the classical-reals trio. *)
Print Assumptions circum_radius_nz.
Print Assumptions egg_of_points_certified.
Print Assumptions circ_eval_dist_sq.
Print Assumptions circ_egg_eq.
Print Assumptions no_equidistant_collinear.
Print Assumptions cos_one_span4.
Print Assumptions sweep_complement.
Print Assumptions opp_abs_sum.
Print Assumptions theta_is_atan2.
Print Assumptions intake_angles_agree.
Print Assumptions pt_eqb_true.
Print Assumptions span_ok_bounds.
Print Assumptions try_triple_inl.
Print Assumptions try_carried_check.
Print Assumptions try_carried_agrees.
Print Assumptions cw_dab_nz.
Print Assumptions cw_dbc_nz.
Print Assumptions cw_denom.
Print Assumptions cw_denom_nz.
Print Assumptions cw_center.
Print Assumptions cw_r_nz.
Print Assumptions cw_orient.
Print Assumptions ang_orient.
Print Assumptions ang_sweep_bounds.
Print Assumptions cw_sweep_neg.
Print Assumptions cw_sweep_abs.
Print Assumptions ang_endpoint_cross_pos.
Print Assumptions cw_endpoint_cross_pos.
Print Assumptions sweep_ccw_not_orientation.
Print Assumptions intake_angles_ctor_shape.
Print Assumptions intake_angles_pm2pi_superseded.
Print Assumptions ang_egg_not_full_span.
