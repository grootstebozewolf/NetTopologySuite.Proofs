(* ============================================================================
   NetTopologySuite.Proofs.IntakeAnglesChart
   ----------------------------------------------------------------------------
   Chart arithmetic for egg_of_points: pole frame, atan3 sweep,
   endpoint and mid evaluation. Letter theorems stay in IntakeAngles.v.
   Not a claimId remint.

   3-axiom host. No Admitted / Axiom / Parameter.
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra Field List.
From NTS.Proofs Require Import Distance Segment SheetHenCook CircleChart Atan2 AtanIvt
  CurveGeometry ArcChordApprox.
From NTS.Proofs Require Export IntakeAnglesCore.
Import ListNotations.
Local Open Scope R_scope.
Local Open Scope list_scope.

Lemma chart_rotate : forall ux uy z,
  zeta_ptx ux uy z =
    ux * cos (2 * atan3 z) - uy * sin (2 * atan3 z) /\
  zeta_pty ux uy z =
    uy * cos (2 * atan3 z) + ux * sin (2 * atan3 z).
Proof.
  intros ux uy z.
  rewrite cos_2_atan3, sin_2_atan3.
  unfold zeta_ptx, zeta_pty.
  split; field; nra.
Qed.

Lemma raw_in_open : forall ux uy za,
  ~ (ux = 0 /\ uy = 0) ->
  - (2 * PI) < atan2 uy ux + 2 * atan3 za < 2 * PI.
Proof.
  intros ux uy za Hu.
  pose proof (atan2_range ux uy Hu) as Ha.
  destruct (atan3_spec za) as [Hz _].
  pose proof PI_RGT_0. lra.
Qed.

Lemma egg_fields : forall a m b,
  circ_o (egg_of_points a m b) = circumcenter_of a m b /\
  circ_r (egg_of_points a m b) = dist (circumcenter_of a m b) a /\
  circ_theta0 (egg_of_points a m b) =
    principal (atan2 (py (circumcenter_of a m b) -
                      py (pole_point (circumcenter_of a m b) m
                            (midpoint a b)))
                     (px (circumcenter_of a m b) -
                      px (pole_point (circumcenter_of a m b) m
                            (midpoint a b)))
               + 2 * atan3 (zeta_of_pt (circumcenter_of a m b)
                              (pole_point (circumcenter_of a m b) m
                                 (midpoint a b)) a)) /\
  circ_sweep (egg_of_points a m b) =
    2 * (atan3 (zeta_of_pt (circumcenter_of a m b)
                  (pole_point (circumcenter_of a m b) m (midpoint a b)) b)
         - atan3 (zeta_of_pt (circumcenter_of a m b)
                    (pole_point (circumcenter_of a m b) m (midpoint a b)) a)).
Proof.
  intros a m b. unfold egg_of_points. repeat split; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Pole frame of a non-degenerate triple.                                     *)
(* -------------------------------------------------------------------------- *)

Lemma mid_ne_of_denom : forall a m b,
  circ_denom a m b <> 0 ->
  midpoint a b <> m.
Proof.
  intros a m b Hd E.
  apply Hd. rewrite circ_denom_orient.
  assert (Ex : px m = (px a + px b) / 2).
  { rewrite <- E. unfold midpoint. cbn. reflexivity. }
  assert (Ey : py m = (py a + py b) / 2).
  { rewrite <- E. unfold midpoint. cbn. reflexivity. }
  assert (orient_pts a m b = 0).
  { unfold orient_pts, orient3, crs. cbn. rewrite Ex, Ey. field. }
  lra.
Qed.

Lemma orient_abm_ne : forall a m b,
  circ_denom a m b <> 0 ->
  orient_pts a b m <> 0.
Proof.
  intros a m b Hd.
  rewrite orient_swap_end_mid.
  rewrite circ_denom_orient in Hd.
  lra.
Qed.

Lemma orient_rev_amb : forall a m b,
  orient_pts b m a = - orient_pts a m b.
Proof.
  intros a m b. unfold orient_pts, orient3, crs. ring.
Qed.

Lemma egg_circle_pack : forall a m b,
  dist_sq a m <> 0 ->
  dist_sq m b <> 0 ->
  dist_sq a b <> 0 ->
  circ_denom a m b <> 0 ->
  dist (circumcenter_of a m b) a <> 0 ->
  let o := circumcenter_of a m b in
  let q := pole_point o m (midpoint a b) in
  dist_sq o q = dist_sq o a /\
  dist_sq o m = dist_sq o a /\
  dist_sq o b = dist_sq o a /\
  q <> a /\ q <> b /\ q <> m /\
  ~ (px o - px q = 0 /\ py o - py q = 0).
Proof.
  intros a m b Ham Hmb Hab Hd Hr o q.
  assert (Hmid : midpoint a b <> m) by (apply mid_ne_of_denom; exact Hd).
  assert (Hpair : (px (midpoint a b), py (midpoint a b)) <> (px m, py m)).
  { intros E. injection E as Ex Ey.
    apply Hmid. apply Point_eq_of_coords; assumption. }
  pose proof (pole_point_radius o m (midpoint a b) Hpair) as Hqrad.
  destruct (circum_equidistant a m b Hd) as [Hm Hb].
  fold o in Hm, Hb, Hqrad.
  assert (Hqa_rad : dist_sq o q = dist_sq o a).
  { unfold q. rewrite Hqrad. exact Hm. }
  assert (Habp : a <> b) by (apply dist_sq_neq_ne; exact Hab).
  assert (Horient : orient_pts a b m <> 0) by (apply orient_abm_ne; exact Hd).
  assert (Hsep : q <> a /\ q <> b /\ q <> m).
  { pose proof (pole_ne_vertices o a b m
      (eq_sym Hm) (eq_trans Hb (eq_sym Hm)) Habp Horient) as H.
    unfold q. exact H. }
  assert (Hsq : dist_sq o a <> 0).
  { unfold o. intros Z. apply Hr. unfold dist. rewrite Z. apply sqrt_0. }
  split; [exact Hqa_rad|].
  split; [exact Hm|].
  split; [exact Hb|].
  split; [exact (proj1 Hsep)|].
  split; [exact (proj1 (proj2 Hsep))|].
  split; [exact (proj2 (proj2 Hsep))|].
  intros [Hx Hy].
  apply Hsq.
  rewrite <- Hqa_rad.
  unfold dist_sq, q in *.
  rewrite Hx, Hy. ring.
Qed.

Lemma on_chart_pt : forall o q p,
  dist_sq o p = dist_sq o q ->
  p <> q ->
  px p = px o + zeta_ptx (px o - px q) (py o - py q) (zeta_of_pt o q p) /\
  py p = py o + zeta_pty (px o - px q) (py o - py q) (zeta_of_pt o q p).
Proof.
  intros o q p Hr Hne.
  destruct (chart_frame o q p Hr Hne) as [_ [Hx Hy]].
  split; assumption.
Qed.

Lemma atan_ends_sep : forall a m b,
  dist_sq a m <> 0 ->
  dist_sq m b <> 0 ->
  dist_sq a b <> 0 ->
  circ_denom a m b <> 0 ->
  dist (circumcenter_of a m b) a <> 0 ->
  let o := circumcenter_of a m b in
  let q := pole_point o m (midpoint a b) in
  atan3 (zeta_of_pt o q b) <> atan3 (zeta_of_pt o q a).
Proof.
  intros a m b Ham Hmb Hab Hd Hr o q E.
  destruct (egg_circle_pack a m b Ham Hmb Hab Hd Hr)
    as [Hqa [Hm [Hb [Hqa_ne [Hqb [Hqm _]]]]]].
  fold o q in Hqa, Hm, Hb, Hqa_ne, Hqb, Hqm.
  apply atan3_inj in E.
  assert (a = b).
  { apply Point_eq_of_coords.
    - destruct (on_chart_pt o q a (eq_sym Hqa) (not_eq_sym Hqa_ne)) as [Hax _].
      destruct (on_chart_pt o q b (eq_trans Hb (eq_sym Hqa)) (not_eq_sym Hqb)) as [Hbx _].
      rewrite Hax, Hbx, E. reflexivity.
    - destruct (on_chart_pt o q a (eq_sym Hqa) (not_eq_sym Hqa_ne)) as [_ Hay].
      destruct (on_chart_pt o q b (eq_trans Hb (eq_sym Hqa)) (not_eq_sym Hqb)) as [_ Hby].
      rewrite Hay, Hby, E. reflexivity. }
  apply (dist_sq_neq_ne a b Hab). exact H.
Qed.

Lemma zeta_mid_strict : forall a m b,
  dist_sq a m <> 0 ->
  dist_sq m b <> 0 ->
  dist_sq a b <> 0 ->
  circ_denom a m b <> 0 ->
  dist (circumcenter_of a m b) a <> 0 ->
  let o := circumcenter_of a m b in
  let q := pole_point o m (midpoint a b) in
  let za := zeta_of_pt o q a in
  let zb := zeta_of_pt o q b in
  let zm := zeta_of_pt o q m in
  (zm - za) * (zm - zb) < 0.
Proof.
  intros a m b Ham Hmb Hab Hd Hr o q za zb zm.
  destruct (egg_circle_pack a m b Ham Hmb Hab Hd Hr)
    as [Hqa [Hm [Hb [Hqa_ne [Hqb [Hqm _]]]]]].
  fold o q in Hqa, Hm, Hb, Hqa_ne, Hqb, Hqm.
  assert (Habp : a <> b) by (apply dist_sq_neq_ne; exact Hab).
  assert (Hamp : a <> m) by (apply dist_sq_neq_ne; exact Ham).
  assert (Hbmp : b <> m) by (apply dist_sq_neq_ne; rewrite dist_sq_sym; exact Hmb).
  assert (Horient : orient_pts a b m <> 0) by (apply orient_abm_ne; exact Hd).
  assert (Hmem : arc_member_AB_M a b m m).
  { left. pose proof (Rsqr_pos_lt _ Horient) as Hs.
    unfold Rsqr in Hs. exact Hs. }
  assert (Hint : in_zeta_interval za zb zm).
  { apply (proj1 (arc_member_iff_zeta_interval o a b m m
      (eq_sym Hm) (eq_trans Hb (eq_sym Hm)) eq_refl
      Habp Horient (not_eq_sym Hqm))).
    fold q za zb zm. exact Hmem. }
  unfold in_zeta_interval in Hint.
  assert (Hza : zm <> za).
  { intros E.
    assert (m = a).
    { apply Point_eq_of_coords.
      - destruct (on_chart_pt o q m (eq_trans Hm (eq_sym Hqa)) (not_eq_sym Hqm)) as [Hmx _].
        destruct (on_chart_pt o q a (eq_sym Hqa) (not_eq_sym Hqa_ne)) as [Hax _].
        rewrite Hmx, Hax. fold zm za. rewrite E. reflexivity.
      - destruct (on_chart_pt o q m (eq_trans Hm (eq_sym Hqa)) (not_eq_sym Hqm)) as [_ Hmy].
        destruct (on_chart_pt o q a (eq_sym Hqa) (not_eq_sym Hqa_ne)) as [_ Hay].
        rewrite Hmy, Hay. fold zm za. rewrite E. reflexivity. }
    apply Hamp. symmetry. exact H. }
  assert (Hzb : zm <> zb).
  { intros E.
    assert (m = b).
    { apply Point_eq_of_coords.
      - destruct (on_chart_pt o q m (eq_trans Hm (eq_sym Hqa)) (not_eq_sym Hqm)) as [Hmx _].
        destruct (on_chart_pt o q b (eq_trans Hb (eq_sym Hqa)) (not_eq_sym Hqb)) as [Hbx _].
        rewrite Hmx, Hbx. fold zm zb. rewrite E. reflexivity.
      - destruct (on_chart_pt o q m (eq_trans Hm (eq_sym Hqa)) (not_eq_sym Hqm)) as [_ Hmy].
        destruct (on_chart_pt o q b (eq_trans Hb (eq_sym Hqa)) (not_eq_sym Hqb)) as [_ Hby].
        rewrite Hmy, Hby. fold zm zb. rewrite E. reflexivity. }
    apply Hbmp. symmetry. exact H. }
  assert ((zm - za) * (zm - zb) <> 0).
  { intros Z. apply Rmult_integral in Z. destruct Z as [Z|Z]; lra. }
  lra.
Qed.

Lemma ratio_open : forall x y,
  0 < y -> 0 < x < y -> 0 < x / y < 1.
Proof.
  intros x y Hy [Hx Hxy].
  split.
  - apply Rdiv_lt_0_compat; assumption.
  - apply Rmult_lt_reg_r with (r := y); [exact Hy|].
    unfold Rdiv. replace ((x * / y) * y) with x by (field; lra).
    rewrite Rmult_1_l. exact Hxy.
Qed.

Lemma ratio_same_sign : forall x y,
  x <> 0 -> y <> 0 -> x * y > 0 ->
  (0 < x /\ 0 < y) \/ (x < 0 /\ y < 0).
Proof.
  intros x y Hx Hy Hp.
  destruct (Rle_dec 0 x) as [Hx0|Hx0].
  - left. assert (0 < x) by lra. assert (0 < y) by nra. split; assumption.
  - right. assert (x < 0) by lra. assert (y < 0) by nra. split; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* circ_eval at the chart parameter is the chart point.                       *)
(* -------------------------------------------------------------------------- *)

Lemma egg_eval_chart : forall a m b z,
  dist_sq a m <> 0 ->
  dist_sq m b <> 0 ->
  dist_sq a b <> 0 ->
  circ_denom a m b <> 0 ->
  dist (circumcenter_of a m b) a <> 0 ->
  let o := circumcenter_of a m b in
  let q := pole_point o m (midpoint a b) in
  let ux := px o - px q in
  let uy := py o - py q in
  let za := zeta_of_pt o q a in
  let zb := zeta_of_pt o q b in
  circ_eval (egg_of_points a m b)
    ((atan3 z - atan3 za) / (atan3 zb - atan3 za))
  = mkPoint (px o + zeta_ptx ux uy z) (py o + zeta_pty ux uy z).
Proof.
  intros a m b z Ham Hmb Hab Hd Hr o q ux uy za zb.
  destruct (egg_circle_pack a m b Ham Hmb Hab Hd Hr)
    as [Hqa [Hm [_ [_ [_ [_ Huv0]]]]]].
  fold o q in Hqa, Hm, Huv0.
  assert (Hden : atan3 zb - atan3 za <> 0).
  { pose proof (atan_ends_sep a m b Ham Hmb Hab Hd Hr) as Hs.
    cbn zeta in Hs. fold o in Hs. fold q in Hs.
    fold zb in Hs. fold za in Hs.
    intros E. apply Hs. lra. }
  set (e := egg_of_points a m b).
  set (t := (atan3 z - atan3 za) / (atan3 zb - atan3 za)).
  assert (Hsweep : circ_sweep e = 2 * (atan3 zb - atan3 za)).
  { unfold e, egg_of_points, o, q, za, zb, ux, uy. reflexivity. }
  assert (Hth : circ_theta0 e = principal (atan2 uy ux + 2 * atan3 za)).
  { unfold e, egg_of_points, o, q, ux, uy, za. reflexivity. }
  assert (Ho : circ_o e = o).
  { unfold e, egg_of_points, o. reflexivity. }
  assert (HrE : circ_r e = dist o a).
  { unfold e, egg_of_points, o. reflexivity. }
  assert (Huv : ~ (ux = 0 /\ uy = 0)).
  { fold ux uy. exact Huv0. }
  assert (Esq : dist_sq o a = ux * ux + uy * uy).
  { rewrite <- Hqa. unfold dist_sq. fold ux uy. ring. }
  assert (Hs : dist o a = sqrt (ux * ux + uy * uy)).
  { unfold dist. rewrite Esq. reflexivity. }
  assert (Hcos : dist o a * cos (atan2 uy ux) = ux).
  { rewrite (cos_atan2 ux uy Huv). rewrite <- Hs. field.
    exact Hr. }
  assert (Hsin : dist o a * sin (atan2 uy ux) = uy).
  { rewrite (sin_atan2 ux uy Huv). rewrite <- Hs. field.
    exact Hr. }
  assert (Hraw : - (2 * PI) < atan2 uy ux + 2 * atan3 za < 2 * PI).
  { apply raw_in_open. exact Huv. }
  assert (Hts : t * circ_sweep e = 2 * (atan3 z - atan3 za)).
  { rewrite Hsweep. unfold t. field. exact Hden. }
  assert (Hcang : cos (circ_theta0 e + t * circ_sweep e)
                  = cos (atan2 uy ux + 2 * atan3 z)).
  { rewrite Hth, Hts. set (raw := atan2 uy ux + 2 * atan3 za). unfold principal.
    destruct (Rle_dec raw (- PI)) as [Hle|Hnle].
    - replace (raw + 2 * PI + 2 * (atan3 z - atan3 za))
        with (raw + 2 * (atan3 z - atan3 za) + 2 * PI) by ring.
      rewrite cos_shift_2pi.
      replace (raw + 2 * (atan3 z - atan3 za))
        with (atan2 uy ux + 2 * atan3 z) by (unfold raw; ring).
      reflexivity.
    - destruct (Rlt_dec PI raw) as [Hlt|Hge].
      + replace (raw - 2 * PI + 2 * (atan3 z - atan3 za))
          with (raw + 2 * (atan3 z - atan3 za) - 2 * PI) by ring.
        rewrite cos_shift_m2pi.
        replace (raw + 2 * (atan3 z - atan3 za))
          with (atan2 uy ux + 2 * atan3 z) by (unfold raw; ring).
        reflexivity.
      + replace (raw + 2 * (atan3 z - atan3 za))
          with (atan2 uy ux + 2 * atan3 z) by (unfold raw; ring).
        reflexivity. }
  assert (Hsang : sin (circ_theta0 e + t * circ_sweep e)
                  = sin (atan2 uy ux + 2 * atan3 z)).
  { rewrite Hth, Hts. set (raw := atan2 uy ux + 2 * atan3 za). unfold principal.
    destruct (Rle_dec raw (- PI)) as [Hle|Hnle].
    - replace (raw + 2 * PI + 2 * (atan3 z - atan3 za))
        with (raw + 2 * (atan3 z - atan3 za) + 2 * PI) by ring.
      rewrite sin_shift_2pi.
      replace (raw + 2 * (atan3 z - atan3 za))
        with (atan2 uy ux + 2 * atan3 z) by (unfold raw; ring).
      reflexivity.
    - destruct (Rlt_dec PI raw) as [Hlt|Hge].
      + replace (raw - 2 * PI + 2 * (atan3 z - atan3 za))
          with (raw + 2 * (atan3 z - atan3 za) - 2 * PI) by ring.
        rewrite sin_shift_m2pi.
        replace (raw + 2 * (atan3 z - atan3 za))
          with (atan2 uy ux + 2 * atan3 z) by (unfold raw; ring).
        reflexivity.
      + replace (raw + 2 * (atan3 z - atan3 za))
          with (atan2 uy ux + 2 * atan3 z) by (unfold raw; ring).
        reflexivity. }
  destruct (chart_rotate ux uy z) as [Hpx Hpy].
  unfold circ_eval. rewrite Ho, HrE.
  apply (f_equal2 mkPoint).
  - rewrite Hcang. rewrite cos_plus.
    replace (dist o a * (cos (atan2 uy ux) * cos (2 * atan3 z)
                       - sin (atan2 uy ux) * sin (2 * atan3 z)))
      with (dist o a * cos (atan2 uy ux) * cos (2 * atan3 z)
          - dist o a * sin (atan2 uy ux) * sin (2 * atan3 z)) by ring.
    rewrite Hcos, Hsin, <- Hpx. ring.
  - rewrite Hsang. rewrite sin_plus.
    replace (dist o a * (sin (atan2 uy ux) * cos (2 * atan3 z)
                       + cos (atan2 uy ux) * sin (2 * atan3 z)))
      with (dist o a * sin (atan2 uy ux) * cos (2 * atan3 z)
          + dist o a * cos (atan2 uy ux) * sin (2 * atan3 z)) by ring.
    rewrite Hcos, Hsin, <- Hpy. ring.
Qed.

Lemma egg_chart_t_open : forall a m b,
  dist_sq a m <> 0 ->
  dist_sq m b <> 0 ->
  dist_sq a b <> 0 ->
  circ_denom a m b <> 0 ->
  dist (circumcenter_of a m b) a <> 0 ->
  let o := circumcenter_of a m b in
  let q := pole_point o m (midpoint a b) in
  let za := zeta_of_pt o q a in
  let zb := zeta_of_pt o q b in
  let zm := zeta_of_pt o q m in
  0 < (atan3 zm - atan3 za) / (atan3 zb - atan3 za) < 1.
Proof.
  intros a m b Ham Hmb Hab Hd Hr o q za zb zm.
  pose proof (zeta_mid_strict a m b Ham Hmb Hab Hd Hr) as Hp.
  cbn zeta in Hp. fold o in Hp. fold q in Hp.
  fold zm in Hp. fold zb in Hp. fold za in Hp.
  pose proof (atan_ends_sep a m b Ham Hmb Hab Hd Hr) as Hsep.
  cbn zeta in Hsep. fold o in Hsep. fold q in Hsep.
  fold zb in Hsep. fold za in Hsep.
  set (num := atan3 zm - atan3 za).
  set (den := atan3 zb - atan3 za).
  assert (Hden : den <> 0) by (unfold den; intros E; apply Hsep; lra).
  destruct (Rtotal_order za zb) as [Hlt|[Heq|Hgt]].
  - assert (Hbet : za < zm < zb) by nra.
    assert (Hnum : 0 < num).
    { unfold num. apply Rlt_0_minus. apply atan3_strict. lra. }
    assert (Hnd : num < den).
    { unfold num, den. apply Rplus_lt_compat_r.
      apply atan3_strict. lra. }
    assert (Hdenp : 0 < den) by lra.
    apply ratio_open; [exact Hdenp | split; assumption].
  - exfalso. apply Hsep. rewrite Heq. reflexivity.
  - assert (Hbet : zb < zm < za) by nra.
    assert (num < 0).
    { unfold num. assert (Hzm : zm < za) by lra.
      pose proof (atan3_strict _ _ Hzm) as Hz. lra. }
    assert (den < num).
    { unfold num, den. apply Rplus_lt_compat_r.
      apply atan3_strict. lra. }
    assert (den < 0) by lra.
    replace (num / den) with ((- num) / (- den)).
    2: { field. exact Hden. }
    apply ratio_open; lra.
Qed.

Lemma egg_on_controls : forall a m b,
  dist_sq a m <> 0 ->
  dist_sq m b <> 0 ->
  dist_sq a b <> 0 ->
  circ_denom a m b <> 0 ->
  dist (circumcenter_of a m b) a <> 0 ->
  let e := egg_of_points a m b in
  circ_eval e 0 = a /\
  circ_eval e 1 = b /\
  (exists t, 0 < t < 1 /\ circ_eval e t = m).
Proof.
  intros a m b Ham Hmb Hab Hd Hr e.
  set (o := circumcenter_of a m b).
  set (q := pole_point o m (midpoint a b)).
  set (ux := px o - px q).
  set (uy := py o - py q).
  set (za := zeta_of_pt o q a).
  set (zb := zeta_of_pt o q b).
  set (zm := zeta_of_pt o q m).
  destruct (egg_circle_pack a m b Ham Hmb Hab Hd Hr)
    as [Hqa [Hm [Hb [Hqa_ne [Hqb [Hqm _]]]]]].
  fold o q in Hqa, Hm, Hb, Hqa_ne, Hqb, Hqm.
  assert (Hden : atan3 zb - atan3 za <> 0).
  { pose proof (atan_ends_sep a m b Ham Hmb Hab Hd Hr) as Hs.
    cbn zeta in Hs. fold o in Hs. fold q in Hs.
    fold zb in Hs. fold za in Hs.
    intros E. apply Hs. lra. }
  assert (Ht0 : (atan3 za - atan3 za) / (atan3 zb - atan3 za) = 0).
  { field. exact Hden. }
  assert (Ht1 : (atan3 zb - atan3 za) / (atan3 zb - atan3 za) = 1).
  { field. exact Hden. }
  destruct (on_chart_pt o q a (eq_sym Hqa) (not_eq_sym Hqa_ne)) as [Hax Hay].
  destruct (on_chart_pt o q b (eq_trans Hb (eq_sym Hqa)) (not_eq_sym Hqb)) as [Hbx Hby].
  destruct (on_chart_pt o q m (eq_trans Hm (eq_sym Hqa)) (not_eq_sym Hqm)) as [Hmx Hmy].
  fold ux uy za in Hax, Hay.
  fold ux uy zb in Hbx, Hby.
  fold ux uy zm in Hmx, Hmy.
  split.
  - pose proof (egg_eval_chart a m b za Ham Hmb Hab Hd Hr) as He.
    cbn zeta in He.
    fold o in He. fold q in He. fold ux in He. fold uy in He.
    fold zb in He. fold za in He.
    rewrite Ht0 in He.
    rewrite <- Hax, <- Hay in He.
    fold e in He.
    transitivity (mkPoint (px a) (py a)).
    + exact He.
    + apply Point_eq_of_coords; reflexivity.
  - split.
    + pose proof (egg_eval_chart a m b zb Ham Hmb Hab Hd Hr) as He.
      cbn zeta in He.
      fold o in He. fold q in He. fold ux in He. fold uy in He.
      fold zb in He. fold za in He.
      rewrite Ht1 in He.
      rewrite <- Hbx, <- Hby in He.
      fold e in He.
      transitivity (mkPoint (px b) (py b)).
      * exact He.
      * apply Point_eq_of_coords; reflexivity.
    + exists ((atan3 zm - atan3 za) / (atan3 zb - atan3 za)).
      split.
      * pose proof (egg_chart_t_open a m b Ham Hmb Hab Hd Hr) as Ht.
        cbn zeta in Ht.
        fold o in Ht. fold q in Ht. fold zm in Ht. fold zb in Ht. fold za in Ht.
        exact Ht.
      * pose proof (egg_eval_chart a m b zm Ham Hmb Hab Hd Hr) as He.
        cbn zeta in He.
        fold o in He. fold q in He. fold ux in He. fold uy in He.
        fold zm in He. fold zb in He. fold za in He.
        rewrite <- Hmx, <- Hmy in He.
        fold e in He.
        transitivity (mkPoint (px m) (py m)).
        -- exact He.
        -- apply Point_eq_of_coords; reflexivity.
Qed.

Lemma egg_theta_range : forall a m b,
  dist_sq a m <> 0 ->
  dist_sq m b <> 0 ->
  dist_sq a b <> 0 ->
  circ_denom a m b <> 0 ->
  dist (circumcenter_of a m b) a <> 0 ->
  - PI < circ_theta0 (egg_of_points a m b) <= PI.
Proof.
  intros a m b Ham Hmb Hab Hd Hr.
  destruct (egg_fields a m b) as [_ [_ [Hth _]]].
  rewrite Hth.
  apply principal_range.
  apply raw_in_open.
  destruct (egg_circle_pack a m b Ham Hmb Hab Hd Hr) as [_ [_ [_ [_ [_ [_ Huv]]]]]].
  exact Huv.
Qed.

Lemma egg_sweep_open : forall a m b,
  dist_sq a m <> 0 ->
  dist_sq m b <> 0 ->
  dist_sq a b <> 0 ->
  circ_denom a m b <> 0 ->
  dist (circumcenter_of a m b) a <> 0 ->
  0 < Rabs (circ_sweep (egg_of_points a m b)) < 2 * PI.
Proof.
  intros a m b Ham Hmb Hab Hd Hr.
  set (o := circumcenter_of a m b).
  set (q := pole_point o m (midpoint a b)).
  set (za := zeta_of_pt o q a).
  set (zb := zeta_of_pt o q b).
  destruct (egg_fields a m b) as [_ [_ [_ Hs]]].
  assert (Hs' : circ_sweep (egg_of_points a m b) = 2 * (atan3 zb - atan3 za)).
  { rewrite Hs. unfold o, q, za, zb. reflexivity. }
  destruct (atan3_spec za) as [[Hza1 Hza2] _].
  destruct (atan3_spec zb) as [[Hzb1 Hzb2] _].
  assert (Hdiff : - PI < atan3 zb - atan3 za < PI) by lra.
  assert (Habsd : Rabs (atan3 zb - atan3 za) < PI).
  { apply Rabs_def1; lra. }
  assert (Habs : Rabs (circ_sweep (egg_of_points a m b))
                 = 2 * Rabs (atan3 zb - atan3 za)).
  { rewrite Hs'. rewrite Rabs_mult.
    rewrite (Rabs_right 2) by lra. reflexivity. }
  assert (Hsep : atan3 zb <> atan3 za).
  { pose proof (atan_ends_sep a m b Ham Hmb Hab Hd Hr) as E.
    fold o q za zb in E. exact E. }
  split.
  - rewrite Habs. apply Rmult_lt_0_compat; [lra|].
    apply Rabs_pos_lt. lra.
  - rewrite Habs. apply Rmult_lt_compat_l; lra.
Qed.

Lemma egg_sweep_sign : forall a m b,
  dist_sq a m <> 0 ->
  dist_sq m b <> 0 ->
  dist_sq a b <> 0 ->
  circ_denom a m b <> 0 ->
  dist (circumcenter_of a m b) a <> 0 ->
  circ_sweep (egg_of_points a m b) * orient_pts a m b > 0.
Proof.
  intros a m b Ham Hmb Hab Hd Hr.
  set (o := circumcenter_of a m b).
  set (q := pole_point o m (midpoint a b)).
  set (ux := px o - px q).
  set (uy := py o - py q).
  set (za := zeta_of_pt o q a).
  set (zb := zeta_of_pt o q b).
  set (zm := zeta_of_pt o q m).
  set (e := egg_of_points a m b).
  destruct (egg_circle_pack a m b Ham Hmb Hab Hd Hr)
    as [Hqa [Hm [Hb [Hqa_ne [Hqb [Hqm Huv0]]]]]].
  fold o q in Hqa, Hm, Hb, Hqa_ne, Hqb, Hqm, Huv0.
  pose proof (zeta_mid_strict a m b Ham Hmb Hab Hd Hr) as Hp.
  cbn zeta in Hp. fold o in Hp. fold q in Hp.
  fold zm in Hp. fold zb in Hp. fold za in Hp.
  assert (Hs : circ_sweep e = 2 * (atan3 zb - atan3 za)).
  { unfold e, egg_of_points, o, q, za, zb. reflexivity. }
  assert (Huv : (ux, uy) <> (0, 0)).
  { intros E. injection E as Ex Ey. apply Huv0. split; assumption. }
  destruct (on_chart_pt o q a (eq_sym Hqa) (not_eq_sym Hqa_ne)) as [Hax Hay].
  destruct (on_chart_pt o q b (eq_trans Hb (eq_sym Hqa)) (not_eq_sym Hqb)) as [Hbx Hby].
  destruct (on_chart_pt o q m (eq_trans Hm (eq_sym Hqa)) (not_eq_sym Hqm)) as [Hmx Hmy].
  fold ux uy za in Hax, Hay.
  fold ux uy zb in Hbx, Hby.
  fold ux uy zm in Hmx, Hmy.
  assert (Horient_chart :
            orient_pts a m b =
            orient3 (px o + zeta_ptx ux uy za) (py o + zeta_pty ux uy za)
                    (px o + zeta_ptx ux uy zm) (py o + zeta_pty ux uy zm)
                    (px o + zeta_ptx ux uy zb) (py o + zeta_pty ux uy zb)).
  { unfold orient_pts, orient3.
    rewrite Hax, Hay, Hmx, Hmy, Hbx, Hby. reflexivity. }
  destruct (Rtotal_order za zb) as [Hlt|[Heq|Hgt]].
  - assert (Hbet : za < zm < zb) by nra.
    destruct (zeta_monotone_off_pole (px o) (py o) ux uy za zm zb Huv
                (proj1 Hbet) (proj2 Hbet)) as [_ [_ Ho3]].
    assert (0 < orient_pts a m b).
    { rewrite Horient_chart. exact Ho3. }
    assert (0 < circ_sweep e).
    { rewrite Hs. apply Rmult_lt_0_compat; [lra|].
      apply Rlt_0_minus. apply atan3_strict. lra. }
    nra.
  - exfalso.
    pose proof (atan_ends_sep a m b Ham Hmb Hab Hd Hr) as Hsep.
    cbn zeta in Hsep. fold o in Hsep. fold q in Hsep.
    fold zb in Hsep. fold za in Hsep.
    apply Hsep. rewrite Heq. reflexivity.
  - assert (Hbet : zb < zm < za) by nra.
    destruct (zeta_monotone_off_pole (px o) (py o) ux uy zb zm za Huv
                (proj1 Hbet) (proj2 Hbet)) as [_ [_ Ho3]].
    assert (0 < orient_pts b m a).
    { unfold orient_pts, orient3.
      rewrite Hbx, Hby, Hmx, Hmy, Hax, Hay. exact Ho3. }
    assert (orient_pts a m b < 0).
    { rewrite (orient_rev_amb a m b) in H. lra. }
    assert (circ_sweep e < 0).
    { rewrite Hs.
      assert (atan3 zb - atan3 za < 0).
      { assert (Hzb : zb < za) by lra.
        pose proof (atan3_strict _ _ Hzb) as Hz. lra. }
      nra. }
    nra.
Qed.

(* Axiom audit. Headlines are the classical-reals trio. *)
Print Assumptions chart_rotate.
Print Assumptions raw_in_open.
Print Assumptions egg_fields.
Print Assumptions mid_ne_of_denom.
Print Assumptions orient_abm_ne.
Print Assumptions orient_rev_amb.
Print Assumptions egg_circle_pack.
Print Assumptions on_chart_pt.
Print Assumptions atan_ends_sep.
Print Assumptions zeta_mid_strict.
Print Assumptions ratio_open.
Print Assumptions ratio_same_sign.
Print Assumptions egg_eval_chart.
Print Assumptions egg_chart_t_open.
Print Assumptions egg_on_controls.
Print Assumptions egg_theta_range.
Print Assumptions egg_sweep_open.
Print Assumptions egg_sweep_sign.
