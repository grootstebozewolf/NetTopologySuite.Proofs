(* ============================================================================
   NetTopologySuite.Proofs.ArcMemberState
   ----------------------------------------------------------------------------
   N2c-i, the arc row. MemberState is IntakeSpiralJts.mkMemberState.
   arc_exit / arc_entry store the certified control point. Direction
   is the unit tangent of circ_eval. Curvature is the constant
   sign(sweep)/radius, which is signed_curv of that parametrization.
   No angles in the output. The compound fold is not this file.
   Chord signed curvature is 0. The clothoid sigma*s/A^2
   instance is norm2_curv, not this file.
   G1 of an exit into a chord (cross(rot90(b-o), d) = 0 and
   sg * dot(rot90(b-o), d) > 0) is named and not proved.
   claimId: none.
   No Admitted / Axiom / Parameter. No classic. No MVT / Rolle /
   RiemannInt.
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra Ranalysis1.
From NTS.Proofs Require Import Distance CircleChart IntakeAnglesCore
  IntakeAnglesChart IntakeAngles IntakeSpiralJts SheetHenCircEgg.
Local Open Scope R_scope.

Definition rsgn (x : R) : R := if Rlt_dec 0 x then 1 else -1.

Definition pt_sub (p q : Point) : Point :=
  mkPoint (px p - px q) (py p - py q).

Definition rot90 (p : Point) : Point := mkPoint (- py p) (px p).

Definition pt_h2 (p : Point) : R := px p * px p + py p * py p.

Lemma point_coords : forall p q, px p = px q -> py p = py q -> p = q.
Proof. intros [] [] Hx Hy. cbn in *. subst. reflexivity. Qed.

Definition arc_sg (a m b : Point) : R := rsgn (orient_pts a m b).

Definition arc_exit (a m b : Point) : MemberState :=
  let o := circumcenter_of a m b in
  let r := dist o b in
  let sg := arc_sg a m b in
  mkMemberState b (pt_scale (sg / r) (rot90 (pt_sub b o))) (sg / r).

Definition arc_entry (a m b : Point) : MemberState :=
  let o := circumcenter_of a m b in
  let r := dist o b in
  let sg := arc_sg a m b in
  mkMemberState a (pt_scale (sg / r) (rot90 (pt_sub a o))) (sg / r).

Definition circ_phi (c : CircularEgg) (t : R) : R :=
  circ_theta0 c + t * circ_sweep c.

Definition circ_vx (c : CircularEgg) (t : R) : R :=
  circ_r c * circ_sweep c * (- sin (circ_phi c t)).

Definition circ_vy (c : CircularEgg) (t : R) : R :=
  circ_r c * circ_sweep c * cos (circ_phi c t).

Definition circ_ax (c : CircularEgg) (t : R) : R :=
  - circ_r c * circ_sweep c * circ_sweep c * cos (circ_phi c t).

Definition circ_ay (c : CircularEgg) (t : R) : R :=
  - circ_r c * circ_sweep c * circ_sweep c * sin (circ_phi c t).

(* cross(γ', γ'') / |γ'|^3, with the derivatives proved below. *)
Definition circ_signed_curv (c : CircularEgg) (t : R) : R :=
  let vx := circ_vx c t in
  let vy := circ_vy c t in
  let ax := circ_ax c t in
  let ay := circ_ay c t in
  let s := sqrt (vx * vx + vy * vy) in
  (vx * ay - vy * ax) / (s * s * s).

Lemma circ_phi_deriv : forall c t,
  derivable_pt_lim (circ_phi c) t (circ_sweep c).
Proof.
  intros c t.
  set (th := circ_theta0 c). set (dth := circ_sweep c).
  assert (E : dth = 0 + dth * 1) by ring.
  apply derivable_pt_lim_ext with
    (f := plus_fct (fct_cte th) (mult_real_fct dth id)).
  - intro z. unfold circ_phi, plus_fct, fct_cte, mult_real_fct, id, th, dth.
    cbn. rewrite Rmult_comm. reflexivity.
  - rewrite E at 2. apply derivable_pt_lim_plus.
    + apply derivable_pt_lim_const.
    + apply derivable_pt_lim_scal. apply derivable_pt_lim_id.
Qed.

Lemma circ_cos_deriv : forall c t,
  derivable_pt_lim (fun u => cos (circ_phi c u)) t
    (- sin (circ_phi c t) * circ_sweep c).
Proof.
  intros c t.
  apply derivable_pt_lim_ext with (f := comp cos (circ_phi c)).
  - intro z. unfold comp. reflexivity.
  - apply derivable_pt_lim_comp; [apply circ_phi_deriv | apply derivable_pt_lim_cos].
Qed.

Lemma circ_sin_deriv : forall c t,
  derivable_pt_lim (fun u => sin (circ_phi c u)) t
    (cos (circ_phi c t) * circ_sweep c).
Proof.
  intros c t.
  apply derivable_pt_lim_ext with (f := comp sin (circ_phi c)).
  - intro z. unfold comp. reflexivity.
  - apply derivable_pt_lim_comp; [apply circ_phi_deriv | apply derivable_pt_lim_sin].
Qed.

Lemma circ_px_deriv : forall c t,
  derivable_pt_lim (fun u => px (circ_eval c u)) t (circ_vx c t).
Proof.
  intros c t.
  set (r := circ_r c). set (dth := circ_sweep c).
  apply derivable_pt_lim_ext with
    (f := plus_fct (fct_cte (px (circ_o c)))
           (mult_real_fct r (fun u => cos (circ_phi c u)))).
  - intro z. unfold plus_fct, fct_cte, mult_real_fct, circ_eval, circ_phi, r. cbn. ring.
  - replace (circ_vx c t) with (0 + r * (- sin (circ_phi c t) * dth))
      by (unfold circ_vx, r, dth; ring).
    apply derivable_pt_lim_plus; [apply derivable_pt_lim_const |].
    apply derivable_pt_lim_scal. apply circ_cos_deriv.
Qed.

Lemma circ_py_deriv : forall c t,
  derivable_pt_lim (fun u => py (circ_eval c u)) t (circ_vy c t).
Proof.
  intros c t.
  set (r := circ_r c). set (dth := circ_sweep c).
  apply derivable_pt_lim_ext with
    (f := plus_fct (fct_cte (py (circ_o c)))
           (mult_real_fct r (fun u => sin (circ_phi c u)))).
  - intro z. unfold plus_fct, fct_cte, mult_real_fct, circ_eval, circ_phi, r. cbn. ring.
  - replace (circ_vy c t) with (0 + r * (cos (circ_phi c t) * dth))
      by (unfold circ_vy, r, dth; ring).
    apply derivable_pt_lim_plus; [apply derivable_pt_lim_const |].
    apply derivable_pt_lim_scal. apply circ_sin_deriv.
Qed.

Lemma circ_vx_deriv : forall c t,
  derivable_pt_lim (circ_vx c) t (circ_ax c t).
Proof.
  intros c t.
  set (k := circ_r c * circ_sweep c).
  apply derivable_pt_lim_ext with
    (f := mult_real_fct k (opp_fct (comp sin (circ_phi c)))).
  - intro z. unfold circ_vx, mult_real_fct, opp_fct, comp, k. ring.
  - replace (circ_ax c t) with (k * (- (cos (circ_phi c t) * circ_sweep c)))
      by (unfold circ_ax, k; ring).
    apply derivable_pt_lim_scal. apply derivable_pt_lim_opp.
    apply derivable_pt_lim_comp; [apply circ_phi_deriv | apply derivable_pt_lim_sin].
Qed.

Lemma circ_vy_deriv : forall c t,
  derivable_pt_lim (circ_vy c) t (circ_ay c t).
Proof.
  intros c t.
  set (k := circ_r c * circ_sweep c).
  apply derivable_pt_lim_ext with
    (f := mult_real_fct k (comp cos (circ_phi c))).
  - intro z. unfold circ_vy, mult_real_fct, comp, k. ring.
  - replace (circ_ay c t) with (k * (- sin (circ_phi c t) * circ_sweep c))
      by (unfold circ_ay, k; ring).
    apply derivable_pt_lim_scal. apply circ_cos_deriv.
Qed.

Lemma rot90_h2 : forall p, pt_h2 (rot90 p) = pt_h2 p.
Proof. intro p. unfold pt_h2, rot90. cbn. ring. Qed.

Lemma scale_h2 : forall k p, pt_h2 (pt_scale k p) = k * k * pt_h2 p.
Proof. intros k p. unfold pt_h2, pt_scale. cbn. ring. Qed.

Lemma scale_scale : forall k1 k2 p,
  pt_scale k1 (pt_scale k2 p) = pt_scale (k1 * k2) p.
Proof. intros. apply point_coords; unfold pt_scale; cbn; ring. Qed.

Lemma rot90_scale : forall k p, rot90 (pt_scale k p) = pt_scale k (rot90 p).
Proof. intros. apply point_coords; unfold rot90, pt_scale; cbn; ring. Qed.

Lemma sub_h2_dist : forall p q, pt_h2 (pt_sub p q) = dist_sq q p.
Proof. intros p q. unfold pt_h2, pt_sub, dist_sq. cbn. ring. Qed.

Lemma circ_speed_sq : forall c t,
  circ_vx c t * circ_vx c t + circ_vy c t * circ_vy c t
    = circ_r c * circ_r c * circ_sweep c * circ_sweep c.
Proof.
  intros c t.
  transitivity (circ_r c * circ_r c * circ_sweep c * circ_sweep c *
    (sin (circ_phi c t) * sin (circ_phi c t)
     + cos (circ_phi c t) * cos (circ_phi c t))).
  - unfold circ_vx, circ_vy. ring.
  - pose proof (sin2_cos2 (circ_phi c t)) as Hs. unfold Rsqr in Hs.
    rewrite Hs. ring.
Qed.

Lemma circ_cross : forall c t,
  circ_vx c t * circ_ay c t - circ_vy c t * circ_ax c t
    = circ_r c * circ_r c * circ_sweep c * circ_sweep c * circ_sweep c.
Proof.
  intros c t.
  transitivity (circ_r c * circ_r c * circ_sweep c * circ_sweep c * circ_sweep c *
    (sin (circ_phi c t) * sin (circ_phi c t)
     + cos (circ_phi c t) * cos (circ_phi c t))).
  - unfold circ_vx, circ_vy, circ_ax, circ_ay. ring.
  - pose proof (sin2_cos2 (circ_phi c t)) as Hs. unfold Rsqr in Hs.
    rewrite Hs. ring.
Qed.

Lemma circ_curv_const : forall c t,
  0 < circ_r c -> circ_sweep c <> 0 ->
  circ_signed_curv c t = rsgn (circ_sweep c) / circ_r c.
Proof.
  intros c t Hr Hnz.
  set (r := circ_r c). set (dth := circ_sweep c).
  unfold circ_signed_curv. cbv zeta.
  rewrite (circ_cross c t). rewrite (circ_speed_sq c t).
  fold r dth.
  assert (Hs : sqrt (r * r * dth * dth) = r * Rabs dth).
  { assert (E : r * r * dth * dth = (r * Rabs dth) * (r * Rabs dth)).
    { destruct (Rle_dec 0 dth) as [Hp|Hn].
      - rewrite (Rabs_pos_eq dth Hp). ring.
      - assert (Hlt : dth < 0) by lra. rewrite (Rabs_left dth Hlt). ring. }
    rewrite E. apply sqrt_square.
    apply Rmult_le_pos; [apply Rlt_le; exact Hr | apply Rabs_pos]. }
  rewrite Hs.
  destruct (Rlt_dec 0 dth) as [Hp|Hn].
  - rewrite (Rabs_pos_eq dth (Rlt_le _ _ Hp)).
    unfold rsgn. destruct (Rlt_dec 0 dth) as [_|Hbad]; [| exfalso; exact (Hbad Hp)].
    field. split; [apply Rgt_not_eq; exact Hr | exact Hnz].
  - assert (Hlt : dth < 0).
    { apply Rnot_lt_le in Hn. destruct (Rle_lt_or_eq _ _ Hn) as [Hlt|Heq]; [exact Hlt|].
      exfalso. apply Hnz. unfold dth in Heq. exact Heq. }
    rewrite (Rabs_left dth Hlt).
    unfold rsgn. destruct (Rlt_dec 0 dth) as [Hbad|_]; [exfalso; lra |].
    field. split; [apply Rgt_not_eq; exact Hr | exact Hnz].
Qed.

Section ArcRow.
Variables a m b : Point.
Hypothesis Ham : dist_sq a m <> 0.
Hypothesis Hmb : dist_sq m b <> 0.
Hypothesis Hab : dist_sq a b <> 0.
Hypothesis Hd : circ_denom a m b <> 0.

Let e : CircularEgg := egg_of_points a m b.
Let o : Point := circumcenter_of a m b.
Let r : R := dist o b.
Let sg : R := arc_sg a m b.

Lemma arc_carry : carry_check e a m b.
Proof. unfold e. apply egg_of_points_certified; assumption. Qed.

Lemma arc_r_pos : 0 < r.
Proof.
  destruct arc_carry as [Hr _].
  assert (Hsq : dist_sq o b = dist_sq o a).
  { unfold o. apply (proj2 (circum_equidistant a m b Hd)). }
  assert (HrE : circ_r e = dist o a).
  { unfold e, o. apply (proj1 (proj2 (egg_fields a m b))). }
  unfold r, dist. rewrite Hsq. unfold dist in HrE. rewrite <- HrE. exact Hr.
Qed.

Lemma arc_r_egg : circ_r e = r.
Proof.
  assert (Hsq : dist_sq o b = dist_sq o a).
  { unfold o. apply (proj2 (circum_equidistant a m b Hd)). }
  assert (HrE : circ_r e = dist o a).
  { unfold e, o. apply (proj1 (proj2 (egg_fields a m b))). }
  rewrite HrE. unfold r, dist. rewrite Hsq. reflexivity.
Qed.

Lemma arc_o_egg : circ_o e = o.
Proof. unfold e, o. apply (proj1 (egg_fields a m b)). Qed.

Lemma arc_dth_nz : circ_sweep e <> 0.
Proof.
  destruct arc_carry as [_ [_ [_ [_ [Hs _]]]]].
  intro Hz. rewrite Hz in Hs. rewrite Rabs_R0 in Hs. lra.
Qed.

Lemma arc_sg_pm : sg = 1 \/ sg = -1.
Proof.
  unfold sg, arc_sg, rsgn.
  destruct (Rlt_dec 0 (orient_pts a m b)); [left | right]; reflexivity.
Qed.

Lemma arc_sg_sq : sg * sg = 1.
Proof. destruct arc_sg_pm as [H|H]; rewrite H; ring. Qed.

Lemma arc_sg_sweep : sg = rsgn (circ_sweep e).
Proof.
  assert (Hp : circ_sweep e * orient_pts a m b > 0).
  { unfold e. apply egg_sweep_sign; try assumption.
    apply circum_radius_nz; assumption. }
  unfold sg, arc_sg, rsgn.
  destruct (Rlt_dec 0 (orient_pts a m b)) as [Ho|Ho];
  destruct (Rlt_dec 0 (circ_sweep e)) as [Hs|Hs]; try reflexivity; exfalso.
  - apply Rnot_lt_le in Hs. nra.
  - apply Rnot_lt_le in Ho. nra.
Qed.

Lemma arc_end_eval : circ_eval e 1 = b.
Proof. destruct arc_carry as [_ [_ [H1 _]]]. exact H1. Qed.

Lemma arc_start_eval : circ_eval e 0 = a.
Proof. destruct arc_carry as [_ [H0 _]]. exact H0. Qed.

Lemma arc_offset : forall t,
  pt_sub (circ_eval e t) o =
  pt_scale r (mkPoint (cos (circ_phi e t)) (sin (circ_phi e t))).
Proof.
  intro t. rewrite <- arc_o_egg, <- arc_r_egg. apply point_coords.
  - unfold pt_sub, pt_scale, circ_eval, circ_phi. cbn. ring.
  - unfold pt_sub, pt_scale, circ_eval, circ_phi. cbn. ring.
Qed.

Lemma arc_exit_pos :
  mst_end (arc_exit a m b) = circ_eval e 1.
Proof.
  unfold arc_exit. cbn [mst_end]. rewrite arc_end_eval. reflexivity.
Qed.

Lemma arc_entry_pos :
  mst_end (arc_entry a m b) = circ_eval e 0.
Proof.
  unfold arc_entry. cbn [mst_end]. rewrite arc_start_eval. reflexivity.
Qed.

Lemma arc_entry_c0 : pt_eqb (mst_end (arc_entry a m b)) a = true.
Proof.
  unfold pt_eqb. rewrite arc_entry_pos, arc_start_eval.
  destruct (Req_EM_T (px a) (px a)) as [_|Hn]; [| exfalso; apply Hn; reflexivity].
  destruct (Req_EM_T (py a) (py a)) as [_|Hn]; [| exfalso; apply Hn; reflexivity].
  reflexivity.
Qed.

Lemma arc_dir_at : forall t,
  let s := r * Rabs (circ_sweep e) in
  s <> 0 /\
  pt_scale (sg / r) (rot90 (pt_sub (circ_eval e t) o)) =
  mkPoint (circ_vx e t / s) (circ_vy e t / s).
Proof.
  intro t. set (s := r * Rabs (circ_sweep e)).
  assert (Hr : 0 < r) by apply arc_r_pos.
  assert (Hnz : circ_sweep e <> 0) by apply arc_dth_nz.
  assert (Hs : s <> 0).
  { unfold s. intro Z.
    destruct (Rmult_integral _ _ Z) as [Hr0|Ha].
    - lra.
    - apply Hnz.
      assert (E : circ_sweep e * circ_sweep e = 0).
      { replace (circ_sweep e * circ_sweep e)
          with (Rsqr (Rabs (circ_sweep e))).
        - unfold Rsqr. rewrite Ha. ring.
        - rewrite <- (Rsqr_abs (circ_sweep e)). unfold Rsqr. reflexivity. }
      destruct (Rmult_integral _ _ E) as [Z0|Z0]; exact Z0. }
  split; [exact Hs |].
  rewrite arc_offset, rot90_scale, scale_scale.
  apply point_coords; unfold pt_scale, rot90; cbn [px py].
  - unfold circ_vx. rewrite arc_r_egg, arc_sg_sweep.
    unfold s. set (dth := circ_sweep e). set (phi := circ_phi e t). unfold rsgn.
    destruct (Rlt_dec 0 dth) as [Hp|Hn].
    + rewrite (Rabs_pos_eq dth (Rlt_le _ _ Hp)).
      replace ((1 / r) * r) with 1 by (field; apply Rgt_not_eq; exact Hr).
      field. split; [exact Hnz | apply Rgt_not_eq; exact Hr].
    + assert (Hlt : dth < 0).
      { apply Rnot_lt_le in Hn. destruct (Rle_lt_or_eq _ _ Hn) as [Hlt|Heq]; [exact Hlt|].
        exfalso. apply Hnz. unfold dth in Heq. exact Heq. }
      rewrite (Rabs_left dth Hlt).
      replace (((-1) / r) * r) with (-1) by (field; apply Rgt_not_eq; exact Hr).
      field. split; [exact Hnz | apply Rgt_not_eq; exact Hr].
  - unfold circ_vy. rewrite arc_r_egg, arc_sg_sweep.
    unfold s. set (dth := circ_sweep e). set (phi := circ_phi e t). unfold rsgn.
    destruct (Rlt_dec 0 dth) as [Hp|Hn].
    + rewrite (Rabs_pos_eq dth (Rlt_le _ _ Hp)).
      replace ((1 / r) * r) with 1 by (field; apply Rgt_not_eq; exact Hr).
      field. split; [exact Hnz | apply Rgt_not_eq; exact Hr].
    + assert (Hlt : dth < 0).
      { apply Rnot_lt_le in Hn. destruct (Rle_lt_or_eq _ _ Hn) as [Hlt|Heq]; [exact Hlt|].
        exfalso. apply Hnz. unfold dth in Heq. exact Heq. }
      rewrite (Rabs_left dth Hlt).
      replace (((-1) / r) * r) with (-1) by (field; apply Rgt_not_eq; exact Hr).
      field. split; [exact Hnz | apply Rgt_not_eq; exact Hr].
Qed.

Lemma arc_exit_dir_tangent :
  let s := r * Rabs (circ_sweep e) in
  mst_dir (arc_exit a m b) =
    mkPoint (circ_vx e 1 / s) (circ_vy e 1 / s).
Proof.
  intro s. unfold arc_exit. cbn [mst_dir].
  pose proof (proj2 (arc_dir_at 1)) as Hdir.
  rewrite arc_end_eval in Hdir. exact Hdir.
Qed.

Lemma arc_entry_dir_tangent :
  let s := r * Rabs (circ_sweep e) in
  mst_dir (arc_entry a m b) =
    mkPoint (circ_vx e 0 / s) (circ_vy e 0 / s).
Proof.
  intro s. unfold arc_entry. cbn [mst_dir].
  pose proof (proj2 (arc_dir_at 0)) as Hdir.
  rewrite arc_start_eval in Hdir. exact Hdir.
Qed.

Lemma arc_exit_dir_unit : pt_h2 (mst_dir (arc_exit a m b)) = 1.
Proof.
  unfold arc_exit. cbn [mst_dir].
  change (circumcenter_of a m b) with o.
  change (dist o b) with r.
  change (arc_sg a m b) with sg.
  rewrite scale_h2, rot90_h2, sub_h2_dist.
  assert (Hr : dist_sq o b = r * r).
  { unfold r, dist. symmetry. apply sqrt_sqrt, dist_sq_nonneg. }
  rewrite Hr. transitivity (sg * sg).
  - field. apply Rgt_not_eq, arc_r_pos.
  - apply arc_sg_sq.
Qed.

Lemma arc_entry_dir_unit : pt_h2 (mst_dir (arc_entry a m b)) = 1.
Proof.
  unfold arc_entry. cbn [mst_dir].
  change (circumcenter_of a m b) with o.
  change (dist o b) with r.
  change (arc_sg a m b) with sg.
  rewrite scale_h2, rot90_h2, sub_h2_dist.
  assert (Hsq : dist_sq o a = dist_sq o b).
  { unfold o. symmetry. apply (proj2 (circum_equidistant a m b Hd)). }
  rewrite Hsq.
  assert (Hr : dist_sq o b = r * r).
  { unfold r, dist. symmetry. apply sqrt_sqrt, dist_sq_nonneg. }
  rewrite Hr. transitivity (sg * sg).
  - field. apply Rgt_not_eq, arc_r_pos.
  - apply arc_sg_sq.
Qed.

Lemma arc_exit_curv : forall t,
  mst_curvature (arc_exit a m b) = circ_signed_curv e t.
Proof.
  intro t. unfold arc_exit. cbn [mst_curvature].
  rewrite circ_curv_const; [rewrite <- arc_sg_sweep, arc_r_egg; reflexivity | |].
  - rewrite arc_r_egg. apply arc_r_pos.
  - apply arc_dth_nz.
Qed.

Lemma arc_entry_curv : forall t,
  mst_curvature (arc_entry a m b) = circ_signed_curv e t.
Proof.
  intro t. unfold arc_entry. cbn [mst_curvature].
  rewrite circ_curv_const; [rewrite <- arc_sg_sweep, arc_r_egg; reflexivity | |].
  - rewrite arc_r_egg. apply arc_r_pos.
  - apply arc_dth_nz.
Qed.

Lemma arc_g2_rational : forall k0,
  k0 = mst_curvature (arc_exit a m b) <->
  k0 * k0 * dist_sq o b = 1 /\ rsgn k0 = rsgn (orient_pts a m b).
Proof.
  intro k0.
  assert (Hr : 0 < r) by apply arc_r_pos.
  assert (Ecur : mst_curvature (arc_exit a m b) = sg / r).
  { unfold arc_exit. cbn [mst_curvature]. unfold sg, r, o. reflexivity. }
  assert (Er2 : r * r = dist_sq o b).
  { unfold r, dist. apply sqrt_sqrt, dist_sq_nonneg. }
  split.
  - intro Hk. rewrite Ecur in Hk. subst k0. split.
    + assert (Hr2 : dist_sq o b = r * r).
      { unfold r, dist. symmetry. apply sqrt_sqrt, dist_sq_nonneg. }
      rewrite Hr2. transitivity (sg * sg);
        [field; apply Rgt_not_eq; exact Hr | apply arc_sg_sq].
    + destruct arc_sg_pm as [H1|Hm].
      * rewrite H1. change (rsgn (orient_pts a m b)) with sg. rewrite H1.
        unfold rsgn. destruct (Rlt_dec 0 (1 / r)) as [_|Hbad]; [reflexivity |].
        exfalso. apply Hbad. apply Rdiv_lt_0_compat; [apply Rlt_0_1 | exact Hr].
      * rewrite Hm. change (rsgn (orient_pts a m b)) with sg. rewrite Hm.
        unfold rsgn. destruct (Rlt_dec 0 ((-1) / r)) as [Hbad|_]; [| reflexivity].
        exfalso.
        assert (Hneg : (-1) / r < 0).
        { unfold Rdiv. replace (-1 * / r) with (- (/ r)) by ring.
          apply Ropp_0_lt_gt_contravar. apply Rinv_0_lt_compat. exact Hr. }
        exact (Rlt_asym _ _ Hneg Hbad).
  - intros [Hsq Hsgn]. rewrite Ecur.
    assert (Hsgn' : rsgn k0 = sg).
    { rewrite Hsgn. unfold sg, arc_sg. reflexivity. }
    assert (Hrr : k0 * k0 * (r * r) = 1) by (rewrite Er2; exact Hsq).
    destruct arc_sg_pm as [H1|Hm].
    + rewrite H1 in Hsgn', Ecur. unfold rsgn in Hsgn'.
      destruct (Rlt_dec 0 k0) as [Hp|Hn]; [| exfalso; lra].
      assert (Hk : k0 * r = 1).
      { assert (E : (k0 * r - 1) * (k0 * r + 1) = 0).
        { replace ((k0 * r - 1) * (k0 * r + 1)) with (k0 * k0 * (r * r) - 1) by ring.
          rewrite Hrr. ring. }
        destruct (Rmult_integral _ _ E) as [Hm1|Hp1].
        - apply (Rplus_eq_compat_r 1) in Hm1. rewrite Rplus_0_l in Hm1.
          replace (k0 * r - 1 + 1) with (k0 * r) in Hm1 by ring. exact Hm1.
        - exfalso.
          assert (Hpos : 0 < k0 * r) by (apply Rmult_lt_0_compat; assumption).
          apply (Rplus_eq_compat_r (-1)) in Hp1.
          replace (k0 * r + 1 + -1) with (k0 * r) in Hp1 by ring.
          rewrite Rplus_0_l in Hp1. rewrite Hp1 in Hpos. lra. }
      transitivity ((k0 * r) / r);
        [field; apply Rgt_not_eq; exact Hr | rewrite Hk, H1; reflexivity].
    + rewrite Hm in Hsgn', Ecur. unfold rsgn in Hsgn'.
      destruct (Rlt_dec 0 k0) as [Hp|Hn]; [exfalso; lra |].
      assert (Hlt : k0 < 0).
      { apply Rnot_lt_le in Hn. destruct (Rle_lt_or_eq _ _ Hn) as [Hlt|Heq]; [exact Hlt|].
        exfalso. rewrite Heq, Rmult_0_l, Rmult_0_l in Hrr. lra. }
      assert (Hk : k0 * r = -1).
      { assert (E : (k0 * r - 1) * (k0 * r + 1) = 0).
        { replace ((k0 * r - 1) * (k0 * r + 1)) with (k0 * k0 * (r * r) - 1) by ring.
          rewrite Hrr. ring. }
        destruct (Rmult_integral _ _ E) as [Hm1|Hp1].
        - exfalso.
          apply (Rplus_eq_compat_r 1) in Hm1. rewrite Rplus_0_l in Hm1.
          replace (k0 * r - 1 + 1) with (k0 * r) in Hm1 by ring.
          assert (Hneg : k0 * r < 0).
          { apply Ropp_lt_cancel. rewrite Ropp_0, Ropp_mult_distr_l.
            apply Rmult_lt_0_compat; [lra | exact Hr]. }
          rewrite Hm1 in Hneg. lra.
        - apply (Rplus_eq_compat_r (-1)) in Hp1.
          replace (k0 * r + 1 + -1) with (k0 * r) in Hp1 by ring.
          rewrite Rplus_0_l in Hp1. exact Hp1. }
      transitivity ((k0 * r) / r);
        [field; apply Rgt_not_eq; exact Hr | rewrite Hk, Hm; reflexivity].
Qed.

End ArcRow.

(* Straight chord: second derivative is 0, so signed curvature is 0. *)
Definition chord_vx (p q : Point) : R := px q - px p.
Definition chord_vy (p q : Point) : R := py q - py p.

Lemma chord_px_deriv : forall p q t,
  derivable_pt_lim (fun u => px p + u * chord_vx p q) t (chord_vx p q).
Proof.
  intros p q t.
  replace (chord_vx p q) with (0 + chord_vx p q * 1) by ring.
  apply derivable_pt_lim_ext with
    (f := plus_fct (fct_cte (px p)) (mult_real_fct (chord_vx p q) id)).
  - intro z. unfold plus_fct, fct_cte, mult_real_fct, id. ring.
  - apply derivable_pt_lim_plus; [apply derivable_pt_lim_const |].
    apply derivable_pt_lim_scal. apply derivable_pt_lim_id.
Qed.

Lemma chord_py_deriv : forall p q t,
  derivable_pt_lim (fun u => py p + u * chord_vy p q) t (chord_vy p q).
Proof.
  intros p q t.
  replace (chord_vy p q) with (0 + chord_vy p q * 1) by ring.
  apply derivable_pt_lim_ext with
    (f := plus_fct (fct_cte (py p)) (mult_real_fct (chord_vy p q) id)).
  - intro z. unfold plus_fct, fct_cte, mult_real_fct, id. ring.
  - apply derivable_pt_lim_plus; [apply derivable_pt_lim_const |].
    apply derivable_pt_lim_scal. apply derivable_pt_lim_id.
Qed.

Lemma chord_v_const : forall p q t,
  derivable_pt_lim (fun _ : R => chord_vx p q) t 0.
Proof. intros. apply derivable_pt_lim_const. Qed.

Lemma chord_w_const : forall p q t,
  derivable_pt_lim (fun _ : R => chord_vy p q) t 0.
Proof. intros. apply derivable_pt_lim_const. Qed.

Lemma chord_signed_curv : forall p q,
  let vx := chord_vx p q in
  let vy := chord_vy p q in
  let s := sqrt (vx * vx + vy * vy) in
  (vx * 0 - vy * 0) / (s * s * s) = 0.
Proof.
  intros. unfold vx, vy, s, Rdiv.
  replace (chord_vx p q * 0 - chord_vy p q * 0) with 0 by ring.
  apply Rmult_0_l.
Qed.

Print Assumptions point_coords.
Print Assumptions circ_phi_deriv.
Print Assumptions circ_cos_deriv.
Print Assumptions circ_sin_deriv.
Print Assumptions circ_px_deriv.
Print Assumptions circ_py_deriv.
Print Assumptions circ_vx_deriv.
Print Assumptions circ_vy_deriv.
Print Assumptions rot90_h2.
Print Assumptions scale_h2.
Print Assumptions scale_scale.
Print Assumptions rot90_scale.
Print Assumptions sub_h2_dist.
Print Assumptions circ_speed_sq.
Print Assumptions circ_cross.
Print Assumptions circ_curv_const.
Print Assumptions arc_carry.
Print Assumptions arc_r_pos.
Print Assumptions arc_r_egg.
Print Assumptions arc_o_egg.
Print Assumptions arc_dth_nz.
Print Assumptions arc_sg_pm.
Print Assumptions arc_sg_sq.
Print Assumptions arc_sg_sweep.
Print Assumptions arc_end_eval.
Print Assumptions arc_start_eval.
Print Assumptions arc_offset.
Print Assumptions arc_exit_pos.
Print Assumptions arc_entry_pos.
Print Assumptions arc_entry_c0.
Print Assumptions arc_dir_at.
Print Assumptions arc_exit_dir_tangent.
Print Assumptions arc_entry_dir_tangent.
Print Assumptions arc_exit_dir_unit.
Print Assumptions arc_entry_dir_unit.
Print Assumptions arc_exit_curv.
Print Assumptions arc_entry_curv.
Print Assumptions arc_g2_rational.
Print Assumptions chord_px_deriv.
Print Assumptions chord_py_deriv.
Print Assumptions chord_v_const.
Print Assumptions chord_w_const.
Print Assumptions chord_signed_curv.
