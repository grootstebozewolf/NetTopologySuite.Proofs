(* ============================================================================
   NetTopologySuite.Proofs.CurveRingWindingLocal
   W2. Off the image, winding is constant on a disc. A simple convex chord
   ring (no self-intersection, either orientation) has winding in {-1,0,1},
   and ±1 is exactly the bounded side. Fixtures keep #804.
   Winding numbers, not a ray-cast crossing count. Does not flip
   RNG_JordanUncond. Imports CurveRingWinding; does not edit it.
   claimId / witness: 0007-curve-ring-wind-local · board ADR-0007.
   3-axiom host lane. No Admitted.
   License: BSD-3-Clause. AI-drafted (Cursor Grok 4.7), human-reviewed.
   ========================================================================== *)
From Stdlib Require Import Reals Lra ZArith Lia List Ranalysis1 Ranalysis5 RNsatz.
From Stdlib Require Import Sqrt_reg Rtrigo_alt Arith.Factorial PeanoNat.
From NTS.Proofs Require Import
  Distance Atan2 AtanIvt CurveRingWinding CircleChart Segment SheetHenCircEgg.
Import ListNotations.
Local Open Scope R_scope.

(* §1  Fixtures. #804 locked_rect, locked_lens, grazing diamond; CW halves. *)

Theorem curve_ring_wind_fixtures :
  wind rect_probe locked_rect = 1 /\
  wind lens_probe locked_lens = 1 /\
  wind graz_B grazing_diamond = -1 /\
  wind graz_A grazing_diamond = -1 /\
  wind cw_centre cw_circle_halves = -1.
Proof.
  split; [exact (proj2 (proj2 (proj2 locked_rect_wind_one))) |].
  split; [exact (proj2 (proj2 (proj2 (proj2 locked_lens_wind_one)))) |].
  split; [exact (proj1 grazing_diamond_wind_neg_one) |].
  split; [exact (proj2 grazing_diamond_wind_neg_one) |].
  exact (proj2 (proj2 (proj2 cw_halves_wind_neg_one))).
Qed.

(* §2  Ring shape, half-planes, reversal. *)

Definition arcs_ok (ms : list WindMember) : Prop :=
  forall c, In (WMArc c) ms -> egg_arc_ok c.

Definition chord_only (ms : list WindMember) : Prop :=
  forall m, In m ms -> exists A B, m = WMChord A B.

Definition strict_convex_ccw (ms : list WindMember) : Prop :=
  chord_only ms /\
  members_closed ms /\
  members_adjacent ms /\
  (3 <= length ms)%nat /\
  NoDup (map member_start ms) /\
  (forall A B V,
      In (WMChord A B) ms ->
      In V (map member_start ms) ->
      V <> A -> V <> B ->
      0 < orient_pts A B V).

Definition kernel_ccw (ms : list WindMember) (P : Point) : Prop :=
  forall A B, In (WMChord A B) ms -> 0 < vcross P A B.

Definition flip_member (m : WindMember) : WindMember :=
  match m with
  | WMChord A B => WMChord B A
  | WMArc c => WMArc c
  end.

Definition rev_chords (ms : list WindMember) : list WindMember :=
  rev (map flip_member ms).

Definition shift (P N : Point) (t : R) : Point :=
  mkPoint (px P + t * px N) (py P + t * py N).

Definition right_normal (A B : Point) : Point :=
  mkPoint (dy A B) (- dx A B).

Definition left_normal (A B : Point) : Point :=
  mkPoint (- dy A B) (dx A B).

Lemma chord_arcs_ok : forall ms, chord_only ms -> arcs_ok ms.
Proof.
  intros ms Hch c Hin. exfalso.
  destruct (Hch (WMArc c) Hin) as [A [B E]]. discriminate.
Qed.

Lemma vcross_orient : forall P A B, vcross P A B = orient_pts A B P.
Proof. intros. unfold vcross, orient_pts, orient3, crs, dx, dy. ring. Qed.

Lemma orient_cycle : forall A B C,
  orient_pts A B C = orient_pts B C A.
Proof. intros. unfold orient_pts, orient3, crs. ring. Qed.

Lemma orient_swap : forall A B C,
  orient_pts B A C = - orient_pts A B C.
Proof. intros. unfold orient_pts, orient3, crs. ring. Qed.

Lemma orient_gp : forall A B C D E,
  orient_pts A B C * orient_pts A D E +
  orient_pts A B E * orient_pts A C D =
  orient_pts A B D * orient_pts A C E.
Proof. intros. unfold orient_pts, orient3, crs. ring. Qed.

Lemma lerp_0 : forall P Q, lerp P Q 0 = P.
Proof.
  intros [xp yp] Q. unfold lerp. cbn.
  replace (xp + 0 * (px Q - xp)) with xp by ring.
  replace (yp + 0 * (py Q - yp)) with yp by ring.
  reflexivity.
Qed.

Lemma lerp_1 : forall P Q, lerp P Q 1 = Q.
Proof.
  intros [xp yp] [xq yq]. unfold lerp. cbn.
  replace (xp + 1 * (xq - xp)) with xq by ring.
  replace (yp + 1 * (yq - yp)) with yq by ring.
  reflexivity.
Qed.

Lemma vcross_lerp_affine : forall P Q A B t,
  vcross (lerp P Q t) A B =
    vcross P A B + t * (vcross Q A B - vcross P A B).
Proof. intros. unfold lerp, vcross, dx, dy. cbn. ring. Qed.

Lemma orient_shift : forall A B P N t,
  orient_pts A B (shift P N t) =
    orient_pts A B P + t * (dx A B * py N - dy A B * px N).
Proof. intros. unfold orient_pts, orient3, crs, shift, dx, dy. cbn. ring. Qed.

Lemma dist_sq_lerp_formula : forall C P Q t,
  dist_sq C (lerp P Q t) =
    (1 - t) * dist_sq C P + t * dist_sq C Q
    - t * (1 - t) * dist_sq P Q.
Proof. intros. unfold dist_sq, lerp. cbn. ring. Qed.

Lemma dist_sq_nonneg : forall A B, 0 <= dist_sq A B.
Proof.
  intros [ax ay] [bx byb]. unfold dist_sq. cbn.
  apply Rplus_le_le_0_compat.
  - pose proof (Rle_0_sqr (ax - bx)) as H. unfold Rsqr in H. exact H.
  - pose proof (Rle_0_sqr (ay - byb)) as H. unfold Rsqr in H. exact H.
Qed.

Lemma sum_sq_zero : forall u v, u * u + v * v = 0 -> u = 0 /\ v = 0.
Proof.
  intros u v H.
  pose proof (sqr_nonneg u) as Hu. pose proof (sqr_nonneg v) as Hv.
  destruct (Rplus_eq_R0 _ _ Hu Hv H) as [Eu Ev].
  split; apply sqr_eq_zero; assumption.
Qed.

Lemma sum_sq_pos : forall u v, u <> 0 \/ v <> 0 -> 0 < u * u + v * v.
Proof.
  intros u v Hnz.
  pose proof (sqr_nonneg u) as Hu. pose proof (sqr_nonneg v) as Hv.
  assert (u * u + v * v <> 0).
  { intro E. destruct (sum_sq_zero _ _ E) as [Eu Ev].
    destruct Hnz as [Hu0|Hv0]; contradiction. }
  lra.
Qed.

Lemma dist_sq_lerp_le : forall C P Q t,
  0 <= t <= 1 ->
  dist_sq C (lerp P Q t) <= (1 - t) * dist_sq C P + t * dist_sq C Q.
Proof.
  intros C P Q t Ht. rewrite dist_sq_lerp_formula.
  assert (0 <= t * (1 - t) * dist_sq P Q).
  { apply Rmult_le_pos; [apply Rmult_le_pos; lra | apply dist_sq_nonneg]. }
  lra.
Qed.

Lemma pt_eq_dec : forall A B : Point, {A = B} + {A <> B}.
Proof.
  intros [ax ay] [bx yb].
  destruct (Req_EM_T ax bx) as [Hx|Hx].
  - destruct (Req_EM_T ay yb) as [Hy|Hy].
    + left. subst. reflexivity.
    + right. intros E. apply Hy. apply (f_equal py) in E. exact E.
  - right. intros E. apply Hx. apply (f_equal px) in E. exact E.
Qed.

Lemma norm_identity : forall wx wy vx vy,
  (wx * wx + wy * wy) * (vx * vx + vy * vy) =
    (wx * vx + wy * vy) * (wx * vx + wy * vy) +
    (wx * vy - wy * vx) * (wx * vy - wy * vx).
Proof. intros. ring. Qed.

Definition line_param (A B X : Point) : R :=
  let vx := px B - px A in
  let vy := py B - py A in
  ((px X - px A) * vx + (py X - py A) * vy) / (vx * vx + vy * vy).

Lemma collinear_param : forall A B X,
  A <> B ->
  orient_pts A B X = 0 ->
  X = shift A (mkPoint (px B - px A) (py B - py A)) (line_param A B X).
Proof.
  intros A B X HAB Hcol.
  set (vx := px B - px A). set (vy := py B - py A).
  set (wx := px X - px A). set (wy := py X - py A).
  set (S2 := vx * vx + vy * vy).
  assert (HS : 0 < S2).
  { unfold S2, vx, vy. destruct A as [ax ay], B as [bx yb]. cbn.
    apply sum_sq_pos.
    destruct (Req_dec (bx - ax) 0) as [Hx|Hx]; [| left; exact Hx].
    right. intro Hy. apply HAB.
    assert (Eax : ax = bx) by lra. assert (Eay : ay = yb) by lra.
    rewrite Eax, Eay. reflexivity. }
  set (t := (wx * vx + wy * vy) / S2).
  assert (Ht : t = line_param A B X).
  { unfold line_param, t, S2, wx, wy, vx, vy. reflexivity. }
  assert (Hcross : wx * vy - wy * vx = 0).
  { unfold orient_pts, orient3, crs in Hcol. unfold wx, wy, vx, vy. cbn in *. lra. }
  assert (Hdot0 : (wx - t * vx) * vx + (wy - t * vy) * vy = 0).
  { assert (HS0 : S2 <> 0) by lra.
    replace ((wx - t * vx) * vx + (wy - t * vy) * vy)
      with (wx * vx + wy * vy - t * (vx * vx + vy * vy)).
    - replace (vx * vx + vy * vy) with S2 by reflexivity.
      unfold t, Rdiv. rewrite Rmult_assoc. rewrite Rinv_l; [| exact HS0]. ring.
    - unfold Rminus. ring. }
  assert (Hcrs0 : (wx - t * vx) * vy - (wy - t * vy) * vx = 0).
  { replace ((wx - t * vx) * vy - (wy - t * vy) * vx) with (wx * vy - wy * vx).
    - exact Hcross.
    - unfold Rminus. ring. }
  pose proof (norm_identity (wx - t * vx) (wy - t * vy) vx vy) as Hid.
  assert (Hwn : (wx - t * vx) * (wx - t * vx) + (wy - t * vy) * (wy - t * vy) = 0).
  { apply (Rmult_eq_reg_r S2); [|lra].
    unfold S2. rewrite Hid. rewrite Hdot0, Hcrs0. ring. }
  destruct (sum_sq_zero _ _ Hwn) as [Hx0 Hy0].
  rewrite <- Ht. unfold shift. destruct X as [xx yy], A as [ax ay]. cbn in *.
  unfold wx, wy in Hx0, Hy0. cbn in Hx0, Hy0.
  replace xx with (ax + t * vx) by lra.
  replace yy with (ay + t * vy) by lra.
  reflexivity.
Qed.

Lemma on_open_chord_sep : forall P A B,
  on_open_chord P A B -> A <> B /\ A <> P /\ B <> P.
Proof.
  intros P A B [Hc Hd]. repeat split.
  - intro E. subst B.
    replace (vdot P A A) with (dist_sq A P) in Hd
      by (unfold vdot, dist_sq, dx, dy; reflexivity).
    pose proof (dist_sq_nonneg A P). lra.
  - intro E. subst P. unfold vdot, dx, dy in Hd. cbn in Hd. lra.
  - intro E. subst P. unfold vdot, dx, dy in Hd. cbn in Hd. lra.
Qed.

Lemma vdot_on_param : forall A B t,
  let V := mkPoint (px B - px A) (py B - py A) in
  let X := shift A V t in
  vdot X A B = - t * (1 - t) *
    ((px B - px A) * (px B - px A) + (py B - py A) * (py B - py A)).
Proof.
  intros A B t V X. unfold X, V, shift, vdot, dx, dy. cbn. ring.
Qed.

Lemma on_open_chord_between : forall P A B,
  on_open_chord P A B -> between A B P /\ orient_pts A B P = 0.
Proof.
  intros P A B Ho.
  destruct (on_open_chord_sep P A B Ho) as [HAB [HAP HBP]].
  destruct Ho as [Hc Hd].
  rewrite vcross_orient in Hc.
  assert (HP : P = shift A (mkPoint (px B - px A) (py B - py A)) (line_param A B P))
    by (apply collinear_param; assumption).
  set (t := line_param A B P) in *.
  set (S2 := (px B - px A) * (px B - px A) + (py B - py A) * (py B - py A)).
  assert (Hv : vdot P A B = - t * (1 - t) * S2).
  { rewrite HP. unfold S2. apply vdot_on_param. }
  assert (HS : 0 < S2).
  { unfold S2. destruct A as [ax ay], B as [bx yb]. cbn. apply sum_sq_pos.
    destruct (Req_dec (bx - ax) 0) as [Hx|Hx]; [| left; exact Hx].
    right. intro Hy. apply HAB.
    assert (Eax : ax = bx) by lra. assert (Eay : ay = yb) by lra.
    rewrite Eax, Eay. reflexivity. }
  assert (Ht : 0 < t < 1).
  { assert (Hprod : - t * (1 - t) * S2 < 0) by lra.
    assert (Hneg : - t * (1 - t) < 0).
    { apply (Rmult_lt_reg_r S2); [exact HS | lra]. }
    assert (Hpos : 0 < t * (1 - t)) by lra.
    destruct (Rlt_dec 0 t) as [Ht0|Ht0].
    - destruct (Rlt_dec t 1) as [Ht1|Ht1]; [lra|].
      assert (0 <= t * (t - 1)).
      { apply Rmult_le_pos; lra. }
      assert (t * (1 - t) = - (t * (t - 1))) by ring. lra.
    - assert (0 <= (- t) * (1 - t)).
      { apply Rmult_le_pos; lra. }
      assert (t * (1 - t) = - ((- t) * (1 - t))) by ring. lra. }
  split; [|exact Hc].
  unfold between. exists t. repeat split; try lra.
  - rewrite HP. unfold shift. cbn. ring.
  - rewrite HP. unfold shift. cbn. ring.
Qed.

Lemma open_chord_on_image : forall P A B,
  on_open_chord P A B -> on_member_image P (WMChord A B).
Proof.
  intros P A B Ho. destruct (on_open_chord_between P A B Ho) as [Hb Hc].
  split; assumption.
Qed.

(* §3  Continuity off the atan2 cut. *)

Lemma continuity_pt_affine : forall a b t0,
  continuity_pt (fun t => a + t * b) t0.
Proof.
  intros a b t0 eps Heps.
  unfold continuity_pt, continue_in, limit1_in, limit_in.
  destruct (Req_dec b 0) as [Hb|Hb].
  - exists 1. split; [lra|]. intros y _.
    unfold R_met; simpl; unfold Rdist. subst b.
    assert (He : a + y * 0 - (a + t0 * 0) = 0) by (unfold Rminus; ring).
    rewrite He. rewrite Rabs_R0. exact Heps.
  - exists (eps / Rabs b). split.
    + apply Rdiv_lt_0_compat; [exact Heps | apply Rabs_pos_lt; exact Hb].
    + intros y [_ Hd]. unfold R_met in *; simpl in *; unfold Rdist in *.
      replace (a + y * b - (a + t0 * b)) with ((y - t0) * b) by ring.
      rewrite Rabs_mult.
      assert (Hb0 : 0 < Rabs b) by (apply Rabs_pos_lt; exact Hb).
      apply (Rmult_lt_compat_r (Rabs b) _ _ Hb0) in Hd.
      replace (eps / Rabs b * Rabs b) with eps in Hd
        by (field; apply Rabs_no_R0; exact Hb).
      exact Hd.
Qed.

Lemma tan_sub : forall x y,
  - (PI / 2) < x < PI / 2 ->
  - (PI / 2) < y < PI / 2 ->
  tan x - tan y = sin (x - y) / (cos x * cos y).
Proof.
  intros x y Hx Hy.
  pose proof (cos_gt_0 x (proj1 Hx) (proj2 Hx)) as Cx.
  pose proof (cos_gt_0 y (proj1 Hy) (proj2 Hy)) as Cy.
  unfold tan. rewrite sin_minus. field. split; lra.
Qed.

Lemma tan_lt_open : forall x y,
  - (PI / 2) < x -> x < y -> y < PI / 2 -> tan x < tan y.
Proof.
  intros x y Hx Hxy Hy.
  assert (Hsub : tan y - tan x = sin (y - x) / (cos y * cos x)).
  { rewrite <- (tan_sub y x); [ring | lra | lra]. }
  pose proof (sin_gt_0 (y - x) ltac:(lra) ltac:(lra)) as Hs.
  pose proof (cos_gt_0 x Hx ltac:(lra)) as Cx.
  pose proof (cos_gt_0 y ltac:(lra) Hy) as Cy.
  assert (0 < cos y * cos x) by (apply Rmult_lt_0_compat; assumption).
  assert (0 < sin (y - x) / (cos y * cos x)).
  { apply Rdiv_lt_0_compat; assumption. }
  lra.
Qed.

Lemma tan_atan3 : forall u, tan (atan3 u) = u.
Proof.
  intro u. destruct (atan3_spec u) as [[Hlo Hhi] Hs].
  pose proof (cos_gt_0 (atan3 u) Hlo Hhi) as Hc.
  unfold tan. rewrite Hs. field. lra.
Qed.

Lemma atan3_lt : forall x y, x < y -> atan3 x < atan3 y.
Proof.
  intros x y Hxy.
  destruct (Rle_lt_dec (atan3 y) (atan3 x)) as [Hle|Hlt]; [| exact Hlt].
  exfalso.
  destruct Hle as [Hlt|Heq].
  - assert (tan (atan3 y) < tan (atan3 x)).
    { apply tan_lt_open.
      - destruct (atan3_spec y) as [[? ?] _]; lra.
      - exact Hlt.
      - destruct (atan3_spec x) as [[? ?] _]; lra. }
    rewrite !tan_atan3 in H. lra.
  - assert (y = x).
    { rewrite <- (tan_atan3 y), <- (tan_atan3 x), Heq. reflexivity. }
    lra.
Qed.

Lemma atan3_continuous : forall u0, continuity_pt atan3 u0.
Proof.
  intros u0 eps Heps.
  unfold continuity_pt, continue_in, limit1_in, limit_in.
  set (a := atan3 u0).
  destruct (atan3_spec u0) as [[Ha1 Ha2] _].
  assert (Hab : - (PI / 2) < a /\ a < PI / 2) by (unfold a; split; assumption).
  pose proof PI_RGT_0 as Hpi.
  set (room := Rmin ((PI / 2 - a) / 2) ((a + PI / 2) / 2)).
  assert (Hroom : 0 < room).
  { unfold room. apply Rmin_glb_lt; destruct Hab as [Hlo Hhi]; lra. }
  set (eps' := Rmin eps room).
  assert (Heps' : 0 < eps').
  { unfold eps'. apply Rmin_glb_lt; assumption. }
  assert (HbandL : - PI / 2 < a - eps').
  { assert (eps' <= (a + PI / 2) / 2).
    { apply Rle_trans with room; [apply Rmin_r | unfold room; apply Rmin_r]. }
    lra. }
  assert (HbandR : a + eps' < PI / 2).
  { assert (eps' <= (PI / 2 - a) / 2).
    { apply Rle_trans with room; [apply Rmin_r | unfold room; apply Rmin_l]. }
    lra. }
  set (lo := tan (a - eps')).
  set (hi := tan (a + eps')).
  assert (Hlu : lo < u0).
  { unfold lo. rewrite <- (tan_atan3 u0). fold a. apply tan_lt_open; lra. }
  assert (Huh : u0 < hi).
  { unfold hi. rewrite <- (tan_atan3 u0). fold a. apply tan_lt_open; lra. }
  set (delta := Rmin (u0 - lo) (hi - u0)).
  assert (Hdelta : 0 < delta) by (unfold delta; apply Rmin_glb_lt; lra).
  exists delta. split; [exact Hdelta|].
  intros y [_ Hd].
  unfold R_met in Hd; simpl in Hd; unfold Rdist in Hd.
  assert (Hloy : lo < y).
  { assert (Rabs (y - u0) < u0 - lo) by (eapply Rlt_le_trans; [exact Hd | apply Rmin_l]).
    apply Rabs_def2 in H. lra. }
  assert (Hhiy : y < hi).
  { assert (Rabs (y - u0) < hi - u0) by (eapply Rlt_le_trans; [exact Hd | apply Rmin_r]).
    apply Rabs_def2 in H. lra. }
  assert (Halo : atan3 lo = a - eps').
  { unfold lo. rewrite atan3_tan; [reflexivity | lra]. }
  assert (Hahi : atan3 hi = a + eps').
  { unfold hi. rewrite atan3_tan; [reflexivity | lra]. }
  assert (Hord : a - eps' < atan3 y < a + eps').
  { split.
    - rewrite <- Halo. apply atan3_lt. exact Hloy.
    - rewrite <- Hahi. apply atan3_lt. exact Hhiy. }
  assert (Habs : - eps < atan3 y - a < eps).
  { assert (eps' <= eps) by (unfold eps'; apply Rmin_l). lra. }
  destruct Habs as [Hl Hr].
  unfold R_met. simpl. unfold Rdist. fold a.
  apply Rabs_def1; assumption.
Qed.

Lemma sin_approx_1 : forall a, sin_approx a 1 = a - a * a * a / 6.
Proof. intro a. unfold sin_approx, sin_term. simpl. field. Qed.

Lemma cos_approx_2 : forall a, cos_approx a 2 = 1 - a ^ 2 / 2 + a ^ 4 / 24.
Proof. intro a. unfold cos_approx, cos_term. simpl. unfold Rdiv. field. Qed.

Lemma tan_gt_arg : forall a, 0 < a <= PI / 4 -> a < tan a.
Proof.
  intros a [Ha0 Ha1].
  pose proof PI_4 as Hpi4.
  assert (Ha4 : a <= 4) by lra.
  assert (Ha2 : a <= 2) by lra.
  destruct (pre_sin_bound a 0 (Rlt_le _ _ Ha0) Ha4) as [Hsl _].
  rewrite sin_approx_1 in Hsl.
  destruct (pre_cos_bound a 0 ltac:(lra) Ha2) as [_ Hcu].
  rewrite cos_approx_2 in Hcu.
  assert (Hgap : 0 < sin a - a * cos a).
  { apply Rlt_le_trans with
      ((a - a * a * a / 6) - a * (1 - a ^ 2 / 2 + a ^ 4 / 24)).
    - replace ((a - a * a * a / 6) - a * (1 - a ^ 2 / 2 + a ^ 4 / 24))
        with (a ^ 3 * (1 / 3 - a ^ 2 / 24)) by field.
      apply Rmult_lt_0_compat.
      + apply pow_lt. exact Ha0.
      + assert (Haa : a * a <= (PI / 4) * (PI / 4)).
        { apply Rmult_le_compat; lra. }
        assert (Hpi1 : PI / 4 <= 1).
        { apply (Rmult_le_reg_r 4); [lra|]. unfold Rdiv.
          rewrite Rmult_assoc. rewrite Rinv_l by lra.
          rewrite Rmult_1_l. rewrite Rmult_1_r. exact Hpi4. }
        assert (Hsq : (PI / 4) * (PI / 4) <= 1).
        { apply Rle_trans with ((PI / 4) * 1).
          - apply Rmult_le_compat_l; [pose proof PI_RGT_0; lra | exact Hpi1].
          - rewrite Rmult_1_r. exact Hpi1. }
        assert (a * a <= 1) by lra.
        replace (a ^ 2) with (a * a) by (simpl; ring).
        unfold Rdiv. lra.
    - apply Rplus_le_compat.
      + exact Hsl.
      + apply Ropp_le_contravar. apply Rmult_le_compat_l; lra. }
  pose proof (cos_gt_0 a ltac:(lra) ltac:(pose proof PI_RGT_0; lra)) as Hc.
  unfold tan. apply (Rmult_lt_reg_r (cos a)); [exact Hc|].
  unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l by lra. rewrite Rmult_1_r.
  lra.
Qed.

Lemma continuity_pt_sqr_sum : forall (u v : R -> R) t,
  continuity_pt u t -> continuity_pt v t ->
  continuity_pt (fun s => u s * u s + v s * v s) t.
Proof.
  intros u v t Hu Hv.
  apply continuity_pt_plus; apply continuity_pt_mult; assumption.
Qed.

Lemma continuity_pt_radius : forall (u v : R -> R) t,
  continuity_pt u t -> continuity_pt v t ->
  continuity_pt (fun s => sqrt (u s * u s + v s * v s)) t.
Proof.
  intros u v t Hu Hv.
  apply (continuity_pt_comp (fun s => u s * u s + v s * v s) sqrt).
  - apply continuity_pt_sqr_sum; assumption.
  - apply continuity_pt_sqrt.
    pose proof (sqr_nonneg (u t)) as Hsu. pose proof (sqr_nonneg (v t)) as Hsv. lra.
Qed.

Lemma atan2_formula : forall y x,
  0 < sqrt (x * x + y * y) + x ->
  atan2 y x = 2 * atan3 (y / (sqrt (x * x + y * y) + x)).
Proof.
  intros y x H. unfold atan2.
  destruct (Rlt_dec 0 (sqrt (x * x + y * y) + x)) as [_|Hn]; [reflexivity | lra].
Qed.

Lemma cont_half_nbhd : forall (f : R -> R) t,
  continuity_pt f t ->
  exists alp, 0 < alp /\ forall s, Rdist s t < alp ->
    Rabs (f s - f t) < Rabs (f t) / 2 + 1.
Proof.
  intros f t Hc.
  unfold continuity_pt, continue_in, limit1_in, limit_in in Hc.
  assert (Heps : 0 < Rabs (f t) / 2 + 1) by (pose proof (Rabs_pos (f t)); lra).
  destruct (Hc (Rabs (f t) / 2 + 1) Heps) as [alp [Halp Hn]].
  exists alp. split; [exact Halp|].
  intros s Hs.
  destruct (Req_dec s t) as [Eq|Neq].
  - subst. rewrite Rminus_diag. rewrite Rabs_R0. exact Heps.
  - apply Hn. split; [split; [exact I | apply not_eq_sym; exact Neq] | exact Hs].
Qed.

Lemma cont_pos_nbhd : forall (f : R -> R) t,
  continuity_pt f t -> 0 < f t ->
  exists alp, 0 < alp /\ forall s, Rdist s t < alp -> f t / 2 < f s.
Proof.
  intros f t Hc Hp.
  unfold continuity_pt, continue_in, limit1_in, limit_in in Hc.
  destruct (Hc (f t / 2) ltac:(lra)) as [alp [Halp Hn]].
  exists alp. split; [exact Halp|].
  intros s Hs.
  destruct (Req_dec s t) as [Eq|Neq].
  - subst. lra.
  - assert (H : Rlimit.dist R_met (f s) (f t) < f t / 2).
    { apply Hn. split; [split; [exact I | apply not_eq_sym; exact Neq] | exact Hs]. }
    unfold R_met in H; simpl in H; unfold Rdist in H. apply Rabs_def2 in H. lra.
Qed.

Lemma cont_neg_nbhd : forall (f : R -> R) t,
  continuity_pt f t -> f t < 0 ->
  exists alp, 0 < alp /\ forall s, Rdist s t < alp -> f s < f t / 2.
Proof.
  intros f t Hc Hp.
  unfold continuity_pt, continue_in, limit1_in, limit_in in Hc.
  destruct (Hc (- f t / 2) ltac:(lra)) as [alp [Halp Hn]].
  exists alp. split; [exact Halp|].
  intros s Hs.
  destruct (Req_dec s t) as [Eq|Neq].
  - subst. lra.
  - assert (H : Rlimit.dist R_met (f s) (f t) < - f t / 2).
    { apply Hn. split; [split; [exact I | apply not_eq_sym; exact Neq] | exact Hs]. }
    unfold R_met in H; simpl in H; unfold Rdist in H. apply Rabs_def2 in H. lra.
Qed.

Lemma px_lerp_cont : forall P Q t,
  continuity_pt (fun s => px (lerp P Q s)) t.
Proof.
  intros P Q t.
  eapply continuity_pt_locally_ext with
    (f := fun s => px P + s * (px Q - px P)) (a := 1).
  - lra.
  - intros y _. unfold lerp. cbn. ring.
  - apply continuity_pt_affine.
Qed.

Lemma py_lerp_cont : forall P Q t,
  continuity_pt (fun s => py (lerp P Q s)) t.
Proof.
  intros P Q t.
  eapply continuity_pt_locally_ext with
    (f := fun s => py P + s * (py Q - py P)) (a := 1).
  - lra.
  - intros y _. unfold lerp. cbn. ring.
  - apply continuity_pt_affine.
Qed.

Lemma vcross_path_cont : forall P Q A B t,
  continuity_pt (fun s => vcross (lerp P Q s) A B) t.
Proof.
  intros P Q A B t.
  eapply continuity_pt_locally_ext with
    (f := fun s => vcross P A B + s * (vcross Q A B - vcross P A B)) (a := 1).
  - lra.
  - intros y _. symmetry. apply vcross_lerp_affine.
  - apply continuity_pt_affine.
Qed.

Lemma vdot_path_cont : forall P Q A B t,
  continuity_pt (fun s => vdot (lerp P Q s) A B) t.
Proof.
  intros P Q A B t. unfold vdot, dx, dy.
  apply continuity_pt_plus.
  - apply continuity_pt_mult.
    + apply continuity_pt_minus.
      * apply continuity_pt_const. intros ? ?. reflexivity.
      * apply px_lerp_cont.
    + apply continuity_pt_minus.
      * apply continuity_pt_const. intros ? ?. reflexivity.
      * apply px_lerp_cont.
  - apply continuity_pt_mult.
    + apply continuity_pt_minus.
      * apply continuity_pt_const. intros ? ?. reflexivity.
      * apply py_lerp_cont.
    + apply continuity_pt_minus.
      * apply continuity_pt_const. intros ? ?. reflexivity.
      * apply py_lerp_cont.
Qed.

Lemma dist_sq_lerp_cont : forall C P Q t,
  continuity_pt (fun s => dist_sq C (lerp P Q s)) t.
Proof.
  intros C P Q t. unfold dist_sq.
  apply continuity_pt_plus; apply continuity_pt_mult;
    apply continuity_pt_minus.
  - apply continuity_pt_const. intros ? ?. reflexivity.
  - apply px_lerp_cont.
  - apply continuity_pt_const. intros ? ?. reflexivity.
  - apply px_lerp_cont.
  - apply continuity_pt_const. intros ? ?. reflexivity.
  - apply py_lerp_cont.
  - apply continuity_pt_const. intros ? ?. reflexivity.
  - apply py_lerp_cont.
Qed.

Lemma rplus_vdot_off_cut : forall X A B,
  A <> X -> B <> X -> ~ on_open_chord X A B ->
  0 < sqrt (vdot X A B * vdot X A B + vcross X A B * vcross X A B) + vdot X A B.
Proof.
  intros X A B HA HB Hcut.
  pose proof (atan2_r_plus_x_nonneg (vdot X A B) (vcross X A B)) as Hnn.
  destruct (Req_dec
    (sqrt (vdot X A B * vdot X A B + vcross X A B * vcross X A B) + vdot X A B) 0)
    as [Hz|Hnz].
  - destruct (atan2_r_plus_x_zero _ _ Hz) as [Hy Hx].
    destruct (Rle_lt_or_eq_dec _ _ Hx) as [Hlt|Heq].
    + exfalso. apply Hcut. split; lra.
    + exfalso. apply (dotcross_nz X A B HA HB). split; lra.
  - lra.
Qed.

Lemma chord_angle_path_cont : forall P Q A B t,
  A <> lerp P Q t -> B <> lerp P Q t ->
  ~ on_open_chord (lerp P Q t) A B ->
  continuity_pt (fun s => chord_angle (lerp P Q s) A B) t.
Proof.
  intros P Q A B t HA HB Hcut.
  set (y := fun s => vcross (lerp P Q s) A B).
  set (x := fun s => vdot (lerp P Q s) A B).
  assert (Hy : continuity_pt y t) by (unfold y; apply vcross_path_cont).
  assert (Hx : continuity_pt x t) by (unfold x; apply vdot_path_cont).
  assert (Hr : continuity_pt (fun s => sqrt (x s * x s + y s * y s)) t)
    by (apply continuity_pt_radius; assumption).
  assert (Hsum : continuity_pt (fun s => sqrt (x s * x s + y s * y s) + x s) t)
    by (apply continuity_pt_plus; assumption).
  assert (Hpos : 0 < sqrt (x t * x t + y t * y t) + x t).
  { unfold x, y. apply rplus_vdot_off_cut; assumption. }
  destruct (cont_pos_nbhd _ t Hsum Hpos) as [alp [Halp Hstay]].
  eapply continuity_pt_locally_ext with (a := alp).
  - exact Halp.
  - intros s Hs. apply eq_sym. apply atan2_formula.
    apply Rlt_trans with ((sqrt (x t * x t + y t * y t) + x t) / 2).
    + apply Rdiv_lt_0_compat; [exact Hpos | lra].
    + apply Hstay. exact Hs.
  - apply continuity_pt_scal.
    apply (continuity_pt_comp (fun s => y s / (sqrt (x s * x s + y s * y s) + x s)) atan3).
    + apply continuity_pt_div.
      * exact Hy.
      * exact Hsum.
      * lra.
    + apply atan3_continuous.
Qed.

Lemma ucross : forall p q, cos p * sin q - sin p * cos q = sin (q - p).
Proof. intros p q. rewrite sin_minus. ring. Qed.

Lemma arc_mid_orient_formula : forall c,
  orient_pts (circ_start c) (circ_end c) (circ_eval c (1 / 2)) =
    circ_r c * circ_r c *
      (2 * sin (circ_sweep c / 2) * (cos (circ_sweep c / 2) - 1)).
Proof.
  intro c.
  set (a := circ_theta0 c). set (s := circ_sweep c). set (r := circ_r c).
  set (Ox := px (circ_o c)). set (Oy := py (circ_o c)).
  unfold orient_pts, orient3, crs, circ_start, circ_end, circ_eval. cbn [px py].
  fold a s r Ox Oy.
  replace (a + 0 * s) with a by ring.
  replace (a + 1 * s) with (a + s) by ring.
  replace (a + 1 / 2 * s) with (a + s / 2) by field.
  set (ca0 := cos a). set (sa0 := sin a).
  set (ca1 := cos (a + s)). set (sa1 := sin (a + s)).
  set (cam := cos (a + s / 2)). set (sam := sin (a + s / 2)).
  replace ((Ox + r * ca1 - (Ox + r * ca0)) * (Oy + r * sam - (Oy + r * sa0)) -
           (Oy + r * sa1 - (Oy + r * sa0)) * (Ox + r * cam - (Ox + r * ca0)))
    with (r * r * ((ca1 - ca0) * (sam - sa0) - (sa1 - sa0) * (cam - ca0))) by ring.
  apply f_equal.
  replace ((ca1 - ca0) * (sam - sa0) - (sa1 - sa0) * (cam - ca0))
    with (ca1 * sam - sa1 * cam - (ca1 * sa0 - sa1 * ca0) - (ca0 * sam - sa0 * cam))
    by ring.
  unfold ca0, sa0, ca1, sa1, cam, sam.
  rewrite (ucross (a + s) (a + s / 2)).
  rewrite (ucross (a + s) a).
  rewrite (ucross a (a + s / 2)).
  replace (a + s / 2 - (a + s)) with (- (s / 2)) by field.
  replace (a - (a + s)) with (- s) by field.
  replace (a + s / 2 - a) with (s / 2) by field.
  rewrite !sin_neg.
  replace (sin s) with (sin (2 * (s / 2))) by (f_equal; field).
  rewrite sin_2a. field.
Qed.

Lemma cos_lt_one_open : forall a, - PI < a < PI -> a <> 0 -> cos a < 1.
Proof.
  intros a Ha Hn.
  replace a with (2 * (a / 2)) by field.
  rewrite cos_2a_sin.
  assert (Hs : sin (a / 2) <> 0).
  { intro Hz.
    destruct (Rtotal_order (a / 2) 0) as [Hlt|[Heq|Hgt]].
    - pose proof (sin_lt_0_var (a / 2) ltac:(lra) Hlt). lra.
    - apply Hn. lra.
    - pose proof (sin_gt_0 (a / 2) Hgt ltac:(lra)). lra. }
  assert (0 < sin (a / 2) * sin (a / 2)).
  { pose proof (sqr_nonneg (sin (a / 2))) as Hs2.
    assert (sin (a / 2) * sin (a / 2) <> 0).
    { intro E. apply Hs. apply sqr_eq_zero. exact E. }
    lra. }
  lra.
Qed.

Lemma sweep_sign_pm : forall c,
  circ_sweep c <> 0 -> sweep_sign c = 1%Z \/ sweep_sign c = (-1)%Z.
Proof.
  intros c Hs. unfold sweep_sign.
  destruct (Rlt_dec 0 (circ_sweep c)) as [Hp|Hp]; [left; reflexivity|].
  destruct (Rlt_dec (circ_sweep c) 0) as [Hn|Hn]; [right; reflexivity|].
  exfalso. apply Hs. lra.
Qed.

Lemma arc_mid_orient_sign : forall c,
  egg_arc_ok c ->
  (sweep_sign c = 1%Z /\
     orient_pts (circ_start c) (circ_end c) (circ_eval c (1 / 2)) < 0) \/
  (sweep_sign c = (-1)%Z /\
     0 < orient_pts (circ_start c) (circ_end c) (circ_eval c (1 / 2))).
Proof.
  intros c Hok.
  destruct Hok as [Hr [Hs [Hab [_ _]]]].
  rewrite arc_mid_orient_formula.
  set (a := circ_sweep c / 2).
  assert (Ha : a = circ_sweep c / 2) by reflexivity.
  assert (Hband : - PI < a < PI).
  { unfold a. destruct (Rabs_def2 _ _ Hab) as [Hhi Hlo].
    pose proof PI_RGT_0 as Hpi. split.
    - apply (Rmult_lt_reg_r 2); [lra|]. unfold Rdiv.
      rewrite Rmult_assoc. rewrite Rinv_l by lra. rewrite Rmult_1_r.
      replace (- PI * 2) with (- (2 * PI)) by ring. exact Hlo.
    - apply (Rmult_lt_reg_r 2); [lra|]. unfold Rdiv.
      rewrite Rmult_assoc. rewrite Rinv_l by lra. rewrite Rmult_1_r.
      replace (PI * 2) with (2 * PI) by ring. exact Hhi. }
  assert (Hnz : a <> 0).
  { unfold a. intro E. apply Hs.
    apply (Rmult_eq_compat_r 2) in E. unfold Rdiv in E.
    rewrite Rmult_assoc in E. rewrite Rinv_l in E by lra.
    rewrite Rmult_1_r in E. rewrite Rmult_0_l in E. exact E. }
  assert (Hcos : cos a < 1) by (apply cos_lt_one_open; assumption).
  assert (Hr2 : 0 < circ_r c * circ_r c).
  { pose proof (sqr_nonneg (circ_r c)) as Hnn.
    assert (circ_r c * circ_r c <> 0).
    { intro E. apply sqr_eq_zero in E. lra. }
    lra. }
  destruct (sweep_sign_pm c Hs) as [Hp|Hn].
  - left. split; [exact Hp|].
    unfold sweep_sign in Hp.
    destruct (Rlt_dec 0 (circ_sweep c)) as [Hsw|Hsw];
      [| destruct (Rlt_dec (circ_sweep c) 0); lia].
    assert (HaP : 0 < a < PI) by (unfold a; pose proof PI_RGT_0; lra).
    pose proof (sin_gt_0 a (proj1 HaP) (proj2 HaP)) as Hsin.
    assert (cos a - 1 < 0) by lra.
    assert (2 * sin a * (cos a - 1) < 0).
    { assert (0 < 2 * sin a) by (apply Rmult_lt_0_compat; lra).
      assert (0 < 2 * sin a * (1 - cos a)).
      { apply Rmult_lt_0_compat; [assumption | lra]. }
      lra. }
    assert (0 < circ_r c * circ_r c * (2 * sin a * (1 - cos a))).
    { apply Rmult_lt_0_compat; [exact Hr2 | lra]. }
    lra.
  - right. split; [exact Hn|].
    unfold sweep_sign in Hn.
    destruct (Rlt_dec 0 (circ_sweep c)) as [Hsw|Hsw]; [lia|].
    destruct (Rlt_dec (circ_sweep c) 0) as [Hneg|Hneg]; [| lia].
    assert (HaN : - PI < a < 0) by (unfold a; pose proof PI_RGT_0; lra).
    pose proof (sin_lt_0_var a (proj1 HaN) (proj2 HaN)) as Hsin.
    assert (cos a - 1 < 0) by lra.
    assert (0 < 2 * sin a * (cos a - 1)).
    { assert (2 * sin a < 0) by lra.
      assert (0 < - (2 * sin a) * (1 - cos a)).
      { apply Rmult_lt_0_compat; lra. }
      lra. }
    assert (0 < circ_r c * circ_r c * (2 * sin a * (cos a - 1))).
    { apply Rmult_lt_0_compat; [exact Hr2 | lra]. }
    lra.
Qed.

Lemma halfplane_affine : forall A B M P Q t,
  orient_pts A B M * orient_pts A B (lerp P Q t) =
    orient_pts A B M * orient_pts A B P +
    t * (orient_pts A B M * orient_pts A B Q -
         orient_pts A B M * orient_pts A B P).
Proof. intros. unfold lerp, orient_pts, orient3, crs. cbn. ring. Qed.

Lemma halfplane_path_cont : forall A B M P Q t,
  continuity_pt (fun s => orient_pts A B M * orient_pts A B (lerp P Q s)) t.
Proof.
  intros A B M P Q t.
  eapply continuity_pt_locally_ext with
    (f := fun s =>
       orient_pts A B M * orient_pts A B P +
       s * (orient_pts A B M * orient_pts A B Q -
            orient_pts A B M * orient_pts A B P))
    (a := 1).
  - lra.
  - intros y _. symmetry. apply halfplane_affine.
  - apply continuity_pt_affine.
Qed.

Lemma segment_b_true : forall c X,
  0 < orient_pts (circ_start c) (circ_end c) (circ_eval c (1 / 2)) *
      orient_pts (circ_start c) (circ_end c) X ->
  dist_sq (circ_o c) X < circ_r c * circ_r c ->
  in_circ_segment_b c X = true.
Proof.
  intros c X Hh Hd. unfold in_circ_segment_b.
  destruct (Rlt_dec 0 _) as [_|Hn]; [| exfalso; apply Hn; exact Hh].
  destruct (Rlt_dec _ _) as [_|Hn]; [| exfalso; apply Hn; exact Hd].
  reflexivity.
Qed.

Lemma segment_b_false_h : forall c X,
  orient_pts (circ_start c) (circ_end c) (circ_eval c (1 / 2)) *
  orient_pts (circ_start c) (circ_end c) X <= 0 ->
  in_circ_segment_b c X = false.
Proof.
  intros c X Hh. unfold in_circ_segment_b.
  destruct (Rlt_dec 0 _) as [Hp|Hp]; [lra | reflexivity].
Qed.

Lemma segment_b_false_d : forall c X,
  circ_r c * circ_r c <= dist_sq (circ_o c) X ->
  in_circ_segment_b c X = false.
Proof.
  intros c X Hd. unfold in_circ_segment_b.
  destruct (Rlt_dec 0 _) as [Hp|Hp]; [| reflexivity].
  destruct (Rlt_dec _ _) as [Hq|Hq]; [lra | reflexivity].
Qed.

Lemma tie_off_chord : forall c X,
  on_open_chord_b X (circ_start c) (circ_end c) = false ->
  chord_tie_k c X =
    if in_circ_segment_b c X then sweep_sign c else 0%Z.
Proof.
  intros c X Hb. unfold chord_tie_k. rewrite Hb. reflexivity.
Qed.

Lemma Rmin_pos : forall x y, 0 < x -> 0 < y -> 0 < Rmin x y.
Proof. intros x y Hx Hy. apply Rmin_glb_lt; assumption. Qed.


(* §4  Chord line meets the disk in the open chord. *)

Lemma dist_along_chord : forall c t,
  dist_sq (circ_o c)
    (shift (circ_start c)
       (mkPoint (px (circ_end c) - px (circ_start c))
                (py (circ_end c) - py (circ_start c))) t) =
  circ_r c * circ_r c -
    t * (1 - t) * dist_sq (circ_start c) (circ_end c).
Proof.
  intros c t.
  pose proof (circ_eval_dist_sq c 0) as HA.
  pose proof (circ_eval_dist_sq c 1) as HB.
  unfold dist_sq, shift, circ_start, circ_end, circ_eval in *.
  cbn [px py] in *.
  set (ox := px (circ_o c)) in *. set (oy := py (circ_o c)) in *.
  set (r := circ_r c) in *.
  set (th := circ_theta0 c) in *. set (s := circ_sweep c) in *.
  set (c0 := cos th) in *. set (s0 := sin th) in *.
  set (c1 := cos (th + s)) in *. set (s1 := sin (th + s)) in *.
  assert (E0 : c0 * c0 + s0 * s0 = 1).
  { pose proof (sin2_cos2 th) as E. unfold Rsqr in E. unfold c0, s0.
    rewrite <- E. ring. }
  assert (E1 : c1 * c1 + s1 * s1 = 1).
  { pose proof (sin2_cos2 (th + s)) as E. unfold Rsqr in E. unfold c1, s1.
    rewrite <- E. ring. }
  nsatz.
Qed.

Lemma line_chord_param : forall c X,
  egg_arc_ok c ->
  vcross X (circ_start c) (circ_end c) = 0 ->
  exists t,
    X = shift (circ_start c)
          (mkPoint (px (circ_end c) - px (circ_start c))
                   (py (circ_end c) - py (circ_start c))) t /\
    dist_sq (circ_o c) X =
      circ_r c * circ_r c
      - t * (1 - t) * dist_sq (circ_start c) (circ_end c).
Proof.
  intros c X Hok Hc.
  destruct Hok as [_ [_ [_ [HAB _]]]].
  rewrite vcross_orient in Hc.
  set (t := line_param (circ_start c) (circ_end c) X).
  exists t. split.
  - apply collinear_param; assumption.
  - replace X with (shift (circ_start c)
        (mkPoint (px (circ_end c) - px (circ_start c))
                 (py (circ_end c) - py (circ_start c))) t) at 1.
    + apply dist_along_chord.
    + symmetry. apply collinear_param; assumption.
Qed.

Lemma chord_sep_pos : forall c,
  egg_arc_ok c -> 0 < dist_sq (circ_start c) (circ_end c).
Proof.
  intros c Hok. destruct Hok as [_ [_ [_ [HAB _]]]].
  destruct (circ_start c) as [ax ay], (circ_end c) as [bx yb].
  unfold dist_sq. cbn. apply sum_sq_pos.
  destruct (Req_dec (ax - bx) 0) as [Hx|Hx]; [| left; exact Hx].
  right. intro Hy. apply HAB.
  assert (Eax : ax = bx) by lra. assert (Eay : ay = yb) by lra.
  rewrite Eax, Eay. reflexivity.
Qed.

Lemma param_open_from_disk : forall c X t,
  egg_arc_ok c ->
  X = shift (circ_start c)
        (mkPoint (px (circ_end c) - px (circ_start c))
                 (py (circ_end c) - py (circ_start c))) t ->
  dist_sq (circ_o c) X < circ_r c * circ_r c ->
  0 < t < 1.
Proof.
  intros c X t Hok HX Hd.
  pose proof (chord_sep_pos c Hok) as Hs.
  rewrite HX, dist_along_chord in Hd.
  assert (0 < t * (1 - t)).
  { apply (Rmult_lt_reg_r (dist_sq (circ_start c) (circ_end c))); [exact Hs|].
    lra. }
  destruct (Rlt_dec 0 t) as [Ht|Ht].
  - destruct (Rlt_dec t 1) as [H1|H1]; [lra|].
    assert (0 <= t * (t - 1)) by (apply Rmult_le_pos; lra).
    assert (t * (1 - t) = - (t * (t - 1))) by ring. lra.
  - assert (0 <= (- t) * (1 - t)) by (apply Rmult_le_pos; lra).
    assert (t * (1 - t) = - ((- t) * (1 - t))) by ring. lra.
Qed.

Lemma open_disk_on_chord : forall c X,
  egg_arc_ok c ->
  vcross X (circ_start c) (circ_end c) = 0 ->
  dist_sq (circ_o c) X < circ_r c * circ_r c ->
  on_open_chord X (circ_start c) (circ_end c).
Proof.
  intros c X Hok Hc Hd.
  destruct (line_chord_param c X Hok Hc) as [t [HX HD]].
  pose proof (param_open_from_disk c X t Hok HX Hd) as Ht.
  pose proof (chord_sep_pos c Hok) as Hs.
  split; [exact Hc|].
  rewrite HX. rewrite vdot_on_param.
  replace ((px (circ_end c) - px (circ_start c)) *
           (px (circ_end c) - px (circ_start c)) +
           (py (circ_end c) - py (circ_start c)) *
           (py (circ_end c) - py (circ_start c)))
    with (dist_sq (circ_start c) (circ_end c)) by (unfold dist_sq; ring).
  assert (0 < t * (1 - t) * dist_sq (circ_start c) (circ_end c)).
  { apply Rmult_lt_0_compat; [| exact Hs].
    destruct Ht as [H0 H1]. apply Rmult_lt_0_compat; lra. }
  lra.
Qed.

Lemma open_chord_inside : forall c X,
  egg_arc_ok c ->
  on_open_chord X (circ_start c) (circ_end c) ->
  dist_sq (circ_o c) X < circ_r c * circ_r c.
Proof.
  intros c X Hok Ho.
  destruct Ho as [Hc Hd].
  destruct (line_chord_param c X Hok Hc) as [t [HX HD]].
  rewrite HD.
  pose proof (chord_sep_pos c Hok) as Hs.
  rewrite HX in Hd. rewrite vdot_on_param in Hd.
  replace ((px (circ_end c) - px (circ_start c)) *
           (px (circ_end c) - px (circ_start c)) +
           (py (circ_end c) - py (circ_start c)) *
           (py (circ_end c) - py (circ_start c)))
    with (dist_sq (circ_start c) (circ_end c)) in Hd by (unfold dist_sq; ring).
  assert (0 < t * (1 - t)).
  { apply (Rmult_lt_reg_r (dist_sq (circ_start c) (circ_end c))); [exact Hs|].
    lra. }
  assert (0 < t * (1 - t) * dist_sq (circ_start c) (circ_end c)).
  { apply Rmult_lt_0_compat; assumption. }
  lra.
Qed.
