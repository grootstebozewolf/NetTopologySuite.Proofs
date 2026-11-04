(* ============================================================================
   NetTopologySuite.Proofs.ArcSectorExact
   ----------------------------------------------------------------------------
   Exact replacement for the oracle's atan2 sector test
   (oracle/driver.ml point_on_arc_sector, run_arc_distance; inventory row
   T4 in docs/transcendental-inventory.tsv).

   The driver decided "Q lies in the angular span of the arc A -> B -> C
   about its centre O" with atan2 and a CCW-offset comparison, inclusive at
   both end rays.  Here the same decision is made from the signs of cross
   and dot products of the offset vectors a = A - O, b = B - O, c = C - O,
   q = Q - O:
     asx_cone a c q   q lies in the closed CCW cone from ray a to ray c
                      (span < pi: x >= 0 /\ y >= 0; span > pi: x >= 0 \/
                      y >= 0; span = pi: x >= 0; zero span: q on ray a),
                      x = cross a q, y = cross q c;
     asx_sector       the arc runs CCW iff b is in asx_cone a c, else CW
                      (q in asx_cone c a); a and c on one ray is the full
                      circle (or a single ray when b is on it too).
   No angle, no transcendental: in Q it is exact (`asx_sector_q`).

   Spec of record.  `asx_sector_on_circle_iff` : for a valid arc and a point
   on its circumcircle, asx_sector = ArcIntersect.arc_span_contains (which
   ArcSpanAtan2.arc_span_contains_atan2_iff_chord_sign already equates with
   the atan2 sector test).  `asx_sector_radial_iff` : for any point other
   than the centre, asx_sector is arc_span_contains of its radial projection
   onto the circle -- the question ARC_DISTANCE asks.
   `asx_sector_q_correct` : the Q boolean is the R predicate on Q2R values.

   Proof: on the circle, cross a q = r^2 sin T, cross q c = r^2 sin (G - T),
   cross a c = r^2 sin G (T, G signed angles from a), so the cone is a sign
   condition on G, T, T - G; the chord orientation is
   r^2 * 4 sin (G/2) sin (T/2) sin ((T-G)/2) (ArcSpanAtan2), whose sign is
   that of G T (T - G).
   claimId: s0-t4-sector-exact.  witness: asx_sector_on_circle_iff.
   3-axiom host (atan2 enters only the proof, through AngleBetween).
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra QArith Qreals.
From NTS.Proofs Require Import Distance CurveGeometry ArcOrient ArcIntersect
  ArcOffsetThreePoint ArcArcCircles AngleBetween ArcSpanAtan2.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The predicate over R.                                                  *)
(* -------------------------------------------------------------------------- *)

Definition asx_cross (ux uy vx vy : R) : R := ux * vy - uy * vx.
Definition asx_dot (ux uy vx vy : R) : R := ux * vx + uy * vy.

(* Closed CCW cone from ray a to ray c, given s = cross a c, x = cross a q,
   y = cross q c, d = dot a c, e = dot a q. *)
Definition asx_cone_vals (s x y d e : R) : Prop :=
  (0 < s /\ 0 <= x /\ 0 <= y) \/
  (s < 0 /\ (0 <= x \/ 0 <= y)) \/
  (s = 0 /\ d < 0 /\ 0 <= x) \/
  (s = 0 /\ 0 <= d /\ x = 0 /\ 0 < e).

Definition asx_cone (ax ay cx cy qx qy : R) : Prop :=
  asx_cone_vals (asx_cross ax ay cx cy) (asx_cross ax ay qx qy)
    (asx_cross qx qy cx cy) (asx_dot ax ay cx cy) (asx_dot ax ay qx qy).

Definition asx_same_dir (ux uy vx vy : R) : Prop :=
  asx_cross ux uy vx vy = 0 /\ 0 < asx_dot ux uy vx vy.

Definition asx_sector (O A B C Q : Point) : Prop :=
  let ax := px A - px O in let ay := py A - py O in
  let bx := px B - px O in let by_ := py B - py O in
  let cx := px C - px O in let cy := py C - py O in
  let qx := px Q - px O in let qy := py Q - py O in
  (asx_same_dir ax ay cx cy /\
     ((asx_same_dir ax ay bx by_ /\ asx_same_dir ax ay qx qy)
      \/ ~ asx_same_dir ax ay bx by_)) \/
  (~ asx_same_dir ax ay cx cy /\
     ((asx_cone ax ay cx cy bx by_ /\ asx_cone ax ay cx cy qx qy)
      \/ (~ asx_cone ax ay cx cy bx by_ /\ asx_cone cx cy ax ay qx qy))).

Lemma asx_cone_vals_scale : forall k s x y d e, 0 < k ->
  asx_cone_vals (k * s) (k * x) (k * y) (k * d) (k * e)
  <-> asx_cone_vals s x y d e.
Proof.
  intros k s x y d e Hk.
  assert (P : forall z, 0 < k * z <-> 0 < z) by (intro z; split; intro; nra).
  assert (N : forall z, k * z < 0 <-> z < 0) by (intro z; split; intro; nra).
  assert (L : forall z, 0 <= k * z <-> 0 <= z) by (intro z; split; intro; nra).
  assert (Z : forall z, k * z = 0 <-> z = 0)
    by (intro z; split; intro H; [nra | subst; ring]).
  unfold asx_cone_vals. rewrite !P, !N, !L, !Z. tauto.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The cone as a sign condition on signed angles.                         *)
(* -------------------------------------------------------------------------- *)

Lemma asx_sin_pos : forall t, 0 < t < PI -> 0 < sin t.
Proof. intros t Ht. apply sin_gt_0; lra. Qed.

Lemma asx_sin_neg : forall t, - PI < t < 0 -> sin t < 0.
Proof. intros t Ht. apply sin_lt_0_var; lra. Qed.

Lemma asx_sin_nonneg : forall t, 0 <= t <= PI -> 0 <= sin t.
Proof. intros t Ht. apply sin_ge_0; lra. Qed.

(* For G in (-pi, pi] \ {0} and T in (-pi, pi]:
   T is in the closed CCW cone from 0 to G  <->  T = 0, T = G, or
   G T (T - G) < 0. *)
Lemma asx_cone_angles : forall G T,
  - PI < G <= PI -> G <> 0 -> - PI < T <= PI ->
  (asx_cone_vals (sin G) (sin T) (sin (G - T)) (cos G) (cos T)
   <-> (T = 0 \/ T = G \/ G * T * (T - G) < 0)).
Proof.
  intros G T HG HG0 HT.
  pose proof PI_RGT_0 as Hpi.
  unfold asx_cone_vals.
  destruct (Rlt_le_dec G PI) as [HGlt|HGpi].
  - destruct (Rlt_le_dec 0 G) as [HGp|HGn].
    + (* 0 < G < pi : sin G > 0 *)
      assert (SG : 0 < sin G) by (apply asx_sin_pos; lra).
      destruct (Rlt_le_dec T 0) as [HTn|HTp].
      * assert (ST : sin T < 0) by (apply asx_sin_neg; lra).
        split.
        -- intros [H|[H|[H|H]]]; lra.
        -- intros [H|[H|H]]; [lra|lra|].
           assert (0 < G * T * (T - G)).
           { replace (G * T * (T - G)) with (G * ((- T) * (G - T))) by ring.
             apply Rmult_lt_0_compat; [lra|]. apply Rmult_lt_0_compat; lra. }
           lra.
      * destruct (Rle_lt_dec T G) as [HTG|HTG].
        -- assert (ST : 0 <= sin T) by (apply asx_sin_nonneg; lra).
           assert (SGT : 0 <= sin (G - T)) by (apply asx_sin_nonneg; lra).
           split.
           ++ intros _. destruct (Req_dec T 0) as [->|HT0]; [left; reflexivity|].
              destruct (Req_dec T G) as [->|HTG']; [right; left; reflexivity|].
              right; right.
              assert (0 < G * T * (G - T))
                by (apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat|]; lra).
              lra.
           ++ intros _. left. split; [exact SG|]. split; assumption.
        -- split.
           ++ intros [H|[H|[H|H]]]; [|lra|lra|lra].
              assert (sin (G - T) < 0) by (apply asx_sin_neg; lra). lra.
           ++ intros [H|[H|H]]; [lra|lra|].
              assert (0 < G * T * (T - G)).
              { apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat|]; lra. }
              lra.
    + (* -pi < G < 0 : sin G < 0 *)
      assert (HGn' : G < 0) by lra.
      assert (SG : sin G < 0) by (apply asx_sin_neg; lra).
      destruct (Rle_lt_dec 0 T) as [HTp|HTn].
      * assert (ST : 0 <= sin T) by (apply asx_sin_nonneg; lra).
        split.
        -- intros _. destruct (Req_dec T 0) as [->|HT0]; [left; auto|].
           right; right.
           assert (0 < (- G) * T * (T - G))
             by (apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat|]; lra).
           lra.
        -- intros _. right; left. split; [exact SG|]. left; exact ST.
      * assert (ST : sin T < 0) by (apply asx_sin_neg; lra).
        destruct (Rle_lt_dec T G) as [HTG|HTG].
        -- assert (SGT : 0 <= sin (G - T)) by (apply asx_sin_nonneg; lra).
           split.
           ++ intros _. destruct (Req_dec T G) as [->|HTG']; [right; left; auto|].
              right; right.
              assert (0 < G * T * (G - T)).
              { replace (G * T * (G - T)) with ((- G) * (- T) * (G - T)) by ring.
                apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat|]; lra. }
              lra.
           ++ intros _. right; left. split; [exact SG|]. right; exact SGT.
        -- assert (SGT : sin (G - T) < 0) by (apply asx_sin_neg; lra).
           split.
           ++ intros [H|[H|[H|H]]]; lra.
           ++ intros [H|[H|H]]; [lra|lra|].
              assert (0 < G * T * (T - G)).
              { replace (G * T * (T - G)) with ((- G) * (- T) * (T - G)) by ring.
                apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat|]; lra. }
              lra.
  - (* G = pi *)
    assert (EG : G = PI) by lra. subst G.
    rewrite sin_PI, cos_PI.
    destruct (Rle_lt_dec 0 T) as [HTp|HTn].
    + assert (ST : 0 <= sin T) by (apply asx_sin_nonneg; lra).
      split.
      * intros _. destruct (Req_dec T 0) as [->|HT0]; [left; auto|].
        destruct (Req_dec T PI) as [->|HTpi]; [right; left; auto|].
        right; right.
        assert (0 < PI * T * (PI - T))
          by (apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat|]; lra).
        lra.
      * intros _. right; right; left. split; [reflexivity|]. split; lra.
    + assert (ST : sin T < 0) by (apply asx_sin_neg; lra).
      split.
      * intros [H|[H|[H|H]]]; lra.
      * intros [H|[H|H]]; [lra|lra|].
        assert (0 < PI * (- T) * (PI - T))
          by (apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat|]; lra).
        lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  On the circle: cross / dot in terms of the signed angles.              *)
(* -------------------------------------------------------------------------- *)

Lemma asx_dot_r2_eq : forall ux uy vx vy r,
  ux * ux + uy * uy = r * r -> vx * vx + vy * vy = r * r ->
  asx_dot ux uy vx vy = r * r -> ux = vx /\ uy = vy.
Proof.
  intros ux uy vx vy r Hu Hv Hd. unfold asx_dot in Hd.
  assert (Z : (ux - vx) * (ux - vx) + (uy - vy) * (uy - vy) = 0) by nra.
  pose proof (sqr_nonneg (ux - vx)). pose proof (sqr_nonneg (uy - vy)).
  assert (Zx : (ux - vx) * (ux - vx) = 0) by lra.
  assert (Zy : (uy - vy) * (uy - vy) = 0) by lra.
  apply sqr_eq_zero in Zx. apply sqr_eq_zero in Zy. split; lra.
Qed.

Lemma asx_norm_sq : forall O X r, dist_sq O X = r * r ->
  (px X - px O) * (px X - px O) + (py X - py O) * (py X - py O) = r * r.
Proof. intros O X r H. unfold dist_sq in H. lra. Qed.

Lemma asx_on_circle_values : forall (O A C P : Point) (r : R),
  0 < r ->
  dist_sq O A = r * r -> dist_sq O C = r * r -> dist_sq O P = r * r ->
  let G := signed_angle_from O A C in
  let T := signed_angle_from O A P in
  let ax := px A - px O in let ay := py A - py O in
  let cx := px C - px O in let cy := py C - py O in
  let qx := px P - px O in let qy := py P - py O in
  asx_cross ax ay cx cy = r * r * sin G /\
  asx_cross ax ay qx qy = r * r * sin T /\
  asx_cross qx qy cx cy = r * r * sin (G - T) /\
  asx_dot ax ay cx cy = r * r * cos G /\
  asx_dot ax ay qx qy = r * r * cos T /\
  asx_dot cx cy qx qy * (r * r) = r * r * (r * r) * cos (G - T).
Proof.
  intros O A C P r Hr HA HC HP G T ax ay cx cy qx qy.
  assert (HuA := on_circle_vec_nonzero O A r Hr HA).
  assert (HuC := on_circle_vec_nonzero O C r Hr HC).
  assert (HuP := on_circle_vec_nonzero O P r Hr HP).
  assert (SA := on_circle_sqrt_offset O A r Hr HA).
  assert (SC := on_circle_sqrt_offset O C r Hr HC).
  assert (SP := on_circle_sqrt_offset O P r Hr HP).
  assert (Hrr : r * r <> 0) by (apply Rgt_not_eq, Rmult_lt_0_compat; lra).
  pose proof (sin_angle_between _ _ _ _ HuA HuC) as sG.
  pose proof (cos_angle_between _ _ _ _ HuA HuC) as cG.
  pose proof (sin_angle_between _ _ _ _ HuA HuP) as sT.
  pose proof (cos_angle_between _ _ _ _ HuA HuP) as cT.
  rewrite SA, SC in sG, cG. rewrite SA, SP in sT, cT.
  fold ax ay cx cy qx qy in sG, cG, sT, cT.
  change (angle_between ax ay cx cy) with G in sG, cG.
  change (angle_between ax ay qx qy) with T in sT, cT.
  assert (E1 : asx_cross ax ay cx cy = r * r * sin G)
    by (rewrite sG; unfold asx_cross; field; lra).
  assert (E2 : asx_cross ax ay qx qy = r * r * sin T)
    by (rewrite sT; unfold asx_cross; field; lra).
  assert (E4 : asx_dot ax ay cx cy = r * r * cos G)
    by (rewrite cG; unfold asx_dot; field; lra).
  assert (E5 : asx_dot ax ay qx qy = r * r * cos T)
    by (rewrite cT; unfold asx_dot; field; lra).
  assert (Na : ax * ax + ay * ay = r * r) by (apply asx_norm_sq; exact HA).
  split; [exact E1|]. split; [exact E2|].
  split.
  - (* Lagrange: dot(a,q) cross(a,c) - dot(a,c) cross(a,q) = cross(q,c) |a|^2 *)
    assert (L : asx_dot ax ay qx qy * asx_cross ax ay cx cy
                - asx_dot ax ay cx cy * asx_cross ax ay qx qy
                = asx_cross qx qy cx cy * (ax * ax + ay * ay))
      by (unfold asx_dot, asx_cross; ring).
    rewrite E1, E2, E4, E5, Na in L. rewrite sin_minus.
    apply Rmult_eq_reg_r with (r * r); [|exact Hrr].
    rewrite <- L. ring.
  - split; [exact E4|]. split; [exact E5|].
    assert (L : asx_dot ax ay cx cy * asx_dot ax ay qx qy
                + asx_cross ax ay cx cy * asx_cross ax ay qx qy
                = asx_dot cx cy qx qy * (ax * ax + ay * ay))
      by (unfold asx_dot, asx_cross; ring).
    rewrite E1, E2, E4, E5, Na in L. rewrite cos_minus.
    rewrite <- L. ring.
Qed.

Lemma asx_same_sign_neg_iff : forall x y, same_sign x y -> (x < 0 <-> y < 0).
Proof. intros x y H. unfold same_sign in H. lra. Qed.

Lemma asx_same_sign_nz : forall x y, same_sign x y -> x <> 0 -> y <> 0.
Proof. intros x y H Hx. unfold same_sign in H. lra. Qed.

(* Off the end points, the cone on the circle is the chord orientation. *)
Lemma asx_cone_on_circle : forall (O A C P : Point) (r : R),
  0 < r ->
  dist_sq O A = r * r -> dist_sq O C = r * r -> dist_sq O P = r * r ->
  ~ (px A = px C /\ py A = py C) ->
  ~ (px P = px A /\ py P = py A) -> ~ (px P = px C /\ py P = py C) ->
  (asx_cone (px A - px O) (py A - py O) (px C - px O) (py C - py O)
            (px P - px O) (py P - py O)
   <-> cross_R_pt A C P < 0) /\ cross_R_pt A C P <> 0.
Proof.
  intros O A C P r Hr HA HC HP HAC HPA HPC.
  destruct (asx_on_circle_values O A C P r Hr HA HC HP)
    as [E1 [E2 [E3 [E4 [E5 E6]]]]].
  set (G := signed_angle_from O A C) in *.
  set (T := signed_angle_from O A P) in *.
  assert (HuA := on_circle_vec_nonzero O A r Hr HA).
  assert (HuC := on_circle_vec_nonzero O C r Hr HC).
  assert (HuP := on_circle_vec_nonzero O P r Hr HP).
  assert (HGr : - PI < G <= PI) by (apply angle_between_range; assumption).
  assert (HTr : - PI < T <= PI) by (apply angle_between_range; assumption).
  assert (HG0 : G <> 0).
  { intro H0. apply HAC.
    exact (on_circle_same_direction_eq O A C r Hr HA HC H0). }
  assert (HT0 : T <> 0).
  { intro H0. apply HPA.
    destruct (on_circle_same_direction_eq O A P r Hr HA HP H0) as [H1 H2].
    split; symmetry; assumption. }
  assert (HTG : T <> G).
  { intro H0. apply HPC.
    assert (Hrr : 0 < r * r) by (apply Rmult_lt_0_compat; lra).
    assert (D : asx_dot (px C - px O) (py C - py O) (px P - px O) (py P - py O)
                = r * r).
    { apply Rmult_eq_reg_r with (r * r); [|clear - Hrr; lra].
      rewrite E6, H0, Rminus_diag, cos_0. ring. }
    destruct (asx_dot_r2_eq _ _ _ _ r (asx_norm_sq O C r HC) (asx_norm_sq O P r HP) D)
      as [Dx Dy].
    clear - Dx Dy. split; lra. }
  assert (Hrr : 0 < r * r) by (apply Rmult_lt_0_compat; lra).
  (* the cone *)
  assert (Hcone : asx_cone (px A - px O) (py A - py O) (px C - px O) (py C - py O)
                    (px P - px O) (py P - py O)
                  <-> G * T * (T - G) < 0).
  { unfold asx_cone. rewrite E1, E2, E3, E4, E5.
    rewrite (asx_cone_vals_scale (r * r) _ _ _ _ _ Hrr).
    rewrite (asx_cone_angles G T HGr HG0 HTr).
    split; [intros [H|[H|H]]; [contradiction|contradiction|exact H]
           |intro H; right; right; exact H]. }
  (* the chord orientation *)
  assert (Hside : cross_R_pt A C P
                  = r * r * (4 * sin (G / 2) * sin (T / 2) * sin ((T - G) / 2))).
  { rewrite (cross_on_circle_value O A C P r Hr HA HC HP).
    fold G T. rewrite (sin_sum_to_product T G). ring. }
  clear E1 E2 E3 E4 E5 E6 HuA HuC HuP HA HC HP HAC HPA HPC.
  assert (S1 := sign_match_sin_half G ltac:(pose proof PI_RGT_0; lra)).
  assert (S2 := sign_match_sin_half T ltac:(pose proof PI_RGT_0; lra)).
  assert (S3 := sign_match_sin_half (T - G) ltac:(pose proof PI_RGT_0; lra)).
  assert (S := same_sign_mult _ _ _ _ (same_sign_mult _ _ _ _ S1 S2) S3).
  assert (Hnz : G * T * (T - G) <> 0).
  { intro H0. apply Rmult_integral in H0. destruct H0 as [H0|H0]; [|lra].
    apply Rmult_integral in H0. destruct H0; contradiction. }
  assert (HsinNz := asx_same_sign_nz _ _ S Hnz).
  set (X := sin (G / 2) * sin (T / 2) * sin ((T - G) / 2)) in *.
  assert (Hside' : cross_R_pt A C P = (r * r * 4) * X)
    by (rewrite Hside; unfold X; ring).
  assert (Hk : 0 < r * r * 4) by (apply Rmult_lt_0_compat; [exact Hrr | lra]).
  clear Hside S1 S2 S3.
  split.
  - rewrite Hcone, Hside', (asx_same_sign_neg_iff _ _ S).
    split; intro H.
    + apply Rmult_lt_reg_l with (/ (r * r * 4)); [apply Rinv_0_lt_compat; lra|].
      rewrite Rmult_0_r, <- Rmult_assoc, Rinv_l by lra. lra.
    + destruct (Rlt_le_dec X 0) as [HX|HX]; [exact HX|].
      assert (0 <= (r * r * 4) * X) by (apply Rmult_le_pos; lra). lra.
  - rewrite Hside'. intro H0.
    apply Rmult_integral in H0. destruct H0 as [H0|H0]; [lra|].
    apply HsinNz. exact H0.
Qed.

(* The cone contains its two end rays (nonzero, non-orthogonal-degenerate
   vectors: a and c nonzero). *)
Lemma asx_cone_ends : forall ax ay cx cy,
  ~ (ax = 0 /\ ay = 0) -> ~ (cx = 0 /\ cy = 0) ->
  asx_cone ax ay cx cy ax ay /\ asx_cone ax ay cx cy cx cy.
Proof.
  intros ax ay cx cy Ha Hc.
  assert (Pa : 0 < ax * ax + ay * ay) by (apply sum_sq_pos; exact Ha).
  assert (Pc : 0 < cx * cx + cy * cy) by (apply sum_sq_pos; exact Hc).
  assert (Lg : asx_dot ax ay cx cy * asx_dot ax ay cx cy
               + asx_cross ax ay cx cy * asx_cross ax ay cx cy
               = (ax * ax + ay * ay) * (cx * cx + cy * cy))
    by (unfold asx_dot, asx_cross; ring).
  unfold asx_cone, asx_cone_vals.
  replace (asx_cross ax ay ax ay) with 0 by (unfold asx_cross; ring).
  replace (asx_cross cx cy cx cy) with 0 by (unfold asx_cross; ring).
  replace (asx_cross ax ay cx cy) with (asx_cross ax ay cx cy) by reflexivity.
  set (s := asx_cross ax ay cx cy) in *.
  set (d := asx_dot ax ay cx cy) in *.
  replace (asx_dot ax ay ax ay) with (ax * ax + ay * ay) by (unfold asx_dot; ring).
  assert (Ecq : asx_cross ax ay cx cy = s) by reflexivity.
  destruct (Rtotal_order 0 s) as [Hs|[Hs|Hs]].
  - split; left; repeat split; lra.
  - assert (Hd : d <> 0).
    { intro H0. rewrite <- Hs, H0 in Lg.
      assert (0 < (ax * ax + ay * ay) * (cx * cx + cy * cy))
        by (apply Rmult_lt_0_compat; assumption).
      lra. }
    destruct (Rlt_le_dec d 0) as [Hdn|Hdp].
    + split; right; right; left; repeat split; lra.
    + split; right; right; right; repeat split; lra.
  - split; right; left; (split; [lra|]); [left; lra | right; lra].
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Headline: on the circumcircle the exact sector is arc_span_contains.   *)
(* -------------------------------------------------------------------------- *)

Lemma asx_pt_eq : forall p q : Point, p = q <-> (px p = px q /\ py p = py q).
Proof.
  intros [x1 y1] [x2 y2]. cbn. split.
  - intro H. inversion H. split; reflexivity.
  - intros [-> ->]. reflexivity.
Qed.




(* The case analysis of the headline, as pure logic over the facts. *)
Lemma asx_sector_logic :
  forall (SDac SDab SDaq CB CP CP' EA EC : Prop) (sB sP : R),
    (EA \/ ~ EA) -> (EC \/ ~ EC) ->
    ~ SDac -> (CB <-> sB < 0) -> sB <> 0 ->
    (EA \/ EC -> CP /\ CP') ->
    (~ EA -> ~ EC -> (CP <-> sP < 0) /\ (CP' <-> 0 < sP) /\ sP <> 0) ->
    ((SDac /\ ((SDab /\ SDaq) \/ ~ SDab)) \/
     (~ SDac /\ ((CB /\ CP) \/ (~ CB /\ CP'))))
    <-> (0 < sB * sP \/ EA \/ EC).
Proof.
  intros SDac SDab SDaq CB CP CP' EA EC sB sP DA DC Hnsd HCB HsB Hends Hin.
  destruct (Rlt_le_dec sB 0) as [HBn|HBp].
  - assert (HCBt : CB) by (apply HCB; exact HBn).
    destruct DA as [HA|HA]; [|destruct DC as [HC|HC]].
    + destruct (Hends (or_introl HA)). split; [intros _; right; left; exact HA|].
      intros _. right. split; [exact Hnsd|]. left; split; assumption.
    + destruct (Hends (or_intror HC)). split; [intros _; right; right; exact HC|].
      intros _. right. split; [exact Hnsd|]. left; split; assumption.
    + destruct (Hin HA HC) as [I1 [I2 I3]]. split.
      * intros [[H _]|[_ [[_ H]|[H _]]]]; [contradiction| |contradiction].
        left. apply I1 in H.
        replace (sB * sP) with ((- sB) * (- sP)) by ring.
        apply Rmult_lt_0_compat; lra.
      * intros [H|[H|H]]; [|contradiction|contradiction].
        right. split; [exact Hnsd|]. left. split; [assumption|].
        apply I1. destruct (Rlt_le_dec sP 0) as [Hn|Hp]; [exact Hn|].
        assert (sB * sP <= 0).
        { replace (sB * sP) with (- ((- sB) * sP)) by ring.
          assert (0 <= (- sB) * sP) by (apply Rmult_le_pos; lra). lra. }
        lra.
  - assert (HBp' : 0 < sB) by (destruct HBp as [H|H]; [exact H|contradiction (HsB (eq_sym H))]).
    assert (HnCB : ~ CB) by (intro H; apply HCB in H; lra).
    destruct DA as [HA|HA]; [|destruct DC as [HC|HC]].
    + destruct (Hends (or_introl HA)). split; [intros _; right; left; exact HA|].
      intros _. right. split; [exact Hnsd|]. right; split; assumption.
    + destruct (Hends (or_intror HC)). split; [intros _; right; right; exact HC|].
      intros _. right. split; [exact Hnsd|]. right; split; assumption.
    + destruct (Hin HA HC) as [I1 [I2 I3]]. split.
      * intros [[H _]|[_ [[H _]|[_ H]]]]; [contradiction|contradiction|].
        left. apply I2 in H. apply Rmult_lt_0_compat; assumption.
      * intros [H|[H|H]]; [|contradiction|contradiction].
        right. split; [exact Hnsd|]. right. split; [assumption|].
        apply I2. destruct (Rlt_le_dec 0 sP) as [Hp|Hn]; [exact Hp|].
        assert (sB * sP <= 0).
        { replace (sB * sP) with (- (sB * (- sP))) by ring.
          assert (0 <= sB * (- sP)) by (apply Rmult_le_pos; lra). lra. }
        lra.
Qed.

Theorem asx_sector_on_circle_dist : forall (a : CircularArc) (P : Point),
  valid_arc a ->
  dist_sq (arc_center a) P = arc_radius a * arc_radius a ->
  (asx_sector (arc_center a) (arc_start a) (arc_mid a) (arc_end a) P
   <-> arc_span_contains a P).
Proof.
  intros a P Hva HP.
  set (O := arc_center a) in *. set (A := arc_start a). set (B := arc_mid a).
  set (C := arc_end a). set (r := arc_radius a) in *.
  assert (Hr : 0 < r) by (apply arc_radius_pos; exact Hva).
  assert (HA : dist_sq O A = r * r).
  { unfold r, arc_radius, dist. rewrite sqrt_sqrt; [reflexivity | apply dist_sq_nonneg]. }
  assert (HC : dist_sq O C = r * r).
  { unfold r. rewrite <- (arc_center_dist_end a Hva).
    unfold dist. rewrite sqrt_sqrt; [reflexivity | apply dist_sq_nonneg]. }
  assert (HB : dist_sq O B = r * r).
  { unfold r. rewrite <- (arc_center_dist_mid a Hva).
    unfold dist. rewrite sqrt_sqrt; [reflexivity | apply dist_sq_nonneg]. }
  assert (Hv := Hva). unfold valid_arc in Hv. fold A B C in Hv.
  assert (HAC : ~ (px A = px C /\ py A = py C))
    by (intros [H1 H2]; apply Hv; rewrite H1, H2; ring).
  assert (HBA : ~ (px B = px A /\ py B = py A))
    by (intros [H1 H2]; apply Hv; rewrite H1, H2; ring).
  assert (HBC : ~ (px B = px C /\ py B = py C))
    by (intros [H1 H2]; apply Hv; rewrite H1, H2; ring).
  assert (HCA : ~ (px C = px A /\ py C = py A))
    by (intros [H1 H2]; apply HAC; split; symmetry; assumption).
  assert (HuA := on_circle_vec_nonzero O A r Hr HA).
  assert (HuC := on_circle_vec_nonzero O C r Hr HC).
  assert (NA := asx_norm_sq O A r HA). assert (NC := asx_norm_sq O C r HC).
  assert (Hnsd : ~ asx_same_dir (px A - px O) (py A - py O) (px C - px O) (py C - py O)).
  { intros [Hs Hd].
    set (d := asx_dot (px A - px O) (py A - py O) (px C - px O) (py C - py O)) in *.
    assert (Lg : d * d + asx_cross (px A - px O) (py A - py O) (px C - px O) (py C - py O)
                         * asx_cross (px A - px O) (py A - py O) (px C - px O) (py C - py O)
                 = ((px A - px O) * (px A - px O) + (py A - py O) * (py A - py O))
                   * ((px C - px O) * (px C - px O) + (py C - py O) * (py C - py O)))
      by (unfold d, asx_dot, asx_cross; ring).
    rewrite Hs, NA, NC in Lg.
    assert (Hrr : 0 < r * r) by (apply Rmult_lt_0_compat; lra).
    assert (Hf : (d - r * r) * (d + r * r) = 0) by (clear - Lg; lra).
    apply Rmult_integral in Hf.
    assert (D : d = r * r) by (destruct Hf as [Hf|Hf]; [lra | clear - Hf Hd Hrr; lra]).
    destruct (asx_dot_r2_eq _ _ _ _ r NA NC D) as [Dx Dy].
    apply HAC. clear - Dx Dy. split; lra. }
  destruct (asx_cone_on_circle O A C B r Hr HA HC HB HAC HBA HBC) as [HconeB HsB].
  destruct (asx_cone_ends _ _ _ _ HuA HuC) as [EA EC].
  destruct (asx_cone_ends _ _ _ _ HuC HuA) as [EC' EA'].
  unfold asx_sector, arc_span_contains, arc_interior_side, arc_side_chord.
  cbv zeta. fold O A B C.
  rewrite !asx_pt_eq.
  apply asx_sector_logic.
  - destruct (Req_dec (px P) (px A)) as [H1|H1];
      [destruct (Req_dec (py P) (py A)) as [H2|H2]|];
      [left; split; assumption | right; intros [_ H]; contradiction
      | right; intros [H _]; contradiction].
  - destruct (Req_dec (px P) (px C)) as [H1|H1];
      [destruct (Req_dec (py P) (py C)) as [H2|H2]|];
      [left; split; assumption | right; intros [_ H]; contradiction
      | right; intros [H _]; contradiction].
  - exact Hnsd.
  - exact HconeB.
  - exact HsB.
  - intros [[E1 E2]|[E1 E2]]; rewrite E1, E2; split; assumption.
  - intros HPA HPC.
    destruct (asx_cone_on_circle O A C P r Hr HA HC HP HAC HPA HPC) as [I1 I2].
    destruct (asx_cone_on_circle O C A P r Hr HC HA HP HCA HPC HPA) as [J1 _].
    assert (Ecr : cross_R_pt C A P = - cross_R_pt A C P)
      by (unfold cross_R_pt; ring).
    split; [exact I1|]. split; [|exact I2].
    rewrite J1, Ecr. split; intro H; lra.
Qed.

(* Same statement with the corpus's on-circle predicate. *)
Theorem asx_sector_on_circle_iff : forall (a : CircularArc) (P : Point),
  valid_arc a ->
  inCircle_R (arc_start a) (arc_mid a) (arc_end a) P = 0 ->
  (asx_sector (arc_center a) (arc_start a) (arc_mid a) (arc_end a) P
   <-> arc_span_contains a P).
Proof.
  intros a P Hva Hc. apply asx_sector_on_circle_dist; [exact Hva|].
  rewrite (inCircle_R_zero_implies_equidistant a P Hva Hc).
  unfold arc_radius, dist. rewrite sqrt_sqrt; [reflexivity | apply dist_sq_nonneg].
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Off the circle: the sector of a point is that of its radial image.     *)
(* -------------------------------------------------------------------------- *)

Definition asx_radial (a : CircularArc) (P : Point) : Point :=
  let O := arc_center a in
  let qx := px P - px O in let qy := py P - py O in
  let k := arc_radius a / sqrt (qx * qx + qy * qy) in
  mkPoint (px O + k * qx) (py O + k * qy).

Lemma asx_cone_scale_q : forall ax ay cx cy qx qy k, 0 < k ->
  asx_cone ax ay cx cy (k * qx) (k * qy) <-> asx_cone ax ay cx cy qx qy.
Proof.
  intros ax ay cx cy qx qy k Hk. unfold asx_cone.
  replace (asx_cross ax ay (k * qx) (k * qy)) with (k * asx_cross ax ay qx qy)
    by (unfold asx_cross; ring).
  replace (asx_cross (k * qx) (k * qy) cx cy) with (k * asx_cross qx qy cx cy)
    by (unfold asx_cross; ring).
  replace (asx_dot ax ay (k * qx) (k * qy)) with (k * asx_dot ax ay qx qy)
    by (unfold asx_dot; ring).
  assert (L : forall z, 0 <= k * z <-> 0 <= z) by (intro z; split; intro; nra).
  assert (P : forall z, 0 < k * z <-> 0 < z) by (intro z; split; intro; nra).
  assert (Z : forall z, k * z = 0 <-> z = 0)
    by (intro z; split; intro H; [nra | subst; ring]).
  unfold asx_cone_vals. rewrite !L, !P, !Z. tauto.
Qed.

Lemma asx_same_dir_scale : forall ax ay qx qy k, 0 < k ->
  asx_same_dir ax ay (k * qx) (k * qy) <-> asx_same_dir ax ay qx qy.
Proof.
  intros ax ay qx qy k Hk. unfold asx_same_dir.
  replace (asx_cross ax ay (k * qx) (k * qy)) with (k * asx_cross ax ay qx qy)
    by (unfold asx_cross; ring).
  replace (asx_dot ax ay (k * qx) (k * qy)) with (k * asx_dot ax ay qx qy)
    by (unfold asx_dot; ring).
  assert (P : forall z, 0 < k * z <-> 0 < z) by (intro z; split; intro; nra).
  assert (Z : forall z, k * z = 0 <-> z = 0)
    by (intro z; split; intro H; [nra | subst; ring]).
  rewrite P, Z. tauto.
Qed.

Lemma asx_sector_scale : forall O A B C Q k, 0 < k ->
  asx_sector O A B C
    (mkPoint (px O + k * (px Q - px O)) (py O + k * (py Q - py O)))
  <-> asx_sector O A B C Q.
Proof.
  intros O A B C Q k Hk. unfold asx_sector. cbv zeta. cbn [px py].
  replace (px O + k * (px Q - px O) - px O) with (k * (px Q - px O)) by ring.
  replace (py O + k * (py Q - py O) - py O) with (k * (py Q - py O)) by ring.
  rewrite !(asx_cone_scale_q _ _ _ _ _ _ k Hk).
  rewrite !(asx_same_dir_scale _ _ _ _ k Hk).
  tauto.
Qed.

(* WITNESS {"claimId":"s0-t4-sector-exact","topic":"curves","lemma":"asx_sector_radial_iff","title":"Exact arc sector test (cross/dot signs about the circumcentre, no atan2): for any point other than the centre it is arc_span_contains of the point's radial projection onto the circumcircle -- the ARC_DISTANCE question","file":"theories/ArcSectorExact.v","witness":"asx_sector_radial_iff","board":"ADR-0006"} *)
Theorem asx_sector_radial_iff : forall (a : CircularArc) (P : Point),
  valid_arc a ->
  ~ (px P = px (arc_center a) /\ py P = py (arc_center a)) ->
  (asx_sector (arc_center a) (arc_start a) (arc_mid a) (arc_end a) P
   <-> arc_span_contains a (asx_radial a P)).
Proof.
  intros a P Hva HPO.
  set (O := arc_center a) in *. set (r := arc_radius a).
  set (qx := px P - px O). set (qy := py P - py O).
  assert (Hr : 0 < r) by (apply arc_radius_pos; exact Hva).
  assert (Hq : ~ (qx = 0 /\ qy = 0))
    by (intros [H1 H2]; apply HPO; unfold qx, qy in *; split; lra).
  assert (Hn : 0 < qx * qx + qy * qy) by (apply sum_sq_pos; exact Hq).
  assert (Hs : 0 < sqrt (qx * qx + qy * qy)) by (apply sqrt_lt_R0; exact Hn).
  set (k := r / sqrt (qx * qx + qy * qy)).
  assert (Hk : 0 < k) by (unfold k; apply Rdiv_lt_0_compat; assumption).
  rewrite <- (asx_sector_scale O _ _ _ P k Hk).
  apply asx_sector_on_circle_dist; [exact Hva|].
  unfold asx_radial. fold O r. fold qx qy. fold k.
  unfold dist_sq. cbn [px py].
  replace ((px O - (px O + k * qx)) * (px O - (px O + k * qx))
           + (py O - (py O + k * qy)) * (py O - (py O + k * qy)))
    with (k * k * (qx * qx + qy * qy)) by ring.
  set (n := qx * qx + qy * qy) in *.
  assert (E : sqrt n * sqrt n = n) by (apply sqrt_sqrt; lra).
  unfold k.
  transitivity (r * r * (n / (sqrt n * sqrt n))); [field; lra|].
  rewrite E. field. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  The extractable decision over Q, and its correctness.                  *)
(* -------------------------------------------------------------------------- *)

Definition asxq_cross (ux uy vx vy : Q) : Q := (ux * vy - uy * vx)%Q.
Definition asxq_dot (ux uy vx vy : Q) : Q := (ux * vx + uy * vy)%Q.

Definition asxq_cone_vals (s x y d e : Q) : bool :=
  if Qlt_le_dec 0 s then Qle_bool 0 x && Qle_bool 0 y
  else if Qlt_le_dec s 0 then Qle_bool 0 x || Qle_bool 0 y
  else if Qlt_le_dec d 0 then Qle_bool 0 x
  else Qeq_bool x 0 && negb (Qle_bool e 0).

Definition asxq_cone (ax ay cx cy qx qy : Q) : bool :=
  asxq_cone_vals (asxq_cross ax ay cx cy) (asxq_cross ax ay qx qy)
    (asxq_cross qx qy cx cy) (asxq_dot ax ay cx cy) (asxq_dot ax ay qx qy).

Definition asxq_same_dir (ux uy vx vy : Q) : bool :=
  Qeq_bool (asxq_cross ux uy vx vy) 0 && negb (Qle_bool (asxq_dot ux uy vx vy) 0).

(* Centre O, arc A -> B -> C, query point X; all exact rationals. *)
Definition asxq_sector (ox oy ax ay bx by_ cx cy xx xy : Q) : bool :=
  let ax' := (ax - ox)%Q in let ay' := (ay - oy)%Q in
  let bx' := (bx - ox)%Q in let by' := (by_ - oy)%Q in
  let cx' := (cx - ox)%Q in let cy' := (cy - oy)%Q in
  let qx' := (xx - ox)%Q in let qy' := (xy - oy)%Q in
  if asxq_same_dir ax' ay' cx' cy' then
    (if asxq_same_dir ax' ay' bx' by' then asxq_same_dir ax' ay' qx' qy' else true)
  else if asxq_cone ax' ay' cx' cy' bx' by' then asxq_cone ax' ay' cx' cy' qx' qy'
  else asxq_cone cx' cy' ax' ay' qx' qy'.

Lemma asx_Q2R_0 : Q2R 0 = 0.
Proof. unfold Q2R. cbn. field. Qed.

Lemma asx_Qle_bool_R : forall x y, Qle_bool x y = true <-> Q2R x <= Q2R y.
Proof.
  intros x y. rewrite Qle_bool_iff. split; [apply Qle_Rle | apply Rle_Qle].
Qed.

Lemma asx_Qeq_bool_R : forall x y, Qeq_bool x y = true <-> Q2R x = Q2R y.
Proof.
  intros x y. rewrite Qeq_bool_iff. split; [apply Qeq_eqR | apply eqR_Qeq].
Qed.

Lemma asx_Qlt_R : forall x y, (x < y)%Q -> Q2R x < Q2R y.
Proof. apply Qlt_Rlt. Qed.

Lemma asx_Qle_R : forall x y, (x <= y)%Q -> Q2R x <= Q2R y.
Proof. apply Qle_Rle. Qed.

Lemma asx_negb_Qle_R : forall x y, negb (Qle_bool x y) = true <-> Q2R y < Q2R x.
Proof.
  intros x y. destruct (Qle_bool x y) eqn:E; cbn.
  - apply asx_Qle_bool_R in E. split; [discriminate | lra].
  - split; [intros _ | reflexivity].
    destruct (Rlt_le_dec (Q2R y) (Q2R x)) as [H|H]; [exact H|].
    apply Rle_Qle, Qle_bool_iff in H. congruence.
Qed.

Lemma asx_Q2R_cross : forall ux uy vx vy,
  Q2R (asxq_cross ux uy vx vy) = asx_cross (Q2R ux) (Q2R uy) (Q2R vx) (Q2R vy).
Proof.
  intros. unfold asxq_cross, asx_cross. rewrite Q2R_minus, !Q2R_mult. reflexivity.
Qed.

Lemma asx_Q2R_dot : forall ux uy vx vy,
  Q2R (asxq_dot ux uy vx vy) = asx_dot (Q2R ux) (Q2R uy) (Q2R vx) (Q2R vy).
Proof.
  intros. unfold asxq_dot, asx_dot. rewrite Q2R_plus, !Q2R_mult. reflexivity.
Qed.

Lemma asxq_cone_vals_correct : forall s x y d e,
  asxq_cone_vals s x y d e = true
  <-> asx_cone_vals (Q2R s) (Q2R x) (Q2R y) (Q2R d) (Q2R e).
Proof.
  intros s x y d e. unfold asxq_cone_vals, asx_cone_vals.
  pose proof asx_Q2R_0 as Z.
  destruct (Qlt_le_dec 0 s) as [Hs|Hs].
  - apply asx_Qlt_R in Hs. rewrite Z in Hs.
    rewrite Bool.andb_true_iff, !asx_Qle_bool_R, Z.
    split; [intros [H1 H2]; left; repeat split; assumption|].
    intros [[_ [H1 H2]]|[[H _]|[[H _]|[H _]]]]; [split; assumption|lra|lra|lra].
  - apply asx_Qle_R in Hs. rewrite Z in Hs.
    destruct (Qlt_le_dec s 0) as [Hs'|Hs'].
    + apply asx_Qlt_R in Hs'. rewrite Z in Hs'.
      rewrite Bool.orb_true_iff, !asx_Qle_bool_R, Z.
      split; [intros H; right; left; split; assumption|].
      intros [[H _]|[[_ H]|[[H _]|[H _]]]]; [lra|exact H|lra|lra].
    + apply asx_Qle_R in Hs'. rewrite Z in Hs'.
      assert (Es : Q2R s = 0) by lra.
      destruct (Qlt_le_dec d 0) as [Hd|Hd].
      * apply asx_Qlt_R in Hd. rewrite Z in Hd.
        rewrite asx_Qle_bool_R, Z.
        split; [intro H; right; right; left; repeat split; assumption|].
        intros [[H _]|[[H _]|[[_ [_ H]]|[_ [H _]]]]]; [lra|lra|exact H|lra].
      * apply asx_Qle_R in Hd. rewrite Z in Hd.
        rewrite Bool.andb_true_iff, asx_Qeq_bool_R, asx_negb_Qle_R, Z.
        split; [intros [H1 H2]; right; right; right; repeat split; assumption|].
        intros [[H _]|[[H _]|[[_ [H _]]|[_ [_ [H1 H2]]]]]];
          [lra|lra|lra|split; assumption].
Qed.

Lemma asxq_cone_correct : forall ax ay cx cy qx qy,
  asxq_cone ax ay cx cy qx qy = true
  <-> asx_cone (Q2R ax) (Q2R ay) (Q2R cx) (Q2R cy) (Q2R qx) (Q2R qy).
Proof.
  intros. unfold asxq_cone, asx_cone.
  rewrite asxq_cone_vals_correct, !asx_Q2R_cross, !asx_Q2R_dot. reflexivity.
Qed.

Lemma asxq_same_dir_correct : forall ux uy vx vy,
  asxq_same_dir ux uy vx vy = true
  <-> asx_same_dir (Q2R ux) (Q2R uy) (Q2R vx) (Q2R vy).
Proof.
  intros. unfold asxq_same_dir, asx_same_dir.
  rewrite Bool.andb_true_iff, asx_Qeq_bool_R, asx_negb_Qle_R, asx_Q2R_0,
    asx_Q2R_cross, asx_Q2R_dot. reflexivity.
Qed.

Lemma asx_bool_iff : forall (b : bool) (P : Prop), (b = true <-> P) ->
  (b = false <-> ~ P).
Proof.
  intros [] P H; split; intro K.
  - discriminate.
  - exfalso. apply K, H. reflexivity.
  - intro HP. apply H in HP. discriminate.
  - reflexivity.
Qed.

(* WITNESS {"claimId":"s0-t4-sector-exact","topic":"curves","lemma":"asxq_sector_correct","title":"The extractable exact-rational sector decision asxq_sector is the R predicate asx_sector on Q2R values (no atan2, no rounding)","file":"theories/ArcSectorExact.v","witness":"asxq_sector_correct","board":"ADR-0006"} *)
Theorem asxq_sector_correct : forall ox oy ax ay bx by_ cx cy xx xy,
  asxq_sector ox oy ax ay bx by_ cx cy xx xy = true
  <-> asx_sector (mkPoint (Q2R ox) (Q2R oy)) (mkPoint (Q2R ax) (Q2R ay))
        (mkPoint (Q2R bx) (Q2R by_)) (mkPoint (Q2R cx) (Q2R cy))
        (mkPoint (Q2R xx) (Q2R xy)).
Proof.
  intros. unfold asxq_sector, asx_sector. cbv zeta. cbn [px py].
  rewrite <- !Q2R_minus.
  pose proof (asxq_same_dir_correct (ax - ox) (ay - oy) (cx - ox) (cy - oy)) as SAC.
  pose proof (asxq_same_dir_correct (ax - ox) (ay - oy) (bx - ox) (by_ - oy)) as SAB.
  pose proof (asxq_same_dir_correct (ax - ox) (ay - oy) (xx - ox) (xy - oy)) as SAX.
  pose proof (asxq_cone_correct (ax - ox) (ay - oy) (cx - ox) (cy - oy)
                (bx - ox) (by_ - oy)) as CB.
  pose proof (asxq_cone_correct (ax - ox) (ay - oy) (cx - ox) (cy - oy)
                (xx - ox) (xy - oy)) as CX.
  pose proof (asxq_cone_correct (cx - ox) (cy - oy) (ax - ox) (ay - oy)
                (xx - ox) (xy - oy)) as CX'.
  pose proof (asx_bool_iff _ _ SAC) as SAC'.
  pose proof (asx_bool_iff _ _ SAB) as SAB'.
  pose proof (asx_bool_iff _ _ CB) as CB'.
  destruct (asxq_same_dir (ax - ox) (ay - oy) (cx - ox) (cy - oy));
  destruct (asxq_same_dir (ax - ox) (ay - oy) (bx - ox) (by_ - oy));
  destruct (asxq_cone (ax - ox) (ay - oy) (cx - ox) (cy - oy) (bx - ox) (by_ - oy));
  rewrite ?SAX, ?CX, ?CX';
  destruct SAC as [SAC1 SAC2]; destruct SAB as [SAB1 SAB2]; destruct CB as [CB1 CB2];
  destruct SAC' as [SAC3 SAC4]; destruct SAB' as [SAB3 SAB4];
  destruct CB' as [CB3 CB4];
  first
    [ specialize (SAC1 eq_refl) | specialize (SAC3 eq_refl) ];
  first
    [ specialize (SAB1 eq_refl) | specialize (SAB3 eq_refl) ];
  first
    [ specialize (CB1 eq_refl) | specialize (CB3 eq_refl) ];
  tauto.
Qed.

Print Assumptions asx_cone_angles.
Print Assumptions asx_cone_on_circle.
Print Assumptions asx_sector_on_circle_dist.
Print Assumptions asx_sector_on_circle_iff.
Print Assumptions asx_sector_radial_iff.
Print Assumptions asxq_sector_correct.
