(* ============================================================================
   NetTopologySuite.Proofs.CircularCookLineArcR
   ----------------------------------------------------------------------------
   ℚ → ℝ soundness bridge for the exact chord × arc classifier.

   CircularCookLineArcZ.I_line_arc_q decides, from eleven exact signs over ℚ,
   whether the chord P→P1 meets the circular arc through A, M, C. This file
   proves that decision is the geometric truth: read the five rational points
   into ℝ through Q2R, and

       I_line_arc_q P P1 A M C <> ILAEmpty
         <->  ArcIntersect.arc_chord_intersects (arc A M C) P P1

   on the classifier's own domain (D ≠ 0, non-degenerate chord). Soundness
   (Hit2 / Hit1 / Touch ⇒ a point of the chord lies on the arc) and
   completeness (Empty ⇒ no such point) are the two directions of that iff.
   Via CircularCookLineArcZ.I_line_arc_lift_agrees the same holds for the
   integer form I_line_arc_z.

   How the proof goes. The chord is X(t) = P + t·d; its squared distance to
   the circumcentre minus r² is the quadratic f(t) = a t² + b t + c whose
   coefficients are exactly q_signs's a, b, c read into ℝ (f_of_t). A point
   of the chord is on the circumcircle iff f(t) = 0 (ArcArcCircles), so the
   roots t± = (−b ± √Δ)/(2a) are the only candidates. The classifier's sign
   tests are then shown to be exact: t± ∈ [0,1] ⟺ its plus_in01 / minus_in01
   booleans (Vieta: c = a t₋ t₊, f(1) = a(1−t₋)(1−t₊)); the side of the chord
   A–C at X(t±) is (U ± κ√Δ)/(2a) and comp_sign_lin_rad computes its sign
   from the signs of U, κ and the comparison U² vs Δκ²; and a root on the
   line A–C and on the circle is A or C itself (line_circle_endpoints), which
   is why on_span_b accepts a zero side. Tangency (Δ = 0) is the single root
   t = −b/(2a) with side sign that of U.

   Not touched: host I_ok / first_cook_scope, sidecar cooks, the oracle wire,
   RootTag (tags are not part of arc_chord_intersects). ℤ ≡ ℚ agreement is
   CircularCookLineArcZ (0-axiom); this file is the ℝ leg and inherits the
   Stdlib Reals axioms.

   WITNESS topic: overlay · claimId: 0007-line-arc-r · witness: 0007-line-arc-r
   board: ADR-0007
   3-axiom (Stdlib Reals: ClassicalDedekindReals.sig_not_dec /
   sig_forall_dec, FunctionalExtensionality.functional_extensionality_dep --
   the corpus's Reals stamp, all on docs/axiom-allowlist.txt). No classic.
   No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import ZArith QArith Qreals Bool Reals Lra.
From NTS.Proofs Require Import Distance Segment CurveGeometry ArcOrient ArcIntersect
  ArcChordApprox ArcArcCircles CircularCookLineArcZ.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Sign vocabulary and the sign of u + v·√R.                              *)
(* -------------------------------------------------------------------------- *)

Definition sgn_spec (c : comparison) (x : R) : Prop :=
  match c with Lt => x < 0 | Eq => x = 0 | Gt => 0 < x end.
Definition cmp_spec (c : comparison) (x y : R) : Prop :=
  match c with Lt => x < y | Eq => x = y | Gt => y < x end.

Lemma CompOpp_spec : forall c x, sgn_spec c x -> sgn_spec (CompOpp c) (- x).
Proof. intros [] x H; cbn in *; lra. Qed.

Lemma is_le0_spec : forall c x, sgn_spec c x -> (is_le0 c = true <-> x <= 0).
Proof. intros [] x H; cbn in *; split; intro; try lra; try reflexivity; discriminate. Qed.
Lemma is_ge0_spec : forall c x, sgn_spec c x -> (is_ge0 c = true <-> 0 <= x).
Proof. intros [] x H; cbn in *; split; intro; try lra; try reflexivity; discriminate. Qed.
Lemma is_eq0_spec : forall c x, sgn_spec c x -> (is_eq0 c = true <-> x = 0).
Proof. intros [] x H; cbn in *; split; intro; try lra; try reflexivity; discriminate. Qed.

(* on_span_b: X is on the chord line, or strictly on M's side of it. *)
Lemma on_span_b_spec :
  forall cX cM x m, sgn_spec cX x -> sgn_spec cM m -> m <> 0 ->
    (on_span_b cX cM = true <-> x = 0 \/ 0 < m * x).
Proof.
  intros [] [] x m Hx Hm Hm0; cbn in *; split; intro H;
    try reflexivity; try discriminate; try (left; lra); try (right; nra);
    try (exfalso; lra); destruct H; try lra; try nra.
Qed.

Lemma sq_lt_abs : forall x y : R, x*x < y*y -> Rabs x < Rabs y.
Proof. intros. apply Rsqr_lt_abs_0. unfold Rsqr. assumption. Qed.

Lemma sum_sign_from_squares :
  forall (u x : R) (cu cx cuu : comparison),
    sgn_spec cu u -> sgn_spec cx x -> cmp_spec cuu (u*u) (x*x) ->
    sgn_spec (comp_sign_lin_rad cu cx cuu) (u + x).
Proof.
  intros u x cu cx cuu Hu Hx Huu.
  destruct cu, cx, cuu; unfold comp_sign_lin_rad; cbn [CompOpp];
    unfold sgn_spec, cmp_spec in *; try lra.
  all: (assert (Hd : u - x < 0) by lra) || (assert (Hd : 0 < u - x) by lra).
  all: destruct (Rtotal_order (u + x) 0) as [H|[H|H]]; try lra; exfalso; nra.
Qed.

(* WITNESS {"claimId":"0007-line-arc-r","topic":"overlay","lemma":"comp_sign_lin_rad_spec","title":"comp_sign_lin_rad computes the sign of u + v*sqrt R from the signs of u and v and the comparison of u^2 with R v^2","file":"theories/CircularCookLineArcR.v","witness":"0007-line-arc-r","board":"ADR-0007"} *)
Lemma comp_sign_lin_rad_spec :
  forall (u v R : R) (cu cv cuu : comparison),
    0 < R ->
    sgn_spec cu u -> sgn_spec cv v -> cmp_spec cuu (u*u) (R*v*v) ->
    sgn_spec (comp_sign_lin_rad cu cv cuu) (u + v * sqrt R).
Proof.
  intros u v R cu cv cuu HR Hu Hv Huu.
  assert (Hs : 0 < sqrt R) by (apply sqrt_lt_R0; exact HR).
  assert (Hss : sqrt R * sqrt R = R) by (apply sqrt_sqrt; lra).
  apply sum_sign_from_squares.
  - exact Hu.
  - destruct cv; unfold sgn_spec in *; nra.
  - destruct cuu; unfold cmp_spec in *; nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The quadratic: its roots, and Vieta bracketing of t± in [0,1].         *)
(* -------------------------------------------------------------------------- *)

Lemma quad_roots :
  forall a b c t, 0 < a -> a*t*t + b*t + c = 0 ->
    0 <= b*b - 4*a*c /\
    (t = (-b + sqrt (b*b - 4*a*c)) / (2*a) \/ t = (-b - sqrt (b*b - 4*a*c)) / (2*a)).
Proof.
  intros a b c t Ha Hf.
  set (D := b*b - 4*a*c).
  assert (HD : (2*a*t + b)*(2*a*t + b) = D).
  { unfold D. replace ((2*a*t + b)*(2*a*t + b)) with (b*b - 4*a*c + 4*a*(a*t*t + b*t + c)) by ring.
    rewrite Hf. ring. }
  assert (HD0 : 0 <= D) by (rewrite <- HD; exact (Rle_0_sqr _)).
  split; [exact HD0 |].
  assert (Hss : sqrt D * sqrt D = D) by (apply sqrt_sqrt; exact HD0).
  assert (Hprod : (2*a*t + b - sqrt D) * (2*a*t + b + sqrt D) = 0) by nra.
  destruct (Rmult_integral _ _ Hprod) as [H1 | H2].
  - left. apply Rmult_eq_reg_r with (r := 2*a); [ | lra]. field_simplify; [ | lra]. lra.
  - right. apply Rmult_eq_reg_r with (r := 2*a); [ | lra]. field_simplify; [ | lra]. lra.
Qed.

Lemma quad_root_plus_is_root :
  forall a b c, 0 < a -> 0 <= b*b - 4*a*c ->
    let t := (-b + sqrt (b*b - 4*a*c)) / (2*a) in a*t*t + b*t + c = 0.
Proof.
  intros a b c Ha HD. cbv zeta.
  set (D := b*b - 4*a*c) in *.
  set (t := (-b + sqrt D) / (2*a)).
  assert (Hss : sqrt D * sqrt D = D) by (apply sqrt_sqrt; exact HD).
  assert (H2 : 2*a*t + b = sqrt D) by (unfold t; field; lra).
  replace (a*t*t + b*t + c) with (((2*a*t + b)*(2*a*t + b) - D) / (4*a)) by (unfold D; field; lra).
  rewrite H2, Hss. field. lra.
Qed.

Lemma quad_root_minus_is_root :
  forall a b c, 0 < a -> 0 <= b*b - 4*a*c ->
    let t := (-b - sqrt (b*b - 4*a*c)) / (2*a) in a*t*t + b*t + c = 0.
Proof.
  intros a b c Ha HD. cbv zeta.
  set (D := b*b - 4*a*c) in *.
  set (t := (-b - sqrt D) / (2*a)).
  assert (Hss : sqrt D * sqrt D = D) by (apply sqrt_sqrt; exact HD).
  assert (H2 : 2*a*t + b = - sqrt D) by (unfold t; field; lra).
  replace (a*t*t + b*t + c) with (((2*a*t + b)*(2*a*t + b) - D) / (4*a)) by (unfold D; field; lra).
  rewrite H2. replace (- sqrt D * - sqrt D) with (sqrt D * sqrt D) by ring. rewrite Hss. field. lra.
Qed.

Section Vieta.
  Variables a b c : R.
  Hypothesis Ha : 0 < a.
  Hypothesis HD : 0 < b*b - 4*a*c.
  Let D := b*b - 4*a*c.
  Let rho := sqrt D / (2*a).
  Let s := -b / (2*a).
  Let tp := s + rho.
  Let tm := s - rho.

  Lemma vieta_rho_pos : 0 < rho.
  Proof. unfold rho. apply Rdiv_lt_0_compat; [apply sqrt_lt_R0; exact HD | lra]. Qed.

  Lemma vieta_2a_s : s * (2*a) = -b.
  Proof. unfold s. field. lra. Qed.
  Lemma vieta_2a_rho : rho * (2*a) = sqrt D.
  Proof. unfold rho. field. lra. Qed.

  Lemma vieta_c : c = a * tm * tp.
  Proof.
    assert (Hss : sqrt D * sqrt D = D) by (apply sqrt_sqrt; unfold D; lra).
    pose proof vieta_2a_s as H1. pose proof vieta_2a_rho as H2.
    apply Rmult_eq_reg_l with (r := 4*a); [ | lra].
    replace (4*a*(a*tm*tp)) with ((s*(2*a))*(s*(2*a)) - (rho*(2*a))*(rho*(2*a)))
      by (unfold tm, tp; ring).
    rewrite H1, H2, Hss. unfold D. ring.
  Qed.

  Lemma vieta_f1 : a + b + c = a * (1 - tm) * (1 - tp).
  Proof.
    pose proof vieta_c as Hc. pose proof vieta_2a_s as H1.
    replace (a*(1 - tm)*(1 - tp)) with (a - s*(2*a) + a*tm*tp) by (unfold tm, tp; ring).
    rewrite H1, <- Hc. ring.
  Qed.

  Lemma vieta_s_ge0 : (0 <= s) <-> (b <= 0).
  Proof. pose proof vieta_2a_s as H2. split; intro H; nra. Qed.

  Lemma vieta_s_le1 : (s <= 1) <-> (0 <= b + 2*a).
  Proof. pose proof vieta_2a_s as H2. split; intro H; nra. Qed.

  Lemma vieta_c_le0 : c <= 0 <-> tm*tp <= 0.
  Proof. pose proof vieta_c as Hc. split; intro H; nra. Qed.
  Lemma vieta_c_ge0 : 0 <= c <-> 0 <= tm*tp.
  Proof. pose proof vieta_c as Hc. split; intro H; nra. Qed.
  Lemma vieta_f1_ge0 : 0 <= a + b + c <-> 0 <= (1-tm)*(1-tp).
  Proof. pose proof vieta_f1 as Hf. split; intro H; nra. Qed.
  Lemma vieta_f1_le0 : a + b + c <= 0 <-> (1-tm)*(1-tp) <= 0.
  Proof. pose proof vieta_f1 as Hf. split; intro H; nra. Qed.

  Lemma vieta_tp_ge0 : (0 <= tp) <-> (c <= 0 \/ 0 <= s).
  Proof.
    pose proof vieta_rho_pos as Hr. rewrite vieta_c_le0.
    assert (Htp : tp = s + rho) by reflexivity.
    assert (Htm : tm = s - rho) by reflexivity.
    split.
    - intro H. destruct (Rle_or_lt 0 s) as [Hs|Hs]; [right; exact Hs | left]. nra.
    - intros [H|H]; nra.
  Qed.

  Lemma vieta_tp_le1 : (tp <= 1) <-> (0 <= a + b + c /\ s <= 1).
  Proof.
    pose proof vieta_rho_pos as Hr. rewrite vieta_f1_ge0.
    assert (Htp : tp = s + rho) by reflexivity.
    assert (Htm : tm = s - rho) by reflexivity.
    split.
    - intro H. split; nra.
    - intros [H1 H2]. nra.
  Qed.

  Lemma vieta_tm_ge0 : (0 <= tm) <-> (0 <= c /\ 0 <= s).
  Proof.
    pose proof vieta_rho_pos as Hr. rewrite vieta_c_ge0.
    assert (Htp : tp = s + rho) by reflexivity.
    assert (Htm : tm = s - rho) by reflexivity.
    split.
    - intro H. split; nra.
    - intros [H1 H2]. nra.
  Qed.

  Lemma vieta_tm_le1 : (tm <= 1) <-> (a + b + c <= 0 \/ s <= 1).
  Proof.
    pose proof vieta_rho_pos as Hr. rewrite vieta_f1_le0.
    assert (Htp : tp = s + rho) by reflexivity.
    assert (Htm : tm = s - rho) by reflexivity.
    split.
    - intro H. destruct (Rle_or_lt s 1) as [Hs|Hs]; [right; exact Hs | left]. nra.
    - intros [H|H]; nra.
  Qed.
End Vieta.

(* -------------------------------------------------------------------------- *)
(* §3  Geometry: the chord is affine, and the chord line meets the            *)
(*     circumcircle only at A and C.                                          *)
(* -------------------------------------------------------------------------- *)

Lemma side_affine :
  forall (A C P : Point) (dx dy t : R),
    cross_R_pt A C (mkPoint (px P + t*dx) (py P + t*dy))
    = cross_R_pt A C P + t * ((px C - px A) * dy - dx * (py C - py A)).
Proof. intros. unfold cross_R_pt. cbn [px py]. ring. Qed.

Lemma cross_R_pt_at_A : forall A C, cross_R_pt A C A = 0.
Proof. intros. unfold cross_R_pt. ring. Qed.
Lemma cross_R_pt_at_C : forall A C, cross_R_pt A C C = 0.
Proof. intros. unfold cross_R_pt. ring. Qed.

(* WITNESS {"claimId":"0007-line-arc-r","topic":"overlay","lemma":"line_circle_endpoints","title":"A point on the chord line A-C and on the circumcircle through A and C is A or C","file":"theories/CircularCookLineArcR.v","witness":"0007-line-arc-r","board":"ADR-0007"} *)
Lemma line_circle_endpoints :
  forall (A C X O : Point),
    (px C - px A)*(px C - px A) + (py C - py A)*(py C - py A) <> 0 ->
    cross_R_pt A C X = 0 ->
    dist_sq O X = dist_sq O A ->
    dist_sq O C = dist_sq O A ->
    X = A \/ X = C.
Proof.
  intros [ax ay] [cx cy] [xx xy] [ox oy] Hn Hcr HX HC.
  unfold cross_R_pt, dist_sq in *. cbn in *.
  set (n2 := (cx - ax)*(cx - ax) + (cy - ay)*(cy - ay)) in *.
  set (s := ((xx - ax)*(cx - ax) + (xy - ay)*(cy - ay)) / n2).
  assert (E1 : ((xx-ax)*(cx-ax) + (xy-ay)*(cy-ay)) * (cx - ax) = (xx - ax) * n2).
  { unfold n2.
    replace (((xx-ax)*(cx-ax) + (xy-ay)*(cy-ay)) * (cx - ax))
      with ((xx - ax) * ((cx - ax)*(cx - ax) + (cy - ay)*(cy - ay))
            + (cy - ay) * ((cx - ax) * (xy - ay) - (xx - ax) * (cy - ay))) by ring.
    rewrite Hcr. ring. }
  assert (E2 : ((xx-ax)*(cx-ax) + (xy-ay)*(cy-ay)) * (cy - ay) = (xy - ay) * n2).
  { unfold n2.
    replace (((xx-ax)*(cx-ax) + (xy-ay)*(cy-ay)) * (cy - ay))
      with ((xy - ay) * ((cx - ax)*(cx - ax) + (cy - ay)*(cy - ay))
            - (cx - ax) * ((cx - ax) * (xy - ay) - (xx - ax) * (cy - ay))) by ring.
    rewrite Hcr. ring. }
  assert (Hwx : xx - ax = s * (cx - ax)).
  { unfold s, Rdiv. rewrite Rmult_assoc, (Rmult_comm (/ n2)), <- Rmult_assoc, E1. field. exact Hn. }
  assert (Hwy : xy - ay = s * (cy - ay)).
  { unfold s, Rdiv. rewrite Rmult_assoc, (Rmult_comm (/ n2)), <- Rmult_assoc, E2. field. exact Hn. }
  assert (Hquad : s * (s - 1) * n2 = 0).
  { unfold n2.
    replace xx with (ax + s * (cx - ax)) in HX by lra.
    replace xy with (ay + s * (cy - ay)) in HX by lra.
    assert (HCs : s * (((ox - cx)*(ox - cx) + (oy - cy)*(oy - cy))
                       - ((ox - ax)*(ox - ax) + (oy - ay)*(oy - ay))) = 0) by (rewrite HC; ring).
    nra. }
  destruct (Rmult_integral _ _ Hquad) as [Hs | Hn0]; [ | contradiction].
  destruct (Rmult_integral _ _ Hs) as [Hs0 | Hs1].
  - left. f_equal; nra.
  - right. f_equal; nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  ℚ → ℝ: points, the circumcentre, and the eleven coefficients.          *)
(* -------------------------------------------------------------------------- *)

Definition qpt_R (p : QPt) : Point := mkPoint (Q2R (qx p)) (Q2R (qy p)).
Definition arc_of (A M C : QPt) : CircularArc := mkCircularArc (qpt_R A) (qpt_R M) (qpt_R C).

Lemma Q2R_2 : Q2R 2 = 2.
Proof. replace 2%Q with (1 + 1)%Q by reflexivity. rewrite Q2R_plus, RMicromega.Q2R_1. lra. Qed.
Lemma Q2R_4 : Q2R 4 = 4.
Proof. replace 4%Q with (2 + 2)%Q by reflexivity. rewrite Q2R_plus, Q2R_2. lra. Qed.

Ltac push_Q2R :=
  repeat first
    [ rewrite Q2R_plus | rewrite Q2R_minus | rewrite Q2R_mult | rewrite Q2R_opp
    | rewrite RMicromega.Q2R_0 | rewrite RMicromega.Q2R_1 | rewrite Q2R_2 | rewrite Q2R_4 ].

Lemma qsgn_spec : forall q : Q, sgn_spec (qsgn q) (Q2R q).
Proof.
  intro q. unfold qsgn. destruct (Qcompare_spec q 0) as [H|H|H]; cbn.
  - rewrite <- RMicromega.Q2R_0. apply Qeq_eqR. exact H.
  - rewrite <- RMicromega.Q2R_0. apply Qlt_Rlt. exact H.
  - rewrite <- RMicromega.Q2R_0. apply Qlt_Rlt. exact H.
Qed.

Lemma Qcompare_spec_R : forall x y : Q, cmp_spec (x ?= y)%Q (Q2R x) (Q2R y).
Proof.
  intros x y. destruct (Qcompare_spec x y) as [H|H|H]; cbn.
  - apply Qeq_eqR. exact H.
  - apply Qlt_Rlt. exact H.
  - apply Qlt_Rlt. exact H.
Qed.

Lemma cross_Q2R : forall A C X : QPt,
  Q2R (qcross A C X) = cross_R_pt (qpt_R A) (qpt_R C) (qpt_R X).
Proof. intros. unfold qcross, cross_R_pt, qpt_R. cbn [px py]. push_Q2R. reflexivity. Qed.

Lemma arcD_Q2R : forall A M C : QPt,
  Q2R (qarc_D A M C)
  = 2 * (px (qpt_R A) * (py (qpt_R M) - py (qpt_R C))
         + px (qpt_R M) * (py (qpt_R C) - py (qpt_R A))
         + px (qpt_R C) * (py (qpt_R A) - py (qpt_R M))).
Proof. intros. unfold qarc_D, qpt_R. cbn [px py]. push_Q2R. reflexivity. Qed.

Lemma valid_arc_of : forall A M C : QPt,
  ~ (qarc_D A M C == 0)%Q -> valid_arc (arc_of A M C).
Proof.
  intros A M C HD Hv. apply HD. apply eqR_Qeq.
  rewrite arcD_Q2R, RMicromega.Q2R_0. unfold arc_of in Hv. cbn [arc_start arc_mid arc_end] in Hv.
  unfold qpt_R in *. cbn [px py] in *. nra.
Qed.

Lemma center_Q2R : forall A M C : QPt,
  ~ (qarc_D A M C == 0)%Q ->
  px (arc_center (arc_of A M C)) = Q2R (qOx A M C) /\
  py (arc_center (arc_of A M C)) = Q2R (qOy A M C).
Proof.
  intros A M C HD.
  unfold qOx, qOy. rewrite !Q2R_div by exact HD.
  unfold qNx, qNy. cbv zeta. rewrite arcD_Q2R.
  unfold arc_center, arc_of, qpt_R. cbn [arc_start arc_mid arc_end px py].
  cbv zeta. push_Q2R. split; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4b The decision tree by name. Booleans mirroring classify_signs's lets,   *)
(*     so its Empty verdict can be read off without re-unfolding the tree.    *)
(* -------------------------------------------------------------------------- *)

Definition s_ge0_b (sd : LineArcSigns) : bool := is_le0 (sg_b sd).
Definition s_le1_b (sd : LineArcSigns) : bool := is_ge0 (sg_b2a sd).
Definition plus_in01_b (sd : LineArcSigns) : bool :=
  (is_le0 (sg_f0 sd) || s_ge0_b sd) && (is_ge0 (sg_f1 sd) && s_le1_b sd).
Definition minus_in01_b (sd : LineArcSigns) : bool :=
  (is_ge0 (sg_f0 sd) && s_ge0_b sd) && (is_le0 (sg_f1 sd) || s_le1_b sd).
Definition sg_plus_c (sd : LineArcSigns) : comparison :=
  comp_sign_lin_rad (sg_U sd) (sg_kappa sd) (sg_U2_vs_disc_kappa2 sd).
Definition sg_minus_c (sd : LineArcSigns) : comparison :=
  comp_sign_lin_rad (sg_U sd) (CompOpp (sg_kappa sd)) (sg_U2_vs_disc_kappa2 sd).
Definition keep_plus_b (sd : LineArcSigns) : bool :=
  plus_in01_b sd && on_span_b (sg_plus_c sd) (sg_M sd).
Definition keep_minus_b (sd : LineArcSigns) : bool :=
  minus_in01_b sd && on_span_b (sg_minus_c sd) (sg_M sd).
Definition touch_keep_b (sd : LineArcSigns) : bool :=
  s_ge0_b sd && s_le1_b sd && on_span_b (sg_U sd) (sg_M sd).

Lemma classify_signs_empty_iff :
  forall sd,
    classify_signs sd = ILAEmpty <->
    (sg_disc sd = Lt
     \/ (sg_disc sd = Eq /\ touch_keep_b sd = false)
     \/ (sg_disc sd = Gt /\ keep_plus_b sd = false /\ keep_minus_b sd = false)).
Proof.
  intro sd.
  unfold classify_signs, touch_keep_b, keep_plus_b, keep_minus_b, plus_in01_b, minus_in01_b,
    s_ge0_b, s_le1_b, sg_plus_c, sg_minus_c.
  cbv zeta beta.
  destruct (sg_disc sd) eqn:Hd.
  - destruct (is_le0 (sg_b sd) && is_ge0 (sg_b2a sd) && on_span_b (sg_U sd) (sg_M sd)) eqn:Ht.
    + split; [discriminate | intros [H|[[_ H]|[H _]]]; discriminate].
    + split; [intros _; right; left; split; [reflexivity | reflexivity] | reflexivity].
  - split; [intros _; left; reflexivity | reflexivity].
  - destruct ((is_le0 (sg_f0 sd) || is_le0 (sg_b sd)) && (is_ge0 (sg_f1 sd) && is_ge0 (sg_b2a sd))
              && on_span_b (comp_sign_lin_rad (sg_U sd) (sg_kappa sd) (sg_U2_vs_disc_kappa2 sd)) (sg_M sd)) eqn:Hp;
    destruct ((is_ge0 (sg_f0 sd) && is_le0 (sg_b sd)) && (is_le0 (sg_f1 sd) || is_ge0 (sg_b2a sd))
              && on_span_b (comp_sign_lin_rad (sg_U sd) (CompOpp (sg_kappa sd)) (sg_U2_vs_disc_kappa2 sd)) (sg_M sd)) eqn:Hm.
    all: split; try discriminate.
    all: try (intros [H|[[H _]|[_ [H1 H2]]]]; try discriminate; congruence).
    all: intros _; right; right; repeat split; congruence.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  The bridge.                                                            *)
(* -------------------------------------------------------------------------- *)

Section Bridge.
  Variables P P1 A M C : QPt.
  Hypothesis HD : ~ (qarc_D A M C == 0)%Q.
  Hypothesis HL : ~ (qchord_L2 P P1 == 0)%Q.

  Let Pr := qpt_R P. Let P1r := qpt_R P1.
  Let Ar := qpt_R A. Let Mr := qpt_R M. Let Cr := qpt_R C.
  Let arc := arc_of A M C.
  Let O := arc_center arc.
  Let dx := px P1r - px Pr. Let dy := py P1r - py Pr.
  Let aR := dx*dx + dy*dy.
  Let bR := 2 * ((px Pr - px O)*dx + (py Pr - py O)*dy).
  Let cR := (px Pr - px O)*(px Pr - px O) + (py Pr - py O)*(py Pr - py O)
            - ((px Ar - px O)*(px Ar - px O) + (py Ar - py O)*(py Ar - py O)).
  Let discR := bR*bR - 4*aR*cR.
  Let kapR := (px Cr - px Ar) * dy - dx * (py Cr - py Ar).
  Let sigP := cross_R_pt Ar Cr Pr.
  Let sigM := cross_R_pt Ar Cr Mr.
  Let UR := 2*aR*sigP - bR*kapR.
  Let X (t : R) : Point := mkPoint (px Pr + t*dx) (py Pr + t*dy).
  Let sd := q_signs P P1 A M C.

  (* -- the Q pieces read into R -------------------------------------------- *)

  Lemma qOx_R : Q2R (qOx A M C) = px O.
  Proof. destruct (center_Q2R A M C HD) as [Hx _]. unfold O, arc. rewrite Hx. reflexivity. Qed.
  Lemma qOy_R : Q2R (qOy A M C) = py O.
  Proof. destruct (center_Q2R A M C HD) as [_ Hy]. unfold O, arc. rewrite Hy. reflexivity. Qed.

  Lemma qA_R : Q2R (qA_ P P1 A M C) = aR.
  Proof. unfold qA_, qchord_L2, aR, dx, dy, P1r, Pr, qpt_R. cbn [px py]. cbv zeta. push_Q2R. reflexivity. Qed.
  Lemma qB_R : Q2R (qB_ P P1 A M C) = bR.
  Proof.
    unfold qB_, qWx, qWy, qDx, qDy. push_Q2R. rewrite qOx_R, qOy_R.
    unfold bR, dx, dy, Pr, P1r, qpt_R. cbn [px py]. reflexivity.
  Qed.
  Lemma qC_R : Q2R (qC_ P P1 A M C) = cR.
  Proof.
    unfold qC_, qWx, qWy. push_Q2R. rewrite qOx_R, qOy_R.
    unfold cR, Pr, Ar, qpt_R. cbn [px py]. reflexivity.
  Qed.
  Lemma qDisc_R : Q2R (qDisc_ P P1 A M C) = discR.
  Proof. unfold qDisc_. push_Q2R. rewrite qA_R, qB_R, qC_R. reflexivity. Qed.
  Lemma qKap_R : Q2R (qKap_ P P1 A M C) = kapR.
  Proof. unfold qKap_, qDx, qDy. push_Q2R. unfold kapR, dx, dy, Cr, Ar, Pr, P1r, qpt_R. cbn [px py]. reflexivity. Qed.
  Lemma qU_R : Q2R (qU_ P P1 A M C) = UR.
  Proof. unfold qU_. push_Q2R. rewrite qA_R, qB_R, qKap_R, cross_Q2R. reflexivity. Qed.

  (* -- the sign record of q_signs, read into R ------------------------------ *)

  Lemma sd_disc : sgn_spec (sg_disc sd) discR.
  Proof. pose proof (qsgn_spec (qDisc_ P P1 A M C)) as H. rewrite qDisc_R in H. unfold sd. rewrite q_signs_named. exact H. Qed.
  Lemma sd_f0 : sgn_spec (sg_f0 sd) cR.
  Proof. pose proof (qsgn_spec (qC_ P P1 A M C)) as H. rewrite qC_R in H. unfold sd. rewrite q_signs_named. exact H. Qed.
  Lemma sd_f1 : sgn_spec (sg_f1 sd) (aR + bR + cR).
  Proof.
    pose proof (qsgn_spec (qA_ P P1 A M C + qB_ P P1 A M C + qC_ P P1 A M C)) as H.
    rewrite !Q2R_plus, qA_R, qB_R, qC_R in H. unfold sd. rewrite q_signs_named. exact H.
  Qed.
  Lemma sd_b : sgn_spec (sg_b sd) bR.
  Proof. pose proof (qsgn_spec (qB_ P P1 A M C)) as H. rewrite qB_R in H. unfold sd. rewrite q_signs_named. exact H. Qed.
  Lemma sd_b2a : sgn_spec (sg_b2a sd) (bR + 2*aR).
  Proof.
    pose proof (qsgn_spec (qB_ P P1 A M C + 2 * qA_ P P1 A M C)) as H.
    rewrite Q2R_plus, Q2R_mult, Q2R_2, qA_R, qB_R in H. unfold sd. rewrite q_signs_named. exact H.
  Qed.
  Lemma sd_M : sgn_spec (sg_M sd) sigM.
  Proof. pose proof (qsgn_spec (qcross A C M)) as H. rewrite cross_Q2R in H. unfold sd. rewrite q_signs_named. exact H. Qed.
  Lemma sd_U : sgn_spec (sg_U sd) UR.
  Proof. pose proof (qsgn_spec (qU_ P P1 A M C)) as H. rewrite qU_R in H. unfold sd. rewrite q_signs_named. exact H. Qed.
  Lemma sd_kappa : sgn_spec (sg_kappa sd) kapR.
  Proof. pose proof (qsgn_spec (qKap_ P P1 A M C)) as H. rewrite qKap_R in H. unfold sd. rewrite q_signs_named. exact H. Qed.
  Lemma sd_U2 : cmp_spec (sg_U2_vs_disc_kappa2 sd) (UR*UR) (discR*kapR*kapR).
  Proof.
    pose proof (Qcompare_spec_R (qU_ P P1 A M C * qU_ P P1 A M C)
                                (qDisc_ P P1 A M C * qKap_ P P1 A M C * qKap_ P P1 A M C)) as H.
    rewrite !Q2R_mult, qU_R, qDisc_R, qKap_R in H. unfold sd. rewrite q_signs_named. exact H.
  Qed.

  (* -- geometry on the R side ----------------------------------------------- *)

  Lemma Hva : valid_arc arc.
  Proof. exact (valid_arc_of A M C HD). Qed.

  Lemma HaR : 0 < aR.
  Proof.
    assert (Hne : aR <> 0).
    { intro H. apply HL. apply eqR_Qeq. rewrite RMicromega.Q2R_0. rewrite <- H. exact qA_R. }
    unfold aR in *. nra.
  Qed.

  Lemma f_of_t :
    forall t, dist_sq O (X t) - dist_sq O Ar = aR*t*t + bR*t + cR.
  Proof. intro t. unfold dist_sq, aR, bR, cR, X. cbn [px py]. ring. Qed.

  Lemma on_circle_iff :
    forall t, inCircle_R Ar Mr Cr (X t) = 0 <-> aR*t*t + bR*t + cR = 0.
  Proof.
    intro t. pose proof Hva as Hv. split; intro H.
    - pose proof (inCircle_R_zero_implies_equidistant arc (X t) Hv H) as He.
      rewrite <- f_of_t. exact (Rminus_diag_eq _ _ He).
    - apply (inCircle_R_zero_of_equidistant arc (X t) Hv).
      change (dist_sq O (X t) = dist_sq O Ar).
      pose proof (f_of_t t) as Hf. rewrite H in Hf. lra.
  Qed.

  Lemma between_X :
    forall Q, between Pr P1r Q <-> exists t, 0 <= t <= 1 /\ Q = X t.
  Proof.
    intro Q. split.
    - intros [t [Ht0 [Ht1 [Hx Hy]]]]. exists t. split; [lra |].
      destruct Q as [qx0 qy0]. unfold X. cbn [px py] in *.
      f_equal; [rewrite Hx | rewrite Hy]; unfold dx, dy; ring.
    - intros [t [[H0 H1] HQ]]. subst Q. exists t. unfold X. cbn [px py].
      repeat split; try lra; unfold dx, dy; ring.
  Qed.

  Lemma side_X : forall t, cross_R_pt Ar Cr (X t) = sigP + t*kapR.
  Proof. intro t. unfold X, sigP, kapR. apply side_affine. Qed.

  Lemma span_iff :
    forall Q, arc_span_contains arc Q <-> (0 < sigM * cross_R_pt Ar Cr Q \/ Q = Ar \/ Q = Cr).
  Proof.
    intro Q. unfold arc_span_contains, arc_interior_side, arc_side_chord, arc, arc_of.
    cbn [arc_start arc_mid arc_end]. tauto.
  Qed.

  Lemma sigM_nonzero : sigM <> 0.
  Proof.
    pose proof Hva as Hv. unfold valid_arc, arc, arc_of in Hv. cbn [arc_start arc_mid arc_end] in Hv.
    unfold sigM, cross_R_pt, Ar, Mr, Cr. intro H. apply Hv. lra.
  Qed.

  Lemma AC_nondegenerate :
    (px Cr - px Ar)*(px Cr - px Ar) + (py Cr - py Ar)*(py Cr - py Ar) <> 0.
  Proof.
    pose proof Hva as Hv. unfold valid_arc, arc, arc_of in Hv. cbn [arc_start arc_mid arc_end] in Hv.
    intro H. apply Hv. unfold Cr, Ar in *.
    set (ux := px (qpt_R C) - px (qpt_R A)) in *.
    set (uy := py (qpt_R C) - py (qpt_R A)) in *.
    pose proof (Rle_0_sqr ux) as Hux0. pose proof (Rle_0_sqr uy) as Huy0. unfold Rsqr in *.
    assert (Hux : ux * ux = 0) by lra.
    assert (Huy : uy * uy = 0) by lra.
    assert (Hx : ux = 0) by (destruct (Rmult_integral _ _ Hux); assumption).
    assert (Hy : uy = 0) by (destruct (Rmult_integral _ _ Huy); assumption).
    rewrite Hx, Hy. ring.
  Qed.

  Lemma root_on_line_is_endpoint :
    forall t, aR*t*t + bR*t + cR = 0 -> cross_R_pt Ar Cr (X t) = 0 -> X t = Ar \/ X t = Cr.
  Proof.
    intros t Hf Hs.
    destruct (arc_center_equidistant arc Hva) as [_ HC].
    apply (line_circle_endpoints Ar Cr (X t) O AC_nondegenerate Hs).
    - pose proof (f_of_t t) as H. rewrite Hf in H. lra.
    - symmetry. exact HC.
  Qed.

  (* good t: X t is a witness to arc_chord_intersects. *)
  Definition good (t : R) : Prop :=
    0 <= t <= 1 /\ aR*t*t + bR*t + cR = 0 /\
    (cross_R_pt Ar Cr (X t) = 0 \/ 0 < sigM * cross_R_pt Ar Cr (X t)).

  Lemma witness_iff : arc_chord_intersects arc Pr P1r <-> exists t, good t.
  Proof.
    split.
    - intros [Q [Hb [Hc Hs]]].
      apply between_X in Hb. destruct Hb as [t [Ht HQ]]. subst Q.
      exists t. split; [exact Ht |].
      split; [apply on_circle_iff; exact Hc |].
      apply span_iff in Hs. destruct Hs as [Hs | [Hs | Hs]].
      + right. exact Hs.
      + left. rewrite Hs. apply cross_R_pt_at_A.
      + left. rewrite Hs. apply cross_R_pt_at_C.
    - intros [t [Ht [Hf Hs]]].
      exists (X t). split; [apply between_X; exists t; split; [exact Ht | reflexivity] |].
      split; [apply on_circle_iff; exact Hf |].
      apply span_iff. destruct Hs as [Hs | Hs].
      + right. exact (root_on_line_is_endpoint t Hf Hs).
      + left. exact Hs.
  Qed.

  (* -- the classifier on its non-Decline domain ------------------------------ *)

  Lemma I_line_arc_q_here : I_line_arc_q P P1 A M C = classify_signs sd.
  Proof.
    unfold I_line_arc_q, sd.
    destruct (Qeq_bool (qarc_D A M C) 0) eqn:E1; [apply Qeq_bool_iff in E1; contradiction |].
    destruct (Qeq_bool (qchord_L2 P P1) 0) eqn:E2; [apply Qeq_bool_iff in E2; contradiction |].
    reflexivity.
  Qed.

  (* -- Δ < 0: no root, no witness --------------------------------------------- *)

  Lemma no_witness_disc_neg : discR < 0 -> ~ (exists t, good t).
  Proof.
    intros Hneg [t [_ [Hf _]]].
    destruct (quad_roots aR bR cR t HaR Hf) as [H0 _]. unfold discR in Hneg. lra.
  Qed.

  (* -- Δ = 0: the kiss t0 = -b/(2a), side sign = sign U ---------------------- *)

  Lemma touch_keep_iff :
    discR = 0 -> (touch_keep_b sd = true <-> good (-bR / (2*aR))).
  Proof.
    intro H0. pose proof HaR as Ha.
    set (s := -bR / (2*aR)).
    assert (H2 : s * (2*aR) = -bR) by (unfold s; field; lra).
    assert (Hf : aR*s*s + bR*s + cR = 0).
    { pose proof (quad_root_plus_is_root aR bR cR Ha) as Hr.
      unfold discR in H0. rewrite H0 in Hr. specialize (Hr (Rle_refl 0)). cbv zeta in Hr.
      rewrite sqrt_0 in Hr. replace ((-bR + 0)/(2*aR)) with s in Hr by (unfold s; field; lra). exact Hr. }
    assert (Hside : cross_R_pt Ar Cr (X s) * (2*aR) = UR).
    { rewrite side_X. unfold UR, sigP. replace bR with (- (s * (2*aR))) by lra. ring. }
    unfold touch_keep_b, s_ge0_b, s_le1_b.
    rewrite !andb_true_iff.
    rewrite (is_le0_spec _ _ sd_b), (is_ge0_spec _ _ sd_b2a).
    rewrite (on_span_b_spec _ _ _ _ sd_U sd_M sigM_nonzero).
    unfold good. split.
    - intros [[Hb Hb2] Hsp]. repeat split.
      + nra.
      + nra.
      + exact Hf.
      + destruct Hsp as [Hu | Hu]; [left | right]; nra.
    - intros [[Hs0 Hs1] [_ Hsp]]. repeat split.
      + nra.
      + nra.
      + destruct Hsp as [Hu | Hu]; [left | right]; nra.
  Qed.

  Lemma good_disc0_is_kiss :
    discR = 0 -> forall t, good t -> t = -bR / (2*aR).
  Proof.
    intros H0 t [_ [Hf _]].
    destruct (quad_roots aR bR cR t HaR Hf) as [_ [Ht | Ht]]; unfold discR in H0; rewrite H0, sqrt_0 in Ht;
      rewrite Ht; field; pose proof HaR; lra.
  Qed.

  (* -- Δ > 0: the two roots -------------------------------------------------- *)

  Lemma keep_plus_iff :
    0 < discR -> (keep_plus_b sd = true <-> good ((-bR + sqrt discR) / (2*aR))).
  Proof.
    intro Hpos. pose proof HaR as Ha.
    set (s := -bR / (2*aR)). set (rho := sqrt discR / (2*aR)).
    assert (Htp : (-bR + sqrt discR) / (2*aR) = s + rho) by (unfold s, rho; field; lra).
    rewrite Htp.
    assert (Hf : aR*(s+rho)*(s+rho) + bR*(s+rho) + cR = 0).
    { pose proof (quad_root_plus_is_root aR bR cR Ha (Rlt_le _ _ Hpos)) as Hr. cbv zeta in Hr.
      rewrite <- Htp. exact Hr. }
    assert (Hside : cross_R_pt Ar Cr (X (s + rho)) * (2*aR) = UR + kapR * sqrt discR).
    { rewrite side_X. unfold UR, sigP, rho, s. field. lra. }
    pose proof (comp_sign_lin_rad_spec UR kapR discR _ _ _ Hpos sd_U sd_kappa sd_U2) as Hsg.
    unfold keep_plus_b, plus_in01_b, s_ge0_b, s_le1_b, sg_plus_c.
    rewrite !andb_true_iff, !orb_true_iff.
    rewrite (is_le0_spec _ _ sd_f0), (is_le0_spec _ _ sd_b), (is_ge0_spec _ _ sd_f1), (is_ge0_spec _ _ sd_b2a).
    rewrite (on_span_b_spec _ _ _ _ Hsg sd_M sigM_nonzero).
    pose proof (vieta_tp_ge0 aR bR cR Ha Hpos) as Hge.
    pose proof (vieta_tp_le1 aR bR cR Ha Hpos) as Hle.
    pose proof (vieta_s_ge0 aR bR Ha) as Hsge.
    pose proof (vieta_s_le1 aR bR Ha) as Hsle.
    cbv zeta in Hge, Hle, Hsge, Hsle.
    fold discR in Hge, Hle. fold rho in Hge, Hle. fold s in Hge, Hle, Hsge, Hsle.
    unfold good. split.
    - intros [[Hin01a [Hin01b Hin01c]] Hsp].
      repeat split.
      + apply Hge. destruct Hin01a as [H|H]; [left; exact H | right; apply Hsge; exact H].
      + apply Hle. split; [exact Hin01b | apply Hsle; exact Hin01c].
      + exact Hf.
      + destruct Hsp as [Hu | Hu]; [left | right]; nra.
    - intros [[Hge0 Hle1] [_ Hsp]].
      repeat split.
      + destruct (proj1 Hge Hge0) as [H|H]; [left; exact H | right; apply Hsge; exact H].
      + exact (proj1 (proj1 Hle Hle1)).
      + apply Hsle. exact (proj2 (proj1 Hle Hle1)).
      + destruct Hsp as [Hu | Hu]; [left | right]; nra.
  Qed.

  Lemma keep_minus_iff :
    0 < discR -> (keep_minus_b sd = true <-> good ((-bR - sqrt discR) / (2*aR))).
  Proof.
    intro Hpos. pose proof HaR as Ha.
    set (s := -bR / (2*aR)). set (rho := sqrt discR / (2*aR)).
    assert (Htm : (-bR - sqrt discR) / (2*aR) = s - rho) by (unfold s, rho; field; lra).
    rewrite Htm.
    assert (Hf : aR*(s-rho)*(s-rho) + bR*(s-rho) + cR = 0).
    { pose proof (quad_root_minus_is_root aR bR cR Ha (Rlt_le _ _ Hpos)) as Hr. cbv zeta in Hr.
      rewrite <- Htm. exact Hr. }
    assert (Hside : cross_R_pt Ar Cr (X (s - rho)) * (2*aR) = UR + (- kapR) * sqrt discR).
    { rewrite side_X. unfold UR, sigP, rho, s. field. lra. }
    assert (HU2' : cmp_spec (sg_U2_vs_disc_kappa2 sd) (UR*UR) (discR*(-kapR)*(-kapR))).
    { replace (discR*(-kapR)*(-kapR)) with (discR*kapR*kapR) by ring. exact sd_U2. }
    pose proof (comp_sign_lin_rad_spec UR (-kapR) discR _ _ _ Hpos sd_U (CompOpp_spec _ _ sd_kappa) HU2') as Hsg.
    unfold keep_minus_b, minus_in01_b, s_ge0_b, s_le1_b, sg_minus_c.
    rewrite !andb_true_iff, !orb_true_iff.
    rewrite (is_ge0_spec _ _ sd_f0), (is_le0_spec _ _ sd_b), (is_le0_spec _ _ sd_f1), (is_ge0_spec _ _ sd_b2a).
    rewrite (on_span_b_spec _ _ _ _ Hsg sd_M sigM_nonzero).
    pose proof (vieta_tm_ge0 aR bR cR Ha Hpos) as Hge.
    pose proof (vieta_tm_le1 aR bR cR Ha Hpos) as Hle.
    pose proof (vieta_s_ge0 aR bR Ha) as Hsge.
    pose proof (vieta_s_le1 aR bR Ha) as Hsle.
    cbv zeta in Hge, Hle, Hsge, Hsle.
    fold discR in Hge, Hle. fold rho in Hge, Hle. fold s in Hge, Hle, Hsge, Hsle.
    unfold good. split.
    - intros [[[Hin01a Hin01b] Hin01c] Hsp].
      repeat split.
      + apply Hge. split; [exact Hin01a | apply Hsge; exact Hin01b].
      + apply Hle. destruct Hin01c as [H|H]; [left; exact H | right; apply Hsle; exact H].
      + exact Hf.
      + destruct Hsp as [Hu | Hu]; [left | right]; nra.
    - intros [[Hge0 Hle1] [_ Hsp]].
      repeat split.
      + exact (proj1 (proj1 Hge Hge0)).
      + apply Hsge. exact (proj2 (proj1 Hge Hge0)).
      + destruct (proj1 Hle Hle1) as [H|H]; [left; exact H | right; apply Hsle; exact H].
      + destruct Hsp as [Hu | Hu]; [left | right]; nra.
  Qed.

  Lemma good_is_root :
    0 < discR -> forall t, good t ->
      t = (-bR + sqrt discR) / (2*aR) \/ t = (-bR - sqrt discR) / (2*aR).
  Proof.
    intros Hpos t [_ [Hf _]].
    destruct (quad_roots aR bR cR t HaR Hf) as [_ Ht]. exact Ht.
  Qed.

  (* -- headline ---------------------------------------------------------------- *)

  (* WITNESS {"claimId":"0007-line-arc-r","topic":"overlay","lemma":"I_line_arc_q_iff_intersects","title":"On its non-Decline domain the exact chord x arc classifier is not Empty iff the real chord meets the real arc (ArcIntersect.arc_chord_intersects) -- soundness and completeness of the sign tests through Q2R","file":"theories/CircularCookLineArcR.v","witness":"0007-line-arc-r","board":"ADR-0007"} *)
  Theorem I_line_arc_q_iff_intersects :
    I_line_arc_q P P1 A M C <> ILAEmpty <-> arc_chord_intersects arc Pr P1r.
  Proof.
    rewrite I_line_arc_q_here, witness_iff.
    pose proof sd_disc as Hd.
    assert (Hempty := classify_signs_empty_iff sd).
    destruct (sg_disc sd) eqn:Hdisc; cbn in Hd.
    - (* Δ = 0 *)
      split.
      + intro Hne. destruct (touch_keep_b sd) eqn:Ht.
        * exists (-bR / (2*aR)). apply touch_keep_iff; [exact Hd | exact Ht].
        * exfalso. apply Hne. apply Hempty. right. left. split; first [reflexivity | exact Hdisc | exact Ht].
      + intros [t Hg] He. apply Hempty in He.
        destruct He as [He | [[_ He] | [He _]]]; try (rewrite Hdisc in He); try discriminate.
        rewrite (good_disc0_is_kiss Hd t Hg) in Hg.
        rewrite <- (touch_keep_iff Hd) in Hg. congruence.
    - (* Δ < 0 *)
      split.
      + intro Hne. exfalso. apply Hne. apply Hempty. left. first [reflexivity | exact Hdisc].
      + intro Hw. exfalso. exact (no_witness_disc_neg Hd Hw).
    - (* Δ > 0 *)
      split.
      + intro Hne. destruct (keep_plus_b sd) eqn:Hp.
        * eexists. apply keep_plus_iff; [exact Hd | exact Hp].
        * destruct (keep_minus_b sd) eqn:Hm.
          -- eexists. apply keep_minus_iff; [exact Hd | exact Hm].
          -- exfalso. apply Hne. apply Hempty. right. right. repeat split; first [reflexivity | assumption].
      + intros [t Hg] He. apply Hempty in He.
        destruct He as [He | [[He _] | [_ [Hp Hm]]]]; try (rewrite Hdisc in He); try discriminate.
        destruct (good_is_root Hd t Hg) as [Ht | Ht]; subst t.
        * rewrite <- (keep_plus_iff Hd) in Hg. congruence.
        * rewrite <- (keep_minus_iff Hd) in Hg. congruence.
  Qed.

  Corollary I_line_arc_q_sound :
    I_line_arc_q P P1 A M C <> ILAEmpty -> arc_chord_intersects arc Pr P1r.
  Proof. apply I_line_arc_q_iff_intersects. Qed.

  Corollary I_line_arc_q_complete :
    I_line_arc_q P P1 A M C = ILAEmpty -> ~ arc_chord_intersects arc Pr P1r.
  Proof. intros He Hi. apply I_line_arc_q_iff_intersects in Hi. exact (Hi He). Qed.
End Bridge.

(* -------------------------------------------------------------------------- *)
(* §6  The integer form, through lift_pt.                                     *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-line-arc-r","topic":"overlay","lemma":"I_line_arc_z_iff_intersects","title":"The integer classifier I_line_arc_z is not Empty iff the real chord meets the real arc, for D <> 0 and a non-degenerate chord, via I_line_arc_lift_agrees","file":"theories/CircularCookLineArcR.v","witness":"0007-line-arc-r","board":"ADR-0007"} *)
Theorem I_line_arc_z_iff_intersects :
  forall P P1 A M C : ZPt,
    zarc_D A M C <> 0%Z ->
    ~ (zx P1 - zx P = 0 /\ zy P1 - zy P = 0)%Z ->
    I_line_arc_z P P1 A M C <> ILAEmpty
    <-> arc_chord_intersects (arc_of (lift_pt A) (lift_pt M) (lift_pt C))
                             (qpt_R (lift_pt P)) (qpt_R (lift_pt P1)).
Proof.
  intros P P1 A M C HD HL.
  rewrite <- I_line_arc_lift_agrees.
  apply I_line_arc_q_iff_intersects.
  - intro H. apply HD. rewrite lift_qarc_D in H. apply (inject_Z_injective _ 0). exact H.
  - intro H. apply HL. rewrite lift_qchord_L2 in H.
    apply z_sum_sq_eq0_iff. apply (inject_Z_injective _ 0). exact H.
Qed.

Print Assumptions comp_sign_lin_rad_spec.
Print Assumptions quad_roots.
Print Assumptions vieta_tp_ge0.
Print Assumptions line_circle_endpoints.
Print Assumptions center_Q2R.
Print Assumptions I_line_arc_q_iff_intersects.
Print Assumptions I_line_arc_q_sound.
Print Assumptions I_line_arc_q_complete.
Print Assumptions I_line_arc_z_iff_intersects.
