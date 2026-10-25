(* ============================================================================
   NetTopologySuite.Proofs.ClothoidPlacement
   ----------------------------------------------------------------------------
   Curvature of a placed clothoid. A placement is o + M p with M a 2x2
   linear map. For a curve with derivatives v, a the placed curve has
   derivatives M v, M a (placed_deriv), so

     curvature = det M * cross(v, a) / |M v|^3      (signed_curv_lin)

   For a similarity M = lam * R (lam > 0, R a rotation) this is
   kappa / lam (signed_curv_similarity, cloth_similarity_curvature), and
   the placed curve keeps a linear law (k0 / lam, k1 / lam, lam * L) in
   placed arc length (cloth_similarity_scaled_law). For a
   reflection-similarity it is - kappa / lam (signed_curv_reflection).
   For a general linear M it need not be kappa / lam nor the
   constructive t / A^2 (cloth_placed_curvature); counterexample
   geos_shear_curvature_ne_naive.

   The host AffPlace is rigid or reflected only: it reads the direction
   of ref1 and the sign of cross(ref1, ref2) (SheetHenClothoidCore
   cloth_sigma / cloth_cos0 / cloth_sin0). A sheared or other
   non-similarity placement exists only as the external placed o M of
   this file. GEOS's frame u = (2, 0), v = (1/2, 1) given to the host
   directly gives the naive 1/25 (host_affplace_curvature_ignores_shear).

   Reverse under any linear M: the signed curvature flips sign and the
   ends swap (cloth_placed_rev_law; no similarity assumption). The
   split / linear-curvature law of ClothoidTraversal carries over to
   placed curves only for similarity placements: the sheared curvature
   is not monotone along the window (geos_shear_curvature_not_affine).
   The converse for every window and every M is ClothoidShearLaw.v
   (claimId cloth-linear-law-iff-similarity); closure of placements under
   affine maps is ClothoidAffine.v (claimId cloth-affine-closure).

   GEOS #1566 (libgeos/geos PR, pinned at 6eb13d1; fixed later on
   libgeos/geos#1566 by 78df3cf "Return the placed curvature of a
   sheared clothoid", in the PR head f93c059): at 6eb13d1
   Clothoid::curvatureOf returns direction * t / A^2 when the frame is
   not a similarity. Oracle case "sheared placement" (u = (2, 0),
   v = (1/2, 1), A = 5, t0 = 1, t1 = 12; geos_shear_columns), oracle
   values from the GEOS test table:
     start 0.009855916895262518 in (0.0098559168952, 0.0098559168953)
           (geos_shear_curvature_enclosure); 6eb13d1 gave 1/25;
     end   0.15895182898207377 in (0.158948, 0.158953)
           (geos_shear_end_curvature_enclosure); 6eb13d1 gave 12/25;
     reversed ends: the negated, swapped enclosures
           (geos_shear_rev_curvature_ends).
   Each enclosure also states that V and Acc are the placed derivatives
   (geos_shear_placed_derivs_at). Enclosures come from Stdlib
   cos_bound / sin_bound at n = 1, double-angle steps and rounded
   rational bounds, all discharged by lra. The Q twin
   geos_shear_q_check recomputes the start comparisons in Q by
   vm_compute as a cross-check; no proof uses it.

   Parked: an error bound for far-field Fresnel quadrature (GEOS uses
   fixed 0.5-wide 16-point Gauss-Legendre panels past the series
   window). LipInt is a dyadic Riemann integral; there is no
   Gauss-Legendre remainder theorem in the corpus, so no bound is
   stated. Parked: placed length (the length of placed o M, which GEOS
   getLength has to integrate across the inflection for a sheared
   frame; no placed length is stated here). Parked: the CompoundCurve junction snap (GEOS 458f82e snaps
   clothoid endpoints to their neighbours; not modelled). Parked: Z / M
   (the placement here is planar; GEOS frames with uz, vz <> 0 and
   measures are out of scope).

   claimId: none new. No claim row. No WITNESS.
   3-axiom host. No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
   ========================================================================== *)

From Stdlib Require Import Reals Lra QArith Ranalysis1.
From NTS.Proofs Require Import Distance SheetHenClothoidCore ClothoidNorm2
  SignedCurvature SheetHenClothoidFrames SheetHenClothoidBounds ClothoidLinearize
  ClothoidTraversal.
Local Open Scope R_scope.

Record Lin2 : Type := mkLin2 { l11 : R; l12 : R; l21 : R; l22 : R }.

Definition lin_ap (M : Lin2) (p : Point) : Point :=
  mkPoint (l11 M * px p + l12 M * py p) (l21 M * px p + l22 M * py p).

Definition lin_det (M : Lin2) : R := l11 M * l22 M - l12 M * l21 M.

Definition placed (o : Point) (M : Lin2) (p : Point) : Point :=
  mkPoint (px o + px (lin_ap M p)) (py o + py (lin_ap M p)).

Lemma curv_cross_lin : forall M v a,
  curv_cross (lin_ap M v) (lin_ap M a) = lin_det M * curv_cross v a.
Proof. intros. unfold curv_cross, lin_ap, lin_det. cbn. ring. Qed.

Lemma signed_curv_lin : forall M v a,
  signed_curv (lin_ap M v) (lin_ap M a)
    = lin_det M * curv_cross v a /
      (sqrt (curv_speed2 (lin_ap M v)) * sqrt (curv_speed2 (lin_ap M v))
       * sqrt (curv_speed2 (lin_ap M v))).
Proof. intros. unfold signed_curv. rewrite curv_cross_lin. reflexivity. Qed.

Definition lin_sim (lam co si : R) : Lin2 :=
  mkLin2 (lam * co) (- (lam * si)) (lam * si) (lam * co).

Definition lin_refl (lam co si : R) : Lin2 :=
  mkLin2 (lam * co) (lam * si) (lam * si) (- (lam * co)).

Lemma curv_speed2_nonneg : forall v, 0 <= curv_speed2 v.
Proof. intro v. unfold curv_speed2. nra. Qed.

Lemma lin_sim_speed2 : forall lam co si v, co * co + si * si = 1 ->
  curv_speed2 (lin_ap (lin_sim lam co si) v) = lam * lam * curv_speed2 v.
Proof.
  intros lam co si v H. unfold curv_speed2, lin_ap, lin_sim. cbn.
  replace ((lam * co * px v + - (lam * si) * py v) * (lam * co * px v + - (lam * si) * py v) +
           (lam * si * px v + lam * co * py v) * (lam * si * px v + lam * co * py v))
    with (lam * lam * (co * co + si * si) * (px v * px v + py v * py v)) by ring.
  rewrite H. ring.
Qed.

Lemma lin_refl_speed2 : forall lam co si v, co * co + si * si = 1 ->
  curv_speed2 (lin_ap (lin_refl lam co si) v) = lam * lam * curv_speed2 v.
Proof.
  intros lam co si v H. unfold curv_speed2, lin_ap, lin_refl. cbn.
  replace ((lam * co * px v + lam * si * py v) * (lam * co * px v + lam * si * py v) +
           (lam * si * px v + - (lam * co) * py v) * (lam * si * px v + - (lam * co) * py v))
    with (lam * lam * (co * co + si * si) * (px v * px v + py v * py v)) by ring.
  rewrite H. ring.
Qed.

Lemma lin_sim_det : forall lam co si, co * co + si * si = 1 ->
  lin_det (lin_sim lam co si) = lam * lam.
Proof.
  intros lam co si H. unfold lin_det, lin_sim. cbn.
  replace (lam * co * (lam * co) - - (lam * si) * (lam * si))
    with (lam * lam * (co * co + si * si)) by ring.
  rewrite H. ring.
Qed.

Lemma lin_refl_det : forall lam co si, co * co + si * si = 1 ->
  lin_det (lin_refl lam co si) = - (lam * lam).
Proof.
  intros lam co si H. unfold lin_det, lin_refl. cbn.
  replace (lam * co * - (lam * co) - lam * si * (lam * si))
    with (- (lam * lam * (co * co + si * si))) by ring.
  rewrite H. ring.
Qed.

Lemma sqrt_scale_sq : forall lam S, 0 < lam -> 0 <= S ->
  sqrt (lam * lam * S) = lam * sqrt S.
Proof.
  intros lam S Hl HS.
  rewrite sqrt_mult_alt by nra.
  rewrite sqrt_square by lra. reflexivity.
Qed.

Theorem signed_curv_similarity : forall lam co si v a,
  0 < lam -> co * co + si * si = 1 -> curv_speed2 v <> 0 ->
  signed_curv (lin_ap (lin_sim lam co si) v) (lin_ap (lin_sim lam co si) a)
    = signed_curv v a / lam.
Proof.
  intros lam co si v a Hl Hu Hv.
  rewrite signed_curv_lin, lin_sim_det, lin_sim_speed2 by exact Hu.
  rewrite sqrt_scale_sq by (try exact Hl; apply curv_speed2_nonneg).
  assert (Hs : 0 < sqrt (curv_speed2 v)).
  { apply sqrt_lt_R0. pose proof (curv_speed2_nonneg v). lra. }
  unfold signed_curv. field. split; lra.
Qed.

Theorem signed_curv_reflection : forall lam co si v a,
  0 < lam -> co * co + si * si = 1 -> curv_speed2 v <> 0 ->
  signed_curv (lin_ap (lin_refl lam co si) v) (lin_ap (lin_refl lam co si) a)
    = - (signed_curv v a / lam).
Proof.
  intros lam co si v a Hl Hu Hv.
  rewrite signed_curv_lin, lin_refl_det, lin_refl_speed2 by exact Hu.
  rewrite sqrt_scale_sq by (try exact Hl; apply curv_speed2_nonneg).
  assert (Hs : 0 < sqrt (curv_speed2 v)).
  { apply sqrt_lt_R0. pose proof (curv_speed2_nonneg v). lra. }
  unfold signed_curv. field. split; lra.
Qed.

Lemma placed_deriv : forall o M (f : R -> Point) t v,
  derivable_pt_lim (fun u => px (f u)) t (px v) ->
  derivable_pt_lim (fun u => py (f u)) t (py v) ->
  derivable_pt_lim (fun u => px (placed o M (f u))) t (px (lin_ap M v)) /\
  derivable_pt_lim (fun u => py (placed o M (f u))) t (py (lin_ap M v)).
Proof.
  intros o M f t v Hx Hy.
  assert (Gen : forall k a b, derivable_pt_lim
            (fun u => k + (a * px (f u) + b * py (f u))) t (a * px v + b * py v)).
  { intros k a b.
    apply derivable_pt_lim_ext with
      (f := plus_fct (fct_cte k)
              (plus_fct (mult_real_fct a (fun u => px (f u)))
                        (mult_real_fct b (fun u => py (f u))))).
    - intro u. reflexivity.
    - replace (a * px v + b * py v) with (0 + (a * px v + b * py v)) by ring.
      apply derivable_pt_lim_plus; [apply derivable_pt_lim_const|].
      apply derivable_pt_lim_plus; apply derivable_pt_lim_scal; assumption. }
  split; [apply (Gen (px o) (l11 M) (l12 M)) | apply (Gen (py o) (l21 M) (l22 M))].
Qed.

Lemma cloth_arc_cross : forall c s, cloth_h2 c <> 0 -> cloth_d c <> 0 ->
  curv_cross (cloth_arc_v c s) (cloth_arc_a c s)
    = cloth_tk0 c + (cloth_tk1 c - cloth_tk0 c) * s / cloth_tlen c.
Proof.
  intros c s Hh Hd.
  rewrite <- cloth_kappa_traversal_linear by exact Hd.
  rewrite <- cloth_arc_signed_curv by exact Hh.
  unfold signed_curv. rewrite cloth_arc_speed2, sqrt_1 by exact Hh. field.
Qed.

(* Any linear placement: curvature det M * kappa / |M v|^3. *)
Theorem cloth_placed_curvature : forall c o M s,
  cloth_A c <> 0 -> cloth_h2 c <> 0 -> cloth_d c <> 0 ->
  let V := lin_ap M (cloth_arc_v c s) in
  let Acc := lin_ap M (cloth_arc_a c s) in
  derivable_pt_lim (fun u => px (placed o M (cloth_arc c u))) s (px V) /\
  derivable_pt_lim (fun u => py (placed o M (cloth_arc c u))) s (py V) /\
  derivable_pt_lim (fun u => px (lin_ap M (cloth_arc_v c u))) s (px Acc) /\
  derivable_pt_lim (fun u => py (lin_ap M (cloth_arc_v c u))) s (py Acc) /\
  signed_curv V Acc
    = lin_det M * (cloth_tk0 c + (cloth_tk1 c - cloth_tk0 c) * s / cloth_tlen c)
      / (sqrt (curv_speed2 V) * sqrt (curv_speed2 V) * sqrt (curv_speed2 V)).
Proof.
  intros c o M s HA Hh Hd V Acc.
  destruct (cloth_arc_unit_speed_linear_curvature c s HA Hh Hd)
    as (Hx & Hy & Hvx & Hvy & _ & _).
  destruct (placed_deriv o M (cloth_arc c) s (cloth_arc_v c s) Hx Hy) as [P1 P2].
  destruct (placed_deriv (mkPoint 0 0) M (cloth_arc_v c) s (cloth_arc_a c s) Hvx Hvy)
    as [P3 P4].
  split; [exact P1|]. split; [exact P2|].
  split.
  - eapply derivable_pt_lim_ext; [|exact P3].
    intro u. unfold placed. cbn. ring.
  - split.
    + eapply derivable_pt_lim_ext; [|exact P4].
      intro u. unfold placed. cbn. ring.
    + unfold V, Acc. rewrite signed_curv_lin, cloth_arc_cross by assumption.
      reflexivity.
Qed.

(* Similarity placement: curvature kappa / lambda. *)
Theorem cloth_similarity_curvature : forall c o lam co si s,
  cloth_A c <> 0 -> cloth_h2 c <> 0 -> cloth_d c <> 0 ->
  0 < lam -> co * co + si * si = 1 ->
  signed_curv (lin_ap (lin_sim lam co si) (cloth_arc_v c s))
              (lin_ap (lin_sim lam co si) (cloth_arc_a c s))
    = (cloth_tk0 c + (cloth_tk1 c - cloth_tk0 c) * s / cloth_tlen c) / lam /\
  derivable_pt_lim (fun u => px (placed o (lin_sim lam co si) (cloth_arc c u))) s
    (px (lin_ap (lin_sim lam co si) (cloth_arc_v c s))) /\
  derivable_pt_lim (fun u => py (placed o (lin_sim lam co si) (cloth_arc c u))) s
    (py (lin_ap (lin_sim lam co si) (cloth_arc_v c s))).
Proof.
  intros c o lam co si s HA Hh Hd Hl Hu.
  destruct (cloth_placed_curvature c o (lin_sim lam co si) s HA Hh Hd)
    as (P1 & P2 & _ & _ & _).
  split; [| split; assumption].
  rewrite signed_curv_similarity by (try assumption; rewrite cloth_arc_speed2 by exact Hh; lra).
  rewrite cloth_arc_signed_curv by exact Hh.
  rewrite cloth_kappa_traversal_linear by exact Hd. reflexivity.
Qed.

(* Similarity placement, read as a traversal law of the placed curve:
   speed lam, placed arc length lam * s, curvature linear in placed arc
   length with law (k0 / lam, k1 / lam, lam * L). Only for a
   similarity: a sheared placement is not linear in arc length
   (geos_shear_curvature_not_affine). *)
Theorem cloth_similarity_scaled_law : forall c lam co si s,
  cloth_A c <> 0 -> cloth_h2 c <> 0 -> cloth_d c <> 0 ->
  0 < lam -> co * co + si * si = 1 ->
  sqrt (curv_speed2 (lin_ap (lin_sim lam co si) (cloth_arc_v c s))) = lam /\
  signed_curv (lin_ap (lin_sim lam co si) (cloth_arc_v c s))
              (lin_ap (lin_sim lam co si) (cloth_arc_a c s))
    = cloth_tk0 c / lam
      + (cloth_tk1 c / lam - cloth_tk0 c / lam) * (lam * s) / (lam * cloth_tlen c).
Proof.
  intros c lam co si s HA Hh Hd Hl Hu.
  pose proof (cloth_tlen_pos c Hd) as HL.
  split.
  - rewrite lin_sim_speed2, cloth_arc_speed2 by assumption.
    rewrite Rmult_1_r. apply sqrt_square. lra.
  - destruct (cloth_similarity_curvature c (mkPoint 0 0) lam co si s HA Hh Hd Hl Hu)
      as (K & _ & _).
    rewrite K. field. split; lra.
Qed.

(* Reverse under any linear placement: the placed reverse at s is the
   placed forward at L - s with the tangent negated, so the signed
   curvature flips sign. No similarity assumption. *)
Lemma cloth_rev_station : forall c s, cloth_d c <> 0 ->
  cloth_station (cloth_rev c) s = cloth_station c (cloth_tlen c - s).
Proof.
  intros c s Hd. unfold cloth_station. rewrite cloth_rev_dir by exact Hd.
  rewrite <- (cloth_dir_abs c).
  pose proof (cloth_dir_sq c) as HD.
  unfold cloth_rev, mk_cloth, cloth_d. cbn [cloth_sd cloth_ed].
  replace (cloth_sd c + cloth_dir c * (cloth_dir c * (cloth_ed c - cloth_sd c) - s))
    with (cloth_sd c + (cloth_dir c * cloth_dir c) * (cloth_ed c - cloth_sd c)
          - cloth_dir c * s) by ring.
  rewrite HD. ring.
Qed.

Lemma cloth_rev_vx : forall c u, cloth_vx (cloth_rev c) u = cloth_vx c u.
Proof. intros [pl A sd ed m0 m1] u. reflexivity. Qed.

Lemma cloth_rev_vy : forall c u, cloth_vy (cloth_rev c) u = cloth_vy c u.
Proof. intros [pl A sd ed m0 m1] u. reflexivity. Qed.

Lemma signed_curv_neg_tangent : forall v a,
  signed_curv (mkPoint (- px v) (- py v)) a = - signed_curv v a.
Proof.
  intros v a. unfold signed_curv.
  replace (curv_speed2 (mkPoint (- px v) (- py v))) with (curv_speed2 v)
    by (unfold curv_speed2; cbn; ring).
  unfold curv_cross. cbn. unfold Rdiv. ring.
Qed.

Theorem cloth_placed_rev_law : forall c M s, cloth_d c <> 0 ->
  signed_curv (lin_ap M (cloth_arc_v (cloth_rev c) s))
              (lin_ap M (cloth_arc_a (cloth_rev c) s))
    = - signed_curv (lin_ap M (cloth_arc_v c (cloth_tlen c - s)))
                    (lin_ap M (cloth_arc_a c (cloth_tlen c - s))).
Proof.
  intros c M s Hd.
  assert (Ev : lin_ap M (cloth_arc_v (cloth_rev c) s)
               = mkPoint (- px (lin_ap M (cloth_arc_v c (cloth_tlen c - s))))
                         (- py (lin_ap M (cloth_arc_v c (cloth_tlen c - s))))).
  { unfold cloth_arc_v. rewrite cloth_rev_dir, cloth_rev_station by exact Hd.
    rewrite !cloth_rev_vx, !cloth_rev_vy. unfold lin_ap. cbn. f_equal; ring. }
  assert (Ea : cloth_arc_a (cloth_rev c) s = cloth_arc_a c (cloth_tlen c - s)).
  { unfold cloth_arc_a. rewrite cloth_rev_station by exact Hd.
    rewrite !cloth_rev_kappa, !cloth_rev_vx, !cloth_rev_vy. reflexivity. }
  rewrite Ev, Ea. apply signed_curv_neg_tangent.
Qed.

(* GEOS #1566 oracle case "sheared placement": u = (2, 0), v = (1/2, 1),
   A = 5, t0 = 1, t1 = 12. *)
Definition geos_shear : Lin2 := mkLin2 2 (1 / 2) 0 1.

Definition geos_shear_egg : ClothoidEgg :=
  mk_cloth (place_east (mkPoint 3 4)) 5 1 12 None None.

(* GEOS places P(t) = origin + A C2(t/A) u + A S2(t/A) v: the columns of
   geos_shear are u and v, and geos_shear_egg is the unit-frame egg. *)
Lemma geos_shear_columns :
  lin_ap geos_shear (mkPoint 1 0) = mkPoint 2 0 /\
  lin_ap geos_shear (mkPoint 0 1) = mkPoint (1 / 2) 1.
Proof. unfold lin_ap, geos_shear. cbn. split; f_equal; ring. Qed.

Lemma geos_shear_det : lin_det geos_shear = 2.
Proof. unfold lin_det, geos_shear. cbn. ring. Qed.

Lemma geos_shear_sigma : cloth_sigma geos_shear_egg = 1.
Proof.
  unfold cloth_sigma, cloth_cross, geos_shear_egg, mk_cloth. cbn [cloth_place].
  rewrite east_cross. destruct (Rle_dec 0 1); [reflexivity | lra].
Qed.

Lemma geos_shear_frame :
  cloth_cos0 geos_shear_egg = 1 /\ cloth_sin0 geos_shear_egg = 0.
Proof.
  unfold cloth_cos0, cloth_sin0, cloth_hypot, cloth_h2, geos_shear_egg, mk_cloth.
  cbn [cloth_place aff_ref1 place_east px py].
  rewrite east_h2, sqrt_1. split; field.
Qed.

Lemma geos_shear_d : cloth_d geos_shear_egg = 11.
Proof. unfold cloth_d, geos_shear_egg, mk_cloth. cbn. ring. Qed.

Lemma geos_shear_dir : cloth_dir geos_shear_egg = 1.
Proof.
  unfold cloth_dir. rewrite geos_shear_d. destruct (Rle_dec 0 11); [reflexivity | lra].
Qed.

Lemma geos_shear_tlen : cloth_tlen geos_shear_egg = 11.
Proof. unfold cloth_tlen. rewrite geos_shear_d. apply Rabs_right. lra. Qed.

(* GEOS curvatureOf at 6eb13d1 returns direction * t / A^2 for a
   non-similarity frame: 1 / 25 at the start and 12 / 25 at the end.
   Those are cloth_tk0 / cloth_tk1 of the constructive egg. *)
Lemma geos_shear_naive_value : cloth_tk0 geos_shear_egg = 1 / 25.
Proof.
  unfold cloth_tk0, cloth_kappa. rewrite geos_shear_dir, geos_shear_sigma.
  unfold geos_shear_egg, mk_cloth. cbn [cloth_sd cloth_A]. field.
Qed.

Lemma geos_shear_end_naive_value : cloth_tk1 geos_shear_egg = 12 / 25.
Proof.
  unfold cloth_tk1, cloth_kappa. rewrite geos_shear_dir, geos_shear_sigma.
  unfold geos_shear_egg, mk_cloth. cbn [cloth_ed cloth_A]. field.
Qed.

Lemma geos_shear_nondeg :
  cloth_A geos_shear_egg <> 0 /\ cloth_h2 geos_shear_egg <> 0 /\
  cloth_d geos_shear_egg <> 0.
Proof.
  split; [unfold geos_shear_egg, mk_cloth; cbn; lra|].
  split; [|rewrite geos_shear_d; lra].
  unfold cloth_h2, geos_shear_egg, mk_cloth. cbn [cloth_place].
  rewrite east_h2. lra.
Qed.

Lemma geos_shear_station : forall s, cloth_station geos_shear_egg s = 1 + s.
Proof.
  intro s. unfold cloth_station. rewrite geos_shear_dir.
  unfold geos_shear_egg, mk_cloth. cbn. ring.
Qed.

Lemma geos_shear_arc_v : forall s,
  cloth_arc_v geos_shear_egg s
    = mkPoint (cos ((1 + s) * (1 + s) / 50)) (sin ((1 + s) * (1 + s) / 50)).
Proof.
  intro s. destruct geos_shear_frame as [Hc Hs].
  assert (Ep : cloth_psi geos_shear_egg (1 + s) = (1 + s) * (1 + s) / 50).
  { unfold cloth_psi. rewrite geos_shear_sigma.
    unfold geos_shear_egg, mk_cloth. cbn [cloth_A]. field. }
  unfold cloth_arc_v. rewrite geos_shear_dir, geos_shear_station.
  unfold cloth_vx, cloth_vy. rewrite Hc, Hs, Ep. f_equal; ring.
Qed.

(* Squared speed of the sheared tangent at heading p. *)
Definition geos_shear_N (p : R) : R :=
  (2 * cos p + sin p * (1 / 2)) * (2 * cos p + sin p * (1 / 2)) + sin p * sin p.

(* V and Acc are the placed derivatives: V of the placed curve, Acc of
   s |-> M v(s), for every origin o. *)
Definition geos_shear_placed_derivs_at (s : R) (V Acc : Point) : Prop :=
  forall o : Point,
  derivable_pt_lim (fun u => px (placed o geos_shear (cloth_arc geos_shear_egg u))) s (px V) /\
  derivable_pt_lim (fun u => py (placed o geos_shear (cloth_arc geos_shear_egg u))) s (py V) /\
  derivable_pt_lim (fun u => px (lin_ap geos_shear (cloth_arc_v geos_shear_egg u))) s (px Acc) /\
  derivable_pt_lim (fun u => py (lin_ap geos_shear (cloth_arc_v geos_shear_egg u))) s (py Acc).

Lemma geos_shear_placed_derivs : forall s,
  geos_shear_placed_derivs_at s
    (lin_ap geos_shear (cloth_arc_v geos_shear_egg s))
    (lin_ap geos_shear (cloth_arc_a geos_shear_egg s)).
Proof.
  intros s o. destruct geos_shear_nondeg as (HA & Hh & Hd).
  destruct (cloth_placed_curvature geos_shear_egg o geos_shear s HA Hh Hd)
    as (P1 & P2 & P3 & P4 & _).
  repeat split; assumption.
Qed.

Lemma geos_shear_placed_curv : forall s,
  signed_curv (lin_ap geos_shear (cloth_arc_v geos_shear_egg s))
              (lin_ap geos_shear (cloth_arc_a geos_shear_egg s))
    = 2 * ((1 + s) / 25) /
      (sqrt (geos_shear_N ((1 + s) * (1 + s) / 50)) *
       sqrt (geos_shear_N ((1 + s) * (1 + s) / 50)) *
       sqrt (geos_shear_N ((1 + s) * (1 + s) / 50))).
Proof.
  intro s. destruct geos_shear_nondeg as (HA & Hh & Hd).
  rewrite signed_curv_lin, geos_shear_det, cloth_arc_cross by assumption.
  rewrite geos_shear_naive_value, geos_shear_end_naive_value, geos_shear_tlen.
  assert (EN : curv_speed2 (lin_ap geos_shear (cloth_arc_v geos_shear_egg s))
               = geos_shear_N ((1 + s) * (1 + s) / 50)).
  { rewrite geos_shear_arc_v. unfold curv_speed2, lin_ap, geos_shear, geos_shear_N.
    cbn. ring. }
  rewrite EN.
  replace (1 / 25 + (12 / 25 - 1 / 25) * s / 11) with ((1 + s) / 25) by field.
  reflexivity.
Qed.

(* Interval tools. Stdlib cos_bound / sin_bound at n = 1 on [0, 7/8]
   (7/8 <= PI/2 by PI2_bounds; Stdlib PI2_3_2 would print
   Classical_Prop.classic), the double-angle step, the squared speed, and the
   enclosure of k / sqrt(N)^3 from bounds on N. *)
Lemma cos_approx_3_poly : forall a,
  cos_approx a 3 = 1 - a ^ 2 / 2 + a ^ 4 / 24 - a ^ 6 / 720.
Proof.
  intro a. unfold cos_approx. cbn [sum_f_R0]. unfold cos_term.
  change (Factorial.fact (2 * 3)) with (6 * (5 * (4 * (3 * (2 * (1 * 1))))))%nat.
  change (Factorial.fact (2 * 2)) with (4 * (3 * (2 * (1 * 1))))%nat.
  change (Factorial.fact (2 * 1)) with (2 * (1 * 1))%nat.
  change (Factorial.fact (2 * 0)) with 1%nat.
  rewrite !mult_INR.
  change (2 * 3)%nat with 6%nat. change (2 * 2)%nat with 4%nat.
  change (2 * 1)%nat with 2%nat. change (2 * 0)%nat with 0%nat.
  simpl INR. field.
Qed.

Lemma cos_approx_4_poly : forall a,
  cos_approx a 4 = 1 - a ^ 2 / 2 + a ^ 4 / 24 - a ^ 6 / 720 + a ^ 8 / 40320.
Proof.
  intro a. change (cos_approx a 4) with (cos_approx a 3 + cos_term a 4).
  rewrite cos_approx_3_poly. unfold cos_term.
  change (Factorial.fact (2 * 4))
    with (8 * (7 * (6 * (5 * (4 * (3 * (2 * (1 * 1))))))))%nat.
  rewrite !mult_INR. change (2 * 4)%nat with 8%nat. simpl INR. field.
Qed.

Lemma sin_approx_3_poly : forall a,
  sin_approx a 3 = a - a ^ 3 / 6 + a ^ 5 / 120 - a ^ 7 / 5040.
Proof.
  intro a. unfold sin_approx. cbn [sum_f_R0]. unfold sin_term.
  change (Factorial.fact (2 * 3 + 1))
    with (7 * (6 * (5 * (4 * (3 * (2 * (1 * 1)))))))%nat.
  change (Factorial.fact (2 * 2 + 1)) with (5 * (4 * (3 * (2 * (1 * 1)))))%nat.
  change (Factorial.fact (2 * 1 + 1)) with (3 * (2 * (1 * 1)))%nat.
  change (Factorial.fact (2 * 0 + 1)) with (1 * 1)%nat.
  rewrite !mult_INR.
  change (2 * 3 + 1)%nat with 7%nat. change (2 * 2 + 1)%nat with 5%nat.
  change (2 * 1 + 1)%nat with 3%nat. change (2 * 0 + 1)%nat with 1%nat.
  simpl INR. field.
Qed.

Lemma sin_approx_4_poly : forall a,
  sin_approx a 4
    = a - a ^ 3 / 6 + a ^ 5 / 120 - a ^ 7 / 5040 + a ^ 9 / 362880.
Proof.
  intro a. change (sin_approx a 4) with (sin_approx a 3 + sin_term a 4).
  rewrite sin_approx_3_poly. unfold sin_term.
  change (Factorial.fact (2 * 4 + 1))
    with (9 * (8 * (7 * (6 * (5 * (4 * (3 * (2 * (1 * 1)))))))))%nat.
  rewrite !mult_INR. change (2 * 4 + 1)%nat with 9%nat. simpl INR. field.
Qed.

Lemma cos_sin_taylor9 : forall x, 0 <= x <= 7 / 8 ->
  (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 <= cos x <=
   1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320) /\
  (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 <= sin x <=
   x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880).
Proof.
  intros x Hx. pose proof PI2_bounds as Hpi.
  pose proof (cos_bound x 1 ltac:(lra) ltac:(lra)) as Hc.
  pose proof (sin_bound x 1 ltac:(lra) ltac:(lra)) as Hs.
  change (2 * 1 + 1)%nat with 3%nat in Hc, Hs.
  change (2 * (1 + 1))%nat with 4%nat in Hc, Hs.
  rewrite cos_approx_3_poly, cos_approx_4_poly in Hc.
  rewrite sin_approx_3_poly, sin_approx_4_poly in Hs.
  split; assumption.
Qed.

Lemma cos_sin_double_bounds : forall x cl ch sl sh,
  0 <= cl -> cl <= cos x <= ch -> 0 <= sl -> sl <= sin x <= sh ->
  2 * cl * cl - 1 <= cos (2 * x) <= 2 * ch * ch - 1 /\
  2 * sl * cl <= sin (2 * x) <= 2 * sh * ch.
Proof.
  intros x cl ch sl sh H0 [H1 H2] H3 [H4 H5].
  rewrite cos_2a_cos, sin_2a. split; split; nra.
Qed.

Lemma geos_N_mono : forall a b c s,
  0 <= a -> a <= c -> 0 <= b -> b <= s ->
  (2 * a + b * (1 / 2)) * (2 * a + b * (1 / 2)) + b * b
    <= (2 * c + s * (1 / 2)) * (2 * c + s * (1 / 2)) + s * s.
Proof.
  intros a b c s Ha Hac Hb Hbs.
  assert (H1 : 0 <= 2 * a + b * (1 / 2)) by lra.
  assert (H2 : 2 * a + b * (1 / 2) <= 2 * c + s * (1 / 2)) by lra.
  apply Rplus_le_compat; apply Rmult_le_compat; lra.
Qed.

Lemma geos_N_bounds_pos : forall c s cl ch sl sh,
  0 <= cl -> cl <= c <= ch -> 0 <= sl -> sl <= s <= sh ->
  (2 * cl + sl * (1 / 2)) * (2 * cl + sl * (1 / 2)) + sl * sl
    <= (2 * c + s * (1 / 2)) * (2 * c + s * (1 / 2)) + s * s <=
  (2 * ch + sh * (1 / 2)) * (2 * ch + sh * (1 / 2)) + sh * sh.
Proof.
  intros c s cl ch sl sh H0 [H1 H2] H3 [H4 H5].
  split; apply geos_N_mono; lra.
Qed.

Lemma geos_N_bounds_neg : forall c s cl ch sl sh,
  cl <= c <= ch -> 0 <= sl -> sl <= s <= sh -> 2 * ch + sh * (1 / 2) <= 0 ->
  (2 * ch + sh * (1 / 2)) * (2 * ch + sh * (1 / 2)) + sl * sl
    <= (2 * c + s * (1 / 2)) * (2 * c + s * (1 / 2)) + s * s <=
  (2 * cl + sl * (1 / 2)) * (2 * cl + sl * (1 / 2)) + sh * sh.
Proof.
  intros c s cl ch sl sh [H1 H2] H3 [H4 H5] H6.
  split; nra.
Qed.

Lemma curv_enclosure_of_bounds : forall k N Nlo Nhi rl rh klo khi,
  0 < rl -> 0 < rh -> rl * rl <= Nlo -> Nlo <= N -> N <= Nhi -> Nhi <= rh * rh ->
  0 <= klo -> k < khi * (Nlo * rl) -> klo * (Nhi * rh) < k ->
  klo < k / (sqrt N * sqrt N * sqrt N) < khi.
Proof.
  intros k N Nlo Nhi rl rh klo khi Hrl0 Hrh0 G1 HNlo HNhi G2 Hklo G3 G4.
  assert (HN0 : 0 <= N) by nra.
  set (r := sqrt N).
  assert (Hrl : rl <= r).
  { unfold r. rewrite <- (sqrt_square rl) by lra.
    apply sqrt_le_1; nra. }
  assert (Hrh : r <= rh).
  { unfold r. rewrite <- (sqrt_square rh) by lra.
    apply sqrt_le_1; nra. }
  assert (Er : r * r = N) by (apply sqrt_sqrt; exact HN0).
  assert (EX : r * r * r = N * r) by (rewrite Er; reflexivity).
  assert (HX1 : Nlo * rl <= r * r * r).
  { rewrite EX. apply Rmult_le_compat; nra. }
  assert (HX2 : r * r * r <= Nhi * rh).
  { rewrite EX. apply Rmult_le_compat; nra. }
  assert (Hr : 0 < r) by lra.
  assert (HXp : 0 < r * r * r)
    by (apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat|]; lra).
  assert (HNl : 0 < Nlo * rl)
    by (apply Rmult_lt_0_compat; [|lra];
        apply Rlt_le_trans with (rl * rl); [apply Rmult_lt_0_compat|]; lra).
  assert (HNh : 0 <= Nhi * rh) by (apply Rmult_le_pos; lra).
  assert (Hk : 0 <= k).
  { apply Rle_trans with (klo * (Nhi * rh)); [apply Rmult_le_pos|]; lra. }
  assert (EXX : k / (r * r * r) * (r * r * r) = k) by (field; lra).
  split.
  - apply (Rmult_lt_reg_r (r * r * r)); [exact HXp|]. rewrite EXX.
    apply Rle_lt_trans with (klo * (Nhi * rh)); [|exact G4].
    apply Rmult_le_compat_l; [lra | exact HX2].
  - apply (Rmult_lt_reg_r (r * r * r)); [exact HXp|]. rewrite EXX.
    assert (Hkhi : 0 < khi).
    { destruct (Rle_dec khi 0) as [Hn|Hn]; [|lra].
      assert (0 <= (- khi) * (Nlo * rl)) by (apply Rmult_le_pos; lra). lra. }
    apply Rlt_le_trans with (khi * (Nlo * rl)); [exact G3|].
    apply Rmult_le_compat_l; [lra | exact HX1].
Qed.

(* Start (s = 0, station 1, heading 1/50). GEOS oracle 0.009855916895262518. *)
Theorem geos_shear_curvature_enclosure :
  let V := lin_ap geos_shear (cloth_arc_v geos_shear_egg 0) in
  let Acc := lin_ap geos_shear (cloth_arc_a geos_shear_egg 0) in
  geos_shear_placed_derivs_at 0 V Acc /\
  (12319896119 / 1250000000000) < signed_curv V Acc < (98559168953 / 10000000000000).
Proof.
  intros V Acc. split; [apply geos_shear_placed_derivs|].
  unfold V, Acc. rewrite geos_shear_placed_curv.
  replace ((1 + 0) * (1 + 0) / 50) with ((1 / 50)) by field.
  replace (2 * ((1 + 0) / 25)) with (2 / 25) by field.
  destruct (cos_sin_taylor9 (1 / 50)) as [[T1 T2] [T3 T4]]; [lra|].
  assert (B0 : (999800006666577 / 1000000000000000) <= cos (1 / 50) <= (499900003333289 / 500000000000000) /\ (19998666693333 / 1000000000000000) <= sin (1 / 50) <= (9999333346667 / 500000000000000)) by (cbn [pow] in *; lra).
  destruct B0 as [[C1 C2] [S1 S2]].
  destruct (geos_N_bounds_pos (cos (1 / 50)) (sin (1 / 50)) (999800006666577 / 1000000000000000) (499900003333289 / 500000000000000) (19998666693333 / 1000000000000000) (9999333346667 / 500000000000000)) as [N1 N2]; try lra.
  unfold geos_shear_N. apply (curv_enclosure_of_bounds _ _ (126215296276421 / 31250000000000) (4038889480845483 / 1000000000000000) (1004849426636333 / 500000000000000) (200969885327267 / 100000000000000)); lra.
Qed.

(* End (s = 11, station 12, heading 72/25 = 4 * 18/25). GEOS oracle 0.15895182898207377; the 6eb13d1 curvatureOf gave 12/25 = 0.48. *)
Theorem geos_shear_end_curvature_enclosure :
  let V := lin_ap geos_shear (cloth_arc_v geos_shear_egg 11) in
  let Acc := lin_ap geos_shear (cloth_arc_a geos_shear_egg 11) in
  geos_shear_placed_derivs_at 11 V Acc /\
  (39737 / 250000) < signed_curv V Acc < (158953 / 1000000).
Proof.
  intros V Acc. split; [apply geos_shear_placed_derivs|].
  unfold V, Acc. rewrite geos_shear_placed_curv.
  replace ((1 + 11) * (1 + 11) / 50) with (2 * (2 * ((18 / 25)))) by field.
  replace (2 * ((1 + 11) / 25)) with (24 / 25) by field.
  destruct (cos_sin_taylor9 (18 / 25)) as [[T1 T2] [T3 T4]]; [lra|].
  assert (B0 : (917729429 / 1220703125) <= cos (18 / 25) <= (375902869708847 / 500000000000000) /\ (65938452935007 / 100000000000000) <= sin (18 / 25) <= (659384672644543 / 1000000000000000)) by (cbn [pow] in *; lra).
  destruct (cos_sin_double_bounds (18 / 25) (917729429 / 1220703125) (375902869708847 / 500000000000000) (65938452935007 / 100000000000000) (659384672644543 / 1000000000000000)) as [D1 D2]; [lra|lra|lra|lra|].
  assert (B1 : (65209176584441 / 500000000000000) <= cos (2 * (18 / 25)) <= (32605934910693 / 250000000000000) /\ (991455785143293 / 1000000000000000) <= sin (2 * (18 / 25)) <= (19829167255129 / 20000000000000)) by lra.
  clear D1 D2.
  destruct (cos_sin_double_bounds (2 * (18 / 25)) (65209176584441 / 500000000000000) (32605934910693 / 250000000000000) (991455785143293 / 1000000000000000) (19829167255129 / 20000000000000)) as [D1 D2]; [lra|lra|lra|lra|].
  assert (B2 : (- (482991053156717 / 500000000000000)) <= cos (2 * (2 * (18 / 25))) <= (- (241494824068797 / 250000000000000)) /\ (129304030738149 / 500000000000000) <= sin (2 * (2 * (18 / 25))) <= (258619414741593 / 1000000000000000)) by lra.
  clear D1 D2.
  destruct B2 as [[C1 C2] [S1 S2]].
  destruct (geos_N_bounds_neg (cos (2 * (2 * (18 / 25)))) (sin (2 * (2 * (18 / 25)))) (- (482991053156717 / 500000000000000)) (- (241494824068797 / 250000000000000)) (129304030738149 / 500000000000000) (258619414741593 / 1000000000000000)) as [N1 N2]; try lra.
  unfold geos_shear_N. apply (curv_enclosure_of_bounds _ _ (3316421132699709 / 1000000000000000) (1658233866524177 / 500000000000000) (227638046465069 / 125000000000000) (1821117166205501 / 1000000000000000)); lra.
Qed.

(* Interior (s = 9, station 10, heading 2 = 4 * 1/2). *)
Theorem geos_shear_mid_curvature_enclosure :
  let V := lin_ap geos_shear (cloth_arc_v geos_shear_egg 9) in
  let Acc := lin_ap geos_shear (cloth_arc_a geos_shear_egg 9) in
  geos_shear_placed_derivs_at 9 V Acc /\
  (419 / 500) < signed_curv V Acc < (8383 / 10000).
Proof.
  intros V Acc. split; [apply geos_shear_placed_derivs|].
  unfold V, Acc. rewrite geos_shear_placed_curv.
  replace ((1 + 9) * (1 + 9) / 50) with (2 * (2 * ((1 / 2)))) by field.
  replace (2 * ((1 + 9) / 25)) with (4 / 5) by field.
  destruct (cos_sin_taylor9 (1 / 2)) as [[T1 T2] [T3 T4]]; [lra|].
  assert (B0 : (877582465277777 / 1000000000000000) <= cos (1 / 2) <= (877582562158979 / 1000000000000000) /\ (239712766617063 / 500000000000000) <= sin (1 / 2) <= (14982048081763 / 31250000000000)) by (cbn [pow] in *; lra).
  destruct (cos_sin_double_bounds (1 / 2) (877582465277777 / 1000000000000000) (877582562158979 / 1000000000000000) (239712766617063 / 500000000000000) (14982048081763 / 31250000000000)) as [D1 D2]; [lra|lra|lra|lra|].
  assert (B1 : (540301966726041 / 1000000000000000) <= cos (2 * (1 / 2)) <= (540302306811037 / 1000000000000000) /\ (420735441372717 / 500000000000000) <= sin (2 * (1 / 2)) <= (420735492543443 / 500000000000000)) by lra.
  clear D1 D2.
  destruct (cos_sin_double_bounds (2 * (1 / 2)) (540301966726041 / 1000000000000000) (540302306811037 / 1000000000000000) (420735441372717 / 500000000000000) (420735492543443 / 500000000000000)) as [D1 D2]; [lra|lra|lra|lra|].
  assert (B2 : (- (83229513900789 / 200000000000000)) <= cos (2 * (2 * (1 / 2))) <= (- (13004588578417 / 31250000000000)) /\ (909296745780111 / 1000000000000000) <= sin (2 * (2 * (1 / 2))) <= (909297428714001 / 1000000000000000)) by lra.
  clear D1 D2.
  destruct B2 as [[C1 C2] [S1 S2]].
  destruct (geos_N_bounds_neg (cos (2 * (2 * (1 / 2)))) (sin (2 * (2 * (1 / 2)))) (- (83229513900789 / 200000000000000)) (- (13004588578417 / 31250000000000)) (909296745780111 / 1000000000000000) (909297428714001 / 1000000000000000)) as [N1 N2]; try lra.
  unfold geos_shear_N. apply (curv_enclosure_of_bounds _ _ (969436283667727 / 1000000000000000) (969438893825153 / 1000000000000000) (984599554980463 / 1000000000000000) (19692017609429 / 20000000000000)); lra.
Qed.

Theorem geos_shear_curvature_ne_naive :
  signed_curv (lin_ap geos_shear (cloth_arc_v geos_shear_egg 0))
              (lin_ap geos_shear (cloth_arc_a geos_shear_egg 0))
    <> cloth_tk0 geos_shear_egg.
Proof.
  rewrite geos_shear_naive_value.
  destruct geos_shear_curvature_enclosure as [_ H]. lra.
Qed.

Theorem geos_shear_end_curvature_ne_naive :
  signed_curv (lin_ap geos_shear (cloth_arc_v geos_shear_egg 11))
              (lin_ap geos_shear (cloth_arc_a geos_shear_egg 11))
    <> cloth_tk1 geos_shear_egg.
Proof.
  rewrite geos_shear_end_naive_value.
  destruct geos_shear_end_curvature_enclosure as [_ H]. lra.
Qed.

(* The sheared curvature is not monotone along the window (start < end
   < interior s = 9), so it is not affine in arc length s, nor in the
   placed arc length (an increasing reparametrization). *)
Theorem geos_shear_curvature_not_affine :
  let k := fun s => signed_curv (lin_ap geos_shear (cloth_arc_v geos_shear_egg s))
                                (lin_ap geos_shear (cloth_arc_a geos_shear_egg s)) in
  k 0 < k 11 < k 9 /\
  ~ (exists a b, forall s, 0 <= s <= 11 -> k s = a + b * s).
Proof.
  intro k.
  destruct geos_shear_curvature_enclosure as [_ H0].
  destruct geos_shear_end_curvature_enclosure as [_ H11].
  destruct geos_shear_mid_curvature_enclosure as [_ H9].
  assert (Ord : k 0 < k 11 < k 9) by (unfold k; lra).
  split; [exact Ord|].
  intros (a & b & Hab).
  rewrite (Hab 0), (Hab 11), (Hab 9) in Ord by lra.
  destruct (Rle_dec 0 b); lra.
Qed.

(* Reversed sheared clothoid: start -k(end), end -k(start)
   (cloth_placed_rev_law; GEOS reversed start -0.15895182898207377). *)
Theorem geos_shear_rev_curvature_ends :
  let kr := fun s =>
    signed_curv (lin_ap geos_shear (cloth_arc_v (cloth_rev geos_shear_egg) s))
                (lin_ap geos_shear (cloth_arc_a (cloth_rev geos_shear_egg) s)) in
  - (158953 / 1000000) < kr 0 < - (158948 / 1000000) /\
  - (98559168953 / 10000000000000) < kr 11 < - (98559168952 / 10000000000000).
Proof.
  intro kr. destruct geos_shear_nondeg as (_ & _ & Hd).
  unfold kr. rewrite !cloth_placed_rev_law by exact Hd.
  rewrite geos_shear_tlen.
  replace (11 - 0) with 11 by ring. replace (11 - 11) with 0 by ring.
  destruct geos_shear_curvature_enclosure as [_ H0].
  destruct geos_shear_end_curvature_enclosure as [_ H11].
  lra.
Qed.

(* The host AffPlace reads only the direction of ref1 and the sign of
   cross(ref1, ref2). GEOS's frame u = (2, 0), v = (1/2, 1) given to the
   host directly is the east unit frame: the host curvature is the naive
   1/25, not the placed 0.009855.... A sheared placement exists only as
   the external placed o M. *)
Definition geos_frame_egg : ClothoidEgg :=
  mk_cloth (mkAffPlace (mkPoint 3 4) (mkPoint 2 0) (mkPoint (1 / 2) 1)) 5 1 12 None None.

Theorem host_affplace_curvature_ignores_shear :
  cloth_cos0 geos_frame_egg = 1 /\ cloth_sin0 geos_frame_egg = 0 /\
  cloth_sigma geos_frame_egg = 1 /\
  signed_curv (cloth_arc_v geos_frame_egg 0) (cloth_arc_a geos_frame_egg 0) = 1 / 25 /\
  signed_curv (cloth_arc_v geos_frame_egg 0) (cloth_arc_a geos_frame_egg 0)
    <> signed_curv (lin_ap geos_shear (cloth_arc_v geos_shear_egg 0))
                   (lin_ap geos_shear (cloth_arc_a geos_shear_egg 0)).
Proof.
  assert (Hh2 : cloth_h2 geos_frame_egg = 4)
    by (unfold cloth_h2, aff_h2, geos_frame_egg, mk_cloth; cbn; ring).
  assert (Hy : cloth_hypot geos_frame_egg = 2).
  { unfold cloth_hypot. rewrite Hh2. replace 4 with (2 * 2) by ring.
    apply sqrt_square. lra. }
  assert (Hs : cloth_sigma geos_frame_egg = 1).
  { unfold cloth_sigma, cloth_cross, aff_cross, geos_frame_egg, mk_cloth. cbn.
    destruct (Rle_dec 0 (2 * 1 - 0 * (1 / 2))); [reflexivity | lra]. }
  assert (HA : cloth_A geos_frame_egg <> 0)
    by (unfold geos_frame_egg, mk_cloth; cbn; lra).
  assert (Hh : cloth_h2 geos_frame_egg <> 0) by (rewrite Hh2; lra).
  assert (Hd : cloth_d geos_frame_egg <> 0)
    by (unfold cloth_d, geos_frame_egg, mk_cloth; cbn; lra).
  assert (Hdir : cloth_dir geos_frame_egg = 1).
  { unfold cloth_dir, cloth_d, geos_frame_egg, mk_cloth. cbn.
    destruct (Rle_dec 0 (12 - 1)); [reflexivity | lra]. }
  assert (K0 : cloth_tk0 geos_frame_egg = 1 / 25).
  { unfold cloth_tk0, cloth_kappa. rewrite Hdir, Hs.
    unfold geos_frame_egg, mk_cloth. cbn [cloth_sd cloth_A]. field. }
  destruct (cloth_arc_unit_speed_linear_curvature geos_frame_egg 0 HA Hh Hd)
    as (_ & _ & _ & _ & _ & K).
  assert (Hk : signed_curv (cloth_arc_v geos_frame_egg 0)
                           (cloth_arc_a geos_frame_egg 0) = 1 / 25).
  { rewrite K, K0. unfold Rdiv. ring. }
  split; [unfold cloth_cos0; rewrite Hy; unfold geos_frame_egg, mk_cloth; cbn; field|].
  split; [unfold cloth_sin0; rewrite Hy; unfold geos_frame_egg, mk_cloth; cbn; field|].
  split; [exact Hs|]. split; [exact Hk|].
  rewrite Hk. destruct geos_shear_curvature_enclosure as [_ H]. lra.
Qed.

(* Q twin of the start enclosure: the same Taylor polynomials at 1/50,
   the same rounded bounds and the same comparisons, recomputed in Q by
   vm_compute. A cross-check only: the R proof above discharges every
   comparison with lra and does not use it. *)
Definition q_z : Q := 1 # 50.
Definition q_cos_lo (x : Q) : Q := 1 - x*x/2 + x*x*x*x/24 - x*x*x*x*x*x/720.
Definition q_cos_hi (x : Q) : Q := q_cos_lo x + x*x*x*x*x*x*x*x/40320.
Definition q_sin_lo (x : Q) : Q := x - x*x*x/6 + x*x*x*x*x/120 - x*x*x*x*x*x*x/5040.
Definition q_sin_hi (x : Q) : Q := q_sin_lo x + x*x*x*x*x*x*x*x*x/362880.
Definition q_N (a b : Q) : Q := (2 * a + b * (1 # 2)) * (2 * a + b * (1 # 2)) + b * b.
Definition q_cl : Q := (999800006666577 # 1000000000000000).
Definition q_ch : Q := (499900003333289 # 500000000000000).
Definition q_sl : Q := (19998666693333 # 1000000000000000).
Definition q_sh : Q := (9999333346667 # 500000000000000).
Definition q_Nlo : Q := (126215296276421 # 31250000000000).
Definition q_Nhi : Q := (4038889480845483 # 1000000000000000).
Definition q_rl : Q := (1004849426636333 # 500000000000000).
Definition q_rh : Q := (200969885327267 # 100000000000000).
Definition q_kl : Q := (12319896119 # 1250000000000).
Definition q_kh : Q := (98559168953 # 10000000000000).
Definition q_cr : Q := (2 # 25).

Definition geos_shear_q_check : bool :=
  Qle_bool q_cl (q_cos_lo q_z) && Qle_bool (q_cos_hi q_z) q_ch &&
  Qle_bool q_sl (q_sin_lo q_z) && Qle_bool (q_sin_hi q_z) q_sh &&
  Qle_bool q_Nlo (q_N q_cl q_sl) && Qle_bool (q_N q_ch q_sh) q_Nhi &&
  Qle_bool (q_rl * q_rl) q_Nlo && Qle_bool q_Nhi (q_rh * q_rh) &&
  negb (Qle_bool (q_kh * (q_Nlo * q_rl)) q_cr) &&
  negb (Qle_bool q_cr (q_kl * (q_Nhi * q_rh))).

Lemma geos_shear_q_check_true : geos_shear_q_check = true.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions curv_cross_lin.
Print Assumptions signed_curv_lin.
Print Assumptions curv_speed2_nonneg.
Print Assumptions lin_sim_speed2.
Print Assumptions lin_refl_speed2.
Print Assumptions lin_sim_det.
Print Assumptions lin_refl_det.
Print Assumptions sqrt_scale_sq.
Print Assumptions signed_curv_similarity.
Print Assumptions signed_curv_reflection.
Print Assumptions placed_deriv.
Print Assumptions cloth_arc_cross.
Print Assumptions cloth_placed_curvature.
Print Assumptions cloth_similarity_curvature.
Print Assumptions cloth_similarity_scaled_law.
Print Assumptions cloth_rev_station.
Print Assumptions cloth_rev_vx.
Print Assumptions cloth_rev_vy.
Print Assumptions signed_curv_neg_tangent.
Print Assumptions cloth_placed_rev_law.
Print Assumptions geos_shear_columns.
Print Assumptions geos_shear_det.
Print Assumptions geos_shear_sigma.
Print Assumptions geos_shear_frame.
Print Assumptions geos_shear_d.
Print Assumptions geos_shear_dir.
Print Assumptions geos_shear_tlen.
Print Assumptions geos_shear_naive_value.
Print Assumptions geos_shear_end_naive_value.
Print Assumptions geos_shear_nondeg.
Print Assumptions geos_shear_station.
Print Assumptions geos_shear_arc_v.
Print Assumptions geos_shear_placed_derivs.
Print Assumptions geos_shear_placed_curv.
Print Assumptions cos_approx_3_poly.
Print Assumptions cos_approx_4_poly.
Print Assumptions sin_approx_3_poly.
Print Assumptions sin_approx_4_poly.
Print Assumptions cos_sin_taylor9.
Print Assumptions cos_sin_double_bounds.
Print Assumptions geos_N_mono.
Print Assumptions geos_N_bounds_pos.
Print Assumptions geos_N_bounds_neg.
Print Assumptions curv_enclosure_of_bounds.
Print Assumptions geos_shear_curvature_enclosure.
Print Assumptions geos_shear_end_curvature_enclosure.
Print Assumptions geos_shear_mid_curvature_enclosure.
Print Assumptions geos_shear_curvature_ne_naive.
Print Assumptions geos_shear_end_curvature_ne_naive.
Print Assumptions geos_shear_curvature_not_affine.
Print Assumptions geos_shear_rev_curvature_ends.
Print Assumptions host_affplace_curvature_ignores_shear.
Print Assumptions geos_shear_q_check_true.
