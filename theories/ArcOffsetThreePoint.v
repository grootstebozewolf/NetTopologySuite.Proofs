(* ============================================================================
   NetTopologySuite.Proofs.ArcOffsetThreePoint
   ----------------------------------------------------------------------------
   Buffer/noder pipeline, Stage 2a-CURVE seam, rung 2: the SQL/MM
   THREE-POINT BRIDGE for arc offsets (issue #65 BUF-*; follows
   `ArcOffset.v`, which proved the offset soundness facts in
   center/radius/angle form).

   SQL/MM Spatial represents an arc by three control points
   (`CurveGeometry.CircularArc`: start / mid / end), with `arc_center` /
   `arc_radius` the derived circumcircle.  A curve-aware buffer that
   "preserves arcs" must therefore emit its offset arcs in the SAME
   three-point form.  This file proves that the radial offset does
   exactly that:

     1. RADIAL OFFSET AS PURE ALGEBRA.  `radial_offset C r d P
        := C + ((r+d)/r)·(P − C)` -- a homothety about the center, no
        trigonometry.  For a point P on the circle (`dist C P = r`,
        `0 < r`):
        - `radial_offset_center_dist`: the offset point is on the
          concentric circle of radius `|r+d|`;
        - `radial_offset_dist`: it is at distance `|d|` from its source;
        - `radial_offset_dist_exact` (headline): for `-r <= d` it is at
          distance exactly `|d|` from the ENTIRE source circle (lower
          bound by the reverse triangle inequality through the center,
          attained at the source point) -- the same defining
          parallel-curve property as `ArcOffset.arc_offset_dist_exact`,
          now in coordinate form.

     2. CIRCUMCENTER UNIQUENESS (`equidistant_point_is_arc_center`).
        The lemma `CurveGeometry.v`'s §2 comment promised: for a valid
        arc, ANY point equidistant from the three control points IS
        `arc_center`.  (`ArcChordApprox.arc_center_equidistant` is the
        existence half; this is the uniqueness half.  Proof: the two
        equidistance equations are linear in the candidate's
        coordinates -- the perpendicular-bisector system -- and
        `valid_arc` makes its determinant the non-zero circumcenter
        divisor, so Cramer pins the candidate to the explicit formula.)

     3. SQL/MM CLOSURE (`arc_offset_preserves_arc`, headline).  For a
        valid arc and `-r < d`, offsetting the three control points
        radially yields a triple that
        - is again a VALID three-point arc (non-collinear: the
          homothety scales the cross product by `((r+d)/r)^2 <> 0`),
        - has the SAME `arc_center` (by uniqueness: the old center is
          equidistant from the new control points),
        - has `arc_radius = r + d`.
        This is "buffer/offset preserving arcs" (issue #65 BUF-*/OFF,
        issue #64 ask) at the representation level: the offset of an
        SQL/MM arc is an SQL/MM arc with the same center and radius
        `r + d`, constructed by pure rational arithmetic on the control
        points (extractable; no transcendental functions).

   The singularity boundary `d = -r` is excluded by `-r < d` in the
   closure theorem (the offset triple collapses to the center and is no
   arc); the distance facts in §1 hold up to and including it, and the
   FAILURE of the parallel-curve property past it is
   `ArcOffset.inner_offset_past_center_not_at_distance`.

   Pure-R; THREE-AXIOM THROUGHOUT (classical-reals trio).  No
   `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance Linearise CurveGeometry ArcChordApprox.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Homothety about a center, and the radial offset.                       *)
(* -------------------------------------------------------------------------- *)

Definition homothety (C : Point) (k : R) (P : Point) : Point :=
  mkPoint (px C + k * (px P - px C)) (py C + k * (py P - py C)).

Lemma dist_sq_homothety_center : forall C k P,
  dist_sq C (homothety C k P) = k * k * dist_sq C P.
Proof.
  intros C k P. unfold dist_sq, homothety. simpl. ring.
Qed.

Lemma dist_sq_homothety_from : forall C k P,
  dist_sq P (homothety C k P) = (k - 1) * (k - 1) * dist_sq C P.
Proof.
  intros C k P. unfold dist_sq, homothety. simpl. ring.
Qed.

(* On-circle points have dist_sq = r^2 (sqrt-to-square bridge). *)
Lemma dist_sq_of_dist : forall P Q r,
  dist P Q = r -> dist_sq P Q = r * r.
Proof.
  intros P Q r H. rewrite <- H. unfold dist.
  symmetry. apply sqrt_sqrt. apply dist_sq_nonneg.
Qed.

(* The radial offset: P pushed away from (d > 0) or toward (d < 0) the       *)
(* center C along its own radius, scaling factor (r+d)/r.                    *)
Definition radial_offset (C : Point) (r d : R) (P : Point) : Point :=
  homothety C ((r + d) / r) P.

(* The offset point lies on the concentric circle of radius |r+d|.           *)
Lemma radial_offset_center_dist : forall C r d P,
  0 < r -> dist C P = r ->
  dist C (radial_offset C r d P) = Rabs (r + d).
Proof.
  intros C r d P Hr HP.
  unfold radial_offset, dist.
  rewrite dist_sq_homothety_center.
  rewrite (dist_sq_of_dist _ _ _ HP).
  replace ((r + d) / r * ((r + d) / r) * (r * r)) with (Rsqr (r + d))
    by (unfold Rsqr; field; lra).
  apply sqrt_Rsqr_abs.
Qed.

(* The offset point is at distance |d| from its source point.                *)
Lemma radial_offset_dist : forall C r d P,
  0 < r -> dist C P = r ->
  dist P (radial_offset C r d P) = Rabs d.
Proof.
  intros C r d P Hr HP.
  unfold radial_offset, dist.
  rewrite dist_sq_homothety_from.
  rewrite (dist_sq_of_dist _ _ _ HP).
  replace (((r + d) / r - 1) * ((r + d) / r - 1) * (r * r)) with (Rsqr d)
    by (unfold Rsqr; field; lra).
  apply sqrt_Rsqr_abs.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  AT DISTANCE d from the whole circle (coordinate form).                 *)
(*                                                                            *)
(* The reverse-triangle lower bound, for ANY point Q on the concentric       *)
(* radius-(r+d) circle (generalising ArcOffset.arc_offset_dist_lower beyond  *)
(* the parametric witness).                                                   *)
(* -------------------------------------------------------------------------- *)

Lemma circle_offset_dist_lower_any : forall C Q X r d,
  0 <= r -> - r <= d ->
  dist C Q = r + d -> dist C X = r ->
  Rabs d <= dist Q X.
Proof.
  intros C Q X r d Hr Hd HQ HX.
  pose proof (dist_triangle C X Q) as T1.   (* dist C Q <= dist C X + dist X Q *)
  pose proof (dist_triangle C Q X) as T2.   (* dist C X <= dist C Q + dist Q X *)
  rewrite (dist_sym X Q) in T1.
  rewrite HQ, HX in T1, T2.
  apply Rabs_le. lra.
Qed.

(* Headline (§1+§2): the radial offset is at distance EXACTLY |d| from the   *)
(* entire source circle -- the defining parallel-curve property, now as pure  *)
(* coordinate algebra on the offset point.                                    *)
Theorem radial_offset_dist_exact : forall C r d P,
  0 < r -> - r <= d -> dist C P = r ->
  (forall X, dist C X = r -> Rabs d <= dist (radial_offset C r d P) X) /\
  dist P (radial_offset C r d P) = Rabs d.
Proof.
  intros C r d P Hr Hd HP.
  split.
  - intros X HX.
    apply (circle_offset_dist_lower_any C (radial_offset C r d P) X r d).
    + lra.
    + lra.
    + rewrite (radial_offset_center_dist C r d P Hr HP).
      apply Rabs_right. lra.
    + exact HX.
  - apply radial_offset_dist; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The three-point bridge: arc_radius is positive for a valid arc.       *)
(* -------------------------------------------------------------------------- *)

Lemma arc_radius_sq_pos : forall a,
  valid_arc a -> 0 < arc_radius_sq a.
Proof.
  intros a Hva.
  destruct (Rle_lt_or_eq_dec 0 (arc_radius_sq a) (arc_radius_sq_nonneg a))
    as [Hlt | Heq]; [ exact Hlt | exfalso ].
  (* radius 0 forces center = start and center = mid (componentwise), hence  *)
  (* start = mid, killing the non-collinearity cross product. *)
  assert (Hs0 : dist_sq (arc_center a) (arc_start a) = 0)
    by (unfold arc_radius_sq in Heq; lra).
  destruct (proj1 (dist_sq_zero_iff_eq _ _) Hs0) as [Hsx Hsy].
  assert (Hm0 : dist_sq (arc_center a) (arc_mid a) = 0)
    by (rewrite <- (arc_radius_sq_eq_mid a Hva); lra).
  destruct (proj1 (dist_sq_zero_iff_eq _ _) Hm0) as [Hmx Hmy].
  unfold valid_arc in Hva. apply Hva. nra.
Qed.

Lemma arc_radius_pos : forall a,
  valid_arc a -> 0 < arc_radius a.
Proof.
  intros a Hva.
  rewrite (arc_radius_eq_sqrt a).
  apply sqrt_lt_R0. apply arc_radius_sq_pos. exact Hva.
Qed.

(* dist (not just dist_sq) from the center to each control point = radius.   *)
Lemma arc_center_dist_start : forall a,
  dist (arc_center a) (arc_start a) = arc_radius a.
Proof. reflexivity. Qed.

Lemma arc_center_dist_mid : forall a,
  valid_arc a -> dist (arc_center a) (arc_mid a) = arc_radius a.
Proof.
  intros a Hva. unfold arc_radius, dist.
  f_equal. symmetry.
  exact (proj1 (arc_center_equidistant a Hva)).
Qed.

Lemma arc_center_dist_end : forall a,
  valid_arc a -> dist (arc_center a) (arc_end a) = arc_radius a.
Proof.
  intros a Hva. unfold arc_radius, dist.
  f_equal. symmetry.
  exact (proj2 (arc_center_equidistant a Hva)).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Circumcenter uniqueness.                                               *)
(*                                                                            *)
(* The promised converse of ArcChordApprox.arc_center_equidistant: any point  *)
(* equidistant (in dist_sq) from the three control points of a valid arc IS  *)
(* the arc_center.  The two equidistance equations are linear in (ux, uy)    *)
(* (perpendicular bisectors); valid_arc makes the system's determinant the   *)
(* non-zero circumcenter divisor, and Cramer's solution is exactly the       *)
(* arc_center formula.                                                        *)
(* -------------------------------------------------------------------------- *)

Lemma point_eq : forall P Q : Point, px P = px Q -> py P = py Q -> P = Q.
Proof.
  intros [x1 y1] [x2 y2] Hx Hy. simpl in Hx, Hy. subst. reflexivity.
Qed.

Theorem equidistant_point_is_arc_center : forall a U,
  valid_arc a ->
  dist_sq U (arc_start a) = dist_sq U (arc_mid a) ->
  dist_sq U (arc_start a) = dist_sq U (arc_end a) ->
  U = arc_center a.
Proof.
  intros a U Hva H1 H2.
  unfold valid_arc in Hva.
  unfold dist_sq in H1, H2.
  unfold arc_center.
  set (ax := px (arc_start a)) in *.
  set (ay := py (arc_start a)) in *.
  set (bx := px (arc_mid a)) in *.
  set (by_ := py (arc_mid a)) in *.
  set (cx := px (arc_end a)) in *.
  set (cy := py (arc_end a)) in *.
  set (ux := px U) in *.
  set (uy := py U) in *.
  set (na := ax * ax + ay * ay).
  set (nb := bx * bx + by_ * by_).
  set (nc := cx * cx + cy * cy).
  set (dd := 2 * (ax * (by_ - cy) + bx * (cy - ay) + cx * (ay - by_))) in *.
  assert (Hdd : dd <> 0) by (unfold dd; intros Heq; apply Hva; nra).
  (* The perpendicular-bisector system (linear in ux, uy). *)
  assert (L1 : 2 * (bx - ax) * ux + 2 * (by_ - ay) * uy = nb - na)
    by (unfold na, nb; nra).
  assert (L2 : 2 * (cx - ax) * ux + 2 * (cy - ay) * uy = nc - na)
    by (unfold na, nc; nra).
  (* Cramer eliminations: multiply L1, L2 by the cross coefficients. *)
  assert (K1x : (2 * (bx - ax) * ux + 2 * (by_ - ay) * uy) * (cy - ay)
                = (nb - na) * (cy - ay)) by (rewrite L1; reflexivity).
  assert (K2x : (2 * (cx - ax) * ux + 2 * (cy - ay) * uy) * (by_ - ay)
                = (nc - na) * (by_ - ay)) by (rewrite L2; reflexivity).
  assert (K1y : (2 * (bx - ax) * ux + 2 * (by_ - ay) * uy) * (cx - ax)
                = (nb - na) * (cx - ax)) by (rewrite L1; reflexivity).
  assert (K2y : (2 * (cx - ax) * ux + 2 * (cy - ay) * uy) * (bx - ax)
                = (nc - na) * (bx - ax)) by (rewrite L2; reflexivity).
  apply point_eq; simpl.
  - (* ux = Cramer x-solution = arc_center's ux formula *)
    fold ux. field_simplify_eq; [ | exact Hdd ].
    unfold dd, na, nb, nc in *. nra.
  - (* uy likewise *)
    fold uy. field_simplify_eq; [ | exact Hdd ].
    unfold dd, na, nb, nc in *. nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  The offset arc in SQL/MM three-point form, and the closure headline.   *)
(* -------------------------------------------------------------------------- *)

Definition arc_offset_arc (a : CircularArc) (d : R) : CircularArc :=
  mkCircularArc
    (radial_offset (arc_center a) (arc_radius a) d (arc_start a))
    (radial_offset (arc_center a) (arc_radius a) d (arc_mid a))
    (radial_offset (arc_center a) (arc_radius a) d (arc_end a)).

(* The homothety scales the non-collinearity cross product by k^2.           *)
Lemma homothety_cross : forall C k A B D,
  (px (homothety C k B) - px (homothety C k A)) *
  (py (homothety C k D) - py (homothety C k A)) -
  (py (homothety C k B) - py (homothety C k A)) *
  (px (homothety C k D) - px (homothety C k A)) =
  k * k *
  ((px B - px A) * (py D - py A) - (py B - py A) * (px D - px A)).
Proof.
  intros C k A B D. unfold homothety. simpl. ring.
Qed.

(* Validity is preserved: the cross product scales by ((r+d)/r)^2 <> 0.      *)
Lemma arc_offset_arc_valid : forall a d,
  valid_arc a -> - arc_radius a < d ->
  valid_arc (arc_offset_arc a d).
Proof.
  intros a d Hva Hd.
  pose proof (arc_radius_pos a Hva) as Hr.
  unfold valid_arc in Hva.
  unfold valid_arc, arc_offset_arc.
  cbn [arc_start arc_mid arc_end]. cbv zeta.
  unfold radial_offset.
  set (k := (arc_radius a + d) / arc_radius a).
  assert (Hk : 0 < k) by (unfold k; apply Rdiv_lt_0_compat; lra).
  rewrite homothety_cross.
  intros Heq. apply Hva.
  destruct (Rmult_integral _ _ Heq) as [Hkk | Hc].
  - exfalso. nra.
  - exact Hc.
Qed.

(* The old center is equidistant from the three NEW control points.          *)
Lemma arc_center_equidistant_offset : forall a d,
  valid_arc a ->
  dist_sq (arc_center a) (arc_start (arc_offset_arc a d)) =
    dist_sq (arc_center a) (arc_mid (arc_offset_arc a d)) /\
  dist_sq (arc_center a) (arc_start (arc_offset_arc a d)) =
    dist_sq (arc_center a) (arc_end (arc_offset_arc a d)).
Proof.
  intros a d Hva.
  destruct (arc_center_equidistant a Hva) as [Hsm Hse].
  unfold arc_offset_arc, radial_offset. simpl.
  rewrite !dist_sq_homothety_center.
  rewrite <- Hsm, <- Hse. split; reflexivity.
Qed.

(* SQL/MM CLOSURE HEADLINE: the radial offset of a valid three-point arc is  *)
(* again a valid three-point arc, with the SAME center and radius r + d.     *)
(* "Buffer/offset preserving arcs" at the representation level.              *)
Theorem arc_offset_preserves_arc : forall a d,
  valid_arc a -> - arc_radius a < d ->
  valid_arc (arc_offset_arc a d) /\
  arc_center (arc_offset_arc a d) = arc_center a /\
  arc_radius (arc_offset_arc a d) = arc_radius a + d.
Proof.
  intros a d Hva Hd.
  pose proof (arc_radius_pos a Hva) as Hr.
  pose proof (arc_offset_arc_valid a d Hva Hd) as Hva'.
  assert (Hcenter : arc_center (arc_offset_arc a d) = arc_center a).
  { symmetry.
    destruct (arc_center_equidistant_offset a d Hva) as [Hsm Hse].
    apply (equidistant_point_is_arc_center (arc_offset_arc a d)
             (arc_center a) Hva' Hsm Hse). }
  split; [ exact Hva' | split; [ exact Hcenter | ] ].
  unfold arc_radius at 1. rewrite Hcenter.
  change (arc_start (arc_offset_arc a d))
    with (radial_offset (arc_center a) (arc_radius a) d (arc_start a)).
  rewrite (radial_offset_center_dist (arc_center a) (arc_radius a) d
             (arc_start a) Hr (arc_center_dist_start a)).
  apply Rabs_right. lra.
Qed.

(* Each offset control point is at distance |d| from its source (the         *)
(* per-point at-distance-d fact, in three-point terms).                       *)
Theorem arc_offset_arc_control_dist : forall a d,
  valid_arc a ->
  dist (arc_start a) (arc_start (arc_offset_arc a d)) = Rabs d /\
  dist (arc_mid a)   (arc_mid   (arc_offset_arc a d)) = Rabs d /\
  dist (arc_end a)   (arc_end   (arc_offset_arc a d)) = Rabs d.
Proof.
  intros a d Hva.
  pose proof (arc_radius_pos a Hva) as Hr.
  unfold arc_offset_arc. simpl.
  repeat split.
  - apply radial_offset_dist; [ exact Hr | exact (arc_center_dist_start a) ].
  - apply radial_offset_dist; [ exact Hr | exact (arc_center_dist_mid a Hva) ].
  - apply radial_offset_dist; [ exact Hr | exact (arc_center_dist_end a Hva) ].
Qed.

(* ========================================================================== *)
(* Axiom audit.  ALL headlines below are 3-axiom (classical-reals trio:      *)
(* sig_not_dec, sig_forall_dec, functional_extensionality_dep).              *)
(* ========================================================================== *)

Print Assumptions radial_offset_dist_exact.
Print Assumptions arc_radius_pos.
Print Assumptions equidistant_point_is_arc_center.
Print Assumptions arc_offset_arc_valid.
Print Assumptions arc_offset_preserves_arc.
Print Assumptions arc_offset_arc_control_dist.
