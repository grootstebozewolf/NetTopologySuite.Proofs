(* ============================================================================
   NetTopologySuite.Proofs.CircularCookEmpty
   ----------------------------------------------------------------------------
   Core-slice rung after CircularCookHit: I.3 ∀ Empty / Decline on the
   integer seam.

   ICircGEmpty ↔ proper pair ∧ γ_full images disjoint on S (triangle
   inequality, not the I.2 discriminant Hit iff).
   ICircGDecline ↔ not a proper pair (d=0 or r≤0).
   Discriminant Empty and image-disjoint are different proofs:
   concentric unequal radii are image-disjoint and Decline.

   QED: Empty / Decline / concentric-unequal honesty fence.
   QEX: CircularArc still has no γ / (tᵢ, tⱼ) — CircGamma stays QEX;
   do not fake Discharge.  first_cook_scope stays chord–chord.
   Sidecar cook stays locked.

   Not glossary 𝓘 for CircularArc eggs.  Not a noder.  Not OverlayNGCurve
   / #857 / fully_intersected / ticket 523.  Not chord-lane constructed 𝓘.
   Not I.8–I.10 / Campaign II / H⊥ / CRV-TOUCH kiss procedure.
   Not a remint of CurveSegment / ExactIntersectionPoints / Dart /
   Hobby / leftover-width.
   ============================================================================ *)

From Stdlib Require Import ZArith Reals Lra Lia Bool.
From NTS.Proofs Require Import Distance SheetHenCook CircularCookZ
  CircularCook CircularCookHit.
Local Open Scope R_scope.

(* WITNESS: campaign=I rung=I.3 claim=0007
   file=theories/CircularCookEmpty.v
   kind=QED-empty-decline-gamma-full
   lock=sidecar-cook-stays-locked
   not=CircGamma-Discharge,CircularArc-span,first-cook-noding
   not=I.8-I.10,Campaign-II,Hperp,CRV-TOUCH-kiss *)

(* -------------------------------------------------------------------------- *)
(* I.3 ∀ Empty / Decline. Image-disjoint ≠ discriminant Empty.                *)
(* ICircGEmpty ↔ proper pair ∧ γ_full images disjoint on S.                   *)
(* ICircGDecline ↔ not a proper pair (d=0 or r≤0).                            *)
(* Sidecar cook stays locked. CircGamma stays QEX.                            *)
(* -------------------------------------------------------------------------- *)

Definition proper_circ_pair (o1x o1y r1 o2x o2y r2 : Z) : Prop :=
  (0 < r1)%Z /\ (0 < r2)%Z /\
  (circ_d2 o1x o1y o2x o2y <> 0)%Z.

Definition full_circle_image (O : Point) (r : R) (p : Point) : Prop :=
  exists t, on_full_circle O r t p.

Definition full_circle_images_disjoint
  (O1 : Point) (r1 : R) (O2 : Point) (r2 : R) : Prop :=
  forall p, ~(full_circle_image O1 r1 p /\ full_circle_image O2 r2 p).

Definition gamma_images_disjoint
  (o1x o1y r1 o2x o2y r2 : Z) : Prop :=
  full_circle_images_disjoint
    (zpt o1x o1y) (IZR r1) (zpt o2x o2y) (IZR r2).

Lemma I_circles_gamma_eq_empty :
  forall o1x o1y r1 o2x o2y r2,
    I_circles_gamma o1x o1y r1 o2x o2y r2 = ICircGEmpty
    <->
    I_circles_z o1x o1y r1 o2x o2y r2 = IZEmpty.
Proof.
  intros o1x o1y r1 o2x o2y r2.
  unfold I_circles_gamma, I_circles_on_z_sheet.
  destruct (I_circles_z o1x o1y r1 o2x o2y r2);
    split; intros H; try discriminate; reflexivity.
Qed.

Lemma I_circles_gamma_eq_decline :
  forall o1x o1y r1 o2x o2y r2,
    I_circles_gamma o1x o1y r1 o2x o2y r2 = ICircGDecline
    <->
    I_circles_z o1x o1y r1 o2x o2y r2 = IZDecline.
Proof.
  intros o1x o1y r1 o2x o2y r2.
  unfold I_circles_gamma, I_circles_on_z_sheet.
  destruct (I_circles_z o1x o1y r1 o2x o2y r2);
    split; intros H; try discriminate; reflexivity.
Qed.

Lemma I_circles_z_touch_is_plus :
  forall o1x o1y r1 o2x o2y r2 h,
    I_circles_z o1x o1y r1 o2x o2y r2 = IZTouch h ->
    h = hen_plus.
Proof.
  intros o1x o1y r1 o2x o2y r2 h Hz.
  unfold I_circles_z, mint_pair, mint_touch in Hz.
  destruct ((r1 <=? 0)%Z || (r2 <=? 0)%Z); [discriminate|].
  destruct (circ_d2 o1x o1y o2x o2y =? 0)%Z; [discriminate|].
  destruct ((circ_d2 o1x o1y o2x o2y =? (r1 + r2) * (r1 + r2))%Z
            || (circ_d2 o1x o1y o2x o2y =? (r1 - r2) * (r1 - r2))%Z);
    [|destruct (((r1 + r2) * (r1 + r2) <? circ_d2 o1x o1y o2x o2y)%Z
                || (circ_d2 o1x o1y o2x o2y <? (r1 - r2) * (r1 - r2))%Z);
      discriminate].
  inversion Hz. reflexivity.
Qed.

Lemma I_circles_z_hit_is_plus_minus :
  forall o1x o1y r1 o2x o2y r2 hp hm,
    I_circles_z o1x o1y r1 o2x o2y r2 = IZHit hp hm ->
    hp = hen_plus /\ hm = hen_minus.
Proof.
  intros o1x o1y r1 o2x o2y r2 hp hm Hz.
  unfold I_circles_z, mint_pair, mint_touch in Hz.
  destruct ((r1 <=? 0)%Z || (r2 <=? 0)%Z); [discriminate|].
  destruct (circ_d2 o1x o1y o2x o2y =? 0)%Z; [discriminate|].
  destruct ((circ_d2 o1x o1y o2x o2y =? (r1 + r2) * (r1 + r2))%Z
            || (circ_d2 o1x o1y o2x o2y =? (r1 - r2) * (r1 - r2))%Z);
    [discriminate|].
  destruct (((r1 + r2) * (r1 + r2) <? circ_d2 o1x o1y o2x o2y)%Z
            || (circ_d2 o1x o1y o2x o2y <? (r1 - r2) * (r1 - r2))%Z);
    [discriminate|].
  inversion Hz. split; reflexivity.
Qed.

Lemma proper_circ_pair_neg_iff :
  forall o1x o1y r1 o2x o2y r2,
    ~ proper_circ_pair o1x o1y r1 o2x o2y r2 <->
    (r1 <= 0 \/ r2 <= 0 \/ circ_d2 o1x o1y o2x o2y = 0)%Z.
Proof.
  intros o1x o1y r1 o2x o2y r2.
  unfold proper_circ_pair.
  split.
  - intros Hn.
    destruct (Z.le_gt_cases r1 0) as [H1|H1]; [left; exact H1|].
    destruct (Z.le_gt_cases r2 0) as [H2|H2]; [right; left; exact H2|].
    destruct (Z.eq_dec (circ_d2 o1x o1y o2x o2y) 0) as [Hd|Hd];
      [right; right; exact Hd|].
    exfalso. apply Hn. split; [lia|split; [lia|exact Hd]].
  - intros H [Hr1 [Hr2 Hd]].
    destruct H as [H|[H|H]]; lia.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"I_circles_gamma_decline_iff","title":"I.3 forall Decline: I_circles_gamma is Decline iff the pair is not proper (d=0 or r<=0)","file":"theories/CircularCookEmpty.v","witness":"0007-I.3-empty-decline","board":"ADR-0007"} *)

Theorem I_circles_gamma_decline_iff :
  forall o1x o1y r1 o2x o2y r2,
    I_circles_gamma o1x o1y r1 o2x o2y r2 = ICircGDecline
    <->
    ~ proper_circ_pair o1x o1y r1 o2x o2y r2.
Proof.
  intros o1x o1y r1 o2x o2y r2.
  rewrite I_circles_gamma_eq_decline.
  rewrite I_circles_z_decline_iff.
  symmetry. apply proper_circ_pair_neg_iff.
Qed.

Lemma on_circle_of_full_circle_image :
  forall O r p,
    full_circle_image O r p ->
    dist_sq O p = r * r.
Proof.
  intros O r p [t [Ht Heq]].
  rewrite Heq. apply circ_gamma_on_circle.
Qed.

Lemma full_circle_image_of_on_circle :
  forall O r p,
    0 < r ->
    dist_sq O p = r * r ->
    full_circle_image O r p.
Proof.
  intros O r p Hr Heq.
  exists (circ_t O p).
  apply on_full_circle_of_retract; assumption.
Qed.

Lemma dist_of_on_circle_pos :
  forall O p r,
    0 < r ->
    dist_sq O p = r * r ->
    dist O p = r.
Proof.
  intros O p r Hr Heq.
  unfold dist. rewrite Heq.
  apply sqrt_Rsqr. lra.
Qed.

(* Triangle: a common circle point forces |r1−r2| ≤ d ≤ r1+r2. *)
Lemma common_circle_point_metric :
  forall O1 O2 r1 r2 p,
    0 < r1 ->
    0 < r2 ->
    dist_sq O1 p = r1 * r1 ->
    dist_sq O2 p = r2 * r2 ->
    Rabs (r1 - r2) <= dist O1 O2 /\
    dist O1 O2 <= r1 + r2.
Proof.
  intros O1 O2 r1 r2 p Hr1 Hr2 H1 H2.
  pose proof (dist_of_on_circle_pos O1 p r1 Hr1 H1) as Hd1.
  pose proof (dist_of_on_circle_pos O2 p r2 Hr2 H2) as Hd2.
  pose proof (dist_triangle O1 p O2) as Hsum.
  rewrite Hd1, (dist_sym p O2), Hd2 in Hsum.
  pose proof (dist_triangle O1 O2 p) as Hrev1.
  rewrite Hd1, Hd2 in Hrev1.
  pose proof (dist_triangle O2 O1 p) as Hrev2.
  rewrite Hd2, (dist_sym O2 O1), Hd1 in Hrev2.
  split.
  - apply Rabs_le. lra.
  - exact Hsum.
Qed.

Lemma common_circle_point_sq :
  forall O1 O2 r1 r2 p,
    0 < r1 ->
    0 < r2 ->
    dist_sq O1 p = r1 * r1 ->
    dist_sq O2 p = r2 * r2 ->
    (r1 - r2) * (r1 - r2) <= dist_sq O1 O2 /\
    dist_sq O1 O2 <= (r1 + r2) * (r1 + r2).
Proof.
  intros O1 O2 r1 r2 p Hr1 Hr2 H1 H2.
  destruct (common_circle_point_metric O1 O2 r1 r2 p Hr1 Hr2 H1 H2)
    as [Habs Hsum].
  pose proof (dist_nonneg O1 O2) as Hdnn.
  pose proof (Rabs_pos (r1 - r2)) as Habsnn.
  assert (Hsumnn : 0 <= r1 + r2) by lra.
  pose proof (dist_mul_self O1 O2) as Hdd.
  split.
  - apply (proj1 (sq_monotone_nonneg
                    (Rabs (r1 - r2)) (dist O1 O2) Habsnn Hdnn)) in Habs.
    assert (Hrabs2 :
              Rabs (r1 - r2) * Rabs (r1 - r2) = (r1 - r2) * (r1 - r2)).
    { rewrite <- Rabs_mult. apply Rabs_right. apply Rle_ge.
      pose proof (Rle_0_sqr (r1 - r2)) as Hz.
      unfold Rsqr in Hz. exact Hz. }
    rewrite Hrabs2, Hdd in Habs.
    exact Habs.
  - apply (proj1 (sq_monotone_nonneg
                    (dist O1 O2) (r1 + r2) Hdnn Hsumnn)) in Hsum.
    rewrite Hdd in Hsum.
    exact Hsum.
Qed.

Definition line_scale (O1 O2 : Point) (s : R) : Point :=
  mkPoint (px O1 + s * (px O2 - px O1))
          (py O1 + s * (py O2 - py O1)).

Lemma line_scale_dist_sq_from_O1 :
  forall O1 O2 s,
    dist_sq O1 (line_scale O1 O2 s) = (s * s) * dist_sq O1 O2.
Proof.
  intros O1 O2 s.
  unfold line_scale, dist_sq. cbn [px py]. ring.
Qed.

Lemma line_scale_dist_sq_from_O2 :
  forall O1 O2 s,
    dist_sq O2 (line_scale O1 O2 s) = ((s - 1) * (s - 1)) * dist_sq O1 O2.
Proof.
  intros O1 O2 s.
  unfold line_scale, dist_sq. cbn [px py]. ring.
Qed.

Lemma common_point_of_kiss_radii :
  forall O1 O2 r1 r2,
    0 < r1 ->
    0 < r2 ->
    0 < dist O1 O2 ->
    (dist O1 O2 = r1 + r2 \/ dist O1 O2 = Rabs (r1 - r2)) ->
    exists p, dist_sq O1 p = r1 * r1 /\ dist_sq O2 p = r2 * r2.
Proof.
  intros O1 O2 r1 r2 Hr1 Hr2 Hdpos Hkiss.
  set (d := dist O1 O2) in *.
  assert (Hdne : d <> 0) by lra.
  assert (Hdd : d * d = dist_sq O1 O2).
  { unfold d, dist. rewrite sqrt_sqrt; [reflexivity | apply dist_sq_nonneg]. }
  destruct Hkiss as [Hext | Hint].
  - exists (line_scale O1 O2 (r1 / d)).
    rewrite line_scale_dist_sq_from_O1, line_scale_dist_sq_from_O2, <- Hdd.
    split.
    + field. exact Hdne.
    + rewrite Hext. field. rewrite <- Hext. exact Hdne.
  - destruct (Rle_dec r2 r1) as [Hle | Hgt].
    + assert (Hdabs : d = r1 - r2).
      { rewrite Hint. rewrite Rabs_right; lra. }
      exists (line_scale O1 O2 (r1 / d)).
      rewrite line_scale_dist_sq_from_O1, line_scale_dist_sq_from_O2, <- Hdd.
      split.
      * field. exact Hdne.
      * rewrite Hdabs. field. rewrite <- Hdabs. exact Hdne.
    + assert (Hdabs : d = r2 - r1).
      { rewrite Hint. rewrite Rabs_left; lra. }
      exists (line_scale O1 O2 (- r1 / d)).
      rewrite line_scale_dist_sq_from_O1, line_scale_dist_sq_from_O2, <- Hdd.
      split.
      * field. exact Hdne.
      * rewrite Hdabs. field. rewrite <- Hdabs. exact Hdne.
Qed.

Lemma touch_lifts_kiss_radii :
  forall o1x o1y r1 o2x o2y r2,
    I_circles_z o1x o1y r1 o2x o2y r2 = IZTouch hen_plus ->
    0 < IZR r1 /\
    0 < IZR r2 /\
    0 < dist (zpt o1x o1y) (zpt o2x o2y) /\
    (dist (zpt o1x o1y) (zpt o2x o2y) = IZR r1 + IZR r2 \/
     dist (zpt o1x o1y) (zpt o2x o2y) = Rabs (IZR r1 - IZR r2)).
Proof.
  intros o1x o1y r1 o2x o2y r2 Htouch.
  apply I_circles_z_touch_iff in Htouch.
  destruct Htouch as [Hr1 [Hr2 [Hd0 Hk]]].
  assert (Hr1R : 0 < IZR r1) by (apply IZR_lt; exact Hr1).
  assert (Hr2R : 0 < IZR r2) by (apply IZR_lt; exact Hr2).
  assert (Hdsq : dist_sq (zpt o1x o1y) (zpt o2x o2y) =
                   IZR (circ_d2 o1x o1y o2x o2y))
    by apply zpt_dist_sq.
  assert (Hd2pos : (0 < circ_d2 o1x o1y o2x o2y)%Z).
  { pose proof (Z.square_nonneg (o2x - o1x)).
    pose proof (Z.square_nonneg (o2y - o1y)).
    unfold circ_d2 in Hd0 |- *. lia. }
  assert (Hdsq_pos : 0 < dist_sq (zpt o1x o1y) (zpt o2x o2y)).
  { rewrite Hdsq. apply IZR_lt. exact Hd2pos. }
  assert (Hdpos : 0 < dist (zpt o1x o1y) (zpt o2x o2y)).
  { unfold dist. apply sqrt_lt_R0. exact Hdsq_pos. }
  split; [exact Hr1R|].
  split; [exact Hr2R|].
  split; [exact Hdpos|].
  destruct Hk as [Hs | Hd].
  - left.
    unfold dist. rewrite Hdsq, Hs, IZR_circ_sum2.
    apply sqrt_Rsqr. lra.
  - right.
    unfold dist. rewrite Hdsq, Hd, IZR_circ_diff2.
    pose proof (Rsqr_abs (IZR r1 - IZR r2)) as Habs.
    unfold Rsqr in Habs. rewrite Habs.
    apply sqrt_Rsqr. apply Rabs_pos.
Qed.

Lemma touch_images_meet :
  forall o1x o1y r1 o2x o2y r2,
    I_circles_z o1x o1y r1 o2x o2y r2 = IZTouch hen_plus ->
    ~ gamma_images_disjoint o1x o1y r1 o2x o2y r2.
Proof.
  intros o1x o1y r1 o2x o2y r2 Htouch Hdisj.
  destruct (touch_lifts_kiss_radii o1x o1y r1 o2x o2y r2 Htouch)
    as [Hr1 [Hr2 [Hdpos Hkiss]]].
  destruct (common_point_of_kiss_radii
              (zpt o1x o1y) (zpt o2x o2y) (IZR r1) (IZR r2)
              Hr1 Hr2 Hdpos Hkiss)
    as [p [Hp1 Hp2]].
  apply (Hdisj p).
  split.
  - apply full_circle_image_of_on_circle; [exact Hr1|exact Hp1].
  - apply full_circle_image_of_on_circle; [exact Hr2|exact Hp2].
Qed.

Lemma hit_images_meet :
  forall o1x o1y r1 o2x o2y r2,
    I_circles_gamma o1x o1y r1 o2x o2y r2 =
      I_circles_gamma_hit_val o1x o1y r1 o2x o2y r2 ->
    ~ gamma_images_disjoint o1x o1y r1 o2x o2y r2.
Proof.
  intros o1x o1y r1 o2x o2y r2 Hhit Hdisj.
  apply I_circles_gamma_hit_iff in Hhit.
  destruct Hhit as [_ Hon].
  destruct Hon as [Hp1 [Hp2 _]].
  apply (Hdisj (gamma_p_plus o1x o1y r1 o2x o2y r2)).
  split.
  - exists (circ_t (zpt o1x o1y) (gamma_p_plus o1x o1y r1 o2x o2y r2)).
    exact Hp1.
  - exists (circ_t (zpt o2x o2y) (gamma_p_plus o1x o1y r1 o2x o2y r2)).
    exact Hp2.
Qed.

Lemma empty_disc_images_disjoint :
  forall o1x o1y r1 o2x o2y r2,
    I_circles_z o1x o1y r1 o2x o2y r2 = IZEmpty ->
    proper_circ_pair o1x o1y r1 o2x o2y r2 /\
    gamma_images_disjoint o1x o1y r1 o2x o2y r2.
Proof.
  intros o1x o1y r1 o2x o2y r2 Hempty.
  apply I_circles_z_empty_iff in Hempty.
  destruct Hempty as [Hr1 [Hr2 [Hd0 [Hs [Hd He]]]]].
  split.
  - split; [exact Hr1|split; [exact Hr2|exact Hd0]].
  - intros p [Him1 Him2].
    pose proof (on_circle_of_full_circle_image
                  (zpt o1x o1y) (IZR r1) p Him1) as Hp1.
    pose proof (on_circle_of_full_circle_image
                  (zpt o2x o2y) (IZR r2) p Him2) as Hp2.
    assert (Hr1R : 0 < IZR r1) by (apply IZR_lt; exact Hr1).
    assert (Hr2R : 0 < IZR r2) by (apply IZR_lt; exact Hr2).
    destruct (common_circle_point_sq
                (zpt o1x o1y) (zpt o2x o2y) (IZR r1) (IZR r2) p
                Hr1R Hr2R Hp1 Hp2)
      as [Hlo Hhi].
    rewrite zpt_dist_sq, <- IZR_circ_diff2 in Hlo.
    rewrite zpt_dist_sq, <- IZR_circ_sum2 in Hhi.
    destruct He as [Hgt | Hlt].
    + apply le_IZR in Hhi. lia.
    + apply le_IZR in Hlo. lia.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"I_circles_gamma_empty_iff","title":"I.3 forall Empty: I_circles_gamma is Empty iff proper pair and full-circle images disjoint on S","file":"theories/CircularCookEmpty.v","witness":"0007-I.3-empty-decline","board":"ADR-0007"} *)

Theorem I_circles_gamma_empty_iff :
  forall o1x o1y r1 o2x o2y r2,
    I_circles_gamma o1x o1y r1 o2x o2y r2 = ICircGEmpty
    <->
    proper_circ_pair o1x o1y r1 o2x o2y r2 /\
    gamma_images_disjoint o1x o1y r1 o2x o2y r2.
Proof.
  intros o1x o1y r1 o2x o2y r2.
  split.
  - intros Hempty.
    apply I_circles_gamma_eq_empty in Hempty.
    apply empty_disc_images_disjoint. exact Hempty.
  - intros [Hproper Hdisj].
    unfold I_circles_gamma, I_circles_on_z_sheet.
    destruct (I_circles_z o1x o1y r1 o2x o2y r2) as [hp hm | | h | ] eqn:Hz.
    + exfalso.
      destruct (I_circles_z_hit_is_plus_minus
                  o1x o1y r1 o2x o2y r2 hp hm Hz) as [-> ->].
      apply (hit_images_meet o1x o1y r1 o2x o2y r2); [|exact Hdisj].
      apply I_circles_gamma_eq_hit_val. exact Hz.
    + reflexivity.
    + exfalso.
      pose proof (I_circles_z_touch_is_plus o1x o1y r1 o2x o2y r2 h Hz) as Hh.
      subst h.
      apply (touch_images_meet o1x o1y r1 o2x o2y r2 Hz Hdisj).
    + exfalso.
      apply I_circles_z_decline_iff in Hz.
      apply proper_circ_pair_neg_iff in Hz.
      exact (Hz Hproper).
Qed.

(* Locked Empty (0,0)/(20,0) r=5 inhabits the forall. *)
Lemma i3_recovers_locked_empty :
  I_circles_gamma 0 0 5 20 0 5 = ICircGEmpty
  <->
  proper_circ_pair 0 0 5 20 0 5 /\
  gamma_images_disjoint 0 0 5 20 0 5.
Proof.
  apply I_circles_gamma_empty_iff.
Qed.

(* Discriminant Empty ≠ image-disjoint: concentric unequal radii. *)
Lemma concentric_unequal_images_disjoint :
  gamma_images_disjoint 0 0 5 0 0 3.
Proof.
  intros p [Him1 Him2].
  pose proof (on_circle_of_full_circle_image (zpt 0 0) (IZR 5) p Him1) as H5.
  pose proof (on_circle_of_full_circle_image (zpt 0 0) (IZR 3) p Him2) as H3.
  rewrite H5 in H3.
  lra.
Qed.

Lemma concentric_unequal_is_decline :
  I_circles_gamma 0 0 5 0 0 3 = ICircGDecline.
Proof.
  apply I_circles_gamma_decline_iff.
  intros [Hr1 [Hr2 Hd]].
  unfold circ_d2 in Hd. lia.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_i3_empty_qed_or_qex","title":"I.3 forall Empty is image-disjoint on a proper pair (QED) or the locked Empty witness declines (QEX); discharged QED; not the I.2 discriminant Hit iff","file":"theories/CircularCookEmpty.v","witness":"0007-I.3-empty-decline","board":"ADR-0007"} *)

Theorem ticket_0007_i3_empty_qed_or_qex :
  (forall o1x o1y r1 o2x o2y r2,
     I_circles_gamma o1x o1y r1 o2x o2y r2 = ICircGEmpty
     <->
     proper_circ_pair o1x o1y r1 o2x o2y r2 /\
     gamma_images_disjoint o1x o1y r1 o2x o2y r2)
  \/
  I_circles_gamma 0 0 5 20 0 5 = ICircGDecline.
Proof.
  left.
  exact I_circles_gamma_empty_iff.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_i3_decline_qed_or_qex","title":"I.3 forall Decline is not a proper pair (QED) or coincident centres are Empty (QEX); discharged QED; d=0 or r<=0","file":"theories/CircularCookEmpty.v","witness":"0007-I.3-empty-decline","board":"ADR-0007"} *)

Theorem ticket_0007_i3_decline_qed_or_qex :
  (forall o1x o1y r1 o2x o2y r2,
     I_circles_gamma o1x o1y r1 o2x o2y r2 = ICircGDecline
     <->
     ~ proper_circ_pair o1x o1y r1 o2x o2y r2)
  \/
  I_circles_gamma 0 0 5 0 0 5 = ICircGEmpty.
Proof.
  left.
  exact I_circles_gamma_decline_iff.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_i3_disc_neq_image_qed_or_qex","title":"I.3 discriminant Empty and image-disjoint differ (QED) or concentric unequal radii are Empty (QEX); discharged QED on Decline + disjoint images","file":"theories/CircularCookEmpty.v","witness":"0007-I.3-empty-decline","board":"ADR-0007"} *)

Theorem ticket_0007_i3_disc_neq_image_qed_or_qex :
  (gamma_images_disjoint 0 0 5 0 0 3 /\
   I_circles_gamma 0 0 5 0 0 3 = ICircGDecline /\
   I_circles_gamma 0 0 5 0 0 3 <> ICircGEmpty)
  \/
  I_circles_gamma 0 0 5 0 0 3 = ICircGEmpty.
Proof.
  left.
  split; [exact concentric_unequal_images_disjoint|].
  split; [exact concentric_unequal_is_decline|].
  rewrite concentric_unequal_is_decline.
  intros H. apply ICircGEmpty_neq_ICircGDecline. symmetry. exact H.
Qed.

(* I.3 is γ_full image-disjoint, not CircularArc span. Cook stays locked. *)
(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_i3_scope_qed_or_qex","title":"I.3 is arc-span Empty (QED) or gamma_full image-disjoint while CircGamma stays QEX (QEX); discharged QEX; sidecar cook stays locked","file":"theories/CircularCookEmpty.v","witness":"0007-I.3-empty-decline","board":"ADR-0007"} *)

Theorem ticket_0007_i3_scope_qed_or_qex :
  (circular_gamma_status = CircGammaDischarged
   /\ first_cook_scope EggCircularArc EggCircularArc)
  \/
  (circular_gamma_status = CircGammaQEX
   /\ ~ first_cook_scope EggCircularArc EggCircularArc).
Proof.
  right.
  split; [exact circular_gamma_is_qex|exact circular_not_first_cook_scope].
Qed.

Print Assumptions circ_gamma_on_circle.
Print Assumptions I_circles_gamma_empty_iff.
Print Assumptions I_circles_gamma_decline_iff.
Print Assumptions common_circle_point_metric.
Print Assumptions common_point_of_kiss_radii.
Print Assumptions concentric_unequal_images_disjoint.
Print Assumptions i3_recovers_locked_empty.
Print Assumptions ticket_0007_i3_empty_qed_or_qex.
Print Assumptions ticket_0007_i3_decline_qed_or_qex.
Print Assumptions ticket_0007_i3_disc_neq_image_qed_or_qex.
Print Assumptions ticket_0007_i3_scope_qed_or_qex.
