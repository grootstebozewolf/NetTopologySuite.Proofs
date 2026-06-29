(* ============================================================================
   NetTopologySuite.Proofs.CurveRingOffsetSimple
   ----------------------------------------------------------------------------
   OFFSET-RING SIMPLICITY FROM CLEARANCE (the global, non-adjacent half).

   ClothoidBufferAssembly (PR #305) proved every ADJACENT offset join is a single
   clean contact.  CurveRingSimple.curve_ring_simple additionally demands that
   NON-adjacent segments meet NOWHERE.  Raw offset is not unconditionally simple
   (RingSimple.bowtie), so this is gated by a clearance hypothesis on the source
   ring -- the standard "clearance > offset distance" sufficient condition, proved
   by a metric TUBE argument (no Jordan/winding machinery):

     every point of an offset segment lies within |d| of the source segment
     (chords: a parallel translate; arcs: the radial correspondent), so if two
     source segments are strictly more than 2|d| apart, their offsets share no
     point (triangle inequality).

   Headline `curve_ring_simple_of_clearance`: a valid, safely-offset CurveRing
   whose non-adjacent source segments have pairwise clearance > 2|d| offsets to a
   `curve_ring_simple` ring.  Covers chords AND arcs, so clothoid osculating-arc
   rings are included; combined with clothoid_buffer_assembly_sound this gives full
   simple-closed-curve soundness for well-separated clothoid buffer rings.

   Honest scope: a SUFFICIENT condition.  NOT claimed: necessity/tightness of the
   2|d| bound, or simplicity without a clearance hypothesis (false -- bowtie).

   Pure-R; classical-reals trio only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
Import ListNotations.
From NTS.Proofs Require Import Vec Direction Distance Segment CurveGeometry ArcOrient ArcIntersect
  ArcChordApprox ArcArcCircles ArcOffsetThreePoint BufferOffset CurveRingOffset CurveRingSimple.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §0  Small metric / homothety helpers.                                      *)
(* -------------------------------------------------------------------------- *)

(* Lightweight point equality decision (classical reals), to avoid importing
   OverlayGraph just for point_eq_dec. *)
Definition pt_eq_dec (p q : Point) : {p = q} + {p <> q}.
Proof.
  destruct (Req_EM_T (px p) (px q)) as [Hx | Hx];
    destruct (Req_EM_T (py p) (py q)) as [Hy | Hy].
  - left. apply point_eq; assumption.
  - right; intro H; apply Hy; rewrite H; reflexivity.
  - right; intro H; apply Hx; rewrite H; reflexivity.
  - right; intro H; apply Hx; rewrite H; reflexivity.
Defined.

Lemma dsq_nonneg : forall p q, 0 <= dist_sq p q.
Proof.
  intros p q. unfold dist_sq.
  apply Rplus_le_le_0_compat;
    (replace ((px p - px q) * (px p - px q)) with (Rsqr (px p - px q)) by (unfold Rsqr; ring)
     || replace ((py p - py q) * (py p - py q)) with (Rsqr (py p - py q)) by (unfold Rsqr; ring));
    apply Rle_0_sqr.
Qed.

Lemma dist_sq_eq_sq : forall p q, dist_sq p q = dist p q * dist p q.
Proof.
  intros p q. unfold dist. rewrite sqrt_sqrt by apply dsq_nonneg. reflexivity.
Qed.

Lemma dist_homothety_center : forall C k P,
  dist C (homothety C k P) = Rabs k * dist C P.
Proof.
  intros C k P. unfold dist.
  rewrite <- sqrt_Rsqr_abs.
  rewrite <- sqrt_mult_alt by apply Rle_0_sqr.
  f_equal. unfold dist_sq, homothety, Rsqr. cbn [px py]. ring.
Qed.

(* radial_offset C r d (homothety C (r/(r+d)) X) = X : the radial back-projection
   is a right inverse of radial_offset. *)
Lemma radial_of_homothety_back : forall C r d X,
  r <> 0 -> r + d <> 0 ->
  radial_offset C r d (homothety C (r / (r + d)) X) = X.
Proof.
  intros C r d X Hr Hrd. unfold radial_offset, homothety.
  apply point_eq; cbn [px py]; field; split; assumption.
Qed.

(* homothety C (r/(r+d)) (radial_offset C r d P) = P : and a left inverse. *)
Lemma homothety_of_radial_back : forall C r d P,
  r <> 0 -> r + d <> 0 ->
  homothety C (r / (r + d)) (radial_offset C r d P) = P.
Proof.
  intros C r d P Hr Hrd. unfold radial_offset, homothety.
  apply point_eq; cbn [px py]; field; split; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §1  Homothety-equivariance of the chord-side signed area (the crux).       *)
(*                                                                            *)
(* cross_R_pt is orient2d on differences, so a common homothety about C scales *)
(* it by k^2.  Hence arc_side_chord of the offset arc at the radial image of P *)
(* is k^2 times arc_side_chord a P -- and k^2 > 0 preserves the interior-side  *)
(* strict sign.                                                                *)
(* -------------------------------------------------------------------------- *)
Lemma arc_side_chord_radial_offset : forall a d P,
  arc_radius a <> 0 ->
  arc_side_chord (arc_offset_arc a d)
    (radial_offset (arc_center a) (arc_radius a) d P)
  = ((arc_radius a + d) / arc_radius a) * ((arc_radius a + d) / arc_radius a)
    * arc_side_chord a P.
Proof.
  intros a d P Hr.
  unfold arc_side_chord, cross_R_pt, arc_offset_arc, radial_offset, homothety.
  cbn [arc_start arc_end px py]. field. exact Hr.
Qed.

Lemma arc_interior_side_offset_iff : forall a d Q,
  arc_radius a <> 0 -> arc_radius a + d <> 0 ->
  (arc_interior_side (arc_offset_arc a d)
     (radial_offset (arc_center a) (arc_radius a) d Q)
   <-> arc_interior_side a Q).
Proof.
  intros a d Q Hr Hrd. unfold arc_interior_side.
  change (arc_mid (arc_offset_arc a d))
    with (radial_offset (arc_center a) (arc_radius a) d (arc_mid a)).
  rewrite (arc_side_chord_radial_offset a d (arc_mid a) Hr).
  rewrite (arc_side_chord_radial_offset a d Q Hr).
  set (k := (arc_radius a + d) / arc_radius a).
  set (M := arc_side_chord a (arc_mid a)).
  set (Pp := arc_side_chord a Q).
  assert (Hk : k <> 0).
  { unfold k. intro H. apply Hrd.
    replace (arc_radius a + d)
      with ((arc_radius a + d) / arc_radius a * arc_radius a) by (field; exact Hr).
    rewrite H. ring. }
  assert (Hk2 : 0 < k * k).
  { pose proof (Rsqr_pos_lt k Hk) as Hs. unfold Rsqr in Hs. exact Hs. }
  assert (Hk4 : 0 < k * k * (k * k)) by (apply Rmult_lt_0_compat; exact Hk2).
  replace (k * k * M * (k * k * Pp)) with (k * k * (k * k) * (M * Pp)) by ring.
  split; intro H.
  - apply (Rmult_lt_reg_l (k * k * (k * k))); [ exact Hk4 | ].
    rewrite Rmult_0_r. exact H.
  - apply Rmult_lt_0_compat; [ exact Hk4 | exact H ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Per-segment tube bounds.                                               *)
(* -------------------------------------------------------------------------- *)

(* Chords: the offset chord is a parallel translate, so X = offset_point A B Q d
   for the corresponding source point Q; distance is |d| (or 0 if A=B). *)
Lemma offset_point_dist_le : forall A B P d, dist P (offset_point A B P d) <= Rabs d.
Proof.
  intros A B P d. destruct (pt_eq_dec A B) as [-> | Hne].
  - replace (offset_point B B P d) with P.
    + rewrite dist_refl. apply Rabs_pos.
    + unfold offset_point, offset_normal, unit_perp, seg_vec, vperp, vscale, pt_translate.
      apply point_eq; cbn [px py vx vy]; ring.
  - rewrite (offset_point_dist A B P d Hne). apply Rle_refl.
Qed.

Lemma chord_offset_tube : forall A B d X,
  between (offset_point A B A d) (offset_point A B B d) X ->
  exists Q, between A B Q /\ dist X Q <= Rabs d.
Proof.
  intros A B d X [t [Ht0 [Ht1 [HXx HXy]]]].
  exists (mkPoint ((1 - t) * px A + t * px B) ((1 - t) * py A + t * py B)).
  set (Q := mkPoint ((1 - t) * px A + t * px B) ((1 - t) * py A + t * py B)).
  split.
  - exists t. cbn [px py]. repeat split; try assumption; reflexivity.
  - assert (HXeq : X = offset_point A B Q d).
    { apply point_eq; cbn [px py].
      - rewrite HXx. unfold offset_point, pt_translate, Q. cbn [px py]. ring.
      - rewrite HXy. unfold offset_point, pt_translate, Q. cbn [px py]. ring. }
    rewrite HXeq, dist_sym. apply offset_point_dist_le.
Qed.

(* Arcs: X on the offset arc lies on the radius-(r+d) circle; its radial
   back-projection Q lies on the source arc and is exactly |d| away. *)
Lemma arc_offset_tube : forall a d X,
  valid_arc a -> - arc_radius a < d ->
  on_arc (arc_offset_arc a d) X ->
  exists Q, on_arc a Q /\ dist X Q <= Rabs d.
Proof.
  intros a d X Hva Hsafe [Hinc Hspan].
  pose proof (arc_radius_pos a Hva) as Hr0.
  assert (Hrd : 0 < arc_radius a + d) by lra.
  assert (Hrne : arc_radius a <> 0) by (apply Rgt_not_eq; exact Hr0).
  assert (Hrdne : arc_radius a + d <> 0) by (apply Rgt_not_eq; exact Hrd).
  pose proof (arc_offset_preserves_arc a d Hva Hsafe) as [Hva' [Hc' Hrad']].
  (* dist (arc_center a) X = arc_radius a + d *)
  assert (HdCX : dist (arc_center a) X = arc_radius a + d).
  { pose proof (inCircle_R_zero_implies_equidistant (arc_offset_arc a d) X Hva' Hinc) as Heqd.
    rewrite Hc' in Heqd.
    assert (Hstep : dist (arc_center a) X
                    = dist (arc_center a) (arc_start (arc_offset_arc a d))).
    { unfold dist. rewrite Heqd. reflexivity. }
    rewrite Hstep.
    unfold arc_offset_arc. cbn [arc_start]. unfold radial_offset.
    rewrite dist_homothety_center.
    replace (dist (arc_center a) (arc_start a)) with (arc_radius a) by reflexivity.
    rewrite Rabs_right by (apply Rle_ge, Rlt_le, Rdiv_lt_0_compat; lra).
    field; lra. }
  set (Q := homothety (arc_center a) (arc_radius a / (arc_radius a + d)) X).
  exists Q.
  (* dist (arc_center a) Q = arc_radius a *)
  assert (HdCQ : dist (arc_center a) Q = arc_radius a).
  { unfold Q. rewrite dist_homothety_center, HdCX.
    rewrite Rabs_right by (apply Rle_ge, Rlt_le, Rdiv_lt_0_compat; lra).
    field; lra. }
  (* radial_offset of Q recovers X *)
  assert (HrofQ : radial_offset (arc_center a) (arc_radius a) d Q = X)
    by (unfold Q; apply radial_of_homothety_back; assumption).
  (* dist X Q = |d| *)
  assert (HdXQ : dist X Q = Rabs d).
  { pose proof (radial_offset_dist (arc_center a) (arc_radius a) d Q Hr0 HdCQ) as Hdd.
    rewrite HrofQ in Hdd. rewrite dist_sym. exact Hdd. }
  split; [ | rewrite HdXQ; apply Rle_refl ].
  split.
  - (* inCircle_R a Q = 0 *)
    apply inCircle_R_zero_of_equidistant; [ exact Hva | ].
    rewrite (dist_sq_eq_sq (arc_center a) Q), (dist_sq_eq_sq (arc_center a) (arc_start a)).
    rewrite HdCQ. unfold arc_radius. reflexivity.
  - (* arc_span_contains a Q *)
    destruct Hspan as [Hint | [Hst | Hen]].
    + left. apply (proj1 (arc_interior_side_offset_iff a d Q Hrne Hrdne)).
      rewrite HrofQ. exact Hint.
    + right; left.
      unfold Q. rewrite Hst.
      change (arc_start (arc_offset_arc a d))
        with (radial_offset (arc_center a) (arc_radius a) d (arc_start a)).
      apply homothety_of_radial_back; assumption.
    + right; right.
      unfold Q. rewrite Hen.
      change (arc_end (arc_offset_arc a d))
        with (radial_offset (arc_center a) (arc_radius a) d (arc_end a)).
      apply homothety_of_radial_back; assumption.
Qed.

(* Generic tube bound over both segment kinds. *)
Lemma offset_within_tube : forall s d X,
  segment_arc_valid s ->
  (match s with CSArc a => - arc_radius a < d | _ => True end) ->
  on_curve_segment (curve_segment_offset s d) X ->
  exists Q, on_curve_segment s Q /\ dist X Q <= Rabs d.
Proof.
  intros [p q | a] d X Hsv Hsafe Hon; cbn [curve_segment_offset on_curve_segment] in *.
  - apply (chord_offset_tube p q d X Hon).
  - apply (arc_offset_tube a d X Hsv Hsafe Hon).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Clearance predicate and the list helper.                               *)
(* -------------------------------------------------------------------------- *)

Definition seg_clear_gt (s1 s2 : CurveSegment) (m : R) : Prop :=
  forall X Y, on_curve_segment s1 X -> on_curve_segment s2 Y -> dist X Y > m.

Lemma nth_error_map_inv : forall (A B : Type) (f : A -> B) (l : list A) (i : nat) (y : B),
  nth_error (map f l) i = Some y -> exists x, nth_error l i = Some x /\ y = f x.
Proof.
  intros A B f l. induction l as [| a l' IH]; intros [| i] y H; cbn in H.
  - discriminate.
  - discriminate.
  - injection H as <-. exists a. split; reflexivity.
  - apply IH. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Headline: clearance > 2|d| ⇒ the offset ring is simple.               *)
(* -------------------------------------------------------------------------- *)
Theorem curve_ring_simple_of_clearance : forall r d,
  (forall i j s1 s2,
     nth_error r i = Some s1 -> nth_error r j = Some s2 ->
     i <> j -> ~ ring_adjacent_positions (length r) i j ->
     seg_clear_gt s1 s2 (2 * Rabs d)) ->
  curve_ring_arcs_valid r ->
  ring_offset_safe r d ->
  curve_ring_simple (curve_ring_offset r d).
Proof.
  intros r d Hclear Hav Hsafe i j s1' s2' Hi' Hj' Hij Hnadj Hmeet.
  unfold curve_ring_offset in Hi', Hj'.
  destruct (nth_error_map_inv _ _ _ _ _ _ Hi') as [s1 [Hi Hs1]].
  destruct (nth_error_map_inv _ _ _ _ _ _ Hj') as [s2 [Hj Hs2]].
  destruct Hmeet as [X [HX1 HX2]].
  cbn in Hs1, Hs2. subst s1' s2'.
  (* per-segment validity + arc safety at i, j *)
  assert (Hsv1 : segment_arc_valid s1)
    by (exact (proj1 (Forall_forall _ _) Hav s1 (nth_error_In r i Hi))).
  assert (Hsv2 : segment_arc_valid s2)
    by (exact (proj1 (Forall_forall _ _) Hav s2 (nth_error_In r j Hj))).
  assert (Hsf1 : match s1 with CSArc a => - arc_radius a < d | _ => True end)
    by (exact (proj1 (Forall_forall _ _) Hsafe s1 (nth_error_In r i Hi))).
  assert (Hsf2 : match s2 with CSArc a => - arc_radius a < d | _ => True end)
    by (exact (proj1 (Forall_forall _ _) Hsafe s2 (nth_error_In r j Hj))).
  destruct (offset_within_tube s1 d X Hsv1 Hsf1 HX1) as [Q1 [HQ1 Hd1]].
  destruct (offset_within_tube s2 d X Hsv2 Hsf2 HX2) as [Q2 [HQ2 Hd2]].
  rewrite curve_ring_offset_length in Hnadj.
  pose proof (Hclear i j s1 s2 Hi Hj Hij Hnadj Q1 Q2 HQ1 HQ2) as Hgt.
  pose proof (dist_triangle Q1 X Q2) as Htri.
  rewrite (dist_sym Q1 X) in Htri.
  lra.
Qed.

Print Assumptions arc_side_chord_radial_offset.
Print Assumptions arc_offset_tube.
Print Assumptions chord_offset_tube.
Print Assumptions curve_ring_simple_of_clearance.
