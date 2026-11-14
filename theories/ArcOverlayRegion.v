(* ============================================================================
   NetTopologySuite.Proofs.ArcOverlayRegion
   ----------------------------------------------------------------------------
   The arc-overlay guarantee restated as REGION closeness.

   `ArcOverlay.arc_overlay_correct_chord_approx` concludes that every point of
   the chord-approximated overlay is within `max_sagitta` of an arc CURVE.  That
   is false for interior points of any polygon wider than a sagitta
   (docs/h1-vacuity/ArcOverlayBridgeQEX.v : arc_overlay_conclusion_refuted), so
   its bridges can never be discharged.  The right statement compares REGIONS:
   the chord overlay and the true curved overlay differ only inside the
   sagitta band around the arcs.

   §1  Band lemma (`segment_point_near_arc`).  For a MINOR arc (central angle
       <= pi, `ArcOrient.arc_minor`), every point of its circular segment
       (`ArcControlTriangleInSegment.in_circular_segment`: on the bulge side of
       the chord, inside the circle) is within `sagitta a` of a point of the
       arc.  Witness: the radial foot.  The minor-arc premise is necessary: a
       major arc's segment contains its centre, which is a full radius from
       the arc (`segment_point_near_arc_needs_minor`, §4).
   §2  True region (`curve_region`).  The chord polygon, flipped inside each
       arc's circular segment (segment parity).  This is the standard curved
       region when the segments are pairwise disjoint and each lies wholly
       inside or wholly outside the chord polygon -- a DEFINITION, not tied
       by any theorem to the POINT_IN_CURVE_RING oracle.
   §3  Headline (`arc_overlay_region_close`).  For valid inputs whose arcs are
       all minor, at every point outside the `max_sagitta` band the chord
       overlay and the true-region overlay agree, for every op.  No bridge
       hypotheses.  Directed form: a point where they disagree is not outside
       the band (`arc_overlay_region_disagree_near_arc`).

   Pure R; three-axiom.  No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay CurveGeometry ArcOrient
  ArcIntersect ArcHotPixel ArcChordApprox ArcDistance ArcOverlay
  ArcArcCircles ArcControlTriangleInSegment.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Band lemma.                                                            *)
(* -------------------------------------------------------------------------- *)

Lemma sqrt_dist_sq : forall p q, sqrt (dist_sq p q) = dist p q.
Proof. reflexivity. Qed.

Lemma abs_coord_le_dist : forall p q,
  Rabs (px p - px q) <= dist p q /\ Rabs (py p - py q) <= dist p q.
Proof.
  intros p q. unfold dist, dist_sq.
  pose proof (Rle_0_sqr (px p - px q)) as Hx.
  pose proof (Rle_0_sqr (py p - py q)) as Hy. unfold Rsqr in Hx, Hy.
  split; rewrite <- sqrt_Rsqr_abs; apply sqrt_le_1_alt; unfold Rsqr; lra.
Qed.

(* The chord-side function is affine: along O + k (P - O) it moves by k. *)
Lemma chord_side_affine : forall a O P k,
  arc_side_chord a (mkPoint (px O + k * (px P - px O)) (py O + k * (py P - py O)))
  = arc_side_chord a O + k * (arc_side_chord a P - arc_side_chord a O).
Proof. intros. unfold arc_side_chord, cross_R_pt. cbn. ring. Qed.

(* s(X) measured from the chord midpoint (s(M) = 0). *)
Lemma side_via_mid : forall a X,
  arc_side_chord a X
  = (px (arc_end a) - px (arc_start a)) * (py X - py (chord_midpoint a))
    - (px X - px (chord_midpoint a)) * (py (arc_end a) - py (arc_start a)).
Proof.
  intros. unfold arc_side_chord, cross_R_pt, chord_midpoint. cbn. field.
Qed.

(* The centre is at least as far from any point strictly on the bulge side as
   from the chord midpoint (minor arc): the chord line separates them. *)
Lemma centre_line_le : forall a P,
  valid_arc a -> arc_minor a -> arc_interior_side a P ->
  dist_sq (arc_center a) (chord_midpoint a) <= dist_sq (arc_center a) P.
Proof.
  intros a P Hva Hmin Hside.
  unfold arc_minor, arc_interior_side in *.
  pose proof (OM_perp_chord a Hva) as Hperp. cbv zeta in Hperp.
  set (O := arc_center a) in *. set (M := chord_midpoint a) in *.
  set (S := arc_start a) in *. set (E := arc_end a) in *.
  set (m := arc_side_chord a (arc_mid a)) in *.
  set (ux := px E - px S). set (uy := py E - py S).
  set (L2 := ux * ux + uy * uy).
  (* s(X) = cross(u, X - S); s(M) = 0, so s(O) = cross(u, O - M). *)
  assert (HsO : arc_side_chord a O = ux * (py O - py M) - (px O - px M) * uy)
    by (rewrite side_via_mid; reflexivity).
  assert (HsPO : arc_side_chord a P - arc_side_chord a O
                 = ux * (py P - py O) - (px P - px O) * uy).
  { unfold arc_side_chord, cross_R_pt, ux, uy. fold S E. ring. }
  (* Lagrange, with dot(u, O - M) = 0. *)
  assert (HO2 : arc_side_chord a O * arc_side_chord a O = L2 * dist_sq O M).
  { rewrite HsO. unfold L2, dist_sq, ux, uy.
    assert (Hd : (px O - px M) * (px E - px S) + (py O - py M) * (py E - py S) = 0)
      by exact Hperp.
    nra. }
  assert (HPO2 : (arc_side_chord a P - arc_side_chord a O)
                 * (arc_side_chord a P - arc_side_chord a O) <= L2 * dist_sq O P).
  { rewrite HsPO. unfold L2, dist_sq.
    assert (Hl : (ux * (py P - py O) - (px P - px O) * uy)
                 * (ux * (py P - py O) - (px P - px O) * uy)
                 + (ux * (px P - px O) + uy * (py P - py O))
                   * (ux * (px P - px O) + uy * (py P - py O))
                 = (ux * ux + uy * uy)
                   * ((px O - px P) * (px O - px P) + (py O - py P) * (py O - py P)))
      by ring.
    pose proof (Rle_0_sqr (ux * (px P - px O) + uy * (py P - py O))) as Hdot.
    unfold Rsqr in Hdot. lra. }
  (* Opposite-or-zero signs: s(O)^2 <= (s(P) - s(O))^2. *)
  assert (Hsg : arc_side_chord a O * arc_side_chord a O
                <= (arc_side_chord a P - arc_side_chord a O)
                   * (arc_side_chord a P - arc_side_chord a O)).
  { nra. }
  (* The chord is non-degenerate. *)
  assert (HL2 : 0 < L2).
  { unfold valid_arc in Hva. cbv zeta in Hva. fold S E in Hva.
    unfold L2, ux, uy.
    destruct (Req_dec (px E - px S) 0) as [Hx | Hx];
    destruct (Req_dec (py E - py S) 0) as [Hy | Hy];
      [ exfalso; apply Hva; rewrite Hx, Hy; ring | nra | nra | nra ]. }
  nra.
Qed.

Theorem segment_point_near_arc : forall a P,
  valid_arc a -> arc_minor a -> in_circular_segment a P ->
  exists X : Point,
    inCircle_R (arc_start a) (arc_mid a) (arc_end a) X = 0 /\
    arc_span_contains a X /\
    dist P X <= sagitta a.
Proof.
  intros a P Hva Hmin [Hside Hin].
  set (O := arc_center a) in *.
  set (r := arc_radius a).
  assert (Hr : 0 <= r) by (unfold r; apply arc_radius_nonneg).
  assert (HrS : r = dist O (arc_start a)) by reflexivity.
  (* P is not the centre: they lie on different sides of the chord. *)
  assert (HdOP : 0 < dist O P).
  { unfold dist. apply sqrt_lt_R0.
    destruct (Rle_lt_or_eq_dec 0 (dist_sq O P) (dist_sq_nonneg O P)) as [H | H];
      [ exact H | exfalso ].
    unfold dist_sq in H.
    pose proof (Rle_0_sqr (px O - px P)) as Hx0.
    pose proof (Rle_0_sqr (py O - py P)) as Hy0. unfold Rsqr in Hx0, Hy0.
    assert (Hx2 : (px O - px P) * (px O - px P) = 0) by lra.
    assert (Hy2 : (py O - py P) * (py O - py P) = 0) by lra.
    assert (Hx : px O = px P)
      by (destruct (Rmult_integral _ _ Hx2); lra).
    assert (Hy : py O = py P)
      by (destruct (Rmult_integral _ _ Hy2); lra).
    unfold arc_minor, arc_interior_side in *. fold O in Hmin.
    assert (E : arc_side_chord a O = arc_side_chord a P).
    { unfold arc_side_chord, cross_R_pt. rewrite Hx, Hy. reflexivity. }
    rewrite E in Hmin. lra. }
  assert (HOP_le_r : dist O P <= r).
  { rewrite HrS. unfold dist. apply sqrt_le_1_alt. exact Hin. }
  set (F := radial_foot O P r).
  exists F. split; [| split].
  - (* on the circle *)
    apply inCircle_R_zero_of_equidistant; [exact Hva |].
    fold O. pose proof (radial_foot_on_circle O P r HdOP Hr) as Hon.
    fold F in Hon.
    rewrite <- (dist_mul_self O F), <- (dist_mul_self O (arc_start a)).
    rewrite Hon, <- HrS. reflexivity.
  - (* in the span: further out along the ray, so further onto the bulge side *)
    left. unfold arc_interior_side.
    unfold F, radial_foot. rewrite chord_side_affine.
    set (k := r / dist O P).
    assert (Hk : 1 <= k).
    { unfold k. apply (Rmult_le_reg_r (dist O P)); [exact HdOP |].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
    unfold arc_minor, arc_interior_side in *. fold O in Hmin.
    nra.
  - (* within one sagitta *)
    unfold F. rewrite radial_foot_dist by exact HdOP.
    rewrite Rabs_left1 by lra.
    assert (HOM : dist O (chord_midpoint a) <= dist O P).
    { unfold dist. apply sqrt_le_1_alt.
      apply centre_line_le; assumption. }
    unfold sagitta.
    rewrite (sagitta_sq_inner_eq_centerline_sq a Hva).
    rewrite sqrt_dist_sq. fold O.
    assert (Hrs : sqrt (arc_radius_sq a) = r).
    { unfold r. symmetry. apply arc_radius_eq_sqrt. }
    rewrite Hrs. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The true curved region: chord polygon, flipped by segment parity.      *)
(* -------------------------------------------------------------------------- *)

Inductive seg_odd (p : Point) : list CircularArc -> Prop :=
| so_in : forall a l,
    in_circular_segment a p -> seg_even p l -> seg_odd p (a :: l)
| so_out : forall a l,
    ~ in_circular_segment a p -> seg_odd p l -> seg_odd p (a :: l)
with seg_even (p : Point) : list CircularArc -> Prop :=
| se_nil : seg_even p []
| se_in : forall a l,
    in_circular_segment a p -> seg_odd p l -> seg_even p (a :: l)
| se_out : forall a l,
    ~ in_circular_segment a p -> seg_even p l -> seg_even p (a :: l).

(* p is in the curved region of A: in the chord polygon and in an even number
   of A's circular segments, or outside it and in an odd number. *)
Definition curve_region (A : CurveGeometry) (n : nat) (p : Point) : Prop :=
  (point_set (to_geometry A n) p /\ seg_even p (arcs_of A)) \/
  (~ point_set (to_geometry A n) p /\ seg_odd p (arcs_of A)).

Lemma off_segments_even : forall p l,
  (forall a, In a l -> ~ in_circular_segment a p) ->
  seg_even p l /\ ~ seg_odd p l.
Proof.
  intros p l. induction l as [| a l IH]; intros Hoff.
  - split; [ constructor | intro H; inversion H ].
  - assert (Ha : ~ in_circular_segment a p) by (apply Hoff; left; reflexivity).
    destruct IH as [He Hno]; [ intros b Hb; apply Hoff; right; exact Hb |].
    split.
    + apply se_out; assumption.
    + intro H; inversion H; subst; contradiction.
Qed.

(* Off every segment, the curved region is the chord polygon. *)
Lemma curve_region_off_segments : forall A n p,
  (forall a, In a (arcs_of A) -> ~ in_circular_segment a p) ->
  (curve_region A n p <-> point_set (to_geometry A n) p).
Proof.
  intros A n p Hoff. destruct (off_segments_even p (arcs_of A) Hoff) as [He Ho].
  unfold curve_region. split.
  - intros [[H _] | [_ H]]; [ exact H | contradiction ].
  - intro H. left. split; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The headline.                                                          *)
(* -------------------------------------------------------------------------- *)

(* boolean_op over arbitrary point predicates. *)
Definition region_op (op : BooleanOp) (RA RB : Point -> Prop) (p : Point) : Prop :=
  match op with
  | Union        => RA p \/ RB p
  | Intersection => RA p /\ RB p
  | Difference   => RA p /\ ~ RB p
  | SymDiff      => (RA p /\ ~ RB p) \/ (RB p /\ ~ RA p)
  end.

Lemma boolean_op_is_region_op : forall op G H p,
  boolean_op op G H p <-> region_op op (point_set G) (point_set H) p.
Proof. intros [] G H p; cbn; tauto. Qed.

Lemma region_op_ext : forall op (RA RA' RB RB' : Point -> Prop) p,
  (RA p <-> RA' p) -> (RB p <-> RB' p) ->
  (region_op op RA RB p <-> region_op op RA' RB' p).
Proof. intros [] RA RA' RB RB' p HA HB; cbn; tauto. Qed.

Lemma fold_sagitta_ge : forall xs acc a,
  (In a xs -> sagitta a <= fold_left (fun m b => Rmax m (sagitta b)) xs acc) /\
  acc <= fold_left (fun m b => Rmax m (sagitta b)) xs acc.
Proof.
  induction xs as [| x xs IH]; intros acc a; cbn.
  - split; [ intros [] | lra ].
  - destruct (IH (Rmax acc (sagitta x)) a) as [Hin Hacc].
    split.
    + intros [<- | H]; [| exact (Hin H)].
      eapply Rle_trans; [ apply Rmax_r | exact Hacc ].
    + eapply Rle_trans; [ apply Rmax_l | exact Hacc ].
Qed.

Lemma sagitta_le_max : forall A B a,
  In a (arcs_of A ++ arcs_of B) -> sagitta a <= max_sagitta A B.
Proof.
  intros A B a H. unfold max_sagitta. exact (proj1 (fold_sagitta_ge _ 0 a) H).
Qed.

Lemma ring_arc_valid : forall r a,
  curve_ring_arcs_valid r -> In a (arcs_of_ring r) -> valid_arc a.
Proof.
  intros r a Hv Hin. unfold arcs_of_ring in Hin.
  apply in_flat_map in Hin. destruct Hin as [s [Hs Ha]].
  unfold curve_ring_arcs_valid in Hv. rewrite Forall_forall in Hv.
  specialize (Hv s Hs).
  destruct s as [p q | b]; cbn in Ha; [ contradiction |].
  destruct Ha as [<- | []]. exact Hv.
Qed.

Lemma arcs_of_valid : forall A a,
  valid_curve_geometry A -> In a (arcs_of A) -> valid_arc a.
Proof.
  intros A a HA Hin. unfold arcs_of in Hin. apply in_flat_map in Hin.
  destruct Hin as [cp [Hcp Ha]].
  unfold valid_curve_geometry in HA. rewrite Forall_forall in HA.
  destruct (HA cp Hcp) as [[Hout _] Hholes].
  unfold arcs_of_polygon in Ha. apply in_app_or in Ha. destruct Ha as [Ha | Ha].
  - exact (ring_arc_valid _ _ Hout Ha).
  - apply in_flat_map in Ha. destruct Ha as [h [Hh Ha]].
    rewrite Forall_forall in Hholes. destruct (Hholes h Hh) as [Hv _].
    exact (ring_arc_valid _ _ Hv Ha).
Qed.

(* A point in a minor arc's segment is arc-close at max_sagitta. *)
Lemma in_segment_arc_close : forall A B a p,
  valid_curve_geometry A -> valid_curve_geometry B ->
  In a (arcs_of A ++ arcs_of B) -> arc_minor a ->
  in_circular_segment a p ->
  arc_close_to_curves p A B (max_sagitta A B).
Proof.
  intros A B a p HA HB Hin Hmin Hseg.
  assert (Hva : valid_arc a).
  { apply in_app_or in Hin.
    destruct Hin as [H | H]; [ exact (arcs_of_valid A a HA H)
                             | exact (arcs_of_valid B a HB H) ]. }
  destruct (segment_point_near_arc a p Hva Hmin Hseg) as (X & Hc & Hs & Hd).
  pose proof (sagitta_le_max A B a Hin) as Hm.
  destruct (abs_coord_le_dist p X) as [Hx Hy].
  exists a, X. repeat split; try assumption; lra.
Qed.

Theorem arc_overlay_region_close :
  forall (A B : CurveGeometry) (op : BooleanOp) (n : nat) (p : Point),
    valid_curve_geometry A -> valid_curve_geometry B ->
    (forall a, In a (arcs_of A ++ arcs_of B) -> arc_minor a) ->
    ~ arc_close_to_curves p A B (max_sagitta A B) ->
    (boolean_op op (to_geometry A n) (to_geometry B n) p <->
     region_op op (curve_region A n) (curve_region B n) p).
Proof.
  intros A B op n p HA HB Hmin Hfar.
  assert (Hoff : forall a, In a (arcs_of A ++ arcs_of B) ->
                   ~ in_circular_segment a p).
  { intros a Ha Hseg.
    exact (Hfar (in_segment_arc_close A B a p HA HB Ha (Hmin a Ha) Hseg)). }
  rewrite boolean_op_is_region_op.
  apply region_op_ext; symmetry; apply curve_region_off_segments;
    intros a Ha; apply Hoff; apply in_or_app; [ left | right ]; exact Ha.
Qed.

(* Directed form: wherever the chord overlay and the curved overlay
   disagree, the point is not outside the max_sagitta band. *)
Corollary arc_overlay_region_disagree_near_arc :
  forall (A B : CurveGeometry) (op : BooleanOp) (n : nat) (p : Point),
    valid_curve_geometry A -> valid_curve_geometry B ->
    (forall a, In a (arcs_of A ++ arcs_of B) -> arc_minor a) ->
    ~ (boolean_op op (to_geometry A n) (to_geometry B n) p <->
       region_op op (curve_region A n) (curve_region B n) p) ->
    ~ ~ arc_close_to_curves p A B (max_sagitta A B).
Proof.
  intros A B op n p HA HB Hmin Hdis Hfar.
  exact (Hdis (arc_overlay_region_close A B op n p HA HB Hmin Hfar)).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The minor-arc premise is necessary.                                    *)
(* -------------------------------------------------------------------------- *)

(* Major arc on the unit circle: chord at y = -4/5, bulge through (0,1).  Its
   sagitta (the minor-segment height) is 1/5, but the centre (0,0) is in its
   segment and a full radius from every circle point. *)
Definition major_arc : CircularArc :=
  mkCircularArc (mkPoint (-3/5) (-4/5)) (mkPoint 0 1) (mkPoint (3/5) (-4/5)).

Lemma major_arc_center : arc_center major_arc = mkPoint 0 0.
Proof.
  unfold arc_center, major_arc. cbn. f_equal; field.
Qed.

Lemma major_arc_valid : valid_arc major_arc.
Proof. unfold valid_arc, major_arc. cbn. lra. Qed.

Lemma major_arc_not_minor : ~ arc_minor major_arc.
Proof.
  unfold arc_minor. rewrite major_arc_center.
  unfold arc_side_chord, cross_R_pt, major_arc. cbn. lra.
Qed.

Lemma major_arc_centre_in_segment : in_circular_segment major_arc (mkPoint 0 0).
Proof.
  split.
  - unfold arc_interior_side, arc_side_chord, cross_R_pt, major_arc. cbn. lra.
  - rewrite major_arc_center. unfold dist_sq, major_arc. cbn. lra.
Qed.

Lemma major_arc_sagitta_lt_1 : sagitta major_arc < 1.
Proof.
  unfold sagitta.
  assert (Hr : arc_radius_sq major_arc = 1).
  { unfold arc_radius_sq. rewrite major_arc_center.
    unfold dist_sq, major_arc. cbn. field. }
  assert (Hi : sagitta_sq_inner major_arc = 16 / 25).
  { unfold sagitta_sq_inner, chord_half_length_sq. rewrite Hr.
    unfold dist_sq, major_arc. cbn.
    rewrite Rmax_right; [ field | lra ]. }
  rewrite Hr, Hi, sqrt_1.
  assert (0 < sqrt (16 / 25)) by (apply sqrt_lt_R0; lra). lra.
Qed.

Theorem segment_point_near_arc_needs_minor :
  ~ (exists X : Point,
       inCircle_R (arc_start major_arc) (arc_mid major_arc) (arc_end major_arc) X = 0 /\
       arc_span_contains major_arc X /\
       dist (mkPoint 0 0) X <= sagitta major_arc).
Proof.
  intros (X & Hc & _ & Hd).
  pose proof (inCircle_R_zero_implies_equidistant major_arc X major_arc_valid Hc)
    as Heq.
  rewrite major_arc_center in Heq.
  assert (H1 : dist_sq (mkPoint 0 0) X = 1).
  { rewrite Heq. unfold dist_sq, major_arc. cbn. field. }
  assert (Hd1 : dist (mkPoint 0 0) X = 1)
    by (unfold dist; rewrite H1; apply sqrt_1).
  pose proof major_arc_sagitta_lt_1. lra.
Qed.

Print Assumptions segment_point_near_arc.
Print Assumptions segment_point_near_arc_needs_minor.
Print Assumptions arc_overlay_region_close.
