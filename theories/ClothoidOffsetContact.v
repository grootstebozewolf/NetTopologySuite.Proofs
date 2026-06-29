(* ============================================================================
   NetTopologySuite.Proofs.ClothoidOffsetContact
   ----------------------------------------------------------------------------
   CLOTHOID-CLOTHOID OFFSET CONTACT SOUNDNESS (buffer assembly, adjacent pair).

   Two consecutive clothoid osculating arcs that are G1-joined (shared endpoint
   + consistent outward normals) offset to arcs whose only contact is the shared
   join -- a single clean contact, no spurious second crossing.

   Geometry: arc_offset_arc is a homothety about the arc CENTRE (so the offset
   arc keeps the centre, radius r+d -- arc_offset_preserves_arc).  With consistent
   normals the two offset circles have centre distance |r1-r2| = |rho1-rho2|, i.e.
   they are INTERNALLY TANGENT, hence meet at exactly one point -- the offset join.

   This file lands four load-bearing facts:
     §1  internally_tangent_circles_unique -- the reusable engine: two circles at
         centre distance |r1-r2| with r1 <> r2 meet at EXACTLY ONE point (radical-
         axis elimination; the corpus had no such lemma).  Distinct radii is the
         generic clothoid case (curvature strictly varies along the spiral).
     §2  two_offset_arcs_join_contact -- the intended G1 join contact SURVIVES the
         offset (the offset arcs still meet, via arc_join_offset_continuous +
         arc_arc_intersects_shared_vertex).
     §3  join_normals_center_dist -- derives the internal-tangency relation
         dist(C1,C2) = |arc_radius a1 - arc_radius a2| from join_normals_consistent
         (a division-heavy `field` derivation, no nra).
     §4  two_clothoid_offset_arcs_meet_only_at_join -- the HEADLINE: every common
         point of the two offset circles equals the offset join.  Glues §3 (the
         centre distance equals |rho1-rho2|, so the offset circles are internally
         tangent) into §1 (internal tangency forces a unique meeting point), with
         the join itself a witness via §2.

   Scope (honest): adjacent-pair contact soundness.  NON-adjacent ring simplicity
   is the noder's job (raw offset is not simple -- RingSimple.bowtie), not claimed.

   Pure-R; classical-reals trio only.  (nra is unreliable in this build, so the
   algebra is done with ring identities + lra + sqr_eq_zero.)

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance ArcOffsetThreePoint CurveGeometry ArcChordApprox
  ArcOrient ArcArcCircles ArcIntersect ArcArcSound CurveRingOffset.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Internally-tangent circles meet at exactly one point (reusable).       *)
(* -------------------------------------------------------------------------- *)

(* Radical-axis elimination over raw reals: a common point's offset from C1
   (zx,zy) is pinned by the tangency.  d = C2 - C1, r1 <> r2. *)
Lemma tangent_coord_pin : forall dx dy zx zy r1 r2 : R,
  r1 - r2 <> 0 ->
  zx * zx + zy * zy = r1 * r1 ->
  dx * dx + dy * dy = (r1 - r2) * (r1 - r2) ->
  (dx - zx) * (dx - zx) + (dy - zy) * (dy - zy) = r2 * r2 ->
  zx * (r1 - r2) = dx * r1 /\ zy * (r1 - r2) = dy * r1.
Proof.
  intros dx dy zx zy r1 r2 Hne E1 ED E2.
  assert (Hexp : (dx - zx) * (dx - zx) + (dy - zy) * (dy - zy)
                 = (dx * dx + dy * dy) + (zx * zx + zy * zy)
                   - 2 * (dx * zx + dy * zy)) by ring.
  assert (Hdot : dx * zx + dy * zy = r1 * (r1 - r2)).
  { rewrite Hexp in E2. rewrite ED, E1 in E2.
    assert (Hrel : (r1 - r2) * (r1 - r2) + r1 * r1 - r2 * r2
                   = 2 * (r1 * (r1 - r2))) by ring.
    lra. }
  assert (Hcross : zx * dy - zy * dx = 0).
  { apply sqr_eq_zero.
    assert (Hlag : (zx * dy - zy * dx) * (zx * dy - zy * dx)
                 = (zx * zx + zy * zy) * (dx * dx + dy * dy)
                   - (dx * zx + dy * zy) * (dx * zx + dy * zy)) by ring.
    rewrite Hlag, E1, ED, Hdot. ring. }
  split.
  - assert (Hidx : zx * (dx * dx + dy * dy)
                 = dx * (dx * zx + dy * zy) + dy * (zx * dy - zy * dx)) by ring.
    rewrite ED, Hdot, Hcross in Hidx.
    rewrite Rmult_0_r, Rplus_0_r in Hidx.
    apply (Rmult_eq_reg_r (r1 - r2)); [ | exact Hne ].
    transitivity (zx * ((r1 - r2) * (r1 - r2))); [ ring | ].
    rewrite Hidx. ring.
  - assert (Hidy : zy * (dx * dx + dy * dy)
                 = dy * (dx * zx + dy * zy) - dx * (zx * dy - zy * dx)) by ring.
    rewrite ED, Hdot, Hcross in Hidy.
    rewrite Rmult_0_r, Rminus_0_r in Hidy.
    apply (Rmult_eq_reg_r (r1 - r2)); [ | exact Hne ].
    transitivity (zy * ((r1 - r2) * (r1 - r2))); [ ring | ].
    rewrite Hidy. ring.
Qed.

(* dist C1 C2 = |r1 - r2| with r1 <> r2: the two circles meet at one point. *)
Lemma internally_tangent_circles_unique : forall (C1 C2 X Y : Point) (r1 r2 : R),
  r1 <> r2 ->
  dist C1 C2 = Rabs (r1 - r2) ->
  dist_sq C1 X = r1 * r1 -> dist_sq C2 X = r2 * r2 ->
  dist_sq C1 Y = r1 * r1 -> dist_sq C2 Y = r2 * r2 ->
  X = Y.
Proof.
  intros C1 C2 X Y r1 r2 Hne Hd HX1 HX2 HY1 HY2.
  assert (Hd12 : r1 - r2 <> 0) by (intro Hc; apply Hne; lra).
  assert (HD : dist_sq C1 C2 = (r1 - r2) * (r1 - r2)).
  { pose proof (dist_mul_self C1 C2) as Hm. rewrite Hd in Hm.
    rewrite <- Hm, <- Rabs_mult. apply Rabs_right. apply Rle_ge, sqr_nonneg. }
  unfold dist_sq in HX1, HX2, HY1, HY2, HD.
  (* centre-offset facts in (dx,dy,zx,zy) coordinates, via ring, for X and Y *)
  assert (EDc : (px C2 - px C1) * (px C2 - px C1) + (py C2 - py C1) * (py C2 - py C1)
                = (r1 - r2) * (r1 - r2)) by (rewrite <- HD; ring).
  assert (E1X : (px X - px C1) * (px X - px C1) + (py X - py C1) * (py X - py C1)
                = r1 * r1) by (rewrite <- HX1; ring).
  assert (E2X : ((px C2 - px C1) - (px X - px C1)) * ((px C2 - px C1) - (px X - px C1))
              + ((py C2 - py C1) - (py X - py C1)) * ((py C2 - py C1) - (py X - py C1))
                = r2 * r2) by (rewrite <- HX2; ring).
  assert (E1Y : (px Y - px C1) * (px Y - px C1) + (py Y - py C1) * (py Y - py C1)
                = r1 * r1) by (rewrite <- HY1; ring).
  assert (E2Y : ((px C2 - px C1) - (px Y - px C1)) * ((px C2 - px C1) - (px Y - px C1))
              + ((py C2 - py C1) - (py Y - py C1)) * ((py C2 - py C1) - (py Y - py C1))
                = r2 * r2) by (rewrite <- HY2; ring).
  destruct (tangent_coord_pin (px C2 - px C1) (py C2 - py C1)
              (px X - px C1) (py X - py C1) r1 r2 Hd12 E1X EDc E2X) as [HXx HXy].
  destruct (tangent_coord_pin (px C2 - px C1) (py C2 - py C1)
              (px Y - px C1) (py Y - py C1) r1 r2 Hd12 E1Y EDc E2Y) as [HYx HYy].
  apply point_eq.
  - assert (Hsub : px X - px C1 = px Y - px C1)
      by (apply (Rmult_eq_reg_r (r1 - r2)); [ rewrite HXx, HYx; reflexivity | exact Hd12 ]).
    lra.
  - assert (Hsub : py X - py C1 = py Y - py C1)
      by (apply (Rmult_eq_reg_r (r1 - r2)); [ rewrite HXy, HYy; reflexivity | exact Hd12 ]).
    lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Positive contact: the intended G1 join survives the offset.            *)
(* -------------------------------------------------------------------------- *)

(* Two consecutive G1-joined arcs offset to arcs that still meet at the join. *)
Theorem two_offset_arcs_join_contact : forall a1 a2 d,
  valid_arc a1 -> valid_arc a2 ->
  arc_end a1 = arc_start a2 ->
  join_normals_consistent a1 a2 ->
  arc_arc_intersects (arc_offset_arc a1 d) (arc_offset_arc a2 d).
Proof.
  intros a1 a2 d Hv1 Hv2 Hjoin Hn.
  apply arc_arc_intersects_shared_vertex.
  apply arc_join_offset_continuous; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The internal-tangency relation from G1-consistent normals.             *)
(* -------------------------------------------------------------------------- *)

(* Consistent normals at the shared join force the two circumcentres to be at
   distance |r1 - r2|: the join P satisfies P-C1 = r1*n, P-C2 = r2*n (common unit
   normal n), so C1-C2 = (r2-r1)*n and |C1-C2| = |r1-r2|*|n| = |r1-r2|. *)
Lemma join_normals_center_dist : forall a1 a2,
  valid_arc a1 -> valid_arc a2 ->
  arc_end a1 = arc_start a2 ->
  join_normals_consistent a1 a2 ->
  dist (arc_center a1) (arc_center a2) = Rabs (arc_radius a1 - arc_radius a2).
Proof.
  intros a1 a2 Hv1 Hv2 Hjoin Hn.
  pose proof (arc_radius_pos a1 Hv1) as Hr1.
  pose proof (arc_radius_pos a2 Hv2) as Hr2.
  unfold join_normals_consistent in Hn. destruct Hn as [Hnx Hny].
  assert (HC1x : px (arc_end a1) - px (arc_center a1)
               = arc_radius a1 * ((px (arc_end a1) - px (arc_center a2)) / arc_radius a2)).
  { rewrite <- Hnx. field. lra. }
  assert (HC1y : py (arc_end a1) - py (arc_center a1)
               = arc_radius a1 * ((py (arc_end a1) - py (arc_center a2)) / arc_radius a2)).
  { rewrite <- Hny. field. lra. }
  assert (Huv : (px (arc_end a1) - px (arc_center a2)) * (px (arc_end a1) - px (arc_center a2))
              + (py (arc_end a1) - py (arc_center a2)) * (py (arc_end a1) - py (arc_center a2))
              = arc_radius a2 * arc_radius a2).
  { rewrite Hjoin. unfold arc_radius. rewrite dist_mul_self. unfold dist_sq. ring. }
  assert (HxC' : (px (arc_center a1) - px (arc_center a2)) * arc_radius a2
               = (px (arc_end a1) - px (arc_center a2)) * (arc_radius a2 - arc_radius a1)).
  { transitivity (((px (arc_end a1) - px (arc_center a2))
                   - (px (arc_end a1) - px (arc_center a1))) * arc_radius a2);
      [ ring | ]. rewrite HC1x. field. lra. }
  assert (HyC' : (py (arc_center a1) - py (arc_center a2)) * arc_radius a2
               = (py (arc_end a1) - py (arc_center a2)) * (arc_radius a2 - arc_radius a1)).
  { transitivity (((py (arc_end a1) - py (arc_center a2))
                   - (py (arc_end a1) - py (arc_center a1))) * arc_radius a2);
      [ ring | ]. rewrite HC1y. field. lra. }
  assert (HD : dist_sq (arc_center a1) (arc_center a2)
             = (arc_radius a1 - arc_radius a2) * (arc_radius a1 - arc_radius a2)).
  { apply (Rmult_eq_reg_r (arc_radius a2 * arc_radius a2)).
    - unfold dist_sq.
      transitivity (((px (arc_center a1) - px (arc_center a2)) * arc_radius a2)
                      * ((px (arc_center a1) - px (arc_center a2)) * arc_radius a2)
                  + ((py (arc_center a1) - py (arc_center a2)) * arc_radius a2)
                      * ((py (arc_center a1) - py (arc_center a2)) * arc_radius a2));
        [ ring | ].
      rewrite HxC', HyC'.
      transitivity (((px (arc_end a1) - px (arc_center a2)) * (px (arc_end a1) - px (arc_center a2))
                   + (py (arc_end a1) - py (arc_center a2)) * (py (arc_end a1) - py (arc_center a2)))
                    * ((arc_radius a2 - arc_radius a1) * (arc_radius a2 - arc_radius a1)));
        [ ring | ].
      rewrite Huv. ring.
    - apply Rmult_integral_contrapositive_currified; intro Hc; lra. }
  unfold dist. rewrite HD.
  replace ((arc_radius a1 - arc_radius a2) * (arc_radius a1 - arc_radius a2))
    with (Rsqr (arc_radius a1 - arc_radius a2)) by (unfold Rsqr; ring).
  apply sqrt_Rsqr_abs.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Headline: two consecutive offset arcs meet ONLY at the shared join.    *)
(*                                                                            *)
(* For two valid, G1-joined arcs of DISTINCT radii (the generic clothoid case)*)
(* offset by a per-arc-safe distance, any point on BOTH offset circumcircles  *)
(* equals the offset join -- no spurious second crossing.  arcs are subsets of *)
(* their circumcircles, so they too meet only at the join.                    *)
(* -------------------------------------------------------------------------- *)
Theorem two_clothoid_offset_arcs_meet_only_at_join : forall a1 a2 d,
  valid_arc a1 -> valid_arc a2 ->
  arc_end a1 = arc_start a2 ->
  join_normals_consistent a1 a2 ->
  arc_radius a1 <> arc_radius a2 ->
  - arc_radius a1 < d -> - arc_radius a2 < d ->
  forall X,
    inCircle_R (arc_start (arc_offset_arc a1 d)) (arc_mid (arc_offset_arc a1 d))
               (arc_end (arc_offset_arc a1 d)) X = 0 ->
    inCircle_R (arc_start (arc_offset_arc a2 d)) (arc_mid (arc_offset_arc a2 d))
               (arc_end (arc_offset_arc a2 d)) X = 0 ->
    X = arc_end (arc_offset_arc a1 d).
Proof.
  intros a1 a2 d Hv1 Hv2 Hjoin Hn Hne Hd1 Hd2 X HX1 HX2.
  destruct (arc_offset_preserves_arc a1 d Hv1 Hd1) as [Hv1' [Hc1 Hrad1]].
  destruct (arc_offset_preserves_arc a2 d Hv2 Hd2) as [Hv2' [Hc2 Hrad2]].
  set (b1 := arc_offset_arc a1 d) in *. set (b2 := arc_offset_arc a2 d) in *.
  pose proof (inCircle_R_zero_implies_equidistant b1 X Hv1' HX1) as HXc1.
  pose proof (inCircle_R_zero_implies_equidistant b2 X Hv2' HX2) as HXc2.
  assert (HXr1 : dist_sq (arc_center b1) X = arc_radius b1 * arc_radius b1)
    by (rewrite HXc1; unfold arc_radius; rewrite dist_mul_self; reflexivity).
  assert (HXr2 : dist_sq (arc_center b2) X = arc_radius b2 * arc_radius b2)
    by (rewrite HXc2; unfold arc_radius; rewrite dist_mul_self; reflexivity).
  assert (Hjoin' : arc_end b1 = arc_start b2)
    by (unfold b1, b2; apply arc_join_offset_continuous; assumption).
  assert (HP1 : dist_sq (arc_center b1) (arc_end b1) = arc_radius b1 * arc_radius b1).
  { destruct (arc_center_equidistant b1 Hv1') as [_ Hse]. rewrite <- Hse.
    unfold arc_radius. rewrite dist_mul_self. reflexivity. }
  assert (HP2 : dist_sq (arc_center b2) (arc_end b1) = arc_radius b2 * arc_radius b2).
  { rewrite Hjoin'. unfold arc_radius. rewrite dist_mul_self. reflexivity. }
  assert (Hrne : arc_radius b1 <> arc_radius b2)
    by (rewrite Hrad1, Hrad2; intro Hc; apply Hne; lra).
  assert (Htang : dist (arc_center b1) (arc_center b2)
                = Rabs (arc_radius b1 - arc_radius b2)).
  { rewrite Hc1, Hc2, Hrad1, Hrad2.
    replace (arc_radius a1 + d - (arc_radius a2 + d))
      with (arc_radius a1 - arc_radius a2) by ring.
    apply join_normals_center_dist; assumption. }
  exact (internally_tangent_circles_unique (arc_center b1) (arc_center b2) X (arc_end b1)
           (arc_radius b1) (arc_radius b2) Hrne Htang HXr1 HXr2 HP1 HP2).
Qed.

Print Assumptions internally_tangent_circles_unique.
Print Assumptions two_offset_arcs_join_contact.
Print Assumptions join_normals_center_dist.
Print Assumptions two_clothoid_offset_arcs_meet_only_at_join.
