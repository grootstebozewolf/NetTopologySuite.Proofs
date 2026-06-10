(* ============================================================================
   NetTopologySuite.Proofs.GeneralTriangleExterior
   ----------------------------------------------------------------------------
   The triangle's EXTERIOR half of the corrected off-ring H1 seam, and the
   half-plane escape engine it needs.

   `RectangleOffringSeam.v` discharged the corrected seam totally for the
   rectangle, using axis-aligned escape rays (an exterior point of a box is
   beyond the box in some axis direction).  That is FALSE for a triangle: an
   exterior point can sit strictly inside the vertex bounding box (e.g.
   (3,3) for the triangle (0,0),(4,0),(0,4)).  What is always true is that an
   exterior point (`gtri p < 0`, some inward slack negative) lies strictly
   beyond ONE EDGE'S HALF-PLANE, while the whole skeleton lies inside it.  So
   the right generic engine is:

     `escape_beyond_halfplane` : if the skeleton satisfies a*x + b*y <= c and
       p satisfies c < a*px p + b*py p (with (a,b) <> 0), then p is in NO
       bounded complement component -- the ray along the outward normal
       escapes every radius.  The radius defeat uses the Cauchy-Schwarz
       polynomial identity (a*X+b*Y)^2 <= (a^2+b^2)(X^2+Y^2) (the difference
       is (a*Y-b*X)^2), so no square roots appear.

   Triangle instantiation:
     - `gtri_image_slacks_nonneg` : the skeleton lies in all three closed
       inner half-planes (each slack is affine along an edge with endpoint
       values 0 / gdbl);
     - `gtri_exterior_escapes`    : `gtri p < 0 -> ~ in_bounded_component_cont`;
     - `gtri_geometric_imp_in_ring` : the TOTAL geometric->parity direction
       (trichotomy: exterior escapes, skeleton is off-ring-excluded, interior
       is the closed strict-interior family);
     - `gtri_parity_seam_offring_of_exterior_parity` : the triangle's TOTAL
       off-ring seam, conditional on the ONE remaining fact -- exterior
       points have even ray parity (`gtri p < 0 -> ~ point_in_ring p`).
       That exterior-parity residual is the named target of the next rung.

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam.
From NTS.Proofs Require Import PointInRingCorrect JCT JCT_OnEdgeCounterexample.
From NTS.Proofs Require Import RectangleJCT RectangleSeparation RectangleOffringSeam.
From NTS.Proofs Require Import GeneralTriangleSeparation GeneralTriangleParity.
From NTS.Proofs Require Import GeneralTriangleHoleNesting GeneralTriangleJCT.
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §0  Square positivity for compound terms (nra cannot synthesise these).
   --------------------------------------------------------------------------- *)

Lemma sqr_nonneg : forall z : R, 0 <= z * z.
Proof. intro z; pose proof (Rle_0_sqr z) as H; unfold Rsqr in H; exact H. Qed.

(* ---------------------------------------------------------------------------
   §1  The half-plane escape engine.
   --------------------------------------------------------------------------- *)

Theorem escape_beyond_halfplane : forall (r : Ring) (p : Point) (a b c : R),
  0 < a * a + b * b ->
  (forall q : Point, ring_image r q -> a * px q + b * py q <= c) ->
  c < a * px p + b * py p ->
  ~ in_bounded_component_cont r p.
Proof.
  intros r p a b c Hs0 Hskel Hp; destruct p as [u v]; cbn [px py] in *.
  intros [M [HM Hb]].
  set (s := a * a + b * b) in *.
  set (v0 := a * u + b * v) in *.
  set (d := ((s + 1) * (M + 1) - v0) / s).
  set (T := Rmax 0 d).
  (* bridging equations so nra can relate the folded atoms to raw terms *)
  assert (Hsdef : s = a * a + b * b) by reflexivity.
  assert (Hv0def : v0 = a * u + b * v) by reflexivity.
  assert (HT0 : 0 <= T) by apply Rmax_l.
  (* The ray's terminal value defeats the radius bound. *)
  assert (HW : (s + 1) * (M + 1) <= v0 + T * s).
  { unfold T. destruct (Rle_dec d 0) as [Hd | Hd].
    - rewrite Rmax_left by lra.
      assert (Hd' : (s + 1) * (M + 1) - v0 = d * s) by (unfold d; field; lra).
      nra.
    - rewrite Rmax_right by lra.
      assert (Hd' : (s + 1) * (M + 1) - v0 = d * s) by (unfold d; field; lra).
      lra. }
  assert (Hconn : connected_in_complement_cont r (mkPoint u v)
                    (mkPoint (u + T * a) (v + T * b))).
  { exists (fun t => mkPoint ((1 - t) * u + t * (u + T * a))
                             ((1 - t) * v + t * (v + T * b))).
    split; [ apply straight_path_continuous | ]. split; [ | split ].
    - cbn [px py]; f_equal; lra.
    - cbn [px py]; f_equal; lra.
    - intros t Ht Himg. apply Hskel in Himg. cbn [px py] in Himg.
      assert (Htt : 0 <= t * T) by nra.
      (* the value along the ray is v0 + (t*T)*s > c *)
      nra. }
  specialize (Hb _ Hconn). cbn [px py] in Hb.
  set (X := u + T * a) in *. set (Y := v + T * b) in *.
  (* Cauchy-Schwarz, square-root-free: the defect is the square (aY - bX)^2. *)
  assert (Hsq : 0 <= (a * Y - b * X) * (a * Y - b * X))
    by (pose proof (Rle_0_sqr (a * Y - b * X)) as Hs'; unfold Rsqr in Hs'; exact Hs').
  assert (HCS : (a * X + b * Y) * (a * X + b * Y) <= s * (X * X + Y * Y))
    by (unfold s; nra).
  assert (Hval : a * X + b * Y = v0 + T * s) by (unfold X, Y, v0, s; ring).
  assert (Hsm : 0 < s * M) by nra.
  assert (H1 : 0 < (s + 1) * (M + 1)) by nra.
  assert (H2 : ((s + 1) * (M + 1)) * ((s + 1) * (M + 1))
                 <= (v0 + T * s) * (v0 + T * s)) by nra.
  assert (H3 : s * (M * M) < ((s + 1) * (M + 1)) * ((s + 1) * (M + 1)))
    by nra.
  nra.
Qed.

(* ---------------------------------------------------------------------------
   §2  The triangle skeleton lies in all three closed inner half-planes.
   --------------------------------------------------------------------------- *)

Lemma gtri_image_slacks_nonneg : forall ax ay bx by_ cx cy q,
  0 < gdbl ax ay bx by_ cx cy ->
  ring_image (gtri_ring ax ay bx by_ cx cy) q ->
  0 <= gsA ax ay bx by_ q /\ 0 <= gsB bx by_ cx cy q /\ 0 <= gsC ax ay cx cy q.
Proof.
  intros ax ay bx by_ cx cy q Hccw [e [t [Hin [Ht [Hx Hy]]]]].
  unfold gdbl in Hccw.
  rewrite (ring_edges_gtri ax ay bx by_ cx cy) in Hin. cbn [In] in Hin.
  destruct Hin as [He | [He | [He | []]]];
    subst e; cbn [px py fst snd] in Hx, Hy;
    unfold gsA, gsB, gsC; rewrite Hx, Hy; repeat split; nra.
Qed.

(* ---------------------------------------------------------------------------
   §3  Exterior escape: a strictly-exterior point is in no bounded component.
   --------------------------------------------------------------------------- *)

Theorem gtri_exterior_escapes : forall ax ay bx by_ cx cy p,
  0 < gdbl ax ay bx by_ cx cy ->
  gtri ax ay bx by_ cx cy p < 0 ->
  ~ in_bounded_component_cont (gtri_ring ax ay bx by_ cx cy) p.
Proof.
  intros ax ay bx by_ cx cy p Hccw Hneg.
  unfold gtri in Hneg.
  (* Cauchy-Schwarz nondegeneracy: a zero-length edge kills gdbl.  Each block
     hands nra the defect square plus the component squares it needs. *)
  assert (HndAB : 0 < (by_ - ay) * (by_ - ay) + (bx - ax) * (bx - ax)).
  { pose proof (sqr_nonneg ((bx - ax) * (cx - ax) + (by_ - ay) * (cy - ay))).
    pose proof (sqr_nonneg (cy - ay)). pose proof (sqr_nonneg (cx - ax)).
    unfold gdbl in Hccw. nra. }
  assert (HndBC : 0 < (cy - by_) * (cy - by_) + (cx - bx) * (cx - bx)).
  { pose proof (sqr_nonneg ((cx - bx) * (ax - bx) + (cy - by_) * (ay - by_))).
    pose proof (sqr_nonneg (ay - by_)). pose proof (sqr_nonneg (ax - bx)).
    unfold gdbl in Hccw. nra. }
  assert (HndCA : 0 < (ay - cy) * (ay - cy) + (ax - cx) * (ax - cx)).
  { pose proof (sqr_nonneg ((ax - cx) * (bx - cx) + (ay - cy) * (by_ - cy))).
    pose proof (sqr_nonneg (by_ - cy)). pose proof (sqr_nonneg (bx - cx)).
    unfold gdbl in Hccw. nra. }
  destruct (Rmin_neg_inv _ _ Hneg) as [H1 | HsC];
    [ destruct (Rmin_neg_inv _ _ H1) as [HsA | HsB] | ].
  - (* gsA < 0 : beyond edge A--B's half-plane *)
    apply (escape_beyond_halfplane _ _ (by_ - ay) (- (bx - ax))
             ((by_ - ay) * ax - (bx - ax) * ay)).
    + nra.
    + intros q Hq.
      destruct (gtri_image_slacks_nonneg ax ay bx by_ cx cy q Hccw Hq) as [HA _].
      unfold gsA in HA. nra.
    + unfold gsA in HsA. nra.
  - (* gsB < 0 : beyond edge B--C's half-plane *)
    apply (escape_beyond_halfplane _ _ (cy - by_) (- (cx - bx))
             ((cy - by_) * bx - (cx - bx) * by_)).
    + nra.
    + intros q Hq.
      destruct (gtri_image_slacks_nonneg ax ay bx by_ cx cy q Hccw Hq) as [_ [HB _]].
      unfold gsB in HB. nra.
    + unfold gsB in HsB. nra.
  - (* gsC < 0 : beyond edge C--A's half-plane *)
    apply (escape_beyond_halfplane _ _ (ay - cy) (- (ax - cx))
             ((ay - cy) * cx - (ax - cx) * cy)).
    + nra.
    + intros q Hq.
      destruct (gtri_image_slacks_nonneg ax ay bx by_ cx cy q Hccw Hq) as [_ [_ HC]].
      unfold gsC in HC. nra.
    + unfold gsC in HsC. nra.
Qed.

(* ---------------------------------------------------------------------------
   §4  The TOTAL geometric -> parity direction of the off-ring seam.
   --------------------------------------------------------------------------- *)

Theorem gtri_geometric_imp_in_ring : forall ax ay bx by_ cx cy p,
  0 < gdbl ax ay bx by_ cx cy ->
  ray_avoids_vertices p (gtri_ring ax ay bx by_ cx cy) ->
  geometric_interior_cont p (gtri_ring ax ay bx by_ cx cy) ->
  point_in_ring p (gtri_ring ax ay bx by_ cx cy).
Proof.
  intros ax ay bx by_ cx cy p Hccw Hrav [Hcompl Hbnd].
  destruct (Rtotal_order (gtri ax ay bx by_ cx cy p) 0) as [Hneg | [Hzero | Hpos]].
  - exfalso. exact (gtri_exterior_escapes ax ay bx by_ cx cy p Hccw Hneg Hbnd).
  - exfalso. apply Hcompl.
    apply (gtri_zero_imp_ring_image ax ay bx by_ cx cy Hccw p Hzero).
  - apply gtri_interior_in_ring; assumption.
Qed.

(* ---------------------------------------------------------------------------
   §5  The triangle's TOTAL off-ring seam, with the single residual isolated:
       exterior points have even ray parity.
   --------------------------------------------------------------------------- *)

Theorem gtri_parity_seam_offring_of_exterior_parity :
  forall ax ay bx by_ cx cy p,
    0 < gdbl ax ay bx by_ cx cy ->
    (gtri ax ay bx by_ cx cy p < 0 ->
       ~ point_in_ring p (gtri_ring ax ay bx by_ cx cy)) ->
    parity_characterises_interior_cont_offring p (gtri_ring ax ay bx by_ cx cy).
Proof.
  intros ax ay bx by_ cx cy p Hccw Hextpar.
  unfold parity_characterises_interior_cont_offring.
  intros _ _ _ Hcompl _ Hrav.
  destruct (Rtotal_order (gtri ax ay bx by_ cx cy p) 0) as [Hneg | [Hzero | Hpos]].
  - split.
    + intros [_ Hbnd]. exfalso.
      exact (gtri_exterior_escapes ax ay bx by_ cx cy p Hccw Hneg Hbnd).
    + intro Hpir. exfalso. exact (Hextpar Hneg Hpir).
  - exfalso. apply Hcompl.
    apply (gtri_zero_imp_ring_image ax ay bx by_ cx cy Hccw p Hzero).
  - symmetry. apply general_triangle_parity_characterises_interior; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions escape_beyond_halfplane.
Print Assumptions gtri_exterior_escapes.
Print Assumptions gtri_geometric_imp_in_ring.
Print Assumptions gtri_parity_seam_offring_of_exterior_parity.
