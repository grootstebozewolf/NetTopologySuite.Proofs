(* ============================================================================
   NetTopologySuite.Proofs.CurveSemicircle
   ----------------------------------------------------------------------------
   Buffer/noder pipeline, Stage 2b/2c-CURVE seam, rung 7: the SEMICIRCLE
   ARC -- one SQL/MM construction closing the two remaining gaps of the
   issue-#65 offset lane:

     (a) the U-TURN JOIN that `CurveRoundJoin` / `CurveOffsetAssembly`
         excluded (`n1 + n2 = 0`: anti-parallel normals, where the
         angular-midpoint normalisation divides by zero), and
     (b) the ROUND ENDCAP for open compound lines (the cap from the
         left (+d) offset boundary around the line end to the right
         (-d) offset boundary).

   Both are the same object: the semicircle centred at the corner/end
   point P with radius |d|, from `P + d*n` to `P - d*n`, with its mid
   control point `P + d*t` at the perpendicular (tangent) direction t.
   Unlike the round join's angular midpoint, the third control point
   here must be SUPPLIED (for antipodal endpoints both semicircles are
   geometrically admissible; `t` picks the sweep side -- for a cap, the
   outward tangent; for a U-turn join, the side away from the input).

     - `semicircle_arc P d n t`: the three-point arc above.
     - `semicircle_arc_valid`: for unit perpendicular `n`, `t` and
       `d <> 0` the control points are non-collinear -- the cross
       factors as `-2d^2 * cross(t,n)`, and `cross(t,n)^2 = 1` by
       `Vec.lagrange_identity` (unit + perpendicular).  A valid SQL/MM
       arc with NO exclusions beyond `d <> 0`.
     - `semicircle_arc_center_radius`: circumcircle EXACTLY `(P, |d|)`
       via `ArcOffsetThreePoint.equidistant_point_is_arc_center` (its
       third consumer).
     - `semicircle_uturn_connects`: at a U-turn join
       (`norm_start s2 = - norm_end s1`) the semicircle splices the two
       offset segments -- closing the exclusion that
       `CurveOffsetAssembly.curve_ring_offset_round_valid` carries as
       its no-U-turn hypothesis (single-join level; threading it
       through the assembly walk is a follow-up).
     - `semicircle_cap_connects`: at the end of a segment the SAME arc
       connects the `+d` offset boundary to the `-d` offset boundary --
       the round endcap of a two-sided buffer over an open compound
       line, in SQL/MM form (curve analogue of `BufferEndcap.v`'s
       round-cap layer).
     - `cap_tangent n := vperp n` supplies a canonical `t`
       (`cap_tangent_unit` / `cap_tangent_perp` discharge the
       hypotheses); the opposite sweep is `vneg (vperp n)`.

   Pure-R; THREE-AXIOM THROUGHOUT (classical-reals trio).  No
   `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance Vec Direction CurveGeometry ArcChordApprox.
From NTS.Proofs Require Import ArcOffsetThreePoint CurveRingOffset CurveRoundJoin.
From NTS.Proofs Require Import BufferOffset.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The semicircle arc.                                                    *)
(* -------------------------------------------------------------------------- *)

Definition semicircle_arc (P : Point) (d : R) (n t : Vec) : CircularArc :=
  mkCircularArc (pt_translate P (d * vx n) (d * vy n))
                (pt_translate P (d * vx t) (d * vy t))
                (pt_translate P (- d * vx n) (- d * vy n)).

(* The control-point cross in scalar form: -2 d^2 cross(t, n).               *)
Lemma semicircle_cross_scalar : forall (p_x p_y d nx ny tx ty : R),
  (p_x + d * tx - (p_x + d * nx)) * (p_y + - d * ny - (p_y + d * ny)) -
  (p_y + d * ty - (p_y + d * ny)) * (p_x + - d * nx - (p_x + d * nx)) =
  (- (2 * (d * d))) * (tx * ny - ty * nx).
Proof. intros. ring. Qed.

Theorem semicircle_arc_valid : forall P d n t,
  vdot n n = 1 -> vdot t t = 1 -> vdot n t = 0 ->
  d <> 0 ->
  valid_arc (semicircle_arc P d n t).
Proof.
  intros P d n t Hn Ht Hperp Hd.
  (* cross(t, n)^2 = 1 by Lagrange (unit + perpendicular) *)
  assert (Hsq : vcross n t * vcross n t = 1).
  { pose proof (lagrange_identity n t) as L.
    unfold vmag_sq in L. rewrite Hn, Ht, Hperp in L. lra. }
  assert (Hcr : vx t * vy n - vy t * vx n <> 0).
  { unfold vcross in Hsq. intros E. nra. }
  unfold valid_arc, semicircle_arc. cbv zeta.
  cbn [arc_start arc_mid arc_end].
  unfold pt_translate. cbn [px py].
  rewrite semicircle_cross_scalar.
  apply Rmult_integral_contrapositive_currified; [ nra | exact Hcr ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The semicircle lies on the offset circle, and its circumcircle is     *)
(*     exactly (P, |d|).                                                       *)
(* -------------------------------------------------------------------------- *)

Theorem semicircle_arc_on_offset_circle : forall P d n t,
  vdot n n = 1 -> vdot t t = 1 ->
  dist P (arc_start (semicircle_arc P d n t)) = Rabs d /\
  dist P (arc_mid   (semicircle_arc P d n t)) = Rabs d /\
  dist P (arc_end   (semicircle_arc P d n t)) = Rabs d.
Proof.
  intros P d n t Hn Ht.
  unfold semicircle_arc. cbn [arc_start arc_mid arc_end].
  assert (Habs : forall (c : R) (v : Vec), vdot v v = 1 ->
            dist P (pt_translate P (c * vx v) (c * vy v)) = Rabs c).
  { intros c v Hv. unfold dist. rewrite (dist_sq_translate_unit P c v Hv).
    replace (c * c) with (Rsqr c) by (unfold Rsqr; ring).
    apply sqrt_Rsqr_abs. }
  repeat split.
  - apply Habs. exact Hn.
  - apply Habs. exact Ht.
  - rewrite (Habs (- d) n Hn). apply Rabs_Ropp.
Qed.

Theorem semicircle_arc_center_radius : forall P d n t,
  vdot n n = 1 -> vdot t t = 1 -> vdot n t = 0 ->
  d <> 0 ->
  arc_center (semicircle_arc P d n t) = P /\
  arc_radius (semicircle_arc P d n t) = Rabs d.
Proof.
  intros P d n t Hn Ht Hperp Hd.
  pose proof (semicircle_arc_valid P d n t Hn Ht Hperp Hd) as Hva.
  assert (Hsm : dist_sq P (arc_start (semicircle_arc P d n t)) =
                dist_sq P (arc_mid (semicircle_arc P d n t))).
  { unfold semicircle_arc. cbn [arc_start arc_mid].
    rewrite (dist_sq_translate_unit P d n Hn).
    rewrite (dist_sq_translate_unit P d t Ht). reflexivity. }
  assert (Hse : dist_sq P (arc_start (semicircle_arc P d n t)) =
                dist_sq P (arc_end (semicircle_arc P d n t))).
  { unfold semicircle_arc. cbn [arc_start arc_end].
    rewrite (dist_sq_translate_unit P d n Hn).
    rewrite (dist_sq_translate_unit P (- d) n Hn). ring. }
  assert (Hcenter : arc_center (semicircle_arc P d n t) = P).
  { symmetry. apply (equidistant_point_is_arc_center _ P Hva Hsm Hse). }
  split; [ exact Hcenter | ].
  unfold arc_radius. rewrite Hcenter.
  destruct (semicircle_arc_on_offset_circle P d n t Hn Ht) as [Hs _].
  exact Hs.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  U-turn join: the semicircle splices anti-parallel-normal joins.        *)
(* -------------------------------------------------------------------------- *)

Theorem semicircle_uturn_connects : forall s1 s2 d t,
  segment_arc_valid s1 -> segment_arc_valid s2 ->
  curve_segment_end s1 = curve_segment_start s2 ->
  segment_norm_start s2 = vneg (segment_norm_end s1) ->
  arc_start (semicircle_arc (curve_segment_end s1) d
               (segment_norm_end s1) t) =
    curve_segment_end (curve_segment_offset s1 d) /\
  arc_end (semicircle_arc (curve_segment_end s1) d
               (segment_norm_end s1) t) =
    curve_segment_start (curve_segment_offset s2 d).
Proof.
  intros s1 s2 d t Hv1 Hv2 HP Hanti.
  split.
  - rewrite (curve_segment_offset_end s1 d Hv1). reflexivity.
  - rewrite (curve_segment_offset_start s2 d Hv2).
    rewrite Hanti. rewrite <- HP.
    unfold semicircle_arc. cbn [arc_end].
    apply point_eq; unfold pt_translate; cbn [px py vx vy vneg]; ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Round endcap: the SAME arc caps an open compound line's end,           *)
(*     connecting the +d offset boundary to the -d offset boundary.           *)
(* -------------------------------------------------------------------------- *)

Theorem semicircle_cap_connects : forall s d t,
  segment_arc_valid s ->
  arc_start (semicircle_arc (curve_segment_end s) d
               (segment_norm_end s) t) =
    curve_segment_end (curve_segment_offset s d) /\
  arc_end (semicircle_arc (curve_segment_end s) d
               (segment_norm_end s) t) =
    curve_segment_end (curve_segment_offset s (- d)).
Proof.
  intros s d t Hv.
  split.
  - rewrite (curve_segment_offset_end s d Hv). reflexivity.
  - rewrite (curve_segment_offset_end s (- d) Hv).
    unfold semicircle_arc. cbn [arc_end].
    apply point_eq; unfold pt_translate; cbn [px py]; ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  A canonical sweep direction: t := vperp n (the opposite sweep is       *)
(*     vneg (vperp n)).                                                       *)
(* -------------------------------------------------------------------------- *)

Definition cap_tangent (n : Vec) : Vec := vperp n.

Lemma cap_tangent_unit : forall n,
  vdot n n = 1 -> vdot (cap_tangent n) (cap_tangent n) = 1.
Proof.
  intros n Hn. unfold cap_tangent, vperp, vdot in *. cbn [vx vy]. lra.
Qed.

Lemma cap_tangent_perp : forall n,
  vdot n (cap_tangent n) = 0.
Proof.
  intros n. unfold cap_tangent, vperp, vdot. cbn [vx vy]. ring.
Qed.

Lemma cap_tangent_opp_unit : forall n,
  vdot n n = 1 ->
  vdot (vneg (cap_tangent n)) (vneg (cap_tangent n)) = 1.
Proof.
  intros n Hn. unfold cap_tangent, vperp, vneg, vdot in *. cbn [vx vy]. lra.
Qed.

Lemma cap_tangent_opp_perp : forall n,
  vdot n (vneg (cap_tangent n)) = 0.
Proof.
  intros n. unfold cap_tangent, vperp, vneg, vdot. cbn [vx vy]. ring.
Qed.

(* ========================================================================== *)
(* Axiom audit.  ALL headlines below are 3-axiom (classical-reals trio:      *)
(* sig_not_dec, sig_forall_dec, functional_extensionality_dep).              *)
(* ========================================================================== *)

Print Assumptions semicircle_arc_valid.
Print Assumptions semicircle_arc_on_offset_circle.
Print Assumptions semicircle_arc_center_radius.
Print Assumptions semicircle_uturn_connects.
Print Assumptions semicircle_cap_connects.
Print Assumptions cap_tangent_unit.
