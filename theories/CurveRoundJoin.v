(* ============================================================================
   NetTopologySuite.Proofs.CurveRoundJoin
   ----------------------------------------------------------------------------
   Buffer/noder pipeline, Stage 2b-CURVE seam, rung 5: the ROUND JOIN
   ARC in SQL/MM three-point form (issue #65 BUF-*; follows
   `CurveRingOffset.v`, whose tear witness
   `tangent_continuity_insufficient_for_offset` proves join edges are
   NECESSARY at non-G1 joins).

   At a join point P where the offset normals n1 (end of the incoming
   segment) and n2 (start of the outgoing segment) differ, the offset
   curve tears: the incoming offset ends at P + d*n1, the outgoing
   starts at P + d*n2.  JTS's round join fills the gap with the
   circular arc centred at P with radius |d| -- and a curve-aware
   buffer must emit that arc AS AN ARC (a `CurveGeometry.CircularArc`),
   not as a chord fan.  This file constructs it and proves it
   well-formed:

     - `round_join_arc P d n1 n2` -- start `P + d*n1`, end `P + d*n2`,
       mid control point `P + d*m^` with `m^` the normalised angular
       midpoint `(n1+n2)/|n1+n2|`.

     - `unit_cross_nonzero` (the TURNING LEMMA): two distinct,
       non-antipodal unit vectors have non-zero cross product.  (Cross
       zero forces `n2 = (n1.n2) n1` by orthogonal decomposition, and
       unit length forces `n1.n2 = +-1` -- i.e. equal or antipodal.)

     - `round_join_arc_valid`: under `n1 <> n2` (the join actually
       turns), `n1 + n2 <> 0` (not the U-turn boundary; that
       configuration is the tear witness's S-curve, handled by ONE
       semicircle in `CurveSemicircle.v`), unit normals, and `d <> 0`,
       the three control
       points are non-collinear: the emitted join is a VALID SQL/MM
       arc.  The control-point cross factors exactly as
       `d^2 * (2-h)/h * cross(n1,n2)` with `h = |n1+n2|` (so validity
       reduces to the turning lemma and `h <> 2`, i.e. `n1 <> n2`).

     - `round_join_arc_center_radius`: its circumcircle is EXACTLY
       (P, |d|) -- `arc_center = P`, `arc_radius = |d|` -- via rung 2's
       circumcenter uniqueness (`equidistant_point_is_arc_center`).
       So the join arc is geometrically the offset circle of the
       corner, as the buffer contract demands.

     - `round_join_connects`: the join arc's start/end coincide with
       the adjacent offset segments' endpoints (via rung 4's uniform
       normal-field lemmas) -- the adjacency facts the assembly rung
       needs to splice join arcs into `curve_ring_offset` output.

     - `segment_norm_end_unit_arc` / `_start_unit_arc` /
       `segment_norm_chord_unit`: the ring's own normal fields ARE
       unit vectors (arcs: radial over a valid arc; chords:
       `unit_perp` of a non-degenerate edge), discharging the unit
       hypotheses at instantiation.

   Pure-R; THREE-AXIOM THROUGHOUT (classical-reals trio).  No
   `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance Vec CurveGeometry ArcChordApprox.
From NTS.Proofs Require Import ArcOffsetThreePoint CurveRingOffset BufferOffset.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The turning lemma: distinct, non-antipodal unit vectors are not        *)
(*     parallel.                                                              *)
(* -------------------------------------------------------------------------- *)

Lemma unit_cross_nonzero : forall n1 n2 : Vec,
  vdot n1 n1 = 1 -> vdot n2 n2 = 1 ->
  n1 <> n2 -> vadd n1 n2 <> vzero ->
  vcross n1 n2 <> 0.
Proof.
  intros n1 n2 H1 H2 Hne Hnap Hc.
  unfold vdot in H1, H2. unfold vcross in Hc.
  set (t := vx n1 * vx n2 + vy n1 * vy n2).
  (* orthogonal decomposition with zero cross: n2 = t * n1 *)
  assert (Hx : vx n2 = t * vx n1).
  { assert (K : vx n2 * (vx n1 * vx n1 + vy n1 * vy n1) - t * vx n1 =
                - vy n1 * (vx n1 * vy n2 - vy n1 * vx n2))
      by (unfold t; ring).
    rewrite H1, Hc in K. lra. }
  assert (Hy : vy n2 = t * vy n1).
  { assert (K : vy n2 * (vx n1 * vx n1 + vy n1 * vy n1) - t * vy n1 =
                vx n1 * (vx n1 * vy n2 - vy n1 * vx n2))
      by (unfold t; ring).
    rewrite H1, Hc in K. lra. }
  (* unit length forces t = +-1 *)
  assert (Ht : t * t = 1).
  { assert (K : (t * vx n1) * (t * vx n1) + (t * vy n1) * (t * vy n1) =
                t * t * (vx n1 * vx n1 + vy n1 * vy n1)) by ring.
    rewrite H1 in K. rewrite Hx, Hy in H2. lra. }
  assert (Hcase : t = 1 \/ t = -1) by nra.
  destruct Hcase as [E | E].
  - apply Hne. apply Vec_eq.
    + rewrite Hx, E. ring.
    + rewrite Hy, E. ring.
  - apply Hnap. apply Vec_eq; unfold vadd, vzero; simpl.
    + rewrite Hx, E. ring.
    + rewrite Hy, E. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The round join arc.                                                    *)
(* -------------------------------------------------------------------------- *)

Definition round_join_arc (P : Point) (d : R) (n1 n2 : Vec) : CircularArc :=
  let m := vscale (/ vmag (vadd n1 n2)) (vadd n1 n2) in
  mkCircularArc (pt_translate P (d * vx n1) (d * vy n1))
                (pt_translate P (d * vx m) (d * vy m))
                (pt_translate P (d * vx n2) (d * vy n2)).

(* Scalar form of the control-point cross product: it factors through the    *)
(* normals' cross with the explicit coefficient d^2 (2-h)/h.                  *)
Lemma round_join_cross_scalar : forall (p_x p_y h d x1 y1 x2 y2 : R),
  h <> 0 ->
  (p_x + d * (/ h * (x1 + x2)) - (p_x + d * x1)) *
  (p_y + d * y2 - (p_y + d * y1)) -
  (p_y + d * (/ h * (y1 + y2)) - (p_y + d * y1)) *
  (p_x + d * x2 - (p_x + d * x1)) =
  (d * d * ((2 - h) * / h)) * (x1 * y2 - y1 * x2).
Proof.
  intros. field. assumption.
Qed.

(* Working facts about h = |n1 + n2| under the join hypotheses. *)
Section JoinFacts.
  Variables (n1 n2 : Vec).
  Hypothesis H1 : vdot n1 n1 = 1.
  Hypothesis H2 : vdot n2 n2 = 1.
  Hypothesis Hne : n1 <> n2.
  Hypothesis Hnap : vadd n1 n2 <> vzero.

  Let h := vmag (vadd n1 n2).

  Lemma join_h_pos : 0 < h.
  Proof.
    unfold h, vmag. apply sqrt_lt_R0.
    apply vmag_sq_pos. exact Hnap.
  Qed.

  Lemma join_h_sq : h * h = vmag_sq (vadd n1 n2).
  Proof.
    unfold h, vmag. apply sqrt_sqrt. apply vmag_sq_nonneg.
  Qed.

  (* |n1+n2|^2 = 2 + 2 (n1.n2) for unit vectors. *)
  Lemma join_sum_sq : vmag_sq (vadd n1 n2) = 2 + 2 * vdot n1 n2.
  Proof.
    unfold vdot in *.
    assert (K : vmag_sq (vadd n1 n2) =
                (vx n1 * vx n1 + vy n1 * vy n1) +
                (vx n2 * vx n2 + vy n2 * vy n2) +
                2 * (vx n1 * vx n2 + vy n1 * vy n2))
      by (unfold vmag_sq, vdot, vadd; simpl; ring).
    rewrite H1, H2 in K. lra.
  Qed.

  (* h = 2 would force n1 = n2. *)
  Lemma join_h_ne_2 : h <> 2.
  Proof.
    intros Eh.
    assert (Hdot : vdot n1 n2 = 1).
    { pose proof join_h_sq as Hsq. rewrite join_sum_sq in Hsq.
      rewrite Eh in Hsq. lra. }
    apply Hne.
    (* |n1 - n2|^2 = 2 - 2 (n1.n2) = 0, so componentwise equal *)
    unfold vdot in H1, H2, Hdot.
    assert (Hz : (vx n1 - vx n2) * (vx n1 - vx n2) +
                 (vy n1 - vy n2) * (vy n1 - vy n2) = 0).
    { assert (K : (vx n1 - vx n2) * (vx n1 - vx n2) +
                  (vy n1 - vy n2) * (vy n1 - vy n2) =
                  (vx n1 * vx n1 + vy n1 * vy n1) +
                  (vx n2 * vx n2 + vy n2 * vy n2) -
                  2 * (vx n1 * vx n2 + vy n1 * vy n2)) by ring.
      rewrite H1, H2, Hdot in K. lra. }
    pose proof (sqr_nonneg (vx n1 - vx n2)) as Ha.
    pose proof (sqr_nonneg (vy n1 - vy n2)) as Hb.
    assert (Hxz : (vx n1 - vx n2) * (vx n1 - vx n2) = 0) by lra.
    assert (Hyz : (vy n1 - vy n2) * (vy n1 - vy n2) = 0) by lra.
    apply sqr_eq_zero in Hxz. apply sqr_eq_zero in Hyz.
    apply Vec_eq; lra.
  Qed.
End JoinFacts.

Theorem round_join_arc_valid : forall P d n1 n2,
  vdot n1 n1 = 1 -> vdot n2 n2 = 1 ->
  n1 <> n2 -> vadd n1 n2 <> vzero ->
  d <> 0 ->
  valid_arc (round_join_arc P d n1 n2).
Proof.
  intros P d n1 n2 H1 H2 Hne Hnap Hd.
  pose proof (join_h_pos n1 n2 Hnap) as Hh.
  pose proof (join_h_ne_2 n1 n2 H1 H2 Hne) as Hh2.
  pose proof (unit_cross_nonzero n1 n2 H1 H2 Hne Hnap) as Hcr.
  unfold vcross in Hcr.
  unfold valid_arc, round_join_arc. cbv zeta.
  cbn [arc_start arc_mid arc_end].
  set (h := vmag (vadd n1 n2)) in *.
  unfold pt_translate, vscale, vadd. cbn [px py vx vy].
  rewrite round_join_cross_scalar by lra.
  apply Rmult_integral_contrapositive_currified; [ | exact Hcr ].
  apply Rmult_integral_contrapositive_currified.
  - nra.
  - apply Rmult_integral_contrapositive_currified.
    + lra.
    + apply Rinv_neq_0_compat. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The join arc lies on the offset circle of the corner.                  *)
(* -------------------------------------------------------------------------- *)

(* dist_sq from P to a point P + d*v with |v| = 1 is d^2. *)
Lemma dist_sq_translate_unit : forall P d (v : Vec),
  vdot v v = 1 ->
  dist_sq P (pt_translate P (d * vx v) (d * vy v)) = d * d.
Proof.
  intros P d v Hv. unfold vdot in Hv.
  unfold dist_sq, pt_translate. simpl.
  replace ((px P - (px P + d * vx v)) * (px P - (px P + d * vx v)) +
           (py P - (py P + d * vy v)) * (py P - (py P + d * vy v)))
    with (d * d * (vx v * vx v + vy v * vy v)) by ring.
  rewrite Hv. ring.
Qed.

(* The angular midpoint is itself a unit vector. *)
Lemma join_mid_unit : forall n1 n2,
  vdot n1 n1 = 1 -> vdot n2 n2 = 1 -> vadd n1 n2 <> vzero ->
  vdot (vscale (/ vmag (vadd n1 n2)) (vadd n1 n2))
       (vscale (/ vmag (vadd n1 n2)) (vadd n1 n2)) = 1.
Proof.
  intros n1 n2 H1 H2 Hnap.
  pose proof (join_h_pos n1 n2 Hnap) as Hh.
  pose proof (join_h_sq n1 n2) as Hsq.
  set (h := vmag (vadd n1 n2)) in *.
  assert (K : vdot (vscale (/ h) (vadd n1 n2)) (vscale (/ h) (vadd n1 n2)) =
              vmag_sq (vadd n1 n2) * / (h * h)).
  { unfold vmag_sq, vdot, vscale, vadd. simpl. field. lra. }
  rewrite K, <- Hsq. field. lra.
Qed.

Theorem round_join_arc_on_offset_circle : forall P d n1 n2,
  vdot n1 n1 = 1 -> vdot n2 n2 = 1 -> vadd n1 n2 <> vzero ->
  dist P (arc_start (round_join_arc P d n1 n2)) = Rabs d /\
  dist P (arc_mid   (round_join_arc P d n1 n2)) = Rabs d /\
  dist P (arc_end   (round_join_arc P d n1 n2)) = Rabs d.
Proof.
  intros P d n1 n2 H1 H2 Hnap.
  unfold round_join_arc. cbv zeta. cbn [arc_start arc_mid arc_end].
  assert (Habs : forall v, vdot v v = 1 ->
            dist P (pt_translate P (d * vx v) (d * vy v)) = Rabs d).
  { intros v Hv. unfold dist. rewrite (dist_sq_translate_unit P d v Hv).
    replace (d * d) with (Rsqr d) by (unfold Rsqr; ring).
    apply sqrt_Rsqr_abs. }
  repeat split; apply Habs.
  - exact H1.
  - apply join_mid_unit; assumption.
  - exact H2.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The circumcircle of the join arc is exactly (P, |d|) -- by rung 2's    *)
(*     circumcenter uniqueness.                                               *)
(* -------------------------------------------------------------------------- *)

Theorem round_join_arc_center_radius : forall P d n1 n2,
  vdot n1 n1 = 1 -> vdot n2 n2 = 1 ->
  n1 <> n2 -> vadd n1 n2 <> vzero ->
  d <> 0 ->
  arc_center (round_join_arc P d n1 n2) = P /\
  arc_radius (round_join_arc P d n1 n2) = Rabs d.
Proof.
  intros P d n1 n2 H1 H2 Hne Hnap Hd.
  pose proof (round_join_arc_valid P d n1 n2 H1 H2 Hne Hnap Hd) as Hva.
  (* P is equidistant (in dist_sq) from the three control points. *)
  assert (Hm : vdot (vscale (/ vmag (vadd n1 n2)) (vadd n1 n2))
                    (vscale (/ vmag (vadd n1 n2)) (vadd n1 n2)) = 1)
    by (apply join_mid_unit; assumption).
  assert (Hsm : dist_sq P (arc_start (round_join_arc P d n1 n2)) =
                dist_sq P (arc_mid (round_join_arc P d n1 n2))).
  { unfold round_join_arc. cbv zeta. cbn [arc_start arc_mid].
    rewrite (dist_sq_translate_unit P d n1 H1).
    rewrite (dist_sq_translate_unit P d _ Hm). reflexivity. }
  assert (Hse : dist_sq P (arc_start (round_join_arc P d n1 n2)) =
                dist_sq P (arc_end (round_join_arc P d n1 n2))).
  { unfold round_join_arc. cbv zeta. cbn [arc_start arc_end].
    rewrite (dist_sq_translate_unit P d n1 H1).
    rewrite (dist_sq_translate_unit P d n2 H2). reflexivity. }
  assert (Hcenter : arc_center (round_join_arc P d n1 n2) = P).
  { symmetry.
    apply (equidistant_point_is_arc_center _ P Hva Hsm Hse). }
  split; [ exact Hcenter | ].
  unfold arc_radius. rewrite Hcenter.
  destruct (round_join_arc_on_offset_circle P d n1 n2 H1 H2 Hnap)
    as [Hs _].
  exact Hs.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  The join arc splices: its endpoints ARE the adjacent offset            *)
(*     segments' endpoints (rung 4's uniform normal field).                   *)
(* -------------------------------------------------------------------------- *)

Theorem round_join_connects : forall s1 s2 d,
  segment_arc_valid s1 -> segment_arc_valid s2 ->
  curve_segment_end s1 = curve_segment_start s2 ->
  arc_start (round_join_arc (curve_segment_end s1) d
               (segment_norm_end s1) (segment_norm_start s2)) =
    curve_segment_end (curve_segment_offset s1 d) /\
  arc_end (round_join_arc (curve_segment_end s1) d
               (segment_norm_end s1) (segment_norm_start s2)) =
    curve_segment_start (curve_segment_offset s2 d).
Proof.
  intros s1 s2 d Hs1 Hs2 HP.
  split.
  - rewrite (curve_segment_offset_end s1 d Hs1). reflexivity.
  - rewrite (curve_segment_offset_start s2 d Hs2).
    unfold round_join_arc. cbv zeta. cbn [arc_end].
    rewrite HP. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  The ring's own normal fields are unit vectors -- discharging the       *)
(*     unit hypotheses at instantiation.                                      *)
(* -------------------------------------------------------------------------- *)

Lemma segment_norm_end_unit_arc : forall a,
  valid_arc a ->
  vdot (segment_norm_end (CSArc a)) (segment_norm_end (CSArc a)) = 1.
Proof.
  intros a Hva.
  pose proof (arc_radius_pos a Hva) as Hr.
  assert (Hd2 : dist_sq (arc_center a) (arc_end a) =
                arc_radius a * arc_radius a)
    by (apply dist_sq_of_dist; apply arc_center_dist_end; exact Hva).
  unfold dist_sq in Hd2.
  cbn [segment_norm_end]. unfold vdot. cbn [vx vy].
  set (r := arc_radius a) in *.
  assert (K : (px (arc_end a) - px (arc_center a)) / r *
              ((px (arc_end a) - px (arc_center a)) / r) +
              (py (arc_end a) - py (arc_center a)) / r *
              ((py (arc_end a) - py (arc_center a)) / r) =
              ((px (arc_center a) - px (arc_end a)) *
               (px (arc_center a) - px (arc_end a)) +
               (py (arc_center a) - py (arc_end a)) *
               (py (arc_center a) - py (arc_end a))) * / (r * r)).
  { field. lra. }
  rewrite K, Hd2. field. lra.
Qed.

Lemma segment_norm_start_unit_arc : forall a,
  valid_arc a ->
  vdot (segment_norm_start (CSArc a)) (segment_norm_start (CSArc a)) = 1.
Proof.
  intros a Hva.
  pose proof (arc_radius_pos a Hva) as Hr.
  assert (Hd2 : dist_sq (arc_center a) (arc_start a) =
                arc_radius a * arc_radius a)
    by (apply dist_sq_of_dist; apply arc_center_dist_start).
  unfold dist_sq in Hd2.
  cbn [segment_norm_start]. unfold vdot. cbn [vx vy].
  set (r := arc_radius a) in *.
  assert (K : (px (arc_start a) - px (arc_center a)) / r *
              ((px (arc_start a) - px (arc_center a)) / r) +
              (py (arc_start a) - py (arc_center a)) / r *
              ((py (arc_start a) - py (arc_center a)) / r) =
              ((px (arc_center a) - px (arc_start a)) *
               (px (arc_center a) - px (arc_start a)) +
               (py (arc_center a) - py (arc_start a)) *
               (py (arc_center a) - py (arc_start a))) * / (r * r)).
  { field. lra. }
  rewrite K, Hd2. field. lra.
Qed.

Lemma segment_norm_chord_unit : forall p q,
  p <> q ->
  vdot (segment_norm_end (CSChord p q)) (segment_norm_end (CSChord p q)) = 1.
Proof.
  intros p q Hpq.
  cbn [segment_norm_end].
  apply vmag_sq_unit_perp.
  apply seg_vec_nonzero. exact Hpq.
Qed.

(* ========================================================================== *)
(* Axiom audit.  ALL headlines below are 3-axiom (classical-reals trio:      *)
(* sig_not_dec, sig_forall_dec, functional_extensionality_dep).              *)
(* ========================================================================== *)

Print Assumptions unit_cross_nonzero.
Print Assumptions round_join_arc_valid.
Print Assumptions round_join_arc_on_offset_circle.
Print Assumptions round_join_arc_center_radius.
Print Assumptions round_join_connects.
Print Assumptions segment_norm_end_unit_arc.
Print Assumptions segment_norm_chord_unit.
