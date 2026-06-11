(* ============================================================================
   NetTopologySuite.Proofs.CurveJoinClassify
   ----------------------------------------------------------------------------
   Buffer/noder pipeline, rung 10 (issue #65, forward pointer P10 brick
   1): CERTIFIED RATIONAL DECISION PROCEDURES for the assembly oracles.

   Rungs 6/8/9 are conditional on the SPECS of two abstract boolean
   oracles -- `g1dec` (are the join normals equal?) and `uturndec` (are
   they anti-parallel?) -- because real-vector equality is not
   computable.  This file shows those oracles are REALIZABLE BY EXACT
   RATIONAL ARITHMETIC, so an extracted implementation can decide them
   with zero rounding and the specs discharge outright on rational
   inputs:

     - Although the normal fields carry an irrational normalisation
       (`/r` with `r = sqrt(...)`), EQUALITY of unit normals is a
       rational condition on the UN-normalised vectors:

           u^ = v^    <->  cross(u,v) = 0  /\  0 < dot(u,v)
           u^ = -(v^) <->  cross(u,v) = 0  /\  dot(u,v) < 0

       (`unit_eq_iff_cross_dot`, `unit_opp_iff_cross_dot`; forward by
       substitution, backward by the rung-5 orthogonal-decomposition
       technique generalised to non-unit vectors).

     - The ring's normal fields ARE normalised rational vectors: the
       RAW normal (`segment_raw_norm_{end,start}`: `vperp` of the
       direction for chords, `P - arc_center` for arcs -- both rational
       in the control points, since `arc_center` is the rational
       circumcenter formula) normalises to exactly
       `segment_norm_{end,start}` (`segment_norm_end_normalises`).

     - HEADLINES `g1_decision_correct` / `uturn_decision_correct`: the
       G1 and U-turn join conditions of rungs 4-9 are EQUIVALENT to the
       two rational sign conditions on the raw normals -- for every
       segment-kind combination.  An oracle computing one cross and one
       dot in exact `Q` is a correct `g1dec` / `uturndec`.

     - `offset_safe_iff_sq`: the per-arc safety bound `-r < d` is
       decidable from the RATIONAL `r^2` (`d >= 0 \/ d^2 < r^2`), so
       `ring_offset_safe` needs no square root either.

   With `valid_arc` (a rational determinant), chord non-degeneracy and
   ring adjacency/closedness (rational point equalities), EVERY
   hypothesis of `curve_ring_offset_total_valid` is therefore decidable
   in exact rational arithmetic over rational control points -- the
   soundness story a `CURVE_JOIN_CLASSIFY` oracle mode wraps.  The
   OCaml driver mode itself (P10 brick 2) is deliberately deferred: the
   oracle binary links against the Flocq-extracted modules and is built
   by CI's container, not in this session's environment.

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
From NTS.Proofs Require Import CurveOffsetAssembly BufferOffset.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Working facts about vmag.                                              *)
(* -------------------------------------------------------------------------- *)

Lemma vmag_pos : forall u : Vec, u <> vzero -> 0 < vmag u.
Proof.
  intros u Hu. unfold vmag. apply sqrt_lt_R0. apply vmag_sq_pos. exact Hu.
Qed.

Lemma vmag_sq_eq : forall u : Vec, vmag u * vmag u = vmag_sq u.
Proof.
  intros u. unfold vmag. apply sqrt_sqrt. apply vmag_sq_nonneg.
Qed.

(* sqrt of a positive-scaled square: vmag (t·u) = t * vmag u for t > 0.      *)
Lemma vmag_scale_pos : forall (t : R) (u : Vec),
  0 < t -> vmag (vscale t u) = t * vmag u.
Proof.
  intros t u Ht.
  unfold vmag.
  assert (Hsq : vmag_sq (vscale t u) = (t * sqrt (vmag_sq u)) *
                                       (t * sqrt (vmag_sq u))).
  { unfold vmag_sq, vdot, vscale. cbn [vx vy].
    assert (Hs : sqrt (vmag_sq u) * sqrt (vmag_sq u) = vmag_sq u)
      by (apply sqrt_sqrt; apply vmag_sq_nonneg).
    unfold vmag_sq, vdot in Hs. nra. }
  rewrite Hsq.
  replace ((t * sqrt (vmag_sq u)) * (t * sqrt (vmag_sq u)))
    with (Rsqr (t * sqrt (vmag_sq u))) by (unfold Rsqr; ring).
  rewrite sqrt_Rsqr; [ reflexivity | ].
  apply Rmult_le_pos; [ lra | apply sqrt_pos ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Unit-vector equality is a rational condition on the raw vectors.       *)
(* -------------------------------------------------------------------------- *)

Theorem unit_eq_iff_cross_dot : forall u v : Vec,
  u <> vzero -> v <> vzero ->
  (vscale (/ vmag u) u = vscale (/ vmag v) v <->
   vcross u v = 0 /\ 0 < vdot u v).
Proof.
  intros u v Hu Hv.
  pose proof (vmag_pos u Hu) as Hmu.
  pose proof (vmag_pos v Hv) as Hmv.
  pose proof (vmag_sq_eq u) as Hsu.
  pose proof (vmag_sq_eq v) as Hsv.
  pose proof (vmag_sq_pos u Hu) as Hqu.
  split.
  - (* normalised equality -> cross zero, dot positive *)
    intros H.
    assert (Hx : / vmag u * vx u = / vmag v * vx v).
    { change (vx (vscale (/ vmag u) u) = vx (vscale (/ vmag v) v)).
      rewrite H. reflexivity. }
    assert (Hy : / vmag u * vy u = / vmag v * vy v).
    { change (vy (vscale (/ vmag u) u) = vy (vscale (/ vmag v) v)).
      rewrite H. reflexivity. }
    assert (Hvx : vx v = vmag v * (/ vmag u * vx u))
      by (rewrite Hx; field; lra).
    assert (Hvy : vy v = vmag v * (/ vmag u * vy u))
      by (rewrite Hy; field; lra).
    split.
    + unfold vcross. rewrite Hvx, Hvy. ring.
    + unfold vdot. rewrite Hvx, Hvy.
      replace (vx u * (vmag v * (/ vmag u * vx u)) +
               vy u * (vmag v * (/ vmag u * vy u)))
        with (vmag v * / vmag u * (vx u * vx u + vy u * vy u)) by ring.
      assert (Hmsq : vx u * vx u + vy u * vy u = vmag u * vmag u)
        by (rewrite Hsu; unfold vmag_sq, vdot; ring).
      rewrite Hmsq.
      replace (vmag v * / vmag u * (vmag u * vmag u))
        with (vmag v * vmag u) by (field; lra).
      apply Rmult_lt_0_compat; assumption.
  - (* cross zero + dot positive -> normalised equality *)
    intros [Hc Hd].
    unfold vcross in Hc. unfold vdot in Hd.
    set (D := vx u * vx v + vy u * vy v) in *.
    (* orthogonal decomposition with zero cross, division-free:          *)
    (*    S · v = D · u  componentwise, with S = |u|².                    *)
    assert (HvxS : vx v * vmag_sq u = D * vx u).
    { assert (K : vx v * (vx u * vx u + vy u * vy u) -
                  (vx u * vx v + vy u * vy v) * vx u =
                  - vy u * (vx u * vy v - vy u * vx v)) by ring.
      rewrite Hc in K. unfold D, vmag_sq, vdot. lra. }
    assert (HvyS : vy v * vmag_sq u = D * vy u).
    { assert (K : vy v * (vx u * vx u + vy u * vy u) -
                  (vx u * vx v + vy u * vy v) * vy u =
                  vx u * (vx u * vy v - vy u * vx v)) by ring.
      rewrite Hc in K. unfold D, vmag_sq, vdot. lra. }
    (* D² = |v|²·|u|², and with D > 0:  D = |v|·|u|.                      *)
    assert (HD2 : vmag_sq u * (D * D - vmag_sq v * vmag_sq u) = 0).
    { assert (K2 : (vx v * vmag_sq u) * (vx v * vmag_sq u) +
                   (vy v * vmag_sq u) * (vy v * vmag_sq u) =
                   (D * vx u) * (D * vx u) + (D * vy u) * (D * vy u))
        by (rewrite HvxS, HvyS; reflexivity).
      unfold D, vmag_sq, vdot in *. nra. }
    assert (HDsq : D * D = vmag_sq v * vmag_sq u).
    { destruct (Rmult_integral _ _ HD2) as [Hz | Hz]; lra. }
    rewrite <- (vmag_sq_eq u), <- (vmag_sq_eq v) in HDsq.
    assert (HDms : D = vmag v * vmag u).
    { assert (Hfac : (D - vmag v * vmag u) * (D + vmag v * vmag u) = 0)
        by nra.
      destruct (Rmult_integral _ _ Hfac) as [Hz | Hz]; nra. }
    (* component goals, cancelled against the positive magnitudes        *)
    rewrite HDms in HvxS, HvyS.
    rewrite <- (vmag_sq_eq u) in HvxS, HvyS.
    apply Vec_eq; unfold vscale; cbn [vx vy].
    + assert (Hz : vmag u * (vmag u * vx v - vmag v * vx u) = 0) by lra.
      destruct (Rmult_integral _ _ Hz) as [H0 | H0]; [ lra | ].
      apply Rmult_eq_reg_l with (vmag u * vmag v); [ | nra ].
      replace (vmag u * vmag v * (/ vmag u * vx u))
        with (vmag v * vx u) by (field; lra).
      replace (vmag u * vmag v * (/ vmag v * vx v))
        with (vmag u * vx v) by (field; lra).
      lra.
    + assert (Hz : vmag u * (vmag u * vy v - vmag v * vy u) = 0) by lra.
      destruct (Rmult_integral _ _ Hz) as [H0 | H0]; [ lra | ].
      apply Rmult_eq_reg_l with (vmag u * vmag v); [ | nra ].
      replace (vmag u * vmag v * (/ vmag u * vy u))
        with (vmag v * vy u) by (field; lra).
      replace (vmag u * vmag v * (/ vmag v * vy v))
        with (vmag u * vy v) by (field; lra).
      lra.
Qed.

(* The unit vector of the negation is the negated unit vector. *)
Lemma unit_vneg : forall u : Vec,
  u <> vzero ->
  vscale (/ vmag (vneg u)) (vneg u) = vneg (vscale (/ vmag u) u).
Proof.
  intros u Hu.
  assert (Hm : vmag (vneg u) = vmag u).
  { unfold vmag. f_equal. unfold vmag_sq, vdot, vneg. cbn [vx vy]. ring. }
  rewrite Hm.
  apply Vec_eq; unfold vscale, vneg; cbn [vx vy]; ring.
Qed.

Lemma vneg_nonzero : forall u : Vec, u <> vzero -> vneg u <> vzero.
Proof.
  intros u Hu Hz. apply Hu.
  assert (Hx : vx (vneg u) = vx vzero) by (rewrite Hz; reflexivity).
  assert (Hy : vy (vneg u) = vy vzero) by (rewrite Hz; reflexivity).
  unfold vneg, vzero in Hx, Hy. cbn [vx vy] in Hx, Hy.
  apply Vec_eq; unfold vzero; cbn [vx vy]; lra.
Qed.

Theorem unit_opp_iff_cross_dot : forall u v : Vec,
  u <> vzero -> v <> vzero ->
  (vscale (/ vmag v) v = vneg (vscale (/ vmag u) u) <->
   vcross u v = 0 /\ vdot u v < 0).
Proof.
  intros u v Hu Hv.
  pose proof (unit_eq_iff_cross_dot (vneg u) v (vneg_nonzero u Hu) Hv)
    as Hiff.
  rewrite (unit_vneg u Hu) in Hiff.
  split.
  - intros H.
    assert (Hcd : vcross (vneg u) v = 0 /\ 0 < vdot (vneg u) v)
      by (apply Hiff; symmetry; exact H).
    destruct Hcd as [Hc Hd].
    unfold vcross, vdot, vneg in Hc, Hd. cbn [vx vy] in Hc, Hd.
    unfold vcross, vdot. split; lra.
  - intros [Hc Hd].
    symmetry. apply Hiff.
    unfold vcross, vdot in Hc, Hd.
    unfold vcross, vdot, vneg. cbn [vx vy].
    split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The raw (rational) normals, and their normalisation bridges.           *)
(* -------------------------------------------------------------------------- *)

(* The UN-normalised offset normal: rational in the control points (for      *)
(* arcs because arc_center is the rational circumcenter formula).            *)
Definition segment_raw_norm_end (s : CurveSegment) : Vec :=
  match s with
  | CSChord p q => vperp (seg_vec p q)
  | CSArc a => mkVec (px (arc_end a) - px (arc_center a))
                     (py (arc_end a) - py (arc_center a))
  end.

Definition segment_raw_norm_start (s : CurveSegment) : Vec :=
  match s with
  | CSChord p q => vperp (seg_vec p q)
  | CSArc a => mkVec (px (arc_start a) - px (arc_center a))
                     (py (arc_start a) - py (arc_center a))
  end.

(* Shared arc case: the radial raw normal is nonzero with vmag = r, and      *)
(* normalises to the radial unit normal.                                      *)
Lemma arc_raw_norm_bridge : forall (C P : Point) (r : R),
  0 < r -> dist C P = r ->
  let raw := mkVec (px P - px C) (py P - py C) in
  raw <> vzero /\ vmag raw = r /\
  mkVec ((px P - px C) / r) ((py P - py C) / r) =
  vscale (/ vmag raw) raw.
Proof.
  intros C P r Hr HP raw.
  assert (Hsq : vmag_sq raw = r * r).
  { unfold raw, vmag_sq, vdot. cbn [vx vy].
    pose proof (dist_sq_of_dist C P r HP) as Hd.
    unfold dist_sq in Hd. nra. }
  assert (Hm : vmag raw = r).
  { unfold vmag. rewrite Hsq.
    replace (r * r) with (Rsqr r) by (unfold Rsqr; ring).
    apply sqrt_Rsqr. lra. }
  assert (Hnz : raw <> vzero).
  { intros Hz. rewrite Hz in Hm.
    unfold vmag, vmag_sq, vdot, vzero in Hm. cbn [vx vy] in Hm.
    replace (0 * 0 + 0 * 0) with 0 in Hm by ring.
    rewrite sqrt_0 in Hm. lra. }
  split; [ exact Hnz | split; [ exact Hm | ] ].
  rewrite Hm.
  apply Vec_eq; unfold vscale, raw; cbn [vx vy]; field; lra.
Qed.

Lemma segment_norm_end_normalises : forall s,
  segment_arc_valid s -> segment_nondeg s ->
  segment_raw_norm_end s <> vzero /\
  segment_norm_end s =
  vscale (/ vmag (segment_raw_norm_end s)) (segment_raw_norm_end s).
Proof.
  intros [p q | a] Hv Hn.
  - (* chord: unit_perp IS the normalised vperp *)
    cbn [segment_raw_norm_end segment_norm_end].
    assert (Hnz : vperp (seg_vec p q) <> vzero).
    { intros Hz.
      apply (seg_vec_nonzero p q Hn).
      assert (Hx : vx (vperp (seg_vec p q)) = 0) by (rewrite Hz; reflexivity).
      assert (Hy : vy (vperp (seg_vec p q)) = 0) by (rewrite Hz; reflexivity).
      unfold vperp in Hx, Hy. cbn [vx vy] in Hx, Hy.
      apply Vec_eq; unfold vzero; cbn [vx vy]; lra. }
    split; [ exact Hnz | ].
    unfold unit_perp.
    (* vmag (vperp w) = vmag w *)
    assert (Hm : vmag (vperp (seg_vec p q)) = vmag (seg_vec p q)).
    { unfold vmag. f_equal. apply vmag_sq_vperp. }
    rewrite Hm. reflexivity.
  - (* arc: the radial bridge with r = arc_radius *)
    pose proof (arc_radius_pos a Hv) as Hr.
    destruct (arc_raw_norm_bridge (arc_center a) (arc_end a) (arc_radius a)
                Hr (arc_center_dist_end a Hv)) as [Hnz [Hm Hbr]].
    cbn [segment_raw_norm_end segment_norm_end].
    split; [ exact Hnz | exact Hbr ].
Qed.

Lemma segment_norm_start_normalises : forall s,
  segment_arc_valid s -> segment_nondeg s ->
  segment_raw_norm_start s <> vzero /\
  segment_norm_start s =
  vscale (/ vmag (segment_raw_norm_start s)) (segment_raw_norm_start s).
Proof.
  intros [p q | a] Hv Hn.
  - (* chords have one constant normal: definitionally the end case *)
    exact (segment_norm_end_normalises (CSChord p q) Hv Hn).
  - pose proof (arc_radius_pos a Hv) as Hr.
    destruct (arc_raw_norm_bridge (arc_center a) (arc_start a) (arc_radius a)
                Hr (arc_center_dist_start a)) as [Hnz [Hm Hbr]].
    cbn [segment_raw_norm_start segment_norm_start].
    split; [ exact Hnz | exact Hbr ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  HEADLINES: the assembly oracles are two rational sign tests.           *)
(* -------------------------------------------------------------------------- *)

Theorem g1_decision_correct : forall s1 s2,
  segment_arc_valid s1 -> segment_nondeg s1 ->
  segment_arc_valid s2 -> segment_nondeg s2 ->
  (segment_norm_end s1 = segment_norm_start s2 <->
   vcross (segment_raw_norm_end s1) (segment_raw_norm_start s2) = 0 /\
   0 < vdot (segment_raw_norm_end s1) (segment_raw_norm_start s2)).
Proof.
  intros s1 s2 Hv1 Hn1 Hv2 Hn2.
  destruct (segment_norm_end_normalises s1 Hv1 Hn1) as [Hnz1 Hb1].
  destruct (segment_norm_start_normalises s2 Hv2 Hn2) as [Hnz2 Hb2].
  rewrite Hb1, Hb2.
  apply unit_eq_iff_cross_dot; assumption.
Qed.

Theorem uturn_decision_correct : forall s1 s2,
  segment_arc_valid s1 -> segment_nondeg s1 ->
  segment_arc_valid s2 -> segment_nondeg s2 ->
  (segment_norm_start s2 = vneg (segment_norm_end s1) <->
   vcross (segment_raw_norm_end s1) (segment_raw_norm_start s2) = 0 /\
   vdot (segment_raw_norm_end s1) (segment_raw_norm_start s2) < 0).
Proof.
  intros s1 s2 Hv1 Hn1 Hv2 Hn2.
  destruct (segment_norm_end_normalises s1 Hv1 Hn1) as [Hnz1 Hb1].
  destruct (segment_norm_start_normalises s2 Hv2 Hn2) as [Hnz2 Hb2].
  rewrite Hb1, Hb2.
  apply unit_opp_iff_cross_dot; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  The per-arc safety bound is decidable from the rational r^2.           *)
(* -------------------------------------------------------------------------- *)

Lemma offset_safe_iff_sq : forall r d : R,
  0 < r ->
  (- r < d <-> 0 <= d \/ d * d < r * r).
Proof.
  intros r d Hr. split; intros H.
  - destruct (Rle_or_lt 0 d) as [Hd | Hd]; [ left; exact Hd | right; nra ].
  - destruct H as [Hd | Hd]; nra.
Qed.

(* ========================================================================== *)
(* Axiom audit.  ALL headlines below are 3-axiom (classical-reals trio:      *)
(* sig_not_dec, sig_forall_dec, functional_extensionality_dep).              *)
(* ========================================================================== *)

Print Assumptions unit_eq_iff_cross_dot.
Print Assumptions unit_opp_iff_cross_dot.
Print Assumptions g1_decision_correct.
Print Assumptions uturn_decision_correct.
Print Assumptions offset_safe_iff_sq.
