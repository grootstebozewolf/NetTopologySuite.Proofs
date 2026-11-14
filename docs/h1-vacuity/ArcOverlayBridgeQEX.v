(* ============================================================================
   docs/h1-vacuity/ArcOverlayBridgeQEX.v  --  hunt probe (QEX), not a product module
   ----------------------------------------------------------------------------
   `arc_overlay_correct_chord_approx` (theories/ArcOverlay.v) takes

     H_A_bridge : forall q, point_set (to_geometry A n) q ->
                    arc_close_to_curves q A B (max_sagitta A B)

   (and H_B_bridge, symmetric).  `arc_close_to_curves` is closeness to an
   arc CURVE, a 1-D set; `point_set` is a 2-D polygon interior.  So the
   bridge asks every interior point of the chord polygon to lie within one
   sagitta of an arc.  The source's §3 comment says this fails for polygons
   wider than the sagitta.  This file makes that a Qed counterexample.

   Witness.  A = B = one valid curve polygon: the square [0,10]^2 whose
   bottom-left corner is the radius-1 arc (0,0) -> (1,-1) -> (2,0) (centre
   (1,0)), closed by four chords.  Its sagitta is at most 1.  The point
   (5,5) is inside the chord polygon (ray parity: one crossing, at x = 10),
   but every arc point has |y| <= 1, so it is 4 away in y.

   Results:
     arc_bridge_witness_valid   A is a valid_curve_geometry.
     H_A_bridge_refuted         the bridge is false for A, B := A, any n.
     arc_overlay_conclusion_refuted
                                the headline's CONCLUSION is false here (Union,
                                Intersection of A with itself): no proof of the bridges can exist
                                in general, so the theorem needs a new
                                conclusion, not a discharge.

   SUMMARY: bug — H_A_bridge of arc_overlay_correct_chord_approx is refuted (Qed).
   AI assistance disclosure: AI-drafted; human review pending.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay CurveGeometry ArcOrient
  ArcIntersect ArcHotPixel ArcChordApprox ArcDistance ArcOverlay.
Import ListNotations.
Local Open Scope R_scope.

Definition qa : CircularArc :=
  mkCircularArc (mkPoint 0 0) (mkPoint 1 (-1)) (mkPoint 2 0).

Definition qring : CurveRing :=
  [ CSArc qa;
    CSChord (mkPoint 2 0) (mkPoint 10 0);
    CSChord (mkPoint 10 0) (mkPoint 10 10);
    CSChord (mkPoint 10 10) (mkPoint 0 10);
    CSChord (mkPoint 0 10) (mkPoint 0 0) ].

Definition qgeom : CurveGeometry := [ mkCurvePolygon qring [] ].

Definition qpt : Point := mkPoint 5 5.

(* -------------------------------------------------------------------------- *)
(* §1  The witness is a valid curve geometry.                                 *)
(* -------------------------------------------------------------------------- *)

Theorem arc_bridge_witness_valid : valid_curve_geometry qgeom.
Proof.
  unfold valid_curve_geometry, qgeom. constructor; [| constructor].
  split; [| constructor].
  unfold valid_curve_ring. split; [| split].
  - unfold curve_ring_arcs_valid, qring.
    repeat constructor.
    unfold valid_arc, qa. cbn. lra.
  - unfold qring, qa. cbn. repeat split.
  - unfold curve_ring_closed, qring, qa. cbn. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  (5,5) is inside the chord polygon.                                     *)
(* -------------------------------------------------------------------------- *)

Ltac no_cross :=
  unfold edge_crosses_ray; cbn [px py fst snd];
  intros [[H1 H2] | [H1 H2]];
  [ try lra | try lra ];
  unfold Rdiv in H2;
  match type of H2 with
  | context [ (?u - ?u) * ?w ] =>
      replace ((u - u) * w) with 0 in H2 by ring; lra
  end.

Lemma qpt_in_chord_ring :
  point_in_ring qpt (chord_approx_ring qring 0).
Proof.
  unfold point_in_ring, qpt, qring, qa.
  cbn [chord_approx_ring flat_map chord_approx_segment chord_approx_arc
       arc_start arc_mid arc_end app ring_edges].
  apply rpo_skip; [ no_cross |].   (* (0,0)   -> (1,-1)  *)
  apply rpo_skip; [ no_cross |].   (* (1,-1)  -> (2,0)   *)
  apply rpo_skip; [ no_cross |].   (* (2,0)   -> (2,0)   *)
  apply rpo_skip; [ no_cross |].   (* (2,0)   -> (10,0)  *)
  apply rpo_skip; [ no_cross |].   (* (10,0)  -> (10,0)  *)
  apply rpo_cross.                 (* (10,0)  -> (10,10) *)
  { unfold edge_crosses_ray. cbn [px py fst snd]. left. split; [lra|].
    replace (10 + (10 - 10) * (5 - 0) / (10 - 0)) with 10
      by (unfold Rdiv; ring).
    lra. }
  apply rpe_skip; [ no_cross |].   (* (10,10) -> (10,10) *)
  apply rpe_skip; [ no_cross |].   (* (10,10) -> (0,10)  *)
  apply rpe_skip; [ no_cross |].   (* (0,10)  -> (0,10)  *)
  apply rpe_skip; [ no_cross |].   (* (0,10)  -> (0,0)   *)
  apply rpe_nil.
Qed.

Lemma qpt_in_point_set : forall n, point_set (to_geometry qgeom n) qpt.
Proof.
  intro n. exists (mkPolygon (chord_approx_ring qring n) []).
  split; [ left; reflexivity |].
  split.
  - exact qpt_in_chord_ring.
  - intros h [].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  (5,5) is more than one sagitta from every arc point.                   *)
(* -------------------------------------------------------------------------- *)

Lemma qa_radius_sq : arc_radius_sq qa = 1.
Proof.
  unfold arc_radius_sq, arc_center, qa, dist_sq. cbn. field.
Qed.

Lemma qa_sagitta_le_1 : sagitta qa <= 1.
Proof.
  pose proof (sagitta_le_radius_sqrt qa) as H.
  rewrite qa_radius_sq, sqrt_1 in H. exact H.
Qed.

Lemma max_sagitta_qgeom_le_1 : max_sagitta qgeom qgeom <= 1.
Proof.
  unfold max_sagitta, arcs_of, qgeom, arcs_of_polygon, arcs_of_ring, qring.
  cbn. pose proof qa_sagitta_le_1. pose proof (sagitta_nonneg qa).
  repeat (apply Rmax_lub; [| lra]). lra.
Qed.

(* A point on qa's circumcircle has |y| <= 1. *)
Lemma qa_circle_y_bound : forall X : Point,
  inCircle_R (arc_start qa) (arc_mid qa) (arc_end qa) X = 0 ->
  Rabs (py X) <= 1.
Proof.
  intros [x y] H. unfold inCircle_R, qa in H. cbn in H |- *.
  match type of H with ?E = 0 =>
    assert (Hid : E = -2 * ((x - 1) * (x - 1) + y * y - 1)) by ring end.
  assert (Hc : (x - 1) * (x - 1) + y * y = 1) by lra.
  assert (Hy2 : y * y <= 1).
  { pose proof (Rle_0_sqr (x - 1)) as Hs. unfold Rsqr in Hs. lra. }
  apply Rabs_le. split; nra.
Qed.

Lemma qpt_not_arc_close :
  ~ arc_close_to_curves qpt qgeom qgeom (max_sagitta qgeom qgeom).
Proof.
  intros (a & X & Hin & Hc & _ & _ & Hy).
  assert (Ha : a = qa).
  { unfold arcs_of, qgeom, arcs_of_polygon, arcs_of_ring, qring in Hin.
    cbn in Hin. destruct Hin as [<- | [<- | []]]; reflexivity. }
  subst a.
  pose proof (qa_circle_y_bound X Hc) as Hb.
  pose proof max_sagitta_qgeom_le_1 as Hs.
  unfold qpt in Hy. cbn [py] in Hy.
  pose proof (Rle_abs (5 - py X)). pose proof (Rle_abs (py X)). lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The bridge is false, and so is the headline's conclusion.              *)
(* -------------------------------------------------------------------------- *)

Theorem H_A_bridge_refuted : forall n : nat,
  ~ (forall q : Point,
       point_set (to_geometry qgeom n) q ->
       arc_close_to_curves q qgeom qgeom (max_sagitta qgeom qgeom)).
Proof.
  intros n H. exact (qpt_not_arc_close (H qpt (qpt_in_point_set n))).
Qed.

(* Union and Intersection of A with itself contain qpt, yet qpt is not
   arc-close: the conclusion `arc_close_to_curves p A B (max_sagitta A B)`
   fails on a valid input. *)
Theorem arc_overlay_conclusion_refuted :
  forall n : nat,
    valid_curve_geometry qgeom /\
    boolean_op Union (to_geometry qgeom n) (to_geometry qgeom n) qpt /\
    boolean_op Intersection (to_geometry qgeom n) (to_geometry qgeom n) qpt /\
    ~ arc_close_to_curves qpt qgeom qgeom (max_sagitta qgeom qgeom).
Proof.
  intro n. split; [exact arc_bridge_witness_valid|]. split; [| split].
  - cbn. left. exact (qpt_in_point_set n).
  - cbn. split; exact (qpt_in_point_set n).
  - exact qpt_not_arc_close.
Qed.

(* Bound to the headline: its H_A_bridge premise at this input is the
   proposition refuted above (a statement drift breaks this). *)
Theorem arc_overlay_headline_vacuous_here : forall (op : BooleanOp) (n : nat),
  ~ (valid_curve_geometry qgeom /\
     (forall q, point_set (to_geometry qgeom n) q ->
        arc_close_to_curves q qgeom qgeom (max_sagitta qgeom qgeom)) /\
     (forall q, point_set (to_geometry qgeom n) q ->
        arc_close_to_curves q qgeom qgeom (max_sagitta qgeom qgeom))).
Proof. intros op n (_ & HA & _). exact (H_A_bridge_refuted n HA). Qed.

Lemma arc_headline_consumes_H_A : forall (op : BooleanOp) (n : nat),
  (forall q, point_set (to_geometry qgeom n) q ->
     arc_close_to_curves q qgeom qgeom (max_sagitta qgeom qgeom)) ->
  (forall q, point_set (to_geometry qgeom n) q ->
     arc_close_to_curves q qgeom qgeom (max_sagitta qgeom qgeom)) ->
  boolean_op op (to_geometry qgeom n) (to_geometry qgeom n) qpt ->
  arc_close_to_curves qpt qgeom qgeom (max_sagitta qgeom qgeom).
Proof.
  intros op n HA HB.
  exact (arc_overlay_correct_chord_approx qgeom qgeom op qpt n
           arc_bridge_witness_valid arc_bridge_witness_valid HA HB).
Qed.

Print Assumptions H_A_bridge_refuted.
Print Assumptions arc_overlay_conclusion_refuted.
