(* ============================================================================
   Probe: does `arc_overlay_correct_chord_approx` factor through DirectedApprox?
   Answer (docs/directed-approximation-2026-11.md): only through the GAP half.
   The theorem is `gap_within` of the chord-op result w.r.t. the arc-curve set;
   no over/under inclusion is stated or provable from it.
   ========================================================================== *)
From Stdlib Require Import Reals List.
From NTS.Proofs Require Import DirectedApprox Distance Overlay CurveGeometry
  ArcIntersect ArcChordApprox ArcOrient ArcHotPixel ArcDistance ArcOverlay.
Import ListNotations.
Open Scope R_scope.

Definition cheb (p q : Point) : R := Rmax (Rabs (px p - px q)) (Rabs (py p - py q)).

Definition arc_curve_pt (A B : CurveGeometry) (X : Point) : Prop :=
  exists a, In a (arcs_of A ++ arcs_of B) /\
    inCircle_R (arc_start a) (arc_mid a) (arc_end a) X = 0 /\
    arc_span_contains a X.

Lemma arc_close_iff_gap :
  forall q A B eps,
    arc_close_to_curves q A B eps <->
    exists y, arc_curve_pt A B y /\ cheb q y <= eps.
Proof.
  intros q A B eps. unfold arc_close_to_curves, arc_curve_pt, cheb. split.
  - intros (a & X & Ha & Hc & Hs & Hx & Hy). exists X. split.
    + exists a. repeat split; assumption.
    + apply Rmax_lub; assumption.
  - intros (X & (a & Ha & Hc & Hs) & H). exists a, X. repeat split; try assumption.
    + eapply Rle_trans; [apply Rmax_l | exact H].
    + eapply Rle_trans; [apply Rmax_r | exact H].
Qed.

(* The chord-polygon hypotheses H_A / H_B are exactly `gap_within`. *)
Definition chord_gap (A B : CurveGeometry) (G : CurveGeometry) (n : nat) :=
  gap_within cheb (max_sagitta A B) (fun _ => True)
             (arc_curve_pt A B) (point_set (to_geometry G n)).

Theorem arc_overlay_via_directed :
  forall (A B : CurveGeometry) (op : BooleanOp) (n : nat),
    chord_gap A B A n -> chord_gap A B B n ->
    gap_within cheb (max_sagitta A B) (fun _ => True) (arc_curve_pt A B)
      (boolean_op op (to_geometry A n) (to_geometry B n)).
Proof.
  intros A B op n HA HB.
  apply (gap_mono_comp _ _ _ _ (fun x => point_set (to_geometry A n) x \/
                                          point_set (to_geometry B n) x)).
  - intros x _ H. destruct op; cbn in H.
    + exact H.
    + left. exact (proj1 H).
    + left. exact (proj1 H).
    + destruct H as [[h _]|[h _]]; [left|right]; exact h.
  - apply gap_or; assumption.
Qed.
