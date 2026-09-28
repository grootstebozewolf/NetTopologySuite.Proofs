(* ============================================================================
   NetTopologySuite.Proofs.ZetaHostHit
   ----------------------------------------------------------------------------
   #770 decision experiment, step 3: P, then the fixtures.

   P  (host_circ_chord_hit_ok).  A ζ that the C1 kernel accepts as a
   segment hit carries the host check: on_circ at t_of_zeta ζ and
   on_chord at tj_of ζ, at the chart point.  Stated over zeta_seg_hit
   (root, chart window, 0 ≤ tj ≤ 1) because classify_zeta (C1.9) is not
   proved.  Under carry-and-check that pair is what I_ok checks; this
   does not change host I_ok, which still declines the mixed pair.

   P uses only C1 (ChartLineQuadratic) and C2 (ZetaEggBridge) lemmas:
   no cos/sin/atan3/atan2/PI lemma and no case split on the sign of Δθ,
   on θ₀ versus π, or on a quadrant.  Its one range hypothesis is
   |Δθ| < 2π, which keeps both arc ends off the pole (F5 is outside it).

   zeta_mid_in_window is generic, not a fixture lemma: the egg's own mid
   (ζ = 0) is always inside the chart window.

   Fixtures F1 (locked quarter), F2 (straddles θ = π), F3 (clockwise major
   arc, Δθ = −3π/2) and F4 (endpoint hit, t = 0, tj = 0): each is P applied
   once.  After apply P they use only the #770 whitelist: PI_RGT_0, sqrt
   arithmetic, cos/sin of the egg's own angles, cos_neg/sin_neg.

   Oracle lane. Not an egg reparameterisation. Does not remint CircGamma,
   leftover Ⅹ, LoopDischarged, I_ok_mixed as host, or MkNurbs.
   No Admitted. No Axiom. No Parameter.
   ========================================================================== *)

From Stdlib Require Import Reals Lra RNsatz.
From NTS.Proofs Require Import
  Distance SheetHenCircEgg SheetHenCookCore CircleChart ChartLineQuadratic
  ZetaEggBridge.
Local Open Scope R_scope.

Section EggChord.
Variables (c : CircularEgg) (s : ChordEgg).

Let O := circ_o c.
Let Q := egg_pole c.
Let S0 := ce_p0 s.
Let dx := px (ce_p1 s) - px (ce_p0 s).
Let dy := py (ce_p1 s) - py (ce_p0 s).

Definition egg_qf (z : R) : R :=
  zeta_qf (px O) (py O) (px Q) (py Q) (px S0) (py S0) dx dy z.
Definition egg_tj (z : R) : R :=
  tj_of (px O) (py O) (px Q) (py Q) (px S0) (py S0) dx dy z.
Definition egg_zA : R := zeta_of_pt O Q (circ_start c).
Definition egg_zB : R := zeta_of_pt O Q (circ_end c).

Definition zeta_seg_hit (z : R) : Prop :=
  egg_qf z = 0 /\ in_zeta_interval egg_zA egg_zB z /\ 0 <= egg_tj z <= 1.

Hypothesis Hr : circ_r c <> 0.
Hypothesis Hs : circ_sweep c <> 0.
Hypothesis Hsw : -(2 * PI) < circ_sweep c < 2 * PI.

Lemma egg_ends_t : t_of_zeta c egg_zA = 0 /\ t_of_zeta c egg_zB = 1.
Proof.
  unfold egg_zA, egg_zB, circ_start, circ_end, O, Q. split.
  - apply t_of_zeta_of_circ_eval; [exact Hr | exact Hs | lra].
  - apply t_of_zeta_of_circ_eval; [exact Hr | exact Hs | lra].
Qed.

Lemma zeta_in_window_iff : forall z,
  in_zeta_interval egg_zA egg_zB z <-> 0 <= t_of_zeta c z <= 1.
Proof.
  intro z. unfold in_zeta_interval.
  rewrite (t_of_zeta_window c z egg_zA egg_zB Hs).
  destruct egg_ends_t as [HA HB]. rewrite HA, HB.
  split; intro H; [split; nra | nra].
Qed.

Lemma zeta_mid_in_window : in_zeta_interval egg_zA egg_zB 0.
Proof.
  apply zeta_in_window_iff. rewrite t_of_zeta_mid. lra.
Qed.

Theorem host_circ_chord_hit_ok : forall z,
  (dx, dy) <> (0, 0) ->
  zeta_seg_hit z ->
  on_circ c (t_of_zeta c z) (zeta_pt O Q z) /\
  on_chord s (egg_tj z) (zeta_pt O Q z).
Proof.
  intros z Hd [Hf [Hw Htj]].
  split.
  - split; [apply zeta_in_window_iff; exact Hw |].
    symmetry. unfold O, Q. apply circ_eval_t_of_zeta. exact Hs.
  - split; [exact Htj |].
    destruct (on_line_param (px O) (py O) (px Q) (py Q) (px S0) (py S0)
                dx dy z Hd Hf) as [Ex Ey].
    unfold zeta_abs_x, zeta_abs_y in Ex, Ey.
    unfold zeta_pt, chord_eval. fold (egg_tj z) in Ex, Ey.
    f_equal.
    + rewrite Ex. unfold S0, dx. ring.
    + rewrite Ey. unfold S0, dy. ring.
Qed.

(* F5's P.  Full span, |Δθ| = 2π: both arc ends are the pole, the C1 window
   {ζ(A), ζ(B)} collapses, and every finite ζ is in span
   (t_of_zeta_full_span).  So this is P without the window conjunct and
   without |Δθ| < 2π.  It is a second statement beside P, not an instance
   of it.  A chord through the pole itself (ζ = ∞) is C1.4, not here. *)
Theorem host_circ_chord_hit_ok_full : forall z,
  Rabs (circ_sweep c) = 2 * PI ->
  (dx, dy) <> (0, 0) ->
  egg_qf z = 0 -> (0 <= egg_tj z <= 1) ->
  on_circ c (t_of_zeta c z) (zeta_pt O Q z) /\
  on_chord s (egg_tj z) (zeta_pt O Q z).
Proof using.
  clear Hr Hs Hsw.
  intros z Hfull Hd Hf Htj.
  assert (Hs0 : circ_sweep c <> 0).
  { intro E. rewrite E, Rabs_R0 in Hfull. pose proof PI_RGT_0. lra. }
  split.
  - split; [pose proof (t_of_zeta_full_span c z Hfull); lra |].
    symmetry. unfold O, Q. apply circ_eval_t_of_zeta. exact Hs0.
  - split; [exact Htj |].
    destruct (on_line_param (px O) (py O) (px Q) (py Q) (px S0) (py S0)
                dx dy z Hd Hf) as [Ex Ey].
    unfold zeta_abs_x, zeta_abs_y in Ex, Ey.
    unfold zeta_pt, chord_eval. fold (egg_tj z) in Ex, Ey.
    f_equal.
    + rewrite Ex. unfold S0, dx. ring.
    + rewrite Ey. unfold S0, dy. ring.
Qed.

End EggChord.

(* -------------------------------------------------------------------------- *)
(* Fixtures.  Each is P applied once; the obligations are the fixture's own    *)
(* data (its egg's cos/sin constants, √2), not transport.                      *)
(* -------------------------------------------------------------------------- *)

(* F1: locked quarter.  O = (0,0), r = 5, θ₀ = 0, Δθ = π/2, chord (5,5)→(0,0).
   Hit at the arc mid: ζ = 0, t = 1/2, tj = 1 − 1/√2. *)
Definition F1_egg : CircularEgg := mkCircularEgg (mkPoint 0 0) 5 0 (PI / 2).
Definition F1_chord : ChordEgg := mkChordEgg (mkPoint 5 5) (mkPoint 0 0).

Theorem F1_hit :
  on_circ F1_egg (t_of_zeta F1_egg 0) (zeta_pt (circ_o F1_egg) (egg_pole F1_egg) 0) /\
  on_chord F1_chord (egg_tj F1_egg F1_chord 0)
    (zeta_pt (circ_o F1_egg) (egg_pole F1_egg) 0).
Proof.
  pose proof PI_RGT_0 as HPI.
  assert (Hq : 0 < sqrt 2) by (apply sqrt_lt_R0; lra).
  assert (H2 : sqrt 2 * sqrt 2 = 2) by (apply sqrt_sqrt; lra).
  assert (Hm : egg_mid_angle F1_egg = PI / 4)
    by (unfold egg_mid_angle, F1_egg; simpl; field).
  apply host_circ_chord_hit_ok; try (unfold F1_egg; simpl; lra).
  - unfold F1_chord. simpl. intro H. injection H. lra.
  - split; [| split].
    + unfold egg_qf, zeta_qf, zeta_qa, zeta_qb, zeta_qc, crs, dot, egg_pole.
      rewrite Hm, cos_PI4, sin_PI4. unfold F1_egg, F1_chord. simpl. ring.
    + apply zeta_mid_in_window; unfold F1_egg; simpl; lra.
    + assert (E : egg_tj F1_egg F1_chord 0 = 1 - 1 / sqrt 2).
      { unfold egg_tj, tj_of, zeta_abs_x, zeta_abs_y, zeta_ptx, zeta_pty,
          dot, egg_pole.
        rewrite Hm, cos_PI4, sin_PI4. unfold F1_egg, F1_chord. simpl.
        field. lra. }
      rewrite E. set (k := 1 / sqrt 2).
      assert (Hk : k * sqrt 2 = 1) by (unfold k; field; lra).
      assert (0 < k) by (unfold k; apply Rdiv_lt_0_compat; lra).
      split; nra.
Qed.

(* F2: straddles the cut at θ = π.  O = (0,0), r = 5, θ₀ = π/2, Δθ = π, so the
   arc is θ ∈ [π/2, 3π/2] and its pole is at θ = 0.  Chord (0,0)→(−5,5) hits
   at θ = 3π/4, not the mid: ζ = 1 − √2, tj = 1/√2. *)
Definition F2_egg : CircularEgg := mkCircularEgg (mkPoint 0 0) 5 (PI / 2) PI.
Definition F2_chord : ChordEgg := mkChordEgg (mkPoint 0 0) (mkPoint (-5) 5).
Definition F2_z : R := 1 - sqrt 2.

Theorem F2_hit :
  on_circ F2_egg (t_of_zeta F2_egg F2_z)
    (zeta_pt (circ_o F2_egg) (egg_pole F2_egg) F2_z) /\
  on_chord F2_chord (egg_tj F2_egg F2_chord F2_z)
    (zeta_pt (circ_o F2_egg) (egg_pole F2_egg) F2_z).
Proof.
  pose proof PI_RGT_0 as HPI.
  assert (Hq : 0 < sqrt 2) by (apply sqrt_lt_R0; lra).
  assert (H2 : sqrt 2 * sqrt 2 = 2) by (apply sqrt_sqrt; lra).
  assert (Hq1 : 1 < sqrt 2) by nra.
  assert (Hm : egg_mid_angle F2_egg = PI)
    by (unfold egg_mid_angle, F2_egg; simpl; field).
  apply host_circ_chord_hit_ok; try (unfold F2_egg; simpl; lra).
  - unfold F2_chord. simpl. intro H. injection H. lra.
  - split; [| split].
    + unfold egg_qf, zeta_qf, zeta_qa, zeta_qb, zeta_qc, crs, dot, egg_pole.
      rewrite Hm, cos_PI, sin_PI. unfold F2_egg, F2_chord, F2_z. simpl.
      set (q := sqrt 2) in *. nsatz.
    + assert (EA : egg_zA F2_egg = -1).
      { unfold egg_zA, zeta_of_pt, zeta_of, crs, dot, egg_pole, circ_start,
          circ_eval.
        rewrite Hm, cos_PI, sin_PI. unfold F2_egg. simpl.
        replace (PI / 2 + 0 * PI) with (PI / 2) by ring.
        rewrite cos_PI2, sin_PI2. field. }
      assert (EB : egg_zB F2_egg = 1).
      { unfold egg_zB, zeta_of_pt, zeta_of, crs, dot, egg_pole, circ_end,
          circ_eval.
        rewrite Hm, cos_PI, sin_PI. unfold F2_egg. simpl.
        replace (PI / 2 + 1 * PI) with (3 * (PI / 2)) by field.
        rewrite cos_3PI2, sin_3PI2. field. }
      unfold in_zeta_interval. rewrite EA, EB. unfold F2_z. nra.
    + assert (E : egg_tj F2_egg F2_chord F2_z = 1 / sqrt 2).
      { unfold egg_tj, tj_of, zeta_abs_x, zeta_abs_y, zeta_ptx, zeta_pty,
          dot, egg_pole.
        rewrite Hm, cos_PI, sin_PI. unfold F2_egg, F2_chord, F2_z. simpl.
        set (q := sqrt 2) in *.
        assert (Hd : 1 + (1 - q) * (1 - q) <> 0) by nra.
        field_simplify_eq; [| split; lra].
        replace (q ^ 3) with (q * (q * q)) by ring.
        replace (q ^ 2) with (q * q) by ring.
        rewrite H2. ring. }
      rewrite E. set (k := 1 / sqrt 2).
      assert (Hk : k * sqrt 2 = 1) by (unfold k; field; lra).
      assert (0 < k) by (unfold k; apply Rdiv_lt_0_compat; lra).
      split; nra.
Qed.

(* F3: CW major arc.  O = (0,0), r = 5, θ₀ = π, Δθ = −3π/2, so the arc runs
   clockwise from θ = π through θ = 0 to θ = −π/2; its mid is π/4.  Chord
   (0,0)→(10,0) hits at (5,0): θ = 0, t = 2/3, ζ = 1 − √2, tj = 1/2. *)
Definition F3_egg : CircularEgg :=
  mkCircularEgg (mkPoint 0 0) 5 PI (- (3 * (PI / 2))).
Definition F3_chord : ChordEgg := mkChordEgg (mkPoint 0 0) (mkPoint 10 0).
Definition F3_z : R := 1 - sqrt 2.

Theorem F3_hit :
  on_circ F3_egg (t_of_zeta F3_egg F3_z)
    (zeta_pt (circ_o F3_egg) (egg_pole F3_egg) F3_z) /\
  on_chord F3_chord (egg_tj F3_egg F3_chord F3_z)
    (zeta_pt (circ_o F3_egg) (egg_pole F3_egg) F3_z).
Proof.
  pose proof PI_RGT_0 as HPI.
  assert (Hq : 0 < sqrt 2) by (apply sqrt_lt_R0; lra).
  assert (H2 : sqrt 2 * sqrt 2 = 2) by (apply sqrt_sqrt; lra).
  assert (Hq1 : 1 < sqrt 2) by nra.
  assert (Hm : egg_mid_angle F3_egg = PI / 4)
    by (unfold egg_mid_angle, F3_egg; simpl; field).
  apply host_circ_chord_hit_ok; try (unfold F3_egg; simpl; lra).
  - unfold F3_chord. simpl. intro H. injection H. lra.
  - split; [| split].
    + unfold egg_qf, zeta_qf, zeta_qa, zeta_qb, zeta_qc, crs, dot, egg_pole.
      rewrite Hm, cos_PI4, sin_PI4. unfold F3_egg, F3_chord, F3_z. simpl.
      set (q := sqrt 2) in *.
      field_simplify_eq; [| lra]. cbn [pow]. nsatz.
    + assert (EA : egg_zA F3_egg = 1 + sqrt 2).
      { unfold egg_zA, zeta_of_pt, zeta_of, crs, dot, egg_pole, circ_start,
          circ_eval.
        rewrite Hm, cos_PI4, sin_PI4. unfold F3_egg. simpl.
        replace (PI + 0 * - (3 * (PI / 2))) with PI by ring.
        rewrite cos_PI, sin_PI.
        set (q := sqrt 2) in *.
        field_simplify_eq; [cbn [pow]; nsatz | repeat split; nra ..]. }
      assert (EB : egg_zB F3_egg = - (1 + sqrt 2)).
      { unfold egg_zB, zeta_of_pt, zeta_of, crs, dot, egg_pole, circ_end,
          circ_eval.
        rewrite Hm, cos_PI4, sin_PI4. unfold F3_egg. simpl.
        replace (PI + 1 * - (3 * (PI / 2))) with (- (PI / 2)) by field.
        rewrite cos_neg, sin_neg, cos_PI2, sin_PI2.
        set (q := sqrt 2) in *.
        field_simplify_eq; [cbn [pow]; nsatz | repeat split; nra ..]. }
      unfold in_zeta_interval. rewrite EA, EB. unfold F3_z. nra.
    + assert (E : egg_tj F3_egg F3_chord F3_z = / 2).
      { unfold egg_tj, tj_of, zeta_abs_x, zeta_abs_y, zeta_ptx, zeta_pty,
          dot, egg_pole.
        rewrite Hm, cos_PI4, sin_PI4. unfold F3_egg, F3_chord, F3_z. simpl.
        set (q := sqrt 2) in *.
        assert (Hd : 1 + (1 - q) * (1 - q) <> 0) by nra.
        field_simplify_eq; [cbn [pow]; nsatz | repeat split; nra ..]. }
      rewrite E. lra.
Qed.

(* F4: endpoint hit.  F1's egg (θ₀ = 0, Δθ = π/2), chord (5,0)→(10,0).  The
   hit is the arc start and the chord start: ζ = egg_zA = 1 − √2, t = 0,
   tj = 0.  zeta_seg_hit is closed at both ends; this checks the convention. *)
Definition F4_chord : ChordEgg := mkChordEgg (mkPoint 5 0) (mkPoint 10 0).
Definition F4_z : R := egg_zA F1_egg.

Theorem F4_endpoint :
  t_of_zeta F1_egg F4_z = 0 /\ egg_tj F1_egg F4_chord F4_z = 0 /\
  on_circ F1_egg (t_of_zeta F1_egg F4_z)
    (zeta_pt (circ_o F1_egg) (egg_pole F1_egg) F4_z) /\
  on_chord F4_chord (egg_tj F1_egg F4_chord F4_z)
    (zeta_pt (circ_o F1_egg) (egg_pole F1_egg) F4_z).
Proof.
  pose proof PI_RGT_0 as HPI.
  assert (Hq : 0 < sqrt 2) by (apply sqrt_lt_R0; lra).
  assert (H2 : sqrt 2 * sqrt 2 = 2) by (apply sqrt_sqrt; lra).
  assert (Hq1 : 1 < sqrt 2) by nra.
  assert (Hm : egg_mid_angle F1_egg = PI / 4)
    by (unfold egg_mid_angle, F1_egg; simpl; field).
  assert (Hr : circ_r F1_egg <> 0) by (unfold F1_egg; simpl; lra).
  assert (Hs : circ_sweep F1_egg <> 0) by (unfold F1_egg; simpl; lra).
  assert (Hsw : -(2 * PI) < circ_sweep F1_egg < 2 * PI)
    by (unfold F1_egg; simpl; lra).
  assert (EA : F4_z = 1 - sqrt 2).
  { unfold F4_z, egg_zA, zeta_of_pt, zeta_of, crs, dot, egg_pole, circ_start,
      circ_eval.
    rewrite Hm, cos_PI4, sin_PI4. unfold F1_egg. simpl.
    replace (0 + 0 * (PI / 2)) with 0 by ring.
    rewrite cos_0, sin_0.
    set (q := sqrt 2) in *.
    field_simplify_eq; [cbn [pow]; nsatz | repeat split; nra ..]. }
  assert (Htj : egg_tj F1_egg F4_chord F4_z = 0).
  { rewrite EA.
    unfold egg_tj, tj_of, zeta_abs_x, zeta_abs_y, zeta_ptx, zeta_pty,
      dot, egg_pole.
    rewrite Hm, cos_PI4, sin_PI4. unfold F1_egg, F4_chord. simpl.
    set (q := sqrt 2) in *.
    assert (Hd : 1 + (1 - q) * (1 - q) <> 0) by nra.
    field_simplify_eq; [cbn [pow]; nsatz | repeat split; nra ..]. }
  split; [exact (proj1 (egg_ends_t F1_egg Hr Hs Hsw)) |].
  split; [exact Htj |].
  apply host_circ_chord_hit_ok; try assumption.
  - unfold F4_chord. simpl. intro H. injection H. lra.
  - split; [| split].
    + rewrite EA.
      unfold egg_qf, zeta_qf, zeta_qa, zeta_qb, zeta_qc, crs, dot, egg_pole.
      rewrite Hm, cos_PI4, sin_PI4. unfold F1_egg, F4_chord. simpl.
      set (q := sqrt 2) in *.
      field_simplify_eq; [cbn [pow]; nsatz | repeat split; nra ..].
    + unfold in_zeta_interval, F4_z. rewrite Rminus_diag_eq by reflexivity.
      lra.
    + rewrite Htj. lra.
Qed.

(* F5: full span, the #872 source case CIRCULARSTRING(1 0, -1 0, 1 0).
   O = (0,0), r = 1, θ₀ = 0, Δθ = 2π; mid π, so the pole is (1, 0), the
   repeated endpoint.  Chord (0,0)→(0,−2) hits (0,−1) at θ = 3π/2, in the
   second half that CircularArc.Flatten drops: ζ = 1, tj = 1/2
   (t = 3/4 is side-ledger: it needs atan3 1).  P does not apply
   (|Δθ| < 2π fails, and the window collapses to ζ(A) = ζ(B)), so this is
   host_circ_chord_hit_ok_full applied once. *)
Definition F5_egg : CircularEgg := mkCircularEgg (mkPoint 0 0) 1 0 (2 * PI).
Definition F5_chord : ChordEgg := mkChordEgg (mkPoint 0 0) (mkPoint 0 (-2)).

Theorem F5_hit :
  on_circ F5_egg (t_of_zeta F5_egg 1) (zeta_pt (circ_o F5_egg) (egg_pole F5_egg) 1) /\
  on_chord F5_chord (egg_tj F5_egg F5_chord 1)
    (zeta_pt (circ_o F5_egg) (egg_pole F5_egg) 1).
Proof.
  pose proof PI_RGT_0 as HPI.
  assert (Hm : egg_mid_angle F5_egg = PI)
    by (unfold egg_mid_angle, F5_egg; simpl; field).
  apply host_circ_chord_hit_ok_full.
  - unfold F5_egg. simpl. apply Rabs_right. lra.
  - unfold F5_chord. simpl. intro H. injection H. lra.
  - unfold egg_qf, zeta_qf, zeta_qa, zeta_qb, zeta_qc, crs, dot, egg_pole.
    rewrite Hm, cos_PI, sin_PI. unfold F5_egg, F5_chord. simpl. ring.
  - assert (E : egg_tj F5_egg F5_chord 1 = / 2).
    { unfold egg_tj, tj_of, zeta_abs_x, zeta_abs_y, zeta_ptx, zeta_pty,
        dot, egg_pole.
      rewrite Hm, cos_PI, sin_PI. unfold F5_egg, F5_chord. simpl. field. }
    rewrite E. lra.
Qed.

Print Assumptions zeta_mid_in_window.
Print Assumptions host_circ_chord_hit_ok.
Print Assumptions F1_hit.
Print Assumptions F2_hit.
Print Assumptions F3_hit.
Print Assumptions F4_endpoint.
Print Assumptions host_circ_chord_hit_ok_full.
Print Assumptions F5_hit.
