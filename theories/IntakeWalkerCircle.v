(* ============================================================================
   NetTopologySuite.Proofs.IntakeWalkerCircle
   ----------------------------------------------------------------------------
   Bag half of ISO CIRCLE (claimId 0007-intake-angles, not reminted).
   Split out of IntakeWalker. The full-turn egg stays
   IntakeCircle.circle_full_param. The bag is two hens at distinct
   points: A and the antipode γ(1/2), two MkCirc of sweep ±π
   (θ₀ of A, then θ₀±π). A src=dst chicken is not used: piece_wf
   and bag_step do not state that ck_src = ck_dst is accepted.

   F5 intake half only. Each bag hen has |Δθ| = π, so the chart
   window |Δθ| < 2π (host_circ_chord_hit_ok) applies to a full
   circle in a mixed pair. The single 2π egg stays outside that
   window and still declines. C1 is not discharged.

   ADR-0005: ogc_iso_circle_same_egg is the lenient normalizer.
   CIRCULARSTRING(A,B,A), B≠A, equals CIRCLE(A,B,ogc_c). ogc_c
   picks CW (GEOS addLinearizedPoints on a collinear triple;
   behavioural reference only). The bag is the item-1 two-hen
   half cycle. IntakeStrict declines.

   3-axiom host. No Admitted / Axiom / Parameter.
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Segment CircleChart SheetHenCook
  IntakeAngles IntakeWalker IntakeCircle.
Import ListNotations.
Local Open Scope R_scope.
Local Open Scope list_scope.

(* WITNESS {"claimId":"0007-intake-angles","topic":"core","lemma":"circle_intake_bag","title":"ISO CIRCLE intake bag: two hens, points A and the antipode, NoDup, two MkCirc of sweep ±π cycling 0 to 1 to 0","file":"theories/IntakeWalkerCircle.v","witness":"0007-intake-angles","board":"ADR-0007"} *)
Theorem circle_intake_bag : forall a b c,
  dist_sq a b <> 0 -> dist_sq b c <> 0 -> dist_sq a c <> 0 ->
  circ_denom a b c <> 0 -> dist (circumcenter_of a b c) a <> 0 ->
  let e := egg_of_points a b c in
  let h1 := circle_half_fst e a b c in
  let h2 := circle_half_snd e a b c in
  let m := circle_antipode e a b c in
  intake_map default_sheet (TCircle CircUnknown [a; b; c]) =
    IntakeBag (mkShcBag default_sheet [0%nat; 1%nat] [a; m]
               (circle_cycle h1 h2)) /\
  NoDup (bag_pts (mkShcBag default_sheet [0%nat; 1%nat] [a; m]
                  (circle_cycle h1 h2))).
Proof.
  intros a b c Hab Hbc Hac Hd Hr e h1 h2 m.
  split.
  - unfold intake_map, intake_map_atom, map_circle_unknown.
    rewrite (try_circle_halves a b c Hab Hbc Hac Hd Hr).
    unfold map_circle_of, circle_cycle. fold e h1 h2 m. reflexivity.
  - cbn [bag_pts].
    assert (Hneq : a <> m).
    { destruct (circle_full_param a b c Hab Hbc Hac Hd Hr) as [H0 _].
      rewrite <- H0. unfold m, e.
      apply circle_start_neq_antipode. exact Hr. }
    apply NoDup_cons.
    + intros Hin. destruct Hin as [Heq|[]]. exact (Hneq (eq_sym Heq)).
    + apply NoDup_cons; [intros Hin; destruct Hin | apply NoDup_nil].
Qed.

(* WITNESS {"claimId":"0007-intake-angles","topic":"core","lemma":"ogc_iso_circle_same_egg","title":"ADR-0005 lenient normalizer: CIRCULARSTRING(A,B,A) with B distinct from A equals ISO CIRCLE(A,B,ogc_c); centre midpoint(A,B), radius |AB|/2, CW sweep -2pi, gamma(0)=A, gamma(1/2)=B, NoDup","file":"theories/IntakeWalkerCircle.v","witness":"0007-intake-angles","board":"ADR-0007"} *)
Theorem ogc_iso_circle_same_egg : forall a b,
  dist_sq a b <> 0 ->
  let c := ogc_c a b in
  let e := egg_of_points a b c in
  let f := circle_of_egg e a b c in
  intake_map default_sheet (TCircularString CircUnknown [a; b; a]) =
    intake_map default_sheet (TCircle CircUnknown [a; b; c]) /\
  intake_map default_sheet (TCircularString CircFullOgc [a; b; a]) =
    intake_map default_sheet (TCircle CircUnknown [a; b; c]) /\
  circ_o f = midpoint a b /\
  circ_r f = dist a b / 2 /\
  circ_sweep f = - (2 * PI) /\
  circ_eval f 0 = a /\
  circ_eval f (1 / 2) = b /\
  NoDup [a; b].
Proof.
  intros a b Hab c e f.
  destruct (cs_lenient_normalizes default_sheet a b Hab) as [Hu HoG].
  fold c in Hu, HoG.
  destruct (ogc_sep a b Hab) as [_ [_ [Hac Hbc]]].
  destruct (ogc_denom_nz a b Hab) as [_ Hd].
  pose proof (ogc_r_nz a b Hab) as Hr.
  fold c in Hac, Hbc, Hd, Hr.
  destruct (circle_full_param a b c Hab Hbc Hac Hd Hr) as
    [He0 [_ [_ [_ [_ [_ [_ [Hneg _]]]]]]]].
  fold f in He0, Hneg.
  assert (Hori : orient_pts a b c < 0) by (apply ogc_orient_neg; exact Hab).
  assert (Hsw : circ_sweep f = - (2 * PI)) by (apply Hneg; exact Hori).
  assert (Hoc : circ_o f = midpoint a b).
  { unfold f, circle_of_egg, e, egg_of_points. cbn.
    apply ogc_center. exact Hab. }
  assert (Hrad : circ_r f = dist a b / 2).
  { unfold f, circle_of_egg, e, egg_of_points, c. cbn.
    rewrite (ogc_center a b Hab). apply ogc_radius. exact Hab. }
  assert (Hhalf : circ_eval f (1 / 2) = b).
  { unfold circle_antipode in *. fold e. fold f.
    apply ogc_antipode_is_b. exact Hab. }
  assert (Hnd : NoDup [a; b]).
  { apply NoDup_cons.
    - intros Hin. destruct Hin as [Heq|[]].
      exact (dist_sq_neq_ne a b Hab (eq_sym Heq)).
    - apply NoDup_cons; [intros Hin; destruct Hin | apply NoDup_nil]. }
  split; [exact Hu|].
  split; [exact HoG|].
  split; [exact Hoc|].
  split; [exact Hrad|].
  split; [exact Hsw|].
  split; [exact He0|].
  split; [exact Hhalf|].
  exact Hnd.
Qed.

Lemma locked_circle_is_half_cycle :
  map_circle default_sheet =
  mkShcBag default_sheet [0%nat; 1%nat] [p50; p_m50]
    (circle_cycle locked_half_fst locked_half_snd) /\
  NoDup (bag_pts (map_circle default_sheet)).
Proof.
  split; [reflexivity | exact locked_circle_pts_nodup].
Qed.

Lemma circle_full_mixed_still_declines : forall ch,
  I_ok (MkCirc locked_full_circle_egg) (MkChord ch) IDecline.
Proof.
  intros ch. unfold I_ok. cbn.
  intros [Ho _].
  unfold circ_open_span, locked_full_circle_egg in Ho. cbn in Ho.
  pose proof PI_RGT_0. lra.
Qed.

(* WITNESS {"claimId":"0007-intake-angles","topic":"core","lemma":"circle_f5_intake_half_only","title":"F5 intake half only: the single 2pi egg is outside the strict chart window and still declines, bag halves have absolute sweep pi, C1 is not discharged","file":"theories/IntakeWalkerCircle.v","witness":"0007-intake-angles","board":"ADR-0007"} *)
Theorem circle_f5_intake_half_only :
  (forall a b c, orient_pts a b c <> 0 ->
     ~ (- (2 * PI) < full_sweep a b c < 2 * PI)) /\
  ~ circle_c1_fullspan_discharged /\
  (forall ch, I_ok (MkCirc locked_full_circle_egg) (MkChord ch) IDecline).
Proof.
  split; [exact full_sweep_outside_strict_window|].
  split; [exact circle_f5_c1_not_done|].
  exact circle_full_mixed_still_declines.
Qed.

Print Assumptions ogc_iso_circle_same_egg.
Print Assumptions circle_intake_bag.
Print Assumptions locked_circle_is_half_cycle.
Print Assumptions circle_full_mixed_still_declines.
Print Assumptions circle_f5_intake_half_only.
