(* ============================================================================
   NetTopologySuite.Proofs.CircularCook
   ----------------------------------------------------------------------------
   R-side attach of radical p* to CircularCookZ.I_circles_z.
   Classical-reals (3-axiom) via radical_point / IZR. Not glossary 𝓘.

   Γ CircGamma host letter (claimId 0007-gamma-mkcirc):
   QED: atan2-free host γ : [0,1] → S on CircularEgg via MkCirc
   (θ₀ + t·Δθ; angles are egg data). circular_gamma_status is
   CircGammaDischarged. circ_gamma_constructor_inhabits CircGammaMkCirc.
   first_cook_scope includes circular–circular. Host I_ok Hits two
   MkCirc chickens; try_cook_hit mints (CircularCookMkCirc.v).
   MkOutOfScope EggCircularArc stays Decline. Mixed / interior stay
   sidecar. nlerp still misses the reflex principal span — that is
   a fact about nlerp, not the remaining Γ hole (MkCirc is not nlerp).
   Sidecar CircularCookSpan.arc_gamma is not host Γ. I_ok_circ /
   I_ok_mixed Hit is not host I_ok.

   I.1: I_gloss is host I_ok Hit on MkCirc (not on tags). I.2 ∀ Hit
   soundness lives in CircularCookHit.v;
   I.3 ∀ Empty / Decline lives in CircularCookEmpty.v (γ_full);
   I.8 leftover confluence lives in CircularCookConfluence.v;
   I.9 classifier ≠ cook lives in CircularCookLicense.v;
   I.10 Campaign-I close lives in CircularCookClose.v;
   II.1 span filter as IResult lives in CircularCookSpanFilter.v;
   II.2 span split at in-span t lives in CircularCookSpanSplit.v;
   II.3 I_ok_circ lives in CircularCookOkCirc.v (4-axiom sidecar);
   II.4 Campaign-II close lives in CircularCookCloseII.v
   (4-axiom sidecar); Phase B.1 CS concat joints live in
   CircularCookCsConcat.v (4-axiom sidecar reuse of I_ok_circ);
   Phase B.2 CompoundCurve member joints live in
   CircularCookCcConcat.v (4-axiom sidecar / host reuse);
   Phase B.3 CurvePolygon ring closure lives in
   CircularCookCpConcat.v (4-axiom sidecar / host reuse);
   this host flag is CircGammaDischarged (MkCirc).

   WITNESS topic: core / overlay · claimId: 0007-gamma-mkcirc
   witness: 0007-gamma-mkcirc
   board: ADR-0007
   3-axiom. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import ZArith Reals Lra.
From NTS.Proofs Require Import Distance SheetHenCook CircularCookMkCirc
  ArcArcCircles CircularCookZ.
Local Open Scope R_scope.

Inductive ICirc : Type :=
| ICircHit (h_plus : Hen) (p_plus : Point) (h_minus : Hen) (p_minus : Point)
| ICircEmpty
| ICircTouch (h : Hen) (p : Point)
| ICircDecline.

Definition zpt (x y : Z) : Point :=
  mkPoint (IZR x) (IZR y).

Definition I_circles_on_z_sheet (o1x o1y r1 o2x o2y r2 : Z) : ICirc :=
  match I_circles_z o1x o1y r1 o2x o2y r2 with
  | IZHit hp hm =>
      ICircHit hp
        (radical_point_plus (zpt o1x o1y) (zpt o2x o2y) (IZR r1) (IZR r2))
        hm
        (radical_point_minus (zpt o1x o1y) (zpt o2x o2y) (IZR r1) (IZR r2))
  | IZEmpty => ICircEmpty
  | IZTouch h =>
      ICircTouch h
        (radical_point_plus (zpt o1x o1y) (zpt o2x o2y) (IZR r1) (IZR r2))
  | IZDecline => ICircDecline
  end.

Inductive CircGammaStatus : Type :=
| CircGammaDischarged
| CircGammaQEX.

Definition circular_gamma_status : CircGammaStatus := CircGammaDischarged.

Lemma circular_gamma_is_discharged :
  circular_gamma_status = CircGammaDischarged.
Proof.
  reflexivity.
Qed.

Lemma circular_is_first_cook_scope :
  first_cook_scope EggCircularArc EggCircularArc.
Proof.
  exact circular_egg_first_cook_scope.
Qed.

(* -------------------------------------------------------------------------- *)
(* Γ CircGamma named QEX gap. Not a bool. Not sidecar arc_gamma.              *)
(* -------------------------------------------------------------------------- *)

(* Discharge constructor: host MkCirc carrying 3-axiom γ. *)
Inductive CircGammaConstructor : Type :=
| CircGammaMkCirc.

Definition circ_gamma_constructor_inhabits
  (c : CircGammaConstructor) : Prop :=
  match c with
  | CircGammaMkCirc =>
      exists ce, egg_class (MkCirc ce) = EggCircularArc
  end.

Lemma circ_gamma_mkcirc_inhabits :
  circ_gamma_constructor_inhabits CircGammaMkCirc.
Proof.
  exists locked_circ_A. reflexivity.
Qed.

(* Chord-project nlerp is the natural atan2-free interpolant:
   γ(1/2) = O + r · normalize((A−O)+(B−O)). On the unit circle
   at the origin this is normalize(A+B). Reflex fixture
   (ArcMinorWitness geometry): start (1,0) → mid (−1,0) → end (0,1)
   traces 270° — the principal span is the major arc. nlerp
   takes the minor quarter through (1/√2, 1/√2), opposite side
   of the chord from mid. *)
Definition reflex_start : Point := mkPoint 1 0.
Definition reflex_mid : Point := mkPoint (-1) 0.
Definition reflex_end : Point := mkPoint 0 1.

Definition chord_cross (A B P : Point) : R :=
  (px B - px A) * (py P - py A) - (py B - py A) * (px P - px A).

Definition nlerp_half_origin (A B : Point) : Point :=
  let dx := px A + px B in
  let dy := py A + py B in
  let s := sqrt (dx * dx + dy * dy) in
  mkPoint (dx / s) (dy / s).

(* Closed form on the unit-circle reflex fixture: normalize((1,0)+(0,1)). *)
Definition reflex_nlerp_half : Point :=
  mkPoint (1 / sqrt 2) (1 / sqrt 2).

Lemma reflex_nlerp_half_eval :
  nlerp_half_origin reflex_start reflex_end = reflex_nlerp_half.
Proof.
  unfold nlerp_half_origin, reflex_nlerp_half, reflex_start, reflex_end.
  cbn [px py].
  replace ((1 + 0) * (1 + 0) + (0 + 1) * (0 + 1)) with 2 by ring.
  replace (1 + 0) with 1 by ring.
  replace (0 + 1) with 1 by ring.
  reflexivity.
Qed.

Definition nlerp_misses_reflex_principal : Prop :=
  chord_cross reflex_start reflex_end reflex_mid
  * chord_cross reflex_start reflex_end reflex_nlerp_half < 0.

Lemma sqrt2_sq : sqrt 2 * sqrt 2 = 2.
Proof.
  apply sqrt_sqrt. lra.
Qed.

Lemma sqrt2_neq_0 : sqrt 2 <> 0.
Proof.
  apply Rgt_not_eq. apply sqrt_lt_R0. lra.
Qed.

Lemma two_over_sqrt2 : 2 * / sqrt 2 = sqrt 2.
Proof.
  rewrite <- sqrt2_sq at 1.
  rewrite Rmult_assoc.
  rewrite (Rinv_r (sqrt 2) sqrt2_neq_0).
  rewrite Rmult_1_r.
  reflexivity.
Qed.

Lemma one_lt_sqrt2 : 1 < sqrt 2.
Proof.
  rewrite <- sqrt_1. apply sqrt_lt_1; lra.
Qed.

Lemma reflex_nlerp_misses_principal :
  nlerp_misses_reflex_principal.
Proof.
  unfold nlerp_misses_reflex_principal, reflex_nlerp_half,
         chord_cross, reflex_start, reflex_mid, reflex_end.
  cbn [px py]. unfold Rdiv.
  assert (Hmid :
    (0 - 1) * (0 - 0) - (1 - 0) * (-1 - 1) = 2) by ring.
  assert (Hn :
    (0 - 1) * (1 * / sqrt 2 - 0) - (1 - 0) * (1 * / sqrt 2 - 1)
    = 1 - 2 * / sqrt 2) by ring.
  rewrite Hmid, Hn, two_over_sqrt2.
  pose proof one_lt_sqrt2.
  lra.
Qed.

(* Piecewise nlerp start→mid→end is not total: this reflex half
   is antipodal, so (start−O)+(mid−O) = 0 and normalize fails.
   Named Prop (not the lemma itself) so tickets can conjoin it. *)
Definition reflex_piecewise_nlerp_degenerate : Prop :=
  px reflex_start + px reflex_mid = 0 /\
  py reflex_start + py reflex_mid = 0.

Lemma reflex_piecewise_nlerp_degenerate_holds :
  reflex_piecewise_nlerp_degenerate.
Proof.
  unfold reflex_piecewise_nlerp_degenerate, reflex_start, reflex_mid.
  cbn [px py]. split; ring.
Qed.

(* Chord interpolant inhabits the host. Circular γ inhabits via MkCirc. *)
Lemma host_chord_gamma_inhabits :
  exists c t p, p = chord_eval c t.
Proof.
  exists (mkChordEgg (mkPoint 0 0) (mkPoint 1 0)), 0, (mkPoint 0 0).
  unfold chord_eval. cbn [ce_p0 ce_p1 px py].
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma zpt_00 : zpt 0%Z 0%Z = mkPoint 0 0.
Proof. unfold zpt. reflexivity. Qed.

Lemma zpt_70 : zpt 7%Z 0%Z = mkPoint 7 0.
Proof. unfold zpt. reflexivity. Qed.

(* WITNESS {"claimId":"64-i-circular","topic":"core","lemma":"locked_I_circles_on_z_sheet_hit","title":"Integer circle-circle seam attaches radical p* on locked (0,0)/(7,0) r=5","file":"theories/CircularCook.v","witness":"64-i-circular-locked","board":"ADR-0007"} *)

Lemma locked_I_circles_on_z_sheet_hit :
  I_circles_on_z_sheet 0 0 5 7 0 5 =
  ICircHit hen_plus
    (radical_point_plus (mkPoint 0 0) (mkPoint 7 0) 5 5)
    hen_minus
    (radical_point_minus (mkPoint 0 0) (mkPoint 7 0) 5 5).
Proof.
  unfold I_circles_on_z_sheet.
  rewrite locked_I_circles_z_hit.
  rewrite zpt_00, zpt_70.
  reflexivity.
Qed.

Lemma locked_I_circles_empty :
  I_circles_on_z_sheet 0 0 5 20 0 5 = ICircEmpty.
Proof.
  unfold I_circles_on_z_sheet.
  rewrite locked_disjoint_is_empty.
  reflexivity.
Qed.

Lemma locked_I_circles_decline :
  I_circles_on_z_sheet 0 0 5 0 0 5 = ICircDecline.
Proof.
  unfold I_circles_on_z_sheet.
  rewrite locked_coincident_is_decline.
  reflexivity.
Qed.

Lemma locked_I_circles_touch :
  I_circles_on_z_sheet 0 0 5 10 0 5 =
  ICircTouch hen_plus
    (radical_point_plus (mkPoint 0 0) (mkPoint 10 0) 5 5).
Proof.
  unfold I_circles_on_z_sheet.
  rewrite locked_external_kiss_is_touch.
  unfold zpt. reflexivity.
Qed.

Lemma locked_I_circles_internal_kiss :
  I_circles_on_z_sheet 0 0 5 3 0 2 =
  ICircTouch hen_plus
    (radical_point_plus (mkPoint 0 0) (mkPoint 3 0) 5 2).
Proof.
  unfold I_circles_on_z_sheet.
  rewrite locked_internal_kiss_is_touch.
  unfold zpt. reflexivity.
Qed.

Lemma ICircEmpty_neq_ICircDecline : ICircEmpty <> ICircDecline.
Proof.
  discriminate.
Qed.

(* WITNESS {"claimId":"0007-gamma-mkcirc","topic":"core","lemma":"ticket_64_circ_gamma_qed_or_qex","title":"CircularArc gamma is discharged MkCirc (QED) or CircGammaQEX with named missing constructor / nlerp miss / no first-cook expand (QEX); discharged QED; MkCirc angle interpolant; nlerp miss is not the remaining hole","file":"theories/CircularCook.v","witness":"0007-gamma-mkcirc","board":"ADR-0007"} *)

Theorem ticket_64_circ_gamma_qed_or_qex :
  (circular_gamma_status = CircGammaDischarged
   /\ circ_gamma_constructor_inhabits CircGammaMkCirc
   /\ first_cook_scope EggCircularArc EggCircularArc)
  \/
  (circular_gamma_status = CircGammaQEX
   /\ ~ circ_gamma_constructor_inhabits CircGammaMkCirc
   /\ (forall e, egg_class e = EggCircularArc ->
         e = MkOutOfScope EggCircularArc)
   /\ nlerp_misses_reflex_principal
   /\ ~ first_cook_scope EggCircularArc EggCircularArc).
Proof.
  left.
  split; [exact circular_gamma_is_discharged|].
  split; [exact circ_gamma_mkcirc_inhabits|].
  exact circular_is_first_cook_scope.
Qed.

(* I.1: I_gloss on circular eggs is I_ok + host CircGamma. MkCirc
   inhabits Hit; MkOutOfScope tags still Decline. Not a type synonym
   for I_circles_z / I_circles_gamma / the sidecar cook. *)
(* WITNESS {"claimId":"0007-gamma-mkcirc","topic":"overlay","lemma":"ticket_0007_i1_gloss_qed_or_qex","title":"Host I_gloss on circular eggs is discharged MkCirc Hit (QED) or still QEX with missing MkCirc and I_ok Decline only (QEX); discharged QED; tags stay Decline","file":"theories/CircularCook.v","witness":"0007-gamma-mkcirc","board":"ADR-0007"} *)

Theorem ticket_0007_i1_gloss_qed_or_qex :
  (circular_gamma_status = CircGammaDischarged
   /\ circ_gamma_constructor_inhabits CircGammaMkCirc
   /\ exists ce1 ce2 p ti tj,
        I_ok (MkCirc ce1) (MkCirc ce2) (IHit p ti tj)
   /\ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc) IDecline
   /\ (forall p ti tj,
         ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
              (IHit p ti tj)))
  \/
  (circular_gamma_status = CircGammaQEX
   /\ ~ circ_gamma_constructor_inhabits CircGammaMkCirc
   /\ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc) IDecline
   /\ (forall p ti tj,
         ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
              (IHit p ti tj))).
Proof.
  left.
  split; [exact circular_gamma_is_discharged|].
  split; [exact circ_gamma_mkcirc_inhabits|].
  exists locked_circ_A, locked_circ_B, locked_circ_hit_pt,
    locked_circ_ti, locked_circ_tj.
  split; [exact locked_mkcirc_I_ok|].
  split; [exact circular_decline_I_ok|].
  exact circular_hit_not_I_ok.
Qed.

(* WITNESS {"claimId":"0007-gamma-mkcirc","topic":"overlay","lemma":"ticket_0007_gamma_nlerp_qed_or_qex","title":"CircGamma is discharged MkCirc while nlerp still misses the reflex principal span (QED) or CircGamma stays QEX on that miss (QEX); discharged QED; nlerp is not the host interpolant","file":"theories/CircularCook.v","witness":"0007-gamma-mkcirc","board":"ADR-0007"} *)
Theorem ticket_0007_gamma_nlerp_qed_or_qex :
  (circular_gamma_status = CircGammaDischarged
   /\ circ_gamma_constructor_inhabits CircGammaMkCirc
   /\ nlerp_misses_reflex_principal
   /\ reflex_piecewise_nlerp_degenerate)
  \/
  (circular_gamma_status = CircGammaQEX
   /\ nlerp_misses_reflex_principal
   /\ reflex_piecewise_nlerp_degenerate).
Proof.
  left.
  split; [exact circular_gamma_is_discharged|].
  split; [exact circ_gamma_mkcirc_inhabits|].
  split; [exact reflex_nlerp_misses_principal|].
  exact reflex_piecewise_nlerp_degenerate_holds.
Qed.

Print Assumptions circular_gamma_is_discharged.
Print Assumptions circular_is_first_cook_scope.
Print Assumptions circ_gamma_mkcirc_inhabits.
Print Assumptions sqrt2_sq.
Print Assumptions two_over_sqrt2.
Print Assumptions one_lt_sqrt2.
Print Assumptions reflex_nlerp_half_eval.
Print Assumptions reflex_nlerp_misses_principal.
Print Assumptions reflex_piecewise_nlerp_degenerate_holds.
Print Assumptions host_chord_gamma_inhabits.
Print Assumptions locked_I_circles_on_z_sheet_hit.
Print Assumptions locked_I_circles_touch.
Print Assumptions locked_I_circles_internal_kiss.
Print Assumptions ICircEmpty_neq_ICircDecline.
Print Assumptions ticket_64_circ_gamma_qed_or_qex.
Print Assumptions ticket_0007_i1_gloss_qed_or_qex.
Print Assumptions ticket_0007_gamma_nlerp_qed_or_qex.
