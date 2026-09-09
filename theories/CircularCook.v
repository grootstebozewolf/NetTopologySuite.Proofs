(* ============================================================================
   NetTopologySuite.Proofs.CircularCook
   ----------------------------------------------------------------------------
   R-side attach of radical p* to CircularCookZ.I_circles_z.
   Classical-reals (3-axiom) via radical_point / IZR. Not glossary 𝓘:
   QEX — no 3-axiom γ : [0,1] → S on CircularArc (atan2 interpolant
   lives in CircularCookSpan.v; sidecar cook of a circular Hit lives
   in CircularCookSplit.v). first_cook_scope stays chord–chord.
   CircGamma stays QEX; the sidecar does not fake Discharge.
   I.1: I_gloss (host I_ok + CircGamma) is undefined while this
   flag is QEX — not a type synonym for the Z / gamma / sidecar
   objects. I.2 ∀ Hit soundness lives in CircularCookHit.v;
   I.3 ∀ Empty / Decline lives in CircularCookEmpty.v (γ_full);
   I.8 leftover confluence lives in CircularCookConfluence.v;
   I.9 classifier ≠ cook lives in CircularCookLicense.v;
   I.10 Campaign-I close lives in CircularCookClose.v;
   II.1 span filter as IResult lives in CircularCookSpanFilter.v;
   II.2 span split at in-span t lives in CircularCookSpanSplit.v;
   this host flag stays QEX.

   WITNESS topic: core · claimId: 64-i-circular · witness: 64-i-circular-locked

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   ========================================================================== *)

From Stdlib Require Import ZArith Reals Lra.
From NTS.Proofs Require Import Distance SheetHenCook ArcArcCircles CircularCookZ.
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

Definition circular_gamma_status : CircGammaStatus := CircGammaQEX.

Lemma circular_gamma_is_qex :
  circular_gamma_status = CircGammaQEX.
Proof.
  reflexivity.
Qed.

Lemma circular_not_first_cook_scope :
  ~ first_cook_scope EggCircularArc EggCircularArc.
Proof.
  intro H. exact H.
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

(* WITNESS {"claimId":"64-circ-hit-params","topic":"core","lemma":"ticket_64_circ_gamma_qed_or_qex","title":"CircularArc gamma is discharged (QED) or still CircGammaQEX (QEX); discharged QEX","file":"theories/CircularCook.v","witness":"64-i-circular-locked","board":"ADR-0007"} *)

Theorem ticket_64_circ_gamma_qed_or_qex :
  circular_gamma_status = CircGammaDischarged
  \/
  circular_gamma_status = CircGammaQEX.
Proof.
  right.
  exact circular_gamma_is_qex.
Qed.

(* I.1: I_gloss on circular eggs is I_ok + host CircGamma. While
   CircGamma is QEX the host admits only Decline — not a constructed
   circular Hit. Not a type synonym for I_circles_z / I_circles_gamma
   / the sidecar cook. *)
(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_i1_gloss_qed_or_qex","title":"Host I_gloss on circular eggs is discharged CircGamma (QED) or still QEX with I_ok Decline only (QEX); discharged QEX; I.1 I_gloss undefined","file":"theories/CircularCook.v","witness":"0007-I.1-fence","board":"ADR-0007"} *)

Theorem ticket_0007_i1_gloss_qed_or_qex :
  (circular_gamma_status = CircGammaDischarged
   /\ exists p ti tj,
        I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
             (IHit p ti tj))
  \/
  (circular_gamma_status = CircGammaQEX
   /\ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc) IDecline
   /\ (forall p ti tj,
         ~ I_ok (MkOutOfScope EggCircularArc) (MkOutOfScope EggCircularArc)
              (IHit p ti tj))).
Proof.
  right.
  split; [exact circular_gamma_is_qex|].
  split; [exact circular_decline_I_ok|].
  exact circular_hit_not_I_ok.
Qed.

Print Assumptions circular_gamma_is_qex.
Print Assumptions circular_not_first_cook_scope.
Print Assumptions locked_I_circles_on_z_sheet_hit.
Print Assumptions locked_I_circles_touch.
Print Assumptions locked_I_circles_internal_kiss.
Print Assumptions ICircEmpty_neq_ICircDecline.
Print Assumptions ticket_64_circ_gamma_qed_or_qex.
Print Assumptions ticket_0007_i1_gloss_qed_or_qex.
