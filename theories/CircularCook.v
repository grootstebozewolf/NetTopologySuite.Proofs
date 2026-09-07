(* ============================================================================
   NetTopologySuite.Proofs.CircularCook
   ----------------------------------------------------------------------------
   Year-1 circular–circular 𝓘 on one sheet: attach p* to the extractable
   classifier in CircularCookZ.v.

   I_circles_on_z_sheet returns real constructors

       ICircHit h+ p+ h− p− | ICircEmpty | ICircDecline

   Hit mints one hen per named radical root (plus / minus). Same named
   root ⇒ same hen by construction — see CircularCookZ.same_named_root_same_hen.
   p* is ArcArcCircles.radical_point_plus / _minus, not a remint of the
   #671 resultant certificate and not 𝓘 itself.

   QEX (one paragraph). Year-1 CircularArc is the three-point
   CurveGeometry carrier, not an interpolant γ : [0,1] → S. SheetHenCook
   names EggCircularArc only as MkOutOfScope — there is no circular
   chord_eval. ArcParamBridge / ArcTraversalBridge realize a sweep-angle
   parameterization (atan2), not a [0,1] egg constructor. Full
   𝓘 = Hit (h*, tᵢ, tⱼ) waits on that constructor. This cut still
   ships Hit with p* + hen. Decline / Empty / Hit are constructors
   returned by a function.

   QEX. SheetHenCook.first_cook_scope stays chord–chord
   (circular_not_first_cook_scope). Do not wholesale-rewrite that
   predicate; chord–chord epic tickets stay standing.

   Not OverlayNGCurve wiring. Not fully_intersected retirement.
   Not a kiss / CRV-TOUCH certificate (tangent → ICircDecline).

   WITNESS topic: core · claimId: 64-i-circular · witness: 64-i-circular-locked
   lane: proofs
   board: ADR-0007

   No `Admitted`, no `Axiom`, no `Parameter`.
   3-axiom floor (classical reals via radical_point / IZR). No Classic
   in the function: classification is I_circles_z.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import ZArith Reals Lra.
From NTS.Proofs Require Import Distance SheetHenCook ArcArcCircles CircularCookZ.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Circular 𝓘 result. Hens are SheetHenCook.Hen (= nat).                     *)
(* -------------------------------------------------------------------------- *)

Inductive ICirc : Type :=
| ICircHit (h_plus : Hen) (p_plus : Point) (h_minus : Hen) (p_minus : Point)
| ICircEmpty
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
  | IZDecline => ICircDecline
  end.

(* Year-1 CircularArc × CircularArc: 𝓘 of the circumcircles, once the
   caller has centres/radii on the integer sheet. Invalid / out-of-scope
   three-point pairs are Decline at I_circles_z (zero radius, coincident
   centres). Span membership is not applied — that is the missing γ. *)
Definition I_circular_circles := I_circles_on_z_sheet.

(* -------------------------------------------------------------------------- *)
(* QEX: no γ : [0,1] → S on CircularArc. First cook scope stays chord–chord. *)
(* -------------------------------------------------------------------------- *)

Inductive CircGammaStatus : Type :=
| CircGammaDischarged
| CircGammaQEX.

Definition circular_gamma_status : CircGammaStatus := CircGammaQEX.

Lemma circular_gamma_is_qex :
  circular_gamma_status = CircGammaQEX.
Proof.
  reflexivity.
Qed.

Lemma circular_gamma_not_discharged :
  circular_gamma_status <> CircGammaDischarged.
Proof.
  discriminate.
Qed.

Lemma circular_not_first_cook_scope :
  ~ first_cook_scope EggCircularArc EggCircularArc.
Proof.
  intro H. exact H.
Qed.

Lemma first_cook_scope_stays_chord_chord :
  first_cook_scope EggChord EggChord /\
  ~ first_cook_scope EggCircularArc EggCircularArc.
Proof.
  split; [exact first_cook_scope_chord_chord | exact circular_not_first_cook_scope].
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked fixture: (0,0)/(7,0) r=5 → Hit with radical p* and hens 0,1.       *)
(* -------------------------------------------------------------------------- *)

Lemma zpt_00 : zpt 0%Z 0%Z = mkPoint 0 0.
Proof. unfold zpt. reflexivity. Qed.

Lemma zpt_70 : zpt 7%Z 0%Z = mkPoint 7 0.
Proof. unfold zpt. reflexivity. Qed.

(* WITNESS {"claimId":"64-i-circular","topic":"core","lemma":"locked_I_circles_on_z_sheet_hit","title":"Year-1 circular I attaches radical p* and mints hens 0,1 on locked (0,0)/(7,0) r=5","file":"theories/CircularCook.v","witness":"64-i-circular-locked","board":"ADR-0007"} *)

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

Lemma ICircEmpty_neq_ICircDecline : ICircEmpty <> ICircDecline.
Proof.
  discriminate.
Qed.

Lemma ICircHit_neq_ICircEmpty :
  forall hp pp hm pm, ICircHit hp pp hm pm <> ICircEmpty.
Proof.
  intros. discriminate.
Qed.

Lemma ICircHit_neq_ICircDecline :
  forall hp pp hm pm, ICircHit hp pp hm pm <> ICircDecline.
Proof.
  intros. discriminate.
Qed.

(* Cook-local hens on the R-side Hit are the named roots. *)
Lemma locked_hit_mints_named_hens :
  match I_circles_on_z_sheet 0 0 5 7 0 5 with
  | ICircHit hp _ hm _ => hp = hen_plus /\ hm = hen_minus
  | _ => False
  end.
Proof.
  rewrite locked_I_circles_on_z_sheet_hit.
  split; reflexivity.
Qed.

Print Assumptions circular_gamma_is_qex.
Print Assumptions circular_not_first_cook_scope.
Print Assumptions first_cook_scope_stays_chord_chord.
Print Assumptions locked_I_circles_on_z_sheet_hit.
Print Assumptions locked_I_circles_empty.
Print Assumptions locked_I_circles_decline.
Print Assumptions ICircEmpty_neq_ICircDecline.
Print Assumptions locked_hit_mints_named_hens.
