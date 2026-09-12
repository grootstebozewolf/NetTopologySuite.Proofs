(* ============================================================================
   NetTopologySuite.Proofs.NurbsCookMkNurbs
   ----------------------------------------------------------------------------
   ADR-0007 letter: NURBS×NURBS first-cook / Hit arm
   (claimId 0007-nurbs-first-cook).

   Host MkNurbs pairs are interpolant_pair. first_cook_scope
   includes EggNurbs × EggNurbs. I_ok Hits two MkNurbs
   chickens on a locked crossing pair via on_nurbs (Cox-de-Boor
   -free chord-parameter interpolant). try_cook_hit mints MkNurbs
   children — not a silent demote to MkChord.

   Locked fixture reuses the SheetHenCook unit-square-diagonal
   geometry already Qed as a proper cross (sidecar NURBS chord
   seed). Eggs carry an off-chord control point. Not length /
   Cox-de-Boor / knot-span as noding.

   MkOutOfScope EggNurbs stays Decline. Mixed NURBS×chord
   stays Decline. SIN / ellipse / spiral / geodesic stay
   out of first cook. ρ / Campaign / length-as-noding stay parked.

   WITNESS topic: overlay · claimId: 0007-nurbs-first-cook
   witness: 0007-nurbs-first-cook
   board: ADR-0007
   3-axiom. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance SheetHenCook.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Locked MkNurbs eggs. Same endpoints as diag_ab / diag_cd.                  *)
(* -------------------------------------------------------------------------- *)

Definition locked_nurbs_A : NurbsEgg :=
  mkNurbsEgg (mkPoint 0 0) (mkPoint 2 2) (mkPoint 2 0).

Definition locked_nurbs_B : NurbsEgg :=
  mkNurbsEgg (mkPoint 0 2) (mkPoint 2 0) (mkPoint 0 0).

Definition locked_nurbs_hit_pt : Point := mkPoint 1 1.
Definition locked_nurbs_ti : R := 1 / 2.
Definition locked_nurbs_tj : R := 1 / 2.

Definition locked_nurbs_ck1 : Chicken :=
  mkChicken 0%nat 1%nat (MkNurbs locked_nurbs_A).

Definition locked_nurbs_ck2 : Chicken :=
  mkChicken 2%nat 3%nat (MkNurbs locked_nurbs_B).

Lemma locked_nurbs_ti_in_01 : 0 <= locked_nurbs_ti <= 1.
Proof.
  unfold locked_nurbs_ti. lra.
Qed.

Lemma locked_nurbs_tj_in_01 : 0 <= locked_nurbs_tj <= 1.
Proof.
  unfold locked_nurbs_tj. lra.
Qed.

Lemma locked_nurbs_A_at_ti :
  nurbs_eval locked_nurbs_A locked_nurbs_ti = locked_nurbs_hit_pt.
Proof.
  unfold nurbs_eval, locked_nurbs_A, locked_nurbs_ti, locked_nurbs_hit_pt.
  cbn [px py nurbs_p0 nurbs_p1].
  apply (f_equal2 mkPoint); field.
Qed.

Lemma locked_nurbs_B_at_tj :
  nurbs_eval locked_nurbs_B locked_nurbs_tj = locked_nurbs_hit_pt.
Proof.
  unfold nurbs_eval, locked_nurbs_B, locked_nurbs_tj, locked_nurbs_hit_pt.
  cbn [px py nurbs_p0 nurbs_p1].
  apply (f_equal2 mkPoint); field.
Qed.

Lemma locked_on_nurbs_A :
  on_nurbs locked_nurbs_A locked_nurbs_ti locked_nurbs_hit_pt.
Proof.
  unfold on_nurbs. split; [exact locked_nurbs_ti_in_01|].
  symmetry. exact locked_nurbs_A_at_ti.
Qed.

Lemma locked_on_nurbs_B :
  on_nurbs locked_nurbs_B locked_nurbs_tj locked_nurbs_hit_pt.
Proof.
  unfold on_nurbs. split; [exact locked_nurbs_tj_in_01|].
  symmetry. exact locked_nurbs_B_at_tj.
Qed.

(* -------------------------------------------------------------------------- *)
(* Host I_ok Hit and try_cook_hit mint on the locked MkNurbs pair.            *)
(* -------------------------------------------------------------------------- *)

Lemma locked_mknurbs_I_ok :
  I_ok (MkNurbs locked_nurbs_A) (MkNurbs locked_nurbs_B)
       (IHit locked_nurbs_hit_pt locked_nurbs_ti locked_nurbs_tj).
Proof.
  unfold I_ok.
  split; [exact locked_on_nurbs_A | exact locked_on_nurbs_B].
Qed.

Definition locked_mknurbs_hit : IResult :=
  IHit locked_nurbs_hit_pt locked_nurbs_ti locked_nurbs_tj.

Definition cooked_mknurbs : CookedPair :=
  cook_hit_nurbs locked_nurbs_ck1 locked_nurbs_ck2
    locked_nurbs_A locked_nurbs_B locked_nurbs_ti locked_nurbs_tj
    crossing_hen.

Lemma cook_hit_nurbs_shares_hen :
  forall c1 c2 e1 e2 ti tj h,
    cooked_shares_hen (cook_hit_nurbs c1 c2 e1 e2 ti tj h).
Proof.
  intros. repeat split; reflexivity.
Qed.

Lemma cooked_mknurbs_shares :
  cooked_shares_hen cooked_mknurbs.
Proof.
  apply cook_hit_nurbs_shares_hen.
Qed.

Lemma cooked_mknurbs_try :
  try_cook_hit locked_nurbs_ck1 locked_nurbs_ck2
    locked_mknurbs_hit crossing_hen = Some cooked_mknurbs.
Proof.
  reflexivity.
Qed.

Lemma cooked_mknurbs_children_are_nurbs :
  egg_class (ck_egg (cp_left1 cooked_mknurbs)) = EggNurbs /\
  egg_class (ck_egg (cp_right1 cooked_mknurbs)) = EggNurbs /\
  egg_class (ck_egg (cp_left2 cooked_mknurbs)) = EggNurbs /\
  egg_class (ck_egg (cp_right2 cooked_mknurbs)) = EggNurbs.
Proof.
  repeat split; reflexivity.
Qed.

Lemma interpolant_pair_mknurbs :
  interpolant_pair (MkNurbs locked_nurbs_A) (MkNurbs locked_nurbs_B).
Proof.
  exact I.
Qed.

Lemma mknurbs_tag_still_decline :
  I_ok (MkOutOfScope EggNurbs) (MkOutOfScope EggNurbs) IDecline.
Proof.
  exact nurbs_decline_I_ok.
Qed.

Lemma mknurbs_tag_hit_false :
  forall p ti tj,
    ~ I_ok (MkOutOfScope EggNurbs) (MkOutOfScope EggNurbs)
         (IHit p ti tj).
Proof.
  intros p ti tj H. exact H.
Qed.

Lemma mknurbs_mixed_still_decline :
  I_ok (MkChord hor_bot) (MkNurbs locked_nurbs_A) IDecline.
Proof.
  unfold I_ok, interpolant_pair. intro H. exact H.
Qed.

Lemma nurbs_chord_not_first_cook_scope :
  ~ first_cook_scope EggNurbs EggChord.
Proof.
  intro H. exact H.
Qed.

Lemma mknurbs_neq_mkchord_locked :
  MkNurbs locked_nurbs_A <> MkChord diag_ab.
Proof.
  discriminate.
Qed.

(* Same-egg Hit on the payload locked record (sidecar ticket reuse). *)
Lemma locked_payload_egg_self_hit :
  I_ok (MkNurbs locked_nurbs_egg) (MkNurbs locked_nurbs_egg)
       (IHit (mkPoint (1 / 2) 0) (1 / 2) (1 / 2)).
Proof.
  unfold I_ok, on_nurbs, nurbs_eval, locked_nurbs_egg.
  cbn [px py nurbs_p0 nurbs_p1].
  split.
  - split; [lra|]. apply (f_equal2 mkPoint); field.
  - split; [lra|]. apply (f_equal2 mkPoint); field.
Qed.

(* WITNESS {"claimId":"0007-nurbs-first-cook","topic":"overlay","lemma":"locked_mknurbs_I_ok","title":"Host I_ok Hits two MkNurbs chickens on the locked crossing NURBS pair","file":"theories/NurbsCookMkNurbs.v","witness":"0007-nurbs-first-cook","board":"ADR-0007"} *)

(* WITNESS {"claimId":"0007-nurbs-first-cook","topic":"overlay","lemma":"cooked_mknurbs_try","title":"try_cook_hit mints MkNurbs hens on the locked NURBS Hit","file":"theories/NurbsCookMkNurbs.v","witness":"0007-nurbs-first-cook","board":"ADR-0007"} *)

(* WITNESS {"claimId":"0007-nurbs-first-cook","topic":"overlay","lemma":"ticket_0007_nurbs_first_cook_qed_or_qex","title":"NURBS times NURBS is first cook with a locked MkNurbs IHit that try_cook_hit mints (QED) or NURBS times NURBS stays QEX (QEX); discharged QED; tags and mixed stay Decline; length-as-noding / Cox-de-Boor / Campaign / rho stay parked","file":"theories/NurbsCookMkNurbs.v","witness":"0007-nurbs-first-cook","board":"ADR-0007"} *)
Theorem ticket_0007_nurbs_first_cook_qed_or_qex :
  (first_cook_scope EggNurbs EggNurbs /\
   interpolant_pair (MkNurbs locked_nurbs_A) (MkNurbs locked_nurbs_B) /\
   I_ok (MkNurbs locked_nurbs_A) (MkNurbs locked_nurbs_B)
        (IHit locked_nurbs_hit_pt locked_nurbs_ti locked_nurbs_tj) /\
   try_cook_hit locked_nurbs_ck1 locked_nurbs_ck2
     locked_mknurbs_hit crossing_hen = Some cooked_mknurbs /\
   cooked_shares_hen cooked_mknurbs /\
   egg_class (ck_egg (cp_left1 cooked_mknurbs)) = EggNurbs /\
   I_ok (MkOutOfScope EggNurbs) (MkOutOfScope EggNurbs) IDecline /\
   I_ok (MkChord hor_bot) (MkNurbs locked_nurbs_A) IDecline /\
   ~ first_cook_scope EggNurbs EggChord /\
   ~ first_cook_scope EggEllipse EggEllipse /\
   cook_loop_status = LoopObligation)
  \/
  (~ first_cook_scope EggNurbs EggNurbs /\
   forall p ti tj,
     ~ I_ok (MkNurbs locked_nurbs_A) (MkNurbs locked_nurbs_B)
          (IHit p ti tj)).
Proof.
  left.
  split; [exact nurbs_egg_first_cook_scope|].
  split; [exact interpolant_pair_mknurbs|].
  split; [exact locked_mknurbs_I_ok|].
  split; [exact cooked_mknurbs_try|].
  split; [exact cooked_mknurbs_shares|].
  split; [reflexivity|].
  split; [exact mknurbs_tag_still_decline|].
  split; [exact mknurbs_mixed_still_decline|].
  split; [exact nurbs_chord_not_first_cook_scope|].
  split; [exact ellipse_ellipse_not_first_scope|].
  exact cook_loop_is_obligation.
Qed.

Print Assumptions locked_nurbs_A_at_ti.
Print Assumptions locked_nurbs_B_at_tj.
Print Assumptions locked_mknurbs_I_ok.
Print Assumptions cooked_mknurbs_try.
Print Assumptions cook_hit_nurbs_shares_hen.
Print Assumptions cooked_mknurbs_shares.
Print Assumptions cooked_mknurbs_children_are_nurbs.
Print Assumptions interpolant_pair_mknurbs.
Print Assumptions mknurbs_mixed_still_decline.
Print Assumptions locked_payload_egg_self_hit.
Print Assumptions ticket_0007_nurbs_first_cook_qed_or_qex.
