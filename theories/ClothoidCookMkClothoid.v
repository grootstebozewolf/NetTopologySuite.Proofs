(* ============================================================================
   NetTopologySuite.Proofs.ClothoidCookMkClothoid
   ----------------------------------------------------------------------------
   ADR-0007 letter: clothoid×clothoid first-cook / Hit arm
   (claimId 0007-clothoid-first-cook).

   Host MkClothoid pairs are interpolant_pair. first_cook_scope
   includes EggClothoid × EggClothoid. I_ok Hits two MkClothoid
   chickens on a locked crossing pair via on_cloth (Fresnel-free
   chord-parameter interpolant). try_cook_hit mints MkClothoid
   children — not a silent demote to MkChord.

   Locked fixture reuses the SheetHenCook unit-square-diagonal
   geometry already Qed as a proper cross (RelateClothoid chord
   seed). Eggs carry JTS (k0, k1, L). Not Fresnel-as-noding.

   MkOutOfScope EggClothoid stays Decline. Mixed clothoid×chord
   stays Decline. NURBS / SIN / ellipse / spiral / geodesic stay
   out of first cook. ρ / Campaign / Fresnel-as-noding stay parked.

   WITNESS topic: overlay · claimId: 0007-clothoid-first-cook
   witness: 0007-clothoid-first-cook
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
(* Locked MkClothoid eggs. Same endpoints as diag_ab / diag_cd.               *)
(* -------------------------------------------------------------------------- *)

Definition locked_cloth_A : ClothoidEgg :=
  mkClothoidEgg (mkPoint 0 0) (mkPoint 2 2) 0 (5 / 1000) 80.

Definition locked_cloth_B : ClothoidEgg :=
  mkClothoidEgg (mkPoint 0 2) (mkPoint 2 0) 0 (5 / 1000) 80.

Definition locked_cloth_hit_pt : Point := mkPoint 1 1.
Definition locked_cloth_ti : R := 1 / 2.
Definition locked_cloth_tj : R := 1 / 2.

Definition locked_cloth_ck1 : Chicken :=
  mkChicken 0%nat 1%nat (MkClothoid locked_cloth_A).

Definition locked_cloth_ck2 : Chicken :=
  mkChicken 2%nat 3%nat (MkClothoid locked_cloth_B).

Lemma locked_cloth_ti_in_01 : 0 <= locked_cloth_ti <= 1.
Proof.
  unfold locked_cloth_ti. lra.
Qed.

Lemma locked_cloth_tj_in_01 : 0 <= locked_cloth_tj <= 1.
Proof.
  unfold locked_cloth_tj. lra.
Qed.

Lemma locked_cloth_A_at_ti :
  cloth_eval locked_cloth_A locked_cloth_ti = locked_cloth_hit_pt.
Proof.
  unfold cloth_eval, locked_cloth_A, locked_cloth_ti, locked_cloth_hit_pt.
  cbn [px py cloth_p0 cloth_p1].
  apply (f_equal2 mkPoint); field.
Qed.

Lemma locked_cloth_B_at_tj :
  cloth_eval locked_cloth_B locked_cloth_tj = locked_cloth_hit_pt.
Proof.
  unfold cloth_eval, locked_cloth_B, locked_cloth_tj, locked_cloth_hit_pt.
  cbn [px py cloth_p0 cloth_p1].
  apply (f_equal2 mkPoint); field.
Qed.

Lemma locked_on_cloth_A :
  on_cloth locked_cloth_A locked_cloth_ti locked_cloth_hit_pt.
Proof.
  unfold on_cloth. split; [exact locked_cloth_ti_in_01|].
  symmetry. exact locked_cloth_A_at_ti.
Qed.

Lemma locked_on_cloth_B :
  on_cloth locked_cloth_B locked_cloth_tj locked_cloth_hit_pt.
Proof.
  unfold on_cloth. split; [exact locked_cloth_tj_in_01|].
  symmetry. exact locked_cloth_B_at_tj.
Qed.

(* -------------------------------------------------------------------------- *)
(* Host I_ok Hit and try_cook_hit mint on the locked MkClothoid pair.         *)
(* -------------------------------------------------------------------------- *)

Lemma locked_mkclothoid_I_ok :
  I_ok (MkClothoid locked_cloth_A) (MkClothoid locked_cloth_B)
       (IHit locked_cloth_hit_pt locked_cloth_ti locked_cloth_tj).
Proof.
  unfold I_ok.
  split; [exact locked_on_cloth_A | exact locked_on_cloth_B].
Qed.

Definition locked_mkclothoid_hit : IResult :=
  IHit locked_cloth_hit_pt locked_cloth_ti locked_cloth_tj.

Definition cooked_mkclothoid : CookedPair :=
  cook_hit_clothoids locked_cloth_ck1 locked_cloth_ck2
    locked_cloth_A locked_cloth_B locked_cloth_ti locked_cloth_tj
    crossing_hen.

Lemma cook_hit_clothoids_shares_hen :
  forall c1 c2 e1 e2 ti tj h,
    cooked_shares_hen (cook_hit_clothoids c1 c2 e1 e2 ti tj h).
Proof.
  intros. repeat split; reflexivity.
Qed.

Lemma cooked_mkclothoid_shares :
  cooked_shares_hen cooked_mkclothoid.
Proof.
  apply cook_hit_clothoids_shares_hen.
Qed.

Lemma cooked_mkclothoid_try :
  try_cook_hit locked_cloth_ck1 locked_cloth_ck2
    locked_mkclothoid_hit crossing_hen = Some cooked_mkclothoid.
Proof.
  reflexivity.
Qed.

Lemma cooked_mkclothoid_children_are_clothoid :
  egg_class (ck_egg (cp_left1 cooked_mkclothoid)) = EggClothoid /\
  egg_class (ck_egg (cp_right1 cooked_mkclothoid)) = EggClothoid /\
  egg_class (ck_egg (cp_left2 cooked_mkclothoid)) = EggClothoid /\
  egg_class (ck_egg (cp_right2 cooked_mkclothoid)) = EggClothoid.
Proof.
  repeat split; reflexivity.
Qed.

Lemma interpolant_pair_mkclothoid :
  interpolant_pair (MkClothoid locked_cloth_A) (MkClothoid locked_cloth_B).
Proof.
  exact I.
Qed.

Lemma mkclothoid_tag_still_decline :
  I_ok (MkOutOfScope EggClothoid) (MkOutOfScope EggClothoid) IDecline.
Proof.
  exact clothoid_decline_I_ok.
Qed.

Lemma mkclothoid_tag_hit_false :
  forall p ti tj,
    ~ I_ok (MkOutOfScope EggClothoid) (MkOutOfScope EggClothoid)
         (IHit p ti tj).
Proof.
  intros p ti tj H. exact H.
Qed.

Lemma mkclothoid_mixed_still_decline :
  I_ok (MkChord hor_bot) (MkClothoid locked_cloth_A) IDecline.
Proof.
  unfold I_ok, interpolant_pair. intro H. exact H.
Qed.

Lemma clothoid_chord_not_first_cook_scope :
  ~ first_cook_scope EggClothoid EggChord.
Proof.
  intro H. exact H.
Qed.

Lemma mkclothoid_neq_mkchord_locked :
  MkClothoid locked_cloth_A <> MkChord diag_ab.
Proof.
  discriminate.
Qed.

(* Same-egg Hit on the intake locked record (sidecar ticket reuse). *)
Lemma locked_intake_egg_self_hit :
  I_ok (MkClothoid locked_clothoid_egg) (MkClothoid locked_clothoid_egg)
       (IHit (mkPoint (1 / 2) 0) (1 / 2) (1 / 2)).
Proof.
  unfold I_ok, on_cloth, cloth_eval, locked_clothoid_egg.
  cbn [px py cloth_p0 cloth_p1].
  split.
  - split; [lra|]. apply (f_equal2 mkPoint); field.
  - split; [lra|]. apply (f_equal2 mkPoint); field.
Qed.

(* WITNESS {"claimId":"0007-clothoid-first-cook","topic":"overlay","lemma":"locked_mkclothoid_I_ok","title":"Host I_ok Hits two MkClothoid chickens on the locked crossing clothoid pair","file":"theories/ClothoidCookMkClothoid.v","witness":"0007-clothoid-first-cook","board":"ADR-0007"} *)

(* WITNESS {"claimId":"0007-clothoid-first-cook","topic":"overlay","lemma":"cooked_mkclothoid_try","title":"try_cook_hit mints MkClothoid hens on the locked clothoid Hit","file":"theories/ClothoidCookMkClothoid.v","witness":"0007-clothoid-first-cook","board":"ADR-0007"} *)

(* WITNESS {"claimId":"0007-clothoid-first-cook","topic":"overlay","lemma":"ticket_0007_clothoid_first_cook_qed_or_qex","title":"Clothoid times clothoid is first cook with a locked MkClothoid IHit that try_cook_hit mints (QED) or clothoid times clothoid stays QEX (QEX); discharged QED; tags and mixed stay Decline; Fresnel-as-noding / Campaign / rho stay parked","file":"theories/ClothoidCookMkClothoid.v","witness":"0007-clothoid-first-cook","board":"ADR-0007"} *)
Theorem ticket_0007_clothoid_first_cook_qed_or_qex :
  (first_cook_scope EggClothoid EggClothoid /\
   interpolant_pair (MkClothoid locked_cloth_A) (MkClothoid locked_cloth_B) /\
   I_ok (MkClothoid locked_cloth_A) (MkClothoid locked_cloth_B)
        (IHit locked_cloth_hit_pt locked_cloth_ti locked_cloth_tj) /\
   try_cook_hit locked_cloth_ck1 locked_cloth_ck2
     locked_mkclothoid_hit crossing_hen = Some cooked_mkclothoid /\
   cooked_shares_hen cooked_mkclothoid /\
   egg_class (ck_egg (cp_left1 cooked_mkclothoid)) = EggClothoid /\
   I_ok (MkOutOfScope EggClothoid) (MkOutOfScope EggClothoid) IDecline /\
   I_ok (MkChord hor_bot) (MkClothoid locked_cloth_A) IDecline /\
   ~ first_cook_scope EggClothoid EggChord /\
   ~ first_cook_scope EggNurbs EggNurbs /\
   cook_loop_status = LoopObligation)
  \/
  (~ first_cook_scope EggClothoid EggClothoid /\
   forall p ti tj,
     ~ I_ok (MkClothoid locked_cloth_A) (MkClothoid locked_cloth_B)
          (IHit p ti tj)).
Proof.
  left.
  split; [exact clothoid_egg_first_cook_scope|].
  split; [exact interpolant_pair_mkclothoid|].
  split; [exact locked_mkclothoid_I_ok|].
  split; [exact cooked_mkclothoid_try|].
  split; [exact cooked_mkclothoid_shares|].
  split; [reflexivity|].
  split; [exact mkclothoid_tag_still_decline|].
  split; [exact mkclothoid_mixed_still_decline|].
  split; [exact clothoid_chord_not_first_cook_scope|].
  split; [exact nurbs_nurbs_not_first_scope|].
  exact cook_loop_is_obligation.
Qed.

Print Assumptions locked_cloth_A_at_ti.
Print Assumptions locked_cloth_B_at_tj.
Print Assumptions locked_mkclothoid_I_ok.
Print Assumptions cooked_mkclothoid_try.
Print Assumptions cook_hit_clothoids_shares_hen.
Print Assumptions cooked_mkclothoid_shares.
Print Assumptions cooked_mkclothoid_children_are_clothoid.
Print Assumptions interpolant_pair_mkclothoid.
Print Assumptions mkclothoid_mixed_still_decline.
Print Assumptions locked_intake_egg_self_hit.
Print Assumptions ticket_0007_clothoid_first_cook_qed_or_qex.
