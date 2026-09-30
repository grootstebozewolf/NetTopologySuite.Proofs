(* ============================================================================
   NetTopologySuite.Proofs.IntakeWalkerClothoid
   ----------------------------------------------------------------------------
   Clothoid half of the first-slice walker (claimId
   0007-intake-mkclothoid, not reminted). Split out of
   IntakeWalker so that module stays under the 1234-line gate.
   Definitions (clothoid_bag, map_clothoid, intake_map) stay in
   IntakeWalker. This file is the lemmas and the ticket.

   3-axiom host. No Admitted / Axiom / Parameter.
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals List.
From NTS.Proofs Require Import SheetHenCook IntakeWalker IsoClothoidIntake IntakeSpiralJts.
Import ListNotations.
Local Open Scope R_scope.
Local Open Scope list_scope.

(* Locked fixture: gamma ends of locked_clothoid_egg, not a chord seed. *)
Lemma locked_cloth_intake_endpoints :
  bag_pts (clothoid_bag default_sheet locked_clothoid_egg) =
    [cloth_eval locked_clothoid_egg 0;
     cloth_eval locked_clothoid_egg 1].
Proof.
  reflexivity.
Qed.

Lemma iso_clothoid_maps :
  intake_map default_sheet (TClothoidIso locked_iso_clothoid) =
    IntakeBag (clothoid_bag default_sheet locked_clothoid_egg).
Proof.
  unfold intake_map, intake_map_atom, map_clothoid.
  rewrite locked_iso_try. reflexivity.
Qed.

Lemma jts_clothoid_maps :
  intake_map default_sheet example5_jts_cst =
    IntakeBag (clothoid_bag default_sheet locked_clothoid_egg).
Proof.
  unfold intake_map, intake_map_atom, map_jts_clothoid, map_clothoid,
    example5_jts_cst.
  rewrite classify_example5, locked_iso_try. reflexivity.
Qed.

Lemma ogc_iso_clothoid_same_bag :
  intake_map default_sheet example5_jts_cst =
    intake_map default_sheet (TClothoidIso locked_iso_clothoid).
Proof.
  rewrite jts_clothoid_maps, iso_clothoid_maps. reflexivity.
Qed.

Lemma ogc_iso_clothoid_same_mkclothoid :
  intake_map default_sheet example5_jts_cst =
    IntakeBag (clothoid_bag default_sheet locked_clothoid_egg) /\
  intake_map default_sheet (TClothoidIso locked_iso_clothoid) =
    IntakeBag (clothoid_bag default_sheet locked_clothoid_egg).
Proof.
  split; [exact jts_clothoid_maps|exact iso_clothoid_maps].
Qed.

Lemma iso_clothoid_chickens_mkclothoid :
  exists b c e,
    intake_map default_sheet (TClothoidIso locked_iso_clothoid) = IntakeBag b /\
    In c (bag_chickens b) /\
    ck_egg c = MkClothoid e /\
    egg_class (ck_egg c) = EggClothoid.
Proof.
  rewrite iso_clothoid_maps.
  exists (clothoid_bag default_sheet locked_clothoid_egg).
  exists (mkChicken 0%nat 1%nat (MkClothoid locked_clothoid_egg)).
  exists locked_clothoid_egg.
  split; [reflexivity|].
  split; [now left|].
  split; reflexivity.
Qed.

Lemma jts_clothoid_chickens_mkclothoid :
  exists b c e,
    intake_map default_sheet example5_jts_cst = IntakeBag b /\
    In c (bag_chickens b) /\
    ck_egg c = MkClothoid e.
Proof.
  rewrite jts_clothoid_maps.
  exists (clothoid_bag default_sheet locked_clothoid_egg).
  exists (mkChicken 0%nat 1%nat (MkClothoid locked_clothoid_egg)).
  exists locked_clothoid_egg.
  split; [reflexivity|].
  split; [now left|].
  reflexivity.
Qed.

Lemma clothoid_intake_not_chord_demote :
  intake_map default_sheet (TClothoidIso locked_iso_clothoid) <>
    IntakeBag (map_ls default_sheet
      [cloth_p0 locked_clothoid_egg; cloth_p1 locked_clothoid_egg]) /\
  intake_map default_sheet example5_jts_cst <>
    IntakeBag (map_ls default_sheet
      [cloth_p0 locked_clothoid_egg; cloth_p1 locked_clothoid_egg]).
Proof.
  rewrite iso_clothoid_maps, jts_clothoid_maps.
  split; discriminate.
Qed.

Lemma clothoid_intake_not_iso_decline :
  intake_map default_sheet (TClothoidIso locked_iso_clothoid) <>
    IntakeDecline ID_IsoClothoid /\
  intake_map default_sheet example5_jts_cst <>
    IntakeDecline ID_MkOutOfScope.
Proof.
  rewrite iso_clothoid_maps, jts_clothoid_maps.
  split; discriminate.
Qed.

Lemma example5_cc_bags_both_clothoid :
  intake_map default_sheet example5_cc_both_clothoid_cst =
    IntakeBag (map_cc_example5 default_sheet).
Proof.
  unfold intake_map, example5_cc_both_clothoid_cst, intake_map_members.
  simpl. unfold intake_map_atom, map_jts_clothoid, map_clothoid.
  rewrite classify_example5, !locked_iso_try.
  unfold map_cc_example5. reflexivity.
Qed.

Lemma example5_cc_not_iso_decline :
  intake_map default_sheet example5_cc_both_clothoid_cst <>
    IntakeDecline ID_IsoClothoid.
Proof.
  rewrite example5_cc_bags_both_clothoid.
  discriminate.
Qed.

Lemma example5_cc_has_mkclothoid :
  exists b c e,
    intake_map default_sheet example5_cc_both_clothoid_cst = IntakeBag b /\
    In c (bag_chickens b) /\
    ck_egg c = MkClothoid e /\
    egg_class (ck_egg c) = EggClothoid.
Proof.
  rewrite example5_cc_bags_both_clothoid.
  exists (map_cc_example5 default_sheet).
  exists (shift_chicken 2%nat
            (mkChicken 0%nat 1%nat (MkClothoid locked_clothoid_egg))).
  exists locked_clothoid_egg.
  split; [reflexivity|].
  unfold map_cc_example5, append_bags, clothoid_bag, shift_chicken.
  simpl.
  split.
  - right. left. reflexivity.
  - split; reflexivity.
Qed.

(* WITNESS {"claimId":"0007-intake-mkclothoid","topic":"overlay","lemma":"ticket_0007_intake_mkclothoid_qed_or_qex","title":"Intake maps ISO and JTS clothoid CST to the same MkClothoid SHC bag (QED) or MkClothoid stays QEX and ISO clothoid Declines ID_IsoClothoid (QEX); discharged QED; one host constructor; OGC\equiv ISO same egg; no silent chord demote; first-cook Hit is the clothoid first-cook letter","file":"theories/IntakeWalkerClothoid.v","witness":"0007-intake-mkclothoid","board":"ADR-0007"} *)
Theorem ticket_0007_intake_mkclothoid_qed_or_qex :
  (intake_ctor_inhabits IntakeMkClothoid /\
   intake_map default_sheet example5_jts_cst =
     IntakeBag (clothoid_bag default_sheet locked_clothoid_egg) /\
   intake_map default_sheet (TClothoidIso locked_iso_clothoid) =
     IntakeBag (clothoid_bag default_sheet locked_clothoid_egg) /\
   intake_map default_sheet example5_jts_cst =
     intake_map default_sheet (TClothoidIso locked_iso_clothoid) /\
   exists b c e,
     intake_map default_sheet (TClothoidIso locked_iso_clothoid) = IntakeBag b /\
     In c (bag_chickens b) /\
     ck_egg c = MkClothoid e /\
     egg_class (ck_egg c) = EggClothoid /\
   intake_map default_sheet example5_cc_both_clothoid_cst =
     IntakeBag (map_cc_example5 default_sheet) /\
   intake_map default_sheet example5_cc_both_clothoid_cst <>
     IntakeDecline ID_IsoClothoid)
  \/
   (~ intake_ctor_inhabits IntakeMkClothoid /\
   intake_map default_sheet (TClothoidIso locked_iso_clothoid) =
     IntakeDecline ID_IsoClothoid).
Proof.
  left.
  split; [exact intake_mkclothoid_inhabits|].
  split; [exact jts_clothoid_maps|].
  split; [exact iso_clothoid_maps|].
  split; [exact ogc_iso_clothoid_same_bag|].
  destruct iso_clothoid_chickens_mkclothoid as [b [c [e [Hb [Hin [He Hcls]]]]]].
  exists b. exists c. exists e.
  split; [exact Hb|].
  split; [exact Hin|].
  split; [exact He|].
  split; [exact Hcls|].
  split; [exact example5_cc_bags_both_clothoid|].
  exact example5_cc_not_iso_decline.
Qed.

Print Assumptions locked_cloth_intake_endpoints.
Print Assumptions iso_clothoid_maps.
Print Assumptions jts_clothoid_maps.
Print Assumptions ogc_iso_clothoid_same_bag.
Print Assumptions ogc_iso_clothoid_same_mkclothoid.
Print Assumptions iso_clothoid_chickens_mkclothoid.
Print Assumptions jts_clothoid_chickens_mkclothoid.
Print Assumptions clothoid_intake_not_chord_demote.
Print Assumptions clothoid_intake_not_iso_decline.
Print Assumptions example5_cc_bags_both_clothoid.
Print Assumptions example5_cc_not_iso_decline.
Print Assumptions example5_cc_has_mkclothoid.
Print Assumptions ticket_0007_intake_mkclothoid_qed_or_qex.
