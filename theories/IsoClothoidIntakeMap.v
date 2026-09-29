(* ============================================================================
   NetTopologySuite.Proofs.IsoClothoidIntakeMap
   ----------------------------------------------------------------------------
   Walker face of normalizer 1 (claimId 0007-intake-mkclothoid,
   not reminted). intake_map on TClothoidIso is map_clothoid.
   Hit builds a cloth_wf egg by direct field copy. Red CST
   examples: missing measure, unexpected measure, sheared frame
   (cloth_wf still holds), tilted placement, degenerate window
   sd = ed, and non-positive scale. sample_iso is a Hit that
   is not the locked egg. A JTS triple other than example5
   declines ID_JtsClothoidNotYet. Horizontal Z drops loc z.
   The locked ISO fields evaluate as locked_clothoid_egg.
   No new witness.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance SheetHenCook IsoClothoidIntake IntakeWalker.
Import ListNotations.
Local Open Scope R_scope.

Lemma iso_intake_hit_wf : forall s f b,
  intake_map s (TClothoidIso f) = IntakeBag b ->
  exists e,
    try_iso_clothoid f = inr e /\
    b = clothoid_bag s e /\
    cloth_wf e /\
    bag_pts b = [cloth_eval e 0; cloth_eval e 1] /\
    cloth_sigma e = frame_hand (ic_ref1 f) (ic_ref2 f).
Proof.
  intros s f b H.
  unfold intake_map, intake_map_atom, map_clothoid in H.
  destruct (try_iso_clothoid f) as [r|e] eqn:Ht.
  - discriminate.
  - inversion H. subst b.
    destruct (try_iso_hit_wf f e Ht) as [Hwf [Heq [Hsig _]]].
    exists e.
    split; [reflexivity|].
    split; [reflexivity|].
    split; [exact Hwf|].
    split; [reflexivity|].
    exact Hsig.
Qed.

Lemma iso_missing_measure_declines :
  intake_map default_sheet (TClothoidIso missing_iso) =
    IntakeDecline ID_MissingMeasure.
Proof.
  unfold intake_map, intake_map_atom, map_clothoid, iso_fail_id.
  rewrite missing_try. reflexivity.
Qed.

Lemma iso_unexpected_measure_declines :
  intake_map default_sheet (TClothoidIso unexpected_iso) =
    IntakeDecline ID_UnexpectedMeasure.
Proof.
  unfold intake_map, intake_map_atom, map_clothoid, iso_fail_id.
  rewrite unexpected_try. reflexivity.
Qed.

Lemma iso_shear_frame_declines :
  intake_map default_sheet (TClothoidIso shear_iso) =
    IntakeDecline ID_NotSimilarityFrame /\
  cloth_wf shear_egg.
Proof.
  split.
  - unfold intake_map, intake_map_atom, map_clothoid, iso_fail_id.
    rewrite shear_try. reflexivity.
  - exact shear_cloth_wf.
Qed.

Lemma iso_degenerate_window_declines :
  intake_map default_sheet (TClothoidIso degenerate_iso) =
    IntakeDecline ID_DegenerateWindow.
Proof.
  unfold intake_map, intake_map_atom, map_clothoid, iso_fail_id.
  rewrite degenerate_try. reflexivity.
Qed.

Lemma iso_nonpositive_scale_declines :
  intake_map default_sheet (TClothoidIso nonpos_iso) =
    IntakeDecline ID_NonPositiveScale.
Proof.
  unfold intake_map, intake_map_atom, map_clothoid, iso_fail_id.
  rewrite nonpos_try. reflexivity.
Qed.

Lemma iso_tilted_placement_declines :
  intake_map default_sheet (TClothoidIso tilted_iso) =
    IntakeDecline ID_TiltedPlacement /\
  similarity_ok (ic_ref1 tilted_iso) (ic_ref2 tilted_iso) = true.
Proof.
  split.
  - unfold intake_map, intake_map_atom, map_clothoid, iso_fail_id.
    rewrite tilted_try. reflexivity.
  - unfold tilted_iso. exact unit_east_sim.
Qed.

Lemma iso_horizontal_z_hits :
  intake_map default_sheet (TClothoidIso flat_z_iso) =
    IntakeBag (clothoid_bag default_sheet locked_clothoid_egg).
Proof.
  unfold intake_map, intake_map_atom, map_clothoid.
  rewrite flat_z_try. reflexivity.
Qed.

Lemma iso_sample_intake_hits :
  intake_map default_sheet (TClothoidIso sample_iso) =
    IntakeBag (clothoid_bag default_sheet sample_egg) /\
  sample_egg <> locked_clothoid_egg /\
  cloth_wf sample_egg.
Proof.
  split.
  - unfold intake_map, intake_map_atom, map_clothoid.
    rewrite sample_try. reflexivity.
  - split; [exact sample_not_locked|exact sample_wf].
Qed.

(* LOCATION z is elevation. Two records that differ only there agree. *)
Definition with_loc_z (f : IsoClothoid) (z : R) : IsoClothoid :=
  mkIsoClothoid (ic_dim f) (ic_loc f) z
    (ic_ref1 f) (ic_ref1_z f) (ic_ref2 f) (ic_ref2_z f)
    (ic_A f) (ic_sd f) (ic_ed f) (ic_m0 f) (ic_m1 f).

Lemma loc_z_same_result : forall s f z1 z2,
  try_iso_clothoid (with_loc_z f z1) =
    try_iso_clothoid (with_loc_z f z2) /\
  intake_map s (TClothoidIso (with_loc_z f z1)) =
    intake_map s (TClothoidIso (with_loc_z f z2)).
Proof.
  intros s f z1 z2.
  unfold with_loc_z, try_iso_clothoid, intake_map, intake_map_atom,
    map_clothoid.
  split; reflexivity.
Qed.

(* Next to sample_not_locked: another triple is not the locked bag. *)
Lemma jts_other_triple_declines :
  intake_map default_sheet (TClothoidJts 0 0 1) =
    IntakeDecline ID_JtsClothoidNotYet.
Proof.
  unfold intake_map, intake_map_atom, map_jts_clothoid.
  rewrite jts_is_example5_other. reflexivity.
Qed.

Lemma locked_iso_intake_eval : forall t,
  exists e,
    intake_map default_sheet (TClothoidIso locked_iso_clothoid) =
      IntakeBag (clothoid_bag default_sheet e) /\
    e = locked_clothoid_egg /\
    cloth_eval e t = cloth_eval locked_clothoid_egg t.
Proof.
  intro t. exists locked_clothoid_egg.
  split; [exact iso_clothoid_maps|].
  split; reflexivity.
Qed.

Print Assumptions iso_intake_hit_wf.
Print Assumptions iso_missing_measure_declines.
Print Assumptions iso_unexpected_measure_declines.
Print Assumptions iso_shear_frame_declines.
Print Assumptions iso_degenerate_window_declines.
Print Assumptions iso_nonpositive_scale_declines.
Print Assumptions iso_tilted_placement_declines.
Print Assumptions iso_horizontal_z_hits.
Print Assumptions iso_sample_intake_hits.
Print Assumptions loc_z_same_result.
Print Assumptions jts_other_triple_declines.
Print Assumptions locked_iso_intake_eval.
