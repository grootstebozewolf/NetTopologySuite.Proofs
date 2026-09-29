(* ============================================================================
   NetTopologySuite.Proofs.IsoClothoidIntake
   ----------------------------------------------------------------------------
   Normalizer 1 for ISO CLOTHOID (claimId 0007-intake-mkclothoid,
   not reminted). Direct field copy into the inflection-placed
   ClothoidEgg of SheetHenClothoidEgg. This mapping is OUR
   normalisation, not an ISO formula: LOCATION, ref1, ref2, scale
   A, distances sd and ed, and the optional measure pair are stored
   as cloth_place / cloth_A / cloth_sd / cloth_ed / cloth_m0 /
   cloth_m1. Handedness is not a field. h = sign(ref1 × ref2),
   the same Rle_dec test as cloth_sigma (0 would be +1; a
   similarity frame has cross ≠ 0). sd and ed are arc length
   from the inflection (our reading; GML's Clothoid uses the
   normalized Fresnel parameter, s = A·√π·t).

   Planar similarity frame, required here and not by cloth_wf.
   cloth_wf accepts any nonzero ref1 whose cross with ref2 is
   nonzero, so a sheared pair is read as orthonormal by cos0/sin0.
   Intake declines that. similarity_ok is: ref1 · ref2 = 0,
   |ref1|² = |ref2|², and |ref1|² ≠ 0 (orthonormal up to one
   common scale, reflection allowed). Otherwise
   ICF_NotSimilarityFrame.

   Measures are the walker's job. dim? and the optional
   STARTM/ENDM pair are independent in wktParser.g4. dim with M
   (WD_M or WD_ZM) requires both measures, else
   ICF_MissingMeasure. No M (WD_XY or WD_Z) with either measure
   present is ICF_UnexpectedMeasure. Success is both None or both
   Some, which is rule 8. A half pair never builds an egg.

   Ref z is carried so a tilted placement is not read as planar.
   Both ref z = 0 is horizontal (WD_Z / WD_ZM accepted; loc z is
   elevation and is not copied). Any nonzero ref z is
   ICF_TiltedPlacement. XY and M fixtures store z = 0.

   sd = ed is ICF_DegenerateWindow. The host still has a constant
   gamma on that window; intake does not accept it. A ≤ 0 is
   ICF_NonPositiveScale so a Hit egg meets cloth_wf.

   Check order: measures, horizontal refs, similarity, A > 0,
   sd ≠ ed. jts_is_example5 is the example5 triple
   (0, 5/1000, 80) only; other JTS triples are the walker's
   ID_JtsClothoidNotYet. SPIRALCURVE and normalizer 2 are out
   of scope. No FTC. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance SheetHenClothoidEgg.
Local Open Scope R_scope.

Inductive WktDim : Type :=
| WD_XY
| WD_Z
| WD_M
| WD_ZM.

Inductive IsoClothoidFail : Type :=
| ICF_MissingMeasure
| ICF_UnexpectedMeasure
| ICF_NotSimilarityFrame
| ICF_NonPositiveScale
| ICF_DegenerateWindow
| ICF_TiltedPlacement.

Record IsoClothoid : Type := mkIsoClothoid {
  ic_dim : WktDim;
  ic_loc : Point;
  ic_loc_z : R;
  ic_ref1 : Point;
  ic_ref1_z : R;
  ic_ref2 : Point;
  ic_ref2_z : R;
  ic_A : R;
  ic_sd : R;
  ic_ed : R;
  ic_m0 : option R;
  ic_m1 : option R
}.

Definition frame_dot (a b : Point) : R :=
  px a * px b + py a * py b.

Definition frame_h2 (a : Point) : R :=
  px a * px a + py a * py a.

Definition frame_cross (a b : Point) : R :=
  px a * py b - py a * px b.

(* sign(ref1 × ref2). Zero maps to +1, matching cloth_sigma. *)
Definition frame_hand (a b : Point) : R :=
  if Rle_dec 0 (frame_cross a b) then 1 else -1.

Definition dim_has_m (d : WktDim) : bool :=
  match d with
  | WD_M | WD_ZM => true
  | WD_XY | WD_Z => false
  end.

Definition measures_fail (d : WktDim) (m0 m1 : option R)
  : option IsoClothoidFail :=
  match dim_has_m d, m0, m1 with
  | true, Some _, Some _ => None
  | true, _, _ => Some ICF_MissingMeasure
  | false, None, None => None
  | false, _, _ => Some ICF_UnexpectedMeasure
  end.

(* Both ref z = 0: the placement is horizontal. loc z is elevation. *)
Definition refs_horizontal (z1 z2 : R) : bool :=
  if Req_EM_T z1 0 then
    if Req_EM_T z2 0 then true else false
  else false.

Definition similarity_ok (a b : Point) : bool :=
  if Req_EM_T (frame_dot a b) 0 then
    if Req_EM_T (frame_h2 a) (frame_h2 b) then
      if Req_EM_T (frame_h2 a) 0 then false else true
    else false
  else false.

Definition try_iso_clothoid (f : IsoClothoid) : IsoClothoidFail + ClothoidEgg :=
  match measures_fail (ic_dim f) (ic_m0 f) (ic_m1 f) with
  | Some r => inl r
  | None =>
      if refs_horizontal (ic_ref1_z f) (ic_ref2_z f) then
        if similarity_ok (ic_ref1 f) (ic_ref2 f) then
          if Rle_dec (ic_A f) 0 then inl ICF_NonPositiveScale
          else if Req_EM_T (ic_sd f) (ic_ed f) then inl ICF_DegenerateWindow
          else inr (mk_cloth (mkAffPlace (ic_loc f) (ic_ref1 f) (ic_ref2 f))
                     (ic_A f) (ic_sd f) (ic_ed f) (ic_m0 f) (ic_m1 f))
        else inl ICF_NotSimilarityFrame
      else inl ICF_TiltedPlacement
  end.

(* example5.txt JTS CLOTHOID (0, 0.005, 80). Other triples are not this. *)
Definition example5_jts_k0 : R := 0.
Definition example5_jts_k1 : R := 5 / 1000.
Definition example5_jts_L : R := 80.

Definition jts_is_example5 (k0 k1 len : R) : bool :=
  if Req_EM_T k0 example5_jts_k0 then
    if Req_EM_T k1 example5_jts_k1 then
      if Req_EM_T len example5_jts_L then true else false
    else false
  else false.

Lemma frame_lagrange : forall a b,
  frame_cross a b * frame_cross a b + frame_dot a b * frame_dot a b =
  frame_h2 a * frame_h2 b.
Proof.
  intros [ax ay] [bx by_].
  unfold frame_cross, frame_dot, frame_h2. cbn. ring.
Qed.

Lemma similarity_cross_nz : forall a b,
  frame_dot a b = 0 ->
  frame_h2 a = frame_h2 b ->
  frame_h2 a <> 0 ->
  frame_cross a b <> 0.
Proof.
  intros a b Hd Heq Hnz Hc.
  pose proof (frame_lagrange a b) as H.
  rewrite Hd, Hc, Heq in H. nra.
Qed.

Lemma similarity_ok_intro : forall a b,
  frame_dot a b = 0 ->
  frame_h2 a = frame_h2 b ->
  frame_h2 a <> 0 ->
  similarity_ok a b = true.
Proof.
  intros a b Hd Heq Hnz.
  unfold similarity_ok.
  destruct (Req_EM_T (frame_dot a b) 0) as [_|Hn]; [|contradiction].
  destruct (Req_EM_T (frame_h2 a) (frame_h2 b)) as [_|Hn]; [|contradiction].
  destruct (Req_EM_T (frame_h2 a) 0) as [Hz|Hnn]; [contradiction|].
  reflexivity.
Qed.

Lemma similarity_ok_spec : forall a b,
  similarity_ok a b = true ->
  frame_dot a b = 0 /\ frame_h2 a = frame_h2 b /\ frame_h2 a <> 0.
Proof.
  intros a b H.
  unfold similarity_ok in H.
  destruct (Req_EM_T (frame_dot a b) 0) as [Hd|Hd].
  - destruct (Req_EM_T (frame_h2 a) (frame_h2 b)) as [He|He].
    + destruct (Req_EM_T (frame_h2 a) 0) as [Hz|Hnz].
      * discriminate.
      * split; [exact Hd|]. split; [exact He|exact Hnz].
    + discriminate.
  - discriminate.
Qed.

Lemma measures_none_coupled : forall d m0 m1,
  measures_fail d m0 m1 = None ->
  (m0 = None /\ m1 = None) \/
  (exists x y, m0 = Some x /\ m1 = Some y).
Proof.
  intros d m0 m1 H.
  destruct d; destruct m0 as [a|]; destruct m1 as [b|];
    simpl in H; try discriminate.
  - left. split; reflexivity.
  - left. split; reflexivity.
  - right. exists a, b. split; reflexivity.
  - right. exists a, b. split; reflexivity.
Qed.

Lemma refs_horizontal_spec : forall z1 z2,
  refs_horizontal z1 z2 = true -> z1 = 0 /\ z2 = 0.
Proof.
  intros z1 z2 H.
  unfold refs_horizontal in H.
  destruct (Req_EM_T z1 0) as [H1|H1]; [|discriminate].
  destruct (Req_EM_T z2 0) as [H2|H2]; [|discriminate].
  split; assumption.
Qed.

Lemma refs_zero_horizontal : refs_horizontal 0 0 = true.
Proof.
  unfold refs_horizontal.
  destruct (Req_EM_T 0 0) as [_|H]; [|exfalso; apply H; reflexivity].
  destruct (Req_EM_T 0 0) as [_|H]; [|exfalso; apply H; reflexivity].
  reflexivity.
Qed.

Lemma try_iso_hit_wf : forall f e,
  try_iso_clothoid f = inr e ->
  cloth_wf e /\
  e = mk_cloth (mkAffPlace (ic_loc f) (ic_ref1 f) (ic_ref2 f))
        (ic_A f) (ic_sd f) (ic_ed f) (ic_m0 f) (ic_m1 f) /\
  cloth_sigma e = frame_hand (ic_ref1 f) (ic_ref2 f) /\
  ic_sd f <> ic_ed f /\
  ic_ref1_z f = 0 /\
  ic_ref2_z f = 0.
Proof.
  intros f e H.
  unfold try_iso_clothoid in H.
  destruct (measures_fail (ic_dim f) (ic_m0 f) (ic_m1 f)) as [r|] eqn:Hm.
  - discriminate.
  - destruct (refs_horizontal (ic_ref1_z f) (ic_ref2_z f)) eqn:Hz.
    + destruct (similarity_ok (ic_ref1 f) (ic_ref2 f)) eqn:Hs.
      * destruct (Rle_dec (ic_A f) 0) as [Ha|Ha].
        -- discriminate.
        -- destruct (Req_EM_T (ic_sd f) (ic_ed f)) as [Heq|Hneq].
           ** discriminate.
           ** inversion H. subst e.
              destruct (similarity_ok_spec _ _ Hs) as [Hd [Hlen Hnz]].
              destruct (refs_horizontal_spec _ _ Hz) as [Hz1 Hz2].
              assert (Hc : frame_cross (ic_ref1 f) (ic_ref2 f) <> 0).
              { apply similarity_cross_nz; assumption. }
              split.
              { apply cloth_wf_mk.
                - apply Rnot_le_lt. exact Ha.
                - unfold aff_h2. cbn. exact Hnz.
                - unfold aff_cross. cbn. exact Hc.
                - apply (measures_none_coupled (ic_dim f) (ic_m0 f) (ic_m1 f)).
                  exact Hm. }
              split. { reflexivity. }
              split.
              { unfold cloth_sigma, frame_hand, cloth_cross, aff_cross. cbn.
                reflexivity. }
              split. { exact Hneq. }
              split; assumption.
      * discriminate.
    + discriminate.
Qed.

(* Locked #883 egg, as ISO fields. Unit east frame, A = 1, window
   [0,1], unmeasured XY. *)
Definition locked_iso_clothoid : IsoClothoid :=
  mkIsoClothoid WD_XY (mkPoint 0 0) 0 (mkPoint 1 0) 0 (mkPoint 0 1) 0
    1 0 1 None None.

Lemma unit_east_sim :
  similarity_ok (mkPoint 1 0) (mkPoint 0 1) = true.
Proof.
  apply similarity_ok_intro; unfold frame_dot, frame_h2; cbn.
  - ring.
  - ring.
  - lra.
Qed.

Lemma locked_iso_try :
  try_iso_clothoid locked_iso_clothoid = inr locked_clothoid_egg.
Proof.
  unfold try_iso_clothoid, locked_iso_clothoid. cbn.
  rewrite refs_zero_horizontal. rewrite unit_east_sim.
  destruct (Rle_dec 1 0) as [Ha|Ha]; [lra|].
  destruct (Req_EM_T 0 1) as [Hs|Hs]; [lra|].
  unfold locked_clothoid_egg, place_east. reflexivity.
Qed.

Lemma locked_iso_same_egg_eval : forall t e,
  try_iso_clothoid locked_iso_clothoid = inr e ->
  cloth_eval e t = cloth_eval locked_clothoid_egg t.
Proof.
  intros t e H. rewrite locked_iso_try in H.
  injection H as Heq. rewrite Heq. reflexivity.
Qed.

Definition missing_iso : IsoClothoid :=
  mkIsoClothoid WD_M (mkPoint 0 0) 0 (mkPoint 1 0) 0 (mkPoint 0 1) 0
    1 0 1 None None.

Lemma missing_try :
  try_iso_clothoid missing_iso = inl ICF_MissingMeasure.
Proof.
  unfold try_iso_clothoid, missing_iso. cbn. reflexivity.
Qed.

Definition unexpected_iso : IsoClothoid :=
  mkIsoClothoid WD_XY (mkPoint 0 0) 0 (mkPoint 1 0) 0 (mkPoint 0 1) 0
    1 0 1 (Some 0) (Some 1).

Lemma unexpected_try :
  try_iso_clothoid unexpected_iso = inl ICF_UnexpectedMeasure.
Proof.
  unfold try_iso_clothoid, unexpected_iso. cbn. reflexivity.
Qed.

(* Sheared refs: cloth_wf holds, similarity does not. *)
Definition shear_iso : IsoClothoid :=
  mkIsoClothoid WD_XY (mkPoint 0 0) 0 (mkPoint 2 0) 0 (mkPoint 1 1) 0
    1 0 1 None None.

Definition shear_egg : ClothoidEgg :=
  mk_cloth (mkAffPlace (mkPoint 0 0) (mkPoint 2 0) (mkPoint 1 1))
    1 0 1 None None.

Lemma shear_cloth_wf : cloth_wf shear_egg.
Proof.
  unfold shear_egg. apply cloth_wf_mk.
  - lra.
  - unfold aff_h2. cbn. lra.
  - unfold aff_cross. cbn. lra.
  - left. split; reflexivity.
Qed.

Lemma shear_try :
  try_iso_clothoid shear_iso = inl ICF_NotSimilarityFrame.
Proof.
  unfold try_iso_clothoid, shear_iso. cbn.
  rewrite refs_zero_horizontal.
  unfold similarity_ok.
  destruct (Req_EM_T (frame_dot (mkPoint 2 0) (mkPoint 1 1)) 0) as [H|H].
  - exfalso. unfold frame_dot in H. cbn in H. lra.
  - reflexivity.
Qed.

Definition degenerate_iso : IsoClothoid :=
  mkIsoClothoid WD_XY (mkPoint 0 0) 0 (mkPoint 1 0) 0 (mkPoint 0 1) 0
    1 0 0 None None.

Lemma degenerate_try :
  try_iso_clothoid degenerate_iso = inl ICF_DegenerateWindow.
Proof.
  unfold try_iso_clothoid, degenerate_iso. cbn.
  rewrite refs_zero_horizontal. rewrite unit_east_sim.
  destruct (Rle_dec 1 0) as [Ha|Ha]; [lra|].
  destruct (Req_EM_T 0 0) as [_|Hs]; [|exfalso; apply Hs; reflexivity].
  reflexivity.
Qed.

Definition nonpos_iso : IsoClothoid :=
  mkIsoClothoid WD_XY (mkPoint 0 0) 0 (mkPoint 1 0) 0 (mkPoint 0 1) 0
    0 0 1 None None.

Lemma nonpos_try :
  try_iso_clothoid nonpos_iso = inl ICF_NonPositiveScale.
Proof.
  unfold try_iso_clothoid, nonpos_iso. cbn.
  rewrite refs_zero_horizontal. rewrite unit_east_sim.
  destruct (Rle_dec 0 0) as [_|Ha]; [|exfalso; apply Ha; lra].
  reflexivity.
Qed.

(* Rotated, scaled, shifted, measured. Not the locked egg. *)
Definition sample_iso : IsoClothoid :=
  mkIsoClothoid WD_M (mkPoint 3 4) 0 (mkPoint 0 2) 0 (mkPoint (-2) 0) 0
    2 1 4 (Some 10) (Some 12).

Definition sample_egg : ClothoidEgg :=
  mk_cloth (mkAffPlace (mkPoint 3 4) (mkPoint 0 2) (mkPoint (-2) 0))
    2 1 4 (Some 10) (Some 12).

Lemma sample_sim :
  similarity_ok (mkPoint 0 2) (mkPoint (-2) 0) = true.
Proof.
  apply similarity_ok_intro; unfold frame_dot, frame_h2; cbn.
  - ring.
  - ring.
  - lra.
Qed.

Lemma sample_try : try_iso_clothoid sample_iso = inr sample_egg.
Proof.
  unfold try_iso_clothoid, sample_iso. cbn.
  rewrite refs_zero_horizontal. rewrite sample_sim.
  destruct (Rle_dec 2 0) as [Ha|Ha]; [lra|].
  destruct (Req_EM_T 1 4) as [Hs|Hs]; [lra|].
  unfold sample_egg. reflexivity.
Qed.

Lemma sample_not_locked : sample_egg <> locked_clothoid_egg.
Proof.
  intro H. apply (f_equal cloth_A) in H. cbn in H. lra.
Qed.

(* WD_Z, planar unit east, both ref z nonzero. 2D similarity holds. *)
Definition tilted_iso : IsoClothoid :=
  mkIsoClothoid WD_Z (mkPoint 0 0) 0 (mkPoint 1 0) 1 (mkPoint 0 1) 1
    1 0 1 None None.

Lemma tilted_try :
  try_iso_clothoid tilted_iso = inl ICF_TiltedPlacement.
Proof.
  unfold try_iso_clothoid, tilted_iso. cbn.
  unfold refs_horizontal.
  destruct (Req_EM_T 1 0) as [H|H]; [lra|].
  reflexivity.
Qed.

(* Horizontal WD_Z: ref z = 0, loc z is elevation and is dropped. *)
Definition flat_z_iso : IsoClothoid :=
  mkIsoClothoid WD_Z (mkPoint 0 0) 5 (mkPoint 1 0) 0 (mkPoint 0 1) 0
    1 0 1 None None.

Lemma flat_z_try :
  try_iso_clothoid flat_z_iso = inr locked_clothoid_egg.
Proof.
  unfold try_iso_clothoid, flat_z_iso. cbn.
  rewrite refs_zero_horizontal. rewrite unit_east_sim.
  destruct (Rle_dec 1 0) as [Ha|Ha]; [lra|].
  destruct (Req_EM_T 0 1) as [Hs|Hs]; [lra|].
  unfold locked_clothoid_egg, place_east. reflexivity.
Qed.

Lemma jts_is_example5_yes :
  jts_is_example5 example5_jts_k0 example5_jts_k1 example5_jts_L = true.
Proof.
  unfold jts_is_example5, example5_jts_k0, example5_jts_k1, example5_jts_L.
  destruct (Req_EM_T 0 0) as [_|H]; [|exfalso; apply H; reflexivity].
  destruct (Req_EM_T (5 / 1000) (5 / 1000)) as [_|H];
    [|exfalso; apply H; reflexivity].
  destruct (Req_EM_T 80 80) as [_|H]; [|exfalso; apply H; reflexivity].
  reflexivity.
Qed.

Lemma jts_is_example5_other : jts_is_example5 0 0 1 = false.
Proof.
  unfold jts_is_example5, example5_jts_k0, example5_jts_k1, example5_jts_L.
  destruct (Req_EM_T 0 0) as [_|H]; [|exfalso; apply H; reflexivity].
  destruct (Req_EM_T 0 (5 / 1000)) as [H|H]; [lra|].
  reflexivity.
Qed.

Lemma sample_wf : cloth_wf sample_egg.
Proof.
  destruct (try_iso_hit_wf sample_iso sample_egg sample_try) as [Hwf _].
  exact Hwf.
Qed.

Print Assumptions frame_lagrange.
Print Assumptions similarity_cross_nz.
Print Assumptions similarity_ok_intro.
Print Assumptions similarity_ok_spec.
Print Assumptions measures_none_coupled.
Print Assumptions try_iso_hit_wf.
Print Assumptions unit_east_sim.
Print Assumptions locked_iso_try.
Print Assumptions locked_iso_same_egg_eval.
Print Assumptions missing_try.
Print Assumptions unexpected_try.
Print Assumptions shear_cloth_wf.
Print Assumptions shear_try.
Print Assumptions degenerate_try.
Print Assumptions nonpos_try.
Print Assumptions sample_sim.
Print Assumptions sample_try.
Print Assumptions sample_not_locked.
Print Assumptions tilted_try.
Print Assumptions flat_z_try.
Print Assumptions jts_is_example5_yes.
Print Assumptions jts_is_example5_other.
Print Assumptions refs_horizontal_spec.
Print Assumptions refs_zero_horizontal.
Print Assumptions sample_wf.
