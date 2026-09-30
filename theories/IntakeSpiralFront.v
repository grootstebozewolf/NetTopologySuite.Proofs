(* ============================================================================
   NetTopologySuite.Proofs.IntakeSpiralFront
   ----------------------------------------------------------------------------
   N2b. SPIRALCURVE clothoid front end onto norm2
   (ClothoidNorm2, claimId 0007-norm2-state). claimId: none.
   Start state is sc_loc and the unit vector along sc_ref1.
   h = sign(ref1 × ref2) = frame_hand. World curvatures are
   h * k0 and h * k1 (CCW positive, norm2's convention).
   Check order: length, then k0 = k1, then the similarity
   frame. Measures are the coupled pair sc_m (both or neither),
   the success case of measures_fail. SpiralOther stays a
   decline in the walker. No Admitted.
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance SheetHenClothoidCore IsoClothoidIntake
  IntakeSpiralJts ClothoidNorm2.
Local Open Scope R_scope.

Inductive SpiralFail : Type :=
| SFail_NonPositiveLength
| SFail_ConstantCurvature
| SFail_NotSimilarity.

Definition spiral_hand (sc : SpiralClothoid) : R :=
  frame_hand (sc_ref1 sc) (sc_ref2 sc).

Definition spiral_dir (sc : SpiralClothoid) : Point :=
  pt_scale (1 / sqrt (frame_h2 (sc_ref1 sc))) (sc_ref1 sc).

Definition spiral_state (sc : SpiralClothoid) : StartState :=
  mkStart (sc_loc sc) (spiral_dir sc) (spiral_hand sc * sc_k0 sc).

Definition spiral_law (sc : SpiralClothoid) : SpiralLaw :=
  mkLaw (spiral_hand sc * sc_k0 sc) (spiral_hand sc * sc_k1 sc) (sc_len sc).

(* option (R * R) is already both-or-neither. That is the Hit
   case of measures_fail (rule 8 / #888). *)
Definition spiral_measures (sc : SpiralClothoid) : option R * option R :=
  match sc_m sc with
  | None => (None, None)
  | Some (a, b) => (Some a, Some b)
  end.

Definition try_spiral_clothoid (sc : SpiralClothoid) : SpiralFail + ClothoidEgg :=
  if Rle_dec (sc_len sc) 0 then inl SFail_NonPositiveLength
  else if Req_EM_T (sc_k0 sc) (sc_k1 sc) then inl SFail_ConstantCurvature
  else if similarity_ok (sc_ref1 sc) (sc_ref2 sc) then
    let ms := spiral_measures sc in
    inr (norm2 (spiral_state sc) (spiral_law sc) (fst ms) (snd ms))
  else inl SFail_NotSimilarity.

Lemma spiral_world_curv : forall sc,
  sl_k0 (spiral_law sc) = spiral_hand sc * sc_k0 sc /\
  sl_k1 (spiral_law sc) = spiral_hand sc * sc_k1 sc /\
  sl_len (spiral_law sc) = sc_len sc /\
  st_pos (spiral_state sc) = sc_loc sc.
Proof. intro sc. repeat split; reflexivity. Qed.

Lemma spiral_measures_coupled : forall sc,
  (fst (spiral_measures sc) = None /\ snd (spiral_measures sc) = None) \/
  (exists a b,
     fst (spiral_measures sc) = Some a /\ snd (spiral_measures sc) = Some b).
Proof.
  intro sc. unfold spiral_measures. destruct (sc_m sc) as [[a b]|].
  - right. exists a, b. split; reflexivity.
  - left. split; reflexivity.
Qed.

Lemma frame_h2_nonneg : forall p, 0 <= frame_h2 p.
Proof.
  intro p. unfold frame_h2.
  pose proof (Rle_0_sqr (px p)) as Hx. pose proof (Rle_0_sqr (py p)) as Hy.
  unfold Rsqr in Hx, Hy. lra.
Qed.

Lemma spiral_dir_unit : forall sc,
  similarity_ok (sc_ref1 sc) (sc_ref2 sc) = true ->
  pt_h2 (spiral_dir sc) = 1.
Proof.
  intros sc Hs.
  destruct (similarity_ok_spec _ _ Hs) as [_ [_ Hnz]].
  set (p := sc_ref1 sc).
  assert (Hp : 0 < frame_h2 p).
  { destruct (Rle_lt_or_eq 0 (frame_h2 p) (frame_h2_nonneg p)) as [Hlt|Heq].
    - exact Hlt.
    - exfalso. apply Hnz. unfold p. symmetry. exact Heq. }
  set (s := sqrt (frame_h2 p)).
  assert (Hs0 : 0 < s) by (unfold s; apply sqrt_lt_R0; exact Hp).
  assert (Hsq : s * s = frame_h2 p).
  { unfold s. apply sqrt_sqrt. apply Rlt_le. exact Hp. }
  assert (Ept : pt_h2 p = frame_h2 p).
  { unfold pt_h2, frame_h2, p. reflexivity. }
  unfold spiral_dir. fold p. fold s.
  replace (pt_h2 (pt_scale (1 / s) p)) with ((1 / s) * (1 / s) * pt_h2 p).
  - rewrite Ept, <- Hsq. field. apply Rgt_not_eq. exact Hs0.
  - unfold pt_h2, pt_scale. cbn. ring.
Qed.

Lemma frame_hand_sq : forall a b, frame_hand a b * frame_hand a b = 1.
Proof.
  intros a b. unfold frame_hand.
  destruct (Rle_dec 0 (frame_cross a b)); ring.
Qed.

Lemma try_spiral_spec : forall sc e,
  try_spiral_clothoid sc = inr e ->
  0 < sc_len sc /\
  sc_k0 sc <> sc_k1 sc /\
  similarity_ok (sc_ref1 sc) (sc_ref2 sc) = true /\
  e = norm2 (spiral_state sc) (spiral_law sc)
        (fst (spiral_measures sc)) (snd (spiral_measures sc)).
Proof.
  intros sc e H.
  unfold try_spiral_clothoid in H.
  destruct (Rle_dec (sc_len sc) 0) as [Hle|Hgt].
  - discriminate.
  - destruct (Req_EM_T (sc_k0 sc) (sc_k1 sc)) as [Heq|Hne].
    + discriminate.
    + destruct (similarity_ok (sc_ref1 sc) (sc_ref2 sc)) eqn:Hs.
      * injection H as H. split; [lra|].
        split; [exact Hne|]. split; [reflexivity|].
        rewrite <- H. reflexivity.
      * discriminate.
Qed.

Lemma spiral_k_sep : forall sc,
  sc_k0 sc <> sc_k1 sc ->
  sl_k0 (spiral_law sc) <> sl_k1 (spiral_law sc).
Proof.
  intros sc Hne E.
  apply Hne.
  apply (Rmult_eq_reg_l (spiral_hand sc)).
  - unfold spiral_law in E. cbn in E. exact E.
  - unfold spiral_hand, frame_hand.
    destruct (Rle_dec 0 (frame_cross (sc_ref1 sc) (sc_ref2 sc))); lra.
Qed.

Lemma norm2_refs_sim : forall st law,
  pt_h2 (st_dir st) = 1 ->
  similarity_ok (norm2_ref1 st law) (norm2_ref2 st law) = true.
Proof.
  intros st law Hu.
  apply similarity_ok_intro.
  - unfold frame_dot, norm2_ref2, rot90, pt_scale. cbn. ring.
  - unfold frame_h2, norm2_ref2, rot90, pt_scale, law_sigma. cbn.
    destruct (Rle_dec (sl_k0 law) (sl_k1 law)); ring.
  - assert (E : frame_h2 (norm2_ref1 st law) = pt_h2 (st_dir st)).
    { rewrite <- (norm2_ref_sumsq st law).
      unfold frame_h2, pt_h2. reflexivity. }
    rewrite E, Hu. lra.
Qed.

Definition spiral_dim (sc : SpiralClothoid) : WktDim :=
  match sc_m sc with
  | Some _ => WD_M
  | None => WD_XY
  end.

Definition iso_of_spiral (sc : SpiralClothoid) : IsoClothoid :=
  let ms := spiral_measures sc in
  let e := norm2 (spiral_state sc) (spiral_law sc) (fst ms) (snd ms) in
  mkIsoClothoid (spiral_dim sc)
    (aff_loc (cloth_place e)) 0
    (aff_ref1 (cloth_place e)) 0
    (aff_ref2 (cloth_place e)) 0
    (cloth_A e) (cloth_sd e) (cloth_ed e)
    (fst ms) (snd ms).

Lemma iso_spiral_same_curve : forall sc e,
  try_spiral_clothoid sc = inr e ->
  try_iso_clothoid (iso_of_spiral sc) = inr e.
Proof.
  intros sc e H.
  destruct (try_spiral_spec sc e H) as [HL [Hne [Hs He]]].
  assert (Hu : pt_h2 (st_dir (spiral_state sc)) = 1).
  { unfold spiral_state. cbn. apply spiral_dir_unit. exact Hs. }
  assert (Hk : sl_k0 (spiral_law sc) <> sl_k1 (spiral_law sc))
    by (apply spiral_k_sep; exact Hne).
  assert (HA : 0 < law_A (spiral_law sc)).
  { apply law_A_pos; [unfold spiral_law; cbn; exact HL| exact Hk]. }
  assert (Hsd : law_sd (spiral_law sc) <> law_ed (spiral_law sc)).
  { intro Heq.
    assert (E : law_ed (spiral_law sc) - law_sd (spiral_law sc) = sc_len sc).
    { rewrite law_ed_sd by exact Hk. unfold spiral_law. cbn. reflexivity. }
    rewrite Heq in E. lra. }
  set (st := spiral_state sc).
  set (law := spiral_law sc).
  assert (Hu' : pt_h2 (st_dir st) = 1) by (unfold st; exact Hu).
  pose proof (norm2_refs_sim st law Hu') as Hsim.
  unfold st, law in Hsim.
  unfold spiral_measures in He.
  unfold try_iso_clothoid, iso_of_spiral, spiral_dim, spiral_measures.
  destruct (sc_m sc) as [[a b]|]; rewrite He;
    cbn [fst snd measures_fail dim_has_m ic_dim ic_loc ic_m0 ic_m1
         ic_ref1_z ic_ref2_z];
    rewrite refs_zero_horizontal;
    unfold norm2, mk_cloth;
    cbn [cloth_place aff_loc aff_ref1 aff_ref2 cloth_A cloth_sd cloth_ed
         ic_ref1 ic_ref2 ic_A ic_sd ic_ed];
    rewrite Hsim;
    destruct (Rle_dec (law_A (spiral_law sc)) 0) as [Hz|_].
  - apply (Rlt_not_le _ _ HA) in Hz. contradiction.
  - destruct (Req_EM_T (law_sd (spiral_law sc)) (law_ed (spiral_law sc)))
      as [Heq|_].
    + contradiction.
    + reflexivity.
  - apply (Rlt_not_le _ _ HA) in Hz. contradiction.
  - destruct (Req_EM_T (law_sd (spiral_law sc)) (law_ed (spiral_law sc)))
      as [Heq|_].
    + contradiction.
    + reflexivity.
Qed.

Definition zero_len_spiral : SpiralClothoid :=
  mkSpiralClothoid (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1) 0 1 1 None.

Definition const_k_spiral : SpiralClothoid :=
  mkSpiralClothoid (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1) 1 2 2 None.

Definition shear_spiral : SpiralClothoid :=
  mkSpiralClothoid (mkPoint 0 0) (mkPoint 2 0) (mkPoint 1 1) 1 0 1 None.

Definition parallel_spiral : SpiralClothoid :=
  mkSpiralClothoid (mkPoint 0 0) (mkPoint 1 0) (mkPoint 2 0) 1 0 1 None.

Lemma zero_len_even_equal_k :
  try_spiral_clothoid zero_len_spiral = inl SFail_NonPositiveLength.
Proof.
  unfold try_spiral_clothoid, zero_len_spiral. cbn.
  destruct (Rle_dec 0 0) as [_|H]; [|exfalso; apply H; lra].
  reflexivity.
Qed.

Lemma const_k_unit_frame :
  try_spiral_clothoid const_k_spiral = inl SFail_ConstantCurvature.
Proof.
  unfold try_spiral_clothoid, const_k_spiral. cbn.
  destruct (Rle_dec 1 0) as [Hle|Hgt]; [lra|].
  destruct (Req_EM_T 2 2) as [_|H]; [|exfalso; apply H; reflexivity].
  reflexivity.
Qed.

Lemma shear_spiral_fails :
  try_spiral_clothoid shear_spiral = inl SFail_NotSimilarity.
Proof.
  unfold try_spiral_clothoid, shear_spiral. cbn.
  destruct (Rle_dec 1 0) as [Hle|Hgt]; [lra|].
  destruct (Req_EM_T 0 1) as [Heq|Hne]; [lra|].
  unfold similarity_ok, frame_dot. cbn.
  destruct (Req_EM_T (2 * 1 + 0 * 1) 0) as [H|H]; [lra|].
  reflexivity.
Qed.

Lemma parallel_spiral_fails :
  try_spiral_clothoid parallel_spiral = inl SFail_NotSimilarity.
Proof.
  unfold try_spiral_clothoid, parallel_spiral. cbn.
  destruct (Rle_dec 1 0) as [Hle|Hgt]; [lra|].
  destruct (Req_EM_T 0 1) as [Heq|Hne]; [lra|].
  unfold similarity_ok, frame_dot. cbn.
  destruct (Req_EM_T (1 * 2 + 0 * 0) 0) as [H|H]; [lra|].
  reflexivity.
Qed.

Lemma sample_law_A2 :
  law_A2 (spiral_law sample_spiral_clothoid) = 16000.
Proof.
  unfold law_A2, spiral_law, sample_spiral_clothoid, spiral_hand, frame_hand,
    frame_cross, example5_jts_L, example5_jts_k0, example5_jts_k1.
  cbn.
  destruct (Rle_dec 0 (1 * 1 - 0 * 0)) as [_|H]; [|exfalso; lra].
  replace (Rabs (1 * (5 / 1000) - 1 * 0)) with (5 / 1000).
  - field.
  - rewrite Rabs_right by lra. ring.
Qed.

Lemma sample_spiral_hits : exists e,
  try_spiral_clothoid sample_spiral_clothoid = inr e /\ cloth_A e <> 1.
Proof.
  assert (Hs : similarity_ok (sc_ref1 sample_spiral_clothoid)
                              (sc_ref2 sample_spiral_clothoid) = true).
  { unfold sample_spiral_clothoid. cbn. exact unit_east_sim. }
  assert (Hlen : 0 < sc_len sample_spiral_clothoid).
  { unfold sample_spiral_clothoid, example5_jts_L. cbn. lra. }
  assert (Hne : sc_k0 sample_spiral_clothoid <> sc_k1 sample_spiral_clothoid).
  { unfold sample_spiral_clothoid, example5_jts_k0, example5_jts_k1. cbn. lra. }
  destruct (try_spiral_clothoid sample_spiral_clothoid) as [f|e] eqn:Ht.
  - unfold try_spiral_clothoid in Ht.
    destruct (Rle_dec (sc_len sample_spiral_clothoid) 0) as [Hbad|Hok]; [lra|].
    destruct (Req_EM_T (sc_k0 sample_spiral_clothoid)
                       (sc_k1 sample_spiral_clothoid)) as [Hbad|Hok2];
      [contradiction|].
    rewrite Hs in Ht. discriminate.
  - exists e. split; [reflexivity|].
    destruct (try_spiral_spec _ _ Ht) as [HL [_ [_ He]]].
    rewrite He. unfold cloth_A, norm2, mk_cloth. cbn.
    intro E.
    assert (Hk : sl_k0 (spiral_law sample_spiral_clothoid) <>
                 sl_k1 (spiral_law sample_spiral_clothoid)).
    { apply spiral_k_sep. exact Hne. }
    assert (Hsq : law_A (spiral_law sample_spiral_clothoid) *
                  law_A (spiral_law sample_spiral_clothoid) =
                  law_A2 (spiral_law sample_spiral_clothoid)).
    { apply law_A_sq.
      - unfold spiral_law. cbn. exact HL.
      - exact Hk. }
    rewrite E, sample_law_A2 in Hsq. lra.
Qed.

Print Assumptions spiral_world_curv.
Print Assumptions spiral_measures_coupled.
Print Assumptions spiral_dir_unit.
Print Assumptions try_spiral_spec.
Print Assumptions spiral_k_sep.
Print Assumptions norm2_refs_sim.
Print Assumptions iso_spiral_same_curve.
Print Assumptions zero_len_even_equal_k.
Print Assumptions const_k_unit_frame.
Print Assumptions shear_spiral_fails.
Print Assumptions parallel_spiral_fails.
Print Assumptions sample_spiral_hits.
