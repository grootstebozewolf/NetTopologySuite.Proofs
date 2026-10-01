(* ============================================================================
   NetTopologySuite.Proofs.SignedCurvature
   ----------------------------------------------------------------------------
   N2c-ii. Generic signed curvature is cross(v, a) / |v|^3.
   circ_signed_curv is that formula; circ_curv_const is restated
   by equality. The clothoid instance is sigma*s/A^2, which is
   cloth_kappa, and on a norm2 egg it is k0 + (k1-k0)*(u/L)
   (positive kappa is CCW, norm2's convention).
   The MemberState fold inherits point and tangent. Lenient
   records parsed k0 and does not enforce G2. Strict declines
   ID_ClothoidCurvatureJump when k0 differs from the inherited
   curvature. k0 = k1 declines ID_JtsConstantCurvature in both
   modes. No chord or circle dispatch. A missing predecessor
   is ID_ClothoidNoContext. No proof of C0, G1, or length
   assumes the G2 equality. Compound wiring is IntakeCompoundFold.
   claimId: none.
   No Admitted. No classic. No MVT / Rolle / RiemannInt.
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance SheetHenClothoidCore ClothoidNorm2
  CurveLength IntakeSpiralJts IsoClothoidIntake SheetHenCircEgg.
From NTS.Proofs Require ArcMemberState.
Local Open Scope R_scope.

Definition curv_cross (v a : Point) : R :=
  px v * py a - py v * px a.

Definition curv_speed2 (v : Point) : R :=
  px v * px v + py v * py v.

Definition signed_curv (v a : Point) : R :=
  let s := sqrt (curv_speed2 v) in
  curv_cross v a / (s * s * s).

Lemma circ_signed_curv_eq : forall c t,
  ArcMemberState.circ_signed_curv c t =
    signed_curv (mkPoint (ArcMemberState.circ_vx c t) (ArcMemberState.circ_vy c t))
                (mkPoint (ArcMemberState.circ_ax c t) (ArcMemberState.circ_ay c t)).
Proof.
  intros c t.
  unfold ArcMemberState.circ_signed_curv, signed_curv, curv_cross, curv_speed2.
  cbn. reflexivity.
Qed.

Lemma circ_signed_is_rsgn : forall c t,
  0 < circ_r c -> circ_sweep c <> 0 ->
  signed_curv (mkPoint (ArcMemberState.circ_vx c t) (ArcMemberState.circ_vy c t))
              (mkPoint (ArcMemberState.circ_ax c t) (ArcMemberState.circ_ay c t))
    = ArcMemberState.rsgn (circ_sweep c) / circ_r c.
Proof.
  intros c t Hr Hnz.
  rewrite <- circ_signed_curv_eq.
  apply ArcMemberState.circ_curv_const; assumption.
Qed.

Lemma chord_signed_is_zero : forall p q,
  signed_curv (mkPoint (ArcMemberState.chord_vx p q) (ArcMemberState.chord_vy p q))
              (mkPoint 0 0) = 0.
Proof.
  intros p q.
  unfold signed_curv, curv_cross, curv_speed2. cbn.
  replace (ArcMemberState.chord_vx p q * 0 - ArcMemberState.chord_vy p q * 0)
    with 0 by ring.
  apply Rmult_0_l.
Qed.

Definition cloth_signed_curv (c : ClothoidEgg) (s : R) : R :=
  cloth_kappa c s.

Lemma cloth_signed_is_sigma : forall c s,
  cloth_signed_curv c s = cloth_sigma c * s / (cloth_A c * cloth_A c).
Proof. intros. reflexivity. Qed.

Lemma norm2_signed_ends : forall st law m0 m1,
  0 < sl_len law -> sl_k0 law <> sl_k1 law -> pt_h2 (st_dir st) = 1 ->
  cloth_signed_curv (norm2 st law m0 m1) (law_sd law) = sl_k0 law /\
  cloth_signed_curv (norm2 st law m0 m1) (law_ed law) = sl_k1 law.
Proof.
  intros st law m0 m1 HL Hne Hu.
  unfold cloth_signed_curv. split.
  - apply norm2_kappa_sd; assumption.
  - apply norm2_kappa_ed; assumption.
Qed.

Lemma kappa_along : forall st law m0 m1 u,
  0 < sl_len law -> sl_k0 law <> sl_k1 law -> pt_h2 (st_dir st) = 1 ->
  cloth_signed_curv (norm2 st law m0 m1) (law_sd law + u) =
    sl_k0 law + (sl_k1 law - sl_k0 law) * (u / sl_len law).
Proof.
  intros st law m0 m1 u HL Hne Hu.
  unfold cloth_signed_curv, cloth_kappa, Rdiv.
  rewrite (norm2_sigma st law m0 m1 Hu).
  unfold norm2, mk_cloth. cbn [cloth_A].
  rewrite (law_A_sq law HL Hne).
  unfold law_sd.
  assert (HA : law_A2 law <> 0) by (apply Rgt_not_eq, law_A2_pos; assumption).
  assert (HL0 : sl_len law <> 0) by (apply Rgt_not_eq; exact HL).
  assert (Habs : Rabs (sl_k1 law - sl_k0 law) <> 0).
  { apply Rabs_no_R0, law_dk_nz. exact Hne. }
  replace (law_sigma law *
             (law_sigma law * sl_k0 law * law_A2 law + u) * / law_A2 law)
    with (law_sigma law * law_sigma law * sl_k0 law +
          law_sigma law * u * / law_A2 law) by (field; exact HA).
  rewrite law_sigma_sq.
  replace (law_A2 law) with (sl_len law * / Rabs (sl_k1 law - sl_k0 law))
    by (unfold law_A2, Rdiv; reflexivity).
  replace (law_sigma law * u *
             / (sl_len law * / Rabs (sl_k1 law - sl_k0 law)))
    with ((law_sigma law * Rabs (sl_k1 law - sl_k0 law)) *
          (u * / sl_len law)) by (field; split; [exact Habs | exact HL0]).
  replace (law_sigma law * Rabs (sl_k1 law - sl_k0 law))
    with (sl_k1 law - sl_k0 law).
  - ring.
  - rewrite <- (law_sigma_dk law Hne).
    rewrite <- Rmult_assoc. rewrite law_sigma_sq. ring.
Qed.

Definition seg_v (p q : Point) : Point :=
  mkPoint (px q - px p) (py q - py p).

Definition line_exit (p q : Point) : MemberState :=
  let n := sqrt (pt_h2 (seg_v p q)) in
  mkMemberState q (pt_scale (1 / n) (seg_v p q)) 0.

Lemma line_exit_unit : forall p q,
  0 < pt_h2 (seg_v p q) ->
  pt_h2 (mst_dir (line_exit p q)) = 1 /\
  mst_end (line_exit p q) = q /\
  mst_curvature (line_exit p q) = 0.
Proof.
  intros p q Hp.
  set (v := seg_v p q).
  set (n := sqrt (pt_h2 v)).
  assert (Hn : 0 < n) by (unfold n; apply sqrt_lt_R0; exact Hp).
  assert (Hsq : n * n = pt_h2 v).
  { unfold n. apply sqrt_sqrt. apply Rlt_le. exact Hp. }
  unfold line_exit. cbn. fold v. fold n.
  split; [|split; reflexivity].
  replace (pt_h2 (pt_scale (1 / n) v)) with ((1 / n) * (1 / n) * pt_h2 v).
  - rewrite <- Hsq. field. apply Rgt_not_eq. exact Hn.
  - unfold pt_h2, pt_scale. cbn. ring.
Qed.

Definition pred_state (m : MemberState) (k0 : R) : StartState :=
  mkStart (mst_end m) (mst_dir m) k0.

Definition build_clothoid (m : MemberState) (k0 k1 len : R)
  : ClothoidEgg * MemberState :=
  let e := norm2 (pred_state m k0) (mkLaw k0 k1 len) None None in
  let ex := cloth_exit e in
  (e, mkMemberState (st_pos ex) (st_dir ex) (st_curv ex)).

Definition fold_clothoid (mode : IntakeMode) (pred : option MemberState)
  (k0 k1 len : R) : IntakeDeclineReason + (ClothoidEgg * MemberState) :=
  match pred with
  | None => inl ID_ClothoidNoContext
  | Some m =>
      if Rle_dec len 0 then inl ID_JtsNonPositiveLength
      else if Req_EM_T k0 k1 then inl ID_JtsConstantCurvature
      else match mode with
           | IntakeLenient => inr (build_clothoid m k0 k1 len)
           | IntakeStrict =>
               if Req_EM_T k0 (mst_curvature m)
               then inr (build_clothoid m k0 k1 len)
               else inl ID_ClothoidCurvatureJump
           end
  end.

Lemma fold_no_context : forall mode k0 k1 len,
  fold_clothoid mode None k0 k1 len = inl ID_ClothoidNoContext.
Proof. intros. reflexivity. Qed.

Lemma fold_length_first : forall mode m k len,
  len <= 0 ->
  fold_clothoid mode (Some m) k k len = inl ID_JtsNonPositiveLength.
Proof.
  intros mode m k len Hle.
  unfold fold_clothoid.
  destruct (Rle_dec len 0) as [_|Hgt]; [reflexivity|].
  exfalso. apply Hgt. exact Hle.
Qed.

Lemma fold_constant_both : forall mode m k len,
  0 < len ->
  fold_clothoid mode (Some m) k k len = inl ID_JtsConstantCurvature.
Proof.
  intros mode m k len HL.
  unfold fold_clothoid.
  destruct (Rle_dec len 0) as [Hle|Hgt]; [lra|].
  destruct (Req_EM_T k k) as [_|Hne]; [reflexivity|].
  exfalso. apply Hne. reflexivity.
Qed.

Lemma fold_hit_egg : forall mode m k0 k1 len e ms,
  fold_clothoid mode (Some m) k0 k1 len = inr (e, ms) ->
  0 < len /\ k0 <> k1 /\
  e = fst (build_clothoid m k0 k1 len) /\
  ms = snd (build_clothoid m k0 k1 len).
Proof.
  intros mode m k0 k1 len e ms H.
  unfold fold_clothoid in H.
  destruct (Rle_dec len 0) as [Hle|Hgt]; [discriminate|].
  destruct (Req_EM_T k0 k1) as [Heq|Hne]; [discriminate|].
  destruct mode.
  - injection H as He Hm. split; [lra|]. split; [exact Hne|].
    rewrite <- He, <- Hm. split; reflexivity.
  - destruct (Req_EM_T k0 (mst_curvature m)) as [_|Hbad]; [|discriminate].
    injection H as He Hm. split; [lra|]. split; [exact Hne|].
    rewrite <- He, <- Hm. split; reflexivity.
Qed.

Lemma fold_c0 : forall mode m k0 k1 len e ms,
  pt_h2 (mst_dir m) = 1 ->
  fold_clothoid mode (Some m) k0 k1 len = inr (e, ms) ->
  cloth_eval e 0 = mst_end m.
Proof.
  intros mode m k0 k1 len e ms Hu H.
  destruct (fold_hit_egg mode m k0 k1 len e ms H) as [_ [_ [He _]]].
  rewrite He. unfold build_clothoid, pred_state. cbn [fst].
  apply norm2_start. cbn. exact Hu.
Qed.

Lemma fold_g1_jts : forall mode m k0 k1 len e ms,
  pt_h2 (mst_dir m) = 1 ->
  fold_clothoid mode (Some m) k0 k1 len = inr (e, ms) ->
  cloth_tangent e 0 = mst_dir m.
Proof.
  intros mode m k0 k1 len e ms Hu H.
  destruct (fold_hit_egg mode m k0 k1 len e ms H) as [HL [Hne [He _]]].
  rewrite He. unfold build_clothoid, pred_state. cbn [fst].
  apply norm2_start_dir; cbn; assumption.
Qed.

Lemma fold_length : forall mode m k0 k1 len e ms,
  pt_h2 (mst_dir m) = 1 ->
  fold_clothoid mode (Some m) k0 k1 len = inr (e, ms) ->
  cloth_ed e - cloth_sd e = len /\
  is_curve_length (cloth_eval e) 0 1 len.
Proof.
  intros mode m k0 k1 len e ms Hu H.
  destruct (fold_hit_egg mode m k0 k1 len e ms H) as [HL [Hne [He _]]].
  rewrite He. unfold build_clothoid, pred_state. cbn [fst].
  apply norm2_length; cbn; assumption.
Qed.

Lemma fold_g2_checked : forall m k0 k1 len e ms,
  fold_clothoid IntakeStrict (Some m) k0 k1 len = inr (e, ms) ->
  k0 = mst_curvature m.
Proof.
  intros m k0 k1 len e ms H.
  unfold fold_clothoid in H.
  destruct (Rle_dec len 0); [discriminate|].
  destruct (Req_EM_T k0 k1); [discriminate|].
  destruct (Req_EM_T k0 (mst_curvature m)) as [Heq|Hbad]; [|discriminate].
  exact Heq.
Qed.

Lemma fold_g2_recorded : forall m k0 k1 len e ms,
  pt_h2 (mst_dir m) = 1 ->
  fold_clothoid IntakeLenient (Some m) k0 k1 len = inr (e, ms) ->
  cloth_curv e 0 = k0.
Proof.
  intros m k0 k1 len e ms Hu H.
  destruct (fold_hit_egg IntakeLenient m k0 k1 len e ms H) as [HL [Hne [He _]]].
  rewrite He. unfold build_clothoid, pred_state. cbn [fst].
  assert (Hc := norm2_curv (mkStart (mst_end m) (mst_dir m) k0)
                            (mkLaw k0 k1 len) None None).
  cbn in Hc. apply (proj1 (Hc HL Hne Hu)).
Qed.

Lemma example5_A2 : law_A2 (mkLaw 0 (5 / 1000) 80) = 16000.
Proof.
  unfold law_A2, Rdiv. cbn [sl_len sl_k0 sl_k1].
  rewrite Rabs_right by lra. field.
Qed.

Lemma example5_line_unit :
  pt_h2 (mst_dir (line_exit (mkPoint 0 0) (mkPoint 100 0))) = 1 /\
  mst_end (line_exit (mkPoint 0 0) (mkPoint 100 0)) = mkPoint 100 0 /\
  mst_curvature (line_exit (mkPoint 0 0) (mkPoint 100 0)) = 0.
Proof.
  apply line_exit_unit. unfold seg_v, pt_h2. cbn. lra.
Qed.

Lemma example5_fold : forall mode,
  exists e ms,
    fold_clothoid mode
      (Some (line_exit (mkPoint 0 0) (mkPoint 100 0)))
      example5_jts_k0 example5_jts_k1 example5_jts_L = inr (e, ms) /\
    cloth_eval e 0 = mkPoint 100 0 /\
    cloth_tangent e 0 = mst_dir (line_exit (mkPoint 0 0) (mkPoint 100 0)) /\
    cloth_ed e - cloth_sd e = example5_jts_L /\
    cloth_A e <> 1.
Proof.
  intro mode.
  set (m := line_exit (mkPoint 0 0) (mkPoint 100 0)).
  destruct example5_line_unit as [Hu [Hp Hk]].
  fold m in Hu, Hp, Hk.
  assert (Hfold :
    fold_clothoid mode (Some m) example5_jts_k0 example5_jts_k1 example5_jts_L =
      inr (build_clothoid m example5_jts_k0 example5_jts_k1 example5_jts_L)).
  { unfold fold_clothoid, example5_jts_k0, example5_jts_k1, example5_jts_L.
    destruct (Rle_dec 80 0) as [Hle|Hgt]; [lra|].
    destruct (Req_EM_T 0 (5 / 1000)) as [Heq|Hne]; [lra|].
    destruct mode.
    - reflexivity.
    - rewrite Hk.
      destruct (Req_EM_T 0 0) as [_|Hbad]; [reflexivity|].
      exfalso. apply Hbad. reflexivity. }
  set (b := build_clothoid m example5_jts_k0 example5_jts_k1 example5_jts_L).
  exists (fst b), (snd b).
  split; [exact Hfold|].
  assert (He : fst b = norm2 (pred_state m example5_jts_k0)
                  (mkLaw example5_jts_k0 example5_jts_k1 example5_jts_L)
                  None None).
  { unfold b, build_clothoid. cbn. reflexivity. }
  split.
  - rewrite <- Hp.
    apply (fold_c0 mode m example5_jts_k0 example5_jts_k1
             example5_jts_L (fst b) (snd b) Hu Hfold).
  - split.
    + apply (fold_g1_jts mode m example5_jts_k0 example5_jts_k1
               example5_jts_L (fst b) (snd b) Hu Hfold).
    + split.
      * apply (proj1 (fold_length mode m example5_jts_k0 example5_jts_k1
                        example5_jts_L (fst b) (snd b) Hu Hfold)).
      * rewrite He. unfold cloth_A, norm2, mk_cloth, pred_state. cbn.
        unfold example5_jts_k0, example5_jts_k1, example5_jts_L.
        intro E.
        assert (HL : 0 < sl_len (mkLaw 0 (5 / 1000) 80)) by (cbn; lra).
        assert (Hne : sl_k0 (mkLaw 0 (5 / 1000) 80) <>
                      sl_k1 (mkLaw 0 (5 / 1000) 80)) by (cbn; lra).
        assert (Hsq : law_A (mkLaw 0 (5 / 1000) 80) *
                      law_A (mkLaw 0 (5 / 1000) 80) =
                      law_A2 (mkLaw 0 (5 / 1000) 80)).
        { apply law_A_sq; assumption. }
        rewrite E, example5_A2 in Hsq. lra.
Qed.

Lemma fold_strict_jump :
  fold_clothoid IntakeStrict
    (Some (line_exit (mkPoint 0 0) (mkPoint 100 0)))
    1 (5 / 1000) 80 = inl ID_ClothoidCurvatureJump.
Proof.
  unfold fold_clothoid.
  destruct (Rle_dec 80 0) as [Hle|Hgt]; [lra|].
  destruct (Req_EM_T 1 (5 / 1000)) as [Heq|Hne]; [lra|].
  destruct example5_line_unit as [_ [_ Hk]].
  rewrite Hk.
  destruct (Req_EM_T 1 0) as [Hbad|Hok]; [lra|].
  reflexivity.
Qed.

Lemma fold_lenient_records_jump :
  exists e ms,
    fold_clothoid IntakeLenient
      (Some (line_exit (mkPoint 0 0) (mkPoint 100 0)))
      1 (5 / 1000) 80 = inr (e, ms) /\
    mst_curvature (line_exit (mkPoint 0 0) (mkPoint 100 0)) = 0 /\
    cloth_curv e 0 = 1.
Proof.
  set (m := line_exit (mkPoint 0 0) (mkPoint 100 0)).
  destruct example5_line_unit as [Hu [_ Hk]]. fold m in Hu, Hk.
  assert (H : fold_clothoid IntakeLenient (Some m) 1 (5 / 1000) 80 =
              inr (build_clothoid m 1 (5 / 1000) 80)).
  { unfold fold_clothoid.
    destruct (Rle_dec 80 0) as [Hle|Hgt]; [lra|].
    destruct (Req_EM_T 1 (5 / 1000)) as [Heq|Hne]; [lra|].
    reflexivity. }
  exists (fst (build_clothoid m 1 (5 / 1000) 80)),
         (snd (build_clothoid m 1 (5 / 1000) 80)).
  split; [exact H|]. split; [exact Hk|].
  apply (fold_g2_recorded m 1 (5 / 1000) 80 _ _ Hu H).
Qed.

Print Assumptions circ_signed_curv_eq.
Print Assumptions circ_signed_is_rsgn.
Print Assumptions chord_signed_is_zero.
Print Assumptions cloth_signed_is_sigma.
Print Assumptions norm2_signed_ends.
Print Assumptions kappa_along.
Print Assumptions line_exit_unit.
Print Assumptions fold_no_context.
Print Assumptions fold_length_first.
Print Assumptions fold_constant_both.
Print Assumptions fold_hit_egg.
Print Assumptions fold_c0.
Print Assumptions fold_g1_jts.
Print Assumptions fold_length.
Print Assumptions fold_g2_checked.
Print Assumptions fold_g2_recorded.
Print Assumptions example5_A2.
Print Assumptions example5_line_unit.
Print Assumptions example5_fold.
Print Assumptions fold_strict_jump.
Print Assumptions fold_lenient_records_jump.
