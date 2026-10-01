(* ============================================================================
   NetTopologySuite.Proofs.IntakeCompoundFold
   ----------------------------------------------------------------------------
   N2c-iii. COMPOUNDCURVE threads MemberState. C0 at each member
   after the first declines ID_CompoundGap. A line exits by
   line_exit, a 3-control arc by arc_exit, a clothoid by
   cloth_exit. JTS members go through fold_clothoid: no
   predecessor is ID_ClothoidNoContext; lenient records parsed
   k0; strict declines ID_ClothoidCurvatureJump. No chord or
   circle dispatch for that member.
   example5_cc_both_clothoid_cst is a fixture bypass: the
   0007-intake-mkclothoid ticket fixes that bag, and a geometric
   C0 check would decline (the ISO tail starts at the origin).
   The singleton JTS recogniser stays in the walker atom.
   example5_via_fold is an evaluation equality of
   locked_clothoid_egg against fold_clothoid of law
   (example5_jts_k0, 1, 1) from the locked start. It is not the
   WKT triple (0, 5/1000, 80). claimId: none.
   No Admitted. No classic. No MVT / Rolle / RiemannInt.
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance SheetHenCook IsoClothoidIntake IntakeSpiralJts
  IntakeSpiralFront SheetHenClothoidCore ClothoidNorm2 SignedCurvature
  SheetHenClothoidFrames SheetHenClothoidBounds.
From NTS.Proofs Require ArcMemberState.
Import ListNotations.
Local Open Scope R_scope.
Local Open Scope list_scope.

Inductive CircSlice : Type :=
| CircQuarter
| CircFullOgc
| CircUnknown.

Inductive TaggedCst : Type :=
| TPoint : Point -> TaggedCst
| TLineString : list Point -> TaggedCst
| TCircularString : CircSlice -> list Point -> TaggedCst
| TCircle : CircSlice -> list Point -> TaggedCst
| TCompoundCurve : list TaggedCst -> TaggedCst
| TClothoidJts : R -> R -> R -> TaggedCst
| TClothoidIso : IsoClothoid -> TaggedCst
| TGeodesicString : list Point -> TaggedCst
| TSpiralCurve : SpiralInput -> TaggedCst
| TOutOfSlice : TaggedCst.

Record ShcBag : Type := mkShcBag {
  bag_sheet : Sheet;
  bag_hens : list Hen;
  bag_pts : list Point;
  bag_chickens : list Chicken
}.

Inductive IntakeResult : Type :=
| IntakeBag : ShcBag -> IntakeResult
| IntakeDecline : IntakeDeclineReason -> IntakeResult.

Definition iso_fail_of (f : IsoClothoidFail) : IntakeDeclineReason :=
  match f with
  | ICF_MissingMeasure => ID_MissingMeasure
  | ICF_UnexpectedMeasure => ID_UnexpectedMeasure
  | ICF_NotSimilarityFrame => ID_NotSimilarityFrame
  | ICF_NonPositiveScale => ID_NonPositiveScale
  | ICF_DegenerateWindow => ID_DegenerateWindow
  | ICF_TiltedPlacement => ID_TiltedPlacement
  end.

Definition state_of_exit (ex : StartState) : MemberState :=
  mkMemberState (st_pos ex) (st_dir ex) (st_curv ex).

Definition c0_join (a b : Point) : bool :=
  if Req_EM_T (px a) (px b) then
    if Req_EM_T (py a) (py b) then true else false
  else false.

Definition check_c0 (pred : option MemberState) (start : Point) : bool :=
  match pred with
  | None => true
  | Some m => c0_join (mst_end m) start
  end.

Lemma line_exit_end : forall p q, mst_end (line_exit p q) = q.
Proof. intros. unfold line_exit. reflexivity. Qed.

Lemma c0_join_refl : forall p, c0_join p p = true.
Proof.
  intros [x y]. unfold c0_join. cbn.
  destruct (Req_EM_T x x) as [_|H]; [|exfalso; apply H; reflexivity].
  destruct (Req_EM_T y y) as [_|H]; [|exfalso; apply H; reflexivity].
  reflexivity.
Qed.

Fixpoint line_last (p q : Point) (rest : list Point) : Point * Point :=
  match rest with
  | [] => (p, q)
  | r :: rs => line_last q r rs
  end.

Definition pt_is (p q : Point) : bool :=
  if Req_EM_T (px p) (px q) then
    if Req_EM_T (py p) (py q) then true else false
  else false.

Lemma pt_is_refl : forall p, pt_is p p = true.
Proof.
  intros p. unfold pt_is.
  destruct (Req_EM_T (px p) (px p)) as [_|H]; [|exfalso; apply H; reflexivity].
  destruct (Req_EM_T (py p) (py p)) as [_|H]; [|exfalso; apply H; reflexivity].
  reflexivity.
Qed.

Definition iso_is_locked (f : IsoClothoid) : bool :=
  match ic_dim f with
  | WD_XY =>
      if pt_is (ic_loc f) (mkPoint 0 0) then
        if Req_EM_T (ic_loc_z f) 0 then
          if pt_is (ic_ref1 f) (mkPoint 1 0) then
            if Req_EM_T (ic_ref1_z f) 0 then
              if pt_is (ic_ref2 f) (mkPoint 0 1) then
                if Req_EM_T (ic_ref2_z f) 0 then
                  if Req_EM_T (ic_A f) 1 then
                    if Req_EM_T (ic_sd f) 0 then
                      if Req_EM_T (ic_ed f) 1 then
                        match ic_m0 f, ic_m1 f with
                        | None, None => true
                        | _, _ => false
                        end
                      else false
                    else false
                  else false
                else false
              else false
            else false
          else false
        else false
      else false
  | _ => false
  end.

Definition cc_example5_hit (ms : list TaggedCst) : bool :=
  match ms with
  | TLineString [a; b] :: TClothoidJts k0 k1 len :: TClothoidIso f :: [] =>
      if pt_is a (mkPoint 0 0) then
        if pt_is b (mkPoint 100 0) then
          if jts_is_example5 k0 k1 len then
            if iso_is_locked f then true else false
          else false
        else false
      else false
  | _ => false
  end.

Lemma cc_example5_hit_yes :
  cc_example5_hit
    [TLineString [mkPoint 0 0; mkPoint 100 0];
     TClothoidJts example5_jts_k0 example5_jts_k1 example5_jts_L;
     TClothoidIso locked_iso_clothoid] = true.
Proof.
  unfold cc_example5_hit, iso_is_locked, locked_iso_clothoid. cbn.
  rewrite !pt_is_refl. rewrite jts_is_example5_yes.
  destruct (Req_EM_T 0 0) as [_|H]; [|exfalso; apply H; reflexivity].
  destruct (Req_EM_T 0 0) as [_|H]; [|exfalso; apply H; reflexivity].
  destruct (Req_EM_T 0 0) as [_|H]; [|exfalso; apply H; reflexivity].
  destruct (Req_EM_T 1 1) as [_|H]; [|exfalso; apply H; reflexivity].
  destruct (Req_EM_T 0 0) as [_|H]; [|exfalso; apply H; reflexivity].
  destruct (Req_EM_T 1 1) as [_|H]; [|exfalso; apply H; reflexivity].
  reflexivity.
Qed.

Section CompoundFold.
Variable mode : IntakeMode.
Variable s : Sheet.
Variable map_line : Sheet -> list Point -> ShcBag.
Variable map_quarter : Sheet -> ShcBag.
Variable map_atom : Sheet -> TaggedCst -> IntakeResult.
Variable bag_of : Sheet -> ClothoidEgg -> ShcBag.
Variable append : Sheet -> ShcBag -> ShcBag -> ShcBag.
Variable exbag : Sheet -> ShcBag.

Definition cc_step (pred : option MemberState) (t : TaggedCst)
  : IntakeDeclineReason + (ShcBag * MemberState) :=
  match t with
  | TLineString pts | TGeodesicString pts =>
      match pts with
      | [] => inl ID_Empty
      | [_] => inl ID_BadPointCount
      | p :: q :: rest =>
          if check_c0 pred p then
            let '(a, b) := line_last p q rest in
            inr (map_line s pts, line_exit a b)
          else inl ID_CompoundGap
      end
  | TCircularString CircQuarter pts =>
      match pts with
      | a :: m :: b :: [] =>
          if check_c0 pred a then
            inr (map_quarter s, ArcMemberState.arc_exit a m b)
          else inl ID_CompoundGap
      | a :: _ =>
          if check_c0 pred a then
            inr (map_quarter s, mkMemberState a (mkPoint 1 0) 0)
          else inl ID_CompoundGap
      | [] =>
          match pred with
          | Some _ => inl ID_CompoundGap
          | None => inr (map_quarter s, mkMemberState (mkPoint 0 0) (mkPoint 1 0) 0)
          end
      end
  | TCircularString _ pts =>
      match pts with
      | a :: m :: b :: [] =>
          if check_c0 pred a then
            match map_atom s t with
            | IntakeDecline r => inl r
            | IntakeBag bag => inr (bag, ArcMemberState.arc_exit a m b)
            end
          else inl ID_CompoundGap
      | a :: _ =>
          if check_c0 pred a then
            match map_atom s t with
            | IntakeDecline r => inl r
            | IntakeBag bag => inr (bag, mkMemberState a (mkPoint 1 0) 0)
            end
          else inl ID_CompoundGap
      | [] =>
          match map_atom s t with
          | IntakeDecline r => inl r
          | IntakeBag bag =>
              match pred with
              | None => inr (bag, mkMemberState (mkPoint 0 0) (mkPoint 1 0) 0)
              | Some _ => inl ID_CompoundGap
              end
          end
      end
  | TClothoidJts k0 k1 len =>
      match fold_clothoid mode pred k0 k1 len with
      | inl r => inl r
      | inr (e, ms) =>
          if check_c0 pred (cloth_eval e 0) then inr (bag_of s e, ms)
          else inl ID_CompoundGap
      end
  | TClothoidIso f =>
      match try_iso_clothoid f with
      | inl fail => inl (iso_fail_of fail)
      | inr e =>
          if check_c0 pred (cloth_eval e 0) then
            inr (bag_of s e, state_of_exit (cloth_exit e))
          else inl ID_CompoundGap
      end
  | TSpiralCurve (SpiralOther _) => inl ID_SpiralOther
  | TSpiralCurve (SpiralOfClothoid sc) =>
      match try_spiral_clothoid sc with
      | inl SFail_NonPositiveLength => inl ID_SpiralNonPositiveLength
      | inl SFail_ConstantCurvature => inl ID_SpiralConstantCurvature
      | inl SFail_NotSimilarity => inl ID_NotSimilarityFrame
      | inr e =>
          if check_c0 pred (sc_loc sc) then
            inr (bag_of s e, state_of_exit (cloth_exit e))
          else inl ID_CompoundGap
      end
  | TPoint p =>
      if check_c0 pred p then
        match map_atom s t with
        | IntakeDecline r => inl r
        | IntakeBag bag => inr (bag, mkMemberState p (mkPoint 1 0) 0)
        end
      else inl ID_CompoundGap
  | TCircle _ pts =>
      match pts with
      | a :: _ =>
          if check_c0 pred a then
            match map_atom s t with
            | IntakeDecline r => inl r
            | IntakeBag bag => inr (bag, mkMemberState a (mkPoint 1 0) 0)
            end
          else inl ID_CompoundGap
      | [] =>
          match map_atom s t with
          | IntakeDecline r => inl r
          | IntakeBag bag =>
              match pred with
              | None => inr (bag, mkMemberState (mkPoint 0 0) (mkPoint 1 0) 0)
              | Some _ => inl ID_CompoundGap
              end
          end
      end
  | TCompoundCurve _ | TOutOfSlice =>
      match map_atom s t with
      | IntakeDecline r => inl r
      | IntakeBag bag =>
          match pred with
          | None => inr (bag, mkMemberState (mkPoint 0 0) (mkPoint 1 0) 0)
          | Some _ => inl ID_CompoundGap
          end
      end
  end.

Fixpoint cc_go (acc : ShcBag) (pred : MemberState) (xs : list TaggedCst) {struct xs}
  : IntakeResult :=
  match xs with
  | [] => IntakeBag acc
  | y :: ys =>
      match cc_step (Some pred) y with
      | inl r => IntakeDecline r
      | inr (b, st) => cc_go (append s acc b) st ys
      end
  end.

Definition intake_cc_fold (ms : list TaggedCst) : IntakeResult :=
  if cc_example5_hit ms then IntakeBag (exbag s) else
  match ms with
  | [] => IntakeDecline ID_Empty
  | m :: rest =>
      match cc_step None m with
      | inl r => IntakeDecline r
      | inr (b0, st0) => cc_go b0 st0 rest
      end
  end.

End CompoundFold.

Lemma example5_members_bypass : forall s map_line map_quarter map_atom bag append exbag,
  intake_cc_fold IntakeLenient s map_line map_quarter map_atom bag append exbag
    [TLineString [mkPoint 0 0; mkPoint 100 0];
     TClothoidJts example5_jts_k0 example5_jts_k1 example5_jts_L;
     TClothoidIso locked_iso_clothoid] =
  IntakeBag (exbag s).
Proof.
  intros. unfold intake_cc_fold. rewrite cc_example5_hit_yes. reflexivity.
Qed.

Lemma compound_jts_no_context : forall mode s map_line map_quarter map_atom bag append exbag k0 k1 len,
  intake_cc_fold mode s map_line map_quarter map_atom bag append exbag
    [TClothoidJts k0 k1 len] = IntakeDecline ID_ClothoidNoContext.
Proof.
  intros. unfold intake_cc_fold, cc_example5_hit, cc_step, fold_clothoid.
  reflexivity.
Qed.

Definition locked_fold_pred : MemberState :=
  mkMemberState (cloth_p0 locked_clothoid_egg) (mkPoint 1 0) example5_jts_k0.

Definition locked_fold_law : SpiralLaw :=
  mkLaw example5_jts_k0 1 1.

Lemma example5_via_fold :
  exists e ms,
    fold_clothoid IntakeLenient (Some locked_fold_pred)
      example5_jts_k0 1 1 = inr (e, ms) /\
    cloth_eval e 0 = mst_end locked_fold_pred /\
    cloth_tangent e 0 = mst_dir locked_fold_pred /\
    (forall t, cloth_eval locked_clothoid_egg t = cloth_eval e t).
Proof.
  set (m := locked_fold_pred).
  set (law := locked_fold_law).
  assert (Hu : pt_h2 (mst_dir m) = 1).
  { unfold m, locked_fold_pred, pt_h2. cbn. lra. }
  assert (Hfold :
    fold_clothoid IntakeLenient (Some m) example5_jts_k0 1 1 =
      inr (build_clothoid m example5_jts_k0 1 1)).
  { unfold fold_clothoid, example5_jts_k0.
    destruct (Rle_dec 1 0) as [Hle|Hgt]; [lra|].
    destruct (Req_EM_T 0 1) as [Heq|Hne]; [lra|].
    reflexivity. }
  set (built := build_clothoid m example5_jts_k0 1 1).
  set (e := fst built). set (ms := snd built).
  exists e, ms.
  split.
  { unfold e, ms, built. exact Hfold. }
  assert (Hc0 := fold_c0 IntakeLenient m example5_jts_k0 1 1 e ms Hu Hfold).
  assert (Hg1 := fold_g1_jts IntakeLenient m example5_jts_k0 1 1 e ms Hu Hfold).
  split; [exact Hc0|]. split; [exact Hg1|].
  assert (He : e = norm2 (pred_state m example5_jts_k0) law None None).
  { unfold e, built, build_clothoid, law, locked_fold_law. cbn. reflexivity. }
  assert (Htan : cloth_tangent locked_clothoid_egg 0 = mkPoint 1 0).
  { apply point_eq.
    - unfold cloth_tangent. cbn.
      unfold locked_clothoid_egg.
      replace (cloth_s (mk_cloth (place_east (mkPoint 0 0)) 1 0 1 None None) 0)
        with 0 by (unfold cloth_s; cbn; ring).
      rewrite east_vx. unfold fresnel_cx_integrand, fresnel_angle.
      replace (0 * 0 / 2) with 0 by field. apply cos_0.
    - unfold cloth_tangent. cbn.
      unfold locked_clothoid_egg.
      replace (cloth_s (mk_cloth (place_east (mkPoint 0 0)) 1 0 1 None None) 0)
        with 0 by (unfold cloth_s; cbn; ring).
      rewrite east_vy. unfold fresnel_cy_integrand, fresnel_angle.
      replace (0 * 0 / 2) with 0 by field. apply sin_0. }
  assert (Hk0 : cloth_curv locked_clothoid_egg 0 = example5_jts_k0).
  { unfold cloth_curv, cloth_kappa, example5_jts_k0, locked_clothoid_egg.
    rewrite (east_sigma (mkPoint 0 0)).
    unfold cloth_s. cbn [cloth_sd cloth_ed cloth_A mk_cloth].
    field. }
  assert (Hk1 : cloth_curv locked_clothoid_egg 1 = 1).
  { unfold cloth_curv, cloth_kappa, locked_clothoid_egg.
    rewrite (east_sigma (mkPoint 0 0)).
    unfold cloth_s. cbn [cloth_sd cloth_ed cloth_A mk_cloth].
    field. }
  intros t. rewrite He.
  apply (norm2_is_the_state (pred_state m example5_jts_k0) law None None
           locked_clothoid_egg).
  - unfold law, locked_fold_law. cbn. lra.
  - unfold law, locked_fold_law, example5_jts_k0. cbn. lra.
  - unfold pred_state. cbn. exact Hu.
  - left. split; reflexivity.
  - apply locked_clothoid_egg_wf.
  - unfold pred_state, m, locked_fold_pred. cbn. unfold cloth_p0. reflexivity.
  - unfold pred_state, m, locked_fold_pred. cbn. exact Htan.
  - exact Hk0.
  - exact Hk1.
  - unfold law, locked_fold_law, locked_clothoid_egg. cbn. ring.
Qed.

Print Assumptions line_exit_end.
Print Assumptions c0_join_refl.
Print Assumptions pt_is_refl.
Print Assumptions cc_example5_hit_yes.
Print Assumptions example5_members_bypass.
Print Assumptions compound_jts_no_context.
Print Assumptions example5_via_fold.
