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
   A multi-window CIRCULARSTRING exits at the last circ_windows
   arc_exit. An empty CIRCULARSTRING declines ID_Empty.
   example5_via_fold is the evaluation equality of fold_clothoid
   on law (example5_jts_k0, example5_jts_k1, example5_jts_L)
   from the example5 line exit. That egg is the norm2 egg of
   the example5 law. It is not locked_clothoid_egg shifted by
   (100,0): the windows are 80 and 1. example5_compound_gap is
   that fold's exit missing the locked start. The three-member
   compound still declines ID_CompoundGap. claimId: none.
   No Admitted. No classic. No MVT / Rolle / RiemannInt.
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance SheetHenCook IsoClothoidIntake IntakeSpiralJts
  IntakeSpiralFront SheetHenClothoidCore ClothoidNorm2 SignedCurvature
  SheetHenClothoidFrames SheetHenClothoidBounds CurveLength IntakeAnglesCore.
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

(* Same 2n+1 window split as the span carrier. The carrier imports
   the walker, so the definition lives here and is reused there. *)
Fixpoint circ_windows_from (a : Point) (pts : list Point) {struct pts}
  : list (Point * Point * Point) :=
  match pts with
  | m :: b :: rest => (a, m, b) :: circ_windows_from b rest
  | _ => []
  end.

Definition circ_windows (pts : list Point) : list (Point * Point * Point) :=
  match pts with
  | a :: rest => circ_windows_from a rest
  | [] => []
  end.

Fixpoint window_exit (w : Point * Point * Point)
  (rest : list (Point * Point * Point)) : MemberState :=
  match rest with
  | [] => let '(a, m, b) := w in ArcMemberState.arc_exit a m b
  | w2 :: rs => window_exit w2 rs
  end.

Lemma check_c0_at_end : forall m p, p = mst_end m -> check_c0 (Some m) p = true.
Proof.
  intros m p H. rewrite H. unfold check_c0. apply c0_join_refl.
Qed.

Lemma c0_join_px_false : forall p q, px p <> px q -> c0_join p q = false.
Proof.
  intros [x1 y1] [x2 y2] H. unfold c0_join. cbn in *.
  destruct (Req_EM_T x1 x2) as [He|Hne].
  - exfalso. apply H. exact He.
  - reflexivity.
Qed.

Section CompoundFold.
Variable mode : IntakeMode.
Variable s : Sheet.
Variable map_line : Sheet -> list Point -> ShcBag.
Variable map_quarter : Sheet -> ShcBag.
Variable map_atom : Sheet -> TaggedCst -> IntakeResult.
Variable bag_of : Sheet -> ClothoidEgg -> ShcBag.
Variable append : Sheet -> ShcBag -> ShcBag -> ShcBag.

Definition with_exit (sl : CircSlice) (t : TaggedCst) (st : MemberState)
  : IntakeDeclineReason + (ShcBag * MemberState) :=
  match sl with
  | CircQuarter => inr (map_quarter s, st)
  | _ =>
      match map_atom s t with
      | IntakeDecline r => inl r
      | IntakeBag b => inr (b, st)
      end
  end.

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
  | TCircularString sl pts =>
      match pts with
      | [] => inl ID_Empty
      | a :: m :: b :: [] =>
          if check_c0 pred a then with_exit sl t (ArcMemberState.arc_exit a m b)
          else inl ID_CompoundGap
      | a :: _ =>
          match circ_windows pts with
          | [] => inl ID_BadPointCount
          | w :: rest =>
              if check_c0 pred a then with_exit sl t (window_exit w rest)
              else inl ID_CompoundGap
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
  match ms with
  | [] => IntakeDecline ID_Empty
  | m :: rest =>
      match cc_step None m with
      | inl r => IntakeDecline r
      | inr (b0, st0) => cc_go b0 st0 rest
      end
  end.

End CompoundFold.

Lemma compound_jts_no_context : forall mode s map_line map_quarter map_atom bag append k0 k1 len,
  intake_cc_fold mode s map_line map_quarter map_atom bag append
    [TClothoidJts k0 k1 len] = IntakeDecline ID_ClothoidNoContext.
Proof.
  intros. unfold intake_cc_fold, cc_step, fold_clothoid. reflexivity.
Qed.

Lemma empty_cs_declines : forall mode s map_line map_quarter map_atom bag append sl,
  intake_cc_fold mode s map_line map_quarter map_atom bag append
    [TCircularString sl []] = IntakeDecline ID_Empty.
Proof.
  intros. unfold intake_cc_fold, cc_step. reflexivity.
Qed.

Definition example5_line : MemberState :=
  line_exit (mkPoint 0 0) (mkPoint 100 0).

Definition example5_law : SpiralLaw :=
  mkLaw example5_jts_k0 example5_jts_k1 example5_jts_L.

Definition example5_egg : ClothoidEgg :=
  norm2 (pred_state example5_line example5_jts_k0) example5_law None None.

Lemma example5_via_fold :
  exists e ms,
    fold_clothoid IntakeLenient (Some example5_line)
      example5_jts_k0 example5_jts_k1 example5_jts_L = inr (e, ms) /\
    cloth_eval e 0 = mst_end example5_line /\
    cloth_tangent e 0 = mst_dir example5_line /\
    (forall t, cloth_eval e t = cloth_eval example5_egg t).
Proof.
  destruct (example5_fold IntakeLenient) as [e [ms [Hf [Hc0 [Hg1 _]]]]].
  exists e, ms.
  split. { exact Hf. }
  split. { exact Hc0. }
  split. { exact Hg1. }
  intros t.
  destruct (fold_hit_egg IntakeLenient example5_line example5_jts_k0
              example5_jts_k1 example5_jts_L e ms Hf)
    as [_ [_ [He _]]].
  rewrite He. unfold example5_egg, build_clothoid. cbn. reflexivity.
Qed.

Lemma example5_end_misses_origin : forall e,
  cloth_eval e 0 = mkPoint 100 0 ->
  is_curve_length (cloth_eval e) 0 1 example5_jts_L ->
  px (cloth_eval e 1) <> 0.
Proof.
  intros e H0 HL Heq.
  assert (Hch : dist (cloth_eval e 0) (cloth_eval e 1) <= 80).
  { unfold example5_jts_L in HL.
    apply curve_length_ge_chord; [lra | exact HL]. }
  rewrite H0 in Hch.
  assert (Hsq : dist_sq (mkPoint 100 0) (cloth_eval e 1) =
                100 * 100 + py (cloth_eval e 1) * py (cloth_eval e 1)).
  { unfold dist_sq. cbn [px py]. rewrite Heq. ring. }
  assert (Hge : 100 <= dist (mkPoint 100 0) (cloth_eval e 1)).
  { unfold dist. rewrite Hsq.
    apply Rle_trans with (sqrt (100 * 100)).
    - rewrite (sqrt_square 100); lra.
    - apply sqrt_le_1.
      + lra.
      + apply Rplus_le_le_0_compat; [lra | apply Rle_0_sqr].
      + apply Rle_trans with (100 * 100 + 0).
        * right. ring.
        * apply Rplus_le_compat_l. apply Rle_0_sqr. }
  lra.
Qed.

Definition fixture_arc_pts : list Point :=
  [mkPoint 0 0; mkPoint 1 0; mkPoint 1 1; mkPoint 0 1; mkPoint 0 2].

Definition fixture_last_exit : MemberState :=
  ArcMemberState.arc_exit (mkPoint 1 1) (mkPoint 0 1) (mkPoint 0 2).

Lemma fixture_windows :
  circ_windows fixture_arc_pts =
    [(mkPoint 0 0, mkPoint 1 0, mkPoint 1 1);
     (mkPoint 1 1, mkPoint 0 1, mkPoint 0 2)].
Proof. reflexivity. Qed.

Lemma fixture_last_is_exit :
  window_exit (mkPoint 0 0, mkPoint 1 0, mkPoint 1 1)
    [(mkPoint 1 1, mkPoint 0 1, mkPoint 0 2)] = fixture_last_exit.
Proof. reflexivity. Qed.

Lemma fixture_last_denoms :
  dist_sq (mkPoint 1 1) (mkPoint 0 1) <> 0 /\
  dist_sq (mkPoint 0 1) (mkPoint 0 2) <> 0 /\
  dist_sq (mkPoint 1 1) (mkPoint 0 2) <> 0 /\
  circ_denom (mkPoint 1 1) (mkPoint 0 1) (mkPoint 0 2) <> 0.
Proof.
  unfold dist_sq, circ_denom. cbn. lra.
Qed.

Lemma pt_h2_agree : forall p, pt_h2 p = ArcMemberState.pt_h2 p.
Proof. intros [x y]. unfold pt_h2, ArcMemberState.pt_h2. reflexivity. Qed.

Lemma fixture_last_unit : pt_h2 (mst_dir fixture_last_exit) = 1.
Proof.
  rewrite pt_h2_agree.
  destruct fixture_last_denoms as [Ham [Hmb [Hab Hd]]].
  apply (ArcMemberState.arc_exit_dir_unit (mkPoint 1 1) (mkPoint 0 1)
           (mkPoint 0 2) Ham Hmb Hab Hd).
Qed.

Lemma locked_clothoid_at_0 :
  cloth_eval locked_clothoid_egg 0 = mkPoint 0 0.
Proof.
  unfold locked_clothoid_egg.
  rewrite (eval_east_01 (mkPoint 0 0) 0).
  rewrite cloth_Cx_0, cloth_Cy_0. cbn [px py].
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma example5_fold_exit : forall e ms,
  fold_clothoid IntakeLenient (Some example5_line)
    example5_jts_k0 example5_jts_k1 example5_jts_L = inr (e, ms) ->
  mst_end ms = cloth_eval e 1.
Proof.
  intros e ms H.
  destruct (fold_hit_egg _ _ _ _ _ _ _ H) as [_ [_ [He Hms]]].
  rewrite Hms, He. unfold build_clothoid, cloth_exit. cbn. reflexivity.
Qed.

(* The JTS fold of the example5 law exits off the locked egg's
   start. locked_clothoid_egg is the ISO atom; this fold is not. *)
Lemma example5_compound_gap : forall e ms,
  fold_clothoid IntakeLenient (Some example5_line)
    example5_jts_k0 example5_jts_k1 example5_jts_L = inr (e, ms) ->
  mst_end ms <> cloth_eval locked_clothoid_egg 0.
Proof.
  intros e ms H Heq.
  rewrite (example5_fold_exit e ms H) in Heq.
  rewrite locked_clothoid_at_0 in Heq.
  destruct example5_line_unit as [Hu [Hp _]].
  unfold example5_line in Hu, Hp, H.
  assert (Hpx : px (cloth_eval e 1) <> 0).
  { apply example5_end_misses_origin.
    - rewrite (fold_c0 IntakeLenient (line_exit (mkPoint 0 0) (mkPoint 100 0))
                 example5_jts_k0 example5_jts_k1 example5_jts_L e ms Hu H).
      exact Hp.
    - apply (proj2 (fold_length IntakeLenient
                     (line_exit (mkPoint 0 0) (mkPoint 100 0))
                     example5_jts_k0 example5_jts_k1 example5_jts_L
                     e ms Hu H)). }
  apply Hpx. rewrite Heq. reflexivity.
Qed.

(* example5_two_spellings (pointwise eval of the JTS norm2 egg equals
   the locked egg plus (100,0)) is false. clothoid_state_unique does
   not apply: the windows and the end curvatures differ. The ISO atom
   is locked_clothoid_egg; the JTS member is example5_egg. *)
Lemma example5_members_differ :
  cloth_A locked_clothoid_egg = 1 /\
  cloth_ed locked_clothoid_egg - cloth_sd locked_clothoid_egg = 1 /\
  cloth_eval locked_clothoid_egg 0 = mkPoint 0 0 /\
  cloth_curv locked_clothoid_egg 1 = 1 /\
  cloth_A example5_egg * cloth_A example5_egg = 16000 /\
  cloth_ed example5_egg - cloth_sd example5_egg = 80 /\
  cloth_eval example5_egg 0 = mkPoint 100 0 /\
  cloth_curv example5_egg 1 = 5 / 1000 /\
  cloth_ed example5_egg - cloth_sd example5_egg <>
    cloth_ed locked_clothoid_egg - cloth_sd locked_clothoid_egg /\
  cloth_curv example5_egg 1 <> cloth_curv locked_clothoid_egg 1.
Proof.
  assert (HlA : cloth_A locked_clothoid_egg = 1) by reflexivity.
  assert (HlW : cloth_ed locked_clothoid_egg - cloth_sd locked_clothoid_egg = 1).
  { unfold locked_clothoid_egg. cbn. ring. }
  assert (Hl0 : cloth_eval locked_clothoid_egg 0 = mkPoint 0 0).
  { exact locked_clothoid_at_0. }
  assert (Hlk : cloth_curv locked_clothoid_egg 1 = 1).
  { unfold cloth_curv, cloth_kappa.
    assert (Hs : cloth_s locked_clothoid_egg 1 = 1).
    { unfold cloth_s, locked_clothoid_egg. cbn. ring. }
    rewrite Hs. unfold locked_clothoid_egg.
    rewrite (east_sigma (mkPoint 0 0)).
    change (cloth_A (mk_cloth (place_east (mkPoint 0 0)) 1 0 1 None None))
      with 1.
    unfold Rdiv. field. }
  assert (HjA : cloth_A example5_egg * cloth_A example5_egg = 16000).
  { unfold example5_egg, cloth_A, norm2, mk_cloth.
    cbn [cloth_A].
    assert (HA : law_A example5_law * law_A example5_law = law_A2 example5_law).
    { apply law_A_sq.
      - unfold example5_law, example5_jts_L. cbn. lra.
      - unfold example5_law, example5_jts_k0, example5_jts_k1. cbn. lra. }
    rewrite HA. unfold example5_law, example5_jts_k0, example5_jts_k1,
      example5_jts_L. exact example5_A2. }
  assert (HjW : cloth_ed example5_egg - cloth_sd example5_egg = 80).
  { unfold example5_egg, norm2, mk_cloth. cbn [cloth_ed cloth_sd].
    unfold example5_law. rewrite law_ed_sd.
    - unfold example5_jts_L. reflexivity.
    - cbn. unfold example5_jts_k0, example5_jts_k1. intro E. lra. }
  assert (Hj0 : cloth_eval example5_egg 0 = mkPoint 100 0).
  { destruct example5_line_unit as [Hu [Hp _]].
    unfold example5_egg.
    rewrite (norm2_start (pred_state example5_line example5_jts_k0)
                         example5_law None None Hu).
    unfold pred_state, example5_line. cbn [st_pos]. exact Hp. }
  assert (Hjk : cloth_curv example5_egg 1 = 5 / 1000).
  { destruct example5_line_unit as [Hu _].
    assert (HL : 0 < sl_len (mkLaw example5_jts_k0 example5_jts_k1
                               example5_jts_L)).
    { unfold example5_jts_L. cbn. lra. }
    assert (Hne : sl_k0 (mkLaw example5_jts_k0 example5_jts_k1
                           example5_jts_L) <>
                  sl_k1 (mkLaw example5_jts_k0 example5_jts_k1
                           example5_jts_L)).
    { cbn. unfold example5_jts_k0, example5_jts_k1. intro E. lra. }
    unfold example5_egg, example5_law.
    rewrite (proj2 (norm2_curv
              (pred_state example5_line example5_jts_k0)
              (mkLaw example5_jts_k0 example5_jts_k1 example5_jts_L)
              None None HL Hne Hu)).
    unfold example5_jts_k1. reflexivity. }
  repeat split; try assumption.
  - rewrite HjW, HlW. lra.
  - rewrite Hjk, Hlk. lra.
Qed.

(* The line joins the JTS fold of the example5 law. The ISO egg
   starts at the origin, and that fold's end is not the origin, so
   the three-member compound declines ID_CompoundGap. *)
Lemma example5_cc_fold_declines :
  forall s map_line map_quarter map_atom bag append,
  intake_cc_fold IntakeLenient s map_line map_quarter map_atom bag append
    [TLineString [mkPoint 0 0; mkPoint 100 0];
     TClothoidJts example5_jts_k0 example5_jts_k1 example5_jts_L;
     TClothoidIso locked_iso_clothoid] = IntakeDecline ID_CompoundGap.
Proof.
  intros s map_line map_quarter map_atom bag append.
  destruct (example5_fold IntakeLenient) as [e [ms [Hfold [Hc0 [_ [_ _]]]]]].
  destruct example5_line_unit as [Hu _].
  assert (Hlen := proj2 (fold_length IntakeLenient
    (line_exit (mkPoint 0 0) (mkPoint 100 0))
    example5_jts_k0 example5_jts_k1 example5_jts_L e ms Hu Hfold)).
  assert (Hmiss : px (cloth_eval e 1) <> 0).
  { apply example5_end_misses_origin; [exact Hc0 | exact Hlen]. }
  assert (Hend : mst_end ms = cloth_eval e 1).
  { apply example5_fold_exit. unfold example5_line. exact Hfold. }
  assert (Hline :
    @cc_step IntakeLenient s map_line map_quarter map_atom bag
      None (TLineString [mkPoint 0 0; mkPoint 100 0]) =
    inr (map_line s [mkPoint 0 0; mkPoint 100 0],
         line_exit (mkPoint 0 0) (mkPoint 100 0))).
  { reflexivity. }
  assert (Hjts :
    @cc_step IntakeLenient s map_line map_quarter map_atom bag
      (Some (line_exit (mkPoint 0 0) (mkPoint 100 0)))
      (TClothoidJts example5_jts_k0 example5_jts_k1 example5_jts_L) =
    inr (bag s e, ms)).
  { unfold cc_step. rewrite Hfold. rewrite Hc0.
    rewrite check_c0_at_end by (symmetry; apply line_exit_end).
    reflexivity. }
  assert (Hiso :
    @cc_step IntakeLenient s map_line map_quarter map_atom bag
      (Some ms) (TClothoidIso locked_iso_clothoid) = inl ID_CompoundGap).
  { unfold cc_step. rewrite locked_iso_try. rewrite locked_clothoid_at_0.
    unfold check_c0.
    rewrite (c0_join_px_false (mst_end ms) (mkPoint 0 0)).
    - reflexivity.
    - rewrite Hend. cbn. exact Hmiss. }
  unfold intake_cc_fold. rewrite Hline. cbn [cc_go].
  rewrite Hjts. cbn [cc_go]. rewrite Hiso. reflexivity.
Qed.

(* Fixture. The example5 line followed by its JTS clothoid is a bag.
   The three-member compound adds the locked ISO atom and declines. *)
Lemma example5_line_jts_bags :
  forall s map_line map_quarter map_atom bag append,
  exists e,
    intake_cc_fold IntakeLenient s map_line map_quarter map_atom bag append
      [TLineString [mkPoint 0 0; mkPoint 100 0];
       TClothoidJts example5_jts_k0 example5_jts_k1 example5_jts_L] =
      IntakeBag (append s (map_line s [mkPoint 0 0; mkPoint 100 0]) (bag s e)).
Proof.
  intros s map_line map_quarter map_atom bag append.
  destruct (example5_fold IntakeLenient) as [e [ms [Hfold [Hc0 _]]]].
  exists e.
  assert (Hline :
    @cc_step IntakeLenient s map_line map_quarter map_atom bag
      None (TLineString [mkPoint 0 0; mkPoint 100 0]) =
    inr (map_line s [mkPoint 0 0; mkPoint 100 0],
         line_exit (mkPoint 0 0) (mkPoint 100 0))).
  { reflexivity. }
  assert (Hjts :
    @cc_step IntakeLenient s map_line map_quarter map_atom bag
      (Some (line_exit (mkPoint 0 0) (mkPoint 100 0)))
      (TClothoidJts example5_jts_k0 example5_jts_k1 example5_jts_L) =
    inr (bag s e, ms)).
  { unfold cc_step. rewrite Hfold. rewrite Hc0.
    rewrite check_c0_at_end by (symmetry; apply line_exit_end).
    reflexivity. }
  unfold intake_cc_fold. rewrite Hline. cbn [cc_go].
  rewrite Hjts. cbn [cc_go]. reflexivity.
Qed.

(* Fixture. A two-arc CIRCULARSTRING followed by a LINESTRING that
   starts at the string's last point is a bag. A JTS clothoid after
   the same string starts on the last window's tangent. *)
Lemma fixture_multi_arc_cs_join :
  forall s map_line map_quarter map_atom bag append,
  intake_cc_fold IntakeLenient s map_line map_quarter map_atom bag append
    [TCircularString CircQuarter fixture_arc_pts;
     TLineString [mkPoint 0 2; mkPoint 3 2]] =
    IntakeBag (append s (map_quarter s)
                 (map_line s [mkPoint 0 2; mkPoint 3 2])) /\
  exists e,
    intake_cc_fold IntakeLenient s map_line map_quarter map_atom bag append
      [TCircularString CircQuarter fixture_arc_pts; TClothoidJts 0 1 1] =
      IntakeBag (append s (map_quarter s) (bag s e)) /\
    cloth_tangent e 0 = mst_dir fixture_last_exit.
Proof.
  intros s map_line map_quarter map_atom bag append.
  assert (Hcs :
    @cc_step IntakeLenient s map_line map_quarter map_atom bag
      None (TCircularString CircQuarter fixture_arc_pts) =
    inr (map_quarter s, fixture_last_exit)).
  { unfold cc_step, fixture_arc_pts, circ_windows, circ_windows_from, with_exit.
    rewrite fixture_last_is_exit. reflexivity. }
  split.
  - assert (Hln :
      @cc_step IntakeLenient s map_line map_quarter map_atom bag
        (Some fixture_last_exit)
        (TLineString [mkPoint 0 2; mkPoint 3 2]) =
      inr (map_line s [mkPoint 0 2; mkPoint 3 2],
           line_exit (mkPoint 0 2) (mkPoint 3 2))).
    { unfold cc_step, line_last, fixture_last_exit.
      rewrite check_c0_at_end by reflexivity. reflexivity. }
    unfold intake_cc_fold. rewrite Hcs. cbn [cc_go].
    rewrite Hln. cbn [cc_go]. reflexivity.
  - set (m := fixture_last_exit).
    assert (Hu := fixture_last_unit). fold m in Hu.
    set (b := build_clothoid m 0 1 1).
    set (e := fst b).
    assert (Hfoldb : fold_clothoid IntakeLenient (Some m) 0 1 1 = inr b).
    { unfold fold_clothoid, b.
      destruct (Rle_dec 1 0) as [Hle|Hgt]; [lra|].
      destruct (Req_EM_T 0 1) as [Heq|Hne]; [lra|].
      reflexivity. }
    assert (Hfold : fold_clothoid IntakeLenient (Some m) 0 1 1 = inr (e, snd b)).
    { rewrite Hfoldb. unfold e. rewrite <- (surjective_pairing b). reflexivity. }
    assert (Hc0 := fold_c0 IntakeLenient m 0 1 1 e (snd b) Hu Hfold).
    assert (Hg1 := fold_g1_jts IntakeLenient m 0 1 1 e (snd b) Hu Hfold).
    assert (Hcl :
      @cc_step IntakeLenient s map_line map_quarter map_atom bag
        (Some m) (TClothoidJts 0 1 1) = inr (bag s e, snd b)).
    { unfold cc_step. rewrite Hfold. rewrite Hc0.
      rewrite check_c0_at_end by reflexivity. reflexivity. }
    exists e. split; [|exact Hg1].
    unfold intake_cc_fold. fold m in Hcs. rewrite Hcs. cbn [cc_go].
    rewrite Hcl. cbn [cc_go]. reflexivity.
Qed.

Print Assumptions line_exit_end.
Print Assumptions c0_join_refl.
Print Assumptions check_c0_at_end.
Print Assumptions c0_join_px_false.
Print Assumptions compound_jts_no_context.
Print Assumptions empty_cs_declines.
Print Assumptions example5_via_fold.
Print Assumptions example5_end_misses_origin.
Print Assumptions fixture_windows.
Print Assumptions fixture_last_is_exit.
Print Assumptions fixture_last_denoms.
Print Assumptions pt_h2_agree.
Print Assumptions fixture_last_unit.
Print Assumptions locked_clothoid_at_0.
Print Assumptions example5_fold_exit.
Print Assumptions example5_compound_gap.
Print Assumptions example5_members_differ.
Print Assumptions example5_cc_fold_declines.
Print Assumptions example5_line_jts_bags.
Print Assumptions fixture_multi_arc_cs_join.
