(* ============================================================================
   NetTopologySuite.Proofs.IntakeWalker
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: first-slice intake walker
   (claimId 0007-intake-walker). Needle AFTER Γ (MkCirc / CircGamma
   #724). One grammar, one mapping table, one bag.

   Successful WKT parse → tagged CST only → mapper total
   (CST × Sheet S) → SHC bag | Intake Decline(reason).
   Grammar accept ≠ valid geometry ≠ cooked graph.
   Intake Decline ≠ cook IDecline. Mapper is thin: no noding,
   no split(t), no snap lattice, no intersection hens.
   Self-overlapping WKT still literal chickens.

   Grammar source of truth: antlr/grammars-v4 PR #4997
   (MERGED 2026-09-08, merge 181f4c9). ISO/IEC 13249-3 §5.1.67.
   Pin lives in tools/WktIntakeWalker/grammar/. Do not invent
   productions. Do not treat example3.txt as an oracle source.

   First slice (what SheetHenCook already inhabited):
     Point, LineString, CircularString, CompoundCurve of those
     two, Circle as two half-span MkCirc (sweep ±π).
   Reuses MkChord / MkCirc. Clothoid is the MkClothoid letter
   in this module (same mapper table). No Fresnel host γ.

   GeodesicString (claimId 0007-intake-geodesic): well-formed
   pts (n≥2, same empty/bad-count as map_ls) bag map_ls S pts
   (MkChord). Sheet geodesic = chord. No MkGeodesic. Non-clothoid
   SPIRAL declines. ID_GeodesicString is not the well-formed
   answer. Not ellipsoid / WKB 13 / emit / first-cook expand.

   SpiralOther declines ID_SpiralOther. A clothoid spiral
   bags norm2 or a named Decline (IntakeSpiralFront).
   CircUnknown well-formed CS/Circle now maps
   through IntakeAngles (claimId 0007-intake-angles): chart
   θ₀/Δθ via 3-axiom atan2, then MkCirc chickens.
   Collinear / duplicate / bad count / empty / zero-radius
   Decline by name. NO silent chord demote at intake. Demote
   is later cook/view. ID_CircGammaLeftover stays on the type
   (first-slice leftover name) but is not the well-formed
   unknown-CS answer.

   Clothoid (claimId 0007-intake-mkclothoid, not reminted):
   one host MkClothoid. ISO fields are normalizer 1 in
   IsoClothoidIntake (direct copy, not an ISO formula).
   Similarity frame or a named Decline. The locked fixture's
   fields map to locked_clothoid_egg (eval-level). JTS
   example5 (0, 5/1000, 80) is that bag; L <= 0 and other
   triples decline by name. example5 bags both.
   ID_IsoClothoid is not the well-formed answer.
   Clothoid×clothoid stays not-first-cook / IDecline.

   Mode D (host endpoints on locked CC LS+CS):
     map_cc_locked members share the host joint
     chord_eval (mkChordEgg p00 p50) 1
       = circ_eval locked_circ_A 0.
     append_bags is hen offset, not geometry. LS–CS is host
     I_ok Hit at the joint (in-scope). No CompoundEgg /
     cs_eval. claimId 0007 kept; witnesses
     0007-B.2-cc-member-joints / 0007-B-mixed-ls-cs-joints
     kept (not reminted).

   ISO CIRCLE(A,B,C) is a full turn from A (θ₀ = angle of A,
   sweep ±2π) at egg level. The bag is A→antipode→A, two
   MkCirc of sweep ±π. Not a src=dst chicken.
   ADR-0005: intake_map is IntakeLenient. CIRCULARSTRING(A,B,A)
   with B≠A normalizes to CIRCLE(A,B,ogc_c) (CW). IntakeStrict
   Declines ID_CsClosedDegenerate. try_cs_eggs still Declines.

   Visitor tags locked CircularString / Circle shapes (exact
   control-point match). Mapper is structural on those tags.
   CircUnknown uses IntakeAngles (chart + 3-axiom atan2 / atan3;
   Req_EM_T on denom / duplicates; no Stdlib Ratan).

   What this is not:
     WKB-order Γ walk / Table 15. Lesson-1 packaging remints.
     WKT zoo / example3.txt oracle source. H⊥ / cathedral
     Landed / Campaign II remint-as-product / 522-n /
     Shewchuk/Hobby/Priest/full Jordan / MerkatorBV.
     Noding / cook / 𝓘 beyond wiring mapper output into
     existing bag consumers. New oracle keyword (ADR-0006).

   ADR-0007 is Accepted (2026-09-07). This letter does not
   reopen Status. ADR-0006 Status stays Accepted. Testable
   𝓘 / cook results stay on the accepted Oracle line protocol.

   WITNESS topic: overlay / core · claimId: 0007-intake-walker
   witness: 0007-intake-walker
   also: 0007-intake-mkclothoid, 0007-intake-geodesic
   also: 0007-B.2-cc-member-joints, 0007-B-mixed-ls-cs-joints
   board: ADR-0007
   3-axiom host. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6, Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance SheetHenCook CircularCookMkCirc IntakeAngles IntakeCircle IsoClothoidIntake IntakeSpiralJts IntakeSpiralFront.
Import ListNotations.
Local Open Scope R_scope.
Local Open Scope list_scope.

(* -------------------------------------------------------------------------- *)
(* Tagged CST. Grammar accept only. ≠ valid geometry ≠ cooked graph.          *)
(* CircSlice is the visitor's locked-shape tag — not a second grammar.        *)
(* -------------------------------------------------------------------------- *)

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

(* Intake Decline. Distinct type from cook IResult / IDecline. *)
Inductive IntakeDeclineReason : Type :=
| ID_Empty
| ID_BadPointCount
| ID_GeodesicString
| ID_SpiralCurve
| ID_SpiralOther
| ID_SpiralClothoidNotYet
| ID_SpiralNonPositiveLength
| ID_SpiralConstantCurvature
| ID_IsoClothoid
| ID_MkOutOfScope
| ID_CircGammaLeftover
| ID_Collinear
| ID_DuplicateControl
| ID_DegenerateArc
| ID_CsClosedDegenerate
| ID_SpanMismatch
| ID_MissingMeasure
| ID_UnexpectedMeasure
| ID_NotSimilarityFrame
| ID_NonPositiveScale
| ID_DegenerateWindow
| ID_TiltedPlacement
| ID_JtsClothoidNotYet
| ID_JtsNonPositiveLength
| ID_JtsConstantCurvature
| ID_ClothoidCurvatureJump
| ID_ClothoidNoContext
| ID_NotFirstSlice.

Definition angle_fail_reason (f : AngleFail) : IntakeDeclineReason :=
  match f with
  | AF_Empty => ID_Empty
  | AF_BadCount => ID_BadPointCount
  | AF_Duplicate => ID_DuplicateControl
  | AF_Collinear => ID_Collinear
  | AF_Degenerate => ID_DegenerateArc
  | AF_CsClosedDegenerate => ID_CsClosedDegenerate
  | AF_SpanMismatch => ID_SpanMismatch
  end.

Record ShcBag : Type := mkShcBag {
  bag_sheet : Sheet;
  bag_hens : list Hen;
  bag_pts : list Point;
  bag_chickens : list Chicken
}.

Inductive IntakeResult : Type :=
| IntakeBag : ShcBag -> IntakeResult
| IntakeDecline : IntakeDeclineReason -> IntakeResult.

Lemma intake_bag_neq_decline :
  forall b r, IntakeBag b <> IntakeDecline r.
Proof.
  intros b r H. discriminate.
Qed.

Lemma cook_ihit_neq_idecline :
  forall p ti tj, IHit p ti tj <> IDecline.
Proof.
  intros. apply IHit_neq_IDecline.
Qed.

Definition grammar_accept_not_valid : Prop := True.
Definition grammar_accept_not_cooked : Prop := True.

Lemma grammar_accept_is_cst_only :
  grammar_accept_not_valid /\ grammar_accept_not_cooked.
Proof.
  split; exact I.
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked first-slice fixtures. Reuse host MkChord / MkCirc.                  *)
(* -------------------------------------------------------------------------- *)

Definition p00 : Point := mkPoint 0 0.
Definition p20 : Point := mkPoint 2 0.
Definition p50 : Point := mkPoint 5 0.
Definition p05 : Point := mkPoint 0 5.
Definition p_m50 : Point := mkPoint (-5) 0.

Definition locked_point_cst : TaggedCst := TPoint p00.
Definition locked_ls_cst : TaggedCst := TLineString [p00; p20].
Definition locked_geodesic_cst : TaggedCst := TGeodesicString [p00; p20].
Definition locked_ls3_cst : TaggedCst := TLineString [p00; p20; p50].
Definition locked_geodesic3_cst : TaggedCst := TGeodesicString [p00; p20; p50].
Definition locked_cs_quarter_cst : TaggedCst :=
  TCircularString CircQuarter [p50; circ_eval locked_circ_A (1 / 2); p05].
Definition locked_circle_cst : TaggedCst :=
  TCircle CircFullOgc [p50; p05; p_m50].
Definition locked_cs_full_ogc_cst : TaggedCst :=
  TCircularString CircFullOgc [p50; p05; p50].
Definition locked_cc_cst : TaggedCst :=
  TCompoundCurve [TLineString [p00; p50]; locked_cs_quarter_cst].

(* example5.txt (grammars-v4 #4997): ISO clothoid; then one COMPOUNDCURVE
   carrying JTS (k0,k1,L) and ISO REFERENCELOCATION forms. *)
Definition example5_jts_cst : TaggedCst :=
  TClothoidJts example5_jts_k0 example5_jts_k1 example5_jts_L.
Definition spiral_bloss : TaggedCst :=
  TSpiralCurve (SpiralOther SOK_Bloss).
Definition example5_iso_clothoid_cst : TaggedCst :=
  TClothoidIso locked_iso_clothoid.
Definition example5_cc_both_clothoid_cst : TaggedCst :=
  TCompoundCurve [TLineString [p00; mkPoint 100 0]; example5_jts_cst;
    TClothoidIso locked_iso_clothoid].

Definition locked_full_circle_egg : CircularEgg :=
  mkCircularEgg (mkPoint 0 0) 5 0 (2 * PI).

Definition locked_half_fst : CircularEgg :=
  mkCircularEgg (mkPoint 0 0) 5 0 PI.

Definition locked_half_snd : CircularEgg :=
  mkCircularEgg (mkPoint 0 0) 5 PI PI.

Definition unknown_cs_cst : TaggedCst :=
  TCircularString CircUnknown [p00; p20; mkPoint 3 1].

Definition overlap_ls_cst : TaggedCst :=
  TLineString [p00; p20; p00].

(* -------------------------------------------------------------------------- *)
(* Thin mapper. Total on TaggedCst × Sheet. No noding / split / snap.         *)
(* -------------------------------------------------------------------------- *)

Definition hens_of_n (n : nat) : list Hen := seq 0 n.

(* Recurse on the structural tail. `q :: rest` is a rebuilt cons, so Rocq
   cannot see a decreasing argument if we pass that reconstructed list. *)
Fixpoint chords_of_pts (pts : list Point) (h0 : nat) {struct pts} : list Chicken :=
  match pts with
  | [] => []
  | p :: rest =>
      match rest with
      | [] => []
      | q :: _ =>
          mkChicken h0 (S h0) (MkChord (mkChordEgg p q))
            :: chords_of_pts rest (S h0)
      end
  end.

Definition map_point (s : Sheet) (p : Point) : ShcBag :=
  mkShcBag s [0%nat] [p] [].

Definition map_ls (s : Sheet) (pts : list Point) : ShcBag :=
  mkShcBag s (hens_of_n (length pts)) pts (chords_of_pts pts 0%nat).

Definition map_cs_from_build (s : Sheet)
  (eggs : list CircularEgg) (ends : list Point) : ShcBag :=
  mkShcBag s (hens_of_n (length ends)) ends (circ_chickens eggs 0%nat).

Definition map_circle_of (s : Sheet) (eggs : list CircularEgg) (ends : list Point)
  : ShcBag :=
  match eggs with
  | [e1; e2] => mkShcBag s [0%nat; 1%nat] ends (circle_cycle e1 e2)
  | _ => mkShcBag s [] [] []
  end.

Definition map_circle_unknown (s : Sheet) (pts : list Point) : IntakeResult :=
  match try_circle_eggs pts with
  | inr f => IntakeDecline (angle_fail_reason f)
  | inl (eggs, ends) => IntakeBag (map_circle_of s eggs ends)
  end.

(* WKT CircUnknown: points only, so try_cs_eggs / egg_of_points.
   Carried angles are IntakeCarried.map_cs_carried, not this path.
   ADR-0005 lenient: a 3-control string with first = last and B≠A
   is CIRCLE(A, B, ogc_c). ogc_c is the CW completion
   (centre midpoint(A,B), radius |AB|/2). GEOS linearizes that
   collinear triple clockwise; behavioural reference only.
   A=B still Declines. *)
Definition map_cs_from_try (s : Sheet) (pts : list Point) : IntakeResult :=
  match try_cs_eggs pts with
  | inr f => IntakeDecline (angle_fail_reason f)
  | inl (eggs, ends) => IntakeBag (map_cs_from_build s eggs ends)
  end.

Definition map_cs_unknown (s : Sheet) (pts : list Point) : IntakeResult :=
  match pts with
  | a :: b :: c :: [] =>
      if Req_EM_T (dist_sq a c) 0 then
        if Req_EM_T (dist_sq a b) 0 then IntakeDecline ID_CsClosedDegenerate
        else map_circle_unknown s [a; b; ogc_c a b]
      else map_cs_from_try s pts
  | _ => map_cs_from_try s pts
  end.

Definition map_cs_quarter (s : Sheet) : ShcBag :=
  mkShcBag s [0%nat; 1%nat] [p50; p05]
    [mkChicken 0%nat 1%nat (MkCirc locked_circ_A)].

Definition map_circle (s : Sheet) : ShcBag :=
  mkShcBag s [0%nat; 1%nat] [p50; p_m50]
    (circle_cycle locked_half_fst locked_half_snd).

Definition shift_chicken (off : nat) (c : Chicken) : Chicken :=
  mkChicken (off + ck_src c)%nat (off + ck_dst c)%nat (ck_egg c).

Definition append_bags (s : Sheet) (a b : ShcBag) : ShcBag :=
  let off := length (bag_hens a) in
  mkShcBag s
    (bag_hens a ++ map (fun h => (off + h)%nat) (bag_hens b))
    (bag_pts a ++ bag_pts b)
    (bag_chickens a ++ map (shift_chicken off) (bag_chickens b)).

Definition map_cc_locked (s : Sheet) : ShcBag :=
  append_bags s
    (mkShcBag s [0%nat; 1%nat] [p00; p50]
       [mkChicken 0%nat 1%nat (MkChord (mkChordEgg p00 p50))])
    (map_cs_quarter s).

(* ISO map_clothoid reads its fields. JTS hits only example5.
   Nested CC as a member is ID_NotFirstSlice. bag_pts are gamma ends. *)
Definition iso_fail_id (f : IsoClothoidFail) : IntakeDeclineReason :=
  match f with
  | ICF_MissingMeasure => ID_MissingMeasure
  | ICF_UnexpectedMeasure => ID_UnexpectedMeasure
  | ICF_NotSimilarityFrame => ID_NotSimilarityFrame
  | ICF_NonPositiveScale => ID_NonPositiveScale
  | ICF_DegenerateWindow => ID_DegenerateWindow
  | ICF_TiltedPlacement => ID_TiltedPlacement
  end.

Definition clothoid_bag (s : Sheet) (e : ClothoidEgg) : ShcBag :=
  mkShcBag s [0%nat; 1%nat]
    [cloth_eval e 0; cloth_eval e 1]
    [mkChicken 0%nat 1%nat (MkClothoid e)].

Definition map_clothoid (s : Sheet) (f : IsoClothoid) : IntakeResult :=
  match try_iso_clothoid f with
  | inl r => IntakeDecline (iso_fail_id r)
  | inr e => IntakeBag (clothoid_bag s e)
  end.

Definition intake_decline_of (d : CertDecline) : IntakeDeclineReason :=
  match d with
  | CD_SpiralOther _ => ID_SpiralOther
  | CD_SpiralClothoidNotYet _ => ID_SpiralClothoidNotYet
  | CD_JtsNonPositiveLength _ _ _ => ID_JtsNonPositiveLength
  | CD_JtsTripleNotYet _ _ _ => ID_JtsClothoidNotYet
  end.

Definition map_spiral (s : Sheet) (sp : SpiralInput) : IntakeResult :=
  match sp with
  | SpiralOther _ => IntakeDecline ID_SpiralOther
  | SpiralOfClothoid sc =>
      match try_spiral_clothoid sc with
      | inl SFail_NonPositiveLength => IntakeDecline ID_SpiralNonPositiveLength
      | inl SFail_ConstantCurvature => IntakeDecline ID_SpiralConstantCurvature
      | inl SFail_NotSimilarity => IntakeDecline ID_NotSimilarityFrame
      | inr e => IntakeBag (clothoid_bag s e)
      end
  end.

Definition map_jts_clothoid (s : Sheet) (k0 k1 len : R) : IntakeResult :=
  match classify_jts k0 k1 len with
  | JC_Example5 => map_clothoid s locked_iso_clothoid
  | JC_NonPositiveLength =>
      IntakeDecline (intake_decline_of (CD_JtsNonPositiveLength k0 k1 len))
  | JC_TripleNotYet =>
      IntakeDecline (intake_decline_of (CD_JtsTripleNotYet k0 k1 len))
  end.

Definition map_cc_example5 (s : Sheet) : ShcBag :=
  append_bags s
    (append_bags s
       (mkShcBag s [0%nat; 1%nat] [p00; mkPoint 100 0]
          [mkChicken 0%nat 1%nat (MkChord (mkChordEgg p00 (mkPoint 100 0)))])
       (clothoid_bag s locked_clothoid_egg))
    (clothoid_bag s locked_clothoid_egg).

Definition intake_map_atom (s : Sheet) (t : TaggedCst) : IntakeResult :=
  match t with
  | TPoint p => IntakeBag (map_point s p)
  | TLineString pts | TGeodesicString pts =>
      match pts with
      | [] => IntakeDecline ID_Empty
      | [_] => IntakeDecline ID_BadPointCount
      | _ :: _ :: _ => IntakeBag (map_ls s pts)
      end
  | TCircularString CircQuarter _ => IntakeBag (map_cs_quarter s)
  | TCircularString CircFullOgc pts
  | TCircularString CircUnknown pts => map_cs_unknown s pts
  | TCircle CircFullOgc _ => IntakeBag (map_circle s)
  | TCircle CircQuarter _ => IntakeBag (map_cs_quarter s)
  | TCircle CircUnknown pts => map_circle_unknown s pts
  | TCompoundCurve _ => IntakeDecline ID_NotFirstSlice
  | TClothoidJts k0 k1 len => map_jts_clothoid s k0 k1 len
  | TClothoidIso f => map_clothoid s f
  | TSpiralCurve sp => map_spiral s sp
  | TOutOfSlice => IntakeDecline ID_NotFirstSlice
  end.

Fixpoint intake_map_members (s : Sheet) (ms : list TaggedCst) {struct ms}
  : IntakeResult :=
  match ms with
  | [] => IntakeDecline ID_Empty
  | m :: rest =>
      match intake_map_atom s m with
      | IntakeDecline r => IntakeDecline r
      | IntakeBag b0 =>
          (fix go (acc : ShcBag) (xs : list TaggedCst) : IntakeResult :=
             match xs with
             | [] => IntakeBag acc
             | y :: ys =>
                 match intake_map_atom s y with
                 | IntakeDecline r => IntakeDecline r
                 | IntakeBag b1 => go (append_bags s acc b1) ys
                 end
             end) b0 rest
      end
  end.

Definition intake_map (s : Sheet) (t : TaggedCst) : IntakeResult :=
  match t with
  | TCompoundCurve ms => intake_map_members s ms
  | _ => intake_map_atom s t
  end.

(* ADR-0005. intake_map is the lenient default. Strict declines a
   3-control CIRCULARSTRING whose first control equals the last.
   No other CST changes. *)
Inductive IntakeMode : Type :=
| IntakeLenient
| IntakeStrict.

Definition intake_map_mode (mode : IntakeMode) (s : Sheet) (t : TaggedCst)
  : IntakeResult :=
  match mode with
  | IntakeLenient => intake_map s t
  | IntakeStrict =>
      match t with
      | TCircularString _ pts =>
          match pts with
          | a :: _ :: c :: [] =>
              if Req_EM_T (dist_sq a c) 0 then IntakeDecline ID_CsClosedDegenerate
              else intake_map s t
          | _ => intake_map s t
          end
      | _ => intake_map s t
      end
  end.

(* -------------------------------------------------------------------------- *)
(* First-slice inhabitance.                                                   *)
(* -------------------------------------------------------------------------- *)

Lemma locked_point_maps :
  intake_map default_sheet locked_point_cst =
    IntakeBag (map_point default_sheet p00).
Proof.
  reflexivity.
Qed.

Lemma locked_ls_maps :
  intake_map default_sheet locked_ls_cst =
    IntakeBag (map_ls default_sheet [p00; p20]).
Proof.
  reflexivity.
Qed.

Lemma locked_ls_is_chord :
  bag_chickens (map_ls default_sheet [p00; p20]) =
    [mkChicken 0%nat 1%nat (MkChord (mkChordEgg p00 p20))].
Proof.
  reflexivity.
Qed.

Lemma locked_cs_quarter_maps :
  intake_map default_sheet locked_cs_quarter_cst =
    IntakeBag (map_cs_quarter default_sheet).
Proof.
  reflexivity.
Qed.

Lemma locked_cs_quarter_is_mkcirc :
  bag_chickens (map_cs_quarter default_sheet) =
    [mkChicken 0%nat 1%nat (MkCirc locked_circ_A)].
Proof.
  reflexivity.
Qed.

Lemma locked_cs_quarter_intake_endpoints :
  bag_pts (map_cs_quarter default_sheet) =
    [circ_eval locked_circ_A 0; circ_eval locked_circ_A 1].
Proof.
  unfold map_cs_quarter, p50, p05. cbn [bag_pts].
  rewrite <- locked_circ_A_at_0, <- locked_circ_A_at_1.
  reflexivity.
Qed.

Lemma locked_circle_maps :
  intake_map default_sheet locked_circle_cst =
    IntakeBag (map_circle default_sheet).
Proof.
  reflexivity.
Qed.

Lemma locked_full_circle_egg_at_0 :
  circ_eval locked_full_circle_egg 0 = p50.
Proof.
  unfold circ_eval, locked_full_circle_egg, p50.
  cbn [px py circ_o circ_r circ_theta0 circ_sweep].
  rewrite Rmult_0_l, Rplus_0_r, cos_0, sin_0.
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma locked_full_circle_egg_at_half :
  circ_eval locked_full_circle_egg (1 / 2) = p_m50.
Proof.
  unfold circ_eval, locked_full_circle_egg, p_m50.
  cbn [px py circ_o circ_r circ_theta0 circ_sweep].
  replace (0 + (1 / 2) * (2 * PI)) with PI by field.
  rewrite cos_PI, sin_PI.
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma locked_full_circle_egg_at_1 :
  circ_eval locked_full_circle_egg 1 = p50.
Proof.
  unfold circ_eval, locked_full_circle_egg, p50.
  cbn [px py circ_o circ_r circ_theta0 circ_sweep].
  replace (0 + 1 * (2 * PI)) with (2 * PI) by ring.
  rewrite cos_two_pi, sin_two_pi.
  apply (f_equal2 mkPoint); ring.
Qed.

Lemma locked_circle_intake_ends :
  bag_pts (map_circle default_sheet)
    = [circ_eval locked_full_circle_egg 0;
       circ_eval locked_full_circle_egg (1 / 2)].
Proof.
  unfold map_circle. cbn [bag_pts].
  rewrite <- locked_full_circle_egg_at_0.
  rewrite <- locked_full_circle_egg_at_half.
  reflexivity.
Qed.

Lemma locked_circle_pts_nodup :
  NoDup (bag_pts (map_circle default_sheet)).
Proof.
  unfold map_circle. cbn [bag_pts].
  apply NoDup_cons.
  - intros Hin. destruct Hin as [H|[]].
    apply (f_equal px) in H. unfold p50, p_m50 in H. cbn in H. lra.
  - apply NoDup_cons; [intros Hin; destruct Hin | apply NoDup_nil].
Qed.

Lemma locked_circle_from_try :
  try_circle_eggs [p50; p05; p_m50] =
    inl ([locked_half_fst; locked_half_snd], [p50; p_m50]).
Proof.
  change p50 with ccw_a.
  change p05 with ccw_b.
  change p_m50 with ccw_c.
  rewrite ccw_try_circle.
  unfold locked_half_fst, locked_half_snd, ccw_a, ccw_c. reflexivity.
Qed.

Lemma map_cs_unknown_open : forall s a b c,
  dist_sq a c <> 0 ->
  map_cs_unknown s [a; b; c] = map_cs_from_try s [a; b; c].
Proof.
  intros s a b c Hac. unfold map_cs_unknown.
  destruct (Req_EM_T (dist_sq a c) 0) as [E|E]; [contradiction|reflexivity].
Qed.

Lemma cs_closed_declines : forall a b,
  intake_map_mode IntakeStrict default_sheet
    (TCircularString CircUnknown [a; b; a]) =
    IntakeDecline ID_CsClosedDegenerate /\
  intake_map_mode IntakeStrict default_sheet
    (TCircularString CircFullOgc [a; b; a]) =
    IntakeDecline ID_CsClosedDegenerate.
Proof.
  intros a b. split; unfold intake_map_mode;
    destruct (Req_EM_T (dist_sq a a) 0) as [_|H];
    try reflexivity; exfalso; apply H; unfold dist_sq; ring.
Qed.

Lemma cs_lenient_normalizes : forall s a b,
  dist_sq a b <> 0 ->
  intake_map s (TCircularString CircUnknown [a; b; a]) =
    intake_map s (TCircle CircUnknown [a; b; ogc_c a b]) /\
  intake_map s (TCircularString CircFullOgc [a; b; a]) =
    intake_map s (TCircle CircUnknown [a; b; ogc_c a b]).
Proof.
  intros s a b Hab. split.
  - unfold intake_map, intake_map_atom, map_cs_unknown.
    destruct (Req_EM_T (dist_sq a a) 0) as [_|Hz].
    + destruct (Req_EM_T (dist_sq a b) 0) as [E|E]; [contradiction|].
      unfold intake_map, intake_map_atom. reflexivity.
    + exfalso. apply Hz. unfold dist_sq. ring.
  - unfold intake_map, intake_map_atom, map_cs_unknown.
    destruct (Req_EM_T (dist_sq a a) 0) as [_|Hz].
    + destruct (Req_EM_T (dist_sq a b) 0) as [E|E]; [contradiction|].
      unfold intake_map, intake_map_atom. reflexivity.
    + exfalso. apply Hz. unfold dist_sq. ring.
Qed.

Lemma cs_lenient_coincident_declines : forall a b,
  dist_sq a b = 0 ->
  intake_map default_sheet (TCircularString CircUnknown [a; b; a]) =
    IntakeDecline ID_CsClosedDegenerate /\
  intake_map default_sheet (TCircularString CircFullOgc [a; b; a]) =
    IntakeDecline ID_CsClosedDegenerate.
Proof.
  intros a b Hab. split.
  - unfold intake_map, intake_map_atom, map_cs_unknown.
    destruct (Req_EM_T (dist_sq a a) 0) as [_|Hz].
    + destruct (Req_EM_T (dist_sq a b) 0) as [_|H];
        [reflexivity|contradiction].
    + exfalso. apply Hz. unfold dist_sq. ring.
  - unfold intake_map, intake_map_atom, map_cs_unknown.
    destruct (Req_EM_T (dist_sq a a) 0) as [_|Hz].
    + destruct (Req_EM_T (dist_sq a b) 0) as [_|H];
        [reflexivity|contradiction].
    + exfalso. apply Hz. unfold dist_sq. ring.
Qed.

Lemma locked_cs_full_ogc_declines :
  intake_map_mode IntakeStrict default_sheet locked_cs_full_ogc_cst =
    IntakeDecline ID_CsClosedDegenerate.
Proof.
  unfold locked_cs_full_ogc_cst.
  exact (proj2 (cs_closed_declines p50 p05)).
Qed.

Lemma locked_p50_p05_apart : dist_sq p50 p05 <> 0.
Proof.
  unfold dist_sq, p50, p05. cbn. lra.
Qed.

Lemma locked_cs_full_ogc_lenient :
  intake_map default_sheet locked_cs_full_ogc_cst =
    intake_map default_sheet (TCircle CircUnknown [p50; p05; ogc_c p50 p05]).
Proof.
  unfold locked_cs_full_ogc_cst.
  exact (proj2 (cs_lenient_normalizes default_sheet p50 p05 locked_p50_p05_apart)).
Qed.

Lemma locked_cc_maps :
  intake_map default_sheet locked_cc_cst =
    IntakeBag (map_cc_locked default_sheet).
Proof.
  reflexivity.
Qed.

Lemma locked_cc_has_chord_and_circ :
  exists c1 c2,
    In c1 (bag_chickens (map_cc_locked default_sheet)) /\
    In c2 (bag_chickens (map_cc_locked default_sheet)) /\
    egg_class (ck_egg c1) = EggChord /\
    egg_class (ck_egg c2) = EggCircularArc.
Proof.
  exists (mkChicken 0%nat 1%nat (MkChord (mkChordEgg p00 p50))).
  exists (shift_chicken 2%nat (mkChicken 0%nat 1%nat (MkCirc locked_circ_A))).
  unfold map_cc_locked, append_bags, map_cs_quarter. cbn.
  split.
  - now left.
  - split.
    + right. now left.
    + split; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Mode D: locked CC LS+CS joint on host endpoints.                           *)
(* append_bags is hen offset, not geometry — equality is chord_eval /         *)
(* circ_eval on the locked members that map_cc_locked is built from.          *)
(* LS–CS is host I_ok Hit at the joint. Not sidecar remint. Not first-cook expand. *)
(* -------------------------------------------------------------------------- *)

Definition locked_cc_ls_egg : ChordEgg := mkChordEgg p00 p50.

Definition locked_cc_joint_pt : Point := p50.

Lemma locked_cc_ls_end :
  chord_eval locked_cc_ls_egg 1 = locked_cc_joint_pt.
Proof.
  unfold locked_cc_ls_egg, locked_cc_joint_pt.
  apply chord_eval_at_1.
Qed.

Lemma locked_cc_cs_start :
  circ_eval locked_circ_A 0 = locked_cc_joint_pt.
Proof.
  unfold locked_cc_joint_pt, p50.
  exact locked_circ_A_at_0.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"locked_cc_joint_host_endpoints","title":"Mode D CC LS+CS joint: locked map_cc_locked LS end equals quarter CS start via host chord_eval / circ_eval; append_bags is hen offset not geometry; in-scope host I_ok is Hit (locked_cc_ls_cs_host_hit), not Decline","file":"theories/IntakeWalker.v","witness":"0007-B.2-cc-member-joints","board":"ADR-0007"} *)

Theorem locked_cc_joint_host_endpoints :
  locked_cc_joint_pt = chord_eval (mkChordEgg p00 p50) 1 /\
  locked_cc_joint_pt = circ_eval locked_circ_A 0.
Proof.
  split.
  - unfold locked_cc_joint_pt.
    change (mkChordEgg p00 p50) with locked_cc_ls_egg.
    symmetry. exact locked_cc_ls_end.
  - unfold locked_cc_joint_pt.
    symmetry. exact locked_cc_cs_start.
Qed.

Lemma locked_cc_joint_host_eval_eq :
  chord_eval (mkChordEgg p00 p50) 1 = circ_eval locked_circ_A 0.
Proof.
  destruct locked_cc_joint_host_endpoints as [Hl Hr].
  rewrite <- Hl. exact Hr.
Qed.

(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"locked_cc_ls_cs_host_hit","title":"Mode D locked CC LS+CS is host I_ok Hit at the joint; in-scope circ times chord; sidecar I_ok_mixed stays sidecar; no first_cook_scope expand","file":"theories/IntakeWalker.v","witness":"0007-B-mixed-ls-cs-joints","board":"ADR-0007"} *)

Lemma locked_cc_ls_cs_host_scope :
  circ_chord_host_scope locked_circ_A (mkChordEgg p00 p50).
Proof.
  split.
  - unfold circ_open_span, locked_circ_A. cbn.
    pose proof PI_RGT_0 as Hpi. lra.
  - unfold chord_nondeg, chord_dx, chord_dy, p00, p50. cbn.
    intro Heq. apply (f_equal fst) in Heq. cbn in Heq. lra.
Qed.

Lemma locked_cc_ls_cs_host_hit :
  I_ok (MkChord (mkChordEgg p00 p50)) (MkCirc locked_circ_A)
       (IHit locked_cc_joint_pt 1 0).
Proof.
  unfold I_ok.
  split; [exact locked_cc_ls_cs_host_scope|].
  split.
  - unfold on_chord. split; [lra|].
    unfold locked_cc_joint_pt. symmetry. exact locked_cc_ls_end.
  - unfold on_circ. split; [lra|].
    symmetry. exact locked_cc_cs_start.
Qed.

(* -------------------------------------------------------------------------- *)
(* Fail-closed Declines. Named tickets. No silent chord demote.               *)
(* -------------------------------------------------------------------------- *)

Lemma locked_geodesic_maps :
  intake_map default_sheet locked_geodesic_cst =
    IntakeBag (map_ls default_sheet [p00; p20]).
Proof. reflexivity. Qed.

Lemma locked_geodesic_same_bag_as_ls :
  intake_map default_sheet locked_geodesic_cst =
    intake_map default_sheet locked_ls_cst.
Proof. reflexivity. Qed.

Lemma locked_geodesic_is_chord :
  bag_chickens (map_ls default_sheet [p00; p20]) =
    [mkChicken 0%nat 1%nat (MkChord (mkChordEgg p00 p20))] /\
  egg_class (MkChord (mkChordEgg p00 p20)) = EggChord.
Proof. split; reflexivity. Qed.

Lemma locked_geodesic_not_geodesic_egg :
  forall c,
    In c (bag_chickens (map_ls default_sheet [p00; p20])) ->
    ck_egg c <> MkOutOfScope EggGeodesicString /\
    egg_class (ck_egg c) = EggChord.
Proof.
  intros c Hin; rewrite (proj1 locked_geodesic_is_chord) in Hin;
    destruct Hin as [Heq|[]]; rewrite <- Heq; split; [discriminate|reflexivity].
Qed.

Lemma geodesic_wellformed_not_id_geodesic :
  intake_map default_sheet locked_geodesic_cst <>
    IntakeDecline ID_GeodesicString.
Proof. rewrite locked_geodesic_maps. discriminate. Qed.

Lemma geodesic_empty_declines :
  intake_map default_sheet (TGeodesicString []) = IntakeDecline ID_Empty.
Proof. reflexivity. Qed.

Lemma geodesic_badcount_declines :
  intake_map default_sheet (TGeodesicString [p00]) =
    IntakeDecline ID_BadPointCount.
Proof. reflexivity. Qed.

Lemma spiral_declines :
  intake_map default_sheet spiral_bloss =
    IntakeDecline ID_SpiralOther.
Proof.
  reflexivity.
Qed.


Lemma out_of_slice_declines :
  intake_map default_sheet TOutOfSlice =
    IntakeDecline ID_NotFirstSlice.
Proof.
  reflexivity.
Qed.

Lemma unknown_cs_maps_mkcirc :
  intake_map default_sheet unknown_cs_cst =
    IntakeBag (map_cs_from_build default_sheet [ang_egg] [p00; mkPoint 3 1]).
Proof.
  unfold unknown_cs_cst, intake_map, intake_map_atom.
  change p00 with ang_a.
  change p20 with ang_b.
  change (mkPoint 3 1) with ang_c.
  rewrite (map_cs_unknown_open _ _ _ _ ang_dac_nz).
  unfold map_cs_from_try. rewrite ang_cs_ok. reflexivity.
Qed.

Lemma unknown_cs_chickens_mkcirc :
  exists b c e,
    intake_map default_sheet unknown_cs_cst = IntakeBag b /\
    In c (bag_chickens b) /\
    ck_egg c = MkCirc e.
Proof.
  rewrite unknown_cs_maps_mkcirc.
  exists (map_cs_from_build default_sheet [ang_egg] [p00; mkPoint 3 1]).
  exists (mkChicken 0%nat 1%nat (MkCirc ang_egg)).
  exists ang_egg.
  split; [reflexivity|].
  split; [now left|].
  reflexivity.
Qed.

Lemma unknown_cs_not_leftover :
  intake_map default_sheet unknown_cs_cst <>
    IntakeDecline ID_CircGammaLeftover.
Proof.
  rewrite unknown_cs_maps_mkcirc.
  discriminate.
Qed.

Lemma unknown_cs_not_chord_demote :
  intake_map default_sheet unknown_cs_cst <>
    IntakeBag (map_ls default_sheet [p00; p20; mkPoint 3 1]).
Proof.
  rewrite unknown_cs_maps_mkcirc.
  discriminate.
Qed.

Lemma collinear_cs_declines :
  intake_map default_sheet (TCircularString CircUnknown [col_a; col_b; col_c]) =
    IntakeDecline ID_Collinear.
Proof.
  unfold intake_map, intake_map_atom.
  rewrite (map_cs_unknown_open _ _ _ _ col_dac_nz).
  unfold map_cs_from_try. rewrite col_cs_collinear. reflexivity.
Qed.

Lemma duplicate_cs_declines :
  intake_map default_sheet (TCircularString CircUnknown [dup_a; dup_b; dup_c]) =
    IntakeDecline ID_DuplicateControl.
Proof.
  unfold intake_map, intake_map_atom.
  rewrite (map_cs_unknown_open _ _ _ _ dup_ac_nz).
  unfold map_cs_from_try. rewrite dup_cs. reflexivity.
Qed.

Lemma badcount_cs_declines :
  intake_map default_sheet (TCircularString CircUnknown [p00; p20]) =
    IntakeDecline ID_BadPointCount.
Proof.
  unfold intake_map, intake_map_atom, map_cs_unknown, map_cs_from_try,
    try_cs_eggs, go_arcs.
  reflexivity.
Qed.

Lemma empty_cs_declines :
  intake_map default_sheet (TCircularString CircUnknown []) =
    IntakeDecline ID_Empty.
Proof.
  reflexivity.
Qed.

Lemma overlap_ls_literal_chickens :
  length (bag_chickens (map_ls default_sheet [p00; p20; p00])) = 2%nat.
Proof.
  reflexivity.
Qed.

Lemma intake_not_cook_split :
  length (bag_hens (map_ls default_sheet [p00; p20])) =
    length (bag_pts (map_ls default_sheet [p00; p20])).
Proof.
  reflexivity.
Qed.

Lemma empty_ls_declines :
  intake_map default_sheet (TLineString []) = IntakeDecline ID_Empty.
Proof.
  reflexivity.
Qed.

Lemma singleton_ls_declines :
  intake_map default_sheet (TLineString [p00]) =
    IntakeDecline ID_BadPointCount.
Proof.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Product face + letter status.                                              *)
(* -------------------------------------------------------------------------- *)

Inductive IntakeWalkerKind : Type :=
| IW_FirstSlice
| IW_WkbGammaWalk
| IW_WktZoo
| IW_Lesson1Remint
| IW_HostCook
| IW_NewOracleKeyword.

Definition intake_walker_kind : IntakeWalkerKind := IW_FirstSlice.

Lemma intake_walker_is_first_slice :
  intake_walker_kind = IW_FirstSlice.
Proof.
  reflexivity.
Qed.

Lemma intake_walker_not_wkb :
  intake_walker_kind <> IW_WkbGammaWalk.
Proof.
  discriminate.
Qed.

Lemma intake_walker_not_zoo :
  intake_walker_kind <> IW_WktZoo.
Proof.
  discriminate.
Qed.

Lemma intake_walker_not_lesson1 :
  intake_walker_kind <> IW_Lesson1Remint.
Proof.
  discriminate.
Qed.

Lemma intake_walker_not_host_cook :
  intake_walker_kind <> IW_HostCook.
Proof.
  discriminate.
Qed.

Lemma intake_walker_not_new_keyword :
  intake_walker_kind <> IW_NewOracleKeyword.
Proof.
  discriminate.
Qed.

Inductive IntakeWalkerLetterStatus : Type :=
| IntakeWalkerLanded
| IntakeWalkerFirstCookExpanded
| IntakeWalkerCampaignDischarged.

Definition intake_walker_letter_status : IntakeWalkerLetterStatus :=
  IntakeWalkerLanded.

Lemma intake_walker_letter_is_landed :
  intake_walker_letter_status = IntakeWalkerLanded.
Proof.
  reflexivity.
Qed.

Lemma intake_walker_not_first_cook_expanded :
  intake_walker_letter_status <> IntakeWalkerFirstCookExpanded.
Proof.
  discriminate.
Qed.

Lemma intake_walker_campaign_not_discharged :
  intake_walker_letter_status <> IntakeWalkerCampaignDischarged.
Proof.
  discriminate.
Qed.

Inductive IntakeCtor : Type :=
| IntakeAnglesFromPoints
| IntakeMkClothoid
| IntakeGeodesicMkChord
| IntakeWkbOrder.

Definition intake_ctor_inhabits (c : IntakeCtor) : Prop :=
  match c with
  | IntakeAnglesFromPoints => True
  | IntakeMkClothoid => True
  | IntakeGeodesicMkChord => True
  | IntakeWkbOrder => False
  end.

Lemma intake_angles_from_points_inhabits :
  intake_ctor_inhabits IntakeAnglesFromPoints.
Proof.
  exact I.
Qed.

Lemma intake_mkclothoid_inhabits :
  intake_ctor_inhabits IntakeMkClothoid.
Proof.
  exact I.
Qed.

Lemma intake_geodesic_mkchord_inhabits :
  intake_ctor_inhabits IntakeGeodesicMkChord.
Proof. exact I. Qed.

Lemma intake_wkb_order_missing :
  ~ intake_ctor_inhabits IntakeWkbOrder.
Proof.
  intro H. exact H.
Qed.

Lemma first_slice_inhabits :
  intake_map default_sheet locked_point_cst =
    IntakeBag (map_point default_sheet p00) /\
  intake_map default_sheet locked_ls_cst =
    IntakeBag (map_ls default_sheet [p00; p20]) /\
  intake_map default_sheet locked_cs_quarter_cst =
    IntakeBag (map_cs_quarter default_sheet) /\
  intake_map default_sheet locked_circle_cst =
    IntakeBag (map_circle default_sheet) /\
  bag_pts (map_circle default_sheet) =
    [circ_eval locked_full_circle_egg 0;
     circ_eval locked_full_circle_egg (1 / 2)] /\
  NoDup (bag_pts (map_circle default_sheet)) /\
  intake_map_mode IntakeStrict default_sheet locked_cs_full_ogc_cst =
    IntakeDecline ID_CsClosedDegenerate /\
  intake_map default_sheet locked_cs_full_ogc_cst =
    intake_map default_sheet (TCircle CircUnknown [p50; p05; ogc_c p50 p05]) /\
  intake_map default_sheet spiral_bloss =
    IntakeDecline ID_SpiralOther /\
  intake_walker_kind = IW_FirstSlice.
Proof.
  repeat split; try exact locked_circle_intake_ends;
    try exact locked_circle_pts_nodup;
    try exact locked_cs_full_ogc_declines;
    try exact locked_cs_full_ogc_lenient; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-intake-walker","topic":"overlay","lemma":"ticket_0007_intake_walker_qed_or_qex","title":"First-slice intake maps Point/LineString/locked CircularString/Circle to SHC bag; ADR-0005 IntakeLenient normalizes CIRCULARSTRING(A,B,A) to CIRCLE(A,B,ogc_c) and IntakeStrict Declines ID_CsClosedDegenerate; fail-closes non-clothoid SPIRALCURVE (QED) or silently demotes SpiralOther to MkChord (QEX); discharged QED; well-formed GEODESICSTRING bagging is the 0007-intake-geodesic letter; clothoid SPIRALCURVE is 0007-intake-spiral; grammar accept is CST only; Intake Decline is not cook IDecline; clothoid bagging is the MkClothoid letter","file":"theories/IntakeWalker.v","witness":"0007-intake-walker","board":"ADR-0007"} *)
Theorem ticket_0007_intake_walker_qed_or_qex :
  (intake_map default_sheet locked_point_cst =
     IntakeBag (map_point default_sheet p00) /\
   intake_map default_sheet locked_ls_cst =
     IntakeBag (map_ls default_sheet [p00; p20]) /\
   intake_map default_sheet locked_cs_quarter_cst =
     IntakeBag (map_cs_quarter default_sheet) /\
   egg_class (ck_egg (hd (mkChicken 0%nat 0%nat (MkChord (mkChordEgg p00 p00)))
                         (bag_chickens (map_cs_quarter default_sheet))))
     = EggCircularArc /\
   intake_map default_sheet locked_circle_cst =
     IntakeBag (map_circle default_sheet) /\
   intake_map_mode IntakeStrict default_sheet locked_cs_full_ogc_cst =
     IntakeDecline ID_CsClosedDegenerate /\
   intake_map default_sheet locked_cs_full_ogc_cst =
     intake_map default_sheet (TCircle CircUnknown [p50; p05; ogc_c p50 p05]) /\
   intake_map default_sheet spiral_bloss =
     IntakeDecline ID_SpiralOther /\
   grammar_accept_not_valid /\ grammar_accept_not_cooked /\
   intake_walker_kind = IW_FirstSlice /\
   intake_walker_kind <> IW_WktZoo /\
   intake_walker_kind <> IW_NewOracleKeyword)
  \/
  (exists k b c,
     intake_map default_sheet (TSpiralCurve (SpiralOther k)) = IntakeBag b /\
     In c (bag_chickens b) /\ egg_class (ck_egg c) = EggChord).
Proof.
  left.
  repeat split; try exact locked_cs_full_ogc_declines;
    try exact locked_cs_full_ogc_lenient;
    try reflexivity; try discriminate.
Qed.

(* WITNESS {"claimId":"0007-intake-angles","topic":"core","lemma":"ticket_0007_intake_angles_qed_or_qex","title":"Intake constructs CircularEgg / MkCirc from arbitrary well-formed WKT circular control points (QED) or angles-from-points stays QEX and unknown CircularString Declines ID_CircGammaLeftover (QEX); discharged QED; not a CircGamma remint; no silent chord demote; clothoid is the MkClothoid letter","file":"theories/IntakeWalker.v","witness":"0007-intake-angles","board":"ADR-0007"} *)
Theorem ticket_0007_intake_angles_qed_or_qex :
  (intake_ctor_inhabits IntakeAnglesFromPoints /\
   exists pts,
     pts = [p00; p20; mkPoint 3 1] /\
     exists b c e,
       intake_map default_sheet (TCircularString CircUnknown pts)
         = IntakeBag b /\
       In c (bag_chickens b) /\
       ck_egg c = MkCirc e)
  \/
  (~ intake_ctor_inhabits IntakeAnglesFromPoints /\
   intake_map default_sheet unknown_cs_cst =
     IntakeDecline ID_CircGammaLeftover).
Proof.
  left.
  split; [exact intake_angles_from_points_inhabits|].
  exists [p00; p20; mkPoint 3 1].
  split; [reflexivity|].
  exact unknown_cs_chickens_mkcirc.
Qed.

(* WITNESS {"claimId":"0007-intake-walker","topic":"overlay","lemma":"ticket_0007_intake_parks_qed_or_qex","title":"Intake walker discharges WKB-order Gamma walk, WKT zoo, Lesson-1 remints, host cook expand, and new oracle keyword (QED) or names them parked (QEX); discharged QEX; clothoid split out to MkClothoid letter; letter landed != first-cook expand / Campaign / bag noder","file":"theories/IntakeWalker.v","witness":"0007-intake-walker","board":"ADR-0007"} *)
Theorem ticket_0007_intake_parks_qed_or_qex :
  (intake_walker_letter_status = IntakeWalkerCampaignDischarged /\
   intake_walker_kind = IW_WkbGammaWalk /\
   intake_walker_kind = IW_WktZoo /\
   intake_walker_kind = IW_HostCook /\
   intake_ctor_inhabits IntakeWkbOrder /\
   cook_loop_status = LoopDischarged)
  \/
  (intake_walker_letter_status = IntakeWalkerLanded /\
   intake_walker_letter_status <> IntakeWalkerCampaignDischarged /\
   intake_walker_kind = IW_FirstSlice /\
   intake_walker_kind <> IW_WkbGammaWalk /\
   intake_walker_kind <> IW_WktZoo /\
   intake_walker_kind <> IW_Lesson1Remint /\
   intake_walker_kind <> IW_HostCook /\
   intake_walker_kind <> IW_NewOracleKeyword /\
   ~ intake_ctor_inhabits IntakeWkbOrder /\
   cook_loop_status = LoopObligation /\
   cook_loop_status <> LoopDischarged).
Proof.
  right.
  split; [exact intake_walker_letter_is_landed|].
  split; [exact intake_walker_campaign_not_discharged|].
  split; [exact intake_walker_is_first_slice|].
  split; [exact intake_walker_not_wkb|].
  split; [exact intake_walker_not_zoo|].
  split; [exact intake_walker_not_lesson1|].
  split; [exact intake_walker_not_host_cook|].
  split; [exact intake_walker_not_new_keyword|].
  split; [exact intake_wkb_order_missing|].
  split; [exact cook_loop_is_obligation|].
  exact cook_loop_not_discharged.
Qed.


Print Assumptions locked_point_maps.
Print Assumptions locked_ls_maps.
Print Assumptions locked_cs_quarter_maps.
Print Assumptions locked_cs_quarter_intake_endpoints.
Print Assumptions locked_cc_ls_end.
Print Assumptions locked_cc_cs_start.
Print Assumptions locked_cc_joint_host_endpoints.
Print Assumptions locked_cc_joint_host_eval_eq.
Print Assumptions locked_cc_ls_cs_host_scope.
Print Assumptions locked_cc_ls_cs_host_hit.
Print Assumptions locked_circle_maps.
Print Assumptions locked_full_circle_egg_at_0.
Print Assumptions locked_full_circle_egg_at_half.
Print Assumptions locked_full_circle_egg_at_1.
Print Assumptions locked_circle_intake_ends.
Print Assumptions locked_circle_pts_nodup.
Print Assumptions locked_circle_from_try.
Print Assumptions map_cs_unknown_open.
Print Assumptions cs_closed_declines.
Print Assumptions cs_lenient_normalizes.
Print Assumptions cs_lenient_coincident_declines.
Print Assumptions locked_cs_full_ogc_declines.
Print Assumptions locked_p50_p05_apart.
Print Assumptions locked_cs_full_ogc_lenient.
Print Assumptions locked_geodesic_maps.
Print Assumptions locked_geodesic_same_bag_as_ls.
Print Assumptions locked_geodesic_is_chord.
Print Assumptions geodesic_wellformed_not_id_geodesic.
Print Assumptions geodesic_empty_declines.
Print Assumptions spiral_declines.
Print Assumptions unknown_cs_maps_mkcirc.
Print Assumptions unknown_cs_chickens_mkcirc.
Print Assumptions unknown_cs_not_leftover.
Print Assumptions unknown_cs_not_chord_demote.
Print Assumptions collinear_cs_declines.
Print Assumptions duplicate_cs_declines.
Print Assumptions badcount_cs_declines.
Print Assumptions empty_cs_declines.
Print Assumptions overlap_ls_literal_chickens.
Print Assumptions first_slice_inhabits.
Print Assumptions intake_angles_from_points_inhabits.
Print Assumptions intake_mkclothoid_inhabits.
Print Assumptions ticket_0007_intake_walker_qed_or_qex.
Print Assumptions ticket_0007_intake_angles_qed_or_qex.
Print Assumptions ticket_0007_intake_parks_qed_or_qex.
Print Assumptions intake_geodesic_mkchord_inhabits.
Print Assumptions intake_bag_neq_decline.
Print Assumptions cook_ihit_neq_idecline.
Print Assumptions grammar_accept_is_cst_only.
Print Assumptions locked_ls_is_chord.
Print Assumptions locked_cs_quarter_is_mkcirc.
Print Assumptions locked_cc_maps.
Print Assumptions locked_cc_has_chord_and_circ.
Print Assumptions locked_geodesic_not_geodesic_egg.
Print Assumptions geodesic_badcount_declines.
Print Assumptions out_of_slice_declines.
Print Assumptions intake_not_cook_split.
Print Assumptions empty_ls_declines.
Print Assumptions singleton_ls_declines.
Print Assumptions intake_walker_is_first_slice.
Print Assumptions intake_walker_not_wkb.
Print Assumptions intake_walker_not_zoo.
Print Assumptions intake_walker_not_lesson1.
Print Assumptions intake_walker_not_host_cook.
Print Assumptions intake_walker_not_new_keyword.
Print Assumptions intake_walker_letter_is_landed.
Print Assumptions intake_walker_not_first_cook_expanded.
Print Assumptions intake_walker_campaign_not_discharged.
Print Assumptions intake_wkb_order_missing.
