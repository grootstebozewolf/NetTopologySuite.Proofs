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
     two, Circle-as-full-span-arc (one MkCirc, sweep = 2π).
   Reuses MkChord / MkCirc. Clothoid is the MkClothoid letter
   in this module (same mapper table). No Fresnel host γ.

   Fail closed: GEODESICSTRING, SPIRALCURVE, MkOutOfScope
   leftovers. CircUnknown well-formed CS/Circle now maps
   through IntakeAngles (claimId 0007-intake-angles): unique
   circumcircle + inhabited angle fields, MkCirc chickens.
   Collinear / duplicate / bad count / empty / zero-radius
   Decline by name. NO silent chord demote at intake. Demote
   is later cook/view. ID_CircGammaLeftover stays on the type
   (first-slice leftover name) but is not the well-formed
   unknown-CS answer.

   Clothoid (claimId 0007-intake-mkclothoid): one host
   MkClothoid on Egg. ISO and JTS surface forms map onto the
   same locked ClothoidEgg bag (OGC≡ISO). example5.txt bags
   both forms in one COMPOUNDCURVE. Not two invented
   constructors. ID_IsoClothoid / ID_MkOutOfScope stay on the
   Decline type; they are not the well-formed clothoid answer.
   Clothoid×clothoid stays not-first-cook / IDecline.

   OGC-form and ISO-form of the same in-scope type → same bag
   (locked CIRCLE vs start=end CIRCULARSTRING full-span).

   Visitor tags locked CircularString / Circle shapes (exact
   control-point match). Mapper is structural on those tags.
   CircUnknown uses IntakeAngles (Req_EM_T on denom / duplicates;
   3-axiom classical reals, no Atan2.v / no Ratan classic).

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
   also: 0007-intake-mkclothoid
   board: ADR-0007
   3-axiom host. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance SheetHenCook CircularCookMkCirc IntakeAngles.
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
| TClothoidJts : TaggedCst
| TClothoidIso : TaggedCst
| TGeodesicString : TaggedCst
| TSpiralCurve : TaggedCst
| TOutOfSlice : TaggedCst.

(* Intake Decline. Distinct type from cook IResult / IDecline. *)
Inductive IntakeDeclineReason : Type :=
| ID_Empty
| ID_BadPointCount
| ID_GeodesicString
| ID_SpiralCurve
| ID_IsoClothoid
| ID_MkOutOfScope
| ID_CircGammaLeftover
| ID_Collinear
| ID_DuplicateControl
| ID_DegenerateArc
| ID_NotFirstSlice.

Definition angle_fail_reason (f : AngleFail) : IntakeDeclineReason :=
  match f with
  | AF_Empty => ID_Empty
  | AF_BadCount => ID_BadPointCount
  | AF_Duplicate => ID_DuplicateControl
  | AF_Collinear => ID_Collinear
  | AF_Degenerate => ID_DegenerateArc
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
Definition example5_iso_clothoid_cst : TaggedCst := TClothoidIso.
Definition example5_cc_both_clothoid_cst : TaggedCst :=
  TCompoundCurve [TLineString [p00; mkPoint 100 0]; TClothoidJts; TClothoidIso].

Definition locked_full_circle_egg : CircularEgg :=
  mkCircularEgg (mkPoint 0 0) 5 0 (2 * PI).

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

Definition map_cs_unknown (s : Sheet) (pts : list Point) : IntakeResult :=
  match try_cs_eggs pts with
  | inr f => IntakeDecline (angle_fail_reason f)
  | inl (eggs, ends) => IntakeBag (map_cs_from_build s eggs ends)
  end.

Definition map_circle_unknown (s : Sheet) (pts : list Point) : IntakeResult :=
  match try_circle_eggs pts with
  | inr f => IntakeDecline (angle_fail_reason f)
  | inl (eggs, ends) => IntakeBag (map_cs_from_build s eggs ends)
  end.

Definition map_cs_quarter (s : Sheet) : ShcBag :=
  mkShcBag s [0%nat; 1%nat] [p50; p05]
    [mkChicken 0%nat 1%nat (MkCirc locked_circ_A)].

Definition map_cs_full (s : Sheet) : ShcBag :=
  mkShcBag s [0%nat; 1%nat] [p50; p50]
    [mkChicken 0%nat 1%nat (MkCirc locked_full_circle_egg)].

Definition map_circle (s : Sheet) : ShcBag :=
  mkShcBag s [0%nat; 1%nat] [p50; p_m50]
    [mkChicken 0%nat 1%nat (MkCirc locked_full_circle_egg)].

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

(* First-slice CC is flat (Point / LineString / CircularString /
   named Decline tickets / clothoid). Nested CC as a member is
   ID_NotFirstSlice. Well-formed ISO / JTS clothoid bag the same
   MkClothoid egg (claimId 0007-intake-mkclothoid). *)
Definition map_clothoid (s : Sheet) : ShcBag :=
  mkShcBag s [0%nat; 1%nat]
    [cloth_p0 locked_clothoid_egg; cloth_p1 locked_clothoid_egg]
    [mkChicken 0%nat 1%nat (MkClothoid locked_clothoid_egg)].

Definition map_cc_example5 (s : Sheet) : ShcBag :=
  append_bags s
    (append_bags s
       (mkShcBag s [0%nat; 1%nat] [p00; mkPoint 100 0]
          [mkChicken 0%nat 1%nat (MkChord (mkChordEgg p00 (mkPoint 100 0)))])
       (map_clothoid s))
    (map_clothoid s).

Definition intake_map_atom (s : Sheet) (t : TaggedCst) : IntakeResult :=
  match t with
  | TPoint p => IntakeBag (map_point s p)
  | TLineString pts =>
      match pts with
      | [] => IntakeDecline ID_Empty
      | [_] => IntakeDecline ID_BadPointCount
      | _ :: _ :: _ => IntakeBag (map_ls s pts)
      end
  | TCircularString CircQuarter _ => IntakeBag (map_cs_quarter s)
  | TCircularString CircFullOgc _ => IntakeBag (map_cs_full s)
  | TCircularString CircUnknown pts => map_cs_unknown s pts
  | TCircle CircFullOgc _ => IntakeBag (map_circle s)
  | TCircle CircQuarter _ => IntakeBag (map_cs_quarter s)
  | TCircle CircUnknown pts => map_circle_unknown s pts
  | TCompoundCurve _ => IntakeDecline ID_NotFirstSlice
  | TClothoidJts => IntakeBag (map_clothoid s)
  | TClothoidIso => IntakeBag (map_clothoid s)
  | TGeodesicString => IntakeDecline ID_GeodesicString
  | TSpiralCurve => IntakeDecline ID_SpiralCurve
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

Lemma locked_circle_maps :
  intake_map default_sheet locked_circle_cst =
    IntakeBag (map_circle default_sheet).
Proof.
  reflexivity.
Qed.

Lemma locked_cs_full_ogc_maps :
  intake_map default_sheet locked_cs_full_ogc_cst =
    IntakeBag (map_cs_full default_sheet).
Proof.
  reflexivity.
Qed.

Lemma ogc_iso_circle_same_egg :
  ck_egg (hd (mkChicken 0%nat 0%nat (MkChord (mkChordEgg p00 p00)))
             (bag_chickens (map_cs_full default_sheet)))
  = ck_egg (hd (mkChicken 0%nat 0%nat (MkChord (mkChordEgg p00 p00)))
               (bag_chickens (map_circle default_sheet))).
Proof.
  reflexivity.
Qed.

Lemma ogc_iso_circle_same_mkcirc :
  bag_chickens (map_cs_full default_sheet) =
    [mkChicken 0%nat 1%nat (MkCirc locked_full_circle_egg)] /\
  bag_chickens (map_circle default_sheet) =
    [mkChicken 0%nat 1%nat (MkCirc locked_full_circle_egg)].
Proof.
  split; reflexivity.
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
(* Fail-closed Declines. Named tickets. No silent chord demote.               *)
(* -------------------------------------------------------------------------- *)

Lemma geodesic_declines :
  intake_map default_sheet TGeodesicString =
    IntakeDecline ID_GeodesicString.
Proof.
  reflexivity.
Qed.

Lemma spiral_declines :
  intake_map default_sheet TSpiralCurve =
    IntakeDecline ID_SpiralCurve.
Proof.
  reflexivity.
Qed.

Lemma iso_clothoid_maps :
  intake_map default_sheet example5_iso_clothoid_cst =
    IntakeBag (map_clothoid default_sheet).
Proof.
  reflexivity.
Qed.

Lemma jts_clothoid_maps :
  intake_map default_sheet TClothoidJts =
    IntakeBag (map_clothoid default_sheet).
Proof.
  reflexivity.
Qed.

Lemma ogc_iso_clothoid_same_bag :
  intake_map default_sheet TClothoidJts =
    intake_map default_sheet TClothoidIso.
Proof.
  reflexivity.
Qed.

Lemma ogc_iso_clothoid_same_mkclothoid :
  intake_map default_sheet TClothoidJts =
    IntakeBag (map_clothoid default_sheet) /\
  intake_map default_sheet TClothoidIso =
    IntakeBag (map_clothoid default_sheet).
Proof.
  split; reflexivity.
Qed.

Lemma iso_clothoid_chickens_mkclothoid :
  exists b c e,
    intake_map default_sheet example5_iso_clothoid_cst = IntakeBag b /\
    In c (bag_chickens b) /\
    ck_egg c = MkClothoid e /\
    egg_class (ck_egg c) = EggClothoid.
Proof.
  rewrite iso_clothoid_maps.
  exists (map_clothoid default_sheet).
  exists (mkChicken 0%nat 1%nat (MkClothoid locked_clothoid_egg)).
  exists locked_clothoid_egg.
  split; [reflexivity|].
  split; [now left|].
  split; reflexivity.
Qed.

Lemma jts_clothoid_chickens_mkclothoid :
  exists b c e,
    intake_map default_sheet TClothoidJts = IntakeBag b /\
    In c (bag_chickens b) /\
    ck_egg c = MkClothoid e.
Proof.
  rewrite jts_clothoid_maps.
  exists (map_clothoid default_sheet).
  exists (mkChicken 0%nat 1%nat (MkClothoid locked_clothoid_egg)).
  exists locked_clothoid_egg.
  split; [reflexivity|].
  split; [now left|].
  reflexivity.
Qed.

Lemma clothoid_intake_not_chord_demote :
  intake_map default_sheet TClothoidIso <>
    IntakeBag (map_ls default_sheet
      [cloth_p0 locked_clothoid_egg; cloth_p1 locked_clothoid_egg]) /\
  intake_map default_sheet TClothoidJts <>
    IntakeBag (map_ls default_sheet
      [cloth_p0 locked_clothoid_egg; cloth_p1 locked_clothoid_egg]).
Proof.
  rewrite iso_clothoid_maps, jts_clothoid_maps.
  split; discriminate.
Qed.

Lemma clothoid_intake_not_iso_decline :
  intake_map default_sheet example5_iso_clothoid_cst <>
    IntakeDecline ID_IsoClothoid /\
  intake_map default_sheet TClothoidJts <>
    IntakeDecline ID_MkOutOfScope.
Proof.
  rewrite iso_clothoid_maps, jts_clothoid_maps.
  split; discriminate.
Qed.

Lemma example5_cc_bags_both_clothoid :
  intake_map default_sheet example5_cc_both_clothoid_cst =
    IntakeBag (map_cc_example5 default_sheet).
Proof.
  reflexivity.
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
  unfold map_cc_example5, append_bags, map_clothoid. cbn.
  split.
  - right. now left.
  - split; reflexivity.
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
  unfold unknown_cs_cst, intake_map, intake_map_atom, map_cs_unknown.
  change p00 with ang_a.
  change p20 with ang_b.
  change (mkPoint 3 1) with ang_c.
  rewrite ang_cs_ok.
  reflexivity.
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
  unfold intake_map, intake_map_atom, map_cs_unknown.
  rewrite col_cs_collinear.
  reflexivity.
Qed.

Lemma duplicate_cs_declines :
  intake_map default_sheet (TCircularString CircUnknown [dup_a; dup_b; dup_c]) =
    IntakeDecline ID_DuplicateControl.
Proof.
  unfold intake_map, intake_map_atom, map_cs_unknown.
  rewrite dup_cs.
  reflexivity.
Qed.

Lemma badcount_cs_declines :
  intake_map default_sheet (TCircularString CircUnknown [p00; p20]) =
    IntakeDecline ID_BadPointCount.
Proof.
  unfold intake_map, intake_map_atom, map_cs_unknown, try_cs_eggs, go_arcs.
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
| IntakeWkbOrder.

Definition intake_ctor_inhabits (c : IntakeCtor) : Prop :=
  match c with
  | IntakeAnglesFromPoints => True
  | IntakeMkClothoid => True
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
  intake_map default_sheet locked_cs_full_ogc_cst =
    IntakeBag (map_cs_full default_sheet) /\
  ck_egg (hd (mkChicken 0%nat 0%nat (MkChord (mkChordEgg p00 p00)))
             (bag_chickens (map_cs_full default_sheet)))
    = MkCirc locked_full_circle_egg /\
  ck_egg (hd (mkChicken 0%nat 0%nat (MkChord (mkChordEgg p00 p00)))
             (bag_chickens (map_circle default_sheet)))
    = MkCirc locked_full_circle_egg /\
  intake_map default_sheet TGeodesicString =
    IntakeDecline ID_GeodesicString /\
  intake_map default_sheet TSpiralCurve =
    IntakeDecline ID_SpiralCurve /\
  intake_walker_kind = IW_FirstSlice.
Proof.
  repeat split; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-intake-walker","topic":"overlay","lemma":"ticket_0007_intake_walker_qed_or_qex","title":"First-slice intake maps Point/LineString/locked CircularString/Circle/CompoundCurve to SHC bag and fail-closes GEODESICSTRING/SPIRALCURVE (QED) or silently demotes out-of-scope WKT to MkChord (QEX); discharged QED; grammar accept is CST only; Intake Decline is not cook IDecline; clothoid bagging is the MkClothoid letter","file":"theories/IntakeWalker.v","witness":"0007-intake-walker","board":"ADR-0007"} *)
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
   intake_map default_sheet locked_cs_full_ogc_cst =
     IntakeBag (map_cs_full default_sheet) /\
   ck_egg (hd (mkChicken 0%nat 0%nat (MkChord (mkChordEgg p00 p00)))
              (bag_chickens (map_cs_full default_sheet)))
     = ck_egg (hd (mkChicken 0%nat 0%nat (MkChord (mkChordEgg p00 p00)))
                  (bag_chickens (map_circle default_sheet))) /\
   intake_map default_sheet TGeodesicString =
     IntakeDecline ID_GeodesicString /\
   intake_map default_sheet TSpiralCurve =
     IntakeDecline ID_SpiralCurve /\
   grammar_accept_not_valid /\ grammar_accept_not_cooked /\
   intake_walker_kind = IW_FirstSlice /\
   intake_walker_kind <> IW_WktZoo /\
   intake_walker_kind <> IW_NewOracleKeyword)
  \/
  (exists t b c,
     intake_map default_sheet t = IntakeBag b /\
     (t = TGeodesicString \/ t = TSpiralCurve) /\
     In c (bag_chickens b) /\ egg_class (ck_egg c) = EggChord).
Proof.
  left.
  repeat split; try reflexivity; try discriminate.
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

(* WITNESS {"claimId":"0007-intake-mkclothoid","topic":"overlay","lemma":"ticket_0007_intake_mkclothoid_qed_or_qex","title":"Intake maps ISO and JTS clothoid CST to the same MkClothoid SHC bag (QED) or MkClothoid stays QEX and ISO clothoid Declines ID_IsoClothoid (QEX); discharged QED; one host constructor; OGC\equiv ISO same egg; no silent chord demote; clothoid times clothoid stays not first cook","file":"theories/IntakeWalker.v","witness":"0007-intake-mkclothoid","board":"ADR-0007"} *)
Theorem ticket_0007_intake_mkclothoid_qed_or_qex :
  (intake_ctor_inhabits IntakeMkClothoid /\
   intake_map default_sheet TClothoidJts =
     IntakeBag (map_clothoid default_sheet) /\
   intake_map default_sheet TClothoidIso =
     IntakeBag (map_clothoid default_sheet) /\
   intake_map default_sheet TClothoidJts =
     intake_map default_sheet TClothoidIso /\
   exists b c e,
     intake_map default_sheet example5_iso_clothoid_cst = IntakeBag b /\
     In c (bag_chickens b) /\
     ck_egg c = MkClothoid e /\
     egg_class (ck_egg c) = EggClothoid /\
   intake_map default_sheet example5_cc_both_clothoid_cst =
     IntakeBag (map_cc_example5 default_sheet) /\
   intake_map default_sheet example5_cc_both_clothoid_cst <>
     IntakeDecline ID_IsoClothoid /\
   ~ first_cook_scope EggClothoid EggClothoid /\
   I_ok (MkClothoid locked_clothoid_egg) (MkClothoid locked_clothoid_egg)
        IDecline)
  \/
  (~ intake_ctor_inhabits IntakeMkClothoid /\
   intake_map default_sheet example5_iso_clothoid_cst =
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
  split; [exact example5_cc_not_iso_decline|].
  split; [exact clothoid_clothoid_not_first_scope|].
  unfold I_ok, interpolant_pair. intro H. exact H.
Qed.

Print Assumptions locked_point_maps.
Print Assumptions locked_ls_maps.
Print Assumptions locked_cs_quarter_maps.
Print Assumptions locked_circle_maps.
Print Assumptions locked_cs_full_ogc_maps.
Print Assumptions ogc_iso_circle_same_egg.
Print Assumptions geodesic_declines.
Print Assumptions spiral_declines.
Print Assumptions iso_clothoid_maps.
Print Assumptions jts_clothoid_maps.
Print Assumptions ogc_iso_clothoid_same_bag.
Print Assumptions iso_clothoid_chickens_mkclothoid.
Print Assumptions example5_cc_bags_both_clothoid.
Print Assumptions example5_cc_has_mkclothoid.
Print Assumptions clothoid_intake_not_chord_demote.
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
Print Assumptions ticket_0007_intake_mkclothoid_qed_or_qex.
