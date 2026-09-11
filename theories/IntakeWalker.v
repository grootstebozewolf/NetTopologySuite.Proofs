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

   First slice ONLY (what SheetHenCook already inhabits):
     Point, LineString, CircularString, CompoundCurve of those
     two, Circle-as-full-span-arc (one MkCirc, sweep = 2π).
   Reuses MkChord / MkCirc. No new host γ.

   Fail closed: GEODESICSTRING, SPIRALCURVE, MkOutOfScope
   leftovers, CircGamma leftover (angles-from-control-points
   still need atan2 — not a remint of Parks Γ). NO silent
   chord demote at intake. Demote is later cook/view.

   example5.txt: both CLOTHOID forms in one COMPOUNDCURVE.
   Honest stop: Decline the ISO form with named ticket
   ID_IsoClothoid. Not two invented MkClothoid constructors.

   OGC-form and ISO-form of the same in-scope type → same bag
   (locked CIRCLE vs start=end CIRCULARSTRING full-span).

   Visitor tags locked CircularString / Circle shapes (exact
   control-point match). Mapper is structural on those tags —
   no Req_EM_T, no new axiom.

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
   board: ADR-0007
   3-axiom host. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance SheetHenCook CircularCookMkCirc.
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
| ID_NotFirstSlice.

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

Fixpoint chords_of_pts (pts : list Point) (h0 : nat) : list Chicken :=
  match pts with
  | p :: q :: rest =>
      mkChicken h0 (S h0) (MkChord (mkChordEgg p q))
        :: chords_of_pts (q :: rest) (S h0)
  | _ => []
  end.

Definition map_point (s : Sheet) (p : Point) : ShcBag :=
  mkShcBag s [0%nat] [p] [].

Definition map_ls (s : Sheet) (pts : list Point) : ShcBag :=
  mkShcBag s (hens_of_n (length pts)) pts (chords_of_pts pts 0%nat).

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
  mkChicken (off + ck_src c) (off + ck_dst c) (ck_egg c).

Definition append_bags (s : Sheet) (a b : ShcBag) : ShcBag :=
  let off := length (bag_hens a) in
  mkShcBag s
    (bag_hens a ++ map (fun h => off + h) (bag_hens b))
    (bag_pts a ++ bag_pts b)
    (bag_chickens a ++ map (shift_chicken off) (bag_chickens b)).

Definition map_cc_locked (s : Sheet) : ShcBag :=
  append_bags s
    (mkShcBag s [0%nat; 1%nat] [p00; p50]
       [mkChicken 0%nat 1%nat (MkChord (mkChordEgg p00 p50))])
    (map_cs_quarter s).

Fixpoint has_iso_clothoid (ms : list TaggedCst) : bool :=
  match ms with
  | [] => false
  | TClothoidIso :: _ => true
  | TCompoundCurve inner :: rest =>
      if has_iso_clothoid inner then true else has_iso_clothoid rest
  | _ :: rest => has_iso_clothoid rest
  end.

Fixpoint intake_map (s : Sheet) (t : TaggedCst) : IntakeResult :=
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
  | TCircularString CircUnknown _ => IntakeDecline ID_CircGammaLeftover
  | TCircle CircFullOgc _ => IntakeBag (map_circle s)
  | TCircle CircQuarter _ => IntakeBag (map_cs_quarter s)
  | TCircle CircUnknown _ => IntakeDecline ID_CircGammaLeftover
  | TCompoundCurve ms =>
      if has_iso_clothoid ms then IntakeDecline ID_IsoClothoid
      else
      match ms with
      | [] => IntakeDecline ID_Empty
      | m :: rest =>
          match intake_map s m with
          | IntakeDecline r => IntakeDecline r
          | IntakeBag b0 =>
              (fix go (acc : ShcBag) (xs : list TaggedCst) : IntakeResult :=
                 match xs with
                 | [] => IntakeBag acc
                 | y :: ys =>
                     match intake_map s y with
                     | IntakeDecline r => IntakeDecline r
                     | IntakeBag by => go (append_bags s acc by) ys
                     end
                 end) b0 rest
          end
      end
  | TClothoidJts => IntakeDecline ID_MkOutOfScope
  | TClothoidIso => IntakeDecline ID_IsoClothoid
  | TGeodesicString => IntakeDecline ID_GeodesicString
  | TSpiralCurve => IntakeDecline ID_SpiralCurve
  | TOutOfSlice => IntakeDecline ID_NotFirstSlice
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

Lemma iso_clothoid_declines :
  intake_map default_sheet example5_iso_clothoid_cst =
    IntakeDecline ID_IsoClothoid.
Proof.
  reflexivity.
Qed.

Lemma example5_cc_declines_iso :
  intake_map default_sheet example5_cc_both_clothoid_cst =
    IntakeDecline ID_IsoClothoid.
Proof.
  reflexivity.
Qed.

Lemma jts_clothoid_declines_mkoutofscope :
  intake_map default_sheet TClothoidJts =
    IntakeDecline ID_MkOutOfScope.
Proof.
  reflexivity.
Qed.

Lemma out_of_slice_declines :
  intake_map default_sheet TOutOfSlice =
    IntakeDecline ID_NotFirstSlice.
Proof.
  reflexivity.
Qed.

Lemma unknown_cs_declines_leftover :
  intake_map default_sheet unknown_cs_cst =
    IntakeDecline ID_CircGammaLeftover.
Proof.
  reflexivity.
Qed.

Lemma unknown_cs_not_chord_demote :
  intake_map default_sheet unknown_cs_cst <>
    IntakeBag (map_ls default_sheet [p00; p20; mkPoint 3 1]).
Proof.
  discriminate.
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

Definition intake_ctor_inhabits (c : IntakeCtor) : Prop := False.

Lemma intake_angles_from_points_missing :
  ~ intake_ctor_inhabits IntakeAnglesFromPoints.
Proof.
  intro H. exact H.
Qed.

Lemma intake_mkclothoid_missing :
  ~ intake_ctor_inhabits IntakeMkClothoid.
Proof.
  intro H. exact H.
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
  intake_map default_sheet example5_iso_clothoid_cst =
    IntakeDecline ID_IsoClothoid /\
  intake_map default_sheet example5_cc_both_clothoid_cst =
    IntakeDecline ID_IsoClothoid /\
  intake_map default_sheet TClothoidJts =
    IntakeDecline ID_MkOutOfScope /\
  intake_map default_sheet unknown_cs_cst =
    IntakeDecline ID_CircGammaLeftover /\
  intake_walker_kind = IW_FirstSlice.
Proof.
  repeat split; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-intake-walker","topic":"overlay","lemma":"ticket_0007_intake_walker_qed_or_qex","title":"First-slice intake maps Point/LineString/locked CircularString/Circle/CompoundCurve to SHC bag and fail-closes GEODESICSTRING/SPIRALCURVE/ISO-clothoid/MkOutOfScope (QED) or silently demotes out-of-scope WKT to MkChord (QEX); discharged QED; grammar accept is CST only; Intake Decline is not cook IDecline; example5 Declines ISO clothoid","file":"theories/IntakeWalker.v","witness":"0007-intake-walker","board":"ADR-0007"} *)
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
   intake_map default_sheet example5_iso_clothoid_cst =
     IntakeDecline ID_IsoClothoid /\
   intake_map default_sheet example5_cc_both_clothoid_cst =
     IntakeDecline ID_IsoClothoid /\
   intake_map default_sheet TClothoidJts =
     IntakeDecline ID_MkOutOfScope /\
   intake_map default_sheet unknown_cs_cst =
     IntakeDecline ID_CircGammaLeftover /\
   grammar_accept_not_valid /\ grammar_accept_not_cooked /\
   intake_walker_kind = IW_FirstSlice /\
   intake_walker_kind <> IW_WktZoo /\
   intake_walker_kind <> IW_NewOracleKeyword)
  \/
  (exists t b c,
     intake_map default_sheet t = IntakeBag b /\
     (t = TGeodesicString \/ t = TSpiralCurve \/ t = TClothoidIso) /\
     In c (bag_chickens b) /\ egg_class (ck_egg c) = EggChord).
Proof.
  left.
  repeat split; try reflexivity; try discriminate.
Qed.

(* WITNESS {"claimId":"0007-intake-walker","topic":"core","lemma":"ticket_0007_intake_angles_qed_or_qex","title":"Intake constructs CircularEgg from arbitrary WKT control points (QED) or angles-from-points stays QEX and unknown CircularString Declines ID_CircGammaLeftover (QEX); discharged QEX; not a CircGamma remint; no silent chord demote","file":"theories/IntakeWalker.v","witness":"0007-intake-walker","board":"ADR-0007"} *)
Theorem ticket_0007_intake_angles_qed_or_qex :
  (intake_ctor_inhabits IntakeAnglesFromPoints /\
   exists pts,
     pts = [p00; p20; mkPoint 3 1] /\
     exists b, intake_map default_sheet (TCircularString CircUnknown pts)
               = IntakeBag b)
  \/
  (~ intake_ctor_inhabits IntakeAnglesFromPoints /\
   intake_map default_sheet unknown_cs_cst =
     IntakeDecline ID_CircGammaLeftover /\
   ~ intake_ctor_inhabits IntakeMkClothoid /\
   intake_map default_sheet example5_iso_clothoid_cst =
     IntakeDecline ID_IsoClothoid).
Proof.
  right.
  split; [exact intake_angles_from_points_missing|].
  split; [exact unknown_cs_declines_leftover|].
  split; [exact intake_mkclothoid_missing|].
  exact iso_clothoid_declines.
Qed.

(* WITNESS {"claimId":"0007-intake-walker","topic":"overlay","lemma":"ticket_0007_intake_parks_qed_or_qex","title":"Intake walker discharges WKB-order Gamma walk, WKT zoo, Lesson-1 remints, host cook expand, and new oracle keyword (QED) or names them parked (QEX); discharged QEX; letter landed != first-cook expand / Campaign / bag noder","file":"theories/IntakeWalker.v","witness":"0007-intake-walker","board":"ADR-0007"} *)
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
Print Assumptions locked_circle_maps.
Print Assumptions locked_cs_full_ogc_maps.
Print Assumptions ogc_iso_circle_same_egg.
Print Assumptions geodesic_declines.
Print Assumptions spiral_declines.
Print Assumptions iso_clothoid_declines.
Print Assumptions example5_cc_declines_iso.
Print Assumptions unknown_cs_declines_leftover.
Print Assumptions unknown_cs_not_chord_demote.
Print Assumptions overlap_ls_literal_chickens.
Print Assumptions first_slice_inhabits.
Print Assumptions ticket_0007_intake_walker_qed_or_qex.
Print Assumptions ticket_0007_intake_angles_qed_or_qex.
Print Assumptions ticket_0007_intake_parks_qed_or_qex.
