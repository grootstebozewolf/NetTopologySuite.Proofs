(* ============================================================================
   NetTopologySuite.Proofs.IntakeGeodesic
   ----------------------------------------------------------------------------
   ADR-0007 letter: GeodesicString as sheet geodesic
   (claimId 0007-intake-geodesic). μ lives in IntakeWalker.
   This module inhabits the sheet-geodesic facts: same bag as
   LineString, MkChord eggs only, γ_ch joints, first-cook
   reuse, and named QEX.

   S = (O; e1, e2). γ_ch(c) : [0,1] → S is chord_eval.
   μ(S, TGeodesicString pts) = μ(S, TLineString pts).
   Well-formedness is the map_ls shape (empty / bad-count).
   Consecutive-duplicate is not a mapper Decline on LS
   (literal degenerate MkChord); geodesic matches.

   eggs(b) = MkChord(mkChordEgg p_i p_{i+1}). No MkCirc /
   MkClothoid / MkGeodesic. Joints: γ_ch(c_i)(1) = p_{i+1}
   = γ_ch(c_{i+1})(0). Consecutive eggs are chord×chord,
   already first_cook_scope.

   π(LS)=LINESTRING, π(G)=GEODESICSTRING, and
   GEODESICSTRING ∉ T_signed (SqlMmSignedTag). κ unchanged.

   What this is not: ambient γ on sphere / torus / cone /
   saddle; plane section (ellipse / conic); MkClothoid or
   MkCirc; first-cook expand; new oracle keyword; WKB 13;
   emit of bytes.

   WITNESS topic: overlay · claimId: 0007-intake-geodesic
   witness: 0007-intake-geodesic
   board: ADR-0007
   3-axiom host. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals List.
From NTS.Proofs Require Import Distance SheetHenCook IntakeWalker SqlMmSignedTag.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* μ(S, c_G) = μ(S, c_LS). Same Decline reasons.                              *)
(* -------------------------------------------------------------------------- *)

Lemma geodesic_ls_same_mu :
  forall s pts,
    intake_map s (TGeodesicString pts) = intake_map s (TLineString pts).
Proof.
  intros s pts.
  unfold intake_map, intake_map_atom.
  destruct pts as [|p rest]; [reflexivity|].
  destruct rest; reflexivity.
Qed.

Lemma geodesic_consec_dup_same_as_ls :
  intake_map default_sheet (TGeodesicString [p00; p00]) =
    intake_map default_sheet (TLineString [p00; p00]) /\
  intake_map default_sheet (TGeodesicString [p00; p00]) =
    IntakeBag (map_ls default_sheet [p00; p00]).
Proof. split; reflexivity. Qed.

Lemma locked_geodesic3_same_bag_as_ls :
  intake_map default_sheet locked_geodesic3_cst =
    intake_map default_sheet locked_ls3_cst /\
  intake_map default_sheet locked_geodesic3_cst =
    IntakeBag (map_ls default_sheet [p00; p20; p50]).
Proof. split; reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Eggs are MkChord(p_i, p_{i+1}) only.                                       *)
(* -------------------------------------------------------------------------- *)

Lemma chords_of_pts_in_is_mkchord :
  forall pts h0 ck,
    In ck (chords_of_pts pts h0) ->
    exists p q, ck_egg ck = MkChord (mkChordEgg p q).
Proof.
  intros pts. induction pts as [|p rest IH]; intros h0 ck Hin.
  - contradiction.
  - destruct rest as [|q rest'].
    + contradiction.
    + simpl in Hin. destruct Hin as [Heq|Hin'].
      * exists p, q. rewrite <- Heq. reflexivity.
      * apply (IH (S h0) ck Hin').
Qed.

Lemma geodesic_bag_eggs_mkchord :
  forall s pts ck,
    In ck (bag_chickens (map_ls s pts)) ->
    exists p q, ck_egg ck = MkChord (mkChordEgg p q).
Proof.
  intros s pts ck Hin.
  unfold map_ls, bag_chickens in Hin.
  apply chords_of_pts_in_is_mkchord in Hin. exact Hin.
Qed.

Lemma geodesic_bag_not_mkcirc :
  forall s pts ck γ,
    In ck (bag_chickens (map_ls s pts)) ->
    ck_egg ck <> MkCirc γ.
Proof.
  intros s pts ck γ Hin Hcirc.
  destruct (geodesic_bag_eggs_mkchord s pts ck Hin) as [p [q Heq]].
  rewrite Heq in Hcirc. discriminate.
Qed.

Lemma geodesic_bag_not_mkclothoid :
  forall s pts ck k,
    In ck (bag_chickens (map_ls s pts)) ->
    ck_egg ck <> MkClothoid k.
Proof.
  intros s pts ck k Hin Hcl.
  destruct (geodesic_bag_eggs_mkchord s pts ck Hin) as [p [q Heq]].
  rewrite Heq in Hcl. discriminate.
Qed.

Lemma locked_geodesic3_eggs :
  bag_chickens (map_ls default_sheet [p00; p20; p50]) =
    [mkChicken 0%nat 1%nat (MkChord (mkChordEgg p00 p20));
     mkChicken 1%nat 2%nat (MkChord (mkChordEgg p20 p50))].
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Joints: γ_ch(c_i)(1) = p_{i+1} = γ_ch(c_{i+1})(0).                         *)
(* -------------------------------------------------------------------------- *)

Lemma chord_sheet_joint :
  forall p q r,
    chord_eval (mkChordEgg p q) 1 = q /\
    chord_eval (mkChordEgg q r) 0 = q.
Proof.
  intros p q r.
  split; [apply chord_eval_at_1|apply chord_eval_at_0].
Qed.

Lemma locked_geodesic3_joints :
  chord_eval (mkChordEgg p00 p20) 1 = p20 /\
  chord_eval (mkChordEgg p20 p50) 0 = p20.
Proof. exact (chord_sheet_joint p00 p20 p50). Qed.

Lemma locked_geodesic3_tau :
  first_slice_tag (MkChord (mkChordEgg p00 p20)) = Some TagLineString /\
  first_slice_tag (MkChord (mkChordEgg p20 p50)) = Some TagLineString.
Proof. split; reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Cook: consecutive eggs are chord×chord, already first_cook_scope.          *)
(* -------------------------------------------------------------------------- *)

Lemma geodesic_consecutive_first_cook :
  forall e1 e2,
    egg_class e1 = EggChord ->
    egg_class e2 = EggChord ->
    first_cook_scope (egg_class e1) (egg_class e2).
Proof.
  intros e1 e2 H1 H2. rewrite H1, H2. exact first_cook_scope_chord_chord.
Qed.

Lemma locked_geodesic3_consecutive_cook :
  first_cook_scope
    (egg_class (MkChord (mkChordEgg p00 p20)))
    (egg_class (MkChord (mkChordEgg p20 p50))).
Proof. exact I. Qed.

(* -------------------------------------------------------------------------- *)
(* Named QEX: not ambient manifold γ, not conic, not emit / WKB 13.           *)
(* -------------------------------------------------------------------------- *)

Inductive IntakeGeodesicQex : Type :=
| IG_EllipsoidGamma
| IG_AmbientManifold
| IG_PlaneSectionConic
| IG_Wkb13SignedIo
| IG_EmitGeodesicBytes
| IG_TauEqPiOnGeodesicProd
| IG_FirstCookExpand
| IG_NewOracleKeyword.

Definition intake_geodesic_qex_inhabits (_ : IntakeGeodesicQex) : Prop := False.

Lemma intake_geodesic_ellipsoid_missing :
  ~ intake_geodesic_qex_inhabits IG_EllipsoidGamma.
Proof. intro H. exact H. Qed.

Lemma intake_geodesic_ambient_missing :
  ~ intake_geodesic_qex_inhabits IG_AmbientManifold.
Proof. intro H. exact H. Qed.

Lemma intake_geodesic_conic_missing :
  ~ intake_geodesic_qex_inhabits IG_PlaneSectionConic.
Proof. intro H. exact H. Qed.

Lemma intake_geodesic_wkb13_missing :
  ~ intake_geodesic_qex_inhabits IG_Wkb13SignedIo.
Proof. intro H. exact H. Qed.

Lemma intake_geodesic_emit_missing :
  ~ intake_geodesic_qex_inhabits IG_EmitGeodesicBytes.
Proof. intro H. exact H. Qed.

Lemma intake_geodesic_tau_eq_pi_missing :
  ~ intake_geodesic_qex_inhabits IG_TauEqPiOnGeodesicProd.
Proof. intro H. exact H. Qed.

Lemma intake_geodesic_no_first_cook_expand :
  ~ intake_geodesic_qex_inhabits IG_FirstCookExpand.
Proof. intro H. exact H. Qed.

Lemma intake_geodesic_no_new_keyword :
  ~ intake_geodesic_qex_inhabits IG_NewOracleKeyword.
Proof. intro H. exact H. Qed.

(* WITNESS {"claimId":"0007-intake-geodesic","topic":"overlay","lemma":"ticket_0007_intake_geodesic_qed_or_qex","title":"Sheet geodesic: well-formed GeodesicString bags the same MkChord SHC bag as LineString, eggs are MkChord only, gamma_ch joints, tau=LINESTRING, pi(G)=GEODESICSTRING not in T_signed, consecutive eggs already first_cook_scope (QED) or ambient manifold / conic / ellipsoid gamma / WKB 13 / emit / tau=pi / first-cook expand inhabit (QEX); discharged QED; not MkCirc/MkClothoid; non-clothoid SPIRALCURVE still Declines","file":"theories/IntakeGeodesic.v","witness":"0007-intake-geodesic","board":"ADR-0007"} *)
Theorem ticket_0007_intake_geodesic_qed_or_qex :
  (intake_ctor_inhabits IntakeGeodesicMkChord /\
   (forall s pts,
      intake_map s (TGeodesicString pts) = intake_map s (TLineString pts)) /\
   intake_map default_sheet locked_geodesic_cst =
     IntakeBag (map_ls default_sheet [p00; p20]) /\
   bag_chickens (map_ls default_sheet [p00; p20]) =
     [mkChicken 0%nat 1%nat (MkChord (mkChordEgg p00 p20))] /\
   bag_chickens (map_ls default_sheet [p00; p20; p50]) =
     [mkChicken 0%nat 1%nat (MkChord (mkChordEgg p00 p20));
      mkChicken 1%nat 2%nat (MkChord (mkChordEgg p20 p50))] /\
   chord_eval (mkChordEgg p00 p20) 1 = p20 /\
   chord_eval (mkChordEgg p20 p50) 0 = p20 /\
   first_slice_tag (MkChord (mkChordEgg p00 p20)) = Some TagLineString /\
   first_slice_tag (MkChord (mkChordEgg p20 p50)) = Some TagLineString /\
   cst_prod_name locked_ls_cst = PiLineString /\
   cst_prod_name locked_geodesic_cst = PiGeodesicString /\
   t_signed_of_prod PiGeodesicString = None /\
   first_cook_scope EggChord EggChord /\
   intake_map default_sheet spiral_bloss = IntakeDecline ID_SpiralOther)
  \/
  (intake_geodesic_qex_inhabits IG_EllipsoidGamma /\
   intake_geodesic_qex_inhabits IG_AmbientManifold /\
   intake_geodesic_qex_inhabits IG_PlaneSectionConic /\
   intake_geodesic_qex_inhabits IG_Wkb13SignedIo /\
   intake_geodesic_qex_inhabits IG_EmitGeodesicBytes /\
   intake_geodesic_qex_inhabits IG_TauEqPiOnGeodesicProd /\
   intake_geodesic_qex_inhabits IG_FirstCookExpand /\
   intake_geodesic_qex_inhabits IG_NewOracleKeyword).
Proof.
  left.
  split; [exact intake_geodesic_mkchord_inhabits|].
  split; [exact geodesic_ls_same_mu|].
  split; [exact locked_geodesic_maps|].
  split; [exact (proj1 locked_geodesic_is_chord)|].
  split; [exact locked_geodesic3_eggs|].
  destruct locked_geodesic3_joints as [Hj1 Hj2].
  split; [exact Hj1|].
  split; [exact Hj2|].
  destruct locked_geodesic3_tau as [Ht1 Ht2].
  split; [exact Ht1|].
  split; [exact Ht2|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact first_cook_scope_chord_chord|].
  exact spiral_declines.
Qed.

Print Assumptions geodesic_ls_same_mu.
Print Assumptions chords_of_pts_in_is_mkchord.
Print Assumptions geodesic_bag_eggs_mkchord.
Print Assumptions chord_sheet_joint.
Print Assumptions locked_geodesic3_joints.
Print Assumptions geodesic_consecutive_first_cook.
Print Assumptions ticket_0007_intake_geodesic_qed_or_qex.
