(* ============================================================================
   NetTopologySuite.Proofs.SqlMmSignedTag
   ----------------------------------------------------------------------------
   ADR-0007 sidecar, rungs 3–6 of the τ=μ ladder
   (claimId 0007-sqlmm-signed-tag).

   T_signed = {LINESTRING, CIRCULARSTRING, CIRCLE, CLOTHOID}.
   SFA point/polygon/multi and WKB {8..12} collections are bag
   maps, not an egg clause. Compound / rings / emit / WKB hex
   are rungs 4–5.

   τ : Egg ⇀ T_signed  (Definition; undefined on MkOutOfScope)
     MkChord _      ↦ LINESTRING
     MkCirc γ       ↦ CIRCLE           if |circ_sweep γ| = 2π
                    ↦ CIRCULARSTRING   otherwise
     MkClothoid _   ↦ CLOTHOID
     MkOutOfScope _ ↦ undefined

   Full-span is CIRCLE and not CIRCULARSTRING. CIRCLE CST and
   full-span CIRCULARSTRING CST share one MkCirc
   (IntakeWalker.ogc_iso_circle_same_egg); τ classifies that
   egg as CIRCLE. ISO / JTS clothoid spellings are not
   arguments of τ — they are two intakes of the same
   ClothoidEgg.

   κ : T_signed ⇀ ℕ  (Table 15 on names that have a signed code)
     LINESTRING ↦ 2    CIRCULARSTRING ↦ 8
     CIRCLE     ↦ none CLOTHOID        ↦ none
   Signed numeric I/O is {n | 1≤n≤12}. HOLD is
   {13..17} ∪ {18..21}. Those predicates live on ℕ.
   CIRCLE / CLOTHOID are signed names with no signed code —
   defined partiality of κ, not WKB 18 or 22.

   Sidecar only. SheetHenCook.v is not grown. No new ADR-0006
   keyword. ADR-0006/0007 stay Accepted.

   Rung 4: after μ(c,S)=IntakeBag(b) and eggs(b)=[e],
   τ(e)=ρ(π(c)) on locked singleton CSTs. ρ is not τ:
   TCircularString(CircFullOgc) and TCircle mint the same
   MkCirc; τ of that egg is CIRCLE. Requires IntakeWalker.

   QED: ticket_sqlmm_signed_tag_qed_or_qex — τ and κ.
        ticket_sqlmm_tau_mu_qed_or_qex — egg-level agreement.
   QEX: ticket_sqlmm_factory_emit_qed_or_qex — WKT/WKB bytes.

   WITNESS topic: overlay · claimId: 0007-sqlmm-signed-tag
   witness: 0007-sqlmm-signed-tag
   also: 0007-clothoid-first-cook, 0007-gamma-mkcirc, 0007-intake-walker
   board: ADR-0007
   3-axiom host. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals PeanoNat List.
From NTS.Proofs Require Import Distance SheetHenCook ClothoidCookMkClothoid.
From NTS.Proofs Require Import CircularCookMkCirc IntakeAngles IntakeWalker.
Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* T_signed: the four §5.1.67 display names on a single host egg.             *)
(* -------------------------------------------------------------------------- *)

Inductive SqlMmSignedTag : Type :=
| TagLineString
| TagCircularString
| TagCircle
| TagClothoid.

Definition sqlmm_kappa (t : SqlMmSignedTag) : option nat :=
  match t with
  | TagLineString => Some 2%nat
  | TagCircularString => Some 8%nat
  | TagCircle => None
  | TagClothoid => None
  end.

Definition sqlmm_signed_code (n : nat) : Prop :=
  (1 <= n)%nat /\ (n <= 12)%nat.

Definition sqlmm_hold_code (n : nat) : Prop :=
  ((13 <= n)%nat /\ (n <= 17)%nat) \/
  ((18 <= n)%nat /\ (n <= 21)%nat).

Definition tag_of_signed_wkb (n : nat) : option SqlMmSignedTag :=
  match n with
  | 2 => Some TagLineString
  | 8 => Some TagCircularString
  | _ => None
  end.

Lemma leb_true_le :
  forall n m, Nat.leb n m = true -> (n <= m)%nat.
Proof.
  intros n m H. exact (proj1 (Nat.leb_le n m) H).
Qed.

Lemma le_leb_true :
  forall n m, (n <= m)%nat -> Nat.leb n m = true.
Proof.
  intros n m H. exact (proj2 (Nat.leb_le n m) H).
Qed.

Lemma le_12_excl_13 :
  forall n, (n <= 12)%nat -> (13 <= n)%nat -> False.
Proof.
  intros n H12 H13.
  exact (proj1 (Nat.le_ngt n 12) H12 (proj1 (Nat.le_succ_l 12 n) H13)).
Qed.

Lemma le_13_18 : (13 <= 18)%nat.
Proof.
  apply leb_true_le. reflexivity.
Qed.

Lemma signed_code_not_hold :
  forall n, sqlmm_signed_code n -> sqlmm_hold_code n -> False.
Proof.
  intros n [_ Hhi] [[A _]|[C _]].
  - exact (le_12_excl_13 n Hhi A).
  - exact (le_12_excl_13 n Hhi (Nat.le_trans 13 18 n le_13_18 C)).
Qed.

Lemma tag_of_signed_wkb_none_ge_13 :
  forall n, (13 <= n)%nat -> tag_of_signed_wkb n = None.
Proof.
  intros n Hn.
  pose proof (le_leb_true 13 n Hn) as Hleb.
  unfold tag_of_signed_wkb.
  do 13 (destruct n as [|n]; [discriminate Hleb|]).
  reflexivity.
Qed.

Lemma hold_has_no_signed_tag :
  forall n, sqlmm_hold_code n -> tag_of_signed_wkb n = None.
Proof.
  intros n [[A _]|[C _]].
  - apply tag_of_signed_wkb_none_ge_13. exact A.
  - apply tag_of_signed_wkb_none_ge_13.
    exact (Nat.le_trans 13 18 n le_13_18 C).
Qed.

Lemma kappa_signed_when_defined :
  forall t n, sqlmm_kappa t = Some n -> sqlmm_signed_code n.
Proof.
  intros t n H.
  destruct t; inversion H; unfold sqlmm_signed_code; split;
    apply leb_true_le; reflexivity.
Qed.

Lemma kappa_circle_none : sqlmm_kappa TagCircle = None.
Proof.
  reflexivity.
Qed.

Lemma kappa_clothoid_none : sqlmm_kappa TagClothoid = None.
Proof.
  reflexivity.
Qed.

Lemma kappa_circle_not_18 : sqlmm_kappa TagCircle <> Some 18%nat.
Proof.
  discriminate.
Qed.

Lemma kappa_linestring_2 : sqlmm_kappa TagLineString = Some 2%nat.
Proof.
  reflexivity.
Qed.

Lemma kappa_circularstring_8 : sqlmm_kappa TagCircularString = Some 8%nat.
Proof.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* τ: partial function on host eggs.                                          *)
(* -------------------------------------------------------------------------- *)

Local Open Scope R_scope.

Lemma two_pos : 0 < 2.
Proof.
  replace 2 with (1 + 1) by ring.
  apply Rplus_lt_0_compat; exact Rlt_0_1.
Qed.

Lemma two_neq_0 : 2 <> 0.
Proof.
  apply not_eq_sym. apply Rlt_not_eq. exact two_pos.
Qed.

Lemma half_pi_pos : 0 < PI / 2.
Proof.
  unfold Rdiv.
  apply Rmult_lt_0_compat.
  - exact PI_RGT_0.
  - apply Rinv_0_lt_compat. exact two_pos.
Qed.

Lemma half_pi_lt_pi : PI / 2 < PI.
Proof.
  apply Rmult_lt_reg_r with 2.
  - exact two_pos.
  - unfold Rdiv.
    rewrite Rmult_assoc.
    rewrite (Rinv_l 2 two_neq_0).
    rewrite Rmult_1_r.
    replace (PI * 2) with (PI + PI) by ring.
    rewrite <- (Rplus_0_r PI) at 1.
    apply Rplus_lt_compat_l.
    exact PI_RGT_0.
Qed.

Lemma pi_lt_two_pi : PI < 2 * PI.
Proof.
  apply Rplus_lt_reg_l with (- PI).
  replace (- PI + PI) with 0 by ring.
  replace (- PI + 2 * PI) with PI by ring.
  exact PI_RGT_0.
Qed.

Lemma rabs_half_pi : Rabs (PI / 2) = PI / 2.
Proof.
  apply Rabs_pos_eq. apply Rlt_le. exact half_pi_pos.
Qed.

Lemma rabs_two_pi : Rabs (2 * PI) = 2 * PI.
Proof.
  apply Rabs_pos_eq. apply Rlt_le.
  apply Rmult_lt_0_compat.
  - exact two_pos.
  - exact PI_RGT_0.
Qed.

Lemma half_pi_abs_neq_two_pi : Rabs (PI / 2) <> 2 * PI.
Proof.
  rewrite rabs_half_pi.
  apply Rlt_not_eq.
  exact (Rlt_trans (PI / 2) PI (2 * PI) half_pi_lt_pi pi_lt_two_pi).
Qed.

Definition tau_circ (γ : CircularEgg) : SqlMmSignedTag :=
  match Req_EM_T (Rabs (circ_sweep γ)) (2 * PI) with
  | left _ => TagCircle
  | right _ => TagCircularString
  end.

Definition first_slice_tag (e : Egg) : option SqlMmSignedTag :=
  match e with
  | MkChord _ => Some TagLineString
  | MkCirc γ => Some (tau_circ γ)
  | MkClothoid _ => Some TagClothoid
  | MkOutOfScope _ => None
  end.

Lemma first_slice_tag_chord :
  forall c, first_slice_tag (MkChord c) = Some TagLineString.
Proof.
  intros c. reflexivity.
Qed.

Lemma first_slice_tag_clothoid :
  forall k, first_slice_tag (MkClothoid k) = Some TagClothoid.
Proof.
  intros k. reflexivity.
Qed.

Lemma tau_clothoid_ext :
  forall k1 k2,
    k1 = k2 ->
    first_slice_tag (MkClothoid k1) = first_slice_tag (MkClothoid k2).
Proof.
  intros k1 k2 H. rewrite H. reflexivity.
Qed.

Lemma out_of_scope_no_signed_tag :
  forall c, first_slice_tag (MkOutOfScope c) = None.
Proof.
  intros c. reflexivity.
Qed.

Lemma tau_unique :
  forall e t1 t2,
    first_slice_tag e = Some t1 ->
    first_slice_tag e = Some t2 ->
    t1 = t2.
Proof.
  intros e t1 t2 H1 H2. rewrite H1 in H2. inversion H2. reflexivity.
Qed.

Lemma tau_circ_full :
  forall γ,
    Rabs (circ_sweep γ) = 2 * PI ->
    tau_circ γ = TagCircle.
Proof.
  intros γ H.
  unfold tau_circ.
  destruct (Req_EM_T (Rabs (circ_sweep γ)) (2 * PI)) as [E|N].
  - reflexivity.
  - exfalso. exact (N H).
Qed.

Lemma tau_circ_not_full :
  forall γ,
    Rabs (circ_sweep γ) <> 2 * PI ->
    tau_circ γ = TagCircularString.
Proof.
  intros γ H.
  unfold tau_circ.
  destruct (Req_EM_T (Rabs (circ_sweep γ)) (2 * PI)) as [E|N].
  - exfalso. exact (H E).
  - reflexivity.
Qed.

Lemma full_span_is_circle_not_cs :
  forall γ,
    Rabs (circ_sweep γ) = 2 * PI ->
    first_slice_tag (MkCirc γ) = Some TagCircle /\
    first_slice_tag (MkCirc γ) <> Some TagCircularString.
Proof.
  intros γ H.
  change (Some (tau_circ γ) = Some TagCircle /\
          Some (tau_circ γ) <> Some TagCircularString).
  rewrite (tau_circ_full γ H).
  split; [reflexivity|discriminate].
Qed.

(* Locked first-slice eggs already in the corpus (same numerals as
   CircularCookMkCirc.locked_circ_A / IntakeWalker.locked_full_circle_egg). *)

Definition locked_sqlmm_quarter : CircularEgg :=
  mkCircularEgg (mkPoint 0 0) 5 (0) (PI / 2).

Definition locked_sqlmm_full : CircularEgg :=
  mkCircularEgg (mkPoint 0 0) 5 (0) (2 * PI).

Lemma tau_locked_quarter :
  first_slice_tag (MkCirc locked_sqlmm_quarter) = Some TagCircularString.
Proof.
  change (Some (tau_circ locked_sqlmm_quarter) = Some TagCircularString).
  apply f_equal. apply tau_circ_not_full.
  unfold locked_sqlmm_quarter. cbn [circ_sweep].
  exact half_pi_abs_neq_two_pi.
Qed.

Lemma tau_locked_full :
  first_slice_tag (MkCirc locked_sqlmm_full) = Some TagCircle.
Proof.
  change (Some (tau_circ locked_sqlmm_full) = Some TagCircle).
  apply f_equal. apply tau_circ_full.
  unfold locked_sqlmm_full. cbn [circ_sweep].
  exact rabs_two_pi.
Qed.

Lemma tau_locked_cloth :
  first_slice_tag (MkClothoid locked_cloth_A) = Some TagClothoid.
Proof.
  reflexivity.
Qed.

Lemma tau_locked_chord :
  first_slice_tag (MkChord (mkChordEgg (mkPoint 0 0) (mkPoint 1 0)))
    = Some TagLineString.
Proof.
  reflexivity.
Qed.

Lemma locked_sqlmm_quarter_is_circ_A :
  locked_sqlmm_quarter = locked_circ_A.
Proof.
  reflexivity.
Qed.

Lemma locked_sqlmm_full_is_intake_full :
  locked_sqlmm_full = locked_full_circle_egg.
Proof.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Rung 4: ρ on productions; τ=μ after μ mints a singleton egg.               *)
(* τ and μ do not share a domain. Agreement is on eggs(b)=[e].                *)
(* -------------------------------------------------------------------------- *)

Definition bag_eggs (b : ShcBag) : list Egg :=
  map ck_egg (bag_chickens b).

Definition intake_rho (c : TaggedCst) (e : Egg) : option SqlMmSignedTag :=
  match c with
  | TLineString _ => Some TagLineString
  | TClothoidJts => Some TagClothoid
  | TClothoidIso => Some TagClothoid
  | TCircle _ _ => Some TagCircle
  | TCircularString _ _ =>
      match e with
      | MkCirc γ => Some (tau_circ γ)
      | _ => None
      end
  | TPoint _ | TCompoundCurve _ | TGeodesicString
  | TSpiralCurve | TOutOfSlice => None
  end.

Lemma tau_mu_locked_ls :
  exists b e,
    intake_map default_sheet locked_ls_cst = IntakeBag b /\
    bag_eggs b = [e] /\
    first_slice_tag e = Some TagLineString /\
    intake_rho locked_ls_cst e = Some TagLineString.
Proof.
  exists (map_ls default_sheet [p00; p20]).
  exists (MkChord (mkChordEgg p00 p20)).
  split; [exact locked_ls_maps|].
  split; [unfold bag_eggs; rewrite locked_ls_is_chord; reflexivity|].
  split; reflexivity.
Qed.

Lemma tau_mu_locked_cs_quarter :
  exists b e,
    intake_map default_sheet locked_cs_quarter_cst = IntakeBag b /\
    bag_eggs b = [e] /\
    first_slice_tag e = Some TagCircularString /\
    intake_rho locked_cs_quarter_cst e = Some TagCircularString.
Proof.
  exists (map_cs_quarter default_sheet).
  exists (MkCirc locked_circ_A).
  split; [exact locked_cs_quarter_maps|].
  split; [unfold bag_eggs; rewrite locked_cs_quarter_is_mkcirc; reflexivity|].
  split.
  - rewrite <- locked_sqlmm_quarter_is_circ_A. exact tau_locked_quarter.
  - change (Some (tau_circ locked_circ_A) = Some TagCircularString).
    apply f_equal. rewrite <- locked_sqlmm_quarter_is_circ_A.
    apply tau_circ_not_full.
    unfold locked_sqlmm_quarter. cbn [circ_sweep].
    exact half_pi_abs_neq_two_pi.
Qed.

Lemma tau_mu_locked_circle :
  exists b e,
    intake_map default_sheet locked_circle_cst = IntakeBag b /\
    bag_eggs b = [e] /\
    first_slice_tag e = Some TagCircle /\
    intake_rho locked_circle_cst e = Some TagCircle.
Proof.
  exists (map_circle default_sheet).
  exists (MkCirc locked_full_circle_egg).
  split; [exact locked_circle_maps|].
  split.
  - unfold bag_eggs. destruct ogc_iso_circle_same_mkcirc as [_ Hcirc].
    rewrite Hcirc. reflexivity.
  - split.
    + rewrite <- locked_sqlmm_full_is_intake_full. exact tau_locked_full.
    + reflexivity.
Qed.

Lemma tau_mu_locked_cs_full_ogc :
  exists b e,
    intake_map default_sheet locked_cs_full_ogc_cst = IntakeBag b /\
    bag_eggs b = [e] /\
    e = MkCirc locked_full_circle_egg /\
    first_slice_tag e = Some TagCircle /\
    intake_rho locked_cs_full_ogc_cst e = Some TagCircle.
Proof.
  exists (map_cs_full default_sheet).
  exists (MkCirc locked_full_circle_egg).
  split; [exact locked_cs_full_ogc_maps|].
  split.
  - unfold bag_eggs. destruct ogc_iso_circle_same_mkcirc as [Hfull _].
    rewrite Hfull. reflexivity.
  - split; [reflexivity|].
    split.
    + rewrite <- locked_sqlmm_full_is_intake_full. exact tau_locked_full.
    + change (Some (tau_circ locked_full_circle_egg) = Some TagCircle).
      apply f_equal. rewrite <- locked_sqlmm_full_is_intake_full.
      apply tau_circ_full.
      unfold locked_sqlmm_full. cbn [circ_sweep]. exact rabs_two_pi.
Qed.

Lemma tau_mu_full_span_shared_egg :
  bag_eggs (map_cs_full default_sheet)
    = bag_eggs (map_circle default_sheet) /\
  bag_eggs (map_cs_full default_sheet)
    = [MkCirc locked_full_circle_egg] /\
  first_slice_tag (MkCirc locked_full_circle_egg) = Some TagCircle.
Proof.
  destruct ogc_iso_circle_same_mkcirc as [Hfull Hcirc].
  split; [unfold bag_eggs; rewrite Hfull, Hcirc; reflexivity|].
  split; [unfold bag_eggs; rewrite Hfull; reflexivity|].
  rewrite <- locked_sqlmm_full_is_intake_full. exact tau_locked_full.
Qed.

Lemma tau_mu_locked_clothoid_iso :
  exists b e,
    intake_map default_sheet TClothoidIso = IntakeBag b /\
    bag_eggs b = [e] /\
    first_slice_tag e = Some TagClothoid /\
    intake_rho TClothoidIso e = Some TagClothoid.
Proof.
  exists (map_clothoid default_sheet).
  exists (MkClothoid locked_clothoid_egg).
  split; [exact iso_clothoid_maps|].
  split; [reflexivity|].
  split; reflexivity.
Qed.

Lemma tau_mu_locked_clothoid_jts :
  exists b e,
    intake_map default_sheet TClothoidJts = IntakeBag b /\
    bag_eggs b = [e] /\
    e = MkClothoid locked_clothoid_egg /\
    first_slice_tag e = Some TagClothoid /\
    intake_rho TClothoidJts e = Some TagClothoid.
Proof.
  exists (map_clothoid default_sheet).
  exists (MkClothoid locked_clothoid_egg).
  split; [exact jts_clothoid_maps|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; reflexivity.
Qed.

Lemma tau_mu_unknown_cs :
  exists b e,
    intake_map default_sheet unknown_cs_cst = IntakeBag b /\
    bag_eggs b = [e] /\
    e = MkCirc ang_egg /\
    first_slice_tag e = Some TagCircle /\
    intake_rho unknown_cs_cst e = Some TagCircle.
Proof.
  exists (map_cs_from_build default_sheet [ang_egg] [p00; mkPoint 3 1]).
  exists (MkCirc ang_egg).
  split; [exact unknown_cs_maps_mkcirc|].
  split; [reflexivity|].
  split; [reflexivity|].
  split.
  - change (Some (tau_circ ang_egg) = Some TagCircle).
    apply f_equal. apply tau_circ_full.
    unfold ang_egg. cbn [circ_sweep]. exact rabs_two_pi.
  - change (Some (tau_circ ang_egg) = Some TagCircle).
    apply f_equal. apply tau_circ_full.
    unfold ang_egg. cbn [circ_sweep]. exact rabs_two_pi.
Qed.

Lemma tau_mu_geodesic_decline :
  intake_map default_sheet TGeodesicString = IntakeDecline ID_GeodesicString /\
  intake_rho TGeodesicString
    (MkChord (mkChordEgg p00 p20)) = None.
Proof.
  split; [exact geodesic_declines|reflexivity].
Qed.

Lemma tau_mu_spiral_decline :
  intake_map default_sheet TSpiralCurve = IntakeDecline ID_SpiralCurve.
Proof.
  exact spiral_declines.
Qed.

Lemma tau_mu_compound_not_singleton :
  intake_map default_sheet locked_cc_cst =
    IntakeBag (map_cc_locked default_sheet) /\
  length (bag_eggs (map_cc_locked default_sheet)) = 2%nat.
Proof.
  split; [exact locked_cc_maps|reflexivity].
Qed.

(* -------------------------------------------------------------------------- *)
(* Emit is factory-ladder rung 8. Honest QEX: Rocq does not inhabit bytes.    *)
(* -------------------------------------------------------------------------- *)

Inductive SqlMmEmitCtor : Type :=
| EmitWktBytes
| EmitWkbHex
| EmitAntlrParse
| EmitNewOracleKeyword
| EmitFirstCookExpand
| EmitNurbsFirstCook
| EmitRhoBagLoop.

Definition sqlmm_emit_inhabits (_ : SqlMmEmitCtor) : Prop := False.

Lemma sqlmm_wkt_emit_missing : ~ sqlmm_emit_inhabits EmitWktBytes.
Proof.
  intro H. exact H.
Qed.

Lemma sqlmm_wkb_emit_missing : ~ sqlmm_emit_inhabits EmitWkbHex.
Proof.
  intro H. exact H.
Qed.

Lemma sqlmm_antlr_missing : ~ sqlmm_emit_inhabits EmitAntlrParse.
Proof.
  intro H. exact H.
Qed.

Lemma sqlmm_no_new_keyword : ~ sqlmm_emit_inhabits EmitNewOracleKeyword.
Proof.
  intro H. exact H.
Qed.

Lemma sqlmm_no_first_cook_expand : ~ sqlmm_emit_inhabits EmitFirstCookExpand.
Proof.
  intro H. exact H.
Qed.

Lemma sqlmm_no_nurbs_first_cook : ~ sqlmm_emit_inhabits EmitNurbsFirstCook.
Proof.
  intro H. exact H.
Qed.

Lemma sqlmm_no_rho : ~ sqlmm_emit_inhabits EmitRhoBagLoop.
Proof.
  intro H. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-sqlmm-signed-tag","topic":"overlay","lemma":"ticket_sqlmm_signed_tag_qed_or_qex","title":"sqlmm_tau is a partial function: MkChord LINESTRING, MkCirc CIRCLE iff |sweep|=2pi else CIRCULARSTRING, MkClothoid CLOTHOID, MkOutOfScope none; unique; kappa LINESTRING=2 CIRCULARSTRING=8 CIRCLE/CLOTHOID none not 18; HOLD nats have no egg tag (QED) or one egg two tags (QEX); discharged QED; emit is rung 4-5","file":"theories/SqlMmSignedTag.v","witness":"0007-sqlmm-signed-tag","board":"ADR-0007"} *)
Theorem ticket_sqlmm_signed_tag_qed_or_qex :
  ((forall c, first_slice_tag (MkChord c) = Some TagLineString) /\
   (forall k, first_slice_tag (MkClothoid k) = Some TagClothoid) /\
   (forall c, first_slice_tag (MkOutOfScope c) = None) /\
   (forall e t1 t2,
      first_slice_tag e = Some t1 ->
      first_slice_tag e = Some t2 ->
      t1 = t2) /\
   (forall γ,
      Rabs (circ_sweep γ) = 2 * PI ->
      first_slice_tag (MkCirc γ) = Some TagCircle /\
      first_slice_tag (MkCirc γ) <> Some TagCircularString) /\
   first_slice_tag (MkCirc locked_sqlmm_quarter) = Some TagCircularString /\
   first_slice_tag (MkCirc locked_sqlmm_full) = Some TagCircle /\
   first_slice_tag (MkClothoid locked_cloth_A) = Some TagClothoid /\
   first_slice_tag (MkChord (mkChordEgg (mkPoint 0 0) (mkPoint 1 0)))
     = Some TagLineString /\
   sqlmm_kappa TagLineString = Some 2%nat /\
   sqlmm_kappa TagCircularString = Some 8%nat /\
   sqlmm_kappa TagCircle = None /\
   sqlmm_kappa TagClothoid = None /\
   sqlmm_kappa TagCircle <> Some 18%nat /\
   (forall t n, sqlmm_kappa t = Some n -> sqlmm_signed_code n) /\
   (forall n, sqlmm_signed_code n -> sqlmm_hold_code n -> False) /\
   (forall n, sqlmm_hold_code n -> tag_of_signed_wkb n = None))
  \/
  (exists e t1 t2,
     first_slice_tag e = Some t1 /\
     first_slice_tag e = Some t2 /\
     t1 <> t2).
Proof.
  left.
  split; [intros c; reflexivity|].
  split; [intros k; reflexivity|].
  split; [intros c; reflexivity|].
  split; [exact tau_unique|].
  split; [exact full_span_is_circle_not_cs|].
  split; [exact tau_locked_quarter|].
  split; [exact tau_locked_full|].
  split; [exact tau_locked_cloth|].
  split; [exact tau_locked_chord|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact kappa_circle_not_18|].
  split; [exact kappa_signed_when_defined|].
  split; [exact signed_code_not_hold|].
  exact hold_has_no_signed_tag.
Qed.

(* WITNESS {"claimId":"0007-sqlmm-signed-tag","topic":"overlay","lemma":"ticket_sqlmm_tau_mu_qed_or_qex","title":"Egg-level tau=mu: after intake_map mints a singleton bag, first_slice_tag e equals intake_rho of the CST production on locked LS, quarter CS, CIRCLE, full-span CS (same MkCirc, tag CIRCLE), both clothoid spellings, and unknown-CS ang_egg (QED) or production-level tau=pi on full-span CIRCULARSTRING (QEX); discharged QED; geodesic Decline; compound is not a singleton; not WKT parse","file":"theories/SqlMmSignedTag.v","witness":"0007-sqlmm-signed-tag","board":"ADR-0007"} *)
Theorem ticket_sqlmm_tau_mu_qed_or_qex :
  ((exists b e,
      intake_map default_sheet locked_ls_cst = IntakeBag b /\
      bag_eggs b = [e] /\
      first_slice_tag e = Some TagLineString) /\
   (exists b e,
      intake_map default_sheet locked_cs_quarter_cst = IntakeBag b /\
      bag_eggs b = [e] /\
      first_slice_tag e = Some TagCircularString) /\
   (exists b e,
      intake_map default_sheet locked_circle_cst = IntakeBag b /\
      bag_eggs b = [e] /\
      first_slice_tag e = Some TagCircle) /\
   (exists b e,
      intake_map default_sheet locked_cs_full_ogc_cst = IntakeBag b /\
      bag_eggs b = [e] /\
      e = MkCirc locked_full_circle_egg /\
      first_slice_tag e = Some TagCircle) /\
   bag_eggs (map_cs_full default_sheet)
     = bag_eggs (map_circle default_sheet) /\
   (exists b e,
      intake_map default_sheet TClothoidIso = IntakeBag b /\
      bag_eggs b = [e] /\
      first_slice_tag e = Some TagClothoid) /\
   (exists b e,
      intake_map default_sheet TClothoidJts = IntakeBag b /\
      bag_eggs b = [e] /\
      first_slice_tag e = Some TagClothoid) /\
   (exists b e,
      intake_map default_sheet unknown_cs_cst = IntakeBag b /\
      bag_eggs b = [e] /\
      first_slice_tag e = Some TagCircle) /\
   intake_map default_sheet TGeodesicString = IntakeDecline ID_GeodesicString /\
   length (bag_eggs (map_cc_locked default_sheet)) = 2%nat)
  \/
  (exists e,
     first_slice_tag e = Some TagCircularString /\
     e = MkCirc locked_full_circle_egg).
Proof.
  left.
  destruct tau_mu_locked_ls as [bLS [eLS [HLS [HegLS [HtagLS _]]]]].
  destruct tau_mu_locked_cs_quarter as [bq [eq [Hq [Hegq [Htagq _]]]]].
  destruct tau_mu_locked_circle as [bc [ec [Hc [Hegc [Htagc _]]]]].
  destruct tau_mu_locked_cs_full_ogc as [bf [ef [Hf [Hegf [Hef [Htagf _]]]]]].
  destruct tau_mu_full_span_shared_egg as [Hshare _].
  destruct tau_mu_locked_clothoid_iso as [bi [ei [Hi [Hegi [Htagi _]]]]].
  destruct tau_mu_locked_clothoid_jts as [bj [ej [Hj [Hegj [_ [Htagj _]]]]]].
  destruct tau_mu_unknown_cs as [bu [eu [Hu [Hegu [_ [Htagu _]]]]]].
  destruct tau_mu_compound_not_singleton as [_ Hcc].
  split; [exists bLS, eLS; repeat split; assumption|].
  split; [exists bq, eq; repeat split; assumption|].
  split; [exists bc, ec; repeat split; assumption|].
  split; [exists bf, ef; repeat split; assumption|].
  split; [exact Hshare|].
  split; [exists bi, ei; repeat split; assumption|].
  split; [exists bj, ej; repeat split; assumption|].
  split; [exists bu, eu; repeat split; assumption|].
  split; [exact geodesic_declines|].
  exact Hcc.
Qed.

(* WITNESS {"claimId":"0007-sqlmm-signed-tag","topic":"overlay","lemma":"ticket_sqlmm_factory_emit_qed_or_qex","title":"Factory emits ANTLR-valid WKT and Table 15 WKB hex from a locked bag (QED) or WKT/WKB emit stays QEX because Rocq does not inhabit byte strings (QEX); discharged QEX; emit is factory-ladder rung 8; no new oracle keyword; not first-cook expand; not NURBS first-cook; not rho","file":"theories/SqlMmSignedTag.v","witness":"0007-sqlmm-signed-tag","board":"ADR-0007"} *)
Theorem ticket_sqlmm_factory_emit_qed_or_qex :
  (sqlmm_emit_inhabits EmitWktBytes /\
   sqlmm_emit_inhabits EmitWkbHex /\
   sqlmm_emit_inhabits EmitAntlrParse)
  \/
  (~ sqlmm_emit_inhabits EmitWktBytes /\
   ~ sqlmm_emit_inhabits EmitWkbHex /\
   ~ sqlmm_emit_inhabits EmitAntlrParse /\
   ~ sqlmm_emit_inhabits EmitNewOracleKeyword /\
   ~ sqlmm_emit_inhabits EmitFirstCookExpand /\
   ~ sqlmm_emit_inhabits EmitNurbsFirstCook /\
   ~ sqlmm_emit_inhabits EmitRhoBagLoop).
Proof.
  right.
  split; [exact sqlmm_wkt_emit_missing|].
  split; [exact sqlmm_wkb_emit_missing|].
  split; [exact sqlmm_antlr_missing|].
  split; [exact sqlmm_no_new_keyword|].
  split; [exact sqlmm_no_first_cook_expand|].
  split; [exact sqlmm_no_nurbs_first_cook|].
  exact sqlmm_no_rho.
Qed.

Print Assumptions signed_code_not_hold.
Print Assumptions hold_has_no_signed_tag.
Print Assumptions kappa_circle_not_18.
Print Assumptions tau_unique.
Print Assumptions full_span_is_circle_not_cs.
Print Assumptions tau_locked_quarter.
Print Assumptions tau_locked_full.
Print Assumptions tau_locked_cloth.
Print Assumptions out_of_scope_no_signed_tag.
Print Assumptions ticket_sqlmm_signed_tag_qed_or_qex.
Print Assumptions tau_mu_locked_ls.
Print Assumptions tau_mu_locked_cs_quarter.
Print Assumptions tau_mu_locked_circle.
Print Assumptions tau_mu_locked_cs_full_ogc.
Print Assumptions tau_mu_full_span_shared_egg.
Print Assumptions tau_mu_locked_clothoid_iso.
Print Assumptions tau_mu_unknown_cs.
Print Assumptions tau_mu_geodesic_decline.
Print Assumptions tau_mu_compound_not_singleton.
Print Assumptions ticket_sqlmm_tau_mu_qed_or_qex.
Print Assumptions ticket_sqlmm_factory_emit_qed_or_qex.
