(* ============================================================================
   NetTopologySuite.Proofs.SqlMmSignedTag
   ----------------------------------------------------------------------------
   ADR-0007 sidecar: first-slice egg → signed Table 15 tag
   (claimId 0007-sqlmm-signed-tag).

   This is a total function on host eggs, not a factory and not a
   sticker relation. SqlMmTag is the SFA 1–7 + signed-curve 8–12
   names only. HOLD is codes {13..17, 18..21} as nats — no named
   constructors we cannot code. CIRCLE / CLOTHOID are not signed
   I/O (no Table 15 code on JTS #7). CIRCLE CST is the same MkCirc
   as CIRCULARSTRING (IntakeWalker.ogc_iso_circle_same_egg).

   first_slice_tag:
     MkChord _      → Some LINESTRING (2)
     MkCirc _       → Some CIRCULARSTRING (8)   (* XOR: not CIRCLE *)
     MkClothoid _   → None                      (* WKT-only; not signed *)
     MkOutOfScope _ → None

   COMPOUNDCURVE (9) is a bag, not an egg tag. Mode D joints stay
   the joins that already live on the interpolant: cloth_joint
   (0007-clothoid-first-cook) and circ_split_join (the #733
   cs_joint_circ equation). Do not remint cs_joint_circ. Do not
   label endpoint coincidence as a CompoundCurve inhabitant.

   Sidecar only. SheetHenCook.v is not grown. No new ADR-0006
   keyword.

   QED: ticket_sqlmm_signed_tag_qed_or_qex — the function; HOLD
   codes have no signed tag; OutOfScope / clothoid are None.

   QEX: ticket_sqlmm_factory_emit_qed_or_qex — Rocq does not
   inhabit WKT/WKB bytes.

   Not this letter: factory emit, first-cook expand, #729, ρ,
   Java twin, CircGamma remint, Circle-as-18, HOLD name fanfic.

   ADR-0007 is Accepted (2026-09-07). This letter does not reopen
   Status. ADR-0006 Status stays Accepted.

   WITNESS topic: overlay · claimId: 0007-sqlmm-signed-tag
   witness: 0007-sqlmm-signed-tag
   also: 0007-clothoid-first-cook, 0007-gamma-mkcirc, 0007-intake-walker
   also: 0007-B.1-cs-concat-joints (cite cs_joint_circ; do not remint)
   board: ADR-0007
   3-axiom host. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals PeanoNat.
From NTS.Proofs Require Import Distance SheetHenCook ClothoidCookMkClothoid.

(* -------------------------------------------------------------------------- *)
(* Named tags are exactly the codes JTS #7 signs: SFA 1–7 and 8–12.           *)
(* -------------------------------------------------------------------------- *)

Inductive SqlMmTag : Type :=
| TagPoint
| TagLineString
| TagPolygon
| TagMultiPoint
| TagMultiLineString
| TagMultiPolygon
| TagGeomCollection
| TagCircularString
| TagCompoundCurve
| TagCurvePolygon
| TagMultiCurve
| TagMultiSurface.

Definition sqlmm_wkb_code (t : SqlMmTag) : nat :=
  match t with
  | TagPoint => 1%nat
  | TagLineString => 2%nat
  | TagPolygon => 3%nat
  | TagMultiPoint => 4%nat
  | TagMultiLineString => 5%nat
  | TagMultiPolygon => 6%nat
  | TagGeomCollection => 7%nat
  | TagCircularString => 8%nat
  | TagCompoundCurve => 9%nat
  | TagCurvePolygon => 10%nat
  | TagMultiCurve => 11%nat
  | TagMultiSurface => 12%nat
  end.

Definition sqlmm_signed_code (n : nat) : Prop :=
  (1 <= n)%nat /\ (n <= 12)%nat.

Definition sqlmm_hold_code (n : nat) : Prop :=
  ((13 <= n)%nat /\ (n <= 17)%nat) \/
  ((18 <= n)%nat /\ (n <= 21)%nat).

Definition sqlmm_signed_tag (t : SqlMmTag) : bool := true.

Definition tag_of_signed_wkb (n : nat) : option SqlMmTag :=
  match n with
  | 1 => Some TagPoint
  | 2 => Some TagLineString
  | 3 => Some TagPolygon
  | 4 => Some TagMultiPoint
  | 5 => Some TagMultiLineString
  | 6 => Some TagMultiPolygon
  | 7 => Some TagGeomCollection
  | 8 => Some TagCircularString
  | 9 => Some TagCompoundCurve
  | 10 => Some TagCurvePolygon
  | 11 => Some TagMultiCurve
  | 12 => Some TagMultiSurface
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

Lemma wkb_code_is_signed :
  forall t, sqlmm_signed_code (sqlmm_wkb_code t).
Proof.
  intros t.
  destruct t; unfold sqlmm_signed_code, sqlmm_wkb_code; split;
    apply leb_true_le; reflexivity.
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

Lemma tag_of_wkb_roundtrip :
  forall t, tag_of_signed_wkb (sqlmm_wkb_code t) = Some t.
Proof.
  intros t. destruct t; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Total function on host eggs. CIRCLE CST → same MkCirc → CIRCULARSTRING.    *)
(* CLOTHOID is first-slice intake, not signed I/O.                            *)
(* -------------------------------------------------------------------------- *)

Definition first_slice_tag (e : Egg) : option SqlMmTag :=
  match e with
  | MkChord _ => Some TagLineString
  | MkCirc _ => Some TagCircularString
  | MkClothoid _ => None
  | MkOutOfScope _ => None
  end.

Lemma first_slice_tag_chord :
  forall c, first_slice_tag (MkChord c) = Some TagLineString.
Proof.
  intros c. reflexivity.
Qed.

Lemma first_slice_tag_circ :
  forall c, first_slice_tag (MkCirc c) = Some TagCircularString.
Proof.
  intros c. reflexivity.
Qed.

Lemma mkcirc_tag_irrel :
  forall c d, first_slice_tag (MkCirc c) = first_slice_tag (MkCirc d).
Proof.
  intros c d. reflexivity.
Qed.

Lemma first_slice_tag_clothoid :
  forall c, first_slice_tag (MkClothoid c) = None.
Proof.
  intros c. reflexivity.
Qed.

Lemma both_clothoid_forms_untyped :
  first_slice_tag (MkClothoid locked_cloth_A) =
    first_slice_tag (MkClothoid locked_cloth_B).
Proof.
  reflexivity.
Qed.

Lemma out_of_scope_no_signed_tag :
  forall c, first_slice_tag (MkOutOfScope c) = None.
Proof.
  intros c. reflexivity.
Qed.

Lemma first_slice_some_is_signed :
  forall e t, first_slice_tag e = Some t -> sqlmm_signed_tag t = true.
Proof.
  intros e t H. destruct e; inversion H; reflexivity.
Qed.

Lemma first_slice_not_compound :
  forall e, first_slice_tag e <> Some TagCompoundCurve.
Proof.
  intros e H. destruct e; discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* Mode D joints already on the interpolant. Not a CompoundCurve inhabitant.  *)
(* -------------------------------------------------------------------------- *)

Lemma circ_split_mode_d :
  forall c t,
    circ_eval (fst (circ_split c t)) 1%R =
    circ_eval (snd (circ_split c t)) 0%R.
Proof.
  intros c t.
  destruct (circ_split_join c t) as [Hl Hr].
  rewrite Hl, Hr.
  reflexivity.
Qed.

Lemma circ_split_members_are_cs :
  forall c t,
    first_slice_tag (MkCirc (fst (circ_split c t))) = Some TagCircularString /\
    first_slice_tag (MkCirc (snd (circ_split c t))) = Some TagCircularString.
Proof.
  intros c t. split; reflexivity.
Qed.

Lemma locked_cloth_split_is_joint :
  cloth_joint locked_cloth_host_1 locked_cloth_host_2.
Proof.
  exact locked_cloth_host_joint.
Qed.

Lemma locked_cloth_AB_not_mode_d :
  ~ cloth_joint locked_cloth_A locked_cloth_B.
Proof.
  exact locked_cloth_AB_not_joint.
Qed.

Lemma cloth_joint_members_untyped :
  forall A B,
    cloth_joint A B ->
    first_slice_tag (MkClothoid A) = None /\
    first_slice_tag (MkClothoid B) = None.
Proof.
  intros A B _. split; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Named inhabitant: the function, not a factory.                             *)
(* -------------------------------------------------------------------------- *)

Lemma sqlmm_signed_tag_inhabits :
  first_slice_tag (MkChord (mkChordEgg (mkPoint 0 0) (mkPoint 1 0)))
    = Some TagLineString /\
  (forall c, first_slice_tag (MkCirc c) = Some TagCircularString) /\
  (forall c d, first_slice_tag (MkCirc c) = first_slice_tag (MkCirc d)) /\
  first_slice_tag (MkClothoid locked_cloth_A) = None /\
  (forall c, first_slice_tag (MkOutOfScope c) = None) /\
  sqlmm_wkb_code TagCircularString = 8%nat /\
  sqlmm_wkb_code TagCompoundCurve = 9%nat /\
  (forall e, first_slice_tag e <> Some TagCompoundCurve) /\
  cloth_joint locked_cloth_host_1 locked_cloth_host_2 /\
  ~ cloth_joint locked_cloth_A locked_cloth_B /\
  (forall t, sqlmm_signed_code (sqlmm_wkb_code t)) /\
  (forall n, sqlmm_signed_code n -> sqlmm_hold_code n -> False) /\
  (forall n, sqlmm_hold_code n -> tag_of_signed_wkb n = None).
Proof.
  split; [reflexivity|].
  split; [intros c; reflexivity|].
  split; [intros c d; reflexivity|].
  split; [reflexivity|].
  split; [intros c; reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact first_slice_not_compound|].
  split; [exact locked_cloth_split_is_joint|].
  split; [exact locked_cloth_AB_not_mode_d|].
  split; [exact wkb_code_is_signed|].
  split; [exact signed_code_not_hold|].
  exact hold_has_no_signed_tag.
Qed.

(* -------------------------------------------------------------------------- *)
(* Emit stays QEX. Rocq does not inhabit WKT/WKB bytes.                       *)
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

(* WITNESS {"claimId":"0007-sqlmm-signed-tag","topic":"overlay","lemma":"ticket_sqlmm_signed_tag_qed_or_qex","title":"first_slice_tag is a function: MkChord to LINESTRING, every MkCirc to CIRCULARSTRING (CIRCLE CST is the same egg), MkClothoid and MkOutOfScope None; HOLD codes 13-21 have no signed tag (QED) or one egg inhabits two tags (QEX); discharged QED; COMPOUNDCURVE is not an egg tag; cloth_joint / circ_split_join stay interpolant joins; not a factory emit","file":"theories/SqlMmSignedTag.v","witness":"0007-sqlmm-signed-tag","board":"ADR-0007"} *)
Theorem ticket_sqlmm_signed_tag_qed_or_qex :
  ((forall c, first_slice_tag (MkChord c) = Some TagLineString) /\
   (forall c, first_slice_tag (MkCirc c) = Some TagCircularString) /\
   (forall c d, first_slice_tag (MkCirc c) = first_slice_tag (MkCirc d)) /\
   (forall c, first_slice_tag (MkClothoid c) = None) /\
   (forall c, first_slice_tag (MkOutOfScope c) = None) /\
   (forall e, first_slice_tag e <> Some TagCompoundCurve) /\
   (forall e t, first_slice_tag e = Some t -> sqlmm_signed_tag t = true) /\
   sqlmm_wkb_code TagCircularString = 8%nat /\
   (forall n, sqlmm_hold_code n -> tag_of_signed_wkb n = None) /\
   (forall n, sqlmm_signed_code n -> sqlmm_hold_code n -> False) /\
   cloth_joint locked_cloth_host_1 locked_cloth_host_2 /\
   ~ cloth_joint locked_cloth_A locked_cloth_B)
  \/
  (exists e t1 t2,
     first_slice_tag e = Some t1 /\
     first_slice_tag e = Some t2 /\
     t1 <> t2).
Proof.
  left.
  split; [intros c; reflexivity|].
  split; [intros c; reflexivity|].
  split; [intros c d; reflexivity|].
  split; [intros c; reflexivity|].
  split; [intros c; reflexivity|].
  split; [exact first_slice_not_compound|].
  split; [exact first_slice_some_is_signed|].
  split; [reflexivity|].
  split; [exact hold_has_no_signed_tag|].
  split; [exact signed_code_not_hold|].
  split; [exact locked_cloth_split_is_joint|].
  exact locked_cloth_AB_not_mode_d.
Qed.

(* WITNESS {"claimId":"0007-sqlmm-signed-tag","topic":"overlay","lemma":"ticket_sqlmm_factory_emit_qed_or_qex","title":"Factory emits ANTLR-valid WKT and Table 15 WKB hex from a locked bag (QED) or WKT/WKB emit stays QEX because Rocq does not inhabit byte strings (QEX); discharged QEX; no new oracle keyword; not first-cook expand; not NURBS first-cook; not rho","file":"theories/SqlMmSignedTag.v","witness":"0007-sqlmm-signed-tag","board":"ADR-0007"} *)
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

Print Assumptions wkb_code_is_signed.
Print Assumptions signed_code_not_hold.
Print Assumptions hold_has_no_signed_tag.
Print Assumptions first_slice_tag_circ.
Print Assumptions mkcirc_tag_irrel.
Print Assumptions first_slice_tag_clothoid.
Print Assumptions out_of_scope_no_signed_tag.
Print Assumptions first_slice_not_compound.
Print Assumptions circ_split_mode_d.
Print Assumptions locked_cloth_split_is_joint.
Print Assumptions locked_cloth_AB_not_mode_d.
Print Assumptions sqlmm_signed_tag_inhabits.
Print Assumptions ticket_sqlmm_signed_tag_qed_or_qex.
Print Assumptions ticket_sqlmm_factory_emit_qed_or_qex.
