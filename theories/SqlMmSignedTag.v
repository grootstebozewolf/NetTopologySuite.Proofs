(* ============================================================================
   NetTopologySuite.Proofs.SqlMmSignedTag
   ----------------------------------------------------------------------------
   ADR-0007 sidecar: SQL/MM Part 3 signed tag (claimId 0007-sqlmm-signed-tag).

   §5.1.67 names + §5.1.68 Table 15 codes. Signed I/O is {8..12}
   (plus boring SFA 1–7). HOLD is {13..17, 18..21}. CIRCLE is
   full-span MkCirc, not WKB 18. CLOTHOID is one egg for both
   surface forms, not WKB 22.

   Host eggs we already inhabit map onto signed tags:
     MkChord      → LINESTRING
     MkCirc       → CIRCULARSTRING; CIRCLE iff |Δθ|=2π
     MkClothoid   → CLOTHOID (ISO REFERENCELOCATION and JTS (k0,k1,L))
     Mode D joint → COMPOUNDCURVE only when eval A 1 = eval B 0

   Reuses (do not remint): cloth_joint (0007-clothoid-first-cook),
   circ_split_join (0007-gamma-mkcirc), first-slice eggs
   (0007-intake-walker). Sidecar only. SheetHenCook.v is not grown.
   No new ADR-0006 keyword.

   QED: ticket_sqlmm_signed_tag_qed_or_qex — first-slice host eggs
   inhabit a signed tag; HOLD codes do not.

   QEX: ticket_sqlmm_factory_emit_qed_or_qex — Rocq does not parse
   ANTLR and does not inhabit WKT/WKB byte strings. Emit is tools/
   + JTS #7 tests. Hex in a comment is still prose.

   Not this letter: first-cook expand, #729, ρ, Java twin,
   CircGamma remint, silent chord demote.

   ADR-0007 is Accepted (2026-09-07). This letter does not reopen
   Status. ADR-0006 Status stays Accepted.

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

From Stdlib Require Import Reals Lra Lia.
From NTS.Proofs Require Import Distance SheetHenCook ClothoidCookMkClothoid.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §5.1.67 names + Table 15 codes.                                            *)
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
| TagMultiSurface
| TagCircle
| TagClothoid
| TagTriangle
| TagPolyhedralSurface
| TagTIN
| TagEllipse
| TagBezier
| TagNurbs
| TagGeodesicString
| TagSpiralCurve
| TagCompoundSurface
| TagBrepSolid.

Definition sqlmm_wkb_code (t : SqlMmTag) : option nat :=
  match t with
  | TagPoint => Some 1%nat
  | TagLineString => Some 2%nat
  | TagPolygon => Some 3%nat
  | TagMultiPoint => Some 4%nat
  | TagMultiLineString => Some 5%nat
  | TagMultiPolygon => Some 6%nat
  | TagGeomCollection => Some 7%nat
  | TagCircularString => Some 8%nat
  | TagCompoundCurve => Some 9%nat
  | TagCurvePolygon => Some 10%nat
  | TagMultiCurve => Some 11%nat
  | TagMultiSurface => Some 12%nat
  | TagCircle => None
  | TagClothoid => None
  | TagTriangle => Some 17%nat
  | TagPolyhedralSurface => Some 15%nat
  | TagTIN => Some 16%nat
  | TagEllipse => Some 18%nat
  | TagBezier => Some 19%nat
  | TagNurbs => Some 21%nat
  | TagGeodesicString => None
  | TagSpiralCurve => None
  | TagCompoundSurface => None
  | TagBrepSolid => None
  end.

Definition sqlmm_signed_code (n : nat) : Prop :=
  (1 <= n)%nat /\ (n <= 12)%nat.

Definition sqlmm_hold_code (n : nat) : Prop :=
  ((13 <= n)%nat /\ (n <= 17)%nat) \/
  ((18 <= n)%nat /\ (n <= 21)%nat).

Definition sqlmm_signed_tag (t : SqlMmTag) : bool :=
  match t with
  | TagPoint | TagLineString | TagPolygon
  | TagMultiPoint | TagMultiLineString | TagMultiPolygon
  | TagGeomCollection
  | TagCircularString | TagCompoundCurve | TagCurvePolygon
  | TagMultiCurve | TagMultiSurface
  | TagCircle | TagClothoid => true
  | TagTriangle | TagPolyhedralSurface | TagTIN
  | TagEllipse | TagBezier | TagNurbs
  | TagGeodesicString | TagSpiralCurve
  | TagCompoundSurface | TagBrepSolid => false
  end.

Definition tag_of_wkb (n : nat) : option SqlMmTag :=
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
  | 13 => Some TagGeodesicString
  | 14 => Some TagSpiralCurve
  | 15 => Some TagPolyhedralSurface
  | 16 => Some TagTIN
  | 17 => Some TagTriangle
  | 18 => Some TagEllipse
  | 19 => Some TagBezier
  | 20 => Some TagCompoundSurface
  | 21 => Some TagNurbs
  | _ => None
  end.

Lemma circle_not_wkb_18 :
  sqlmm_wkb_code TagCircle <> Some 18%nat.
Proof.
  discriminate.
Qed.

Lemma clothoid_not_wkb_22 :
  sqlmm_wkb_code TagClothoid <> Some 22%nat.
Proof.
  discriminate.
Qed.

Lemma signed_code_not_hold :
  forall n, sqlmm_signed_code n -> sqlmm_hold_code n -> False.
Proof.
  intros n [Hlo Hhi] [[A B]|[C D]].
  - lia.
  - lia.
Qed.

Lemma hold_wkb_tag_not_signed :
  forall n t,
    sqlmm_hold_code n ->
    tag_of_wkb n = Some t ->
    sqlmm_signed_tag t = false.
Proof.
  intros n t Hhold Ht.
  assert ((n = 13 \/ n = 14 \/ n = 15 \/ n = 16 \/ n = 17 \/
           n = 18 \/ n = 19 \/ n = 20 \/ n = 21)%nat) as Hn.
  { unfold sqlmm_hold_code in Hhold. lia. }
  destruct Hn as [E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]; subst n;
    inversion Ht; subst t; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Host egg → signed tag. CIRCLE is full-span MkCirc, not code 18.            *)
(* -------------------------------------------------------------------------- *)

Definition circ_full_span (c : CircularEgg) : Prop :=
  circ_sweep c = 2 * PI \/ circ_sweep c = - (2 * PI).

Inductive ClothoidSurface : Type :=
| ClothSurfIso
| ClothSurfJts.

Definition clothoid_surface_tag (_ : ClothoidSurface) : SqlMmTag :=
  TagClothoid.

Lemma both_clothoid_forms_one_tag :
  clothoid_surface_tag ClothSurfIso = clothoid_surface_tag ClothSurfJts.
Proof.
  reflexivity.
Qed.

Inductive HostEggInhabits : Egg -> SqlMmTag -> Prop :=
| inhabit_chord : forall c, HostEggInhabits (MkChord c) TagLineString
| inhabit_circ : forall c, HostEggInhabits (MkCirc c) TagCircularString
| inhabit_circle : forall c,
    circ_full_span c -> HostEggInhabits (MkCirc c) TagCircle
| inhabit_cloth : forall c, HostEggInhabits (MkClothoid c) TagClothoid.

Lemma host_egg_inhabits_signed :
  forall e t, HostEggInhabits e t -> sqlmm_signed_tag t = true.
Proof.
  intros e t H. inversion H; reflexivity.
Qed.

Lemma hold_tag_not_host :
  forall e t, sqlmm_signed_tag t = false -> ~ HostEggInhabits e t.
Proof.
  intros e t Hs H. inversion H; subst; discriminate.
Qed.

Lemma out_of_scope_no_signed_tag :
  forall c t, ~ HostEggInhabits (MkOutOfScope c) t.
Proof.
  intros c t H. inversion H.
Qed.

(* -------------------------------------------------------------------------- *)
(* Mode D joint → COMPOUNDCURVE only when eval A 1 = eval B 0.                *)
(* Reuses cloth_joint / circ_split_join. Not interior I_ok Hit.               *)
(* -------------------------------------------------------------------------- *)

Definition egg_end (e : Egg) : option Point :=
  match e with
  | MkChord c => Some (chord_eval c 1)
  | MkCirc c => Some (circ_eval c 1)
  | MkClothoid c => Some (cloth_eval c 1)
  | MkOutOfScope _ => None
  end.

Definition egg_start (e : Egg) : option Point :=
  match e with
  | MkChord c => Some (chord_eval c 0)
  | MkCirc c => Some (circ_eval c 0)
  | MkClothoid c => Some (cloth_eval c 0)
  | MkOutOfScope _ => None
  end.

Definition mode_d_joint (A B : Egg) : Prop :=
  match egg_end A, egg_start B with
  | Some p, Some q => p = q
  | _, _ => False
  end.

Definition cs_joint_circ (A B : CircularEgg) : Prop :=
  circ_eval A 1 = circ_eval B 0.

Definition CompoundInhabits (A B : Egg) (t : SqlMmTag) : Prop :=
  t = TagCompoundCurve /\ mode_d_joint A B.

Lemma cloth_joint_is_mode_d :
  forall A B,
    cloth_joint A B <-> mode_d_joint (MkClothoid A) (MkClothoid B).
Proof.
  intros A B.
  unfold cloth_joint, mode_d_joint, egg_end, egg_start.
  split; intros H; exact H.
Qed.

Lemma cs_joint_circ_is_mode_d :
  forall A B,
    cs_joint_circ A B <-> mode_d_joint (MkCirc A) (MkCirc B).
Proof.
  intros A B.
  unfold cs_joint_circ, mode_d_joint, egg_end, egg_start.
  split; intros H; exact H.
Qed.

Lemma cloth_joint_inhabits_compound :
  forall A B,
    cloth_joint A B ->
    CompoundInhabits (MkClothoid A) (MkClothoid B) TagCompoundCurve.
Proof.
  intros A B H.
  split; [reflexivity|].
  apply cloth_joint_is_mode_d.
  exact H.
Qed.

Lemma cs_joint_circ_inhabits_compound :
  forall A B,
    cs_joint_circ A B ->
    CompoundInhabits (MkCirc A) (MkCirc B) TagCompoundCurve.
Proof.
  intros A B H.
  split; [reflexivity|].
  apply cs_joint_circ_is_mode_d.
  exact H.
Qed.

Lemma circ_split_cs_joint_circ :
  forall c t,
    cs_joint_circ (fst (circ_split c t)) (snd (circ_split c t)).
Proof.
  intros c t.
  unfold cs_joint_circ.
  destruct (circ_split_join c t) as [Hl Hr].
  rewrite Hl, Hr.
  reflexivity.
Qed.

Lemma no_joint_no_compound :
  forall A B, ~ mode_d_joint A B ->
    ~ CompoundInhabits A B TagCompoundCurve.
Proof.
  intros A B Hnj [Heq Hj].
  exact (Hnj Hj).
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked first-slice eggs.                                                   *)
(* -------------------------------------------------------------------------- *)

Definition locked_sqlmm_chord : ChordEgg :=
  mkChordEgg (mkPoint 0 0) (mkPoint 1 0).

Definition locked_sqlmm_quarter : CircularEgg :=
  mkCircularEgg (mkPoint 0 0) 5 0 (PI / 2).

Definition locked_sqlmm_full : CircularEgg :=
  mkCircularEgg (mkPoint 0 0) 5 0 (2 * PI).

Definition locked_sqlmm_ls_to_circ : ChordEgg :=
  mkChordEgg (mkPoint 0 0) (circ_eval locked_sqlmm_quarter 0).

Lemma locked_chord_inhabits :
  HostEggInhabits (MkChord locked_sqlmm_chord) TagLineString.
Proof.
  apply inhabit_chord.
Qed.

Lemma locked_quarter_inhabits_cs :
  HostEggInhabits (MkCirc locked_sqlmm_quarter) TagCircularString.
Proof.
  apply inhabit_circ.
Qed.

Lemma locked_full_span :
  circ_full_span locked_sqlmm_full.
Proof.
  unfold circ_full_span, locked_sqlmm_full.
  left. reflexivity.
Qed.

Lemma locked_full_inhabits_cs :
  HostEggInhabits (MkCirc locked_sqlmm_full) TagCircularString.
Proof.
  apply inhabit_circ.
Qed.

Lemma locked_full_inhabits_circle :
  HostEggInhabits (MkCirc locked_sqlmm_full) TagCircle.
Proof.
  apply inhabit_circle.
  exact locked_full_span.
Qed.

Lemma pi_half_lt_pi : PI / 2 < PI.
Proof.
  pose proof PI_RGT_0 as HP.
  replace (PI / 2) with ((1 / 2) * PI) by field.
  rewrite <- (Rmult_1_l PI) at 2.
  apply Rmult_lt_compat_r; [exact HP|].
  lra.
Qed.

Lemma pi_lt_two_pi : PI < 2 * PI.
Proof.
  pose proof PI_RGT_0 as HP.
  rewrite <- (Rmult_1_l PI) at 1.
  apply Rmult_lt_compat_r; [exact HP|].
  lra.
Qed.

Lemma pi_half_lt_two_pi : PI / 2 < 2 * PI.
Proof.
  apply Rlt_trans with PI.
  - exact pi_half_lt_pi.
  - exact pi_lt_two_pi.
Qed.

Lemma pi_half_neq_two_pi : PI / 2 <> 2 * PI.
Proof.
  apply Rlt_not_eq.
  exact pi_half_lt_two_pi.
Qed.

Lemma neg_two_pi_lt_0 : - (2 * PI) < 0.
Proof.
  pose proof PI_RGT_0 as HP.
  rewrite <- Ropp_0.
  apply Ropp_lt_contravar.
  apply Rmult_lt_0_compat; [lra|exact HP].
Qed.

Lemma zero_lt_pi_half : 0 < PI / 2.
Proof.
  pose proof PI_RGT_0 as HP.
  replace (PI / 2) with ((1 / 2) * PI) by field.
  apply Rmult_lt_0_compat; [lra|exact HP].
Qed.

Lemma pi_half_neq_neg_two_pi : PI / 2 <> - (2 * PI).
Proof.
  intro H.
  apply (Rlt_not_eq (- (2 * PI)) (PI / 2)).
  - apply Rlt_trans with 0.
    + exact neg_two_pi_lt_0.
    + exact zero_lt_pi_half.
  - rewrite H. reflexivity.
Qed.

Lemma locked_quarter_not_full :
  ~ circ_full_span locked_sqlmm_quarter.
Proof.
  unfold circ_full_span, locked_sqlmm_quarter.
  intros [H|H].
  - exact (pi_half_neq_two_pi H).
  - exact (pi_half_neq_neg_two_pi H).
Qed.

Lemma locked_quarter_not_circle :
  ~ HostEggInhabits (MkCirc locked_sqlmm_quarter) TagCircle.
Proof.
  intros H. inversion H; subst.
  apply locked_quarter_not_full.
  assumption.
Qed.

Lemma locked_cloth_inhabits :
  HostEggInhabits (MkClothoid locked_cloth_A) TagClothoid.
Proof.
  apply inhabit_cloth.
Qed.

Lemma locked_cloth_split_compound :
  CompoundInhabits
    (MkClothoid locked_cloth_host_1)
    (MkClothoid locked_cloth_host_2)
    TagCompoundCurve.
Proof.
  apply cloth_joint_inhabits_compound.
  exact locked_cloth_host_joint.
Qed.

Lemma locked_cloth_AB_no_compound :
  ~ CompoundInhabits
      (MkClothoid locked_cloth_A) (MkClothoid locked_cloth_B)
      TagCompoundCurve.
Proof.
  apply no_joint_no_compound.
  intros H.
  apply locked_cloth_AB_not_joint.
  apply cloth_joint_is_mode_d.
  exact H.
Qed.

Lemma locked_circ_split_compound :
  CompoundInhabits
    (MkCirc (fst (circ_split locked_sqlmm_quarter (1 / 2))))
    (MkCirc (snd (circ_split locked_sqlmm_quarter (1 / 2))))
    TagCompoundCurve.
Proof.
  apply cs_joint_circ_inhabits_compound.
  apply circ_split_cs_joint_circ.
Qed.

Lemma locked_ls_cs_mode_d :
  mode_d_joint (MkChord locked_sqlmm_ls_to_circ) (MkCirc locked_sqlmm_quarter).
Proof.
  unfold mode_d_joint, egg_end, egg_start, locked_sqlmm_ls_to_circ.
  rewrite chord_eval_at_1.
  reflexivity.
Qed.

Lemma locked_ls_cs_compound :
  CompoundInhabits
    (MkChord locked_sqlmm_ls_to_circ) (MkCirc locked_sqlmm_quarter)
    TagCompoundCurve.
Proof.
  split; [reflexivity|].
  exact locked_ls_cs_mode_d.
Qed.

Lemma compound_inhabits_signed :
  forall A B,
    CompoundInhabits A B TagCompoundCurve ->
    sqlmm_signed_tag TagCompoundCurve = true.
Proof.
  intros A B _. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Named inhabitant package.                                                  *)
(* -------------------------------------------------------------------------- *)

Lemma sqlmm_signed_tag_inhabits :
  HostEggInhabits (MkChord locked_sqlmm_chord) TagLineString /\
  HostEggInhabits (MkCirc locked_sqlmm_quarter) TagCircularString /\
  HostEggInhabits (MkCirc locked_sqlmm_full) TagCircle /\
  HostEggInhabits (MkClothoid locked_cloth_A) TagClothoid /\
  clothoid_surface_tag ClothSurfIso = TagClothoid /\
  clothoid_surface_tag ClothSurfJts = TagClothoid /\
  CompoundInhabits
    (MkClothoid locked_cloth_host_1)
    (MkClothoid locked_cloth_host_2)
    TagCompoundCurve /\
  CompoundInhabits
    (MkCirc (fst (circ_split locked_sqlmm_quarter (1 / 2))))
    (MkCirc (snd (circ_split locked_sqlmm_quarter (1 / 2))))
    TagCompoundCurve /\
  sqlmm_signed_tag TagLineString = true /\
  sqlmm_signed_tag TagCircularString = true /\
  sqlmm_signed_tag TagCircle = true /\
  sqlmm_signed_tag TagClothoid = true /\
  sqlmm_signed_tag TagCompoundCurve = true /\
  sqlmm_wkb_code TagCircularString = Some 8%nat /\
  sqlmm_wkb_code TagCompoundCurve = Some 9%nat /\
  sqlmm_wkb_code TagCircle <> Some 18%nat /\
  sqlmm_wkb_code TagClothoid <> Some 22%nat /\
  ~ HostEggInhabits (MkCirc locked_sqlmm_quarter) TagCircle /\
  ~ CompoundInhabits
      (MkClothoid locked_cloth_A) (MkClothoid locked_cloth_B)
      TagCompoundCurve /\
  (forall e t, HostEggInhabits e t -> sqlmm_signed_tag t = true) /\
  (forall n t,
     sqlmm_hold_code n ->
     tag_of_wkb n = Some t ->
     sqlmm_signed_tag t = false).
Proof.
  split; [exact locked_chord_inhabits|].
  split; [exact locked_quarter_inhabits_cs|].
  split; [exact locked_full_inhabits_circle|].
  split; [exact locked_cloth_inhabits|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact locked_cloth_split_compound|].
  split; [exact locked_circ_split_compound|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact circle_not_wkb_18|].
  split; [exact clothoid_not_wkb_22|].
  split; [exact locked_quarter_not_circle|].
  split; [exact locked_cloth_AB_no_compound|].
  split; [exact host_egg_inhabits_signed|].
  exact hold_wkb_tag_not_signed.
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

(* WITNESS {"claimId":"0007-sqlmm-signed-tag","topic":"overlay","lemma":"ticket_sqlmm_signed_tag_qed_or_qex","title":"First-slice host eggs inhabit a signed SQL/MM tag and HOLD codes 13-17/18-21 do not (QED) or a HOLD code inhabits a signed host tag (QEX); discharged QED; CIRCLE is full-span MkCirc not WKB 18; CLOTHOID is one egg for both surface forms; COMPOUNDCURVE only when eval A 1 = eval B 0; reuses cloth_joint / circ_split_join; not a factory emit","file":"theories/SqlMmSignedTag.v","witness":"0007-sqlmm-signed-tag","board":"ADR-0007"} *)
Theorem ticket_sqlmm_signed_tag_qed_or_qex :
  (HostEggInhabits (MkChord locked_sqlmm_chord) TagLineString /\
   HostEggInhabits (MkCirc locked_sqlmm_quarter) TagCircularString /\
   HostEggInhabits (MkCirc locked_sqlmm_full) TagCircle /\
   HostEggInhabits (MkClothoid locked_cloth_A) TagClothoid /\
   clothoid_surface_tag ClothSurfIso = clothoid_surface_tag ClothSurfJts /\
   CompoundInhabits
     (MkClothoid locked_cloth_host_1)
     (MkClothoid locked_cloth_host_2)
     TagCompoundCurve /\
   CompoundInhabits
     (MkChord locked_sqlmm_ls_to_circ) (MkCirc locked_sqlmm_quarter)
     TagCompoundCurve /\
   sqlmm_wkb_code TagCircularString = Some 8%nat /\
   sqlmm_wkb_code TagCompoundCurve = Some 9%nat /\
   sqlmm_wkb_code TagCircle <> Some 18%nat /\
   ~ HostEggInhabits (MkCirc locked_sqlmm_quarter) TagCircle /\
   ~ CompoundInhabits
       (MkClothoid locked_cloth_A) (MkClothoid locked_cloth_B)
       TagCompoundCurve /\
   (forall e t, HostEggInhabits e t -> sqlmm_signed_tag t = true) /\
   (forall n t,
      sqlmm_hold_code n ->
      tag_of_wkb n = Some t ->
      sqlmm_signed_tag t = false))
  \/
  (exists e, HostEggInhabits e TagEllipse).
Proof.
  left.
  destruct sqlmm_signed_tag_inhabits
    as [Hc [Hq [Hf [Hcl [Hiso [Hjts [Hcc [Hcs [ _
        [_ [_ [_ [_ [H8 [H9 [H18 [H22 [Hnq [Hnab [Hsgn Hhold]]]]]]]]]]]]]]]]]]]].
  split; [exact Hc|].
  split; [exact Hq|].
  split; [exact Hf|].
  split; [exact Hcl|].
  split; [rewrite Hiso, Hjts; reflexivity|].
  split; [exact Hcc|].
  split; [exact locked_ls_cs_compound|].
  split; [exact H8|].
  split; [exact H9|].
  split; [exact H18|].
  split; [exact Hnq|].
  split; [exact Hnab|].
  split; [exact Hsgn|].
  exact Hhold.
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

Print Assumptions circle_not_wkb_18.
Print Assumptions clothoid_not_wkb_22.
Print Assumptions signed_code_not_hold.
Print Assumptions hold_wkb_tag_not_signed.
Print Assumptions host_egg_inhabits_signed.
Print Assumptions hold_tag_not_host.
Print Assumptions cloth_joint_is_mode_d.
Print Assumptions cs_joint_circ_is_mode_d.
Print Assumptions cloth_joint_inhabits_compound.
Print Assumptions circ_split_cs_joint_circ.
Print Assumptions pi_half_neq_two_pi.
Print Assumptions pi_half_neq_neg_two_pi.
Print Assumptions locked_full_inhabits_circle.
Print Assumptions locked_quarter_not_full.
Print Assumptions locked_quarter_not_circle.
Print Assumptions locked_cloth_split_compound.
Print Assumptions locked_cloth_AB_no_compound.
Print Assumptions locked_circ_split_compound.
Print Assumptions locked_ls_cs_compound.
Print Assumptions sqlmm_signed_tag_inhabits.
Print Assumptions ticket_sqlmm_signed_tag_qed_or_qex.
Print Assumptions ticket_sqlmm_factory_emit_qed_or_qex.
