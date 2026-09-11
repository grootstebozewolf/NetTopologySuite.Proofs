(* ============================================================================
   NetTopologySuite.Proofs.Flocq.IeeeRBridge
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: two-way IEEE binary64 ↔ ℝ bridge
   (claimId 0007-ieee-oracle-bridge).

   Product face: the Oracle (ADR-0006 Accepted line protocol) speaks
   IEEE binary64 on the wire; this module packages the coordinate
   realization that decodes those bits to ℝ and rounds ℝ back under
   a named finite / no-overflow / int-safe regime. Test surface for
   the three chord product faces — NodingNG (𝓘 + cook), OverlayNG
   (snap ≠ 𝓘), RelateNG (matrix/witness, 67-c parallel chords).

   Packages, does not remint:
     SheetHenCook.CoordRealization / binary64_same_sheet_as_R /
       coord_realization_preserves_sheet
     Validate_binary64_bridge.B2R_bp / map_B2R_bp / point_int_safe
     B64_bridge.b64_safe / b64_*_correct (finite + no-overflow)
     B64_lib.b64_format_B2R / b64_round_generic
     Orient_b64_exact.coord_int_safe / generic_format_IZR_le_bpow_prec
     OverlayNG.overlayng_same_sheet_as_R / overlayng_snap_neq_I
     NodingNG.nodingng_is_I_plus_cook

   QED: named two-way inhabitant — IEEE→ℝ (B2R) then round is identity;
   ℝ→IEEE (binary_normalize / ieee_of_Z) recovers IZR on the integer
   window; B2R_bp lifts a point; same sheet as ℝ realization; bridge
   ≠ 𝓘 / ≠ cook / ≠ OverlayNG snap.

   QEX: full FP noder; unrestricted round-trip outside the safe
   regime; kiss on the binary64 sheet. Honest remaining. Do not fake
   Discharge. Shewchuk A–D / Hobby / full Jordan stay off the
   critical path.

   Parks Γ / ι / ρ (named QEX, landed). This letter cites them once;
   it does not remint CircGamma, ι, leftover_width, or LoopDischarged.
   First cook stays chord–chord. Host CircGamma stays QEX. No H⊥ /
   Multi Landed / Phase B done-when / SQL/MM cathedral / MerkatorBV /
   522-n.

   ADR-0006 Status stays Accepted. ADR-0007 Status stays Accepted.
   No new Oracle keyword: generators attach as adapters on
   INTERSECT_FILTERED / INTERSECT_POINT_XY / OVERLAY_UNIFIED /
   ORIENT (Decision 1–2: line protocol, not FFI / RocqRefRunner /
   extract `eval` collapse).

   WITNESS topic: overlay · claimId: 0007-ieee-oracle-bridge
   witness: 0007-ieee-oracle-bridge
   board: ADR-0007
   Flocq C1 (classic via B2R / round). No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Lra.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import IEEE754.BinarySingleNaN.
From Flocq Require Import Core.

From NTS.Proofs Require Import Distance SheetHenCook NodingNG OverlayNG.
From NTS.Proofs.Flocq Require Import
  Validate_binary64 B64_bridge B64_lib
  Orient_b64_exact Validate_binary64_bridge.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Packaged projections. IEEE → ℝ is B2R / B2R_bp. Not a remint.             *)
(* -------------------------------------------------------------------------- *)

Definition ieee_to_R (x : binary64) : R :=
  Binary.B2R prec emax x.

Definition ieee_point_to_R (p : BPoint) : Point :=
  B2R_bp p.

Lemma ieee_point_to_R_is_B2R_bp :
  forall p : BPoint, ieee_point_to_R p = B2R_bp p.
Proof.
  intros p. reflexivity.
Qed.

Lemma ieee_map_points_to_R_is_map_B2R_bp :
  forall pts, map ieee_point_to_R pts = map_B2R_bp pts.
Proof.
  intros pts. reflexivity.
Qed.

(* IEEE → ℝ → round is identity: B2R lands in generic_format. *)
Lemma ieee_to_R_round_id :
  forall x : binary64,
    b64_round (ieee_to_R x) = ieee_to_R x.
Proof.
  intros x.
  apply b64_round_generic.
  apply b64_format_B2R.
Qed.

(* -------------------------------------------------------------------------- *)
(* ℝ → IEEE on the integer-safe / finite window. Packages Flocq               *)
(* binary_normalize + Orient_b64_exact.generic_format_IZR_le_bpow_prec.       *)
(* Same constructor KakeyaOrient2d_b64.b64Z uses; not a remint of that        *)
(* file's gnarly triple.                                                      *)
(* -------------------------------------------------------------------------- *)

Definition ieee_of_Z (m : Z) : binary64 :=
  Binary.binary_normalize prec emax prec_gt_0_b64 prec_lt_emax_b64
    mode_b64 m 0 false.

Lemma ieee_of_Z_B2R :
  forall m : Z, (Z.abs m <= 2 ^ 53)%Z ->
    Binary.B2R prec emax (ieee_of_Z m) = IZR m
    /\ Binary.is_finite prec emax (ieee_of_Z m) = true.
Proof.
  intros m Hm. unfold ieee_of_Z.
  pose proof (Binary.binary_normalize_correct prec emax
                prec_gt_0_b64 prec_lt_emax_b64 mode_b64 m 0 false) as H.
  assert (HF2R : F2R (Float radix2 m 0) = IZR m).
  { unfold F2R; simpl. lra. }
  rewrite HF2R in H.
  assert (Hround : Generic_fmt.round radix2 (SpecFloat.fexp prec emax)
                     (round_mode mode_b64) (IZR m) = IZR m).
  { apply Generic_fmt.round_generic; [apply valid_rnd_round_mode |].
    apply generic_format_IZR_le_bpow_prec. unfold prec; lia. }
  rewrite Hround in H.
  assert (Hbnd : Rabs (IZR m) < bpow radix2 emax).
  { rewrite <- abs_IZR.
    apply (Rle_lt_trans _ (bpow radix2 53)).
    - rewrite bpow_radix2_eq_IZR_pow by lia. apply IZR_le. exact Hm.
    - apply bpow_lt; unfold emax; lia. }
  apply Rlt_bool_true in Hbnd. rewrite Hbnd in H.
  destruct H as [HB2R [Hfin _]]. split; assumption.
Qed.

(* Named hypotheses: finite + no-overflow (B64_bridge.b64_safe). *)
Lemma ieee_plus_round_trip :
  forall x y : binary64,
    b64_safe Rplus x y ->
    Binary.B2R prec emax (b64_plus x y)
      = b64_round (Binary.B2R prec emax x + Binary.B2R prec emax y)
    /\ Binary.is_finite prec emax (b64_plus x y) = true.
Proof.
  exact b64_plus_correct.
Qed.

Lemma ieee_coord_int_safe_of_Z :
  forall m : Z, (Z.abs m <= 2 ^ 25)%Z -> coord_int_safe (ieee_of_Z m).
Proof.
  intros m Hm.
  destruct (ieee_of_Z_B2R m ltac:(lia)) as [HR Hf].
  split; [exact Hf | exists m; split; [exact HR | exact Hm]].
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked int-safe points: NodingNG crossing + 67-c parallel chords.          *)
(* -------------------------------------------------------------------------- *)

Definition ieee_pt (x y : Z) : BPoint :=
  mkBP (ieee_of_Z x) (ieee_of_Z y).

(* Unit-square diagonals — NodingNG Hit inhabitant on the wire. *)
Definition ieee_nodingng_hit_a0 : BPoint := ieee_pt 0 0.
Definition ieee_nodingng_hit_a1 : BPoint := ieee_pt 1 1.
Definition ieee_nodingng_hit_b0 : BPoint := ieee_pt 0 1.
Definition ieee_nodingng_hit_b1 : BPoint := ieee_pt 1 0.

(* 67-c / NodingNG Empty — parallel unit segments. *)
Definition ieee_relateng_67c_a0 : BPoint := ieee_pt 0 0.
Definition ieee_relateng_67c_a1 : BPoint := ieee_pt 1 0.
Definition ieee_relateng_67c_b0 : BPoint := ieee_pt 0 1.
Definition ieee_relateng_67c_b1 : BPoint := ieee_pt 1 1.

Lemma ieee_pt_B2R :
  forall x y : Z,
    (Z.abs x <= 2 ^ 53)%Z ->
    (Z.abs y <= 2 ^ 53)%Z ->
    B2R_bp (ieee_pt x y) = mkPoint (IZR x) (IZR y).
Proof.
  intros x y Hx Hy.
  unfold ieee_pt, B2R_bp; cbn [bx by_].
  destruct (ieee_of_Z_B2R x Hx) as [HRx _].
  destruct (ieee_of_Z_B2R y Hy) as [HRy _].
  rewrite HRx, HRy. reflexivity.
Qed.

Lemma ieee_nodingng_hit_B2R :
  B2R_bp ieee_nodingng_hit_a0 = mkPoint 0 0 /\
  B2R_bp ieee_nodingng_hit_a1 = mkPoint 1 1 /\
  B2R_bp ieee_nodingng_hit_b0 = mkPoint 0 1 /\
  B2R_bp ieee_nodingng_hit_b1 = mkPoint 1 0.
Proof.
  repeat split; apply ieee_pt_B2R; lia.
Qed.

Lemma ieee_relateng_67c_B2R :
  B2R_bp ieee_relateng_67c_a0 = mkPoint 0 0 /\
  B2R_bp ieee_relateng_67c_a1 = mkPoint 1 0 /\
  B2R_bp ieee_relateng_67c_b0 = mkPoint 0 1 /\
  B2R_bp ieee_relateng_67c_b1 = mkPoint 1 1.
Proof.
  repeat split; apply ieee_pt_B2R; lia.
Qed.

Lemma ieee_nodingng_hit_int_safe :
  point_int_safe ieee_nodingng_hit_a0 /\
  point_int_safe ieee_nodingng_hit_a1 /\
  point_int_safe ieee_nodingng_hit_b0 /\
  point_int_safe ieee_nodingng_hit_b1.
Proof.
  unfold point_int_safe, ieee_nodingng_hit_a0, ieee_nodingng_hit_a1,
         ieee_nodingng_hit_b0, ieee_nodingng_hit_b1, ieee_pt.
  cbn [bx by_].
  repeat split; apply ieee_coord_int_safe_of_Z; lia.
Qed.

Lemma ieee_relateng_67c_int_safe :
  point_int_safe ieee_relateng_67c_a0 /\
  point_int_safe ieee_relateng_67c_a1 /\
  point_int_safe ieee_relateng_67c_b0 /\
  point_int_safe ieee_relateng_67c_b1.
Proof.
  unfold point_int_safe, ieee_relateng_67c_a0, ieee_relateng_67c_a1,
         ieee_relateng_67c_b0, ieee_relateng_67c_b1, ieee_pt.
  cbn [bx by_].
  repeat split; apply ieee_coord_int_safe_of_Z; lia.
Qed.

(* Point-level round-trip: decode then round each coord. *)
Lemma ieee_point_round_trip :
  forall p : BPoint,
    b64_round (px (B2R_bp p)) = px (B2R_bp p) /\
    b64_round (py (B2R_bp p)) = py (B2R_bp p).
Proof.
  intros p.
  split; apply ieee_to_R_round_id.
Qed.

(* -------------------------------------------------------------------------- *)
(* Same sheet as ℝ realization. Packages SheetHenCook / OverlayNG.            *)
(* -------------------------------------------------------------------------- *)

Lemma ieee_coord_preserves_sheet :
  forall (s : Sheet) (n1 n2 : CoordRealization),
    realiz_sheet (mkSheetRealization s n1) =
    realiz_sheet (mkSheetRealization s n2).
Proof.
  exact coord_realization_preserves_sheet.
Qed.

Lemma ieee_same_sheet_as_R :
  forall s : Sheet,
    realiz_sheet (mkSheetRealization s RealizeBinary64) =
    realiz_sheet (mkSheetRealization s RealizeR).
Proof.
  exact binary64_same_sheet_as_R.
Qed.

Lemma ieee_overlayng_same_sheet :
  forall s : Sheet,
    realiz_sheet (mkSheetRealization s RealizeBinary64) =
    realiz_sheet (mkSheetRealization s RealizeR).
Proof.
  exact overlayng_same_sheet_as_R.
Qed.

(* -------------------------------------------------------------------------- *)
(* What the bridge is / is not. Kind tag, not a second kernel.                *)
(* -------------------------------------------------------------------------- *)

Inductive IeeeBridgeKind : Type :=
| IB_TwoWayRoundTrip
| IB_Cook
| IB_I
| IB_OverlayNGSnap
| IB_FpNoder
| IB_Unrestricted
| IB_KissOnB64.

Definition ieee_bridge_kind : IeeeBridgeKind := IB_TwoWayRoundTrip.

Lemma ieee_bridge_is_two_way : ieee_bridge_kind = IB_TwoWayRoundTrip.
Proof.
  reflexivity.
Qed.

Lemma ieee_bridge_neq_cook : ieee_bridge_kind <> IB_Cook.
Proof.
  discriminate.
Qed.

Lemma ieee_bridge_neq_I : ieee_bridge_kind <> IB_I.
Proof.
  discriminate.
Qed.

Lemma ieee_bridge_neq_overlayng_snap : ieee_bridge_kind <> IB_OverlayNGSnap.
Proof.
  discriminate.
Qed.

Lemma ieee_bridge_packages_nodingng :
  nodingng_kind = NNG_I_plus_cook /\
  ieee_bridge_kind <> IB_Cook.
Proof.
  split; [exact nodingng_is_I_plus_cook | exact ieee_bridge_neq_cook].
Qed.

Lemma ieee_bridge_packages_overlayng :
  overlayng_kind = ONG_SnapSequence /\
  CtorSnapRound <> CtorI /\
  ieee_bridge_kind <> IB_OverlayNGSnap.
Proof.
  split; [exact overlayng_is_snap_sequence |].
  split; [exact overlayng_snap_neq_I | exact ieee_bridge_neq_overlayng_snap].
Qed.

(* -------------------------------------------------------------------------- *)
(* Named QEX parks: FP noder / unrestricted round-trip / kiss on b64.         *)
(* Honest remaining. Do not fake Discharge.                                   *)
(* -------------------------------------------------------------------------- *)

Inductive IeeeBridgeParkCtor : Type :=
| FpNoderOnSheet
| UnrestrictedRoundTrip
| KissOnBinary64Sheet.

Definition ieee_bridge_park_inhabits (c : IeeeBridgeParkCtor) : Prop :=
  match c with
  | FpNoderOnSheet => False
  | UnrestrictedRoundTrip => False
  | KissOnBinary64Sheet => False
  end.

Lemma ieee_fp_noder_missing :
  ~ ieee_bridge_park_inhabits FpNoderOnSheet.
Proof.
  intro H. exact H.
Qed.

Lemma ieee_unrestricted_missing :
  ~ ieee_bridge_park_inhabits UnrestrictedRoundTrip.
Proof.
  intro H. exact H.
Qed.

Lemma ieee_kiss_on_b64_missing :
  ~ ieee_bridge_park_inhabits KissOnBinary64Sheet.
Proof.
  intro H. exact H.
Qed.

Inductive IeeeBridgeLetterStatus : Type :=
| IeeeBridgeLanded
| IeeeFpNoderDischarged
| IeeeUnrestrictedDischarged.

Definition ieee_bridge_letter_status : IeeeBridgeLetterStatus :=
  IeeeBridgeLanded.

Lemma ieee_bridge_letter_is_landed :
  ieee_bridge_letter_status = IeeeBridgeLanded /\
  ieee_bridge_letter_status <> IeeeFpNoderDischarged /\
  ieee_bridge_letter_status <> IeeeUnrestrictedDischarged /\
  ~ ieee_bridge_park_inhabits FpNoderOnSheet /\
  ~ ieee_bridge_park_inhabits UnrestrictedRoundTrip /\
  ~ ieee_bridge_park_inhabits KissOnBinary64Sheet.
Proof.
  split; [reflexivity |].
  split; [discriminate |].
  split; [discriminate |].
  split; [exact ieee_fp_noder_missing |].
  split; [exact ieee_unrestricted_missing |].
  exact ieee_kiss_on_b64_missing.
Qed.

(* Named QED package: two-way inhabitant + same sheet + ≠ I/cook/snap. *)
Lemma ieee_bridge_inhabits :
  (forall x : binary64, b64_round (ieee_to_R x) = ieee_to_R x) /\
  (forall m : Z, (Z.abs m <= 2 ^ 53)%Z ->
     Binary.B2R prec emax (ieee_of_Z m) = IZR m
     /\ Binary.is_finite prec emax (ieee_of_Z m) = true) /\
  (forall p : BPoint, ieee_point_to_R p = B2R_bp p) /\
  (forall (s : Sheet) (n1 n2 : CoordRealization),
     realiz_sheet (mkSheetRealization s n1) =
     realiz_sheet (mkSheetRealization s n2)) /\
  (forall s : Sheet,
     realiz_sheet (mkSheetRealization s RealizeBinary64) =
     realiz_sheet (mkSheetRealization s RealizeR)) /\
  B2R_bp ieee_nodingng_hit_a0 = mkPoint 0 0 /\
  B2R_bp ieee_relateng_67c_a0 = mkPoint 0 0 /\
  point_int_safe ieee_nodingng_hit_a0 /\
  point_int_safe ieee_relateng_67c_a0 /\
  ieee_bridge_kind = IB_TwoWayRoundTrip /\
  ieee_bridge_kind <> IB_Cook /\
  ieee_bridge_kind <> IB_I /\
  ieee_bridge_kind <> IB_OverlayNGSnap /\
  nodingng_kind = NNG_I_plus_cook /\
  overlayng_kind = ONG_SnapSequence /\
  CtorSnapRound <> CtorI.
Proof.
  split; [exact ieee_to_R_round_id |].
  split; [exact ieee_of_Z_B2R |].
  split; [exact ieee_point_to_R_is_B2R_bp |].
  split; [exact ieee_coord_preserves_sheet |].
  split; [exact ieee_same_sheet_as_R |].
  split; [exact (proj1 ieee_nodingng_hit_B2R) |].
  split; [exact (proj1 ieee_relateng_67c_B2R) |].
  split; [exact (proj1 ieee_nodingng_hit_int_safe) |].
  split; [exact (proj1 ieee_relateng_67c_int_safe) |].
  split; [exact ieee_bridge_is_two_way |].
  split; [exact ieee_bridge_neq_cook |].
  split; [exact ieee_bridge_neq_I |].
  split; [exact ieee_bridge_neq_overlayng_snap |].
  split; [exact nodingng_is_I_plus_cook |].
  split; [exact overlayng_is_snap_sequence |].
  exact overlayng_snap_neq_I.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-ieee-oracle-bridge","topic":"overlay","lemma":"ticket_0007_ieee_bridge_qed_or_qex","title":"IEEE binary64 two-way bridge inhabits B2R/round under the finite int-safe regime on the same sheet as R (QED) or snap equals I (QEX); discharged QED; bridge != cook / != I / != OverlayNG snap; NodingNG Hit and RelateNG 67-c points decode","file":"theories-flocq/IeeeRBridge.v","witness":"0007-ieee-oracle-bridge","board":"ADR-0007"} *)
Theorem ticket_0007_ieee_bridge_qed_or_qex :
  ((forall x : binary64, b64_round (ieee_to_R x) = ieee_to_R x) /\
   (forall m : Z, (Z.abs m <= 2 ^ 53)%Z ->
      Binary.B2R prec emax (ieee_of_Z m) = IZR m
      /\ Binary.is_finite prec emax (ieee_of_Z m) = true) /\
   (forall p : BPoint, ieee_point_to_R p = B2R_bp p) /\
   (forall (s : Sheet) (n1 n2 : CoordRealization),
      realiz_sheet (mkSheetRealization s n1) =
      realiz_sheet (mkSheetRealization s n2)) /\
   (forall s : Sheet,
      realiz_sheet (mkSheetRealization s RealizeBinary64) =
      realiz_sheet (mkSheetRealization s RealizeR)) /\
   B2R_bp ieee_nodingng_hit_a0 = mkPoint 0 0 /\
   B2R_bp ieee_relateng_67c_a0 = mkPoint 0 0 /\
   point_int_safe ieee_nodingng_hit_a0 /\
   point_int_safe ieee_relateng_67c_a0 /\
   ieee_bridge_kind = IB_TwoWayRoundTrip /\
   ieee_bridge_kind <> IB_Cook /\
   ieee_bridge_kind <> IB_I /\
   ieee_bridge_kind <> IB_OverlayNGSnap /\
   nodingng_kind = NNG_I_plus_cook /\
   overlayng_kind = ONG_SnapSequence /\
   CtorSnapRound <> CtorI)
  \/
  CtorSnapRound = CtorI.
Proof.
  left.
  exact ieee_bridge_inhabits.
Qed.

(* Full FP noder (𝓘 realized in Flocq on the sheet) stays Honest remaining. *)
(* WITNESS {"claimId":"0007-ieee-oracle-bridge","topic":"overlay","lemma":"ticket_0007_ieee_bridge_fp_noder_qed_or_qex","title":"IEEE bridge discharges a full floating-point noder on the binary64 sheet (QED) or parks FpNoderOnSheet as Honest remaining (QEX); discharged QEX; bridge is not a cook and not OverlayNG snap","file":"theories-flocq/IeeeRBridge.v","witness":"0007-ieee-oracle-bridge","board":"ADR-0007"} *)
Theorem ticket_0007_ieee_bridge_fp_noder_qed_or_qex :
  (ieee_bridge_letter_status = IeeeFpNoderDischarged
   /\ ieee_bridge_park_inhabits FpNoderOnSheet)
  \/
  (ieee_bridge_letter_status = IeeeBridgeLanded
   /\ ~ ieee_bridge_park_inhabits FpNoderOnSheet
   /\ ieee_bridge_kind = IB_TwoWayRoundTrip
   /\ ieee_bridge_kind <> IB_FpNoder
   /\ ieee_bridge_kind <> IB_Cook
   /\ nodingng_kind = NNG_I_plus_cook).
Proof.
  right.
  split; [reflexivity |].
  split; [exact ieee_fp_noder_missing |].
  split; [exact ieee_bridge_is_two_way |].
  split; [discriminate |].
  split; [exact ieee_bridge_neq_cook |].
  exact nodingng_is_I_plus_cook.
Qed.

(* Unrestricted round-trip outside the safe regime, and kiss on the
   binary64 sheet, stay Honest remaining. Named QEX. Do not fake Discharge. *)
(* WITNESS {"claimId":"0007-ieee-oracle-bridge","topic":"overlay","lemma":"ticket_0007_ieee_bridge_unrestricted_qed_or_qex","title":"IEEE bridge discharges unrestricted round-trip outside the int-safe regime and kiss on the binary64 sheet (QED) or parks UnrestrictedRoundTrip / KissOnBinary64Sheet as Honest remaining (QEX); discharged QEX","file":"theories-flocq/IeeeRBridge.v","witness":"0007-ieee-oracle-bridge","board":"ADR-0007"} *)
Theorem ticket_0007_ieee_bridge_unrestricted_qed_or_qex :
  (ieee_bridge_letter_status = IeeeUnrestrictedDischarged
   /\ ieee_bridge_park_inhabits UnrestrictedRoundTrip
   /\ ieee_bridge_park_inhabits KissOnBinary64Sheet)
  \/
  (ieee_bridge_letter_status = IeeeBridgeLanded
   /\ ~ ieee_bridge_park_inhabits UnrestrictedRoundTrip
   /\ ~ ieee_bridge_park_inhabits KissOnBinary64Sheet
   /\ ieee_bridge_kind = IB_TwoWayRoundTrip
   /\ ieee_bridge_kind <> IB_Unrestricted
   /\ ieee_bridge_kind <> IB_KissOnB64).
Proof.
  right.
  split; [reflexivity |].
  split; [exact ieee_unrestricted_missing |].
  split; [exact ieee_kiss_on_b64_missing |].
  split; [exact ieee_bridge_is_two_way |].
  split; [discriminate |].
  discriminate.
Qed.

Print Assumptions ieee_to_R_round_id.
Print Assumptions ieee_of_Z_B2R.
Print Assumptions ieee_pt_B2R.
Print Assumptions ieee_nodingng_hit_B2R.
Print Assumptions ieee_relateng_67c_B2R.
Print Assumptions ieee_same_sheet_as_R.
Print Assumptions ieee_bridge_inhabits.
Print Assumptions ieee_fp_noder_missing.
Print Assumptions ticket_0007_ieee_bridge_qed_or_qex.
Print Assumptions ticket_0007_ieee_bridge_fp_noder_qed_or_qex.
Print Assumptions ticket_0007_ieee_bridge_unrestricted_qed_or_qex.
