(* ============================================================================
   NetTopologySuite.Proofs.Adr0007NodingEpic
   ----------------------------------------------------------------------------
   ADR-0007 ticket-named QED ∨ QEX stops (same shape as ticket 508 /
   ticket 522).

   The noding constructor is part of the specification: sheet, hen,
   egg, chicken, cook / 𝓘. First cook scope is chord–chord only.

   QED: chord–chord inhabits the cook interface; Empty ≠ Decline;
   ShareOne mints one hen; noded-on-S is cook evidence.
   `ticket_0007_chord_chord_qed_or_qex` discharges left.
   `ticket_0007_empty_neq_decline_qed_or_qex` discharges left.
   `ticket_0007_identity_qed_or_qex` discharges left.
   `ticket_0007_noded_cook_qed_or_qex` discharges left.

   QEX: a documented out-of-scope pair (clothoid–clothoid) is missing
   from first cook scope; numeric coord-pair equality does not decide
   hen identity; silent pairwise_nodable excludes the proper-crossing
   case a noder exists for.
   `ticket_0007_qed_or_qex` discharges right on clothoid–clothoid
   (`clothoid_clothoid_not_first_scope`), 508-style.
   `ticket_0007_dart_eq_qed_or_qex` discharges right.
   `ticket_0007_silent_nodable_qed_or_qex` discharges right.

   Cook termination host-lane close: pairwise interior split is
   finite and one Hit-split is confluent (leftover bag independent
   of parent order).
   `ticket_0007_pairwise_split_qed_or_qex` discharges left.
   The bag-level repeat-until-noded loop is a named 508-style
   QEX gap (missing CookLoopBagTerm; leftover_quad width
   conserved; kiss / share / mint not covered). Not a soft gap.
   ρ letter lives in SheetHenCookLoop.v
   (`ticket_0007_rho_gap_qed_or_qex` and friends).
   `ticket_0007_cook_term_qed_or_qex` discharges right.

   binary64 / OverlayNGRobust sit on one sheet (QED).
   `ticket_0007_sheet_realiz_qed_or_qex` discharges left.

   Chicken vs Dart: DdirDart := (Hen * Hen) is the chicken
   projection (QED). One type equation, not three types.
   `ticket_0007_chicken_dart_qed_or_qex` discharges left.

   Letter after Accept (not a noder): chord split(t) + one Hit cook
   step mints one hen and replaces each crossed chicken by two
   incident on that hen. `ticket_0007_cook_step_qed_or_qex`
   discharges left on the crossing pair. Out-of-scope pairs mint
   nothing (`ticket_0007_cook_step_scope_qed_or_qex` discharges
   right). Not a remint of leftover_width / pairwise_split.

   Letter after Accept (not a noder): proper-cross signs license a constructed
   Hit via Intersect.strict_intersection_point. That Hit recovers
   the unit-square witness and cooks. `ticket_0007_constructed_I_qed_or_qex`
   discharges left. Missing signs do not license the formula
   (`ticket_0007_constructed_I_scope_qed_or_qex` discharges right).
   Equal constructed p* (operand swap) licenses ShareOne
   (`ticket_0007_share_constructed_qed_or_qex` discharges left).
   Not a remint of Intersect. Not a total 𝓘.

   Letter after Accept (not a noder): a circular IHit still cannot
   feed the host cook step. Circular eggs stay MkOutOfScope;
   try_cook_hit returns None. `ticket_0007_circ_host_cook_qed_or_qex`
   discharges right. First cook scope stays chord–chord. Host
   CircGamma stays QEX (CircularCook.v). The 4-axiom sidecar
   CircularCookSplit.v feeds the locked circular Hit into a
   same-shape split(t) cook; I.7 MintTwo / p- lives there too.
   That is not this host module. Do not fake CircGamma Discharge.
   I.1 Fence: chord × circular Decline inhabits I_ok (honest host
   arm). A constructed mixed Hit does not. The four-object pairwise
   fence lives in CircularCookSplit.v — not a type synonym.
   I.9 classifier ≠ cook lives in CircularCookLicense.v — a
   Z-classifier Hit is tags 0/1 and does not license host
   try_cook_hit / circ_split / first_cook_scope expansion.
   I.10 Campaign-I close lives in CircularCookClose.v — sidecar
   cook on both roots; CircGamma stays QEX; first cook stays
   chord–chord; I_CIRCULAR stays a classifier; #666 fence holds;
   Campaign II and H⊥ were named parked at that close.
   II.1 span filter as IResult lives in CircularCookSpanFilter.v
   (4-axiom sidecar; not Required here). II.2 span split at
   in-span t lives in CircularCookSpanSplit.v (4-axiom sidecar;
   not Required here). II.3 I_ok_circ lives in
   CircularCookOkCirc.v (4-axiom sidecar; not Required here).
   II.4 Campaign-II close lives in CircularCookCloseII.v
   (4-axiom sidecar; not Required here). Phase B.1 CircularString
   concat joints live in CircularCookCsConcat.v (4-axiom sidecar
   reuse of I_ok_circ / arc_gamma; not Required here). Phase B.2
   CompoundCurve member joints live in CircularCookCcConcat.v
   (4-axiom sidecar / host reuse; not Required here). Phase B
   mixed LS–CS joints live in SidecarCircMixed.v (4-axiom
   sidecar I_ok_mixed Hit at concat endpoints; not Required
   here). Phase B.3 CurvePolygon ring closure lives in
   CircularCookCpConcat.v (4-axiom sidecar / host reuse of B.1
   I_ok_circ / B.2 host I_ok / I_ok_mixed; not Required here).
   Phase B MultiCurve / MultiSurface bags live in
   SidecarCircBags.v (4-axiom sidecar reuse of B.1–B.3 /
   I_ok_mixed; bag ≠ concat; not Required here). Phase B ι
   interior circular×chord cook lives in SidecarCircInterior.v
   (4-axiom sidecar QEX: I_ok_mixed Hit is joint-only; not
   Required here). Host CircGamma stays QEX. first cook stays
   chord–chord. H⊥ stays parked. Not a bag noder.
   Phase B.1–B.3 letters landed. Mixed LS–CS inhabits sidecar
   I_ok_mixed; host I_ok mixed stays Decline (I.1). Interior
   mixed cook stays parked (named mixed_joint_params gate).
   Required-type CC / CP Landed (mixed I_ok_mixed Hit, not
   host I_ok); CS stays Gap; Multi stays Gap (optional Part 3
   bag inhabitant, not required-type). Phase B stays Open —
   letter landed ≠ SQL/MM done / Phase B done-when /
   cathedral Landed. Not this host module.
   Clothoid egg sidecar lives in SidecarClothoidEgg.v
   (3-axiom; Decline-on-host + RelateClothoid chord-seed;
   not Required here). ι interior Hit discharge lives in
   SidecarCircInteriorHit.v (4-axiom sidecar; I_ok_interior
   ≠ I_ok_mixed; joint gate stands; not Required here).
   First cook stays chord–chord.

   QEX is not a new Accept cycle. ADR-0007 is Accepted (2026-09-07).
   These letters do not reopen Status. Constructed chord-chord I is
   not I_circles_z / I_CIRCULAR and not glossary I with gamma / t.
   Host CircGamma stays QEX. Do not remint CurveSegment / Exact*
   zoo types / Dart. Do not steal 508-* / 522-* board mints. Do
   not claim a complete FP noder or close Hobby. Do not close 510.

   Testable 𝓘 / cook results sit on the accepted Oracle line protocol
   (ADR-0006). This module mints no keyword and no second external seam.
   A later keyword attaches as an Oracle adapter, never as FFI or
   RocqRefRunner.

   WITNESS topic: overlay · claimId: 0007 · witness: 0007-qed-qex
   lane: proofs
   board: ADR-0007

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import Distance Segment SheetHenCook SheetHenCookLoop.
Local Open Scope R_scope.

(* ADR-0007 stop: every egg-class pair is in first cook scope (QED)
   or a documented out-of-scope pair is missing (QEX). Discharged QEX
   on clothoid–clothoid — the 508-style carrier miss. *)
(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_qed_or_qex","title":"ADR-0007 stop is first-cook-scope completeness (QED) or a documented out-of-scope pair (QEX); discharged QEX on clothoid-clothoid","file":"theories/Adr0007NodingEpic.v","witness":"0007-qed-qex","board":"ADR-0007"} *)

Theorem ticket_0007_qed_or_qex :
  (forall a b : EggClass, first_cook_scope a b)
  \/
  (exists a b : EggClass, ~ first_cook_scope a b).
Proof.
  right.
  exists EggClothoid, EggClothoid.
  exact clothoid_clothoid_not_first_scope.
Qed.

(* Chord–chord inhabits the cook interface (QED) or a documented
   miss (QEX). Crossing Hit + disjoint Empty + never Decline in
   scope. First cook scope is chord–chord. *)
Theorem ticket_0007_chord_chord_qed_or_qex :
  (first_cook_scope EggChord EggChord /\
   egg_class (cw_e1 crossing_witness) = EggChord /\
   egg_class (cw_e2 crossing_witness) = EggChord /\
   (exists p ti tj, cw_result crossing_witness = IHit p ti tj) /\
   cw_result disjoint_witness = IEmpty /\
   (forall c1 c2 o,
      I_ok (MkChord c1) (MkChord c2) o -> o <> IDecline))
  \/
  (exists a b : EggClass, ~ first_cook_scope a b).
Proof.
  left.
  split; [exact first_cook_scope_chord_chord|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [|split].
  - exists cross_pt, (1 / 2), (1 / 2).
    reflexivity.
  - reflexivity.
  - exact I_ok_chord_not_decline.
Qed.

(* Empty ≠ Decline as distinct 𝓘 outcomes (QED) or they coincide (QEX).
   Discharged QED. *)
Theorem ticket_0007_empty_neq_decline_qed_or_qex :
  IEmpty <> IDecline
  \/
  IEmpty = IDecline.
Proof.
  left.
  exact IEmpty_neq_IDecline.
Qed.

(* Structural identity: coincident cook successes share one hen when
   the cook so decides (QED) or the share policy fails (QEX).
   Discharged QED on ShareOne. *)
Theorem ticket_0007_identity_qed_or_qex :
  (forall h : Hen,
     fst (apply_id_decision (ShareOne h)) =
     snd (apply_id_decision (ShareOne h)))
  \/
  (exists h : Hen,
     fst (apply_id_decision (ShareOne h)) <>
     snd (apply_id_decision (ShareOne h))).
Proof.
  left.
  exact share_one_same_hen.
Qed.

(* Numeric coord-pair equality decides hen identity (QED) or it does
   not (QEX). Discharged QEX — dart_eq_dec answers the wrong question.
   Local CoordDart mirrors Dart.v:50; not a remint. *)
Theorem ticket_0007_dart_eq_qed_or_qex :
  (forall (h1 h2 : Hen) (d1 d2 : CoordDart),
     h1 = h2 <-> d1 = d2)
  \/
  ~ (forall (h1 h2 : Hen) (d1 d2 : CoordDart),
       h1 = h2 <-> d1 = d2).
Proof.
  right.
  exact coord_eq_not_hen_eq.
Qed.

(* Noded on S is cook evidence (QED) or no such package exists (QEX).
   Discharged QED on the crossing witness. *)
Theorem ticket_0007_noded_cook_qed_or_qex :
  (exists n : NodedOnSheet,
     I_ok (cw_e1 (noded_cook n)) (cw_e2 (noded_cook n))
          (cw_result (noded_cook n)))
  \/
  (forall n : NodedOnSheet,
     ~ I_ok (cw_e1 (noded_cook n)) (cw_e2 (noded_cook n))
            (cw_result (noded_cook n))).
Proof.
  left.
  exists noded_crossing.
  exact (noded_on_sheet_carries_I_ok noded_crossing).
Qed.

(* Silent pairwise_nodable / fully_intersected discharges the
   constructor (QED) or a documented proper-crossing pair is excluded
   by that hypothesis (QEX). Discharged QEX — the noder's job is the
   excluded case. Epic-stop shaped; not a Hobby rewrite. *)
Theorem ticket_0007_silent_nodable_qed_or_qex :
  (forall A B C D : Point,
     (exists X, between A B X /\ between C D X) ->
     pairwise_nodable_shadow A B C D)
  \/
  (exists A B C D : Point,
     (exists X, between A B X /\ between C D X) /\
     ~ pairwise_nodable_shadow A B C D).
Proof.
  right.
  exists (mkPoint 0 0), (mkPoint 2 2), (mkPoint 0 2), (mkPoint 2 0).
  split.
  - exists cross_pt.
    split; [exact crossing_midpoint_ab | exact crossing_midpoint_cd].
  - exact crossing_not_nodable_shadow.
Qed.

(* Pairwise interior split + one-step confluence on the chord lane
   (QED) or the leftover-width measure fails (QEX). Discharged QED —
   interior Hit splits [0,1] into two strictly shorter leftovers
   whose bag does not depend on parent order. The bag loop is not
   this stop. *)
(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_pairwise_split_qed_or_qex","title":"ADR-0007 pairwise chord split is finite and one Hit-split is confluent (QED) or the leftover-width measure fails (QEX); discharged QED","file":"theories/Adr0007NodingEpic.v","witness":"0007-pairwise-split","board":"ADR-0007"} *)
Theorem ticket_0007_pairwise_split_qed_or_qex :
  (interior_split_finite /\ split_step_confluent_holds)
  \/
  ~ interior_split_finite.
Proof.
  left.
  split; [exact interior_split_finite_holds|].
  exact split_step_confluent_holds_proof.
Qed.

(* Bag-level cook loop on the chord lane (QED: discharged with a
   bag-term measure) or the named 508-style gap (QEX). Discharged
   QEX — CookLoopBagTerm is missing; leftover_quad width is
   conserved; pairwise width decrease is a sibling QED stop, not
   this discharge. Honest remaining / CRV-TOUCH. Not a soft gap.
   ρ letter: SheetHenCookLoop.v / witness 0007-rho-bag-loop. *)
(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_cook_term_qed_or_qex","title":"ADR-0007 bag cook loop is discharged with a bag-term measure (QED) or named QEX: CookLoopBagTerm missing, leftover_quad width conserved; pairwise split is a sibling QED stop","file":"theories/Adr0007NodingEpic.v","witness":"0007-cook-term","board":"ADR-0007"} *)
Theorem ticket_0007_cook_term_qed_or_qex :
  (cook_loop_status = LoopDischarged
   /\ cook_loop_ctor_inhabits CookLoopBagTerm
   /\ interior_split_finite)
  \/
  (cook_loop_status = LoopObligation
   /\ ~ cook_loop_ctor_inhabits CookLoopBagTerm
   /\ interior_split_finite
   /\ split_step_confluent_holds
   /\ (forall ti tj,
         0 < ti < 1 ->
         0 < tj < 1 ->
         leftover_quad_width ti tj =
         leftover_width 0 1 + leftover_width 0 1)
   /\ arc_cook_term_status = ArcTermSister).
Proof.
  right.
  split; [exact cook_loop_is_obligation|].
  split; [exact cook_loop_bag_term_missing|].
  split; [exact interior_split_finite_holds|].
  split; [exact split_step_confluent_holds_proof|].
  split; [exact leftover_quad_width_conserved|].
  reflexivity.
Qed.

(* binary64 / OverlayNGRobust sit on one sheet (QED) or changing the
   number type yields a second sheet (QEX). Discharged QED —
   realization preserves S; OverlayNGRobust is a finite snap-sequence,
   not 𝓘. *)
(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_sheet_realiz_qed_or_qex","title":"ADR-0007 binary64 and OverlayNGRobust sit on one sheet (QED) or a second sheet appears (QEX); discharged QED","file":"theories/Adr0007NodingEpic.v","witness":"0007-sheet-realiz","board":"ADR-0007"} *)
Theorem ticket_0007_sheet_realiz_qed_or_qex :
  ((forall (s : Sheet) (n1 n2 : CoordRealization),
      realiz_sheet (mkSheetRealization s n1) =
      realiz_sheet (mkSheetRealization s n2))
   /\
   (forall (s : Sheet) (n : nat),
      overlay_ng_robust_is_finite_snap s n)
   /\
   CtorSnapRound <> CtorI)
  \/
  (exists (s : Sheet) (n1 n2 : CoordRealization),
     realiz_sheet (mkSheetRealization s n1) <>
     realiz_sheet (mkSheetRealization s n2)).
Proof.
  left.
  split; [exact coord_realization_preserves_sheet|].
  split; [exact overlay_ng_robust_is_finite_snap_holds|].
  exact overlay_ng_robust_is_snap_not_I.
Qed.

(* DdirDart := (Hen * Hen) is the chicken projection (QED) or the
   hen-id view is not that pair (QEX). Discharged QED — one type
   equation; CoordDart stays the Dart.v:50 story; no third type. *)
(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_chicken_dart_qed_or_qex","title":"ADR-0007 ddir migration is Hen-id pair equals chicken ends (QED) or that equation fails (QEX); discharged QED","file":"theories/Adr0007NodingEpic.v","witness":"0007-chicken-dart","board":"ADR-0007"} *)
Theorem ticket_0007_chicken_dart_qed_or_qex :
  (DdirDart = (Hen * Hen)%type /\
   RoleHenIdDart <> RoleCoordDart /\
   (forall c : Chicken, hen_id_dart_of_chicken c = (ck_src c, ck_dst c)) /\
   (forall c : Chicken, chicken_gamma_source c = ck_egg c))
  \/
  DdirDart <> (Hen * Hen)%type.
Proof.
  left.
  exact ddir_migration_one_equation.
Qed.

(* Core-slice circular tickets: ticket_64_circ_hit_params_qed_or_qex
   (QED, CircularCookHit.v, full/atan2), CircularCookSpan.v span γ
   (QED, 4-axiom sidecar), ticket_64_circ_gamma_qed_or_qex (QEX,
   CircularCook.v named gap: no MkCirc / nlerp miss / no first-cook
   expand; sidecar arc_gamma is not host Γ), and CircularCookSplit.v (4-axiom
   sidecar cook of a locked circular Hit). I.2 ∀ Hit soundness
   lives in CircularCookHit.v (ticket_0007_i2_hit_sound_qed_or_qex);
   I.3 ∀ Empty / Decline lives in CircularCookEmpty.v
   (ticket_0007_i3_empty_qed_or_qex; 4-axiom γ_full; not Required
   here); I.8 leftover confluence lives in CircularCookConfluence.v
   (ticket_0007_i8_confluent_qed_or_qex; 4-axiom γ_full; not
   Required here); I.9 classifier ≠ cook lives in
   CircularCookLicense.v (ticket_0007_i9_tags_qed_or_qex; 4-axiom;
   not Required here). Not Required here — host lane stays atan2-free.
   Host CircGamma stays QEX; first cook stays chord–chord. The host
   circular-Hit→cook bridge is the QEX stop
   ticket_0007_circ_host_cook_qed_or_qex below. *)

(* Letter after Accept: one Hit cook step on chord–chord (QED) or
   the step fails to mint (QEX). Discharged QED — crossing chickens
   share one minted hen after split(t). Not the bag noder loop. *)
(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_cook_step_qed_or_qex","title":"ADR-0007 letter after Accept is one Hit cook step (QED) or no mint (QEX); discharged QED on chord-chord split sharing one hen","file":"theories/Adr0007NodingEpic.v","witness":"0007-cook-split","board":"ADR-0007"} *)
Theorem ticket_0007_cook_step_qed_or_qex :
  (exists cp : CookedPair,
     try_cook_hit crossing_ck1 crossing_ck2
       (cw_result crossing_witness) crossing_hen = Some cp /\
     cooked_shares_hen cp /\
     cp_hen cp = crossing_hen)
  \/
  try_cook_hit crossing_ck1 crossing_ck2
    (cw_result crossing_witness) crossing_hen = None.
Proof.
  left.
  exists cooked_crossing.
  split; [exact cooked_crossing_try|].
  split; [exact cooked_crossing_shares|].
  reflexivity.
Qed.

(* Out-of-scope / Empty / Decline mint a hen (QED) or they do not
   (QEX). Discharged QEX — clothoid Decline and chord Empty allocate
   no hen. *)
Theorem ticket_0007_cook_step_scope_qed_or_qex :
  (forall c1 c2 o h, try_cook_hit c1 c2 o h <> None)
  \/
  (try_cook_hit clothoid_ck1 clothoid_ck2 IDecline crossing_hen = None /\
   try_cook_hit crossing_ck1 crossing_ck2 IEmpty crossing_hen = None).
Proof.
  right.
  split; [exact try_cook_hit_clothoid_none|].
  apply try_cook_hit_empty_none.
Qed.

(* Next rung: constructed 𝓘 from proper-cross signs (QED) or the
   formula is not licensed (QEX). Discharged QED — signs on the
   unit-square diagonals produce the same Hit the cook already
   splits, via Intersect.strict_intersection_point. Not a remint. *)
(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_constructed_I_qed_or_qex","title":"ADR-0007 next rung is constructed I from proper-cross signs (QED) or the formula is unlicensed (QEX); discharged QED on Intersect.strict_intersection_point recovering the unit-square Hit","file":"theories/Adr0007NodingEpic.v","witness":"0007-constructed-I","board":"ADR-0007"} *)
Theorem ticket_0007_constructed_I_qed_or_qex :
  (proper_cross_signs diag_ab diag_cd /\
   I_ok (MkChord diag_ab) (MkChord diag_cd)
        (constructed_hit diag_ab diag_cd) /\
   constructed_hit diag_ab diag_cd = IHit cross_pt (1 / 2) (1 / 2) /\
   try_cook_hit crossing_ck1 crossing_ck2
     (constructed_hit diag_ab diag_cd) crossing_hen = Some cooked_crossing /\
   cooked_shares_hen cooked_crossing)
  \/
  ~ proper_cross_signs diag_ab diag_cd.
Proof.
  left.
  split; [exact crossing_proper_cross_signs|].
  split; [apply constructed_hit_I_ok; exact crossing_proper_cross_signs|].
  split; [exact constructed_hit_crossing_eq|].
  split; [exact cooked_constructed_crossing|].
  exact cooked_crossing_shares.
Qed.

(* Constructed 𝓘 is total on chord–chord (QED) or missing signs do
   not license the formula (QEX). Discharged QEX — disjoint
   horizontals are Empty, not a constructed Hit. *)
Theorem ticket_0007_constructed_I_scope_qed_or_qex :
  (forall c1 c2,
     I_ok (MkChord c1) (MkChord c2) (constructed_hit c1 c2))
  \/
  (~ proper_cross_signs hor_bot hor_top /\
   I_ok (MkChord hor_bot) (MkChord hor_top) IEmpty).
Proof.
  right.
  split; [exact disjoint_not_proper_cross|].
  exact disjoint_I_ok.
Qed.

(* Equal constructed p* licenses ShareOne (QED) or operand swap
   names two points (QEX). Discharged QED — Intersect.strict_
   intersection_point_sym. The basis, not dart_eq_dec. *)
Theorem ticket_0007_share_constructed_qed_or_qex :
  (forall h : Hen,
     hit_point (constructed_hit diag_ab diag_cd) =
     hit_point (constructed_hit diag_cd diag_ab) /\
     fst (apply_id_decision (ShareOne h)) =
     snd (apply_id_decision (ShareOne h)))
  \/
  (exists h : Hen,
     hit_point (constructed_hit diag_ab diag_cd) <>
     hit_point (constructed_hit diag_cd diag_ab)).
Proof.
  left.
  intros h.
  apply (equal_constructed_p_share diag_ab diag_cd h
           crossing_proper_cross_signs).
Qed.

(* Next rung: a circular IHit feeds the host cook step (QED) or the
   host cook still declines circular eggs (QEX). Discharged QEX —
   MkOutOfScope EggCircularArc is not first cook scope, so
   try_cook_hit returns None even when the result is IHit.
   CircGamma stays QEX in CircularCook.v; do not fake Discharge.
   Not a remint of ArcSplitAtNode. Kiss/Touch is not this stop. *)
(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_circ_host_cook_qed_or_qex","title":"ADR-0007 circular IHit feeds the host cook (QED) or try_cook_hit still declines circular eggs (QEX); discharged QEX; CircGamma stays QEX","file":"theories/Adr0007NodingEpic.v","witness":"0007-circ-cook","board":"ADR-0007"} *)
Theorem ticket_0007_circ_host_cook_qed_or_qex :
  (exists cp : CookedPair,
     try_cook_hit circular_ck1 circular_ck2
       (IHit cross_pt (1 / 2) (1 / 2)) crossing_hen = Some cp)
  \/
  (try_cook_hit circular_ck1 circular_ck2
     (IHit cross_pt (1 / 2) (1 / 2)) crossing_hen = None
   /\ ~ first_cook_scope EggCircularArc EggCircularArc).
Proof.
  right.
  split; [apply try_cook_hit_circular_hit_none|].
  exact circular_egg_not_first_cook_scope.
Qed.

(* I.1: chord × circular Decline inhabits I_ok (QED) or a mixed
   constructed Hit is licensed (QEX). Discharged QED — first cook
   scope stays chord–chord; mixed Empty / Hit are False. Not a
   constructed mixed Hit. *)
(* WITNESS {"claimId":"0007","topic":"overlay","lemma":"ticket_0007_chord_circ_decline_qed_or_qex","title":"Chord times circular Decline inhabits I_ok (QED) or a mixed Hit is licensed (QEX); discharged QED; I.1 honest host arm","file":"theories/Adr0007NodingEpic.v","witness":"0007-I.1-fence","board":"ADR-0007"} *)

Theorem ticket_0007_chord_circ_decline_qed_or_qex :
  (I_ok (MkChord hor_bot) (MkOutOfScope EggCircularArc) IDecline
   /\ (forall p ti tj,
         ~ I_ok (MkChord hor_bot) (MkOutOfScope EggCircularArc)
              (IHit p ti tj))
   /\ ~ I_ok (MkChord hor_bot) (MkOutOfScope EggCircularArc) IEmpty
   /\ ~ first_cook_scope EggChord EggCircularArc)
  \/
  I_ok (MkChord hor_bot) (MkOutOfScope EggCircularArc)
       (IHit cross_pt (1 / 2) (1 / 2)).
Proof.
  left.
  split; [exact chord_circular_decline_I_ok|].
  split; [exact chord_circular_hit_not_I_ok|].
  split; [exact chord_circular_empty_not_I_ok|].
  exact chord_circular_not_first_cook_scope.
Qed.

Print Assumptions ticket_0007_qed_or_qex.
Print Assumptions ticket_0007_chord_chord_qed_or_qex.
Print Assumptions ticket_0007_empty_neq_decline_qed_or_qex.
Print Assumptions ticket_0007_identity_qed_or_qex.
Print Assumptions ticket_0007_dart_eq_qed_or_qex.
Print Assumptions ticket_0007_noded_cook_qed_or_qex.
Print Assumptions ticket_0007_silent_nodable_qed_or_qex.
Print Assumptions ticket_0007_pairwise_split_qed_or_qex.
Print Assumptions ticket_0007_cook_term_qed_or_qex.
Print Assumptions ticket_0007_sheet_realiz_qed_or_qex.
Print Assumptions ticket_0007_chicken_dart_qed_or_qex.
Print Assumptions ticket_0007_cook_step_qed_or_qex.
Print Assumptions ticket_0007_cook_step_scope_qed_or_qex.
Print Assumptions ticket_0007_constructed_I_qed_or_qex.
Print Assumptions ticket_0007_constructed_I_scope_qed_or_qex.
Print Assumptions ticket_0007_share_constructed_qed_or_qex.
Print Assumptions ticket_0007_circ_host_cook_qed_or_qex.
Print Assumptions ticket_0007_chord_circ_decline_qed_or_qex.
