(* ============================================================================
   NetTopologySuite.Proofs.NodingNG
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: NodingNG chord lane
   (claimId 0007-nodingng-chord).

   Product face: NodingNG = 𝓘 + cook on one sheet. First cook is
   chord–chord. This module packages Accepted ADR-0007 chord 𝓘 and
   one cook step (or a finite locked bag of one-steps) as the
   NodingNG API — not a remint of SheetHenCook, not OverlayNG, not
   RelateNG, not a DCEL kernel, not a Geometry subclass.

   QED: two chord eggs on one sheet, an 𝓘 result, and one cook
   step yield NodedOnSheet evidence. Empty ≠ Decline. Snap ≠ 𝓘.
   Identity is structural (ShareOne / MintTwo). A locked two-pair
   bag (Hit cook + Empty no-mint) is still pairwise / one-step.

   QEX: the full repeat-until-noded bag loop stays LoopObligation.
   Cite Parks ρ — CookLoopBagTerm missing; leftover_quad width
   conserved. Do not fake LoopDischarged. NodingNG chord is not
   a bag noder.

   Parks Γ / ι / ρ (named QEX, landed). This letter cites ρ; it
   does not remint CircGamma, ι, or leftover_width. First cook
   stays chord–chord. Host CircGamma stays QEX. Shewchuk A–D /
   Hobby / Priest / Jordan are not dependencies. No H⊥ / Multi
   Landed / Phase B done-when / SQL/MM cathedral / MerkatorBV /
   522-n.

   ADR-0007 is Accepted (2026-09-07). This letter does not reopen
   Status. QEX is not a new Accept cycle.

   Testable 𝓘 / cook results sit on the accepted Oracle line
   protocol (ADR-0006). This module mints no keyword and no
   second external seam.

   WITNESS topic: overlay · claimId: 0007-nodingng-chord
   witness: 0007-nodingng-chord
   board: ADR-0007
   3-axiom host. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import Distance SheetHenCook SheetHenCookLoop.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Product face: a NodingNG chord pair is two chickens on one sheet           *)
(* whose eggs are chords and whose 𝓘 result inhabits I_ok.                    *)
(* -------------------------------------------------------------------------- *)

Record NodingNGChordPair : Type := mkNodingNGChordPair {
  nng_sheet : Sheet;
  nng_c1 : Chicken;
  nng_c2 : Chicken;
  nng_I : IResult;
  nng_ok : I_ok (ck_egg nng_c1) (ck_egg nng_c2) nng_I
}.

(* NodedOnSheet is cook evidence: the pair's I_ok is the witness. *)
Definition nodingng_noded (p : NodingNGChordPair) : NodedOnSheet :=
  mkNoded (nng_sheet p)
    (mkCookWitness (ck_egg (nng_c1 p)) (ck_egg (nng_c2 p))
                   (nng_I p) (nng_ok p)).

Lemma nodingng_noded_carries_I_ok :
  forall p : NodingNGChordPair,
    I_ok (cw_e1 (noded_cook (nodingng_noded p)))
         (cw_e2 (noded_cook (nodingng_noded p)))
         (cw_result (noded_cook (nodingng_noded p))).
Proof.
  intros p.
  exact (nng_ok p).
Qed.

Lemma nodingng_noded_same_sheet :
  forall p : NodingNGChordPair,
    noded_sheet (nodingng_noded p) = nng_sheet p.
Proof.
  intros p. reflexivity.
Qed.

(* Hit cook: 𝓘 Hit plus one try_cook_hit step sharing the minted hen. *)
Definition nodingng_hit_cooks (p : NodingNGChordPair) (h : Hen) : Prop :=
  (exists pt ti tj, nng_I p = IHit pt ti tj) /\
  (exists cp : CookedPair,
     try_cook_hit (nng_c1 p) (nng_c2 p) (nng_I p) h = Some cp /\
     cooked_shares_hen cp /\
     cp_hen cp = h).

(* Empty: 𝓘 Empty, no hen minted, still noded-on-S. *)
Definition nodingng_empty_no_mint (p : NodingNGChordPair) : Prop :=
  nng_I p = IEmpty /\
  (forall h, try_cook_hit (nng_c1 p) (nng_c2 p) IEmpty h = None).

(* -------------------------------------------------------------------------- *)
(* Locked crossing inhabitant (unit-square diagonals). Reuses SheetHenCook.   *)
(* -------------------------------------------------------------------------- *)

Definition nodingng_crossing_pair : NodingNGChordPair :=
  mkNodingNGChordPair default_sheet crossing_ck1 crossing_ck2
    (IHit cross_pt (1 / 2) (1 / 2)) crossing_I_ok.

Definition nodingng_crossing_noded : NodedOnSheet :=
  nodingng_noded nodingng_crossing_pair.

Lemma nodingng_crossing_eggs_are_chords :
  egg_class (ck_egg (nng_c1 nodingng_crossing_pair)) = EggChord /\
  egg_class (ck_egg (nng_c2 nodingng_crossing_pair)) = EggChord.
Proof.
  split; reflexivity.
Qed.

Lemma nodingng_crossing_hit_cooks :
  nodingng_hit_cooks nodingng_crossing_pair crossing_hen.
Proof.
  split.
  - exists cross_pt, (1 / 2), (1 / 2). reflexivity.
  - exists cooked_crossing.
    split; [exact cooked_crossing_try|].
    split; [exact cooked_crossing_shares|].
    reflexivity.
Qed.

Lemma nodingng_crossing_is_noded :
  noded_sheet nodingng_crossing_noded = default_sheet /\
  I_ok (cw_e1 (noded_cook nodingng_crossing_noded))
       (cw_e2 (noded_cook nodingng_crossing_noded))
       (cw_result (noded_cook nodingng_crossing_noded)).
Proof.
  split; [reflexivity|].
  exact (nodingng_noded_carries_I_ok nodingng_crossing_pair).
Qed.

(* General chord-chord Hit: 𝓘 + one cook step packages NodedOnSheet. *)
Lemma nodingng_chord_hit_packages_noded :
  forall (s : Sheet) (c1 c2 : Chicken) (e1 e2 : ChordEgg) p ti tj h,
    ck_egg c1 = MkChord e1 ->
    ck_egg c2 = MkChord e2 ->
    forall (Hok : I_ok (MkChord e1) (MkChord e2) (IHit p ti tj)),
      exists (cp : CookedPair) (n : NodedOnSheet),
        try_cook_hit c1 c2 (IHit p ti tj) h = Some cp /\
        cooked_shares_hen cp /\
        cp_hen cp = h /\
        noded_sheet n = s /\
        I_ok (cw_e1 (noded_cook n)) (cw_e2 (noded_cook n))
             (cw_result (noded_cook n)).
Proof.
  intros s c1 c2 e1 e2 p ti tj h He1 He2 Hok.
  destruct (try_cook_hit_chord_hit_some c1 c2 e1 e2 p ti tj h He1 He2)
    as [cp [Htry [Hshare Hhen]]].
  exists cp.
  exists (mkNoded s (mkCookWitness (MkChord e1) (MkChord e2)
                                   (IHit p ti tj) Hok)).
  split; [exact Htry|].
  split; [exact Hshare|].
  split; [exact Hhen|].
  split; [reflexivity|].
  exact Hok.
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked Empty inhabitant (disjoint horizontals). No hen minted.             *)
(* -------------------------------------------------------------------------- *)

Definition nodingng_disjoint_ck1 : Chicken :=
  mkChicken 0%nat 1%nat (MkChord hor_bot).
Definition nodingng_disjoint_ck2 : Chicken :=
  mkChicken 2%nat 3%nat (MkChord hor_top).

Definition nodingng_disjoint_pair : NodingNGChordPair :=
  mkNodingNGChordPair default_sheet nodingng_disjoint_ck1 nodingng_disjoint_ck2
    IEmpty disjoint_I_ok.

Definition nodingng_disjoint_noded : NodedOnSheet :=
  nodingng_noded nodingng_disjoint_pair.

Lemma nodingng_disjoint_empty_no_mint :
  nodingng_empty_no_mint nodingng_disjoint_pair.
Proof.
  split; [reflexivity|].
  intros h.
  apply try_cook_hit_empty_none.
Qed.

Lemma nodingng_disjoint_is_noded :
  noded_sheet nodingng_disjoint_noded = default_sheet /\
  cw_result (noded_cook nodingng_disjoint_noded) = IEmpty /\
  I_ok (cw_e1 (noded_cook nodingng_disjoint_noded))
       (cw_e2 (noded_cook nodingng_disjoint_noded))
       (cw_result (noded_cook nodingng_disjoint_noded)).
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  exact (nodingng_noded_carries_I_ok nodingng_disjoint_pair).
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked two-pair bag of one-steps: Hit cook + Empty no-mint, one sheet.     *)
(* Finite locked bag — not the repeat-until-noded loop.                       *)
(* -------------------------------------------------------------------------- *)

Record NodingNGLockedBag : Type := mkNodingNGLockedBag {
  nng_bag_sheet : Sheet;
  nng_hit : NodingNGChordPair;
  nng_empty : NodingNGChordPair
}.

Definition nodingng_locked_bag : NodingNGLockedBag :=
  mkNodingNGLockedBag default_sheet
    nodingng_crossing_pair nodingng_disjoint_pair.

Definition nodingng_locked_bag_ok (b : NodingNGLockedBag) : Prop :=
  nng_sheet (nng_hit b) = nng_bag_sheet b /\
  nng_sheet (nng_empty b) = nng_bag_sheet b /\
  nodingng_hit_cooks (nng_hit b) crossing_hen /\
  nodingng_empty_no_mint (nng_empty b).

Lemma nodingng_locked_bag_inhabits :
  nodingng_locked_bag_ok nodingng_locked_bag.
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact nodingng_crossing_hit_cooks|].
  exact nodingng_disjoint_empty_no_mint.
Qed.

(* -------------------------------------------------------------------------- *)
(* NodingNG laws reused from SheetHenCook: Empty ≠ Decline, snap ≠ 𝓘,        *)
(* ShareOne / MintTwo structural. Not OverlayNG. Not a bag noder.             *)
(* -------------------------------------------------------------------------- *)

Lemma nodingng_empty_neq_decline : IEmpty <> IDecline.
Proof.
  exact IEmpty_neq_IDecline.
Qed.

Lemma nodingng_snap_neq_I : CtorSnapRound <> CtorI.
Proof.
  exact snap_round_neq_I.
Qed.

Lemma nodingng_share_one_same_hen :
  forall h : Hen,
    fst (apply_id_decision (ShareOne h)) =
    snd (apply_id_decision (ShareOne h)).
Proof.
  exact share_one_same_hen.
Qed.

Lemma nodingng_mint_two_may_differ :
  exists a b : Hen,
    fst (apply_id_decision (MintTwo a b)) <>
    snd (apply_id_decision (MintTwo a b)).
Proof.
  exact mint_two_may_differ.
Qed.

Lemma nodingng_not_overlay_ng_robust :
  CtorSnapRound <> CtorI /\
  (forall (s : Sheet) (n : nat), overlay_ng_robust_is_finite_snap s n).
Proof.
  split; [exact overlay_ng_robust_is_snap_not_I|].
  exact overlay_ng_robust_is_finite_snap_holds.
Qed.

(* What NodingNG is / is not. Kind tag, not a second kernel. *)
Inductive NodingNGKind : Type :=
| NNG_I_plus_cook
| NNG_OverlayNG
| NNG_RelateNG
| NNG_LoopNoder.

Definition nodingng_kind : NodingNGKind := NNG_I_plus_cook.

Lemma nodingng_is_I_plus_cook : nodingng_kind = NNG_I_plus_cook.
Proof.
  reflexivity.
Qed.

Lemma nodingng_not_overlayng : nodingng_kind <> NNG_OverlayNG.
Proof.
  discriminate.
Qed.

Lemma nodingng_not_relateng : nodingng_kind <> NNG_RelateNG.
Proof.
  discriminate.
Qed.

Lemma nodingng_not_loop_noder : nodingng_kind <> NNG_LoopNoder.
Proof.
  discriminate.
Qed.

Inductive NodingNGLetterStatus : Type :=
| NodingNGChordLanded
| NodingNGLoopDischarged.

Definition nodingng_letter_status : NodingNGLetterStatus :=
  NodingNGChordLanded.

Lemma nodingng_letter_is_landed :
  nodingng_letter_status = NodingNGChordLanded /\
  cook_loop_status = LoopObligation /\
  cook_loop_status <> LoopDischarged.
Proof.
  split; [reflexivity|].
  split; [exact cook_loop_is_obligation|exact cook_loop_not_discharged].
Qed.

(* Named QED package: the chord inhabitant + laws. *)
Lemma nodingng_chord_inhabits :
  first_cook_scope EggChord EggChord /\
  nodingng_hit_cooks nodingng_crossing_pair crossing_hen /\
  noded_sheet nodingng_crossing_noded = default_sheet /\
  I_ok (cw_e1 (noded_cook nodingng_crossing_noded))
       (cw_e2 (noded_cook nodingng_crossing_noded))
       (cw_result (noded_cook nodingng_crossing_noded)) /\
  nodingng_empty_no_mint nodingng_disjoint_pair /\
  IEmpty <> IDecline /\
  CtorSnapRound <> CtorI /\
  (forall h : Hen,
     fst (apply_id_decision (ShareOne h)) =
     snd (apply_id_decision (ShareOne h))) /\
  (exists a b : Hen,
     fst (apply_id_decision (MintTwo a b)) <>
     snd (apply_id_decision (MintTwo a b))) /\
  nodingng_locked_bag_ok nodingng_locked_bag /\
  nodingng_kind = NNG_I_plus_cook.
Proof.
  split; [exact first_cook_scope_chord_chord|].
  split; [exact nodingng_crossing_hit_cooks|].
  split; [reflexivity|].
  split; [exact (nodingng_noded_carries_I_ok nodingng_crossing_pair)|].
  split; [exact nodingng_disjoint_empty_no_mint|].
  split; [exact nodingng_empty_neq_decline|].
  split; [exact nodingng_snap_neq_I|].
  split; [exact nodingng_share_one_same_hen|].
  split; [exact nodingng_mint_two_may_differ|].
  split; [exact nodingng_locked_bag_inhabits|].
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-nodingng-chord","topic":"overlay","lemma":"ticket_0007_nodingng_chord_qed_or_qex","title":"NodingNG chord is I plus one cook step yielding NodedOnSheet (QED) or first cook is not chord-chord (QEX); discharged QED; Empty != Decline; snap != I; ShareOne/MintTwo structural; locked two-pair bag of one-steps","file":"theories/NodingNG.v","witness":"0007-nodingng-chord","board":"ADR-0007"} *)
Theorem ticket_0007_nodingng_chord_qed_or_qex :
  (first_cook_scope EggChord EggChord /\
   nodingng_hit_cooks nodingng_crossing_pair crossing_hen /\
   noded_sheet nodingng_crossing_noded = default_sheet /\
   I_ok (cw_e1 (noded_cook nodingng_crossing_noded))
        (cw_e2 (noded_cook nodingng_crossing_noded))
        (cw_result (noded_cook nodingng_crossing_noded)) /\
   nodingng_empty_no_mint nodingng_disjoint_pair /\
   IEmpty <> IDecline /\
   CtorSnapRound <> CtorI /\
   (forall h : Hen,
      fst (apply_id_decision (ShareOne h)) =
      snd (apply_id_decision (ShareOne h))) /\
   (exists a b : Hen,
      fst (apply_id_decision (MintTwo a b)) <>
      snd (apply_id_decision (MintTwo a b))) /\
   nodingng_locked_bag_ok nodingng_locked_bag /\
   nodingng_kind = NNG_I_plus_cook /\
   nodingng_kind <> NNG_OverlayNG /\
   nodingng_kind <> NNG_RelateNG)
  \/
  ~ first_cook_scope EggChord EggChord.
Proof.
  left.
  destruct nodingng_chord_inhabits as [Hscope Hrest].
  split; [exact Hscope|].
  destruct Hrest as [Hcook Hrest].
  split; [exact Hcook|].
  destruct Hrest as [Hsheet Hrest].
  split; [exact Hsheet|].
  destruct Hrest as [Hok Hrest].
  split; [exact Hok|].
  destruct Hrest as [Hempty Hrest].
  split; [exact Hempty|].
  destruct Hrest as [Hneq Hrest].
  split; [exact Hneq|].
  destruct Hrest as [Hsnap Hrest].
  split; [exact Hsnap|].
  destruct Hrest as [Hshare Hrest].
  split; [exact Hshare|].
  destruct Hrest as [Hmint Hrest].
  split; [exact Hmint|].
  destruct Hrest as [Hbag Hkind].
  split; [exact Hbag|].
  split; [exact Hkind|].
  split; [exact nodingng_not_overlayng|].
  exact nodingng_not_relateng.
Qed.

(* Parks ρ: NodingNG chord is pairwise / one-step, not LoopDischarged.
   Cite leftover_quad_width_conserved / CookLoopBagTerm missing.
   Do not fake Discharge. *)
(* WITNESS {"claimId":"0007-nodingng-chord","topic":"overlay","lemma":"ticket_0007_nodingng_rho_qed_or_qex","title":"NodingNG chord discharges the bag-level repeat-until-noded loop (QED) or stays pairwise/one-step while Parks rho CookLoopBagTerm is missing (QEX); discharged QEX; leftover_quad width conserved","file":"theories/NodingNG.v","witness":"0007-nodingng-chord","board":"ADR-0007"} *)
Theorem ticket_0007_nodingng_rho_qed_or_qex :
  (nodingng_letter_status = NodingNGLoopDischarged
   /\ cook_loop_status = LoopDischarged
   /\ cook_loop_ctor_inhabits CookLoopBagTerm)
  \/
  (nodingng_letter_status = NodingNGChordLanded
   /\ cook_loop_status = LoopObligation
   /\ ~ cook_loop_ctor_inhabits CookLoopBagTerm
   /\ (forall ti tj,
         0 < ti < 1 ->
         0 < tj < 1 ->
         leftover_quad_width ti tj =
         leftover_width 0 1 + leftover_width 0 1)
   /\ nodingng_kind = NNG_I_plus_cook
   /\ nodingng_kind <> NNG_LoopNoder
   /\ nodingng_locked_bag_ok nodingng_locked_bag).
Proof.
  right.
  split; [reflexivity|].
  split; [exact cook_loop_is_obligation|].
  split; [exact cook_loop_bag_term_missing|].
  split; [exact leftover_quad_width_conserved|].
  split; [exact nodingng_is_I_plus_cook|].
  split; [exact nodingng_not_loop_noder|].
  exact nodingng_locked_bag_inhabits.
Qed.

(* Scope fence: NodingNG stays chord product + LoopObligation. Host
   first cook includes circular / clothoid; NURBS stays out. *)
(* WITNESS {"claimId":"0007-nodingng-chord","topic":"overlay","lemma":"ticket_0007_nodingng_scope_qed_or_qex","title":"NodingNG discharges the bag loop (QED) or stays pairwise/one-step while host first cook includes chord/circular/clothoid and NURBS stays out (QEX); discharged QEX","file":"theories/NodingNG.v","witness":"0007-nodingng-chord","board":"ADR-0007"} *)
Theorem ticket_0007_nodingng_scope_qed_or_qex :
  (first_cook_scope EggCircularArc EggCircularArc
   /\ first_cook_scope EggClothoid EggClothoid
   /\ cook_loop_status = LoopDischarged)
  \/
  (first_cook_scope EggChord EggChord
   /\ first_cook_scope EggCircularArc EggCircularArc
   /\ first_cook_scope EggClothoid EggClothoid
   /\ ~ first_cook_scope EggNurbs EggNurbs
   /\ cook_loop_status = LoopObligation
   /\ nodingng_letter_status = NodingNGChordLanded).
Proof.
  right.
  split; [exact first_cook_scope_chord_chord|].
  split; [exact circular_egg_first_cook_scope|].
  split; [exact clothoid_egg_first_cook_scope|].
  split; [exact nurbs_nurbs_not_first_scope|].
  split; [exact cook_loop_is_obligation|].
  reflexivity.
Qed.

Print Assumptions nodingng_noded_carries_I_ok.
Print Assumptions nodingng_crossing_hit_cooks.
Print Assumptions nodingng_chord_hit_packages_noded.
Print Assumptions nodingng_disjoint_empty_no_mint.
Print Assumptions nodingng_locked_bag_inhabits.
Print Assumptions nodingng_chord_inhabits.
Print Assumptions ticket_0007_nodingng_chord_qed_or_qex.
Print Assumptions ticket_0007_nodingng_rho_qed_or_qex.
Print Assumptions ticket_0007_nodingng_scope_qed_or_qex.
