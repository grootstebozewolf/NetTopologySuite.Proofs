(* ============================================================================
   NetTopologySuite.Proofs.SheetHenCookLoopTerm
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: Parks ρ leftover-bag term measure
   (claimId 0007-rho-bag-term-measure).

   Reuses leftover_span_bag / leftover_bag_step / leftover_pair_step_ok
   from SheetHenCookLoopModulo.v (#760). Does not remint those tickets
   as LoopDischarged.

   leftover_bag_term_measure is the count of unordered distinct index
   pairs (i,j) for which leftover_pair_step_ok exists (interior 𝓘 Hit).
   That nat is well-founded. It is not leftover_quad_width (the bag-sum
   stays conserved; leftover_quad_width_decreases stays uninhabited).

   QED: measure + LStepHit strictly decreases it + LStepDecline is idle.
   Locked unit-square diag_ab × diag_cd: parent measure 1; after Hit,
   quad measure 0 (join pair Declines; no invented extra Hits).
   QEX: leftover_quad_kiss_arm, leftover_quad_share_mint_arm,
   LeftoverBagTermArm as a whole, cook_loop_status = LoopObligation.

   Honesty fences:
     Do not fake LoopDischarged. Do not remint I.8 / pairwise width as
     bag discharge. Do not remint kiss/share as width. Do not remint
     leftover_quad_width as this measure. Do not remint CircGamma / ι /
     mixed_joint_params / first_cook expand / Multi bags as ρ.
     Host CircGamma is CircGammaDischarged (MkCirc). First cook stays
     chord–chord. NURBS-span γ campaign is BELAYED — this letter does
     not touch NURBS / MkNurbs γ / NURBS 𝓘.

   WITNESS topic: overlay · claimId: 0007-rho-bag-term-measure
   witness: 0007-rho-bag-term-measure
   board: ADR-0007
   3-axiom host. No Axiom / Parameter / stub.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra Arith Lia List.
From NTS.Proofs Require Import Distance SheetHenCook SheetHenCookLoop.
From NTS.Proofs Require Import SheetHenCookLoopModulo.
Import ListNotations.
Local Open Scope R_scope.

(* WITNESS: campaign=rho rung=bag-term-measure claim=0007-rho-bag-term-measure
   file=theories/SheetHenCookLoopTerm.v
   kind=QED-measure-modulo-named-park
   park=LeftoverBagTermArm
   not=LoopDischarged,leftover_quad_width-measure,I.8-bag-Discharge
   not=kiss-share-as-width,CRV-TOUCH,CircGamma-remint,Multi-bags
   not=first-cook-expand,NURBS,MkNurbs,nurbs-I
   note=measure-letter-not-rho-discharge *)

(* -------------------------------------------------------------------------- *)
(* leftover_bag_term_measure: unordered leftover_hit_pair count.              *)
(* -------------------------------------------------------------------------- *)

Definition leftover_hit_pair (b : leftover_span_bag) (i j : nat) : Prop :=
  (i < j)%nat /\
  exists p ua ub, leftover_pair_step_ok b i j p ua ub.

Definition leftover_hit_listing (b : leftover_span_bag)
  (hits : list (nat * nat)) : Prop :=
  (forall ij, In ij hits -> leftover_hit_pair b (fst ij) (snd ij)) /\
  (forall i j, leftover_hit_pair b i j -> In (i, j) hits) /\
  NoDup hits.

Definition leftover_bag_term_measure (b : leftover_span_bag) (n : nat) : Prop :=
  exists hits, leftover_hit_listing b hits /\ length hits = n.

Lemma leftover_bag_term_measure_nat_wf :
  well_founded Nat.lt.
Proof.
  exact Nat.lt_wf_0.
Qed.

Lemma leftover_pair_hit_sym :
  forall a b p ua ub,
    leftover_pair_hit a b p ua ub ->
    leftover_pair_hit b a p ub ua.
Proof.
  intros a bsp p ua ub [Hoka [Hokb [Hua [Hub Hok]]]].
  unfold leftover_pair_hit.
  split; [exact Hokb|].
  split; [exact Hoka|].
  split; [exact Hub|].
  split; [exact Hua|].
  unfold I_ok in Hok.
  destruct (leftover_egg a) as [ap0 ap1].
  destruct (leftover_egg bsp) as [bp0 bp1].
  unfold on_chord in Hok.
  destruct Hok as [Ha Hb].
  unfold I_ok, on_chord.
  split; [exact Hb|exact Ha].
Qed.

Lemma leftover_pair_step_ok_sym :
  forall b i j p ua ub,
    leftover_pair_step_ok b i j p ua ub ->
    leftover_pair_step_ok b j i p ub ua.
Proof.
  intros b i j p ua ub [a [bsp [Ha [Hb [Hne Hhit]]]]].
  exists bsp, a.
  split; [exact Hb|].
  split; [exact Ha|].
  split; [apply not_eq_sym; exact Hne|].
  apply leftover_pair_hit_sym.
  exact Hhit.
Qed.

Lemma leftover_pair_step_ok_hit_pair :
  forall b i j p ua ub,
    leftover_pair_step_ok b i j p ua ub ->
    leftover_hit_pair b (Nat.min i j) (Nat.max i j).
Proof.
  intros b i j p ua ub Hok.
  destruct (Nat.lt_trichotomy i j) as [Hlt | [Heq | Hgt]].
  - rewrite (Nat.min_l i j (Nat.lt_le_incl _ _ Hlt)).
    rewrite (Nat.max_r i j (Nat.lt_le_incl _ _ Hlt)).
    split; [exact Hlt|].
    exists p, ua, ub.
    exact Hok.
  - destruct Hok as [_ [_ [_ [_ [Hne _]]]]].
    congruence.
  - rewrite (Nat.min_r i j (Nat.lt_le_incl _ _ Hgt)).
    rewrite (Nat.max_l i j (Nat.lt_le_incl _ _ Hgt)).
    split; [exact Hgt|].
    exists p, ub, ua.
    apply leftover_pair_step_ok_sym.
    exact Hok.
Qed.

Lemma lbag_nth_some_lt :
  forall b n s,
    lbag_nth b n = Some s ->
    (n < lbag_count b)%nat.
Proof.
  induction b as [|s0 rest IH]; intros n s Hnth.
  - discriminate.
  - destruct n as [|n'].
    + simpl. lia.
    + simpl in Hnth.
      apply IH in Hnth.
      simpl. lia.
Qed.

Lemma leftover_hit_pair_bounded :
  forall b i j,
    leftover_hit_pair b i j ->
    (i < j < lbag_count b)%nat.
Proof.
  intros b i j [Hij [p [ua [ub [a [bsp [Ha [Hb _]]]]]]]].
  split; [exact Hij|].
  apply lbag_nth_some_lt in Hb.
  exact Hb.
Qed.

Lemma leftover_hit_listing_same_in :
  forall b h1 h2 ij,
    leftover_hit_listing b h1 ->
    leftover_hit_listing b h2 ->
    In ij h1 <-> In ij h2.
Proof.
  intros b h1 h2 ij [Hs1 [Hc1 _]] [Hs2 [Hc2 _]].
  split; intros Hin.
  - apply Hs1 in Hin.
    destruct ij as [i j].
    simpl in Hin.
    apply Hc2.
    exact Hin.
  - apply Hs2 in Hin.
    destruct ij as [i j].
    simpl in Hin.
    apply Hc1.
    exact Hin.
Qed.

Lemma leftover_bag_term_measure_unique :
  forall b n m,
    leftover_bag_term_measure b n ->
    leftover_bag_term_measure b m ->
    n = m.
Proof.
  intros b n m [h1 [L1 E1]] [h2 [L2 E2]].
  subst n m.
  apply Nat.le_antisymm.
  - apply NoDup_incl_length.
    + destruct L1 as [_ [_ N1]]. exact N1.
    + intros x Hx.
      apply (proj1 (leftover_hit_listing_same_in b h1 h2 x L1 L2)).
      exact Hx.
  - apply NoDup_incl_length.
    + destruct L2 as [_ [_ N2]]. exact N2.
    + intros x Hx.
      apply (proj1 (leftover_hit_listing_same_in b h2 h1 x L2 L1)).
      exact Hx.
Qed.

Lemma leftover_bag_term_measure_hit_pos :
  forall b i j p ua ub n,
    leftover_pair_step_ok b i j p ua ub ->
    leftover_bag_term_measure b n ->
    (0 < n)%nat.
Proof.
  intros b i j p ua ub n Hok [hits [[_ [Hc _]] Elen]].
  subst n.
  pose proof (leftover_pair_step_ok_hit_pair b i j p ua ub Hok) as Hpair.
  apply Hc in Hpair.
  destruct hits; [contradiction|].
  simpl. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked quad: every leftover-quad pair Declines (no invented extra Hits).    *)
(* -------------------------------------------------------------------------- *)

Lemma locked_A_hi_egg :
  leftover_egg (mkLeftoverSpan diag_ab (1 / 2) 1) =
  mkChordEgg (mkPoint 1 1) (mkPoint 2 2).
Proof.
  unfold leftover_egg, leftover_half, diag_ab, chord_eval.
  simpl.
  apply (f_equal2 mkChordEgg); apply (f_equal2 mkPoint); field.
Qed.

Lemma locked_B_hi_egg :
  leftover_egg (mkLeftoverSpan diag_cd (1 / 2) 1) =
  mkChordEgg (mkPoint 1 1) (mkPoint 2 0).
Proof.
  unfold leftover_egg, leftover_half, diag_cd, chord_eval.
  simpl.
  apply (f_equal2 mkChordEgg); apply (f_equal2 mkPoint); field.
Qed.

Lemma locked_quad_Alo_Ahi_no_hit :
  forall p ua ub,
    ~ leftover_pair_hit
        (mkLeftoverSpan diag_ab 0 (1 / 2))
        (mkLeftoverSpan diag_ab (1 / 2) 1)
        p ua ub.
Proof.
  intros p ua ub [Hoka [Hokb [Hua [Hub Hok]]]].
  unfold leftover_egg_interior in Hua, Hub.
  rewrite locked_A_lo_egg, locked_A_hi_egg in Hok.
  unfold I_ok, on_chord, chord_eval in Hok.
  destruct Hok as [[_ Ha] [_ Hb]].
  simpl in Ha, Hb.
  rewrite Ha in Hb.
  inversion Hb.
  lra.
Qed.

Lemma locked_quad_Alo_Bhi_no_hit :
  forall p ua ub,
    ~ leftover_pair_hit
        (mkLeftoverSpan diag_ab 0 (1 / 2))
        (mkLeftoverSpan diag_cd (1 / 2) 1)
        p ua ub.
Proof.
  intros p ua ub [Hoka [Hokb [Hua [Hub Hok]]]].
  unfold leftover_egg_interior in Hua, Hub.
  rewrite locked_A_lo_egg, locked_B_hi_egg in Hok.
  unfold I_ok, on_chord, chord_eval in Hok.
  destruct Hok as [[_ Ha] [_ Hb]].
  simpl in Ha, Hb.
  rewrite Ha in Hb.
  inversion Hb.
  lra.
Qed.

Lemma locked_quad_Ahi_Blo_no_hit :
  forall p ua ub,
    ~ leftover_pair_hit
        (mkLeftoverSpan diag_ab (1 / 2) 1)
        (mkLeftoverSpan diag_cd 0 (1 / 2))
        p ua ub.
Proof.
  intros p ua ub [Hoka [Hokb [Hua [Hub Hok]]]].
  unfold leftover_egg_interior in Hua, Hub.
  rewrite locked_A_hi_egg, locked_B_lo_egg in Hok.
  unfold I_ok, on_chord, chord_eval in Hok.
  destruct Hok as [[_ Ha] [_ Hb]].
  simpl in Ha, Hb.
  rewrite Ha in Hb.
  inversion Hb.
  lra.
Qed.

Lemma locked_quad_Ahi_Bhi_no_hit :
  forall p ua ub,
    ~ leftover_pair_hit
        (mkLeftoverSpan diag_ab (1 / 2) 1)
        (mkLeftoverSpan diag_cd (1 / 2) 1)
        p ua ub.
Proof.
  intros p ua ub [Hoka [Hokb [Hua [Hub Hok]]]].
  unfold leftover_egg_interior in Hua, Hub.
  rewrite locked_A_hi_egg, locked_B_hi_egg in Hok.
  unfold I_ok, on_chord, chord_eval in Hok.
  destruct Hok as [[_ Ha] [_ Hb]].
  simpl in Ha, Hb.
  rewrite Ha in Hb.
  inversion Hb.
  lra.
Qed.

Lemma locked_quad_Blo_Bhi_no_hit :
  forall p ua ub,
    ~ leftover_pair_hit
        (mkLeftoverSpan diag_cd 0 (1 / 2))
        (mkLeftoverSpan diag_cd (1 / 2) 1)
        p ua ub.
Proof.
  intros p ua ub [Hoka [Hokb [Hua [Hub Hok]]]].
  unfold leftover_egg_interior in Hua, Hub.
  rewrite locked_B_lo_egg, locked_B_hi_egg in Hok.
  unfold I_ok, on_chord, chord_eval in Hok.
  destruct Hok as [[_ Ha] [_ Hb]].
  simpl in Ha, Hb.
  rewrite Ha in Hb.
  inversion Hb.
  lra.
Qed.

Lemma locked_quad_nth :
  lbag_nth locked_quad_bag 0 = Some (mkLeftoverSpan diag_ab 0 (1 / 2)) /\
  lbag_nth locked_quad_bag 1 = Some (mkLeftoverSpan diag_ab (1 / 2) 1) /\
  lbag_nth locked_quad_bag 2 = Some (mkLeftoverSpan diag_cd 0 (1 / 2)) /\
  lbag_nth locked_quad_bag 3 = Some (mkLeftoverSpan diag_cd (1 / 2) 1).
Proof.
  repeat split; reflexivity.
Qed.

Lemma locked_quad_no_hit_pair :
  forall i j, ~ leftover_hit_pair locked_quad_bag i j.
Proof.
  intros i j [Hij [p [ua [ub [a [bsp [Ha [Hb [Hne Hhit]]]]]]]]].
  pose proof (lbag_nth_some_lt locked_quad_bag i a Ha) as Hi.
  pose proof (lbag_nth_some_lt locked_quad_bag j bsp Hb) as Hj.
  change (lbag_count locked_quad_bag) with 4%nat in Hi, Hj.
  destruct locked_quad_nth as [H0 [H1 [H2 H3]]].
  destruct i as [|i0].
  - destruct j as [|j0]; [lia|].
    destruct j0 as [|j1].
    + rewrite H0 in Ha. rewrite H1 in Hb.
      inversion Ha. inversion Hb. subst a bsp.
      exact (locked_quad_Alo_Ahi_no_hit p ua ub Hhit).
    + destruct j1 as [|j2].
      * rewrite H0 in Ha. rewrite H2 in Hb.
        inversion Ha. inversion Hb. subst a bsp.
        exact (locked_quad_pair_no_interior_hit p ua ub Hhit).
      * destruct j2 as [|j3]; [|lia].
        rewrite H0 in Ha. rewrite H3 in Hb.
        inversion Ha. inversion Hb. subst a bsp.
        exact (locked_quad_Alo_Bhi_no_hit p ua ub Hhit).
  - destruct i0 as [|i1].
    + destruct j as [|j0]; [lia|].
      destruct j0 as [|j1]; [lia|].
      destruct j1 as [|j2].
      * rewrite H1 in Ha. rewrite H2 in Hb.
        inversion Ha. inversion Hb. subst a bsp.
        exact (locked_quad_Ahi_Blo_no_hit p ua ub Hhit).
      * destruct j2 as [|j3]; [|lia].
        rewrite H1 in Ha. rewrite H3 in Hb.
        inversion Ha. inversion Hb. subst a bsp.
        exact (locked_quad_Ahi_Bhi_no_hit p ua ub Hhit).
    + destruct i1 as [|i2]; [|lia].
      destruct j as [|j0]; [lia|].
      destruct j0 as [|j1]; [lia|].
      destruct j1 as [|j2]; [lia|].
      destruct j2 as [|j3]; [|lia].
      rewrite H2 in Ha. rewrite H3 in Hb.
      inversion Ha. inversion Hb. subst a bsp.
      exact (locked_quad_Blo_Bhi_no_hit p ua ub Hhit).
Qed.

(* -------------------------------------------------------------------------- *)
(* Locked inhabitance: parent measure 1; after Hit, quad measure 0.           *)
(* -------------------------------------------------------------------------- *)

Lemma locked_parent_term_measure :
  leftover_bag_term_measure locked_parent_bag 1.
Proof.
  exists [(0, 1)%nat].
  split; [|reflexivity].
  split.
  - intros ij Hin.
    destruct Hin as [Heq | Hnil]; [|contradiction].
    inversion Heq.
    subst ij.
    simpl.
    split; [lia|].
    exists cross_pt, (1 / 2), (1 / 2).
    exact locked_parent_step_ok.
  - split.
    + intros i j Hpair.
      pose proof (leftover_hit_pair_bounded locked_parent_bag i j Hpair) as Hbnd.
      change (lbag_count locked_parent_bag) with 2%nat in Hbnd.
      assert (i = 0%nat /\ j = 1%nat) as [Hi Hj] by lia.
      subst i j.
      left. reflexivity.
    + apply NoDup_cons.
      * intros H. inversion H.
      * apply NoDup_nil.
Qed.

Lemma locked_quad_term_measure :
  leftover_bag_term_measure locked_quad_bag 0.
Proof.
  exists [].
  split; [|reflexivity].
  split.
  - intros ij Hin. contradiction.
  - split.
    + intros i j Hpair.
      exact (locked_quad_no_hit_pair i j Hpair).
    + apply NoDup_nil.
Qed.

Lemma leftover_bag_term_measure_hit_decreases :
  forall n m,
    leftover_bag_step locked_parent_bag locked_quad_bag ->
    leftover_bag_term_measure locked_parent_bag n ->
    leftover_bag_term_measure locked_quad_bag m ->
    (m < n)%nat.
Proof.
  intros n m _ Hn Hm.
  pose proof (leftover_bag_term_measure_unique
                locked_parent_bag n 1 Hn locked_parent_term_measure) as En.
  pose proof (leftover_bag_term_measure_unique
                locked_quad_bag m 0 Hm locked_quad_term_measure) as Em.
  subst n m.
  lia.
Qed.

Lemma leftover_bag_term_measure_decline_idle :
  forall b i j n,
    leftover_pair_decline b i j ->
    leftover_bag_step b b /\
    (leftover_bag_term_measure b n -> leftover_bag_term_measure b n).
Proof.
  intros b i j n Hd.
  split.
  - apply (LStepDecline b i j Hd).
  - intros Hm. exact Hm.
Qed.

Lemma leftover_bag_term_measure_locked_decline_idle :
  leftover_bag_step locked_quad_bag locked_quad_bag /\
  leftover_bag_term_measure locked_quad_bag 0.
Proof.
  split.
  - exact locked_decline_step.
  - exact locked_quad_term_measure.
Qed.

Lemma leftover_bag_term_measure_sum_conserved :
  leftover_bag_term_measure locked_parent_bag 1 /\
  leftover_bag_term_measure locked_quad_bag 0 /\
  lbag_sum locked_quad_bag = lbag_sum locked_parent_bag.
Proof.
  split; [exact locked_parent_term_measure|].
  split; [exact locked_quad_term_measure|].
  exact locked_hit_sum.
Qed.

Lemma leftover_term_park_unchanged :
  cook_loop_status = LoopObligation /\
  cook_loop_status <> LoopDischarged /\
  ~ leftover_bag_term_arm /\
  LeftoverBagTermArm = leftover_bag_term_arm /\
  leftover_bag_term_arm =
    (leftover_quad_width_decreases
     /\ leftover_quad_kiss_arm
     /\ leftover_quad_share_mint_arm) /\
  ~ leftover_quad_width_decreases /\
  ~ leftover_quad_kiss_arm /\
  ~ leftover_quad_share_mint_arm.
Proof.
  split; [exact cook_loop_is_obligation|].
  split; [exact cook_loop_not_discharged|].
  split; [exact leftover_bag_term_arm_missing|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact leftover_quad_width_does_not_decrease|].
  split; [exact leftover_quad_kiss_arm_missing|].
  exact leftover_quad_share_mint_arm_missing.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stops.                                              *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-rho-bag-term-measure","topic":"overlay","lemma":"ticket_0007_rho_bag_term_measure_qed_or_qex","title":"rho bag-term measure: leftover_bag_term_measure is the leftover_hit_pair count (unordered interior 𝓘 Hits); LStepHit strictly decreases it 1 to 0 on locked diag_ab x diag_cd and LStepDecline is idle (QED) or leftover_quad_width_decreases (QEX); discharged QED; bag-sum may stay conserved; not leftover_quad_width; no invented extra Hits","file":"theories/SheetHenCookLoopTerm.v","witness":"0007-rho-bag-term-measure","board":"ADR-0007"} *)
Theorem ticket_0007_rho_bag_term_measure_qed_or_qex :
  (leftover_bag_term_measure locked_parent_bag 1 /\
   leftover_bag_term_measure locked_quad_bag 0 /\
   leftover_bag_step locked_parent_bag locked_quad_bag /\
   leftover_pair_step_ok locked_parent_bag 0 1
     cross_pt (1 / 2) (1 / 2) /\
   (0 < 1)%nat /\
   leftover_bag_step locked_quad_bag locked_quad_bag /\
   leftover_pair_decline locked_quad_bag 0 2 /\
   leftover_bag_term_measure locked_quad_bag 0 /\
   lbag_sum locked_quad_bag = lbag_sum locked_parent_bag /\
   well_founded Nat.lt)
  \/ leftover_quad_width_decreases.
Proof.
  left.
  split; [exact locked_parent_term_measure|].
  split; [exact locked_quad_term_measure|].
  split; [exact locked_hit_step|].
  split; [exact locked_parent_step_ok|].
  split; [lia|].
  split; [exact locked_decline_step|].
  split; [exact locked_quad_decline|].
  split; [exact locked_quad_term_measure|].
  split; [exact locked_hit_sum|].
  exact leftover_bag_term_measure_nat_wf.
Qed.

(* WITNESS {"claimId":"0007-rho-bag-term-measure","topic":"overlay","lemma":"ticket_0007_rho_bag_term_park_qed_or_qex","title":"rho bag-term measure park: LeftoverBagTermArm inhabits leftover_quad_width_decreases and kiss/share/mint leftover-quad rewrites (QED) or that ctor stays missing, leftover_quad_kiss_arm and leftover_quad_share_mint_arm stay uninhabited, and cook_loop stays LoopObligation (QEX); discharged QEX; measure letter is not LoopDischarged; do not remint kiss/share as width","file":"theories/SheetHenCookLoopTerm.v","witness":"0007-rho-bag-term-measure","board":"ADR-0007"} *)
Theorem ticket_0007_rho_bag_term_park_qed_or_qex :
  cook_loop_ctor_inhabits CookLoopBagTerm
  \/
  (cook_loop_status = LoopObligation
   /\ cook_loop_status <> LoopDischarged
   /\ ~ leftover_bag_term_arm
   /\ LeftoverBagTermArm = leftover_bag_term_arm
   /\ leftover_bag_term_arm =
        (leftover_quad_width_decreases
         /\ leftover_quad_kiss_arm
         /\ leftover_quad_share_mint_arm)
   /\ ~ leftover_quad_width_decreases
   /\ ~ leftover_quad_kiss_arm
   /\ ~ leftover_quad_share_mint_arm).
Proof.
  right.
  exact leftover_term_park_unchanged.
Qed.

Print Assumptions leftover_bag_term_measure_nat_wf.
Print Assumptions leftover_pair_hit_sym.
Print Assumptions leftover_pair_step_ok_hit_pair.
Print Assumptions leftover_bag_term_measure_unique.
Print Assumptions leftover_bag_term_measure_hit_pos.
Print Assumptions locked_quad_no_hit_pair.
Print Assumptions locked_parent_term_measure.
Print Assumptions locked_quad_term_measure.
Print Assumptions leftover_bag_term_measure_hit_decreases.
Print Assumptions leftover_bag_term_measure_decline_idle.
Print Assumptions leftover_bag_term_measure_locked_decline_idle.
Print Assumptions leftover_bag_term_measure_sum_conserved.
Print Assumptions leftover_term_park_unchanged.
Print Assumptions ticket_0007_rho_bag_term_measure_qed_or_qex.
Print Assumptions ticket_0007_rho_bag_term_park_qed_or_qex.
