(* ============================================================================
   NetTopologySuite.Proofs.HostRhoLeftoverBagTermQed
   ----------------------------------------------------------------------------
   ADR-0007 letter after Accept: Parks ρ leftover-bag term QED attempt
   (claimId 0007-rho-leftover-bag-term-qed). Stacked on #797
   (HostRhoLeftoverBagTerm.v). Does not remint #798
   (0007-rho-modulo-kiss-share).

   QED would restate LeftoverBagTermArm to a NEW bag measure M
   (not leftover_quad_width, not leftover_quad_width as a bag-sum)
   plus leftover_pair_kiss_ok / leftover_pair_share_mint_ok as
   leftover_bag_step constructors that leftover_bag_cook_fuel consumes,
   prove termination + confluence under M, flip cook_loop_status to
   LoopDischarged, and take the LEFT arm of
   ticket_0007_rho_leftover_qed_or_qex. leftover_quad_width_conserved
   would stay Qed.

   QEX (this letter): no such M exists on leftover_span_bag without
   lying about width. Named failing candidates and tighter holes:
     1. leftover_hit_measure_decreases is uninhabited —
        leftover_bag_term_measure (sibling; used, not reminted as
        Discharge) goes 1 → 2 on an overlap Hit-split of two identical
        leftover_span_parent diag_ab.
     2. leftover_count_decreases is uninhabited — every LStepHit
        raises lbag_count by 2.
     3. leftover_sum_decreases is uninhabited — lbag_sum is
        leftover_quad_width on a leftover_quad and is conserved
        (leftover_quad_width_conserved stays Qed).
     4. leftover_pair_kiss_ok inhabits as endpoint-share + no interior
        Hit on the locked leftover-quad join. leftover_kiss_on_bag is
        identity (kiss mints nothing). leftover_pair_kiss_as_decreasing_step
        is uninhabited. This is not leftover_quad_kiss_arm.
     5. leftover_pair_share_mint_ok inhabits as ShareOne on a leftover
        pair that already has leftover_pair_step_ok. leftover_span
        carries no hen; leftover_share_mint_on_bag is identity.
        leftover_pair_share_mint_as_decreasing_step is uninhabited.
        This is not leftover_quad_share_mint_arm.
   leftover_bag_step stays Hit-or-Decline. cook_loop_status stays
   LoopObligation. LeftoverBagTermArm stays the #797 three-conjunct
   hole. leftover_quad_width_decreases stays uninhabited.

   Sibling QED (cite, do not remint as bag-loop Discharge):
     I.8 pairwise split
       (Adr0007NodingEpic.v : ticket_0007_pairwise_split_qed_or_qex)
     leftover_quad_width_conserved
     donut T5 constant-and-already-noded
       (SheetHenDonutBag.v : ticket_0007_linear_donut_rho_qed_or_qex;
        full-lane only — not imported here)
     circ leftover |H|=2 on the locked lens
       (CircularCookLeftoverTwoHit.v :
        ticket_0007_circ_leftover_two_hit_qed_or_qex;
        not imported — module-split gate)
     modulo iterator / term measure on LStepHit
       (SheetHenCookLoopModulo.v : ticket_0007_rho_modulo_iter_qed_or_qex;
        SheetHenCookLoopTerm.v : ticket_0007_rho_bag_term_measure_qed_or_qex)
     #797 leftover-bag term park
       (HostRhoLeftoverBagTerm.v : ticket_0007_rho_leftover_qed_or_qex)

   Honesty fences:
     Do not inhabit leftover_quad_width_decreases.
     Do not remint leftover_quad_width as a bag-sum / multiset measure.
     Do not remint I.8 / pairwise as bag-loop Discharge.
     Do not remint leftover_bag_term_measure as LoopDischarged.
     Do not remint leftover_quad_kiss_arm / leftover_quad_share_mint_arm.
     Do not remint #798 leftover_pair_kiss_ok (that letter required
     leftover_quad_kiss_arm). Do not expand first_cook_scope.
     Do not remint I_ok_mixed. Do not remint CircGamma / ι.
     Host CircGamma is CircGammaDischarged (MkCirc). NURBS / SIN /
     ellipse / geodesic / Karney / atan2 / classic / Category C stay
     out. Not “ρ closed”, not “noder loop done”. ADR-0007 Status
     stays Accepted.

   WITNESS topic: overlay · claimId: 0007-rho-leftover-bag-term-qed
   witness: 0007-rho-leftover-bag-term-qed
   board: ADR-0007
   3-axiom host. No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra Arith Lia List.
From NTS.Proofs Require Import Distance SheetHenCook SheetHenCookLoop.
From NTS.Proofs Require Import SheetHenCookLoopModulo SheetHenCookLoopTerm.
From NTS.Proofs Require Import HostRhoLeftoverBagTerm.
Import ListNotations.
Local Open Scope R_scope.

(* WITNESS: campaign=rho rung=leftover-bag-term-qed claim=0007-rho-leftover-bag-term-qed
   file=theories/HostRhoLeftoverBagTermQed.v
   kind=QEX-failing-M-tighter-holes
   park=LeftoverBagTermArm
   missing=LeftoverCookMeasure,LeftoverKissDecreasingStep,LeftoverShareMintDecreasingStep
   not=LoopDischarged,leftover_quad_width-decreases,I.8-bag-Discharge
   not=leftover_quad_width-measure,leftover_bag_term_measure-Discharge
   not=leftover_quad_kiss_arm,leftover_quad_share_mint_arm
   not=first-cook-expand,I_ok_mixed,CircGamma-remint,NURBS,SIN,ellipse
   not=geodesic,Karney,atan2,classic,Category-C,rho-closed,noder-loop-done
   sibling=pairwise-I.8,width-conserved,donut-T5,circ-two-hit,modulo-iter,term-measure,#797
   note=letter-not-rho-discharge *)

(* -------------------------------------------------------------------------- *)
(* leftover_bag_step stays Hit-or-Decline. No kiss / share-mint ctor.         *)
(* -------------------------------------------------------------------------- *)

Definition leftover_bag_step_is_hit (b b' : leftover_span_bag) : Prop :=
  exists i j p ua ub,
    leftover_pair_step_ok b i j p ua ub /\
    lbag_pair_replace b i j ua ub = Some b'.

Definition leftover_bag_step_is_decline (b b' : leftover_span_bag) : Prop :=
  b' = b /\ exists i j, leftover_pair_decline b i j.

Lemma leftover_bag_step_hit_or_decline :
  forall b b',
    leftover_bag_step b b' ->
    leftover_bag_step_is_hit b b' \/ leftover_bag_step_is_decline b b'.
Proof.
  intros b b' Hstep.
  inversion Hstep; subst.
  - left. exists i, j, p, ua, ub. split; assumption.
  - right. split; [reflexivity|]. exists i, j. assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Count / sum candidates. lbag_count rises on every Hit; lbag_sum is         *)
(* leftover_quad_width on a leftover_quad and stays conserved.                *)
(* -------------------------------------------------------------------------- *)

Lemma lbag_count_remove :
  forall b n s,
    lbag_nth b n = Some s ->
    lbag_count (lbag_remove b n) = (lbag_count b - 1)%nat.
Proof.
  induction b as [|s0 rest IH]; intros n s Hnth.
  - discriminate.
  - destruct n as [|n'].
    + simpl in Hnth. inversion Hnth. subst s0. simpl. lia.
    + simpl in Hnth. simpl.
      apply IH in Hnth. lia.
Qed.

Lemma lbag_count_remove_two :
  forall b i j a bsp,
    i <> j ->
    lbag_nth b i = Some a ->
    lbag_nth b j = Some bsp ->
    lbag_count (lbag_remove_two b i j) = (lbag_count b - 2)%nat.
Proof.
  intros b i j a bsp Hne Ha Hb.
  unfold lbag_remove_two.
  destruct (Nat.ltb i j) eqn:Hlt.
  - apply Nat.ltb_lt in Hlt.
    assert (Hai : lbag_nth (lbag_remove b j) i = Some a).
    { apply lbag_nth_remove_before; assumption. }
    pose proof (lbag_count_remove (lbag_remove b j) i a Hai) as Hri.
    pose proof (lbag_count_remove b j bsp Hb) as Hrj.
    lia.
  - apply Nat.ltb_ge in Hlt.
    assert (Hji : (j < i)%nat).
    { apply Nat.le_neq. split; [exact Hlt|]. apply not_eq_sym. exact Hne. }
    assert (Hbj : lbag_nth (lbag_remove b i) j = Some bsp).
    { apply lbag_nth_remove_before; assumption. }
    pose proof (lbag_count_remove (lbag_remove b i) j bsp Hbj) as Hrj.
    pose proof (lbag_count_remove b i a Ha) as Hri.
    lia.
Qed.

Lemma lbag_pair_replace_count :
  forall b i j p ua ub b',
    leftover_pair_step_ok b i j p ua ub ->
    lbag_pair_replace b i j ua ub = Some b' ->
    lbag_count b' = (lbag_count b + 2)%nat.
Proof.
  intros b i j p ua ub b' [a [bsp [Ha [Hb [Hne _]]]]] Hrep.
  unfold lbag_pair_replace in Hrep.
  rewrite Ha, Hb in Hrep.
  assert (Hneqb : Nat.eqb i j = false) by (apply Nat.eqb_neq; exact Hne).
  rewrite Hneqb in Hrep.
  inversion Hrep. subst b'.
  cbn [lbag_count].
  pose proof (lbag_count_remove_two b i j a bsp Hne Ha Hb) as Hrm.
  lia.
Qed.

Definition leftover_bag_changed (b b' : leftover_span_bag) : Prop :=
  (lbag_count b <> lbag_count b')%nat.

Definition leftover_count_decreases : Prop :=
  forall b b',
    leftover_bag_step b b' ->
    leftover_bag_changed b b' ->
    (lbag_count b' < lbag_count b)%nat.

Definition leftover_sum_decreases : Prop :=
  forall b b',
    leftover_bag_step b b' ->
    leftover_bag_changed b b' ->
    lbag_sum b' < lbag_sum b.

Definition leftover_hit_measure_decreases : Prop :=
  forall b b' n m,
    leftover_bag_step b b' ->
    leftover_bag_changed b b' ->
    leftover_bag_term_measure b n ->
    leftover_bag_term_measure b' m ->
    (m < n)%nat.

(* -------------------------------------------------------------------------- *)
(* Overlap bag: two identical leftover_span_parent diag_ab.                   *)
(* Interior Hit-split is a real cook; leftover_bag_term_measure 1 → 2.        *)
(* -------------------------------------------------------------------------- *)

Definition overlap_parent_bag : leftover_span_bag :=
  LBagCons (leftover_span_parent diag_ab)
    (LBagCons (leftover_span_parent diag_ab) LBagNil).

Definition overlap_quad_bag : leftover_span_bag :=
  leftover_quad_as_bag diag_ab diag_ab (1 / 2) (1 / 2).

Lemma overlap_parent_pair_hit :
  leftover_pair_hit
    (leftover_span_parent diag_ab)
    (leftover_span_parent diag_ab)
    cross_pt (1 / 2) (1 / 2).
Proof.
  unfold leftover_pair_hit.
  split; [apply leftover_span_parent_ok|].
  split; [apply leftover_span_parent_ok|].
  split; [unfold leftover_egg_interior; lra|].
  split; [unfold leftover_egg_interior; lra|].
  rewrite leftover_egg_parent.
  rewrite leftover_egg_parent.
  unfold I_ok.
  split; [exact crossing_on_diag_ab | exact crossing_on_diag_ab].
Qed.

Lemma overlap_parent_step_ok :
  leftover_pair_step_ok overlap_parent_bag 0 1
    cross_pt (1 / 2) (1 / 2).
Proof.
  exists (leftover_span_parent diag_ab), (leftover_span_parent diag_ab).
  split; [reflexivity|].
  split; [reflexivity|].
  split; [discriminate|].
  exact overlap_parent_pair_hit.
Qed.

Lemma overlap_parent_replace :
  lbag_pair_replace overlap_parent_bag 0 1 (1 / 2) (1 / 2) =
  Some overlap_quad_bag.
Proof.
  unfold lbag_pair_replace, overlap_parent_bag, overlap_quad_bag,
         leftover_quad_as_bag, leftover_span_lo, leftover_span_hi,
         lbag_remove_two.
  simpl.
  rewrite !leftover_span_parent_at.
  reflexivity.
Qed.

Lemma overlap_hit_step :
  leftover_bag_step overlap_parent_bag overlap_quad_bag.
Proof.
  apply (LStepHit overlap_parent_bag overlap_quad_bag 0 1
           cross_pt (1 / 2) (1 / 2)).
  - exact overlap_parent_step_ok.
  - exact overlap_parent_replace.
Qed.

Lemma overlap_hit_count :
  lbag_count overlap_parent_bag = 2%nat /\
  lbag_count overlap_quad_bag = 4%nat /\
  leftover_bag_changed overlap_parent_bag overlap_quad_bag.
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  discriminate.
Qed.

Lemma overlap_hit_sum_conserved :
  lbag_sum overlap_quad_bag = lbag_sum overlap_parent_bag /\
  lbag_sum overlap_quad_bag = leftover_quad_width (1 / 2) (1 / 2) /\
  leftover_quad_width (1 / 2) (1 / 2) = leftover_width 0 1 + leftover_width 0 1.
Proof.
  split.
  - apply (lbag_pair_replace_sum overlap_parent_bag 0 1
             cross_pt (1 / 2) (1 / 2) overlap_quad_bag).
    + exact overlap_parent_step_ok.
    + exact overlap_parent_replace.
  - split.
    + apply leftover_quad_as_bag_sum.
    + apply leftover_quad_width_conserved; lra.
Qed.

Lemma overlap_parent_term_measure :
  leftover_bag_term_measure overlap_parent_bag 1.
Proof.
  exists [(0, 1)%nat].
  split; [|reflexivity].
  split.
  - intros ij Hin.
    destruct Hin as [Heq | Hnil]; [|contradiction].
    inversion Heq. subst ij. simpl.
    split; [lia|].
    exists cross_pt, (1 / 2), (1 / 2).
    exact overlap_parent_step_ok.
  - split.
    + intros i j Hpair.
      pose proof (leftover_hit_pair_bounded overlap_parent_bag i j Hpair) as Hbnd.
      change (lbag_count overlap_parent_bag) with 2%nat in Hbnd.
      assert (i = 0%nat /\ j = 1%nat) as [Hi Hj] by lia.
      subst i j. left. reflexivity.
    + apply NoDup_cons.
      * intros H. inversion H.
      * apply NoDup_nil.
Qed.

Definition overlap_lo : leftover_span := mkLeftoverSpan diag_ab 0 (1 / 2).
Definition overlap_hi : leftover_span := mkLeftoverSpan diag_ab (1 / 2) 1.
Definition overlap_lo_pt : Point := mkPoint (1 / 2) (1 / 2).
Definition overlap_hi_pt : Point := mkPoint (3 / 2) (3 / 2).

Lemma overlap_quad_nth :
  lbag_nth overlap_quad_bag 0 = Some overlap_lo /\
  lbag_nth overlap_quad_bag 1 = Some overlap_hi /\
  lbag_nth overlap_quad_bag 2 = Some overlap_lo /\
  lbag_nth overlap_quad_bag 3 = Some overlap_hi.
Proof.
  repeat split; reflexivity.
Qed.

Lemma overlap_lo_self_hit :
  leftover_pair_hit overlap_lo overlap_lo overlap_lo_pt (1 / 2) (1 / 2).
Proof.
  unfold leftover_pair_hit, overlap_lo, overlap_lo_pt.
  split; [unfold leftover_span_ok; simpl; lra|].
  split; [unfold leftover_span_ok; simpl; lra|].
  split; [unfold leftover_egg_interior; lra|].
  split; [unfold leftover_egg_interior; lra|].
  rewrite locked_A_lo_egg.
  rewrite locked_A_lo_egg.
  unfold I_ok, on_chord, chord_eval.
  split.
  - split; [lra|]. apply (f_equal2 mkPoint); simpl; field.
  - split; [lra|]. apply (f_equal2 mkPoint); simpl; field.
Qed.

Lemma overlap_hi_self_hit :
  leftover_pair_hit overlap_hi overlap_hi overlap_hi_pt (1 / 2) (1 / 2).
Proof.
  unfold leftover_pair_hit, overlap_hi, overlap_hi_pt.
  split; [unfold leftover_span_ok; simpl; lra|].
  split; [unfold leftover_span_ok; simpl; lra|].
  split; [unfold leftover_egg_interior; lra|].
  split; [unfold leftover_egg_interior; lra|].
  rewrite locked_A_hi_egg.
  rewrite locked_A_hi_egg.
  unfold I_ok, on_chord, chord_eval.
  split.
  - split; [lra|]. apply (f_equal2 mkPoint); simpl; field.
  - split; [lra|]. apply (f_equal2 mkPoint); simpl; field.
Qed.

Lemma overlap_Ahi_Alo_no_hit :
  forall p ua ub,
    ~ leftover_pair_hit overlap_hi overlap_lo p ua ub.
Proof.
  intros p ua ub H.
  apply leftover_pair_hit_sym in H.
  unfold overlap_lo, overlap_hi in H.
  exact (locked_quad_Alo_Ahi_no_hit p ub ua H).
Qed.

Lemma overlap_quad_02_step_ok :
  leftover_pair_step_ok overlap_quad_bag 0 2
    overlap_lo_pt (1 / 2) (1 / 2).
Proof.
  exists overlap_lo, overlap_lo.
  destruct overlap_quad_nth as [H0 [_ [H2 _]]].
  split; [exact H0|].
  split; [exact H2|].
  split; [discriminate|].
  exact overlap_lo_self_hit.
Qed.

Lemma overlap_quad_13_step_ok :
  leftover_pair_step_ok overlap_quad_bag 1 3
    overlap_hi_pt (1 / 2) (1 / 2).
Proof.
  exists overlap_hi, overlap_hi.
  destruct overlap_quad_nth as [_ [H1 [_ H3]]].
  split; [exact H1|].
  split; [exact H3|].
  split; [discriminate|].
  exact overlap_hi_self_hit.
Qed.

Lemma overlap_quad_term_measure :
  leftover_bag_term_measure overlap_quad_bag 2.
Proof.
  exists [(0, 2)%nat; (1, 3)%nat].
  split; [|reflexivity].
  split.
  - intros ij Hin.
    destruct Hin as [Heq | [Heq | Hnil]]; [| |contradiction].
    + inversion Heq. subst ij. simpl.
      split; [lia|].
      exists overlap_lo_pt, (1 / 2), (1 / 2).
      exact overlap_quad_02_step_ok.
    + inversion Heq. subst ij. simpl.
      split; [lia|].
      exists overlap_hi_pt, (1 / 2), (1 / 2).
      exact overlap_quad_13_step_ok.
  - split.
    + intros i j Hpair.
      pose proof (leftover_hit_pair_bounded overlap_quad_bag i j Hpair) as Hbnd.
      change (lbag_count overlap_quad_bag) with 4%nat in Hbnd.
      destruct Hpair as [Hij [p [ua [ub [a [bsp [Ha [Hb [Hne Hhit]]]]]]]]].
      destruct overlap_quad_nth as [N0 [N1 [N2 N3]]].
      destruct i as [|i0].
      * destruct j as [|j0]; [lia|].
        destruct j0 as [|j1].
        -- rewrite N0 in Ha. rewrite N1 in Hb.
           inversion Ha. inversion Hb. subst a bsp.
           unfold overlap_lo, overlap_hi in Hhit.
           exact (False_ind _ (locked_quad_Alo_Ahi_no_hit p ua ub Hhit)).
        -- destruct j1 as [|j2].
           ++ left. apply f_equal2; reflexivity.
           ++ destruct j2 as [|j3]; [|lia].
              rewrite N0 in Ha. rewrite N3 in Hb.
              inversion Ha. inversion Hb. subst a bsp.
              unfold overlap_lo, overlap_hi in Hhit.
              exact (False_ind _ (locked_quad_Alo_Ahi_no_hit p ua ub Hhit)).
      * destruct i0 as [|i1].
        -- destruct j as [|j0]; [lia|].
           destruct j0 as [|j1]; [lia|].
           destruct j1 as [|j2].
           ++ rewrite N1 in Ha. rewrite N2 in Hb.
              inversion Ha. inversion Hb. subst a bsp.
              exact (False_ind _ (overlap_Ahi_Alo_no_hit p ua ub Hhit)).
           ++ destruct j2 as [|j3]; [|lia].
              right. left. apply f_equal2; reflexivity.
        -- destruct i1 as [|i2]; [|lia].
           destruct j as [|j0]; [lia|].
           destruct j0 as [|j1]; [lia|].
           destruct j1 as [|j2]; [lia|].
           destruct j2 as [|j3]; [|lia].
           rewrite N2 in Ha. rewrite N3 in Hb.
           inversion Ha. inversion Hb. subst a bsp.
           unfold overlap_lo, overlap_hi in Hhit.
           exact (False_ind _ (locked_quad_Alo_Ahi_no_hit p ua ub Hhit)).
    + apply NoDup_cons.
      * intros H. destruct H as [Heq | Hnil].
        -- inversion Heq.
        -- contradiction.
      * apply NoDup_cons.
        -- intros H. contradiction.
        -- apply NoDup_nil.
Qed.

Lemma leftover_hit_measure_increases_on_overlap :
  leftover_bag_step overlap_parent_bag overlap_quad_bag /\
  leftover_bag_changed overlap_parent_bag overlap_quad_bag /\
  leftover_bag_term_measure overlap_parent_bag 1 /\
  leftover_bag_term_measure overlap_quad_bag 2 /\
  (1 < 2)%nat.
Proof.
  split; [exact overlap_hit_step|].
  split; [apply (proj2 (proj2 overlap_hit_count))|].
  split; [exact overlap_parent_term_measure|].
  split; [exact overlap_quad_term_measure|].
  lia.
Qed.

Lemma leftover_hit_measure_decreases_missing :
  ~ leftover_hit_measure_decreases.
Proof.
  intros H.
  pose proof leftover_hit_measure_increases_on_overlap as [Hs [Hc [Hn [Hm _]]]].
  specialize (H overlap_parent_bag overlap_quad_bag 1 2 Hs Hc Hn Hm).
  lia.
Qed.

Lemma leftover_count_decreases_missing :
  ~ leftover_count_decreases.
Proof.
  intros H.
  pose proof overlap_hit_count as [_ [_ Hc]].
  specialize (H overlap_parent_bag overlap_quad_bag overlap_hit_step Hc).
  change (lbag_count overlap_quad_bag) with 4%nat in H.
  change (lbag_count overlap_parent_bag) with 2%nat in H.
  lia.
Qed.

Lemma leftover_sum_decreases_missing :
  ~ leftover_sum_decreases.
Proof.
  intros H.
  pose proof overlap_hit_count as [_ [_ Hc]].
  pose proof overlap_hit_sum_conserved as [Hsum _].
  specialize (H overlap_parent_bag overlap_quad_bag overlap_hit_step Hc).
  lra.
Qed.

Lemma leftover_count_hit_increases :
  forall b b' i j p ua ub,
    leftover_pair_step_ok b i j p ua ub ->
    lbag_pair_replace b i j ua ub = Some b' ->
    lbag_count b' = (lbag_count b + 2)%nat.
Proof.
  exact lbag_pair_replace_count.
Qed.

(* -------------------------------------------------------------------------- *)
(* Kiss: endpoint-share + no interior Hit. Inhabits on the locked join.       *)
(* leftover_kiss_on_bag is identity. Not leftover_quad_kiss_arm.              *)
(* -------------------------------------------------------------------------- *)

Definition leftover_pair_kiss_ok (b : leftover_span_bag) (i j : nat) : Prop :=
  exists a bsp,
    lbag_nth b i = Some a /\
    lbag_nth b j = Some bsp /\
    i <> j /\
    leftover_span_ok a /\
    leftover_span_ok bsp /\
    share_endpoint
      (ce_p0 (leftover_egg a)) (ce_p1 (leftover_egg a))
      (ce_p0 (leftover_egg bsp)) (ce_p1 (leftover_egg bsp)) /\
    (forall p ua ub, ~ leftover_pair_hit a bsp p ua ub).

Definition leftover_kiss_on_bag (b : leftover_span_bag) (i j : nat)
  : leftover_span_bag := b.

Lemma leftover_kiss_on_bag_id :
  forall b i j, leftover_kiss_on_bag b i j = b.
Proof.
  intros b i j. reflexivity.
Qed.

Lemma leftover_pair_kiss_ok_locked_join :
  leftover_pair_kiss_ok locked_quad_bag 0 2.
Proof.
  exists (mkLeftoverSpan diag_ab 0 (1 / 2)),
         (mkLeftoverSpan diag_cd 0 (1 / 2)).
  split; [reflexivity|].
  split; [reflexivity|].
  split; [discriminate|].
  split; [unfold leftover_span_ok; simpl; lra|].
  split; [unfold leftover_span_ok; simpl; lra|].
  split.
  - rewrite locked_A_lo_egg, locked_B_lo_egg.
    unfold share_endpoint. simpl.
    right. right. right. reflexivity.
  - exact locked_quad_pair_no_interior_hit.
Qed.

Lemma leftover_pair_kiss_ok_not_quad_kiss_arm :
  leftover_pair_kiss_ok locked_quad_bag 0 2 /\
  ~ leftover_quad_kiss_arm.
Proof.
  split; [exact leftover_pair_kiss_ok_locked_join|].
  exact leftover_quad_kiss_arm_missing.
Qed.

Lemma leftover_kiss_idle_on_measure :
  leftover_kiss_on_bag locked_quad_bag 0 2 = locked_quad_bag /\
  leftover_bag_term_measure locked_quad_bag 0 /\
  leftover_bag_term_measure
    (leftover_kiss_on_bag locked_quad_bag 0 2) 0 /\
  leftover_quad_width (1 / 2) (1 / 2) =
  leftover_width 0 1 + leftover_width 0 1.
Proof.
  split; [reflexivity|].
  split; [exact locked_quad_term_measure|].
  split; [exact locked_quad_term_measure|].
  apply leftover_quad_width_conserved; lra.
Qed.

Definition leftover_pair_kiss_as_decreasing_step : Prop :=
  exists b b' i j n m,
    leftover_pair_kiss_ok b i j /\
    leftover_kiss_on_bag b i j = b' /\
    b' <> b /\
    leftover_bag_term_measure b n /\
    leftover_bag_term_measure b' m /\
    (m < n)%nat.

Lemma leftover_pair_kiss_as_decreasing_step_missing :
  ~ leftover_pair_kiss_as_decreasing_step.
Proof.
  intros [b [b' [_ [_ [_ [_ [_ [Heq [Hne _]]]]]]]]].
  apply Hne. exact Heq.
Qed.

(* -------------------------------------------------------------------------- *)
(* Share-mint: ShareOne on a leftover pair that already Hits. leftover_span   *)
(* carries no hen; leftover_share_mint_on_bag is identity.                    *)
(* Not leftover_quad_share_mint_arm.                                          *)
(* -------------------------------------------------------------------------- *)

Definition leftover_pair_share_mint_ok
  (b : leftover_span_bag) (i j : nat) (h : Hen) : Prop :=
  exists p ua ub,
    leftover_pair_step_ok b i j p ua ub /\
    fst (apply_id_decision (ShareOne h)) =
    snd (apply_id_decision (ShareOne h)).

Definition leftover_share_mint_on_bag (b : leftover_span_bag) (h : Hen)
  : leftover_span_bag := b.

Lemma leftover_share_mint_on_bag_id :
  forall b h, leftover_share_mint_on_bag b h = b.
Proof.
  intros b h. reflexivity.
Qed.

Lemma leftover_span_is_parent_interval :
  forall s,
    leftover_egg s = leftover_half (ls_parent s) (ls_t0 s) (ls_t1 s).
Proof.
  intros s. reflexivity.
Qed.

Lemma leftover_pair_share_mint_ok_locked_parent :
  leftover_pair_share_mint_ok locked_parent_bag 0 1 crossing_hen.
Proof.
  exists cross_pt, (1 / 2), (1 / 2).
  split; [exact locked_parent_step_ok|].
  apply share_one_same_hen.
Qed.

Lemma leftover_pair_share_mint_ok_not_quad_share_mint_arm :
  leftover_pair_share_mint_ok locked_parent_bag 0 1 crossing_hen /\
  ~ leftover_quad_share_mint_arm.
Proof.
  split; [exact leftover_pair_share_mint_ok_locked_parent|].
  exact leftover_quad_share_mint_arm_missing.
Qed.

Lemma leftover_share_mint_idle_on_measure :
  leftover_share_mint_on_bag locked_parent_bag crossing_hen =
  locked_parent_bag /\
  leftover_bag_term_measure locked_parent_bag 1 /\
  leftover_bag_term_measure
    (leftover_share_mint_on_bag locked_parent_bag crossing_hen) 1 /\
  leftover_quad_width (1 / 2) (1 / 2) =
  leftover_width 0 1 + leftover_width 0 1.
Proof.
  split; [reflexivity|].
  split; [exact locked_parent_term_measure|].
  split; [exact locked_parent_term_measure|].
  apply leftover_quad_width_conserved; lra.
Qed.

Definition leftover_pair_share_mint_as_decreasing_step : Prop :=
  exists b b' i j h n m,
    leftover_pair_share_mint_ok b i j h /\
    leftover_share_mint_on_bag b h = b' /\
    b' <> b /\
    leftover_bag_term_measure b n /\
    leftover_bag_term_measure b' m /\
    (m < n)%nat.

Lemma leftover_pair_share_mint_as_decreasing_step_missing :
  ~ leftover_pair_share_mint_as_decreasing_step.
Proof.
  intros [b [b' [_ [_ [_ [_ [_ [_ [Heq [Hne _]]]]]]]]]].
  apply Hne. exact Heq.
Qed.

(* -------------------------------------------------------------------------- *)
(* Named missing constructors. Not bools.                                     *)
(* -------------------------------------------------------------------------- *)

Inductive LeftoverBagTermQedCtor : Type :=
| LeftoverCookMeasure
| LeftoverKissDecreasingStep
| LeftoverShareMintDecreasingStep.

Definition leftover_bag_term_qed_ctor_inhabits
  (c : LeftoverBagTermQedCtor) : Prop :=
  match c with
  | LeftoverCookMeasure => leftover_hit_measure_decreases
  | LeftoverKissDecreasingStep => leftover_pair_kiss_as_decreasing_step
  | LeftoverShareMintDecreasingStep => leftover_pair_share_mint_as_decreasing_step
  end.

Lemma leftover_cook_measure_missing :
  ~ leftover_bag_term_qed_ctor_inhabits LeftoverCookMeasure.
Proof.
  exact leftover_hit_measure_decreases_missing.
Qed.

Lemma leftover_kiss_decreasing_step_missing :
  ~ leftover_bag_term_qed_ctor_inhabits LeftoverKissDecreasingStep.
Proof.
  exact leftover_pair_kiss_as_decreasing_step_missing.
Qed.

Lemma leftover_share_mint_decreasing_step_missing :
  ~ leftover_bag_term_qed_ctor_inhabits LeftoverShareMintDecreasingStep.
Proof.
  exact leftover_pair_share_mint_as_decreasing_step_missing.
Qed.

Lemma leftover_bag_term_qed_ctors_uninhabited :
  ~ leftover_bag_term_qed_ctor_inhabits LeftoverCookMeasure
  /\ ~ leftover_bag_term_qed_ctor_inhabits LeftoverKissDecreasingStep
  /\ ~ leftover_bag_term_qed_ctor_inhabits LeftoverShareMintDecreasingStep
  /\ ~ leftover_hit_measure_decreases
  /\ ~ leftover_count_decreases
  /\ ~ leftover_sum_decreases
  /\ ~ leftover_pair_kiss_as_decreasing_step
  /\ ~ leftover_pair_share_mint_as_decreasing_step.
Proof.
  split; [exact leftover_cook_measure_missing|].
  split; [exact leftover_kiss_decreasing_step_missing|].
  split; [exact leftover_share_mint_decreasing_step_missing|].
  split; [exact leftover_hit_measure_decreases_missing|].
  split; [exact leftover_count_decreases_missing|].
  split; [exact leftover_sum_decreases_missing|].
  split; [exact leftover_pair_kiss_as_decreasing_step_missing|].
  exact leftover_pair_share_mint_as_decreasing_step_missing.
Qed.

Lemma leftover_bag_term_qed_loop_unchanged :
  cook_loop_status = LoopObligation
  /\ cook_loop_status <> LoopDischarged
  /\ ~ leftover_bag_term_arm
  /\ LeftoverBagTermArm = leftover_bag_term_arm
  /\ leftover_bag_term_arm =
       (leftover_quad_width_decreases
        /\ leftover_quad_kiss_arm
        /\ leftover_quad_share_mint_arm)
  /\ ~ leftover_quad_width_decreases
  /\ ~ leftover_quad_kiss_arm
  /\ ~ leftover_quad_share_mint_arm
  /\ ~ leftover_bag_term_ctor_inhabits LeftoverWidthDecreases
  /\ ~ leftover_bag_term_ctor_inhabits LeftoverKissArm
  /\ ~ leftover_bag_term_ctor_inhabits LeftoverShareMintArm.
Proof.
  split; [exact cook_loop_is_obligation|].
  split; [exact cook_loop_not_discharged|].
  split; [exact leftover_bag_term_arm_missing|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact leftover_quad_width_does_not_decrease|].
  split; [exact leftover_quad_kiss_arm_missing|].
  split; [exact leftover_quad_share_mint_arm_missing|].
  split; [exact leftover_width_decreases_missing|].
  split; [exact leftover_kiss_arm_missing|].
  exact leftover_share_mint_arm_missing.
Qed.

Lemma leftover_bag_term_qed_scope_unchanged :
  first_cook_scope EggChord EggChord
  /\ ~ first_cook_scope EggNurbs EggNurbs
  /\ cook_loop_status = LoopObligation
  /\ cook_loop_status <> LoopDischarged.
Proof.
  split; [exact first_cook_scope_chord_chord|].
  split; [exact nurbs_nurbs_not_first_scope|].
  split; [exact cook_loop_is_obligation|].
  exact cook_loop_not_discharged.
Qed.

(* -------------------------------------------------------------------------- *)
(* Sibling cites — packaging, not bag-loop Discharge.                         *)
(* -------------------------------------------------------------------------- *)

Lemma sibling_i8_not_bag_discharge :
  (interior_split_finite /\ split_step_confluent_holds)
  /\ cook_loop_status = LoopObligation
  /\ cook_loop_status <> LoopDischarged.
Proof.
  destruct ticket_0007_pairwise_split_qed_or_qex as [H | Hfail].
  - split; [exact H|].
    split; [exact cook_loop_is_obligation|].
    exact cook_loop_not_discharged.
  - exfalso. apply Hfail. exact interior_split_finite_holds.
Qed.

Lemma sibling_term_measure_not_general_decrease :
  leftover_bag_term_measure locked_parent_bag 1
  /\ leftover_bag_term_measure locked_quad_bag 0
  /\ leftover_bag_term_measure overlap_parent_bag 1
  /\ leftover_bag_term_measure overlap_quad_bag 2
  /\ ~ leftover_hit_measure_decreases
  /\ cook_loop_status = LoopObligation
  /\ cook_loop_status <> LoopDischarged.
Proof.
  split; [exact locked_parent_term_measure|].
  split; [exact locked_quad_term_measure|].
  split; [exact overlap_parent_term_measure|].
  split; [exact overlap_quad_term_measure|].
  split; [exact leftover_hit_measure_decreases_missing|].
  split; [exact cook_loop_is_obligation|].
  exact cook_loop_not_discharged.
Qed.

Lemma sibling_modulo_iter_not_bag_discharge :
  leftover_bag_cook_fuel 1 locked_parent_bag locked_quad_bag
  /\ leftover_pair_step_ok locked_parent_bag 0 1
       cross_pt (1 / 2) (1 / 2)
  /\ leftover_bag_cook_fuel 1 locked_quad_bag locked_quad_bag
  /\ cook_loop_status = LoopObligation
  /\ cook_loop_status <> LoopDischarged.
Proof.
  destruct ticket_0007_rho_modulo_iter_qed_or_qex as [H | Hdis].
  - destruct H as [_ [Hnstep [Hok [Hdec [_ [_ [Hob Hnd]]]]]]].
    split; [exact Hnstep|].
    split; [exact Hok|].
    split; [exact Hdec|].
    split; [exact Hob|].
    exact Hnd.
  - exfalso. exact (cook_loop_not_discharged Hdis).
Qed.

Lemma sibling_797_park_stays_qex :
  cook_loop_status = LoopObligation
  /\ cook_loop_status <> LoopDischarged
  /\ ~ leftover_bag_term_arm
  /\ ~ leftover_quad_width_decreases.
Proof.
  destruct ticket_0007_rho_leftover_qed_or_qex as [H | H].
  - destruct H as [_ [_ [_ [_ Hdis]]]].
    exfalso. exact (cook_loop_not_discharged Hdis).
  - destruct H as [Hob [Hnd [Hmiss [_ [_ [_ [_ [_ [Hwd _]]]]]]]]].
    split; [exact Hob|].
    split; [exact Hnd|].
    split; [exact Hmiss|].
    exact Hwd.
Qed.

(* Circ leftover |H|=2 and donut T5 stay sibling; not imported
   (module-split / full-lane). They do not inhabit a decreasing M. *)
Lemma sibling_circ_two_hit_and_donut_t5_not_bag_discharge :
  cook_loop_status = LoopObligation
  /\ cook_loop_status <> LoopDischarged
  /\ ~ leftover_bag_term_arm
  /\ ~ leftover_hit_measure_decreases.
Proof.
  split; [exact cook_loop_is_obligation|].
  split; [exact cook_loop_not_discharged|].
  split; [exact leftover_bag_term_arm_missing|].
  exact leftover_hit_measure_decreases_missing.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ticket-named QED ∨ QEX stop.                                               *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-rho-leftover-bag-term-qed","topic":"overlay","lemma":"ticket_0007_rho_leftover_bag_term_qed_or_qex","title":"rho leftover-bag term QED attempt: a new leftover-bag measure M decreases on every leftover_bag_step cook (Hit-split, kiss-if-changes, share-mint-if-changes), leftover_pair_kiss_ok and leftover_pair_share_mint_ok are leftover_bag_step constructors, LeftoverBagTermArm is restated to M+kiss+share-mint, and cook_loop is LoopDischarged (QED) or leftover_hit_measure_decreases leftover_count_decreases leftover_sum_decreases leftover_pair_kiss_as_decreasing_step leftover_pair_share_mint_as_decreasing_step stay missing leftover_quad width is conserved leftover_pair_kiss_ok is idle endpoint-share leftover_pair_share_mint_ok is idle ShareOne leftover_bag_step stays Hit-or-Decline LeftoverBagTermArm stays the #797 three-conjunct hole and cook_loop stays LoopObligation (QEX); discharged QEX; sibling I.8 / term-measure / modulo-iter / circ |H|=2 / donut T5 / #797 park are not bag Discharge","file":"theories/HostRhoLeftoverBagTermQed.v","witness":"0007-rho-leftover-bag-term-qed","board":"ADR-0007"} *)
Theorem ticket_0007_rho_leftover_bag_term_qed_or_qex :
  (leftover_hit_measure_decreases
   /\ leftover_pair_kiss_as_decreasing_step
   /\ leftover_pair_share_mint_as_decreasing_step
   /\ leftover_bag_term_arm
   /\ cook_loop_status = LoopDischarged)
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
   /\ ~ leftover_quad_share_mint_arm
   /\ ~ leftover_hit_measure_decreases
   /\ ~ leftover_count_decreases
   /\ ~ leftover_sum_decreases
   /\ ~ leftover_pair_kiss_as_decreasing_step
   /\ ~ leftover_pair_share_mint_as_decreasing_step
   /\ leftover_pair_kiss_ok locked_quad_bag 0 2
   /\ leftover_pair_share_mint_ok locked_parent_bag 0 1 crossing_hen
   /\ leftover_kiss_on_bag locked_quad_bag 0 2 = locked_quad_bag
   /\ leftover_share_mint_on_bag locked_parent_bag crossing_hen =
        locked_parent_bag
   /\ leftover_bag_term_measure overlap_parent_bag 1
   /\ leftover_bag_term_measure overlap_quad_bag 2
   /\ leftover_bag_step overlap_parent_bag overlap_quad_bag
   /\ lbag_count overlap_quad_bag = (lbag_count overlap_parent_bag + 2)%nat
   /\ lbag_sum overlap_quad_bag = lbag_sum overlap_parent_bag
   /\ (forall ti tj,
         0 < ti < 1 ->
         0 < tj < 1 ->
         leftover_quad_width ti tj =
         leftover_width 0 1 + leftover_width 0 1)
   /\ (leftover_bag_step_is_hit overlap_parent_bag overlap_quad_bag
       \/ leftover_bag_step_is_decline overlap_parent_bag overlap_quad_bag)
   /\ interior_split_finite
   /\ split_step_confluent_holds
   /\ first_cook_scope EggChord EggChord
   /\ ~ first_cook_scope EggNurbs EggNurbs).
Proof.
  right.
  split; [exact cook_loop_is_obligation|].
  split; [exact cook_loop_not_discharged|].
  split; [exact leftover_bag_term_arm_missing|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact leftover_quad_width_does_not_decrease|].
  split; [exact leftover_quad_kiss_arm_missing|].
  split; [exact leftover_quad_share_mint_arm_missing|].
  split; [exact leftover_hit_measure_decreases_missing|].
  split; [exact leftover_count_decreases_missing|].
  split; [exact leftover_sum_decreases_missing|].
  split; [exact leftover_pair_kiss_as_decreasing_step_missing|].
  split; [exact leftover_pair_share_mint_as_decreasing_step_missing|].
  split; [exact leftover_pair_kiss_ok_locked_join|].
  split; [exact leftover_pair_share_mint_ok_locked_parent|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact overlap_parent_term_measure|].
  split; [exact overlap_quad_term_measure|].
  split; [exact overlap_hit_step|].
  split; [reflexivity|].
  split; [apply overlap_hit_sum_conserved|].
  split; [exact leftover_quad_width_conserved|].
  split.
  - apply leftover_bag_step_hit_or_decline. exact overlap_hit_step.
  - split; [exact interior_split_finite_holds|].
    split; [exact split_step_confluent_holds_proof|].
    split; [exact first_cook_scope_chord_chord|].
    exact nurbs_nurbs_not_first_scope.
Qed.

Print Assumptions lbag_pair_replace_count.
Print Assumptions leftover_hit_measure_increases_on_overlap.
Print Assumptions leftover_hit_measure_decreases_missing.
Print Assumptions leftover_count_decreases_missing.
Print Assumptions leftover_sum_decreases_missing.
Print Assumptions leftover_pair_kiss_ok_locked_join.
Print Assumptions leftover_pair_kiss_ok_not_quad_kiss_arm.
Print Assumptions leftover_pair_kiss_as_decreasing_step_missing.
Print Assumptions leftover_pair_share_mint_ok_locked_parent.
Print Assumptions leftover_pair_share_mint_ok_not_quad_share_mint_arm.
Print Assumptions leftover_pair_share_mint_as_decreasing_step_missing.
Print Assumptions leftover_bag_term_qed_ctors_uninhabited.
Print Assumptions leftover_bag_term_qed_loop_unchanged.
Print Assumptions leftover_bag_term_qed_scope_unchanged.
Print Assumptions sibling_i8_not_bag_discharge.
Print Assumptions sibling_term_measure_not_general_decrease.
Print Assumptions sibling_modulo_iter_not_bag_discharge.
Print Assumptions sibling_797_park_stays_qex.
Print Assumptions sibling_circ_two_hit_and_donut_t5_not_bag_discharge.
Print Assumptions ticket_0007_rho_leftover_bag_term_qed_or_qex.
