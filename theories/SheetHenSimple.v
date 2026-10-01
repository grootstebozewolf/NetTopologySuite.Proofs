(* ============================================================================
   NetTopologySuite.Proofs.SheetHenSimple
   ----------------------------------------------------------------------------
   CS/CC rung 3. claimId: 0007-cscc-issimple. witness: cscc_issimple.
   A carrier the loop accepts is simple iff the arm fixpoint adds no
   interior vertex. Reads the loop. Does not edit it.
   simple_cscc_egg_fixtures / touch_egg_fixtures are samples. claimId: none.
   3-axiom host. No Admitted.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lia List PeanoNat Bool.
From NTS.Proofs Require Import
  Distance SheetHenCook SheetHenCookCore SheetHenBag
  SheetHenRho SheetHenBagRun SheetHenLoop3 SheetHenPickSpec
  SheetHenNodedOv SheetHenRhoLoop SheetHenBagRunFix SheetHenRhoConfFix.
Import ListNotations.
Local Open Scope R_scope.

(* A live chord/circle bag the loop will run: well-formed, no decline. *)
Definition loop_carrier (b : SheetBag) : Prop :=
  match b with
  | BagDeclined _ => False
  | BagLive _ pcs => bag_inv b /\ no_decline_pair pcs
  end.

(* Every oracle hit the overlap rule still sees is already a vertex of
   both supports. That is the carrier meeting only at vertices. *)
Definition cscc_IsSimple (b : SheetBag) : Prop :=
  match b with
  | BagDeclined _ => False
  | BagLive _ pcs =>
      forall i j a c p ti tj,
        nth_error pcs i = Some a ->
        nth_error pcs j = Some c ->
        i <> j ->
        I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck c)) (IHit p ti tj) ->
        (overlap (bp_support a) (bp_support c) ->
           In p (overlap_endpoints pcs (bp_support a) (bp_support c))) ->
        family_vertex pcs (bp_support a) p /\
        family_vertex pcs (bp_support c) p
  end.

(* The arm fixpoint minted no vertex that the carrier did not already have. *)
Definition loop_fixpoint_adds_no_interior (b : SheetBag) : Prop :=
  match b with
  | BagDeclined _ => False
  | BagLive _ pcs =>
      match bag_run_arm (S (rho b)) b with
      | BagDeclined _ => False
      | BagLive _ pcs' =>
          forall s p, family_vertex pcs' s p -> family_vertex pcs s p
      end
  end.

Lemma vertex_both_nn : forall pcs s1 s2 p,
  ~ ~ (family_vertex pcs s1 p /\ family_vertex pcs s2 p) ->
  family_vertex pcs s1 p /\ family_vertex pcs s2 p.
Proof.
  intros pcs s1 s2 p Hnn.
  destruct (vertex_b pcs s1 p) eqn:E1;
    destruct (vertex_b pcs s2 p) eqn:E2.
  - split; apply vertex_spec; assumption.
  - exfalso. apply Hnn. intros [_ H2]. apply vertex_spec in H2. congruence.
  - exfalso. apply Hnn. intros [H1 _]. apply vertex_spec in H1. congruence.
  - exfalso. apply Hnn. intros [H1 _]. apply vertex_spec in H1. congruence.
Qed.

Lemma cscc_IsSimple_noded_ov : forall sh pcs,
  cscc_IsSimple (BagLive sh pcs) <-> bag_noded_ov (BagLive sh pcs).
Proof.
  intros sh pcs. split.
  - intros H i j a c p ti tj Hi Hj Hij Hok Hante.
    unfold progress_hit. intros Hnot. apply Hnot.
    apply (H i j a c p ti tj Hi Hj Hij Hok).
    intros Ho. apply Hante. exact Ho.
  - intros H i j a c p ti tj Hi Hj Hij Hok Hante.
    apply vertex_both_nn.
    exact (H i j a c p ti tj Hi Hj Hij Hok Hante).
Qed.

Lemma missing_support_vertex : forall pcs e1 e2 p,
  ~ vertex_of_both pcs (bp_support e1) (bp_support e2) p ->
  ~ family_vertex pcs (bp_support e1) p \/
  ~ family_vertex pcs (bp_support e2) p.
Proof.
  intros pcs e1 e2 p Hnv.
  destruct (vertex_b pcs (bp_support e1) p) eqn:E1;
    destruct (vertex_b pcs (bp_support e2) p) eqn:E2.
  - exfalso. apply Hnv. split; apply vertex_spec; assumption.
  - right. intros Hv. apply vertex_spec in Hv. congruence.
  - left. intros Hv. apply vertex_spec in Hv. congruence.
  - left. intros Hv. apply vertex_spec in Hv. congruence.
Qed.

Lemma step_hit_pieces : forall sh pcs i j e1 e2 P ti tj,
  nth_error pcs i = Some e1 ->
  nth_error pcs j = Some e2 ->
  step_hit (BagLive sh pcs) (mkHitPick i j P ti tj) =
  BagLive sh (progress_pieces pcs i j e1 e2 ti tj (mint_or_share pcs P)).
Proof.
  intros sh pcs i j e1 e2 P ti tj Hi Hj.
  unfold step_hit, hp_i, hp_j, hp_ti, hp_tj, hp_P. cbn.
  rewrite Hi, Hj. reflexivity.
Qed.

Lemma arm_keeps_family_vertex : forall fuel sh pcs s p,
  bag_inv (BagLive sh pcs) ->
  family_vertex pcs s p ->
  match bag_run_arm fuel (BagLive sh pcs) with
  | BagLive _ pcs' => family_vertex pcs' s p
  | BagDeclined _ => True
  end.
Proof.
  induction fuel as [|fuel IH]; intros sh pcs s p Hinv Hv.
  - exact Hv.
  - cbn [bag_run_arm].
    destruct (pick_arm (BagLive sh pcs)) eqn:Harm.
    + pose proof (pick_bag_spec (BagLive sh pcs) Hinv) as Hs.
      rewrite Harm in Hs. destruct Hs as [w [Hw Hok]].
      assert (En : arm_next (BagLive sh pcs) =
                   Some (step_hit (BagLive sh pcs) w)).
      { unfold arm_next. rewrite Harm, Hw. reflexivity. }
      rewrite En.
      destruct w as [i j P ti tj].
      destruct Hok as [e1 [e2 [Hi [Hj [Hij [Hw1 [Hw2 [_ _]]]]]]]].
      assert (Hstep := step_hit_pieces sh pcs i j e1 e2 P ti tj Hi Hj).
      rewrite Hstep.
      apply IH.
      * rewrite <- Hstep.
        exact (proj1 (arm_hit_preserves sh pcs (mkHitPick i j P ti tj) Hinv Hw)).
      * apply (progress_vertices_mono pcs i j e1 e2 ti tj
                 (mint_or_share pcs P) s p Hi Hj Hij Hv).
    + assert (En : arm_next (BagLive sh pcs) = Some (BagDeclined sh)).
      { unfold arm_next, step_decline. rewrite Harm. reflexivity. }
      rewrite En. rewrite bag_run_arm_declined. exact I.
    + assert (En : arm_next (BagLive sh pcs) = None).
      { unfold arm_next. rewrite Harm. reflexivity. }
      rewrite En. exact Hv.
Qed.

Lemma positive_rho_adds_vertex : forall sh pcs,
  bag_inv (BagLive sh pcs) ->
  no_decline_pair pcs ->
  (0 < rho_pcs pcs)%nat ->
  exists s p,
    ~ family_vertex pcs s p /\
    match bag_run_arm (S (rho_pcs pcs)) (BagLive sh pcs) with
    | BagLive _ pcs' => family_vertex pcs' s p
    | BagDeclined _ => True
    end.
Proof.
  intros sh pcs Hinv Hnd Hpos.
  pose proof (pick_bag_spec (BagLive sh pcs) Hinv) as Hs.
  destruct (pick_arm (BagLive sh pcs)) eqn:Harm.
  - destruct Hs as [w [Hw Hok]].
    destruct w as [i j P ti tj].
    destruct Hok as [e1 [e2 [Hi [Hj [Hij [Hw1 [Hw2 [_ Hadm]]]]]]]].
    destruct (missing_support_vertex pcs e1 e2 P
               (proj1 (proj2 Hadm))) as [Hmiss|Hmiss].
    + exists (bp_support e1), P. split; [exact Hmiss|].
      assert (En : arm_next (BagLive sh pcs) =
        Some (step_hit (BagLive sh pcs) (mkHitPick i j P ti tj))).
      { unfold arm_next. rewrite Harm, Hw. reflexivity. }
      cbn [bag_run_arm]. rewrite En.
      assert (Hstep := step_hit_pieces sh pcs i j e1 e2 P ti tj Hi Hj).
      rewrite Hstep.
      apply (arm_keeps_family_vertex (rho_pcs pcs) sh
               (progress_pieces pcs i j e1 e2 ti tj (mint_or_share pcs P))
               (bp_support e1) P).
      * rewrite <- Hstep.
        exact (proj1 (arm_hit_preserves sh pcs (mkHitPick i j P ti tj)
                       Hinv Hw)).
      * exact (proj1 (hit_becomes_vertex pcs i j e1 e2 P ti tj
                        (mint_or_share pcs P) Hi Hj Hw1 Hw2 (proj1 Hadm))).
    + exists (bp_support e2), P. split; [exact Hmiss|].
      assert (En : arm_next (BagLive sh pcs) =
        Some (step_hit (BagLive sh pcs) (mkHitPick i j P ti tj))).
      { unfold arm_next. rewrite Harm, Hw. reflexivity. }
      cbn [bag_run_arm]. rewrite En.
      assert (Hstep := step_hit_pieces sh pcs i j e1 e2 P ti tj Hi Hj).
      rewrite Hstep.
      apply (arm_keeps_family_vertex (rho_pcs pcs) sh
               (progress_pieces pcs i j e1 e2 ti tj (mint_or_share pcs P))
               (bp_support e2) P).
      * rewrite <- Hstep.
        exact (proj1 (arm_hit_preserves sh pcs (mkHitPick i j P ti tj)
                       Hinv Hw)).
      * exact (proj2 (hit_becomes_vertex pcs i j e1 e2 P ti tj
                        (mint_or_share pcs P) Hi Hj Hw1 Hw2 (proj1 Hadm))).
  - exfalso.
    destruct Hs as [_ Hd].
    apply (proj2 (live_decline_forall pcs) Hnd). exact Hd.
  - exfalso.
    destruct Hs as [_ [Hz _]].
    unfold rho in Hz. rewrite Hz in Hpos. exact (Nat.nlt_0_r _ Hpos).
Qed.

(* WITNESS {"claimId":"0007-cscc-issimple","topic":"overlay","lemma":"cscc_issimple","title":"CS/CC IsSimple iff the loop fixpoint adds no interior vertex","file":"theories/SheetHenSimple.v","witness":"cscc_issimple","board":"ADR-0007"} *)
Theorem cscc_issimple : forall b,
  loop_carrier b ->
  cscc_IsSimple b <-> loop_fixpoint_adds_no_interior b.
Proof.
  intros b Hcar. destruct b as [sh pcs|sh]; [| exact (False_rect _ Hcar)].
  destruct Hcar as [Hinv Hnd]. split.
  - intros Hs.
    apply cscc_IsSimple_noded_ov in Hs.
    assert (Hz : rho_pcs pcs = 0%nat).
    { apply (noded_ov_rho_zero sh pcs Hinv Hnd Hs). }
    assert (Erun : bag_run_arm (S (rho (BagLive sh pcs))) (BagLive sh pcs) =
                   BagLive sh pcs).
    { unfold rho. rewrite Hz.
      apply (rho_zero_arm_fix 1%nat sh pcs Hinv Hnd Hz). }
    unfold loop_fixpoint_adds_no_interior. rewrite Erun.
    intros s p Hv. exact Hv.
  - intros Hfix.
    apply cscc_IsSimple_noded_ov.
    apply (proj1 (rho_zero_iff_noded_ov sh pcs Hinv Hnd)).
    destruct (Nat.eq_dec (rho_pcs pcs) 0%nat) as [Hz|Hnz].
    + exact Hz.
    + exfalso.
      assert (Hpos : (0 < rho_pcs pcs)%nat) by lia.
      destruct (positive_rho_adds_vertex sh pcs Hinv Hnd Hpos)
        as [s [p [Hmiss Hfin]]].
      unfold loop_fixpoint_adds_no_interior in Hfix.
      unfold rho in Hfix.
      destruct (bag_run_arm (S (rho_pcs pcs)) (BagLive sh pcs))
        as [sh' pcs'|sh'] eqn:Eb.
      * apply Hmiss. apply Hfix. exact Hfin.
      * exact Hfix.
Qed.

(* Sample. Two half-turns of one circle meet at their endpoints. *)
Lemma simple_cscc_egg_fixtures :
  loop_carrier iso_half_bag /\
  cscc_IsSimple iso_half_bag /\
  loop_fixpoint_adds_no_interior iso_half_bag.
Proof.
  assert (Hinv : bag_inv iso_half_bag) by apply iso_half_inv.
  assert (Hnl : ~ live_decline iso_half_pcs).
  { pose proof iso_half_no_decline as Hnd.
    unfold no_live_decline, iso_half_bag in Hnd. exact Hnd. }
  assert (Hpair : no_decline_pair iso_half_pcs).
  { intros a c Ha Hc Hneq Hd. apply Hnl. exists a, c.
    repeat split; assumption. }
  assert (Hcar : loop_carrier iso_half_bag).
  { unfold loop_carrier, iso_half_bag. split; assumption. }
  assert (Hz : rho_pcs iso_half_pcs = 0%nat) by exact iso_half_pair_rho_zero.
  assert (Hfix : loop_fixpoint_adds_no_interior iso_half_bag).
  { unfold loop_fixpoint_adds_no_interior, iso_half_bag, rho. rewrite Hz.
    assert (E : bag_run_arm 1%nat (BagLive default_sheet iso_half_pcs) =
                BagLive default_sheet iso_half_pcs).
    { apply (rho_zero_arm_fix 1%nat default_sheet iso_half_pcs Hinv Hpair Hz). }
    rewrite E. intros s p Hv. exact Hv. }
  split; [exact Hcar|]. split.
  - apply (proj2 (cscc_issimple iso_half_bag Hcar)). exact Hfix.
  - exact Hfix.
Qed.

(* Sample. Three chords meet off their vertices, so the carrier is not simple
   and the fixpoint has a vertex to add. *)
Lemma touch_egg_fixtures :
  loop_carrier x3_bag /\
  ~ cscc_IsSimple x3_bag /\
  ~ loop_fixpoint_adds_no_interior x3_bag.
Proof.
  assert (Hcar : loop_carrier x3_bag).
  { unfold loop_carrier, x3_bag. split; [apply x3_inv | apply x3_no_decline]. }
  assert (Hnot : ~ cscc_IsSimple x3_bag).
  { intros Hs.
    pose proof (proj1 (admissible_hit_spec x3_pcs x3_pcA x3_pcB
                         x3_pAB (1 / 2) (1 / 2)) x3_hit_AB) as Hadm.
    destruct Hadm as [Hok [Hnv Hov]].
    apply Hnv.
    unfold x3_bag in Hs. apply (Hs 0%nat 1%nat x3_pcA x3_pcB x3_pAB (1 / 2) (1 / 2)).
    - reflexivity.
    - reflexivity.
    - discriminate.
    - exact Hok.
    - intros Ho. apply Hov. exact Ho. }
  split; [exact Hcar|]. split; [exact Hnot|].
  intros Hfix. apply Hnot.
  apply (proj2 (cscc_issimple x3_bag Hcar)). exact Hfix.
Qed.

Print Assumptions step_hit_pieces.
Print Assumptions vertex_both_nn.
Print Assumptions cscc_IsSimple_noded_ov.
Print Assumptions missing_support_vertex.
Print Assumptions arm_keeps_family_vertex.
Print Assumptions positive_rho_adds_vertex.
Print Assumptions cscc_issimple.
Print Assumptions simple_cscc_egg_fixtures.
Print Assumptions touch_egg_fixtures.
