(* ============================================================================
   NetTopologySuite.Proofs.SheetHenSimple
   ----------------------------------------------------------------------------
   CS/CC rung 3. claimId: 0007-cscc-issimple. witness: cscc_issimple.
   On a carrier the loop accepts, IsSimple (pieces meet only at shared
   vertices, and no two pieces coincide_same) holds iff the arm fixpoint
   adds no interior vertex and no two pieces coincide. A retrace adds no
   vertex yet is not simple: bag_noded_ov allows coincident pieces.
   Reads the loop. Does not edit it.
   simple_cscc_egg_fixtures / touch_egg_fixtures / retrace_fixtures /
   spike_ring_fixtures are samples. claimId: none.
   3-axiom host. No Admitted.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List PeanoNat Bool.
From NTS.Proofs Require Import
  Distance SheetHenCook SheetHenCookCore SheetHenCircEgg SheetHenBag
  SheetHenRho SheetHenBagRun SheetHenLoop3 SheetHenPickSpec
  SheetHenNodedOv SheetHenRhoLoop SheetHenBagRunFix SheetHenRhoConfFix
  SheetHenRhoWitness SheetHenRhoCount SheetHenRhoCarrier.
Import ListNotations.
Local Open Scope R_scope.

(* A live chord/circle bag the loop will run: well-formed, no decline. *)
Definition loop_carrier (b : SheetBag) : Prop :=
  match b with
  | BagDeclined _ => False
  | BagLive _ pcs => bag_inv b /\ no_decline_pair pcs
  end.

(* Every common point of two pieces is a vertex of both supports. *)
Definition cscc_meets_at_vertices (b : SheetBag) : Prop :=
  match b with
  | BagDeclined _ => False
  | BagLive _ pcs =>
      forall i j a c p ti tj,
        nth_error pcs i = Some a ->
        nth_error pcs j = Some c ->
        i <> j ->
        I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck c)) (IHit p ti tj) ->
        family_vertex pcs (bp_support a) p /\
        family_vertex pcs (bp_support c) p
  end.

(* Letter 1's coincide_same at two indices: a piece laid twice. *)
Definition cscc_no_same_pieces (b : SheetBag) : Prop :=
  match b with
  | BagDeclined _ => False
  | BagLive _ pcs =>
      forall i j a c,
        nth_error pcs i = Some a ->
        nth_error pcs j = Some c ->
        i <> j -> ~ coincide_same a c
  end.

Definition cscc_IsSimple (b : SheetBag) : Prop :=
  cscc_meets_at_vertices b /\ cscc_no_same_pieces b.

(* Two pieces coincide: coincide_same, or overlapping supports sharing a
   point that is not a vertex of both. bag_noded_ov allows the second. *)
Definition pieces_coincide (pcs : list BagPiece) (a c : BagPiece) : Prop :=
  coincide_same a c \/
  (overlap (bp_support a) (bp_support c) /\
   exists p ti tj,
     I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck c)) (IHit p ti tj) /\
     ~ vertex_of_both pcs (bp_support a) (bp_support c) p).

Definition no_coincident_pieces (b : SheetBag) : Prop :=
  match b with
  | BagDeclined _ => False
  | BagLive _ pcs =>
      forall i j a c,
        nth_error pcs i = Some a ->
        nth_error pcs j = Some c ->
        i <> j -> ~ pieces_coincide pcs a c
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

Lemma meets_at_vertices_noded_ov : forall sh pcs,
  cscc_meets_at_vertices (BagLive sh pcs) -> bag_noded_ov (BagLive sh pcs).
Proof.
  intros sh pcs H i j a c p ti tj Hi Hj Hij Hok _.
  unfold progress_hit. intros Hnot. apply Hnot.
  exact (H i j a c p ti tj Hi Hj Hij Hok).
Qed.

Lemma noded_ov_meets_at_vertices : forall sh pcs,
  bag_noded_ov (BagLive sh pcs) ->
  no_coincident_pieces (BagLive sh pcs) ->
  cscc_meets_at_vertices (BagLive sh pcs).
Proof.
  intros sh pcs Hov Hnc i j a c p ti tj Hi Hj Hij Hok.
  apply vertex_both_nn. intros Hnv.
  destruct (overlap_b (bp_support a) (bp_support c)) eqn:Eo.
  - apply (Hnc i j a c Hi Hj Hij). right. split; [exact Eo|].
    exists p, ti, tj. split; [exact Hok| exact Hnv].
  - apply (Hov i j a c p ti tj Hi Hj Hij Hok).
    + intros Ho. unfold overlap_pair in Ho. congruence.
    + exact Hnv.
Qed.

Lemma simple_no_coincident : forall sh pcs,
  cscc_IsSimple (BagLive sh pcs) -> no_coincident_pieces (BagLive sh pcs).
Proof.
  intros sh pcs [Hm Hs] i j a c Hi Hj Hij [Hsame|[_ [p [ti [tj [Hok Hnv]]]]]].
  - exact (Hs i j a c Hi Hj Hij Hsame).
  - apply Hnv. exact (Hm i j a c p ti tj Hi Hj Hij Hok).
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

Lemma fixpoint_iff_noded_ov : forall sh pcs,
  loop_carrier (BagLive sh pcs) ->
  loop_fixpoint_adds_no_interior (BagLive sh pcs) <->
  bag_noded_ov (BagLive sh pcs).
Proof.
  intros sh pcs [Hinv Hnd]. split.
  - intros Hfix.
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
  - intros Hov.
    assert (Hz : rho_pcs pcs = 0%nat).
    { apply (noded_ov_rho_zero sh pcs Hinv Hnd Hov). }
    assert (Erun : bag_run_arm (S (rho (BagLive sh pcs))) (BagLive sh pcs) =
                   BagLive sh pcs).
    { unfold rho. rewrite Hz.
      apply (rho_zero_arm_fix 1%nat sh pcs Hinv Hnd Hz). }
    unfold loop_fixpoint_adds_no_interior. rewrite Erun.
    intros s p Hv. exact Hv.
Qed.

(* WITNESS {"claimId":"0007-cscc-issimple","topic":"overlay","lemma":"cscc_issimple","title":"CS/CC IsSimple iff the loop fixpoint adds no interior vertex and no two pieces coincide","file":"theories/SheetHenSimple.v","witness":"cscc_issimple","board":"ADR-0007"} *)
Theorem cscc_issimple : forall b,
  loop_carrier b ->
  cscc_IsSimple b <->
  loop_fixpoint_adds_no_interior b /\ no_coincident_pieces b.
Proof.
  intros b Hcar. destruct b as [sh pcs|sh]; [| exact (False_rect _ Hcar)].
  split.
  - intros Hs. split.
    + apply (proj2 (fixpoint_iff_noded_ov sh pcs Hcar)).
      apply meets_at_vertices_noded_ov. exact (proj1 Hs).
    + apply simple_no_coincident. exact Hs.
  - intros [Hfix Hnc]. split.
    + apply noded_ov_meets_at_vertices; [| exact Hnc].
      apply (proj1 (fixpoint_iff_noded_ov sh pcs Hcar)). exact Hfix.
    + intros i j a c Hi Hj Hij Hsame.
      apply (Hnc i j a c Hi Hj Hij). left. exact Hsame.
Qed.

(* -------------------------------------------------------------------------- *)
(* Sample. Two half-turns of one circle meet only at their two endpoints.   *)
(* -------------------------------------------------------------------------- *)

Lemma iso_halves_meet_at_ends : forall ti tj p,
  on_circ (window_circ iso_half_fst (mkWindow 0 1)) ti p ->
  on_circ (window_circ iso_half_snd (mkWindow 0 1)) tj p ->
  p = mkPoint 5 0 \/ p = mkPoint (-5) 0.
Proof.
  intros ti tj p [Hti Hp] [Htj Hq].
  unfold window_circ, circ_eval, iso_half_fst, iso_half_snd in Hp, Hq.
  cbn [circ_o circ_r circ_theta0 circ_sweep win_lo win_hi px py] in Hp, Hq.
  rewrite Hp in Hq. injection Hq as _ Hy.
  replace (0 + 0 * PI + ti * ((1 - 0) * PI)) with (ti * PI) in Hp, Hy by ring.
  replace (PI + 0 * PI + tj * ((1 - 0) * PI)) with (tj * PI + PI) in Hy by ring.
  rewrite neg_sin in Hy.
  pose proof PI_RGT_0 as Hpi.
  assert (Si : 0 <= sin (ti * PI)).
  { apply sin_ge_0; nra. }
  assert (Sj : 0 <= sin (tj * PI)).
  { apply sin_ge_0; nra. }
  assert (Z : sin (ti * PI) = 0) by lra.
  destruct (Req_dec ti 0) as [E0|N0].
  - left. rewrite Hp, E0.
    replace (0 * PI) with 0 by ring. rewrite cos_0, sin_0.
    apply (f_equal2 mkPoint); ring.
  - destruct (Req_dec ti 1) as [E1|N1].
    + right. rewrite Hp, E1.
      replace (1 * PI) with PI by ring. rewrite cos_PI, sin_PI.
      apply (f_equal2 mkPoint); ring.
    + exfalso.
      assert (Pos : 0 < sin (ti * PI)).
      { apply sin_gt_0.
        - apply Rmult_lt_0_compat; [lra| exact Hpi].
        - assert (ti < 1) by lra. nra. }
      lra.
Qed.

Lemma iso_half_meets_at_vertices : cscc_meets_at_vertices iso_half_bag.
Proof.
  unfold iso_half_bag, cscc_meets_at_vertices.
  intros i j a c p ti tj Hi Hj Hij Hok.
  assert (Hi2 : (i < 2)%nat) by (apply (nth_length _ _ _ _ Hi)).
  assert (Hj2 : (j < 2)%nat) by (apply (nth_length _ _ _ _ Hj)).
  destruct i as [|[|i]]; destruct j as [|[|j]]; try lia.
  - simpl in Hi, Hj. inversion Hi. inversion Hj. subst a c.
    destruct Hok as [Ha Hc].
    exact (iso_antipode_hens p (iso_halves_meet_at_ends ti tj p Ha Hc)).
  - simpl in Hi, Hj. inversion Hi. inversion Hj. subst a c.
    destruct Hok as [Ha Hc].
    destruct (iso_antipode_hens p (iso_halves_meet_at_ends tj ti p Hc Ha))
      as [Vf Vs].
    split; [exact Vs| exact Vf].
Qed.

Lemma iso_half_no_same_pieces : cscc_no_same_pieces iso_half_bag.
Proof.
  unfold iso_half_bag, cscc_no_same_pieces.
  intros i j a c Hi Hj Hij [Hs _].
  assert (Hi2 : (i < 2)%nat) by (apply (nth_length _ _ _ _ Hi)).
  assert (Hj2 : (j < 2)%nat) by (apply (nth_length _ _ _ _ Hj)).
  destruct i as [|[|i]]; destruct j as [|[|j]]; try lia.
  - simpl in Hi, Hj. inversion Hi. inversion Hj. subst a c.
    apply iso_supports_distinct. exact Hs.
  - simpl in Hi, Hj. inversion Hi. inversion Hj. subst a c.
    apply iso_supports_distinct. symmetry. exact Hs.
Qed.

Lemma simple_cscc_egg_fixtures :
  loop_carrier iso_half_bag /\
  cscc_IsSimple iso_half_bag /\
  loop_fixpoint_adds_no_interior iso_half_bag /\
  no_coincident_pieces iso_half_bag.
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
  assert (Hs : cscc_IsSimple iso_half_bag).
  { split; [exact iso_half_meets_at_vertices| exact iso_half_no_same_pieces]. }
  destruct (proj1 (cscc_issimple iso_half_bag Hcar) Hs) as [Hfix Hnc].
  exact (conj Hcar (conj Hs (conj Hfix Hnc))).
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
  pose proof (proj1 (admissible_hit_spec x3_pcs x3_pcA x3_pcB
                       x3_pAB (1 / 2) (1 / 2)) x3_hit_AB) as Hadm.
  destruct Hadm as [Hok [Hnv Hov]].
  assert (Hnot : ~ cscc_IsSimple x3_bag).
  { intros [Hs _]. apply Hnv.
    unfold x3_bag in Hs.
    apply (Hs 0%nat 1%nat x3_pcA x3_pcB x3_pAB (1 / 2) (1 / 2));
      [reflexivity| reflexivity| discriminate| exact Hok]. }
  split; [exact Hcar|]. split; [exact Hnot|].
  intros Hfix.
  apply (proj1 (fixpoint_iff_noded_ov default_sheet x3_pcs Hcar)) in Hfix.
  apply (Hfix 0%nat 1%nat x3_pcA x3_pcB x3_pAB (1 / 2) (1 / 2));
    [reflexivity| reflexivity| discriminate| exact Hok| | exact Hnv].
  intros Ho. apply Hov. exact Ho.
Qed.

(* -------------------------------------------------------------------------- *)
(* Retrace A -> B -> A. Piece 1 lays piece 0's chord again, so coincide_same. *)
(* The fixpoint adds no vertex (rho = 0), yet the carrier is not simple.    *)
(* -------------------------------------------------------------------------- *)

Definition retrace_A : Point := mkPoint 0 0.
Definition retrace_B : Point := mkPoint 1 0.
Definition retrace_chord : ChordEgg := mkChordEgg retrace_A retrace_B.
Definition unit_chord_pc (src dst : nat) (c : ChordEgg) : BagPiece :=
  mkBagPiece (mkChicken src dst (MkChord (window_chord c (mkWindow 0 1))))
             (SuppChord c) (mkWindow 0 1) nil.
Definition retrace_pcs : list BagPiece :=
  [unit_chord_pc 0 1 retrace_chord; unit_chord_pc 1 0 retrace_chord].
Definition retrace_bag : SheetBag := BagLive default_sheet retrace_pcs.

Lemma unit_chord_pc_wf : forall n m c, piece_wf (unit_chord_pc n m c).
Proof.
  intros n m c. unfold piece_wf, piece_realizes, unit_chord_pc. cbn.
  split; [reflexivity| unfold window_ordered; cbn; lra].
Qed.

Lemma unit_chord_pcs_inv : forall sh pcs,
  (forall pc, In pc pcs -> exists n m c, pc = unit_chord_pc n m c) ->
  bag_inv (BagLive sh pcs).
Proof.
  intros sh pcs H pc Hin. destruct (H pc Hin) as [n [m [c ->]]].
  apply unit_chord_pc_wf.
Qed.

Lemma retrace_rho : rho_pcs retrace_pcs = 0%nat.
Proof.
  unfold rho_pcs, retrace_pcs. cbn [supports_of bp_support unit_chord_pc existsb].
  rewrite support_eqb_refl. reflexivity.
Qed.

Lemma retrace_carrier : loop_carrier retrace_bag.
Proof.
  unfold loop_carrier, retrace_bag. split.
  - apply unit_chord_pcs_inv. intros pc Hin.
    destruct Hin as [<-|[<-|[]]]; eexists; eexists; eexists; reflexivity.
  - intros a c Ha Hc _ Hd.
    destruct Ha as [<-|[<-|[]]]; destruct Hc as [<-|[<-|[]]]; exact Hd.
Qed.

Lemma retrace_fixtures :
  loop_carrier retrace_bag /\
  loop_fixpoint_adds_no_interior retrace_bag /\
  ~ no_coincident_pieces retrace_bag /\
  ~ cscc_IsSimple retrace_bag.
Proof.
  assert (Hsame : ~ cscc_no_same_pieces retrace_bag).
  { intros H. apply (H 0%nat 1%nat (unit_chord_pc 0 1 retrace_chord)
                      (unit_chord_pc 1 0 retrace_chord));
      [reflexivity| reflexivity| discriminate|].
    split; reflexivity. }
  split; [exact retrace_carrier|]. split.
  - unfold loop_fixpoint_adds_no_interior, retrace_bag, rho.
    rewrite retrace_rho.
    assert (E : bag_run_arm 1%nat (BagLive default_sheet retrace_pcs) =
                BagLive default_sheet retrace_pcs).
    { apply (rho_zero_arm_fix 1%nat default_sheet retrace_pcs).
      - exact (proj1 retrace_carrier).
      - exact (proj2 retrace_carrier).
      - exact retrace_rho. }
    rewrite E. intros s p Hv. exact Hv.
  - split.
    + intros Hnc. apply Hsame. intros i j a c Hi Hj Hij Hs.
      apply (Hnc i j a c Hi Hj Hij). left. exact Hs.
    + intros [_ Hs]. exact (Hsame Hs).
Qed.

(* -------------------------------------------------------------------------- *)
(* Zero-area spike. Triangle A -> B -> C -> A with the spike B -> S -> B     *)
(* laid at B: the out and back pieces coincide_same. Not simple.            *)
(* -------------------------------------------------------------------------- *)

Definition spike_A : Point := mkPoint 0 0.
Definition spike_B : Point := mkPoint 2 0.
Definition spike_C : Point := mkPoint 1 2.
Definition spike_S : Point := mkPoint 3 (-1).
Definition spike_pcs : list BagPiece :=
  [unit_chord_pc 0 1 (mkChordEgg spike_A spike_B);
   unit_chord_pc 1 2 (mkChordEgg spike_B spike_S);
   unit_chord_pc 2 1 (mkChordEgg spike_B spike_S);
   unit_chord_pc 1 3 (mkChordEgg spike_B spike_C);
   unit_chord_pc 3 0 (mkChordEgg spike_C spike_A)].
Definition spike_bag : SheetBag := BagLive default_sheet spike_pcs.

Lemma spike_ring_fixtures :
  bag_inv spike_bag /\
  ~ no_coincident_pieces spike_bag /\
  ~ cscc_IsSimple spike_bag.
Proof.
  assert (Hsame : ~ cscc_no_same_pieces spike_bag).
  { intros H.
    apply (H 1%nat 2%nat (unit_chord_pc 1 2 (mkChordEgg spike_B spike_S))
             (unit_chord_pc 2 1 (mkChordEgg spike_B spike_S)));
      [reflexivity| reflexivity| discriminate|].
    split; reflexivity. }
  split.
  - apply unit_chord_pcs_inv. intros pc Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]];
      eexists; eexists; eexists; reflexivity.
  - split.
    + intros Hnc. apply Hsame. intros i j a c Hi Hj Hij Hs.
      apply (Hnc i j a c Hi Hj Hij). left. exact Hs.
    + intros [_ Hs]. exact (Hsame Hs).
Qed.

Print Assumptions step_hit_pieces.
Print Assumptions vertex_both_nn.
Print Assumptions meets_at_vertices_noded_ov.
Print Assumptions noded_ov_meets_at_vertices.
Print Assumptions simple_no_coincident.
Print Assumptions missing_support_vertex.
Print Assumptions arm_keeps_family_vertex.
Print Assumptions positive_rho_adds_vertex.
Print Assumptions fixpoint_iff_noded_ov.
Print Assumptions cscc_issimple.
Print Assumptions iso_halves_meet_at_ends.
Print Assumptions iso_half_meets_at_vertices.
Print Assumptions iso_half_no_same_pieces.
Print Assumptions simple_cscc_egg_fixtures.
Print Assumptions touch_egg_fixtures.
Print Assumptions unit_chord_pc_wf.
Print Assumptions unit_chord_pcs_inv.
Print Assumptions retrace_rho.
Print Assumptions retrace_carrier.
Print Assumptions retrace_fixtures.
Print Assumptions spike_ring_fixtures.
