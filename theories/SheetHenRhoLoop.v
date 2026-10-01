(* ============================================================================
   NetTopologySuite.Proofs.SheetHenRhoLoop
   ----------------------------------------------------------------------------
   Letter 6a-ii. claimId: none.
   Headline: bag_run_arm_noded.
   rho_zero_noded_ov and rho_zero_iff_noded_ov under bag_inv and
   no_decline_pair. gap_bag_counted is the gap regression in
   SheetHenNodedOvGap. rho_zero_arm_fix is the identity at rho zero.
   CookLoopRho is rho_loop_discharged: the universal arm and selector
   confluence. The confluence conjunct is letter 6a-iii
   (run_vset_determined). cook_loop_rho_fixture is the iso-half bag
   alone. claimId: none on that fixture. cook_loop_status is
   LoopDischarged. Does not remint 0007-loop-letter6.
   3-axiom host. No Admitted.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List PeanoNat Bool.
From NTS.Proofs Require Import Distance SheetHenCook SheetHenCookCore SheetHenBag
  SheetHenRho SheetHenBagRun SheetHenLoop3 SheetHenBagRunFix SheetHenPickSpec
  SheetHenNodedOv HostCircChordOracle.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* A rho-zero live bag has no progress hit at a symmetric overlap endpoint.  *)
(* Same-support endpoints are vertices. Distinct supports would be counted.  *)
(* -------------------------------------------------------------------------- *)

Lemma fold_nat_in_zero : forall (A : Type) (g : A -> nat) xs y,
  fold_right Nat.add 0%nat (map g xs) = 0%nat ->
  In y xs -> g y = 0%nat.
Proof.
  intros A g xs y Hz Hin. induction xs as [|x tl IH]; [contradiction|].
  simpl in Hz. apply Nat.eq_add_0 in Hz. destruct Hz as [Hx Htl].
  destruct Hin as [->|Hin]; [exact Hx| apply IH; assumption].
Qed.

Lemma pair_sum_cell_zero : forall ss f a b,
  NoDup ss ->
  (forall x y, f x y = f y x) ->
  pair_sum ss f = 0%nat ->
  In a ss -> In b ss -> a <> b ->
  f a b = 0%nat.
Proof.
  induction ss as [|s tl IH]; intros f a b Hnd Hsym Hz Ha Hb Hneq.
  - contradiction.
  - simpl in Hz. apply Nat.eq_add_0 in Hz. destruct Hz as [Hf Hp].
    apply NoDup_cons_iff in Hnd. destruct Hnd as [_ Hnd].
    destruct Ha as [Ea|Ha]; destruct Hb as [Eb|Hb].
    + rewrite Ea in Eb. exfalso. exact (Hneq Eb).
    + rewrite <- Ea. apply (fold_nat_in_zero _ (f s) tl b Hf Hb).
    + rewrite <- Eb. rewrite (Hsym a s).
      apply (fold_nat_in_zero _ (f s) tl a Hf Ha).
    + apply IH; assumption.
Qed.

Lemma rho_zero_counted_nil : forall pcs s1 s2,
  rho_pcs pcs = 0%nat ->
  In s1 (supports_of pcs) ->
  In s2 (supports_of pcs) ->
  s1 <> s2 ->
  counted pcs s1 s2 = nil.
Proof.
  intros pcs s1 s2 Hz Hs1 Hs2 Hneq.
  assert (E : length (counted pcs s1 s2) = 0%nat).
  { unfold rho_pcs in Hz.
    apply (pair_sum_cell_zero (supports_of pcs)
             (fun x y => length (counted pcs x y)) s1 s2);
      [apply supports_NoDup| | exact Hz| exact Hs1| exact Hs2| exact Hneq].
    intros x y. rewrite counted_sym. reflexivity. }
  destruct (counted pcs s1 s2); [reflexivity| simpl in E; discriminate].
Qed.

Lemma canon_self : forall s, canon2 s s = (s, s).
Proof.
  intro s. unfold canon2. rewrite rlex_refl. reflexivity.
Qed.

Lemma same_circle_refl : forall c, same_circle_b c c = true.
Proof.
  intro c. unfold same_circle_b.
  apply andb_true_intro. split; [apply pt_eqb_true; reflexivity| apply req_b_true; ring].
Qed.

Lemma overlap_b_same_circle : forall c,
  overlap_b (SuppCircle c) (SuppCircle c) = true.
Proof.
  intro c. unfold overlap_b. rewrite canon_self. simpl. apply same_circle_refl.
Qed.

Lemma circ_self_vertex : forall pcs c p,
  In p (circ_overlap_pts pcs c c) ->
  family_vertex pcs (SuppCircle c) p.
Proof.
  intros pcs c p Hin.
  unfold circ_overlap_pts in Hin. rewrite dedup_In in Hin.
  apply filter_In in Hin. destruct Hin as [_ Hb].
  unfold circ_end_in_other_b in Hb. apply orb_prop in Hb.
  destruct Hb as [Hb|Hb]; apply andb_prop in Hb; destruct Hb as [He _];
    unfold boundary_end_b in He; apply andb_prop in He; destruct He as [Hv _];
    apply vertex_spec; exact Hv.
Qed.

Lemma chord_deg_self_vertex : forall pcs c p,
  chord_dd c = 0 ->
  In p (overlap_pts pcs (SuppChord c) (SuppChord c)) ->
  family_vertex pcs (SuppChord c) p.
Proof.
  intros pcs c p Hd Hin.
  unfold overlap_pts in Hin.
  destruct (all_keys (SuppChord c) (SuppChord c) pcs) as [|k tl] eqn:Eks.
  - destruct Hin.
  - assert (Eb : req_b (chord_dd c) 0 = true) by (apply req_b_true; exact Hd).
    destruct (rle_b (Rmax (rmin_list (k :: tl)) (rmin_list (k :: tl)))
                    (Rmin (rmax_list (k :: tl)) (rmax_list (k :: tl)))).
    + rewrite dedup_In in Hin.
      assert (Hp : p = ce_p0 c).
      { destruct Hin as [<-|[<-|[]]]; unfold point_of_key; rewrite Eb; reflexivity. }
      subst p.
      assert (Hk : In k (all_keys (SuppChord c) (SuppChord c) pcs)).
      { rewrite Eks. left. reflexivity. }
      apply in_flat_map in Hk. destruct Hk as [pc [Hpc Hkeys]].
      unfold piece_keys in Hkeys.
      destruct (support_eqb (bp_support pc) (SuppChord c)) eqn:Heq.
      * apply support_eqb_true in Heq.
        exists pc. split; [exact Hpc|]. split; [exact Heq|].
        left. unfold support_at. rewrite Heq. symmetry. apply chord_eval_deg. exact Hd.
      * simpl in Hkeys. contradiction.
    + destruct Hin.
Qed.

Lemma self_overlap_vertex : forall pcs s p,
  In p (overlap_endpoints pcs s s) ->
  family_vertex pcs s p.
Proof.
  intros pcs s p Hin.
  unfold overlap_endpoints in Hin. rewrite canon_self in Hin.
  destruct s as [c|c]; simpl in Hin.
  - destruct (Req_EM_T (chord_dd c) 0) as [Hd|Hd].
    + apply chord_deg_self_vertex; assumption.
    + apply chord_self_overlap_vertex; assumption.
  - apply circ_self_vertex. exact Hin.
Qed.

Theorem rho_zero_noded_ov : forall sh pcs,
  bag_inv (BagLive sh pcs) ->
  no_decline_pair pcs ->
  rho_pcs pcs = 0%nat ->
  bag_noded_ov (BagLive sh pcs).
Proof.
  intros sh pcs Hinv _ Hz i j a c p ti tj Hi Hj Hij Hok Hante.
  cbn [progress_hit]. intro Hnot.
  destruct (support_eqb (bp_support a) (bp_support c)) eqn:Eeq.
  - apply support_eqb_true in Eeq. apply Hnot. rewrite Eeq in *.
    split.
    + apply self_overlap_vertex. apply Hante. unfold overlap_pair.
      destruct (bp_support c) as [ch|ci];
        [apply overlap_b_same_chord | apply overlap_b_same_circle].
    + apply self_overlap_vertex. apply Hante. unfold overlap_pair.
      destruct (bp_support c) as [ch|ci];
        [apply overlap_b_same_chord | apply overlap_b_same_circle].
  - assert (Hdist : bp_support a <> bp_support c).
    { intro E. apply support_eqb_true in E. congruence. }
    assert (Hadm : admissible_hit pcs a c p ti tj).
    { split; [exact Hok|]. split; [exact Hnot|].
      intro Ho. apply Hante. unfold overlap, overlap_pair in *. exact Ho. }
    assert (HinC : In p (counted pcs (bp_support a) (bp_support c))).
    { apply (admissible_in_counted pcs a c p ti tj).
      - eapply nth_error_In. exact Hi.
      - eapply nth_error_In. exact Hj.
      - apply Hinv. eapply nth_error_In. exact Hi.
      - apply Hinv. eapply nth_error_In. exact Hj.
      - exact Hdist.
      - exact Hadm. }
    assert (Hnil : counted pcs (bp_support a) (bp_support c) = nil).
    { apply rho_zero_counted_nil; [exact Hz| | | exact Hdist].
      - apply supports_in. exists a.
        split; [eapply nth_error_In; exact Hi| reflexivity].
      - apply supports_in. exists c.
        split; [eapply nth_error_In; exact Hj| reflexivity]. }
    rewrite Hnil in HinC. destruct HinC.
Qed.

Theorem rho_zero_iff_noded_ov : forall sh pcs,
  bag_inv (BagLive sh pcs) ->
  no_decline_pair pcs ->
  rho_pcs pcs = 0%nat <-> bag_noded_ov (BagLive sh pcs).
Proof.
  intros sh pcs Hinv Hnd. split.
  - apply rho_zero_noded_ov; assumption.
  - apply noded_ov_rho_zero; assumption.
Qed.

Lemma rho_zero_arm_fix : forall fuel sh pcs,
  bag_inv (BagLive sh pcs) ->
  no_decline_pair pcs ->
  rho_pcs pcs = 0%nat ->
  bag_run_arm fuel (BagLive sh pcs) = BagLive sh pcs.
Proof.
  intros fuel sh pcs Hinv Hnd Hz.
  destruct fuel as [|fuel]; [reflexivity|].
  cbn [bag_run_arm].
  assert (E : arm_next (BagLive sh pcs) = None).
  { unfold arm_next.
    assert (Harm : pick_arm (BagLive sh pcs) = ArmStop).
    { apply zero_live_is_stop; [exact Hinv| unfold rho; exact Hz|].
      unfold no_live_decline.
      apply (proj2 (live_decline_forall pcs)). exact Hnd. }
    rewrite Harm. reflexivity. }
  rewrite E. reflexivity.
Qed.

Lemma step_hit_sheet : forall sh pcs w,
  match step_hit (BagLive sh pcs) w with
  | BagLive sh' _ => sh' = sh
  | BagDeclined sh' => sh' = sh
  end.
Proof.
  intros sh pcs w. unfold step_hit. simpl.
  destruct (nth_error pcs (hp_i w));
  destruct (nth_error pcs (hp_j w)); reflexivity.
Qed.

(* Steps keep the sheet, so the live arm's pcs' is still BagLive sh. *)
Lemma bag_run_arm_keeps_sheet : forall fuel sh pcs,
  match bag_run_arm fuel (BagLive sh pcs) with
  | BagLive sh' _ => sh' = sh
  | BagDeclined sh' => sh' = sh
  end.
Proof.
  induction fuel as [|fuel IH]; intros sh pcs; [reflexivity|].
  cbn [bag_run_arm]. unfold arm_next.
  destruct (pick_arm (BagLive sh pcs)) eqn:Harm.
  - destruct (pick_bag (BagLive sh pcs)) as [w|] eqn:Hw.
    + pose proof (step_hit_sheet sh pcs w) as Esh.
      destruct (step_hit (BagLive sh pcs) w) as [sh1 pcs1|sh1] eqn:Es.
      * simpl in Esh. subst sh1. apply IH.
      * simpl in Esh. subst sh1. rewrite bag_run_arm_declined. reflexivity.
    + reflexivity.
  - cbn [step_decline]. rewrite bag_run_arm_declined. reflexivity.
  - reflexivity.
Qed.

Theorem bag_run_arm_noded : forall sh pcs,
  bag_inv (BagLive sh pcs) ->
  match bag_run_arm (S (rho_pcs pcs)) (BagLive sh pcs) with
  | BagDeclined _ => True
  | BagLive _ pcs' => bag_noded_ov (BagLive sh pcs') /\ bag_inv (BagLive sh pcs')
  end.
Proof.
  intros sh pcs Hinv.
  pose proof (bag_run_arm_spec (BagLive sh pcs) Hinv) as Hs.
  pose proof (bag_run_arm_inv (S (rho_pcs pcs)) (BagLive sh pcs) Hinv) as Hi.
  pose proof (bag_run_arm_keeps_sheet (S (rho_pcs pcs)) sh pcs) as Hsh.
  cbn [rho] in Hs.
  destruct (bag_run_arm (S (rho_pcs pcs)) (BagLive sh pcs))
    as [sh' pcs'|sh'] eqn:E.
  - simpl in Hs, Hi, Hsh. subst sh'.
    destruct Hs as [Hz Hnd]. split.
    + apply rho_zero_noded_ov; [exact Hi| | exact Hz].
      unfold no_decline_pair. apply (proj1 (live_decline_forall pcs')). exact Hnd.
    + exact Hi.
  - exact I.
Qed.

(* A selector is lawful when every answer is a real admissible hit and an
   existing admissible hit is not answered by None. *)
Definition selector : Type := SheetBag -> option HitPick.

Definition has_adm_hit (pcs : list BagPiece) : Prop :=
  exists i j a c p ti tj,
    nth_error pcs i = Some a /\
    nth_error pcs j = Some c /\
    i <> j /\
    piece_wf a /\
    piece_wf c /\
    bp_support a <> bp_support c /\
    admissible_hit pcs a c p ti tj.

Definition lawful (pick : selector) : Prop :=
  (forall b, pick_spec pick b) /\
  (forall sh pcs,
     bag_inv (BagLive sh pcs) ->
     has_adm_hit pcs ->
     pick (BagLive sh pcs) <> None).

Definition vmem (pcs : list BagPiece) (p : Point) : Prop :=
  exists pc, In pc pcs /\ piece_endpoint pc p.

Definition vset_eq (pcs1 pcs2 : list BagPiece) : Prop :=
  forall p, vmem pcs1 p <-> vmem pcs2 p.

Definition run_pcs (pick : selector) (b : SheetBag) : list BagPiece :=
  match bag_run pick (S (rho b)) b with
  | BagLive _ pcs => pcs
  | BagDeclined _ => nil
  end.

(* Universal arm, and vertex-set independence of two lawful selectors.
   The second conjunct is discharged by run_vset_determined (6a-iii). *)
Definition rho_loop_discharged : Prop :=
  (forall sh pcs,
     bag_inv (BagLive sh pcs) ->
     match bag_run_arm (S (rho_pcs pcs)) (BagLive sh pcs) with
     | BagDeclined _ => True
     | BagLive _ pcs' =>
         bag_noded_ov (BagLive sh pcs') /\ bag_inv (BagLive sh pcs')
     end) /\
  (forall pick1 pick2 sh pcs,
     lawful pick1 ->
     lawful pick2 ->
     bag_inv (BagLive sh pcs) ->
     no_decline_pair pcs ->
     vset_eq (run_pcs pick1 (BagLive sh pcs))
             (run_pcs pick2 (BagLive sh pcs))).

Definition CookLoopRho : Prop := rho_loop_discharged.

(* Fixture. One already-noded bag. claimId: none. This is not CookLoopRho. *)
Lemma cook_loop_rho_fixture :
  bag_inv iso_half_bag /\
  no_decline_pair iso_half_pcs /\
  (rho_pcs iso_half_pcs = 0%nat <-> bag_noded_ov iso_half_bag) /\
  (forall fuel, bag_run_arm fuel iso_half_bag = iso_half_bag).
Proof.
  assert (Hinv : bag_inv iso_half_bag) by apply iso_half_inv.
  assert (Hnd : no_decline_pair iso_half_pcs).
  { unfold no_decline_pair.
    apply (proj1 (live_decline_forall iso_half_pcs)).
    exact iso_half_no_decline. }
  assert (Hz : rho_pcs iso_half_pcs = 0%nat) by exact iso_half_pair_rho_zero.
  split; [exact Hinv|].
  split; [exact Hnd|].
  split.
  - apply rho_zero_iff_noded_ov; [exact Hinv| exact Hnd].
  - intro fuel. unfold iso_half_bag.
    apply rho_zero_arm_fix; [exact Hinv| exact Hnd| exact Hz].
Qed.

Lemma cook_loop_rho_status :
  cook_loop_status = LoopDischarged /\ cook_loop_status <> LoopObligation.
Proof.
  split; [apply cook_loop_is_discharged| apply cook_loop_not_obligation].
Qed.

Print Assumptions fold_nat_in_zero.
Print Assumptions pair_sum_cell_zero.
Print Assumptions rho_zero_counted_nil.
Print Assumptions canon_self.
Print Assumptions same_circle_refl.
Print Assumptions overlap_b_same_circle.
Print Assumptions circ_self_vertex.
Print Assumptions chord_deg_self_vertex.
Print Assumptions self_overlap_vertex.
Print Assumptions rho_zero_noded_ov.
Print Assumptions rho_zero_iff_noded_ov.
Print Assumptions rho_zero_arm_fix.
Print Assumptions step_hit_sheet.
Print Assumptions bag_run_arm_keeps_sheet.
Print Assumptions bag_run_arm_noded.
Print Assumptions cook_loop_rho_fixture.
Print Assumptions cook_loop_rho_status.
