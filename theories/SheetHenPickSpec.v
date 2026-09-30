(* ============================================================================
   NetTopologySuite.Proofs.SheetHenPickSpec
   ----------------------------------------------------------------------------
   Headline: pick_bag_spec. claimId: 0007-loop-letter5-pick.
   Witness: pick_bag_spec. Consumer: letter5_obligation.
   The concrete pick_bag has three arms. ArmHit is a returned hit.
   ArmDecline is a live IDecline pair, and pick_bag returns None.
   ArmStop is the None arm: no live IDecline pair, so rho is 0.
   Proved from scan completeness and hit_param_line_line,
   hit_param_line_circle, hit_param_circle_circle (via adm_list_covers).
   Does not remint 0007-loop-letter3-strict.
   3-axiom host. No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lia List PeanoNat Bool.
From NTS.Proofs Require Import SheetHenCook SheetHenBag SheetHenRho
  SheetHenBagRun SheetHenLoop3.
Import ListNotations.
Local Open Scope R_scope.

Lemma nth_length : forall (A : Type) (l : list A) n (x : A),
  nth_error l n = Some x -> (n < length l)%nat.
Proof.
  intros A l n x. revert l.
  induction n as [|n IH]; intros [|h t] H; simpl in *; try discriminate.
  - lia.
  - apply IH in H. lia.
Qed.

Lemma nth_none_ge : forall (A : Type) (l : list A) n,
  nth_error l n = None -> (length l <= n)%nat.
Proof.
  intros A l n. revert l.
  induction n as [|n IH]; intros [|h t] H; simpl in *; try discriminate.
  - lia.
  - lia.
  - apply IH in H. lia.
Qed.

Lemma fold_nat_zero : forall (A : Type) (g : A -> nat) xs,
  (forall y, In y xs -> g y = 0%nat) ->
  fold_right Nat.add 0%nat (map g xs) = 0%nat.
Proof.
  intros A g xs Hg. induction xs as [|y tl IH]; simpl; [reflexivity|].
  rewrite (Hg y (or_introl eq_refl)).
  rewrite IH; [reflexivity|].
  intros z Hz. apply Hg. right. exact Hz.
Qed.

Lemma pair_sum_offdiag_zero : forall ss f,
  NoDup ss ->
  (forall a b, In a ss -> In b ss -> a <> b -> f a b = 0%nat) ->
  pair_sum ss f = 0%nat.
Proof.
  induction ss as [|s tl IH]; intros f Hnd Hz; simpl; [reflexivity|].
  inversion Hnd as [|s0 tl0 Hnin Hnd']; subst.
  rewrite fold_nat_zero.
  - rewrite IH; [reflexivity| exact Hnd'|].
    intros a b Ha Hb Hneq. apply Hz; [right| right|]; assumption.
  - intros y Hy. apply Hz; [left; reflexivity| right; exact Hy|].
    intro E. subst y. exact (Hnin Hy).
Qed.

Lemma some_inj : forall (A : Type) (x y : A), Some x = Some y -> x = y.
Proof.
  intros A x y H. inversion H. reflexivity.
Qed.

Lemma least_nil : forall cs, least_ti cs = None -> cs = nil.
Proof.
  intros [|c tl] H; [reflexivity|].
  simpl in H. destruct (least_ti tl) as [d|];
    [destruct (rle_b (hc_ti c) (hc_ti d))|]; discriminate.
Qed.

Lemma scan_j_none : forall fuel pcs i j,
  scan_j pcs i j fuel = None ->
  forall j' a b,
    (j <= j')%nat ->
    (j' < j + fuel)%nat ->
    nth_error pcs i = Some a ->
    nth_error pcs j' = Some b ->
    pair_ok a b = true ->
    adm_list pcs a b = nil.
Proof.
  induction fuel as [|fuel IH]; intros pcs i j Hnone j' a b Hlo Hhi Hi Hj Hok.
  - lia.
  - cbn [scan_j] in Hnone.
    destruct (nth_error pcs i) as [a0|] eqn:Hi0.
    2: { discriminate Hi. }
    destruct (nth_error pcs j) as [b0|] eqn:Hj0.
    2: {
      apply nth_none_ge in Hj0. apply nth_length in Hj. lia. }
    apply some_inj in Hi. subst a0.
    destruct (pair_ok a b0) eqn:Eok.
    + destruct (least_ti (adm_list pcs a b0)) as [c|] eqn:El.
      * discriminate Hnone.
      * apply least_nil in El.
        destruct (Nat.eq_dec j' j) as [E|Hneq].
        -- subst j'. rewrite Hj in Hj0. apply some_inj in Hj0. subst b0. exact El.
        -- apply (IH pcs i (S j) Hnone j' a b); try assumption; try lia.
    + destruct (Nat.eq_dec j' j) as [E|Hneq].
      * subst j'. rewrite Hj in Hj0. apply some_inj in Hj0. subst b0.
        rewrite Hok in Eok. discriminate Eok.
      * apply (IH pcs i (S j) Hnone j' a b); try assumption; try lia.
Qed.

Lemma scan_i_none : forall fuel pcs i,
  scan_i pcs i fuel = None ->
  forall i' j a b,
    (i <= i')%nat ->
    (i' < i + fuel)%nat ->
    (i' < j)%nat ->
    nth_error pcs i' = Some a ->
    nth_error pcs j = Some b ->
    pair_ok a b = true ->
    adm_list pcs a b = nil.
Proof.
  induction fuel as [|fuel IH]; intros pcs i Hnone i' j a b Hlo Hhi Hij Hi Hj Hok.
  - lia.
  - cbn [scan_i] in Hnone.
    destruct (scan_j pcs i (S i) (S (length pcs))) as [ans|] eqn:Ej.
    + discriminate Hnone.
    + destruct (Nat.eq_dec i' i) as [E|Hneq].
      * subst i'.
        assert (Hle : (S i <= j)%nat) by (apply Nat.le_succ_l; exact Hij).
        assert (Hjb : (j < S i + S (length pcs))%nat).
        { apply nth_length in Hj. lia. }
        apply (scan_j_none (S (length pcs)) pcs i (S i) Ej j a b
                 Hle Hjb Hi Hj Hok).
      * apply (IH pcs (S i) Hnone i' j a b); try assumption; lia.
Qed.

Lemma pick_none_adm_nil : forall pcs i j a b,
  pick pcs = None ->
  (i < j)%nat ->
  nth_error pcs i = Some a ->
  nth_error pcs j = Some b ->
  pair_ok a b = true ->
  adm_list pcs a b = nil.
Proof.
  intros pcs i j a b H Hij Hi Hj Hok.
  unfold pick in H.
  apply (scan_i_none (S (length pcs)) pcs 0%nat H i j a b).
  - apply Nat.le_0_l.
  - apply nth_length in Hi. lia.
  - exact Hij.
  - exact Hi.
  - exact Hj.
  - exact Hok.
Qed.

Lemma counted_images : forall pcs s1 s2 p,
  In p (counted pcs s1 s2) ->
  support_image pcs s1 p /\ support_image pcs s2 p.
Proof.
  intros pcs s1 s2 p Hin.
  unfold counted in Hin.
  destruct (canon2 s1 s2) as [u v] eqn:Ec.
  rewrite dedup_In in Hin. apply filter_In in Hin. destruct Hin as [_ Hk].
  unfold keep_b in Hk. apply andb_prop in Hk. destruct Hk as [Hi _].
  apply andb_prop in Hi. destruct Hi as [Hu Hv].
  apply in_image_spec in Hu. apply in_image_spec in Hv.
  destruct (canon_orient s1 s2 u v Ec) as [[-> ->]|[-> ->]]; split; assumption.
Qed.

Lemma counted_is_overlap_end : forall pcs s1 s2 p,
  In p (counted pcs s1 s2) ->
  overlap_b s1 s2 = true ->
  In p (overlap_endpoints pcs s1 s2).
Proof.
  intros pcs s1 s2 p Hin Ho.
  unfold counted in Hin. unfold overlap_endpoints.
  destruct (canon2 s1 s2) as [u v] eqn:Ec.
  rewrite dedup_In in Hin. apply filter_In in Hin. destruct Hin as [Hraw _].
  unfold overlap_b in Ho. rewrite Ec in Ho.
  destruct u as [cu|cu]; destruct v as [cv|cv]; simpl in Ho; try discriminate.
  - unfold raw_pts in Hraw. rewrite Ho in Hraw. exact Hraw.
  - unfold raw_pts in Hraw. rewrite Ho in Hraw. exact Hraw.
Qed.

Definition pair_declines_b (a c : BagPiece) : bool :=
  match ck_egg (bp_ck a), ck_egg (bp_ck c) with
  | MkCirc cu, MkChord s => negb (circ_open_span_b cu && chord_nondeg_b s)
  | MkChord s, MkCirc cu => negb (circ_open_span_b cu && chord_nondeg_b s)
  | _, _ => false
  end.

Lemma pair_declines_irrefl : forall a, pair_declines_b a a = false.
Proof.
  intros [[src dst egg] sup w prov]. simpl.
  destruct egg as [e|e|e|e|e]; reflexivity.
Qed.

Lemma pair_declines_spec : forall a c,
  piece_wf a -> piece_wf c ->
  pair_declines_b a c = true <->
  I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck c)) IDecline.
Proof.
  intros a c Ha Hc.
  destruct a as [[sa da ea] supa wa pa].
  destruct c as [[sc dc ec] supc wc pc0].
  destruct Ha as [Hra _]. destruct Hc as [Hrc _]. simpl in *.
  destruct supa as [ua|ua].
  - destruct ea as [ea|ea|ea|ea|ea];
      try (solve [simpl in Hra; exfalso; exact Hra]).
    destruct supc as [uc|uc].
    + destruct ec as [ec|ec|ec|ec|ec];
        try (solve [simpl in Hrc; exfalso; exact Hrc]).
      simpl. split; intro H; [discriminate| contradiction].
    + destruct ec as [ec|ec|ec|ec|ec];
        try (solve [simpl in Hrc; exfalso; exact Hrc]).
      simpl. split; intro H.
      * apply negb_true_iff in H. intro Hs. apply scope_spec in Hs. congruence.
      * apply negb_true_iff.
        destruct (circ_open_span_b ec && chord_nondeg_b ea) eqn:Eb;
          [| reflexivity].
        exfalso. apply H. apply scope_spec. exact Eb.
  - destruct ea as [ea|ea|ea|ea|ea];
      try (solve [simpl in Hra; exfalso; exact Hra]).
    destruct supc as [uc|uc].
    + destruct ec as [ec|ec|ec|ec|ec];
        try (solve [simpl in Hrc; exfalso; exact Hrc]).
      simpl. split; intro H.
      * apply negb_true_iff in H. intro Hs. apply scope_spec in Hs. congruence.
      * apply negb_true_iff.
        destruct (circ_open_span_b ea && chord_nondeg_b ec) eqn:Eb;
          [| reflexivity].
        exfalso. apply H. apply scope_spec. exact Eb.
    + destruct ec as [ec|ec|ec|ec|ec];
        try (solve [simpl in Hrc; exfalso; exact Hrc]).
      simpl. split; intro H; [discriminate| contradiction].
Qed.

Lemma nodecline_class : forall a b,
  piece_wf a -> piece_wf b ->
  ~ I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck b)) IDecline ->
  match ck_egg (bp_ck a), ck_egg (bp_ck b) with
  | MkChord _, MkChord _ => True
  | MkCirc _, MkCirc _ => True
  | MkCirc c, MkChord s => circ_chord_host_scope c s
  | MkChord s, MkCirc c => circ_chord_host_scope c s
  | _, _ => False
  end.
Proof.
  intros a b Ha Hb Hnd.
  destruct a as [[sa da ea] supa wa pa].
  destruct b as [[sb db eb] supb wb pb].
  destruct Ha as [Hra _]. destruct Hb as [Hrb _]. simpl in *.
  destruct supa as [ua|ua].
  - destruct ea as [ea|ea|ea|ea|ea];
      try (solve [simpl in Hra; exfalso; exact Hra]).
    destruct supb as [ub|ub].
    + destruct eb as [eb|eb|eb|eb|eb];
        try (solve [simpl in Hrb; exfalso; exact Hrb]).
      exact I.
    + destruct eb as [eb|eb|eb|eb|eb];
        try (solve [simpl in Hrb; exfalso; exact Hrb]).
      destruct (circ_open_span_b eb && chord_nondeg_b ea) eqn:Es.
      * apply scope_spec. exact Es.
      * exfalso. apply Hnd. simpl. intro Hs.
        apply scope_spec in Hs. congruence.
  - destruct ea as [ea|ea|ea|ea|ea];
      try (solve [simpl in Hra; exfalso; exact Hra]).
    destruct supb as [ub|ub].
    + destruct eb as [eb|eb|eb|eb|eb];
        try (solve [simpl in Hrb; exfalso; exact Hrb]).
      destruct (circ_open_span_b ea && chord_nondeg_b eb) eqn:Es.
      * apply scope_spec. exact Es.
      * exfalso. apply Hnd. simpl. intro Hs.
        apply scope_spec in Hs. congruence.
    + destruct eb as [eb|eb|eb|eb|eb];
        try (solve [simpl in Hrb; exfalso; exact Hrb]).
      exact I.
Qed.

Lemma counted_adm_in : forall pcs a b p,
  piece_wf a -> piece_wf b ->
  window_pts (bp_support a) (bp_window a) p ->
  window_pts (bp_support b) (bp_window b) p ->
  In p (counted pcs (bp_support a) (bp_support b)) ->
  ~ I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck b)) IDecline ->
  exists ti tj, In (mkHitCand p ti tj) (adm_list pcs a b).
Proof.
  intros pcs a b p Ha Hb Hwa Hwb Hin Hnd.
  edestruct (adm_list_covers pcs a b p Ha Hb Hwa Hwb Hin
              (counted_not_vertex pcs (bp_support a) (bp_support b) p Hin))
    as [ti [tj [Hinc _]]].
  - intro Ho. apply (counted_is_overlap_end pcs (bp_support a) (bp_support b) p Hin Ho).
  - apply nodecline_class; assumption.
  - exists ti, tj. exact Hinc.
Qed.

Definition live_decline (pcs : list BagPiece) : Prop :=
  exists a c, In a pcs /\ In c pcs /\ a <> c /\
    I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck c)) IDecline.

Lemma live_decline_forall : forall pcs,
  ~ live_decline pcs <->
  (forall a c, In a pcs -> In c pcs -> a <> c ->
     ~ I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck c)) IDecline).
Proof.
  intros pcs. split.
  - intros H a c Ha Hc Hneq Hd. apply H. exists a, c. repeat split; assumption.
  - intros H [a [c [Ha [Hc [Hneq Hd]]]]]. exact (H a c Ha Hc Hneq Hd).
Qed.

Definition index_declines (pcs : list BagPiece) (i j : nat) : bool :=
  match nth_error pcs i, nth_error pcs j with
  | Some a, Some c => if Nat.eqb i j then false else pair_declines_b a c
  | _, _ => false
  end.

Definition declines_at (pcs : list BagPiece) : bool :=
  let n := length pcs in
  existsb (fun i => existsb (index_declines pcs i) (seq 0 n)) (seq 0 n).

Lemma declines_at_spec : forall pcs,
  (forall pc, In pc pcs -> piece_wf pc) ->
  declines_at pcs = true <-> live_decline pcs.
Proof.
  intros pcs Hwf. split.
  - intro H. unfold declines_at in H.
    apply existsb_exists in H. destruct H as [i [Hi Hb]].
    apply existsb_exists in Hb. destruct Hb as [j [Hj Hidx]].
    unfold index_declines in Hidx.
    destruct (nth_error pcs i) as [a|] eqn:Ha; [| discriminate].
    destruct (nth_error pcs j) as [c|] eqn:Hc; [| discriminate].
    destruct (Nat.eqb i j) eqn:Eij; [discriminate|].
    exists a, c.
    split; [eapply nth_error_In; exact Ha|].
    split; [eapply nth_error_In; exact Hc|].
    split.
    + intro E. subst c. rewrite pair_declines_irrefl in Hidx. discriminate.
    + apply (proj1 (pair_declines_spec a c
             (Hwf a (nth_error_In _ _ Ha)) (Hwf c (nth_error_In _ _ Hc)))).
      exact Hidx.
  - intros [a [c [Ha [Hc [Hneq Hd]]]]].
    destruct (In_nth_error _ _ Ha) as [i Hi].
    destruct (In_nth_error _ _ Hc) as [j Hj].
    assert (Hbw : pair_declines_b a c = true).
    { apply (proj2 (pair_declines_spec a c (Hwf a Ha) (Hwf c Hc))). exact Hd. }
    unfold declines_at. apply existsb_exists. exists i. split.
    + apply in_seq. split; [apply Nat.le_0_l|].
      apply nth_length in Hi. exact Hi.
    + apply existsb_exists. exists j. split.
      * apply in_seq. split; [apply Nat.le_0_l|].
        apply nth_length in Hj. exact Hj.
      * unfold index_declines. rewrite Hi, Hj.
        destruct (Nat.eqb i j) eqn:Eij.
        -- apply Nat.eqb_eq in Eij. subst j.
           rewrite Hi in Hj. inversion Hj. subst c. contradiction.
        -- exact Hbw.
Qed.

Lemma pair_ok_wf : forall a b,
  piece_wf a -> piece_wf b -> bp_support a <> bp_support b ->
  pair_ok a b = true.
Proof.
  intros a b Ha Hb Hneq. unfold pair_ok. apply andb_true_intro. split.
  - apply andb_true_intro. split; apply piece_wf_b_spec; assumption.
  - apply negb_true_iff.
    destruct (support_eqb (bp_support a) (bp_support b)) eqn:Es; [| reflexivity].
    apply support_eqb_true in Es. contradiction.
Qed.

Lemma no_hit_pair : forall pcs i j a b p,
  (forall pc, In pc pcs -> piece_wf pc) ->
  pick pcs = None ->
  ~ live_decline pcs ->
  (i < j)%nat ->
  nth_error pcs i = Some a ->
  nth_error pcs j = Some b ->
  window_pts (bp_support a) (bp_window a) p ->
  window_pts (bp_support b) (bp_window b) p ->
  In p (counted pcs (bp_support a) (bp_support b)) ->
  bp_support a <> bp_support b ->
  False.
Proof.
  intros pcs i j a b p Hwf Hpick Hdec Hij Hi Hj Hwa Hwb Hin Hneq.
  assert (Hnil : adm_list pcs a b = nil).
  { apply (pick_none_adm_nil pcs i j a b Hpick Hij Hi Hj).
    apply pair_ok_wf; [apply Hwf; eapply nth_error_In; exact Hi|
                        apply Hwf; eapply nth_error_In; exact Hj| exact Hneq]. }
  assert (Hnd : ~ I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck b)) IDecline).
  { intro Hd. apply Hdec. exists a, b.
    split; [eapply nth_error_In; exact Hi|].
    split; [eapply nth_error_In; exact Hj|].
    split; [| exact Hd].
    intro E. subst b. apply Hneq. reflexivity. }
  destruct (counted_adm_in pcs a b p
             (Hwf a (nth_error_In _ _ Hi)) (Hwf b (nth_error_In _ _ Hj))
             Hwa Hwb Hin Hnd) as [ti [tj HinA]].
  rewrite Hnil in HinA. destruct HinA.
Qed.

Lemma pick_none_rho0 : forall pcs,
  (forall pc, In pc pcs -> piece_wf pc) ->
  pick pcs = None ->
  ~ live_decline pcs ->
  rho_pcs pcs = 0%nat.
Proof.
  intros pcs Hwf Hpick Hdec.
  unfold rho_pcs. apply pair_sum_offdiag_zero; [apply supports_NoDup|].
  intros s1 s2 Hs1 Hs2 Hneq.
  destruct (counted pcs s1 s2) as [|p rest] eqn:Ec; [reflexivity|].
  exfalso.
  assert (Hp : In p (counted pcs s1 s2)).
  { rewrite Ec. left. reflexivity. }
  destruct (counted_images pcs s1 s2 p Hp) as [Ia Ib].
  destruct Ia as [a [Ha [Hsa Hwa]]].
  destruct Ib as [b [Hb [Hsb Hwb]]].
  destruct (In_nth_error _ _ Ha) as [i Hi].
  destruct (In_nth_error _ _ Hb) as [j Hj].
  assert (Hwa' : window_pts (bp_support a) (bp_window a) p).
  { rewrite Hsa. exact Hwa. }
  assert (Hwb' : window_pts (bp_support b) (bp_window b) p).
  { rewrite Hsb. exact Hwb. }
  assert (Hsab : bp_support a <> bp_support b).
  { rewrite Hsa, Hsb. exact Hneq. }
  destruct (Nat.lt_trichotomy i j) as [Hij|[Eij|Hji]].
  - apply (no_hit_pair pcs i j a b p Hwf Hpick Hdec Hij Hi Hj Hwa' Hwb').
    + rewrite Hsa, Hsb. exact Hp.
    + exact Hsab.
  - subst j. rewrite Hi in Hj. inversion Hj. subst b.
    apply Hsab. reflexivity.
  - apply (no_hit_pair pcs j i b a p Hwf Hpick Hdec Hji Hj Hi Hwb' Hwa').
    + rewrite Hsb, Hsa. rewrite counted_sym. exact Hp.
    + intro E. apply Hsab. symmetry. exact E.
Qed.

Inductive PickArm : Type := ArmHit | ArmDecline | ArmStop.

Definition pick_arm (b : SheetBag) : PickArm :=
  match b with
  | BagDeclined _ => ArmStop
  | BagLive _ pcs =>
      match pick pcs with
      | Some _ => ArmHit
      | None => if declines_at pcs then ArmDecline else ArmStop
      end
  end.

Definition hit_ok (b : SheetBag) (w : HitPick) : Prop :=
  match b with
  | BagDeclined _ => False
  | BagLive _ pcs =>
      exists e1 e2,
        nth_error pcs (hp_i w) = Some e1 /\
        nth_error pcs (hp_j w) = Some e2 /\
        hp_i w <> hp_j w /\
        piece_wf e1 /\ piece_wf e2 /\
        bp_support e1 <> bp_support e2 /\
        admissible_hit pcs e1 e2 (hp_P w) (hp_ti w) (hp_tj w)
  end.

Definition no_live_decline (b : SheetBag) : Prop :=
  match b with
  | BagDeclined _ => True
  | BagLive _ pcs => ~ live_decline pcs
  end.

(* WITNESS {"claimId":"0007-loop-letter5-pick","topic":"overlay","lemma":"pick_bag_spec","title":"concrete pick_bag has hit, decline, and stop arms","file":"theories/SheetHenPickSpec.v","witness":"pick_bag_spec","board":"ADR-0007"} *)
Theorem pick_bag_spec : forall b, bag_inv b ->
  match pick_arm b with
  | ArmHit => exists w, pick_bag b = Some w /\ hit_ok b w
  | ArmDecline =>
      pick_bag b = None /\
      match b with
      | BagDeclined _ => False
      | BagLive _ pcs => live_decline pcs
      end
  | ArmStop =>
      pick_bag b = None /\ rho b = 0%nat /\ no_live_decline b
  end.
Proof.
  intros [sh pcs|sh] Hinv.
  - unfold pick_arm.
    destruct (pick pcs) as [[[i j] [[p ti] tj]]|] eqn:Ep.
    + eexists. split.
      * unfold pick_bag. rewrite Ep. reflexivity.
      * apply (pick_bag_progress sh pcs). unfold pick_bag. rewrite Ep. reflexivity.
    + destruct (declines_at pcs) eqn:Ed.
      * split; [unfold pick_bag; rewrite Ep; reflexivity|].
        apply (proj1 (declines_at_spec pcs Hinv)). exact Ed.
      * split; [unfold pick_bag; rewrite Ep; reflexivity|]. split.
        -- apply pick_none_rho0; [exact Hinv| exact Ep|].
           intro Hd. apply (proj2 (declines_at_spec pcs Hinv)) in Hd.
           rewrite Ed in Hd. discriminate Hd.
        -- intro Hd. apply (proj2 (declines_at_spec pcs Hinv)) in Hd.
           rewrite Ed in Hd. discriminate Hd.
  - unfold pick_arm, pick_bag, rho, no_live_decline. simpl.
    repeat split; exact I.
Qed.

Theorem letter5_obligation : forall b,
  bag_inv b ->
  pick_arm b = ArmStop ->
  pick_bag b = None /\ rho b = 0%nat /\ no_live_decline b.
Proof.
  intros b Hinv Harm.
  pose proof (pick_bag_spec b Hinv) as Hs.
  rewrite Harm in Hs. exact Hs.
Qed.

Print Assumptions some_inj.
Print Assumptions nth_length.
Print Assumptions nth_none_ge.
Print Assumptions fold_nat_zero.
Print Assumptions pair_sum_offdiag_zero.
Print Assumptions least_nil.
Print Assumptions scan_j_none.
Print Assumptions scan_i_none.
Print Assumptions pick_none_adm_nil.
Print Assumptions counted_images.
Print Assumptions counted_is_overlap_end.
Print Assumptions pair_declines_irrefl.
Print Assumptions pair_declines_spec.
Print Assumptions nodecline_class.
Print Assumptions counted_adm_in.
Print Assumptions live_decline_forall.
Print Assumptions declines_at_spec.
Print Assumptions pair_ok_wf.
Print Assumptions no_hit_pair.
Print Assumptions pick_none_rho0.
Print Assumptions pick_bag_spec.
Print Assumptions letter5_obligation.
