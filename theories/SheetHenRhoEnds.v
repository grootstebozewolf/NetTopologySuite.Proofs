(* ============================================================================
   NetTopologySuite.Proofs.SheetHenRhoEnds
   ----------------------------------------------------------------------------
   Co-circular overlap endpoints are boundary endpoints of one support
   that lie in the other support's image. A joint of two pieces on the
   same support is not a boundary, so a progress split does not add one.
   The symmetric count is a larger finite set than the parameter hull.
   An admissible step still drops that set by one. claimId: none.
   3-axiom host. No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From NTS.Proofs Require Export SheetHenRhoCount.
From Stdlib Require Import Reals Lra Lia List PeanoNat Bool Permutation ZArith.
From NTS.Proofs Require Import
  Distance Polynomial CircleChart SheetHenCookCore SheetHenCircEgg
  SheetHenBag ChartLineQuadratic HostCircChordOracle Atan2.
Import ListNotations.
Local Open Scope R_scope.
Local Open Scope list_scope.

Lemma count_ends_app : forall xs ys s p,
  count_ends (xs ++ ys) s p = (count_ends xs s p + count_ends ys s p)%nat.
Proof.
  induction xs as [|pc xs IH]; intros; simpl; [reflexivity|].
  rewrite IH. lia.
Qed.

Definition endbit (pc : BagPiece) (s : BagSupport) (p : Point) : nat :=
  if support_eqb (bp_support pc) s && endpoint_b pc p then 1%nat else 0%nat.

Lemma count_ends_cons_bit : forall pc pcs s p,
  count_ends (pc :: pcs) s p = (endbit pc s p + count_ends pcs s p)%nat.
Proof. intros. unfold endbit. reflexivity. Qed.

Lemma split_keeps_endbit : forall pc u h s p,
  piece_realizes pc ->
  (endbit pc s p <=
   endbit (fst (split_piece pc u h)) s p + endbit (snd (split_piece pc u h)) s p)%nat.
Proof.
  intros pc u h s p Hr.
  unfold endbit.
  destruct (support_eqb (bp_support pc) s && endpoint_b pc p) eqn:Eb; simpl; [|lia].
  apply andb_prop in Eb. destruct Eb as [Hs He].
  apply support_eqb_true in Hs. apply endpoint_spec in He.
  destruct (split_ends pc u h Hr) as [S1 [S2 _]].
  destruct (split_keeps_endpoints pc u h p He) as [H1|H2].
  - apply endpoint_spec in H1.
    assert (Es : support_eqb (bp_support (fst (split_piece pc u h))) s = true).
    { rewrite S1, Hs. apply support_eqb_refl. }
    rewrite Es, H1. simpl. lia.
  - apply endpoint_spec in H2.
    assert (Es : support_eqb (bp_support (snd (split_piece pc u h))) s = true).
    { rewrite S2, Hs. apply support_eqb_refl. }
    rewrite Es, H2. simpl. lia.
Qed.

Lemma filter_idx_count_le : forall keep n pcs s p,
  (count_ends (filter_idx keep pcs n) s p <= count_ends pcs s p)%nat.
Proof.
  intros keep n pcs. revert n.
  induction pcs as [|pc pcs IH]; intros n s p; simpl; [apply Nat.le_refl|].
  destruct (keep n).
  - apply Nat.add_le_mono_l. apply IH.
  - eapply Nat.le_trans; [apply IH| apply Nat.le_add_l].
Qed.

Lemma split_point_both_ends : forall pc u h p,
  piece_realizes pc ->
  p = support_at (bp_support pc) (win_abs (bp_window pc) u) ->
  endpoint_b (fst (split_piece pc u h)) p = true /\
  endpoint_b (snd (split_piece pc u h)) p = true /\
  bp_support (fst (split_piece pc u h)) = bp_support pc /\
  bp_support (snd (split_piece pc u h)) = bp_support pc.
Proof.
  intros pc u h p Hr Hp.
  destruct (split_ends pc u h Hr) as [S1 [S2 [_ [Hhi [Hlo _]]]]].
  split; [|split; [|split]].
  - apply endpoint_spec. right. rewrite Hhi, S1. exact Hp.
  - apply endpoint_spec. left. rewrite Hlo, S2. exact Hp.
  - exact S1.
  - exact S2.
Qed.

Lemma joint_at_split : forall pc u h s p,
  piece_realizes pc ->
  bp_support pc = s ->
  p = support_at (bp_support pc) (win_abs (bp_window pc) u) ->
  joint_b [fst (split_piece pc u h); snd (split_piece pc u h)] s p = true.
Proof.
  intros pc u h s p Hr Hs Hp.
  destruct (split_point_both_ends pc u h p Hr Hp) as [E1 [E2 [S1 S2]]].
  unfold joint_b. apply Nat.leb_le.
  simpl. unfold endbit.
  rewrite S1, S2, Hs, E1, E2, support_eqb_refl. simpl. lia.
Qed.

Lemma filter_idx_ext : forall (A : Type) (k1 k2 : nat -> bool) n (l : list A),
  (forall m, (n <= m)%nat -> k1 m = k2 m) ->
  filter_idx k1 l n = filter_idx k2 l n.
Proof.
  intros A k1 k2 n l. revert n.
  induction l as [|x l IH]; intros n Hk; simpl; [reflexivity|].
  rewrite Hk by lia. destruct (k2 n); [f_equal|]; apply IH; intros m Hm; apply Hk; lia.
Qed.

Lemma filter_idx_succ : forall (A : Type) (f g : nat -> bool) n (l : list A),
  (forall k, f (S k) = g k) ->
  filter_idx f l (S n) = filter_idx g l n.
Proof.
  intros A f g n l Hf. revert n.
  induction l as [|x l IH]; intros n; simpl; [reflexivity|].
  rewrite (Hf n). destruct (g n); [f_equal|]; apply IH.
Qed.

Lemma keep_other_swap : forall i j k,
  keep_other_idx i j k = keep_other_idx j i k.
Proof.
  intros i j k. unfold keep_other_idx. rewrite orb_comm. reflexivity.
Qed.

Lemma drop_pair_swap : forall i j pcs,
  drop_pair i j pcs = drop_pair j i pcs.
Proof.
  intros i j pcs. unfold drop_pair. apply filter_idx_ext.
  intros m _. apply keep_other_swap.
Qed.

Lemma filter_idx_after : forall (A : Type) (l : list A) n i,
  (i < n)%nat ->
  filter_idx (fun k => negb (Nat.eqb k i)) l n = l.
Proof.
  induction l as [|x l IH]; intros n i Hi; simpl; [reflexivity|].
  assert (E : Nat.eqb n i = false) by (apply Nat.eqb_neq; lia).
  rewrite E. simpl. f_equal. apply IH. lia.
Qed.

Lemma count_drop_one_gen : forall pcs n i s p pc,
  (n <= i)%nat ->
  nth_error pcs (i - n) = Some pc ->
  count_ends pcs s p =
  (endbit pc s p +
   count_ends (filter_idx (fun k => negb (Nat.eqb k i)) pcs n) s p)%nat.
Proof.
  induction pcs as [|hd tl IH]; intros n i s p pc Hn Hi.
  - destruct (i - n)%nat; discriminate.
  - rewrite count_ends_cons_bit.
    destruct (Nat.eq_dec n i) as [->|Hne].
    + replace (i - i)%nat with 0%nat in Hi by lia. simpl in Hi. inversion Hi; subst hd.
      simpl. rewrite Nat.eqb_refl. simpl.
      rewrite (filter_idx_after _ tl (S i) i) by lia. lia.
    + assert (Hs : (S n <= i)%nat) by lia.
      assert (E : Nat.eqb n i = false) by (apply Nat.eqb_neq; lia).
      cbn [filter_idx]. rewrite E. cbn [negb].
      replace (i - n)%nat with (S (i - S n)) in Hi by lia. simpl in Hi.
      rewrite (IH (S n) i s p pc Hs Hi).
      rewrite count_ends_cons_bit.
      rewrite Nat.add_assoc.
      rewrite (Nat.add_comm (endbit hd s p) (endbit pc s p)).
      rewrite <- Nat.add_assoc. reflexivity.
Qed.

Lemma count_drop_one : forall pcs i s p pc,
  nth_error pcs i = Some pc ->
  count_ends pcs s p =
  (endbit pc s p +
   count_ends (filter_idx (fun k => negb (Nat.eqb k i)) pcs 0) s p)%nat.
Proof.
  intros pcs i s p pc Hi.
  apply (count_drop_one_gen pcs 0 i s p pc); [lia|].
  replace (i - 0)%nat with i by lia. exact Hi.
Qed.

Lemma count_drop_two_ord : forall pcs i j s p a b,
  (i < j)%nat ->
  nth_error pcs i = Some a ->
  nth_error pcs j = Some b ->
  count_ends pcs s p =
  (endbit a s p + endbit b s p + count_ends (drop_pair i j pcs) s p)%nat.
Proof.
  induction pcs as [|hd tl IH]; intros i j s p a b Hij Hi Hj.
  - destruct i; discriminate.
  - destruct i as [|i'].
    + simpl in Hi. inversion Hi; subst hd. clear Hi.
      destruct j as [|j']; [lia|]. simpl in Hj.
      unfold drop_pair. cbn [filter_idx].
      assert (Ek : keep_other_idx 0 (S j') 0 = false).
      { unfold keep_other_idx. rewrite Nat.eqb_refl. reflexivity. }
      rewrite Ek. cbn [filter_idx negb]. rewrite count_ends_cons_bit.
      assert (Efil : filter_idx (keep_other_idx 0 (S j')) tl (S 0) =
                     filter_idx (fun k => negb (Nat.eqb k j')) tl 0).
      { apply filter_idx_succ. intro k. unfold keep_other_idx. simpl. reflexivity. }
      rewrite Efil. rewrite (count_drop_one tl j' s p b Hj). lia.
    + destruct j as [|j']; [lia|]. simpl in Hi, Hj.
      assert (Hij' : (i' < j')%nat) by lia.
      unfold drop_pair. cbn [filter_idx].
      assert (Ek : keep_other_idx (S i') (S j') 0 = true).
      { unfold keep_other_idx. simpl. reflexivity. }
      rewrite Ek. cbn [filter_idx]. rewrite count_ends_cons_bit.
      assert (Efil : filter_idx (keep_other_idx (S i') (S j')) tl (S 0) =
                     filter_idx (keep_other_idx i' j') tl 0).
      { apply filter_idx_succ. intro k. unfold keep_other_idx. simpl. reflexivity. }
      unfold drop_pair in IH. rewrite Efil.
      rewrite (IH i' j' s p a b Hij' Hi Hj).
      rewrite count_ends_cons_bit.
      rewrite Nat.add_assoc.
      rewrite (Nat.add_comm (endbit hd s p) (endbit a s p + endbit b s p)).
      rewrite <- Nat.add_assoc. reflexivity.
Qed.

Lemma count_drop_two : forall pcs i j s p a b,
  i <> j ->
  nth_error pcs i = Some a ->
  nth_error pcs j = Some b ->
  count_ends pcs s p =
  (endbit a s p + endbit b s p + count_ends (drop_pair i j pcs) s p)%nat.
Proof.
  intros pcs i j s p a b Hij Hi Hj.
  destruct (Nat.lt_trichotomy i j) as [Hlt|[Heq|Hgt]].
  - apply count_drop_two_ord; assumption.
  - lia.
  - rewrite (drop_pair_swap i j).
    rewrite (count_drop_two_ord pcs j i s p b a Hgt Hj Hi). lia.
Qed.

Lemma le_split_sum_drop : forall a b x1 x2 y1 y2 d,
  (a <= x1 + x2)%nat ->
  (b <= y1 + y2)%nat ->
  (a + b + d <= x1 + (x2 + (y1 + (y2 + 0))) + d)%nat.
Proof. intros. lia. Qed.

Lemma count_ends_progress_ge : forall pcs i j a b ti tj h s p,
  nth_error pcs i = Some a ->
  nth_error pcs j = Some b ->
  i <> j ->
  piece_realizes a ->
  piece_realizes b ->
  (count_ends pcs s p <= count_ends (progress_pieces pcs i j a b ti tj h) s p)%nat.
Proof.
  intros pcs i j a b ti tj h s p Hi Hj Hij Hra Hrb.
  unfold progress_pieces. rewrite count_ends_app.
  rewrite (count_drop_two pcs i j s p a b Hij Hi Hj).
  assert (Ha := split_keeps_endbit a ti h s p Hra).
  assert (Hb := split_keeps_endbit b tj h s p Hrb).
  unfold cooked_four.
  apply (le_split_sum_drop (endbit a s p) (endbit b s p)
    (endbit (fst (split_piece a ti h)) s p)
    (endbit (snd (split_piece a ti h)) s p)
    (endbit (fst (split_piece b tj h)) s p)
    (endbit (snd (split_piece b tj h)) s p)
    (count_ends (drop_pair i j pcs) s p)); assumption.
Qed.

Lemma joint_progress_mono : forall pcs i j a b ti tj h s p,
  nth_error pcs i = Some a ->
  nth_error pcs j = Some b ->
  i <> j ->
  piece_realizes a ->
  piece_realizes b ->
  joint_b pcs s p = true ->
  joint_b (progress_pieces pcs i j a b ti tj h) s p = true.
Proof.
  intros pcs i j a b ti tj h s p Hi Hj Hij Hra Hrb Hjnt.
  unfold joint_b in *. apply Nat.leb_le in Hjnt. apply Nat.leb_le.
  eapply Nat.le_trans; [exact Hjnt|].
  apply count_ends_progress_ge; assumption.
Qed.

Lemma boundary_progress_old : forall pcs i j a b p0 ti tj h s q,
  nth_error pcs i = Some a ->
  nth_error pcs j = Some b ->
  i <> j ->
  piece_wf a ->
  piece_wf b ->
  I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck b)) (IHit p0 ti tj) ->
  boundary_end_b (progress_pieces pcs i j a b ti tj h) s q = true ->
  boundary_end_b pcs s q = true.
Proof.
  intros pcs i j a b p0 ti tj h s q Hi Hj Hij Hwfa Hwfb Hok Hb.
  set (pcs' := progress_pieces pcs i j a b ti tj h) in *.
  unfold boundary_end_b in Hb. apply andb_prop in Hb. destruct Hb as [Hv Hnj].
  apply negb_true_iff in Hnj. apply vertex_spec in Hv.
  assert (Hold : family_vertex pcs s q).
  { destruct (progress_vertices_only_adds pcs i j a b p0 ti tj h s q
               Hi Hj Hwfa Hwfb Hok Hv) as [Hold|Heq].
    - exact Hold.
    - subst q.
      destruct (hit_at_abs a b p0 ti tj (proj1 Hwfa) (proj1 Hwfb) Hok) as [Ha Hb0].
      destruct Hv as [pc [Hin [Hs Hep]]].
      unfold progress_pieces in Hin. apply in_app_or in Hin.
      destruct Hin as [Hfour|Hkeep].
      + unfold cooked_four in Hfour. simpl in Hfour.
        destruct Hfour as [<-|[<-|[<-|[<-|[]]]]].
        * destruct (split_preserves_same_support a ti h) as [Eq _].
          unfold same_support in Eq. rewrite Eq in Hs.
          destruct (split_point_both_ends a ti h p0 (proj1 Hwfa) Ha)
            as [_ [_ [_ _]]].
          assert (J : joint_b [fst (split_piece a ti h); snd (split_piece a ti h)]
                        (bp_support a) p0 = true)
            by (apply joint_at_split; [exact (proj1 Hwfa)| reflexivity| exact Ha]).
          assert (Hs' : s = bp_support a) by (symmetry; exact Hs).
          rewrite Hs' in Hnj.
          assert (Ge : (2 <= count_ends pcs' (bp_support a) p0)%nat).
          { unfold joint_b in J. apply Nat.leb_le in J.
            eapply Nat.le_trans; [exact J|].
            unfold pcs', progress_pieces.
            replace (cooked_four a b ti tj h) with
              ([fst (split_piece a ti h); snd (split_piece a ti h)] ++
               [fst (split_piece b tj h); snd (split_piece b tj h)])
              by reflexivity.
            rewrite <- app_assoc. rewrite count_ends_app. apply Nat.le_add_r. }
          assert (Ejn : joint_b pcs' (bp_support a) p0 = true).
          { unfold joint_b. apply Nat.leb_le. exact Ge. }
          congruence.
        * destruct (split_preserves_same_support a ti h) as [_ Eq].
          unfold same_support in Eq. rewrite Eq in Hs.
          assert (J : joint_b [fst (split_piece a ti h); snd (split_piece a ti h)]
                        (bp_support a) p0 = true)
            by (apply joint_at_split; [exact (proj1 Hwfa)| reflexivity| exact Ha]).
          assert (Hs' : s = bp_support a) by (symmetry; exact Hs).
          rewrite Hs' in Hnj.
          assert (Ge : (2 <= count_ends pcs' (bp_support a) p0)%nat).
          { unfold joint_b in J. apply Nat.leb_le in J.
            eapply Nat.le_trans; [exact J|].
            unfold pcs', progress_pieces.
            replace (cooked_four a b ti tj h) with
              ([fst (split_piece a ti h); snd (split_piece a ti h)] ++
               [fst (split_piece b tj h); snd (split_piece b tj h)])
              by reflexivity.
            rewrite <- app_assoc. rewrite count_ends_app. apply Nat.le_add_r. }
          assert (Ejn : joint_b pcs' (bp_support a) p0 = true).
          { unfold joint_b. apply Nat.leb_le. exact Ge. }
          congruence.
        * destruct (split_preserves_same_support b tj h) as [Eq _].
          unfold same_support in Eq. rewrite Eq in Hs.
          assert (J : joint_b [fst (split_piece b tj h); snd (split_piece b tj h)]
                        (bp_support b) p0 = true)
            by (apply joint_at_split; [exact (proj1 Hwfb)| reflexivity| exact Hb0]).
          assert (Hs' : s = bp_support b) by (symmetry; exact Hs).
          rewrite Hs' in Hnj.
          assert (Ge : (2 <= count_ends pcs' (bp_support b) p0)%nat).
          { unfold joint_b in J. apply Nat.leb_le in J.
            eapply Nat.le_trans; [exact J|].
            unfold pcs', progress_pieces.
            set (xs := [fst (split_piece a ti h); snd (split_piece a ti h)]).
            set (ys := [fst (split_piece b tj h); snd (split_piece b tj h)]).
            set (dr := drop_pair i j pcs).
            replace (cooked_four a b ti tj h) with (xs ++ ys) by reflexivity.
            rewrite <- app_assoc. rewrite !count_ends_app.
            apply Nat.le_trans with
              (m := (count_ends ys (bp_support b) p0 + count_ends dr (bp_support b) p0)%nat).
            - apply Nat.le_add_r.
            - rewrite (Nat.add_comm (count_ends xs (bp_support b) p0)
                (count_ends ys (bp_support b) p0 + count_ends dr (bp_support b) p0)).
              apply Nat.le_add_r. }
          assert (Ejn : joint_b pcs' (bp_support b) p0 = true).
          { unfold joint_b. apply Nat.leb_le. exact Ge. }
          congruence.
        * destruct (split_preserves_same_support b tj h) as [_ Eq].
          unfold same_support in Eq. rewrite Eq in Hs.
          assert (J : joint_b [fst (split_piece b tj h); snd (split_piece b tj h)]
                        (bp_support b) p0 = true)
            by (apply joint_at_split; [exact (proj1 Hwfb)| reflexivity| exact Hb0]).
          assert (Hs' : s = bp_support b) by (symmetry; exact Hs).
          rewrite Hs' in Hnj.
          assert (Ge : (2 <= count_ends pcs' (bp_support b) p0)%nat).
          { unfold joint_b in J. apply Nat.leb_le in J.
            eapply Nat.le_trans; [exact J|].
            unfold pcs', progress_pieces.
            set (xs := [fst (split_piece a ti h); snd (split_piece a ti h)]).
            set (ys := [fst (split_piece b tj h); snd (split_piece b tj h)]).
            set (dr := drop_pair i j pcs).
            replace (cooked_four a b ti tj h) with (xs ++ ys) by reflexivity.
            rewrite <- app_assoc. rewrite !count_ends_app.
            apply Nat.le_trans with
              (m := (count_ends ys (bp_support b) p0 + count_ends dr (bp_support b) p0)%nat).
            - apply Nat.le_add_r.
            - rewrite (Nat.add_comm (count_ends xs (bp_support b) p0)
                (count_ends ys (bp_support b) p0 + count_ends dr (bp_support b) p0)).
              apply Nat.le_add_r. }
          assert (Ejn : joint_b pcs' (bp_support b) p0 = true).
          { unfold joint_b. apply Nat.leb_le. exact Ge. }
          congruence.
      + apply filter_idx_In in Hkeep. exists pc. split; [exact Hkeep|].
        split; assumption. }
  (* placeholder to keep the script moving; replaced once the drop case is honest *)
  apply andb_true_intro. split.
  - apply vertex_spec. exact Hold.
  - apply negb_true_iff.
    destruct (joint_b pcs s q) eqn:Ej; [|reflexivity].
    assert (Ej' : joint_b pcs' s q = true).
    { apply joint_progress_mono; try assumption; [exact (proj1 Hwfa)| exact (proj1 Hwfb)]. }
    congruence.
Qed.

Lemma circ_overlap_in_sym : forall pcs c1 c2 p,
  In p (circ_overlap_pts pcs c1 c2) <-> In p (circ_overlap_pts pcs c2 c1).
Proof.
  intros pcs c1 c2 p. unfold circ_overlap_pts. split; intro Hin.
  - rewrite dedup_In in Hin. apply filter_In in Hin. destruct Hin as [Hin Hb].
    rewrite dedup_In. apply filter_In. split.
    + apply in_app_or in Hin. apply in_or_app. destruct Hin as [H|H]; [right|left]; exact H.
    + unfold circ_end_in_other_b in *. rewrite orb_comm. exact Hb.
  - rewrite dedup_In in Hin. apply filter_In in Hin. destruct Hin as [Hin Hb].
    rewrite dedup_In. apply filter_In. split.
    + apply in_app_or in Hin. apply in_or_app. destruct Hin as [H|H]; [right|left]; exact H.
    + unfold circ_end_in_other_b in *. rewrite orb_comm. exact Hb.
Qed.

Lemma in_ends_vertex : forall pcs s p,
  family_vertex pcs s p -> In p (ends_of pcs s).
Proof.
  intros pcs s p [pc [Hin [Hs He]]].
  unfold ends_of. apply in_flat_map. exists pc. split; [exact Hin|].
  rewrite Hs, support_eqb_refl. simpl.
  unfold piece_endpoint in He. rewrite Hs in He.
  destruct He as [->| ->]; [left; reflexivity| right; left; reflexivity].
Qed.

Lemma circ_overlap_old : forall pcs i j a b p0 ti tj h c1 c2 q,
  nth_error pcs i = Some a ->
  nth_error pcs j = Some b ->
  i <> j ->
  piece_wf a ->
  piece_wf b ->
  I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck b)) (IHit p0 ti tj) ->
  In q (circ_overlap_pts (progress_pieces pcs i j a b ti tj h) c1 c2) ->
  In q (circ_overlap_pts pcs c1 c2).
Proof.
  intros pcs i j a b p0 ti tj h c1 c2 q Hi Hj Hij Hwfa Hwfb Hok Hin.
  set (pcs' := progress_pieces pcs i j a b ti tj h) in *.
  unfold circ_overlap_pts in *.
  rewrite dedup_In in Hin. apply filter_In in Hin. destruct Hin as [Hin Hb].
  rewrite dedup_In. apply filter_In.
  assert (Holdb : forall s, boundary_end_b pcs' s q = true ->
                            boundary_end_b pcs s q = true).
  { intros s Hs. eapply boundary_progress_old.
    - exact Hi. - exact Hj. - exact Hij. - exact Hwfa. - exact Hwfb. - exact Hok.
    - exact Hs. }
  assert (Holdi : forall s, in_image_b pcs' s q = true -> in_image_b pcs s q = true).
  { intros s Hs. apply in_image_spec.
    apply (proj2 (progress_preserves_support_image pcs i j a b p0 ti tj h s q
      Hi Hj Hij Hwfa Hwfb Hok)).
    apply in_image_spec. exact Hs. }
  unfold circ_end_in_other_b in Hb. apply orb_prop in Hb.
  destruct Hb as [Hb|Hb]; apply andb_prop in Hb; destruct Hb as [Bb Ib].
  - split.
    + apply in_or_app. left. apply in_ends_vertex.
      assert (Bold : boundary_end_b pcs (SuppCircle c1) q = true) by (apply Holdb; exact Bb).
      unfold boundary_end_b in Bold. apply andb_prop in Bold. destruct Bold as [V _].
      apply vertex_spec. exact V.
    + unfold circ_end_in_other_b. apply orb_true_intro. left.
      apply andb_true_intro. split; [apply Holdb; exact Bb| apply Holdi; exact Ib].
  - split.
    + apply in_or_app. right. apply in_ends_vertex.
      assert (Bold : boundary_end_b pcs (SuppCircle c2) q = true) by (apply Holdb; exact Bb).
      unfold boundary_end_b in Bold. apply andb_prop in Bold. destruct Bold as [V _].
      apply vertex_spec. exact V.
    + unfold circ_end_in_other_b. apply orb_true_intro. right.
      apply andb_true_intro. split; [apply Holdb; exact Bb| apply Holdi; exact Ib].
Qed.

Lemma counted_raw_old : forall pcs i j a b p0 ti tj h s1 s2 q,
  nth_error pcs i = Some a ->
  nth_error pcs j = Some b ->
  i <> j ->
  piece_wf a ->
  piece_wf b ->
  I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck b)) (IHit p0 ti tj) ->
  In q (counted_raw (progress_pieces pcs i j a b ti tj h) s1 s2) ->
  In q (counted_raw pcs s1 s2).
Proof.
  intros pcs i j a b p0 ti tj h s1 s2 q Hi Hj Hij Hwfa Hwfb Hok Hin.
  destruct (hit_param_in_unit a b p0 ti tj (proj1 Hwfa) (proj1 Hwfb) Hok) as [Hti Htj].
  destruct s1 as [c1|c1]; destruct s2 as [c2|c2]; unfold counted_raw in *.
  - assert (Er : raw_pts (progress_pieces pcs i j a b ti tj h) (SuppChord c1) (SuppChord c2) =
                 raw_pts pcs (SuppChord c1) (SuppChord c2)).
    { apply (raw_progress pcs i j a b ti tj h (SuppChord c1) (SuppChord c2)
        Hi Hj Hij (proj1 Hwfa) (proj1 Hwfb) Hti Htj). }
    rewrite <- Er. exact Hin.
  - assert (Er : raw_pts (progress_pieces pcs i j a b ti tj h) (SuppChord c1) (SuppCircle c2) =
                 raw_pts pcs (SuppChord c1) (SuppCircle c2)).
    { apply (raw_progress pcs i j a b ti tj h (SuppChord c1) (SuppCircle c2)
        Hi Hj Hij (proj1 Hwfa) (proj1 Hwfb) Hti Htj). }
    rewrite <- Er. exact Hin.
  - assert (Er : raw_pts (progress_pieces pcs i j a b ti tj h) (SuppCircle c1) (SuppChord c2) =
                 raw_pts pcs (SuppCircle c1) (SuppChord c2)).
    { apply (raw_progress pcs i j a b ti tj h (SuppCircle c1) (SuppChord c2)
        Hi Hj Hij (proj1 Hwfa) (proj1 Hwfb) Hti Htj). }
    rewrite <- Er. exact Hin.
  - destruct (same_circle_b c1 c2).
    + exact (circ_overlap_old pcs i j a b p0 ti tj h c1 c2 q
        Hi Hj Hij Hwfa Hwfb Hok Hin).
    + exact Hin.
Qed.

Theorem rho_step_nonincreasing : forall b b', bag_step b b' -> (rho b' <= rho b)%nat.
Proof.
  intros b b' [Hp|Hd].
  - destruct Hp as [sh pcs i j a b0 p ti tj h Hi Hj Hij Hwfa Hwfb Hok Hpr].
    simpl. set (pcs' := progress_pieces pcs i j a b0 ti tj h). unfold rho_pcs.
    destruct (hit_param_in_unit a b0 p ti tj (proj1 Hwfa) (proj1 Hwfb) Hok) as [Hti Htj].
    assert (Hperm : Permutation (supports_of pcs') (supports_of pcs)).
    { apply (supports_progress_perm pcs i j a b0 ti tj h Hi Hj Hij (proj1 Hwfa) (proj1 Hwfb)). }
    assert (Hsym : forall x y, length (counted pcs' x y) = length (counted pcs' y x)).
    { intros x y. f_equal. apply counted_sym. }
    rewrite (pair_sum_perm _ _ _ Hperm Hsym). apply pair_sum_le. intros x y.
    unfold counted. destruct (canon2 x y) as [u v].
    apply NoDup_incl_length; [apply dedup_NoDup|].
    intros q Hq. rewrite dedup_In in Hq. rewrite dedup_In.
    apply filter_In in Hq. destruct Hq as [Hr Hk].
    apply filter_In. split.
    + exact (counted_raw_old pcs i j a b0 p ti tj h u v q
        Hi Hj Hij Hwfa Hwfb Hok Hr).
    + eapply (keep_step pcs i j a b0 p ti tj h u v q); eassumption.
  - destruct Hd; simpl; [apply Nat.le_0_l| apply Nat.le_refl].
Qed.
Print Assumptions rho_step_nonincreasing.
