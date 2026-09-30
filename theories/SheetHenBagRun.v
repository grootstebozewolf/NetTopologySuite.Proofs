(* ============================================================================
   NetTopologySuite.Proofs.SheetHenBagRun
   ----------------------------------------------------------------------------
   ∀-bag letter 3 of 6. Admissible step, strict ρ decrease, structural
   bag_run. claimId: 0007-loop-letter3-strict
   witness: rho_step_strict (bag_run_fixpoint secondary).
   Does not remint 0007-forall-bag and does not steal its witness.
   Does not name the loop discharge. Selector existence is letter 5.
   Merge stays off this letter: ρ is the only measure.

   Letter 1's StepProgress takes h : Hen as a parameter. It does not
   consult pt_eqb, so a third support that already has a hen at P can
   be given a second identifier. mint_or_share is the lookup. piece_wf
   does not mention the hen, so reuse preserves it (split_piece_wf).

   3-axiom host. No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List PeanoNat Bool Permutation.
From NTS.Proofs Require Import Distance SheetHenCook SheetHenBag SheetHenRho.
Import ListNotations.
Local Open Scope R_scope.
Local Open Scope list_scope.

(* -------------------------------------------------------------------------- *)
(* Decisions for the Hit arm of I_ok, vertices, and overlap endpoints.        *)
(* -------------------------------------------------------------------------- *)

Lemma req_b_false : forall x y, req_b x y = false <-> x <> y.
Proof.
  intros x y. unfold req_b. destruct (Req_EM_T x y) as [E|N]; simpl; split; intro H.
  - discriminate.
  - congruence.
  - exact N.
  - reflexivity.
Qed.

Definition on_chord_b (c : ChordEgg) (t : R) (p : Point) : bool :=
  rle_b 0 t && rle_b t 1 && pt_eqb p (chord_eval c t).

Lemma on_chord_spec : forall c t p, on_chord_b c t p = true <-> on_chord c t p.
Proof.
  intros c t p. unfold on_chord_b, on_chord. split; intro H.
  - apply andb_prop in H. destruct H as [Hb Hp].
    apply andb_prop in Hb. destruct Hb as [H0 H1].
    split; [split; apply rle_b_true; assumption|].
    apply pt_eqb_true. exact Hp.
  - destruct H as [[H0 H1] Hp].
    apply andb_true_intro. split.
    + apply andb_true_intro. split; apply rle_b_true; assumption.
    + apply pt_eqb_true. exact Hp.
Qed.

Definition on_circ_b (c : CircularEgg) (t : R) (p : Point) : bool :=
  rle_b 0 t && rle_b t 1 && pt_eqb p (circ_eval c t).

Lemma on_circ_spec : forall c t p, on_circ_b c t p = true <-> on_circ c t p.
Proof.
  intros c t p. unfold on_circ_b, on_circ. split; intro H.
  - apply andb_prop in H. destruct H as [Hb Hp].
    apply andb_prop in Hb. destruct Hb as [H0 H1].
    split; [split; apply rle_b_true; assumption|].
    apply pt_eqb_true. exact Hp.
  - destruct H as [[H0 H1] Hp].
    apply andb_true_intro. split.
    + apply andb_true_intro. split; apply rle_b_true; assumption.
    + apply pt_eqb_true. exact Hp.
Qed.

Definition on_cloth_b (c : ClothoidEgg) (t : R) (p : Point) : bool :=
  rle_b 0 t && rle_b t 1 && pt_eqb p (cloth_eval c t).

Lemma on_cloth_spec : forall c t p, on_cloth_b c t p = true <-> on_cloth c t p.
Proof.
  intros c t p. unfold on_cloth_b, on_cloth. split; intro H.
  - apply andb_prop in H. destruct H as [Hb Hp].
    apply andb_prop in Hb. destruct Hb as [H0 H1].
    split; [split; apply rle_b_true; assumption|].
    apply pt_eqb_true. exact Hp.
  - destruct H as [[H0 H1] Hp].
    apply andb_true_intro. split.
    + apply andb_true_intro. split; apply rle_b_true; assumption.
    + apply pt_eqb_true. exact Hp.
Qed.

Definition chord_nondeg_b (s : ChordEgg) : bool :=
  negb (req_b (chord_dx s) 0 && req_b (chord_dy s) 0).

Lemma chord_nondeg_spec : forall s, chord_nondeg_b s = true <-> chord_nondeg s.
Proof.
  intros s. unfold chord_nondeg_b, chord_nondeg. split; intro H.
  - intro Heq. apply pair_equal_spec in Heq. destruct Heq as [Hx Hy].
    apply negb_true_iff in H. apply andb_false_iff in H.
    destruct H as [H|H]; apply req_b_false in H; contradiction.
  - apply negb_true_iff. apply andb_false_iff.
    destruct (req_b (chord_dx s) 0) eqn:Ex;
      destruct (req_b (chord_dy s) 0) eqn:Ey.
    + apply req_b_true in Ex. apply req_b_true in Ey.
      exfalso. apply H. apply pair_equal_spec. split; assumption.
    + right. reflexivity.
    + left. reflexivity.
    + left. reflexivity.
Qed.

Definition circ_open_span_b (c : CircularEgg) : bool :=
  if Rlt_dec (- (2 * PI)) (circ_sweep c) then
    if Rlt_dec (circ_sweep c) (2 * PI) then true else false
  else false.

Lemma circ_open_span_spec :
  forall c, circ_open_span_b c = true <-> circ_open_span c.
Proof.
  intros c. unfold circ_open_span_b, circ_open_span.
  destruct (Rlt_dec (- (2 * PI)) (circ_sweep c)) as [H1|H1];
    destruct (Rlt_dec (circ_sweep c) (2 * PI)) as [H2|H2]; simpl; split; intro H.
  - split; assumption.
  - reflexivity.
  - discriminate.
  - destruct H as [_ Hb]. contradiction.
  - discriminate.
  - destruct H as [Ha _]. contradiction.
  - discriminate.
  - destruct H as [Ha _]. contradiction.
Qed.

Lemma scope_spec : forall c s,
  circ_open_span_b c && chord_nondeg_b s = true <-> circ_chord_host_scope c s.
Proof.
  intros c s. unfold circ_chord_host_scope.
  rewrite andb_true_iff, circ_open_span_spec, chord_nondeg_spec.
  reflexivity.
Qed.

Definition I_ok_hit_b (e1 e2 : Egg) (p : Point) (ti tj : R) : bool :=
  match e1, e2 with
  | MkChord c1, MkChord c2 => on_chord_b c1 ti p && on_chord_b c2 tj p
  | MkCirc c1, MkCirc c2 => on_circ_b c1 ti p && on_circ_b c2 tj p
  | MkCirc c, MkChord s =>
      circ_open_span_b c && chord_nondeg_b s &&
      on_circ_b c ti p && on_chord_b s tj p
  | MkChord s, MkCirc c =>
      circ_open_span_b c && chord_nondeg_b s &&
      on_chord_b s ti p && on_circ_b c tj p
  | MkClothoid c1, MkClothoid c2 => on_cloth_b c1 ti p && on_cloth_b c2 tj p
  | _, _ => false
  end.

Lemma I_ok_hit_spec : forall e1 e2 p ti tj,
  I_ok_hit_b e1 e2 p ti tj = true <-> I_ok e1 e2 (IHit p ti tj).
Proof.
  intros e1 e2 p ti tj.
  destruct e1; destruct e2; simpl;
    try (split; intro H; try discriminate; contradiction).
  - rewrite andb_true_iff, on_chord_spec, on_chord_spec. reflexivity.
  - rewrite !andb_true_iff. rewrite <- andb_true_iff.
    rewrite scope_spec, on_chord_spec, on_circ_spec. tauto.
  - rewrite !andb_true_iff. rewrite <- andb_true_iff.
    rewrite scope_spec, on_circ_spec, on_chord_spec. tauto.
  - rewrite andb_true_iff, on_circ_spec, on_circ_spec. reflexivity.
  - rewrite andb_true_iff, on_cloth_spec, on_cloth_spec. reflexivity.
Qed.

(* vertex_of_both is letter 1's family_vertex on both supports. *)
Definition vertex_of_both (pcs : list BagPiece) (s1 s2 : BagSupport) (p : Point)
  : Prop :=
  family_vertex pcs s1 p /\ family_vertex pcs s2 p.

Lemma canon_orient : forall s1 s2 u v,
  canon2 s1 s2 = (u, v) ->
  (u = s1 /\ v = s2) \/ (u = s2 /\ v = s1).
Proof.
  intros s1 s2 u v H. unfold canon2 in H.
  destruct (rlex_le (support_reals s1) (support_reals s2)); inversion H; auto.
Qed.

Lemma vertex_of_both_spec : forall pcs s1 s2 p,
  vertex_b pcs s1 p && vertex_b pcs s2 p = true <-> vertex_of_both pcs s1 s2 p.
Proof.
  intros pcs s1 s2 p. unfold vertex_of_both. split; intro H.
  - apply andb_prop in H. destruct H as [Ha Hb].
    split; apply vertex_spec; assumption.
  - destruct H as [Ha Hb]. apply andb_true_intro.
    split; apply vertex_spec; assumption.
Qed.

Definition in_pts_b (p : Point) (ps : list Point) : bool :=
  existsb (pt_eqb p) ps.

Lemma in_pts_spec : forall p ps, in_pts_b p ps = true <-> In p ps.
Proof.
  intros p ps. unfold in_pts_b. rewrite existsb_exists. split.
  - intros [q [Hin Hb]]. apply pt_eqb_true in Hb. subst q. exact Hin.
  - intro Hin. exists p. split; [exact Hin|]. apply pt_eqb_true. reflexivity.
Qed.

(* Overlap of carriers, in the canon order letter 2 counts. Mixed pairs
   are not overlap: their candidates are the transverse root list. *)
Definition overlap_b (s1 s2 : BagSupport) : bool :=
  match canon2 s1 s2 with
  | (SuppChord a, SuppChord b) => same_line_b a b
  | (SuppCircle a, SuppCircle b) => same_circle_b a b
  | _ => false
  end.

Definition overlap (s1 s2 : BagSupport) : Prop := overlap_b s1 s2 = true.

Definition overlap_endpoints (pcs : list BagPiece) (s1 s2 : BagSupport)
  : list Point :=
  let '(u, v) := canon2 s1 s2 in overlap_pts pcs u v.

Lemma overlap_b_circ_chord : forall c s,
  overlap_b (SuppCircle c) (SuppChord s) = false.
Proof.
  intros c s. unfold overlap_b.
  destruct (canon2 (SuppCircle c) (SuppChord s)) as [u v] eqn:Ec.
  destruct (canon_orient _ _ _ _ Ec) as [[-> ->]|[-> ->]]; reflexivity.
Qed.

Lemma overlap_b_chord_circ : forall s c,
  overlap_b (SuppChord s) (SuppCircle c) = false.
Proof.
  intros s c. unfold overlap_b.
  destruct (canon2 (SuppChord s) (SuppCircle c)) as [u v] eqn:Ec.
  destruct (canon_orient _ _ _ _ Ec) as [[-> ->]|[-> ->]]; reflexivity.
Qed.

Lemma overlap_impl_spec : forall pcs s1 s2 p,
  negb (overlap_b s1 s2) || in_pts_b p (overlap_endpoints pcs s1 s2) = true
  <-> (overlap s1 s2 -> In p (overlap_endpoints pcs s1 s2)).
Proof.
  intros pcs s1 s2 p. unfold overlap. split; intro H.
  - intro Ho. rewrite Ho in H. simpl in H. apply in_pts_spec. exact H.
  - destruct (overlap_b s1 s2) eqn:Eo; simpl.
    + apply in_pts_spec. apply H. reflexivity.
    + reflexivity.
Qed.

(* Frame: I_ok on the piece eggs, not a vertex of both supports, and an
   overlap hit is an overlap endpoint. Distinct supports are required
   by rho_candidates_complete and are a hypothesis of the strict step. *)
Definition admissible_hit (pcs : list BagPiece) (e1 e2 : BagPiece)
    (P : Point) (ti tj : R) : Prop :=
  I_ok (ck_egg (bp_ck e1)) (ck_egg (bp_ck e2)) (IHit P ti tj) /\
  ~ vertex_of_both pcs (bp_support e1) (bp_support e2) P /\
  (overlap (bp_support e1) (bp_support e2) ->
     In P (overlap_endpoints pcs (bp_support e1) (bp_support e2))).

Definition admissible_hit_b (pcs : list BagPiece) (e1 e2 : BagPiece)
    (P : Point) (ti tj : R) : bool :=
  I_ok_hit_b (ck_egg (bp_ck e1)) (ck_egg (bp_ck e2)) P ti tj &&
  negb (vertex_b pcs (bp_support e1) P && vertex_b pcs (bp_support e2) P) &&
  (negb (overlap_b (bp_support e1) (bp_support e2)) ||
   in_pts_b P (overlap_endpoints pcs (bp_support e1) (bp_support e2))).

Lemma admissible_hit_spec : forall pcs e1 e2 P ti tj,
  admissible_hit_b pcs e1 e2 P ti tj = true <->
  admissible_hit pcs e1 e2 P ti tj.
Proof.
  intros pcs e1 e2 P ti tj. unfold admissible_hit_b, admissible_hit. split; intro H.
  - apply andb_prop in H. destruct H as [H Hb].
    apply andb_prop in H. destruct H as [Hi Hn].
    split; [apply I_ok_hit_spec; exact Hi|].
    split.
    + intro Hv. apply negb_true_iff in Hn.
      apply vertex_of_both_spec in Hv. congruence.
    + apply overlap_impl_spec. exact Hb.
  - destruct H as [Hi [Hn Hb]].
    apply andb_true_intro. split.
    + apply andb_true_intro. split.
      * apply I_ok_hit_spec. exact Hi.
      * apply negb_true_iff.
        destruct (vertex_b pcs (bp_support e1) P &&
                  vertex_b pcs (bp_support e2) P) eqn:Ev; [|reflexivity].
        exfalso. apply Hn. apply vertex_of_both_spec. exact Ev.
    + apply overlap_impl_spec. exact Hb.
Qed.

Lemma admissible_hit_dec : forall pcs e1 e2 P ti tj,
  {admissible_hit pcs e1 e2 P ti tj} + {~ admissible_hit pcs e1 e2 P ti tj}.
Proof.
  intros pcs e1 e2 P ti tj.
  destruct (admissible_hit_b pcs e1 e2 P ti tj) eqn:E.
  - left. apply admissible_hit_spec. exact E.
  - right. intro H. apply admissible_hit_spec in H. congruence.
Qed.

(* -------------------------------------------------------------------------- *)
(* Letter 1 does not dedup hens by point. mint_or_share does.                 *)
(* -------------------------------------------------------------------------- *)

Lemma letter1_step_accepts_any_hen :
  forall sh pcs i j a b p ti tj h1 h2,
    nth_error pcs i = Some a ->
    nth_error pcs j = Some b ->
    i <> j ->
    piece_wf a ->
    piece_wf b ->
    I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck b)) (IHit p ti tj) ->
    progress_hit pcs a b (IHit p ti tj) ->
    bag_progress_step (BagLive sh pcs)
      (BagLive sh (progress_pieces pcs i j a b ti tj h1)) /\
    bag_progress_step (BagLive sh pcs)
      (BagLive sh (progress_pieces pcs i j a b ti tj h2)).
Proof.
  intros sh pcs i j a b p ti tj h1 h2 Hi Hj Hij Hw1 Hw2 Hok Hpr.
  split; apply StepProgress with (p := p); assumption.
Qed.

Definition hen_sits (pc : BagPiece) (h : Hen) (p : Point) : Prop :=
  (ck_src (bp_ck pc) = h /\
   p = support_at (bp_support pc) (win_lo (bp_window pc))) \/
  (ck_dst (bp_ck pc) = h /\
   p = support_at (bp_support pc) (win_hi (bp_window pc))).

Definition hens_unique_by_point (pcs : list BagPiece) : Prop :=
  forall pc1 pc2 h1 h2 p,
    In pc1 pcs -> In pc2 pcs ->
    hen_sits pc1 h1 p -> hen_sits pc2 h2 p ->
    h1 = h2.

Fixpoint hen_list (pcs : list BagPiece) : list Hen :=
  match pcs with
  | nil => nil
  | pc :: tl => ck_src (bp_ck pc) :: ck_dst (bp_ck pc) :: hen_list tl
  end.

Fixpoint list_max_nat (l : list nat) : nat :=
  match l with
  | nil => O
  | n :: tl => Nat.max n (list_max_nat tl)
  end.

Definition fresh_hen (pcs : list BagPiece) : Hen :=
  S (list_max_nat (hen_list pcs)).

Lemma list_max_ge : forall l n, In n l -> (n <= list_max_nat l)%nat.
Proof.
  induction l as [|m tl IH]; intros n Hin; simpl in Hin; [contradiction|].
  simpl. destruct Hin as [->|Hin].
  - apply Nat.le_max_l.
  - apply Nat.le_trans with (list_max_nat tl); [apply IH; exact Hin|].
    apply Nat.le_max_r.
Qed.

Lemma fresh_not_member : forall pcs h, In h (hen_list pcs) -> fresh_hen pcs <> h.
Proof.
  intros pcs h Hin Heq.
  assert (Hle : (h <= list_max_nat (hen_list pcs))%nat).
  { apply list_max_ge. exact Hin. }
  unfold fresh_hen in Heq. lia.
Qed.

Lemma hen_sits_in_list : forall pcs pc h p,
  In pc pcs -> hen_sits pc h p -> In h (hen_list pcs).
Proof.
  induction pcs as [|hd tl IH]; intros pc h p Hin Hs; simpl in Hin; [contradiction|].
  simpl. destruct Hin as [->|Hin].
  - destruct Hs as [[<- _]|[<- _]]; [left|right; left]; reflexivity.
  - right. right. eapply IH; eassumption.
Qed.

Fixpoint lookup_hen_at (pcs : list BagPiece) (p : Point) : option Hen :=
  match pcs with
  | nil => None
  | pc :: tl =>
      if pt_eqb p (support_at (bp_support pc) (win_lo (bp_window pc)))
      then Some (ck_src (bp_ck pc))
      else if pt_eqb p (support_at (bp_support pc) (win_hi (bp_window pc)))
      then Some (ck_dst (bp_ck pc))
      else lookup_hen_at tl p
  end.

Definition mint_or_share (pcs : list BagPiece) (p : Point) : Hen :=
  match lookup_hen_at pcs p with
  | Some h => h
  | None => fresh_hen pcs
  end.

Lemma lookup_hen_at_sits : forall pcs p h,
  lookup_hen_at pcs p = Some h ->
  exists pc, In pc pcs /\ hen_sits pc h p.
Proof.
  induction pcs as [|pc tl IH]; intros p h H; simpl in H; [discriminate|].
  destruct (pt_eqb p (support_at (bp_support pc) (win_lo (bp_window pc)))) eqn:Elo.
  - inversion H. subst h. exists pc. split; [left; reflexivity|].
    left. split; [reflexivity|]. apply pt_eqb_true. exact Elo.
  - destruct (pt_eqb p (support_at (bp_support pc) (win_hi (bp_window pc)))) eqn:Ehi.
    + inversion H. subst h. exists pc. split; [left; reflexivity|].
      right. split; [reflexivity|]. apply pt_eqb_true. exact Ehi.
    + destruct (IH p h H) as [pc0 [Hin Hs]].
      exists pc0. split; [right; exact Hin| exact Hs].
Qed.

Lemma sits_lookup_some : forall pcs pc h p,
  In pc pcs -> hen_sits pc h p ->
  exists h', lookup_hen_at pcs p = Some h'.
Proof.
  induction pcs as [|hd tl IH]; intros pc h p Hin Hs; simpl in Hin; [contradiction|].
  simpl.
  destruct (pt_eqb p (support_at (bp_support hd) (win_lo (bp_window hd)))) eqn:Elo.
  - exists (ck_src (bp_ck hd)). reflexivity.
  - destruct (pt_eqb p (support_at (bp_support hd) (win_hi (bp_window hd)))) eqn:Ehi.
    + exists (ck_dst (bp_ck hd)). reflexivity.
    + destruct Hin as [<-|Hin].
      * destruct Hs as [[_ Hp]|[_ Hp]].
        -- assert (Et : pt_eqb p (support_at (bp_support hd) (win_lo (bp_window hd))) = true)
             by (apply pt_eqb_true; exact Hp).
           congruence.
        -- assert (Et : pt_eqb p (support_at (bp_support hd) (win_hi (bp_window hd))) = true)
             by (apply pt_eqb_true; exact Hp).
           congruence.
      * eapply IH; eassumption.
Qed.

Lemma mint_agrees : forall pcs pc h p,
  hens_unique_by_point pcs ->
  In pc pcs ->
  hen_sits pc h p ->
  mint_or_share pcs p = h.
Proof.
  intros pcs pc h p Hu Hin Hs.
  unfold mint_or_share.
  destruct (sits_lookup_some pcs pc h p Hin Hs) as [h' Hlk].
  rewrite Hlk.
  destruct (lookup_hen_at_sits pcs p h' Hlk) as [pc' [Hin' Hs']].
  apply (Hu pc' pc h' h p Hin' Hin Hs' Hs).
Qed.

Lemma mint_or_share_cases : forall pcs p,
  (exists pc, In pc pcs /\ hen_sits pc (mint_or_share pcs p) p) \/
  (lookup_hen_at pcs p = None /\
   mint_or_share pcs p = fresh_hen pcs /\
   (forall h, In h (hen_list pcs) -> fresh_hen pcs <> h)).
Proof.
  intros pcs p. unfold mint_or_share.
  destruct (lookup_hen_at pcs p) as [h|] eqn:El.
  - left. destruct (lookup_hen_at_sits pcs p h El) as [pc [Hin Hs]].
    exists pc. split; [exact Hin| exact Hs].
  - right. split; [reflexivity|]. split; [reflexivity|].
    intros h Hin. apply fresh_not_member. exact Hin.
Qed.

Lemma lo_child_sits : forall pc u h hq q,
  piece_realizes pc ->
  hen_sits (fst (split_piece pc u h)) hq q ->
  (hq = ck_src (bp_ck pc) /\
   q = support_at (bp_support pc) (win_lo (bp_window pc))) \/
  (hq = h /\
   q = support_at (bp_support pc) (win_abs (bp_window pc) u)).
Proof.
  intros [[src dst egg] sup w prov] u h hq q Hr Hsit.
  destruct sup as [c|c]; destruct egg as [e|e|e|e|e];
    simpl in Hr; try contradiction; simpl in Hsit;
    destruct Hsit as [[Hq Hp]|[Hq Hp]].
  - left. split; [symmetry; exact Hq| exact Hp].
  - right. split; [symmetry; exact Hq| exact Hp].
  - left. split; [symmetry; exact Hq| exact Hp].
  - right. split; [symmetry; exact Hq| exact Hp].
Qed.

Lemma hi_child_sits : forall pc u h hq q,
  piece_realizes pc ->
  hen_sits (snd (split_piece pc u h)) hq q ->
  (hq = h /\
   q = support_at (bp_support pc) (win_abs (bp_window pc) u)) \/
  (hq = ck_dst (bp_ck pc) /\
   q = support_at (bp_support pc) (win_hi (bp_window pc))).
Proof.
  intros [[src dst egg] sup w prov] u h hq q Hr Hsit.
  destruct sup as [c|c]; destruct egg as [e|e|e|e|e];
    simpl in Hr; try contradiction; simpl in Hsit;
    destruct Hsit as [[Hq Hp]|[Hq Hp]].
  - left. split; [symmetry; exact Hq| exact Hp].
  - right. split; [symmetry; exact Hq| exact Hp].
  - left. split; [symmetry; exact Hq| exact Hp].
  - right. split; [symmetry; exact Hq| exact Hp].
Qed.

Lemma child_sit_account : forall parent u h pc hq q,
  piece_realizes parent ->
  (pc = fst (split_piece parent u h) \/ pc = snd (split_piece parent u h)) ->
  hen_sits pc hq q ->
  hen_sits parent hq q \/
  (hq = h /\ q = support_at (bp_support parent) (win_abs (bp_window parent) u)).
Proof.
  intros parent u h pc hq q Hr [->| ->] Hs.
  - destruct (lo_child_sits parent u h hq q Hr Hs) as [[Hq Hp]|[Hq Hp]].
    + left. left. split; [symmetry; exact Hq| exact Hp].
    + right. split; [exact Hq| exact Hp].
  - destruct (hi_child_sits parent u h hq q Hr Hs) as [[Hq Hp]|[Hq Hp]].
    + right. split; [exact Hq| exact Hp].
    + left. right. split; [symmetry; exact Hq| exact Hp].
Qed.

Lemma progress_sit_account : forall pcs i j a b ti tj h pc hq q,
  nth_error pcs i = Some a ->
  nth_error pcs j = Some b ->
  piece_realizes a ->
  piece_realizes b ->
  In pc (progress_pieces pcs i j a b ti tj h) ->
  hen_sits pc hq q ->
  (exists parent, In parent pcs /\ hen_sits parent hq q) \/
  (hq = h /\
    (q = support_at (bp_support a) (win_abs (bp_window a) ti) \/
     q = support_at (bp_support b) (win_abs (bp_window b) tj))).
Proof.
  intros pcs i j a b ti tj h pc hq q Hi Hj Hra Hrb Hin Hs.
  unfold progress_pieces in Hin. apply in_app_or in Hin.
  destruct Hin as [Hc|Hk].
  - unfold cooked_four in Hc. simpl in Hc.
    destruct Hc as [<-|[<-|[<-|[<-|[]]]]].
    + destruct (child_sit_account a ti h (fst (split_piece a ti h)) hq q Hra
                 (or_introl eq_refl) Hs) as [Hold|[Hq Hp]].
      * left. exists a. split; [eapply nth_error_In; exact Hi| exact Hold].
      * right. split; [exact Hq| left; exact Hp].
    + destruct (child_sit_account a ti h (snd (split_piece a ti h)) hq q Hra
                 (or_intror eq_refl) Hs) as [Hold|[Hq Hp]].
      * left. exists a. split; [eapply nth_error_In; exact Hi| exact Hold].
      * right. split; [exact Hq| left; exact Hp].
    + destruct (child_sit_account b tj h (fst (split_piece b tj h)) hq q Hrb
                 (or_introl eq_refl) Hs) as [Hold|[Hq Hp]].
      * left. exists b. split; [eapply nth_error_In; exact Hj| exact Hold].
      * right. split; [exact Hq| right; exact Hp].
    + destruct (child_sit_account b tj h (snd (split_piece b tj h)) hq q Hrb
                 (or_intror eq_refl) Hs) as [Hold|[Hq Hp]].
      * left. exists b. split; [eapply nth_error_In; exact Hj| exact Hold].
      * right. split; [exact Hq| right; exact Hp].
  - left. exists pc. split; [eapply filter_idx_In; exact Hk| exact Hs].
Qed.

Theorem mint_or_share_preserves_unique : forall pcs i j e1 e2 P ti tj,
  hens_unique_by_point pcs ->
  nth_error pcs i = Some e1 ->
  nth_error pcs j = Some e2 ->
  piece_wf e1 ->
  piece_wf e2 ->
  I_ok (ck_egg (bp_ck e1)) (ck_egg (bp_ck e2)) (IHit P ti tj) ->
  hens_unique_by_point
    (progress_pieces pcs i j e1 e2 ti tj (mint_or_share pcs P)).
Proof.
  intros pcs i j e1 e2 P ti tj Hu Hi Hj Hw1 Hw2 Hok.
  set (h := mint_or_share pcs P).
  set (pcs' := progress_pieces pcs i j e1 e2 ti tj h).
  intros pc1 pc2 h1 h2 q Hin1 Hin2 Hs1 Hs2.
  destruct (hit_at_abs e1 e2 P ti tj (proj1 Hw1) (proj1 Hw2) Hok) as [Ha Hb].
  destruct (progress_sit_account pcs i j e1 e2 ti tj h pc1 h1 q
              Hi Hj (proj1 Hw1) (proj1 Hw2) Hin1 Hs1)
    as [[par1 [I1 S1]]|[Hq1 Hj1]].
  - destruct (progress_sit_account pcs i j e1 e2 ti tj h pc2 h2 q
               Hi Hj (proj1 Hw1) (proj1 Hw2) Hin2 Hs2)
      as [[par2 [I2 S2]]|[Hq2 Hj2]].
    + apply (Hu par1 par2 h1 h2 q I1 I2 S1 S2).
    + assert (Eq : q = P).
      { destruct Hj2 as [Hq|Hq]; rewrite Hq; symmetry; assumption. }
      subst q.
      assert (Eh : h = h1) by (apply (mint_agrees pcs par1 h1 P Hu I1 S1)).
      rewrite Hq2, <- Eh. reflexivity.
  - assert (Eq : q = P).
    { destruct Hj1 as [Hq|Hq]; rewrite Hq; symmetry; assumption. }
    subst q.
    destruct (progress_sit_account pcs i j e1 e2 ti tj h pc2 h2 P
               Hi Hj (proj1 Hw1) (proj1 Hw2) Hin2 Hs2)
      as [[par2 [I2 S2]]|[Hq2 _]].
    + assert (Eh : h = h2) by (apply (mint_agrees pcs par2 h2 P Hu I2 S2)).
      rewrite Hq1. exact Eh.
    + rewrite Hq1, Hq2. reflexivity.
Qed.

Lemma piece_wf_independent_of_hen : forall pc u h1 h2,
  piece_wf pc ->
  0 <= u <= 1 ->
  piece_wf (fst (split_piece pc u h1)) /\
  piece_wf (snd (split_piece pc u h1)) /\
  piece_wf (fst (split_piece pc u h2)) /\
  piece_wf (snd (split_piece pc u h2)).
Proof.
  intros pc u h1 h2 Hwf Hu.
  destruct (split_piece_wf pc u h1 Hwf Hu) as [A B].
  destruct (split_piece_wf pc u h2 Hwf Hu) as [C D].
  split; [exact A| split; [exact B| split; [exact C| exact D]]].
Qed.

(* -------------------------------------------------------------------------- *)
(* The step is letter 1's progress step at a supplied admissible hit, with    *)
(* the hen chosen by mint_or_share. pick plugs in later; it is not built.     *)
(* -------------------------------------------------------------------------- *)

Record HitPick : Type := mkHitPick {
  hp_i : nat;
  hp_j : nat;
  hp_P : Point;
  hp_ti : R;
  hp_tj : R
}.

Definition step_hit (b : SheetBag) (w : HitPick) : SheetBag :=
  match b with
  | BagDeclined sh => BagDeclined sh
  | BagLive sh pcs =>
      match nth_error pcs (hp_i w), nth_error pcs (hp_j w) with
      | Some e1, Some e2 =>
          BagLive sh (progress_pieces pcs (hp_i w) (hp_j w) e1 e2
                        (hp_ti w) (hp_tj w) (mint_or_share pcs (hp_P w)))
      | _, _ => BagDeclined sh
      end
  end.

Lemma step_hit_is_progress : forall sh pcs i j e1 e2 P ti tj,
  nth_error pcs i = Some e1 ->
  nth_error pcs j = Some e2 ->
  i <> j ->
  piece_wf e1 ->
  piece_wf e2 ->
  admissible_hit pcs e1 e2 P ti tj ->
  bag_progress_step (BagLive sh pcs)
    (step_hit (BagLive sh pcs) (mkHitPick i j P ti tj)).
Proof.
  intros sh pcs i j e1 e2 P ti tj Hi Hj Hij Hw1 Hw2 Hadm.
  destruct Hadm as [Hok [Hnv _]].
  unfold step_hit. simpl. rewrite Hi, Hj.
  apply StepProgress with (p := P); try assumption.
Qed.

Lemma admissible_step_preserves_inv : forall sh pcs i j e1 e2 P ti tj,
  bag_inv (BagLive sh pcs) ->
  nth_error pcs i = Some e1 ->
  nth_error pcs j = Some e2 ->
  i <> j ->
  piece_wf e1 ->
  piece_wf e2 ->
  admissible_hit pcs e1 e2 P ti tj ->
  bag_inv (step_hit (BagLive sh pcs) (mkHitPick i j P ti tj)).
Proof.
  intros sh pcs i j e1 e2 P ti tj Hinv Hi Hj Hij Hw1 Hw2 Hadm.
  eapply step_preserves_inv; [exact Hinv|].
  left. apply (step_hit_is_progress sh pcs i j e1 e2 P ti tj); assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* An admissible hit is a ρ candidate, and the step removes it.               *)
(* -------------------------------------------------------------------------- *)

Lemma win_abs_bounds : forall w u,
  window_ordered w ->
  0 <= u <= 1 ->
  win_lo w <= win_abs w u <= win_hi w.
Proof.
  intros w u Ho Hu.
  destruct (subwindow_ordered w u Ho Hu) as [Hlo Hhi].
  unfold window_ordered, sub_lo, sub_hi in Hlo, Hhi. simpl in Hlo, Hhi.
  split; assumption.
Qed.

Lemma both_in_image : forall pcs e1 e2 P ti tj,
  In e1 pcs ->
  In e2 pcs ->
  piece_wf e1 ->
  piece_wf e2 ->
  I_ok (ck_egg (bp_ck e1)) (ck_egg (bp_ck e2)) (IHit P ti tj) ->
  support_image pcs (bp_support e1) P /\
  support_image pcs (bp_support e2) P.
Proof.
  intros pcs e1 e2 P ti tj I1 I2 Hw1 Hw2 Hok.
  destruct (hit_param_in_unit e1 e2 P ti tj (proj1 Hw1) (proj1 Hw2) Hok) as [Hti Htj].
  destruct (hit_at_abs e1 e2 P ti tj (proj1 Hw1) (proj1 Hw2) Hok) as [Ha Hb].
  destruct (win_abs_bounds (bp_window e1) ti (proj2 Hw1) Hti) as [Alo Ahi].
  destruct (win_abs_bounds (bp_window e2) tj (proj2 Hw2) Htj) as [Blo Bhi].
  split.
  - exists e1. split; [exact I1|]. split; [reflexivity|].
    exists (win_abs (bp_window e1) ti). split; [split; assumption|]. exact Ha.
  - exists e2. split; [exact I2|]. split; [reflexivity|].
    exists (win_abs (bp_window e2) tj). split; [split; assumption|]. exact Hb.
Qed.

Lemma admissible_class : forall pcs e1 e2 P ti tj,
  admissible_hit pcs e1 e2 P ti tj ->
  (forall a b, canon2 (bp_support e1) (bp_support e2) = (SuppChord a, SuppChord b) ->
     same_line_b a b = false \/
     In P (overlap_pts pcs (SuppChord a) (SuppChord b))) /\
  (forall a b, canon2 (bp_support e1) (bp_support e2) = (SuppCircle a, SuppCircle b) ->
     same_circle_b a b = false \/
     In P (overlap_pts pcs (SuppCircle a) (SuppCircle b))).
Proof.
  intros pcs e1 e2 P ti tj [_ [_ Hov]].
  set (s1 := bp_support e1). set (s2 := bp_support e2). split.
  - intros a b Hc.
    destruct (same_line_b a b) eqn:Es; [|left; reflexivity].
    right.
    assert (Ho : overlap s1 s2).
    { unfold overlap, overlap_b. rewrite Hc. exact Es. }
    assert (He : overlap_endpoints pcs s1 s2 =
                 overlap_pts pcs (SuppChord a) (SuppChord b)).
    { unfold overlap_endpoints. rewrite Hc. reflexivity. }
    rewrite <- He. apply Hov. exact Ho.
  - intros a b Hc.
    destruct (same_circle_b a b) eqn:Es; [|left; reflexivity].
    right.
    assert (Ho : overlap s1 s2).
    { unfold overlap, overlap_b. rewrite Hc. exact Es. }
    assert (He : overlap_endpoints pcs s1 s2 =
                 overlap_pts pcs (SuppCircle a) (SuppCircle b)).
    { unfold overlap_endpoints. rewrite Hc. reflexivity. }
    rewrite <- He. apply Hov. exact Ho.
Qed.

Lemma admissible_in_counted : forall pcs e1 e2 P ti tj,
  In e1 pcs ->
  In e2 pcs ->
  piece_wf e1 ->
  piece_wf e2 ->
  bp_support e1 <> bp_support e2 ->
  admissible_hit pcs e1 e2 P ti tj ->
  In P (counted pcs (bp_support e1) (bp_support e2)).
Proof.
  intros pcs e1 e2 P ti tj I1 I2 Hw1 Hw2 Hdist Hadm.
  destruct Hadm as [Hok [Hnv Hov]].
  destruct (both_in_image pcs e1 e2 P ti tj I1 I2 Hw1 Hw2 Hok) as [Ia Ib].
  destruct (admissible_class pcs e1 e2 P ti tj (conj Hok (conj Hnv Hov))) as [Hl Hc].
  apply rho_candidates_complete; assumption.
Qed.

Lemma split_joint_endpoint : forall pc u h,
  piece_realizes pc ->
  piece_endpoint (fst (split_piece pc u h))
    (support_at (bp_support pc) (win_abs (bp_window pc) u)) /\
  piece_endpoint (snd (split_piece pc u h))
    (support_at (bp_support pc) (win_abs (bp_window pc) u)).
Proof.
  intros pc u h Hr.
  destruct (split_windows_sub pc u h Hr) as [Hs1 [Hs2 [Hw1 Hw2]]].
  split.
  - right. rewrite Hs1, Hw1. unfold sub_lo. simpl. reflexivity.
  - left. rewrite Hs2, Hw2. unfold sub_hi. simpl. reflexivity.
Qed.

Lemma hit_becomes_vertex : forall pcs i j e1 e2 P ti tj h,
  nth_error pcs i = Some e1 ->
  nth_error pcs j = Some e2 ->
  piece_wf e1 ->
  piece_wf e2 ->
  I_ok (ck_egg (bp_ck e1)) (ck_egg (bp_ck e2)) (IHit P ti tj) ->
  family_vertex (progress_pieces pcs i j e1 e2 ti tj h) (bp_support e1) P /\
  family_vertex (progress_pieces pcs i j e1 e2 ti tj h) (bp_support e2) P.
Proof.
  intros pcs i j e1 e2 P ti tj h Hi Hj Hw1 Hw2 Hok.
  destruct (hit_at_abs e1 e2 P ti tj (proj1 Hw1) (proj1 Hw2) Hok) as [Ha Hb].
  destruct (split_joint_endpoint e1 ti h (proj1 Hw1)) as [Ea _].
  destruct (split_joint_endpoint e2 tj h (proj1 Hw2)) as [Eb _].
  rewrite <- Ha in Ea. rewrite <- Hb in Eb.
  split.
  - exists (fst (split_piece e1 ti h)). split.
    + unfold progress_pieces. apply in_or_app. left.
      unfold cooked_four. simpl. left. reflexivity.
    + split.
      * destruct (split_preserves_same_support e1 ti h) as [Eq _].
        unfold same_support in Eq. exact Eq.
      * exact Ea.
  - exists (fst (split_piece e2 tj h)). split.
    + unfold progress_pieces. apply in_or_app. left.
      unfold cooked_four. simpl. right. right. left. reflexivity.
    + split.
      * destruct (split_preserves_same_support e2 tj h) as [Eq _].
        unfold same_support in Eq. exact Eq.
      * exact Eb.
Qed.

Lemma admissible_progress : forall pcs e1 e2 P ti tj,
  admissible_hit pcs e1 e2 P ti tj ->
  progress_hit pcs e1 e2 (IHit P ti tj).
Proof.
  intros pcs e1 e2 P ti tj [_ [Hnv _]].
  unfold progress_hit, vertex_of_both. exact Hnv.
Qed.

Lemma counted_shrink_incl : forall pcs i j e1 e2 P ti tj h s1 s2 q,
  nth_error pcs i = Some e1 ->
  nth_error pcs j = Some e2 ->
  i <> j ->
  piece_wf e1 ->
  piece_wf e2 ->
  I_ok (ck_egg (bp_ck e1)) (ck_egg (bp_ck e2)) (IHit P ti tj) ->
  progress_hit pcs e1 e2 (IHit P ti tj) ->
  In q (counted (progress_pieces pcs i j e1 e2 ti tj h) s1 s2) ->
  In q (counted pcs s1 s2).
Proof.
  intros pcs i j e1 e2 P ti tj h s1 s2 q Hi Hj Hij Hw1 Hw2 Hok Hpr Hin.
  set (pcs' := progress_pieces pcs i j e1 e2 ti tj h) in *.
  unfold counted in Hin. destruct (canon2 s1 s2) as [u v] eqn:Ec.
  rewrite dedup_In in Hin. apply filter_In in Hin. destruct Hin as [Hraw Hkeep].
  destruct (hit_param_in_unit e1 e2 P ti tj (proj1 Hw1) (proj1 Hw2) Hok) as [Hti Htj].
  assert (Hr : raw_pts pcs' u v = raw_pts pcs u v).
  { apply (raw_progress pcs i j e1 e2 ti tj h u v Hi Hj Hij
            (proj1 Hw1) (proj1 Hw2) Hti Htj). }
  rewrite Hr in Hraw.
  assert (Hk : keep_b pcs u v q = true).
  { eapply keep_step.
    - exact Hi. - exact Hj. - exact Hij. - exact Hw1. - exact Hw2.
    - exact Hok. - exact Hpr. - exact Hkeep. }
  unfold counted. rewrite Ec. rewrite dedup_In. apply filter_In. split; assumption.
Qed.

Lemma counted_step_le : forall pcs i j e1 e2 P ti tj h s1 s2,
  nth_error pcs i = Some e1 ->
  nth_error pcs j = Some e2 ->
  i <> j ->
  piece_wf e1 ->
  piece_wf e2 ->
  I_ok (ck_egg (bp_ck e1)) (ck_egg (bp_ck e2)) (IHit P ti tj) ->
  progress_hit pcs e1 e2 (IHit P ti tj) ->
  (length (counted (progress_pieces pcs i j e1 e2 ti tj h) s1 s2)
   <= length (counted pcs s1 s2))%nat.
Proof.
  intros pcs i j e1 e2 P ti tj h s1 s2 Hi Hj Hij Hw1 Hw2 Hok Hpr.
  set (pcs' := progress_pieces pcs i j e1 e2 ti tj h).
  unfold counted. destruct (canon2 s1 s2) as [u v].
  destruct (hit_param_in_unit e1 e2 P ti tj (proj1 Hw1) (proj1 Hw2) Hok) as [Hti Htj].
  assert (Er : raw_pts pcs' u v = raw_pts pcs u v).
  { apply (raw_progress pcs i j e1 e2 ti tj h u v Hi Hj Hij
            (proj1 Hw1) (proj1 Hw2) Hti Htj). }
  rewrite Er. apply dedup_filter_length. intros q Hq.
  eapply keep_step.
  - exact Hi. - exact Hj. - exact Hij. - exact Hw1. - exact Hw2.
  - exact Hok. - exact Hpr. - exact Hq.
Qed.

Lemma hit_leaves_counted : forall pcs i j e1 e2 P ti tj h,
  nth_error pcs i = Some e1 ->
  nth_error pcs j = Some e2 ->
  piece_wf e1 ->
  piece_wf e2 ->
  I_ok (ck_egg (bp_ck e1)) (ck_egg (bp_ck e2)) (IHit P ti tj) ->
  ~ In P (counted (progress_pieces pcs i j e1 e2 ti tj h)
            (bp_support e1) (bp_support e2)).
Proof.
  intros pcs i j e1 e2 P ti tj h Hi Hj Hw1 Hw2 Hok Hin.
  set (pcs' := progress_pieces pcs i j e1 e2 ti tj h) in *.
  set (s1 := bp_support e1). set (s2 := bp_support e2).
  unfold counted, s1, s2 in Hin.
  destruct (canon2 (bp_support e1) (bp_support e2)) as [u v] eqn:Ec.
  simpl in Hin. rewrite dedup_In in Hin. apply filter_In in Hin.
  destruct Hin as [_ Hkeep].
  unfold keep_b in Hkeep. apply andb_prop in Hkeep. destruct Hkeep as [_ Hneg].
  apply negb_true_iff in Hneg.
  destruct (hit_becomes_vertex pcs i j e1 e2 P ti tj h Hi Hj Hw1 Hw2 Hok) as [V1 V2].
  assert (Hb : vertex_b pcs' u P = true /\ vertex_b pcs' v P = true).
  { destruct (canon_orient s1 s2 u v Ec) as [[-> ->]|[-> ->]];
      split; apply vertex_spec; assumption. }
  assert (Bad : vertex_b pcs' u P && vertex_b pcs' v P = true).
  { apply andb_true_intro. exact Hb. }
  rewrite Bad in Hneg. discriminate.
Qed.

Lemma nodup_drop_lt : forall (A : Type) (l1 l2 : list A) (a : A),
  NoDup l1 ->
  (forall x, In x l1 -> In x l2) ->
  In a l2 ->
  ~ In a l1 ->
  (length l1 < length l2)%nat.
Proof.
  intros A l1 l2 a Hnd Hincl Hin Hnin.
  destruct (in_split a l2 Hin) as [l2a [l2b Heq]]. subst l2.
  assert (Hle : (length l1 <= length (l2a ++ l2b))%nat).
  { apply NoDup_incl_length; [exact Hnd|].
    intros x Hx. specialize (Hincl x Hx).
    apply in_app_or in Hincl. destruct Hincl as [H|H].
    - apply in_or_app. left. exact H.
    - simpl in H. destruct H as [->|H].
      + contradiction.
      + apply in_or_app. right. exact H. }
  assert (Hlen : length (l2a ++ a :: l2b) = S (length (l2a ++ l2b))).
  { rewrite !length_app. simpl. rewrite Nat.add_succ_r. reflexivity. }
  rewrite Hlen. apply Nat.lt_succ_r. exact Hle.
Qed.

Lemma support_eq_dec : forall s1 s2 : BagSupport, {s1 = s2} + {s1 <> s2}.
Proof.
  intros s1 s2. destruct (support_eqb s1 s2) eqn:E.
  - left. apply support_eqb_true. exact E.
  - right. intro Heq. apply support_eqb_true in Heq. congruence.
Qed.

Lemma fold_add_lt : forall (A : Type) (f g : A -> nat) (l : list A) (b : A),
  In b l ->
  (forall x, (f x <= g x)%nat) ->
  (f b < g b)%nat ->
  (fold_right Nat.add 0%nat (map f l) < fold_right Nat.add 0%nat (map g l))%nat.
Proof.
  intros A f g l b Hin Hle Hlt.
  induction l as [|x tl IH]; simpl in Hin; [contradiction|].
  simpl. destruct Hin as [->|Hin].
  - apply Nat.add_lt_le_mono; [exact Hlt|].
    clear IH Hlt b. induction tl as [|y tl IHy]; simpl; [lia|].
    apply Nat.add_le_mono; [apply Hle| exact IHy].
  - apply Nat.add_le_lt_mono; [apply Hle| apply IH; exact Hin].
Qed.

Lemma pair_sum_strict_one : forall ss f g a b,
  NoDup ss ->
  In a ss ->
  In b ss ->
  a <> b ->
  (forall x y, f x y = f y x) ->
  (forall x y, g x y = g y x) ->
  (forall x y, (f x y <= g x y)%nat) ->
  (f a b < g a b)%nat ->
  (pair_sum ss f < pair_sum ss g)%nat.
Proof.
  induction ss as [|s tl IH]; intros f g a b Hnd Ha Hb Hab Hfs Hgs Hle Hlt;
    simpl in Ha; [contradiction|].
  simpl. inversion Hnd as [|s0 tl0 Hnin Hnd']; subst s0 tl0.
  destruct (support_eq_dec s a) as [->|Hsa].
  - assert (Hb' : In b tl).
    { destruct Hb as [Heq|Hb']; [rewrite Heq in Hab; contradiction| exact Hb']. }
    apply Nat.add_lt_le_mono.
    + apply (fold_add_lt _ (f a) (g a) tl b Hb').
      * intros x. apply Hle.
      * exact Hlt.
    + apply pair_sum_le. exact Hle.
  - destruct (support_eq_dec s b) as [->|Hsb].
    + assert (Ha' : In a tl).
      { destruct Ha as [Heq|Ha']; [rewrite Heq in Hab; contradiction| exact Ha']. }
      apply Nat.add_lt_le_mono.
      * apply (fold_add_lt _ (f b) (g b) tl a Ha').
        -- intros x. apply Hle.
        -- rewrite Hfs, Hgs. exact Hlt.
      * apply pair_sum_le. exact Hle.
    + assert (Ha' : In a tl).
      { destruct Ha as [Heq|Ha']; [contradiction| exact Ha']. }
      assert (Hb' : In b tl).
      { destruct Hb as [Heq|Hb']; [contradiction| exact Hb']. }
      apply Nat.add_le_lt_mono.
      * assert (Hrow : forall l,
                 (fold_right Nat.add 0%nat (map (f s) l) <=
                  fold_right Nat.add 0%nat (map (g s) l))%nat).
        { intro l. induction l as [|y l IHl]; simpl; [lia|].
          apply Nat.add_le_mono; [apply Hle| exact IHl]. }
        exact (Hrow tl).
      * apply (IH f g a b Hnd' Ha' Hb' Hab Hfs Hgs Hle Hlt).
Qed.

(* WITNESS {"claimId":"0007-loop-letter3-strict","topic":"overlay","lemma":"rho_step_strict","title":"admissible hit strictly decreases rho","file":"theories/SheetHenBagRun.v","witness":"rho_step_strict","board":"ADR-0007"} *)
Theorem rho_step_strict : forall sh pcs i j e1 e2 P ti tj,
  nth_error pcs i = Some e1 ->
  nth_error pcs j = Some e2 ->
  i <> j ->
  piece_wf e1 ->
  piece_wf e2 ->
  bp_support e1 <> bp_support e2 ->
  admissible_hit pcs e1 e2 P ti tj ->
  (rho (step_hit (BagLive sh pcs) (mkHitPick i j P ti tj)) <
   rho (BagLive sh pcs))%nat.
Proof.
  intros sh pcs i j e1 e2 P ti tj Hi Hj Hij Hw1 Hw2 Hdist Hadm.
  set (h := mint_or_share pcs P).
  set (pcs' := progress_pieces pcs i j e1 e2 ti tj h).
  set (s1 := bp_support e1). set (s2 := bp_support e2).
  assert (Hpr : progress_hit pcs e1 e2 (IHit P ti tj)).
  { apply admissible_progress. exact Hadm. }
  assert (Hok : I_ok (ck_egg (bp_ck e1)) (ck_egg (bp_ck e2)) (IHit P ti tj)).
  { exact (proj1 Hadm). }
  unfold step_hit. simpl. rewrite Hi, Hj. simpl.
  assert (Hin : In P (counted pcs s1 s2)).
  { exact (admissible_in_counted pcs e1 e2 P ti tj
            (nth_error_In _ _ Hi) (nth_error_In _ _ Hj)
            Hw1 Hw2 Hdist Hadm). }
  assert (Hout : ~ In P (counted pcs' s1 s2)).
  { apply (hit_leaves_counted pcs i j e1 e2 P ti tj h); assumption. }
  assert (Hincl : forall q, In q (counted pcs' s1 s2) -> In q (counted pcs s1 s2)).
  { intros q Hq.
    apply (counted_shrink_incl pcs i j e1 e2 P ti tj h s1 s2 q); assumption. }
  assert (Hone : (length (counted pcs' s1 s2) < length (counted pcs s1 s2))%nat).
  { unfold counted in Hin, Hout, Hincl. unfold counted.
    destruct (canon2 s1 s2) as [u v]. simpl in Hin, Hout, Hincl. simpl.
    apply nodup_drop_lt with (a := P).
    - apply dedup_NoDup.
    - exact Hincl.
    - exact Hin.
    - exact Hout. }
  assert (Hle : forall x y,
            (length (counted pcs' x y) <= length (counted pcs x y))%nat).
  { intros x y.
    apply (counted_step_le pcs i j e1 e2 P ti tj h x y); assumption. }
  assert (Hperm : Permutation (supports_of pcs') (supports_of pcs)).
  { apply (supports_progress_perm pcs i j e1 e2 ti tj h Hi Hj Hij
            (proj1 Hw1) (proj1 Hw2)). }
  assert (Hsym' : forall x y,
            length (counted pcs' x y) = length (counted pcs' y x)).
  { intros x y. f_equal. apply counted_sym. }
  unfold rho, rho_pcs. fold h. fold pcs'.
  rewrite (pair_sum_perm (supports_of pcs') (supports_of pcs)
            (fun x y => length (counted pcs' x y)) Hperm Hsym').
  apply pair_sum_strict_one with (a := s1) (b := s2).
  - apply supports_NoDup.
  - apply supports_in. exists e1. split; [eapply nth_error_In; exact Hi| reflexivity].
  - apply supports_in. exists e2. split; [eapply nth_error_In; exact Hj| reflexivity].
  - exact Hdist.
  - intros x y. f_equal. apply counted_sym.
  - intros x y. f_equal. apply counted_sym.
  - exact Hle.
  - exact Hone.
Qed.

(* -------------------------------------------------------------------------- *)
(* bag_run on fuel ρ+1. A decline stops. The selector is a parameter.         *)
(* -------------------------------------------------------------------------- *)

Definition pick_spec (pick : SheetBag -> option HitPick) (b : SheetBag) : Prop :=
  match b, pick b with
  | _, None => True
  | BagDeclined _, Some _ => False
  | BagLive _ pcs, Some w =>
      exists e1 e2,
        nth_error pcs (hp_i w) = Some e1 /\
        nth_error pcs (hp_j w) = Some e2 /\
        hp_i w <> hp_j w /\
        piece_wf e1 /\
        piece_wf e2 /\
        bp_support e1 <> bp_support e2 /\
        admissible_hit pcs e1 e2 (hp_P w) (hp_ti w) (hp_tj w)
  end.

Definition run_stopped (pick : SheetBag -> option HitPick) (b : SheetBag) : Prop :=
  match b with
  | BagDeclined _ => True
  | BagLive _ _ => pick b = None
  end.

Fixpoint bag_run (pick : SheetBag -> option HitPick) (fuel : nat) (b : SheetBag)
  : SheetBag :=
  match fuel with
  | O => b
  | S n =>
      match b with
      | BagDeclined _ => b
      | BagLive _ _ =>
          match pick b with
          | None => b
          | Some w => bag_run pick n (step_hit b w)
          end
      end
  end.

Fixpoint bag_run_steps (pick : SheetBag -> option HitPick) (fuel : nat) (b : SheetBag)
  : nat :=
  match fuel with
  | O => O
  | S n =>
      match b with
      | BagDeclined _ => O
      | BagLive _ _ =>
          match pick b with
          | None => O
          | Some w => S (bag_run_steps pick n (step_hit b w))
          end
      end
  end.

Lemma step_hit_rho_lt : forall b w,
  match b with
  | BagDeclined _ => False
  | BagLive _ pcs =>
      exists e1 e2,
        nth_error pcs (hp_i w) = Some e1 /\
        nth_error pcs (hp_j w) = Some e2 /\
        hp_i w <> hp_j w /\
        piece_wf e1 /\
        piece_wf e2 /\
        bp_support e1 <> bp_support e2 /\
        admissible_hit pcs e1 e2 (hp_P w) (hp_ti w) (hp_tj w)
  end ->
  (rho (step_hit b w) < rho b)%nat.
Proof.
  intros [sh pcs|sh] w H; [|contradiction].
  destruct w as [i j P ti tj].
  simpl in H.
  destruct H as [e1 [e2 [Hi [Hj [Hij [Hw1 [Hw2 [Hdist Hadm]]]]]]]].
  eapply rho_step_strict.
  - exact Hi. - exact Hj. - exact Hij. - exact Hw1. - exact Hw2.
  - exact Hdist. - exact Hadm.
Qed.

Lemma bag_run_fuel_stopped : forall pick fuel b,
  (forall b0, pick_spec pick b0) ->
  (rho b < fuel)%nat ->
  run_stopped pick (bag_run pick fuel b).
Proof.
  intros pick fuel.
  induction fuel as [|fuel IH]; intros b Hspec Hfuel.
  - lia.
  - destruct b as [sh pcs|sh].
    + simpl.
      destruct (pick (BagLive sh pcs)) as [w|] eqn:Ep.
      * assert (Hlt : (rho (step_hit (BagLive sh pcs) w) <
                       rho (BagLive sh pcs))%nat).
        { apply step_hit_rho_lt.
          specialize (Hspec (BagLive sh pcs)).
          unfold pick_spec in Hspec. rewrite Ep in Hspec. exact Hspec. }
        apply IH; [exact Hspec|].
        apply Nat.lt_le_trans with (rho (BagLive sh pcs));
          [exact Hlt | apply Nat.lt_succ_r; exact Hfuel].
      * unfold run_stopped. exact Ep.
    + simpl. exact I.
Qed.

Theorem bag_run_fixpoint : forall pick b,
  (forall b0, pick_spec pick b0) ->
  run_stopped pick (bag_run pick (S (rho b)) b).
Proof.
  intros pick b Hspec.
  apply bag_run_fuel_stopped; [exact Hspec|].
  apply Nat.lt_succ_diag_r.
Qed.

Definition rho_adm_step_strict := rho_step_strict.

(* Letter 5, unproved. bag_run never takes the IDecline arm. *)
Definition letter5_obligation : Prop :=
  forall pick b, (forall b0, pick_spec pick b0) -> pick b = None ->
  rho b = 0%nat /\ match b with
  | BagDeclined _ => True
  | BagLive _ pcs => forall a c, In a pcs -> In c pcs -> a <> c ->
      ~ I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck c)) IDecline end.

Lemma counted_not_vertex : forall pcs s1 s2 p,
  In p (counted pcs s1 s2) -> ~ vertex_of_both pcs s1 s2 p.
Proof.
  intros pcs s1 s2 p Hin Hv.
  unfold counted in Hin. destruct (canon2 s1 s2) as [u v] eqn:Ec.
  rewrite dedup_In in Hin. apply filter_In in Hin. destruct Hin as [_ Hk].
  unfold keep_b in Hk. apply andb_prop in Hk. destruct Hk as [_ Hn].
  apply negb_true_iff in Hn.
  destruct Hv as [V1 V2].
  assert (Hb : vertex_b pcs u p = true /\ vertex_b pcs v p = true).
  { destruct (canon_orient s1 s2 u v Ec) as [[-> ->]|[-> ->]];
      split; apply vertex_spec; assumption. }
  assert (Bad : vertex_b pcs u p && vertex_b pcs v p = true).
  { apply andb_true_intro. exact Hb. }
  rewrite Bad in Hn. discriminate.
Qed.

Lemma pair_sum_zero : forall ss f,
  (forall a b, f a b = 0%nat) -> pair_sum ss f = 0%nat.
Proof.
  intros ss f Hz.
  induction ss as [|s tl IH]; simpl.
  - reflexivity.
  - rewrite IH. rewrite Nat.add_0_r. clear IH.
    induction tl as [|b tl IHb]; simpl.
    + reflexivity.
    + rewrite (Hz s b). rewrite IHb. reflexivity.
Qed.

Theorem no_admissible_hit_noded : forall pcs,
  (forall s1 s2 p, In p (counted pcs s1 s2) -> vertex_of_both pcs s1 s2 p) ->
  rho_pcs pcs = 0%nat /\
  (forall e1 e2 P ti tj,
     In e1 pcs -> In e2 pcs ->
     piece_wf e1 -> piece_wf e2 ->
     bp_support e1 <> bp_support e2 ->
     ~ admissible_hit pcs e1 e2 P ti tj).
Proof.
  intros pcs Hv. split.
  - unfold rho_pcs. apply pair_sum_zero. intros a b.
    destruct (counted pcs a b) as [|p tl] eqn:Ec.
    + reflexivity.
    + exfalso.
      assert (Hin : In p (counted pcs a b)).
      { rewrite Ec. left. reflexivity. }
      apply (counted_not_vertex pcs a b p Hin). apply Hv. exact Hin.
  - intros e1 e2 P ti tj I1 I2 Hw1 Hw2 Hdist Hadm.
    assert (Hin : In P (counted pcs (bp_support e1) (bp_support e2))).
    { exact (admissible_in_counted pcs e1 e2 P ti tj I1 I2 Hw1 Hw2 Hdist Hadm). }
    apply (counted_not_vertex pcs (bp_support e1) (bp_support e2) P Hin).
    apply Hv. exact Hin.
Qed.

Print Assumptions req_b_false.
Print Assumptions on_chord_spec.
Print Assumptions on_circ_spec.
Print Assumptions on_cloth_spec.
Print Assumptions chord_nondeg_spec.
Print Assumptions circ_open_span_spec.
Print Assumptions scope_spec.
Print Assumptions I_ok_hit_spec.
Print Assumptions canon_orient.
Print Assumptions vertex_of_both_spec.
Print Assumptions in_pts_spec.
Print Assumptions overlap_b_circ_chord.
Print Assumptions overlap_b_chord_circ.
Print Assumptions overlap_impl_spec.
Print Assumptions admissible_hit_spec.
Print Assumptions admissible_hit_dec.
Print Assumptions letter1_step_accepts_any_hen.
Print Assumptions list_max_ge.
Print Assumptions fresh_not_member.
Print Assumptions hen_sits_in_list.
Print Assumptions lookup_hen_at_sits.
Print Assumptions sits_lookup_some.
Print Assumptions mint_agrees.
Print Assumptions mint_or_share_cases.
Print Assumptions lo_child_sits.
Print Assumptions hi_child_sits.
Print Assumptions child_sit_account.
Print Assumptions progress_sit_account.
Print Assumptions mint_or_share_preserves_unique.
Print Assumptions piece_wf_independent_of_hen.
Print Assumptions step_hit_is_progress.
Print Assumptions admissible_step_preserves_inv.
Print Assumptions win_abs_bounds.
Print Assumptions both_in_image.
Print Assumptions admissible_class.
Print Assumptions admissible_in_counted.
Print Assumptions split_joint_endpoint.
Print Assumptions hit_becomes_vertex.
Print Assumptions admissible_progress.
Print Assumptions counted_shrink_incl.
Print Assumptions counted_step_le.
Print Assumptions hit_leaves_counted.
Print Assumptions nodup_drop_lt.
Print Assumptions support_eq_dec.
Print Assumptions fold_add_lt.
Print Assumptions pair_sum_strict_one.
Print Assumptions rho_step_strict.
Print Assumptions step_hit_rho_lt.
Print Assumptions bag_run_fuel_stopped.
Print Assumptions bag_run_fixpoint.
Print Assumptions counted_not_vertex.
Print Assumptions pair_sum_zero.
Print Assumptions no_admissible_hit_noded.
