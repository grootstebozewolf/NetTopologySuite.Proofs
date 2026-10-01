(* ============================================================================
   NetTopologySuite.Proofs.SheetHenRhoConf
   ----------------------------------------------------------------------------
   Letter 6a-iii. claimId: none.
   Headline: run_vset_determined.
   Two lawful selectors finish with the same vertex set.
   target_step_invariant and vset_step_grows are the step facts.
   cook_loop_rho_holds discharges CookLoopRho. cook_loop_status stays
   LoopObligation. Does not remint 0007-loop-letter6.
   3-axiom host. No Admitted.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List PeanoNat Bool.
From NTS.Proofs Require Import
  Distance SheetHenCook SheetHenCookCore SheetHenBag
  SheetHenRho SheetHenRhoCount SheetHenRhoEnds
  SheetHenBagRun SheetHenLoop3 SheetHenPickSpec
  SheetHenNodedOv SheetHenRhoLoop HostCircChordOracle.
Import ListNotations.
Local Open Scope R_scope.

Lemma vset_step_grows : forall pcs i j e1 e2 ti tj h p,
  nth_error pcs i = Some e1 ->
  nth_error pcs j = Some e2 ->
  i <> j ->
  vmem pcs p ->
  vmem (progress_pieces pcs i j e1 e2 ti tj h) p.
Proof.
  intros pcs i j e1 e2 ti tj h p Hi Hj Hij [pc [Hin Hep]].
  assert (Hv : family_vertex pcs (bp_support pc) p).
  { exists pc. split; [exact Hin|]. split; [reflexivity| exact Hep]. }
  destruct (progress_vertices_mono pcs i j e1 e2 ti tj h _ p Hi Hj Hij Hv)
    as [pc' [Hin' [_ Hep']]].
  exists pc'. split; [exact Hin'| exact Hep'].
Qed.

Definition pending (pcs : list BagPiece) (p : Point) : Prop :=
  exists s1 s2, s1 <> s2 /\ In p (counted pcs s1 s2).

Definition target (pcs : list BagPiece) (p : Point) : Prop :=
  vmem pcs p \/ pending pcs p.

Fixpoint vmem_b (pcs : list BagPiece) (p : Point) : bool :=
  match pcs with
  | nil => false
  | pc :: tl => endpoint_b pc p || vmem_b tl p
  end.

Lemma vmem_spec : forall pcs p, vmem_b pcs p = true <-> vmem pcs p.
Proof.
  intros pcs p. induction pcs as [|pc tl IH]; simpl.
  - split; intro H; [discriminate| destruct H as [pc [[] _]]].
  - rewrite orb_true_iff, IH, endpoint_spec. split.
    + intros [He|Hv].
      * exists pc. split; [left; reflexivity| exact He].
      * destruct Hv as [pc' [Hin Hep]].
        exists pc'. split; [right; exact Hin| exact Hep].
    + intros [pc' [[->|Hin] Hep]].
      * left. exact Hep.
      * right. exists pc'. split; assumption.
Qed.

Lemma hit_not_decline : forall e1 e2 p ti tj,
  I_ok e1 e2 (IHit p ti tj) -> ~ I_ok e1 e2 IDecline.
Proof.
  intros e1 e2 p ti tj H Hd.
  destruct e1; destruct e2; simpl in H, Hd; try contradiction.
  - destruct H as [Hs _]. exact (Hd Hs).
  - destruct H as [Hs _]. exact (Hd Hs).
Qed.

Lemma decline_swap : forall e1 e2,
  I_ok e1 e2 IDecline -> I_ok e2 e1 IDecline.
Proof.
  intros e1 e2 H.
  destruct e1; destruct e2; simpl in H; simpl; try contradiction; exact H.
Qed.

Lemma hit_in_windows : forall a b p ti tj,
  piece_wf a -> piece_wf b ->
  I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck b)) (IHit p ti tj) ->
  window_pts (bp_support a) (bp_window a) p /\
  window_pts (bp_support b) (bp_window b) p.
Proof.
  intros a b p ti tj Ha Hb Hok.
  destruct (hit_at_abs a b p ti tj (proj1 Ha) (proj1 Hb) Hok) as [Ea Eb].
  destruct (hit_param_in_unit a b p ti tj (proj1 Ha) (proj1 Hb) Hok) as [Hti Htj].
  destruct (win_abs_bounds (bp_window a) ti (proj2 Ha) Hti) as [Halo Hahi].
  destruct (win_abs_bounds (bp_window b) tj (proj2 Hb) Htj) as [Hblo Hbhi].
  split.
  - exists (win_abs (bp_window a) ti). split; [split; assumption| exact Ea].
  - exists (win_abs (bp_window b) tj). split; [split; assumption| exact Eb].
Qed.

Lemma chord_window_const : forall c lo hi t,
  chord_eval c lo = chord_eval c hi ->
  lo <= t <= hi ->
  chord_eval c t = chord_eval c lo.
Proof.
  intros c lo hi t Heq Ht.
  destruct (Req_EM_T lo hi) as [E|N].
  - assert (Et : t = lo) by lra. subst t. reflexivity.
  - destruct (chord_eval_lin c t) as [Htx Hty].
    destruct (chord_eval_lin c lo) as [Hlx Hly].
    destruct (chord_eval_lin c hi) as [Hhx Hhy].
    assert (Hx : px (chord_eval c hi) = px (chord_eval c lo)) by (rewrite Heq; reflexivity).
    assert (Hy : py (chord_eval c hi) = py (chord_eval c lo)) by (rewrite Heq; reflexivity).
    assert (Dx : (hi - lo) * chord_dx c = 0).
    { replace ((hi - lo) * chord_dx c)
        with (px (chord_eval c hi) - px (chord_eval c lo)) by (rewrite Hhx, Hlx; ring).
      rewrite Hx. ring. }
    assert (Dy : (hi - lo) * chord_dy c = 0).
    { replace ((hi - lo) * chord_dy c)
        with (py (chord_eval c hi) - py (chord_eval c lo)) by (rewrite Hhy, Hly; ring).
      rewrite Hy. ring. }
    apply Rmult_integral in Dx. apply Rmult_integral in Dy.
    destruct Dx as [Hz|Hdx]; [lra|]. destruct Dy as [Hz|Hdy]; [lra|].
    apply pt_eq_coords.
    + rewrite Htx, Hlx, Hdx. ring.
    + rewrite Hty, Hly, Hdy. ring.
Qed.

Lemma chord_point_nondeg : forall pc p s,
  piece_wf pc ->
  ck_egg (bp_ck pc) = MkChord s ->
  window_pts (bp_support pc) (bp_window pc) p ->
  ~ piece_endpoint pc p ->
  chord_nondeg s.
Proof.
  intros pc p s Hwf Hs Hpt Hne.
  destruct (chord_nondeg_b s) eqn:Eb; [apply chord_nondeg_spec; exact Eb|].
  exfalso.
  unfold chord_nondeg_b in Eb. apply negb_false_iff in Eb.
  apply andb_prop in Eb. destruct Eb as [Ex Ey].
  apply req_b_true in Ex. apply req_b_true in Ey.
  destruct Hwf as [Hr Ho].
  destruct pc as [[src dst egg] sup w prov].
  destruct sup as [c|c]; destruct egg as [e|e|e|e|e];
    simpl in Hr, Hs, Hpt, Hne; try contradiction; try discriminate.
  injection Hs as ->.
  unfold window_chord in Hr.
  assert (Hends : chord_eval c (win_lo w) = chord_eval c (win_hi w)).
  { apply pt_eq_coords.
    - unfold chord_dx in Ex. rewrite Hr in Ex. simpl in Ex.
      symmetry. apply Rminus_diag_uniq. exact Ex.
    - unfold chord_dy in Ey. rewrite Hr in Ey. simpl in Ey.
      symmetry. apply Rminus_diag_uniq. exact Ey. }
  destruct Hpt as [t [Ht Hp]].
  assert (Et : chord_eval c t = chord_eval c (win_lo w)).
  { apply (chord_window_const c (win_lo w) (win_hi w) t Hends Ht). }
  apply Hne. left. simpl. exact (eq_trans Hp Et).
Qed.

Definition has_chord (pcs : list BagPiece) : Prop :=
  exists pc s, In pc pcs /\ ck_egg (bp_ck pc) = MkChord s.

Definition circles_open (pcs : list BagPiece) : Prop :=
  forall pc c, In pc pcs -> ck_egg (bp_ck pc) = MkCirc c -> circ_open_span c.

Definition scope_ready (pcs : list BagPiece) : Prop :=
  has_chord pcs -> circles_open pcs.

Lemma no_decline_scope : forall pcs,
  (forall pc, In pc pcs -> piece_wf pc) ->
  no_decline_pair pcs ->
  scope_ready pcs.
Proof.
  intros pcs Hwf Hnd Hch pc c Hin Hc.
  destruct Hch as [qc [s [Hqin Hs]]].
  assert (Hneq : pc <> qc).
  { intro E. subst qc. rewrite Hc in Hs. discriminate. }
  assert (Hdec : ~ I_ok (ck_egg (bp_ck pc)) (ck_egg (bp_ck qc)) IDecline).
  { apply Hnd; assumption. }
  pose proof (nodecline_class pc qc (Hwf pc Hin) (Hwf qc Hqin) Hdec) as Hcl.
  revert Hcl. rewrite Hc, Hs. simpl. intros Hcl. exact (proj1 Hcl).
Qed.

Lemma split_parent_chord : forall pc u h ch,
  ck_egg (bp_ck (fst (split_piece pc u h))) = MkChord ch \/
  ck_egg (bp_ck (snd (split_piece pc u h))) = MkChord ch ->
  exists ch0, ck_egg (bp_ck pc) = MkChord ch0.
Proof.
  intros [[src dst egg] sup w prov] u h ch H.
  destruct egg as [e|e|e|e|e]; simpl in H.
  - exists e. reflexivity.
  - destruct H as [H|H]; discriminate.
  - destruct H as [H|H]; discriminate.
  - destruct H as [H|H]; discriminate.
  - destruct H as [H|H]; discriminate.
Qed.

Lemma split_circ_child_open : forall pc u h c,
  0 <= u <= 1 ->
  (forall e, ck_egg (bp_ck pc) = MkCirc e -> circ_open_span e) ->
  ck_egg (bp_ck (fst (split_piece pc u h))) = MkCirc c \/
  ck_egg (bp_ck (snd (split_piece pc u h))) = MkCirc c ->
  circ_open_span c.
Proof.
  intros [[src dst egg] sup w prov] u h c Hu Hop Hch.
  destruct egg as [e|e|e|e|e]; simpl in Hch.
  - destruct Hch as [H|H]; discriminate.
  - assert (Ho : circ_open_span e) by (apply Hop; reflexivity).
    destruct Ho as [Hlo Hhi].
    destruct Hch as [H|H]; injection H as <-.
    + unfold circ_open_span, circ_split. cbn [fst circ_sweep]. nra.
    + unfold circ_open_span, circ_split. cbn [snd circ_sweep]. nra.
  - destruct Hch as [H|H]; discriminate.
  - destruct Hch as [H|H]; discriminate.
  - destruct Hch as [H|H]; discriminate.
Qed.

Lemma progress_scope_ready : forall pcs i j e1 e2 P ti tj h,
  nth_error pcs i = Some e1 ->
  nth_error pcs j = Some e2 ->
  piece_wf e1 ->
  piece_wf e2 ->
  I_ok (ck_egg (bp_ck e1)) (ck_egg (bp_ck e2)) (IHit P ti tj) ->
  scope_ready pcs ->
  scope_ready (progress_pieces pcs i j e1 e2 ti tj h).
Proof.
  intros pcs i j e1 e2 P ti tj h Hi Hj Hw1 Hw2 Hok Hready Hch.
  destruct (hit_param_in_unit e1 e2 P ti tj (proj1 Hw1) (proj1 Hw2) Hok) as [Hti Htj].
  assert (Hold : has_chord pcs).
  { destruct Hch as [pc [s [Hin Hs]]].
    unfold progress_pieces in Hin. apply in_app_or in Hin.
    destruct Hin as [Hfour|Hdrop].
    - unfold cooked_four in Hfour. simpl in Hfour.
      destruct Hfour as [<-|[<-|[<-|[<-|[]]]]].
      + destruct (split_parent_chord e1 ti h s (or_introl Hs)) as [s0 He].
        exists e1, s0. split; [eapply nth_error_In; exact Hi| exact He].
      + destruct (split_parent_chord e1 ti h s (or_intror Hs)) as [s0 He].
        exists e1, s0. split; [eapply nth_error_In; exact Hi| exact He].
      + destruct (split_parent_chord e2 tj h s (or_introl Hs)) as [s0 He].
        exists e2, s0. split; [eapply nth_error_In; exact Hj| exact He].
      + destruct (split_parent_chord e2 tj h s (or_intror Hs)) as [s0 He].
        exists e2, s0. split; [eapply nth_error_In; exact Hj| exact He].
    - exists pc, s. split; [exact (filter_idx_In _ _ _ _ _ Hdrop)| exact Hs]. }
  intros pc c Hin Hc.
  unfold progress_pieces in Hin. apply in_app_or in Hin.
  destruct Hin as [Hfour|Hdrop].
  - unfold cooked_four in Hfour. simpl in Hfour.
    destruct Hfour as [<-|[<-|[<-|[<-|[]]]]].
    + apply (split_circ_child_open e1 ti h c Hti).
      * intros e He. exact (Hready Hold e1 e (nth_error_In _ _ Hi) He).
      * left. exact Hc.
    + apply (split_circ_child_open e1 ti h c Hti).
      * intros e He. exact (Hready Hold e1 e (nth_error_In _ _ Hi) He).
      * right. exact Hc.
    + apply (split_circ_child_open e2 tj h c Htj).
      * intros e He. exact (Hready Hold e2 e (nth_error_In _ _ Hj) He).
      * left. exact Hc.
    + apply (split_circ_child_open e2 tj h c Htj).
      * intros e He. exact (Hready Hold e2 e (nth_error_In _ _ Hj) He).
      * right. exact Hc.
  - exact (Hready Hold pc c (filter_idx_In _ _ _ _ _ Hdrop) Hc).
Qed.

Lemma wf_egg_class : forall pc,
  piece_wf pc ->
  (exists s, ck_egg (bp_ck pc) = MkChord s) \/
  (exists c, ck_egg (bp_ck pc) = MkCirc c).
Proof.
  intros [[src dst egg] sup w prov] [Hr _].
  destruct sup as [cs|cc]; destruct egg as [e|e|e|e|e]; simpl in Hr; try contradiction.
  - left. exists e. reflexivity.
  - right. exists e. reflexivity.
Qed.

Lemma pair_share_nondecline : forall pcs a b p,
  (forall pc, In pc pcs -> piece_wf pc) ->
  scope_ready pcs ->
  In a pcs -> In b pcs ->
  window_pts (bp_support a) (bp_window a) p ->
  window_pts (bp_support b) (bp_window b) p ->
  ~ vmem pcs p ->
  ~ I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck b)) IDecline.
Proof.
  intros pcs a b p Hwf Hscope Ha Hb Hwa Hwb Hnv Hd.
  assert (Hnea : ~ piece_endpoint a p).
  { intro Hep. apply Hnv. exists a. split; assumption. }
  assert (Hneb : ~ piece_endpoint b p).
  { intro Hep. apply Hnv. exists b. split; assumption. }
  destruct (wf_egg_class a (Hwf a Ha)) as [[sa Ea]|[ca Ea]];
    destruct (wf_egg_class b (Hwf b Hb)) as [[sb Eb]|[cb Eb]];
    rewrite Ea, Eb in Hd; simpl in Hd; try contradiction.
  - assert (Hnd : chord_nondeg sa).
    { apply (chord_point_nondeg a p sa); [apply Hwf; exact Ha| exact Ea| exact Hwa| exact Hnea]. }
    assert (Ho : circ_open_span cb).
    { exact (Hscope (ex_intro _ a (ex_intro _ sa (conj Ha Ea))) b cb Hb Eb). }
    apply Hd. split; assumption.
  - assert (Hnd : chord_nondeg sb).
    { apply (chord_point_nondeg b p sb); [apply Hwf; exact Hb| exact Eb| exact Hwb| exact Hneb]. }
    assert (Ho : circ_open_span ca).
    { exact (Hscope (ex_intro _ b (ex_intro _ sb (conj Hb Eb))) a ca Ha Ea). }
    apply Hd. split; assumption.
Qed.

Lemma pending_not_vmem_hit : forall pcs p,
  (forall pc, In pc pcs -> piece_wf pc) ->
  scope_ready pcs ->
  pending pcs p ->
  ~ vmem pcs p ->
  has_adm_hit pcs.
Proof.
  intros pcs p Hwf Hscope [s1 [s2 [Hneq Hin]]] Hnv.
  destruct (counted_images pcs s1 s2 p Hin) as [Ia Ib].
  destruct Ia as [a [Ha [Hsa Hwa]]].
  destruct Ib as [b [Hb [Hsb Hwb]]].
  assert (Hwa' : window_pts (bp_support a) (bp_window a) p).
  { rewrite Hsa. exact Hwa. }
  assert (Hwb' : window_pts (bp_support b) (bp_window b) p).
  { rewrite Hsb. exact Hwb. }
  assert (Hdist : bp_support a <> bp_support b).
  { rewrite Hsa, Hsb. exact Hneq. }
  assert (Hpieces : a <> b).
  { intro E. subst b. exact (Hdist eq_refl). }
  assert (Hnd : ~ I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck b)) IDecline).
  { apply (pair_share_nondecline pcs a b p); assumption. }
  assert (HinC : In p (counted pcs (bp_support a) (bp_support b))).
  { rewrite Hsa, Hsb. exact Hin. }
  destruct (counted_adm_in pcs a b p (Hwf a Ha) (Hwf b Hb) Hwa' Hwb' HinC Hnd)
    as [ti [tj HinA]].
  pose proof (adm_list_admissible pcs a b (mkHitCand p ti tj) HinA) as Hadm.
  destruct (In_nth_error _ _ Ha) as [i Hi].
  destruct (In_nth_error _ _ Hb) as [j Hj].
  exists i, j, a, b, p, ti, tj.
  split; [exact Hi|]. split; [exact Hj|].
  split.
  - intro Eij. subst j. rewrite Hi in Hj. inversion Hj. subst b. exact (Hpieces eq_refl).
  - split; [apply Hwf; exact Ha|].
    split; [apply Hwf; exact Hb|].
    split; [exact Hdist| exact Hadm].
Qed.

Lemma keep_nonhit : forall pcs i j e1 e2 P ti tj h s1 s2 p,
  nth_error pcs i = Some e1 ->
  nth_error pcs j = Some e2 ->
  i <> j ->
  piece_wf e1 ->
  piece_wf e2 ->
  I_ok (ck_egg (bp_ck e1)) (ck_egg (bp_ck e2)) (IHit P ti tj) ->
  p <> P ->
  keep_b pcs s1 s2 p = true ->
  keep_b (progress_pieces pcs i j e1 e2 ti tj h) s1 s2 p = true.
Proof.
  intros pcs i j e1 e2 P ti tj h s1 s2 p Hi Hj Hij Hw1 Hw2 Hok Hneq Hk.
  set (pcs' := progress_pieces pcs i j e1 e2 ti tj h) in *.
  unfold keep_b in Hk. apply andb_prop in Hk. destruct Hk as [Himg Hn].
  apply andb_prop in Himg. destruct Himg as [Ia Ib].
  apply negb_true_iff in Hn.
  unfold keep_b. apply andb_true_intro. split.
  - apply andb_true_intro. split.
    + apply in_image_spec.
      apply (proj1 (progress_preserves_support_image pcs i j e1 e2 P ti tj h s1 p
        Hi Hj Hij Hw1 Hw2 Hok)).
      apply in_image_spec. exact Ia.
    + apply in_image_spec.
      apply (proj1 (progress_preserves_support_image pcs i j e1 e2 P ti tj h s2 p
        Hi Hj Hij Hw1 Hw2 Hok)).
      apply in_image_spec. exact Ib.
  - apply negb_true_iff.
    destruct (vertex_b pcs' s1 p && vertex_b pcs' s2 p) eqn:Ev; [| reflexivity].
    exfalso. apply andb_prop in Ev. destruct Ev as [V1 V2].
    apply vertex_spec in V1. apply vertex_spec in V2.
    destruct (progress_vertices_only_adds pcs i j e1 e2 P ti tj h s1 p
               Hi Hj Hw1 Hw2 Hok V1) as [O1|E1].
    + destruct (progress_vertices_only_adds pcs i j e1 e2 P ti tj h s2 p
                 Hi Hj Hw1 Hw2 Hok V2) as [O2|E2].
      * assert (Bold : vertex_b pcs s1 p && vertex_b pcs s2 p = true).
        { apply andb_true_intro. split; apply vertex_spec; assumption. }
        rewrite Bold in Hn. discriminate.
      * subst p. exact (Hneq eq_refl).
    + subst p. exact (Hneq eq_refl).
Qed.

Lemma circ_overlap_vertex : forall pcs c1 c2 p,
  In p (circ_overlap_pts pcs c1 c2) ->
  vmem pcs p.
Proof.
  intros pcs c1 c2 p Hin.
  unfold circ_overlap_pts in Hin. rewrite dedup_In in Hin.
  apply filter_In in Hin. destruct Hin as [_ Hb].
  unfold circ_end_in_other_b in Hb. apply orb_prop in Hb.
  destruct Hb as [Hb|Hb].
  - apply andb_prop in Hb. destruct Hb as [Bb _].
    unfold boundary_end_b in Bb. apply andb_prop in Bb. destruct Bb as [Vb _].
    apply vertex_spec in Vb. destruct Vb as [pc [Hpc [_ Hep]]].
    exists pc. split; [exact Hpc| exact Hep].
  - apply andb_prop in Hb. destruct Hb as [Bb _].
    unfold boundary_end_b in Bb. apply andb_prop in Bb. destruct Bb as [Vb _].
    apply vertex_spec in Vb. destruct Vb as [pc [Hpc [_ Hep]]].
    exists pc. split; [exact Hpc| exact Hep].
Qed.

Lemma pending_nonhit_step : forall pcs i j e1 e2 P ti tj h p,
  nth_error pcs i = Some e1 ->
  nth_error pcs j = Some e2 ->
  i <> j ->
  piece_wf e1 ->
  piece_wf e2 ->
  I_ok (ck_egg (bp_ck e1)) (ck_egg (bp_ck e2)) (IHit P ti tj) ->
  progress_hit pcs e1 e2 (IHit P ti tj) ->
  pending pcs p ->
  p <> P ->
  vmem pcs p \/ pending (progress_pieces pcs i j e1 e2 ti tj h) p.
Proof.
  intros pcs i j e1 e2 P ti tj h p Hi Hj Hij Hw1 Hw2 Hok Hpr [s1 [s2 [Hneq Hin]]] HneqP.
  set (pcs' := progress_pieces pcs i j e1 e2 ti tj h) in *.
  destruct (hit_param_in_unit e1 e2 P ti tj (proj1 Hw1) (proj1 Hw2) Hok) as [Hti Htj].
  unfold counted in Hin. destruct (canon2 s1 s2) as [u v] eqn:Ec.
  rewrite dedup_In in Hin. apply filter_In in Hin. destruct Hin as [Hraw Hk].
  destruct u as [cu|cu]; destruct v as [cv|cv].
  - assert (Er : raw_pts pcs' (SuppChord cu) (SuppChord cv) =
                 raw_pts pcs (SuppChord cu) (SuppChord cv)).
    { apply (raw_progress pcs i j e1 e2 ti tj h (SuppChord cu) (SuppChord cv)
        Hi Hj Hij (proj1 Hw1) (proj1 Hw2) Hti Htj). }
    right. exists s1, s2. split; [exact Hneq|].
    unfold counted. rewrite Ec. rewrite dedup_In. apply filter_In. split.
    + unfold counted_raw. rewrite Er. exact Hraw.
    + apply (keep_nonhit pcs i j e1 e2 P ti tj h (SuppChord cu) (SuppChord cv) p
        Hi Hj Hij Hw1 Hw2 Hok HneqP Hk).
  - assert (Er : raw_pts pcs' (SuppChord cu) (SuppCircle cv) =
                 raw_pts pcs (SuppChord cu) (SuppCircle cv)).
    { apply (raw_progress pcs i j e1 e2 ti tj h (SuppChord cu) (SuppCircle cv)
        Hi Hj Hij (proj1 Hw1) (proj1 Hw2) Hti Htj). }
    right. exists s1, s2. split; [exact Hneq|].
    unfold counted. rewrite Ec. rewrite dedup_In. apply filter_In. split.
    + unfold counted_raw. rewrite Er. exact Hraw.
    + apply (keep_nonhit pcs i j e1 e2 P ti tj h (SuppChord cu) (SuppCircle cv) p
        Hi Hj Hij Hw1 Hw2 Hok HneqP Hk).
  - assert (Er : raw_pts pcs' (SuppCircle cu) (SuppChord cv) =
                 raw_pts pcs (SuppCircle cu) (SuppChord cv)).
    { apply (raw_progress pcs i j e1 e2 ti tj h (SuppCircle cu) (SuppChord cv)
        Hi Hj Hij (proj1 Hw1) (proj1 Hw2) Hti Htj). }
    right. exists s1, s2. split; [exact Hneq|].
    unfold counted. rewrite Ec. rewrite dedup_In. apply filter_In. split.
    + unfold counted_raw. rewrite Er. exact Hraw.
    + apply (keep_nonhit pcs i j e1 e2 P ti tj h (SuppCircle cu) (SuppChord cv) p
        Hi Hj Hij Hw1 Hw2 Hok HneqP Hk).
  - destruct (same_circle_b cu cv) eqn:Es.
    + left. apply (circ_overlap_vertex pcs cu cv p).
      unfold counted_raw in Hraw. rewrite Es in Hraw. exact Hraw.
    + right. exists s1, s2. split; [exact Hneq|].
      unfold counted. rewrite Ec. rewrite dedup_In. apply filter_In. split.
      * unfold counted_raw. rewrite Es.
        unfold counted_raw in Hraw. rewrite Es in Hraw. exact Hraw.
      * apply (keep_nonhit pcs i j e1 e2 P ti tj h (SuppCircle cu) (SuppCircle cv) p
          Hi Hj Hij Hw1 Hw2 Hok HneqP Hk).
Qed.

Lemma target_step_invariant : forall pcs i j e1 e2 P ti tj h,
  nth_error pcs i = Some e1 ->
  nth_error pcs j = Some e2 ->
  i <> j ->
  piece_wf e1 ->
  piece_wf e2 ->
  bp_support e1 <> bp_support e2 ->
  admissible_hit pcs e1 e2 P ti tj ->
  forall p,
    target (progress_pieces pcs i j e1 e2 ti tj h) p <-> target pcs p.
Proof.
  intros pcs i j e1 e2 P ti tj h Hi Hj Hij Hw1 Hw2 Hdist Hadm p.
  assert (Hok : I_ok (ck_egg (bp_ck e1)) (ck_egg (bp_ck e2)) (IHit P ti tj)).
  { exact (proj1 Hadm). }
  assert (Hpr : progress_hit pcs e1 e2 (IHit P ti tj)).
  { apply admissible_progress. exact Hadm. }
  set (pcs' := progress_pieces pcs i j e1 e2 ti tj h) in *.
  split.
  - intros [Hv|Hp].
    + destruct Hv as [pc [Hin Hep]].
      assert (Hf : family_vertex pcs' (bp_support pc) p).
      { exists pc. split; [exact Hin|]. split; [reflexivity| exact Hep]. }
      destruct (progress_vertices_only_adds pcs i j e1 e2 P ti tj h _ p
                 Hi Hj Hw1 Hw2 Hok Hf) as [Hold|Heq].
      * left. destruct Hold as [pc0 [Hin0 [_ Hep0]]].
        exists pc0. split; assumption.
      * subst p. right. exists (bp_support e1), (bp_support e2). split; [exact Hdist|].
        apply (admissible_in_counted pcs e1 e2 P ti tj
          (nth_error_In _ _ Hi) (nth_error_In _ _ Hj) Hw1 Hw2 Hdist Hadm).
    + destruct Hp as [s1 [s2 [Hneq Hin]]].
      right. exists s1, s2. split; [exact Hneq|].
      apply (counted_shrink_incl pcs i j e1 e2 P ti tj h s1 s2 p); assumption.
  - intros [Hv|Hp].
    + left. apply (vset_step_grows pcs i j e1 e2 ti tj h p Hi Hj Hij Hv).
    + destruct (pt_eqb p P) eqn:Ep.
      * assert (E : p = P) by (apply (proj1 (pt_eqb_true p P)); exact Ep).
        subst p. left.
        destruct (hit_becomes_vertex pcs i j e1 e2 P ti tj h Hi Hj Hw1 Hw2 Hok) as [V1 _].
        destruct V1 as [pc [Hin [_ Hep]]]. exists pc. split; assumption.
      * assert (HneqP : p <> P).
        { intro E. apply (proj2 (pt_eqb_true p P)) in E. congruence. }
        destruct (pending_nonhit_step pcs i j e1 e2 P ti tj h p
                   Hi Hj Hij Hw1 Hw2 Hok Hpr Hp HneqP) as [Hold|Hstay].
        -- left. apply (vset_step_grows pcs i j e1 e2 ti tj h p Hi Hj Hij Hold).
        -- right. exact Hstay.
Qed.

Lemma has_adm_ordered : forall pcs,
  has_adm_hit pcs ->
  exists i j a b,
    (i < j)%nat /\
    nth_error pcs i = Some a /\
    nth_error pcs j = Some b /\
    pair_ok a b = true /\
    adm_list pcs a b <> nil.
Proof.
  intros pcs [i [j [a [b [p [ti [tj [Hi [Hj [Hij [Hw1 [Hw2 [Hdist Hadm]]]]]]]]]]]]].
  destruct (hit_in_windows a b p ti tj Hw1 Hw2 (proj1 Hadm)) as [Hwa Hwb].
  assert (Hnd : ~ I_ok (ck_egg (bp_ck a)) (ck_egg (bp_ck b)) IDecline).
  { exact (hit_not_decline _ _ p ti tj (proj1 Hadm)). }
  assert (Hin : In p (counted pcs (bp_support a) (bp_support b))).
  { apply (admissible_in_counted pcs a b p ti tj
      (nth_error_In _ _ Hi) (nth_error_In _ _ Hj) Hw1 Hw2 Hdist Hadm). }
  destruct (Nat.lt_trichotomy i j) as [Hlt|[Eij|Hgt]].
  - destruct (counted_adm_in pcs a b p Hw1 Hw2 Hwa Hwb Hin Hnd) as [ti' [tj' HinA]].
    exists i, j, a, b. split; [exact Hlt|].
    split; [exact Hi|]. split; [exact Hj|].
    split; [apply pair_ok_wf; assumption|].
    intro Hnil. rewrite Hnil in HinA. destruct HinA.
  - subst j. rewrite Hi in Hj. inversion Hj. subst b. exfalso. exact (Hdist eq_refl).
  - assert (Hnds : ~ I_ok (ck_egg (bp_ck b)) (ck_egg (bp_ck a)) IDecline).
    { intro Hd. apply Hnd. apply decline_swap. exact Hd. }
    destruct (counted_adm_in pcs b a p Hw2 Hw1 Hwb Hwa) as [ti' [tj' HinA]].
    + rewrite counted_sym. exact Hin.
    + exact Hnds.
    + exists j, i, b, a. split; [exact Hgt|].
      split; [exact Hj|]. split; [exact Hi|].
      split; [apply pair_ok_wf; try assumption; intro E; apply Hdist; symmetry; exact E|].
      intro Hnil. rewrite Hnil in HinA. destruct HinA.
Qed.

Lemma pick_bag_lawful : lawful pick_bag.
Proof.
  split.
  - intros [sh pcs|sh].
    + unfold pick_spec, pick_bag.
      destruct (pick pcs) as [[[i j] [[p ti] tj]]|] eqn:Ep; [simpl| exact I].
      apply (pick_bag_progress sh pcs (mkHitPick i j p ti tj)).
      unfold pick_bag. rewrite Ep. reflexivity.
    + unfold pick_spec, pick_bag. exact I.
  - intros sh pcs _ Hhit Ep.
    destruct (has_adm_ordered pcs Hhit) as [i [j [a [b [Hlt [Hi [Hj [Hok Hnil]]]]]]]].
    unfold pick_bag in Ep.
    destruct (pick pcs) as [[[i0 j0] [[p0 ti0] tj0]]|] eqn:Epk.
    + simpl in Ep. discriminate Ep.
    + apply Hnil.
      apply (pick_none_adm_nil pcs i j a b Epk Hlt Hi Hj Hok).
Qed.

Fixpoint scan_j_down (pcs : list BagPiece) (i j : nat) : option HitPick :=
  match j with
  | O => None
  | S j' =>
      if Nat.leb j' i then None
      else
        match nth_error pcs i, nth_error pcs j' with
        | Some a, Some b =>
            if pair_ok a b then
              match least_ti (adm_list pcs a b) with
              | Some c => Some (mkHitPick i j' (hc_p c) (hc_ti c) (hc_tj c))
              | None => scan_j_down pcs i j'
              end
            else scan_j_down pcs i j'
        | _, _ => scan_j_down pcs i j'
        end
  end.

Fixpoint scan_i_down (pcs : list BagPiece) (i : nat) : option HitPick :=
  match i with
  | O => None
  | S i' =>
      match scan_j_down pcs i' (length pcs) with
      | Some w => Some w
      | None => scan_i_down pcs i'
      end
  end.

Definition pick_rev (b : SheetBag) : option HitPick :=
  match b with
  | BagDeclined _ => None
  | BagLive _ pcs => scan_i_down pcs (length pcs)
  end.

Lemma scan_j_down_spec : forall pcs i j w,
  scan_j_down pcs i j = Some w ->
  exists e1 e2,
    nth_error pcs (hp_i w) = Some e1 /\
    nth_error pcs (hp_j w) = Some e2 /\
    hp_i w <> hp_j w /\
    piece_wf e1 /\ piece_wf e2 /\
    bp_support e1 <> bp_support e2 /\
    admissible_hit pcs e1 e2 (hp_P w) (hp_ti w) (hp_tj w).
Proof.
  intros pcs i j. induction j as [|j' IH]; intros w H; simpl in H; [discriminate|].
  destruct (Nat.leb j' i) eqn:Hle; [discriminate|].
  destruct (nth_error pcs i) as [a|] eqn:Hi; [| apply IH; exact H].
  destruct (nth_error pcs j') as [b|] eqn:Hj; [| apply IH; exact H].
  destruct (pair_ok a b) eqn:Eok; [| apply IH; exact H].
  destruct (least_ti (adm_list pcs a b)) as [c|] eqn:El; [| apply IH; exact H].
  inversion H; subst w. clear H. simpl.
  destruct (pair_ok_spec a b Eok) as [Ha [Hb Hd]].
  exists a, b. split; [exact Hi|]. split; [exact Hj|].
  split.
  - apply Nat.leb_nle in Hle. lia.
  - split; [exact Ha|]. split; [exact Hb|]. split; [exact Hd|].
    apply (adm_list_admissible pcs a b c). apply least_in. exact El.
Qed.

Lemma scan_i_down_spec : forall pcs i w,
  scan_i_down pcs i = Some w ->
  exists e1 e2,
    nth_error pcs (hp_i w) = Some e1 /\
    nth_error pcs (hp_j w) = Some e2 /\
    hp_i w <> hp_j w /\
    piece_wf e1 /\ piece_wf e2 /\
    bp_support e1 <> bp_support e2 /\
    admissible_hit pcs e1 e2 (hp_P w) (hp_ti w) (hp_tj w).
Proof.
  intros pcs i. induction i as [|i' IH]; intros w H; simpl in H; [discriminate|].
  destruct (scan_j_down pcs i' (length pcs)) as [w0|] eqn:Ej.
  - inversion H; subst w. apply (scan_j_down_spec pcs i' (length pcs) w0 Ej).
  - apply IH. exact H.
Qed.

Lemma scan_j_down_nil : forall pcs i j,
  scan_j_down pcs i j = None ->
  forall j' a b,
    (i < j')%nat ->
    (j' < j)%nat ->
    nth_error pcs i = Some a ->
    nth_error pcs j' = Some b ->
    pair_ok a b = true ->
    adm_list pcs a b = nil.
Proof.
  intros pcs i j. induction j as [|j0 IH]; intros Hnone j' a b Hlt Hhi Hi Hj Hok.
  - lia.
  - cbn -[pair_ok adm_list least_ti] in Hnone.
    destruct (Nat.leb j0 i) eqn:Hle.
    + apply Nat.leb_le in Hle. lia.
    + remember (nth_error pcs i) as ei eqn:Hei.
      remember (nth_error pcs j0) as ej eqn:Hej.
      destruct ei as [ai|]; destruct ej as [bj|].
      * assert (ai = a) as -> by congruence.
        destruct (pair_ok a bj) eqn:Eok.
        -- destruct (least_ti (adm_list pcs a bj)) as [c|] eqn:El.
           ++ discriminate Hnone.
           ++ destruct (Nat.eq_dec j' j0) as [->|Hneq].
              ** rewrite <- Hej in Hj.
                 assert (bj = b) as -> by congruence.
                 apply least_nil in El. exact El.
              ** apply (IH Hnone j' a b); try assumption. lia.
        -- destruct (Nat.eq_dec j' j0) as [->|Hneq].
           ++ rewrite <- Hej in Hj.
              assert (bj = b) as -> by congruence.
              congruence.
           ++ apply (IH Hnone j' a b); try assumption. lia.
      * destruct (Nat.eq_dec j' j0) as [->|Hneq].
        -- rewrite <- Hej in Hj. discriminate Hj.
        -- apply (IH Hnone j' a b); try assumption. lia.
      * discriminate Hi.
      * discriminate Hi.
Qed.

Lemma scan_i_down_nil : forall pcs i,
  scan_i_down pcs i = None ->
  forall i' j a b,
    (i' < i)%nat ->
    (i' < j)%nat ->
    nth_error pcs i' = Some a ->
    nth_error pcs j = Some b ->
    pair_ok a b = true ->
    adm_list pcs a b = nil.
Proof.
  intros pcs i. induction i as [|i0 IH]; intros Hnone i' j a b Hi Hij Hia Hjb Hok.
  - lia.
  - simpl in Hnone.
    destruct (scan_j_down pcs i0 (length pcs)) as [w|] eqn:Ej; [discriminate|].
    destruct (Nat.eq_dec i' i0) as [->|Hneq].
    + apply (scan_j_down_nil pcs i0 (length pcs) Ej j a b Hij).
      * apply nth_error_Some. rewrite Hjb. discriminate.
      * exact Hia.
      * exact Hjb.
      * exact Hok.
    + apply (IH Hnone i' j a b); try assumption. lia.
Qed.

Lemma pick_rev_lawful : lawful pick_rev.
Proof.
  split.
  - intros [sh pcs|sh].
    + unfold pick_spec, pick_rev.
      destruct (scan_i_down pcs (length pcs)) as [w|] eqn:Es; [| exact I].
      apply (scan_i_down_spec pcs (length pcs) w Es).
    + unfold pick_spec, pick_rev. exact I.
  - intros sh pcs _ Hhit Ep.
    destruct (has_adm_ordered pcs Hhit) as [i [j [a [b [Hlt [Hi [Hj [Hok Hnil]]]]]]]].
    unfold pick_rev in Ep.
    apply Hnil.
    apply (scan_i_down_nil pcs (length pcs) Ep i j a b).
    + apply nth_error_Some. rewrite Hi. discriminate.
    + exact Hlt.
    + exact Hi.
    + exact Hj.
    + exact Hok.
Qed.

Lemma bag_run_stopped_id : forall pick fuel b,
  run_stopped pick b ->
  bag_run pick fuel b = b.
Proof.
  intros pick fuel. induction fuel as [|fuel IH]; intros b Hs; simpl.
  - reflexivity.
  - destruct b as [sh pcs|sh].
    + unfold run_stopped in Hs. rewrite Hs. reflexivity.
    + reflexivity.
Qed.

Lemma bag_run_plus : forall pick n k b,
  bag_run pick (n + k)%nat b = bag_run pick k (bag_run pick n b).
Proof.
  intros pick n. induction n as [|n IH]; intros k b.
  - simpl. reflexivity.
  - replace (S n + k)%nat with (S (n + k))%nat by lia. simpl.
    destruct b as [sh pcs|sh].
    + destruct (pick (BagLive sh pcs)) as [w|] eqn:Ep.
      * apply IH.
      * rewrite (bag_run_stopped_id pick k (BagLive sh pcs)).
        -- reflexivity.
        -- unfold run_stopped. exact Ep.
    + symmetry.
      apply (bag_run_stopped_id pick k (BagDeclined sh)).
      exact I.
Qed.

Lemma run_after_step : forall pick sh pcs w,
  (forall b0, pick_spec pick b0) ->
  pick (BagLive sh pcs) = Some w ->
  (rho (step_hit (BagLive sh pcs) w) < rho (BagLive sh pcs))%nat ->
  bag_run pick (S (rho (BagLive sh pcs))) (BagLive sh pcs) =
  bag_run pick (S (rho (step_hit (BagLive sh pcs) w)))
            (step_hit (BagLive sh pcs) w).
Proof.
  intros pick sh pcs w Hspec Hep Hlt.
  set (b' := step_hit (BagLive sh pcs) w).
  set (r := rho (BagLive sh pcs)).
  set (r' := rho b').
  assert (Hle : (S r' <= r)%nat).
  { apply Nat.le_succ_l. exact Hlt. }
  assert (Hcut : r = (S r' + (r - S r'))%nat).
  { rewrite (Nat.add_comm (S r') (r - S r')).
    symmetry. apply (Nat.sub_add (S r') r Hle). }
  cbn -[step_hit rho]. rewrite Hep.
  replace
    (match b' with
     | BagLive _ _ =>
         match pick b' with
         | Some w0 => bag_run pick r' (step_hit b' w0)
         | None => b'
         end
     | BagDeclined _ => b'
     end)
    with (bag_run pick (S r') b') by reflexivity.
  replace (step_hit (BagLive sh pcs) w) with b' by reflexivity.
  rewrite Hcut. rewrite bag_run_plus.
  rewrite (bag_run_stopped_id pick (r - S r') (bag_run pick (S r') b')).
  - reflexivity.
  - unfold r'. apply bag_run_fixpoint. exact Hspec.
Qed.

Lemma run_vmem_target_le : forall n pick sh pcs,
  (rho_pcs pcs < n)%nat ->
  lawful pick ->
  bag_inv (BagLive sh pcs) ->
  scope_ready pcs ->
  forall p, vmem (run_pcs pick (BagLive sh pcs)) p <-> target pcs p.
Proof.
  induction n as [|n IH]; intros pick sh pcs Hlt Hlaw Hinv Hscope p.
  - lia.
  - destruct (pick (BagLive sh pcs)) as [w|] eqn:Ep.
    + pose proof (proj1 Hlaw (BagLive sh pcs)) as Hspec.
      unfold pick_spec in Hspec. rewrite Ep in Hspec.
      destruct w as [i j P ti tj].
      destruct Hspec as [e1 [e2 [Hi [Hj [Hij [Hw1 [Hw2 [Hdist Hadm]]]]]]]].
      set (h := mint_or_share pcs P).
      set (pcs' := progress_pieces pcs i j e1 e2 ti tj h).
      assert (Es : step_hit (BagLive sh pcs) (mkHitPick i j P ti tj) = BagLive sh pcs').
      { unfold step_hit. simpl in *.
        rewrite Hi, Hj. reflexivity. }
      assert (Hdrop : (rho_pcs pcs' < rho_pcs pcs)%nat).
      { pose proof (rho_step_strict sh pcs i j e1 e2 P ti tj Hi Hj Hij Hw1 Hw2 Hdist Hadm)
          as Hd.
        rewrite Es in Hd. cbn [rho] in Hd. exact Hd. }
      assert (Hlt' : (rho_pcs pcs' < n)%nat).
      { apply Nat.lt_le_trans with (rho_pcs pcs); [exact Hdrop|].
        apply Nat.lt_succ_r. exact Hlt. }
      assert (Hinv' : bag_inv (BagLive sh pcs')).
      { pose proof (admissible_step_preserves_inv sh pcs i j e1 e2 P ti tj
          Hinv Hi Hj Hij Hw1 Hw2 Hadm) as Hi2.
        rewrite Es in Hi2. exact Hi2. }
      assert (Hscope' : scope_ready pcs').
      { apply (progress_scope_ready pcs i j e1 e2 P ti tj h Hi Hj Hw1 Hw2
          (proj1 Hadm) Hscope). }
      assert (Heq : bag_run pick (S (rho (BagLive sh pcs))) (BagLive sh pcs) =
                    bag_run pick (S (rho (BagLive sh pcs'))) (BagLive sh pcs')).
      { rewrite <- Es.
        apply (run_after_step pick sh pcs (mkHitPick i j P ti tj) (proj1 Hlaw) Ep).
        rewrite Es. exact Hdrop. }
      unfold run_pcs. rewrite Heq.
      fold (run_pcs pick (BagLive sh pcs')).
      rewrite (IH pick sh pcs' Hlt' Hlaw Hinv' Hscope' p).
      apply (target_step_invariant pcs i j e1 e2 P ti tj h
        Hi Hj Hij Hw1 Hw2 Hdist Hadm).
    + unfold run_pcs. simpl. rewrite Ep.
      split.
      * intro Hv. left. exact Hv.
      * intros [Hv|Hp]; [exact Hv|].
        destruct (vmem_b pcs p) eqn:Ev.
        -- apply vmem_spec. exact Ev.
        -- exfalso.
           assert (Hnv : ~ vmem pcs p).
           { intro Hv2. apply vmem_spec in Hv2. congruence. }
           assert (Hhit : has_adm_hit pcs).
           { apply (pending_not_vmem_hit pcs p); [exact Hinv| exact Hscope| exact Hp| exact Hnv]. }
           apply (proj2 Hlaw sh pcs Hinv Hhit). exact Ep.
Qed.

Lemma run_vmem_target : forall pick sh pcs,
  lawful pick ->
  bag_inv (BagLive sh pcs) ->
  scope_ready pcs ->
  forall p, vmem (run_pcs pick (BagLive sh pcs)) p <-> target pcs p.
Proof.
  intros pick sh pcs Hlaw Hinv Hscope p.
  apply (run_vmem_target_le (S (rho_pcs pcs)) pick sh pcs).
  - apply Nat.lt_succ_diag_r.
  - exact Hlaw.
  - exact Hinv.
  - exact Hscope.
Qed.

Theorem run_vset_determined : forall pick1 pick2 sh pcs,
  lawful pick1 ->
  lawful pick2 ->
  bag_inv (BagLive sh pcs) ->
  no_decline_pair pcs ->
  vset_eq (run_pcs pick1 (BagLive sh pcs))
          (run_pcs pick2 (BagLive sh pcs)).
Proof.
  intros pick1 pick2 sh pcs H1 H2 Hinv Hnd p.
  assert (Hscope : scope_ready pcs).
  { apply no_decline_scope; [exact Hinv| exact Hnd]. }
  rewrite (run_vmem_target pick1 sh pcs H1 Hinv Hscope p).
  rewrite (run_vmem_target pick2 sh pcs H2 Hinv Hscope p).
  reflexivity.
Qed.

Lemma cook_loop_rho_holds : CookLoopRho.
Proof.
  unfold CookLoopRho, rho_loop_discharged. split.
  - exact bag_run_arm_noded.
  - exact run_vset_determined.
Qed.


Print Assumptions vset_step_grows.
Print Assumptions vmem_spec.
Print Assumptions hit_not_decline.
Print Assumptions decline_swap.
Print Assumptions hit_in_windows.
Print Assumptions chord_window_const.
Print Assumptions chord_point_nondeg.
Print Assumptions no_decline_scope.
Print Assumptions split_parent_chord.
Print Assumptions split_circ_child_open.
Print Assumptions progress_scope_ready.
Print Assumptions wf_egg_class.
Print Assumptions pair_share_nondecline.
Print Assumptions pending_not_vmem_hit.
Print Assumptions keep_nonhit.
Print Assumptions circ_overlap_vertex.
Print Assumptions pending_nonhit_step.
Print Assumptions target_step_invariant.
Print Assumptions has_adm_ordered.
Print Assumptions pick_bag_lawful.
Print Assumptions scan_j_down_spec.
Print Assumptions scan_i_down_spec.
Print Assumptions scan_j_down_nil.
Print Assumptions scan_i_down_nil.
Print Assumptions pick_rev_lawful.
Print Assumptions bag_run_stopped_id.
Print Assumptions bag_run_plus.
Print Assumptions run_after_step.
Print Assumptions run_vmem_target_le.
Print Assumptions run_vmem_target.
Print Assumptions run_vset_determined.
Print Assumptions cook_loop_rho_holds.
