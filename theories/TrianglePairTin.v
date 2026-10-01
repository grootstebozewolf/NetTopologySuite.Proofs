(* NetTopologySuite.Proofs.TrianglePairTin
   A TIN is valid iff every distinct pair has disjoint open interiors,
   and every shared boundary is either empty or exactly one edge whose
   endpoints are vertices of both triangles. tri_de9im decides the
   dimensions: II = F, and BB = F or BB = 1 on that edge.
   Fixtures: a two-triangle strip, an overlap (II = 2), a T-junction
   (BB = 0).
   topic: relate
   claimId: tri-de9im-t3
   witness: tin_valid_iff
   3-axiom host. No Admitted. No Jordan.
   AI-drafted (Cursor Grok 4.7).
   License: BSD-3-Clause *)
From Stdlib Require Import Reals Lra List Bool.
Import ListNotations.
From NTS.Proofs Require Import Distance Orientation Convex ConvexClip
  DE9IM TrianglePairCommon TrianglePairClip TrianglePairEdge
  TrianglePairBound TrianglePairExterior.
Local Open Scope R_scope.

Definition edge_id (P Q R S : Point) : Prop :=
  (P = R /\ Q = S) \/ (P = S /\ Q = R).

Definition vert_edge (A B C P Q : Point) : Prop :=
  edge_id P Q A B \/ edge_id P Q B C \/ edge_id P Q C A.

Definition pair_sem (A B C D E F : Point) : Prop :=
  (~ exists X, tri_open A B C X /\ tri_open D E F X) /\
  ((~ exists X, on_bd A B C X /\ on_bd D E F X) \/
   (exists P Q, P <> Q /\ vert_edge A B C P Q /\ vert_edge D E F P Q /\
      (forall X, on_bd A B C X /\ on_bd D E F X <-> on_seg P Q X))).

Definition pair_im (A B C D E F : Point) : Prop :=
  im_ii (tri_de9im A B C D E F) = DimF /\
  (im_bb (tri_de9im A B C D E F) = DimF \/
   (im_bb (tri_de9im A B C D E F) = Dim1 /\
    exists P Q, P <> Q /\ vert_edge A B C P Q /\ vert_edge D E F P Q /\
      (forall X, on_bd A B C X /\ on_bd D E F X <-> on_seg P Q X))).

Lemma ii_dimF_iff : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  ii_entry A B C D E F = DimF <->
  ~ exists X, tri_open A B C X /\ tri_open D E F X.
Proof.
  intros A B C D E F HA HB. unfold ii_entry. split.
  - intros Hent [X HX].
    destruct (Rlt_dec 0 (poly_area2 (tri_inter A B C D E F))) as [Hp|Hn].
    + discriminate.
    + apply Hn. apply (proj1 (ii_nonempty_iff A B C D E F HA HB)).
      exists X. exact HX.
  - intros Hempty.
    destruct (Rlt_dec 0 (poly_area2 (tri_inter A B C D E F))) as [Hp|Hn].
    + exfalso. apply Hempty.
      apply (proj2 (ii_nonempty_iff A B C D E F HA HB)). exact Hp.
    + reflexivity.
Qed.

Lemma vert_on_edge : forall A B C P Q,
  vert_edge A B C P Q ->
  exists e, In e (e3 A B C) /\
    forall X, on_seg P Q X -> on_seg (fst e) (snd e) X.
Proof.
  intros A B C P Q H.
  destruct H as [H|[H|H]]; destruct H as [[-> ->]|[-> ->]].
  - exists (A, B). split; [unfold e3; simpl; auto|]. intros X HX. exact HX.
  - exists (A, B). split; [unfold e3; simpl; auto|].
    intros X HX. apply on_seg_sym. exact HX.
  - exists (B, C). split; [unfold e3; simpl; auto|]. intros X HX. exact HX.
  - exists (B, C). split; [unfold e3; simpl; auto|].
    intros X HX. apply on_seg_sym. exact HX.
  - exists (C, A). split; [unfold e3; simpl; auto|]. intros X HX. exact HX.
  - exists (C, A). split; [unfold e3; simpl; auto|].
    intros X HX. apply on_seg_sym. exact HX.
Qed.

Lemma edge_gives_dim1 : forall A B C D E F P Q,
  0 < cross A B C -> 0 < cross D E F ->
  P <> Q -> vert_edge A B C P Q -> vert_edge D E F P Q ->
  bb_entry A B C D E F = Dim1.
Proof.
  intros A B C D E F P Q HA HB Hne He Hf.
  apply (proj2 (bb_dim1_iff A B C D E F HA HB)).
  destruct (vert_on_edge A B C P Q He) as [e [Hei Hall]].
  destruct (vert_on_edge D E F P Q Hf) as [f [Hfi Hallf]].
  exists P, Q. repeat split; try assumption.
  - exists e. split; assumption.
  - exists f. split; assumption.
Qed.

Lemma im_ii_eq : forall A B C D E F,
  im_ii (tri_de9im A B C D E F) = ii_entry A B C D E F.
Proof. intros. exact (proj1 (tri_de9im_entries A B C D E F)). Qed.

Lemma im_bb_eq : forall A B C D E F,
  im_bb (tri_de9im A B C D E F) = bb_entry A B C D E F.
Proof.
  intros A B C D E F.
  destruct (tri_de9im_entries A B C D E F) as [_ [_ [_ [_ [H _]]]]]. exact H.
Qed.

Theorem pair_tin_valid_iff : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  pair_sem A B C D E F <-> pair_im A B C D E F.
Proof.
  intros A B C D E F HA HB. split.
  - intros [Hopen [Hempty|Hedge]].
    + split.
      * rewrite im_ii_eq. apply ii_dimF_iff; assumption.
      * left. rewrite im_bb_eq. apply bb_dimF_iff; assumption.
    + destruct Hedge as [P [Q [Hne [He [Hf Hex]]]]].
      split.
      * rewrite im_ii_eq. apply ii_dimF_iff; assumption.
      * right. split.
        -- rewrite im_bb_eq. apply (edge_gives_dim1 A B C D E F P Q); assumption.
        -- exists P, Q. split; [exact Hne|]. split; [exact He|].
           split; [exact Hf|]. exact Hex.
  - intros [Hii [Hbb|Hedge]].
    + split.
      * apply ii_dimF_iff; try assumption.
      * left. apply bb_dimF_iff; try assumption.
    + destruct Hedge as [Hbb [P [Q [Hne [He [Hf Hex]]]]]].
      split.
      * apply ii_dimF_iff; try assumption.
      * right. exists P, Q. split; [exact Hne|]. split; [exact He|].
        split; [exact Hf|]. exact Hex.
Qed.

Definition Tri := (Point * Point * Point)%type.

Definition tri_pos (T : Tri) : Prop :=
  match T with ((A, B), C) => 0 < cross A B C end.

Definition tri_pair_sem (T U : Tri) : Prop :=
  match T, U with
  | ((A, B), C), ((D, E), F) => pair_sem A B C D E F
  end.

Definition tri_pair_im (T U : Tri) : Prop :=
  match T, U with
  | ((A, B), C), ((D, E), F) => pair_im A B C D E F
  end.

Fixpoint tin_sem (ts : list Tri) : Prop :=
  match ts with
  | [] => True
  | T :: rest => (forall U, In U rest -> tri_pair_sem T U) /\ tin_sem rest
  end.

Fixpoint tin_im (ts : list Tri) : Prop :=
  match ts with
  | [] => True
  | T :: rest => (forall U, In U rest -> tri_pair_im T U) /\ tin_im rest
  end.

Theorem tin_valid_iff : forall ts,
  (forall T, In T ts -> tri_pos T) ->
  tin_sem ts <-> tin_im ts.
Proof.
  intros ts Hccw. induction ts as [|T rest IH].
  - simpl. split; intros; exact I.
  - assert (Hrest : forall U, In U rest -> tri_pos U).
    { intros U HU. apply Hccw. simpl. right. exact HU. }
    assert (HT : tri_pos T).
    { apply Hccw. simpl. left. reflexivity. }
    simpl. split.
    + intros [Hall Htail]. split.
      * intros U HU.
        assert (HU' := Hall U HU).
        destruct T as [[A B] C], U as [[D E] F].
        simpl in HT, HU'. apply pair_tin_valid_iff.
        -- exact HT.
        -- apply Hrest in HU. simpl in HU. exact HU.
        -- exact HU'.
      * apply IH. exact Hrest. exact Htail.
    + intros [Hall Htail]. split.
      * intros U HU.
        assert (HU' := Hall U HU).
        destruct T as [[A B] C], U as [[D E] F].
        simpl in HT, HU'. apply pair_tin_valid_iff.
        -- exact HT.
        -- apply Hrest in HU. simpl in HU. exact HU.
        -- exact HU'.
      * apply IH. exact Hrest. exact Htail.
Qed.

(* Two-triangle strip. Shared edge (1,0)--(0,1), interiors on opposite sides. *)
Lemma strip_ccw :
  0 < cross (mkPoint 1 0) (mkPoint 0 1) (mkPoint 0 0) /\
  0 < cross (mkPoint 0 1) (mkPoint 1 0) (mkPoint 1 1).
Proof. split; unfold cross; simpl; lra. Qed.

Lemma strip_apart :
  ~ exists X, tri_open (mkPoint 1 0) (mkPoint 0 1) (mkPoint 0 0) X /\
              tri_open (mkPoint 0 1) (mkPoint 1 0) (mkPoint 1 1) X.
Proof.
  destruct strip_ccw as [HA HB].
  apply ii_dimF_iff; try assumption.
  apply ii_entry_dimF_outer; try assumption.
  left. unfold outer3, cross; simpl. repeat split; lra.
Qed.

Lemma strip_bd : forall X,
  on_bd (mkPoint 1 0) (mkPoint 0 1) (mkPoint 0 0) X /\
  on_bd (mkPoint 0 1) (mkPoint 1 0) (mkPoint 1 1) X <->
  on_seg (mkPoint 1 0) (mkPoint 0 1) X.
Proof.
  intros X. split.
  - intros [HA HD].
    destruct HA as [Hab|[Hbc|Hca]].
    + exact Hab.
    + destruct HD as [Hde|[Hef|Hfd]].
      * destruct Hbc as [t [Ht ->]]. destruct Hde as [s [Hs Heq]].
        unfold convex_combination in Heq. simpl in Heq.
        injection Heq as Hx Hy. simpl in Hx, Hy.
        assert (t = 0) by lra. subst t.
        replace (convex_combination (mkPoint 0 1) (mkPoint 0 0) 0)
          with (mkPoint 0 1)
          by (unfold convex_combination; simpl; f_equal; lra).
        exact (proj2 (seg_ends (mkPoint 1 0) (mkPoint 0 1))).
      * destruct Hbc as [t [Ht ->]]. destruct Hef as [s [Hs Heq]].
        unfold convex_combination in Heq. simpl in Heq.
        apply (f_equal px) in Heq. simpl in Heq. lra.
      * destruct Hbc as [t [Ht ->]]. destruct Hfd as [s [Hs Heq]].
        unfold convex_combination in Heq. simpl in Heq.
        injection Heq as Hx Hy. simpl in Hx, Hy.
        assert (t = 0) by lra. subst t.
        replace (convex_combination (mkPoint 0 1) (mkPoint 0 0) 0)
          with (mkPoint 0 1)
          by (unfold convex_combination; simpl; f_equal; lra).
        exact (proj2 (seg_ends (mkPoint 1 0) (mkPoint 0 1))).
    + destruct HD as [Hde|[Hef|Hfd]].
      * destruct Hca as [t [Ht ->]]. destruct Hde as [s [Hs Heq]].
        unfold convex_combination in Heq. simpl in Heq.
        injection Heq as Hx Hy. simpl in Hx, Hy.
        assert (t = 1) by lra. subst t.
        replace (convex_combination (mkPoint 0 0) (mkPoint 1 0) 1)
          with (mkPoint 1 0)
          by (unfold convex_combination; simpl; f_equal; lra).
        exact (proj1 (seg_ends (mkPoint 1 0) (mkPoint 0 1))).
      * destruct Hca as [t [Ht ->]]. destruct Hef as [s [Hs Heq]].
        unfold convex_combination in Heq. simpl in Heq.
        injection Heq as Hx Hy. simpl in Hx, Hy.
        assert (t = 1) by lra. subst t.
        replace (convex_combination (mkPoint 0 0) (mkPoint 1 0) 1)
          with (mkPoint 1 0)
          by (unfold convex_combination; simpl; f_equal; lra).
        exact (proj1 (seg_ends (mkPoint 1 0) (mkPoint 0 1))).
      * destruct Hca as [t [Ht ->]]. destruct Hfd as [s [Hs Heq]].
        unfold convex_combination in Heq. simpl in Heq.
        apply (f_equal py) in Heq. simpl in Heq. lra.
  - intros HX. split.
    + left. exact HX.
    + left. apply on_seg_sym. exact HX.
Qed.

Theorem tin_strip :
  pair_sem (mkPoint 1 0) (mkPoint 0 1) (mkPoint 0 0)
           (mkPoint 0 1) (mkPoint 1 0) (mkPoint 1 1) /\
  im_ii (tri_de9im (mkPoint 1 0) (mkPoint 0 1) (mkPoint 0 0)
                   (mkPoint 0 1) (mkPoint 1 0) (mkPoint 1 1)) = DimF /\
  im_bb (tri_de9im (mkPoint 1 0) (mkPoint 0 1) (mkPoint 0 0)
                   (mkPoint 0 1) (mkPoint 1 0) (mkPoint 1 1)) = Dim1.
Proof.
  destruct strip_ccw as [HA HB].
  assert (Hsem : pair_sem (mkPoint 1 0) (mkPoint 0 1) (mkPoint 0 0)
                           (mkPoint 0 1) (mkPoint 1 0) (mkPoint 1 1)).
  { split; [apply strip_apart|]. right.
    exists (mkPoint 1 0), (mkPoint 0 1). split.
    - apply pts_neq. left. lra.
    - split; [left; left; split; reflexivity|].
      split; [left; right; split; reflexivity|]. exact strip_bd. }
  split; [exact Hsem|].
  destruct (proj1 (pair_tin_valid_iff _ _ _ _ _ _ HA HB) Hsem) as [Hii [Hbad|Hok]].
  - exfalso.
    assert (Hpt : on_bd (mkPoint 1 0) (mkPoint 0 1) (mkPoint 0 0) (mkPoint 1 0) /\
                  on_bd (mkPoint 0 1) (mkPoint 1 0) (mkPoint 1 1) (mkPoint 1 0)).
    { apply strip_bd. exact (proj1 (seg_ends (mkPoint 1 0) (mkPoint 0 1))). }
    apply bb_dimF_iff in Hbad; try assumption.
    apply Hbad. exists (mkPoint 1 0). exact Hpt.
  - destruct Hok as [Hbb _]. split; assumption.
Qed.

Theorem tin_overlap :
  im_ii (tri_de9im (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
                   (mkPoint (1/4) (1/4)) (mkPoint (5/4) (1/4))
                   (mkPoint (1/4) (5/4))) = Dim2 /\
  ~ pair_sem (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
             (mkPoint (1/4) (1/4)) (mkPoint (5/4) (1/4)) (mkPoint (1/4) (5/4)).
Proof.
  assert (HA : 0 < cross (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1))
    by (unfold cross; simpl; lra).
  assert (HB : 0 < cross (mkPoint (1/4) (1/4)) (mkPoint (5/4) (1/4))
                         (mkPoint (1/4) (5/4)))
    by (unfold cross; simpl; lra).
  destruct ii_entry_fixtures as [Hov _].
  unfold fxA0, fxA1, fxA2 in Hov.
  rewrite im_ii_eq. split; [exact Hov|].
  intros Hsem. apply pair_tin_valid_iff in Hsem; try assumption.
  destruct Hsem as [Hii _]. rewrite im_ii_eq in Hii. rewrite Hov in Hii.
  discriminate.
Qed.

Lemma overlap_pos_cross_E : forall A B D E,
  cross A B E <> 0 -> overlap_pos_b A B D E = false.
Proof.
  intros A B D E HE. unfold overlap_pos_b.
  destruct (point_eqb A B); [reflexivity|].
  destruct (point_eqb D E); [reflexivity|].
  destruct (Req_dec_T (cross A B D) 0); [|reflexivity].
  destruct (Req_dec_T (cross A B E) 0); [contradiction|reflexivity].
Qed.

Lemma tj_no_overlap :
  bb_overlap (mkPoint 0 0) (mkPoint 2 0) (mkPoint 1 2)
             (mkPoint 1 0) (mkPoint 0 (-1)) (mkPoint 2 (-1)) = false.
Proof.
  unfold bb_overlap, e3. simpl.
  (* Nine edge pairs. Each fails overlap_pos_cross or overlap_pos_cross_E. *)
  assert (HabE : cross (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 (-1)) <> 0)
    by (unfold cross; simpl; lra).
  assert (HabF : cross (mkPoint 0 0) (mkPoint 2 0) (mkPoint 2 (-1)) <> 0)
    by (unfold cross; simpl; lra).
  rewrite (overlap_pos_cross_E (mkPoint 0 0) (mkPoint 2 0)
             (mkPoint 1 0) (mkPoint 0 (-1)) HabE).
  rewrite (overlap_pos_cross (mkPoint 0 0) (mkPoint 2 0)
             (mkPoint 0 (-1)) (mkPoint 2 (-1)) HabE).
  rewrite (overlap_pos_cross (mkPoint 0 0) (mkPoint 2 0)
             (mkPoint 2 (-1)) (mkPoint 1 0) HabF).
  assert (HbcD : cross (mkPoint 2 0) (mkPoint 1 2) (mkPoint 1 0) <> 0)
    by (unfold cross; simpl; lra).
  assert (HbcE : cross (mkPoint 2 0) (mkPoint 1 2) (mkPoint 0 (-1)) <> 0)
    by (unfold cross; simpl; lra).
  assert (HbcF : cross (mkPoint 2 0) (mkPoint 1 2) (mkPoint 2 (-1)) <> 0)
    by (unfold cross; simpl; lra).
  rewrite (overlap_pos_cross (mkPoint 2 0) (mkPoint 1 2)
             (mkPoint 1 0) (mkPoint 0 (-1)) HbcD).
  rewrite (overlap_pos_cross (mkPoint 2 0) (mkPoint 1 2)
             (mkPoint 0 (-1)) (mkPoint 2 (-1)) HbcE).
  rewrite (overlap_pos_cross (mkPoint 2 0) (mkPoint 1 2)
             (mkPoint 2 (-1)) (mkPoint 1 0) HbcF).
  assert (HcaD : cross (mkPoint 1 2) (mkPoint 0 0) (mkPoint 1 0) <> 0)
    by (unfold cross; simpl; lra).
  assert (HcaE : cross (mkPoint 1 2) (mkPoint 0 0) (mkPoint 0 (-1)) <> 0)
    by (unfold cross; simpl; lra).
  assert (HcaF : cross (mkPoint 1 2) (mkPoint 0 0) (mkPoint 2 (-1)) <> 0)
    by (unfold cross; simpl; lra).
  rewrite (overlap_pos_cross (mkPoint 1 2) (mkPoint 0 0)
             (mkPoint 1 0) (mkPoint 0 (-1)) HcaD).
  rewrite (overlap_pos_cross (mkPoint 1 2) (mkPoint 0 0)
             (mkPoint 0 (-1)) (mkPoint 2 (-1)) HcaE).
  rewrite (overlap_pos_cross (mkPoint 1 2) (mkPoint 0 0)
             (mkPoint 2 (-1)) (mkPoint 1 0) HcaF).
  reflexivity.
Qed.

Lemma tj_touch :
  bb_touch (mkPoint 0 0) (mkPoint 2 0) (mkPoint 1 2)
           (mkPoint 1 0) (mkPoint 0 (-1)) (mkPoint 2 (-1)) = true.
Proof.
  apply bb_touch_spec.
  exists ((mkPoint 0 0), (mkPoint 2 0)),
         ((mkPoint 1 0), (mkPoint 0 (-1))).
  repeat split.
  - unfold e3. simpl. auto.
  - unfold e3. simpl. auto.
  - simpl. apply orb_true_iff. right.
    apply orb_true_iff. left. apply orb_true_iff. left. apply orb_true_iff. left.
    apply on_seg_b_iff. exists (1/2). split; [lra|].
    unfold convex_combination. simpl. f_equal; lra.
Qed.

Theorem tin_tjunction :
  im_bb (tri_de9im (mkPoint 0 0) (mkPoint 2 0) (mkPoint 1 2)
                   (mkPoint 1 0) (mkPoint 0 (-1)) (mkPoint 2 (-1))) = Dim0 /\
  ~ pair_sem (mkPoint 0 0) (mkPoint 2 0) (mkPoint 1 2)
             (mkPoint 1 0) (mkPoint 0 (-1)) (mkPoint 2 (-1)).
Proof.
  assert (HA : 0 < cross (mkPoint 0 0) (mkPoint 2 0) (mkPoint 1 2))
    by (unfold cross; simpl; lra).
  assert (HB : 0 < cross (mkPoint 1 0) (mkPoint 0 (-1)) (mkPoint 2 (-1)))
    by (unfold cross; simpl; lra).
  assert (Hbb : bb_entry (mkPoint 0 0) (mkPoint 2 0) (mkPoint 1 2)
                         (mkPoint 1 0) (mkPoint 0 (-1)) (mkPoint 2 (-1)) = Dim0).
  { apply bb_dim0_flags. apply tj_no_overlap. apply tj_touch. }
  rewrite im_bb_eq. split; [exact Hbb|].
  intros Hsem. apply pair_tin_valid_iff in Hsem; try assumption.
  destruct Hsem as [_ [Hbad|Hok]].
  - rewrite im_bb_eq in Hbad. rewrite Hbb in Hbad. discriminate.
  - destruct Hok as [Hdim _]. rewrite im_bb_eq in Hdim. rewrite Hbb in Hdim.
    discriminate.
Qed.

Print Assumptions ii_dimF_iff.
Print Assumptions vert_on_edge.
Print Assumptions edge_gives_dim1.
Print Assumptions im_ii_eq.
Print Assumptions im_bb_eq.
Print Assumptions pair_tin_valid_iff.
Print Assumptions tin_valid_iff.
Print Assumptions strip_ccw.
Print Assumptions strip_apart.
Print Assumptions strip_bd.
Print Assumptions tin_strip.
Print Assumptions tin_overlap.
Print Assumptions overlap_pos_cross_E.
Print Assumptions tj_no_overlap.
Print Assumptions tj_touch.
Print Assumptions tin_tjunction.
