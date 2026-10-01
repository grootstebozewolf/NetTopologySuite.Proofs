(* NetTopologySuite.Proofs.TrianglePairTin
   A TIN is valid iff every distinct pair has disjoint open interiors,
   and the shared boundary is empty, exactly one edge whose endpoints
   are vertices of both triangles, or exactly one point V that is a
   vertex of both. tri_de9im decides the dimensions: II = F, and
   BB = F, or BB = 1 on that edge, or BB = 0 at that vertex.
   Fixtures: a two-triangle strip, an overlap (II = 2), a T-junction
   (BB = 0 at a point that is a vertex of only one triangle), a
   four-triangle centre fan.
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

Definition pair_edge (A B C D E F : Point) : Prop :=
  exists P Q, P <> Q /\ vert_edge A B C P Q /\ vert_edge D E F P Q /\
    (forall X, on_bd A B C X /\ on_bd D E F X <-> on_seg P Q X).

(* Boundaries meet at exactly one point, and that point is a vertex of both. *)
Definition pair_vtx (A B C D E F : Point) : Prop :=
  exists V,
    (V = A \/ V = B \/ V = C) /\
    (V = D \/ V = E \/ V = F) /\
    on_bd A B C V /\ on_bd D E F V /\
    (forall X, on_bd A B C X /\ on_bd D E F X -> X = V).

Definition pair_sem (A B C D E F : Point) : Prop :=
  (~ exists X, tri_open A B C X /\ tri_open D E F X) /\
  ((~ exists X, on_bd A B C X /\ on_bd D E F X) \/
   pair_edge A B C D E F \/
   pair_vtx A B C D E F).

Definition pair_im (A B C D E F : Point) : Prop :=
  im_ii (tri_de9im A B C D E F) = DimF /\
  (im_bb (tri_de9im A B C D E F) = DimF \/
   (im_bb (tri_de9im A B C D E F) = Dim1 /\ pair_edge A B C D E F) \/
   (im_bb (tri_de9im A B C D E F) = Dim0 /\ pair_vtx A B C D E F)).

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

Lemma vtx_gives_dim0 : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  pair_vtx A B C D E F ->
  bb_entry A B C D E F = Dim0.
Proof.
  intros A B C D E F HA HB [V [_ [_ [Ha [Hb Honly]]]]].
  apply (proj2 (bb_dim0_iff A B C D E F HA HB)). split.
  - exists V. split; assumption.
  - intros [P [Q [Hne [He Hf]]]].
    destruct He as [e [Hine Hall]]. destruct Hf as [f [Hinf Hallf]].
    assert (Hp : on_seg P Q P) by apply (proj1 (seg_ends P Q)).
    assert (Hq : on_seg P Q Q) by apply (proj2 (seg_ends P Q)).
    assert (EP : P = V).
    { apply Honly. split.
      - apply (seg_e3_bd A B C e P Hine). apply Hall. exact Hp.
      - apply (seg_e3_bd D E F f P Hinf). apply Hallf. exact Hp. }
    assert (EQ : Q = V).
    { apply Honly. split.
      - apply (seg_e3_bd A B C e Q Hine). apply Hall. exact Hq.
      - apply (seg_e3_bd D E F f Q Hinf). apply Hallf. exact Hq. }
    apply Hne. rewrite EP, EQ. reflexivity.
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
  - intros [Hopen [Hempty|[Hedge|Hvtx]]].
    + split.
      * rewrite im_ii_eq. apply ii_dimF_iff; assumption.
      * left. rewrite im_bb_eq. apply bb_dimF_iff; assumption.
    + destruct Hedge as [P [Q [Hne [He [Hf Hex]]]]].
      split.
      * rewrite im_ii_eq. apply ii_dimF_iff; assumption.
      * right. left. split.
        -- rewrite im_bb_eq. apply (edge_gives_dim1 A B C D E F P Q); assumption.
        -- exists P, Q. split; [exact Hne|]. split; [exact He|].
           split; [exact Hf|]. exact Hex.
    + split.
      * rewrite im_ii_eq. apply ii_dimF_iff; assumption.
      * right. right. split.
        -- rewrite im_bb_eq. apply vtx_gives_dim0; assumption.
        -- exact Hvtx.
  - intros [Hii [Hbb|[Hedge|Hvtx]]].
    + split.
      * apply ii_dimF_iff; try assumption.
      * left. apply bb_dimF_iff; try assumption.
    + destruct Hedge as [_ Hedge].
      split.
      * apply ii_dimF_iff; try assumption.
      * right. left. exact Hedge.
    + destruct Hvtx as [_ Hvtx].
      split.
      * apply ii_dimF_iff; try assumption.
      * right. right. exact Hvtx.
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
  { split; [apply strip_apart|]. right. left.
    exists (mkPoint 1 0), (mkPoint 0 1). split.
    - apply pts_neq. left. lra.
    - split; [left; left; split; reflexivity|].
      split; [left; right; split; reflexivity|]. exact strip_bd. }
  split; [exact Hsem|].
  destruct (proj1 (pair_tin_valid_iff _ _ _ _ _ _ HA HB) Hsem)
    as [Hii [Hbad|[Hok|Hvtx]]].
  - exfalso.
    assert (Hpt : on_bd (mkPoint 1 0) (mkPoint 0 1) (mkPoint 0 0) (mkPoint 1 0) /\
                  on_bd (mkPoint 0 1) (mkPoint 1 0) (mkPoint 1 1) (mkPoint 1 0)).
    { apply strip_bd. exact (proj1 (seg_ends (mkPoint 1 0) (mkPoint 0 1))). }
    apply bb_dimF_iff in Hbad; try assumption.
    apply Hbad. exists (mkPoint 1 0). exact Hpt.
  - destruct Hok as [Hbb _]. split; assumption.
  - exfalso. destruct Hvtx as [Hdim _]. rewrite im_bb_eq in Hdim.
    assert (H1 : bb_entry (mkPoint 1 0) (mkPoint 0 1) (mkPoint 0 0)
                          (mkPoint 0 1) (mkPoint 1 0) (mkPoint 1 1) = Dim1).
    { apply (edge_gives_dim1 _ _ _ _ _ _ (mkPoint 1 0) (mkPoint 0 1));
        try assumption.
      - apply pts_neq. left. lra.
      - left. left. split; reflexivity.
      - left. right. split; reflexivity. }
    rewrite H1 in Hdim. discriminate.
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

(* The only shared boundary point is (1,0), the midpoint of the host base. *)
Lemma tj_meet : forall X,
  on_bd (mkPoint 0 0) (mkPoint 2 0) (mkPoint 1 2) X /\
  on_bd (mkPoint 1 0) (mkPoint 0 (-1)) (mkPoint 2 (-1)) X ->
  X = mkPoint 1 0.
Proof.
  intros X [HA HB].
  destruct HA as [Hab|[Hbc|Hca]].
  - destruct HB as [Hde|[Hef|Hfd]].
    + destruct Hab as [t [Ht ->]]. destruct Hde as [s [Hs Heq]].
      unfold convex_combination in Heq. simpl in Heq. injection Heq as Hx Hy.
      simpl in Hx, Hy. assert (s = 0) by lra. assert (t = 1/2) by lra.
      subst s t. unfold convex_combination. simpl. f_equal; lra.
    + destruct Hab as [t [Ht ->]]. destruct Hef as [s [Hs Heq]].
      unfold convex_combination in Heq. simpl in Heq. injection Heq as Hx Hy.
      simpl in Hx, Hy. exfalso. lra.
    + destruct Hab as [t [Ht ->]]. destruct Hfd as [s [Hs Heq]].
      unfold convex_combination in Heq. simpl in Heq. injection Heq as Hx Hy.
      simpl in Hx, Hy. assert (s = 1) by lra. assert (t = 1/2) by lra.
      subst s t. unfold convex_combination. simpl. f_equal; lra.
  - destruct HB as [Hde|[Hef|Hfd]];
      destruct Hbc as [t [Ht ->]];
      [destruct Hde as [s [Hs Heq]] | destruct Hef as [s [Hs Heq]]
       | destruct Hfd as [s [Hs Heq]]];
      unfold convex_combination in Heq; simpl in Heq; injection Heq as Hx Hy;
      simpl in Hx, Hy; exfalso; lra.
  - destruct HB as [Hde|[Hef|Hfd]];
      destruct Hca as [t [Ht ->]];
      [destruct Hde as [s [Hs Heq]] | destruct Hef as [s [Hs Heq]]
       | destruct Hfd as [s [Hs Heq]]];
      unfold convex_combination in Heq; simpl in Heq; injection Heq as Hx Hy;
      simpl in Hx, Hy; exfalso; lra.
Qed.

Lemma tj_not_host :
  mkPoint 1 0 <> mkPoint 0 0 /\
  mkPoint 1 0 <> mkPoint 2 0 /\
  mkPoint 1 0 <> mkPoint 1 2.
Proof.
  split; [| split].
  - apply pts_neq. left. lra.
  - apply pts_neq. left. lra.
  - apply pts_neq. right. lra.
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
  destruct Hsem as [_ [Hbad|[Hedge|Hvtx]]].
  - rewrite im_bb_eq in Hbad. rewrite Hbb in Hbad. discriminate.
  - destruct Hedge as [Hdim _]. rewrite im_bb_eq in Hdim. rewrite Hbb in Hdim.
    discriminate.
  - destruct Hvtx as [_ [V [Hva [Hvb [HVa [HVb Honly]]]]]].
    assert (EV : V = mkPoint 1 0).
    { apply tj_meet. split; assumption. }
    destruct tj_not_host as [H0 [H2 Hc]].
    destruct Hva as [Ea|[Eb|Ec]].
    + rewrite Ea in EV. symmetry in EV. exact (H0 EV).
    + rewrite Eb in EV. symmetry in EV. exact (H2 EV).
    + rewrite Ec in EV. symmetry in EV. exact (Hc EV).
Qed.

(* Square (0,0)(1,0)(1,1)(0,1) split into four triangles at the centre.
   Adjacent triangles share a radius. Opposite triangles meet only there. *)
Definition fanSW : Point := mkPoint 0 0.
Definition fanSE : Point := mkPoint 1 0.
Definition fanNE : Point := mkPoint 1 1.
Definition fanNW : Point := mkPoint 0 1.
Definition fanC : Point := mkPoint (1/2) (1/2).

Definition fan_ts : list Tri :=
  [((fanSW, fanSE), fanC); ((fanSE, fanNE), fanC);
   ((fanNE, fanNW), fanC); ((fanNW, fanSW), fanC)].

Lemma centre_bd : forall A B, on_bd A B fanC fanC.
Proof.
  intros A B. right. right. exact (proj1 (seg_ends fanC A)).
Qed.

Ltac bd_prep :=
  match goal with
  | H : convex_combination _ _ _ = convex_combination _ _ _ |- _ =>
      unfold convex_combination in H; simpl in H;
      let Hx := fresh "Hx" in
      let Hy := fresh "Hy" in
      injection H as Hx Hy; simpl in Hx, Hy
  end.

Lemma fan01_bd : forall X,
  on_bd fanSW fanSE fanC X /\ on_bd fanSE fanNE fanC X <-> on_seg fanSE fanC X.
Proof.
  intros X. split.
  - intros [HA HB]. destruct HA as [Hab|[Hbc|Hca]].
    + destruct HB as [Hde|[Hef|Hfd]].
      * destruct Hab as [t [Ht ->]]. destruct Hde as [s [Hs Heq]].
        bd_prep. assert (t = 1) by lra. subst t.
        rewrite convex_combination_at_1. apply (proj1 (seg_ends fanSE fanC)).
      * destruct Hab as [t [Ht ->]]. destruct Hef as [s [Hs Heq]].
        bd_prep. exfalso. lra.
      * destruct Hab as [t [Ht ->]]. destruct Hfd as [s [Hs Heq]].
        bd_prep. assert (t = 1) by lra. subst t.
        rewrite convex_combination_at_1. apply (proj1 (seg_ends fanSE fanC)).
    + exact Hbc.
    + destruct HB as [Hde|[Hef|Hfd]].
      * destruct Hca as [t [Ht ->]]. destruct Hde as [s [Hs Heq]].
        bd_prep. exfalso. lra.
      * destruct Hca as [t [Ht ->]]. destruct Hef as [s [Hs Heq]].
        bd_prep. assert (t = 0) by lra. subst t.
        rewrite convex_combination_at_0. apply (proj2 (seg_ends fanSE fanC)).
      * destruct Hca as [t [Ht ->]]. destruct Hfd as [s [Hs Heq]].
        bd_prep. assert (t = 0) by lra. subst t.
        rewrite convex_combination_at_0. apply (proj2 (seg_ends fanSE fanC)).
  - intros HX. split.
    + right. left. exact HX.
    + right. right. apply on_seg_sym. exact HX.
Qed.

Lemma fan12_bd : forall X,
  on_bd fanSE fanNE fanC X /\ on_bd fanNE fanNW fanC X <-> on_seg fanNE fanC X.
Proof.
  intros X. split.
  - intros [HA HB]. destruct HA as [Hab|[Hbc|Hca]].
    + destruct HB as [Hde|[Hef|Hfd]].
      * destruct Hab as [t [Ht ->]]. destruct Hde as [s [Hs Heq]].
        bd_prep. assert (t = 1) by lra. subst t.
        rewrite convex_combination_at_1. apply (proj1 (seg_ends fanNE fanC)).
      * destruct Hab as [t [Ht ->]]. destruct Hef as [s [Hs Heq]].
        bd_prep. exfalso. lra.
      * destruct Hab as [t [Ht ->]]. destruct Hfd as [s [Hs Heq]].
        bd_prep. assert (t = 1) by lra. subst t.
        rewrite convex_combination_at_1. apply (proj1 (seg_ends fanNE fanC)).
    + exact Hbc.
    + destruct HB as [Hde|[Hef|Hfd]].
      * destruct Hca as [t [Ht ->]]. destruct Hde as [s [Hs Heq]].
        bd_prep. exfalso. lra.
      * destruct Hca as [t [Ht ->]]. destruct Hef as [s [Hs Heq]].
        bd_prep. assert (t = 0) by lra. subst t.
        rewrite convex_combination_at_0. apply (proj2 (seg_ends fanNE fanC)).
      * destruct Hca as [t [Ht ->]]. destruct Hfd as [s [Hs Heq]].
        bd_prep. assert (t = 0) by lra. subst t.
        rewrite convex_combination_at_0. apply (proj2 (seg_ends fanNE fanC)).
  - intros HX. split.
    + right. left. exact HX.
    + right. right. apply on_seg_sym. exact HX.
Qed.

Lemma fan23_bd : forall X,
  on_bd fanNE fanNW fanC X /\ on_bd fanNW fanSW fanC X <-> on_seg fanNW fanC X.
Proof.
  intros X. split.
  - intros [HA HB]. destruct HA as [Hab|[Hbc|Hca]].
    + destruct HB as [Hde|[Hef|Hfd]].
      * destruct Hab as [t [Ht ->]]. destruct Hde as [s [Hs Heq]].
        bd_prep. assert (t = 1) by lra. subst t.
        rewrite convex_combination_at_1. apply (proj1 (seg_ends fanNW fanC)).
      * destruct Hab as [t [Ht ->]]. destruct Hef as [s [Hs Heq]].
        bd_prep. exfalso. lra.
      * destruct Hab as [t [Ht ->]]. destruct Hfd as [s [Hs Heq]].
        bd_prep. assert (t = 1) by lra. subst t.
        rewrite convex_combination_at_1. apply (proj1 (seg_ends fanNW fanC)).
    + exact Hbc.
    + destruct HB as [Hde|[Hef|Hfd]].
      * destruct Hca as [t [Ht ->]]. destruct Hde as [s [Hs Heq]].
        bd_prep. exfalso. lra.
      * destruct Hca as [t [Ht ->]]. destruct Hef as [s [Hs Heq]].
        bd_prep. assert (t = 0) by lra. subst t.
        rewrite convex_combination_at_0. apply (proj2 (seg_ends fanNW fanC)).
      * destruct Hca as [t [Ht ->]]. destruct Hfd as [s [Hs Heq]].
        bd_prep. assert (t = 0) by lra. subst t.
        rewrite convex_combination_at_0. apply (proj2 (seg_ends fanNW fanC)).
  - intros HX. split.
    + right. left. exact HX.
    + right. right. apply on_seg_sym. exact HX.
Qed.

Lemma fan30_bd : forall X,
  on_bd fanSW fanSE fanC X /\ on_bd fanNW fanSW fanC X <-> on_seg fanSW fanC X.
Proof.
  intros X. split.
  - intros [HA HB]. destruct HA as [Hab|[Hbc|Hca]].
    + destruct HB as [Hde|[Hef|Hfd]].
      * destruct Hab as [t [Ht ->]]. destruct Hde as [s [Hs Heq]].
        bd_prep. assert (t = 0) by lra. subst t.
        rewrite convex_combination_at_0. apply (proj1 (seg_ends fanSW fanC)).
      * destruct Hab as [t [Ht ->]]. destruct Hef as [s [Hs Heq]].
        bd_prep. assert (t = 0) by lra. subst t.
        rewrite convex_combination_at_0. apply (proj1 (seg_ends fanSW fanC)).
      * destruct Hab as [t [Ht ->]]. destruct Hfd as [s [Hs Heq]].
        bd_prep. exfalso. lra.
    + destruct HB as [Hde|[Hef|Hfd]].
      * destruct Hbc as [t [Ht ->]]. destruct Hde as [s [Hs Heq]].
        bd_prep. exfalso. lra.
      * destruct Hbc as [t [Ht ->]]. destruct Hef as [s [Hs Heq]].
        bd_prep. assert (t = 1) by lra. subst t.
        rewrite convex_combination_at_1. apply (proj2 (seg_ends fanSW fanC)).
      * destruct Hbc as [t [Ht ->]]. destruct Hfd as [s [Hs Heq]].
        bd_prep. assert (t = 1) by lra. subst t.
        rewrite convex_combination_at_1. apply (proj2 (seg_ends fanSW fanC)).
    + apply on_seg_sym. exact Hca.
  - intros HX. split.
    + right. right. apply on_seg_sym. exact HX.
    + right. left. exact HX.
Qed.

Lemma fan02_only : forall X,
  on_bd fanSW fanSE fanC X /\ on_bd fanNE fanNW fanC X -> X = fanC.
Proof.
  intros X [HA HB]. destruct HA as [Hab|[Hbc|Hca]].
  - destruct HB as [Hde|[Hef|Hfd]];
      destruct Hab as [t [Ht ->]];
      [destruct Hde as [s [Hs Heq]] | destruct Hef as [s [Hs Heq]]
       | destruct Hfd as [s [Hs Heq]]];
      bd_prep; exfalso; lra.
  - destruct HB as [Hde|[Hef|Hfd]].
    + destruct Hbc as [t [Ht ->]]. destruct Hde as [s [Hs Heq]].
      bd_prep. exfalso. lra.
    + destruct Hbc as [t [Ht ->]]. destruct Hef as [s [Hs Heq]].
      bd_prep. assert (t = 1) by lra. subst t.
      rewrite convex_combination_at_1. reflexivity.
    + destruct Hbc as [t [Ht ->]]. destruct Hfd as [s [Hs Heq]].
      bd_prep. assert (t = 1) by lra. subst t.
      rewrite convex_combination_at_1. reflexivity.
  - destruct HB as [Hde|[Hef|Hfd]].
    + destruct Hca as [t [Ht ->]]. destruct Hde as [s [Hs Heq]].
      bd_prep. exfalso. lra.
    + destruct Hca as [t [Ht ->]]. destruct Hef as [s [Hs Heq]].
      bd_prep. assert (t = 0) by lra. subst t.
      rewrite convex_combination_at_0. reflexivity.
    + destruct Hca as [t [Ht ->]]. destruct Hfd as [s [Hs Heq]].
      bd_prep. assert (t = 0) by lra. subst t.
      rewrite convex_combination_at_0. reflexivity.
Qed.

Lemma fan13_only : forall X,
  on_bd fanSE fanNE fanC X /\ on_bd fanNW fanSW fanC X -> X = fanC.
Proof.
  intros X [HA HB]. destruct HA as [Hab|[Hbc|Hca]].
  - destruct HB as [Hde|[Hef|Hfd]];
      destruct Hab as [t [Ht ->]];
      [destruct Hde as [s [Hs Heq]] | destruct Hef as [s [Hs Heq]]
       | destruct Hfd as [s [Hs Heq]]];
      bd_prep; exfalso; lra.
  - destruct HB as [Hde|[Hef|Hfd]].
    + destruct Hbc as [t [Ht ->]]. destruct Hde as [s [Hs Heq]].
      bd_prep. exfalso. lra.
    + destruct Hbc as [t [Ht ->]]. destruct Hef as [s [Hs Heq]].
      bd_prep. assert (t = 1) by lra. subst t.
      rewrite convex_combination_at_1. reflexivity.
    + destruct Hbc as [t [Ht ->]]. destruct Hfd as [s [Hs Heq]].
      bd_prep. assert (t = 1) by lra. subst t.
      rewrite convex_combination_at_1. reflexivity.
  - destruct HB as [Hde|[Hef|Hfd]].
    + destruct Hca as [t [Ht ->]]. destruct Hde as [s [Hs Heq]].
      bd_prep. exfalso. lra.
    + destruct Hca as [t [Ht ->]]. destruct Hef as [s [Hs Heq]].
      bd_prep. assert (t = 0) by lra. subst t.
      rewrite convex_combination_at_0. reflexivity.
    + destruct Hca as [t [Ht ->]]. destruct Hfd as [s [Hs Heq]].
      bd_prep. assert (t = 0) by lra. subst t.
      rewrite convex_combination_at_0. reflexivity.
Qed.

Lemma fan01_sem : pair_sem fanSW fanSE fanC fanSE fanNE fanC.
Proof.
  split.
  - apply some_outer_disjoint; try (unfold cross; simpl; lra).
    right. left. unfold outer3, cross; simpl. repeat split; lra.
  - right. left. exists fanSE, fanC. split.
    + apply pts_neq. left. lra.
    + split; [right; left; left; split; reflexivity|].
      split; [right; right; right; split; reflexivity|]. exact fan01_bd.
Qed.

Lemma fan12_sem : pair_sem fanSE fanNE fanC fanNE fanNW fanC.
Proof.
  split.
  - apply some_outer_disjoint; try (unfold cross; simpl; lra).
    right. left. unfold outer3, cross; simpl. repeat split; lra.
  - right. left. exists fanNE, fanC. split.
    + apply pts_neq. left. lra.
    + split; [right; left; left; split; reflexivity|].
      split; [right; right; right; split; reflexivity|]. exact fan12_bd.
Qed.

Lemma fan23_sem : pair_sem fanNE fanNW fanC fanNW fanSW fanC.
Proof.
  split.
  - apply some_outer_disjoint; try (unfold cross; simpl; lra).
    right. left. unfold outer3, cross; simpl. repeat split; lra.
  - right. left. exists fanNW, fanC. split.
    + apply pts_neq. left. lra.
    + split; [right; left; left; split; reflexivity|].
      split; [right; right; right; split; reflexivity|]. exact fan23_bd.
Qed.

Lemma fan30_sem : pair_sem fanSW fanSE fanC fanNW fanSW fanC.
Proof.
  split.
  - apply some_outer_disjoint; try (unfold cross; simpl; lra).
    right. right. left. unfold outer3, cross; simpl. repeat split; lra.
  - right. left. exists fanSW, fanC. split.
    + apply pts_neq. right. lra.
    + split; [right; right; right; split; reflexivity|].
      split; [right; left; left; split; reflexivity|]. exact fan30_bd.
Qed.

Lemma fan02_sem : pair_sem fanSW fanSE fanC fanNE fanNW fanC.
Proof.
  split.
  - apply some_outer_disjoint; try (unfold cross; simpl; lra).
    right. left. unfold outer3, cross; simpl. repeat split; lra.
  - right. right. exists fanC. split; [| split; [| split; [| split]]].
    + right. right. reflexivity.
    + right. right. reflexivity.
    + apply centre_bd.
    + apply centre_bd.
    + exact fan02_only.
Qed.

Lemma fan13_sem : pair_sem fanSE fanNE fanC fanNW fanSW fanC.
Proof.
  split.
  - apply some_outer_disjoint; try (unfold cross; simpl; lra).
    right. left. unfold outer3, cross; simpl. repeat split; lra.
  - right. right. exists fanC. split; [| split; [| split; [| split]]].
    + right. right. reflexivity.
    + right. right. reflexivity.
    + apply centre_bd.
    + apply centre_bd.
    + exact fan13_only.
Qed.

Theorem tin_fan :
  tin_sem fan_ts /\
  im_ii (tri_de9im fanSW fanSE fanC fanNE fanNW fanC) = DimF /\
  im_bb (tri_de9im fanSW fanSE fanC fanNE fanNW fanC) = Dim0.
Proof.
  split; [| split].
  - simpl. split.
    + intros U HU. simpl in HU. destruct HU as [<-|[<-|[<-|[]]]].
      * apply fan01_sem.
      * apply fan02_sem.
      * apply fan30_sem.
    + split.
      * intros U HU. simpl in HU. destruct HU as [<-|[<-|[]]].
        -- apply fan12_sem.
        -- apply fan13_sem.
      * split.
        -- intros U HU. simpl in HU. destruct HU as [<-|[]]. apply fan23_sem.
        -- split; [intros U HU; simpl in HU; destruct HU | exact I].
  - assert (HA : 0 < cross fanSW fanSE fanC) by (unfold cross; simpl; lra).
    assert (HB : 0 < cross fanNE fanNW fanC) by (unfold cross; simpl; lra).
    rewrite im_ii_eq. apply ii_dimF_iff; try assumption.
    destruct fan02_sem as [Hapart _]. exact Hapart.
  - assert (HA : 0 < cross fanSW fanSE fanC) by (unfold cross; simpl; lra).
    assert (HB : 0 < cross fanNE fanNW fanC) by (unfold cross; simpl; lra).
    rewrite im_bb_eq. apply vtx_gives_dim0; try assumption.
    destruct fan02_sem as [_ [Hempty|[Hedge|Hvtx]]].
    + exfalso. apply Hempty. exists fanC. split; apply centre_bd.
    + exfalso. destruct Hedge as [P [Q [Hne [_ [_ Hex]]]]]. apply Hne.
      assert (HP : on_bd fanSW fanSE fanC P /\ on_bd fanNE fanNW fanC P).
      { apply Hex. apply (proj1 (seg_ends P Q)). }
      assert (HQ : on_bd fanSW fanSE fanC Q /\ on_bd fanNE fanNW fanC Q).
      { apply Hex. apply (proj2 (seg_ends P Q)). }
      rewrite (fan02_only P HP), (fan02_only Q HQ). reflexivity.
    + exact Hvtx.
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
Print Assumptions tj_meet.
Print Assumptions tj_not_host.
Print Assumptions tin_tjunction.
Print Assumptions centre_bd.
Print Assumptions fan01_bd.
Print Assumptions fan12_bd.
Print Assumptions fan23_bd.
Print Assumptions fan30_bd.
Print Assumptions fan02_only.
Print Assumptions fan13_only.
Print Assumptions fan01_sem.
Print Assumptions fan12_sem.
Print Assumptions fan23_sem.
Print Assumptions fan30_sem.
Print Assumptions fan02_sem.
Print Assumptions fan13_sem.
Print Assumptions tin_fan.
Print Assumptions vtx_gives_dim0.
