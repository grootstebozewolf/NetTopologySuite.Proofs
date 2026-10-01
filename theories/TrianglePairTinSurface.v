(* NetTopologySuite.Proofs.TrianglePairTinSurface
   A valid TIN's carrier partitions into cell interior and cell boundary.
   Cell boundary: a point of an edge used by exactly one triangle.
   Cell interior: a triangle open, the relative interior of an edge used
   at least twice, or a vertex that lies on no once-edge.
   This is that cell partition, not the topological interior or boundary.
   Fixtures: fan_centre_int_cells_fixtures, fan_base_bd_cells_fixtures,
   fan_radius_int_cells_fixtures.
   topic: relate
   claimId: tri-de9im-tin-surface
   witness: tin_surface
   3-axiom host. No Admitted. No Jordan.
   AI-drafted (Cursor Grok 4.7).
   License: BSD-3-Clause *)
From Stdlib Require Import Reals Lra Lia List Bool PeanoNat.
Import ListNotations.
From NTS.Proofs Require Import Distance Orientation Convex ConvexClip
  DE9IM TrianglePairCommon TrianglePairClip TrianglePairEdge
  TrianglePairBound TrianglePairExterior TrianglePairMatrix TrianglePairTin.
Local Open Scope R_scope.

Definition edge_id_b (P Q R S : Point) : bool :=
  (point_eqb P R && point_eqb Q S) || (point_eqb P S && point_eqb Q R).

Definition vert_edge_b (A B C P Q : Point) : bool :=
  edge_id_b P Q A B || edge_id_b P Q B C || edge_id_b P Q C A.

Definition tri_edge_b (T : Tri) (P Q : Point) : bool :=
  match T with ((A, B), C) => vert_edge_b A B C P Q end.

Fixpoint edge_uses (ts : list Tri) (P Q : Point) : nat :=
  match ts with
  | [] => 0%nat
  | T :: rest =>
      if tri_edge_b T P Q then S (edge_uses rest P Q) else edge_uses rest P Q
  end.

Definition on_seg_open (P Q X : Point) : Prop :=
  exists t, 0 < t < 1 /\ X = convex_combination P Q t.

Definition open_of (T : Tri) (X : Point) : Prop :=
  match T with ((A, B), C) => tri_open A B C X end.

Definition bd_of (T : Tri) (X : Point) : Prop :=
  match T with ((A, B), C) => on_bd A B C X end.

Definition vert_of (T : Tri) (X : Point) : Prop :=
  match T with ((A, B), C) => X = A \/ X = B \/ X = C end.

Definition tri_edges (T : Tri) : list (Point * Point) :=
  match T with ((A, B), C) => [(A, B); (B, C); (C, A)] end.

Definition tin_bd_cells (ts : list Tri) (X : Point) : Prop :=
  exists P Q, P <> Q /\ edge_uses ts P Q = 1%nat /\ on_seg P Q X.

Definition shared_rel (ts : list Tri) (X : Point) : Prop :=
  exists P Q, P <> Q /\ (2 <= edge_uses ts P Q)%nat /\ on_seg_open P Q X.

Definition tin_vert (ts : list Tri) (X : Point) : Prop :=
  exists T, In T ts /\ vert_of T X.

Definition internal_vert (ts : list Tri) (X : Point) : Prop :=
  tin_vert ts X /\ ~ tin_bd_cells ts X.

Definition tin_int_cells (ts : list Tri) (X : Point) : Prop :=
  (exists T, In T ts /\ open_of T X) \/ shared_rel ts X \/ internal_vert ts X.

Definition tin_carrier (ts : list Tri) (X : Point) : Prop :=
  exists T, In T ts /\ (open_of T X \/ bd_of T X).

Definition once_edge_b (ts : list Tri) (e : Point * Point) (X : Point) : bool :=
  Nat.eqb (edge_uses ts (fst e) (snd e)) 1 && on_seg_b (fst e) (snd e) X.

Fixpoint once_in (ts acc : list Tri) (X : Point) : bool :=
  match acc with
  | [] => false
  | T :: rest =>
      existsb (fun e => once_edge_b ts e X) (tri_edges T) || once_in ts rest X
  end.

Definition on_once_b (ts : list Tri) (X : Point) : bool := once_in ts ts X.

Definition tri_eqb (T U : Tri) : bool :=
  match T, U with
  | ((A, B), C), ((D, E), F) =>
      point_eqb A D && point_eqb B E && point_eqb C F
  end.

Lemma edge_id_b_true : forall P Q R S,
  edge_id_b P Q R S = true <-> edge_id P Q R S.
Proof.
  intros P Q R S. unfold edge_id_b, edge_id. split.
  - intros H. apply orb_true_iff in H. destruct H as [H|H].
    + apply andb_true_iff in H. destruct H as [H1 H2].
      apply point_eqb_true in H1, H2. left. split; assumption.
    + apply andb_true_iff in H. destruct H as [H1 H2].
      apply point_eqb_true in H1, H2. right. split; assumption.
  - intros [[-> ->]|[-> ->]]; apply orb_true_iff.
    + left. apply andb_true_iff. split; apply point_eqb_refl.
    + right. apply andb_true_iff. split; apply point_eqb_refl.
Qed.

Lemma edge_id_b_false : forall P Q R S,
  edge_id_b P Q R S = false -> ~ edge_id P Q R S.
Proof.
  intros P Q R S H Hid. apply edge_id_b_true in Hid. congruence.
Qed.

Lemma vert_edge_b_true : forall A B C P Q,
  vert_edge_b A B C P Q = true <-> vert_edge A B C P Q.
Proof.
  intros A B C P Q. unfold vert_edge_b, vert_edge. split.
  - intros H. apply orb_true_iff in H. destruct H as [H|H].
    + apply orb_true_iff in H. destruct H as [H|H].
      * left. apply edge_id_b_true. exact H.
      * right. left. apply edge_id_b_true. exact H.
    + right. right. apply edge_id_b_true. exact H.
  - intros [H|[H|H]]; apply orb_true_iff.
    + left. apply orb_true_iff. left. apply edge_id_b_true. exact H.
    + left. apply orb_true_iff. right. apply edge_id_b_true. exact H.
    + right. apply edge_id_b_true. exact H.
Qed.

Lemma tri_edge_b_true : forall T P Q,
  tri_edge_b T P Q = true <->
  match T with ((A, B), C) => vert_edge A B C P Q end.
Proof.
  intros [[A B] C] P Q. unfold tri_edge_b. apply vert_edge_b_true.
Qed.

Lemma tri_edge_b_false : forall A B C P Q,
  tri_edge_b ((A, B), C) P Q = false -> ~ vert_edge A B C P Q.
Proof.
  intros A B C P Q H Hv. apply vert_edge_b_true in Hv.
  unfold tri_edge_b in H. congruence.
Qed.

Lemma edge_id_sym : forall P Q R S, edge_id P Q R S -> edge_id R S P Q.
Proof.
  intros P Q R S [[-> ->]|[-> ->]].
  - left. split; reflexivity.
  - right. split; reflexivity.
Qed.

Lemma edge_id_trans : forall P Q R S U V,
  edge_id P Q R S -> edge_id R S U V -> edge_id P Q U V.
Proof.
  intros P Q R S U V H1 H2.
  destruct H1 as [[-> ->]|[-> ->]]; destruct H2 as [[-> ->]|[-> ->]].
  - left. split; reflexivity.
  - right. split; reflexivity.
  - right. split; reflexivity.
  - left. split; reflexivity.
Qed.

Lemma on_seg_of_id : forall P Q R S X,
  edge_id P Q R S -> on_seg P Q X -> on_seg R S X.
Proof.
  intros P Q R S X [[-> ->]|[-> ->]] H.
  - exact H.
  - apply on_seg_sym. exact H.
Qed.

Lemma vert_edge_transfer : forall A B C P Q R S,
  edge_id P Q R S -> vert_edge A B C R S -> vert_edge A B C P Q.
Proof.
  intros A B C P Q R S Hid [H|[H|H]].
  - left. apply (edge_id_trans P Q R S A B Hid H).
  - right. left. apply (edge_id_trans P Q R S B C Hid H).
  - right. right. apply (edge_id_trans P Q R S C A Hid H).
Qed.

Lemma canon_of_vert : forall A B C P Q,
  vert_edge A B C P Q ->
  exists R S, edge_id P Q R S /\
    ((R = A /\ S = B) \/ (R = B /\ S = C) \/ (R = C /\ S = A)).
Proof.
  intros A B C P Q H.
  destruct H as [H|[H|H]]; destruct H as [[-> ->]|[-> ->]].
  - exists A, B. split. left. split; reflexivity. left. split; reflexivity.
  - exists A, B. split. right. split; reflexivity. left. split; reflexivity.
  - exists B, C. split. left. split; reflexivity. right. left. split; reflexivity.
  - exists B, C. split. right. split; reflexivity. right. left. split; reflexivity.
  - exists C, A. split. left. split; reflexivity. right. right. split; reflexivity.
  - exists C, A. split. right. split; reflexivity. right. right. split; reflexivity.
Qed.

Lemma bd_of_edge : forall A B C P Q X,
  vert_edge A B C P Q -> on_seg P Q X -> on_bd A B C X.
Proof.
  intros A B C P Q X He Hs.
  destruct (canon_of_vert A B C P Q He) as [R [S [Hid Hc]]].
  assert (HR : on_seg R S X) by (apply (on_seg_of_id P Q R S X); assumption).
  destruct Hc as [[-> ->]|[[-> ->]|[-> ->]]].
  - left. exact HR.
  - right. left. exact HR.
  - right. right. exact HR.
Qed.

Lemma edge_uses_id : forall ts P Q R S,
  edge_id P Q R S -> edge_uses ts P Q = edge_uses ts R S.
Proof.
  induction ts as [|T rest IH]; intros P Q R S Hid; simpl.
  - reflexivity.
  - destruct T as [[A B] C].
    assert (Hb : vert_edge_b A B C P Q = vert_edge_b A B C R S).
    { destruct (vert_edge_b A B C P Q) eqn:Hp;
      destruct (vert_edge_b A B C R S) eqn:Hr; try reflexivity.
      - apply vert_edge_b_true in Hp.
        assert (Hvr : vert_edge A B C R S).
        { apply (vert_edge_transfer A B C R S P Q).
          - apply edge_id_sym. exact Hid.
          - exact Hp. }
        apply vert_edge_b_true in Hvr. congruence.
      - apply vert_edge_b_true in Hr.
        assert (Hvp : vert_edge A B C P Q).
        { apply (vert_edge_transfer A B C P Q R S Hid Hr). }
        apply vert_edge_b_true in Hvp. congruence. }
    unfold tri_edge_b. rewrite Hb.
    destruct (vert_edge_b A B C R S).
    + f_equal. apply IH. exact Hid.
    + apply IH. exact Hid.
Qed.

Lemma edge_uses_sym : forall ts P Q, edge_uses ts P Q = edge_uses ts Q P.
Proof.
  intros ts P Q. apply edge_uses_id. right. split; reflexivity.
Qed.

Lemma uses_cons_true : forall T rest P Q,
  tri_edge_b T P Q = true ->
  edge_uses (T :: rest) P Q = S (edge_uses rest P Q).
Proof.
  intros T rest P Q H. simpl. rewrite H. reflexivity.
Qed.

Lemma uses_cons_false : forall T rest P Q,
  tri_edge_b T P Q = false ->
  edge_uses (T :: rest) P Q = edge_uses rest P Q.
Proof.
  intros T rest P Q H. simpl. rewrite H. reflexivity.
Qed.

Lemma uses_member : forall ts T P Q,
  In T ts -> tri_edge_b T P Q = true -> (1 <= edge_uses ts P Q)%nat.
Proof.
  induction ts as [|U rest IH]; intros T P Q Hin Hb; simpl in Hin.
  - contradiction.
  - simpl. destruct Hin as [->|Hin].
    + rewrite Hb. lia.
    + destruct (tri_edge_b U P Q) eqn:Hu.
      * lia.
      * apply (IH T P Q); assumption.
Qed.

Lemma uses_ge1_owner : forall ts P Q,
  (1 <= edge_uses ts P Q)%nat ->
  exists T, In T ts /\ tri_edge_b T P Q = true.
Proof.
  induction ts as [|T rest IH]; intros P Q H; simpl in H.
  - lia.
  - destruct (tri_edge_b T P Q) eqn:Hb.
    + exists T. split. left. reflexivity. exact Hb.
    + destruct (IH P Q H) as [U [Hin HbU]].
      exists U. split. right. exact Hin. exact HbU.
Qed.

Lemma uses_eq1_owner : forall ts P Q,
  edge_uses ts P Q = 1%nat ->
  exists T, In T ts /\ tri_edge_b T P Q = true /\
    (forall U, In U ts -> tri_edge_b U P Q = true -> U = T).
Proof.
  induction ts as [|T rest IH]; intros P Q H; simpl in H.
  - discriminate.
  - destruct (tri_edge_b T P Q) eqn:Hb.
    + injection H as Hrest.
      exists T. split; [left; reflexivity|]. split; [exact Hb|].
      intros U Hin HbU. destruct Hin as [->|Hin].
      * reflexivity.
      * assert (Hge : (1 <= edge_uses rest P Q)%nat).
        { apply (uses_member rest U P Q Hin HbU). }
        lia.
    + destruct (IH P Q H) as [W [Hin [HbW Huniq]]].
      exists W. split; [right; exact Hin|]. split; [exact HbW|].
      intros U HinU HbU. destruct HinU as [->|HinU].
      * congruence.
      * apply Huniq; assumption.
Qed.

Lemma once_in_true : forall ts acc X,
  once_in ts acc X = true ->
  exists T e, In T acc /\ In e (tri_edges T) /\ once_edge_b ts e X = true.
Proof.
  induction acc as [|T rest IH]; intros X H; simpl in H.
  - discriminate.
  - apply orb_true_iff in H. destruct H as [H|H].
    + apply existsb_exists in H. destruct H as [e [He Hb]].
      exists T, e. split. left. reflexivity. split; assumption.
    + destruct (IH X H) as [U [e [Hin [He Hb]]]].
      exists U, e. split. right. exact Hin. split; assumption.
Qed.

Lemma once_in_hit : forall ts acc X T,
  In T acc ->
  existsb (fun e => once_edge_b ts e X) (tri_edges T) = true ->
  once_in ts acc X = true.
Proof.
  induction acc as [|U rest IH]; intros X T Hin Hex; simpl in Hin.
  - contradiction.
  - simpl. destruct Hin as [->|Hin].
    + rewrite Hex. reflexivity.
    + rewrite (IH X T Hin Hex). apply orb_true_r.
Qed.

Lemma on_once_bd_cells : forall ts X,
  (forall T, In T ts -> tri_pos T) ->
  on_once_b ts X = true -> tin_bd_cells ts X.
Proof.
  intros ts X Hpos H.
  unfold on_once_b in H.
  destruct (once_in_true ts ts X H) as [T [e [Hin [He HuOn]]]].
  unfold once_edge_b in HuOn. apply andb_true_iff in HuOn.
  destruct HuOn as [Hn Hs].
  apply Nat.eqb_eq in Hn. apply on_seg_b_iff in Hs.
  exists (fst e), (snd e). split; [| split; assumption].
  destruct T as [[A B] C]. simpl in He.
  destruct (edge_sep A B C) as [Hab [Hbc Hca]].
  { apply Hpos in Hin. simpl in Hin. exact Hin. }
  destruct He as [<-|[<-|[<-|[]]]].
  - exact Hab.
  - exact Hbc.
  - exact Hca.
Qed.

Lemma bd_cells_on_once : forall ts X,
  (forall T, In T ts -> tri_pos T) ->
  tin_bd_cells ts X -> on_once_b ts X = true.
Proof.
  intros ts X Hpos [P [Q [_ [Hu Hs]]]].
  destruct (uses_eq1_owner ts P Q Hu) as [T [Hin [Hb _]]].
  unfold on_once_b. apply (once_in_hit ts ts X T Hin).
  destruct T as [[A B] C]. apply tri_edge_b_true in Hb. simpl in Hb.
  destruct (canon_of_vert A B C P Q Hb) as [R [S [Hid Hc]]].
  apply existsb_exists. exists (R, S). split.
  - destruct Hc as [[-> ->]|[[-> ->]|[-> ->]]]; simpl; auto.
  - unfold once_edge_b. simpl. apply andb_true_iff. split.
    + apply Nat.eqb_eq. rewrite <- (edge_uses_id ts P Q R S Hid). exact Hu.
    + apply on_seg_b_iff. apply (on_seg_of_id P Q R S X Hid Hs).
Qed.

Lemma not_once_not_bd_cells : forall ts X,
  (forall T, In T ts -> tri_pos T) ->
  on_once_b ts X = false -> ~ tin_bd_cells ts X.
Proof.
  intros ts X Hpos H Hb. apply bd_cells_on_once in Hb; auto. congruence.
Qed.

Lemma tri_open_not_bd : forall A B C X,
  tri_open A B C X -> ~ on_bd A B C X.
Proof.
  intros A B C X [Hab [Hbc Hca]] [Hs|[Hs|Hs]].
  - apply on_seg_cross0 in Hs. lra.
  - apply on_seg_cross0 in Hs. lra.
  - apply on_seg_cross0 in Hs. lra.
Qed.

Lemma open_misses_bd : forall A B C D E F X,
  0 < cross A B C -> 0 < cross D E F ->
  (~ exists Y, tri_open A B C Y /\ tri_open D E F Y) ->
  tri_open A B C X -> ~ on_bd D E F X.
Proof.
  intros A B C D E F X HA HB Hdis HX Hb.
  set (I := inner_pt D E F).
  set (room := troom A B C X I).
  assert (Hroom : 0 < room) by (apply troom_pos; exact HX).
  set (t := Rmin (1 / 2) (room / 2)).
  assert (Ht0 : 0 < t).
  { unfold t. apply Rmin_pos. lra. apply Rdiv_lt_0_compat; lra. }
  assert (Ht1 : t <= 1).
  { unfold t. eapply Rle_trans. apply Rmin_l. lra. }
  assert (Htr : t < room).
  { unfold t. eapply Rle_lt_trans. apply Rmin_r. lra. }
  set (Y := convex_combination X I t).
  apply Hdis. exists Y. split.
  - apply (nudge_tri_open A B C X I t HA HX Ht0 Htr).
  - apply (near_open D E F X t HB).
    + apply on_bd_in_tri. exact Hb.
    + split; [exact Ht0 | exact Ht1].
Qed.

Lemma tri_eqb_true : forall T U, tri_eqb T U = true -> T = U.
Proof.
  intros [[A B] C] [[D E] F] H. unfold tri_eqb in H.
  apply andb_true_iff in H. destruct H as [H Hf].
  apply andb_true_iff in H. destruct H as [Ha Hb].
  apply point_eqb_true in Ha, Hb, Hf. subst. reflexivity.
Qed.

Lemma tri_eqb_false_inv : forall T U, tri_eqb T U = false -> T <> U.
Proof.
  intros T U H E. subst U. destruct T as [[A B] C]. unfold tri_eqb in H.
  rewrite point_eqb_refl, point_eqb_refl, point_eqb_refl in H. discriminate.
Qed.

Lemma pair_edge_sym : forall A B C D E F,
  pair_edge A B C D E F -> pair_edge D E F A B C.
Proof.
  intros A B C D E F [P [Q [Hne [Ha [Hb Hex]]]]].
  exists P, Q. split; [exact Hne|]. split; [exact Hb|]. split; [exact Ha|].
  intros X. split.
  - intros [H1 H2]. apply Hex. split; assumption.
  - intros Hs. destruct (proj2 (Hex X) Hs) as [H1 H2]. split; assumption.
Qed.

Lemma pair_vtx_sym : forall A B C D E F,
  pair_vtx A B C D E F -> pair_vtx D E F A B C.
Proof.
  intros A B C D E F [V [Ha [Hb [HVa [HVb Honly]]]]].
  exists V. split; [exact Hb|]. split; [exact Ha|]. split; [exact HVb|].
  split; [exact HVa|]. intros X [H1 H2]. apply Honly. split; assumption.
Qed.

Lemma pair_sem_sym : forall A B C D E F,
  pair_sem A B C D E F -> pair_sem D E F A B C.
Proof.
  intros A B C D E F [Ho [Hempty|[Hedge|Hvtx]]].
  - split.
    + intros [X [H1 H2]]. apply Ho. exists X. split; assumption.
    + left. intros [X [H1 H2]]. apply Hempty. exists X. split; assumption.
  - split.
    + intros [X [H1 H2]]. apply Ho. exists X. split; assumption.
    + right. left. apply pair_edge_sym. exact Hedge.
  - split.
    + intros [X [H1 H2]]. apply Ho. exists X. split; assumption.
    + right. right. apply pair_vtx_sym. exact Hvtx.
Qed.

Lemma tri_pair_sem_sym : forall T U, tri_pair_sem T U -> tri_pair_sem U T.
Proof.
  intros [[A B] C] [[D E] F] H. simpl in *. apply pair_sem_sym. exact H.
Qed.

Lemma tin_ordered_pair : forall ts T U,
  tin_sem ts -> In T ts -> In U ts -> T <> U ->
  tri_pair_sem T U \/ tri_pair_sem U T.
Proof.
  induction ts as [|V rest IH]; intros T U Hsem HinT HinU Hneq.
  - simpl in HinT. contradiction.
  - simpl in Hsem. destruct Hsem as [Hall Hrest].
    simpl in HinT, HinU.
    destruct HinT as [<-|HinT]; destruct HinU as [<-|HinU].
    + exfalso. apply Hneq. reflexivity.
    + left. apply Hall. exact HinU.
    + right. apply Hall. exact HinT.
    + apply IH; assumption.
Qed.

Lemma open_vs_bd : forall ts T U X,
  (forall V, In V ts -> tri_pos V) ->
  tin_sem ts -> In T ts -> In U ts ->
  open_of T X -> bd_of U X -> False.
Proof.
  intros ts T U X Hpos Hsem HinT HinU Ho Hb.
  destruct (tri_eqb T U) eqn:Heq.
  - apply tri_eqb_true in Heq. subst U.
    destruct T as [[A B] C]. apply (tri_open_not_bd A B C X Ho Hb).
  - assert (Hneq : T <> U) by (apply tri_eqb_false_inv; exact Heq).
    destruct (tin_ordered_pair ts T U Hsem HinT HinU Hneq) as [HTU|HUT].
    + destruct T as [[A B] C], U as [[D E] F]. simpl in Ho, Hb, HTU.
      destruct HTU as [Hopen _].
      apply (open_misses_bd A B C D E F X).
      * apply Hpos in HinT. simpl in HinT. exact HinT.
      * apply Hpos in HinU. simpl in HinU. exact HinU.
      * exact Hopen.
      * exact Ho.
      * exact Hb.
    + apply tri_pair_sem_sym in HUT.
      destruct T as [[A B] C], U as [[D E] F]. simpl in Ho, Hb, HUT.
      destruct HUT as [Hopen _].
      apply (open_misses_bd A B C D E F X).
      * apply Hpos in HinT. simpl in HinT. exact HinT.
      * apply Hpos in HinU. simpl in HinU. exact HinU.
      * exact Hopen.
      * exact Ho.
      * exact Hb.
Qed.

Lemma open_not_bd_cells : forall ts X,
  (forall T, In T ts -> tri_pos T) -> tin_sem ts ->
  (exists T, In T ts /\ open_of T X) -> ~ tin_bd_cells ts X.
Proof.
  intros ts X Hpos Hsem [T [HinT Ho]] [P [Q [_ [Hu Hs]]]].
  destruct (uses_eq1_owner ts P Q Hu) as [U [HinU [Hb _]]].
  destruct U as [[D E] F]. apply tri_edge_b_true in Hb. simpl in Hb.
  apply (open_vs_bd ts T ((D, E), F) X Hpos Hsem HinT HinU Ho).
  apply (bd_of_edge D E F P Q X Hb Hs).
Qed.

Lemma combo_eq_left : forall P Q t,
  P <> Q -> convex_combination P Q t = P -> t = 0.
Proof.
  intros P Q t Hne Heq. unfold convex_combination in Heq.
  destruct P as [pxp pyp], Q as [pxq pyq]. simpl in Heq.
  injection Heq as Ex Ey.
  destruct (Req_dec_T t 0) as [Ht|Ht]; [exact Ht|].
  exfalso. apply Hne. f_equal.
  - apply (Rmult_eq_reg_l t pxp pxq); [| exact Ht].
    assert (Eqx : t * pxp = t * pxq) by lra. exact Eqx.
  - apply (Rmult_eq_reg_l t pyp pyq); [| exact Ht].
    assert (Eqy : t * pyp = t * pyq) by lra. exact Eqy.
Qed.

Lemma combo_eq_right : forall P Q t,
  P <> Q -> convex_combination P Q t = Q -> t = 1.
Proof.
  intros P Q t Hne Heq. unfold convex_combination in Heq.
  destruct P as [pxp pyp], Q as [pxq pyq]. simpl in Heq.
  injection Heq as Ex Ey.
  destruct (Req_dec_T t 1) as [Ht|Ht]; [exact Ht|].
  exfalso. apply Hne. f_equal.
  - apply (Rmult_eq_reg_l (1 - t) pxp pxq); [| lra].
    assert (Eqx : (1 - t) * pxp = (1 - t) * pxq) by lra. exact Eqx.
  - apply (Rmult_eq_reg_l (1 - t) pyp pyq); [| lra].
    assert (Eqy : (1 - t) * pyp = (1 - t) * pyq) by lra. exact Eqy.
Qed.

Lemma on_seg_open_seg : forall P Q X, on_seg_open P Q X -> on_seg P Q X.
Proof.
  intros P Q X [t [Ht Hx]]. exists t. split; [lra | exact Hx].
Qed.

Lemma seg_open_of_not_end : forall P Q X,
  P <> Q -> on_seg P Q X -> X <> P -> X <> Q -> on_seg_open P Q X.
Proof.
  intros P Q X Hne [t [[Ht0 Ht1] Hx]] HnP HnQ.
  exists t. split; [| exact Hx]. split.
  - destruct (Req_dec_T t 0) as [Z|Z].
    + exfalso. subst t. rewrite convex_combination_at_0 in Hx.
      apply HnP. exact Hx.
    + lra.
  - destruct (Req_dec_T t 1) as [Z|Z].
    + exfalso. subst t. rewrite convex_combination_at_1 in Hx.
      apply HnQ. exact Hx.
    + lra.
Qed.

Lemma relint_not_ends : forall P Q X,
  P <> Q -> on_seg_open P Q X -> X <> P /\ X <> Q.
Proof.
  intros P Q X Hne [t [[Ht0 Ht1] Hx]]. split.
  - intros Heq.
    assert (Et : t = 0).
    { apply (combo_eq_left P Q t Hne). rewrite <- Hx, Heq. reflexivity. }
    lra.
  - intros Heq.
    assert (Et : t = 1).
    { apply (combo_eq_right P Q t Hne). rewrite <- Hx, Heq. reflexivity. }
    lra.
Qed.

Lemma seg_ab_bc : forall A B C X,
  0 < cross A B C -> on_seg A B X -> on_seg B C X -> X = B.
Proof.
  intros A B C X Hd [t [_ Hx]] Hs.
  assert (Hz : cross B C X = 0) by (apply on_seg_cross0; exact Hs).
  rewrite Hx, cross_combo in Hz.
  replace (cross B C B) with 0 in Hz by (unfold cross; ring).
  assert (Hc : cross B C A = cross A B C).
  { symmetry. apply (cross_cycle A B C). }
  assert (Hz0 : (1 - t) * cross A B C = 0).
  { rewrite Hc in Hz. ring_simplify in Hz. ring_simplify. exact Hz. }
  assert (Ht : 1 - t = 0).
  { apply (Rmult_eq_reg_r (cross A B C) (1 - t) 0).
    - rewrite Rmult_0_l. exact Hz0.
    - lra. }
  assert (Et : t = 1) by lra. subst t.
  rewrite convex_combination_at_1 in Hx. exact Hx.
Qed.

Lemma seg_ab_ca : forall A B C X,
  0 < cross A B C -> on_seg A B X -> on_seg C A X -> X = A.
Proof.
  intros A B C X Hd [t [_ Hx]] Hs.
  assert (Hz : cross C A X = 0) by (apply on_seg_cross0; exact Hs).
  rewrite Hx, cross_combo in Hz.
  replace (cross C A A) with 0 in Hz by (unfold cross; ring).
  assert (Hc : cross C A B = cross A B C).
  { symmetry. apply (cross_cycle2 A B C). }
  assert (Hz0 : t * cross A B C = 0).
  { rewrite Hc in Hz. ring_simplify in Hz. ring_simplify. exact Hz. }
  assert (Ht : t = 0).
  { apply (Rmult_eq_reg_r (cross A B C) t 0).
    - rewrite Rmult_0_l. exact Hz0.
    - lra. }
  subst t. rewrite convex_combination_at_0 in Hx. exact Hx.
Qed.

Lemma seg_bc_ca : forall A B C X,
  0 < cross A B C -> on_seg B C X -> on_seg C A X -> X = C.
Proof.
  intros A B C X Hd [t [_ Hx]] Hs.
  assert (Hz : cross C A X = 0) by (apply on_seg_cross0; exact Hs).
  rewrite Hx, cross_combo in Hz.
  replace (cross C A C) with 0 in Hz by (unfold cross; ring).
  assert (Hc : cross C A B = cross A B C).
  { symmetry. apply (cross_cycle2 A B C). }
  assert (Hz0 : (1 - t) * cross A B C = 0).
  { rewrite Hc in Hz. ring_simplify in Hz. ring_simplify. exact Hz. }
  assert (Ht : 1 - t = 0).
  { apply (Rmult_eq_reg_r (cross A B C) (1 - t) 0).
    - rewrite Rmult_0_l. exact Hz0.
    - lra. }
  assert (Et : t = 1) by lra. subst t.
  rewrite convex_combination_at_1 in Hx. exact Hx.
Qed.

Lemma canon_meet : forall A B C R S U V X,
  0 < cross A B C ->
  ((R = A /\ S = B) \/ (R = B /\ S = C) \/ (R = C /\ S = A)) ->
  ((U = A /\ V = B) \/ (U = B /\ V = C) \/ (U = C /\ V = A)) ->
  on_seg R S X -> on_seg U V X ->
  (R = U /\ S = V) \/ X = A \/ X = B \/ X = C.
Proof.
  intros A B C R S U V X Hd HR HU Hs1 Hs2.
  destruct HR as [[-> ->]|[[-> ->]|[-> ->]]];
  destruct HU as [[-> ->]|[[-> ->]|[-> ->]]].
  - left. split; reflexivity.
  - right. right. left. apply (seg_ab_bc A B C X Hd Hs1 Hs2).
  - right. left. apply (seg_ab_ca A B C X Hd Hs1 Hs2).
  - right. right. left. apply (seg_ab_bc A B C X Hd Hs2 Hs1).
  - left. split; reflexivity.
  - right. right. right. apply (seg_bc_ca A B C X Hd Hs1 Hs2).
  - right. left. apply (seg_ab_ca A B C X Hd Hs2 Hs1).
  - right. right. right. apply (seg_bc_ca A B C X Hd Hs2 Hs1).
  - left. split; reflexivity.
Qed.

Lemma relint_not_vert : forall A B C P Q X,
  0 < cross A B C -> P <> Q -> vert_edge A B C P Q ->
  on_seg_open P Q X -> X <> A /\ X <> B /\ X <> C.
Proof.
  intros A B C P Q X Hd Hne He Ho.
  destruct (relint_not_ends P Q X Hne Ho) as [HnP HnQ].
  destruct He as [H|[H|H]]; destruct H as [[-> ->]|[-> ->]].
  - split; [exact HnP|]. split; [exact HnQ|]. intros ->.
    destruct Ho as [t [[Ht0 Ht1] Ht]].
    assert (cross A B C = 0).
    { rewrite Ht. apply on_seg_cross0. exists t. split; [lra| reflexivity]. }
    lra.
  - split; [exact HnQ|]. split; [exact HnP|]. intros ->.
    destruct Ho as [t [[Ht0 Ht1] Ht]].
    assert (Hz : cross B A C = 0).
    { rewrite Ht. apply on_seg_cross0. exists t. split; [lra| reflexivity]. }
    assert (cross B A C = - cross A B C) by (unfold cross; ring). lra.
  - split.
    + intros ->.
      destruct Ho as [t [[Ht0 Ht1] Ht]].
      assert (Hz : cross B C A = 0).
      { rewrite Ht. apply on_seg_cross0. exists t. split; [lra| reflexivity]. }
      assert (cross B C A = cross A B C) by (symmetry; apply (cross_cycle A B C)). lra.
    + split; [exact HnP| exact HnQ].
  - split.
    + intros ->.
      destruct Ho as [t [[Ht0 Ht1] Ht]].
      assert (Hz : cross C B A = 0).
      { rewrite Ht. apply on_seg_cross0. exists t. split; [lra| reflexivity]. }
      assert (cross C B A = - cross A B C) by (unfold cross; ring). lra.
    + split; [exact HnQ| exact HnP].
  - split; [exact HnQ|]. split.
    + intros ->.
      destruct Ho as [t [[Ht0 Ht1] Ht]].
      assert (Hz : cross C A B = 0).
      { rewrite Ht. apply on_seg_cross0. exists t. split; [lra| reflexivity]. }
      assert (cross C A B = cross A B C) by (symmetry; apply (cross_cycle2 A B C)). lra.
    + exact HnP.
  - split; [exact HnP|]. split.
    + intros ->.
      destruct Ho as [t [[Ht0 Ht1] Ht]].
      assert (Hz : cross A C B = 0).
      { rewrite Ht. apply on_seg_cross0. exists t. split; [lra| reflexivity]. }
      assert (cross A C B = - cross A B C) by (unfold cross; ring). lra.
    + exact HnQ.
Qed.

Lemma two_edges_at_vertex : forall A B C P Q R S X,
  0 < cross A B C ->
  vert_edge A B C P Q -> vert_edge A B C R S ->
  ~ edge_id P Q R S ->
  on_seg P Q X -> on_seg R S X ->
  X = A \/ X = B \/ X = C.
Proof.
  intros A B C P Q R S X Hd HeP HeR Hnid HsP HsR.
  destruct (canon_of_vert A B C P Q HeP) as [P1 [Q1 [HidP HcP]]].
  destruct (canon_of_vert A B C R S HeR) as [R1 [S1 [HidR HcR]]].
  assert (H1 : on_seg P1 Q1 X) by (apply (on_seg_of_id P Q P1 Q1 X); assumption).
  assert (H2 : on_seg R1 S1 X) by (apply (on_seg_of_id R S R1 S1 X); assumption).
  destruct (canon_meet A B C P1 Q1 R1 S1 X Hd HcP HcR H1 H2) as [[-> ->]|Hvert].
  - exfalso. apply Hnid.
    apply (edge_id_trans P Q R1 S1 R S HidP). apply edge_id_sym. exact HidR.
  - exact Hvert.
Qed.

Lemma same_edge_if_relint : forall A B C P Q R S X,
  0 < cross A B C -> P <> Q ->
  vert_edge A B C P Q -> on_seg_open P Q X ->
  vert_edge A B C R S -> on_seg R S X ->
  edge_id P Q R S.
Proof.
  intros A B C P Q R S X Hd Hne HeP Ho HeR Hs.
  destruct (edge_id_b P Q R S) eqn:Hid.
  - apply edge_id_b_true. exact Hid.
  - exfalso.
    assert (Hnid : ~ edge_id P Q R S) by (apply edge_id_b_false; exact Hid).
    assert (Hv : X = A \/ X = B \/ X = C).
    { apply (two_edges_at_vertex A B C P Q R S X Hd HeP HeR Hnid).
      - apply on_seg_open_seg. exact Ho.
      - exact Hs. }
    destruct (relint_not_vert A B C P Q X Hd Hne HeP Ho) as [nA Hrest].
    destruct Hrest as [nB nC].
    destruct Hv as [-> | [-> | ->]].
    + apply nA. reflexivity.
    + apply nB. reflexivity.
    + apply nC. reflexivity.
Qed.

Lemma rel_not_sem : forall A B C D E F P Q X,
  0 < cross A B C -> 0 < cross D E F ->
  P <> Q -> vert_edge A B C P Q -> on_seg_open P Q X ->
  on_bd D E F X -> ~ vert_edge D E F P Q ->
  ~ pair_sem A B C D E F.
Proof.
  intros A B C D E F P Q X HA HD Hne He Ho Hb Hmiss Hsem.
  destruct Hsem as [_ [Hempty|[Hedge|Hvtx]]].
  - apply Hempty. exists X. split.
    + apply (bd_of_edge A B C P Q X He). apply on_seg_open_seg. exact Ho.
    + exact Hb.
  - destruct Hedge as [R [S [_ [HeA [HeD Hex]]]]].
    assert (Hon : on_bd A B C X).
    { apply (bd_of_edge A B C P Q X He). apply on_seg_open_seg. exact Ho. }
    assert (Hs : on_seg R S X) by (apply (proj1 (Hex X)); split; assumption).
    assert (Hid : edge_id P Q R S).
    { apply (same_edge_if_relint A B C P Q R S X HA Hne He Ho HeA Hs). }
    apply Hmiss. apply (vert_edge_transfer D E F P Q R S Hid HeD).
  - destruct Hvtx as [V [Hva [_ [_ [_ Honly]]]]].
    assert (Hon : on_bd A B C X).
    { apply (bd_of_edge A B C P Q X He). apply on_seg_open_seg. exact Ho. }
    assert (EX : X = V) by (apply Honly; split; assumption).
    destruct (relint_not_vert A B C P Q X HA Hne He Ho) as [nA Hbc].
    destruct Hbc as [nB nC].
    destruct Hva as [Ea|[Eb|Ec]].
    + apply nA. rewrite <- Ea. exact EX.
    + apply nB. rewrite <- Eb. exact EX.
    + apply nC. rewrite <- Ec. exact EX.
Qed.

Lemma shared_not_bd_cells : forall ts X,
  (forall T, In T ts -> tri_pos T) -> tin_sem ts ->
  shared_rel ts X -> ~ tin_bd_cells ts X.
Proof.
  intros ts X Hpos Hsem [P [Q [Hpq [Hge Ho]]]] [R [S [_ [Hu Hs]]]].
  destruct (edge_id_b P Q R S) eqn:Hid.
  - apply edge_id_b_true in Hid.
    assert (Eu : edge_uses ts P Q = edge_uses ts R S).
    { apply edge_uses_id. exact Hid. }
    lia.
  - assert (Hnid : ~ edge_id P Q R S) by (apply edge_id_b_false; exact Hid).
    destruct (uses_eq1_owner ts R S Hu) as [W [HinW [HbW _]]].
    destruct (uses_ge1_owner ts P Q) as [T [HinT HbT]].
    { lia. }
    destruct (tri_edge_b W P Q) eqn:HWPQ.
    + destruct W as [[A B] C].
      apply tri_edge_b_true in HbW. simpl in HbW.
      apply tri_edge_b_true in HWPQ. simpl in HWPQ.
      assert (HA : 0 < cross A B C).
      { apply Hpos in HinW. simpl in HinW. exact HinW. }
      assert (Hv : X = A \/ X = B \/ X = C).
      { apply (two_edges_at_vertex A B C P Q R S X HA HWPQ HbW Hnid).
        - apply on_seg_open_seg. exact Ho.
        - exact Hs. }
      destruct (relint_not_vert A B C P Q X HA Hpq HWPQ Ho) as [nA Hbc].
      destruct Hbc as [nB nC].
      destruct Hv as [-> | [-> | ->]].
      * apply nA. reflexivity.
      * apply nB. reflexivity.
      * apply nC. reflexivity.
    + assert (Hneq : T <> W) by (intros Heq; subst T; congruence).
      assert (Hpair : tri_pair_sem T W).
      { destruct (tin_ordered_pair ts T W Hsem HinT HinW Hneq) as [HTW|HWT].
        - exact HTW.
        - apply tri_pair_sem_sym. exact HWT. }
      destruct T as [[A B] C], W as [[D E] F].
      apply tri_edge_b_true in HbT. simpl in HbT.
      apply tri_edge_b_true in HbW. simpl in HbW.
      assert (Hmiss : ~ vert_edge D E F P Q).
      { apply tri_edge_b_false. exact HWPQ. }
      assert (HA : 0 < cross A B C).
      { apply Hpos in HinT. simpl in HinT. exact HinT. }
      assert (HD : 0 < cross D E F).
      { apply Hpos in HinW. simpl in HinW. exact HinW. }
      simpl in Hpair.
      apply (rel_not_sem A B C D E F P Q X HA HD Hpq HbT Ho).
      * apply (bd_of_edge D E F R S X HbW Hs).
      * exact Hmiss.
      * exact Hpair.
Qed.

Lemma vert_on_bd : forall A B C X,
  X = A \/ X = B \/ X = C -> on_bd A B C X.
Proof.
  intros A B C X [-> | [-> | ->]].
  - left. apply (proj1 (seg_ends A B)).
  - left. apply (proj2 (seg_ends A B)).
  - right. left. apply (proj2 (seg_ends B C)).
Qed.

Lemma edge_not_once_ge2 : forall ts A B C P Q X,
  In ((A, B), C) ts -> vert_edge A B C P Q -> on_seg P Q X ->
  on_once_b ts X = false -> (2 <= edge_uses ts P Q)%nat.
Proof.
  intros ts A B C P Q X Hin He Hs Hon.
  assert (Hge : (1 <= edge_uses ts P Q)%nat).
  { apply uses_member with (T := ((A, B), C)).
    - exact Hin.
    - apply tri_edge_b_true. exact He. }
  destruct (Nat.eq_dec (edge_uses ts P Q) 1%nat) as [Heq|Hne].
  - exfalso.
    destruct (canon_of_vert A B C P Q He) as [R [S [Hid Hc]]].
    assert (Htrue : on_once_b ts X = true).
    { unfold on_once_b. apply (once_in_hit ts ts X ((A, B), C) Hin).
      apply existsb_exists. exists (R, S). split.
      - destruct Hc as [[-> ->]|[[-> ->]|[-> ->]]]; simpl; tauto.
      - unfold once_edge_b. simpl. apply andb_true_iff. split.
        + apply Nat.eqb_eq. rewrite <- (edge_uses_id ts P Q R S Hid). exact Heq.
        + apply on_seg_b_iff. apply (on_seg_of_id P Q R S X Hid Hs). }
    congruence.
  - lia.
Qed.

Lemma vert_of_eqb : forall A B C X,
  point_eqb X A || point_eqb X B || point_eqb X C = true ->
  X = A \/ X = B \/ X = C.
Proof.
  intros A B C X H. apply orb_true_iff in H. destruct H as [H|H].
  - apply orb_true_iff in H. destruct H as [H|H].
    + left. apply point_eqb_true. exact H.
    + right. left. apply point_eqb_true. exact H.
  - right. right. apply point_eqb_true. exact H.
Qed.

Lemma carrier_cover : forall ts X,
  (forall T, In T ts -> tri_pos T) -> tin_sem ts ->
  tin_carrier ts X -> tin_int_cells ts X \/ tin_bd_cells ts X.
Proof.
  intros ts X Hpos Hsem [T [Hin [Ho|Hb]]].
  - left. left. exists T. split; assumption.
  - destruct (on_once_b ts X) eqn:Hon.
    + right. apply on_once_bd_cells; assumption.
    + left. destruct T as [[A B] C].
      destruct (point_eqb X A || point_eqb X B || point_eqb X C) eqn:Hv.
      * right. right. split.
        -- exists ((A, B), C). split; [exact Hin|]. apply vert_of_eqb. exact Hv.
        -- apply not_once_not_bd_cells; assumption.
      * right. left.
        assert (HnA : X <> A).
        { intros ->. rewrite point_eqb_refl in Hv. simpl in Hv. discriminate. }
        assert (HnB : X <> B).
        { intros ->. rewrite point_eqb_refl in Hv. rewrite orb_true_r in Hv.
          simpl in Hv. discriminate. }
        assert (HnC : X <> C).
        { intros ->. rewrite point_eqb_refl in Hv. rewrite orb_true_r in Hv.
          simpl in Hv. discriminate. }
        assert (HposT : 0 < cross A B C).
        { apply Hpos in Hin. simpl in Hin. exact Hin. }
        destruct (edge_sep A B C HposT) as [Habn [Hbcn Hcan]].
        destruct Hb as [Hab|[Hbc|Hca]].
        -- exists A, B. split; [exact Habn|]. split.
           ++ apply (edge_not_once_ge2 ts A B C A B X Hin).
              ** left. left. split; reflexivity.
              ** exact Hab.
              ** exact Hon.
           ++ apply seg_open_of_not_end; assumption.
        -- exists B, C. split; [exact Hbcn|]. split.
           ++ apply (edge_not_once_ge2 ts A B C B C X Hin).
              ** right. left. left. split; reflexivity.
              ** exact Hbc.
              ** exact Hon.
           ++ apply seg_open_of_not_end; assumption.
        -- exists C, A. split; [exact Hcan|]. split.
           ++ apply (edge_not_once_ge2 ts A B C C A X Hin).
              ** right. right. left. split; reflexivity.
              ** exact Hca.
              ** exact Hon.
           ++ apply seg_open_of_not_end; assumption.
Qed.

Lemma int_cells_in_carrier : forall ts X,
  (forall T, In T ts -> tri_pos T) ->
  tin_int_cells ts X \/ tin_bd_cells ts X -> tin_carrier ts X.
Proof.
  intros ts X Hpos [Hint|Hbnd].
  - destruct Hint as [[T [Hin Ho]]|[Hs|Hi]].
    + exists T. split; [exact Hin|]. left. exact Ho.
    + destruct Hs as [P [Q [_ [Hge Ho]]]].
      destruct (uses_ge1_owner ts P Q) as [T [Hin Hb]].
      { lia. }
      destruct T as [[A B] C]. apply tri_edge_b_true in Hb. simpl in Hb.
      exists ((A, B), C). split; [exact Hin|]. right.
      apply (bd_of_edge A B C P Q X Hb). apply on_seg_open_seg. exact Ho.
    + destruct Hi as [[T [Hin Hv]] _].
      destruct T as [[A B] C]. exists ((A, B), C). split; [exact Hin|]. right.
      apply vert_on_bd. exact Hv.
  - destruct Hbnd as [P [Q [_ [Hu Hs]]]].
    destruct (uses_eq1_owner ts P Q Hu) as [T [Hin [Hb _]]].
    destruct T as [[A B] C]. apply tri_edge_b_true in Hb. simpl in Hb.
    exists ((A, B), C). split; [exact Hin|]. right.
    apply (bd_of_edge A B C P Q X Hb Hs).
Qed.

Theorem tin_surface : forall ts X,
  (forall T, In T ts -> tri_pos T) -> tin_sem ts ->
  (tin_carrier ts X <-> tin_int_cells ts X \/ tin_bd_cells ts X) /\
  ~ (tin_int_cells ts X /\ tin_bd_cells ts X).
Proof.
  intros ts X Hpos Hsem. split.
  - split.
    + intros Hc. apply carrier_cover; assumption.
    + intros H. apply int_cells_in_carrier; assumption.
  - intros [Hint Hbnd]. destruct Hint as [Ho|[Hs|Hi]].
    + apply (open_not_bd_cells ts X Hpos Hsem Ho Hbnd).
    + apply (shared_not_bd_cells ts X Hpos Hsem Hs Hbnd).
    + destruct Hi as [_ Hn]. contradiction.
Qed.

(* Fixtures. The centre fan of TrianglePairTin: four triangles of the
   unit square. The centre is an internal vertex. The base midpoint lies
   on a once-edge. The radius midpoint is a shared relative interior. *)

Ltac kill_eqb :=
  repeat match goal with
  | |- context [point_eqb ?a ?a] => rewrite (point_eqb_refl a)
  | |- context [point_eqb ?a ?b] =>
      rewrite (point_eqb_false_neq a b) by
        (apply pts_neq; first
           [ left; unfold fanSW, fanSE, fanNE, fanNW, fanC; simpl; lra
           | right; unfold fanSW, fanSE, fanNE, fanNW, fanC; simpl; lra ])
  end.

Ltac fan_b :=
  cbv [tri_edge_b vert_edge_b edge_id_b]; kill_eqb; simpl; reflexivity.

Lemma fan_uses_SWSE : edge_uses fan_ts fanSW fanSE = 1%nat.
Proof.
  unfold fan_ts.
  rewrite uses_cons_true by fan_b.
  rewrite uses_cons_false by fan_b.
  rewrite uses_cons_false by fan_b.
  rewrite uses_cons_false by fan_b.
  reflexivity.
Qed.

Lemma fan_uses_SEC : edge_uses fan_ts fanSE fanC = 2%nat.
Proof.
  unfold fan_ts.
  rewrite uses_cons_true by fan_b.
  rewrite uses_cons_true by fan_b.
  rewrite uses_cons_false by fan_b.
  rewrite uses_cons_false by fan_b.
  reflexivity.
Qed.

Lemma fan_uses_NEC : edge_uses fan_ts fanNE fanC = 2%nat.
Proof.
  unfold fan_ts.
  rewrite uses_cons_false by fan_b.
  rewrite uses_cons_true by fan_b.
  rewrite uses_cons_true by fan_b.
  rewrite uses_cons_false by fan_b.
  reflexivity.
Qed.

Lemma fan_uses_NWC : edge_uses fan_ts fanNW fanC = 2%nat.
Proof.
  unfold fan_ts.
  rewrite uses_cons_false by fan_b.
  rewrite uses_cons_false by fan_b.
  rewrite uses_cons_true by fan_b.
  rewrite uses_cons_true by fan_b.
  reflexivity.
Qed.

Lemma fan_uses_SWC : edge_uses fan_ts fanSW fanC = 2%nat.
Proof.
  unfold fan_ts.
  rewrite uses_cons_true by fan_b.
  rewrite uses_cons_false by fan_b.
  rewrite uses_cons_false by fan_b.
  rewrite uses_cons_true by fan_b.
  reflexivity.
Qed.

Lemma apex_off_base : forall A B C, 0 < cross A B C -> ~ on_seg A B C.
Proof.
  intros A B C Hd Hs. apply on_seg_cross0 in Hs. lra.
Qed.

Lemma fan_t0_centre_uses : forall P Q,
  vert_edge fanSW fanSE fanC P Q -> on_seg P Q fanC ->
  edge_uses fan_ts P Q = 2%nat.
Proof.
  intros P Q He Hs. destruct He as [H|[H|H]].
  - exfalso. apply (apex_off_base fanSW fanSE fanC).
    + unfold cross; simpl; lra.
    + apply (on_seg_of_id P Q fanSW fanSE fanC H Hs).
  - rewrite (edge_uses_id fan_ts P Q fanSE fanC H). exact fan_uses_SEC.
  - rewrite (edge_uses_id fan_ts P Q fanC fanSW H).
    rewrite (edge_uses_sym fan_ts fanC fanSW). exact fan_uses_SWC.
Qed.

Lemma fan_t1_centre_uses : forall P Q,
  vert_edge fanSE fanNE fanC P Q -> on_seg P Q fanC ->
  edge_uses fan_ts P Q = 2%nat.
Proof.
  intros P Q He Hs. destruct He as [H|[H|H]].
  - exfalso. apply (apex_off_base fanSE fanNE fanC).
    + unfold cross; simpl; lra.
    + apply (on_seg_of_id P Q fanSE fanNE fanC H Hs).
  - rewrite (edge_uses_id fan_ts P Q fanNE fanC H). exact fan_uses_NEC.
  - rewrite (edge_uses_id fan_ts P Q fanC fanSE H).
    rewrite (edge_uses_sym fan_ts fanC fanSE). exact fan_uses_SEC.
Qed.

Lemma fan_t2_centre_uses : forall P Q,
  vert_edge fanNE fanNW fanC P Q -> on_seg P Q fanC ->
  edge_uses fan_ts P Q = 2%nat.
Proof.
  intros P Q He Hs. destruct He as [H|[H|H]].
  - exfalso. apply (apex_off_base fanNE fanNW fanC).
    + unfold cross; simpl; lra.
    + apply (on_seg_of_id P Q fanNE fanNW fanC H Hs).
  - rewrite (edge_uses_id fan_ts P Q fanNW fanC H). exact fan_uses_NWC.
  - rewrite (edge_uses_id fan_ts P Q fanC fanNE H).
    rewrite (edge_uses_sym fan_ts fanC fanNE). exact fan_uses_NEC.
Qed.

Lemma fan_t3_centre_uses : forall P Q,
  vert_edge fanNW fanSW fanC P Q -> on_seg P Q fanC ->
  edge_uses fan_ts P Q = 2%nat.
Proof.
  intros P Q He Hs. destruct He as [H|[H|H]].
  - exfalso. apply (apex_off_base fanNW fanSW fanC).
    + unfold cross; simpl; lra.
    + apply (on_seg_of_id P Q fanNW fanSW fanC H Hs).
  - rewrite (edge_uses_id fan_ts P Q fanSW fanC H). exact fan_uses_SWC.
  - rewrite (edge_uses_id fan_ts P Q fanC fanNW H).
    rewrite (edge_uses_sym fan_ts fanC fanNW). exact fan_uses_NWC.
Qed.

Lemma fan_centre_not_bd_cells : ~ tin_bd_cells fan_ts fanC.
Proof.
  intros [P [Q [_ [Hu Hs]]]].
  destruct (uses_eq1_owner fan_ts P Q Hu) as [T [Hin [Hb _]]].
  simpl in Hin. destruct Hin as [<- | [<- | [<- | [<- | []]]]].
  - apply tri_edge_b_true in Hb. simpl in Hb.
    assert (H2 : edge_uses fan_ts P Q = 2%nat).
    { apply fan_t0_centre_uses; assumption. }
    lia.
  - apply tri_edge_b_true in Hb. simpl in Hb.
    assert (H2 : edge_uses fan_ts P Q = 2%nat).
    { apply fan_t1_centre_uses; assumption. }
    lia.
  - apply tri_edge_b_true in Hb. simpl in Hb.
    assert (H2 : edge_uses fan_ts P Q = 2%nat).
    { apply fan_t2_centre_uses; assumption. }
    lia.
  - apply tri_edge_b_true in Hb. simpl in Hb.
    assert (H2 : edge_uses fan_ts P Q = 2%nat).
    { apply fan_t3_centre_uses; assumption. }
    lia.
Qed.

Lemma fan_centre_int_cells_fixtures : tin_int_cells fan_ts fanC.
Proof.
  right. right. split.
  - exists ((fanSW, fanSE), fanC). split.
    + unfold fan_ts. simpl. left. reflexivity.
    + right. right. reflexivity.
  - exact fan_centre_not_bd_cells.
Qed.

Definition fan_base : Point := mkPoint (1 / 2) 0.

Lemma fan_base_bd_cells_fixtures : tin_bd_cells fan_ts fan_base.
Proof.
  exists fanSW, fanSE. split.
  - apply pts_neq. left. unfold fanSW, fanSE. simpl. lra.
  - split.
    + exact fan_uses_SWSE.
    + exists (1 / 2). split; [lra|].
      unfold convex_combination, fanSW, fanSE, fan_base. simpl. f_equal; lra.
Qed.

Definition fan_rad : Point := mkPoint (3 / 4) (1 / 4).

Lemma fan_radius_int_cells_fixtures : tin_int_cells fan_ts fan_rad.
Proof.
  right. left. exists fanSE, fanC. split.
  - apply pts_neq. left. unfold fanSE, fanC. simpl. lra.
  - split.
    + rewrite fan_uses_SEC. lia.
    + exists (1 / 2). split; [lra|].
      unfold convex_combination, fanSE, fanC, fan_rad. simpl. f_equal; lra.
Qed.

Lemma fan_tri_pos : forall T, In T fan_ts -> tri_pos T.
Proof.
  intros T Hin. simpl in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; unfold tri_pos, cross; simpl; lra.
Qed.

Lemma fan_partition : forall X,
  (tin_carrier fan_ts X <-> tin_int_cells fan_ts X \/ tin_bd_cells fan_ts X) /\
  ~ (tin_int_cells fan_ts X /\ tin_bd_cells fan_ts X).
Proof.
  intros X. apply tin_surface.
  - exact fan_tri_pos.
  - exact (proj1 tin_fan).
Qed.

Print Assumptions edge_id_b_true.
Print Assumptions edge_id_b_false.
Print Assumptions vert_edge_b_true.
Print Assumptions tri_edge_b_true.
Print Assumptions tri_edge_b_false.
Print Assumptions edge_id_sym.
Print Assumptions edge_id_trans.
Print Assumptions on_seg_of_id.
Print Assumptions vert_edge_transfer.
Print Assumptions canon_of_vert.
Print Assumptions bd_of_edge.
Print Assumptions edge_uses_id.
Print Assumptions edge_uses_sym.
Print Assumptions uses_cons_true.
Print Assumptions uses_cons_false.
Print Assumptions uses_member.
Print Assumptions uses_ge1_owner.
Print Assumptions uses_eq1_owner.
Print Assumptions once_in_true.
Print Assumptions once_in_hit.
Print Assumptions on_once_bd_cells.
Print Assumptions bd_cells_on_once.
Print Assumptions not_once_not_bd_cells.
Print Assumptions tri_open_not_bd.
Print Assumptions open_misses_bd.
Print Assumptions tri_eqb_true.
Print Assumptions tri_eqb_false_inv.
Print Assumptions pair_edge_sym.
Print Assumptions pair_vtx_sym.
Print Assumptions pair_sem_sym.
Print Assumptions tri_pair_sem_sym.
Print Assumptions tin_ordered_pair.
Print Assumptions open_vs_bd.
Print Assumptions open_not_bd_cells.
Print Assumptions combo_eq_left.
Print Assumptions combo_eq_right.
Print Assumptions on_seg_open_seg.
Print Assumptions seg_open_of_not_end.
Print Assumptions relint_not_ends.
Print Assumptions seg_ab_bc.
Print Assumptions seg_ab_ca.
Print Assumptions seg_bc_ca.
Print Assumptions canon_meet.
Print Assumptions relint_not_vert.
Print Assumptions two_edges_at_vertex.
Print Assumptions same_edge_if_relint.
Print Assumptions rel_not_sem.
Print Assumptions shared_not_bd_cells.
Print Assumptions vert_on_bd.
Print Assumptions edge_not_once_ge2.
Print Assumptions vert_of_eqb.
Print Assumptions carrier_cover.
Print Assumptions int_cells_in_carrier.
Print Assumptions tin_surface.
Print Assumptions fan_uses_SWSE.
Print Assumptions fan_uses_SEC.
Print Assumptions fan_uses_NEC.
Print Assumptions fan_uses_NWC.
Print Assumptions fan_uses_SWC.
Print Assumptions apex_off_base.
Print Assumptions fan_t0_centre_uses.
Print Assumptions fan_t1_centre_uses.
Print Assumptions fan_t2_centre_uses.
Print Assumptions fan_t3_centre_uses.
Print Assumptions fan_centre_not_bd_cells.
Print Assumptions fan_centre_int_cells_fixtures.
Print Assumptions fan_base_bd_cells_fixtures.
Print Assumptions fan_radius_int_cells_fixtures.
Print Assumptions fan_tri_pos.
Print Assumptions fan_partition.
