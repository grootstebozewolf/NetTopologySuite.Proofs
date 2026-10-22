(* NetTopologySuite.Proofs.TrianglePairTinRelate2
   Remaining TIN x triangle DE-9IM cells, against the metric interior
   and boundary (tin_interior_eq / tin_boundary_eq). A is the TIN, B the
   CCW query. II stays in TrianglePairTinRelate. Each cell is a
   nonemptiness characterization; no assembled nine-cell tin_de9im here.
   IB: metric interior meets the query boundary. The open-triangle arm
   is ib_entry = Dim1; a shared edge or an internal vertex can meet the
   query boundary without being tri_open.
   BI / BB: metric boundary, i.e. a once-edge (edge_uses = 1), meets the
   query interior or the query boundary. Not the disjunction of the
   triangles' bi_entry / bb_entry: an internal edge is metric interior.
   BB Dim1 is a positive once-edge subsegment lying on a query edge.
   IE: metric interior meets the query exterior. The open arm is
   ie_entry = Dim2; shared-edge and internal-vertex arms stay.
   BE: a positive once-edge subsegment lies outside the closed query.
   EI / EB: the query interior, or a positive query-boundary subsegment,
   misses the carrier, hence misses both the metric interior and the
   metric boundary.
   EE: a point lies outside the carrier and outside the query.
   Fixtures: fan_inside_relate_fixtures, fan_cross_relate_fixtures,
   fan_touch_centre_relate_fixtures, fan_edge_relate_fixtures,
   fan_disjoint_relate_fixtures.
   topic: relate
   claimId: tri-de9im-t6
   witness: tin_query_ib
   3-axiom host. No Admitted. No Jordan.
   AI-drafted (Cursor Grok 4.7).
   License: BSD-3-Clause *)
From Stdlib Require Import Reals Lra Lia List Bool.
Import ListNotations.
From NTS.Proofs Require Import Distance Orientation Convex ConvexClip
  DE9IM TrianglePairCommon TrianglePairClip TrianglePairEdge
  TrianglePairBound TrianglePairExterior TrianglePairTin
  TrianglePairTinSurface TrianglePairTinRelate TinSurfaceTopo
  TinSurfaceVertex.
Local Open Scope R_scope.

Lemma valid_sem : forall ts,
  (forall T, In T ts -> tri_pos T) -> tin_im ts -> tin_sem ts.
Proof.
  intros ts Hpos Him. apply (proj2 (tin_valid_iff ts Hpos)). exact Him.
Qed.

Definition tri_ib (T : Tri) (D E F : Point) : DimValue :=
  match T with ((A, B), C) => ib_entry A B C D E F end.

Definition tri_ie (T : Tri) (D E F : Point) : DimValue :=
  match T with ((A, B), C) => ie_entry A B C D E F end.

Lemma tri_ib_dim1_iff : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  tri_ib ((A, B), C) D E F = Dim1 <->
  exists X, tri_open A B C X /\ on_bd D E F X.
Proof.
  intros A B C D E F HA HD. unfold tri_ib. apply ib_cell_iff; assumption.
Qed.

Lemma tri_ie_dim2_iff : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  tri_ie ((A, B), C) D E F = Dim2 <->
  exists X, tri_open A B C X /\ ~ in_tri D E F X.
Proof.
  intros A B C D E F HA HD. unfold tri_ie. apply ie_open_iff; assumption.
Qed.

Theorem tin_query_ib : forall ts D E F,
  (forall T, In T ts -> tri_pos T) -> tin_im ts -> 0 < cross D E F ->
  (exists X, interior_pt (tin_carrier ts) X /\ on_bd D E F X) <->
  (exists T, In T ts /\ tri_ib T D E F = Dim1) \/
  (exists X, shared_rel ts X /\ on_bd D E F X) \/
  (exists X, internal_vert ts X /\ on_bd D E F X).
Proof.
  intros ts D E F Hpos Him HD.
  assert (Hsem : tin_sem ts) by (apply valid_sem; assumption). split.
  - intros [X [Hint Hb]].
    apply (proj1 (tin_interior_eq ts X Hpos Hsem)) in Hint.
    destruct Hint as [[T [Hin Ho]]|[Hs|Hv]].
    + left. exists T. split; [exact Hin|].
      destruct T as [[A B] C]. apply tri_ib_dim1_iff.
      * apply Hpos in Hin. simpl in Hin. exact Hin.
      * exact HD.
      * exists X. split; assumption.
    + right. left. exists X. split; assumption.
    + right. right. exists X. split; assumption.
  - intros [Hopen|[Hs|Hv]].
    + destruct Hopen as [T [Hin Hib]].
      destruct T as [[A B] C].
      apply tri_ib_dim1_iff in Hib.
      * destruct Hib as [X [Ho Hb]]. exists X. split; [| exact Hb].
        apply (proj2 (tin_interior_eq ts X Hpos Hsem)).
        left. exists ((A, B), C). split; assumption.
      * apply Hpos in Hin. simpl in Hin. exact Hin.
      * exact HD.
    + destruct Hs as [X [Hs Hb]]. exists X. split; [| exact Hb].
      apply (proj2 (tin_interior_eq ts X Hpos Hsem)). right. left. exact Hs.
    + destruct Hv as [X [Hv Hb]]. exists X. split; [| exact Hb].
      apply (proj2 (tin_interior_eq ts X Hpos Hsem)). right. right. exact Hv.
Qed.

Theorem tin_query_bi : forall ts D E F,
  (forall T, In T ts -> tri_pos T) -> tin_im ts -> 0 < cross D E F ->
  (exists X, boundary_pt (tin_carrier ts) X /\ tri_open D E F X) <->
  (exists P Q X, P <> Q /\ edge_uses ts P Q = 1%nat /\
     on_seg P Q X /\ tri_open D E F X).
Proof.
  intros ts D E F Hpos Him HD.
  assert (Hsem : tin_sem ts) by (apply valid_sem; assumption). split.
  - intros [X [Hb Ho]].
    apply (proj1 (tin_boundary_eq ts X Hpos Hsem)) in Hb.
    destruct Hb as [P [Q [Hne [Hu Hs]]]].
    exists P, Q, X. split; [exact Hne|]. split; [exact Hu|]. split; [exact Hs| exact Ho].
  - intros [P [Q [X [Hne [Hu [Hs Ho]]]]]]. exists X. split; [| exact Ho].
    apply (proj2 (tin_boundary_eq ts X Hpos Hsem)).
    exists P, Q. split; [exact Hne|]. split; [exact Hu| exact Hs].
Qed.

Theorem tin_query_bb : forall ts D E F,
  (forall T, In T ts -> tri_pos T) -> tin_im ts ->
  (exists X, boundary_pt (tin_carrier ts) X /\ on_bd D E F X) <->
  (exists P Q X, P <> Q /\ edge_uses ts P Q = 1%nat /\
     on_seg P Q X /\ on_bd D E F X).
Proof.
  intros ts D E F Hpos Him.
  assert (Hsem : tin_sem ts) by (apply valid_sem; assumption). split.
  - intros [X [Hb Ho]].
    apply (proj1 (tin_boundary_eq ts X Hpos Hsem)) in Hb.
    destruct Hb as [P [Q [Hne [Hu Hs]]]].
    exists P, Q, X. split; [exact Hne|]. split; [exact Hu|]. split; [exact Hs| exact Ho].
  - intros [P [Q [X [Hne [Hu [Hs Ho]]]]]]. exists X. split; [| exact Ho].
    apply (proj2 (tin_boundary_eq ts X Hpos Hsem)).
    exists P, Q. split; [exact Hne|]. split; [exact Hu| exact Hs].
Qed.

Theorem tin_query_bb_dim1 : forall ts D E F P Q,
  (forall T, In T ts -> tri_pos T) -> tin_im ts -> P <> Q ->
  (exists U V, U <> V /\ edge_uses ts U V = 1%nat /\
     (forall X, on_seg P Q X -> on_seg U V X)) ->
  (forall X, on_seg P Q X -> on_bd D E F X) <->
  (forall X, on_seg P Q X ->
     boundary_pt (tin_carrier ts) X /\ on_bd D E F X).
Proof.
  intros ts D E F P Q Hpos Him Hne [U [V [Huv [Hu Hsub]]]].
  assert (Hsem : tin_sem ts) by (apply valid_sem; assumption). split.
  - intros Hall X Hs. split; [| apply Hall; exact Hs].
    apply (proj2 (tin_boundary_eq ts X Hpos Hsem)).
    exists U, V. repeat split; [exact Huv | exact Hu | apply Hsub; exact Hs].
  - intros Hall X Hs. destruct (Hall X Hs) as [_ Ho]. exact Ho.
Qed.

Theorem tin_query_ie : forall ts D E F,
  (forall T, In T ts -> tri_pos T) -> tin_im ts -> 0 < cross D E F ->
  (exists X, interior_pt (tin_carrier ts) X /\ ~ in_tri D E F X) <->
  (exists T, In T ts /\ tri_ie T D E F = Dim2) \/
  (exists X, shared_rel ts X /\ ~ in_tri D E F X) \/
  (exists X, internal_vert ts X /\ ~ in_tri D E F X).
Proof.
  intros ts D E F Hpos Him HD.
  assert (Hsem : tin_sem ts) by (apply valid_sem; assumption). split.
  - intros [X [Hint Hout]].
    apply (proj1 (tin_interior_eq ts X Hpos Hsem)) in Hint.
    destruct Hint as [[T [Hin Ho]]|[Hs|Hv]].
    + left. exists T. split; [exact Hin|].
      destruct T as [[A B] C]. apply tri_ie_dim2_iff.
      * apply Hpos in Hin. simpl in Hin. exact Hin.
      * exact HD.
      * exists X. split; assumption.
    + right. left. exists X. split; assumption.
    + right. right. exists X. split; assumption.
  - intros [Hopen|[Hs|Hv]].
    + destruct Hopen as [T [Hin Hie]].
      destruct T as [[A B] C].
      apply tri_ie_dim2_iff in Hie.
      * destruct Hie as [X [Ho Hout]]. exists X. split; [| exact Hout].
        apply (proj2 (tin_interior_eq ts X Hpos Hsem)).
        left. exists ((A, B), C). split; assumption.
      * apply Hpos in Hin. simpl in Hin. exact Hin.
      * exact HD.
    + destruct Hs as [X [Hs Hout]]. exists X. split; [| exact Hout].
      apply (proj2 (tin_interior_eq ts X Hpos Hsem)). right. left. exact Hs.
    + destruct Hv as [X [Hv Hout]]. exists X. split; [| exact Hout].
      apply (proj2 (tin_interior_eq ts X Hpos Hsem)). right. right. exact Hv.
Qed.

Theorem tin_query_be : forall ts D E F P Q,
  (forall T, In T ts -> tri_pos T) -> tin_im ts -> P <> Q ->
  (exists U V, U <> V /\ edge_uses ts U V = 1%nat /\
     (forall X, on_seg P Q X -> on_seg U V X)) ->
  (forall X, on_seg P Q X -> ~ in_tri D E F X) <->
  (forall X, on_seg P Q X ->
     boundary_pt (tin_carrier ts) X /\ ~ in_tri D E F X).
Proof.
  intros ts D E F P Q Hpos Him Hne [U [V [Huv [Hu Hsub]]]].
  assert (Hsem : tin_sem ts) by (apply valid_sem; assumption). split.
  - intros Hall X Hs. split; [| apply Hall; exact Hs].
    apply (proj2 (tin_boundary_eq ts X Hpos Hsem)).
    exists U, V. repeat split; [exact Huv | exact Hu | apply Hsub; exact Hs].
  - intros Hall X Hs. destruct (Hall X Hs) as [_ Ho]. exact Ho.
Qed.

Lemma carrier_closed_metric : forall ts X,
  (forall T, In T ts -> tri_pos T) -> tin_sem ts ->
  (~ tin_carrier ts X <->
     ~ interior_pt (tin_carrier ts) X /\ ~ boundary_pt (tin_carrier ts) X).
Proof.
  intros ts X Hpos Hsem. split.
  - intros Hc. split.
    + intros Hi. apply Hc. apply interior_in. exact Hi.
    + intros Hb. apply Hc. apply boundary_in_carrier; assumption.
  - intros [Hi Hb] Hc.
    destruct (proj1 (proj1 (tin_surface ts X Hpos Hsem)) Hc) as [Hint|Hbd].
    + apply Hi. apply (proj2 (tin_interior_eq ts X Hpos Hsem)). exact Hint.
    + apply Hb. apply (proj2 (tin_boundary_eq ts X Hpos Hsem)). exact Hbd.
Qed.

Theorem tin_query_ei : forall ts D E F,
  (forall T, In T ts -> tri_pos T) -> tin_im ts -> 0 < cross D E F ->
  (exists X, tri_open D E F X /\ ~ tin_carrier ts X) <->
  (exists X, tri_open D E F X /\
     ~ interior_pt (tin_carrier ts) X /\ ~ boundary_pt (tin_carrier ts) X).
Proof.
  intros ts D E F Hpos Him HD.
  assert (Hsem : tin_sem ts) by (apply valid_sem; assumption). split.
  - intros [X [Ho Hc]]. exists X. split; [exact Ho|].
    apply carrier_closed_metric; assumption.
  - intros [X [Ho Hm]]. exists X. split; [exact Ho|].
    apply carrier_closed_metric; assumption.
Qed.

Theorem tin_query_eb : forall ts D E F P Q,
  (forall T, In T ts -> tri_pos T) -> tin_im ts -> P <> Q ->
  (exists e, In e (e3 D E F) /\
     (forall X, on_seg P Q X -> on_seg (fst e) (snd e) X)) ->
  (forall X, on_seg P Q X -> ~ tin_carrier ts X) <->
  (forall X, on_seg P Q X ->
     ~ interior_pt (tin_carrier ts) X /\ ~ boundary_pt (tin_carrier ts) X).
Proof.
  intros ts D E F P Q Hpos Him Hne He.
  assert (Hsem : tin_sem ts) by (apply valid_sem; assumption). split.
  - intros Hall X Hs. apply carrier_closed_metric; [assumption | assumption |].
    apply Hall. exact Hs.
  - intros Hall X Hs.
    apply carrier_closed_metric; [assumption | assumption | apply Hall; exact Hs].
Qed.

Fixpoint px_span (ts : list Tri) : R :=
  match ts with
  | [] => 0
  | ((A, B), C) :: rest =>
      Rmax (px A) (Rmax (px B) (Rmax (px C) (px_span rest)))
  end.

Lemma rmax3_le : forall a b c s,
  a <= s -> b <= s -> c <= s -> Rmax a (Rmax b c) <= s.
Proof.
  intros a b c s Ha Hb Hc.
  apply Rmax_lub; [exact Ha|]. apply Rmax_lub; assumption.
Qed.

Lemma span_verts : forall ts A B C,
  In ((A, B), C) ts ->
  px A <= px_span ts /\ px B <= px_span ts /\ px C <= px_span ts.
Proof.
  induction ts as [|T rest IH]; intros A B C Hin; [contradiction|].
  destruct T as [[U V] W]. simpl in Hin. destruct Hin as [Heq|Hin].
  - injection Heq as -> -> ->. simpl. split; [| split].
    + apply Rmax_l.
    + apply Rle_trans with (r2 := Rmax (px B) (Rmax (px C) (px_span rest))).
      * apply Rmax_l.
      * apply Rmax_r.
    + apply Rle_trans with (r2 := Rmax (px C) (px_span rest)).
      * apply Rmax_l.
      * apply Rle_trans with
          (r2 := Rmax (px B) (Rmax (px C) (px_span rest)));
          [apply Rmax_r | apply Rmax_r].
  - destruct (IH A B C Hin) as [Ha [Hb Hc]]. simpl.
    assert (Hs : px_span rest <=
      Rmax (px U) (Rmax (px V) (Rmax (px W) (px_span rest)))).
    { apply Rle_trans with (r2 := Rmax (px W) (px_span rest)).
      - apply Rmax_r.
      - apply Rle_trans with (r2 := Rmax (px V) (Rmax (px W) (px_span rest))).
        + apply Rmax_r.
        + apply Rmax_r. }
    split; [| split]; (apply Rle_trans with (r2 := px_span rest); [assumption | exact Hs]).
Qed.

Lemma carrier_px_le : forall ts X,
  (forall T, In T ts -> tri_pos T) ->
  tin_carrier ts X -> px X <= px_span ts.
Proof.
  intros ts X Hpos [T [Hin HT]]. destruct T as [[A B] C].
  assert (Htri : in_tri A B C X).
  { destruct HT as [Ho|Hb].
    - apply tri_open_in.
      + apply Hpos in Hin. simpl in Hin. exact Hin.
      + exact Ho.
    - apply on_bd_in_tri. exact Hb. }
  apply Rle_trans with (r2 := Rmax (px A) (Rmax (px B) (px C))).
  - apply px_in_tri_le. exact Htri.
  - destruct (span_verts ts A B C Hin) as [Ha [Hb Hc]].
    apply rmax3_le; assumption.
Qed.

Theorem tin_query_ee : forall ts D E F,
  (forall T, In T ts -> tri_pos T) -> tin_im ts ->
  exists X, ~ tin_carrier ts X /\ ~ in_tri D E F X /\
    ~ interior_pt (tin_carrier ts) X /\ ~ boundary_pt (tin_carrier ts) X.
Proof.
  intros ts D E F Hpos Him.
  assert (Hsem : tin_sem ts) by (apply valid_sem; assumption).
  set (q := Rmax (px D) (Rmax (px E) (px F))).
  set (far := Rmax (px_span ts) q + 1).
  set (X := mkPoint far 0).
  assert (Hs : px_span ts < far).
  { assert (Hle : px_span ts <= Rmax (px_span ts) q) by apply Rmax_l.
    unfold far. lra. }
  assert (Hq : q < far).
  { assert (Hle : q <= Rmax (px_span ts) q) by apply Rmax_r.
    unfold far. lra. }
  assert (Hout : ~ tin_carrier ts X).
  { intros Hc. apply (Rlt_not_le far (px_span ts) Hs).
    replace far with (px X) by reflexivity.
    apply carrier_px_le; assumption. }
  exists X. split; [| split; [| split]].
  - exact Hout.
  - intros Hin. apply (Rlt_not_le far q Hq).
    replace far with (px X) by reflexivity.
    apply Rle_trans with (r2 := q).
    + apply px_in_tri_le. exact Hin.
    + unfold q. apply Rle_refl.
  - intros Hi. apply Hout. apply interior_in. exact Hi.
  - intros Hb. apply Hout. apply boundary_in_carrier; assumption.
Qed.

(* Samples on the centre fan. inA/inB/inC, crA/crB/crC, tcB/tcC and
   djA/djB/djC are reused from TrianglePairTinRelate. *)

Definition inM : Point := mkPoint (3 / 8) (1 / 16).

Lemma fan_inside_relate_fixtures :
  interior_pt (tin_carrier fan_ts) inM /\ on_bd inA inB inC inM /\
  interior_pt (tin_carrier fan_ts) fanC /\ ~ in_tri inA inB inC fanC.
Proof.
  assert (Hsem : tin_sem fan_ts) by exact (proj1 tin_fan).
  split; [| split; [| split]].
  - apply (proj2 (tin_interior_eq fan_ts inM fan_tri_pos Hsem)).
    left. exists ((fanSW, fanSE), fanC). split.
    + unfold fan_ts. simpl. left. reflexivity.
    + unfold open_of, tri_open, cross, fanSW, fanSE, fanC, inM.
      simpl. repeat split; lra.
  - left. exists (1 / 2). split; [lra|].
    unfold convex_combination, inA, inB, inM. simpl. f_equal; lra.
  - apply (proj2 (tin_interior_eq fan_ts fanC fan_tri_pos Hsem)).
    exact fan_centre_int_cells_fixtures.
  - apply out_of_cross.
    + unfold cross, inA, inB, inC. simpl. lra.
    + right. left. unfold cross, inA, inB, inC, fanC. simpl. lra.
Qed.

Definition crM : Point := mkPoint (2 / 5) (1 / 20).
Definition crE : Point := mkPoint (1 / 2) 0.

Lemma fan_cross_relate_fixtures :
  interior_pt (tin_carrier fan_ts) crM /\ on_bd crA crB crC crM /\
  boundary_pt (tin_carrier fan_ts) crE /\ tri_open crA crB crC crE.
Proof.
  assert (Hsem : tin_sem fan_ts) by exact (proj1 tin_fan).
  split; [| split; [| split]].
  - apply (proj2 (tin_interior_eq fan_ts crM fan_tri_pos Hsem)).
    left. exists ((fanSW, fanSE), fanC). split.
    + unfold fan_ts. simpl. left. reflexivity.
    + unfold open_of, tri_open, cross, fanSW, fanSE, fanC, crM.
      simpl. repeat split; lra.
  - right. right. apply on_seg_sym. exists (3 / 5). split; [lra|].
    unfold convex_combination, crA, crC, crM. simpl. f_equal; lra.
  - apply (proj2 (tin_boundary_eq fan_ts crE fan_tri_pos Hsem)).
    exists fanSW, fanSE. split.
    + apply pts_neq. left. unfold fanSW, fanSE. simpl. lra.
    + split; [exact fan_uses_SWSE|]. exists (1 / 2). split; [lra|].
      unfold convex_combination, fanSW, fanSE, crE. simpl. f_equal; lra.
  - unfold tri_open, cross, crA, crB, crC, crE. simpl. repeat split; lra.
Qed.

Lemma fan_touch_centre_relate_fixtures :
  interior_pt (tin_carrier fan_ts) fanC /\ on_bd fanC tcB tcC fanC /\
  ~ tri_open fanC tcB tcC fanC.
Proof.
  assert (Hsem : tin_sem fan_ts) by exact (proj1 tin_fan).
  split; [| split].
  - apply (proj2 (tin_interior_eq fan_ts fanC fan_tri_pos Hsem)).
    exact fan_centre_int_cells_fixtures.
  - left. exact (proj1 (seg_ends fanC tcB)).
  - intros [Hz _]. unfold cross, fanC, tcB in Hz. simpl in Hz. lra.
Qed.

Definition esB : Point := mkPoint (1 / 2) (- (1)).

Lemma fan_edge_relate_fixtures :
  edge_uses fan_ts fanSW fanSE = 1%nat /\
  (forall X, on_seg fanSW fanSE X -> on_bd fanSW esB fanSE X) /\
  boundary_pt (tin_carrier fan_ts) fan_base /\ on_bd fanSW esB fanSE fan_base.
Proof.
  assert (Hsem : tin_sem fan_ts) by exact (proj1 tin_fan).
  split; [| split; [| split]].
  - exact fan_uses_SWSE.
  - intros X Hs. right. right. apply on_seg_sym. exact Hs.
  - apply (proj2 (tin_boundary_eq fan_ts fan_base fan_tri_pos Hsem)).
    exact fan_base_bd_cells_fixtures.
  - right. right. apply on_seg_sym.
    exists (1 / 2). split; [lra|].
    unfold convex_combination, fanSW, fanSE, fan_base. simpl. f_equal; lra.
Qed.

Definition djP : Point := mkPoint (10 / 3) (10 / 3).
Definition djM : Point := mkPoint (7 / 2) 3.
Definition eeP : Point := mkPoint 5 0.

Lemma fan_low_out : forall X, py X < 3 -> ~ in_tri djA djB djC X.
Proof.
  intros X Hy. apply out_of_cross.
  - unfold cross, djA, djB, djC. simpl. lra.
  - left. unfold cross, djA, djB. simpl. lra.
Qed.

Lemma fan_corner_px : forall T, In T fan_ts ->
  match T with
  | ((A, B), C) => px A <= 1 /\ px B <= 1 /\ px C <= 1
  end.
Proof.
  intros T Hin. simpl in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
    unfold fanSW, fanSE, fanNE, fanNW, fanC; simpl; lra.
Qed.

Lemma fan_px_out : forall X, 1 < px X -> ~ tin_carrier fan_ts X.
Proof.
  intros X Hx [T [Hin HT]]. destruct T as [[A B] C].
  destruct (fan_corner_px ((A, B), C) Hin) as [Ha [Hb Hc]].
  assert (Htri : in_tri A B C X).
  { destruct HT as [Ho|Hbd].
    - apply tri_open_in.
      + apply fan_tri_pos in Hin. simpl in Hin. exact Hin.
      + exact Ho.
    - apply on_bd_in_tri. exact Hbd. }
  assert (Hle : px X <= 1).
  { apply Rle_trans with (r2 := Rmax (px A) (Rmax (px B) (px C))).
    - apply px_in_tri_le. exact Htri.
    - apply rmax3_le; assumption. }
  exact (Rlt_not_le (px X) 1 Hx Hle).
Qed.

Lemma fan_disjoint_relate_fixtures :
  interior_pt (tin_carrier fan_ts) fanC /\ ~ in_tri djA djB djC fanC /\
  boundary_pt (tin_carrier fan_ts) fan_base /\ ~ in_tri djA djB djC fan_base /\
  tri_open djA djB djC djP /\ ~ tin_carrier fan_ts djP /\
  on_bd djA djB djC djM /\ ~ tin_carrier fan_ts djM /\
  ~ tin_carrier fan_ts eeP /\ ~ in_tri djA djB djC eeP.
Proof.
  assert (Hsem : tin_sem fan_ts) by exact (proj1 tin_fan).
  split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
  - apply (proj2 (tin_interior_eq fan_ts fanC fan_tri_pos Hsem)).
    exact fan_centre_int_cells_fixtures.
  - apply fan_low_out. unfold fanC. simpl. lra.
  - apply (proj2 (tin_boundary_eq fan_ts fan_base fan_tri_pos Hsem)).
    exact fan_base_bd_cells_fixtures.
  - apply fan_low_out. unfold fan_base. simpl. lra.
  - unfold tri_open, cross, djA, djB, djC, djP. simpl. repeat split; lra.
  - apply fan_px_out. unfold djP. simpl. lra.
  - left. exists (1 / 2). split; [lra|].
    unfold convex_combination, djA, djB, djM. simpl. f_equal; lra.
  - apply fan_px_out. unfold djM. simpl. lra.
  - apply fan_px_out. unfold eeP. simpl. lra.
  - apply fan_low_out. unfold eeP. simpl. lra.
Qed.

Print Assumptions valid_sem.
Print Assumptions tri_ib.
Print Assumptions tri_ie.
Print Assumptions tri_ib_dim1_iff.
Print Assumptions tri_ie_dim2_iff.
Print Assumptions tin_query_ib.
Print Assumptions tin_query_bi.
Print Assumptions tin_query_bb.
Print Assumptions tin_query_bb_dim1.
Print Assumptions tin_query_ie.
Print Assumptions tin_query_be.
Print Assumptions carrier_closed_metric.
Print Assumptions tin_query_ei.
Print Assumptions tin_query_eb.
Print Assumptions px_span.
Print Assumptions rmax3_le.
Print Assumptions span_verts.
Print Assumptions carrier_px_le.
Print Assumptions tin_query_ee.
Print Assumptions inM.
Print Assumptions fan_inside_relate_fixtures.
Print Assumptions crM.
Print Assumptions crE.
Print Assumptions fan_cross_relate_fixtures.
Print Assumptions fan_touch_centre_relate_fixtures.
Print Assumptions esB.
Print Assumptions fan_edge_relate_fixtures.
Print Assumptions djP.
Print Assumptions djM.
Print Assumptions eeP.
Print Assumptions fan_low_out.
Print Assumptions fan_corner_px.
Print Assumptions fan_px_out.
Print Assumptions fan_disjoint_relate_fixtures.
