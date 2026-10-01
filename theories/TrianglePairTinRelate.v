(* NetTopologySuite.Proofs.TrianglePairTinRelate
   II against the cell interior of TrianglePairTinSurface, not a DE-9IM
   cell yet. A CCW query open meets tin_int_cells exactly when some
   triangle's II cell is Dim2, or the open meets a shared-edge relative
   interior, or it meets an internal vertex. The wording flips to a
   DE-9IM cell when tin_int_cells_eq lands.
   Fixtures against the centre fan: fan_inside_ii_fixtures,
   fan_cross_ii_fixtures, fan_touch_centre_fixtures,
   fan_touch_ii_fixtures, fan_disjoint_ii_fixtures.
   The centre-touch fixture keeps the centre on the query boundary. The
   query open still meets a fan open, so that pair's II cell is Dim2.
   topic: relate
   claimId: tri-de9im-t5
   witness: tin_query_ii
   3-axiom host. No Admitted. No Jordan.
   AI-drafted (Cursor Grok 4.7).
   License: BSD-3-Clause *)
From Stdlib Require Import Reals Lra Lia List Bool.
Import ListNotations.
From NTS.Proofs Require Import Distance Orientation Convex ConvexClip
  DE9IM TrianglePairCommon TrianglePairClip TrianglePairEdge
  TrianglePairBound TrianglePairExterior TrianglePairMatrix
  TrianglePairTin TrianglePairTinSurface.
Local Open Scope R_scope.

Definition tri_ii (T : Tri) (D E F : Point) : DimValue :=
  match T with ((A, B), C) => im_ii (tri_de9im A B C D E F) end.

Lemma ii_dim2_iff : forall A B C D E F,
  0 < cross A B C -> 0 < cross D E F ->
  ii_entry A B C D E F = Dim2 <->
  exists X, tri_open A B C X /\ tri_open D E F X.
Proof.
  intros A B C D E F HA HB. unfold ii_entry. split.
  - intros H. destruct (Rlt_dec 0 (poly_area2 (tri_inter A B C D E F))) as [Hp|Hn].
    + apply (proj2 (ii_nonempty_iff A B C D E F HA HB)). exact Hp.
    + discriminate.
  - intros Hex.
    destruct (Rlt_dec 0 (poly_area2 (tri_inter A B C D E F))) as [Hp|Hn].
    + reflexivity.
    + exfalso. apply Hn. apply (proj1 (ii_nonempty_iff A B C D E F HA HB)). exact Hex.
Qed.

Lemma tri_ii_dim2_iff : forall T D E F,
  tri_pos T -> 0 < cross D E F ->
  tri_ii T D E F = Dim2 <->
  exists X, open_of T X /\ tri_open D E F X.
Proof.
  intros [[A B] C] D E F HT HD. unfold tri_ii, tri_pos, open_of in *.
  rewrite im_ii_eq. apply ii_dim2_iff; assumption.
Qed.

Theorem tin_query_ii : forall ts D E F,
  (forall T, In T ts -> tri_pos T) -> tin_sem ts -> 0 < cross D E F ->
  (exists X, tin_int_cells ts X /\ tri_open D E F X) <->
  (exists T, In T ts /\ tri_ii T D E F = Dim2) \/
  (exists X, shared_rel ts X /\ tri_open D E F X) \/
  (exists X, internal_vert ts X /\ tri_open D E F X).
Proof.
  intros ts D E F Hpos Hsem HD. split.
  - intros [X [Hint Ho]]. destruct Hint as [[T [Hin Hop]]|[Hs|Hv]].
    + left. exists T. split; [exact Hin|].
      apply tri_ii_dim2_iff.
      * apply Hpos. exact Hin.
      * exact HD.
      * exists X. split; assumption.
    + right. left. exists X. split; assumption.
    + right. right. exists X. split; assumption.
  - intros [H2|[Hs|Hv]].
    + destruct H2 as [T [Hin Hii]].
      apply tri_ii_dim2_iff in Hii.
      * destruct Hii as [X [Hop Ho]]. exists X. split.
        -- left. exists T. split; assumption.
        -- exact Ho.
      * apply Hpos. exact Hin.
      * exact HD.
    + destruct Hs as [X [Hs Ho]]. exists X. split.
      * right. left. exact Hs.
      * exact Ho.
    + destruct Hv as [X [Hv Ho]]. exists X. split.
      * right. right. exact Hv.
      * exact Ho.
Qed.

(* Fixtures. Coordinates are concrete; crosses are discharged by lra. *)

Definition inA : Point := mkPoint (1 / 4) (1 / 16).
Definition inB : Point := mkPoint (1 / 2) (1 / 16).
Definition inC : Point := mkPoint (3 / 8) (1 / 8).
Definition inP : Point := mkPoint (3 / 8) (1 / 10).

Lemma fan_inside_ii_fixtures :
  0 < cross inA inB inC /\
  tri_open fanSW fanSE fanC inP /\ tri_open inA inB inC inP /\
  tri_ii ((fanSW, fanSE), fanC) inA inB inC = Dim2.
Proof.
  split; [| split; [| split]].
  - unfold cross, inA, inB, inC. simpl. lra.
  - unfold tri_open, cross, fanSW, fanSE, fanC, inP. simpl. repeat split; lra.
  - unfold tri_open, cross, inA, inB, inC, inP. simpl. repeat split; lra.
  - apply tri_ii_dim2_iff.
    + unfold tri_pos, cross, fanSW, fanSE, fanC. simpl. lra.
    + unfold cross, inA, inB, inC. simpl. lra.
    + exists inP. split.
      * unfold open_of, tri_open, cross, fanSW, fanSE, fanC, inP. simpl. repeat split; lra.
      * unfold tri_open, cross, inA, inB, inC, inP. simpl. repeat split; lra.
Qed.

Definition crA : Point := mkPoint (1 / 4) (- (1 / 4)).
Definition crB : Point := mkPoint (3 / 4) (- (1 / 4)).
Definition crC : Point := mkPoint (1 / 2) (1 / 4).
Definition crP : Point := mkPoint (1 / 2) (1 / 16).

Lemma fan_cross_ii_fixtures :
  0 < cross crA crB crC /\
  tri_open fanSW fanSE fanC crP /\ tri_open crA crB crC crP /\
  tri_ii ((fanSW, fanSE), fanC) crA crB crC = Dim2.
Proof.
  split; [| split; [| split]].
  - unfold cross, crA, crB, crC. simpl. lra.
  - unfold tri_open, cross, fanSW, fanSE, fanC, crP. simpl. repeat split; lra.
  - unfold tri_open, cross, crA, crB, crC, crP. simpl. repeat split; lra.
  - apply tri_ii_dim2_iff.
    + unfold tri_pos, cross, fanSW, fanSE, fanC. simpl. lra.
    + unfold cross, crA, crB, crC. simpl. lra.
    + exists crP. split.
      * unfold open_of, tri_open, cross, fanSW, fanSE, fanC, crP. simpl. repeat split; lra.
      * unfold tri_open, cross, crA, crB, crC, crP. simpl. repeat split; lra.
Qed.

Definition tcB : Point := mkPoint 2 0.
Definition tcC : Point := mkPoint 2 1.
Definition tcP : Point := mkPoint (3 / 5) (1 / 2).

Lemma fan_touch_centre_fixtures :
  on_bd fanC tcB tcC fanC /\ tin_int_cells fan_ts fanC /\
  ~ tri_open fanC tcB tcC fanC.
Proof.
  split; [| split].
  - left. apply (proj1 (seg_ends fanC tcB)).
  - exact fan_centre_int_cells_fixtures.
  - intros [Hz _]. unfold cross, fanC, tcB in Hz. simpl in Hz. lra.
Qed.

Lemma fan_touch_ii_fixtures :
  0 < cross fanC tcB tcC /\
  tri_open fanSE fanNE fanC tcP /\ tri_open fanC tcB tcC tcP /\
  tri_ii ((fanSE, fanNE), fanC) fanC tcB tcC = Dim2.
Proof.
  split; [| split; [| split]].
  - unfold cross, fanC, tcB, tcC. simpl. lra.
  - unfold tri_open, cross, fanSE, fanNE, fanC, tcP. simpl. repeat split; lra.
  - unfold tri_open, cross, fanC, tcB, tcC, tcP. simpl. repeat split; lra.
  - apply tri_ii_dim2_iff.
    + unfold tri_pos, cross, fanSE, fanNE, fanC. simpl. lra.
    + unfold cross, fanC, tcB, tcC. simpl. lra.
    + exists tcP. split.
      * unfold open_of, tri_open, cross, fanSE, fanNE, fanC, tcP. simpl. repeat split; lra.
      * unfold tri_open, cross, fanC, tcB, tcC, tcP. simpl. repeat split; lra.
Qed.

Definition djA : Point := mkPoint 3 3.
Definition djB : Point := mkPoint 4 3.
Definition djC : Point := mkPoint 3 4.

Lemma fan_low_cross : forall X,
  py X <= 1 -> cross djA djB X <= 0.
Proof.
  intros X Hy. unfold cross, djA, djB. simpl. lra.
Qed.

Lemma fan_tri_miss : forall A B C X,
  py A <= 1 -> py B <= 1 -> py C <= 1 ->
  in_tri A B C X -> ~ tri_open djA djB djC X.
Proof.
  intros A B C X Ha Hb Hc Hin [Hab _].
  assert (Hz : cross djA djB X <= 0).
  { apply (cross_tri_le djA djB A B C X).
    - apply fan_low_cross. exact Ha.
    - apply fan_low_cross. exact Hb.
    - apply fan_low_cross. exact Hc.
    - exact Hin. }
  lra.
Qed.

Lemma fan_corner_py : forall T, In T fan_ts ->
  match T with
  | ((A, B), C) => py A <= 1 /\ py B <= 1 /\ py C <= 1 /\ 0 < cross A B C
  end.
Proof.
  intros T Hin. simpl in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | []]]]];
    unfold fanSW, fanSE, fanNE, fanNW, fanC, cross; simpl; lra.
Qed.

Lemma fan_disjoint_ii_fixtures : forall X,
  tin_int_cells fan_ts X -> ~ tri_open djA djB djC X.
Proof.
  intros X Hint Ho.
  destruct Hint as [[T [Hin Hop]]|[Hs|Hv]].
  - destruct T as [[A B] C]. simpl in Hop.
    destruct (fan_corner_py ((A, B), C) Hin) as [Ha [Hb [Hc Hpos]]].
    apply (fan_tri_miss A B C X Ha Hb Hc).
    + apply tri_open_closed; assumption.
    + exact Ho.
  - destruct Hs as [P [Q [_ [Hge HoS]]]].
    destruct (uses_ge1_owner fan_ts P Q) as [T [Hin Hb]].
    { lia. }
    destruct T as [[A B] C]. apply tri_edge_b_true in Hb. simpl in Hb.
    destruct (fan_corner_py ((A, B), C) Hin) as [Ha [Hbnd [Hc _]]].
    apply (fan_tri_miss A B C X Ha Hbnd Hc).
    + apply on_bd_in_tri. apply (bd_of_edge A B C P Q X Hb).
      apply on_seg_open_seg. exact HoS.
    + exact Ho.
  - destruct Hv as [[T [Hin Hvert]] _].
    destruct T as [[A B] C].
    destruct (fan_corner_py ((A, B), C) Hin) as [Ha [Hb [Hc _]]].
    apply (fan_tri_miss A B C X Ha Hb Hc).
    + apply on_bd_in_tri. apply vert_on_bd. exact Hvert.
    + exact Ho.
Qed.

Print Assumptions ii_dim2_iff.
Print Assumptions tri_ii_dim2_iff.
Print Assumptions tin_query_ii.
Print Assumptions fan_inside_ii_fixtures.
Print Assumptions fan_cross_ii_fixtures.
Print Assumptions fan_touch_centre_fixtures.
Print Assumptions fan_touch_ii_fixtures.
Print Assumptions fan_low_cross.
Print Assumptions fan_tri_miss.
Print Assumptions fan_corner_py.
Print Assumptions fan_disjoint_ii_fixtures.
