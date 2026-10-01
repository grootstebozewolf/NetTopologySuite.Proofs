(* NetTopologySuite.Proofs.TrianglePairDe9imQ
   Pinned fixture table of proved tri_de9im cells on the TIN fixtures.
   Not a computed Q matrix: clip_rational shows clip vertices are
   rational, and a Q clip that decides all nine cells is a new kernel
   past the module cap. The computed nine-cell Q twin with
   tri_de9im_Q_agrees is future work. cross_Q is the rational cross;
   Q2R of it is the real cross. The table pins II, BB where
   TrianglePairTin proves it, and EE (always Dim2). Other cells stay
   uncomputed.
   Fixtures: strip_pins_fixtures, overlap_pins_fixtures,
   tjunction_pins_fixtures, fan_pins_fixtures.
   The T-junction is not a valid TIN.
   topic: relate
   claimId: tri-de9im-q
   witness: tri_de9im_fixture_pins_Q
   3-axiom host. No Admitted. No Jordan.
   AI-drafted (Cursor Grok 4.7).
   License: BSD-3-Clause *)
From Stdlib Require Import Reals Lra List QArith Qreals.
Import ListNotations.
From NTS.Proofs Require Import Distance Orientation DE9IM
  TrianglePairClip TrianglePairBound TrianglePairExterior TrianglePairTin.
Local Open Scope R_scope.

Definition cross_Q (ax ay bx by_ cx cy : Q) : Q :=
  ((bx - ax) * (cy - ay) - (cx - ax) * (by_ - ay))%Q.

Definition qpt (x y : Q) : Point := mkPoint (Q2R x) (Q2R y).

Lemma cross_Q_R : forall ax ay bx by_ cx cy,
  Q2R (cross_Q ax ay bx by_ cx cy)
  = cross (qpt ax ay) (qpt bx by_) (qpt cx cy).
Proof.
  intros. unfold cross_Q, cross, qpt. cbn [px py].
  rewrite Q2R_minus. rewrite !Q2R_mult. rewrite !Q2R_minus. reflexivity.
Qed.

Lemma Q2R_2 : Q2R 2 = 2.
Proof.
  replace 2%Q with (1 + 1)%Q by reflexivity.
  rewrite Q2R_plus, RMicromega.Q2R_1. lra.
Qed.

Lemma Q2R_4 : Q2R 4 = 4.
Proof.
  replace 4%Q with (2 + 2)%Q by reflexivity. rewrite Q2R_plus, Q2R_2. lra.
Qed.

Lemma Q2R_5 : Q2R 5 = 5.
Proof.
  replace 5%Q with (4 + 1)%Q by reflexivity.
  rewrite Q2R_plus, Q2R_4, RMicromega.Q2R_1. lra.
Qed.

Lemma Q2R_nz2 : ~ (2 == 0)%Q.
Proof. intro H. discriminate. Qed.

Lemma Q2R_nz4 : ~ (4 == 0)%Q.
Proof. intro H. discriminate. Qed.

Lemma Q2R_quarter : Q2R (1 / 4) = 1 / 4.
Proof.
  rewrite Q2R_div; [| exact Q2R_nz4].
  rewrite RMicromega.Q2R_1, Q2R_4. reflexivity.
Qed.

Lemma Q2R_half : Q2R (1 / 2) = 1 / 2.
Proof.
  rewrite Q2R_div; [| exact Q2R_nz2].
  rewrite RMicromega.Q2R_1, Q2R_2. reflexivity.
Qed.

Lemma Q2R_five_q : Q2R (5 / 4) = 5 / 4.
Proof.
  rewrite Q2R_div; [| exact Q2R_nz4]. rewrite Q2R_5, Q2R_4. reflexivity.
Qed.

Lemma Q2R_neg1 : Q2R (- (1)) = - (1).
Proof. rewrite Q2R_opp, RMicromega.Q2R_1. reflexivity. Qed.

Lemma qpt_eq : forall (x y : Q) (rx ry : R),
  Q2R x = rx -> Q2R y = ry -> qpt x y = mkPoint rx ry.
Proof. intros x y rx ry Hx Hy. unfold qpt. f_equal; assumption. Qed.

Ltac qpt_int :=
  apply qpt_eq;
  match goal with
  | |- Q2R 0 = _ => apply RMicromega.Q2R_0
  | |- Q2R 1 = _ => apply RMicromega.Q2R_1
  | |- Q2R 2 = _ => apply Q2R_2
  | |- Q2R (- (1)) = _ => apply Q2R_neg1
  | |- Q2R (1 / 2) = _ => apply Q2R_half
  | |- Q2R (1 / 4) = _ => apply Q2R_quarter
  | |- Q2R (5 / 4) = _ => apply Q2R_five_q
  end.

Ltac qpt_as := symmetry; qpt_int.

Lemma cross_Q_gt : forall ax ay bx by_ cx cy,
  (cross_Q ax ay bx by_ cx cy ?= 0)%Q = Gt ->
  0 < cross (qpt ax ay) (qpt bx by_) (qpt cx cy).
Proof.
  intros ax ay bx by_ cx cy H.
  assert (Hq : (0 < cross_Q ax ay bx by_ cx cy)%Q).
  { apply Qgt_alt. exact H. }
  apply Qlt_Rlt in Hq. rewrite RMicromega.Q2R_0 in Hq.
  rewrite <- cross_Q_R. exact Hq.
Qed.

Lemma strip_cross_Q :
  (cross_Q 1 0 0 1 0 0 ?= 0)%Q = Gt /\
  (cross_Q 0 1 1 0 1 1 ?= 0)%Q = Gt.
Proof. split; reflexivity. Qed.

Lemma overlap_cross_Q :
  (cross_Q 0 0 1 0 0 1 ?= 0)%Q = Gt /\
  (cross_Q (1 / 4) (1 / 4) (5 / 4) (1 / 4) (1 / 4) (5 / 4) ?= 0)%Q = Gt.
Proof. split; reflexivity. Qed.

Lemma tjunction_cross_Q :
  (cross_Q 0 0 2 0 1 2 ?= 0)%Q = Gt /\
  (cross_Q 1 0 0 (- (1)) 2 (- (1)) ?= 0)%Q = Gt.
Proof. split; reflexivity. Qed.

Lemma fan_cross_Q :
  (cross_Q 0 0 1 0 (1 / 2) (1 / 2) ?= 0)%Q = Gt /\
  (cross_Q 1 1 0 1 (1 / 2) (1 / 2) ?= 0)%Q = Gt.
Proof. split; reflexivity. Qed.

Lemma strip_cross_pos :
  0 < cross (qpt 1 0) (qpt 0 1) (qpt 0 0) /\
  0 < cross (qpt 0 1) (qpt 1 0) (qpt 1 1).
Proof. destruct strip_cross_Q as [Ha Hb]. split; apply cross_Q_gt; assumption. Qed.

Lemma overlap_cross_pos :
  0 < cross (qpt 0 0) (qpt 1 0) (qpt 0 1) /\
  0 < cross (qpt (1 / 4) (1 / 4)) (qpt (5 / 4) (1 / 4)) (qpt (1 / 4) (5 / 4)).
Proof. destruct overlap_cross_Q as [Ha Hb]. split; apply cross_Q_gt; assumption. Qed.

Lemma tjunction_cross_pos :
  0 < cross (qpt 0 0) (qpt 2 0) (qpt 1 2) /\
  0 < cross (qpt 1 0) (qpt 0 (- (1))) (qpt 2 (- (1))).
Proof. destruct tjunction_cross_Q as [Ha Hb]. split; apply cross_Q_gt; assumption. Qed.

Lemma fan_cross_pos :
  0 < cross (qpt 0 0) (qpt 1 0) (qpt (1 / 2) (1 / 2)) /\
  0 < cross (qpt 1 1) (qpt 0 1) (qpt (1 / 2) (1 / 2)).
Proof. destruct fan_cross_Q as [Ha Hb]. split; apply cross_Q_gt; assumption. Qed.

Lemma ee_cell : forall A B C D E F,
  im_ee (tri_de9im A B C D E F) = Dim2.
Proof. intros. unfold tri_de9im. simpl. apply ee_always. Qed.

(* Row-major partial matrix. QC_unk is an uncomputed cell, not a claim. *)
Inductive QCell : Type := QC_F | QC_0 | QC_1 | QC_2 | QC_unk.

Definition qcell_of (d : DimValue) : QCell :=
  match d with
  | None => QC_F
  | Some O => QC_0
  | Some (S O) => QC_1
  | Some (S (S O)) => QC_2
  | _ => QC_unk
  end.

Definition pin9 (ii ib ie bi bb be ei eb ee : QCell) : list QCell :=
  [ii; ib; ie; bi; bb; be; ei; eb; ee].

Definition strip_im : IntersectionMatrix :=
  tri_de9im (qpt 1 0) (qpt 0 1) (qpt 0 0) (qpt 0 1) (qpt 1 0) (qpt 1 1).

Definition overlap_im : IntersectionMatrix :=
  tri_de9im (qpt 0 0) (qpt 1 0) (qpt 0 1)
            (qpt (1 / 4) (1 / 4)) (qpt (5 / 4) (1 / 4)) (qpt (1 / 4) (5 / 4)).

Definition tjunction_im : IntersectionMatrix :=
  tri_de9im (qpt 0 0) (qpt 2 0) (qpt 1 2)
            (qpt 1 0) (qpt 0 (- (1))) (qpt 2 (- (1))).

Definition fan_im : IntersectionMatrix :=
  tri_de9im (qpt 0 0) (qpt 1 0) (qpt (1 / 2) (1 / 2))
            (qpt 1 1) (qpt 0 1) (qpt (1 / 2) (1 / 2)).

(* Oracle strings: F????1??2, 2???????2, ????0???2, F????0??2. *)
Definition strip_q : list QCell :=
  pin9 QC_F QC_unk QC_unk QC_unk QC_1 QC_unk QC_unk QC_unk QC_2.
Definition overlap_q : list QCell :=
  pin9 QC_2 QC_unk QC_unk QC_unk QC_unk QC_unk QC_unk QC_unk QC_2.
Definition tjunction_q : list QCell :=
  pin9 QC_unk QC_unk QC_unk QC_unk QC_0 QC_unk QC_unk QC_unk QC_2.
Definition fan_q : list QCell :=
  pin9 QC_F QC_unk QC_unk QC_unk QC_0 QC_unk QC_unk QC_unk QC_2.

Lemma strip_pins_fixtures :
  im_ii strip_im = DimF /\ im_bb strip_im = Dim1 /\ im_ee strip_im = Dim2.
Proof.
  unfold strip_im.
  replace (qpt 1 0) with (mkPoint 1 0) by qpt_as.
  replace (qpt 0 1) with (mkPoint 0 1) by qpt_as.
  replace (qpt 0 0) with (mkPoint 0 0) by qpt_as.
  replace (qpt 1 1) with (mkPoint 1 1) by qpt_as.
  destruct tin_strip as [_ [Hii Hbb]].
  split; [exact Hii | split; [exact Hbb | apply ee_cell]].
Qed.

Lemma overlap_pins_fixtures :
  im_ii overlap_im = Dim2 /\ im_ee overlap_im = Dim2.
Proof.
  unfold overlap_im.
  replace (qpt 0 0) with (mkPoint 0 0) by qpt_as.
  replace (qpt 1 0) with (mkPoint 1 0) by qpt_as.
  replace (qpt 0 1) with (mkPoint 0 1) by qpt_as.
  replace (qpt (1 / 4) (1 / 4)) with (mkPoint (1 / 4) (1 / 4)) by qpt_as.
  replace (qpt (5 / 4) (1 / 4)) with (mkPoint (5 / 4) (1 / 4)) by qpt_as.
  replace (qpt (1 / 4) (5 / 4)) with (mkPoint (1 / 4) (5 / 4)) by qpt_as.
  destruct tin_overlap as [Hii _].
  split; [exact Hii | apply ee_cell].
Qed.

Lemma tjunction_pins_fixtures :
  im_bb tjunction_im = Dim0 /\ im_ee tjunction_im = Dim2.
Proof.
  unfold tjunction_im.
  replace (qpt 0 0) with (mkPoint 0 0) by qpt_as.
  replace (qpt 2 0) with (mkPoint 2 0) by qpt_as.
  replace (qpt 1 2) with (mkPoint 1 2) by qpt_as.
  replace (qpt 1 0) with (mkPoint 1 0) by qpt_as.
  replace (qpt 0 (- (1))) with (mkPoint 0 (- (1))) by qpt_as.
  replace (qpt 2 (- (1))) with (mkPoint 2 (- (1))) by qpt_as.
  destruct tin_tjunction as [Hbb _].
  split; [exact Hbb | apply ee_cell].
Qed.

Lemma fan_pins_fixtures :
  im_ii fan_im = DimF /\ im_bb fan_im = Dim0 /\ im_ee fan_im = Dim2.
Proof.
  unfold fan_im.
  replace (qpt 0 0) with fanSW by (unfold fanSW; qpt_as).
  replace (qpt 1 0) with fanSE by (unfold fanSE; qpt_as).
  replace (qpt 1 1) with fanNE by (unfold fanNE; qpt_as).
  replace (qpt 0 1) with fanNW by (unfold fanNW; qpt_as).
  replace (qpt (1 / 2) (1 / 2)) with fanC by (unfold fanC; qpt_as).
  destruct tin_fan as [_ [Hii Hbb]].
  split; [exact Hii | split; [exact Hbb | apply ee_cell]].
Qed.

Ltac cells_to_q :=
  repeat match goal with
  | H : im_ii _ = _ |- _ => rewrite H
  | H : im_bb _ = _ |- _ => rewrite H
  | H : im_ee _ = _ |- _ => rewrite H
  end;
  unfold strip_q, overlap_q, tjunction_q, fan_q, pin9,
    qcell_of, DimF, Dim0, Dim1, Dim2;
  simpl; repeat split; reflexivity.

Lemma strip_q_pin :
  nth 0 strip_q QC_unk = qcell_of (im_ii strip_im) /\
  nth 4 strip_q QC_unk = qcell_of (im_bb strip_im) /\
  nth 8 strip_q QC_unk = qcell_of (im_ee strip_im).
Proof.
  destruct strip_pins_fixtures as [Hii [Hbb Hee]]. cells_to_q.
Qed.

Lemma overlap_q_pin :
  nth 0 overlap_q QC_unk = qcell_of (im_ii overlap_im) /\
  nth 8 overlap_q QC_unk = qcell_of (im_ee overlap_im).
Proof.
  destruct overlap_pins_fixtures as [Hii Hee]. cells_to_q.
Qed.

Lemma tjunction_q_pin :
  nth 4 tjunction_q QC_unk = qcell_of (im_bb tjunction_im) /\
  nth 8 tjunction_q QC_unk = qcell_of (im_ee tjunction_im).
Proof.
  destruct tjunction_pins_fixtures as [Hbb Hee]. cells_to_q.
Qed.

Lemma fan_q_pin :
  nth 0 fan_q QC_unk = qcell_of (im_ii fan_im) /\
  nth 4 fan_q QC_unk = qcell_of (im_bb fan_im) /\
  nth 8 fan_q QC_unk = qcell_of (im_ee fan_im).
Proof.
  destruct fan_pins_fixtures as [Hii [Hbb Hee]]. cells_to_q.
Qed.

Theorem tri_de9im_fixture_pins_Q :
  (nth 0 strip_q QC_unk = qcell_of (im_ii strip_im) /\
   nth 4 strip_q QC_unk = qcell_of (im_bb strip_im) /\
   nth 8 strip_q QC_unk = qcell_of (im_ee strip_im)) /\
  (nth 0 overlap_q QC_unk = qcell_of (im_ii overlap_im) /\
   nth 8 overlap_q QC_unk = qcell_of (im_ee overlap_im)) /\
  (nth 4 tjunction_q QC_unk = qcell_of (im_bb tjunction_im) /\
   nth 8 tjunction_q QC_unk = qcell_of (im_ee tjunction_im)) /\
  (nth 0 fan_q QC_unk = qcell_of (im_ii fan_im) /\
   nth 4 fan_q QC_unk = qcell_of (im_bb fan_im) /\
   nth 8 fan_q QC_unk = qcell_of (im_ee fan_im)).
Proof.
  split; [| split; [| split]].
  - exact strip_q_pin.
  - exact overlap_q_pin.
  - exact tjunction_q_pin.
  - exact fan_q_pin.
Qed.

Print Assumptions cross_Q_R.
Print Assumptions Q2R_2.
Print Assumptions Q2R_4.
Print Assumptions Q2R_5.
Print Assumptions Q2R_nz2.
Print Assumptions Q2R_nz4.
Print Assumptions Q2R_quarter.
Print Assumptions Q2R_half.
Print Assumptions Q2R_five_q.
Print Assumptions Q2R_neg1.
Print Assumptions qpt_eq.
Print Assumptions cross_Q_gt.
Print Assumptions strip_cross_Q.
Print Assumptions overlap_cross_Q.
Print Assumptions tjunction_cross_Q.
Print Assumptions fan_cross_Q.
Print Assumptions strip_cross_pos.
Print Assumptions overlap_cross_pos.
Print Assumptions tjunction_cross_pos.
Print Assumptions fan_cross_pos.
Print Assumptions ee_cell.
Print Assumptions strip_pins_fixtures.
Print Assumptions overlap_pins_fixtures.
Print Assumptions tjunction_pins_fixtures.
Print Assumptions fan_pins_fixtures.
Print Assumptions strip_q_pin.
Print Assumptions overlap_q_pin.
Print Assumptions tjunction_q_pin.
Print Assumptions fan_q_pin.
Print Assumptions tri_de9im_fixture_pins_Q.
