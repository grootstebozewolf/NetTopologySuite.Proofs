(* NetTopologySuite.Proofs.TrianglePairCommon
   Shared open-triangle and separating-edge vocabulary for the pair clip.
   topic: relate
   claimId: tri-de9im-a
   witness: ConvexClip.clip_halfplane
   3-axiom host. No Admitted. No Jordan.
   AI-drafted (Cursor Grok 4.7), human-reviewed.
   License: BSD-3-Clause *)

From Stdlib Require Import Reals Lra List.
Import ListNotations.
From NTS.Proofs Require Import Distance Orientation.
Local Open Scope R_scope.

Definition tri_open (A B C X : Point) : Prop :=
  0 < cross A B X /\ 0 < cross B C X /\ 0 < cross C A X.

Definition seg_room (sx sg : R) : R :=
  if Rle_dec 0 (sg - sx) then 1 else sx / (sx - sg).

Lemma seg_room_pos : forall sx sg, 0 < sx -> 0 < seg_room sx sg.
Proof.
  intros sx sg Hs. unfold seg_room.
  destruct (Rle_dec 0 (sg - sx)) as [|H].
  - lra.
  - apply Rnot_le_lt in H.
    apply Rdiv_lt_0_compat; lra.
Qed.

Lemma slack_nonneg_room : forall sx sg t,
  0 < sx -> 0 <= t -> t <= seg_room sx sg ->
  0 <= (1 - t) * sx + t * sg.
Proof.
  intros sx sg t Hs Ht0 Ht. unfold seg_room in Ht.
  destruct (Rle_dec 0 (sg - sx)) as [Hg|Hg].
  - replace ((1 - t) * sx + t * sg) with (sx + t * (sg - sx)) by ring.
    apply Rplus_le_le_0_compat; [apply Rlt_le; exact Hs |].
    apply Rmult_le_pos; lra.
  - apply Rnot_le_lt in Hg.
    assert (Hd : 0 < sx - sg) by lra.
    assert (Hnz : sx - sg <> 0).
    { apply not_eq_sym. apply Rlt_not_eq. exact Hd. }
    replace ((1 - t) * sx + t * sg)
      with ((sx - sg) * (sx / (sx - sg) - t)) by (field; exact Hnz).
    apply Rmult_le_pos; lra.
Qed.

Fixpoint rmin_list (rs : list R) : R :=
  match rs with
  | [] => 1 / 2
  | a :: t => Rmin a (rmin_list t)
  end.

Lemma Rmin_pos : forall a b, 0 < a -> 0 < b -> 0 < Rmin a b.
Proof.
  intros a b Ha Hb. destruct (Rle_dec a b) as [H|H].
  - rewrite Rmin_left by exact H. exact Ha.
  - apply Rnot_le_lt in H. rewrite Rmin_right by (apply Rlt_le; exact H). exact Hb.
Qed.

Lemma rmin_list_pos : forall rs,
  (forall a, In a rs -> 0 < a) -> 0 < rmin_list rs.
Proof.
  induction rs as [|a rs IH]; intros Hp.
  - simpl. lra.
  - simpl. apply Rmin_pos.
    + apply Hp. simpl. left. reflexivity.
    + apply IH. intros b Hb. apply Hp. simpl. right. exact Hb.
Qed.

Lemma rmin_list_le : forall rs a, In a rs -> rmin_list rs <= a.
Proof.
  induction rs as [|b rs IH]; intros a Hin; simpl in Hin; try contradiction.
  simpl. destruct Hin as [<-|Hin].
  - apply Rmin_l.
  - apply Rle_trans with (r2 := rmin_list rs).
    + apply Rmin_r.
    + apply IH. exact Hin.
Qed.

Lemma rmin_list_half : forall rs, rmin_list rs <= 1 / 2.
Proof.
  induction rs as [|a rs IH].
  - simpl. lra.
  - simpl. apply Rle_trans with (r2 := rmin_list rs); [apply Rmin_r | exact IH].
Qed.

(* -------------------------------------------------------------------------- *)
(* A closed outer edge of either triangle keeps the interiors apart.          *)
(* The converse uses the same clip: no outer edge, so the interiors meet.     *)
(* -------------------------------------------------------------------------- *)

Definition outer3 (p q a b c : Point) : Prop :=
  cross p q a <= 0 /\ cross p q b <= 0 /\ cross p q c <= 0.

Definition some_outer (A B C D E F : Point) : Prop :=
  outer3 A B D E F \/ outer3 B C D E F \/ outer3 C A D E F \/
  outer3 D E A B C \/ outer3 E F A B C \/ outer3 F D A B C.

