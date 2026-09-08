(* ============================================================================
   nts-eval micro unit — claimId 64-circ-z-partition
   ----------------------------------------------------------------------------
   Twin of CircularCookZ partition: Hit ↔ |r1−r2|² < d² < (r1+r2)²
   (positive radii) plus complementary Empty / Touch / Decline, and the
   locked internal-kiss Touch witness.
   ========================================================================== *)

(* WITNESS {"claimId":"64-circ-z-partition","topic":"core","lemma":"I_circles_z_hit_iff","title":"Hit iff positive radii and |r1-r2|^2 < d^2 < (r1+r2)^2"} *)

From Stdlib Require Import ZArith Bool Lia.
Open Scope Z_scope.

Definition HenZ : Type := nat.
Definition hen_plus : HenZ := 0%nat.
Definition hen_minus : HenZ := 1%nat.

Inductive IZResult : Type :=
| IZHit (h_plus h_minus : HenZ)
| IZEmpty
| IZTouch (h : HenZ)
| IZDecline.

Definition circ_d2 (o1x o1y o2x o2y : Z) : Z :=
  (o2x - o1x) * (o2x - o1x) + (o2y - o1y) * (o2y - o1y).

Definition circ_sum2 (r1 r2 : Z) : Z := (r1 + r2) * (r1 + r2).
Definition circ_diff2 (r1 r2 : Z) : Z := (r1 - r2) * (r1 - r2).

Definition mint_pair : IZResult := IZHit hen_plus hen_minus.
Definition mint_touch : IZResult := IZTouch hen_plus.

Definition I_circles_z (o1x o1y r1 o2x o2y r2 : Z) : IZResult :=
  if (r1 <=? 0) || (r2 <=? 0) then IZDecline
  else if circ_d2 o1x o1y o2x o2y =? 0 then IZDecline
  else if (circ_d2 o1x o1y o2x o2y =? (r1 + r2) * (r1 + r2))
          || (circ_d2 o1x o1y o2x o2y =? (r1 - r2) * (r1 - r2))
       then mint_touch
  else if ((r1 + r2) * (r1 + r2) <? circ_d2 o1x o1y o2x o2y)
          || (circ_d2 o1x o1y o2x o2y <? (r1 - r2) * (r1 - r2))
       then IZEmpty
  else mint_pair.

Theorem I_circles_z_hit_iff :
  forall o1x o1y r1 o2x o2y r2,
    I_circles_z o1x o1y r1 o2x o2y r2 = IZHit hen_plus hen_minus <->
    0 < r1 /\ 0 < r2 /\
    circ_diff2 r1 r2 < circ_d2 o1x o1y o2x o2y /\
    circ_d2 o1x o1y o2x o2y < circ_sum2 r1 r2.
Proof.
  intros o1x o1y r1 o2x o2y r2.
  unfold I_circles_z, mint_pair, mint_touch, circ_sum2, circ_diff2.
  destruct ((r1 <=? 0) || (r2 <=? 0)) eqn:Hr.
  - split; [discriminate|].
    intros [H1 [H2 _]].
    apply orb_true_iff in Hr.
    rewrite !Z.leb_le in Hr.
    lia.
  - apply orb_false_iff in Hr.
    destruct Hr as [Hr1 Hr2].
    rewrite Z.leb_gt in Hr1, Hr2.
    destruct (circ_d2 o1x o1y o2x o2y =? 0) eqn:Hd0.
    + apply Z.eqb_eq in Hd0. split; [discriminate|].
      intros [_ [_ [Hlt _]]].
      rewrite Hd0 in Hlt. exfalso.
      pose proof (Z.square_nonneg (r1 - r2)). lia.
    + apply Z.eqb_neq in Hd0.
      destruct ((circ_d2 o1x o1y o2x o2y =? (r1 + r2) * (r1 + r2))
                || (circ_d2 o1x o1y o2x o2y =? (r1 - r2) * (r1 - r2))) eqn:Hk.
      * split; [discriminate|].
        intros [_ [_ [Hlt Hgt]]].
        apply orb_true_iff in Hk.
        rewrite !Z.eqb_eq in Hk.
        lia.
      * apply orb_false_iff in Hk.
        destruct Hk as [Hs Hd].
        apply Z.eqb_neq in Hs, Hd.
        destruct (((r1 + r2) * (r1 + r2) <? circ_d2 o1x o1y o2x o2y)
                  || (circ_d2 o1x o1y o2x o2y <? (r1 - r2) * (r1 - r2))) eqn:He.
        -- split; [discriminate|].
          intros [_ [_ [Hlt Hgt]]].
          apply orb_true_iff in He.
          rewrite !Z.ltb_lt in He.
          lia.
        -- apply orb_false_iff in He.
           destruct He as [Hs2 Hd2].
           rewrite Z.ltb_ge in Hs2, Hd2.
           split.
           ++ intros _. split; [lia|split; [lia|split; lia]].
           ++ intros. reflexivity.
Qed.

Theorem I_circles_z_touch_iff :
  forall o1x o1y r1 o2x o2y r2,
    I_circles_z o1x o1y r1 o2x o2y r2 = IZTouch hen_plus <->
    0 < r1 /\ 0 < r2 /\
    circ_d2 o1x o1y o2x o2y <> 0 /\
    (circ_d2 o1x o1y o2x o2y = circ_sum2 r1 r2 \/
     circ_d2 o1x o1y o2x o2y = circ_diff2 r1 r2).
Proof.
  intros o1x o1y r1 o2x o2y r2.
  unfold I_circles_z, mint_pair, mint_touch, circ_sum2, circ_diff2.
  destruct ((r1 <=? 0) || (r2 <=? 0)) eqn:Hr.
  - split; [discriminate|].
    intros [H1 [H2 _]].
    apply orb_true_iff in Hr.
    rewrite !Z.leb_le in Hr.
    lia.
  - apply orb_false_iff in Hr.
    destruct Hr as [Hr1 Hr2].
    rewrite Z.leb_gt in Hr1, Hr2.
    destruct (circ_d2 o1x o1y o2x o2y =? 0) eqn:Hd0.
    + apply Z.eqb_eq in Hd0. split; [discriminate|].
      intros [_ [_ [Hnz _]]]. congruence.
    + apply Z.eqb_neq in Hd0.
      destruct ((circ_d2 o1x o1y o2x o2y =? (r1 + r2) * (r1 + r2))
                || (circ_d2 o1x o1y o2x o2y =? (r1 - r2) * (r1 - r2))) eqn:Hk.
      * apply orb_true_iff in Hk.
        rewrite !Z.eqb_eq in Hk.
        split.
        -- intros _. split; [lia|split; [lia|split; [exact Hd0|exact Hk]]].
        -- intros. reflexivity.
      * apply orb_false_iff in Hk.
        destruct Hk as [Hs Hd].
        apply Z.eqb_neq in Hs, Hd.
        destruct (((r1 + r2) * (r1 + r2) <? circ_d2 o1x o1y o2x o2y)
                  || (circ_d2 o1x o1y o2x o2y <? (r1 - r2) * (r1 - r2))) eqn:He.
        -- split; [discriminate|]. intros [_ [_ [_ [H|H]]]]; congruence.
        -- split; [discriminate|]. intros [_ [_ [_ [H|H]]]]; congruence.
Qed.

Theorem I_circles_z_empty_iff :
  forall o1x o1y r1 o2x o2y r2,
    I_circles_z o1x o1y r1 o2x o2y r2 = IZEmpty <->
    0 < r1 /\ 0 < r2 /\
    circ_d2 o1x o1y o2x o2y <> 0 /\
    circ_d2 o1x o1y o2x o2y <> circ_sum2 r1 r2 /\
    circ_d2 o1x o1y o2x o2y <> circ_diff2 r1 r2 /\
    (circ_sum2 r1 r2 < circ_d2 o1x o1y o2x o2y \/
     circ_d2 o1x o1y o2x o2y < circ_diff2 r1 r2).
Proof.
  intros o1x o1y r1 o2x o2y r2.
  unfold I_circles_z, mint_pair, mint_touch, circ_sum2, circ_diff2.
  destruct ((r1 <=? 0) || (r2 <=? 0)) eqn:Hr.
  - split; [discriminate|].
    intros [H1 [H2 _]].
    apply orb_true_iff in Hr.
    rewrite !Z.leb_le in Hr.
    lia.
  - apply orb_false_iff in Hr.
    destruct Hr as [Hr1 Hr2].
    rewrite Z.leb_gt in Hr1, Hr2.
    destruct (circ_d2 o1x o1y o2x o2y =? 0) eqn:Hd0.
    + apply Z.eqb_eq in Hd0. split; [discriminate|].
      intros [_ [_ [Hnz _]]]. congruence.
    + apply Z.eqb_neq in Hd0.
      destruct ((circ_d2 o1x o1y o2x o2y =? (r1 + r2) * (r1 + r2))
                || (circ_d2 o1x o1y o2x o2y =? (r1 - r2) * (r1 - r2))) eqn:Hk.
      * apply orb_true_iff in Hk.
        rewrite !Z.eqb_eq in Hk.
        split; [discriminate|].
        intros [_ [_ [_ [Hs [Hd _]]]]].
        destruct Hk; congruence.
      * apply orb_false_iff in Hk.
        destruct Hk as [Hs Hd].
        apply Z.eqb_neq in Hs, Hd.
        destruct (((r1 + r2) * (r1 + r2) <? circ_d2 o1x o1y o2x o2y)
                  || (circ_d2 o1x o1y o2x o2y <? (r1 - r2) * (r1 - r2))) eqn:He.
        -- apply orb_true_iff in He.
           rewrite !Z.ltb_lt in He.
           split.
           ++ intros _.
              split; [lia|split; [lia|split; [exact Hd0|split; [exact Hs|split; [exact Hd|exact He]]]]].
           ++ intros. reflexivity.
        -- apply orb_false_iff in He.
           destruct He as [Hs2 Hd2].
           rewrite Z.ltb_ge in Hs2, Hd2.
           split; [discriminate|].
           intros [_ [_ [_ [_ [_ [H|H]]]]]]; lia.
Qed.

Theorem I_circles_z_decline_iff :
  forall o1x o1y r1 o2x o2y r2,
    I_circles_z o1x o1y r1 o2x o2y r2 = IZDecline <->
    r1 <= 0 \/ r2 <= 0 \/ circ_d2 o1x o1y o2x o2y = 0.
Proof.
  intros o1x o1y r1 o2x o2y r2.
  unfold I_circles_z, mint_pair, mint_touch.
  destruct ((r1 <=? 0) || (r2 <=? 0)) eqn:Hr.
  - apply orb_true_iff in Hr.
    rewrite !Z.leb_le in Hr.
    split.
    + intros _. destruct Hr; [left|right; left]; exact H.
    + intros. reflexivity.
  - apply orb_false_iff in Hr.
    destruct Hr as [Hr1 Hr2].
    rewrite Z.leb_gt in Hr1, Hr2.
    destruct (circ_d2 o1x o1y o2x o2y =? 0) eqn:Hd0.
    + apply Z.eqb_eq in Hd0. split; [intros; right; right; exact Hd0|intros; reflexivity].
    + apply Z.eqb_neq in Hd0.
      destruct ((circ_d2 o1x o1y o2x o2y =? (r1 + r2) * (r1 + r2))
                || (circ_d2 o1x o1y o2x o2y =? (r1 - r2) * (r1 - r2))) eqn:Hk.
      * split; [discriminate|]. intros [H|[H|H]]; lia.
      * destruct (((r1 + r2) * (r1 + r2) <? circ_d2 o1x o1y o2x o2y)
                  || (circ_d2 o1x o1y o2x o2y <? (r1 - r2) * (r1 - r2))) eqn:He.
        -- split; [discriminate|]. intros [H|[H|H]]; lia.
        -- split; [discriminate|]. intros [H|[H|H]]; lia.
Qed.

Lemma locked_internal_kiss_is_touch :
  I_circles_z 0 0 5 3 0 2 = IZTouch hen_plus.
Proof.
  apply I_circles_z_touch_iff.
  unfold circ_d2, circ_sum2, circ_diff2. lia.
Qed.

Print Assumptions I_circles_z_hit_iff.
Print Assumptions I_circles_z_touch_iff.
Print Assumptions I_circles_z_empty_iff.
Print Assumptions I_circles_z_decline_iff.
Print Assumptions locked_internal_kiss_is_touch.
