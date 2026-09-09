(* ============================================================================
   NetTopologySuite.Proofs.CircularCookZ
   ----------------------------------------------------------------------------
   Integer circle–circle discriminant classifier + named-root hen mint.

   I_circles_z is an extractable seam, not glossary 𝓘 (that is Hit (p*, tᵢ, tⱼ);
   there is no γ / [0,1] here). Hens 0/1 are birth certificates of the named
   radical roots, not a proved identity. I.9: those tags are not a cook
   license (CircularCookLicense.v). I.10: I_CIRCULAR stays a
   classifier (CircularCookClose.v).

       I_circles_z : Hit | Empty | Touch | Decline

   Touch is tangent contact (one hen). Decline is degenerate input
   (r ≤ 0 or coincident centres), not the egg/arc case.

   WITNESS topic: core · claimId: 64-circ-z-partition · witness: 64-circ-z-internal-kiss
   0-axiom (Z only). No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   ========================================================================== *)

From Stdlib Require Import ZArith Bool Lia.
Open Scope Z_scope.

Definition HenZ : Type := nat.

(* Birth certificates: plus/minus radical roots. *)
Definition hen_plus : HenZ := 0%nat.
Definition hen_minus : HenZ := 1%nat.

Inductive RadicalRoot : Type :=
| RootPlus
| RootMinus.

Definition hen_of_root (r : RadicalRoot) : HenZ :=
  match r with
  | RootPlus => hen_plus
  | RootMinus => hen_minus
  end.

Inductive IZResult : Type :=
| IZHit (h_plus h_minus : HenZ)
| IZEmpty
| IZTouch (h : HenZ)
| IZDecline.

Definition circ_d2 (o1x o1y o2x o2y : Z) : Z :=
  (o2x - o1x) * (o2x - o1x) + (o2y - o1y) * (o2y - o1y).

Definition mint_pair : IZResult := IZHit hen_plus hen_minus.

Definition mint_touch : IZResult := IZTouch hen_plus.

(* Squared tests, no sqrt.
   Decline: r ≤ 0 or coincident centres.
   Touch:   kiss (d = r1±r2).
   Empty:   disjoint circumcircles.
   Hit:     proper intersection; mint plus/minus hens. *)
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

(* WITNESS {"claimId":"64-i-circular","topic":"core","lemma":"locked_I_circles_z_hit","title":"Integer circle-circle discriminant: locked (0,0)/(7,0) r=5 is Hit hens 0 and 1","file":"theories/CircularCookZ.v","witness":"64-i-circular-locked","board":"ADR-0007"} *)

Lemma locked_I_circles_z_hit :
  I_circles_z 0 0 5 7 0 5 = IZHit hen_plus hen_minus.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma locked_disjoint_is_empty :
  I_circles_z 0 0 5 20 0 5 = IZEmpty.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma locked_coincident_is_decline :
  I_circles_z 0 0 5 0 0 5 = IZDecline.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma locked_zero_radius_is_decline :
  I_circles_z 0 0 0 7 0 5 = IZDecline.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma locked_external_kiss_is_touch :
  I_circles_z 0 0 5 10 0 5 = IZTouch hen_plus.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma IZEmpty_neq_IZDecline : IZEmpty <> IZDecline.
Proof.
  discriminate.
Qed.

Lemma IZTouch_neq_IZDecline : forall h, IZTouch h <> IZDecline.
Proof.
  intros. discriminate.
Qed.

Lemma IZTouch_neq_IZHit :
  forall h hp hm, IZTouch h <> IZHit hp hm.
Proof.
  intros. discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* Partition: constructor ↔ the same squared tests the classifier runs.        *)
(* Hit is the open interval |r1−r2|² < d² < (r1+r2)² on positive radii.       *)
(* Decline owns r≤0 and coincident centres (d²=0), so those are not Empty.    *)
(* -------------------------------------------------------------------------- *)

Definition circ_sum2 (r1 r2 : Z) : Z := (r1 + r2) * (r1 + r2).
Definition circ_diff2 (r1 r2 : Z) : Z := (r1 - r2) * (r1 - r2).

(* |r1−r2|² = (r1−r2)²; circ_diff2 is the squared test the classifier runs. *)

(* WITNESS {"claimId":"64-circ-z-partition","topic":"core","lemma":"I_circles_z_hit_iff","title":"Hit iff positive radii and |r1-r2|^2 < d^2 < (r1+r2)^2","file":"theories/CircularCookZ.v","witness":"64-circ-z-internal-kiss","board":"ADR-0007"} *)

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

(* Internal kiss: smaller circle inside the larger, d = |r1−r2|. Touch. *)
Lemma locked_internal_kiss_is_touch :
  I_circles_z 0 0 5 3 0 2 = IZTouch hen_plus.
Proof.
  apply I_circles_z_touch_iff.
  unfold circ_d2, circ_sum2, circ_diff2. lia.
Qed.

(* I.9: classifier hens are tags 0/1. IZHit never carries (p*, t).
   Oracle I_CIRCULAR prints HIT 0 1 on the locked fixture. *)
Lemma classifier_hens_are_tags :
  hen_plus = 0%nat /\ hen_minus = 1%nat.
Proof.
  split; reflexivity.
Qed.

Lemma iz_hit_only_tags :
  forall o1x o1y r1 o2x o2y r2 hp hm,
    I_circles_z o1x o1y r1 o2x o2y r2 = IZHit hp hm ->
    hp = hen_plus /\ hm = hen_minus.
Proof.
  intros o1x o1y r1 o2x o2y r2 hp hm H.
  unfold I_circles_z, mint_pair, mint_touch in H.
  destruct ((r1 <=? 0) || (r2 <=? 0)); [discriminate H|].
  destruct (circ_d2 o1x o1y o2x o2y =? 0); [discriminate H|].
  destruct ((circ_d2 o1x o1y o2x o2y =? (r1 + r2) * (r1 + r2))
            || (circ_d2 o1x o1y o2x o2y =? (r1 - r2) * (r1 - r2)));
    [discriminate H|].
  destruct (((r1 + r2) * (r1 + r2) <? circ_d2 o1x o1y o2x o2y)
            || (circ_d2 o1x o1y o2x o2y <? (r1 - r2) * (r1 - r2)));
    [discriminate H|].
  inversion H. split; reflexivity.
Qed.

Print Assumptions locked_I_circles_z_hit.
Print Assumptions locked_external_kiss_is_touch.
Print Assumptions IZEmpty_neq_IZDecline.
Print Assumptions IZTouch_neq_IZDecline.
Print Assumptions IZTouch_neq_IZHit.
Print Assumptions I_circles_z_hit_iff.
Print Assumptions I_circles_z_touch_iff.
Print Assumptions I_circles_z_empty_iff.
Print Assumptions I_circles_z_decline_iff.
Print Assumptions locked_internal_kiss_is_touch.
Print Assumptions classifier_hens_are_tags.
Print Assumptions iz_hit_only_tags.
