(* ============================================================================
   NetTopologySuite.Proofs.TaggedIntegralChange
   ----------------------------------------------------------------------------
   Two facts about TaggedIntegral's RInt:
   - RInt_bounded: an RInt-integrable function is bounded (re-tag one cell
     of a fine uniform partition);
   - RInt_exp_change: int_(e^a)^(e^b) f = int_a^b f(e^u) e^u du for any
     RInt-integrable f (no antiderivative needed).
   Moved verbatim from the probe lane (docs/h1-vacuity/AlpogeSixthBatch.v Part E); the Alpöge audit probes
   re-export it.  Allowlist-clean: every Print Assumptions shows at most the
   corpus trio (sig_not_dec, sig_forall_dec, functional_extensionality_dep).

   claimId: none
   No Admitted, no Axiom, no Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
   ============================================================================ *)
From Stdlib Require Import Reals Lra Psatz Lia List Factorial ZArith.
From NTS.Proofs Require Import ExpSeriesClean LogRpowClean TaggedIntegral.
Import ListNotations.
Local Open Scope R_scope.

(* E1. an RInt-integrable function is bounded (re-tagging one cell of a
   fine uniform partition moves the Riemann sum by (f y - f t) h). *)
Fixpoint widths_ge (h a : R) (l : list (R * R)) : Prop :=
  match l with [] => True | (t, x) :: l' => h <= x - a /\ widths_ge h x l' end.
Fixpoint tagmax (f : R -> R) (l : list (R * R)) : R :=
  match l with [] => 0 | (t, x) :: l' => Rmax (Rabs (f t)) (tagmax f l') end.

Lemma tagmax_nonneg : forall f l, 0 <= tagmax f l.
Proof. intros f l. induction l as [|[t x] l IH]; simpl; [lra|]. eapply Rle_trans; [exact IH|apply Rmax_r]. Qed.

Lemma retag : forall f h l a b y, 0 < h -> tpart a b l -> widths_ge h a l -> a <= y <= b -> a < b ->
  exists l' t w, tpart a b l' /\ (forall d, fine d a l -> fine d a l') /\
    tsum f a l' - tsum f a l = (f y - f t) * w /\ h <= w /\ Rabs (f t) <= tagmax f l.
Proof.
  intros f h l. induction l as [|[t x] l IH]; intros a b y Hh Hp Hw Hy Hab.
  - simpl in Hp. lra.
  - simpl in Hp, Hw. destruct Hp as [H1 [H2 H3]]. destruct Hw as [Hw1 Hw2].
    destruct (Rle_or_lt y x) as [Hyx|Hyx].
    + exists ((y, x) :: l), t, (x - a).
      refine (conj _ (conj _ (conj _ (conj _ _)))).
      * simpl. split; [lra|split; [lra|exact H3]].
      * intros dd Hf. simpl in *. exact Hf.
      * simpl. ring.
      * lra.
      * simpl. apply Rmax_l.
    + assert (Hxb : x <= b) by exact (tpart_le _ _ _ H3).
      destruct (IH x b y Hh H3 Hw2 ltac:(lra) ltac:(lra)) as [l' [t' [w [P1 [P2 [P3 [P4 P5]]]]]]].
      exists ((t, x) :: l'), t', w.
      refine (conj _ (conj _ (conj _ (conj _ _)))).
      * simpl. split; [lra|split; [lra|exact P1]].
      * intros dd [D1 D2]. simpl. split; [exact D1|apply P2; exact D2].
      * simpl. rewrite <- P3. ring.
      * exact P4.
      * simpl. eapply Rle_trans; [exact P5|apply Rmax_r].
Qed.

Lemma upart_widths : forall n a h, widths_ge h a (upart a h n).
Proof. induction n as [|n IH]; intros a h; simpl; [trivial|]. split; [lra|apply IH]. Qed.

Theorem RInt_bounded : forall f A B I, RInt f A B I -> exists M, forall y, A <= y <= B -> Rabs (f y) <= M.
Proof.
  intros f A B I [HAB HI].
  destruct (Req_dec A B) as [E|Hne].
  - exists (Rabs (f A)). intros y Hy. replace y with A by lra. lra.
  - assert (Hlt : A < B) by lra.
    destruct (HI 1 ltac:(lra)) as [d [Hd Hfine]].
    destruct (archimed ((B - A) / d)) as [Hn _].
    set (n := Z.to_nat (up ((B - A) / d))).
    assert (Hn0 : (B - A) / d < INR n).
    { unfold n. rewrite INR_IZR_INZ, Z2Nat.id; [lra|].
      assert (0 < (B - A) / d) by (apply Rdiv_lt_0_compat; lra).
      apply le_IZR. lra. }
    assert (HnP : 0 < INR n).
    { assert (0 < (B - A) / d) by (apply Rdiv_lt_0_compat; lra). lra. }
    set (h := (B - A) / INR n).
    assert (Hh : 0 < h) by (apply Rdiv_lt_0_compat; lra).
    assert (Hhd : h < d).
    { unfold h. apply (Rmult_lt_reg_r (INR n)); [lra|]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra.
      replace (B - A) with ((B - A) / d * d) by (field; lra). nra. }
    assert (HB : A + INR n * h = B) by (unfold h; field; lra).
    set (P := upart A h n).
    assert (HP : tpart A B P) by (rewrite <- HB; apply upart_tpart; lra).
    assert (HPf : fine d A P) by (apply upart_fine; exact Hhd).
    exists (tagmax f P + 2 / h). intros y Hy.
    destruct (retag f h P A B y Hh HP (upart_widths n A h) Hy Hlt) as [l' [t [w [P1 [P2 [P3 [P4 P5]]]]]]].
    pose proof (Hfine P HP HPf) as F1. pose proof (Hfine l' P1 (P2 d HPf)) as F2.
    assert (Hdw : Rabs ((f y - f t) * w) < 2).
    { rewrite <- P3. replace (tsum f A l' - tsum f A P) with ((tsum f A l' - I) - (tsum f A P - I)) by ring.
      eapply Rle_lt_trans; [apply Rabs_triang|]. rewrite Rabs_Ropp. lra. }
    rewrite Rabs_mult, (Rabs_right w) in Hdw by lra.
    assert (Hq : Rabs (f y - f t) < 2 / h).
    { apply (Rmult_lt_reg_r h); [lra|]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra.
      pose proof (Rabs_pos (f y - f t)). nra. }
    pose proof (Rabs_triang (f y - f t) (f t)). replace (f y - f t + f t) with (f y) in H by ring. lra.
Qed.

(* E2. change of variables y = e^u for an RInt-integrable f (no
   antiderivative needed): exp maps fine partitions to fine partitions,
   and  |e^t (x' - x) - (e^x' - e^x)| <= e^b (x' - x)^2  on each cell *)
Fixpoint imgp (l : list (R * R)) : list (R * R) :=
  match l with [] => [] | (t, x) :: l' => (exp t, exp x) :: imgp l' end.

Lemma imgp_tpart : forall l a b, tpart a b l -> tpart (exp a) (exp b) (imgp l).
Proof.
  induction l as [|[t x] l IH]; simpl; intros a b H; [subst; reflexivity|].
  destruct H as [H1 [H2 H3]]. repeat split; [apply exp_le_mono; lra|apply exp_le_mono; lra|apply IH; exact H3].
Qed.

Lemma exp_cell : forall x x', x <= x' ->
  exp x * (x' - x) <= exp x' - exp x <= exp x' * (x' - x).
Proof.
  intros x x' Hx. destruct (Req_dec x x') as [E|Hne]; [subst; split; lra|].
  assert (Hlt : x < x') by lra.
  destruct (mvt_le exp exp x x' Hlt ltac:(intros; apply derivable_pt_lim_exp)) as [c [Hc Hc1]].
  destruct (mvt_ge exp exp x x' Hlt ltac:(intros; apply derivable_pt_lim_exp)) as [c' [Hc' Hc2]].
  pose proof (exp_le_mono x c ltac:(lra)). pose proof (exp_le_mono c' x' ltac:(lra)).
  split.
  - apply (Rmult_le_reg_r (/ (x' - x))); [apply Rinv_0_lt_compat; lra|].
    rewrite Rmult_assoc, Rinv_r by lra. rewrite Rmult_1_r. unfold Rdiv in Hc1. lra.
  - apply (Rmult_le_reg_r (/ (x' - x))); [apply Rinv_0_lt_compat; lra|].
    rewrite (Rmult_assoc (exp x')), Rinv_r by lra. rewrite Rmult_1_r. unfold Rdiv in Hc2. lra.
Qed.

Lemma imgp_fine : forall l a b d, tpart a b l -> fine (d / exp b) a l -> 0 < d -> fine d (exp a) (imgp l).
Proof.
  induction l as [|[t x] l IH]; simpl; intros a b d Hp Hf Hd; [trivial|].
  destruct Hp as [H1 [H2 H3]]. destruct Hf as [F1 F2].
  assert (Hxb : x <= b) by exact (tpart_le _ _ _ H3).
  split; [|apply (IH x b d H3 F2 Hd)].
  destruct (exp_cell a x ltac:(lra)) as [_ Hu].
  pose proof (exp_le_mono x b Hxb). pose proof (exp_pos b). pose proof (exp_pos x).
  assert (Hq : x - a < d / exp b) by exact F1.
  assert (Hq' : exp b * (x - a) < d).
  { apply (Rmult_lt_compat_l (exp b)) in Hq; [|lra]. unfold Rdiv in Hq.
    rewrite <- Rmult_assoc, (Rmult_comm (exp b) d), Rmult_assoc, Rinv_r in Hq by lra. lra. }
  assert (exp x * (x - a) <= exp b * (x - a)) by (apply Rmult_le_compat_r; lra). lra.
Qed.

Lemma tsum_img_close : forall f M l a b d, 0 <= M -> 0 <= d ->
  tpart a b l -> fine d a l ->
  (forall t, a <= t <= b -> Rabs (f (exp t)) <= M) ->
  Rabs (tsum (fun u => f (exp u) * exp u) a l - tsum f (exp a) (imgp l)) <= M * exp b * d * (b - a).
Proof.
  intros f M. induction l as [|[t x] l IH]; simpl; intros a b d HM Hd Hp Hf Hb.
  - subst. rewrite Rminus_diag, Rabs_R0. lra.
  - destruct Hp as [H1 [H2 H3]]. destruct Hf as [F1 F2].
    assert (Hxb : x <= b) by exact (tpart_le _ _ _ H3).
    pose proof (IH x b d HM Hd H3 F2 ltac:(intros; apply Hb; lra)) as IHx.
    replace (f (exp t) * exp t * (x - a) + tsum (fun u => f (exp u) * exp u) x l -
             (f (exp t) * (exp x - exp a) + tsum f (exp x) (imgp l)))
      with (f (exp t) * (exp t * (x - a) - (exp x - exp a)) +
            (tsum (fun u => f (exp u) * exp u) x l - tsum f (exp x) (imgp l))) by ring.
    eapply Rle_trans; [apply Rabs_triang|].
    rewrite Rabs_mult.
    destruct (exp_cell a x ltac:(lra)) as [Lo Up].
    pose proof (exp_le_mono a t ltac:(lra)). pose proof (exp_le_mono t x ltac:(lra)).
    pose proof (exp_le_mono x b Hxb).
    assert (Hc : Rabs (exp t * (x - a) - (exp x - exp a)) <= exp b * (x - a) * (x - a)).
    { apply Rabs_le. split.
      - assert (exp x * (x - a) <= exp b * (x - a)) by (apply Rmult_le_compat_r; lra).
        assert (exp t * (x - a) >= exp a * (x - a)) by (apply Rle_ge, Rmult_le_compat_r; lra).
        assert (exp x - exp a <= exp b * (x - a)) by lra.
        assert (0 <= exp a) by (left; apply exp_pos).
        assert (exp a * (x - a) >= 0) by (apply Rle_ge, Rmult_le_pos; lra).
        (* exp t (x-a) - (e^x - e^a) >= e^a (x-a) - e^x (x-a) >= -(e^x - e^a)(x-a) *)
        assert (exp t * (x - a) - (exp x - exp a) >= - ((exp x - exp a) * (x - a))).
        { assert ((exp x - exp a) * (x - a) >= exp x * (x - a) - exp t * (x - a)).
          { assert (exp x - exp a >= 0) by lra.
            assert ((exp x - exp a) * (x - a) >= 0) by (apply Rle_ge, Rmult_le_pos; lra).
            assert ((exp x - exp a) * (x - a) <= exp x * (x - a)) by nra. nra. }
          nra. }
        assert ((exp x - exp a) * (x - a) <= exp b * (x - a) * (x - a)).
        { apply Rmult_le_compat_r; lra. }
        lra.
      - assert (exp t * (x - a) <= exp x * (x - a)) by (apply Rmult_le_compat_r; lra).
        assert (exp x * (x - a) - (exp x - exp a) <= (exp x - exp a) * (x - a)).
        { (* e^x (x-a) - (e^x - e^a) <= e^x (x-a) - e^a (x-a) = (e^x - e^a)(x-a) *) lra. }
        assert (exp x * (x - a) <= exp b * (x - a)) by (apply Rmult_le_compat_r; lra).
        assert ((exp x - exp a) * (x - a) <= exp b * (x - a) * (x - a)).
        { apply Rmult_le_compat_r; lra. }
        lra. }
    pose proof (Hb t ltac:(lra)) as Hft. pose proof (Rabs_pos (f (exp t))).
    pose proof (exp_pos b).
    assert (Hcell : Rabs (f (exp t)) * Rabs (exp t * (x - a) - (exp x - exp a)) <= M * exp b * d * (x - a)).
    { eapply Rle_trans; [apply Rmult_le_compat; [lra|apply Rabs_pos|exact Hft|exact Hc]|].
      assert (exp b * (x - a) * (x - a) <= exp b * d * (x - a)).
      { assert (0 <= exp b * (x - a)) by (apply Rmult_le_pos; lra).
        replace (exp b * d * (x - a)) with (exp b * (x - a) * d) by ring.
        apply Rmult_le_compat_l; lra. }
      replace (M * exp b * d * (x - a)) with (M * (exp b * d * (x - a))) by ring.
      apply Rmult_le_compat_l; lra. }
    replace (M * exp b * d * (b - a)) with (M * exp b * d * (x - a) + M * exp b * d * (b - x)) by ring.
    lra.
Qed.

Theorem RInt_exp_change : forall f a b I, a <= b ->
  RInt f (exp a) (exp b) I -> RInt (fun u => f (exp u) * exp u) a b I.
Proof.
  intros f a b I Hab HI.
  destruct (RInt_bounded f _ _ I HI) as [M0 HM0].
  set (M := Rabs M0 + 1).
  assert (HM : 0 < M) by (unfold M; pose proof (Rabs_pos M0); lra).
  assert (HMb : forall t, a <= t <= b -> Rabs (f (exp t)) <= M).
  { intros t Ht. eapply Rle_trans; [apply HM0; split; apply exp_le_mono; lra|]. unfold M. pose proof (Rle_abs M0). lra. }
  split; [exact Hab|]. intros eps Heps.
  destruct HI as [_ HI]. destruct (HI (eps / 2) ltac:(lra)) as [d [Hd Hf]].
  pose proof (exp_pos b) as Heb.
  set (d2 := eps / (2 * (M * exp b * (b - a + 1)))).
  assert (Hd2 : 0 < d2).
  { unfold d2. apply Rdiv_lt_0_compat; [lra|]. apply Rmult_lt_0_compat; [lra|].
    apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat; lra|lra]. }
  exists (Rmin (d / exp b) d2). split; [apply Rmin_glb_lt; [apply Rdiv_lt_0_compat; lra|exact Hd2]|].
  intros l Hp Hfl.
  pose proof (imgp_tpart l a b Hp) as Hp'.
  pose proof (imgp_fine l a b d Hp (fine_mono l a _ _ (Rmin_l _ _) Hfl) Hd) as Hf'.
  pose proof (Hf _ Hp' Hf') as C1.
  pose proof (tsum_img_close f M l a b (Rmin (d / exp b) d2) ltac:(lra)
                ltac:(left; apply Rmin_glb_lt; [apply Rdiv_lt_0_compat; lra|exact Hd2]) Hp Hfl HMb) as C2.
  assert (C3 : M * exp b * Rmin (d / exp b) d2 * (b - a) < eps / 2).
  { assert (Hm : Rmin (d / exp b) d2 <= d2) by apply Rmin_r.
    assert (0 <= M * exp b) by (apply Rmult_le_pos; lra).
    assert (M * exp b * Rmin (d / exp b) d2 * (b - a) <= M * exp b * d2 * (b - a)).
    { apply Rmult_le_compat_r; [lra|]. apply Rmult_le_compat_l; lra. }
    assert (M * exp b * d2 * (b - a) < eps / 2).
    { unfold d2. assert (Hpos : 0 < M * exp b * (b - a + 1)) by (apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat|]; lra).
      replace (M * exp b * (eps / (2 * (M * exp b * (b - a + 1)))) * (b - a))
        with (eps / 2 * ((M * exp b * (b - a)) / (M * exp b * (b - a + 1)))) by (field; lra).
      assert (Hr : (M * exp b * (b - a)) / (M * exp b * (b - a + 1)) < 1).
      { apply (Rmult_lt_reg_r (M * exp b * (b - a + 1))); [lra|].
        unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. rewrite Rmult_1_r, Rmult_1_l.
        assert (0 < M * exp b) by (apply Rmult_lt_0_compat; lra). nra. }
      assert (0 <= (M * exp b * (b - a)) / (M * exp b * (b - a + 1))).
      { apply Rmult_le_pos; [apply Rmult_le_pos; [|lra]; apply Rmult_le_pos; lra|left; apply Rinv_0_lt_compat; lra]. }
      nra. }
    lra. }
  replace (tsum (fun u => f (exp u) * exp u) a l - I)
    with ((tsum (fun u => f (exp u) * exp u) a l - tsum f (exp a) (imgp l)) + (tsum f (exp a) (imgp l) - I)) by ring.
  eapply Rle_lt_trans; [apply Rabs_triang|]. lra.
Qed.


Print Assumptions tagmax_nonneg.
Print Assumptions retag.
Print Assumptions upart_widths.
Print Assumptions RInt_bounded.
Print Assumptions imgp_tpart.
Print Assumptions exp_cell.
Print Assumptions imgp_fine.
Print Assumptions tsum_img_close.
Print Assumptions RInt_exp_change.
