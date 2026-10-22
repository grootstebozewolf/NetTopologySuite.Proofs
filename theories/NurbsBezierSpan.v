(* ============================================================================
   NetTopologySuite.Proofs.NurbsBezierSpan
   ----------------------------------------------------------------------------
   One clamped Bézier span is the Bernstein basis, and de Boor on that
   knot vector is de Casteljau (claimId 0007-nurbs-bezier-span,
   witness a41_eq_definition_bz).

   Knots: p+1 zeros, then p+1 ones.  Degree-q basis functions are nonzero
   only on the index window [p-q, p], where they are Bernstein polynomials
   of degree q.  The de Boor blends on that window are the constant u, so
   the triangular scheme is de Casteljau.  The rational point is the
   homogeneous evaluation divided by a positive weight sum; unit weights
   recover the polynomial (bezier_eval).

   NurbsSumBridge supplies sum_first f (S p) = sum_f_R0 f p.  This file
   does not edit NurbsBasis, NurbsDeBoor, BernsteinBasis, or MkNurbs.

   No Admitted. No Axiom. No Parameter.
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List Bool PeanoNat Compare_dec.
From NTS.Proofs Require Import
  Distance NurbsDeBoor NurbsBasis BernsteinBasis NurbsSumBridge
  SheetHenCircEgg AtanIvt.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Clamped knot vector.  Indices that the recurrence reads stay <= 2p+1.     *)
(* -------------------------------------------------------------------------- *)

Definition bz_knots (p : nat) : list R :=
  repeat 0 (S p) ++ repeat 1 (S p).

Lemma bz_knots_length : forall p, length (bz_knots p) = (2 * S p)%nat.
Proof.
  intro p. unfold bz_knots. rewrite length_app, !repeat_length. lia.
Qed.

Lemma nth_repeat_prefix : forall (a : R) n i,
  (i < n)%nat -> nth i (repeat a n) 0 = a.
Proof.
  intros a n. induction n as [|n IH]; intros i Hi; [lia|].
  destruct i as [|i]; simpl; [reflexivity|]. apply IH. lia.
Qed.

Lemma bz_nth_lo : forall p i,
  (i <= p)%nat -> nthR (bz_knots p) i = 0.
Proof.
  intros p i Hi. unfold nthR, bz_knots.
  rewrite app_nth1 by (rewrite repeat_length; lia).
  apply nth_repeat_prefix. lia.
Qed.

Lemma bz_nth_hi : forall p i,
  (S p <= i <= 2 * p + 1)%nat -> nthR (bz_knots p) i = 1.
Proof.
  intros p i Hi. unfold nthR, bz_knots.
  rewrite app_nth2 by (rewrite repeat_length; lia).
  rewrite repeat_length.
  apply nth_repeat_prefix. lia.
Qed.

Lemma bz_nth_out : forall p i,
  (2 * S p <= i)%nat -> nthR (bz_knots p) i = 0.
Proof.
  intros p i Hi. unfold nthR.
  rewrite nth_overflow by (rewrite bz_knots_length; lia). reflexivity.
Qed.

Lemma bz_nth_bound : forall p i,
  (i <= 2 * p + 1)%nat -> (i < length (bz_knots p))%nat.
Proof.
  intros p i Hi. rewrite bz_knots_length. lia.
Qed.

Theorem bz_wf : forall p,
  let U := bz_knots p in
  knots_nondecreasing U /\
  clamped_lo U p /\
  clamped_hi U (S p) p /\
  nthR U p < nthR U (S p) /\
  length U = (S p + p + 1)%nat.
Proof.
  intro p. repeat split.
  - intros i Hi.
    destruct (le_dec i p) as [Hip|Hgt].
    + destruct (Nat.eq_dec i p) as [->|Hne].
      * rewrite bz_nth_lo by lia. rewrite bz_nth_hi by lia. lra.
      * rewrite !bz_nth_lo by lia. lra.
    + rewrite !bz_nth_hi by (rewrite bz_knots_length in Hi; lia). lra.
  - intros i Hi. rewrite !bz_nth_lo by lia. reflexivity.
  - intros i Hi. rewrite !bz_nth_hi by lia. reflexivity.
  - rewrite bz_nth_lo by lia. rewrite bz_nth_hi by lia. lra.
  - rewrite bz_knots_length. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* Degree 0.  u = 1 takes the Req_EM_T right-end branch (i = p).             *)
(* -------------------------------------------------------------------------- *)

Lemma andb_leb_neq : forall a b,
  a <> b -> andb (Nat.leb a b) (Nat.leb b a) = false.
Proof.
  intros a b Hne.
  destruct (lt_eq_lt_dec a b) as [[Hlt|Heq]|Hgt].
  - apply andb_false_intro2. apply Nat.leb_gt. exact Hlt.
  - contradiction.
  - apply andb_false_intro1. apply Nat.leb_gt. exact Hgt.
Qed.

Lemma indicator_flat0 : forall u,
  0 <= u ->
  match total_order_T 0 u with
  | inleft (left _) =>
      match total_order_T u 0 with
      | inleft (left _) => 1 | _ => 0 end
  | inleft (right _) =>
      match total_order_T u 0 with
      | inleft (left _) => 1 | _ => 0 end
  | inright _ => 0
  end = 0.
Proof.
  intros u Hu.
  destruct (total_order_T 0 u) as [[Hlt|Heq]|Hgt].
  - destruct (total_order_T u 0) as [[Hlt2|Heq2]|Hgt2]; lra.
  - destruct (total_order_T u 0) as [[Hlt2|Heq2]|Hgt2]; lra.
  - lra.
Qed.

Lemma indicator_01 : forall u,
  0 <= u < 1 ->
  match total_order_T 0 u with
  | inleft (left _) =>
      match total_order_T u 1 with
      | inleft (left _) => 1 | _ => 0 end
  | inleft (right _) =>
      match total_order_T u 1 with
      | inleft (left _) => 1 | _ => 0 end
  | inright _ => 0
  end = 1.
Proof.
  intros u [Hu0 Hu1].
  destruct (total_order_T 0 u) as [[Hlt|Heq]|Hgt].
  - destruct (total_order_T u 1) as [[Hlt2|Heq2]|Hgt2]; lra.
  - destruct (total_order_T u 1) as [[Hlt2|Heq2]|Hgt2]; lra.
  - lra.
Qed.

Lemma indicator_from_hi : forall u hi lo,
  u < hi ->
  match total_order_T hi u with
  | inleft (left _) =>
      match total_order_T u lo with
      | inleft (left _) => 1 | _ => 0 end
  | inleft (right _) =>
      match total_order_T u lo with
      | inleft (left _) => 1 | _ => 0 end
  | inright _ => 0
  end = 0.
Proof.
  intros u hi lo Hu.
  destruct (total_order_T hi u) as [[Hlt|Heq]|Hgt].
  - destruct (total_order_T u lo) as [[Hlt2|Heq2]|Hgt2]; lra.
  - destruct (total_order_T u lo) as [[Hlt2|Heq2]|Hgt2]; lra.
  - reflexivity.
Qed.

Lemma bz_basis_deg0 : forall p i u,
  0 <= u <= 1 ->
  N (bz_knots p) (S p) i O u =
    if andb (Nat.leb p i) (Nat.leb i p) then 1 else 0.
Proof.
  intros p i u Hu.
  assert (Hend : nthR (bz_knots p) (S p) = 1) by (apply bz_nth_hi; lia).
  cbn [N].
  destruct (Req_EM_T u (nthR (bz_knots p) (S p))) as [Heq|Hne].
  - replace (S p - 1)%nat with p by lia.
    destruct (Nat.eq_dec i p) as [->|Hneq].
    + rewrite !Nat.leb_refl. simpl. reflexivity.
    + rewrite andb_leb_neq by congruence. reflexivity.
  - assert (Hu1 : u < 1).
    { destruct (total_order_T u 1) as [[Hlt|Hequ]|Hgt].
      - exact Hlt.
      - exfalso. apply Hne. rewrite Hend. exact Hequ.
      - destruct Hu as [_ Hle]. lra. }
    destruct (lt_eq_lt_dec i p) as [[Hlt| ->]|Hgt].
    + rewrite (bz_nth_lo p i) by lia.
      rewrite (bz_nth_lo p (S i)) by lia.
      rewrite indicator_flat0 by (destruct Hu as [H0 _]; exact H0).
      rewrite andb_leb_neq by lia. reflexivity.
    + rewrite (bz_nth_lo p p) by lia. rewrite Hend.
      rewrite indicator_01 by (split; [destruct Hu as [H0 _]; exact H0 | exact Hu1]).
      rewrite !Nat.leb_refl. simpl. reflexivity.
    + rewrite andb_leb_neq by lia.
      destruct (le_dec i (2 * p + 1)) as [Hb|Ho].
      * rewrite (bz_nth_hi p i) by lia.
        rewrite indicator_from_hi by exact Hu1. reflexivity.
      * rewrite (bz_nth_out p i) by lia.
        rewrite (bz_nth_out p (S i)) by lia.
        rewrite indicator_flat0 by (destruct Hu as [H0 _]; exact H0).
        reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Window coefficients.  In-window denominators are 1, or 0 on a flat edge.  *)
(* -------------------------------------------------------------------------- *)

Lemma bz_left_edge : forall p q i u,
  (S q <= p)%nat ->
  i = (p - S q)%nat ->
  left_c (bz_knots p) i (S q) u = 0.
Proof.
  intros p q i u Hq ->. unfold left_c.
  assert (H0 : nthR (bz_knots p) (p - S q) = 0) by (apply bz_nth_lo; lia).
  assert (H1 : nthR (bz_knots p) (p - S q + S q) = 0).
  { replace (p - S q + S q)%nat with p by lia. apply bz_nth_lo. lia. }
  rewrite H0, H1.
  destruct (Req_EM_T (0 - 0) 0) as [_|Hn]; [reflexivity|].
  exfalso. apply Hn. ring.
Qed.

Lemma bz_left_open : forall p q i u,
  (S q <= p)%nat ->
  ((p - S q) < i)%nat ->
  (i <= p)%nat ->
  left_c (bz_knots p) i (S q) u = u.
Proof.
  intros p q i u Hq Hlo Hi. unfold left_c.
  assert (Ha : nthR (bz_knots p) i = 0) by (apply bz_nth_lo; lia).
  assert (Hb : nthR (bz_knots p) (i + S q) = 1) by (apply bz_nth_hi; lia).
  rewrite Ha, Hb.
  destruct (Req_EM_T (1 - 0) 0) as [Hz|Hnz].
  - lra.
  - field.
Qed.

Lemma bz_right_open : forall p q i u,
  (S q <= p)%nat ->
  ((p - S q) <= i)%nat ->
  (i < p)%nat ->
  right_c (bz_knots p) i (S q) u = 1 - u.
Proof.
  intros p q i u Hq Hlo Hi. unfold right_c.
  replace (i + S q + 1)%nat with (i + S q + 1)%nat by lia.
  assert (Ha : nthR (bz_knots p) (S i) = 0) by (apply bz_nth_lo; lia).
  assert (Hb : nthR (bz_knots p) (i + S q + 1) = 1) by (apply bz_nth_hi; lia).
  rewrite Ha, Hb.
  destruct (Req_EM_T (1 - 0) 0) as [Hz|Hnz].
  - lra.
  - field.
Qed.

Lemma bz_right_top : forall p q u,
  (S q <= p)%nat ->
  right_c (bz_knots p) p (S q) u = 0.
Proof.
  intros p q u Hq. unfold right_c.
  assert (Ha : nthR (bz_knots p) (S p) = 1) by (apply bz_nth_hi; lia).
  assert (Hb : nthR (bz_knots p) (p + S q + 1) = 1) by (apply bz_nth_hi; lia).
  rewrite Ha, Hb.
  destruct (Req_EM_T (1 - 1) 0) as [_|Hn]; [reflexivity|].
  exfalso. apply Hn. ring.
Qed.

Lemma bern_left_edge : forall n t, bern (S n) O t = (1 - t) * bern n O t.
Proof. intros n t. rewrite bern_Sn. ring. Qed.

Lemma bern_right_edge : forall n t, bern (S n) (S n) t = t * bern n n t.
Proof.
  intros n t. rewrite bern_Sn. rewrite (bern_gt n (S n) t) by lia. ring.
Qed.

Theorem bz_basis_window : forall p q i u,
  (q <= p)%nat ->
  0 <= u <= 1 ->
  N (bz_knots p) (S p) i q u =
    if andb (Nat.leb (p - q) i) (Nat.leb i p) then
      bern q (i - (p - q)) u else 0.
Proof.
  intros p q. induction q as [|q IH]; intros i u Hq Hu.
  - rewrite bz_basis_deg0 by exact Hu.
    replace (p - 0)%nat with p by lia.
    destruct (andb (Nat.leb p i) (Nat.leb i p)) eqn:Hb.
    + apply andb_prop in Hb. destruct Hb as [Ha Hc].
      apply Nat.leb_le in Ha. apply Nat.leb_le in Hc.
      assert (Heq : i = p) by lia. subst.
      replace (p - p)%nat with 0%nat by lia. simpl. reflexivity.
    + reflexivity.
  - assert (Hq' : (q <= p)%nat) by lia.
    rewrite N_step.
    rewrite (IH i u Hq' Hu).
    rewrite (IH (S i) u Hq' Hu).
    set (lo := (p - S q)%nat).
    assert (Hpq : (p - q)%nat = S lo) by lia.
    rewrite !Hpq.
    destruct (Nat.leb lo i) eqn:Hloi; destruct (Nat.leb i p) eqn:Hip;
      cbn [andb]; cbn iota.
    + apply Nat.leb_le in Hloi. apply Nat.leb_le in Hip.
      destruct (Nat.eq_dec i lo) as [->|Hnei].
      * rewrite (bz_left_edge p q lo u Hq) by reflexivity.
        rewrite (bz_right_open p q lo u Hq) by lia.
        replace (andb (Nat.leb (S lo) lo) (Nat.leb lo p)) with false
          by (symmetry; apply andb_false_intro1; apply Nat.leb_gt; lia).
        replace (andb (Nat.leb (S lo) (S lo)) (Nat.leb (S lo) p)) with true
          by (symmetry; apply andb_true_intro; split;
              [apply Nat.leb_refl | apply Nat.leb_le; lia]).
        cbn iota.
        replace (S lo - S lo)%nat with 0%nat by lia.
        replace (lo - lo)%nat with 0%nat by lia.
        rewrite Rmult_0_l, Rplus_0_l. rewrite bern_Sn. rewrite ?andb_false_r. cbn [andb]; cbn iota. ring.
      * destruct (Nat.eq_dec i p) as [->|Hnep].
        -- rewrite (bz_left_open p q p u Hq) by lia.
           rewrite (bz_right_top p q u Hq).
           assert (Ha : Nat.leb (S lo) p = true) by (apply Nat.leb_le; lia).
           assert (Hb : Nat.leb p p = true) by apply Nat.leb_refl.
           assert (Hc : Nat.leb (S p) p = false) by (apply Nat.leb_gt; lia).
           rewrite ?Ha, ?Hb, ?Hc. cbn [andb]; cbn iota.
           replace (p - S lo)%nat with q by lia.
           replace (p - lo)%nat with (S q) by lia.
           rewrite Rmult_0_l, Rplus_0_r. rewrite <- bern_right_edge. reflexivity.
        -- rewrite (bz_left_open p q i u Hq) by lia.
           rewrite (bz_right_open p q i u Hq) by lia.
           assert (Hslo : Nat.leb (S lo) i = true) by (apply Nat.leb_le; lia).
           assert (Hip' : Nat.leb i p = true) by (apply Nat.leb_le; lia).
           assert (Hsi : Nat.leb (S i) p = true) by (apply Nat.leb_le; lia).
           assert (HsloS : Nat.leb (S lo) (S i) = true) by (apply Nat.leb_le; lia).
           rewrite ?Hslo, ?Hip', ?Hsi, ?HsloS. cbn [andb]; cbn iota.
           replace (i - S lo)%nat with (i - lo - 1)%nat by lia.
           replace (S i - S lo)%nat with (i - lo)%nat by lia.
           remember (i - lo)%nat as j eqn:Hj.
           destruct j as [|k]; [lia|].
           rewrite bern_Sn. cbn iota.
           replace (S k - 1)%nat with k by lia.
           ring.
    + apply Nat.leb_gt in Hip.
      replace (andb (Nat.leb (S lo) i) (Nat.leb i p)) with false
        by (symmetry; apply andb_false_intro2; apply Nat.leb_gt; lia).
      replace (andb (Nat.leb (S lo) (S i)) (Nat.leb (S i) p)) with false
        by (symmetry; apply andb_false_intro2; apply Nat.leb_gt; lia).
      rewrite ?andb_false_r. rewrite ?andb_false_r. cbn [andb]; cbn iota. ring.
    + apply Nat.leb_gt in Hloi.
      assert (Hslo : Nat.leb (S lo) i = false) by (apply Nat.leb_gt; lia).
      assert (HsloS : Nat.leb (S lo) (S i) = false) by (apply Nat.leb_gt; lia).
      rewrite ?Hslo, ?HsloS. cbn [andb]; cbn iota. ring.
    + apply Nat.leb_gt in Hloi. apply Nat.leb_gt in Hip. lia.
Qed.

Corollary bz_basis_bern : forall p i u,
  (i <= p)%nat ->
  0 <= u <= 1 ->
  N (bz_knots p) (S p) i p u = bern p i u.
Proof.
  intros p i u Hi Hu.
  rewrite (bz_basis_window p p i u) by (exact Hu || lia).
  replace (p - p)%nat with 0%nat by lia.
  replace (Nat.leb 0 i) with true by (symmetry; apply Nat.leb_le; lia).
  replace (Nat.leb i p) with true by (symmetry; apply Nat.leb_le; exact Hi).
  simpl. replace (i - 0)%nat with i by lia. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* de Boor alpha is u, so the rounds are de Casteljau.                        *)
(* -------------------------------------------------------------------------- *)

Lemma bz_alpha : forall p k j u,
  (1 <= k)%nat -> (k <= j)%nat -> (j <= p)%nat ->
  alpha_at (bz_knots p) p p k j u = u.
Proof.
  intros p k j u Hk Hj Hp. unfold alpha_at, knot_idx.
  replace (p - p + j)%nat with j by lia.
  rewrite (bz_nth_lo p j) by lia.
  assert (Hhi : nthR (bz_knots p) (j + (p - k) + 1) = 1).
  { apply bz_nth_hi. lia. }
  rewrite Hhi. field.
Qed.

Definition round_casteljau (k : nat) (u : R) (row : list R) : list R :=
  map (fun j =>
    if Nat.ltb j k then nthR row j
    else blend u (nthR row (j - 1)) (nthR row j))
    (seq 0 (length row)).

Fixpoint rounds_casteljau (m : nat) (u : R) (row : list R) : list R :=
  match m with
  | O => row
  | S m' => round_casteljau (S m') u (rounds_casteljau m' u row)
  end.

Lemma round_casteljau_length : forall k u row,
  length (round_casteljau k u row) = length row.
Proof.
  intros. unfold round_casteljau. rewrite length_map, length_seq. reflexivity.
Qed.

Lemma rounds_casteljau_length : forall m u row,
  length (rounds_casteljau m u row) = length row.
Proof.
  induction m as [|m IH]; intros; simpl; [reflexivity|].
  rewrite round_casteljau_length. apply IH.
Qed.

Lemma round_casteljau_nth : forall k u row j,
  (j < length row)%nat ->
  nth j (round_casteljau k u row) 0 =
    if Nat.ltb j k then nthR row j
    else blend u (nthR row (j - 1)) (nthR row j).
Proof.
  intros k u row j Hj. unfold round_casteljau.
  rewrite map_nth_seq by exact Hj. reflexivity.
Qed.

Lemma round_deboor_casteljau : forall p k u row,
  (1 <= k)%nat ->
  length row = S p ->
  round_deboor k p p (bz_knots p) u row = round_casteljau k u row.
Proof.
  intros p k u row Hk Hlen.
  unfold round_deboor, round_casteljau. apply map_ext_in.
  intros j Hj.
  assert (Hjlen : (j < length row)%nat).
  { apply in_seq in Hj. lia. }
  assert (Hjp : (j <= p)%nat) by lia.
  destruct (Nat.ltb j k) eqn:Hlt.
  - reflexivity.
  - apply Nat.ltb_ge in Hlt. rewrite bz_alpha by lia. reflexivity.
Qed.

Lemma bz_rounds_casteljau : forall p m u row,
  (m <= p)%nat ->
  length row = S p ->
  deboor_rounds m p p (bz_knots p) u row = rounds_casteljau m u row.
Proof.
  intros p m. induction m as [|m IH]; intros u row Hm Hlen.
  - reflexivity.
  - simpl. rewrite (IH u row) by lia.
    apply round_deboor_casteljau; [lia|].
    rewrite rounds_casteljau_length. exact Hlen.
Qed.

(* -------------------------------------------------------------------------- *)
(* de Casteljau slot = Bernstein combination.                                 *)
(* -------------------------------------------------------------------------- *)

Lemma sum_f_R0_ext : forall (f g : nat -> R) n,
  (forall i, (i <= n)%nat -> f i = g i) ->
  sum_f_R0 f n = sum_f_R0 g n.
Proof.
  intros f g n H. induction n as [|n IH].
  - rewrite !sum_f_R0_0. apply H. lia.
  - rewrite !sum_f_R0_S. rewrite IH by (intros i Hi; apply H; lia).
    f_equal. apply H. lia.
Qed.

Lemma sum_f_R0_plus : forall (f g : nat -> R) n,
  sum_f_R0 (fun i => f i + g i) n = sum_f_R0 f n + sum_f_R0 g n.
Proof.
  intros f g n. induction n as [|n IH].
  - rewrite !sum_f_R0_0. ring.
  - rewrite !sum_f_R0_S, IH. ring.
Qed.

Lemma sum_f_R0_scale : forall a (f : nat -> R) n,
  sum_f_R0 (fun i => a * f i) n = a * sum_f_R0 f n.
Proof.
  intros a f n. induction n as [|n IH].
  - rewrite !sum_f_R0_0. ring.
  - rewrite !sum_f_R0_S, IH. ring.
Qed.

Lemma sum_f_R0_drop_last : forall (f : nat -> R) n,
  f (S n) = 0 -> sum_f_R0 f (S n) = sum_f_R0 f n.
Proof.
  intros f n H. rewrite sum_f_R0_S, H. ring.
Qed.

Lemma sum_prev_shift : forall (g : nat -> R) m,
  sum_f_R0 (fun i => match i with O => 0 | S i' => g i' end) (S m)
  = sum_f_R0 g m.
Proof.
  intros g m. induction m as [|m IH].
  - rewrite sum_f_R0_S, sum_f_R0_0. simpl. ring.
  - rewrite (sum_f_R0_S (fun i => match i with O => 0 | S i' => g i' end) (S m)).
    rewrite IH. rewrite (sum_f_R0_S g m). simpl. ring.
Qed.

Lemma bern_combo_step : forall m u (f : nat -> R),
  sum_f_R0 (fun i => bern (S m) i u * f i) (S m)
  = (1 - u) * sum_f_R0 (fun i => bern m i u * f i) m
    + u * sum_f_R0 (fun i => bern m i u * f (S i)) m.
Proof.
  intros m u f.
  rewrite (sum_f_R0_ext
    (fun i => bern (S m) i u * f i)
    (fun i => (1 - u) * (bern m i u * f i)
            + u * ((match i with O => 0 | S i' => bern m i' u end) * f i))
    (S m)).
  - rewrite sum_f_R0_plus.
    rewrite (sum_f_R0_scale (1 - u) (fun i => bern m i u * f i) (S m)).
    rewrite (sum_f_R0_drop_last (fun i => bern m i u * f i) m)
      by (rewrite bern_gt by lia; ring).
    rewrite (sum_f_R0_scale u
      (fun i => (match i with O => 0 | S i' => bern m i' u end) * f i) (S m)).
    rewrite (sum_f_R0_ext
      (fun i => (match i with O => 0 | S i' => bern m i' u end) * f i)
      (fun i => match i with O => 0 | S i' => bern m i' u * f (S i') end)
      (S m)).
    + rewrite (sum_prev_shift (fun i => bern m i u * f (S i)) m). ring.
    + intros i Hi. destruct i as [|i]; ring.
  - intros i Hi. rewrite bern_Sn. destruct i as [|i]; ring.
Qed.

Lemma casteljau_slot : forall m u row j,
  (m <= j)%nat ->
  (j < length row)%nat ->
  nth j (rounds_casteljau m u row) 0 =
    sum_f_R0 (fun i => bern m i u * nthR row (j - m + i)) m.
Proof.
  induction m as [|m IH]; intros u row j Hmj Hj.
  - simpl.
    replace (j - 0 + 0)%nat with j by lia. unfold nthR. ring.
  - simpl.
    rewrite round_casteljau_nth
      by (rewrite rounds_casteljau_length; exact Hj).
    assert (Hlt : Nat.ltb j (S m) = false) by (apply Nat.ltb_ge; lia).
    rewrite Hlt. unfold blend, nthR.
    rewrite (IH u row (j - 1)%nat) by lia.
    rewrite (IH u row j) by lia.
    set (f := fun i => nthR row ((j - S m + i)%nat)).
    rewrite (sum_f_R0_ext
      (fun i => bern m i u * nthR row ((j - 1 - m + i)%nat))
      (fun i => bern m i u * f i) m).
    + rewrite (sum_f_R0_ext
        (fun i => bern m i u * nthR row ((j - m + i)%nat))
        (fun i => bern m i u * f (S i)) m).
      * rewrite <- (bern_combo_step m u f). reflexivity.
      * intros i Hi. unfold f. f_equal.
        replace (j - m + i)%nat with (j - S m + S i)%nat by lia. reflexivity.
    + intros i Hi. unfold f. f_equal.
      replace (j - 1 - m + i)%nat with (j - S m + i)%nat by lia. reflexivity.
Qed.

Theorem bz_deboor_bern : forall p (slot : nat -> R) u,
  nth p (deboor_rounds p p p (bz_knots p) u (init_row slot p)) 0 =
  sum_f_R0 (fun i => bern p i u * slot i) p.
Proof.
  intros p slot u.
  rewrite (bz_rounds_casteljau p p u (init_row slot p))
    by (try apply init_row_length; lia).
  rewrite casteljau_slot
    by (try rewrite init_row_length; lia).
  apply sum_f_R0_ext. intros i Hi.
  replace (p - p + i)%nat with i by lia.
  unfold nthR. rewrite init_row_nth by lia. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Homogeneous evaluator.  Unit weights are the polynomial bezier_eval.       *)
(* -------------------------------------------------------------------------- *)

Definition unit_weights (p : nat) : list R := repeat 1 (S p).

Lemma unit_weight_nth : forall p i,
  (i <= p)%nat -> nthR (unit_weights p) i = 1.
Proof.
  intros p i Hi. unfold nthR, unit_weights.
  apply nth_repeat_prefix. lia.
Qed.

Definition bz_hom_eval (p : nat) (ctrl : list Point) (W : list R) (u : R)
  : Point :=
  mkPoint
    (nth p (deboor_rounds p p p (bz_knots p) u
            (init_row (fun j => hom_x ctrl W j) p)) 0 /
     nth p (deboor_rounds p p p (bz_knots p) u
            (init_row (fun j => nthR W j) p)) 0)
    (nth p (deboor_rounds p p p (bz_knots p) u
            (init_row (fun j => hom_y ctrl W j) p)) 0 /
     nth p (deboor_rounds p p p (bz_knots p) u
            (init_row (fun j => nthR W j) p)) 0).

Definition bezier_eval (p : nat) (ctrl : list Point) (u : R) : Point :=
  bz_hom_eval p ctrl (unit_weights p) u.

Lemma sum_f_R0_nonneg : forall (f : nat -> R) n,
  (forall i, (i <= n)%nat -> 0 <= f i) -> 0 <= sum_f_R0 f n.
Proof.
  intros f n H. induction n as [|n IH].
  - rewrite sum_f_R0_0. apply H. lia.
  - rewrite sum_f_R0_S. apply Rplus_le_le_0_compat.
    + apply IH. intros i Hi. apply H. lia.
    + apply H. lia.
Qed.

Lemma sum_f_R0_zero_term : forall (f : nat -> R) n i,
  (forall k, (k <= n)%nat -> 0 <= f k) ->
  sum_f_R0 f n = 0 ->
  (i <= n)%nat ->
  f i = 0.
Proof.
  intros f n. induction n as [|n IH]; intros i Hnn Hz Hi.
  - rewrite sum_f_R0_0 in Hz. replace i with 0%nat by lia. exact Hz.
  - rewrite sum_f_R0_S in Hz.
    assert (Hsnn : 0 <= sum_f_R0 f n).
    { apply sum_f_R0_nonneg. intros k Hk. apply Hnn. lia. }
    assert (Hfnn : 0 <= f (S n)) by (apply Hnn; lia).
    assert (Hs : sum_f_R0 f n = 0) by lra.
    assert (Hf : f (S n) = 0) by lra.
    destruct (Nat.eq_dec i (S n)) as [->|Hne].
    + exact Hf.
    + apply IH; [intros k Hk; apply Hnn; lia | exact Hs | lia].
Qed.

Lemma sum_f_R0_zeros : forall n, sum_f_R0 (fun _ => 0) n = 0.
Proof.
  induction n as [|n IH].
  - rewrite sum_f_R0_0. reflexivity.
  - rewrite sum_f_R0_S, IH. ring.
Qed.

Lemma bz_den_pos : forall p u W,
  0 <= u <= 1 ->
  (forall i, (i <= p)%nat -> 0 < nthR W i) ->
  0 < sum_f_R0 (fun i => bern p i u * nthR W i) p.
Proof.
  intros p u W Hu HW.
  set (s := sum_f_R0 (fun i => bern p i u * nthR W i) p).
  assert (Hnn : forall i, (i <= p)%nat -> 0 <= bern p i u * nthR W i).
  { intros i Hi. apply Rmult_le_pos.
    - apply bern_nonneg; lra.
    - apply Rlt_le. apply HW. exact Hi. }
  assert (Hs0 : 0 <= s) by (unfold s; apply sum_f_R0_nonneg; exact Hnn).
  destruct (Req_EM_T s 0) as [Hz|Hnz].
  - exfalso.
    assert (Hber : forall i, (i <= p)%nat -> bern p i u = 0).
    { intros i Hi.
      assert (E : bern p i u * nthR W i = 0).
      { apply (sum_f_R0_zero_term (fun k => bern p k u * nthR W k) p i); assumption. }
      apply Rmult_integral in E. destruct E as [Eb|Ew].
      + exact Eb.
      + exfalso. apply (Rgt_not_eq _ 0 (HW i Hi)). exact Ew. }
    assert (Hsum0 : sum_f_R0 (fun i => bern p i u) p = 0).
    { rewrite (sum_f_R0_ext _ (fun _ => 0) p).
      - apply sum_f_R0_zeros.
      - intros i Hi. apply Hber. exact Hi. }
    rewrite bern_partition in Hsum0. lra.
  - destruct (total_order_T 0 s) as [[Hlt|Heq]|Hgt].
    + exact Hlt.
    + exfalso. apply Hnz. symmetry. exact Heq.
    + lra.
Qed.

Lemma point_ext : forall a b : Point, px a = px b -> py a = py b -> a = b.
Proof.
  intros [xa ya] [xb yb]. simpl. intros. subst. reflexivity.
Qed.

(* WITNESS {"claimId":"0007-nurbs-bezier-span","topic":"metric","lemma":"a41_eq_definition_bz","title":"One clamped span: de Boor equals the rational Bernstein combination","file":"theories/NurbsBezierSpan.v","witness":"a41_eq_definition_bz","board":"0007-nurbs-bezier-span"} *)

Theorem a41_eq_definition_bz : forall p (ctrl : list Point) (W : list R) u,
  0 <= u <= 1 ->
  length ctrl = S p ->
  length W = S p ->
  (forall i, (i <= p)%nat -> 0 < nthR W i) ->
  0 < sum_f_R0 (fun i => bern p i u * nthR W i) p /\
  nth p (deboor_rounds p p p (bz_knots p) u
          (init_row (fun j => hom_x ctrl W j) p)) 0 =
    sum_f_R0 (fun i => bern p i u * hom_x ctrl W i) p /\
  nth p (deboor_rounds p p p (bz_knots p) u
          (init_row (fun j => hom_y ctrl W j) p)) 0 =
    sum_f_R0 (fun i => bern p i u * hom_y ctrl W i) p /\
  nth p (deboor_rounds p p p (bz_knots p) u
          (init_row (fun j => nthR W j) p)) 0 =
    sum_f_R0 (fun i => bern p i u * nthR W i) p /\
  bz_hom_eval p ctrl W u =
    mkPoint
      (sum_f_R0 (fun i => bern p i u * hom_x ctrl W i) p /
       sum_f_R0 (fun i => bern p i u * nthR W i) p)
      (sum_f_R0 (fun i => bern p i u * hom_y ctrl W i) p /
       sum_f_R0 (fun i => bern p i u * nthR W i) p).
Proof.
  intros p ctrl W u Hu Hlc HlW Hpos.
  assert (Hix : forall i, (i <= p)%nat -> (i < length ctrl)%nat) by (intros; lia).
  assert (Hiw : forall i, (i <= p)%nat -> (i < length W)%nat) by (intros; lia).
  clear Hix Hiw.
  repeat split.
  - apply bz_den_pos; assumption.
  - apply bz_deboor_bern.
  - apply bz_deboor_bern.
  - apply bz_deboor_bern.
  - unfold bz_hom_eval. rewrite !bz_deboor_bern. reflexivity.
Qed.

Lemma bezier_eval_poly : forall p ctrl u,
  bezier_eval p ctrl u =
  mkPoint
    (sum_f_R0 (fun i => bern p i u * px (nth i ctrl (mkPoint 0 0))) p)
    (sum_f_R0 (fun i => bern p i u * py (nth i ctrl (mkPoint 0 0))) p).
Proof.
  intros p ctrl u. unfold bezier_eval, bz_hom_eval.
  rewrite !bz_deboor_bern.
  assert (Hden :
    sum_f_R0 (fun i => bern p i u * nthR (unit_weights p) i) p = 1).
  { rewrite (sum_f_R0_ext _ (fun i => bern p i u) p).
    - apply bern_partition.
    - intros i Hi. rewrite unit_weight_nth by exact Hi. ring. }
  rewrite Hden.
  rewrite (sum_f_R0_ext
    (fun i => bern p i u * hom_x ctrl (unit_weights p) i)
    (fun i => bern p i u * px (nth i ctrl (mkPoint 0 0))) p).
  - rewrite (sum_f_R0_ext
      (fun i => bern p i u * hom_y ctrl (unit_weights p) i)
      (fun i => bern p i u * py (nth i ctrl (mkPoint 0 0))) p).
    + unfold Rdiv. rewrite Rinv_1, !Rmult_1_r. reflexivity.
    + intros i Hi. unfold hom_y. rewrite unit_weight_nth by exact Hi. ring.
  - intros i Hi. unfold hom_x. rewrite unit_weight_nth by exact Hi. ring.
Qed.

Lemma bern0_O : forall n, bern n O 0 = 1.
Proof.
  induction n as [|n IH]; simpl; [|rewrite IH]; ring.
Qed.

Lemma bern0_S : forall n i, bern n (S i) 0 = 0.
Proof.
  induction n as [|n IH]; intros i; simpl.
  - reflexivity.
  - rewrite IH. destruct i as [|i]; ring.
Qed.

Lemma bern1_diag : forall n, bern n n 1 = 1.
Proof.
  induction n as [|n IH]; simpl.
  - reflexivity.
  - rewrite IH. ring.
Qed.

Lemma bern1_below : forall n i, (i < n)%nat -> bern n i 1 = 0.
Proof.
  induction n as [|n IH]; intros i Hi; [lia|].
  destruct i as [|i].
  - simpl. ring.
  - simpl. rewrite (IH i) by lia. ring.
Qed.

Lemma sum_f_R0_single0 : forall n (f : nat -> R),
  (forall i, (0 < i)%nat -> (i <= n)%nat -> f i = 0) ->
  sum_f_R0 f n = f 0%nat.
Proof.
  intros n f H. induction n as [|n IH].
  - rewrite sum_f_R0_0. reflexivity.
  - rewrite sum_f_R0_S. rewrite IH by (intros i Hi1 Hi2; apply H; lia).
    rewrite (H (S n)) by lia. ring.
Qed.

Lemma sum_f_R0_prefix0 : forall n (f : nat -> R),
  (forall i, (i < n)%nat -> f i = 0) ->
  sum_f_R0 f n = f n.
Proof.
  induction n as [|n IH]; intros f H.
  - rewrite sum_f_R0_0. reflexivity.
  - rewrite sum_f_R0_S.
    assert (Hs : sum_f_R0 f n = f n).
    { apply IH. intros i Hi. apply H. lia. }
    rewrite Hs. rewrite (H n) by lia. ring.
Qed.

Lemma sum_bern_at_0 : forall p (g : nat -> R),
  sum_f_R0 (fun i => bern p i 0 * g i) p = g 0%nat.
Proof.
  intros p g. rewrite sum_f_R0_single0.
  - rewrite bern0_O. ring.
  - intros i Hi1 Hi2. destruct i as [|i]; [lia|]. rewrite bern0_S. ring.
Qed.

Lemma sum_bern_at_1 : forall p (g : nat -> R),
  sum_f_R0 (fun i => bern p i 1 * g i) p = g p.
Proof.
  intros p g. rewrite sum_f_R0_prefix0.
  - rewrite bern1_diag. ring.
  - intros i Hi. rewrite bern1_below by exact Hi. ring.
Qed.

Lemma bezier_eval_0 : forall p ctrl,
  bezier_eval p ctrl 0 = nth 0 ctrl (mkPoint 0 0).
Proof.
  intros p ctrl. rewrite bezier_eval_poly. apply point_ext; cbn [px py].
  - rewrite sum_bern_at_0. reflexivity.
  - rewrite sum_bern_at_0. reflexivity.
Qed.

Lemma bezier_eval_1 : forall p ctrl,
  bezier_eval p ctrl 1 = nth p ctrl (mkPoint 0 0).
Proof.
  intros p ctrl. rewrite bezier_eval_poly. apply point_ext; cbn [px py].
  - rewrite sum_bern_at_1. reflexivity.
  - rewrite sum_bern_at_1. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Fixtures.                                                                  *)
(* -------------------------------------------------------------------------- *)

Definition tt_quad_ctrl : list Point :=
  [mkPoint 0 0; mkPoint 1 2; mkPoint 2 0].

Lemma tt_quad_fixtures :
  bezier_eval 2 tt_quad_ctrl 0 = mkPoint 0 0 /\
  bezier_eval 2 tt_quad_ctrl (1 / 2) = mkPoint 1 1 /\
  bezier_eval 2 tt_quad_ctrl 1 = mkPoint 2 0.
Proof.
  split; [|split].
  - rewrite bezier_eval_0. reflexivity.
  - rewrite bezier_eval_poly. apply point_ext; cbn [px py].
    + rewrite sum_f_R0_S, sum_f_R0_S, sum_f_R0_0.
      rewrite <- bern2_0_bern, <- bern2_1_bern, <- bern2_2_bern.
      unfold bern2_0, bern2_1, bern2_2, tt_quad_ctrl. cbn [nth px]. field.
    + rewrite sum_f_R0_S, sum_f_R0_S, sum_f_R0_0.
      rewrite <- bern2_0_bern, <- bern2_1_bern, <- bern2_2_bern.
      unfold bern2_0, bern2_1, bern2_2, tt_quad_ctrl. cbn [nth py]. field.
  - rewrite bezier_eval_1. reflexivity.
Qed.

Definition cubic_third_ctrl : list Point :=
  [mkPoint 0 0; mkPoint 27 0; mkPoint 0 27; mkPoint 27 27].

Lemma cubic_third_fixtures :
  bezier_eval 3 cubic_third_ctrl (1 / 3) = mkPoint 13 7.
Proof.
  rewrite bezier_eval_poly. apply point_ext; cbn [px py].
  - rewrite sum_f_R0_S, sum_f_R0_S, sum_f_R0_S, sum_f_R0_0.
    rewrite <- bern3_0_bern, <- bern3_1_bern, <- bern3_2_bern, <- bern3_3_bern.
    unfold bern3_0, bern3_1, bern3_2, bern3_3, cubic_third_ctrl.
    cbn [nth px]. field.
  - rewrite sum_f_R0_S, sum_f_R0_S, sum_f_R0_S, sum_f_R0_0.
    rewrite <- bern3_0_bern, <- bern3_1_bern, <- bern3_2_bern, <- bern3_3_bern.
    unfold bern3_0, bern3_1, bern3_2, bern3_3, cubic_third_ctrl.
    cbn [nth py]. field.
Qed.

(* Chart quarter: controls (1,0), (1,1), (0,1), weights (1, cos(π/4), 1). *)

Definition chart_ctrl : list Point :=
  [mkPoint 1 0; mkPoint 1 1; mkPoint 0 1].

Definition chart_w : list R := [1; sqrt 2 / 2; 1].

Definition chart_egg : CircularEgg :=
  mkCircularEgg (mkPoint 0 0) 1 0 (PI / 2).

Definition chart_uden (t : R) : R := sqrt 2 + (1 - sqrt 2) * t.
Definition chart_u (t : R) : R := t / chart_uden t.
Definition chart_phi (t : R) : R := 2 * atan3 (chart_u t).

Definition chart_numx (t : R) : R :=
  sum_f_R0 (fun i => bern 2 i t * hom_x chart_ctrl chart_w i) 2.
Definition chart_numy (t : R) : R :=
  sum_f_R0 (fun i => bern 2 i t * hom_y chart_ctrl chart_w i) 2.
Definition chart_den (t : R) : R :=
  sum_f_R0 (fun i => bern 2 i t * nthR chart_w i) 2.

Lemma sqrt2_sqr : sqrt 2 * sqrt 2 = 2.
Proof. apply sqrt_sqrt. lra. Qed.

Lemma sqrt2_pos : 0 < sqrt 2.
Proof. apply sqrt_lt_R0. lra. Qed.

Lemma chart_w_pos : forall i, (i <= 2)%nat -> 0 < nthR chart_w i.
Proof.
  intros i Hi. destruct i as [|[|[|i]]].
  - unfold nthR, chart_w. simpl. lra.
  - unfold nthR, chart_w. simpl.
    apply Rdiv_lt_0_compat; [exact sqrt2_pos | lra].
  - unfold nthR, chart_w. simpl. lra.
  - lia.
Qed.

Lemma chart_den_pos : forall t, 0 <= t <= 1 -> 0 < chart_den t.
Proof.
  intros t Ht. unfold chart_den. apply bz_den_pos; [exact Ht|].
  intros i Hi. apply chart_w_pos. lia.
Qed.

Lemma chart_uden_pos : forall t, 0 <= t <= 1 -> 0 < chart_uden t.
Proof.
  intros t [Ht0 Ht1]. unfold chart_uden.
  replace (sqrt 2 + (1 - sqrt 2) * t) with (sqrt 2 * (1 - t) + t) by ring.
  destruct (total_order_T 0 t) as [[Hlt|Heq]|Hgt].
  - assert (0 <= sqrt 2 * (1 - t)).
    { apply Rmult_le_pos; [apply Rlt_le, sqrt2_pos | lra]. }
    lra.
  - subst. replace (sqrt 2 * (1 - 0) + 0) with (sqrt 2) by ring. exact sqrt2_pos.
  - lra.
Qed.

Lemma twice_half_sqrt2 : forall x, 2 * x * (sqrt 2 / 2) = x * sqrt 2.
Proof. intro x. field. Qed.

Lemma twice_half_sqrt2_1 : forall x, 2 * x * (1 * (sqrt 2 / 2)) = x * sqrt 2.
Proof. intro x. field. Qed.

Lemma chart_numx_poly : forall t,
  chart_numx t = (1 - t) * (1 - t) + t * (1 - t) * sqrt 2.
Proof.
  intro t. unfold chart_numx, hom_x, nthR, chart_ctrl, chart_w.
  rewrite sum_f_R0_S, sum_f_R0_S, sum_f_R0_0.
  cbn [nth px].
  rewrite <- bern2_0_bern, <- bern2_1_bern, <- bern2_2_bern.
  unfold bern2_0, bern2_1, bern2_2.
  rewrite (twice_half_sqrt2_1 (t * (1 - t))).
  ring.
Qed.

Lemma chart_numy_poly : forall t,
  chart_numy t = t * (1 - t) * sqrt 2 + t * t.
Proof.
  intro t. unfold chart_numy, hom_y, nthR, chart_ctrl, chart_w.
  rewrite sum_f_R0_S, sum_f_R0_S, sum_f_R0_0.
  cbn [nth py].
  rewrite <- bern2_0_bern, <- bern2_1_bern, <- bern2_2_bern.
  unfold bern2_0, bern2_1, bern2_2.
  rewrite (twice_half_sqrt2_1 (t * (1 - t))).
  ring.
Qed.

Lemma chart_den_poly : forall t,
  chart_den t = (1 - t) * (1 - t) + t * (1 - t) * sqrt 2 + t * t.
Proof.
  intro t. unfold chart_den, nthR, chart_w.
  rewrite sum_f_R0_S, sum_f_R0_S, sum_f_R0_0.
  cbn [nth].
  rewrite <- bern2_0_bern, <- bern2_1_bern, <- bern2_2_bern.
  unfold bern2_0, bern2_1, bern2_2.
  rewrite (twice_half_sqrt2 (t * (1 - t))).
  ring.
Qed.

Lemma two_numx_uden : forall t,
  2 * chart_numx t = chart_uden t * chart_uden t - t * t.
Proof.
  intro t. rewrite chart_numx_poly. unfold chart_uden.
  set (s := sqrt 2).
  assert (Hs : s * s = 2) by (unfold s; apply sqrt2_sqr).
  replace (s + (1 - s) * t) with (s * (1 - t) + t) by ring.
  replace ((s * (1 - t) + t) * (s * (1 - t) + t) - t * t)
    with (s * s * ((1 - t) * (1 - t)) + 2 * s * (1 - t) * t) by ring.
  rewrite Hs. ring.
Qed.

Lemma two_den_uden : forall t,
  2 * chart_den t = chart_uden t * chart_uden t + t * t.
Proof.
  intro t. rewrite chart_den_poly. unfold chart_uden.
  set (s := sqrt 2).
  assert (Hs : s * s = 2) by (unfold s; apply sqrt2_sqr).
  replace (s + (1 - s) * t) with (s * (1 - t) + t) by ring.
  replace ((s * (1 - t) + t) * (s * (1 - t) + t) + t * t)
    with (s * s * ((1 - t) * (1 - t)) + 2 * s * (1 - t) * t + 2 * (t * t))
    by ring.
  rewrite Hs. ring.
Qed.

Lemma two_numy_uden : forall t,
  2 * chart_numy t = 2 * t * chart_uden t.
Proof.
  intro t. rewrite chart_numy_poly. unfold chart_uden. ring.
Qed.

Lemma chart_weierstrass_x : forall t,
  0 <= t <= 1 ->
  chart_numx t / chart_den t =
    (1 - chart_u t * chart_u t) / (1 + chart_u t * chart_u t).
Proof.
  intros t Ht.
  set (D := chart_den t). set (U := chart_uden t).
  assert (HD : 0 < D) by (unfold D; apply chart_den_pos; exact Ht).
  assert (HU : 0 < U) by (unfold U; apply chart_uden_pos; exact Ht).
  assert (Hsq : 0 < U * U + t * t).
  { assert (0 < U * U) by (apply Rmult_lt_0_compat; exact HU).
    assert (0 <= t * t) by apply Rle_0_sqr. lra. }
  unfold chart_u. fold U.
  replace ((1 - (t / U) * (t / U)) / (1 + (t / U) * (t / U)))
    with ((U * U - t * t) / (U * U + t * t)) by (field; lra).
  pose proof (two_numx_uden t) as Hx.
  pose proof (two_den_uden t) as Hd.
  fold D in Hd. fold U in Hx, Hd.
  replace (chart_numx t / D) with ((2 * chart_numx t) / (2 * D)) by (field; lra).
  rewrite Hx, Hd. reflexivity.
Qed.

Lemma chart_weierstrass_y : forall t,
  0 <= t <= 1 ->
  chart_numy t / chart_den t =
    (2 * chart_u t) / (1 + chart_u t * chart_u t).
Proof.
  intros t Ht.
  set (D := chart_den t). set (U := chart_uden t).
  assert (HD : 0 < D) by (unfold D; apply chart_den_pos; exact Ht).
  assert (HU : 0 < U) by (unfold U; apply chart_uden_pos; exact Ht).
  assert (Hsq : 0 < U * U + t * t).
  { assert (0 < U * U) by (apply Rmult_lt_0_compat; exact HU).
    assert (0 <= t * t) by apply Rle_0_sqr. lra. }
  unfold chart_u. fold U.
  replace ((2 * (t / U)) / (1 + (t / U) * (t / U)))
    with ((2 * t * U) / (U * U + t * t)) by (field; lra).
  pose proof (two_numy_uden t) as Hy.
  pose proof (two_den_uden t) as Hd.
  fold D in Hd. fold U in Hy, Hd.
  replace (chart_numy t / D) with ((2 * chart_numy t) / (2 * D)) by (field; lra).
  rewrite Hy, Hd. reflexivity.
Qed.

Lemma conic_quad_fixtures :
  nthR chart_w 1 = cos (PI / 4) /\
  (forall t, 0 <= t <= 1 ->
    bz_hom_eval 2 chart_ctrl chart_w t =
    circ_eval chart_egg (chart_phi t / (PI / 2))).
Proof.
  split.
  - unfold nthR, chart_w. simpl.
    pose proof sqrt2_pos as Hs.
    rewrite <- sqrt2_sqr at 2.
    replace (sqrt 2 / (sqrt 2 * sqrt 2)) with (1 / sqrt 2) by (field; lra).
    symmetry. apply cos_PI4.
  - intros t Ht.
    assert (HlenC : length chart_ctrl = S 2) by reflexivity.
    assert (HlenW : length chart_w = S 2) by reflexivity.
    destruct (a41_eq_definition_bz 2 chart_ctrl chart_w t Ht HlenC HlenW
                (fun i Hi => chart_w_pos i (Hi)))
      as [Hw [Hx [Hy [Hww Heval]]]].
    rewrite Heval.
    fold (chart_numx t) (chart_numy t) (chart_den t).
    unfold circ_eval, chart_egg. apply point_ext; cbn [px py circ_o circ_r circ_theta0 circ_sweep].
    + rewrite Rplus_0_l, (Rmult_1_l (cos _)).
      replace (chart_phi t / (PI / 2) * (PI / 2)) with (chart_phi t)
        by (field; pose proof PI_RGT_0; lra).
      rewrite Rplus_0_l. unfold chart_phi. rewrite cos_2_atan3.
      apply chart_weierstrass_x. exact Ht.
    + rewrite Rplus_0_l, (Rmult_1_l (sin _)).
      replace (chart_phi t / (PI / 2) * (PI / 2)) with (chart_phi t)
        by (field; pose proof PI_RGT_0; lra).
      rewrite Rplus_0_l. unfold chart_phi. rewrite sin_2_atan3.
      apply chart_weierstrass_y. exact Ht.
Qed.

(* -------------------------------------------------------------------------- *)
(* Full declaration sweep.                                                    *)
(* -------------------------------------------------------------------------- *)

Print Assumptions bz_knots.
Print Assumptions bz_knots_length.
Print Assumptions nth_repeat_prefix.
Print Assumptions bz_nth_lo.
Print Assumptions bz_nth_hi.
Print Assumptions bz_nth_out.
Print Assumptions bz_nth_bound.
Print Assumptions bz_wf.
Print Assumptions andb_leb_neq.
Print Assumptions indicator_flat0.
Print Assumptions indicator_01.
Print Assumptions indicator_from_hi.
Print Assumptions bz_basis_deg0.
Print Assumptions bz_left_edge.
Print Assumptions bz_left_open.
Print Assumptions bz_right_open.
Print Assumptions bz_right_top.
Print Assumptions bern_left_edge.
Print Assumptions bern_right_edge.
Print Assumptions bz_basis_window.
Print Assumptions bz_basis_bern.
Print Assumptions bz_alpha.
Print Assumptions round_casteljau.
Print Assumptions rounds_casteljau.
Print Assumptions round_casteljau_length.
Print Assumptions rounds_casteljau_length.
Print Assumptions round_casteljau_nth.
Print Assumptions round_deboor_casteljau.
Print Assumptions bz_rounds_casteljau.
Print Assumptions sum_f_R0_ext.
Print Assumptions sum_f_R0_plus.
Print Assumptions sum_f_R0_scale.
Print Assumptions sum_f_R0_drop_last.
Print Assumptions sum_prev_shift.
Print Assumptions bern_combo_step.
Print Assumptions casteljau_slot.
Print Assumptions bz_deboor_bern.
Print Assumptions unit_weights.
Print Assumptions unit_weight_nth.
Print Assumptions bz_hom_eval.
Print Assumptions bezier_eval.
Print Assumptions sum_f_R0_nonneg.
Print Assumptions sum_f_R0_zero_term.
Print Assumptions sum_f_R0_zeros.
Print Assumptions bz_den_pos.
Print Assumptions point_ext.
Print Assumptions a41_eq_definition_bz.
Print Assumptions bezier_eval_poly.
Print Assumptions bern0_O.
Print Assumptions bern0_S.
Print Assumptions bern1_diag.
Print Assumptions bern1_below.
Print Assumptions sum_f_R0_single0.
Print Assumptions sum_f_R0_prefix0.
Print Assumptions sum_bern_at_0.
Print Assumptions sum_bern_at_1.
Print Assumptions bezier_eval_0.
Print Assumptions bezier_eval_1.
Print Assumptions tt_quad_ctrl.
Print Assumptions tt_quad_fixtures.
Print Assumptions cubic_third_ctrl.
Print Assumptions cubic_third_fixtures.
Print Assumptions chart_ctrl.
Print Assumptions chart_w.
Print Assumptions chart_egg.
Print Assumptions chart_uden.
Print Assumptions chart_u.
Print Assumptions chart_phi.
Print Assumptions chart_numx.
Print Assumptions chart_numy.
Print Assumptions chart_den.
Print Assumptions sqrt2_sqr.
Print Assumptions sqrt2_pos.
Print Assumptions chart_w_pos.
Print Assumptions chart_den_pos.
Print Assumptions chart_uden_pos.
Print Assumptions twice_half_sqrt2.
Print Assumptions twice_half_sqrt2_1.
Print Assumptions chart_numx_poly.
Print Assumptions chart_numy_poly.
Print Assumptions chart_den_poly.
Print Assumptions two_numx_uden.
Print Assumptions two_den_uden.
Print Assumptions two_numy_uden.
Print Assumptions chart_weierstrass_x.
Print Assumptions chart_weierstrass_y.
Print Assumptions conic_quad_fixtures.
