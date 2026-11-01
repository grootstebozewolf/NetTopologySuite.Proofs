(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_CarryCleanLadder
   ----------------------------------------------------------------------------
   Rung-independent machinery for the carry_clean bridge (B64_CarryClean.v),
   so that a rung composes steps instead of re-deriving them.  Rung 5
   (B64_CarryCleanRung5.v) is its first user.

   CONTENTS.
     ts_facts                 one TwoSum, as facts (finite, RN, exact, half-ulp)
     priest_keys_general      the keys at ANY length: |g_j| < ulp(g_(j+2)) for
                              the sorted components of two Priest chains.  Per
                              chain, everything after the first component at
                              or below |g| lies below ulp(g); counting gives
                              j + 1 components below ulp(g_(j+2)).
     priest_third_nonzero     at most one zero per chain, so g_3, g_4, ... are
                              nonzero
     sstate, sstate_step,     the LAYERED STATE: the running sum Q is a
       sstate_shape           multiple of 2^L, the errors so far lie below
                              2^L, layered.  A step whose new input g has every
                              error so far below ulp(g) keeps the state; the
                              final state's output is all singles.
     tie_values               the tie lifted out of rung 4: Q = +-B, |g| near
                              B, and the TwoSum gives an anti partner, a twin
                              partner, or a multiple of 2u
     tie_finish_tail          the tie at the top, over any layered tail
     shape_insert_anti,       one pair between singles above and a layered
       shape_insert_twin      tail below
     rn_absorb                RN(g + y) = g when |y| < ulp(g) / 4
     anti_final, twin_final   the step after a tie: the next input keeps the
                              anti pair below everything new, or absorbs the
                              tiny running sum so the twin moves up

   NOT HERE.  An induction over n: after a tie, a later step could tie again
   in principle; this module handles the step right after a tie, which is
   what rung 5 needs.

   NTS / JTS COUNTERPART.  None in-library (JTS/NTS use `CGAlgorithmsDD`,
   double-double); this lane serves the corpus's exact orientation.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lia Lra List Permutation.
From Flocq Require Import IEEE754.Binary Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
     B64_Pff_bridge B64_Expansion B64_FastExpansionSum
     B64_FastExpansionSum_Shewchuk B64_Overlap_Hierarchy B64_CarryCleanAlgo
     B64_CarryCleanCore B64_CarryCleanRung2 B64_CarryCleanRung3
     B64_CarryCleanRung4.

Import ListNotations.
Local Open Scope R_scope.

Local Abbreviation b2r := (Binary.B2R prec emax).
Local Abbreviation RN := (round radix2 b64_fexp (BinarySingleNaN.round_mode mode_b64)).

(* --------------------------------------------------------------------------
   One TwoSum, as facts.
   -------------------------------------------------------------------------- *)

Lemma ts_facts :
  forall g q, b64_TwoSum_safe g q ->
    let Q := fst (b64_TwoSum g q) in
    let h := snd (b64_TwoSum g q) in
    b64_fin Q /\ b64_fin h /\ b2r Q = RN (b2r g + b2r q)
    /\ b2r Q + b2r h = b2r g + b2r q /\ strict_succ_b64 Q h
    /\ Q = b64_plus g q.
Proof.
  intros g q S Q h.
  pose proof S as (A1 & A2 & A3 & A4 & A5 & A6).
  pose proof (b64_TwoSum_correct g q A1 A2 A3 A4 A5 A6) as Hex.
  pose proof (b64_TwoSum_nonoverlap g q A1 A2 A3 A4 A5 A6) as Hno.
  destruct (b64_plus_correct g q A1) as [RQ FQ].
  destruct (b64_plus_correct _ _ A6) as [_ Fh].
  unfold Q, h. unfold b64_TwoSum in *. cbn [fst snd] in *.
  repeat split; assumption.
Qed.

(* --------------------------------------------------------------------------
   The keys for any length: |g_j| < ulp(g_(j+2)).

   Within one Priest chain, every component after the first one at or below
   |g| lies below ulp(g).  So the components at or above ulp(g) number at
   most (those above |g|) + 1 per chain, i.e. at most n - (j + 3) + 2 when
   g = g_(j+2); hence at least j + 1 components lie below ulp(g_(j+2)).
   -------------------------------------------------------------------------- *)

Lemma priest_snd_nonzero :
  forall a b : binary64, priest_nonoverlapping_b64 a b -> b2r b <> 0.
Proof.
  intros a b [mx [my [kx [ky [Hx [Hy [_ [[Hylo _] _]]]]]]]] H0.
  rewrite Hy in H0. apply Rmult_integral in H0. destruct H0 as [H0 | H0].
  - rewrite H0, Rabs_R0 in Hylo. pose proof (bpow_gt_0 radix2 (prec - 1)). lra.
  - pose proof (bpow_gt_0 radix2 ky). lra.
Qed.

Lemma priest_chain_tail_lt :
  forall a rest, priest_chain (a :: rest) ->
    Forall (fun x => Rabs (b2r x) < ulp radix2 b64_fexp (b2r a)) rest.
Proof.
  intros a rest. revert a. induction rest as [| b rest IH]; intros a H; [ constructor | ].
  cbn [priest_chain] in H. destruct H as [Pab Hc].
  destruct (priest_pair_lt_ulp a b Pab) as [_ Hb].
  pose proof (priest_snd_nonzero a b Pab) as Hb0.
  pose proof (ulp_le_abs_b64 b Hb0) as Hub.
  constructor; [ exact Hb | ].
  eapply Forall_impl; [ | exact (IH b Hc) ]. cbn beta. intros x Hx. lra.
Qed.

Definition is_above (G : R) (x : binary64) : bool :=
  if Rlt_dec G (Rabs (b2r x)) then true else false.

Definition cnt_gt (G : R) (l : list binary64) : nat := length (filter (is_above G) l).

Lemma cnt_gt_app : forall G l1 l2, cnt_gt G (l1 ++ l2) = (cnt_gt G l1 + cnt_gt G l2)%nat.
Proof. intros. unfold cnt_gt. rewrite filter_app, length_app. reflexivity. Qed.

Lemma cnt_app : forall M l1 l2, cnt M (l1 ++ l2) = (cnt M l1 + cnt M l2)%nat.
Proof. intros. unfold cnt. rewrite filter_app, length_app. reflexivity. Qed.

Lemma cnt_gt_perm : forall G l l', Permutation l l' -> cnt_gt G l = cnt_gt G l'.
Proof.
  intros G l l' H. induction H as [| x l l' _ IH | x y l | l l' l'' _ IH1 _ IH2].
  - reflexivity.
  - unfold cnt_gt in *. cbn [filter]. destruct (is_above G x); cbn [length]; lia.
  - unfold cnt_gt. cbn [filter]. destruct (is_above G x), (is_above G y); reflexivity.
  - lia.
Qed.

Lemma cnt_le_length : forall M l, (cnt M l <= length l)%nat.
Proof.
  intros M l. induction l as [| x l IH]; [ cbn; lia | ].
  pose proof (cnt_cons_le M x l). cbn [length]. lia.
Qed.

Lemma b64_nonzero_ge_emin :
  forall x : binary64, b2r x <> 0 -> bpow radix2 (3 - emax - prec) <= Rabs (b2r x).
Proof.
  intros x Hx. destruct (Rlt_or_le (Rabs (b2r x)) (bpow radix2 (3 - emax - prec))) as [H | H];
    [ exfalso; apply Hx, binary64_below_emin_is_zero, H | exact H ].
Qed.

(* Per chain: the components at or above ulp(g) are at most those above |g|,
   plus one. *)
Lemma chain_count :
  forall (g : binary64) c, priest_chain c ->
    (length c <= cnt (ulp radix2 b64_fexp (b2r g)) c + cnt_gt (Rabs (b2r g)) c + 1)%nat.
Proof.
  intros g c. induction c as [| a rest IH]; intro Hc; [ cbn; lia | ].
  set (T := ulp radix2 b64_fexp (b2r g)) in *.
  destruct (Rlt_or_le (Rabs (b2r g)) (Rabs (b2r a))) as [Hbig | Hsmall].
  - (* a above |g|: counted on the right *)
    assert (Hr : priest_chain rest)
      by (destruct rest; [ exact I | exact (proj2 Hc) ]).
    specialize (IH Hr).
    unfold cnt_gt. cbn [filter length]. unfold is_above at 1.
    destruct (Rlt_dec _ _) as [_ | Hn]; [ | contradiction ].
    cbn [length]. fold (cnt_gt (Rabs (b2r g)) rest).
    pose proof (cnt_cons_ge T a rest). lia.
  - (* a at or below |g|: the rest lies below ulp(a) <= ulp(g) *)
    pose proof (priest_chain_tail_lt a rest Hc) as Ht.
    pose proof (ulp_mono a g Hsmall) as Hu.
    assert (Hall : cnt T rest = length rest).
    { clear IH Hc. induction rest as [| x rest IHr]; [ reflexivity | ].
      inversion Ht as [| ? ? Hx Ht']; subst.
      rewrite cnt_cons_in by (unfold T; lra). cbn [length]. rewrite IHr; [ reflexivity | exact Ht' ]. }
    pose proof (cnt_cons_ge T a rest). cbn [length]. lia.
Qed.

(* In a sorted list, at most n - (i + 1) components exceed the i-th. *)
Lemma sorted_cnt_gt :
  forall s i, sorted_asc s -> (i < length s)%nat ->
    (cnt_gt (Rabs (b2r (nth i s b64_two_unit))) s <= length s - S i)%nat.
Proof.
  induction s as [| x s IH]; intros i Hs Hi; [ cbn in Hi; lia | ].
  assert (Hcons : forall G, (cnt_gt G (x :: s) <= S (cnt_gt G s))%nat).
  { intro G. unfold cnt_gt. cbn [filter]. destruct (is_above G x); cbn [length]; lia. }
  assert (Hle : forall G, (cnt_gt G s <= length s)%nat).
  { intro G. unfold cnt_gt. apply filter_length_le. }
  destruct i as [| i].
  - cbn [nth length]. unfold cnt_gt. cbn [filter]. unfold is_above at 1.
    destruct (Rlt_dec _ _) as [H | _]; [ lra | ].
    fold (cnt_gt (Rabs (b2r x)) s). specialize (Hle (Rabs (b2r x))). lia.
  - cbn [nth length] in *.
    pose proof (IH i (sorted_asc_tail _ _ Hs) ltac:(lia)) as Hi'.
    assert (Hx : Rabs (b2r x) <= Rabs (b2r (nth i s b64_two_unit))).
    { pose proof (sorted_head_le x s Hs) as Hf. rewrite Forall_forall in Hf.
      apply Hf, nth_In. lia. }
    unfold cnt_gt in *. cbn [filter]. unfold is_above at 1.
    destruct (Rlt_dec _ _) as [H | _]; [ lra | ]. lia.
Qed.

Theorem priest_keys_general :
  forall e f j,
    priest_chain e -> priest_chain f ->
    let s := sort_by_abs (e ++ f) in
    (j + 2 < length s)%nat ->
    Rabs (b2r (nth j s b64_two_unit))
      < ulp radix2 b64_fexp (b2r (nth (j + 2) s b64_two_unit)).
Proof.
  intros e f j He Hf s Hj.
  set (g := nth (j + 2) s b64_two_unit).
  set (T := ulp radix2 b64_fexp (b2r g)).
  assert (Hp : Permutation (e ++ f) s) by apply sort_by_abs_perm.
  assert (Hs : sorted_asc s) by apply sort_by_abs_sorted.
  pose proof (chain_count g e He) as Ce. pose proof (chain_count g f Hf) as Cf.
  fold T in Ce, Cf.
  pose proof (sorted_cnt_gt s (j + 2) Hs Hj) as Cs. fold g in Cs.
  rewrite <- (cnt_gt_perm _ _ _ Hp), cnt_gt_app in Cs.
  pose proof (Permutation_length Hp) as Hlen. rewrite length_app in Hlen.
  apply (stat_lt T (e ++ f) s j Hs Hp ltac:(lia)).
  rewrite cnt_app. lia.
Qed.

(* At most one zero per chain, so the third sorted component is nonzero. *)
Lemma chain_zeros :
  forall c, priest_chain c -> (cnt (bpow radix2 (3 - emax - prec)) c <= 1)%nat.
Proof.
  intros [| a [| b rest]] Hc; [ cbn; lia | pose proof (cnt_cons_le (bpow radix2 (3 - emax - prec)) a []); cbn in *; lia | ].
  cbn [priest_chain] in Hc. destruct Hc as [Pab Hc].
  pose proof (priest_pair_lt_ulp a b Pab) as [Ha0 _].
  assert (Hnz : forall x, In x (a :: b :: rest) -> b2r x <> 0).
  { intros x [<- | Hx]; [ exact Ha0 | ].
    clear Ha0. revert a b Pab Hc Hx. induction rest as [| c rest IH]; intros a b Pab Hc Hx.
    - destruct Hx as [<- | []]. exact (priest_snd_nonzero _ _ Pab).
    - destruct Hx as [<- | Hx]; [ exact (priest_snd_nonzero _ _ Pab) | ].
      cbn [priest_chain] in Hc. destruct Hc as [Pbc Hc'].
      exact (IH b c Pbc Hc' Hx). }
  assert (H0 : forall l, (forall x, In x l -> b2r x <> 0) ->
                 cnt (bpow radix2 (3 - emax - prec)) l = 0%nat).
  { induction l as [| x l IHl]; intro Hl; [ reflexivity | ].
    rewrite cnt_cons_out by (apply b64_nonzero_ge_emin, Hl; left; reflexivity).
    apply IHl. intros y Hy. apply Hl. right. exact Hy. }
  rewrite (H0 _ Hnz). lia.
Qed.

Lemma priest_third_nonzero :
  forall e f j,
    priest_chain e -> priest_chain f ->
    let s := sort_by_abs (e ++ f) in
    (2 <= j)%nat -> (j < length s)%nat -> b2r (nth j s b64_two_unit) <> 0.
Proof.
  intros e f j He Hf s H2 Hj.
  assert (Hp : Permutation (e ++ f) s) by apply sort_by_abs_perm.
  assert (Hs : sorted_asc s) by apply sort_by_abs_sorted.
  assert (Hc : (cnt (bpow radix2 (3 - emax - prec)) (e ++ f) <= j)%nat).
  { rewrite cnt_app. pose proof (chain_zeros e He). pose proof (chain_zeros f Hf). lia. }
  pose proof (stat_ge _ (e ++ f) s j Hs Hp Hj Hc) as Hge.
  pose proof (bpow_gt_0 radix2 (3 - emax - prec)). intro H0. rewrite H0, Rabs_R0 in Hge. lra.
Qed.

(* --------------------------------------------------------------------------
   The layered state.  After a TwoSum, the running sum Q is a multiple of
   2^L and every error so far lies below 2^L, layered; the errors before
   the newest one lie below 2^K.  A step that does not tie keeps the state.
   -------------------------------------------------------------------------- *)

Definition sstate (Q : binary64) (E : list binary64) (L K : Z) : Prop :=
  b64_fin Q /\ Forall b64_fin E /\ pow2_multiple L (b2r Q)
  /\ Forall (below L) E /\ layered E /\ Forall (below K) (tl E).

Lemma sstate_init : forall g K, b64_fin g -> sstate g [] (cexp radix2 b64_fexp (b2r g)) K.
Proof.
  intros g K Hg. repeat split; try constructor; try exact I; [ exact Hg | ].
  apply b64_pow2_multiple_cexp.
Qed.

Lemma below_mono : forall c c' l, (c <= c')%Z -> Forall (below c) l -> Forall (below c') l.
Proof.
  intros c c' l Hc H. eapply Forall_impl; [ | exact H ]. unfold below. intros y Hy.
  assert (bpow radix2 c <= bpow radix2 c') by (apply bpow_le, Hc). lra.
Qed.

Lemma sstate_step :
  forall Q E L K g,
    sstate Q E L K -> b64_fin g -> b64_TwoSum_safe g Q ->
    Forall (below (cexp radix2 b64_fexp (b2r g))) E ->
    let Q' := fst (b64_TwoSum g Q) in
    let h := snd (b64_TwoSum g Q) in
    let c := Z.min (cexp radix2 b64_fexp (b2r g)) L in
    sstate Q' (h :: E) (Z.max c (cexp radix2 b64_fexp (b2r Q'))) c.
Proof.
  intros Q E L K g (FQ & FE & MQ & BE & LE & _) Fg S Bg Q' h c.
  destruct (ts_facts g Q S) as (FQ' & Fh & RQ' & Hex & Hno & _). fold Q' h in FQ', Fh, RQ', Hex, Hno.
  assert (Mg : pow2_multiple c (b2r g))
    by (apply (pow2_multiple_le _ _ _ (Z.le_min_l _ _)), b64_pow2_multiple_cexp).
  assert (MQc : pow2_multiple c (b2r Q)) by (apply (pow2_multiple_le _ _ _ (Z.le_min_r _ _)), MQ).
  assert (MQ' : pow2_multiple c (b2r Q'))
    by (rewrite RQ'; apply round_pow2_multiple, pow2_multiple_plus; assumption).
  assert (Mh : pow2_multiple c (b2r h)).
  { replace (b2r h) with ((b2r g + b2r Q) - b2r Q') by lra.
    apply pow2_multiple_minus; [ apply pow2_multiple_plus | ]; assumption. }
  assert (BEc : Forall (below c) E).
  { unfold c. destruct (Z.min_spec (cexp radix2 b64_fexp (b2r g)) L) as [[_ Hm] | [_ Hm]];
      rewrite Hm; assumption. }
  unfold strict_succ_b64 in Hno. pose proof (half_ulp_below Q' h Hno) as Hh.
  repeat split.
  - exact FQ'.
  - constructor; assumption.
  - destruct (Z.max_spec c (cexp radix2 b64_fexp (b2r Q'))) as [[_ Hm] | [_ Hm]];
      rewrite Hm; [ apply b64_pow2_multiple_cexp | exact MQ' ].
  - constructor; [ unfold below; apply Rlt_le_trans with (1 := Hh); apply bpow_le, Z.le_max_r | ].
    apply (below_mono c); [ apply Z.le_max_l | exact BEc ].
  - exists c. split; assumption.
  - exact LE.
  - exact BEc.
Qed.

Lemma sstate_shape :
  forall Q E L K, sstate Q E L K ->
    exists bs, drop_zeros (Q :: E) = flat_map cblock_expand bs /\ carry_shape bs.
Proof.
  intros Q E L K (FQ & FE & MQ & BE & LE & _).
  destruct (singles_shape_of_layered (Q :: E)) as [bs [Hl [Hs _]]].
  - constructor; assumption.
  - apply layered_filter. split; [ exists L; split; assumption | exact LE ].
  - exists bs. split; assumption.
Qed.

(* --------------------------------------------------------------------------
   The tie, as values.  If Q = s B and g is a multiple of u = ulp(g) with
   B - 2u <= |g| (B = 2^(mag g), fexp (mag g + 1) = cexp g + 1), then the
   TwoSum (Q', h') of g and Q is an anti pair partner, a twin partner, or a
   multiple of 2u.
   -------------------------------------------------------------------------- *)

Lemma tie_values :
  forall (g Q : binary64) (s : R),
    b64_fin g -> b64_TwoSum_safe g Q -> (s = 1 \/ s = -1) ->
    let c := cexp radix2 b64_fexp (b2r g) in
    let M := mag radix2 (b2r g) in
    b2r g <> 0 -> (2 <= M - c)%Z -> b64_fexp (M + 1) = (c + 1)%Z ->
    b2r Q = s * bpow radix2 M ->
    bpow radix2 M - 2 * bpow radix2 c <= Rabs (b2r g) ->
    let Q' := fst (b64_TwoSum g Q) in
    let h' := snd (b64_TwoSum g Q) in
       (b2r h' = - (s * bpow radix2 c) /\ b2r Q' = s * (2 * bpow radix2 M))
    \/ (b2r h' = 0 /\ b2r Q' = s * bpow radix2 c)
    \/ (b2r h' = 0 /\ pow2_multiple (c + 1) (b2r Q') /\ b2r Q' <> 0).
Proof.
  intros g Q s Fg S Hs c M Hg0 HMc HfM HQ Hgl Q' h'.
  destruct (ts_facts g Q S) as (FQ' & Fh & RQ' & Hex & _ & _). fold Q' h' in FQ', Fh, RQ', Hex.
  set (B := bpow radix2 M) in *. set (u := bpow radix2 c) in *.
  assert (Hu : 0 < u) by apply bpow_gt_0. assert (HB0 : 0 < B) by apply bpow_gt_0.
  assert (HcM : c = b64_fexp M) by reflexivity.
  set (K := Zpower radix2 (M - c)).
  assert (HBK : B = IZR K * u).
  { unfold B, u, K. rewrite IZR_Zpower by lia. rewrite <- bpow_plus. f_equal. lia. }
  assert (HKe : Z.even K = true).
  { unfold K. replace (M - c)%Z with (1 + (M - c - 1))%Z by ring.
    rewrite Zpower_plus by lia. cbn [Zpower Z.pow_pos Pos.iter radix_val radix2].
    rewrite Z.even_mul. reflexivity. }
  assert (HK4 : (4 <= K)%Z).
  { unfold K. replace (M - c)%Z with (2 + (M - c - 2))%Z by ring.
    rewrite Zpower_plus by lia. cbn [Zpower Z.pow_pos Pos.iter radix_val radix2].
    assert (0 < Zpower radix2 (M - c - 2))%Z by (apply Zpower_gt_0; lia). lia. }
  assert (HK4R : 4 <= IZR K) by (apply IZR_le; exact HK4).
  assert (FB : generic_format radix2 b64_fexp B).
  { apply generic_format_bpow. unfold SpecFloat.fexp in *. unfold prec in *. lia. }
  assert (Hg5B : Rabs (b2r g) <= B - u).
  { unfold B, u. rewrite HcM, <- pred_bpow.
    exact (pred_ge_gt radix2 b64_fexp _ _
             (generic_format_abs _ _ _ (Binary.generic_format_B2R prec emax g)) FB
             (bpow_mag_gt radix2 (b2r g))). }
  destruct (b64_pow2_multiple_cexp g) as [m Hm]. fold c u in Hm.
  assert (Hmb : (K - 2 <= Z.abs m <= K - 1)%Z).
  { rewrite Hm, Rabs_mult, (Rabs_pos_eq u) in Hg5B, Hgl by lra.
    rewrite <- abs_IZR in Hg5B, Hgl. rewrite HBK in Hg5B, Hgl.
    split.
    - apply le_IZR. rewrite minus_IZR. apply Rmult_le_reg_r with u; [ lra | ]. lra.
    - apply le_IZR. rewrite minus_IZR. apply Rmult_le_reg_r with u; [ lra | ]. lra. }
  assert (Hm4 : m = (K - 1)%Z \/ m = (K - 2)%Z \/ m = (- (K - 1))%Z \/ m = (- (K - 2))%Z) by lia.
  assert (Hce : forall v, B <= Rabs v < 2 * B -> cexp radix2 b64_fexp v = (c + 1)%Z).
  { intros v [Hl Hh]. unfold cexp.
    assert (Hmv : mag radix2 v = (M + 1)%Z :> Z).
    { apply mag_unique. rewrite Z.add_simpl_r. split; [ exact Hl | ].
      rewrite bpow_plus. change (bpow radix2 1) with 2. unfold B in Hh. lra. }
    rewrite Hmv. exact HfM. }
  assert (Hu2 : 2 * u = bpow radix2 (c + 1))
    by (unfold u; rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
  assert (Hfmt : forall j : Z, Rabs (IZR j * (2 * u)) < 2 * B ->
                   generic_format radix2 b64_fexp (IZR j * (2 * u))).
  { intros j Hj. rewrite Hu2. apply (fmt_scaled j (c + 1) (M + 1)).
    - rewrite <- Hu2. rewrite bpow_plus. change (bpow radix2 1) with 2. unfold B in Hj. lra.
    - lia. }
  assert (Hfu : generic_format radix2 b64_fexp u).
  { apply generic_format_bpow. unfold c, cexp, SpecFloat.fexp. unfold prec. lia. }
  assert (HK : IZR K * u = B) by (symmetry; exact HBK).
  assert (Hrnd : forall v, generic_format radix2 b64_fexp v -> RN v = v)
    by (intros v Hv; apply round_generic; [ apply valid_rnd_N | exact Hv ]).
  destruct Hs as [-> | ->]; repeat rewrite Rmult_1_l in HQ |- *.
  - (* Q = B *)
    destruct Hm4 as [Em | [Em | [Em | Em]]]; rewrite Em in Hm.
    + assert (Hv : b2r g + b2r Q = (IZR (K - 1) + / 2) * bpow radix2 (c + 1)).
      { rewrite Hm, HQ, <- Hu2, minus_IZR. rewrite <- HK. field. }
      assert (HcV : cexp radix2 b64_fexp (b2r g + b2r Q) = (c + 1)%Z).
      { apply Hce. rewrite Hm, HQ, minus_IZR, <- HK. rewrite Rabs_pos_eq; [ | nra ]. split; nra. }
      assert (HQ5 : b2r Q' = 2 * B).
      { rewrite RQ', round_NE_mid with (n := (K - 1)%Z); [ | rewrite HcV; exact Hv ].
        rewrite HcV, Z.even_sub, HKe. cbn. replace (K - 1 + 1)%Z with K by ring.
        rewrite <- Hu2, <- HK. ring. }
      left. split; [ | lra ].
      rewrite Hm, HQ, HQ5, minus_IZR, <- HK in Hex. lra.
    + assert (Hv : b2r g + b2r Q = IZR (K - 1) * (2 * u)) by (rewrite Hm, HQ, !minus_IZR, <- HK; ring).
      assert (HQ5 : b2r Q' = IZR (K - 1) * (2 * u)).
      { rewrite RQ', Hv. apply Hrnd, Hfmt. rewrite minus_IZR, Rabs_pos_eq; [ rewrite <- HK; lra | nra ]. }
      right; right. split; [ | split ].
      * rewrite Hm, HQ, HQ5, !minus_IZR, <- HK in Hex. lra.
      * rewrite HQ5, Hu2. exists (K - 1)%Z. reflexivity.
      * rewrite HQ5, minus_IZR. nra.
    + assert (Hv : b2r g + b2r Q = u) by (rewrite Hm, HQ, opp_IZR, minus_IZR, <- HK; ring).
      assert (HQ5 : b2r Q' = u) by (rewrite RQ', Hv; apply Hrnd, Hfu).
      right; left. split; lra.
    + assert (Hv : b2r g + b2r Q = IZR 1 * (2 * u))
        by (rewrite Hm, HQ, opp_IZR, minus_IZR, <- HK; cbn; ring).
      assert (HQ5 : b2r Q' = IZR 1 * (2 * u)).
      { rewrite RQ', Hv. apply Hrnd, Hfmt. rewrite Rabs_pos_eq by (cbn; lra). rewrite <- HK. cbn. nra. }
      right; right. split; [ | split ].
      * rewrite Hv in Hex. lra.
      * rewrite HQ5, Hu2. exists 1%Z. reflexivity.
      * rewrite HQ5. cbn. lra.
  - (* Q = -B *)
    destruct Hm4 as [Em | [Em | [Em | Em]]]; rewrite Em in Hm.
    + assert (Hv : b2r g + b2r Q = - u) by (rewrite Hm, HQ, minus_IZR, <- HK; ring).
      assert (HQ5 : b2r Q' = - u) by (rewrite RQ', Hv; apply Hrnd, generic_format_opp, Hfu).
      right; left. split; lra.
    + assert (Hv : b2r g + b2r Q = IZR (-1) * (2 * u)) by (rewrite Hm, HQ, minus_IZR, <- HK; cbn; ring).
      assert (HQ5 : b2r Q' = IZR (-1) * (2 * u)).
      { rewrite RQ', Hv. apply Hrnd, Hfmt. cbn. rewrite Rabs_left by lra. rewrite <- HK. nra. }
      right; right. split; [ | split ].
      * rewrite Hv in Hex. lra.
      * rewrite HQ5, Hu2. exists (-1)%Z. reflexivity.
      * rewrite HQ5. cbn. lra.
    + assert (Hv : b2r g + b2r Q = (IZR (- K) + / 2) * bpow radix2 (c + 1)).
      { rewrite Hm, HQ, <- Hu2, opp_IZR, minus_IZR, opp_IZR. rewrite <- HK. field. }
      assert (HcV : cexp radix2 b64_fexp (b2r g + b2r Q) = (c + 1)%Z).
      { apply Hce. rewrite Hm, HQ, opp_IZR, minus_IZR, <- HK. rewrite Rabs_left; [ | nra ]. split; nra. }
      assert (HQ5 : b2r Q' = - (2 * B)).
      { rewrite RQ', round_NE_mid with (n := (- K)%Z); [ | rewrite HcV; exact Hv ].
        rewrite HcV, Z.even_opp, HKe. rewrite opp_IZR, <- Hu2, <- HK. ring. }
      left. split; [ | lra ].
      rewrite Hm, HQ, HQ5, opp_IZR, minus_IZR, <- HK in Hex. lra.
    + assert (Hv : b2r g + b2r Q = IZR (- (K - 1)) * (2 * u)).
      { rewrite Hm, HQ, !opp_IZR, !minus_IZR, <- HK. ring. }
      assert (HQ5 : b2r Q' = IZR (- (K - 1)) * (2 * u)).
      { rewrite RQ', Hv. apply Hrnd, Hfmt. rewrite opp_IZR, minus_IZR, Rabs_left; [ rewrite <- HK; lra | nra ]. }
      right; right. split; [ | split ].
      * rewrite Hm, HQ, HQ5, !opp_IZR, !minus_IZR, <- HK in Hex. lra.
      * rewrite HQ5, Hu2. exists (- (K - 1))%Z. reflexivity.
      * rewrite HQ5, opp_IZR, minus_IZR. nra.
Qed.

(* --------------------------------------------------------------------------
   Shapes with one pair in the middle: singles above, the pair, a layered
   tail below.
   -------------------------------------------------------------------------- *)

Lemma strict_desc_app :
  forall l1 l2, strict_desc (l1 ++ l2) -> strict_desc l1 /\ strict_desc l2.
Proof.
  induction l1 as [| x l1 IH]; intros l2 H; [ split; [ exact I | exact H ] | ].
  destruct l1 as [| y l1'].
  - split; [ exact I | ]. cbn [app] in H. exact (strict_desc_tail _ _ H).
  - cbn [app] in H. destruct H as [Hxy H].
    destruct (IH l2 H) as [H1 H2]. split; [ split; assumption | exact H2 ].
Qed.

Lemma keys_insert :
  forall pre b t,
    strict_desc pre -> strict_desc t ->
    Forall (fun x => block_key b < Rabs (b2r x)) pre ->
    Forall (fun x => Rabs (b2r x) < block_key b) t ->
    keys_decreasing (map CSingle pre ++ b :: map CSingle t).
Proof.
  induction pre as [| x pre IH]; intros b t Hp Ht Ha Hb.
  - cbn [map app]. apply keys_prefix; [ | exact Ht ].
    intros y Hy. rewrite Forall_forall in Hb. exact (Hb y Hy).
  - inversion Ha as [| ? ? Hx Ha']; subst. cbn [map app].
    split; [ | apply IH; [ exact (strict_desc_tail _ _ Hp) | exact Ht | exact Ha' | exact Hb ] ].
    destruct pre as [| y pre']; cbn [map app block_key].
    + exact Hx.
    + exact (proj1 Hp).
Qed.

Lemma reduce_insert :
  forall pre b t,
    flat_map cblock_reduce (map CSingle pre ++ b :: map CSingle t)
    = pre ++ cblock_reduce b ++ t.
Proof.
  intros pre b t. rewrite flat_map_app. cbn [flat_map]. rewrite !reduce_singles. reflexivity.
Qed.

Lemma expand_insert :
  forall pre b t,
    flat_map cblock_expand (map CSingle pre ++ b :: map CSingle t)
    = pre ++ cblock_expand b ++ t.
Proof.
  intros pre b t. rewrite flat_map_app. cbn [flat_map]. rewrite !expand_singles. reflexivity.
Qed.

Lemma shape_insert_anti :
  forall (pre t : list binary64) (a b : binary64),
    Forall b64_nz pre -> Forall b64_nz t -> b64_fin a -> b64_fin b ->
    b2r b = - b2r a -> b2r a <> 0 ->
    Forall (fun x => Rabs (b2r a) < Rabs (b2r x)) pre ->
    Forall (fun x => Rabs (b2r x) < Rabs (b2r a)) t ->
    layered (pre ++ t) ->
    exists bs, pre ++ a :: b :: t = flat_map cblock_expand bs /\ carry_shape bs.
Proof.
  intros pre t a b Np Nt Fa Fb Hba Ha0 Hp Ht Lpt.
  assert (Nb : b2r b <> 0) by (rewrite Hba; intro H; apply Ha0; lra).
  assert (Eb : b = b64_neg a).
  { apply b64_eq_of_R; [ exact Fb | apply b64_neg_fin, Fa | rewrite b64_neg_R; exact Hba | exact Nb ]. }
  assert (Npt : Forall b64_nz (pre ++ t)) by (apply Forall_app; split; assumption).
  destruct (layered_desc _ Lpt Npt) as [Dpt Cpt].
  destruct (strict_desc_app _ _ Dpt) as [Dp Dt].
  exists (map CSingle pre ++ CAnti a :: map CSingle t).
  split; [ rewrite expand_insert, Eb; reflexivity | ].
  split; [ | split ].
  - apply Forall_app. split; [ apply Forall_map, Np | ].
    constructor; [ split; assumption | apply Forall_map, Nt ].
  - apply keys_insert; assumption.
  - rewrite reduce_insert. cbn [cblock_reduce app]. exact Cpt.
Qed.

Lemma shape_insert_twin :
  forall (pre t : list binary64) (x : binary64),
    Forall b64_nz pre -> Forall b64_nz t -> b64_fin x -> b2r x <> 0 ->
    2 * Rabs (b2r x) < bpow radix2 emax ->
    Forall (fun y => 2 * Rabs (b2r x) < Rabs (b2r y)) pre ->
    Forall (fun y => Rabs (b2r y) < 2 * Rabs (b2r x)) t ->
    layered (pre ++ b64_mult x b64_two_unit :: t) ->
    exists bs, pre ++ x :: x :: t = flat_map cblock_expand bs /\ carry_shape bs.
Proof.
  intros pre t x Np Nt Fx Hx0 Hov Hp Ht Lpt.
  destruct (double_exact x Fx Hov) as [Hd Fd].
  assert (Nd : b64_nz (b64_mult x b64_two_unit)) by (split; [ exact Fd | rewrite Hd; lra ]).
  assert (Npt : Forall b64_nz (pre ++ b64_mult x b64_two_unit :: t))
    by (apply Forall_app; split; [ exact Np | constructor; assumption ]).
  destruct (layered_desc _ Lpt Npt) as [Dpt Cpt].
  destruct (strict_desc_app _ _ Dpt) as [Dp Dt]. pose proof (strict_desc_tail _ _ Dt) as Dt'.
  exists (map CSingle pre ++ CTwin x :: map CSingle t).
  split; [ rewrite expand_insert; reflexivity | ].
  split; [ | split ].
  - apply Forall_app. split; [ apply Forall_map, Np | ].
    constructor; [ split; [ split; assumption | exact Hov ] | apply Forall_map, Nt ].
  - apply keys_insert; assumption.
  - rewrite reduce_insert. cbn [cblock_reduce app]. exact Cpt.
Qed.

Lemma drop_zeros_app : forall l1 l2, drop_zeros (l1 ++ l2) = drop_zeros l1 ++ drop_zeros l2.
Proof. intros. unfold drop_zeros. apply filter_app. Qed.

Lemma drop_zeros_cons_zero :
  forall x l, b64_is_zero x = true -> drop_zeros (x :: l) = drop_zeros l.
Proof. intros x l Hz. unfold drop_zeros. cbn [filter]. rewrite Hz. reflexivity. Qed.

Lemma drop_zeros_nonzero_mult :
  forall c l, Forall (pow2_multiple c) (map b2r l) -> Forall b64_fin l ->
    Forall (fun x => bpow radix2 c <= Rabs (b2r x)) (drop_zeros l).
Proof.
  intros c l Hm Hf. apply Forall_forall. intros y Hy.
  pose proof (drop_zeros_nz l Hf) as Hn. rewrite Forall_forall in Hn. destruct (Hn y Hy) as [_ Hy0].
  unfold drop_zeros in Hy. apply filter_In in Hy. destruct Hy as [Hy _].
  rewrite Forall_forall in Hm. destruct (Hm (b2r y) (in_map _ _ _ Hy)) as [n Hn'].
  exact (scaled_nonzero_ge _ n c Hn' Hy0).
Qed.

(* --------------------------------------------------------------------------
   The tie at the top, over any layered tail.
   -------------------------------------------------------------------------- *)

Lemma tie_finish_tail :
  forall (Q h' h : binary64) (t : list binary64) (c : Z),
    b64_fin Q -> b64_fin h' -> b64_fin h -> Forall b64_fin t ->
    Forall (below c) t -> layered t ->
    2 * bpow radix2 c < bpow radix2 emax ->
    Rabs (b2r h) = bpow radix2 c ->
    (   (b2r h' = - b2r h /\ pow2_multiple c (b2r Q) /\ bpow radix2 c < Rabs (b2r Q))
     \/ (b2r h' = 0 /\ b2r Q = b2r h)
     \/ (b2r h' = 0 /\ pow2_multiple (c + 1) (b2r Q) /\ b2r Q <> 0)) ->
    exists bs, drop_zeros (Q :: h' :: h :: t) = flat_map cblock_expand bs /\ carry_shape bs.
Proof.
  intros Q h' h t c FQ Fh' Fh Ft Bt Lt Hov Hh Hcase.
  pose proof (bpow_gt_0 radix2 c) as Hc0.
  assert (Hh0 : b2r h <> 0) by (intro H; rewrite H, Rabs_R0 in Hh; lra).
  destruct Hcase as [(Ha & Mq & Hq) | [(Hz & Hq) | (Hz & Mq & Hq0)]].
  - apply (shape_anti Q h' h t c); try assumption.
    + lra.
    + rewrite Ha, Rabs_Ropp. lra.
    + rewrite Ha, Rabs_Ropp. lra.
  - rewrite drop_zeros_skip2 by (apply b64_is_zero_true; assumption).
    apply (shape_twin Q h t c); try assumption.
    + lra.
    + rewrite Hq. lra.
    + rewrite Hq. lra.
    + apply pow2_multiple_pm. rewrite Hq. exact Hh.
  - destruct (singles_shape_of_layered (Q :: h' :: h :: t)) as [bs [E [S _]]].
    + repeat constructor; assumption.
    + rewrite drop_zeros_skip2 by (apply b64_is_zero_true; assumption).
      rewrite (drop_zeros_cons_nz Q) by (apply b64_is_zero_false; assumption).
      rewrite (drop_zeros_cons_nz h) by (apply b64_is_zero_false; assumption).
      assert (Bt0 : Forall (below c) (drop_zeros t)) by (apply Forall_filter_sub, Bt).
      assert (H2c : bpow radix2 c < bpow radix2 (c + 1)) by (apply bpow_lt; lia).
      split; [ exists (c + 1)%Z; split; [ exact Mq | ] | ].
      { constructor; [ unfold below; lra | ].
        eapply Forall_impl; [ | exact Bt0 ]. unfold below. intros y Hy. lra. }
      split; [ exists c; split; [ apply pow2_multiple_pm, Hh | exact Bt0 ] | ].
      apply layered_filter, Lt.
    + exists bs. split; assumption.
Qed.

(* --------------------------------------------------------------------------
   Absorption: a summand below a quarter ulp rounds away.
   -------------------------------------------------------------------------- *)

Lemma fexp_near :
  forall a b, (a - 1 <= b <= a)%Z -> (b64_fexp a - 1 <= b64_fexp b <= b64_fexp a)%Z.
Proof. intros a b H. unfold SpecFloat.fexp. unfold prec. lia. Qed.

Lemma rn_absorb :
  forall (g : binary64) (y : R),
    b2r g <> 0 -> Rabs y < ulp radix2 b64_fexp (b2r g) / 4 -> RN (b2r g + y) = b2r g.
Proof.
  intros g y Hg0 Hy.
  change (BinarySingleNaN.round_mode mode_b64) with (Znearest (fun t => negb (Z.even t))).
  rewrite ulp_neq_0 in Hy by exact Hg0.
  set (e := cexp radix2 b64_fexp (b2r g)) in *.
  set (Mg := mag radix2 (b2r g)).
  assert (He : e = b64_fexp Mg) by reflexivity.
  pose proof (mag_generic_gt radix2 b64_fexp (b2r g) Hg0 (Binary.generic_format_B2R prec emax g))
    as Hgt. fold e Mg in Hgt.
  assert (FB : generic_format radix2 b64_fexp (bpow radix2 Mg))
    by (apply generic_format_bpow, fexp_succ_le; rewrite <- He; exact Hgt).
  assert (Hg : Rabs (b2r g) <= bpow radix2 Mg - bpow radix2 e).
  { rewrite He, <- pred_bpow.
    exact (pred_ge_gt radix2 b64_fexp _ _
             (generic_format_abs _ _ _ (Binary.generic_format_B2R prec emax g)) FB
             (bpow_mag_gt radix2 (b2r g))). }
  assert (Hlo : bpow radix2 (Mg - 1) <= Rabs (b2r g)) by (apply bpow_mag_le, Hg0).
  pose proof (bpow_gt_0 radix2 e) as He0.
  assert (Hem : bpow radix2 e <= bpow radix2 (Mg - 1)) by (apply bpow_le; lia).
  set (z := b2r g + y).
  assert (Hz1 : Rabs z < bpow radix2 Mg) by (unfold z; pose proof (Rabs_triang (b2r g) y); lra).
  assert (Hz2 : bpow radix2 (Mg - 2) < Rabs z).
  { unfold z. pose proof (Rabs_triang_inv (b2r g) (- y)) as Ht.
    replace (b2r g - - y) with (b2r g + y) in Ht by ring. rewrite Rabs_Ropp in Ht.
    assert (H2 : bpow radix2 (Mg - 1) = 2 * bpow radix2 (Mg - 2)).
    { replace (bpow radix2 (Mg - 1)) with (bpow radix2 ((Mg - 2) + 1)) by (f_equal; ring).
      rewrite bpow_plus. change (bpow radix2 1) with 2. ring. }
    assert (bpow radix2 e <= 2 * bpow radix2 (Mg - 2)) by lra.
    lra. }
  assert (Hz0 : z <> 0) by (intro H; rewrite H, Rabs_R0 in Hz2; pose proof (bpow_gt_0 radix2 (Mg - 2)); lra).
  assert (Hmz : (Mg - 1 <= mag radix2 z <= Mg)%Z).
  { split.
    - assert (Hm : (Mg - 2 < mag radix2 z)%Z).
      { apply (lt_bpow radix2). apply Rlt_le_trans with (1 := Hz2).
        pose proof (bpow_mag_gt radix2 z). lra. }
      lia.
    - apply mag_le_bpow; assumption. }
  set (ez := cexp radix2 b64_fexp z).
  assert (Hez : (e - 1 <= ez <= e)%Z).
  { unfold ez, cexp. rewrite He. apply fexp_near, Hmz. }
  (* g is a multiple of 2^ez, and z sits within half a unit of it *)
  destruct (b64_pow2_multiple_cexp g) as [n Hn]. fold e in Hn.
  destruct (pow2_multiple_le ez e (b2r g) (proj2 Hez) (ex_intro _ n Hn)) as [k Hk].
  assert (Hez0 : 0 < bpow radix2 ez) by apply bpow_gt_0.
  assert (Hsm : scaled_mantissa radix2 b64_fexp z = IZR k + y * bpow radix2 (- ez)).
  { unfold scaled_mantissa. fold ez. unfold z. rewrite Hk, Rmult_plus_distr_r, Rmult_assoc, <- bpow_plus.
    replace (ez + - ez)%Z with 0%Z by ring. change (bpow radix2 0) with 1. ring. }
  assert (Hfrac : Rabs (y * bpow radix2 (- ez)) < / 2).
  { rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 (- ez))) by (left; apply bpow_gt_0).
    assert (Hb : bpow radix2 e <= 2 * bpow radix2 ez).
    { replace (2 * bpow radix2 ez) with (bpow radix2 (ez + 1))
        by (rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
      apply bpow_le. lia. }
    assert (Hinv : bpow radix2 (- ez) * bpow radix2 ez = 1).
    { rewrite <- bpow_plus. replace (- ez + ez)%Z with 0%Z by ring. reflexivity. }
    pose proof (bpow_gt_0 radix2 (- ez)). pose proof (Rabs_pos y). nra. }
  unfold round, F2R. cbn [Fnum Fexp]. fold ez.
  rewrite (Znearest_imp _ _ k); [ rewrite Hk; reflexivity | ].
  rewrite Hsm. replace (IZR k + y * bpow radix2 (- ez) - IZR k) with (y * bpow radix2 (- ez)) by ring.
  exact Hfrac.
Qed.

(* --------------------------------------------------------------------------
   One step after a tie.
   -------------------------------------------------------------------------- *)

(* After the anti pair (a, b), Q is a multiple of 2^Mlev above it; the next
   TwoSum keeps everything above the pair and leaves the tail below. *)
Lemma anti_final :
  forall (g Q a b : binary64) (t : list binary64) (Mlev c : Z),
    b64_fin g -> b64_TwoSum_safe g Q -> b64_fin a -> b64_fin b -> Forall b64_fin t ->
    pow2_multiple Mlev (b2r Q) -> (Mlev <= cexp radix2 b64_fexp (b2r g))%Z -> (c < Mlev)%Z ->
    b2r b = - b2r a -> Rabs (b2r a) = bpow radix2 c ->
    Forall (below c) t -> layered t ->
    let Q' := fst (b64_TwoSum g Q) in
    let h' := snd (b64_TwoSum g Q) in
    exists bs, drop_zeros (Q' :: h' :: a :: b :: t) = flat_map cblock_expand bs /\ carry_shape bs.
Proof.
  intros g Q a b t Mlev c Fg S Fa Fb Ft MQ HMg HcM Hba Ha Bt Lt Q' h'.
  destruct (ts_facts g Q S) as (FQ' & Fh & RQ' & Hex & Hno & _). fold Q' h' in FQ', Fh, RQ', Hex, Hno.
  pose proof (bpow_gt_0 radix2 c) as Hc0.
  assert (HcM' : bpow radix2 c < bpow radix2 Mlev) by (apply bpow_lt, HcM).
  assert (Ha0 : b2r a <> 0) by (intro H; rewrite H, Rabs_R0 in Ha; lra).
  assert (Hb0 : b2r b <> 0) by (rewrite Hba; intro H; apply Ha0; lra).
  assert (Mg : pow2_multiple Mlev (b2r g)) by (apply (pow2_multiple_le _ _ _ HMg), b64_pow2_multiple_cexp).
  assert (MQ' : pow2_multiple Mlev (b2r Q'))
    by (rewrite RQ'; apply round_pow2_multiple, pow2_multiple_plus; assumption).
  assert (Mh : pow2_multiple Mlev (b2r h')).
  { replace (b2r h') with ((b2r g + b2r Q) - b2r Q') by lra.
    apply pow2_multiple_minus; [ apply pow2_multiple_plus | ]; assumption. }
  assert (BtM : Forall (below Mlev) t) by (apply (below_mono c); [ lia | exact Bt ]).
  pose proof (head_pair_layered Q' h' t Mlev FQ' Fh Hno MQ' Mh BtM Lt) as Lall.
  change (Q' :: h' :: t) with ([Q'; h'] ++ t) in Lall. rewrite drop_zeros_app in Lall.
  change (Q' :: h' :: a :: b :: t) with ([Q'; h'] ++ a :: b :: t).
  rewrite drop_zeros_app.
  rewrite (drop_zeros_cons_nz a) by (apply b64_is_zero_false; assumption).
  rewrite (drop_zeros_cons_nz b) by (apply b64_is_zero_false; assumption).
  apply shape_insert_anti; try assumption.
  - apply drop_zeros_nz. repeat constructor; assumption.
  - apply drop_zeros_nz, Ft.
  - pose proof (drop_zeros_nonzero_mult Mlev [Q'; h']) as Hge.
    assert (Hm2 : Forall (pow2_multiple Mlev) (map b2r [Q'; h'])) by (repeat constructor; assumption).
    specialize (Hge Hm2 ltac:(repeat constructor; assumption)).
    eapply Forall_impl; [ | exact Hge ]. cbn beta. intros y Hy. lra.
  - eapply Forall_impl; [ | apply Forall_filter_sub, Bt ]. unfold below. intros y Hy. lra.
Qed.

(* After the twin (Q, h) with Q tiny next to g, g absorbs Q: the next
   TwoSum returns (g, Q), and the twin moves up to (h', h). *)
Lemma twin_final :
  forall (g Q z h : binary64) (t : list binary64) (c : Z),
    b64_fin g -> b2r g <> 0 -> b64_TwoSum_safe g Q -> b64_fin z -> b64_fin h -> Forall b64_fin t ->
    b2r z = 0 -> b2r Q = b2r h -> Rabs (b2r h) = bpow radix2 c ->
    bpow radix2 c < ulp radix2 b64_fexp (b2r g) / 4 ->
    2 * bpow radix2 c < bpow radix2 emax ->
    Forall (below c) t -> layered t ->
    let Q' := fst (b64_TwoSum g Q) in
    let h' := snd (b64_TwoSum g Q) in
    exists bs, drop_zeros (Q' :: h' :: z :: h :: t) = flat_map cblock_expand bs /\ carry_shape bs.
Proof.
  intros g Q z h t c Fg Hg0 S Fz Fh Ft Hz HQh Hh Hsmall Hov Bt Lt Q' h'.
  destruct (ts_facts g Q S) as (FQ' & Fh' & RQ' & Hex & _ & _). fold Q' h' in FQ', Fh', RQ', Hex.
  pose proof (bpow_gt_0 radix2 c) as Hc0.
  assert (Hh0 : b2r h <> 0) by (intro H; rewrite H, Rabs_R0 in Hh; lra).
  assert (HQ' : b2r Q' = b2r g) by (rewrite RQ'; apply rn_absorb; [ exact Hg0 | rewrite HQh, Hh; exact Hsmall ]).
  assert (Hh' : b2r h' = b2r h) by lra.
  assert (Eh : h = h') by (apply b64_eq_of_R; [ exact Fh | exact Fh' | symmetry; exact Hh' | exact Hh0 ]).
  assert (HQ0 : b2r Q' <> 0) by (rewrite HQ'; exact Hg0).
  rewrite (drop_zeros_cons_nz Q') by (apply b64_is_zero_false; assumption).
  rewrite (drop_zeros_cons_nz h') by (apply b64_is_zero_false; [ exact Fh' | rewrite Hh'; exact Hh0 ]).
  rewrite (drop_zeros_cons_zero z) by (apply b64_is_zero_true; assumption).
  rewrite (drop_zeros_cons_nz h) by (apply b64_is_zero_false; assumption).
  rewrite <- Eh.
  change (Q' :: h :: h :: drop_zeros t) with ([Q'] ++ h :: h :: drop_zeros t).
  assert (Hov' : 2 * Rabs (b2r h) < bpow radix2 emax) by (rewrite Hh; exact Hov).
  pose proof (ulp_le_abs_b64 g Hg0) as Hug.
  set (eg := cexp radix2 b64_fexp (b2r g)).
  assert (Hue : ulp radix2 b64_fexp (b2r g) = bpow radix2 eg) by (apply ulp_neq_0, Hg0).
  destruct (double_exact h Fh Hov') as [Hd Fd].
  apply shape_insert_twin; try assumption.
  - constructor; [ split; assumption | constructor ].
  - apply drop_zeros_nz, Ft.
  - constructor; [ rewrite HQ', Hh; lra | constructor ].
  - eapply Forall_impl; [ | apply Forall_filter_sub, Bt ]. unfold below. intros y Hy. rewrite Hh. lra.
  - (* layered [Q'; 2h] ++ tail *)
    cbn [app]. split.
    + exists eg. split.
      * rewrite HQ'. apply b64_pow2_multiple_cexp.
      * constructor.
        { unfold below. rewrite Hd, Rabs_mult, Rabs_pos_eq by lra. rewrite <- Hue. lra. }
        eapply Forall_impl; [ | apply Forall_filter_sub, Bt ]. unfold below. intros y Hy. rewrite <- Hue. lra.
    + split; [ | apply layered_filter, Lt ].
      exists (c + 1)%Z. split.
      * rewrite Hd. destruct (pow2_multiple_pm c (b2r h) Hh) as [n Hn].
        exists n. rewrite Hn, bpow_plus. change (bpow radix2 1) with 2. ring.
      * apply (below_mono c); [ lia | apply Forall_filter_sub, Bt ].
Qed.

Print Assumptions ts_facts.
Print Assumptions priest_keys_general.
Print Assumptions priest_third_nonzero.
Print Assumptions sstate_step.
Print Assumptions tie_values.
Print Assumptions tie_finish_tail.
Print Assumptions rn_absorb.
Print Assumptions anti_final.
Print Assumptions twin_final.
