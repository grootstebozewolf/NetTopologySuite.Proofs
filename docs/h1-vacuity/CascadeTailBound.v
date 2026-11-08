(* CascadeTailBound.v -- arbitrary-length tail bound and closed look-ahead
   for the TwoSum cascade of Fast-Expansion-Sum, in Flocq's FLX format
   (radix 2, precision p >= 2, unbounded exponents), round-to-nearest-even.
   Mechanizes docs/cascade-tail-bound-2026-11.md.  All Qed, no Admitted.

   HEADLINE  cascade_tail_bound : for two Priest chains e, f (chainR p) whose
     components, sorted by |.| ascending, are g_0 .. g_n (Permutation of
     e ++ f; nonzero; FLX-representable), the cascade Q_0 = g_0,
     Q_j = RN(g_j + Q_(j-1)), h_j = g_j + Q_(j-1) - Q_j satisfies, for every
     1 <= k <= n,
         |Q_(k-1) - g_(k-1)| <= 2 ulp(g_k)      (tail bound)
         |h_k| <= ulp(g_k)                      (error bound)
   and cascade_closed_lookahead : |h_k| <= ulp(g_(k+1)).

   STRUCTURE  stepA (tail bound => error bound); tie_even, gap, case_half,
     case_full (monotone rounding near 2^e); Tsum_bound (ulp sum), lemma_B
     (|Q_(k-2)| <= 2U); tail_bound_and_lookahead (strong induction, keys and
     Lemma S as hypotheses); chain_count / keys_derived (the Priest keys
     |g_j| < ulp(g_(j+2)) by counting) and tail_lt / chain_small /
     HS_derived (Lemma S by per-chain telescoping) discharge them.

   NOT COVERED  binary64 itself: FLT underflow, the binary64 cascade
     b64_grow_expansion_aux, and its link to this FLX model are not done here. *)
From Stdlib Require Import Reals ZArith Lia Lra List Permutation.
Import ListNotations.
From Flocq Require Import Core.

Local Open Scope R_scope.

Section Cascade.

Variable p : Z.
Hypothesis Hp : (2 <= p)%Z.

Local Instance p_gt_0 : Prec_gt_0 p.
Proof. unfold Prec_gt_0. lia. Qed.
Local Instance p_NE : Exists_NE radix2 (FLX_exp p).
Proof. apply exists_NE_FLX. right. lia. Qed.

Local Abbreviation fexp := (FLX_exp p).
Local Abbreviation F := (generic_format radix2 fexp).
Local Abbreviation RN := (round radix2 fexp ZnearestE).
Local Abbreviation ulp := (ulp radix2 fexp).
Local Abbreviation bpow := (bpow radix2).
Local Abbreviation mag := (mag radix2).

Definition mult (s : Z) (x : R) : Prop := exists n : Z, x = IZR n * bpow s.

(* ------------------------------------------------------------------ *)
(* Format facts                                                        *)
(* ------------------------------------------------------------------ *)

Lemma F_mult : forall x, F x -> mult (mag x - p) x.
Proof.
  intros x H. exists (Ztrunc (scaled_mantissa radix2 fexp x)).
  unfold generic_format, F2R in H. simpl in H. exact H.
Qed.

Lemma ulp_eq : forall x, x <> 0 -> ulp x = bpow (mag x - p).
Proof. intros x Hx. rewrite ulp_neq_0 by exact Hx. reflexivity. Qed.

Lemma bpow_split : forall s t, (s <= t)%Z -> bpow t = IZR (Zpower radix2 (t - s)) * bpow s.
Proof.
  intros s t H. rewrite IZR_Zpower by lia. rewrite <- bpow_plus. f_equal. ring.
Qed.

Lemma abs_mult : forall n s, Rabs (IZR n * bpow s) = IZR (Z.abs n) * bpow s.
Proof.
  intros n s. rewrite Rabs_mult, abs_IZR, (Rabs_pos_eq (bpow s)) by apply bpow_ge_0. reflexivity.
Qed.

(* A multiple of 2^s strictly below 2^t is at most 2^t - 2^s. *)
Lemma mult_below : forall s t x, mult s x -> (s <= t)%Z -> Rabs x < bpow t -> Rabs x <= bpow t - bpow s.
Proof.
  intros s t x [n ->] Hst H. rewrite abs_mult in *. rewrite (bpow_split s t Hst) in *.
  pose proof (bpow_gt_0 radix2 s) as Hs.
  assert (H1 : IZR (Z.abs n) < IZR (Zpower radix2 (t - s))).
  { apply Rmult_lt_reg_r with (bpow s); assumption. }
  apply lt_IZR in H1. assert (H2 : (Z.abs n <= Zpower radix2 (t - s) - 1)%Z) by lia.
  apply IZR_le in H2. rewrite minus_IZR in H2. nra.
Qed.

(* A multiple of 2^s of magnitude at most 2^(s+p) is representable. *)
Lemma rep : forall s x, mult s x -> Rabs x <= bpow (s + p) -> F x.
Proof.
  intros s x [n ->] H. rewrite abs_mult in H. rewrite (bpow_split s (s + p)) in H by lia.
  replace (s + p - s)%Z with p in H by ring.
  pose proof (bpow_gt_0 radix2 s) as Hs.
  assert (H1 : IZR (Z.abs n) <= IZR (Zpower radix2 p)).
  { apply Rmult_le_reg_r with (bpow s); assumption. }
  apply le_IZR in H1.
  destruct (Z.eq_dec (Z.abs n) (Zpower radix2 p)) as [He | Hne].
  - assert (Hb : F (bpow (s + p))) by (apply generic_format_bpow; unfold FLX_exp; lia).
    assert (Ev : IZR (Zpower radix2 p) * bpow s = bpow (s + p))
      by (rewrite (bpow_split s (s + p)) by lia; replace (s + p - s)%Z with p by ring; reflexivity).
    destruct (Z.abs_spec n) as [[_ Hn] | [_ Hn]]; rewrite Hn in He.
    + rewrite He, Ev. exact Hb.
    + replace n with (- Zpower radix2 p)%Z by lia. rewrite opp_IZR.
      replace (- IZR (Zpower radix2 p) * bpow s) with (- (IZR (Zpower radix2 p) * bpow s)) by ring.
      rewrite Ev. apply generic_format_opp, Hb.
  - apply generic_format_FLX. apply (FLX_spec _ _ _ (Float radix2 n s)); [ reflexivity | cbn [Fnum]; lia ].
Qed.

(* Nothing representable lies strictly between 2^e and 2^e + 2^(e+1-p). *)
Lemma gap : forall e x, F x -> Rabs x < bpow e + bpow (e + 1 - p) -> Rabs x <= bpow e.
Proof.
  intros e x Fx H. destruct (Rle_or_lt (Rabs x) (bpow e)) as [Hle | Hgt]; [ exact Hle | exfalso ].
  assert (Hx0 : x <> 0) by (intro Z; rewrite Z, Rabs_R0 in Hgt; pose proof (bpow_gt_0 radix2 e); lra).
  assert (Hsm : bpow (e + 1 - p) <= bpow e) by (apply bpow_le; lia).
  assert (Hm : mag x = (e + 1)%Z :> Z).
  { apply mag_unique. replace (e + 1 - 1)%Z with e by ring.
    rewrite bpow_plus. change (bpow 1) with 2. split; lra. }
  destruct (F_mult x Fx) as [n Hn]. rewrite Hm in Hn. rewrite Hn, abs_mult in Hgt, H.
  rewrite (bpow_split (e + 1 - p) e) in Hgt by lia.
  pose proof (bpow_gt_0 radix2 (e + 1 - p)) as Hs.
  assert (H1 : IZR (Zpower radix2 (e - (e + 1 - p))) < IZR (Z.abs n))
    by (apply Rmult_lt_reg_r with (bpow (e + 1 - p)); assumption).
  apply lt_IZR in H1. assert (H2 : (Zpower radix2 (e - (e + 1 - p)) + 1 <= Z.abs n)%Z) by lia.
  apply IZR_le in H2. rewrite plus_IZR in H2.
  rewrite (bpow_split (e + 1 - p) e) in H by lia. nra.
Qed.

(* Ties-to-even just above a power of two. *)
Lemma tie_even : forall e, RN (bpow e + bpow (e - p)) = bpow e.
Proof.
  intro e.
  assert (Hlt : bpow (e - p) < bpow e) by (apply bpow_lt; lia).
  assert (Hm : mag (bpow e + bpow (e - p)) = (e + 1)%Z :> Z).
  { apply mag_unique. replace (e + 1 - 1)%Z with e by ring. pose proof (bpow_gt_0 radix2 (e - p)).
    rewrite Rabs_pos_eq by (pose proof (bpow_gt_0 radix2 e); lra).
    rewrite bpow_plus. change (bpow 1) with 2. split; lra. }
  unfold round, scaled_mantissa, cexp. rewrite Hm. unfold FLX_exp, F2R. simpl.
  set (N := Zpower radix2 (p - 1)).
  assert (HN : IZR N = bpow (p - 1)) by (unfold N; apply IZR_Zpower; lia).
  assert (Hsc : (bpow e + bpow (e - p)) * bpow (- (e + 1 - p)) = IZR N + / 2).
  { rewrite HN, Rmult_plus_distr_r, <- !bpow_plus.
    replace (e + - (e + 1 - p))%Z with (p - 1)%Z by ring.
    replace (e - p + - (e + 1 - p))%Z with (-1)%Z by ring. reflexivity. }
  rewrite Hsc.
  assert (Hfl : Zfloor (IZR N + / 2) = N).
  { apply Zfloor_imp. rewrite plus_IZR. simpl. lra. }
  assert (Hev : Z.even N = true).
  { unfold N. replace (p - 1)%Z with (1 + (p - 2))%Z by ring.
    rewrite Zpower_plus by lia. rewrite Z.even_mul. reflexivity. }
  unfold Znearest. rewrite Hfl.
  replace (IZR N + / 2 - IZR N) with (/ 2) by ring. rewrite Rcompare_Eq by reflexivity.
  rewrite Hev. simpl. rewrite HN, <- bpow_plus. f_equal. ring.
Qed.


Lemma mag_bounds : forall x, x <> 0 -> bpow (mag x - 1) <= Rabs x < bpow (mag x).
Proof. intros x Hx. split; [ apply bpow_mag_le | apply bpow_mag_gt ]; exact Hx. Qed.

Lemma pow_double : forall e, bpow (e + 1) = 2 * bpow e.
Proof. intro e. rewrite bpow_plus. change (bpow 1) with 2. ring. Qed.

(* ------------------------------------------------------------------ *)
(* Step A: the tail bound at k gives the error bound at k              *)
(* ------------------------------------------------------------------ *)

Lemma stepA :
  forall g a Q, F g -> g <> 0 -> F a -> Rabs a <= Rabs g -> F Q ->
    Rabs (Q - a) <= 2 * ulp g ->
    Rabs (g + Q - RN (g + Q)) <= ulp g.
Proof.
  intros g a Q Fg Hg0 Fa Hag FQ HQa.
  rewrite (ulp_eq g Hg0) in *. set (m := (mag g : Z)). fold m in HQa |- *.
  set (u := bpow (m - p)) in *.
  pose proof (mag_bounds g Hg0) as [Hg1 Hg2]. fold m in Hg1, Hg2.
  assert (Hu2 : 2 * u = bpow (m + 1 - p)) by (unfold u; rewrite <- pow_double; f_equal; ring).
  assert (Hgu : Rabs g <= bpow m - u) by (apply mult_below; [ apply F_mult, Fg | lia | exact Hg2 ]).
  assert (Hu0 : 0 < u) by apply bpow_gt_0.
  (* |Q| <= 2^m *)
  assert (HQ : Rabs Q <= bpow m).
  { destruct (Rlt_or_le (Rabs a) (bpow (m - 1))) as [Hsmall | Hbig].
    - assert (H2u : 2 * u <= bpow (m - 1)) by (rewrite Hu2; apply bpow_le; lia).
      pose proof (Rabs_triang_inv Q a). pose proof (pow_double (m - 1)) as Hd.
      replace (m - 1 + 1)%Z with m in Hd by ring. lra.
    - assert (Ha0 : a <> 0) by (intro Z; rewrite Z, Rabs_R0 in Hbig; pose proof (bpow_gt_0 radix2 (m - 1)); lra).
      assert (Hma : mag a = m :> Z).
      { apply mag_unique. split; [ exact Hbig | lra ]. }
      assert (Hau : Rabs a <= bpow m - u).
      { apply mult_below; [ | lia | lra ]. pose proof (F_mult a Fa) as Hm. rewrite Hma in Hm. exact Hm. }
      apply gap; [ exact FQ | ]. pose proof (Rabs_triang_inv Q a). lra. }
  (* the sum stays below 2^(m+1) *)
  set (x := g + Q).
  assert (Hx : Rabs x < bpow (m + 1)).
  { unfold x. pose proof (Rabs_triang g Q). rewrite pow_double. lra. }
  pose proof (error_le_half_ulp radix2 fexp (fun t => negb (Z.even t)) x) as He.
  replace (x - RN x) with (- (RN x - x)) by ring. rewrite Rabs_Ropp.
  apply Rle_trans with (1 := He).
  destruct (Req_dec x 0) as [Hx0 | Hx0].
  - rewrite Hx0, ulp_FLX_0; [ lra | exact p_gt_0 ].
  - rewrite (ulp_eq x Hx0). assert (Hmx : (mag x <= m + 1)%Z) by (apply mag_le_bpow; assumption).
    assert (bpow (mag x - p) <= bpow (m + 1 - p)) by (apply bpow_le; lia). lra.
Qed.

(* ------------------------------------------------------------------ *)
(* Lattice helpers                                                     *)
(* ------------------------------------------------------------------ *)

Lemma mult_plus : forall s x y, mult s x -> mult s y -> mult s (x + y).
Proof. intros s x y [n ->] [m ->]. exists (n + m)%Z. rewrite plus_IZR. ring. Qed.

Lemma mult_k : forall s k, mult s (IZR k * bpow s).
Proof. intros s k. exists k. reflexivity. Qed.

Lemma mult_bpow : forall s t, (s <= t)%Z -> mult s (bpow t).
Proof. intros s t H. exists (Zpower radix2 (t - s)). apply bpow_split, H. Qed.

(* consecutive multiples of 2^s are 2^s apart *)
Lemma mult_step : forall s x y, mult s x -> mult s y -> x < y -> x + bpow s <= y.
Proof.
  intros s x y [n ->] [m ->] H. pose proof (bpow_gt_0 radix2 s).
  assert (H1 : IZR n < IZR m) by (apply Rmult_lt_reg_r with (bpow s); assumption).
  apply lt_IZR in H1. assert (H2 : (n + 1 <= m)%Z) by lia. apply IZR_le in H2. rewrite plus_IZR in H2. nra.
Qed.

Lemma succ_pow : forall e, succ radix2 fexp (bpow e) = bpow e + bpow (e + 1 - p).
Proof.
  intro e. rewrite succ_eq_pos by apply bpow_ge_0. rewrite ulp_bpow. reflexivity.
Qed.

Lemma bpow_e_p : forall e, bpow e = IZR (Zpower radix2 p) * bpow (e - p).
Proof. intro e. rewrite (bpow_split (e - p) e) by lia. replace (e - (e - p))%Z with p by ring. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The two monotone-rounding cases, for a positive a in [2^(e-1), 2^e) *)
(* ------------------------------------------------------------------ *)

Section Pos.
Variables (e : Z) (a b : R).
Hypothesis Fa : F a.
Hypothesis Ha : bpow (e - 1) <= a < bpow e.
Let w := bpow (e - p).

Lemma a_mult : mult (e - p) a.
Proof.
  assert (Hm : mag a = e :> Z) by (apply mag_unique; rewrite Rabs_pos_eq by (pose proof (bpow_gt_0 radix2 (e - 1)); lra); exact Ha).
  pose proof (F_mult a Fa) as H. rewrite Hm in H. exact H.
Qed.

Lemma a_top : a <= bpow e - w.
Proof.
  assert (Hpos : 0 <= a) by (pose proof (bpow_gt_0 radix2 (e - 1)); lra).
  pose proof (mult_below (e - p) e a a_mult ltac:(lia) ltac:(rewrite Rabs_pos_eq by exact Hpos; apply Ha)) as H.
  rewrite Rabs_pos_eq in H by exact Hpos. exact H.
Qed.

Lemma w_facts : 0 < w /\ 4 * w <= bpow e /\ 2 * w = bpow (e + 1 - p) /\ bpow (e - 1) * 2 = bpow e.
Proof.
  unfold w. split; [ apply bpow_gt_0 | ]. split.
  - replace 4 with (bpow 2) by reflexivity. rewrite <- bpow_plus. apply bpow_le. lia.
  - split; [ rewrite <- pow_double; f_equal; ring | ].
    pose proof (pow_double (e - 1)) as H. replace (e - 1 + 1)%Z with e in H by ring. lra.
Qed.

(* a shifted by k*w stays representable while within [-2^e, 2^e] *)
Lemma shift_F : forall k, Rabs (a + IZR k * w) <= bpow e -> F (a + IZR k * w).
Proof.
  intros k H. apply (rep (e - p)); [ apply mult_plus; [ exact a_mult | apply mult_k ] | ].
  replace (e - p + p)%Z with e by ring. exact H.
Qed.

Lemma case_half : Rabs b < 4 * w -> Rabs (RN (a + b) - a) <= 4 * w.
Proof.
  intro Hb. destruct w_facts as (Hw & H4 & H2 & Hd). pose proof a_top as Ht.
  pose proof (Rabs_def2 _ _ Hb) as [Hb1 Hb2].
  apply Rabs_le. split.
  - (* lower: a - 4w is representable *)
    assert (Fz : F (a + IZR (-4) * w)).
    { apply shift_F. apply Rabs_le. replace (IZR (-4)) with (-4) by reflexivity. split; lra. }
    pose proof (round_le radix2 fexp ZnearestE (a + IZR (-4) * w) (a + b) ltac:(replace (IZR (-4)) with (-4) by reflexivity; lra)) as R.
    rewrite (round_generic radix2 fexp ZnearestE _ Fz) in R. replace (IZR (-4)) with (-4) in R by reflexivity. lra.
  - (* upper *)
    destruct (Rle_or_lt (a + 4 * w) (bpow e)) as [Hy | Hy].
    + assert (Fy : F (a + IZR 4 * w)) by (apply shift_F; rewrite Rabs_pos_eq; replace (IZR 4) with 4 by reflexivity; lra).
      pose proof (round_le radix2 fexp ZnearestE (a + b) (a + IZR 4 * w) ltac:(replace (IZR 4) with 4 by reflexivity; lra)) as R.
      rewrite (round_generic radix2 fexp ZnearestE _ Fy) in R. replace (IZR 4) with 4 in R by reflexivity. lra.
    + assert (Fe : F (bpow e)) by (apply generic_format_bpow; unfold FLX_exp; lia).
      destruct (Rlt_or_le (a + b) (bpow e + w)) as [Hx | Hx].
      * assert (Hmid : a + b < (bpow e + succ radix2 fexp (bpow e)) / 2) by (rewrite succ_pow; lra).
        pose proof (round_N_le_midp radix2 fexp (fun t => negb (Z.even t)) (bpow e) (a + b) Fe Hmid). lra.
      * (* a + 4w > 2^e + w, so a + 4w >= 2^e + 2w *)
        assert (My : mult (e - p) (a + IZR 4 * w)) by (apply mult_plus; [ exact a_mult | apply mult_k ]).
        assert (Mx : mult (e - p) (bpow e + w)) by (apply mult_plus; [ apply mult_bpow; lia | exists 1%Z; unfold w; ring ]).
        pose proof (mult_step (e - p) _ _ Mx My ltac:(replace (IZR 4) with 4 by reflexivity; lra)) as Hst.
        replace (IZR 4) with 4 in Hst by reflexivity. fold w in Hst.
        set (c := bpow e + 2 * w).
        assert (Fc : F c).
        { unfold c. rewrite H2. apply (rep (e + 1 - p)).
          - apply mult_plus; [ apply mult_bpow; lia | exists 1%Z; ring ].
          - rewrite Rabs_pos_eq by (pose proof (bpow_gt_0 radix2 e); pose proof (bpow_gt_0 radix2 (e + 1 - p)); lra).
            replace (e + 1 - p + p)%Z with (e + 1)%Z by ring. rewrite pow_double. rewrite <- H2. lra. }
        assert (Hmc : mag c = (e + 1)%Z :> Z).
        { apply mag_unique. replace (e + 1 - 1)%Z with e by ring. rewrite pow_double.
          rewrite Rabs_pos_eq by (unfold c; lra). unfold c. split; lra. }
        assert (Hsc : succ radix2 fexp c = c + 2 * w).
        { rewrite succ_eq_pos by (unfold c; lra). rewrite ulp_eq by (unfold c; lra). rewrite Hmc. rewrite H2. reflexivity. }
        assert (Hmid : a + b < (c + succ radix2 fexp c) / 2) by (rewrite Hsc; unfold c; lra).
        pose proof (round_N_le_midp radix2 fexp (fun t => negb (Z.even t)) c (a + b) Fc Hmid). unfold c in *. lra.
Qed.

Lemma case_full : Rabs b <= 2 * w -> Rabs (RN (a + b) - a) <= 2 * w.
Proof.
  intro Hb. destruct w_facts as (Hw & H4 & H2 & Hd). pose proof a_top as Ht.
  pose proof (Rabs_le_inv _ _ Hb) as [Hb1 Hb2].
  apply Rabs_le. split.
  - assert (Fz : F (a + IZR (-2) * w)).
    { apply shift_F. apply Rabs_le. replace (IZR (-2)) with (-2) by reflexivity. split; lra. }
    pose proof (round_le radix2 fexp ZnearestE (a + IZR (-2) * w) (a + b) ltac:(replace (IZR (-2)) with (-2) by reflexivity; lra)) as R.
    rewrite (round_generic radix2 fexp ZnearestE _ Fz) in R. replace (IZR (-2)) with (-2) in R by reflexivity. lra.
  - destruct (Rle_or_lt (a + 2 * w) (bpow e)) as [Hy | Hy].
    + assert (Fy : F (a + IZR 2 * w)) by (apply shift_F; rewrite Rabs_pos_eq; replace (IZR 2) with 2 by reflexivity; lra).
      pose proof (round_le radix2 fexp ZnearestE (a + b) (a + IZR 2 * w) ltac:(replace (IZR 2) with 2 by reflexivity; lra)) as R.
      rewrite (round_generic radix2 fexp ZnearestE _ Fy) in R. replace (IZR 2) with 2 in R by reflexivity. lra.
    + (* then a = 2^e - w *)
      assert (Mz : mult (e - p) (bpow e + IZR (-2) * w)) by (apply mult_plus; [ apply mult_bpow; lia | apply mult_k ]).
      pose proof (mult_step (e - p) _ _ Mz a_mult ltac:(replace (IZR (-2)) with (-2) by reflexivity; lra)) as Hst.
      replace (IZR (-2)) with (-2) in Hst by reflexivity. fold w in Hst.
      assert (Ha' : a = bpow e - w) by lra.
      assert (Fe : F (bpow e)) by (apply generic_format_bpow; unfold FLX_exp; lia).
      destruct (Rlt_or_le (a + b) (bpow e + w)) as [Hx | Hx].
      * assert (Hmid : a + b < (bpow e + succ radix2 fexp (bpow e)) / 2) by (rewrite succ_pow; lra).
        pose proof (round_N_le_midp radix2 fexp (fun t => negb (Z.even t)) (bpow e) (a + b) Fe Hmid). lra.
      * assert (Hx' : a + b = bpow e + w) by lra.
        rewrite Hx'. unfold w. rewrite tie_even. fold w. lra.
Qed.

End Pos.

(* Both signs, via odd symmetry of ties-to-even. *)
Lemma RN_shift_opp : forall a b, RN (a + b) - a = - (RN (- a + - b) - - a).
Proof.
  intros a b. replace (- a + - b) with (- (a + b)) by ring. rewrite round_NE_opp. ring.
Qed.

Lemma case_half_any : forall a b, F a -> a <> 0 ->
  Rabs b < 4 * bpow (mag a - p) -> Rabs (RN (a + b) - a) <= 4 * bpow (mag a - p).
Proof.
  intros a b Fa Ha0 Hb. pose proof (mag_bounds a Ha0) as Hm.
  destruct (Rle_or_lt 0 a) as [Hpos | Hneg].
  - rewrite Rabs_pos_eq in Hm by exact Hpos. apply case_half; assumption.
  - rewrite RN_shift_opp, Rabs_Ropp. rewrite <- (mag_opp radix2 a) in Hb |- *.
    rewrite Rabs_left in Hm by exact Hneg. rewrite <- (mag_opp radix2 a) in Hm.
    apply case_half; [ apply generic_format_opp, Fa | exact Hm | rewrite Rabs_Ropp; exact Hb ].
Qed.

Lemma case_full_any : forall a b, F a -> a <> 0 ->
  Rabs b <= 2 * bpow (mag a - p) -> Rabs (RN (a + b) - a) <= 2 * bpow (mag a - p).
Proof.
  intros a b Fa Ha0 Hb. pose proof (mag_bounds a Ha0) as Hm.
  destruct (Rle_or_lt 0 a) as [Hpos | Hneg].
  - rewrite Rabs_pos_eq in Hm by exact Hpos. apply case_full; assumption.
  - rewrite RN_shift_opp, Rabs_Ropp. rewrite <- (mag_opp radix2 a) in Hb |- *.
    rewrite Rabs_left in Hm by exact Hneg. rewrite <- (mag_opp radix2 a) in Hm.
    apply case_full; [ apply generic_format_opp, Fa | exact Hm | rewrite Rabs_Ropp; exact Hb ].
Qed.

(* ------------------------------------------------------------------ *)
(* The cascade                                                         *)
(* ------------------------------------------------------------------ *)

Section Run.
Variable g : nat -> R.     (* sorted inputs g_0 .. g_n, ascending |.| *)
Variable n : nat.

Fixpoint Q (j : nat) : R :=
  match j with O => g O | S j' => RN (g (S j') + Q j') end.
Definition h (j : nat) : R :=
  match j with O => 0 | S j' => g (S j') + Q j' - Q (S j') end.
Fixpoint Ssum (j : nat) : R :=
  match j with O => g O | S j' => Ssum j' + g (S j') end.
Fixpoint Hsum (j : nat) : R :=
  match j with O => 0 | S j' => Hsum j' + h (S j') end.
Fixpoint Tsum (j : nat) : R :=
  match j with O => ulp (g O) | S j' => Tsum j' + ulp (g (S j')) end.

Hypothesis Hf : forall j, (j <= n)%nat -> F (g j).
Hypothesis Hnz : forall j, (j <= n)%nat -> g j <> 0.
Hypothesis Hsort : forall j, (S j <= n)%nat -> Rabs (g j) <= Rabs (g (S j)).
(* priest_keys_general *)
Hypothesis Hkey : forall j, (j + 2 <= n)%nat -> Rabs (g j) < ulp (g (j + 2)).
(* Lemma S (exact partial sum of two Priest chains) *)
Hypothesis HS : forall k, (2 <= k <= n)%nat -> Rabs (Ssum (k - 2)) < 2 * ulp (g k).

Lemma FQ : forall j, (j <= n)%nat -> F (Q j).
Proof.
  intros [| j] H; [ apply Hf, H | ]. simpl. apply generic_format_round; auto with typeclass_instances.
Qed.

Lemma SQH : forall j, Ssum j = Q j + Hsum j.
Proof. induction j as [| j IH]; simpl; [ ring | ]. rewrite IH. unfold h. simpl. ring. Qed.

Let r := bpow (- p).

Lemma r_facts : 0 < r /\ r <= / 4.
Proof.
  unfold r. split; [ apply bpow_gt_0 | ].
  replace (/ 4) with (bpow (-2)) by reflexivity. apply bpow_le. lia.
Qed.

Lemma ulp_key : forall j, (j + 2 <= n)%nat -> ulp (g j) <= r * ulp (g (j + 2)).
Proof.
  intros j Hj. pose proof (Hkey j Hj) as K.
  assert (H0 : g j <> 0) by (apply Hnz; lia). assert (H2 : g (j + 2)%nat <> 0) by (apply Hnz; lia).
  rewrite (ulp_eq _ H2) in *. rewrite (ulp_eq _ H0).
  assert (Hm : (mag (g j) <= mag (g (j + 2)%nat) - p)%Z) by (apply mag_le_bpow; assumption).
  unfold r. rewrite <- bpow_plus. apply bpow_le. lia.
Qed.

Lemma ulp_mono : forall j, (S j <= n)%nat -> ulp (g j) <= ulp (g (S j)).
Proof. intros j Hj. apply ulp_le; auto with typeclass_instances. Qed.

Lemma ulp_nonneg : forall x, 0 <= ulp x.
Proof. intro x. apply ulp_ge_0. Qed.

(* Lemma U, in division-free form *)
Lemma Tsum_bound : forall j, (1 <= j <= n)%nat ->
  (1 - r) * Tsum j <= ulp (g j) + ulp (g (j - 1)).
Proof.
  destruct r_facts as [Hr0 Hr1].
  intro j. induction j as [j IH] using (well_founded_induction lt_wf). intros Hj.
  destruct j as [| [| i]]; [ lia | | ].
  - simpl. pose proof (ulp_nonneg (g O)). pose proof (ulp_nonneg (g 1%nat)). nra.
  - cbn [Tsum]. replace (S (S i) - 1)%nat with (S i) by lia.
    pose proof (ulp_nonneg (g (S i))). pose proof (ulp_nonneg (g (S (S i)))).
    destruct i as [| i'].
    + cbn [Tsum]. pose proof (ulp_key 0 ltac:(lia)) as K. simpl in K.
      pose proof (ulp_nonneg (g O)). nra.
    + pose proof (IH (S i') ltac:(lia) ltac:(lia)) as IHi.
      replace (S i' - 1)%nat with i' in IHi by lia.
      pose proof (ulp_key (S i') ltac:(lia)) as K1. replace (S i' + 2)%nat with (S (S (S i'))) in K1 by lia.
      pose proof (ulp_key i' ltac:(lia)) as K2. replace (i' + 2)%nat with (S (S i')) in K2 by lia.
      nra.
Qed.

Definition LA (j : nat) : Prop := Rabs (h j) <= ulp (g j).
Definition TB (j : nat) : Prop := Rabs (Q (j - 1) - g (j - 1)) <= 2 * ulp (g j).

Lemma Hsum_bound : forall j, (forall i, (1 <= i <= j)%nat -> LA i) -> Rabs (Hsum j) <= Tsum j.
Proof.
  induction j as [| j IH]; intro HL; cbn [Hsum Tsum].
  - rewrite Rabs_R0. apply ulp_nonneg.
  - pose proof (Rabs_triang (Hsum j) (h (S j))).
    pose proof (IH (fun i Hi => HL i ltac:(lia))). pose proof (HL (S j) ltac:(lia)). unfold LA in *. lra.
Qed.

(* Lemma B *)
Lemma lemma_B : forall k, (2 <= k <= n)%nat -> (forall i, (1 <= i <= k - 2)%nat -> LA i) ->
  Rabs (Q (k - 2)) <= 2 * ulp (g k).
Proof.
  intros k Hk HL. destruct r_facts as [Hr0 Hr1].
  assert (Hk0 : g k <> 0) by (apply Hnz; lia).
  set (U := ulp (g k)). set (m := (mag (g k) : Z)).
  assert (HU : U = bpow (m - p)) by (unfold U, m; apply ulp_eq, Hk0).
  set (t := (m - p + 1)%Z).
  assert (H2U : 2 * U = bpow t) by (rewrite HU; unfold t; rewrite pow_double; ring).
  assert (Hsp : bpow (t + 1 - p) = 4 * r * U).
  { rewrite HU. unfold r, t. replace (m - p + 1 + 1 - p)%Z with ((m - p) + - p + 2)%Z by ring.
    rewrite !bpow_plus. change (bpow 2) with 4. ring. }
  pose proof (HS k Hk) as Hs. fold U in Hs. rewrite SQH in Hs.
  assert (HH : Rabs (Hsum (k - 2)) <= 4 * r * U).
  { destruct (Nat.eq_dec (k - 2) 0) as [E | E].
    - rewrite E. simpl. rewrite Rabs_R0. pose proof (ulp_nonneg (g k)). fold U in H. nra.
    - pose proof (Hsum_bound (k - 2) HL) as HB.
      pose proof (Tsum_bound (k - 2) ltac:(lia)) as TB2.
      pose proof (ulp_key (k - 2) ltac:(lia)) as K1. replace (k - 2 + 2)%nat with k in K1 by lia. fold U in K1.
      pose proof (ulp_key (k - 2 - 1) ltac:(lia)) as K2. replace (k - 2 - 1 + 2)%nat with (S (k - 2)) in K2 by lia.
      pose proof (ulp_mono (k - 2 + 1) ltac:(lia)) as M. replace (S (k - 2 + 1)) with k in M by lia.
      replace (k - 2 + 1)%nat with (S (k - 2)) in M by lia. fold U in M.
      assert (Tnn : 0 <= Tsum (k - 2)) by (pose proof (Rabs_pos (Hsum (k - 2))); lra).
      nra. }
  apply Rle_trans with (bpow t); [ | lra ].
  apply gap; [ apply FQ; lia | ].
  replace (Q (k - 2)) with (Ssum (k - 2) - Hsum (k - 2)) by (rewrite SQH; ring).
  pose proof (Rabs_triang (Ssum (k - 2)) (- Hsum (k - 2))) as Tr. rewrite Rabs_Ropp in Tr.
  unfold Rminus. rewrite Hsp. rewrite SQH. replace (Q (k - 2) + Hsum (k - 2) + - Hsum (k - 2)) with (Q (k - 2)) by ring.
  pose proof (Rabs_triang (Q (k - 2) + Hsum (k - 2)) (- Hsum (k - 2))) as Tr2.
  replace (Q (k - 2) + Hsum (k - 2) + - Hsum (k - 2)) with (Q (k - 2)) in Tr2 by ring.
  rewrite Rabs_Ropp in Tr2. lra.
Qed.

(* ------------------------------------------------------------------ *)
(* Main theorem: T(k) and LA(k) for every 1 <= k <= n                  *)
(* ------------------------------------------------------------------ *)

Lemma LA_of_TB : forall k, (1 <= k <= n)%nat -> TB k -> LA k.
Proof.
  intros [| k'] Hk HT; [ lia | ]. unfold LA, TB in *. replace (S k' - 1)%nat with k' in HT by lia.
  unfold h. cbn [Q].
  apply (stepA (g (S k')) (g k') (Q k')); [ apply Hf; lia | apply Hnz; lia | apply Hf; lia
    | apply Hsort; lia | apply FQ; lia | exact HT ].
Qed.

Lemma TB_step : forall k, (2 <= k <= n)%nat ->
  (forall i, (1 <= i < k)%nat -> TB i /\ LA i) -> TB k.
Proof.
  intros k Hk IH. destruct k as [| [| k']]; [ lia | lia | ].
  set (K := S (S k')). unfold TB. replace (K - 1)%nat with (S k') by (unfold K; lia).
  set (a := g (S k')). set (b := Q k').
  assert (HQ : Q (S k') = RN (a + b)) by reflexivity.
  assert (Ha0 : a <> 0) by (apply Hnz; lia). assert (HK0 : g K <> 0) by (apply Hnz; unfold K; lia).
  assert (Fa : F a) by (apply Hf; lia).
  set (U := ulp (g K)). set (mK := (mag (g K) : Z)). set (ma := (mag a : Z)).
  assert (HU : U = bpow (mK - p)) by (apply ulp_eq, HK0).
  assert (Hw : ulp a = bpow (ma - p)) by (apply ulp_eq, Ha0).
  assert (Hma : (ma <= mK)%Z).
  { apply mag_le_abs; [ exact Ha0 | ]. apply Hsort. unfold K; lia. }
  (* facts from the induction hypothesis at S k' *)
  destruct (IH (S k') ltac:(lia)) as [TBk LAk]. unfold TB, LA in TBk, LAk.
  replace (S k' - 1)%nat with k' in TBk by lia. fold a b in TBk. fold a in LAk.
  rewrite Hw in TBk, LAk.
  assert (Hhk : h (S k') = a + b - RN (a + b)) by reflexivity.
  assert (Key : Rabs (g k') < U).
  { pose proof (Hkey k' ltac:(unfold K in *; lia)) as Kk.
    replace (k' + 2)%nat with K in Kk by (unfold K; lia). exact Kk. }
  assert (Hb : Rabs b < U + 2 * bpow (ma - p)).
  { pose proof (Rabs_triang_inv b (g k')). lra. }
  assert (Hrho : RN (a + b) - a = b - h (S k')) by (rewrite Hhk; ring).
  rewrite HQ.
  destruct (Z_le_gt_dec ma (mK - 2)) as [C1 | C1].
  - (* w <= U/4 *)
    assert (Hw4 : 4 * bpow (ma - p) <= U).
    { rewrite HU. replace 4 with (bpow 2) by reflexivity. rewrite <- bpow_plus. apply bpow_le. lia. }
    rewrite Hrho. pose proof (Rabs_triang b (- h (S k'))) as Tr. rewrite Rabs_Ropp in Tr.
    unfold Rminus. pose proof (bpow_gt_0 radix2 (ma - p)). lra.
  - destruct (Z.eq_dec ma (mK - 1)) as [C2 | C2].
    + (* w = U/2 *)
      assert (HwU : 2 * bpow (ma - p) = U).
      { rewrite HU, C2, <- pow_double. f_equal. ring. }
      assert (Hb' : Rabs b < 4 * bpow (ma - p)) by lra.
      pose proof (case_half_any a b Fa Ha0 Hb') as R. fold ma in R. lra.
    + (* w = U *)
      assert (C3 : ma = mK) by lia.
      assert (HwU : bpow (ma - p) = U) by (rewrite HU, C3; reflexivity).
      assert (HB : Rabs b <= 2 * U).
      { pose proof (lemma_B K ltac:(unfold K; lia)
                      (fun i Hi => proj2 (IH i ltac:(unfold K in Hi; lia)))) as LB.
        replace (K - 2)%nat with k' in LB by (unfold K; lia). exact LB. }
      assert (Hb' : Rabs b <= 2 * bpow (mag a - p)) by (fold ma; lra).
      pose proof (case_full_any a b Fa Ha0 Hb') as R. fold ma in R. lra.
Qed.

Theorem tail_bound_and_lookahead :
  forall k, (1 <= k <= n)%nat -> TB k /\ LA k.
Proof.
  intro k. induction k as [k IH] using (well_founded_induction lt_wf). intro Hk.
  assert (HT : TB k).
  { destruct (Nat.eq_dec k 1) as [E | E].
    - subst k. unfold TB. simpl. rewrite Rminus_diag, Rabs_R0. pose proof (ulp_nonneg (g 1%nat)). lra.
    - apply TB_step; [ lia | ]. intros i Hi. apply IH; lia. }
  split; [ exact HT | apply LA_of_TB; assumption ].
Qed.

(* The closed look-ahead used by the cascade invariant: |h_k| <= ulp(g_{k+1}). *)
Corollary closed_lookahead :
  forall k, (1 <= k)%nat -> (S k <= n)%nat -> Rabs (h k) <= ulp (g (S k)).
Proof.
  intros k Hk Hk'. destruct (tail_bound_and_lookahead k ltac:(lia)) as [_ L]. unfold LA in L.
  apply Rle_trans with (1 := L). apply ulp_mono. exact Hk'.
Qed.

End Run.

(* ------------------------------------------------------------------ *)
(* Discharging the keys and Lemma S from two Priest chains             *)
(* ------------------------------------------------------------------ *)

(* Priest's relation (B64_Overlap_Hierarchy.priest_nonoverlapping_R with
   prec generalised to p) and chains, largest first. *)
Definition priestR (x y : R) : Prop :=
  exists (mx my kx ky : Z),
    x = IZR mx * bpow kx /\ y = IZR my * bpow ky /\
    bpow (p - 1) <= Rabs (IZR mx) < bpow p /\
    bpow (p - 1) <= Rabs (IZR my) < bpow p /\
    (kx - ky >= p)%Z.

Fixpoint chainR (l : list R) : Prop :=
  match l with
  | nil => True
  | x :: r => match r with nil => True | y :: _ => priestR x y /\ chainR r end
  end.

Lemma chainR_tail : forall x c, chainR (x :: c) -> chainR c.
Proof. intros x [| y c] H; [ exact I | apply H ]. Qed.

Fixpoint sumf (phi : R -> R) (l : list R) : R :=
  match l with nil => 0 | x :: r => phi x + sumf phi r end.

Lemma sumf_app : forall phi l1 l2, sumf phi (l1 ++ l2) = sumf phi l1 + sumf phi l2.
Proof. intros phi l1 l2. induction l1 as [| x l1 IH]; simpl; [ ring | rewrite IH; ring ]. Qed.

Lemma sumf_perm : forall phi l l', Permutation l l' -> sumf phi l = sumf phi l'.
Proof. intros phi l l' H. induction H; simpl; lra. Qed.

Lemma sumf_nonneg : forall phi l, (forall x, 0 <= phi x) -> 0 <= sumf phi l.
Proof. intros phi l H. induction l as [| x l IH]; simpl; [ lra | pose proof (H x); lra ]. Qed.

Lemma sumf_ext : forall phi psi l, (forall x, In x l -> phi x = psi x) -> sumf phi l = sumf psi l.
Proof.
  intros phi psi l H. induction l as [| x l IH]; simpl; [ reflexivity | ].
  rewrite (H x (or_introl eq_refl)), IH; [ reflexivity | intros y Hy; apply H; right; exact Hy ].
Qed.

Lemma sumf_le : forall phi psi l, (forall x, phi x <= psi x) -> sumf phi l <= sumf psi l.
Proof. intros phi psi l H. induction l as [| x l IH]; simpl; [ lra | pose proof (H x); lra ]. Qed.

Lemma in_le_sum : forall y l, In y l -> Rabs y <= sumf Rabs l.
Proof.
  intros y l. induction l as [| x l IH]; intro Hin; [ destruct Hin | ].
  pose proof (sumf_nonneg Rabs l Rabs_pos). simpl. destruct Hin as [-> | Hin].
  - lra.
  - pose proof (IH Hin). pose proof (Rabs_pos x). lra.
Qed.

Lemma abs_sum_le : forall l, Rabs (sumf (fun x => x) l) <= sumf Rabs l.
Proof.
  induction l as [| x l IH]; simpl; [ rewrite Rabs_R0; lra | ].
  pose proof (Rabs_triang x (sumf (fun x => x) l)). lra.
Qed.

(* normalised representation facts *)
Lemma norm_facts : forall m k, bpow (p - 1) <= Rabs (IZR m) < bpow p ->
  let x := IZR m * bpow k in
  x <> 0 /\ ulp x = bpow k /\ mult k x /\ Rabs x <= bpow (k + p) - bpow k
  /\ bpow (k + p - 1) <= Rabs x.
Proof.
  intros m k [H1 H2] x. pose proof (bpow_gt_0 radix2 k) as Hk.
  assert (Ha : Rabs x = Rabs (IZR m) * bpow k)
    by (unfold x; rewrite Rabs_mult, (Rabs_pos_eq (bpow k)) by lra; reflexivity).
  assert (Lo : bpow (k + p - 1) <= Rabs x)
    by (rewrite Ha; replace (k + p - 1)%Z with ((p - 1) + k)%Z by ring; rewrite bpow_plus; nra).
  assert (Hi : Rabs x < bpow (k + p))
    by (rewrite Ha; rewrite Zplus_comm, bpow_plus; nra).
  assert (Hx0 : x <> 0) by (intro Z; rewrite Z, Rabs_R0 in Lo; pose proof (bpow_gt_0 radix2 (k + p - 1)); lra).
  assert (Hm : mag x = (k + p)%Z :> Z) by (apply mag_unique; split; [ exact Lo | exact Hi ]).
  split; [ exact Hx0 | ]. split; [ rewrite ulp_eq by exact Hx0; rewrite Hm; f_equal; ring | ].
  split; [ exists m; reflexivity | ]. split; [ | exact Lo ].
  apply mult_below; [ exists m; reflexivity | lia | exact Hi ].
Qed.

(* Every component after x in a Priest chain sums to less than ulp x. *)
Lemma tail_lt : forall c x y, chainR (x :: y :: c) -> sumf Rabs (y :: c) < ulp x.
Proof.
  induction c as [| z c IH]; intros x y H.
  - destruct H as [(mx & my & kx & ky & Hx & Hy & Nx & Ny & Hg) _].
    destruct (norm_facts mx kx Nx) as (_ & Ux & _ & _ & _). destruct (norm_facts my ky Ny) as (_ & _ & _ & Uy & _).
    rewrite <- Hx in Ux. rewrite <- Hy in Uy. rewrite Ux. simpl.
    assert (bpow (ky + p) <= bpow kx) by (apply bpow_le; lia). pose proof (bpow_gt_0 radix2 ky). lra.
  - destruct H as [(mx & my & kx & ky & Hx & Hy & Nx & Ny & Hg) Hr].
    pose proof (IH y z Hr) as IHyz.
    destruct (norm_facts mx kx Nx) as (_ & Ux & _ & _ & _). destruct (norm_facts my ky Ny) as (_ & Uy & _ & Ay & _).
    rewrite <- Hx in Ux. rewrite <- Hy in Uy, Ay. rewrite Uy in IHyz. rewrite Ux.
    change (sumf Rabs (y :: z :: c)) with (Rabs y + sumf Rabs (z :: c)).
    assert (bpow (ky + p) <= bpow kx) by (apply bpow_le; lia). lra.
Qed.

Section Keys.
Variable G : R.
Definition phiK (x : R) : R :=
  if Rle_dec (ulp G) (Rabs x) then if Rle_dec (Rabs x) (Rabs G) then 1 else 0 else 0.

Lemma phiK_one : forall x, ulp G <= Rabs x -> Rabs x <= Rabs G -> phiK x = 1.
Proof.
  intros x H1 H2. unfold phiK.
  destruct (Rle_dec _ _) as [_ | N1]; [ | contradiction ].
  destruct (Rle_dec _ _) as [_ | N2]; [ reflexivity | contradiction ].
Qed.

Lemma phiK_nonneg : forall x, 0 <= phiK x.
Proof. intro x. unfold phiK. destruct (Rle_dec _ _); [ destruct (Rle_dec _ _) | ]; lra. Qed.

(* at most one component per chain lies in [ulp G, |G|] *)
Lemma chain_count : forall c, chainR c -> sumf phiK c <= 1.
Proof.
  induction c as [| x c IH]; intro Hc; simpl; [ lra | ].
  unfold phiK at 1. destruct (Rle_dec (ulp G) (Rabs x)) as [H1 | H1];
    [ destruct (Rle_dec (Rabs x) (Rabs G)) as [H2 | H2] | ].
  - destruct c as [| y c']; [ simpl; lra | ].
    pose proof (tail_lt c' x y Hc) as T.
    assert (Ux : ulp x <= ulp G) by (apply ulp_le; auto with typeclass_instances).
    rewrite (sumf_ext phiK (fun _ => 0) (y :: c')).
    + simpl. assert (Hz : forall l, sumf (fun _ => 0) l = 0) by (induction l; simpl; lra). rewrite Hz. lra.
    + intros z Hz. pose proof (in_le_sum z (y :: c') Hz). unfold phiK.
      destruct (Rle_dec (ulp G) (Rabs z)); [ lra | reflexivity ].
  - pose proof (IH (chainR_tail x c Hc)). lra.
  - pose proof (IH (chainR_tail x c Hc)). lra.
Qed.
End Keys.

Section Small.
Variable t : Z.
Definition phiS (x : R) : R := if Rlt_dec (Rabs x) (bpow t) then Rabs x else 0.

Lemma phiS_le : forall x, phiS x <= Rabs x.
Proof. intro x. unfold phiS. destruct (Rlt_dec _ _); [ lra | apply Rabs_pos ]. Qed.
Lemma phiS_nonneg : forall x, 0 <= phiS x.
Proof. intro x. unfold phiS. destruct (Rlt_dec _ _); [ apply Rabs_pos | lra ]. Qed.

(* the components of one chain below 2^t sum to less than 2^t *)
Lemma chain_small : forall c, chainR c -> sumf phiS c < bpow t.
Proof.
  induction c as [| x c IH]; intro Hc; simpl; [ apply bpow_gt_0 | ].
  unfold phiS at 1. destruct (Rlt_dec (Rabs x) (bpow t)) as [H1 | H1].
  - destruct c as [| y c']; [ simpl; lra | ].
    pose proof (tail_lt c' x y Hc) as T.
    destruct Hc as [(mx & my & kx & ky & Hx & Hy & Nx & Ny & Hg) _].
    destruct (norm_facts mx kx Nx) as (_ & Ux & Mx & _ & Lo). rewrite <- Hx in Ux, Mx, Lo.
    assert (Hkt : (kx <= t)%Z).
    { assert (bpow (kx + p - 1) < bpow t) by lra. apply lt_bpow in H. lia. }
    pose proof (mult_below kx t x Mx Hkt H1) as Hb.
    pose proof (sumf_le phiS Rabs (y :: c') phiS_le) as L. simpl in L, T. rewrite Ux in T. cbn [sumf]. lra.
  - pose proof (IH (chainR_tail x c Hc)). lra.
Qed.
End Small.

Section Merge.
Variable g : nat -> R.
Variable n : nat.
Variables e f : list R.
Hypothesis Hf : forall j, (j <= n)%nat -> F (g j).
Hypothesis Hnz : forall j, (j <= n)%nat -> g j <> 0.
Hypothesis Hsort : forall j, (S j <= n)%nat -> Rabs (g j) <= Rabs (g (S j)).
Hypothesis Hce : chainR e.
Hypothesis Hcf : chainR f.
Hypothesis Hperm : Permutation (map g (seq 0 (S n))) (e ++ f).

Lemma sorted_le : forall i j, (i <= j <= n)%nat -> Rabs (g i) <= Rabs (g j).
Proof.
  intros i j [Hij Hjn]. induction Hij as [| j Hij IH]; [ lra | ].
  pose proof (IH ltac:(lia)). pose proof (Hsort j Hjn). lra.
Qed.

Lemma seq_split : forall a b, (a <= b)%nat -> seq 0 b = seq 0 a ++ seq a (b - a).
Proof. intros a b H. replace b with (a + (b - a))%nat at 1 by lia. rewrite seq_app. reflexivity. Qed.

Lemma keys_derived : forall j, (j + 2 <= n)%nat -> Rabs (g j) < ulp (g (j + 2)).
Proof.
  intros j Hj. replace (j + 2)%nat with (S (S j)) by lia.
  destruct (Rlt_or_le (Rabs (g j)) (ulp (g (S (S j))))) as [H | H]; [ exact H | exfalso ].
  set (G := g (S (S j))) in *.
  assert (HG0 : G <> 0) by (apply Hnz; lia).
  assert (HGu : ulp G <= Rabs G).
  { rewrite ulp_eq by exact HG0. pose proof (mag_bounds G HG0) as [Lo _].
    assert (bpow (mag G - p) <= bpow (mag G - 1)) by (apply bpow_le; lia). lra. }
  pose proof (sorted_le j (S j) ltac:(lia)) as S1. pose proof (sorted_le (S j) (S (S j)) ltac:(lia)) as S2.
  fold G in S2.
  assert (Three : sumf (phiK G) (map g (seq j 3)) = 3).
  { cbn [seq map sumf]. fold G.
    rewrite (phiK_one G (g j)) by lra. rewrite (phiK_one G (g (S j))) by lra.
    rewrite (phiK_one G G) by lra. ring. }
  assert (Big : 3 <= sumf (phiK G) (map g (seq 0 (S n)))).
  { rewrite (seq_split j (S n)) by lia. rewrite map_app, sumf_app.
    replace (S n - j)%nat with (3 + (S n - j - 3))%nat by lia. rewrite seq_app, map_app, sumf_app.
    rewrite Three. pose proof (sumf_nonneg (phiK G) (map g (seq 0 j)) (phiK_nonneg G)).
    pose proof (sumf_nonneg (phiK G) (map g (seq (j + 3) (S n - j - 3))) (phiK_nonneg G)). lra. }
  rewrite (sumf_perm _ _ _ Hperm), sumf_app in Big.
  pose proof (chain_count G e Hce). pose proof (chain_count G f Hcf). lra.
Qed.

Lemma Ssum_seq : forall j, Ssum g j = sumf (fun x => x) (map g (seq 0 (S j))).
Proof.
  induction j as [| j IH]; [ simpl; ring | ].
  rewrite seq_S, map_app, sumf_app. cbn [Ssum]. rewrite IH. simpl. ring.
Qed.

Lemma HS_derived : forall k, (2 <= k <= n)%nat -> Rabs (Ssum g (k - 2)) < 2 * ulp (g k).
Proof.
  intros k Hk. assert (Hk0 : g k <> 0) by (apply Hnz; lia).
  set (t := (mag (g k) - p)%Z). assert (HU : ulp (g k) = bpow t) by (apply ulp_eq, Hk0).
  rewrite HU, Ssum_seq. replace (S (k - 2)) with (k - 1)%nat by lia.
  set (l1 := map g (seq 0 (k - 1))). set (l2 := map g (seq (k - 1) (S n - (k - 1)))).
  assert (Hgl : map g (seq 0 (S n)) = l1 ++ l2) by (unfold l1, l2; rewrite (seq_split (k - 1) (S n)) by lia; apply map_app).
  assert (Small : forall z, In z l1 -> Rabs z < bpow t).
  { intros z Hz. unfold l1 in Hz. apply in_map_iff in Hz as [i [<- Hi]]. apply in_seq in Hi.
    pose proof (sorted_le i (k - 2) ltac:(lia)) as L. pose proof (keys_derived (k - 2) ltac:(lia)) as K.
    replace (k - 2 + 2)%nat with k in K by lia. rewrite HU in K. lra. }
  assert (E1 : sumf Rabs l1 = sumf (phiS t) l1).
  { apply sumf_ext. intros z Hz. unfold phiS. destruct (Rlt_dec _ _) as [_ | N]; [ reflexivity | ].
    exfalso. apply N, Small, Hz. }
  pose proof (abs_sum_le l1) as A.
  pose proof (sumf_nonneg (phiS t) l2 (phiS_nonneg t)) as N2.
  pose proof (sumf_perm (phiS t) _ _ Hperm) as P. rewrite Hgl, !sumf_app in P.
  pose proof (chain_small t e Hce). pose proof (chain_small t f Hcf). lra.
Qed.

(* THE THEOREM, from two Priest chains and their sorted merge. *)
Theorem cascade_tail_bound :
  forall k, (1 <= k <= n)%nat ->
    Rabs (Q g (k - 1) - g (k - 1)) <= 2 * ulp (g k) /\ Rabs (h g k) <= ulp (g k).
Proof.
  intros k Hk. exact (tail_bound_and_lookahead g n Hf Hnz Hsort keys_derived HS_derived k Hk).
Qed.

Corollary cascade_closed_lookahead :
  forall k, (1 <= k)%nat -> (S k <= n)%nat -> Rabs (h g k) <= ulp (g (S k)).
Proof. exact (closed_lookahead g n Hf Hnz Hsort keys_derived HS_derived). Qed.

End Merge.

End Cascade.

Print Assumptions cascade_tail_bound.
Print Assumptions cascade_closed_lookahead.
Check cascade_tail_bound.
