(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Orient_b64_expansion_cc
   ----------------------------------------------------------------------------
   orient2d via fast_expansion_sum + carry_clean.  The rebuilt Stage D
   expansion, with NO dependence on the refuted
   `fast_expansion_sum_strong_nonoverlap_headline` (Orient_b64_expansion.v).

   PROOF PATH
   ----------
     Dekker / TwoProduct pairs      b64_Dekker_pair_priest_chain     (QED)
       -> Priest chains             (zeros dropped: [r;t], [r], [t], [])
       -> fast_expansion_sum
       -> carry_clean               carry_clean_fes_priest_ordered    (QED)
       -> nonoverlapping_chain + descending magnitudes + exact sum
       -> sign = sign of leading    nonoverlapping_chain_sign_correct (QED)
     overflow margin from coords    orient2d_cc_overflow_margin       (QED)

   1. DEKKER PAIRS ARE PRIEST CHAINS.  Under the Dekker safety and the
      no-underflow precondition already carried by Stage D, a nonzero pair
      (r, t) satisfies Priest's condition: |x*y| >= 2^-969 makes r normal,
      so ulp(r) = 2^(mag r - 53), and |t| <= ulp(r)/2 gives
      mag t <= mag r - 53, a gap of at least 53 = prec digits.  A zero
      component is dropped: the zero-high case r = 0 forces t = 0
      (b64_Dekker_zero_high), the zero-low case leaves [r], and the
      singleton/empty lists are Priest chains trivially.  carry_clean skips
      zeros and fast_expansion_sum treats them as exact no-ops
      (fes_drop_zeros_eq), so the raw pairs can be fed directly.

   2. THE OVERFLOW MARGIN FROM COORDINATES.  carry_clean's premise
      abs_sum e + abs_sum f <= 2^(emax-5) = 2^1019 follows from
        |coord| <= 2^orient2d_cc_coord_exp = 2^507  (six coordinates)
      plus the exact differences already in Stage D's safety predicate:
        |diff| <= 2^508,  |dx*dy| <= 2^1016,
        |r| <= 2^1016 (rounding to a power of two is monotone),
        |t| = |dx*dy - r| <= 2^1017,
        abs_sum per pair <= 3 * 2^1016,  both pairs <= 6 * 2^1016 <= 2^1019.
      The budget is `orient2d_cc_coord_budget`: 2*(507+1) + 3 = 1019 = emax-5.

   3. fast_expansion_sum_safe is NOT a hypothesis here: it follows from the
      same margin (B64_CarryCleanSign.fes_safe_of_overflow).  The precondition
      `b64_orient2d_expansion_cc_safe` is Stage D's `b64_orient2d_expansion_safe`
      minus that conjunct (`b64_orient2d_expansion_safe_cc_safe`).

   topic: binary64
   claimId: orient2d-expansion-carry-clean
   witness: b64_orient2d_expansion_cc_sign_correct

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lia Lra List.
From Flocq Require Import IEEE754.Binary IEEE754.BinarySingleNaN Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
     Orient_b64_sound B64_Pff_bridge B64_Expansion B64_FastExpansionSum
     B64_FastExpansionSum_Shewchuk B64_Overlap_Hierarchy B64_CarryCleanAlgo
     B64_CarryCleanCore B64_CarryCleanLadder B64_CarryCleanRung4
     B64_CarryCleanTarget B64_NonoverlapSign B64_CarryCleanSign
     Orient_b64_expansion.

Import ListNotations.
Local Open Scope R_scope.
Local Abbreviation b2r := (Binary.B2R prec emax).
Local Abbreviation rnd64 := (round radix2 (SpecFloat.fexp prec emax) (round_mode mode_b64)).

(* --------------------------------------------------------------------------
   Real-number facts about binary64.
   -------------------------------------------------------------------------- *)

(* Every nonzero double has a 53-bit normalized significand (as a real,
   with an unbounded exponent): z = m * 2^(mag z - 53). *)
Lemma b64_normalized_repr :
  forall z : binary64, b2r z <> 0 ->
    exists m : Z, b2r z = IZR m * bpow radix2 (mag radix2 (b2r z) - prec)
      /\ bpow radix2 (prec - 1) <= Rabs (IZR m) < bpow radix2 prec.
Proof.
  intros z Hz.
  pose proof (generic_format_FLX_FLT radix2 (3 - emax - prec) prec (b2r z)
                (Binary.generic_format_B2R prec emax z)) as Hf.
  set (k := (mag radix2 (b2r z) - prec)%Z).
  exists (Ztrunc (scaled_mantissa radix2 (FLX_exp prec) (b2r z))).
  unfold generic_format, F2R in Hf. cbn [Fnum Fexp] in Hf.
  change (cexp radix2 (FLX_exp prec) (b2r z)) with k in Hf.
  set (m := Ztrunc (scaled_mantissa radix2 (FLX_exp prec) (b2r z))) in Hf |- *.
  split; [ exact Hf | ].
  assert (Hm : Rabs (IZR m) = Rabs (b2r z) * bpow radix2 (- k)).
  { rewrite Hf. rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 k)) by (left; apply bpow_gt_0).
    rewrite Rmult_assoc, <- bpow_plus, Z.add_opp_diag_r. change (bpow radix2 0) with 1. ring. }
  rewrite Hm.
  pose proof (bpow_mag_le radix2 (b2r z) Hz) as Hlo.
  pose proof (bpow_mag_gt radix2 (b2r z)) as Hhi.
  pose proof (bpow_gt_0 radix2 (- k)) as Hk.
  split.
  - replace (prec - 1)%Z with ((mag radix2 (b2r z) - 1) + - k)%Z by (unfold k; ring).
    rewrite bpow_plus. apply Rmult_le_compat_r; [ lra | exact Hlo ].
  - replace prec with (mag radix2 (b2r z) + - k)%Z at 2 by (unfold k; ring).
    rewrite bpow_plus. apply Rmult_lt_compat_r; [ lra | exact Hhi ].
Qed.

Lemma b64_fexp_bpow_ok :
  forall a : Z, (3 - emax - prec <= a)%Z -> (SpecFloat.fexp prec emax (a + 1) <= a)%Z.
Proof.
  intros a Ha. unfold SpecFloat.fexp, SpecFloat.emin. unfold prec, emax in *. lia.
Qed.

Lemma rnd64_abs_le_bpow :
  forall (z : R) (a : Z), (3 - emax - prec <= a)%Z ->
    Rabs z <= bpow radix2 a -> Rabs (rnd64 z) <= bpow radix2 a.
Proof.
  intros z a Ha Hz.
  apply abs_round_le_generic; [ auto with typeclass_instances | auto with typeclass_instances | | exact Hz ].
  apply generic_format_bpow. apply b64_fexp_bpow_ok. exact Ha.
Qed.

Lemma rnd64_abs_ge_bpow :
  forall (z : R) (a : Z), (3 - emax - prec <= a)%Z ->
    bpow radix2 a <= Rabs z -> bpow radix2 a <= Rabs (rnd64 z).
Proof.
  intros z a Ha Hz.
  apply abs_round_ge_generic; [ auto with typeclass_instances | auto with typeclass_instances | | exact Hz ].
  apply generic_format_bpow. apply b64_fexp_bpow_ok. exact Ha.
Qed.

(* --------------------------------------------------------------------------
   1. Dekker pairs are Priest chains.
   -------------------------------------------------------------------------- *)

Definition dekker_no_underflow (x y : binary64) : Prop :=
  b2r x * b2r y = 0
  \/ bpow radix2 (3 - emax - prec + 2 * prec - 1) <= Rabs (b2r x * b2r y).

Lemma b64_Dekker_fst_R :
  forall x y, b64_Dekker_safe x y ->
    b2r (fst (b64_Dekker x y)) = rnd64 (b2r x * b2r y)
    /\ b64_fin (fst (b64_Dekker x y)).
Proof.
  intros x y Hs.
  destruct Hs as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hr _]]]]]]]]]]]]].
  exact (b64_mult_correct x y Hr).
Qed.

Lemma b64_Dekker_snd_fin :
  forall x y, b64_Dekker_safe x y -> b64_fin (snd (b64_Dekker x y)).
Proof.
  intros x y Hs.
  destruct Hs as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Ht4]]]]]]]]]]]]]]]].
  exact (proj2 (b64_plus_correct _ _ Ht4)).
Qed.

Lemma b64_Dekker_sum_R :
  forall x y, b64_Dekker_safe x y -> dekker_no_underflow x y ->
    b2r x * b2r y = b2r (fst (b64_Dekker x y)) + b2r (snd (b64_Dekker x y)).
Proof.
  intros x y Hs Hu. pose proof (b64_Dekker_correct x y Hs Hu) as H.
  destruct (b64_Dekker x y) as [r t]. exact H.
Qed.

Lemma b64_Dekker_err_R :
  forall x y, b64_Dekker_safe x y -> dekker_no_underflow x y ->
    Rabs (b2r (snd (b64_Dekker x y)))
    <= ulp radix2 (SpecFloat.fexp prec emax) (b2r (fst (b64_Dekker x y))) / 2.
Proof.
  intros x y Hs Hu. pose proof (b64_Dekker_nonoverlap x y Hs Hu) as H.
  destruct (b64_Dekker x y) as [r t]. exact H.
Qed.

(* Zero high component: reachable only as (0, 0). *)
Lemma b64_Dekker_zero_high :
  forall x y, b64_Dekker_safe x y -> dekker_no_underflow x y ->
    b2r (fst (b64_Dekker x y)) = 0 -> b2r (snd (b64_Dekker x y)) = 0.
Proof.
  intros x y Hs Hu Hr.
  destruct (b64_Dekker_fst_R x y Hs) as [HR _].
  pose proof (b64_Dekker_sum_R x y Hs Hu) as Hsum.
  assert (Hxy : b2r x * b2r y = 0).
  { destruct Hu as [H0 | Hbig]; [ exact H0 | exfalso ].
    pose proof (rnd64_abs_ge_bpow _ (3 - emax - prec + 2 * prec - 1) ltac:(unfold prec, emax; lia) Hbig) as Hge.
    rewrite <- HR, Hr, Rabs_R0 in Hge. pose proof (bpow_gt_0 radix2 (3 - emax - prec + 2 * prec - 1)). lra. }
  lra.
Qed.

(* Both components nonzero: Priest's condition, a 53-digit gap. *)
Theorem b64_Dekker_pair_priest :
  forall x y, b64_Dekker_safe x y -> dekker_no_underflow x y ->
    b2r (fst (b64_Dekker x y)) <> 0 -> b2r (snd (b64_Dekker x y)) <> 0 ->
    priest_nonoverlapping_b64 (fst (b64_Dekker x y)) (snd (b64_Dekker x y)).
Proof.
  intros x y Hs Hu Hr0 Ht0.
  destruct (b64_Dekker_fst_R x y Hs) as [HR _].
  pose proof (b64_Dekker_err_R x y Hs Hu) as Herr.
  set (r := fst (b64_Dekker x y)) in *. set (t := snd (b64_Dekker x y)) in *.
  set (E := (3 - emax - prec + 2 * prec - 1)%Z).
  (* r is normal *)
  assert (Hxy : bpow radix2 E <= Rabs (b2r x * b2r y)).
  { destruct Hu as [H0 | Hbig]; [ | exact Hbig ].
    exfalso. apply Hr0. rewrite HR, H0. apply round_0. auto with typeclass_instances. }
  assert (Hrbig : bpow radix2 E <= Rabs (b2r r)).
  { rewrite HR. apply rnd64_abs_ge_bpow; [ unfold E, prec, emax; lia | exact Hxy ]. }
  assert (Hmagr : (E < mag radix2 (b2r r))%Z).
  { pose proof (bpow_mag_gt radix2 (b2r r)) as Hg.
    apply (lt_bpow radix2). lra. }
  assert (Hulp : ulp radix2 (SpecFloat.fexp prec emax) (b2r r)
                 = bpow radix2 (mag radix2 (b2r r) - prec)).
  { rewrite ulp_neq_0 by exact Hr0. f_equal. unfold cexp, SpecFloat.fexp, SpecFloat.emin.
    unfold E, prec, emax in *. lia. }
  rewrite Hulp in Herr.
  assert (Hhalf : bpow radix2 (mag radix2 (b2r r) - prec) / 2
                  = bpow radix2 (mag radix2 (b2r r) - prec - 1)).
  { replace (mag radix2 (b2r r) - prec)%Z with ((mag radix2 (b2r r) - prec - 1) + 1)%Z at 1 by ring.
    rewrite bpow_plus, bpow_1. cbn [IZR radix_val radix2 Z.of_nat]. field. }
  rewrite Hhalf in Herr.
  assert (Hmagt : (mag radix2 (b2r t) <= mag radix2 (b2r r) - prec)%Z).
  { pose proof (bpow_mag_le radix2 (b2r t) Ht0) as Hl.
    assert (bpow radix2 (mag radix2 (b2r t) - 1) <= bpow radix2 (mag radix2 (b2r r) - prec - 1)) by lra.
    apply le_bpow in H. lia. }
  destruct (b64_normalized_repr r Hr0) as (mx & Hx & Hmx).
  destruct (b64_normalized_repr t Ht0) as (my & Hy & Hmy).
  exists mx, my, (mag radix2 (b2r r) - prec)%Z, (mag radix2 (b2r t) - prec)%Z.
  repeat split; try assumption; try apply Hmx; try apply Hmy. lia.
Qed.

Lemma drop_zeros_pair_cases :
  forall r t : binary64,
    (b64_is_zero r = false /\ b64_is_zero t = false /\ drop_zeros [r; t] = [r; t])
    \/ (exists l, drop_zeros [r; t] = l /\ (length l <= 1)%nat).
Proof.
  intros r t. unfold drop_zeros. cbn [filter].
  destruct (b64_is_zero r) eqn:Er; destruct (b64_is_zero t) eqn:Et; cbn [negb].
  - right. eexists. split; [ reflexivity | cbn; lia ].
  - right. eexists. split; [ reflexivity | cbn; lia ].
  - right. eexists. split; [ reflexivity | cbn; lia ].
  - left. repeat split; reflexivity.
Qed.

Lemma priest_chain_short : forall l : list binary64, (length l <= 1)%nat -> priest_chain l.
Proof. intros [| a [| b l]] H; cbn in H; [ exact I | exact I | lia ]. Qed.

(* The Stage D input from one Dekker product, zeros dropped, is a Priest
   chain; both raw components are finite. *)
Theorem b64_Dekker_pair_priest_chain :
  forall x y, b64_Dekker_safe x y -> dekker_no_underflow x y ->
    priest_chain (drop_zeros [fst (b64_Dekker x y); snd (b64_Dekker x y)])
    /\ Forall b64_fin [fst (b64_Dekker x y); snd (b64_Dekker x y)].
Proof.
  intros x y Hs Hu.
  pose proof (proj2 (b64_Dekker_fst_R x y Hs)) as Fr.
  pose proof (b64_Dekker_snd_fin x y Hs) as Ft.
  split; [ | repeat constructor; assumption ].
  destruct (drop_zeros_pair_cases (fst (b64_Dekker x y)) (snd (b64_Dekker x y)))
    as [(Er & Et & ->) | (l & -> & Hl)]; [ | exact (priest_chain_short l Hl) ].
  split; [ | exact I ].
  apply b64_Dekker_pair_priest; [ exact Hs | exact Hu | | ].
  - exact (proj2 (b64_nz_of_not_zero _ Fr Er)).
  - exact (proj2 (b64_nz_of_not_zero _ Ft Et)).
Qed.

(* --------------------------------------------------------------------------
   2. Magnitude of one Dekker pair.
   -------------------------------------------------------------------------- *)

Lemma b64_Dekker_pair_abs_sum :
  forall x y (a : Z), b64_Dekker_safe x y -> dekker_no_underflow x y ->
    (3 - emax - prec <= a)%Z ->
    Rabs (b2r x * b2r y) <= bpow radix2 a ->
    abs_sum [fst (b64_Dekker x y); snd (b64_Dekker x y)] <= 3 * bpow radix2 a.
Proof.
  intros x y a Hs Hu Ha Hxy.
  destruct (b64_Dekker_fst_R x y Hs) as [HR _].
  pose proof (b64_Dekker_sum_R x y Hs Hu) as Hsum.
  assert (Hr : Rabs (b2r (fst (b64_Dekker x y))) <= bpow radix2 a)
    by (rewrite HR; apply rnd64_abs_le_bpow; assumption).
  assert (Ht : Rabs (b2r (snd (b64_Dekker x y)))
               <= Rabs (b2r x * b2r y) + Rabs (b2r (fst (b64_Dekker x y)))).
  { replace (b2r (snd (b64_Dekker x y))) with (b2r x * b2r y + - b2r (fst (b64_Dekker x y))) by lra.
    eapply Rle_trans; [ apply Rabs_triang | rewrite Rabs_Ropp; lra ]. }
  cbn [abs_sum]. lra.
Qed.

(* --------------------------------------------------------------------------
   The coordinate domain and its budget (auditable constants).
   -------------------------------------------------------------------------- *)

Definition orient2d_cc_coord_exp : Z := 507.

(* 2 * (507 + 1) bits for a product of two differences, plus 3 bits for
   six products' worth of components (6 <= 2^3), lands exactly on emax - 5. *)
Lemma orient2d_cc_coord_budget :
  (2 * (orient2d_cc_coord_exp + 1) + 3 = emax - 5)%Z.
Proof. reflexivity. Qed.

Definition coord_in_cc_domain (c : binary64) : Prop :=
  Binary.is_finite prec emax c = true /\ Rabs (b2r c) <= bpow radix2 orient2d_cc_coord_exp.

Definition orient2d_inputs_cc_domain (P0 P1 Q : BPoint) : Prop :=
  coord_in_cc_domain (bx P0)  /\ coord_in_cc_domain (by_ P0) /\
  coord_in_cc_domain (bx P1)  /\ coord_in_cc_domain (by_ P1) /\
  coord_in_cc_domain (bx Q)   /\ coord_in_cc_domain (by_ Q).

(* Stage D's safety predicate minus `fast_expansion_sum_safe`, which is now
   derived (fes_safe_of_overflow). *)
Definition b64_orient2d_expansion_cc_safe (P0 P1 Q : BPoint) : Prop :=
  b64_orient2d_expansion_diffs_safe P0 P1 Q /\
  b64_orient2d_expansion_diffs_exact P0 P1 Q /\
  b64_Dekker_safe (b64_minus (bx P1) (bx P0)) (b64_minus (by_ Q) (by_ P0)) /\
  b64_Dekker_safe (b64_minus (bx P0) (bx Q))  (b64_minus (by_ P1) (by_ P0)) /\
  dekker_no_underflow (b64_minus (bx P1) (bx P0)) (b64_minus (by_ Q) (by_ P0)) /\
  dekker_no_underflow (b64_minus (bx P0) (bx Q))  (b64_minus (by_ P1) (by_ P0)).

Lemma b64_orient2d_expansion_safe_cc_safe :
  forall P0 P1 Q, b64_orient2d_expansion_safe P0 P1 Q -> b64_orient2d_expansion_cc_safe P0 P1 Q.
Proof.
  intros P0 P1 Q (H1 & H2 & H3 & H4 & H5 & H6 & _).
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 H6))))).
Qed.

Lemma diff_abs_le :
  forall a b : binary64, coord_in_cc_domain a -> coord_in_cc_domain b ->
    Rabs (b2r a - b2r b) <= bpow radix2 (orient2d_cc_coord_exp + 1).
Proof.
  intros a b [_ Ha] [_ Hb].
  rewrite bpow_plus, bpow_1. cbn [IZR radix_val radix2 Z.of_nat].
  unfold Rminus. eapply Rle_trans; [ apply Rabs_triang | rewrite Rabs_Ropp; lra ].
Qed.

Lemma prod_abs_le :
  forall a b : R, Rabs a <= bpow radix2 (orient2d_cc_coord_exp + 1) ->
    Rabs b <= bpow radix2 (orient2d_cc_coord_exp + 1) ->
    Rabs (a * b) <= bpow radix2 (2 * (orient2d_cc_coord_exp + 1)).
Proof.
  intros a b Ha Hb. rewrite Rabs_mult.
  replace (2 * (orient2d_cc_coord_exp + 1))%Z
    with ((orient2d_cc_coord_exp + 1) + (orient2d_cc_coord_exp + 1))%Z by ring.
  rewrite bpow_plus. apply Rmult_le_compat; try apply Rabs_pos; assumption.
Qed.

(* THE OVERFLOW MARGIN, from coordinates. *)
Theorem orient2d_cc_overflow_margin :
  forall P0 P1 Q,
    b64_orient2d_expansion_cc_safe P0 P1 Q ->
    orient2d_inputs_cc_domain P0 P1 Q ->
    let D1 := b64_Dekker (b64_minus (bx P1) (bx P0)) (b64_minus (by_ Q) (by_ P0)) in
    let D2 := b64_Dekker (b64_minus (bx P0) (bx Q))  (b64_minus (by_ P1) (by_ P0)) in
    abs_sum [fst D1; snd D1] + abs_sum [fst D2; snd D2] <= bpow radix2 (emax - 5).
Proof.
  intros P0 P1 Q (_ & (HM1 & HM2 & HM3 & HM4) & HD1 & HD2 & HU1 & HU2)
         (Cx0 & Cy0 & Cx1 & Cy1 & Cxq & Cyq) D1 D2.
  set (a := (2 * (orient2d_cc_coord_exp + 1))%Z).
  assert (Ha : (3 - emax - prec <= a)%Z) by (unfold a, orient2d_cc_coord_exp, prec, emax; lia).
  assert (P1b : Rabs (b2r (b64_minus (bx P1) (bx P0)) * b2r (b64_minus (by_ Q) (by_ P0))) <= bpow radix2 a).
  { rewrite HM1, HM2. apply prod_abs_le; apply diff_abs_le; assumption. }
  assert (P2b : Rabs (b2r (b64_minus (bx P0) (bx Q)) * b2r (b64_minus (by_ P1) (by_ P0))) <= bpow radix2 a).
  { rewrite HM3, HM4. apply prod_abs_le; apply diff_abs_le; assumption. }
  pose proof (b64_Dekker_pair_abs_sum _ _ a HD1 HU1 Ha P1b) as S1.
  pose proof (b64_Dekker_pair_abs_sum _ _ a HD2 HU2 Ha P2b) as S2.
  fold D1 in S1. fold D2 in S2.
  assert (Hb : 6 * bpow radix2 a <= bpow radix2 (emax - 5)).
  { rewrite <- orient2d_cc_coord_budget. fold a. rewrite bpow_plus.
    change (bpow radix2 3) with 8. pose proof (bpow_gt_0 radix2 a). lra. }
  lra.
Qed.

(* fast_expansion_sum_safe, hence Stage D's full safety predicate, follows. *)
Theorem b64_orient2d_expansion_cc_safe_full :
  forall P0 P1 Q,
    b64_orient2d_expansion_cc_safe P0 P1 Q ->
    orient2d_inputs_cc_domain P0 P1 Q ->
    b64_orient2d_expansion_safe P0 P1 Q.
Proof.
  intros P0 P1 Q Hs Hd.
  pose proof (orient2d_cc_overflow_margin P0 P1 Q Hs Hd) as Hov. cbv zeta in Hov.
  destruct Hs as (H1 & H2 & H3 & H4 & H5 & H6).
  pose proof (proj2 (b64_Dekker_pair_priest_chain _ _ H3 H5)) as F1.
  pose proof (proj2 (b64_Dekker_pair_priest_chain _ _ H4 H6)) as F2.
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6
           (fes_safe_of_overflow _ _ F1 F2 Hov))))))).
Qed.

(* --------------------------------------------------------------------------
   3. The carry_clean expansion and its sign.
   -------------------------------------------------------------------------- *)

Definition b64_orient2d_expansion_cc (P0 P1 Q : BPoint) : list binary64 :=
  carry_clean (b64_orient2d_expansion P0 P1 Q).

Definition b64_orient2d_expansion_cc_sign (P0 P1 Q : BPoint) : expansion_sign :=
  sign_of_expansion (b64_orient2d_expansion_cc P0 P1 Q).

Lemma abs_sum_drop_zeros : forall l, abs_sum (drop_zeros l) = abs_sum l.
Proof.
  induction l as [| x l IH]; [ reflexivity | ].
  unfold drop_zeros in *. cbn [filter].
  destruct (b64_is_zero x) eqn:Hz; cbn [negb abs_sum]; rewrite IH; [ | reflexivity ].
  rewrite (b64_is_zero_R x Hz), Rabs_R0. ring.
Qed.

Lemma Forall_fin_drop_zeros :
  forall l, Forall b64_fin l -> Forall b64_fin (drop_zeros l).
Proof.
  intros l F. eapply Forall_impl; [ | exact (Forall_drop_zeros_nz l F) ].
  intros a [Ha _]. exact Ha.
Qed.

Lemma b64_orient2d_expansion_pairs :
  forall P0 P1 Q,
    b64_orient2d_expansion P0 P1 Q
    = fast_expansion_sum
        [fst (b64_Dekker (b64_minus (bx P1) (bx P0)) (b64_minus (by_ Q) (by_ P0)));
         snd (b64_Dekker (b64_minus (bx P1) (bx P0)) (b64_minus (by_ Q) (by_ P0)))]
        [fst (b64_Dekker (b64_minus (bx P0) (bx Q)) (b64_minus (by_ P1) (by_ P0)));
         snd (b64_Dekker (b64_minus (bx P0) (bx Q)) (b64_minus (by_ P1) (by_ P0)))].
Proof.
  intros P0 P1 Q. unfold b64_orient2d_expansion.
  destruct (b64_Dekker (b64_minus (bx P1) (bx P0)) (b64_minus (by_ Q) (by_ P0))).
  destruct (b64_Dekker (b64_minus (bx P0) (bx Q)) (b64_minus (by_ P1) (by_ P0))).
  reflexivity.
Qed.

(* Value preservation, nonoverlap and descending order, together. *)
Theorem b64_orient2d_expansion_cc_props :
  forall P0 P1 Q,
    b64_orient2d_expansion_cc_safe P0 P1 Q ->
    orient2d_inputs_cc_domain P0 P1 Q ->
    let c := b64_orient2d_expansion_cc P0 P1 Q in
    nonoverlapping_chain c /\ mag_desc c
    /\ Forall (fun y => b2r y <> 0) c
    /\ expansion_R c = cross_R_BP P0 P1 Q.
Proof.
  intros P0 P1 Q Hs Hd c.
  pose proof (b64_orient2d_expansion_sum P0 P1 Q
                (b64_orient2d_expansion_cc_safe_full P0 P1 Q Hs Hd)) as Hcross.
  pose proof (orient2d_cc_overflow_margin P0 P1 Q Hs Hd) as Hov. cbv zeta in Hov.
  destruct Hs as (_ & _ & H3 & H4 & H5 & H6).
  destruct (b64_Dekker_pair_priest_chain _ _ H3 H5) as [Pe Fe].
  destruct (b64_Dekker_pair_priest_chain _ _ H4 H6) as [Pf Ff].
  unfold c, b64_orient2d_expansion_cc.
  rewrite b64_orient2d_expansion_pairs in Hcross |- *.
  set (e := [fst (b64_Dekker (b64_minus (bx P1) (bx P0)) (b64_minus (by_ Q) (by_ P0)));
             snd (b64_Dekker (b64_minus (bx P1) (bx P0)) (b64_minus (by_ Q) (by_ P0)))]) in *.
  set (f := [fst (b64_Dekker (b64_minus (bx P0) (bx Q)) (b64_minus (by_ P1) (by_ P0)));
             snd (b64_Dekker (b64_minus (bx P0) (bx Q)) (b64_minus (by_ P1) (by_ P0)))]) in *.
  (* zeros out: carry_clean on the raw output = carry_clean on Priest input *)
  rewrite <- (carry_clean_drop_zeros (fast_expansion_sum e f)),
          (fes_drop_zeros_eq e f Fe Ff Hov), carry_clean_drop_zeros.
  assert (Hov' : abs_sum (drop_zeros e) + abs_sum (drop_zeros f) <= bpow radix2 (emax - 5))
    by (rewrite !abs_sum_drop_zeros; exact Hov).
  destruct (carry_clean_fes_priest_ordered (drop_zeros e) (drop_zeros f) Pe Pf
              (Forall_fin_drop_zeros e Fe) (Forall_fin_drop_zeros f Ff) Hov')
    as (No & Md & Nz & Hsum).
  split; [ exact No | split; [ exact Md | split; [ exact Nz | ] ] ].
  rewrite Hsum, !expansion_R_drop_zeros, <- Hcross.
  symmetry. apply fast_expansion_sum_correct.
  exact (fes_safe_of_overflow e f Fe Ff Hov).
Qed.

(* HEADLINE: the carry_clean expansion's sign is the sign of cross_R_BP, on
   the coordinate domain, with no strong-nonoverlap hypothesis. *)
Theorem b64_orient2d_expansion_cc_sign_correct :
  forall P0 P1 Q,
    b64_orient2d_expansion_cc_safe P0 P1 Q ->
    orient2d_inputs_cc_domain P0 P1 Q ->
    match b64_orient2d_expansion_cc_sign P0 P1 Q with
    | ExpPos  => 0 < cross_R_BP P0 P1 Q
    | ExpNeg  => cross_R_BP P0 P1 Q < 0
    | ExpZero => cross_R_BP P0 P1 Q = 0
    end.
Proof.
  intros P0 P1 Q Hs Hd.
  destruct (b64_orient2d_expansion_cc_props P0 P1 Q Hs Hd) as (No & Md & _ & Hsum).
  pose proof (nonoverlapping_chain_sign_correct _ No Md) as H.
  unfold b64_orient2d_expansion_cc_sign. rewrite Hsum in H. exact H.
Qed.

(* --------------------------------------------------------------------------
   Assumption audit.
   -------------------------------------------------------------------------- *)

Print Assumptions b64_normalized_repr.
Print Assumptions b64_Dekker_zero_high.
Print Assumptions b64_Dekker_pair_priest.
Print Assumptions b64_Dekker_pair_priest_chain.
Print Assumptions b64_Dekker_pair_abs_sum.
Print Assumptions orient2d_cc_coord_budget.
Print Assumptions orient2d_cc_overflow_margin.
Print Assumptions b64_orient2d_expansion_cc_safe_full.
Print Assumptions b64_orient2d_expansion_cc_props.
Print Assumptions b64_orient2d_expansion_cc_sign_correct.
