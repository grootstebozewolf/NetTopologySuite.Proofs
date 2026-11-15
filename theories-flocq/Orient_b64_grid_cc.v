(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Orient_b64_grid_cc
   ----------------------------------------------------------------------------
   The SHARED BINARY-LATTICE theorem: Stage D on carry_clean with NO
   per-operation hypotheses.  On a shared binary lattice, the coordinate
   domain alone implies every hypothesis of b64_orient_sign_exact_cc_sound
   (Orient_b64_stage_d_cc.v).

   WHAT "SHARED" COSTS.  Any six finite doubles lie on SOME common lattice
   (take k as the smallest of their exponents), so sharing k is free.  The
   restriction is the coefficient bound |n| < 2^52 on that common lattice,
   i.e. a bounded DYNAMIC RANGE: the six coordinates' scales span at most
   about 52 bits.  1 and 2^-60 fail exactly there (on the 2^-112 lattice, 1
   has coefficient 2^112).  The lattice then gives both ends of the
   numerical argument: bounded coefficients make differences exact and
   bound every intermediate from above; the lattice spacing keeps every
   nonzero product away from zero.

   PROVENANCE.  The idea is classical in robust geometry (bounded-integer or
   fixed-point inputs make coordinate differences exact; cf. Fortune and
   Van Wyk, and the input assumptions behind Shewchuk's predicates).  What
   is new here is the mechanized derivation for this Dekker implementation
   (all 17 operations), the no-underflow side, and the two QEX showing a
   magnitude bound cannot replace the lattice.  The ceiling 426 comes from
   the crude per-step bounds, not from anything intrinsic.

   THE DOMAIN (orient2d_inputs_on_grid k).  All six coordinates are
   n * 2^k with ONE shared k and |n| < 2^52, grid_lo <= k <= grid_hi:
       grid_lo = -484   so a nonzero Dekker product is >= 2^(2k) >= 2^-968
                        (Dekker's no-underflow precondition needs 2^-969);
       grid_hi =  426   so every Dekker intermediate stays below 2^1024 by
                        the crude per-step bounds below (2p + 64 <= 1023 with
                        p = 53 + k); coordinates are below 2^478 <= 2^507.
   The integer regime |coord| <= 2^25 is the case k = 0.

   WHAT FOLLOWS FROM IT (orient2d_grid_hyps).
     - exact differences: (n1 - n2) 2^k with |n1 - n2| < 2^53 is a double
       (fmt_scaled), so b64_minus rounds nothing;
     - overflow safety of the four differences and of all 2 x 17 Dekker
       operations (b64_Dekker_safe_of_bound: one magnitude bound per step);
     - Dekker's no-underflow precondition;
     - the coordinate domain |coord| <= 2^507 of the carry_clean margin.
   Hence b64_orient_sign_exact_cc_grid_sound: on the grid the carry_clean
   decoder returns exactly the sign of the true orientation, and
   b64_orient_sign_stage_d_cc_int_sound: in the integer regime the full
   Stage D decoder needs no expansion-safety hypothesis at all.

   WHY A GRID AND NOT |coord| <= 2^507 ALONE (QEX, proved below).
     cc_domain_diffs_not_exact:  P0.x = 2^-60, P1.x = 1 -- inside the domain,
       1 - 2^-60 needs 61 bits, so the difference rounds;
     cc_domain_underflow:        coordinates 2^-600 -- inside the domain, the
       differences are exact, but the Dekker product 2^-1200 underflows.
   So exactness and no-underflow are not consequences of the magnitude
   bound; the grid is what supplies them.

   topic: binary64
   claimId: orient2d-stage-d-carry-clean-grid
   witness: b64_orient_sign_exact_cc_grid_sound

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human-reviewed (2026-11-14,
     J. Bloemscheer, PR #1018 @ 444eefe).
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lia Lra List.
From Flocq Require Import IEEE754.Binary IEEE754.BinarySingleNaN Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
     Orient_b64_sound B64_Pff_bridge B64_Expansion B64_CarryCleanAlgo
     B64_CarryCleanRung4 Orient_b64_exact Orient_b64_exact_full Orientation_b64
     Orient_b64_expansion Orient_b64_stage_d Orient_b64_expansion_cc
     Orient_b64_stage_d_cc.

Local Open Scope R_scope.
Local Abbreviation b2r := (Binary.B2R prec emax).
Local Abbreviation rnd64 := (round radix2 (SpecFloat.fexp prec emax) (round_mode mode_b64)).

(* -------------------------------------------------------------------------- *)
(* The grid domain.                                                           *)
(* -------------------------------------------------------------------------- *)

Definition grid_lo : Z := (-484)%Z.
Definition grid_hi : Z := 426%Z.

Definition coord_on_grid (k : Z) (c : binary64) : Prop :=
  Binary.is_finite prec emax c = true /\
  exists n : Z, b2r c = IZR n * bpow radix2 k /\ (Z.abs n < 2 ^ 52)%Z.

Definition orient2d_inputs_on_grid (k : Z) (P0 P1 Q : BPoint) : Prop :=
  (grid_lo <= k <= grid_hi)%Z /\
  coord_on_grid k (bx P0) /\ coord_on_grid k (by_ P0) /\
  coord_on_grid k (bx P1) /\ coord_on_grid k (by_ P1) /\
  coord_on_grid k (bx Q)  /\ coord_on_grid k (by_ Q).

Lemma IZR_abs_lt_pow : forall (n : Z) (m : Z), (0 <= m)%Z -> (Z.abs n < 2 ^ m)%Z ->
  Rabs (IZR n) < bpow radix2 m.
Proof.
  intros n m Hm Hn. rewrite <- abs_IZR.
  rewrite <- (IZR_Zpower radix2 m) by exact Hm. apply IZR_lt.
  change (Zpower radix2 m) with (2 ^ m)%Z. exact Hn.
Qed.

Lemma grid_abs_lt : forall (n k m : Z), (0 <= m)%Z -> (Z.abs n < 2 ^ m)%Z ->
  Rabs (IZR n * bpow radix2 k) < bpow radix2 (m + k).
Proof.
  intros n k m Hm Hn. rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 k)) by apply bpow_ge_0.
  rewrite bpow_plus. apply Rmult_lt_compat_r; [ apply bpow_gt_0 | exact (IZR_abs_lt_pow n m Hm Hn) ].
Qed.

Lemma grid_in_cc_domain :
  forall k c, (k <= grid_hi)%Z -> coord_on_grid k c -> coord_in_cc_domain c.
Proof.
  intros k c Hk (Fc & n & Hn & Hb). split; [ exact Fc | ].
  rewrite Hn. left. apply Rlt_le_trans with (bpow radix2 (52 + k)).
  - apply grid_abs_lt; [ lia | exact Hb ].
  - apply bpow_le. unfold grid_hi, orient2d_cc_coord_exp in *. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* Exact differences on the grid.                                             *)
(* -------------------------------------------------------------------------- *)

Lemma grid_minus :
  forall k a b, (grid_lo <= k <= grid_hi)%Z -> coord_on_grid k a -> coord_on_grid k b ->
    b64_safe Rminus a b
    /\ Binary.is_finite prec emax (b64_minus a b) = true
    /\ b2r (b64_minus a b) = b2r a - b2r b
    /\ exists d : Z, b2r (b64_minus a b) = IZR d * bpow radix2 k /\ (Z.abs d < 2 ^ 53)%Z.
Proof.
  intros k a b Hk (Fa & na & Ha & Hna) (Fb & nb & Hb & Hnb).
  set (d := (na - nb)%Z).
  assert (Hd : (Z.abs d < 2 ^ 53)%Z) by (unfold d; lia).
  assert (Hab : b2r a - b2r b = IZR d * bpow radix2 k) by (rewrite Ha, Hb; unfold d; rewrite minus_IZR; ring).
  assert (Hlt : Rabs (IZR d * bpow radix2 k) < bpow radix2 (53 + k)) by (apply grid_abs_lt; [ lia | exact Hd ]).
  assert (Hfmt : generic_format radix2 b64_fexp (IZR d * bpow radix2 k)).
  { apply (fmt_scaled d k (53 + k)); [ exact Hlt | ].
    unfold SpecFloat.fexp, SpecFloat.emin, prec, emax. unfold grid_lo, grid_hi in Hk. lia. }
  assert (Hr : rnd64 (b2r a - b2r b) = b2r a - b2r b).
  { rewrite Hab. apply round_generic; [ auto with typeclass_instances | exact Hfmt ]. }
  assert (S : b64_safe Rminus a b).
  { refine (conj Fa (conj Fb _)). change (Rabs (rnd64 (b2r a - b2r b)) < bpow radix2 emax).
    rewrite Hr, Hab. apply Rlt_le_trans with (1 := Hlt). apply bpow_le.
    unfold grid_hi in Hk. unfold emax. lia. }
  destruct (b64_minus_correct a b S) as [HR HF].
  assert (HR' : b2r (b64_minus a b) = b2r a - b2r b) by (rewrite HR; exact Hr).
  refine (conj S (conj HF (conj HR' _))).
  exists d. split; [ rewrite HR'; exact Hab | exact Hd ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Dekker safety from one magnitude bound per step.                           *)
(* -------------------------------------------------------------------------- *)

Lemma st_plus :
  forall a b pa pb q, b64_fin a -> b64_fin b ->
    Rabs (b2r a) <= bpow radix2 pa -> Rabs (b2r b) <= bpow radix2 pb ->
    (pa <= q - 1)%Z -> (pb <= q - 1)%Z -> (-1000 <= q)%Z -> (q < emax)%Z ->
    b64_safe Rplus a b /\ b64_fin (b64_plus a b) /\ Rabs (b2r (b64_plus a b)) <= bpow radix2 q.
Proof.
  intros a b pa pb q Fa Fb Ha Hb Hpa Hpb Hlo Hhi.
  assert (Hs : Rabs (b2r a + b2r b) <= bpow radix2 q).
  { eapply Rle_trans; [ apply Rabs_triang | ].
    pose proof (bpow_le radix2 pa (q - 1) Hpa). pose proof (bpow_le radix2 pb (q - 1) Hpb).
    replace (bpow radix2 q) with (2 * bpow radix2 (q - 1))
      by (replace q with (1 + (q - 1))%Z at 2 by ring; rewrite bpow_plus; reflexivity). lra. }
  assert (Hr : Rabs (rnd64 (b2r a + b2r b)) <= bpow radix2 q)
    by (apply rnd64_abs_le_bpow; [ unfold prec, emax; lia | exact Hs ]).
  assert (S : b64_safe Rplus a b).
  { refine (conj Fa (conj Fb _)). apply Rle_lt_trans with (1 := Hr). apply bpow_lt. exact Hhi. }
  destruct (b64_plus_correct a b S) as [HR HF].
  refine (conj S (conj HF _)). rewrite HR. exact Hr.
Qed.

Lemma st_minus :
  forall a b pa pb q, b64_fin a -> b64_fin b ->
    Rabs (b2r a) <= bpow radix2 pa -> Rabs (b2r b) <= bpow radix2 pb ->
    (pa <= q - 1)%Z -> (pb <= q - 1)%Z -> (-1000 <= q)%Z -> (q < emax)%Z ->
    b64_safe Rminus a b /\ b64_fin (b64_minus a b) /\ Rabs (b2r (b64_minus a b)) <= bpow radix2 q.
Proof.
  intros a b pa pb q Fa Fb Ha Hb Hpa Hpb Hlo Hhi.
  assert (Hs : Rabs (b2r a - b2r b) <= bpow radix2 q).
  { unfold Rminus. eapply Rle_trans; [ apply Rabs_triang | rewrite Rabs_Ropp ].
    pose proof (bpow_le radix2 pa (q - 1) Hpa). pose proof (bpow_le radix2 pb (q - 1) Hpb).
    replace (bpow radix2 q) with (2 * bpow radix2 (q - 1))
      by (replace q with (1 + (q - 1))%Z at 2 by ring; rewrite bpow_plus; reflexivity). lra. }
  assert (Hr : Rabs (rnd64 (b2r a - b2r b)) <= bpow radix2 q)
    by (apply rnd64_abs_le_bpow; [ unfold prec, emax; lia | exact Hs ]).
  assert (S : b64_safe Rminus a b).
  { refine (conj Fa (conj Fb _)). apply Rle_lt_trans with (1 := Hr). apply bpow_lt. exact Hhi. }
  destruct (b64_minus_correct a b S) as [HR HF].
  refine (conj S (conj HF _)). rewrite HR. exact Hr.
Qed.

Lemma st_mult :
  forall a b pa pb q, b64_fin a -> b64_fin b ->
    Rabs (b2r a) <= bpow radix2 pa -> Rabs (b2r b) <= bpow radix2 pb ->
    (pa + pb <= q)%Z -> (-1000 <= q)%Z -> (q < emax)%Z ->
    b64_safe Rmult a b /\ b64_fin (b64_mult a b) /\ Rabs (b2r (b64_mult a b)) <= bpow radix2 q.
Proof.
  intros a b pa pb q Fa Fb Ha Hb Hq Hlo Hhi.
  assert (Hs : Rabs (b2r a * b2r b) <= bpow radix2 q).
  { rewrite Rabs_mult. apply Rle_trans with (bpow radix2 pa * bpow radix2 pb).
    - apply Rmult_le_compat; try apply Rabs_pos; assumption.
    - rewrite <- bpow_plus. apply bpow_le. exact Hq. }
  assert (Hr : Rabs (rnd64 (b2r a * b2r b)) <= bpow radix2 q)
    by (apply rnd64_abs_le_bpow; [ unfold prec, emax; lia | exact Hs ]).
  assert (S : b64_safe Rmult a b).
  { refine (conj Fa (conj Fb _)). apply Rle_lt_trans with (1 := Hr). apply bpow_lt. exact Hhi. }
  destruct (b64_mult_correct a b S) as [HR HF].
  refine (conj S (conj HF _)). rewrite HR. exact Hr.
Qed.

Lemma veltkamp_C_facts :
  b64_fin b64_veltkamp_C /\ Rabs (b2r b64_veltkamp_C) <= bpow radix2 28.
Proof.
  assert (HC : b64_veltkamp_C = Binary.B754_finite prec emax false 4503599660924928 (-25) eq_refl)
    by (apply Binary.B2FF_inj; vm_compute; reflexivity).
  rewrite HC. split; [ reflexivity | ]. rewrite abs_B2R_fin.
  apply Rle_trans with (bpow radix2 53 * bpow radix2 (-25)).
  - apply Rmult_le_compat_r; [ apply bpow_ge_0 | ].
    rewrite <- IZR_Zpower by lia. apply IZR_le. cbn. lia.
  - rewrite <- bpow_plus. apply bpow_le. lia.
Qed.

(* Seventeen steps, each bounded by a power of two: inputs 2^p, the split
   constant 2^28, splits 2^(p+31), partial products 2^(2p+62), the error
   accumulation 2^(2p+64) < 2^1024. *)
Theorem b64_Dekker_safe_of_bound :
  forall x y (p : Z), b64_fin x -> b64_fin y ->
    Rabs (b2r x) <= bpow radix2 p -> Rabs (b2r y) <= bpow radix2 p ->
    (-450 <= p)%Z -> (2 * p + 64 < emax)%Z ->
    b64_Dekker_safe x y.
Proof.
  intros x y p Fx Fy Hx Hy Hlo Hhi.
  assert (He : emax = 1024%Z) by reflexivity.
  destruct veltkamp_C_facts as [FC HC].
  unfold b64_Dekker_safe. cbv zeta.
  set (px := b64_mult x b64_veltkamp_C).
  set (qx := b64_minus x px). set (hx := b64_plus qx px). set (tx := b64_minus x hx).
  set (py := b64_mult y b64_veltkamp_C).
  set (qy := b64_minus y py). set (hy := b64_plus qy py). set (ty := b64_minus y hy).
  set (x1y1 := b64_mult hx hy). set (x1y2 := b64_mult hx ty).
  set (x2y1 := b64_mult tx hy). set (x2y2 := b64_mult tx ty).
  set (r := b64_mult x y). set (t1 := b64_minus x1y1 r).
  set (t2 := b64_plus t1 x1y2). set (t3 := b64_plus t2 x2y1).
  destruct (st_mult x b64_veltkamp_C p 28 (p + 28) Fx FC Hx HC ltac:(lia) ltac:(lia) ltac:(lia))
    as (S1 & F1 & B1). fold px in F1, B1.
  destruct (st_minus x px p (p + 28) (p + 29) Fx F1 Hx B1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (S2 & F2 & B2). fold qx in F2, B2.
  destruct (st_plus qx px (p + 29) (p + 28) (p + 30) F2 F1 B2 B1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (S3 & F3 & B3). fold hx in F3, B3.
  destruct (st_minus x hx p (p + 30) (p + 31) Fx F3 Hx B3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (S4 & F4 & B4). fold tx in F4, B4.
  destruct (st_mult y b64_veltkamp_C p 28 (p + 28) Fy FC Hy HC ltac:(lia) ltac:(lia) ltac:(lia))
    as (S5 & F5 & B5). fold py in F5, B5.
  destruct (st_minus y py p (p + 28) (p + 29) Fy F5 Hy B5 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (S6 & F6 & B6). fold qy in F6, B6.
  destruct (st_plus qy py (p + 29) (p + 28) (p + 30) F6 F5 B6 B5 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (S7 & F7 & B7). fold hy in F7, B7.
  destruct (st_minus y hy p (p + 30) (p + 31) Fy F7 Hy B7 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (S8 & F8 & B8). fold ty in F8, B8.
  destruct (st_mult hx hy (p + 30) (p + 30) (2 * p + 60) F3 F7 B3 B7 ltac:(lia) ltac:(lia) ltac:(lia))
    as (S9 & F9 & B9). fold x1y1 in F9, B9.
  destruct (st_mult hx ty (p + 30) (p + 31) (2 * p + 61) F3 F8 B3 B8 ltac:(lia) ltac:(lia) ltac:(lia))
    as (S10 & F10 & B10). fold x1y2 in F10, B10.
  destruct (st_mult tx hy (p + 31) (p + 30) (2 * p + 61) F4 F7 B4 B7 ltac:(lia) ltac:(lia) ltac:(lia))
    as (S11 & F11 & B11). fold x2y1 in F11, B11.
  destruct (st_mult tx ty (p + 31) (p + 31) (2 * p + 62) F4 F8 B4 B8 ltac:(lia) ltac:(lia) ltac:(lia))
    as (S12 & F12 & B12). fold x2y2 in F12, B12.
  destruct (st_mult x y p p (2 * p) Fx Fy Hx Hy ltac:(lia) ltac:(lia) ltac:(lia))
    as (S13 & F13 & B13). fold r in F13, B13.
  destruct (st_minus x1y1 r (2 * p + 60) (2 * p) (2 * p + 61) F9 F13 B9 B13 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (S14 & F14 & B14). fold t1 in F14, B14.
  destruct (st_plus t1 x1y2 (2 * p + 61) (2 * p + 61) (2 * p + 62) F14 F10 B14 B10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (S15 & F15 & B15). fold t2 in F15, B15.
  destruct (st_plus t2 x2y1 (2 * p + 62) (2 * p + 61) (2 * p + 63) F15 F11 B15 B11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (S16 & F16 & B16). fold t3 in F16, B16.
  destruct (st_plus t3 x2y2 (2 * p + 63) (2 * p + 62) (2 * p + 64) F16 F12 B16 B12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (S17 & _ & _).
  exact (conj S1 (conj S2 (conj S3 (conj S4 (conj S5 (conj S6 (conj S7 (conj S8
           (conj S9 (conj S10 (conj S11 (conj S12 (conj S13 (conj S14 (conj S15
           (conj S16 S17)))))))))))))))).
Qed.

(* -------------------------------------------------------------------------- *)
(* Everything Stage D assumes, from the grid.                                 *)
(* -------------------------------------------------------------------------- *)

Lemma grid_diff_bound :
  forall k (d : Z), (Z.abs d < 2 ^ 53)%Z -> Rabs (IZR d * bpow radix2 k) <= bpow radix2 (53 + k).
Proof. intros k d Hd. left. apply grid_abs_lt; [ lia | exact Hd ]. Qed.

Lemma grid_no_underflow :
  forall k x y (d1 d2 : Z), (grid_lo <= k)%Z ->
    b2r x = IZR d1 * bpow radix2 k -> b2r y = IZR d2 * bpow radix2 k ->
    dekker_no_underflow x y.
Proof.
  intros k x y d1 d2 Hk Hx Hy. unfold dekker_no_underflow. rewrite Hx, Hy.
  replace (IZR d1 * bpow radix2 k * (IZR d2 * bpow radix2 k))
    with (IZR (d1 * d2) * bpow radix2 (k + k))
    by (rewrite mult_IZR, bpow_plus; ring).
  destruct (Z.eq_dec (d1 * d2) 0) as [H0 | H0].
  - left. rewrite H0. ring.
  - right. rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 (k + k))) by apply bpow_ge_0.
    rewrite <- abs_IZR.
    assert (H1 : 1 <= IZR (Z.abs (d1 * d2))) by (apply IZR_le; lia).
    apply Rle_trans with (bpow radix2 (k + k)).
    + apply bpow_le. unfold grid_lo in Hk. unfold emax, prec. lia.
    + pose proof (bpow_ge_0 radix2 (k + k)). nra.
Qed.

Lemma grid_dekker_pair :
  forall k a b c d, (grid_lo <= k <= grid_hi)%Z ->
    coord_on_grid k a -> coord_on_grid k b -> coord_on_grid k c -> coord_on_grid k d ->
    b64_Dekker_safe (b64_minus a b) (b64_minus c d)
    /\ dekker_no_underflow (b64_minus a b) (b64_minus c d).
Proof.
  intros k a b c d Hk Ga Gb Gc Gd.
  destruct (grid_minus k a b Hk Ga Gb) as (_ & F1 & _ & d1 & H1 & Hd1).
  destruct (grid_minus k c d Hk Gc Gd) as (_ & F2 & _ & d2 & H2 & Hd2).
  split.
  - apply (b64_Dekker_safe_of_bound _ _ (53 + k)); try assumption.
    + rewrite H1. exact (grid_diff_bound k d1 Hd1).
    + rewrite H2. exact (grid_diff_bound k d2 Hd2).
    + unfold grid_lo, grid_hi in Hk. lia.
    + unfold grid_lo, grid_hi in Hk. unfold emax. lia.
  - exact (grid_no_underflow k _ _ d1 d2 (proj1 Hk) H1 H2).
Qed.

(* HEADLINE (hypotheses).  The grid alone gives the domain and the whole
   Stage D safety predicate. *)
Theorem orient2d_grid_hyps :
  forall k P0 P1 Q, orient2d_inputs_on_grid k P0 P1 Q ->
    orient2d_inputs_cc_domain P0 P1 Q /\ b64_orient2d_expansion_cc_safe P0 P1 Q.
Proof.
  intros k P0 P1 Q (Hk & Gx0 & Gy0 & Gx1 & Gy1 & Gxq & Gyq).
  split.
  { repeat split; apply (grid_in_cc_domain k); try apply Hk; assumption. }
  destruct (grid_minus k _ _ Hk Gx1 Gx0) as (S1 & _ & E1 & _).
  destruct (grid_minus k _ _ Hk Gyq Gy0) as (S2 & _ & E2 & _).
  destruct (grid_minus k _ _ Hk Gx0 Gxq) as (S3 & _ & E3 & _).
  destruct (grid_minus k _ _ Hk Gy1 Gy0) as (S4 & _ & E4 & _).
  destruct (grid_dekker_pair k _ _ _ _ Hk Gx1 Gx0 Gyq Gy0) as [D1 U1].
  destruct (grid_dekker_pair k _ _ _ _ Hk Gx0 Gxq Gy1 Gy0) as [D2 U2].
  exact (conj (conj S1 (conj S2 (conj S3 S4)))
           (conj (conj E1 (conj E2 (conj E3 E4))) (conj D1 (conj D2 (conj U1 U2))))).
Qed.

(* HEADLINE (soundness).  On the grid, no per-operation hypothesis: the
   carry_clean decoder is definite and returns the true orientation sign. *)
Theorem b64_orient_sign_exact_cc_grid_sound :
  forall k P0 P1 Q, orient2d_inputs_on_grid k P0 P1 Q ->
    match b64_orient_sign_exact_cc P0 P1 Q with
    | OrientRPos       => 0 < cross_R_BP P0 P1 Q
    | OrientRNeg       => cross_R_BP P0 P1 Q < 0
    | OrientRZero      => cross_R_BP P0 P1 Q = 0
    | OrientRNan       => False
    | OrientRUncertain => False
    end.
Proof.
  intros k P0 P1 Q G.
  destruct (orient2d_grid_hyps k P0 P1 Q G) as [Hd Hs].
  pose proof (b64_orient_sign_exact_cc_sound P0 P1 Q Hd Hs) as H.
  pose proof (b64_orient_sign_exact_cc_definite P0 P1 Q) as [HnN HnU].
  destruct (b64_orient_sign_exact_cc P0 P1 Q); try exact H.
  - exact (HnN eq_refl).
  - exact (HnU eq_refl).
Qed.

(* The integer regime is the grid k = 0. *)
Lemma int_safe_on_grid :
  forall P0 P1 Q, orient2d_inputs_int_safe P0 P1 Q -> orient2d_inputs_on_grid 0 P0 P1 Q.
Proof.
  assert (C : forall c, coord_int_safe c -> coord_on_grid 0 c).
  { intros c (Fc & n & Hn & Hb). split; [ exact Fc | ]. exists n.
    split; [ rewrite Hn; change (bpow radix2 0) with 1; ring | lia ]. }
  intros P0 P1 Q (H1 & H2 & H3 & H4 & H5 & H6).
  split; [ unfold grid_lo, grid_hi; lia | ].
  repeat split; apply C; assumption.
Qed.

(* The full Stage D decoder in the integer regime, with NO expansion-safety
   hypothesis: strictly stronger than b64_orient_sign_stage_d_cc_sound. *)
Theorem b64_orient_sign_stage_d_cc_int_sound :
  forall P0 P1 Q : BPoint,
    orient2d_inputs_int_safe P0 P1 Q ->
    match b64_orient_sign_stage_d_cc P0 P1 Q with
    | OrientRPos       => 0 < cross_R_BP P0 P1 Q
    | OrientRNeg       => cross_R_BP P0 P1 Q < 0
    | OrientRZero      => cross_R_BP P0 P1 Q = 0
    | OrientRNan       => True
    | OrientRUncertain => True
    end.
Proof.
  intros P0 P1 Q Hint.
  destruct (orient2d_grid_hyps 0 P0 P1 Q (int_safe_on_grid P0 P1 Q Hint)) as [_ Hs].
  exact (b64_orient_sign_stage_d_cc_sound P0 P1 Q Hint Hs).
Qed.

(* -------------------------------------------------------------------------- *)
(* QEX: the magnitude bound alone does not give exactness or no-underflow.   *)
(* -------------------------------------------------------------------------- *)

Definition q_zero : binary64 := Binary.B754_zero prec emax false.
Definition q_one  : binary64 := Binary.B754_finite prec emax false 4503599627370496 (-52) eq_refl.
Definition q_2m60 : binary64 := Binary.B754_finite prec emax false 4503599627370496 (-112) eq_refl.
Definition q_2m600 : binary64 := Binary.B754_finite prec emax false 4503599627370496 (-652) eq_refl.

Lemma q_pow : forall s e H,
  b2r (Binary.B754_finite prec emax s 4503599627370496 e H)
  = (if s then -1 else 1) * bpow radix2 (52 + e).
Proof.
  intros s e H. rewrite B2R_fin, bpow_plus.
  assert (Hm : IZR (Z.pos 4503599627370496) = bpow radix2 52)
    by (rewrite <- IZR_Zpower by lia; reflexivity).
  destruct s; cbn [cond_Zopp].
  - change (Z.neg 4503599627370496) with (- Z.pos 4503599627370496)%Z.
    rewrite opp_IZR, Hm. ring.
  - rewrite Hm. ring.
Qed.

Lemma q_small_domain : forall e H, (52 + e <= 0)%Z ->
  coord_in_cc_domain (Binary.B754_finite prec emax false 4503599627370496 e H).
Proof.
  intros e H He. split; [ reflexivity | ]. rewrite q_pow, Rmult_1_l, Rabs_pos_eq by apply bpow_ge_0.
  apply bpow_le. unfold orient2d_cc_coord_exp. lia.
Qed.

(* (1 - 2^-60 needs 61 bits.) *)
Theorem cc_domain_diffs_not_exact :
  let P0 := mkBP q_2m60 q_zero in
  let P1 := mkBP q_one q_zero in
  let Q  := mkBP q_zero q_zero in
  orient2d_inputs_cc_domain P0 P1 Q /\ ~ b64_orient2d_expansion_diffs_exact P0 P1 Q.
Proof.
  intros P0 P1 Q.
  assert (Z0 : coord_in_cc_domain q_zero).
  { split; [ reflexivity | ]. cbn [Binary.B2R q_zero]. rewrite Rabs_R0. apply bpow_ge_0. }
  split.
  { unfold orient2d_inputs_cc_domain, P0, P1, Q; cbn [bx by_].
    repeat split; try (apply Z0); try (apply q_small_domain; lia). }
  intros (H1 & _). unfold P0, P1, Q in H1; cbn [bx by_] in H1.
  assert (Hm : b64_minus q_one q_2m60 = q_one) by (apply Binary.B2FF_inj; vm_compute; reflexivity).
  rewrite Hm in H1. unfold q_one, q_2m60 in H1. rewrite !q_pow in H1.
  pose proof (bpow_gt_0 radix2 (52 + -112)). lra.
Qed.

(* (2^-600 * 2^-600 = 2^-1200 is far below the smallest double.) *)
Theorem cc_domain_underflow :
  let P0 := mkBP q_zero q_zero in
  let P1 := mkBP q_2m600 q_zero in
  let Q  := mkBP q_zero q_2m600 in
  orient2d_inputs_cc_domain P0 P1 Q /\ b64_orient2d_expansion_diffs_exact P0 P1 Q
  /\ ~ dekker_no_underflow (b64_minus (bx P1) (bx P0)) (b64_minus (by_ Q) (by_ P0)).
Proof.
  intros P0 P1 Q.
  assert (Z0 : coord_in_cc_domain q_zero).
  { split; [ reflexivity | ]. cbn [Binary.B2R q_zero]. rewrite Rabs_R0. apply bpow_ge_0. }
  assert (Hm : b64_minus q_2m600 q_zero = q_2m600) by (apply Binary.B2FF_inj; vm_compute; reflexivity).
  assert (Hz : b64_minus q_zero q_zero = q_zero) by (apply Binary.B2FF_inj; vm_compute; reflexivity).
  assert (V : b2r q_2m600 = bpow radix2 (-600)).
  { unfold q_2m600. rewrite q_pow, Rmult_1_l. reflexivity. }
  split; [ | split ].
  - unfold orient2d_inputs_cc_domain, P0, P1, Q; cbn [bx by_].
    repeat split; try (apply Z0); try (apply q_small_domain; lia).
  - unfold b64_orient2d_expansion_diffs_exact, P0, P1, Q; cbn [bx by_].
    rewrite Hm, Hz. cbn [Binary.B2R q_zero]. repeat split; ring.
  - unfold dekker_no_underflow, P0, P1, Q; cbn [bx by_]. rewrite Hm, V.
    rewrite <- bpow_plus. intros [H | H].
    + pose proof (bpow_gt_0 radix2 (-600 + -600)). lra.
    + rewrite Rabs_pos_eq in H by apply bpow_ge_0. apply le_bpow in H.
      unfold emax, prec in H. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit.                                                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions grid_in_cc_domain.
Print Assumptions grid_minus.
Print Assumptions b64_Dekker_safe_of_bound.
Print Assumptions grid_no_underflow.
Print Assumptions orient2d_grid_hyps.
Print Assumptions b64_orient_sign_exact_cc_grid_sound.
Print Assumptions int_safe_on_grid.
Print Assumptions b64_orient_sign_stage_d_cc_int_sound.
Print Assumptions cc_domain_diffs_not_exact.
Print Assumptions cc_domain_underflow.
