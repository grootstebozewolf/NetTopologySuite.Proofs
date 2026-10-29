(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_Priest_FES_counterexample
   ----------------------------------------------------------------------------
   QEX on the Priest route: the corpus's `fast_expansion_sum` does NOT carry
   Priest's gap condition from input to output -- and its output on
   Priest-valid input need not even be Shewchuk-nonoverlapping.  This is NOT
   the route's stop condition: Priest's one-digit bound is still open.

   THE QUESTION ANSWERED.  With Priest 1991 §2's component condition stated
   as `priest_nonoverlapping_b64` and `priest_chain`
   (B64_Overlap_Hierarchy.v): if both inputs are Priest expansions, is the
   output of `fast_expansion_sum` one?  Priest himself never claims this --
   his summation is followed by a renormalization pass, which the corpus's
   algorithm lacks -- so a NO here measures the missing pass; it does not
   refute Priest.

   THE ANSWER IS NO, on Shewchuk's own example.  Shewchuk 1997 §2.4, after
   Theorem 13, gives the four-bit expansion

       11110000 + 1111 + 0.1111            added to itself

   to show that plain nonoverlapping is not preserved.  At p = 4 those three
   components have normalised exponents 4, 0, -4: a gap of exactly p between
   neighbours.  So Shewchuk's counterexample input is ALREADY a Priest
   expansion -- a fact the corpus had not noticed.  Its binary64 lift, with
   M = 2^53 - 1, is

       e = f = [ M * 2^106 ; M * 2^53 ; M ]          (gaps 53, 53)

   and `fast_expansion_sum e f` evaluates (machine-checked below, sort step
   included) to

       [ 2^160 ; -2^106 ; 2^106 ; -2^53 ; 2^53 - 2 ; +0 ]

   The neighbours -2^106 and 2^106 have the same magnitude: they overlap in
   Shewchuk's sense, so a fortiori they violate Priest's 53-digit gap.  The
   pair survives `compress` (no zero sits between them), so the failure is
   not an artefact of zero padding.

   WHAT THIS SETTLES, all Qed:

     priest in  =/=>  priest out          (fes_priest_gap_preservation_false)
     priest in  =/=>  nonoverlapping out  (fes_priest_to_nonoverlapping_false)

   The second is strictly stronger (priest => nonoverlapping, rung proved in
   B64_Overlap_Hierarchy.v): on Priest-valid input the algorithm falls TWO
   rungs of the hierarchy, not one.

   WHAT THIS DOES NOT SETTLE (do not overclaim).
     - Priest's ONE-DIGIT bound -- the "Priest-style bound" of the route's
       stop condition (docs/thm13-priest-route.md §4).  The offending pair
       sits inside the one-bit slack (`witness_overlap_within_1`), so this
       witness is CONSISTENT with that bound.  Whether `fast_expansion_sum`
       keeps Priest-valid inputs within it is open.  Randomised binary64
       search (2e5 cases) and exhaustive p = 3 search (length <= 2, exponents
       in [-4, 4]) found no `overlap_within 1` failure; evidence, not proof.
     - Shewchuk's Theorem 13 itself (strongly nonoverlapping in and out,
       round-to-even).  The witness input is Priest-valid but NOT strongly
       nonoverlapping (M * 2^53 and M are adjacent and not powers of two), so
       nothing here contradicts Theorem 13.

   PROVENANCE.  The trace was first found by a Python double-precision model
   of `fast_expansion_sum` (insertion sort by |x|, `<=` keeps x first;
   Knuth TwoSum `(e_i, Q)`; output `qfinal :: rev hs`), then checked here by
   `vm_compute` against the corpus definition.  The sort uses `Rle_dec` and is
   not computable; it is discharged by case analysis on concrete magnitudes
   (`sort_witness`), closing the structural gap that
   B64_Shewchuk_Thm13_counterexample.v left as a hand-trace.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lia Lra List.
From Flocq Require Import IEEE754.Binary Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_Expansion
     B64_Expansion_Shewchuk B64_FastExpansionSum_Shewchuk
     B64_Shewchuk_Thm13_counterexample B64_Overlap_Hierarchy.

Import ListNotations.
Local Open Scope R_scope.

(* --------------------------------------------------------------------------
   The witness.  M = 2^53 - 1, a full 53-bit significand; the input
   components are M * 2^k.
   -------------------------------------------------------------------------- *)

Definition mant_M : positive := 9007199254740991.

Definition bM_scaled (k : Z) (H : SpecFloat.bounded prec emax mant_M k = true)
  : binary64 := Binary.B754_finite prec emax false mant_M k H.

Definition bM_2p106 : binary64 := bM_scaled 106 eq_refl.   (* M * 2^106 *)
Definition bM_2p53  : binary64 := bM_scaled 53 eq_refl.    (* M * 2^53  *)
Definition bM       : binary64 := bM_scaled 0 eq_refl.     (* M         *)

Definition fes_input : list binary64 := [bM_2p106; bM_2p53; bM].

(* The output, as `vm_compute` reports it.  Mantissa 2^52 at exponent e is
   2^(52+e). *)
Definition b2p160    : binary64 :=
  Binary.B754_finite prec emax false 4503599627370496 108 eq_refl.
Definition bneg2p106 : binary64 :=
  Binary.B754_finite prec emax true  4503599627370496 54 eq_refl.
Definition b2p106    : binary64 :=
  Binary.B754_finite prec emax false 4503599627370496 54 eq_refl.
Definition bneg2p53  : binary64 :=
  Binary.B754_finite prec emax true  4503599627370496 1 eq_refl.
Definition b2p53m2   : binary64 :=   (* 2^53 - 2 *)
  Binary.B754_finite prec emax false 9007199254740990 0 eq_refl.
Definition bposzero  : binary64 := Binary.B754_zero prec emax false.

(* --------------------------------------------------------------------------
   Concrete magnitudes.
   -------------------------------------------------------------------------- *)

Lemma IZR_M_pos : 0 < IZR (Z.pos mant_M).
Proof. apply IZR_lt. unfold mant_M. lia. Qed.

Lemma bM_scaled_R : forall k H, Binary.B2R prec emax (bM_scaled k H)
                                = IZR (Z.pos mant_M) * bpow radix2 k.
Proof. intros k H. reflexivity. Qed.

Lemma bM_scaled_abs : forall k H, Rabs (Binary.B2R prec emax (bM_scaled k H))
                                  = IZR (Z.pos mant_M) * bpow radix2 k.
Proof.
  intros k H. rewrite bM_scaled_R. apply Rabs_pos_eq.
  pose proof IZR_M_pos. pose proof (bpow_gt_0 radix2 k). nra.
Qed.

Lemma abs_bM_lt_bM_2p53 :
  Rabs (Binary.B2R prec emax bM) < Rabs (Binary.B2R prec emax bM_2p53).
Proof.
  unfold bM_2p53, bM. rewrite !bM_scaled_abs. pose proof IZR_M_pos.
  apply Rmult_lt_compat_l; [ lra | apply bpow_lt; lia ].
Qed.

Lemma abs_bM_2p53_lt_bM_2p106 :
  Rabs (Binary.B2R prec emax bM_2p53) < Rabs (Binary.B2R prec emax bM_2p106).
Proof.
  unfold bM_2p106, bM_2p53. rewrite !bM_scaled_abs. pose proof IZR_M_pos.
  apply Rmult_lt_compat_l; [ lra | apply bpow_lt; lia ].
Qed.

(* --------------------------------------------------------------------------
   The input is a Priest expansion: gap 53 = prec at each link.
   -------------------------------------------------------------------------- *)

Lemma mantissa_M_normalised :
  bpow radix2 (prec - 1) <= Rabs (IZR (Z.pos mant_M)) < bpow radix2 prec.
Proof.
  rewrite Rabs_pos_eq by (left; exact IZR_M_pos).
  unfold prec. rewrite <- !IZR_Zpower by lia.
  split; [ apply IZR_le | apply IZR_lt ]; vm_compute; congruence.
Qed.

Lemma priest_bM_scaled :
  forall kx ky Hx Hy, (kx - ky >= prec)%Z ->
    priest_nonoverlapping_b64 (bM_scaled kx Hx) (bM_scaled ky Hy).
Proof.
  intros kx ky Hx Hy Hgap.
  exists (Z.pos mant_M), (Z.pos mant_M), kx, ky.
  repeat split; try (apply bM_scaled_R); try apply mantissa_M_normalised;
    exact Hgap.
Qed.

Lemma fes_input_priest : priest_chain fes_input.
Proof.
  unfold fes_input, bM_2p106, bM_2p53, bM. simpl.
  repeat split; try apply priest_bM_scaled; unfold prec; lia.
Qed.

(* --------------------------------------------------------------------------
   Structural link, step 1: the magnitude sort.  `Rle_dec` does not compute,
   so each comparison is decided from the two strict inequalities; a tie (an
   element against its own copy) takes the `<=` branch.
   -------------------------------------------------------------------------- *)

Lemma insert_by_abs_nil : forall x, insert_by_abs x [] = [x].
Proof. reflexivity. Qed.

Lemma insert_by_abs_le :
  forall x y ys,
    Rabs (Binary.B2R prec emax x) <= Rabs (Binary.B2R prec emax y) ->
    insert_by_abs x (y :: ys) = x :: y :: ys.
Proof.
  intros x y ys H. simpl. destruct (Rle_dec _ _); [ reflexivity | contradiction ].
Qed.

Lemma insert_by_abs_gt :
  forall x y ys,
    Rabs (Binary.B2R prec emax y) < Rabs (Binary.B2R prec emax x) ->
    insert_by_abs x (y :: ys) = y :: insert_by_abs x ys.
Proof.
  intros x y ys H. simpl. destruct (Rle_dec _ _) as [Hle | _]; [ lra | reflexivity ].
Qed.

Lemma sort_witness :
  sort_by_abs (fes_input ++ fes_input)
  = [bM; bM; bM_2p53; bM_2p53; bM_2p106; bM_2p106].
Proof.
  pose proof abs_bM_lt_bM_2p53 as Hlo.
  pose proof abs_bM_2p53_lt_bM_2p106 as Hhi.
  unfold fes_input. cbn [app sort_by_abs].
  repeat first [ rewrite insert_by_abs_nil
               | rewrite insert_by_abs_le by lra
               | rewrite insert_by_abs_gt by lra ].
  reflexivity.
Qed.

(* --------------------------------------------------------------------------
   Structural link, step 2: the cascade.  Compared through `B2FF`, which is
   proof-free, then lifted back with `B2FF_inj`.
   -------------------------------------------------------------------------- *)

Lemma map_B2FF_inj :
  forall l1 l2 : list binary64,
    map (Binary.B2FF prec emax) l1 = map (Binary.B2FF prec emax) l2 -> l1 = l2.
Proof.
  induction l1 as [| x l1 IH]; intros [| y l2] H; try discriminate; [ reflexivity | ].
  simpl in H. injection H as Hxy Hl.
  f_equal; [ apply Binary.B2FF_inj; exact Hxy | apply IH; exact Hl ].
Qed.

Lemma fes_witness :
  fast_expansion_sum fes_input fes_input
  = [b2p160; bneg2p106; b2p106; bneg2p53; b2p53m2; bposzero].
Proof.
  apply map_B2FF_inj.
  unfold fast_expansion_sum. rewrite sort_witness.
  vm_compute. reflexivity.
Qed.

Lemma compress_witness :
  compress [b2p160; bneg2p106; b2p106; bneg2p53; b2p53m2; bposzero]
  = [b2p160; bneg2p106; b2p106; bneg2p53; b2p53m2].
Proof.
  cbn [compress].
  assert (Hsign : forall s m e H,
             Rcompare (Binary.B2R prec emax
                         (Binary.B754_finite prec emax s m e H)) 0
             = if s then Lt else Gt).
  { intros s m e H. cbn [Binary.B2R]. unfold F2R; cbn [Fnum Fexp].
    pose proof (bpow_gt_0 radix2 e) as He.
    destruct s.
    - apply Rcompare_Lt. apply Ropp_lt_cancel.
      rewrite Ropp_0, Ropp_mult_distr_l, <- opp_IZR.
      apply Rmult_lt_0_compat; [ apply IZR_lt; simpl; lia | exact He ].
    - apply Rcompare_Gt.
      apply Rmult_lt_0_compat; [ apply IZR_lt; simpl; lia | exact He ]. }
  unfold b2p160, bneg2p106, b2p106, bneg2p53, b2p53m2, bposzero.
  rewrite !Hsign.
  cbn [Binary.B2R]. rewrite Rcompare_Eq by reflexivity.
  reflexivity.
Qed.

(* --------------------------------------------------------------------------
   The offending pair: -2^106 followed by 2^106.
   -------------------------------------------------------------------------- *)

(* Mantissa 2^52 at exponent e, either sign, is +/- 2^(52+e). *)
Lemma pow2_mantissa_R :
  forall s e H,
    Binary.B2R prec emax (Binary.B754_finite prec emax s 4503599627370496 e H)
    = (if s then -1 else 1) * bpow radix2 (52 + e).
Proof.
  intros s e H. cbn [Binary.B2R]. unfold F2R; cbn [Fnum Fexp].
  rewrite bpow_plus, <- IZR_mant_bpow.
  destruct s; cbn [cond_Zopp].
  - change (Z.neg 4503599627370496) with (- Z.pos 4503599627370496)%Z.
    rewrite opp_IZR. ring.
  - ring.
Qed.

Lemma bneg2p106_b2p106_overlap : ~ nonoverlapping_b64 bneg2p106 b2p106.
Proof.
  unfold nonoverlapping_b64, bneg2p106, b2p106.
  rewrite !pow2_mantissa_R. cbv iota.
  pose proof (bpow_gt_0 radix2 (52 + 54)) as Hp.
  apply equal_magnitude_overlaps; [ lra | ].
  rewrite Rabs_left, Rabs_right by lra. lra.
Qed.

(* The same pair IS within one bit of slack: -2^106 = (-1) * 2^106 and
   |2^106| < 2^107.  A fact about this witness only. *)
Lemma witness_overlap_within_1 : overlap_within_b64 1 bneg2p106 b2p106.
Proof.
  unfold overlap_within_b64, overlap_within, bneg2p106, b2p106.
  rewrite !pow2_mantissa_R. cbv iota.
  pose proof (bpow_gt_0 radix2 (52 + 54)) as Hp.
  left. exists (-1)%Z, (52 + 54)%Z. split.
  - reflexivity.
  - rewrite Rabs_right by lra.
    apply Rlt_le_trans with (bpow radix2 (52 + 54 + 1)); [ | right; reflexivity ].
    rewrite Rmult_1_l. apply bpow_lt. lia.
Qed.

(* --------------------------------------------------------------------------
   Headlines.
   -------------------------------------------------------------------------- *)

Theorem fes_witness_not_nonoverlapping :
  ~ nonoverlapping_chain (compress (fast_expansion_sum fes_input fes_input)).
Proof.
  rewrite fes_witness, compress_witness.
  simpl. intros [_ [H _]]. exact (bneg2p106_b2p106_overlap H).
Qed.

Theorem fes_witness_not_priest :
  ~ priest_chain (compress (fast_expansion_sum fes_input fes_input)).
Proof.
  intro H. apply fes_witness_not_nonoverlapping.
  apply priest_chain_nonoverlapping_chain. exact H.
Qed.

(* QEX, strong form: Priest-valid inputs need not even give a
   Shewchuk-nonoverlapping output. *)
Theorem fes_priest_to_nonoverlapping_false :
  ~ (forall e f : b64_expansion,
        priest_chain e -> priest_chain f ->
        nonoverlapping_chain (compress (fast_expansion_sum e f))).
Proof.
  intro H. apply fes_witness_not_nonoverlapping.
  apply H; exact fes_input_priest.
Qed.

(* QEX: Priest's gap condition is not carried from input to output.  Not
   Priest's own claim (he renormalizes); his one-digit bound stays open. *)
Theorem fes_priest_gap_preservation_false :
  ~ (forall e f : b64_expansion,
        priest_chain e -> priest_chain f ->
        priest_chain (compress (fast_expansion_sum e f))).
Proof.
  intro H. apply fes_witness_not_priest.
  apply H; exact fes_input_priest.
Qed.

(* --------------------------------------------------------------------------
   Assumption audit.
   -------------------------------------------------------------------------- *)

Print Assumptions fes_input_priest.
Print Assumptions sort_witness.
Print Assumptions fes_witness.
Print Assumptions compress_witness.
Print Assumptions pow2_mantissa_R.
Print Assumptions bneg2p106_b2p106_overlap.
Print Assumptions witness_overlap_within_1.
Print Assumptions fes_witness_not_nonoverlapping.
Print Assumptions fes_witness_not_priest.
Print Assumptions fes_priest_to_nonoverlapping_false.
Print Assumptions fes_priest_gap_preservation_false.
