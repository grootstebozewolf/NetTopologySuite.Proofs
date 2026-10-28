(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_Priest_FES_counterexample
   ----------------------------------------------------------------------------
   The Priest route's stop condition, met as QEX: the corpus's
   `fast_expansion_sum` does NOT preserve Priest's component condition --
   and does not even land in Shewchuk's weaker nonoverlapping relation.

   THE QUESTION (docs/thm13-priest-route.md §5).  With Priest 1991 §2's
   condition stated as `priest_nonoverlapping_b64` (B64_Overlap_Hierarchy.v):
   if both inputs are Priest expansions, is the output of
   `fast_expansion_sum` one?

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

     priest in  =/=>  priest out          (fes_priest_preservation_false)
     priest in  =/=>  nonoverlapping out  (fes_priest_to_nonoverlapping_false)

   The second is strictly stronger (priest => nonoverlapping, rung proved in
   B64_Overlap_Hierarchy.v): the corpus's algorithm, on Priest-valid input,
   falls TWO rungs of the hierarchy, not one.  This is exactly the shape
   Shewchuk describes for Priest's own merge-and-sum: without a
   renormalization pass the output components may overlap, and Priest
   renormalizes for that reason.  `fast_expansion_sum` has no
   renormalization pass.

   WHAT THIS DOES NOT SETTLE (do not overclaim).
     - Priest's ONE-DIGIT bound.  The offending pair sits inside the
       one-bit slack (`witness_overlap_within_1`), consistent with Shewchuk's
       summary that Priest's components "overlap by at most one digit".  That
       is ONE witness, not a theorem; whether `fast_expansion_sum` preserves
       `overlap_within 1` (or Priest's exact one-digit statement) under
       Priest-valid inputs is not decided here.  Randomised binary64 search
       (2e5 cases) and exhaustive p = 3 search (length <= 2, exponents in
       [-4, 4]) found no `overlap_within 1` failure; that is evidence, not
       proof.
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
   Priest's condition along an expansion, mirroring `nonoverlapping_chain`.
   A zero component has no normalised significand, so a Priest chain is
   zero-free; inputs are compared raw, outputs after `compress`.
   -------------------------------------------------------------------------- *)

Fixpoint priest_chain (e : b64_expansion) : Prop :=
  match e with
  | nil => True
  | _ :: nil => True
  | a :: (b :: _) as rest =>
      priest_nonoverlapping_b64 a b /\ priest_chain rest
  end.

Lemma priest_chain_nonoverlapping_chain :
  forall e : b64_expansion, priest_chain e -> nonoverlapping_chain e.
Proof.
  induction e as [| a e' IH]; [ simpl; trivial | ].
  destruct e' as [| b e'']; [ simpl; trivial | ].
  intros [Hp Hrest]. simpl. split.
  - apply priest_nonoverlapping_weaker. exact Hp.
  - apply IH. exact Hrest.
Qed.

(* --------------------------------------------------------------------------
   The witness.  M = 2^53 - 1 = 9007199254740991, a full 53-bit significand.
   -------------------------------------------------------------------------- *)

Definition pM (k : Z) (H : SpecFloat.bounded prec emax 9007199254740991 k = true)
  : binary64 := Binary.B754_finite prec emax false 9007199254740991 k H.

Definition wA : binary64 := pM 106 eq_refl.   (* M * 2^106 *)
Definition wB : binary64 := pM 53 eq_refl.    (* M * 2^53  *)
Definition wC : binary64 := pM 0 eq_refl.     (* M         *)

Definition w_in : list binary64 := [wA; wB; wC].

(* The output, as `vm_compute` reports it. *)
Definition o1 : binary64 :=   (*  2^160   *)
  Binary.B754_finite prec emax false 4503599627370496 108 eq_refl.
Definition o2 : binary64 :=   (* -2^106   *)
  Binary.B754_finite prec emax true  4503599627370496 54 eq_refl.
Definition o3 : binary64 :=   (*  2^106   *)
  Binary.B754_finite prec emax false 4503599627370496 54 eq_refl.
Definition o4 : binary64 :=   (* -2^53    *)
  Binary.B754_finite prec emax true  4503599627370496 1 eq_refl.
Definition o5 : binary64 :=   (*  2^53-2  *)
  Binary.B754_finite prec emax false 9007199254740990 0 eq_refl.
Definition o6 : binary64 := Binary.B754_zero prec emax false.

(* --------------------------------------------------------------------------
   Concrete magnitudes.
   -------------------------------------------------------------------------- *)

Lemma IZR_M_pos : 0 < IZR 9007199254740991.
Proof. apply IZR_lt. lia. Qed.

Lemma pM_R : forall k H, Binary.B2R prec emax (pM k H)
                         = IZR 9007199254740991 * bpow radix2 k.
Proof. intros k H. reflexivity. Qed.

Lemma pM_abs : forall k H, Rabs (Binary.B2R prec emax (pM k H))
                           = IZR 9007199254740991 * bpow radix2 k.
Proof.
  intros k H. rewrite pM_R. apply Rabs_pos_eq.
  pose proof IZR_M_pos. pose proof (bpow_gt_0 radix2 k). nra.
Qed.

Lemma abs_C_lt_B :
  Rabs (Binary.B2R prec emax wC) < Rabs (Binary.B2R prec emax wB).
Proof.
  unfold wB, wC. rewrite !pM_abs. pose proof IZR_M_pos.
  apply Rmult_lt_compat_l; [ lra | apply bpow_lt; lia ].
Qed.

Lemma abs_B_lt_A :
  Rabs (Binary.B2R prec emax wB) < Rabs (Binary.B2R prec emax wA).
Proof.
  unfold wA, wB. rewrite !pM_abs. pose proof IZR_M_pos.
  apply Rmult_lt_compat_l; [ lra | apply bpow_lt; lia ].
Qed.

(* --------------------------------------------------------------------------
   The inputs are Priest expansions: gap 53 = prec at each link.
   -------------------------------------------------------------------------- *)

Lemma mantissa_M_normalised :
  bpow radix2 (prec - 1) <= Rabs (IZR 9007199254740991) < bpow radix2 prec.
Proof.
  rewrite Rabs_pos_eq by (left; exact IZR_M_pos).
  unfold prec. rewrite <- !IZR_Zpower by lia.
  split; [ apply IZR_le | apply IZR_lt ]; vm_compute; congruence.
Qed.

Lemma priest_pM :
  forall kx ky Hx Hy, (kx - ky >= prec)%Z ->
    priest_nonoverlapping_b64 (pM kx Hx) (pM ky Hy).
Proof.
  intros kx ky Hx Hy Hgap.
  exists 9007199254740991%Z, 9007199254740991%Z, kx, ky.
  repeat split; try (apply pM_R); try apply mantissa_M_normalised; exact Hgap.
Qed.

Lemma w_in_priest : priest_chain w_in.
Proof.
  unfold w_in, wA, wB, wC. simpl.
  repeat split; try apply priest_pM; unfold prec; lia.
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

Lemma sort_witness : sort_by_abs (w_in ++ w_in) = [wC; wC; wB; wB; wA; wA].
Proof.
  pose proof abs_C_lt_B as HCB.
  pose proof abs_B_lt_A as HBA.
  unfold w_in. cbn [app sort_by_abs].
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
  fast_expansion_sum w_in w_in = [o1; o2; o3; o4; o5; o6].
Proof.
  apply map_B2FF_inj.
  unfold fast_expansion_sum. rewrite sort_witness.
  vm_compute. reflexivity.
Qed.

Lemma compress_witness :
  compress [o1; o2; o3; o4; o5; o6] = [o1; o2; o3; o4; o5].
Proof.
  cbn [compress].
  assert (Hpos : forall s m e H,
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
  unfold o1, o2, o3, o4, o5, o6. rewrite !Hpos.
  cbn [Binary.B2R]. rewrite Rcompare_Eq by reflexivity.
  reflexivity.
Qed.

(* --------------------------------------------------------------------------
   The offending pair: -2^106 followed by 2^106.
   -------------------------------------------------------------------------- *)

Lemma o2_R : Binary.B2R prec emax o2 = - bpow radix2 106.
Proof.
  unfold o2. cbn [Binary.B2R]. unfold F2R; cbn [Fnum Fexp].
  change (cond_Zopp true (Z.pos 4503599627370496))
    with (- Z.pos 4503599627370496)%Z.
  rewrite opp_IZR, IZR_mant_bpow, Ropp_mult_distr_l_reverse, <- bpow_plus.
  reflexivity.
Qed.

Lemma o3_R : Binary.B2R prec emax o3 = bpow radix2 106.
Proof.
  unfold o3. cbn [Binary.B2R]. unfold F2R; cbn [Fnum Fexp].
  change (cond_Zopp false (Z.pos 4503599627370496))
    with (Z.pos 4503599627370496).
  rewrite IZR_mant_bpow, <- bpow_plus. reflexivity.
Qed.

(* Two nonzero reals of equal magnitude never satisfy Shewchuk's relation:
   x = r 2^s with |y| = |x| < 2^s forces 0 < |r| < 1. *)
Lemma equal_magnitude_overlaps :
  forall x y : R, x <> 0 -> Rabs x = Rabs y -> ~ nonoverlapping_R x y.
Proof.
  assert (Hcore : forall x y r s,
             x <> 0 -> Rabs x = Rabs y ->
             x = IZR r * bpow radix2 s -> Rabs y < bpow radix2 s -> False).
  { intros x y r s Hx0 Habs Hx Hy.
    pose proof (bpow_gt_0 radix2 s) as Hs.
    rewrite <- Habs, Hx, Rabs_mult, (Rabs_pos_eq (bpow radix2 s)) in Hy
      by lra.
    rewrite <- abs_IZR in Hy.
    assert (Hlt1 : IZR (Z.abs r) < 1) by nra.
    apply lt_IZR in Hlt1.
    assert (r = 0%Z) by lia. subst r.
    apply Hx0. rewrite Hx. simpl. lra. }
  intros x y Hx0 Habs.
  unfold nonoverlapping_R, overlap_within.
  intros [ [r [s [Hx Hy]]] | [r [s [Hy Hx]]] ];
    rewrite Z.add_0_r in *.
  - exact (Hcore x y r s Hx0 Habs Hx Hy).
  - apply (Hcore y x r s); [ | symmetry; exact Habs | exact Hy | exact Hx ].
    intro Hy0. pose proof (Rabs_pos_lt x Hx0) as Hp.
    rewrite Habs, Hy0, Rabs_R0 in Hp. lra.
Qed.

Lemma o2_o3_overlap : ~ nonoverlapping_b64 o2 o3.
Proof.
  unfold nonoverlapping_b64. rewrite o2_R, o3_R.
  apply equal_magnitude_overlaps.
  - pose proof (bpow_gt_0 radix2 106). lra.
  - rewrite Rabs_Ropp. reflexivity.
Qed.

(* The same pair IS within one bit of slack: -2^106 = (-1) * 2^106 and
   |2^106| < 2^107.  A fact about this witness only. *)
Lemma witness_overlap_within_1 : overlap_within_b64 1 o2 o3.
Proof.
  unfold overlap_within_b64, overlap_within. rewrite o2_R, o3_R.
  left. exists (-1)%Z, 106%Z. split.
  - simpl. lra.
  - rewrite Rabs_pos_eq by (left; apply bpow_gt_0). apply bpow_lt. lia.
Qed.

(* --------------------------------------------------------------------------
   Headlines.
   -------------------------------------------------------------------------- *)

Theorem fes_witness_not_nonoverlapping :
  ~ nonoverlapping_chain (compress (fast_expansion_sum w_in w_in)).
Proof.
  rewrite fes_witness, compress_witness.
  simpl. intros [_ [H _]]. exact (o2_o3_overlap H).
Qed.

Theorem fes_witness_not_priest :
  ~ priest_chain (compress (fast_expansion_sum w_in w_in)).
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
  apply H; exact w_in_priest.
Qed.

(* QEX, the Priest route's stop condition: Priest's condition is not
   preserved by the corpus's `fast_expansion_sum`. *)
Theorem fes_priest_preservation_false :
  ~ (forall e f : b64_expansion,
        priest_chain e -> priest_chain f ->
        priest_chain (compress (fast_expansion_sum e f))).
Proof.
  intro H. apply fes_witness_not_priest.
  apply H; exact w_in_priest.
Qed.

(* --------------------------------------------------------------------------
   Assumption audit.
   -------------------------------------------------------------------------- *)

Print Assumptions priest_chain_nonoverlapping_chain.
Print Assumptions w_in_priest.
Print Assumptions sort_witness.
Print Assumptions fes_witness.
Print Assumptions compress_witness.
Print Assumptions equal_magnitude_overlaps.
Print Assumptions o2_o3_overlap.
Print Assumptions witness_overlap_within_1.
Print Assumptions fes_witness_not_nonoverlapping.
Print Assumptions fes_witness_not_priest.
Print Assumptions fes_priest_to_nonoverlapping_false.
Print Assumptions fes_priest_preservation_false.
