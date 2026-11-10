(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_NonoverlapSign
   ----------------------------------------------------------------------------
   Sign of a nonoverlapping expansion.  The sign of the sum equals the sign of
   the leading (most significant) component, provided the components are in
   descending order of magnitude.  This is the step from `nonoverlapping_chain`
   to a sign test.

   THE ORDER HYPOTHESIS IS NECESSARY (QEX, proved below).
   `nonoverlapping_chain` (B64_Overlap_Hierarchy.v) only links adjacent
   components, and `nonoverlapping_R` is symmetric, so the chain does not
   order components by magnitude.  Without an order the sign claim is false:

     [-4; 1; 8]   is a nonoverlapping chain (-4 = -1*2^2 with |1| < 2^2, and
                  8 = 1*2^3 with |1| < 2^3).  The leading component is
                  negative; the sum is +5.        (nonoverlap_sign_unordered_qex)
     [8; 1; -4; 1; -4; 1; -4]
                  is a nonoverlapping chain.  The largest component, 8, is
                  positive; the sum is -1.        (nonoverlap_sign_largest_qex)

   So neither the leading nor the largest component decides the sign of a
   bare `nonoverlapping_chain`.  The missing hypothesis is DESCENDING
   MAGNITUDE (`mag_desc`: |e_(i+1)| <= |e_i|), the corpus's largest-first
   convention.  It is not assumed for the Stage D use: carry_clean's output on
   Priest input has strictly decreasing magnitudes by the block pattern already
   proved in B64_CarryCleanTarget.v (see B64_CarryCleanSign.v).

   THE DOMINATION ARGUMENT (real core, `nonoverlap_tail_bound_R`).
   For a chain in descending order, either the tail sums to zero in absolute
   value, or the head is r*2^s with sum |tail| < 2^s.  Induction from the
   back: if y = r'*2^s' heads the tail with sum |rest| < 2^s', and
   |y| < 2^s (the link x -> y; the other branch of `nonoverlapping_R` is
   ruled out by |y| <= |x|), then s' < s and y, a multiple of 2^s' below 2^s,
   has |y| <= 2^s - 2^s'; so |y| + sum |rest| < 2^s.  A nonzero head has
   |x| >= 2^s, so it strictly dominates the tail and no cancellation can flip
   its sign.

   ZEROS are handled by the order, not excluded: in descending order a zero
   component is followed only by zeros, so an all-zero (or empty) expansion
   has sum 0 and sign ExpZero (`mag_desc_zero_head`), and otherwise the
   head is the most significant nonzero component.

   The core is stated over real lists (`chain_R`, `desc_R`); no binary64
   fact is used.  The binary64 form transports along `map B2R`.

   topic: binary64
   claimId: nonoverlap-chain-sign
   witness: nonoverlapping_chain_sign_correct

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human-reviewed (2026-11-10, J. Bloemscheer, PR #1017 @ 16a1b47).
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lia Lra List.
From Flocq Require Import IEEE754.Binary Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_Expansion
     B64_Overlap_Hierarchy.

Import ListNotations.
Local Open Scope R_scope.

(* ==========================================================================
   Real core.
   ========================================================================== *)

Fixpoint chain_R (l : list R) : Prop :=
  match l with
  | nil => True
  | _ :: nil => True
  | a :: (b :: _) as rest => nonoverlapping_R a b /\ chain_R rest
  end.

Fixpoint desc_R (l : list R) : Prop :=
  match l with
  | nil => True
  | _ :: nil => True
  | a :: (b :: _) as rest => Rabs b <= Rabs a /\ desc_R rest
  end.

Fixpoint sum_list_R (l : list R) : R :=
  match l with nil => 0 | x :: xs => x + sum_list_R xs end.

Fixpoint abs_sum_list_R (l : list R) : R :=
  match l with nil => 0 | x :: xs => Rabs x + abs_sum_list_R xs end.

Lemma abs_sum_list_R_nonneg : forall l, 0 <= abs_sum_list_R l.
Proof.
  induction l as [| x l IH]; cbn [abs_sum_list_R]; [ lra | ].
  pose proof (Rabs_pos x). lra.
Qed.

Lemma sum_list_R_abs_le : forall l, Rabs (sum_list_R l) <= abs_sum_list_R l.
Proof.
  induction l as [| x l IH]; cbn [sum_list_R abs_sum_list_R].
  - rewrite Rabs_R0. lra.
  - eapply Rle_trans; [ apply Rabs_triang | lra ].
Qed.

(* In descending order a zero head forces an all-zero list. *)
Lemma desc_R_zero_head :
  forall l x, desc_R (x :: l) -> x = 0 -> abs_sum_list_R (x :: l) = 0.
Proof.
  induction l as [| y l IH]; intros x Hd Hx.
  - cbn [abs_sum_list_R]. rewrite Hx, Rabs_R0. lra.
  - cbn [desc_R] in Hd. destruct Hd as [Hyx Hd].
    rewrite Hx, Rabs_R0 in Hyx.
    assert (Hy : y = 0).
    { pose proof (Rabs_pos y). apply Rabs_eq_R0. lra. }
    specialize (IH y Hd Hy). cbn [abs_sum_list_R] in IH |- *.
    rewrite Hx, Rabs_R0. lra.
Qed.

(* A nonzero multiple of 2^s is at least 2^s in magnitude. *)
Lemma pow2_multiple_ge :
  forall (r s : Z) (x : R),
    x = IZR r * bpow radix2 s -> x <> 0 -> bpow radix2 s <= Rabs x.
Proof.
  intros r s x Hx Hnz.
  assert (Hr : r <> 0%Z) by (intro E; subst r; apply Hnz; rewrite Hx; ring).
  rewrite Hx, Rabs_mult, (Rabs_pos_eq (bpow radix2 s)) by (left; apply bpow_gt_0).
  rewrite <- abs_IZR.
  assert (H1 : 1 <= IZR (Z.abs r)) by (apply IZR_le; lia).
  pose proof (bpow_gt_0 radix2 s). nra.
Qed.

(* A multiple of 2^s' strictly below 2^s (s' <= s) is at most 2^s - 2^s'. *)
Lemma pow2_multiple_below :
  forall (r s s' : Z) (y : R),
    y = IZR r * bpow radix2 s' -> (s' <= s)%Z -> Rabs y < bpow radix2 s ->
    Rabs y <= bpow radix2 s - bpow radix2 s'.
Proof.
  intros r s s' y Hy Hss Hlt.
  assert (Hp' : 0 < bpow radix2 s') by apply bpow_gt_0.
  assert (Hsplit : bpow radix2 s = IZR (Zpower radix2 (s - s')) * bpow radix2 s').
  { rewrite IZR_Zpower by lia. rewrite <- bpow_plus. f_equal. ring. }
  assert (Habs : Rabs y = IZR (Z.abs r) * bpow radix2 s').
  { rewrite Hy, Rabs_mult, (Rabs_pos_eq (bpow radix2 s')) by lra.
    rewrite abs_IZR. reflexivity. }
  rewrite Habs, Hsplit in Hlt |- *.
  assert (Hz : (Z.abs r < Zpower radix2 (s - s'))%Z).
  { apply lt_IZR. apply Rmult_lt_reg_r with (bpow radix2 s'); assumption. }
  assert (Hz' : IZR (Z.abs r) <= IZR (Zpower radix2 (s - s')) - 1).
  { rewrite <- minus_IZR. apply IZR_le. lia. }
  nra.
Qed.

(* THE DOMINATION INVARIANT.  For a descending nonoverlapping chain x :: rest,
   either the tail is identically zero, or x = r * 2^s with sum |rest| < 2^s. *)
Lemma nonoverlap_tail_bound_R :
  forall rest x,
    chain_R (x :: rest) -> desc_R (x :: rest) ->
    abs_sum_list_R rest = 0
    \/ exists r s : Z, x = IZR r * bpow radix2 s
                      /\ abs_sum_list_R rest < bpow radix2 s.
Proof.
  induction rest as [| y rest IH]; intros x Hc Hd.
  - left. reflexivity.
  - cbn [chain_R] in Hc. destruct Hc as [Hxy Hc].
    cbn [desc_R] in Hd. destruct Hd as [Hyx Hd].
    destruct (Req_dec y 0) as [Hy0 | Hy0].
    { left. exact (desc_R_zero_head rest y Hd Hy0). }
    (* y <> 0: the link x -> y is the first branch of nonoverlapping_R. *)
    destruct Hxy as [(r & s & Hx & Hylt) | (r & s & Hy & Hxlt)];
      rewrite Z.add_0_r in *.
    2: { exfalso. pose proof (pow2_multiple_ge r s y Hy Hy0). lra. }
    right. exists r, s. split; [ exact Hx | ].
    cbn [abs_sum_list_R].
    destruct (IH y Hc Hd) as [Hz | (r' & s' & Hy' & Hrest)].
    + rewrite Hz. lra.
    + assert (Hge : bpow radix2 s' <= Rabs y) by exact (pow2_multiple_ge r' s' y Hy' Hy0).
      assert (Hss : (s' <= s)%Z).
      { destruct (Z_le_gt_dec s' s) as [H | H]; [ exact H | ].
        exfalso. assert (bpow radix2 s < bpow radix2 s') by (apply bpow_lt; lia). lra. }
      pose proof (pow2_multiple_below r' s s' y Hy' Hss Hylt). lra.
Qed.

(* A nonzero head strictly dominates the whole tail. *)
Theorem nonoverlap_head_dominates_R :
  forall rest x,
    chain_R (x :: rest) -> desc_R (x :: rest) -> x <> 0 ->
    abs_sum_list_R rest < Rabs x.
Proof.
  intros rest x Hc Hd Hx.
  destruct (nonoverlap_tail_bound_R rest x Hc Hd) as [Hz | (r & s & Hxr & Hlt)].
  - rewrite Hz. apply Rabs_pos_lt. exact Hx.
  - pose proof (pow2_multiple_ge r s x Hxr Hx). lra.
Qed.

(* Sign of the sum = sign of the head (real form). *)
Theorem nonoverlap_sign_R :
  forall rest x,
    chain_R (x :: rest) -> desc_R (x :: rest) ->
    (0 < x -> 0 < sum_list_R (x :: rest)) /\
    (x < 0 -> sum_list_R (x :: rest) < 0) /\
    (x = 0 -> sum_list_R (x :: rest) = 0).
Proof.
  intros rest x Hc Hd.
  pose proof (sum_list_R_abs_le rest) as Hsr.
  cbn [sum_list_R]. split; [ | split ].
  - intro Hp.
    pose proof (nonoverlap_head_dominates_R rest x Hc Hd (Rgt_not_eq _ _ Hp)) as H.
    rewrite Rabs_pos_eq in H by lra.
    pose proof (Rle_abs (- sum_list_R rest)) as Ha. rewrite Rabs_Ropp in Ha. lra.
  - intro Hn.
    pose proof (nonoverlap_head_dominates_R rest x Hc Hd (Rlt_not_eq _ _ Hn)) as H.
    rewrite Rabs_left in H by lra.
    pose proof (Rle_abs (sum_list_R rest)) as Ha. lra.
  - intro Hz. pose proof (desc_R_zero_head rest x Hd Hz) as H0.
    cbn [abs_sum_list_R] in H0. rewrite Hz, Rabs_R0 in H0.
    rewrite Hz. pose proof (Rabs_pos (sum_list_R rest)) as Hp0.
    assert (Hr0 : Rabs (sum_list_R rest) = 0) by lra.
    apply Rabs_eq_R0 in Hr0. lra.
Qed.

(* --------------------------------------------------------------------------
   QEX: the order hypothesis cannot be dropped.
   -------------------------------------------------------------------------- *)

Lemma nonoverlapping_R_link_down :
  forall (r s : Z) (x y : R),
    x = IZR r * bpow radix2 s -> Rabs y < bpow radix2 s -> nonoverlapping_R x y.
Proof. intros r s x y Hx Hy. left. exists r, s. split; [ exact Hx | ]. rewrite Z.add_0_r. exact Hy. Qed.

Lemma nonoverlapping_R_link_up :
  forall (r s : Z) (x y : R),
    y = IZR r * bpow radix2 s -> Rabs x < bpow radix2 s -> nonoverlapping_R x y.
Proof. intros r s x y Hy Hx. right. exists r, s. split; [ exact Hy | ]. rewrite Z.add_0_r. exact Hx. Qed.

Lemma bpow2_R : bpow radix2 2 = 4.
Proof. reflexivity. Qed.
Lemma bpow3_R : bpow radix2 3 = 8.
Proof. reflexivity. Qed.

(* [-4; 1; 8]: a nonoverlapping chain, negative head, positive sum. *)
Theorem nonoverlap_sign_unordered_qex :
  chain_R [-4; 1; 8] /\ -4 < 0 /\ 0 < sum_list_R [-4; 1; 8]
  /\ ~ desc_R [-4; 1; 8].
Proof.
  split; [ | split; [ lra | split ] ].
  - cbn [chain_R]. split; [ | split; [ | exact I ] ].
    + apply (nonoverlapping_R_link_down (-1) 2); [ rewrite bpow2_R; cbn; lra | ].
      rewrite bpow2_R, Rabs_pos_eq by lra. lra.
    + apply (nonoverlapping_R_link_up 1 3); [ rewrite bpow3_R; cbn; lra | ].
      rewrite bpow3_R, Rabs_pos_eq by lra. lra.
  - cbn [sum_list_R]. lra.
  - cbn [desc_R]. intros [_ [H _]].
    rewrite (Rabs_pos_eq 8), (Rabs_pos_eq 1) in H by lra. lra.
Qed.

(* [8; 1; -4; 1; -4; 1; -4]: a nonoverlapping chain whose LARGEST component is
   positive and whose sum is negative. *)
Theorem nonoverlap_sign_largest_qex :
  chain_R [8; 1; -4; 1; -4; 1; -4]
  /\ Forall (fun y => Rabs y <= 8) [8; 1; -4; 1; -4; 1; -4]
  /\ sum_list_R [8; 1; -4; 1; -4; 1; -4] < 0.
Proof.
  assert (L81 : nonoverlapping_R 8 1).
  { apply (nonoverlapping_R_link_down 1 3); [ rewrite bpow3_R; cbn; lra | ].
    rewrite bpow3_R, Rabs_pos_eq by lra. lra. }
  assert (L14 : nonoverlapping_R 1 (-4)).
  { apply (nonoverlapping_R_link_up (-1) 2); [ rewrite bpow2_R; cbn; lra | ].
    rewrite bpow2_R, Rabs_pos_eq by lra. lra. }
  assert (L41 : nonoverlapping_R (-4) 1).
  { apply (nonoverlapping_R_link_down (-1) 2); [ rewrite bpow2_R; cbn; lra | ].
    rewrite bpow2_R, Rabs_pos_eq by lra. lra. }
  split; [ | split ].
  - cbn [chain_R]. repeat split; assumption.
  - assert (A1 : Rabs 1 <= 8) by (rewrite Rabs_pos_eq; lra).
    assert (A4 : Rabs (-4) <= 8) by (rewrite Rabs_left; lra).
    assert (A8 : Rabs 8 <= 8) by (rewrite Rabs_pos_eq; lra).
    repeat (apply Forall_cons; [ cbv beta; assumption | ]). apply Forall_nil.
  - cbn [sum_list_R]. lra.
Qed.

(* ==========================================================================
   binary64 form.
   ========================================================================== *)

Local Abbreviation b2r := (Binary.B2R prec emax).

Fixpoint mag_desc (e : b64_expansion) : Prop :=
  match e with
  | nil => True
  | _ :: nil => True
  | a :: (b :: _) as rest => Rabs (b2r b) <= Rabs (b2r a) /\ mag_desc rest
  end.

Lemma nonoverlapping_chain_R_map :
  forall e, nonoverlapping_chain e -> chain_R (map b2r e).
Proof.
  induction e as [| a e IH]; intro H; [ exact I | ].
  destruct e as [| b e']; [ exact I | ].
  destruct H as [H1 H2]. split; [ exact H1 | exact (IH H2) ].
Qed.

Lemma mag_desc_R_map : forall e, mag_desc e -> desc_R (map b2r e).
Proof.
  induction e as [| a e IH]; intro H; [ exact I | ].
  destruct e as [| b e']; [ exact I | ].
  destruct H as [H1 H2]. split; [ exact H1 | exact (IH H2) ].
Qed.

Lemma expansion_R_map : forall e, expansion_R e = sum_list_R (map b2r e).
Proof. induction e as [| a e IH]; [ reflexivity | cbn [expansion_R map sum_list_R]; rewrite IH; reflexivity ]. Qed.

(* All-zero case, separately: a zero head in descending order means the
   whole expansion is zero, its sum is 0 and its sign is ExpZero. *)
Theorem mag_desc_zero_head :
  forall e x, mag_desc (x :: e) -> b2r x = 0 ->
    expansion_R (x :: e) = 0 /\ sign_of_expansion (x :: e) = ExpZero.
Proof.
  induction e as [| y e IH]; intros x Hd Hx.
  - cbn [expansion_R sign_of_expansion]. rewrite Hx, Rcompare_Eq by reflexivity.
    split; [ ring | reflexivity ].
  - destruct Hd as [Hyx Hd]. rewrite Hx, Rabs_R0 in Hyx.
    assert (Hy : b2r y = 0) by (pose proof (Rabs_pos (b2r y)); apply Rabs_eq_R0; lra).
    destruct (IH y Hd Hy) as [Hs Hsg].
    split.
    + cbn [expansion_R] in Hs |- *. rewrite Hx. lra.
    + cbn [sign_of_expansion]. rewrite Hx, Rcompare_Eq by reflexivity.
      exact Hsg.
Qed.

(* HEADLINE: sign of a descending nonoverlapping expansion.  sign_of_expansion
   reads the leading nonzero component; under mag_desc that is the most
   significant one, and it decides the sign of the exact sum. *)
Theorem nonoverlapping_chain_sign_correct :
  forall e : b64_expansion,
    nonoverlapping_chain e -> mag_desc e ->
    match sign_of_expansion e with
    | ExpPos  => 0 < expansion_R e
    | ExpNeg  => expansion_R e < 0
    | ExpZero => expansion_R e = 0
    end.
Proof.
  intros [| x rest] Hc Hd; [ reflexivity | ].
  pose proof (nonoverlapping_chain_R_map _ Hc) as HcR.
  pose proof (mag_desc_R_map _ Hd) as HdR.
  cbn [map] in HcR, HdR.
  destruct (nonoverlap_sign_R (map b2r rest) (b2r x) HcR HdR) as (Hp & Hn & _).
  cbn [sign_of_expansion].
  destruct (Rcompare_spec (b2r x) 0) as [Hlt | Heq | Hgt].
  - rewrite expansion_R_map. exact (Hn Hlt).
  - destruct (mag_desc_zero_head rest x Hd Heq) as [Hs Hsg].
    cbn [sign_of_expansion] in Hsg. rewrite Heq, Rcompare_Eq in Hsg by reflexivity.
    rewrite Hsg. exact Hs.
  - rewrite expansion_R_map. exact (Hp Hgt).
Qed.

(* The same sign is that of the head: a nonzero head dominates the tail. *)
Corollary nonoverlapping_chain_head_dominates :
  forall x rest,
    nonoverlapping_chain (x :: rest) -> mag_desc (x :: rest) -> b2r x <> 0 ->
    Rabs (expansion_R rest) < Rabs (b2r x).
Proof.
  intros x rest Hc Hd Hx.
  pose proof (nonoverlapping_chain_R_map _ Hc) as HcR.
  pose proof (mag_desc_R_map _ Hd) as HdR. cbn [map] in HcR, HdR.
  pose proof (nonoverlap_head_dominates_R (map b2r rest) (b2r x) HcR HdR Hx).
  rewrite expansion_R_map. eapply Rle_lt_trans; [ apply sum_list_R_abs_le | exact H ].
Qed.

(* binary64 QEX: [-4; 1; 8] as doubles is a nonoverlapping_chain on which
   sign_of_expansion is wrong.  So the order hypothesis is needed in the
   binary64 statement too. *)
Definition qex_m4 : binary64 := Binary.B754_finite prec emax true  4503599627370496 (-50) eq_refl.
Definition qex_1  : binary64 := Binary.B754_finite prec emax false 4503599627370496 (-52) eq_refl.
Definition qex_8  : binary64 := Binary.B754_finite prec emax false 4503599627370496 (-49) eq_refl.

Lemma qex_mant : IZR (Zpos 4503599627370496) = bpow radix2 52.
Proof. rewrite <- IZR_Zpower by lia. reflexivity. Qed.

Lemma qex_m4_R : b2r qex_m4 = -4.
Proof.
  unfold qex_m4. cbn [Binary.B2R]. unfold F2R. cbn [Fnum Fexp cond_Zopp].
  change (Zneg 4503599627370496) with (- Zpos 4503599627370496)%Z.
  rewrite opp_IZR, qex_mant, Ropp_mult_distr_l_reverse, <- bpow_plus.
  reflexivity.
Qed.

Lemma qex_1_R : b2r qex_1 = 1.
Proof.
  unfold qex_1. cbn [Binary.B2R]. unfold F2R. cbn [Fnum Fexp cond_Zopp].
  rewrite qex_mant, <- bpow_plus. reflexivity.
Qed.

Lemma qex_8_R : b2r qex_8 = 8.
Proof.
  unfold qex_8. cbn [Binary.B2R]. unfold F2R. cbn [Fnum Fexp cond_Zopp].
  rewrite qex_mant, <- bpow_plus. reflexivity.
Qed.

Theorem nonoverlapping_chain_sign_unordered_false :
  ~ (forall e : b64_expansion,
       nonoverlapping_chain e ->
       match sign_of_expansion e with
       | ExpPos  => 0 < expansion_R e
       | ExpNeg  => expansion_R e < 0
       | ExpZero => expansion_R e = 0
       end).
Proof.
  intro H. specialize (H [qex_m4; qex_1; qex_8]).
  assert (Hc : nonoverlapping_chain [qex_m4; qex_1; qex_8]).
  { cbn [nonoverlapping_chain]. unfold nonoverlapping_b64.
    rewrite qex_m4_R, qex_1_R, qex_8_R.
    destruct nonoverlap_sign_unordered_qex as [Hc _]. cbn [chain_R] in Hc. exact Hc. }
  specialize (H Hc).
  cbn [sign_of_expansion expansion_R] in H.
  rewrite qex_m4_R, qex_1_R, qex_8_R in H.
  rewrite Rcompare_Lt in H by lra. lra.
Qed.

(* --------------------------------------------------------------------------
   Assumption audit.
   -------------------------------------------------------------------------- *)

Print Assumptions nonoverlap_tail_bound_R.
Print Assumptions nonoverlap_head_dominates_R.
Print Assumptions nonoverlap_sign_R.
Print Assumptions nonoverlap_sign_unordered_qex.
Print Assumptions nonoverlap_sign_largest_qex.
Print Assumptions mag_desc_zero_head.
Print Assumptions nonoverlapping_chain_sign_correct.
Print Assumptions nonoverlapping_chain_head_dominates.
Print Assumptions nonoverlapping_chain_sign_unordered_false.
