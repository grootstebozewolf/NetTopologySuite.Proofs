(* AlpogeBrestDivin.v -- NACK hunt on bRest_all and divinN_of_hypV.

   bRest_all
     FinalAll.lean:13-46, called from LinkBrest.lean:24 at Cabs = 2.
     Conclusion: Closed (D3 3 A) (fun Fm CH => forall hc, TuSize ->
     DGamSize -> RemainingDivisionBounds Fm Cabs CH), with fields
     hh, bu, rr, la (IndefiniteRealisationChoice.lean:158-163).
   divinN_of_hypV
     DivinNOfHypV.lean:117-130.  The constant is |C|+1 from LinkN's
     own C.  The threshold is the max of the four tails and x1+1,
     inside the existential.

   Mirror CocoSgt/riemann-hypothesis-lean @ 7cbf7a0, read from source.
   Within docs/axiom-allowlist.txt.  No Admitted.  Not a proof of RH.
   Verdict on the external development: PASS-STATIC / PENDING.

   Evidence for docs/attacks/2026-11-22-alpoge-brest-divinn.md.
   NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Cursor Grok 4.7
*)
From Stdlib Require Import Reals Lra Lia Psatz.
From NTS.Proofs Require Import ExpSeriesClean LogRpowClean.
Local Open Scope R_scope.

(* ===================================================================== *)
(* divinN_of_hypV: the algebraic bound and the max of the tails           *)
(* DivinNOfHypV.lean:79-115 and :117-130.                                 *)
(* ===================================================================== *)

(* b <= f * m * b * y once 1 <= f, 1 <= m, 1 <= y and 0 <= b.
   This is hbB in divinN_at (line 100-103), with B0 = f * m * b * y. *)
Theorem scale_le_product : forall f m b y,
  0 <= b -> 1 <= f -> 1 <= m -> 1 <= y -> b <= f * m * b * y.
Proof.
  intros f m b y Hb Hf Hm Hy.
  assert (Hfm : 1 <= f * m).
  { replace 1 with (1 * 1) by ring.
    apply Rmult_le_compat; lra. }
  assert (Hfmy : 1 <= f * m * y).
  { replace 1 with (1 * 1) by ring.
    apply Rmult_le_compat; lra. }
  replace b with (b * 1) at 1 by ring.
  replace (f * m * b * y) with (b * (f * m * y)) by ring.
  apply Rmult_le_compat_l; assumption.
Qed.

(* y = 1/2 fails the same comparison.  The 1 <= y guard is load-bearing. *)
Theorem scale_le_product_needs_y :
  ~ (1 <= 1 * 1 * 1 * (1 / 2)).
Proof. lra. Qed.

(* C * (y*B0 + log2*Nc) <= (|C|+1) * y * (B0+Nc), the divinN_at calc
   (lines 105-115).  log2 is the square Real.log^2, hence nonnegative. *)
Theorem divin_abs_bound : forall C y B0 Nc log2,
  0 <= y -> 0 <= B0 -> 0 <= Nc -> 0 <= log2 -> log2 <= y ->
  C * (y * B0 + log2 * Nc) <= (Rabs C + 1) * y * (B0 + Nc).
Proof.
  intros C y B0 Nc log2 Hy HB Hn Hl HyL.
  assert (Hsum : 0 <= y * B0 + log2 * Nc).
  { apply Rplus_le_le_0_compat; apply Rmult_le_pos; assumption. }
  assert (Hnq : log2 * Nc <= y * Nc).
  { apply Rmult_le_compat_r; assumption. }
  assert (Hle : y * B0 + log2 * Nc <= y * (B0 + Nc)).
  { replace (y * (B0 + Nc)) with (y * B0 + y * Nc) by ring.
    apply Rplus_le_compat_l. exact Hnq. }
  assert (Habs : C * (y * B0 + log2 * Nc) <= Rabs C * (y * B0 + log2 * Nc)).
  { apply Rmult_le_compat_r; [exact Hsum|apply Rle_abs]. }
  assert (Habs2 : Rabs C * (y * B0 + log2 * Nc) <= Rabs C * (y * (B0 + Nc))).
  { apply Rmult_le_compat_l; [apply Rabs_pos|exact Hle]. }
  assert (Hone : Rabs C * (y * (B0 + Nc)) <= (Rabs C + 1) * (y * (B0 + Nc))).
  { replace ((Rabs C + 1) * (y * (B0 + Nc)))
      with (Rabs C * (y * (B0 + Nc)) + 1 * (y * (B0 + Nc))) by ring.
    apply Rle_trans with (Rabs C * (y * (B0 + Nc)) + 0).
    - rewrite Rplus_0_r. apply Rle_refl.
    - apply Rplus_le_compat_l. rewrite Rmult_1_l.
      apply Rmult_le_pos; [exact Hy|]. apply Rplus_le_le_0_compat; assumption. }
  replace ((Rabs C + 1) * y * (B0 + Nc)) with ((Rabs C + 1) * (y * (B0 + Nc))) by ring.
  apply Rle_trans with (Rabs C * (y * B0 + log2 * Nc)); [exact Habs|].
  apply Rle_trans with (Rabs C * (y * (B0 + Nc))); [exact Habs2|exact Hone].
Qed.

(* Using C in place of |C| reverses the inequality when C < 0 and the
   parenthesis is strictly smaller than y*(B0+Nc). *)
Theorem divin_abs_needs_abs :
  ~ ((-1) * (2 * 1 + 1 * 1) <= (-1) * (2 * (1 + 1))).
Proof. lra. Qed.

(* The four tails and x1+1, packed as in divinN_of_hypV line 123. *)
Theorem divin_threshold_pack : forall x1 x3 x4 x6 x1fam x,
  Rmax (Rmax x1 (Rmax x3 x4)) (Rmax x6 (x1fam + 1)) <= x ->
  x1 <= x /\ x3 <= x /\ x4 <= x /\ x6 <= x /\ x1fam + 1 <= x.
Proof.
  intros x1 x3 x4 x6 x1fam x Hx.
  assert (Ha : Rmax x1 (Rmax x3 x4) <= x).
  { apply Rle_trans with (Rmax (Rmax x1 (Rmax x3 x4)) (Rmax x6 (x1fam + 1)));
      [apply Rmax_l|exact Hx]. }
  assert (Hb : Rmax x6 (x1fam + 1) <= x).
  { apply Rle_trans with (Rmax (Rmax x1 (Rmax x3 x4)) (Rmax x6 (x1fam + 1)));
      [apply Rmax_r|exact Hx]. }
  assert (H34 : Rmax x3 x4 <= x).
  { apply Rle_trans with (Rmax x1 (Rmax x3 x4)); [apply Rmax_r|exact Ha]. }
  split; [|split; [|split; [|split]]].
  - apply Rle_trans with (Rmax x1 (Rmax x3 x4)); [apply Rmax_l|exact Ha].
  - apply Rle_trans with (Rmax x3 x4); [apply Rmax_l|exact H34].
  - apply Rle_trans with (Rmax x3 x4); [apply Rmax_r|exact H34].
  - apply Rle_trans with (Rmax x6 (x1fam + 1)); [apply Rmax_l|exact Hb].
  - apply Rle_trans with (Rmax x6 (x1fam + 1)); [apply Rmax_r|exact Hb].
Qed.

(* A threshold that only clears x1 misses a later tail. *)
Theorem divin_threshold_needs_all :
  let x1 := 0 in let x6 := 5 in
  x1 <= 1 /\ ~ (x6 <= 1).
Proof. simpl. split; lra. Qed.

(* log^2 <= x^eps is NOT true of every pair of functions.
   Lean names Real.log and Real.rpow (DivinNOfHypV.lean:59). *)
Theorem log_sq_not_for_every_fn :
  ~ (forall (lg : R -> R) (pw : R -> R -> R) (eps : R),
       0 < eps -> exists x0, forall x, x0 <= x -> lg x * lg x <= pw x eps).
Proof.
  intro H.
  destruct (H (fun _ => 0) (fun _ _ => -1) 1) as [x0 Hx]; [lra|].
  specialize (Hx x0 (Rle_refl x0)).
  lra.
Qed.

Section Divin.
Variable eps x1fam : R.
Variable Ix : R -> Type.
(* Pointwise readings.  LinkAt is LinkN_at at the C from LinkN. *)
Variable VVAt : forall x, Ix x -> Prop.
Variable LinkAt : R -> forall x, Ix x -> Prop.
Variable RankAt : forall x, Ix x -> Prop.
Variable DivAt : R -> forall x, Ix x -> nat -> Prop.
(* [QEX] Real.log and Real.rpow, DivinNOfHypV.lean:59-74.
   One pair of functions, not every pair (see log_sq_not_for_every_fn).
   The Stdlib names are not written: ln and Rpower pull classic. *)
Variable logf : R -> R.
Variable powf : R -> R -> R.
Hypothesis log_sq_le_rpow :
  0 < eps -> exists x6, forall x, x6 <= x -> logf x * logf x <= powf x eps.
Hypothesis hV : exists x1, forall x, x1 <= x -> forall i, VVAt x i.
Hypothesis hN : exists (C x3 : R), forall x, x3 <= x -> forall i, LinkAt C x i.
Hypothesis hR : exists x4, forall x, x4 <= x -> forall i, RankAt x i.
(* [QEX] divinN_at + vvRecord, DivinNOfHypV.lean:79 and :126-130.
   The bound constant it consumes is |C|+1, and it is told x1fam+1 <= x. *)
Hypothesis divin_at : forall C x i j,
  x1fam + 1 <= x ->
  LinkAt C x i -> RankAt x i -> VVAt x i ->
  logf x * logf x <= powf x eps ->
  DivAt (Rabs C + 1) x i j.

Theorem divinN_of_hypV_r : 0 < eps ->
  exists (Cb x0 : R), forall x, x0 <= x -> forall i j, DivAt Cb x i j.
Proof.
  intros He.
  destruct hV as [x1 H1].
  destruct hN as [C [x3 H3]].
  destruct hR as [x4 H4].
  destruct (log_sq_le_rpow He) as [x6 H6].
  exists (Rabs C + 1).
  exists (Rmax (Rmax x1 (Rmax x3 x4)) (Rmax x6 (x1fam + 1))).
  intros x Hx i j.
  destruct (divin_threshold_pack x1 x3 x4 x6 x1fam x Hx) as [G1 [G3 [G4 [G6 G7]]]].
  apply (divin_at C x i j).
  - exact G7.
  - apply H3. exact G3.
  - apply H4. exact G4.
  - apply H1. exact G1.
  - apply H6. exact G6.
Qed.
End Divin.

(* ===================================================================== *)
(* log_sq_le_rpow for the allowlist-clean log and power                   *)
(* (theories/LogRpowClean.v: Lc, rpc).  DivinNOfHypV.lean:59-74 states it  *)
(* for Real.log / Real.rpow; with Lc / rpc it is proved, not assumed.     *)
(* ===================================================================== *)
(* rpc x a -> oo as x -> oo (tendsto_rpow_atTop) *)
Lemma rpc_eventually_ge : forall a M, 0 < a -> exists x0, forall x, x0 <= x -> M <= rpc x a.
Proof.
  intros a M Ha. exists (exp (Rabs M / a)). intros x Hx.
  pose proof (exp_pos (Rabs M / a)) as He.
  assert (HL : Rabs M / a <= Lc x) by (rewrite <- (Lc_exp (Rabs M / a)); apply Lc_le_mono; assumption).
  assert (Hz : Rabs M <= a * Lc x).
  { apply (Rmult_le_compat_l a) in HL; [|lra].
    replace (a * (Rabs M / a)) with (Rabs M) in HL by (field; lra). exact HL. }
  unfold rpc. pose proof (exp_ge_1_plus (a * Lc x) ltac:(pose proof (Rabs_pos M); lra)).
  pose proof (Rle_abs M). lra.
Qed.

Theorem log_sq_le_rpc : forall eps, 0 < eps ->
  exists x6, forall x, x6 <= x -> Lc x * Lc x <= rpc x eps.
Proof.
  intros eps He. set (t := eps / 4).
  assert (Ht : 0 < t) by (unfold t; lra).
  destruct (rpc_eventually_ge (eps / 2) (/ (t * t)) ltac:(lra)) as [x0 Hx0].
  exists (Rmax 1 x0). intros x Hx.
  assert (Hx1 : 1 <= x) by (eapply Rle_trans; [apply Rmax_l|exact Hx]).
  assert (HL0 : 0 <= Lc x) by (apply Lc_nonneg; exact Hx1).
  pose proof (Lc_le_rpc_div x t ltac:(lra) Ht) as H1.
  pose proof (Hx0 x (Rle_trans _ _ _ (Rmax_r _ _) Hx)) as H2.
  set (q := rpc x t) in *.
  assert (Hq : 0 < q) by apply rpc_pos.
  assert (Hq2 : rpc x (eps / 2) = q * q) by (unfold q; rewrite <- rpc_add; f_equal; unfold t; field).
  assert (Hq4 : rpc x eps = (q * q) * (q * q)) by (rewrite <- Hq2, <- rpc_add; f_equal; field).
  rewrite Hq2 in H2. rewrite Hq4. clearbody q.
  assert (Hsq : Lc x * Lc x <= (q / t) * (q / t)) by (apply Rmult_le_compat; lra).
  assert (Ht2 : 0 < t * t) by nra.
  replace ((q / t) * (q / t)) with ((q * q) * / (t * t)) in Hsq by (field; lra).
  assert (Hqq : 0 <= q * q) by nra.
  assert ((q * q) * / (t * t) <= (q * q) * (q * q)) by (apply Rmult_le_compat_l; lra).
  lra.
Qed.

(* divinN_of_hypV with logf = Lc, powf = rpc: the log-square premise is
   discharged; the remaining premises are the Lean proof's QEX calls. *)
Theorem divinN_of_hypV_clean : forall eps x1fam (Ix : R -> Type)
  (VVAt : forall x, Ix x -> Prop) (LinkAt : R -> forall x, Ix x -> Prop)
  (RankAt : forall x, Ix x -> Prop) (DivAt : R -> forall x, Ix x -> nat -> Prop),
  (exists x1, forall x, x1 <= x -> forall i, VVAt x i) ->
  (exists (C x3 : R), forall x, x3 <= x -> forall i, LinkAt C x i) ->
  (exists x4, forall x, x4 <= x -> forall i, RankAt x i) ->
  (forall C x i j, x1fam + 1 <= x -> LinkAt C x i -> RankAt x i -> VVAt x i ->
     Lc x * Lc x <= rpc x eps -> DivAt (Rabs C + 1) x i j) ->
  0 < eps -> exists (Cb x0 : R), forall x, x0 <= x -> forall i j, DivAt Cb x i j.
Proof.
  intros eps x1fam Ix VVAt LinkAt RankAt DivAt hV hN hR hD He.
  exact (divinN_of_hypV_r eps x1fam Ix VVAt LinkAt RankAt DivAt Lc rpc
           (fun H => log_sq_le_rpc eps H) hV hN hR hD He).
Qed.

Print Assumptions rpc_eventually_ge.
Print Assumptions log_sq_le_rpc.
Print Assumptions divinN_of_hypV_clean.

(* ===================================================================== *)
(* bRest_all: record assembly.  FinalAll.lean:13-46.                      *)
(* ===================================================================== *)

Lemma zero_lt_three : 0 < 3.
Proof. lra. Qed.

Section Brest.
Variable Fam : Type.
Variable InD3 : Fam -> Prop.
Variable x1 sel1 : Fam -> R.
Variable Ix : Fam -> R -> Type.
Variable RowsB DivG DcPt : forall (Fm : Fam) (x : R), Ix Fm x -> Prop.
Variable TuSize DGamSize Tie : Fam -> Prop.
Variable Frame : Fam -> R -> Prop.
Variable GFrame Rank : Fam -> Prop.
Variable Sharp : Fam -> R -> Prop.
Variable Bu Rr La : Fam -> Prop.
(* RemainingDivisionBounds Fm Cabs CH.  Cabs is a parameter of the
   structure (IndefiniteRealisationChoice.lean:158).  hh mentions CH.
   bu, rr, la are exists-x0 tails (lines 161-163). *)
Record RemBounds (Cabs CH : R) (Fm : Fam) : Prop := mkRem {
  rem_hh : Frame Fm CH;
  rem_bu : Bu Fm;
  rem_rr : Rr Fm;
  rem_la : La Fm
}.
(* FinalAll.lean:20-26.  Guards x1 < x, sel <= x, and the index i. *)
Hypothesis hRB : forall Fm x (i : Ix Fm x), InD3 Fm ->
  x1 Fm < x -> sel1 Fm <= x -> RowsB Fm x i.
Hypothesis hDivG : forall Fm x (i : Ix Fm x), InD3 Fm ->
  x1 Fm < x -> sel1 Fm <= x -> DivG Fm x i.
Hypothesis hDcPtG : forall Fm x (i : Ix Fm x), InD3 Fm ->
  x1 Fm < x -> sel1 Fm <= x -> DcPt Fm x i.
(* [QEX] closed_funSharp_thr, FinalAll.lean:31.  CF0 is the witness it returns. *)
Hypothesis funSharp : forall Fm, InD3 Fm ->
  (forall x (i : Ix Fm x), x1 Fm < x -> sel1 Fm <= x -> RowsB Fm x i) ->
  (forall x (i : Ix Fm x), x1 Fm < x -> sel1 Fm <= x -> DivG Fm x i) ->
  forall hc : InD3 Fm, TuSize Fm -> DGamSize Fm -> exists CF0 : R, Sharp Fm CF0.
(* [QEX] linkG_frame, FinalAll.lean:35 *)
Hypothesis linkG_frame : forall Fm, InD3 Fm ->
  forall hc : InD3 Fm, TuSize Fm -> DGamSize Fm -> GFrame Fm.
Hypothesis tie_holds : forall Fm, InD3 Fm -> Tie Fm.
(* [QEX] muRank_of_lvl Fm (0 < 3), FinalAll.lean:38 *)
Hypothesis muRank_of_lvl : forall Fm, 0 < 3 -> Tie Fm -> TuSize Fm -> Rank Fm.
(* [QEX] hh_of_lvl, FinalAll.lean:40-41.  Consumes CF0, the frame, and the rank. *)
Hypothesis hh_of_lvl : forall Fm CH (CF0 : R), Sharp Fm CF0 -> GFrame Fm -> Rank Fm -> Frame Fm CH.
(* [QEX] buRat_rrFull_closed, FinalAll.lean:43 *)
Hypothesis bu_rr : forall Fm, InD3 Fm ->
  (forall x (i : Ix Fm x), x1 Fm < x -> sel1 Fm <= x -> DcPt Fm x i) ->
  forall hc : InD3 Fm, TuSize Fm -> DGamSize Fm -> Bu Fm /\ Rr Fm.
(* [QEX] la_of Fm, FinalAll.lean:46 *)
Hypothesis la_of : forall Fm, La Fm.

Theorem bRest_all_r : forall (Cabs : R) Fm CH, InD3 Fm ->
  forall hc : InD3 Fm, TuSize Fm -> DGamSize Fm -> RemBounds Cabs CH Fm.
Proof.
  intros Cabs Fm CH HD hc HU HG.
  assert (H3 : 0 < 3) by apply zero_lt_three.
  assert (HT : Tie Fm) by (apply tie_holds; exact HD).
  assert (Hrk : Rank Fm) by (apply (muRank_of_lvl Fm H3 HT HU)).
  destruct (funSharp Fm HD (fun x i hx hs => hRB Fm x i HD hx hs)
                      (fun x i hx hs => hDivG Fm x i HD hx hs) hc HU HG) as [CF0 HS].
  assert (Hgf : GFrame Fm) by (apply (linkG_frame Fm HD hc HU HG)).
  destruct (bu_rr Fm HD (fun x i hx hs => hDcPtG Fm x i HD hx hs) hc HU HG) as [HB Hrr].
  apply mkRem.
  - apply (hh_of_lvl Fm CH CF0 HS Hgf Hrk).
  - exact HB.
  - exact Hrr.
  - apply la_of.
Qed.

(* LinkBrest.lean:24 instantiates Cabs with the literal 2. *)
Theorem link_brest_at_two : forall Fm CH, InD3 Fm ->
  forall hc : InD3 Fm, TuSize Fm -> DGamSize Fm -> RemBounds 2 CH Fm.
Proof.
  intros Fm CH HD hc HU HG. apply (bRest_all_r 2 Fm CH HD hc HU HG).
Qed.
End Brest.

Print Assumptions scale_le_product.
Print Assumptions scale_le_product_needs_y.
Print Assumptions divin_abs_bound.
Print Assumptions divin_abs_needs_abs.
Print Assumptions divin_threshold_pack.
Print Assumptions divin_threshold_needs_all.
Print Assumptions log_sq_not_for_every_fn.
Print Assumptions divinN_of_hypV_r.
Print Assumptions zero_lt_three.
Print Assumptions bRest_all_r.
Print Assumptions link_brest_at_two.
