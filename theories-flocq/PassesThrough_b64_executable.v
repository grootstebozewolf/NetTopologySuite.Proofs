(* ============================================================================
   NetTopologySuite.Proofs.Flocq.PassesThrough_b64_executable
   ----------------------------------------------------------------------------
   EXECUTABLE realisation of the conservative closed Liang-Barsky filter of
   `PassesThrough_b64_conservative.v`.

   The conservative proof uses Flocq's directed rounding modes (mode_DN/mode_UP),
   which native floating point does not expose.  Here every directed operation is
   instead
          DN(x op y) := pred ( x op y )      UP(x op y) := succ ( x op y )
   where `x op y` is the ORDINARY round-to-nearest-even binary64 operation the
   oracle already extracts (b64_minus / b64_plus / b64_div) and pred/succ are
   IEEE nextDown/nextUp on binary64 (Flocq `Bpred`/`Bsucc`; .NET:
   `Math.BitDecrement` / `Math.BitIncrement`).

   Refinement (weakest form sufficient for the enclosure proofs):
     fin (exec_DN x y)  /\  B2R (exec_DN x y) <= B2R x op B2R y
                        /\  |B2R (exec_DN x y)| <= 2^(k+1)   (given |x op y| <= 2^k),
     and symmetrically for UP.
   Moreover exec_DN <= Flocq_DN and exec_UP >= Flocq_UP (`ex_*_refines_*`):
   the executable bounds are at least as wide.  EQUALITY with the Flocq term is
   FALSE whenever the exact result is representable (`ex_sub_dn_not_flocq`:
   1 - 0, exec DN = 1 - 2^-53 < 1 = Flocq DN), so it is not claimed.

   The conservative geometry is proved ONCE, generically, in
   `PassesThrough_b64_conservative.v` over a record of primitives carrying exactly
   these laws (`dprims`).  This module only supplies the second instance
   (`exec_prims`) and discharges its laws; no geometry is re-proved here.
   No Admitted / Axiom / Parameter.
   ========================================================================== *)
From Stdlib Require Import Reals ZArith Lra Lia Bool.
From Flocq Require Import IEEE754.Binary IEEE754.BinarySingleNaN Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib B64_AbsErr
  HotPixel_b64 PassesThrough_b64_compute PassesThrough_b64_grid_core
  PassesThrough_b64_grid_bounds PassesThrough_b64_conservative.
Local Open Scope R_scope.

Local Notation B2R := (Binary.B2R prec emax).
Local Notation fin := (Binary.is_finite prec emax).
Local Notation fexp := (SpecFloat.fexp prec emax).
Local Notation rnd_m := (fun m => round radix2 (SpecFloat.fexp prec emax) (round_mode m)).

(* -------------------------------------------------------------------------- *)
(* §1  Executable directed operations: nearest operation, then pred / succ.   *)
(* -------------------------------------------------------------------------- *)
Definition ex_pred (w : binary64) : binary64 :=
  Binary.Bpred prec emax prec_gt_0_b64 prec_lt_emax_b64 w.
Definition ex_succ (w : binary64) : binary64 :=
  Binary.Bsucc prec emax prec_gt_0_b64 prec_lt_emax_b64 w.

Definition ex_sub_dn (x y : binary64) : binary64 := ex_pred (b64_minus x y).
Definition ex_sub_up (x y : binary64) : binary64 := ex_succ (b64_minus x y).
Definition ex_add_dn (x y : binary64) : binary64 := ex_pred (b64_plus x y).
Definition ex_add_up (x y : binary64) : binary64 := ex_succ (b64_plus x y).
Definition ex_div_dn (x y : binary64) : binary64 := ex_pred (b64_div x y).
Definition ex_div_up (x y : binary64) : binary64 := ex_succ (b64_div x y).

(* -------------------------------------------------------------------------- *)
(* §2  pred/succ of a nearest-rounded value encloses the exact real.          *)
(* -------------------------------------------------------------------------- *)
Lemma ne_pred_ok : forall (w : binary64) (z : R) (k : Z),
  fin w = true -> B2R w = rnd_m mode_NE z -> (0 <= k <= 1020)%Z ->
  Rabs z <= bpow radix2 k ->
  fin (ex_pred w) = true /\ B2R (ex_pred w) = pred radix2 fexp (B2R w) /\
  B2R (ex_pred w) <= z /\ Rabs (B2R (ex_pred w)) <= bpow radix2 (k + 1).
Proof.
  intros w z k Fw Ew Hk Hz.
  assert (Hr : Rabs (B2R w) <= bpow radix2 k).
  { rewrite Ew. apply rnd_abs_le_bpow; [unfold emax; lia | exact Hz]. }
  assert (Fr : generic_format radix2 fexp (B2R w)).
  { rewrite Ew. exact (generic_format_round radix2 fexp (round_mode mode_NE) _). }
  assert (Hsucc : succ radix2 fexp (- B2R w) <= bpow radix2 (k + 1)).
  { apply (succ_le_lt radix2 fexp).
    - apply generic_format_opp. exact Fr.
    - apply generic_format_bpow_b64. unfold emax; lia.
    - apply Rle_lt_trans with (bpow radix2 k);
        [apply Rabs_le_inv in Hr; lra | apply bpow_lt; lia]. }
  pose proof (Binary.Bpred_correct prec emax prec_gt_0_b64 prec_lt_emax_b64 w Fw) as H.
  assert (Hlt : - bpow radix2 emax < pred radix2 fexp (B2R w)).
  { unfold pred.
    pose proof (bpow_lt radix2 (k + 1) emax ltac:(unfold emax; lia)). lra. }
  apply Rlt_bool_true in Hlt. unfold ex_pred.
  rewrite Hlt in H. destruct H as [HE [HF _]].
  refine (conj HF (conj HE (conj _ _))).
  - rewrite HE, Ew. exact (pred_round_le_id radix2 fexp (round_mode mode_NE) z).
  - rewrite HE. apply Rabs_le. split.
    + unfold pred. lra.
    + eapply Rle_trans; [apply pred_le_id|].
      apply Rabs_le_inv in Hr.
      pose proof (bpow_mono k (k + 1) ltac:(lia)). lra.
Qed.

Lemma ne_succ_ok : forall (w : binary64) (z : R) (k : Z),
  fin w = true -> B2R w = rnd_m mode_NE z -> (0 <= k <= 1020)%Z ->
  Rabs z <= bpow radix2 k ->
  fin (ex_succ w) = true /\ B2R (ex_succ w) = succ radix2 fexp (B2R w) /\
  z <= B2R (ex_succ w) /\ Rabs (B2R (ex_succ w)) <= bpow radix2 (k + 1).
Proof.
  intros w z k Fw Ew Hk Hz.
  assert (Hr : Rabs (B2R w) <= bpow radix2 k).
  { rewrite Ew. apply rnd_abs_le_bpow; [unfold emax; lia | exact Hz]. }
  assert (Fr : generic_format radix2 fexp (B2R w)).
  { rewrite Ew. exact (generic_format_round radix2 fexp (round_mode mode_NE) _). }
  assert (Hsucc : succ radix2 fexp (B2R w) <= bpow radix2 (k + 1)).
  { apply (succ_le_lt radix2 fexp).
    - exact Fr.
    - apply generic_format_bpow_b64. unfold emax; lia.
    - apply Rle_lt_trans with (bpow radix2 k);
        [apply Rabs_le_inv in Hr; lra | apply bpow_lt; lia]. }
  pose proof (Binary.Bsucc_correct prec emax prec_gt_0_b64 prec_lt_emax_b64 w Fw) as H.
  assert (Hlt : succ radix2 fexp (B2R w) < bpow radix2 emax).
  { pose proof (bpow_lt radix2 (k + 1) emax ltac:(unfold emax; lia)). lra. }
  apply Rlt_bool_true in Hlt. unfold ex_succ.
  rewrite Hlt in H. destruct H as [HE [HF _]].
  refine (conj HF (conj HE (conj _ _))).
  - rewrite HE, Ew. exact (succ_round_ge_id radix2 fexp (round_mode mode_NE) z).
  - rewrite HE. apply Rabs_le. split.
    + eapply Rle_trans; [|apply succ_ge_id].
      apply Rabs_le_inv in Hr.
      pose proof (bpow_mono k (k + 1) ltac:(lia)). lra.
    + exact Hsucc.
Qed.

(* ... and is at least as wide as the Flocq directed result. *)
Lemma ne_pred_le_dn : forall (w : binary64) (z : R),
  B2R w = rnd_m mode_NE z -> B2R (ex_pred w) = pred radix2 fexp (B2R w) ->
  B2R (ex_pred w) <= rnd_m mode_DN z.
Proof.
  intros w z Ew HE.
  assert (Hf : generic_format radix2 fexp (B2R w))
    by (rewrite Ew; exact (generic_format_round radix2 fexp (round_mode mode_NE) _)).
  assert (Hle : pred radix2 fexp (B2R w) <= z)
    by (rewrite Ew; exact (pred_round_le_id radix2 fexp (round_mode mode_NE) z)).
  pose proof (round_DN_pt radix2 fexp z) as [_ [_ Hg]].
  rewrite HE. apply Hg; [exact (generic_format_pred radix2 fexp _ Hf) | exact Hle].
Qed.

Lemma ne_succ_ge_up : forall (w : binary64) (z : R),
  B2R w = rnd_m mode_NE z -> B2R (ex_succ w) = succ radix2 fexp (B2R w) ->
  rnd_m mode_UP z <= B2R (ex_succ w).
Proof.
  intros w z Ew HE.
  assert (Hf : generic_format radix2 fexp (B2R w))
    by (rewrite Ew; exact (generic_format_round radix2 fexp (round_mode mode_NE) _)).
  assert (Hge : z <= succ radix2 fexp (B2R w))
    by (rewrite Ew; exact (succ_round_ge_id radix2 fexp (round_mode mode_NE) z)).
  pose proof (round_UP_pt radix2 fexp z) as [_ [_ Hg]].
  rewrite HE. apply Hg; [exact (generic_format_succ radix2 fexp _ Hf) | exact Hge].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Per-operation refinement (nearest operation is finite, no overflow).   *)
(* -------------------------------------------------------------------------- *)
Lemma div_ne_ok : forall x y,
  fin x = true -> B2R y <> 0 -> Rabs (B2R x / B2R y) <= bpow radix2 1004 ->
  fin (b64_div x y) = true /\ B2R (b64_div x y) = rnd_m mode_NE (B2R x / B2R y).
Proof.
  intros x y Fx Hy Hb.
  pose proof (Binary.Bdiv_correct prec emax prec_gt_0_b64 prec_lt_emax_b64
                default_nan_b64 mode_NE x y Hy) as H.
  assert (Hlt : Rlt_bool (Rabs (rnd_m mode_NE (B2R x / B2R y))) (bpow radix2 emax) = true).
  { apply Rlt_bool_true.
    eapply Rle_lt_trans; [apply (rnd_abs_le_bpow mode_NE _ 1004); [unfold emax; lia | exact Hb]|].
    apply bpow_lt; unfold emax; lia. }
  unfold b64_div, mode_b64. rewrite Hlt in H. destruct H as [H1 [H2 _]].
  split; [rewrite H2; exact Fx | exact H1].
Qed.

Local Ltac ne_sub_prelude x y k Hb Hk Fx Fy :=
  destruct (minus_m_ok mode_NE x y Fx Fy
              (Rle_trans _ _ _ Hb (bpow_mono _ _ (proj2 Hk)))) as [Fw Ew].
Local Ltac ne_add_prelude x y k Hb Hk Fx Fy :=
  destruct (plus_m_ok mode_NE x y Fx Fy
              (Rle_trans _ _ _ Hb (bpow_mono _ _ (proj2 Hk)))) as [Fw Ew].

Lemma ex_sub_dn_ok : forall x y k, fin x = true -> fin y = true ->
  (0 <= k <= 1000)%Z -> Rabs (B2R x - B2R y) <= bpow radix2 k ->
  fin (ex_sub_dn x y) = true /\ B2R (ex_sub_dn x y) <= B2R x - B2R y /\
  Rabs (B2R (ex_sub_dn x y)) <= bpow radix2 (k + 1).
Proof.
  intros x y k Fx Fy Hk Hb. ne_sub_prelude x y k Hb Hk Fx Fy.
  destruct (ne_pred_ok (b64_minus x y) _ k Fw Ew ltac:(lia) Hb) as [F [_ [E M]]].
  exact (conj F (conj E M)).
Qed.
Lemma ex_sub_up_ok : forall x y k, fin x = true -> fin y = true ->
  (0 <= k <= 1000)%Z -> Rabs (B2R x - B2R y) <= bpow radix2 k ->
  fin (ex_sub_up x y) = true /\ B2R x - B2R y <= B2R (ex_sub_up x y) /\
  Rabs (B2R (ex_sub_up x y)) <= bpow radix2 (k + 1).
Proof.
  intros x y k Fx Fy Hk Hb. ne_sub_prelude x y k Hb Hk Fx Fy.
  destruct (ne_succ_ok (b64_minus x y) _ k Fw Ew ltac:(lia) Hb) as [F [_ [E M]]].
  exact (conj F (conj E M)).
Qed.
Lemma ex_add_dn_ok : forall x y k, fin x = true -> fin y = true ->
  (0 <= k <= 1000)%Z -> Rabs (B2R x + B2R y) <= bpow radix2 k ->
  fin (ex_add_dn x y) = true /\ B2R (ex_add_dn x y) <= B2R x + B2R y /\
  Rabs (B2R (ex_add_dn x y)) <= bpow radix2 (k + 1).
Proof.
  intros x y k Fx Fy Hk Hb. ne_add_prelude x y k Hb Hk Fx Fy.
  destruct (ne_pred_ok (b64_plus x y) _ k Fw Ew ltac:(lia) Hb) as [F [_ [E M]]].
  exact (conj F (conj E M)).
Qed.
Lemma ex_add_up_ok : forall x y k, fin x = true -> fin y = true ->
  (0 <= k <= 1000)%Z -> Rabs (B2R x + B2R y) <= bpow radix2 k ->
  fin (ex_add_up x y) = true /\ B2R x + B2R y <= B2R (ex_add_up x y) /\
  Rabs (B2R (ex_add_up x y)) <= bpow radix2 (k + 1).
Proof.
  intros x y k Fx Fy Hk Hb. ne_add_prelude x y k Hb Hk Fx Fy.
  destruct (ne_succ_ok (b64_plus x y) _ k Fw Ew ltac:(lia) Hb) as [F [_ [E M]]].
  exact (conj F (conj E M)).
Qed.
Lemma ex_div_dn_ok : forall x y, fin x = true -> B2R y <> 0 ->
  Rabs (B2R x / B2R y) <= bpow radix2 1004 ->
  fin (ex_div_dn x y) = true /\ B2R (ex_div_dn x y) <= B2R x / B2R y.
Proof.
  intros x y Fx Hy Hb. destruct (div_ne_ok x y Fx Hy Hb) as [Fw Ew].
  destruct (ne_pred_ok (b64_div x y) _ 1004 Fw Ew ltac:(lia) Hb) as [F [_ [E _]]].
  exact (conj F E).
Qed.
Lemma ex_div_up_ok : forall x y, fin x = true -> B2R y <> 0 ->
  Rabs (B2R x / B2R y) <= bpow radix2 1004 ->
  fin (ex_div_up x y) = true /\ B2R x / B2R y <= B2R (ex_div_up x y).
Proof.
  intros x y Fx Hy Hb. destruct (div_ne_ok x y Fx Hy Hb) as [Fw Ew].
  destruct (ne_succ_ok (b64_div x y) _ 1004 Fw Ew ltac:(lia) Hb) as [F [_ [E _]]].
  exact (conj F E).
Qed.

(* The executable bounds are at least as wide as Flocq's mode_DN / mode_UP. *)
Theorem ex_sub_dn_refines_flocq : forall x y k, fin x = true -> fin y = true ->
  (0 <= k <= 1000)%Z -> Rabs (B2R x - B2R y) <= bpow radix2 k ->
  B2R (ex_sub_dn x y) <= B2R (b64_minus_m mode_DN x y).
Proof.
  intros x y k Fx Fy Hk Hb. ne_sub_prelude x y k Hb Hk Fx Fy.
  destruct (minus_m_ok mode_DN x y Fx Fy
              (Rle_trans _ _ _ Hb (bpow_mono _ _ (proj2 Hk)))) as [_ Ed].
  rewrite Ed.
  destruct (ne_pred_ok (b64_minus x y) _ k Fw Ew ltac:(lia) Hb) as [_ [HE _]].
  exact (ne_pred_le_dn (b64_minus x y) _ Ew HE).
Qed.

Theorem ex_sub_up_refines_flocq : forall x y k, fin x = true -> fin y = true ->
  (0 <= k <= 1000)%Z -> Rabs (B2R x - B2R y) <= bpow radix2 k ->
  B2R (b64_minus_m mode_UP x y) <= B2R (ex_sub_up x y).
Proof.
  intros x y k Fx Fy Hk Hb. ne_sub_prelude x y k Hb Hk Fx Fy.
  destruct (minus_m_ok mode_UP x y Fx Fy
              (Rle_trans _ _ _ Hb (bpow_mono _ _ (proj2 Hk)))) as [_ Eu].
  rewrite Eu.
  destruct (ne_succ_ok (b64_minus x y) _ k Fw Ew ltac:(lia) Hb) as [_ [HE _]].
  exact (ne_succ_ge_up (b64_minus x y) _ Ew HE).
Qed.

Theorem ex_div_dn_refines_flocq : forall x y, fin x = true -> B2R y <> 0 ->
  Rabs (B2R x / B2R y) <= bpow radix2 1004 ->
  B2R (ex_div_dn x y) <= B2R (b64_div_m mode_DN x y).
Proof.
  intros x y Fx Hy Hb.
  destruct (div_ne_ok x y Fx Hy Hb) as [Fw Ew].
  destruct (div_m_ok mode_DN x y Fx Hy Hb) as [_ Ed]. rewrite Ed.
  destruct (ne_pred_ok (b64_div x y) _ 1004 Fw Ew ltac:(lia) Hb) as [_ [HE _]].
  exact (ne_pred_le_dn (b64_div x y) _ Ew HE).
Qed.

Theorem ex_div_up_refines_flocq : forall x y, fin x = true -> B2R y <> 0 ->
  Rabs (B2R x / B2R y) <= bpow radix2 1004 ->
  B2R (b64_div_m mode_UP x y) <= B2R (ex_div_up x y).
Proof.
  intros x y Fx Hy Hb.
  destruct (div_ne_ok x y Fx Hy Hb) as [Fw Ew].
  destruct (div_m_ok mode_UP x y Fx Hy Hb) as [_ Eu]. rewrite Eu.
  destruct (ne_succ_ok (b64_div x y) _ 1004 Fw Ew ltac:(lia) Hb) as [_ [HE _]].
  exact (ne_succ_ge_up (b64_div x y) _ Ew HE).
Qed.

(* Equality with the Flocq term is FALSE when the exact result is representable:
   1 - 0 = 1, Flocq DN = 1, executable DN = pred 1 < 1. *)
Theorem ex_sub_dn_not_flocq :
  b64_compare (ex_sub_dn b64_one b64_zero) (b64_minus_m mode_DN b64_one b64_zero)
  = Some Lt.
Proof. vm_compute. reflexivity. Qed.
Theorem ex_sub_up_not_flocq :
  b64_compare (b64_minus_m mode_UP b64_one b64_zero) (ex_sub_up b64_one b64_zero)
  = Some Lt.
Proof. vm_compute. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* §5  The executable instance: nearest operation, then pred/succ.            *)
(* -------------------------------------------------------------------------- *)
Definition exec_prims : dprims :=
  mkDP ex_sub_dn ex_sub_up ex_add_dn ex_add_up ex_div_dn ex_div_up
       ex_sub_dn_ok ex_sub_up_ok ex_add_dn_ok ex_add_up_ok
       ex_div_dn_ok ex_div_up_ok.

Definition b64_touches_exec (P0 P1 C : BPoint) : bool := g_touches exec_prims P0 P1 C.

Definition b64_passes_through_hot_pixel_exec (P0 P1 C : BPoint) : bool :=
  b64_touches_exec P0 P1 C && b64_touches_exec (b64_snap P0) (b64_snap P1) C.

(* EXACT closed-pixel touch  ->  the executable conservative touch accepts. *)
Theorem b64_touches_complete_exec :
  forall P0 P1 C : BPoint,
    b64_liang_barsky_touches P0 P1 C = true ->
    b64_touches_exec P0 P1 C = true.
Proof. intros. exact (g_touches_complete exec_prims P0 P1 C H). Qed.

Theorem b64_passes_through_complete_exec :
  forall P0 P1 C : BPoint,
    b64_passes_through_hot_pixel P0 P1 C = true ->
    b64_passes_through_hot_pixel_exec P0 P1 C = true.
Proof.
  intros P0 P1 C H. unfold b64_passes_through_hot_pixel in H.
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  unfold b64_passes_through_hot_pixel_exec.
  apply Bool.andb_true_iff. split; apply b64_touches_complete_exec; assumption.
Qed.

Print Assumptions ex_sub_dn_ok.
Print Assumptions ex_sub_up_ok.
Print Assumptions ex_div_dn_ok.
Print Assumptions ex_div_up_ok.
Print Assumptions ex_sub_dn_refines_flocq.
Print Assumptions ex_div_up_refines_flocq.
Print Assumptions b64_touches_complete_exec.
Print Assumptions b64_passes_through_complete_exec.
