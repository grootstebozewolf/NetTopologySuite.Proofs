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

   The conservative geometry is then re-instantiated ONCE, generically, over a
   record of primitives carrying exactly these laws (`dprims`); all pure-real
   lemmas (outward division, Rmin/Rmax monotonicity, guards, ub_max_ok, dom_ok)
   are imported from the conservative module unchanged.
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
  Rabs (B2R x / B2R y) <= bpow radix2 1002 ->
  B2R (ex_div_dn x y) <= B2R (b64_div_m mode_DN x y).
Proof.
  intros x y Fx Hy Hb.
  assert (Hb' : Rabs (B2R x / B2R y) <= bpow radix2 1004)
    by (eapply Rle_trans; [exact Hb | apply bpow_mono; lia]).
  destruct (div_ne_ok x y Fx Hy Hb') as [Fw Ew].
  destruct (div_m_ok mode_DN x y Fx Hy Hb) as [_ Ed]. rewrite Ed.
  destruct (ne_pred_ok (b64_div x y) _ 1004 Fw Ew ltac:(lia) Hb') as [_ [HE _]].
  exact (ne_pred_le_dn (b64_div x y) _ Ew HE).
Qed.

Theorem ex_div_up_refines_flocq : forall x y, fin x = true -> B2R y <> 0 ->
  Rabs (B2R x / B2R y) <= bpow radix2 1002 ->
  B2R (b64_div_m mode_UP x y) <= B2R (ex_div_up x y).
Proof.
  intros x y Fx Hy Hb.
  assert (Hb' : Rabs (B2R x / B2R y) <= bpow radix2 1004)
    by (eapply Rle_trans; [exact Hb | apply bpow_mono; lia]).
  destruct (div_ne_ok x y Fx Hy Hb') as [Fw Ew].
  destruct (div_m_ok mode_UP x y Fx Hy Hb) as [_ Eu]. rewrite Eu.
  destruct (ne_succ_ok (b64_div x y) _ 1004 Fw Ew ltac:(lia) Hb') as [_ [HE _]].
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
(* §4  Interface of directed primitives, and the generic conservative filter. *)
(*     A `dprims` carries exactly the laws the enclosure proofs consume.      *)
(*     (Magnitude slack k+1: valid both for Flocq mode_DN/UP and for          *)
(*      nearest-then-pred/succ.)                                              *)
(* -------------------------------------------------------------------------- *)
Record dprims := mkDP {
  sdn : binary64 -> binary64 -> binary64;
  sup : binary64 -> binary64 -> binary64;
  adn : binary64 -> binary64 -> binary64;
  aup : binary64 -> binary64 -> binary64;
  ddn : binary64 -> binary64 -> binary64;
  dup : binary64 -> binary64 -> binary64;
  sdn_ok : forall x y k, fin x = true -> fin y = true -> (0 <= k <= 1000)%Z ->
    Rabs (B2R x - B2R y) <= bpow radix2 k ->
    fin (sdn x y) = true /\ B2R (sdn x y) <= B2R x - B2R y /\
    Rabs (B2R (sdn x y)) <= bpow radix2 (k + 1);
  sup_ok : forall x y k, fin x = true -> fin y = true -> (0 <= k <= 1000)%Z ->
    Rabs (B2R x - B2R y) <= bpow radix2 k ->
    fin (sup x y) = true /\ B2R x - B2R y <= B2R (sup x y) /\
    Rabs (B2R (sup x y)) <= bpow radix2 (k + 1);
  adn_ok : forall x y k, fin x = true -> fin y = true -> (0 <= k <= 1000)%Z ->
    Rabs (B2R x + B2R y) <= bpow radix2 k ->
    fin (adn x y) = true /\ B2R (adn x y) <= B2R x + B2R y /\
    Rabs (B2R (adn x y)) <= bpow radix2 (k + 1);
  aup_ok : forall x y k, fin x = true -> fin y = true -> (0 <= k <= 1000)%Z ->
    Rabs (B2R x + B2R y) <= bpow radix2 k ->
    fin (aup x y) = true /\ B2R x + B2R y <= B2R (aup x y) /\
    Rabs (B2R (aup x y)) <= bpow radix2 (k + 1);
  ddn_ok : forall x y, fin x = true -> B2R y <> 0 ->
    Rabs (B2R x / B2R y) <= bpow radix2 1004 ->
    fin (ddn x y) = true /\ B2R (ddn x y) <= B2R x / B2R y;
  dup_ok : forall x y, fin x = true -> B2R y <> 0 ->
    Rabs (B2R x / B2R y) <= bpow radix2 1004 ->
    fin (dup x y) = true /\ B2R x / B2R y <= B2R (dup x y)
}.

Lemma div_abs_bound504 : forall n d : R,
  bpow radix2 (-500) <= Rabs d -> Rabs n <= bpow radix2 504 ->
  Rabs (n / d) <= bpow radix2 1004.
Proof.
  intros n d Hd Hn.
  assert (Hpos : 0 < bpow radix2 (-500)) by apply bpow_gt_0.
  assert (Hd0 : 0 < Rabs d) by lra.
  assert (Hne : d <> 0).
  { intro H. rewrite H, Rabs_R0 in Hd0. lra. }
  unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv by exact Hne.
  assert (Hi : / Rabs d <= bpow radix2 500).
  { replace (bpow radix2 500) with (/ bpow radix2 (-500)).
    - apply Rinv_le_contravar; assumption.
    - replace (-500)%Z with (-(500))%Z by reflexivity.
      rewrite bpow_opp, Rinv_inv. reflexivity. }
  assert (Hi0 : 0 <= / Rabs d) by (apply Rlt_le, Rinv_0_lt_compat; exact Hd0).
  assert (Hn0 : 0 <= Rabs n) by apply Rabs_pos.
  eapply Rle_trans; [apply Rmult_le_compat; [exact Hn0 | exact Hi0 | exact Hn | exact Hi]|].
  rewrite bpow_sum. replace (504 + 500)%Z with 1004%Z by reflexivity. apply Rle_refl.
Qed.

Section Generic.
Variable P : dprims.

Definition g_lo_m (cc : binary64) := sdn P cc b64_half.
Definition g_lo_p (cc : binary64) := sup P cc b64_half.
Definition g_hi_m (cc : binary64) := adn P cc b64_half.
Definition g_hi_p (cc : binary64) := aup P cc b64_half.
Definition g_pmin (c0 cc : binary64) := sdn P (g_lo_m cc) c0.
Definition g_pmax (c0 cc : binary64) := sup P (g_lo_p cc) c0.
Definition g_rmin (c0 cc : binary64) := sdn P (g_hi_m cc) c0.
Definition g_rmax (c0 cc : binary64) := sup P (g_hi_p cc) c0.
Definition g_bmin (c0 c1 : binary64) := sdn P c1 c0.
Definition g_bmax (c0 c1 : binary64) := sup P c1 c0.

Definition g_q_lower (nmin nmax bmin bmax : binary64) : option binary64 :=
  if b64_le b64_pn500 bmin then
    Some (ddn P nmin (if b64_le b64_zero nmin then bmax else bmin))
  else if b64_le bmax b64_mn500 then
    Some (ddn P nmax (if b64_le nmax b64_zero then bmin else bmax))
  else None.

Definition g_q_upper (nmin nmax bmin bmax : binary64) : option binary64 :=
  if b64_le b64_pn500 bmin then
    Some (dup P nmax (if b64_le b64_zero nmax then bmin else bmax))
  else if b64_le bmax b64_mn500 then
    Some (dup P nmin (if b64_le nmin b64_zero then bmax else bmin))
  else None.

Definition g_axis_lo (c0 c1 cc : binary64) : option binary64 :=
  if b64_eqb c1 c0 then Some b64_zero
  else opt_min
         (g_q_lower (g_pmin c0 cc) (g_pmax c0 cc) (g_bmin c0 c1) (g_bmax c0 c1))
         (g_q_lower (g_rmin c0 cc) (g_rmax c0 cc) (g_bmin c0 c1) (g_bmax c0 c1)).

Definition g_axis_hi (c0 c1 cc : binary64) : option binary64 :=
  if b64_eqb c1 c0 then Some b64_one
  else opt_max
         (g_q_upper (g_pmin c0 cc) (g_pmax c0 cc) (g_bmin c0 c1) (g_bmax c0 c1))
         (g_q_upper (g_rmin c0 cc) (g_rmax c0 cc) (g_bmin c0 c1) (g_bmax c0 c1)).

Definition g_axis_guard (c0 c1 cc : binary64) : bool :=
  if b64_eqb c1 c0
  then andb (b64_le (g_lo_m cc) c0) (b64_le c0 (g_hi_p cc))
  else true.

Definition g_touches (P0 P1 C : BPoint) : bool :=
  if b64_dom (bx P0) && b64_dom (by_ P0) && b64_dom (bx P1) && b64_dom (by_ P1)
     && b64_dom (bx C) && b64_dom (by_ C)
  then
    g_axis_guard (bx P0) (bx P1) (bx C) && g_axis_guard (by_ P0) (by_ P1) (by_ C)
    && b64_le
         (ub_max (ub_max b64_zero (g_axis_lo (bx P0) (bx P1) (bx C)))
                 (g_axis_lo (by_ P0) (by_ P1) (by_ C)))
         (ub_min (ub_min b64_one (g_axis_hi (bx P0) (bx P1) (bx C)))
                 (g_axis_hi (by_ P0) (by_ P1) (by_ C)))
  else true.

Lemma g_q_lower_ok : forall nmin nmax bmin bmax a b,
  fin nmin = true -> fin nmax = true -> fin bmin = true -> fin bmax = true ->
  Rabs (B2R nmin) <= bpow radix2 504 -> Rabs (B2R nmax) <= bpow radix2 504 ->
  B2R nmin <= a -> a <= B2R nmax -> B2R bmin <= b -> b <= B2R bmax ->
  match g_q_lower nmin nmax bmin bmax with
  | Some v => fin v = true /\ B2R v <= a / b
  | None => True
  end.
Proof.
  intros nmin nmax bmin bmax a b Fn1 Fn2 Fb1 Fb2 Hn1 Hn2 Ha1 Ha2 Hb1 Hb2.
  pose proof (bpow_gt_0 radix2 (-500)) as Hl.
  unfold g_q_lower.
  destruct (b64_le b64_pn500 bmin) eqn:E1.
  - apply b64ae_le_true in E1; [|exact fin_pn500|exact Fb1]. rewrite B2R_pn500 in E1.
    destruct (b64_le b64_zero nmin) eqn:E2.
    + apply b64ae_le_true in E2; [|exact is_finite_b64_zero|exact Fn1].
      rewrite B2R_b64_zero in E2.
      assert (Hbm : bpow radix2 (-500) <= B2R bmax) by lra.
      destruct (ddn_ok P nmin bmax Fn1 ltac:(lra)
                  (div_abs_bound504 _ _ (Rabs_ge_pos _ Hbm) Hn1)) as [Fv Ev].
      cbn zeta. split; [exact Fv|]. eapply Rle_trans; [exact Ev|].
      apply (lowP1 (B2R bmin) b (B2R bmax) a (B2R nmin)); lra.
    + apply b64ae_le_false in E2; [|exact is_finite_b64_zero|exact Fn1].
      rewrite B2R_b64_zero in E2.
      destruct (ddn_ok P nmin bmin Fn1 ltac:(lra)
                  (div_abs_bound504 _ _ (Rabs_ge_pos _ E1) Hn1)) as [Fv Ev].
      split; [exact Fv|]. eapply Rle_trans; [exact Ev|].
      apply (lowP2 (B2R bmin) b (B2R bmax) a (B2R nmin)); lra.
  - destruct (b64_le bmax b64_mn500) eqn:E3; [|exact I].
    apply b64ae_le_true in E3; [|exact Fb2|exact fin_mn500]. rewrite B2R_mn500 in E3.
    destruct (b64_le nmax b64_zero) eqn:E4.
    + apply b64ae_le_true in E4; [|exact Fn2|exact is_finite_b64_zero].
      rewrite B2R_b64_zero in E4.
      assert (Hbm : B2R bmin <= - bpow radix2 (-500)) by lra.
      destruct (ddn_ok P nmax bmin Fn2 ltac:(lra)
                  (div_abs_bound504 _ _ (Rabs_ge_neg _ Hbm) Hn2)) as [Fv Ev].
      split; [exact Fv|]. eapply Rle_trans; [exact Ev|].
      apply (lowN1 (B2R bmin) b (B2R bmax) a (B2R nmax)); lra.
    + apply b64ae_le_false in E4; [|exact Fn2|exact is_finite_b64_zero].
      rewrite B2R_b64_zero in E4.
      destruct (ddn_ok P nmax bmax Fn2 ltac:(lra)
                  (div_abs_bound504 _ _ (Rabs_ge_neg _ E3) Hn2)) as [Fv Ev].
      split; [exact Fv|]. eapply Rle_trans; [exact Ev|].
      apply (lowN2 (B2R bmin) b (B2R bmax) a (B2R nmax)); lra.
Qed.

Lemma g_q_upper_ok : forall nmin nmax bmin bmax a b,
  fin nmin = true -> fin nmax = true -> fin bmin = true -> fin bmax = true ->
  Rabs (B2R nmin) <= bpow radix2 504 -> Rabs (B2R nmax) <= bpow radix2 504 ->
  B2R nmin <= a -> a <= B2R nmax -> B2R bmin <= b -> b <= B2R bmax ->
  match g_q_upper nmin nmax bmin bmax with
  | Some v => fin v = true /\ a / b <= B2R v
  | None => True
  end.
Proof.
  intros nmin nmax bmin bmax a b Fn1 Fn2 Fb1 Fb2 Hn1 Hn2 Ha1 Ha2 Hb1 Hb2.
  pose proof (bpow_gt_0 radix2 (-500)) as Hl.
  unfold g_q_upper.
  destruct (b64_le b64_pn500 bmin) eqn:E1.
  - apply b64ae_le_true in E1; [|exact fin_pn500|exact Fb1]. rewrite B2R_pn500 in E1.
    destruct (b64_le b64_zero nmax) eqn:E2.
    + apply b64ae_le_true in E2; [|exact is_finite_b64_zero|exact Fn2].
      rewrite B2R_b64_zero in E2.
      destruct (dup_ok P nmax bmin Fn2 ltac:(lra)
                  (div_abs_bound504 _ _ (Rabs_ge_pos _ E1) Hn2)) as [Fv Ev].
      split; [exact Fv|]. eapply Rle_trans; [|exact Ev].
      apply (upP1 (B2R bmin) b (B2R bmax) a (B2R nmax)); lra.
    + apply b64ae_le_false in E2; [|exact is_finite_b64_zero|exact Fn2].
      rewrite B2R_b64_zero in E2.
      assert (Hbm : bpow radix2 (-500) <= B2R bmax) by lra.
      destruct (dup_ok P nmax bmax Fn2 ltac:(lra)
                  (div_abs_bound504 _ _ (Rabs_ge_pos _ Hbm) Hn2)) as [Fv Ev].
      split; [exact Fv|]. eapply Rle_trans; [|exact Ev].
      apply (upP2 (B2R bmin) b (B2R bmax) a (B2R nmax)); lra.
  - destruct (b64_le bmax b64_mn500) eqn:E3; [|exact I].
    apply b64ae_le_true in E3; [|exact Fb2|exact fin_mn500]. rewrite B2R_mn500 in E3.
    destruct (b64_le nmin b64_zero) eqn:E4.
    + apply b64ae_le_true in E4; [|exact Fn1|exact is_finite_b64_zero].
      rewrite B2R_b64_zero in E4.
      destruct (dup_ok P nmin bmax Fn1 ltac:(lra)
                  (div_abs_bound504 _ _ (Rabs_ge_neg _ E3) Hn1)) as [Fv Ev].
      split; [exact Fv|]. eapply Rle_trans; [|exact Ev].
      apply (upN1 (B2R bmin) b (B2R bmax) a (B2R nmin)); lra.
    + apply b64ae_le_false in E4; [|exact Fn1|exact is_finite_b64_zero].
      rewrite B2R_b64_zero in E4.
      assert (Hbm : B2R bmin <= - bpow radix2 (-500)) by lra.
      destruct (dup_ok P nmin bmin Fn1 ltac:(lra)
                  (div_abs_bound504 _ _ (Rabs_ge_neg _ Hbm) Hn1)) as [Fv Ev].
      split; [exact Fv|]. eapply Rle_trans; [|exact Ev].
      apply (upN2 (B2R bmin) b (B2R bmax) a (B2R nmin)); lra.
Qed.


(* Everything the quotient lemmas need about one axis (magnitudes 2^504). *)
Lemma g_axis_facts : forall c0 c1 cc,
  fin c0 = true -> fin c1 = true -> fin cc = true ->
  Rabs (B2R c0) <= bpow radix2 500 -> Rabs (B2R c1) <= bpow radix2 500 ->
  Rabs (B2R cc) <= bpow radix2 500 ->
  let lo := B2R cc - / 2 in let hi := B2R cc + / 2 in
  fin (g_lo_m cc) = true /\ fin (g_lo_p cc) = true /\
  fin (g_hi_m cc) = true /\ fin (g_hi_p cc) = true /\
  B2R (g_lo_m cc) <= lo /\ lo <= B2R (g_lo_p cc) /\
  B2R (g_hi_m cc) <= hi /\ hi <= B2R (g_hi_p cc) /\
  fin (g_pmin c0 cc) = true /\ fin (g_pmax c0 cc) = true /\
  fin (g_rmin c0 cc) = true /\ fin (g_rmax c0 cc) = true /\
  B2R (g_pmin c0 cc) <= lo - B2R c0 /\ lo - B2R c0 <= B2R (g_pmax c0 cc) /\
  B2R (g_rmin c0 cc) <= hi - B2R c0 /\ hi - B2R c0 <= B2R (g_rmax c0 cc) /\
  Rabs (B2R (g_pmin c0 cc)) <= bpow radix2 504 /\
  Rabs (B2R (g_pmax c0 cc)) <= bpow radix2 504 /\
  Rabs (B2R (g_rmin c0 cc)) <= bpow radix2 504 /\
  Rabs (B2R (g_rmax c0 cc)) <= bpow radix2 504 /\
  fin (g_bmin c0 c1) = true /\ fin (g_bmax c0 c1) = true /\
  B2R (g_bmin c0 c1) <= B2R c1 - B2R c0 /\ B2R c1 - B2R c0 <= B2R (g_bmax c0 c1).
Proof.
  intros c0 c1 cc F0 F1 Fc H0 H1 Hc lo hi.
  destruct B2R_and_finite_b64_half as [Bh Fh].
  assert (Hh : Rabs (B2R b64_half) <= bpow radix2 500).
  { rewrite Bh, Rabs_right by lra. exact half_le_500. }
  assert (Hdb : forall z, Rabs z <= bpow radix2 500 + bpow radix2 500 ->
                          Rabs z <= bpow radix2 501).
  { intros z Hz. pose proof (bpow_double 500) as D.
    replace (500 + 1)%Z with 501%Z in D by reflexivity. lra. }
  destruct (sdn_ok P cc b64_half 501 Fc Fh ltac:(lia)
              (Hdb _ (abs_diff_le _ _ _ _ Hc Hh))) as [Flm [Rlm Alm]].
  destruct (sup_ok P cc b64_half 501 Fc Fh ltac:(lia)
              (Hdb _ (abs_diff_le _ _ _ _ Hc Hh))) as [Flp [Rlp Alp]].
  destruct (adn_ok P cc b64_half 501 Fc Fh ltac:(lia)
              (Hdb _ (abs_sum_le _ _ _ _ Hc Hh))) as [Fhm [Rhm Ahm]].
  destruct (aup_ok P cc b64_half 501 Fc Fh ltac:(lia)
              (Hdb _ (abs_sum_le _ _ _ _ Hc Hh))) as [Fhp [Rhp Ahp]].
  rewrite Bh in Rlm, Rlp, Rhm, Rhp.
  replace (501 + 1)%Z with 502%Z in Alm, Alp, Ahm, Ahp by reflexivity.
  (* numerators: |lo_m - c0| <= 2^502 + 2^500 <= 2^503 *)
  assert (H503 : bpow radix2 502 + bpow radix2 500 <= bpow radix2 503).
  { pose proof (bpow_double 502) as D.
    replace (502 + 1)%Z with 503%Z in D by reflexivity.
    pose proof (bpow_mono 500 502 ltac:(lia)). lra. }
  assert (Hst : forall z, Rabs z <= bpow radix2 502 + bpow radix2 500 ->
                          Rabs z <= bpow radix2 503).
  { intros z Hz. eapply Rle_trans; [exact Hz | exact H503]. }
  destruct (sdn_ok P (g_lo_m cc) c0 503 Flm F0 ltac:(lia)
              (Hst _ (abs_diff_le _ _ _ _ Alm H0))) as [Fpm [Rpm Apm]].
  destruct (sup_ok P (g_lo_p cc) c0 503 Flp F0 ltac:(lia)
              (Hst _ (abs_diff_le _ _ _ _ Alp H0))) as [Fpp [Rpp App]].
  destruct (sdn_ok P (g_hi_m cc) c0 503 Fhm F0 ltac:(lia)
              (Hst _ (abs_diff_le _ _ _ _ Ahm H0))) as [Frm [Rrm Arm]].
  destruct (sup_ok P (g_hi_p cc) c0 503 Fhp F0 ltac:(lia)
              (Hst _ (abs_diff_le _ _ _ _ Ahp H0))) as [Frp [Rrp Arp]].
  replace (503 + 1)%Z with 504%Z in Apm, App, Arm, Arp by reflexivity.
  assert (Hb : Rabs (B2R c1 - B2R c0) <= bpow radix2 501)
    by (apply Hdb; apply abs_diff_le; assumption).
  destruct (sdn_ok P c1 c0 501 F1 F0 ltac:(lia) Hb) as [Fbm [Rbm Abm]].
  destruct (sup_ok P c1 c0 501 F1 F0 ltac:(lia) Hb) as [Fbp [Rbp Abp]].
  unfold g_pmin, g_pmax, g_rmin, g_rmax, g_bmin, g_bmax, g_lo_m, g_lo_p, g_hi_m, g_hi_p in *.
  unfold lo, hi. repeat split; try assumption; lra.
Qed.

(* POLARITY, lower bound:  computed lower  <=  exact lower  (lb_tlo). *)
Lemma g_axis_lo_ok : forall c0 c1 cc,
  fin c0 = true -> fin c1 = true -> fin cc = true ->
  Rabs (B2R c0) <= bpow radix2 500 -> Rabs (B2R c1) <= bpow radix2 500 ->
  Rabs (B2R cc) <= bpow radix2 500 ->
  match g_axis_lo c0 c1 cc with
  | Some v => fin v = true /\
      B2R v <= lb_tlo (B2R c0) (B2R c1) (B2R cc - / 2) (B2R cc + / 2)
  | None => True
  end.
Proof.
  intros c0 c1 cc F0 F1 Fc H0 H1 Hc.
  unfold g_axis_lo.
  destruct (b64_eqb c1 c0) eqn:Eeq.
  - apply (proj1 (b64_eqb_true_iff_B2R _ _ F1 F0)) in Eeq.
    split; [exact is_finite_b64_zero|].
    unfold lb_tlo. destruct (Req_dec_T _ _) as [_|Hn]; [|exfalso; apply Hn; exact Eeq].
    rewrite B2R_b64_zero. lra.
  - assert (Hne : B2R c1 <> B2R c0).
    { intro H. apply (proj2 (b64_eqb_true_iff_B2R _ _ F1 F0)) in H.
      rewrite H in Eeq. discriminate. }
    destruct (g_axis_facts c0 c1 cc F0 F1 Fc H0 H1 Hc) as
      (_&_&_&_&_&_&_&_& Fpm&Fpp&Frm&Frp& Rpm&Rpp&Rrm&Rrp& Apm&App&Arm&Arp&
       Fbm&Fbp& Rbm&Rbp).
    unfold lb_tlo. destruct (Req_dec_T _ _) as [Hc'|_]; [exfalso; apply Hne; exact Hc'|].
    pose proof (g_q_lower_ok (g_pmin c0 cc) (g_pmax c0 cc) (g_bmin c0 c1) (g_bmax c0 c1)
                  (B2R cc - / 2 - B2R c0) (B2R c1 - B2R c0)
                  Fpm Fpp Fbm Fbp Apm App Rpm Rpp Rbm Rbp) as Hp.
    pose proof (g_q_lower_ok (g_rmin c0 cc) (g_rmax c0 cc) (g_bmin c0 c1) (g_bmax c0 c1)
                  (B2R cc + / 2 - B2R c0) (B2R c1 - B2R c0)
                  Frm Frp Fbm Fbp Arm Arp Rrm Rrp Rbm Rbp) as Hr.
    unfold opt_min.
    destruct (g_q_lower (g_pmin c0 cc) (g_pmax c0 cc) (g_bmin c0 c1) (g_bmax c0 c1))
      as [A|]; [|exact I].
    destruct (g_q_lower (g_rmin c0 cc) (g_rmax c0 cc) (g_bmin c0 c1) (g_bmax c0 c1))
      as [Bv|]; [|exact I].
    destruct Hp as [FA HA]. destruct Hr as [FB HB].
    split; [apply is_finite_b64_min; assumption|].
    rewrite (b64_min_B2R _ _ FA FB).
    apply Rmin_mono; assumption.
Qed.


(* POLARITY, upper bound:  exact upper (lb_thi)  <=  computed upper. *)
Lemma g_axis_hi_ok : forall c0 c1 cc,
  fin c0 = true -> fin c1 = true -> fin cc = true ->
  Rabs (B2R c0) <= bpow radix2 500 -> Rabs (B2R c1) <= bpow radix2 500 ->
  Rabs (B2R cc) <= bpow radix2 500 ->
  match g_axis_hi c0 c1 cc with
  | Some v => fin v = true /\
      lb_thi (B2R c0) (B2R c1) (B2R cc - / 2) (B2R cc + / 2) <= B2R v
  | None => True
  end.
Proof.
  intros c0 c1 cc F0 F1 Fc H0 H1 Hc.
  unfold g_axis_hi.
  destruct (b64_eqb c1 c0) eqn:Eeq.
  - apply (proj1 (b64_eqb_true_iff_B2R _ _ F1 F0)) in Eeq.
    destruct B2R_and_finite_b64_one as [B1 F1']. split; [exact F1'|].
    unfold lb_thi. destruct (Req_dec_T _ _) as [_|Hn]; [|exfalso; apply Hn; exact Eeq].
    rewrite B1. lra.
  - assert (Hne : B2R c1 <> B2R c0).
    { intro H. apply (proj2 (b64_eqb_true_iff_B2R _ _ F1 F0)) in H.
      rewrite H in Eeq. discriminate. }
    destruct (g_axis_facts c0 c1 cc F0 F1 Fc H0 H1 Hc) as
      (_&_&_&_&_&_&_&_& Fpm&Fpp&Frm&Frp& Rpm&Rpp&Rrm&Rrp& Apm&App&Arm&Arp&
       Fbm&Fbp& Rbm&Rbp).
    unfold lb_thi. destruct (Req_dec_T _ _) as [Hc'|_]; [exfalso; apply Hne; exact Hc'|].
    pose proof (g_q_upper_ok (g_pmin c0 cc) (g_pmax c0 cc) (g_bmin c0 c1) (g_bmax c0 c1)
                  (B2R cc - / 2 - B2R c0) (B2R c1 - B2R c0)
                  Fpm Fpp Fbm Fbp Apm App Rpm Rpp Rbm Rbp) as Hp.
    pose proof (g_q_upper_ok (g_rmin c0 cc) (g_rmax c0 cc) (g_bmin c0 c1) (g_bmax c0 c1)
                  (B2R cc + / 2 - B2R c0) (B2R c1 - B2R c0)
                  Frm Frp Fbm Fbp Arm Arp Rrm Rrp Rbm Rbp) as Hr.
    unfold opt_max.
    destruct (g_q_upper (g_pmin c0 cc) (g_pmax c0 cc) (g_bmin c0 c1) (g_bmax c0 c1))
      as [A|]; [|exact I].
    destruct (g_q_upper (g_rmin c0 cc) (g_rmax c0 cc) (g_bmin c0 c1) (g_bmax c0 c1))
      as [Bv|]; [|exact I].
    destruct Hp as [FA HA]. destruct Hr as [FB HB].
    split; [apply is_finite_b64_max; assumption|].
    rewrite (b64_max_B2R _ _ FA FB).
    apply Rmax_mono; assumption.
Qed.


(* The degenerate-axis guard accepts whenever the exact guard does. *)
Lemma g_axis_guard_ok : forall c0 c1 cc,
  fin c0 = true -> fin c1 = true -> fin cc = true ->
  Rabs (B2R c0) <= bpow radix2 500 -> Rabs (B2R c1) <= bpow radix2 500 ->
  Rabs (B2R cc) <= bpow radix2 500 ->
  lb_inslab (B2R c0) (B2R c1) (B2R cc - / 2) (B2R cc + / 2) = true ->
  g_axis_guard c0 c1 cc = true.
Proof.
  intros c0 c1 cc F0 F1 Fc H0 H1 Hc Hs.
  destruct (g_axis_facts c0 c1 cc F0 F1 Fc H0 H1 Hc) as
    (Flm&_&_&Fhp& Rlm&_&_&Rhp& _).
  unfold g_axis_guard.
  destruct (b64_eqb c1 c0) eqn:Eeq; [|reflexivity].
  apply (proj1 (b64_eqb_true_iff_B2R _ _ F1 F0)) in Eeq.
  unfold lb_inslab in Hs. destruct (Req_dec_T _ _) as [_|Hn]; [|exfalso; apply Hn; exact Eeq].
  apply Bool.andb_true_iff in Hs. destruct Hs as [Hs1 Hs2].
  apply Rle_bool_elim in Hs1. apply Rle_bool_elim in Hs2.
  apply Bool.andb_true_iff. split; apply b64_le_complete; try assumption; lra.
Qed.


(* COMPLETENESS of the repaired touch: every exact closed-pixel touch is accepted,
   for EVERY binary64 triple (out-of-domain inputs are accepted by definition). *)
Theorem g_touches_complete :
  forall P0 P1 C : BPoint,
    b64_liang_barsky_touches P0 P1 C = true ->
    g_touches P0 P1 C = true.
Proof.
  intros P0 P1 C Hs. unfold g_touches.
  destruct (b64_dom (bx P0) && b64_dom (by_ P0) && b64_dom (bx P1)
            && b64_dom (by_ P1) && b64_dom (bx C) && b64_dom (by_ C)) eqn:Ed;
    [|reflexivity].
  apply Bool.andb_true_iff in Ed; destruct Ed as [Ed Dcy_].
  apply Bool.andb_true_iff in Ed; destruct Ed as [Ed Dcx_].
  apply Bool.andb_true_iff in Ed; destruct Ed as [Ed Dy1_].
  apply Bool.andb_true_iff in Ed; destruct Ed as [Ed Dx1_].
  apply Bool.andb_true_iff in Ed; destruct Ed as [Dx0_ Dy0_].
  destruct (dom_ok _ Dcy_) as [Fcy Hcy]. destruct (dom_ok _ Dcx_) as [Fcx Hcx].
  destruct (dom_ok _ Dy1_) as [Fy1 Hy1]. destruct (dom_ok _ Dx1_) as [Fx1 Hx1].
  destruct (dom_ok _ Dy0_) as [Fy0 Hy0]. destruct (dom_ok _ Dx0_) as [Fx0 Hx0].
  unfold b64_liang_barsky_touches in Hs. cbv zeta in Hs.
  apply Bool.andb_true_iff in Hs. destruct Hs as [Hab Hcmp].
  apply Bool.andb_true_iff in Hab. destruct Hab as [HA HB].
  apply Rle_bool_elim in Hcmp.
  apply Bool.andb_true_iff. split.
  - apply Bool.andb_true_iff. split.
    + exact (g_axis_guard_ok _ _ _ Fx0 Fx1 Fcx Hx0 Hx1 Hcx HA).
    + exact (g_axis_guard_ok _ _ _ Fy0 Fy1 Fcy Hy0 Hy1 Hcy HB).
  - pose proof (g_axis_lo_ok _ _ _ Fx0 Fx1 Fcx Hx0 Hx1 Hcx) as Lx.
    pose proof (g_axis_lo_ok _ _ _ Fy0 Fy1 Fcy Hy0 Hy1 Hcy) as Ly.
    pose proof (g_axis_hi_ok _ _ _ Fx0 Fx1 Fcx Hx0 Hx1 Hcx) as Ux.
    pose proof (g_axis_hi_ok _ _ _ Fy0 Fy1 Fcy Hy0 Hy1 Hcy) as Uy.
    destruct (ub_max_ok b64_zero (g_axis_lo (bx P0) (bx P1) (bx C)) 0
                (lb_tlo (B2R (bx P0)) (B2R (bx P1))
                   (B2R (bx C) - / 2) (B2R (bx C) + / 2))
                is_finite_b64_zero ltac:(rewrite B2R_b64_zero; lra) Lx)
      as [F1 B1].
    destruct (ub_max_ok (ub_max b64_zero (g_axis_lo (bx P0) (bx P1) (bx C)))
                (g_axis_lo (by_ P0) (by_ P1) (by_ C))
                (Rmax 0 (lb_tlo (B2R (bx P0)) (B2R (bx P1))
                   (B2R (bx C) - / 2) (B2R (bx C) + / 2)))
                (lb_tlo (B2R (by_ P0)) (B2R (by_ P1))
                   (B2R (by_ C) - / 2) (B2R (by_ C) + / 2))
                F1 B1 Ly) as [F2 B2].
    destruct B2R_and_finite_b64_one as [Bone Fone].
    destruct (ub_min_ok b64_one (g_axis_hi (bx P0) (bx P1) (bx C)) 1
                (lb_thi (B2R (bx P0)) (B2R (bx P1))
                   (B2R (bx C) - / 2) (B2R (bx C) + / 2))
                Fone ltac:(rewrite Bone; lra) Ux) as [F3 B3].
    destruct (ub_min_ok (ub_min b64_one (g_axis_hi (bx P0) (bx P1) (bx C)))
                (g_axis_hi (by_ P0) (by_ P1) (by_ C))
                (Rmin 1 (lb_thi (B2R (bx P0)) (B2R (bx P1))
                   (B2R (bx C) - / 2) (B2R (bx C) + / 2)))
                (lb_thi (B2R (by_ P0)) (B2R (by_ P1))
                   (B2R (by_ C) - / 2) (B2R (by_ C) + / 2))
                F3 B3 Uy) as [F4 B4].
    apply b64_le_complete; [exact F2 | exact F4|].
    rewrite <- Rmax_assoc in B2. rewrite <- Rmin_assoc in B4.
    eapply Rle_trans; [exact B2|].
    eapply Rle_trans; [exact Hcmp | exact B4].
Qed.


End Generic.

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
