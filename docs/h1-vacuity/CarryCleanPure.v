(* CarryCleanPure.v -- the "pure finite-sequence" carry_clean theorem.
   No floating point: signed dyadics (reals of the form m*2^k), exact rewrites
   only.  Outcome: QED, arbitrary length -- and VACUOUS for the real bridge:
   Priest's relation forces strictly decreasing magnitudes (priest_lt), so a
   zero-free Priest chain is already a normal form of the rewrite system and
   carry_clean is the identity on it.  carry_clean only matters on
   fast_expansion_sum output, which is not a Priest chain.
   NOT CITABLE.  The rewrite system `steps` is not the product carry_clean
   (B64_CarryCleanAlgo.v) and no lemma links the two; the result is vacuous.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human-reviewed (2026-11-10, J. Bloemscheer, on main @ 4eb6c4b6):
     rung 0, signed off as vacuous and not citable.
     Assisted-by: Claude
*)
From Stdlib Require Import Reals ZArith Lia Lra List.
From Flocq Require Import Core.
Import ListNotations.
Local Open Scope R_scope.

Section Pure.
Variable p : Z.
Hypothesis Hp : (1 <= p)%Z.

(* Priest's condition on x above y: both normalised to p-bit mantissas,
   exponent gap >= p (B64_Overlap_Hierarchy.priest_nonoverlapping_R, with
   prec generalised to p). *)
Definition priest (x y : R) : Prop :=
  exists (mx my kx ky : Z),
    x = IZR mx * bpow radix2 kx /\ y = IZR my * bpow radix2 ky /\
    bpow radix2 (p - 1) <= Rabs (IZR mx) < bpow radix2 p /\
    bpow radix2 (p - 1) <= Rabs (IZR my) < bpow radix2 p /\
    (kx - ky >= p)%Z.

Fixpoint priest_seq (e : list R) : Prop :=
  match e with
  | nil | _ :: nil => True
  | a :: (b :: _) as r => priest a b /\ priest_seq r
  end.

(* Shewchuk's nonoverlap (lowest bit of x above the top bit of y). *)
Definition nonov (x y : R) : Prop :=
  exists (r s : Z), x = IZR r * bpow radix2 s /\ Rabs y < bpow radix2 s.

Fixpoint nonov_seq (e : list R) : Prop :=
  match e with
  | nil | _ :: nil => True
  | a :: (b :: _) as r => nonov a b /\ nonov_seq r
  end.

(* The exact rewrites, anywhere in the sequence; no rounding exists. *)
Inductive step : list R -> list R -> Prop :=
  | s_zero  : forall l1 l2, step (l1 ++ 0 :: l2) (l1 ++ l2)
  | s_anti  : forall l1 x l2, step (l1 ++ x :: (-x) :: l2) (l1 ++ l2)
  | s_twin  : forall l1 x l2, step (l1 ++ x :: x :: l2) (l1 ++ (2 * x) :: l2).

Inductive steps : list R -> list R -> Prop :=
  | st_refl : forall l, steps l l
  | st_step : forall l m n, step l m -> steps m n -> steps l n.

Fixpoint sumR (l : list R) : R :=
  match l with nil => 0 | x :: r => x + sumR r end.

Lemma sumR_app : forall a b, sumR (a ++ b) = sumR a + sumR b.
Proof. induction a; cbn; intros; [ lra | rewrite IHa; lra ]. Qed.

(* 1. value preservation *)
Lemma step_sum : forall l m, step l m -> sumR l = sumR m.
Proof.
  intros l m []; rewrite ?sumR_app; cbn; lra.
Qed.
Lemma steps_sum : forall l m, steps l m -> sumR l = sumR m.
Proof. intros l m H; induction H; [ reflexivity | rewrite <- IHsteps; apply step_sum; exact H ]. Qed.

(* 2. termination: the length strictly decreases at every step. *)
Lemma step_len : forall l m, step l m -> (length m < length l)%nat.
Proof. intros l m []; rewrite ?length_app; cbn; lia. Qed.
Lemma step_wf : well_founded (fun m l => step l m).
Proof.
  intro l. remember (length l) as n eqn:Hn. revert l Hn.
  induction n using lt_wf_ind; intros l Hn. constructor. intros m Hm.
  eapply H; [ | reflexivity ]. pose proof (step_len _ _ Hm). lia.
Qed.

(* Priest's relation forces strictly decreasing, nonzero magnitudes. *)
Lemma priest_lt : forall x y, priest x y -> Rabs y < Rabs x.
Proof.
  intros x y (mx & my & kx & ky & Hx & Hy & [Hx1 Hx2] & [Hy1 Hy2] & Hk).
  rewrite Hx, Hy, !Rabs_mult, !(Rabs_right (bpow radix2 _)) by (apply Rle_ge, bpow_ge_0).
  assert (Hb : bpow radix2 (p + ky) <= bpow radix2 kx) by (apply bpow_le; lia).
  assert (H1 : bpow radix2 (p - 1) * bpow radix2 kx
               = bpow radix2 (p - 1 + kx)) by (rewrite bpow_plus; reflexivity).
  assert (H2 : bpow radix2 p * bpow radix2 ky = bpow radix2 (p + ky))
    by (rewrite bpow_plus; reflexivity).
  assert (H3 : bpow radix2 kx <= bpow radix2 (p - 1) * bpow radix2 kx).
  { rewrite H1. apply bpow_le. lia. }
  assert (Hky := bpow_gt_0 radix2 ky). assert (Hkx := bpow_gt_0 radix2 kx).
  assert (Hy3 : Rabs (IZR my) * bpow radix2 ky < bpow radix2 p * bpow radix2 ky)
    by (apply Rmult_lt_compat_r; assumption).
  assert (Hx3 : bpow radix2 (p - 1) * bpow radix2 kx
                <= Rabs (IZR mx) * bpow radix2 kx)
    by (apply Rmult_le_compat_r; [ lra | assumption ]).
  lra.
Qed.

(* A Priest chain has pairwise strictly decreasing magnitudes. *)
Lemma priest_seq_head_lt :
  forall a b r, priest_seq (a :: b :: r) -> Rabs b < Rabs a.
Proof. intros a b r [H _]. apply priest_lt, H. Qed.

Lemma priest_seq_app_r : forall l1 l2, priest_seq (l1 ++ l2) -> priest_seq l2.
Proof.
  induction l1 as [| a l1 IH]; intros l2 H; [ exact H | ].
  apply IH. cbn in H. destruct (l1 ++ l2) as [| b r]; [ exact I | apply H ].
Qed.

Lemma priest_seq_nonzero_head :
  forall a b r, priest_seq (a :: b :: r) -> a <> 0 /\ b <> 0.
Proof.
  intros a b r [(mx & my & kx & ky & Hx & Hy & [Hx1 Hx2] & [Hy1 Hy2] & _) _].
  assert (Hpos : forall m k, bpow radix2 (p - 1) <= Rabs (IZR m) ->
                   IZR m * bpow radix2 k <> 0).
  { intros m k H Hz. apply Rmult_integral in Hz as [Hz | Hz].
    - rewrite Hz, Rabs_R0 in H. pose proof (bpow_gt_0 radix2 (p - 1)). lra.
    - pose proof (bpow_gt_0 radix2 k). lra. }
  split; [ rewrite Hx | rewrite Hy ]; apply Hpos; assumption.
Qed.

(* Core: no step applies to a nonzero Priest chain.  (Priest's relation
   already forces both members of a pair to be nonzero; only the singleton
   [0] is vacuously a chain, and it just reduces to [].) *)
Theorem priest_seq_irreducible :
  forall e m, priest_seq e -> Forall (fun x => x <> 0) e -> ~ step e m.
Proof.
  intros e m He Hz Hs. destruct Hs as [l1 l2 | l1 x l2 | l1 x l2].
  - apply Forall_app in Hz as [_ Hz]. inversion Hz as [| ? ? H0 _]. apply H0. reflexivity.
  - apply priest_seq_app_r in He. apply priest_seq_head_lt in He.
    rewrite Rabs_Ropp in He. lra.
  - apply priest_seq_app_r in He. apply priest_seq_head_lt in He. lra.
Qed.

(* Zero-free chains are normal forms: any rewriting sequence is empty. *)
Corollary C_of_priest :
  forall e e', priest_seq e -> Forall (fun x => x <> 0) e -> steps e e' -> e' = e.
Proof.
  intros e e' He Hz Hs. inversion Hs; subst; [ reflexivity | ].
  exfalso. eapply priest_seq_irreducible; eauto.
Qed.

(* Priest => Shewchuk, pairwise. *)
Lemma priest_nonov : forall x y, priest x y -> nonov x y.
Proof.
  intros x y (mx & my & kx & ky & Hx & Hy & [_ Hx2] & [Hy1 Hy2] & Hk).
  exists mx, kx. split; [ exact Hx | ].
  rewrite Hy, Rabs_mult, (Rabs_right (bpow radix2 ky)) by (apply Rle_ge, bpow_ge_0).
  apply Rlt_le_trans with (bpow radix2 p * bpow radix2 ky).
  - apply Rmult_lt_compat_r; [ apply bpow_gt_0 | exact Hy2 ].
  - rewrite <- bpow_plus. apply bpow_le. lia.
Qed.

Lemma priest_seq_nonov_seq : forall e, priest_seq e -> nonov_seq e.
Proof.
  induction e as [| a r IH]; [ intros; exact I | ].
  destruct r as [| b r']; [ intros; exact I | ].
  intros [H1 H2]. split; [ apply priest_nonov, H1 | apply IH, H2 ].
Qed.

(* THE THEOREM, arbitrary length: value preserved and nonoverlap preserved
   -- the latter because the rewriting is the identity.  Termination of
   `steps` is the separate lemma step_wf, not part of this statement. *)
Theorem carry_clean_pure :
  forall e, priest_seq e -> Forall (fun x => x <> 0) e ->
    (forall e', steps e e' -> sumR e' = sumR e /\ e' = e /\ nonov_seq e').
Proof.
  intros e He Hz e' Hs. pose proof (C_of_priest e e' He Hz Hs) as ->.
  split; [ reflexivity | split; [ reflexivity | apply priest_seq_nonov_seq, He ] ].
Qed.
End Pure.

Print Assumptions carry_clean_pure.
Print Assumptions step_wf.
