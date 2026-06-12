(* ============================================================================
   NetTopologySuite.Proofs.ClothoidHalley
   ----------------------------------------------------------------------------
   Route (C') conditional bounded-iteration interface for Halley-on-L on the
   clothoid chord-length residual.

   Companion: clothoid-halley-coq Clothoid.Halley/Solver.cs (EUPL-1.2).
   Problem order in oracle vectors: (k0, k1, L); assembly uses d2, L, and
   the six moment scalars P, Q, R, T, S2c, S2s evaluated at the current L.

   This file does NOT internalise Fresnel/quadrature moments (route D).  It
   supplies:
     - the Solver.cs polynomial assembly (f, f', f'');
     - one Halley update step with the reference safety heuristics;
     - a fuel-bounded iteration skeleton (structural termination);
     - a conditional <=4-iteration headline discharged as a named Section
       hypothesis, witnessed by the 9,058-record golden_vectors corpus
       (docs/audit-phase4-curves.md section 6.1, table 3).

   Structural idiom mirrors theories/ClothoidResidual.v and
   theories-flocq/HobbyTheorem_b64.v: hard analytic / empirical facts are
   premises, not Admitted.

   No Admitted, no Axiom, no Parameter.
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lia.
From Stdlib Require Import Lra.
From Stdlib Require Import Rfunctions.

From NTS.Proofs Require Import Real.
From NTS.Proofs Require Import ClothoidDegenerate.

Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Polynomial assembly (Solver.cs residual block).                              *)
(* -------------------------------------------------------------------------- *)

Definition clothoid_r2 (P Q : R) : R := P * P + Q * Q.

Definition clothoid_f (d2 L P Q : R) : R :=
  L * L * clothoid_r2 P Q - d2.

Definition clothoid_fp (L P Q Rm T : R) : R :=
  2 * L * clothoid_r2 P Q + 2 * L * L * (Q * Rm - P * T).

Definition clothoid_fpp (L P Q Rm T S2c S2s : R) : R :=
  2 * clothoid_r2 P Q
  + 8 * L * (Q * Rm - P * T)
  + 2 * L * L * (Rm * Rm + T * T - P * S2c - Q * S2s).

Definition clothoid_tol_scale (d2 : R) : R := Rmax d2 1.

Definition clothoid_converged (f d2 tol : R) : Prop :=
  Rabs f < tol * clothoid_tol_scale d2.

Definition clothoid_converged_bool (f d2 tol : R) : bool :=
  if Rlt_dec (Rabs f) (tol * clothoid_tol_scale d2) then true else false.

Definition clothoid_halley_denom (f fp fpp : R) : R :=
  2 * fp * fp - f * fpp.

Definition clothoid_halley_step (f fp fpp : R) : R :=
  2 * f * fp / clothoid_halley_denom f fp fpp.

Definition clothoid_halley_denom_guard (denom fp : R) : Prop :=
  denom <> 0 /\ 0 < fp.

Definition clothoid_halley_l_new (L f fp fpp : R) : R :=
  let step := clothoid_halley_step f fp fpp in
  let raw := L - step in
  if Rle_dec raw 0 then 0.5 * L else raw.

Definition clothoid_halley_l_fallback (L : R) : R := 1.5 * L.

(* Six moment scalars at the current iterate (oracle-supplied / quadrature). *)
Record clothoid_moments : Type := MkClothoidMoments {
  cmP : R;
  cmQ : R;
  cmR : R;
  cmT : R;
  cmS2c : R;
  cmS2s : R
}.

Definition clothoid_eval_moments (mom : R -> clothoid_moments) (L : R) :=
  mom L.

Definition clothoid_residual_at (d2 : R) (mom : R -> clothoid_moments) (L : R) :=
  let m := clothoid_eval_moments mom L in
  clothoid_f d2 L (cmP m) (cmQ m).

Definition clothoid_fp_at (mom : R -> clothoid_moments) (L : R) :=
  let m := clothoid_eval_moments mom L in
  clothoid_fp L (cmP m) (cmQ m) (cmR m) (cmT m).

Definition clothoid_fpp_at (mom : R -> clothoid_moments) (L : R) :=
  let m := clothoid_eval_moments mom L in
  clothoid_fpp L (cmP m) (cmQ m) (cmR m) (cmT m) (cmS2c m) (cmS2s m).

Definition clothoid_halley_denom_guard_bool (denom fp : R) : bool :=
  if Rgt_dec fp 0 then
    if Rgt_dec (Rabs denom) 0 then true else false
  else false.

Definition clothoid_halley_l_update (d2 tol : R) (mom : R -> clothoid_moments)
  (L : R) : R :=
  let f := clothoid_residual_at d2 mom L in
  let fp := clothoid_fp_at mom L in
  let fpp := clothoid_fpp_at mom L in
  let denom := clothoid_halley_denom f fp fpp in
  if clothoid_converged_bool f d2 tol then L
  else if clothoid_halley_denom_guard_bool denom fp then clothoid_halley_l_new L f fp fpp
  else clothoid_halley_l_fallback L.

Fixpoint clothoid_halley_fuel (fuel : nat) (L : R) (d2 tol : R)
  (mom : R -> clothoid_moments) : R :=
  match fuel with
  | O => L
  | S fuel' =>
      clothoid_halley_fuel fuel'
        (clothoid_halley_l_update d2 tol mom L) d2 tol mom
  end.

Definition clothoid_halley_max_iter_default : nat := 50.

Definition clothoid_halley_corpus_iter_bound : nat := 4.

(* -------------------------------------------------------------------------- *)
(* Structural lemmas.                                                         *)
(* -------------------------------------------------------------------------- *)

Lemma clothoid_tol_scale_pos : forall d2, 0 < clothoid_tol_scale d2.
Proof.
  intro d2. unfold clothoid_tol_scale.
  rewrite Rmax_comm.
  pose proof (Rmax_l 1 d2) as H1.
  lra.
Qed.

Lemma clothoid_converged_zero :
  forall d2 tol, 0 < tol -> clothoid_converged 0 d2 tol.
Proof.
  intros d2 tol Htol.
  unfold clothoid_converged.
  rewrite Rabs_R0.
  apply Rmult_lt_0_compat; [exact Htol | apply clothoid_tol_scale_pos].
Qed.

(* -------------------------------------------------------------------------- *)
(* Degenerate straight-chord witness (route A composition).                   *)
(* -------------------------------------------------------------------------- *)

Definition degenerate_moments (_ : R) : clothoid_moments :=
  MkClothoidMoments 1 0 0 0 0 0.

Lemma degenerate_residual_at_chord :
  forall d L, 0 < d ->
    clothoid_residual_at (d * d) degenerate_moments L =
    degenerate_residual d L.
Proof.
  intros d L _.
  unfold clothoid_residual_at, degenerate_moments, clothoid_f, clothoid_r2,
         degenerate_residual.
  simpl. ring.
Qed.

Lemma degenerate_halley_fixed_at_root :
  forall d tol, 0 < d -> 0 < tol ->
    clothoid_halley_l_update (d * d) tol degenerate_moments d = d.
Proof.
  intros d tol Hd Htol.
  unfold clothoid_halley_l_update.
  set (f := clothoid_residual_at (d * d) degenerate_moments d).
  assert (Hf : f = 0).
  { subst f. rewrite degenerate_residual_at_chord; [ | exact Hd ]. apply degenerate_root_exact. }
  assert (Hcb : clothoid_converged_bool f (d * d) tol = true).
  {
    unfold clothoid_converged_bool.
    rewrite Hf, Rabs_R0.
    destruct (Rlt_dec 0 (tol * clothoid_tol_scale (d * d))) as [Hlt | Hnlt].
    - reflexivity.
    - exfalso. apply Hnlt. apply Rmult_lt_0_compat; [exact Htol | apply clothoid_tol_scale_pos].
  }
  simpl. rewrite Hcb. reflexivity.
Qed.

Lemma degenerate_halley_converged_at_chord :
  forall d tol, 0 < d -> 0 < tol ->
    clothoid_converged
      (clothoid_residual_at (d * d) degenerate_moments d) (d * d) tol.
Proof.
  intros d tol Hd Htol.
  rewrite degenerate_residual_at_chord; [ | exact Hd ].
  rewrite degenerate_root_exact.
  apply clothoid_converged_zero. exact Htol.
Qed.

(* -------------------------------------------------------------------------- *)
(* Conditional <=4-iteration interface (corpus witness).                      *)
(*                                                                            *)
(* Pin: clothoid-halley-coq data/golden_vectors.json (9,058 ProRail records,  *)
(*      iteration counts <= 4 on the filtered monotone-branch pipeline).      *)
(* -------------------------------------------------------------------------- *)

Section ClothoidHalleyCorpusBound.

Variable Problem : Type.
Variable iterations_used : Problem -> nat.
Variable solve_L : Problem -> R.

Hypothesis H_iterations_le_max :
  forall p : Problem,
    (iterations_used p <= clothoid_halley_max_iter_default)%nat.

Hypothesis H_filtered_corpus_le_four :
  forall p : Problem,
    (iterations_used p <= clothoid_halley_corpus_iter_bound)%nat.

Theorem clothoid_halley_filtered_corpus_le_four :
  forall p : Problem,
    (iterations_used p <= clothoid_halley_corpus_iter_bound)%nat.
Proof. intro p. apply H_filtered_corpus_le_four. Qed.

Theorem clothoid_halley_filtered_corpus_le_max :
  forall p : Problem,
    (iterations_used p <= clothoid_halley_max_iter_default)%nat.
Proof. intro p. apply H_iterations_le_max. Qed.

End ClothoidHalleyCorpusBound.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                               *)
(* -------------------------------------------------------------------------- *)

Print Assumptions clothoid_halley_filtered_corpus_le_four.
Print Assumptions degenerate_halley_fixed_at_root.