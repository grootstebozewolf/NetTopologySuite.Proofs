(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Orient_b64_Ozaki
   ----------------------------------------------------------------------------
   Phase 0 -- Ozaki/Rump gamma_2 filter soundness for `b64_orient2d`.

   Formal certificate for the Ozaki et al. (2012) -style orient2d filter
   adopted by JTS PR locationtech/jts#1093.  The filter threshold is

       |fl(det)| > gamma_2 * (|fl(t1)| + |fl(t2)|)

   with `gamma_n = n * u / (1 - n * u)` and `u = 2^-prec = 2^-53` the
   binary64 unit roundoff (Higham, "Accuracy and Stability of Numerical
   Algorithms", ch.3; Ozaki/Ogita/Rump/Oishi 2012, eq.(15)).  The two
   product terms `t1 := dx1 * dy1` and `t2 := dx2 * dy2` are the
   intermediate values computed by `b64_orient2d_terms`, where
   `dx1, dy1, dx2, dy2` are the four binary64 coordinate differences.

   Interpretation discipline (matches the existing
   `b64_orient_sign_stage_d_sound`): the predicate decides the *sign of
   the exact mathematical determinant `cross_R_BP` of the actual double
   inputs*, NOT "approximately collinear up to decimal rounding".  The
   tolerance-based variant for the decimal-input failure modes is a
   separate predicate; see the comment block at the foot of this file.

   DELIVERABLES
   ------------
     1. `b64_unit_roundoff`, `b64_gamma2`              -- definitions.
     2. `b64_gamma2_pos`, `b64_gamma2_lt_1`            -- structural bounds.
     3. `b64_orient2d_ozaki_err_R`                     -- the R-valued filter
                                                        threshold expression.
     4. `b64_ozaki_filter_sound_generic`               -- abstract soundness:
                                                        given any error
                                                        bound + the filter
                                                        check, signs match.
     5. `b64_orient2d_ozaki_filter_sound_small_int`    -- headline soundness
                                                        in the integer regime
                                                        (composes via
                                                        `b64_orient2d_exact_for_small_int`).

   Out of scope for this file (deferred slice -- the Shewchuk Stage A
   forward-error chain, sibling to the prose at the foot of
   `Orient_b64_sound.v`): the general-regime instantiation of (4) with a
   concrete `gamma_2`-shaped bound on `|B2R det - cross_R_BP|`.  That
   bound requires the normal-range relative-error lemma chain
   (`relative_error_N_FLT`-style) threaded through the four `b64_minus`,
   two `b64_mult`, outer `b64_minus` operations, which is its own
   multi-session engagement.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Lra.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import IEEE754.BinarySingleNaN.
From Flocq Require Import Core.

From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import B64_bridge.
From NTS.Proofs.Flocq Require Import B64_lib.
From NTS.Proofs.Flocq Require Import Orientation_b64.
From NTS.Proofs.Flocq Require Import Orient_b64_R.
From NTS.Proofs.Flocq Require Import Orient_b64_sound.
From NTS.Proofs.Flocq Require Import Orient_b64_exact.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Unit roundoff and gamma_2 constant.                                        *)
(*                                                                            *)
(* `u = 2^-prec = 2^-53` is the binary64 unit roundoff (half the spacing at  *)
(* 1.0).  `gamma_2 = 2u / (1 - 2u)` is the Ozaki/Rump constant for the       *)
(* 2-term sum-of-products error budget.                                       *)
(*                                                                            *)
(* Numerically:                                                              *)
(*   u       ~= 1.11e-16                                                     *)
(*   gamma_2 ~= 2.22e-16                                                     *)
(*                                                                            *)
(* Compare Shewchuk's Stage A coefficient `(3 + 16 * eps) * eps` (defined    *)
(* in `Orientation_b64.v`), which is ~6.66e-16 -- the Ozaki bound is        *)
(* roughly 3x tighter, the headline of the JTS PR.                          *)
(*                                                                            *)
(* Concrete-rational form: `bpow radix2 (- prec)` is definitionally equal   *)
(* to `/ IZR (Z.pow_pos 2 53)` (same pattern as `eps_b64_eq_bpow` from      *)
(* `B64_FastExpansionSum_Shewchuk_Route2.v`); the `_eq_inv` lemma makes      *)
(* this available to `lra` via the explicit IZR comparison.                  *)
(* -------------------------------------------------------------------------- *)

Definition b64_unit_roundoff : R := bpow radix2 (- prec).

Definition b64_gamma2 : R :=
  2 * b64_unit_roundoff / (1 - 2 * b64_unit_roundoff).

Lemma b64_unit_roundoff_eq_inv :
  b64_unit_roundoff = / IZR (Z.pow_pos 2 53).
Proof. unfold b64_unit_roundoff, prec. reflexivity. Qed.

Lemma b64_unit_roundoff_pos : 0 < b64_unit_roundoff.
Proof. unfold b64_unit_roundoff. apply bpow_gt_0. Qed.

(* Headroom bound: `u < / 8`.  Tight enough that `1 - 2u`, `1 - 4u`, etc.,  *)
(* all stay positive; downstream `lra` calls close on this single fact.    *)
Lemma b64_unit_roundoff_lt_eighth : b64_unit_roundoff < / 8.
Proof.
  rewrite b64_unit_roundoff_eq_inv.
  apply Rinv_lt_contravar.
  - apply Rmult_lt_0_compat; [lra | apply IZR_lt; lia].
  - apply IZR_lt. lia.
Qed.

Lemma b64_gamma2_pos : 0 < b64_gamma2.
Proof.
  unfold b64_gamma2.
  pose proof b64_unit_roundoff_pos as Hu_pos.
  pose proof b64_unit_roundoff_lt_eighth as Hu_small.
  apply Rdiv_lt_0_compat; lra.
Qed.

Lemma b64_gamma2_lt_1 : b64_gamma2 < 1.
Proof.
  unfold b64_gamma2.
  pose proof b64_unit_roundoff_pos as Hu_pos.
  pose proof b64_unit_roundoff_lt_eighth as Hu_small.
  assert (Hden_pos : 0 < 1 - 2 * b64_unit_roundoff) by lra.
  unfold Rdiv.
  (* Goal: `2u * / (1 - 2u) < 1`.
     Strategy: bound the LHS by `(1 - 2u) * / (1 - 2u) = 1` via
     `Rmult_lt_compat_r` (numerator strict bound + positive inverse), then
     close via `Rinv_r`.  Avoids the `Rmult_assoc` rewriting ambiguity. *)
  apply (Rlt_le_trans _ ((1 - 2 * b64_unit_roundoff)
                          * / (1 - 2 * b64_unit_roundoff))).
  - apply Rmult_lt_compat_r.
    + apply Rinv_0_lt_compat. exact Hden_pos.
    + lra.
  - rewrite Rinv_r by lra. apply Rle_refl.
Qed.

(* -------------------------------------------------------------------------- *)
(* The Ozaki filter's R-valued error threshold.                              *)
(*                                                                            *)
(* `b64_orient2d_ozaki_err_R P0 P1 Q := gamma_2 * (|B2R t1| + |B2R t2|)`     *)
(* where `t1, t2` are the two product terms computed by                       *)
(* `b64_orient2d_terms`.  Lifted via `Binary.B2R` so the filter check is     *)
(* stated as a real-arithmetic inequality, matching the rest of the corpus.  *)
(* -------------------------------------------------------------------------- *)

Definition b64_orient2d_ozaki_err_R (P0 P1 Q : BPoint) : R :=
  let dx1 := b64_minus (bx P1) (bx P0) in
  let dy1 := b64_minus (by_ Q)  (by_ P0) in
  let dx2 := b64_minus (bx Q)   (bx P0) in
  let dy2 := b64_minus (by_ P1) (by_ P0) in
  b64_gamma2 *
    (Rabs (Binary.B2R prec emax (b64_mult dx1 dy1))
     + Rabs (Binary.B2R prec emax (b64_mult dx2 dy2))).

Lemma b64_orient2d_ozaki_err_R_nonneg :
  forall P0 P1 Q : BPoint, 0 <= b64_orient2d_ozaki_err_R P0 P1 Q.
Proof.
  intros P0 P1 Q.
  unfold b64_orient2d_ozaki_err_R.
  pose proof b64_gamma2_pos as Hg.
  pose proof (Rabs_pos (Binary.B2R prec emax
                (b64_mult (b64_minus (bx P1) (bx P0))
                          (b64_minus (by_ Q)  (by_ P0))))) as Ht1.
  pose proof (Rabs_pos (Binary.B2R prec emax
                (b64_mult (b64_minus (bx Q)  (bx P0))
                          (b64_minus (by_ P1) (by_ P0))))) as Ht2.
  apply Rmult_le_pos; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Abstract Ozaki filter soundness.                                           *)
(*                                                                            *)
(* The signs of a binary64 value `det` and an R-valued reference `det_R`     *)
(* agree whenever the forward error `|B2R det - det_R|` is bounded by some  *)
(* `err_bound` AND the filter check `|B2R det| > err_bound` succeeds.  No   *)
(* arithmetic structure on `err_bound` is required -- this is the generic   *)
(* same-sign lemma the gamma_2 filter (and Shewchuk's filter, and any        *)
(* future variant) instantiates.                                              *)
(*                                                                            *)
(* The structure exposes a clean composition discipline for any future       *)
(* forward-error theorem: pair it with this lemma to obtain a sign-          *)
(* correspondence theorem.  See `Orient_b64_sound.v`'s "Still pending"       *)
(* prose for the deferred slice that would supply the concrete gamma_2-      *)
(* shaped bound on `|B2R det - cross_R_BP|` in the general regime.           *)
(* -------------------------------------------------------------------------- *)

Lemma b64_ozaki_filter_sound_generic :
  forall (det : binary64) (det_R err_bound : R),
    Rabs (Binary.B2R prec emax det - det_R) <= err_bound ->
    Rabs (Binary.B2R prec emax det) > err_bound ->
    (0 < Binary.B2R prec emax det <-> 0 < det_R)
    /\ (Binary.B2R prec emax det < 0 <-> det_R < 0).
Proof.
  intros det det_R err_bound Herr Hfilt.
  set (d := Binary.B2R prec emax det) in *.
  (* From the abs-form Herr, get linear bounds plus `err_bound >= 0`. *)
  pose proof (Rabs_pos (d - det_R)) as Habs_dr_pos.
  assert (Herr_nonneg : 0 <= err_bound) by lra.
  apply Rabs_le_inv in Herr.
  destruct Herr as [Herr_lo Herr_hi].
  destruct (Rle_or_lt 0 d) as [Hd_nn | Hd_neg].
  - (* d >= 0: |d| = d, so Hfilt becomes `d > err_bound >= 0`. *)
    rewrite Rabs_pos_eq in Hfilt by exact Hd_nn.
    split; split; intro H; lra.
  - (* d < 0: |d| = -d, so Hfilt becomes `-d > err_bound`, i.e., d < -err_bound. *)
    rewrite Rabs_left in Hfilt by exact Hd_neg.
    split; split; intro H; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Headline: filter sound vs `cross_R_BP` in the small-int regime.            *)
(*                                                                            *)
(* In the integer regime (`orient2d_inputs_int_safe`), the corpus already    *)
(* proves `B2R (b64_orient2d P0 P1 Q) = cross_R_BP P0 P1 Q` exactly          *)
(* (`b64_orient2d_exact_for_small_int`).  The Ozaki filter check then        *)
(* transfers directly: the FP value equals the exact reference, so the       *)
(* sign correspondence is unconditional in this regime (the filter           *)
(* premise is satisfied vacuously).                                           *)
(*                                                                            *)
(* This is the FILTER-side analogue of                                        *)
(* `b64_orient_sign_filtered_sound_small_int`: same regime, same exact       *)
(* identity composition, different filter threshold (gamma_2 vs Shewchuk's   *)
(* (3 + 16 * eps) * eps).  The general-regime variant -- where the          *)
(* differences themselves carry rounding error -- is the deferred Slice 2c   *)
(* forward-error chain documented in `Orient_b64_sound.v`'s prose.           *)
(* -------------------------------------------------------------------------- *)

Theorem b64_orient2d_ozaki_filter_sound_small_int :
  forall P0 P1 Q : BPoint,
    orient2d_inputs_int_safe P0 P1 Q ->
    Rabs (Binary.B2R prec emax (b64_orient2d P0 P1 Q))
      > b64_orient2d_ozaki_err_R P0 P1 Q ->
    (0 < Binary.B2R prec emax (b64_orient2d P0 P1 Q)
       <-> 0 < cross_R_BP P0 P1 Q)
    /\ (Binary.B2R prec emax (b64_orient2d P0 P1 Q) < 0
       <-> cross_R_BP P0 P1 Q < 0).
Proof.
  intros P0 P1 Q Hint _Hfilt.
  pose proof (b64_orient2d_exact_for_small_int _ _ _ Hint) as Hexact.
  rewrite Hexact.
  split; split; intro H; exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* Tolerance-based variant (out of scope for this file).                      *)
(*                                                                            *)
(* The headline above answers "correct sign of the exact determinant of the  *)
(* actual double inputs", matching the discipline of                          *)
(* `b64_orient_sign_stage_d_sound`.  The separate predicate the JTS          *)
(* maintainer mentioned -- "tolerance-based algorithms as a workaround" for *)
(* the decimal-to-double rounding failure that the failure_viewer            *)
(* demonstrates -- is a different theorem with a different specification.   *)
(* The corpus's Phase 1 `HasIntersect_sound` K*eps framework is the natural *)
(* foundation for that follow-up.                                             *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                              *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_gamma2_pos.
Print Assumptions b64_gamma2_lt_1.
Print Assumptions b64_orient2d_ozaki_err_R_nonneg.
Print Assumptions b64_ozaki_filter_sound_generic.
Print Assumptions b64_orient2d_ozaki_filter_sound_small_int.
