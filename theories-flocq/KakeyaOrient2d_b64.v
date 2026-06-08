(* ============================================================================
   NetTopologySuite.Proofs.Flocq.KakeyaOrient2d_b64
   ----------------------------------------------------------------------------
   Stage D orient2d, exercised on the Besicovitch-Kakeya "gnarlies": a concrete
   integer-coordinate, near-degenerate (here, EXACTLY collinear) triangle of the
   kind the Perron-tree construction produces, run through the integer-safe
   expansion predicate.

   The Perron triangles (theories/PerronStage.v) live over rationals k/2^n.
   Scaled by 2^(n+1) their vertices are integers and orient2d's SIGN is
   unchanged (cross is scale-equivariant with a positive factor).  So the gnarly
   orientation question is an integer-coordinate problem, and the merged
   integer-safe expansion sign-correctness
   (`b64_orient2d_expansion_int_sign_correct_coords`, Orient_b64_int_safe_coords)
   applies -- WITHOUT the deferred general
   `fast_expansion_sum_nonoverlap_shewchuk`.

   This file ships:
     - `b64Z` : a binary64 from an integer, with `B2R = IZR` and the integer
       contract on the |m| <= 2^25 window (`b64Z_coord_int_safe`).
     - `kakeya_P0/P1/Q` : a concrete integer triple, exactly collinear -- the
       hardest orient2d case (floating filters are non-decisive; the exact
       predicate must return "collinear").
     - `kakeya_inputs_int_safe` : the triple meets `orient2d_inputs_int_safe`.
     - `kakeya_cross_zero` : its exact `cross_R_BP` is 0 (the geometric fact).
     - `kakeya_orient2d_sign_zero` : the integer-safe expansion predicate returns
       `ExpZero` on it -- CONDITIONAL on `b64_orient2d_expansion_safe` (the
       per-op no-overflow bundle).  Discharging that bundle from
       `orient2d_inputs_int_safe` (the bounded-coordinate Dekker-safety assembly)
       is the documented remaining step; it needs no new mathematics, only the
       `b64_safe_*_of_bounded` helpers (B64_bridge) applied across the two
       Dekker chains and the fast-expansion-sum.

   Pure-Flocq (binary64); no `Admitted` / `Axiom` / `Parameter` introduced; no
   dependence on the deferred headline.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lia Lra.
From Flocq Require Import IEEE754.Binary IEEE754.BinarySingleNaN Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
                                     Orient_b64_sound B64_Expansion
                                     B64_Expansion_Shewchuk B64_Pff_bridge
                                     Orient_b64_exact Orient_b64_expansion
                                     Orient_b64_int_safe Orient_b64_int_safe_coords.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* A binary64 holding an integer.                                             *)
(* -------------------------------------------------------------------------- *)

Definition b64Z (m : Z) : binary64 :=
  Binary.binary_normalize prec emax prec_gt_0_b64 prec_lt_emax_b64
    mode_NE m 0 false.

Lemma b64Z_R :
  forall m : Z, (Z.abs m <= 2 ^ 53)%Z ->
    Binary.B2R prec emax (b64Z m) = IZR m
    /\ Binary.is_finite prec emax (b64Z m) = true.
Proof.
  intros m Hm. unfold b64Z.
  pose proof (Binary.binary_normalize_correct prec emax
                prec_gt_0_b64 prec_lt_emax_b64 mode_NE m 0 false) as H.
  assert (HF2R : F2R (Float radix2 m 0) = IZR m).
  { unfold F2R; simpl. lra. }
  rewrite HF2R in H.
  assert (Hround : Generic_fmt.round radix2 (SpecFloat.fexp prec emax)
                     (round_mode mode_NE) (IZR m) = IZR m).
  { apply Generic_fmt.round_generic; [apply valid_rnd_round_mode |].
    apply generic_format_IZR_le_bpow_prec. unfold prec; lia. }
  rewrite Hround in H.
  assert (Hbnd : Rabs (IZR m) < bpow radix2 emax).
  { rewrite <- abs_IZR.
    apply (Rle_lt_trans _ (bpow radix2 53)).
    - rewrite bpow_radix2_eq_IZR_pow by lia. apply IZR_le. exact Hm.
    - apply bpow_lt; unfold emax; lia. }
  apply Rlt_bool_true in Hbnd. rewrite Hbnd in H.
  destruct H as [HB2R [Hfin _]]. split; assumption.
Qed.

Lemma b64Z_coord_int_safe :
  forall m : Z, (Z.abs m <= 2 ^ 25)%Z -> coord_int_safe (b64Z m).
Proof.
  intros m Hm.
  destruct (b64Z_R m ltac:(lia)) as [HR Hf].
  split; [ exact Hf | exists m; split; [ exact HR | exact Hm ] ].
Qed.

(* -------------------------------------------------------------------------- *)
(* A concrete gnarly triple: exactly collinear, integer coordinates.          *)
(*                                                                            *)
(*   P0 = (0, 0)   P1 = (2^21, 1)   Q = (2^22, 2)                              *)
(*                                                                            *)
(* These lie on the line y = x / 2^21, so cross = 0.  All coordinates are     *)
(* <= 2^22 < 2^25.  (This is the integer-scaled image of three collinear      *)
(* points of the Perron base line -- the orientation question that the thin   *)
(* slivers force.)                                                             *)
(* -------------------------------------------------------------------------- *)

Definition kakeya_P0 : BPoint := mkBP (b64Z 0)       (b64Z 0).
Definition kakeya_P1 : BPoint := mkBP (b64Z (2 ^ 21)) (b64Z 1).
Definition kakeya_Q  : BPoint := mkBP (b64Z (2 ^ 22)) (b64Z 2).

Lemma kakeya_inputs_int_safe :
  orient2d_inputs_int_safe kakeya_P0 kakeya_P1 kakeya_Q.
Proof.
  unfold orient2d_inputs_int_safe, kakeya_P0, kakeya_P1, kakeya_Q; cbn [bx by_].
  repeat split; apply b64Z_coord_int_safe; lia.
Qed.

(* The exact orientation: collinear. *)
Lemma kakeya_cross_zero :
  cross_R_BP kakeya_P0 kakeya_P1 kakeya_Q = 0.
Proof.
  unfold cross_R_BP, kakeya_P0, kakeya_P1, kakeya_Q; cbn [bx by_].
  rewrite (proj1 (b64Z_R 0 ltac:(lia))).
  rewrite (proj1 (b64Z_R (2 ^ 21) ltac:(lia))).
  rewrite (proj1 (b64Z_R 1 ltac:(lia))).
  rewrite (proj1 (b64Z_R (2 ^ 22) ltac:(lia))).
  rewrite (proj1 (b64Z_R 2 ltac:(lia))).
  rewrite <- !minus_IZR, <- !mult_IZR, <- minus_IZR.
  replace (((2 ^ 21) - 0) * (2 - 0) - ((2 ^ 22) - 0) * (1 - 0))%Z with 0%Z by lia.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* The integer-safe expansion predicate returns ExpZero on the gnarly triple. *)
(*                                                                            *)
(* CONDITIONAL on b64_orient2d_expansion_safe (the per-op no-overflow bundle); *)
(* see header for the discharge plan.  The point: GIVEN safety, the exact      *)
(* expansion predicate is decisive and correct (ExpZero = collinear) on a      *)
(* configuration where floating-point filters are not.                        *)
(* -------------------------------------------------------------------------- *)

Theorem kakeya_orient2d_sign_zero :
  b64_orient2d_expansion_safe kakeya_P0 kakeya_P1 kakeya_Q ->
  b64_orient2d_expansion_sign kakeya_P0 kakeya_P1 kakeya_Q = ExpZero.
Proof.
  intros Hsafe.
  pose proof (b64_orient2d_expansion_int_sign_correct_coords
                kakeya_P0 kakeya_P1 kakeya_Q kakeya_inputs_int_safe Hsafe) as Hsign.
  rewrite kakeya_cross_zero in Hsign.
  destruct (b64_orient2d_expansion_sign kakeya_P0 kakeya_P1 kakeya_Q);
    [ exfalso; lra | exfalso; lra | reflexivity ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit.                                                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions kakeya_inputs_int_safe.
Print Assumptions kakeya_cross_zero.
Print Assumptions kakeya_orient2d_sign_zero.
