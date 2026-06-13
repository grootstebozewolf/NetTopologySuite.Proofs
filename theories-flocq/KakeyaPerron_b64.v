(* ============================================================================
   NetTopologySuite.Proofs.Flocq.KakeyaPerron_b64
   ----------------------------------------------------------------------------
   The Perron / Besicovitch-Kakeya shape as a binary64 coordinate-safety
   stress test.

   `PerronStage.perron_stage n` is 2^n thin triangles -- apex (1/2,1), base
   points (k/2^n, 0), each of signed area 1/2^n -> 0.  Extreme area
   concentration and fine dyadic coordinates make it a natural adversary for
   the float plane.  The well-posed question (cf. docs/hat-soundness.md) is the
   COORDINATE-SAFETY WINDOW, not an exact-R failure: scaling stage-n vertices by
   2^(n+1) makes them integers of magnitude <= 2^(n+1), so they are
   `coord_int_safe` -- hence `b64_orient2d` is bit-exact on them -- exactly up
   to the stage where 2^(n+1) leaves the 2^25 window.  That bound, n <= 24, is
   the binary64 SOUNDNESS DIAMETER: the orientation/area sign of every Perron
   triangle is computed without rounding up to stage 24, and the scaled apex
   y-coordinate (2^(n+1)) first leaves the window at stage 25.

   Generalises the concrete collinear triple of KakeyaOrient2d_b64.v (itself
   "the integer-scaled image of three collinear Perron base-line points").

   Pure integer-regime b64; no `Admitted` / `Axiom` / `Parameter`; allowlist
   axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lia Lra.
From Flocq Require Import IEEE754.Binary IEEE754.BinarySingleNaN Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
                                     Orient_b64_sound Orient_b64_exact
                                     Orientation_b64 KakeyaOrient2d_b64.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Integer / power-of-two helpers.                                         *)
(* -------------------------------------------------------------------------- *)

Lemma pow2_nat_Z : forall n : nat, Z.of_nat (2 ^ n) = (2 ^ Z.of_nat n)%Z.
Proof.
  intros n. rewrite Nat2Z.inj_pow. reflexivity.
Qed.

Lemma pow2_le_2p25 : forall e : Z, (0 <= e)%Z -> (e <= 25)%Z -> (2 ^ e <= 2 ^ 25)%Z.
Proof.
  intros e He Hle. apply Z.pow_le_mono_r; lia.
Qed.

Lemma absle_nonneg : forall m b : Z, (0 <= m)%Z -> (m <= b)%Z -> (Z.abs m <= b)%Z.
Proof. intros m b H0 Hb. rewrite Z.abs_eq by exact H0. exact Hb. Qed.

Lemma two_pow_succ_nat : forall n : nat,
  (2 ^ Z.of_nat (n + 1) = 2 * 2 ^ Z.of_nat n)%Z.
Proof.
  intros n. replace (Z.of_nat (n + 1)) with (Z.of_nat n + 1)%Z by lia.
  rewrite Z.pow_add_r by lia. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Scaled-integer Perron vertices (scale 2^(n+1)).                         *)
(*   base_pt k = (k/2^n, 0)  ↦  (2k, 0);   apex (1/2,1) ↦ (2^n, 2^(n+1)).      *)
(* -------------------------------------------------------------------------- *)

Definition perron_b64_apex (n : nat) : BPoint :=
  mkBP (b64Z (2 ^ Z.of_nat n)) (b64Z (2 ^ Z.of_nat (n + 1))).

Definition perron_b64_base (n k : nat) : BPoint :=
  mkBP (b64Z (2 * Z.of_nat k)) (b64Z 0).

(* -------------------------------------------------------------------------- *)
(* §3  Coordinate safety up to the window (n <= 24).                           *)
(* -------------------------------------------------------------------------- *)

Theorem perron_b64_inputs_int_safe :
  forall n k : nat,
    (n <= 24)%nat -> (k < 2 ^ n)%nat ->
    orient2d_inputs_int_safe
      (perron_b64_apex n) (perron_b64_base n k) (perron_b64_base n (S k)).
Proof.
  intros n k Hn Hk.
  (* k and S k bounded by 2^n (in Z) *)
  assert (Hk' : (Z.of_nat k < 2 ^ Z.of_nat n)%Z)
    by (rewrite <- pow2_nat_Z; apply Nat2Z.inj_lt; exact Hk).
  assert (Hsk' : (Z.of_nat (S k) <= 2 ^ Z.of_nat n)%Z)
    by (rewrite <- pow2_nat_Z; apply Nat2Z.inj_le; lia).
  (* power bounds *)
  assert (Hpn : (0 <= 2 ^ Z.of_nat n)%Z) by (apply Z.pow_nonneg; lia).
  assert (Hbn : (2 ^ Z.of_nat n <= 2 ^ 25)%Z) by (apply pow2_le_2p25; lia).
  assert (Hbn1 : (2 ^ Z.of_nat (n + 1) <= 2 ^ 25)%Z) by (apply pow2_le_2p25; lia).
  assert (Hsucc : (2 ^ Z.of_nat (n + 1) = 2 * 2 ^ Z.of_nat n)%Z) by (apply two_pow_succ_nat).
  unfold orient2d_inputs_int_safe, perron_b64_apex, perron_b64_base; cbn [bx by_].
  repeat split; apply b64Z_coord_int_safe; apply absle_nonneg; lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Headline: b64_orient2d is bit-exact on every stage-n triangle, n <= 24. *)
(* -------------------------------------------------------------------------- *)

Theorem perron_tri_b64_orient_exact :
  forall n k : nat,
    (n <= 24)%nat -> (k < 2 ^ n)%nat ->
    Binary.B2R prec emax
      (b64_orient2d (perron_b64_apex n) (perron_b64_base n k) (perron_b64_base n (S k)))
    = cross_R_BP (perron_b64_apex n) (perron_b64_base n k) (perron_b64_base n (S k)).
Proof.
  intros n k Hn Hk.
  apply b64_orient2d_exact_for_small_int.
  apply perron_b64_inputs_int_safe; assumption.
Qed.

(* The exact value of that cross is 2^(n+2) > 0: every Perron triangle is a
   genuinely-oriented (CCW) sliver, and its sign is computed correctly. *)
Theorem perron_tri_b64_cross_pos :
  forall n k : nat,
    (n <= 24)%nat -> (k < 2 ^ n)%nat ->
    cross_R_BP (perron_b64_apex n) (perron_b64_base n k) (perron_b64_base n (S k))
    = IZR (2 ^ Z.of_nat (n + 2)).
Proof.
  intros n k Hn Hk.
  assert (Hb : forall m : Z, (Z.abs m <= 2 ^ 25)%Z ->
                 Binary.B2R prec emax (b64Z m) = IZR m)
    by (intros m Hm; apply (proj1 (b64Z_R m ltac:(lia)))).
  assert (Hk' : (Z.of_nat k < 2 ^ Z.of_nat n)%Z)
    by (rewrite <- pow2_nat_Z; apply Nat2Z.inj_lt; exact Hk).
  assert (Hsk' : (Z.of_nat (S k) <= 2 ^ Z.of_nat n)%Z)
    by (rewrite <- pow2_nat_Z; apply Nat2Z.inj_le; lia).
  assert (Hpn : (0 <= 2 ^ Z.of_nat n)%Z) by (apply Z.pow_nonneg; lia).
  assert (Hbn : (2 ^ Z.of_nat n <= 2 ^ 25)%Z) by (apply pow2_le_2p25; lia).
  assert (Hbn1 : (2 ^ Z.of_nat (n + 1) <= 2 ^ 25)%Z) by (apply pow2_le_2p25; lia).
  assert (Hsucc : (2 ^ Z.of_nat (n + 1) = 2 * 2 ^ Z.of_nat n)%Z) by (apply two_pow_succ_nat).
  unfold cross_R_BP, perron_b64_apex, perron_b64_base; cbn [bx by_].
  rewrite (Hb 0%Z) by (cbn; lia).
  rewrite (Hb (2 ^ Z.of_nat n)%Z) by (rewrite Z.abs_eq; lia).
  rewrite (Hb (2 ^ Z.of_nat (n + 1))%Z) by (rewrite Z.abs_eq; lia).
  rewrite (Hb (2 * Z.of_nat k)%Z) by (rewrite Z.abs_eq; lia).
  rewrite (Hb (2 * Z.of_nat (S k))%Z) by (rewrite Z.abs_eq; lia).
  rewrite <- !minus_IZR, <- !mult_IZR, <- minus_IZR.
  apply f_equal.
  (* algebra: the base k-terms cancel, leaving 2^(n+1)*2 = 2^(n+2) *)
  replace (Z.of_nat (n + 2)) with (Z.of_nat (n + 1) + 1)%Z by lia.
  rewrite Z.pow_add_r by lia. rewrite Nat2Z.inj_succ. rewrite Hsucc. ring.
Qed.

Corollary perron_tri_b64_cross_positive :
  forall n k : nat, (n <= 24)%nat -> (k < 2 ^ n)%nat ->
    cross_R_BP (perron_b64_apex n) (perron_b64_base n k) (perron_b64_base n (S k)) > 0.
Proof.
  intros n k Hn Hk. rewrite (perron_tri_b64_cross_pos n k Hn Hk).
  apply IZR_lt. apply Z.pow_pos_nonneg; lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  The brink / soundness diameter: stage 25's scaled apex leaves the       *)
(* window.                                                                     *)
(* -------------------------------------------------------------------------- *)

Theorem perron_b64_apex_unsafe_at_25 : ~ coord_int_safe (b64Z (2 ^ 26)).
Proof.
  intros [_ [m [HR Hm]]].
  rewrite (proj1 (b64Z_R (2 ^ 26) ltac:(lia))) in HR.
  apply eq_IZR in HR.            (* m = 2^26 *)
  subst m. revert Hm. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Integer-regime b64; allowlist axioms only.                    *)
(* -------------------------------------------------------------------------- *)

Print Assumptions perron_b64_inputs_int_safe.
Print Assumptions perron_tri_b64_orient_exact.
Print Assumptions perron_tri_b64_cross_positive.
Print Assumptions perron_b64_apex_unsafe_at_25.
