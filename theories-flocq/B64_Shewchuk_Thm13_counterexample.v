(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_Shewchuk_Thm13_counterexample
   ----------------------------------------------------------------------------
   Shewchuk Theorem 13 headline — counterexample to the corpus statement.

   The deferred headline `fast_expansion_sum_nonoverlap_shewchuk`
   (B64_FastExpansionSum_Shewchuk.v:483) claims that, for `nonoverlap_shewchuk`
   inputs `e`, `f`, the output `fast_expansion_sum e f` is again
   `nonoverlap_shewchuk`.  But the corpus's `nonoverlap_shewchuk` is built on

       strict_succ_b64 a b := |B2R b| <= ulp(B2R a) / 2

   i.e. EACH component must lie within a HALF-ULP of its predecessor.  That is
   the correct postcondition of a SINGLE TwoSum's (high, low) pair, but it is
   strictly stronger than Shewchuk's "(strongly) nonoverlapping", which only
   forbids overlapping significand bits.  `fast_expansion_sum` of several terms
   emits bit-disjoint components that are NOT within a half-ulp.

   Concrete witness.  Take the value 257 = 256 + 1:
     - `256` and `1` are bit-disjoint (a legitimate Shewchuk expansion), but
       `strict_succ_b64 256 1` is FALSE (`1 > ulp(256)/2 = 2^-45`), so
       `nonoverlap_shewchuk [256; 1]` is FALSE.
     - 257 is the exact sum of two VALID `nonoverlap_shewchuk` inputs
       `e = [2^60; 1]` and `f = [-(2^60 - 256)]`, and `fast_expansion_sum`
       emits `256` (last residue) and `1` (earlier committed low part) as
       SEPARATE components (it never re-merges bit-disjoint parts), so its
       output compresses to `[256; 1]` — which fails `nonoverlap_shewchuk`.

   This file machine-checks the load-bearing facts:
     - `nonoverlap_shewchuk_256_1_false`  : the output predicate fails on [256;1]
     - `e_nonoverlap`, `f_nonoverlap`      : the inputs are valid
     - `inputs_sum_eq`                     : expansion_R e + expansion_R f
                                             = expansion_R [256; 1] = 257
   establishing that `strict_succ_b64`/`nonoverlap_shewchuk` is too strong to be
   `fast_expansion_sum`'s postcondition — the headline is FALSE as stated and
   belongs in docs/admitted-counterexamples.txt (Tier 2), alongside the already-
   refuted building block `b64_grow_expansion_nonoverlap`.

   The final structural link (`fast_expansion_sum e f` reduces, through the
   noncomputable magnitude-sort, to a list compressing to [256; 1]) is recorded
   as a hand-trace in the header / docs; `sort_by_abs` and `compress` use
   `Rcompare` and so are not `vm_compute`-able, which is why that last step is
   carried by the cascade traces in B64_pathB_trace_4A.v rather than reduced here.

   Pure-Flocq (binary64); no `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lia Lra List.
From Flocq Require Import IEEE754.Binary Core Ulp.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_lib
                                     B64_Expansion B64_Expansion_Shewchuk.
Import ListNotations.
Local Open Scope R_scope.

(* Concrete binary64 values (mantissa 2^52 = 4503599627370496). *)
Definition b1     : binary64 := Binary.B754_finite prec emax false 4503599627370496 (-52) eq_refl. (* 1     = bpow 0  *)
Definition b256   : binary64 := Binary.B754_finite prec emax false 4503599627370496 (-44) eq_refl. (* 256   = bpow 8  *)
Definition b2p60  : binary64 := Binary.B754_finite prec emax false 4503599627370496 8     eq_refl. (* 2^60  = bpow 60 *)
(* -(2^60 - 256) = -(2^53 - 2) * 2^7. *)
Definition bneg   : binary64 := Binary.B754_finite prec emax true  9007199254740990 7     eq_refl.

(* Mantissa 2^52 as a bpow. *)
Lemma IZR_mant_bpow : IZR 4503599627370496 = bpow radix2 52.
Proof. rewrite <- (IZR_Zpower radix2 52) by lia. reflexivity. Qed.

Lemma bpow1eq2 : bpow radix2 1 = 2.
Proof. rewrite bpow_1. reflexivity. Qed.

Lemma bpow_dbl : forall a : Z, bpow radix2 (a + 1) = 2 * bpow radix2 a.
Proof. intro a. rewrite bpow_plus, bpow1eq2. lra. Qed.

(* B2R values, each as a bpow (for ulp reasoning). *)
Lemma b1_R    : Binary.B2R prec emax b1    = bpow radix2 0.
Proof. unfold b1.   cbn [Binary.B2R]. unfold F2R; cbn [Fnum Fexp cond_Zopp].
  rewrite IZR_mant_bpow, <- bpow_plus. reflexivity. Qed.
Lemma b256_R  : Binary.B2R prec emax b256  = bpow radix2 8.
Proof. unfold b256. cbn [Binary.B2R]. unfold F2R; cbn [Fnum Fexp cond_Zopp].
  rewrite IZR_mant_bpow, <- bpow_plus. reflexivity. Qed.
Lemma b2p60_R : Binary.B2R prec emax b2p60 = bpow radix2 60.
Proof. unfold b2p60. cbn [Binary.B2R]. unfold F2R; cbn [Fnum Fexp cond_Zopp].
  rewrite IZR_mant_bpow, <- bpow_plus. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* The output predicate FAILS on [256; 1]: strict_succ_b64 256 1 is false.    *)
(* -------------------------------------------------------------------------- *)

Lemma strict_succ_b64_256_1_false : ~ strict_succ_b64 b256 b1.
Proof.
  unfold strict_succ_b64. rewrite b1_R, b256_R.
  rewrite ulp_bpow.
  (* goal: ~ ( |bpow 0| <= bpow (b64_fexp (8+1)) / 2 ) *)
  rewrite Rabs_pos_eq by apply bpow_ge_0.
  assert (Hfexp : b64_fexp (8 + 1) = (-44)%Z).
  { unfold b64_fexp, SpecFloat.fexp, SpecFloat.emin, prec, emax. lia. }
  rewrite Hfexp.
  intro H.
  (* bpow(-44)/2 < bpow(-44) < bpow 0, contradicting H. *)
  pose proof (bpow_lt radix2 (-44) 0 ltac:(lia)) as Hm.
  pose proof (bpow_gt_0 radix2 (-44)) as Hp.
  lra.
Qed.

Lemma nonoverlap_shewchuk_256_1_false :
  ~ nonoverlap_shewchuk [b256; b1].
Proof.
  unfold nonoverlap_shewchuk.
  (* compress [256;1] = [256;1] (both nonzero). *)
  assert (Hc : compress [b256; b1] = [b256; b1]).
  { cbn [compress].
    rewrite b256_R, b1_R.
    rewrite (Rcompare_Gt (bpow radix2 8) 0) by apply bpow_gt_0.
    rewrite (Rcompare_Gt (bpow radix2 0) 0) by apply bpow_gt_0.
    reflexivity. }
  rewrite Hc. cbn [nonoverlap_strict].
  intros [Hss _]. exact (strict_succ_b64_256_1_false Hss).
Qed.

(* -------------------------------------------------------------------------- *)
(* The inputs are VALID nonoverlap_shewchuk, and their exact sum is 257.       *)
(* -------------------------------------------------------------------------- *)

Definition e_in : list binary64 := [b2p60; b1].
Definition f_in : list binary64 := [bneg].

Lemma e_nonoverlap : nonoverlap_shewchuk e_in.
Proof.
  unfold nonoverlap_shewchuk, e_in.
  assert (Hc : compress [b2p60; b1] = [b2p60; b1]).
  { cbn [compress]. rewrite b2p60_R, b1_R.
    rewrite (Rcompare_Gt (bpow radix2 60) 0) by apply bpow_gt_0.
    rewrite (Rcompare_Gt (bpow radix2 0) 0) by apply bpow_gt_0.
    reflexivity. }
  rewrite Hc. cbn [nonoverlap_strict]. split; [| exact I].
  (* strict_succ_b64 2^60 1 : |1| <= ulp(2^60)/2 = bpow 7. *)
  unfold strict_succ_b64. rewrite b1_R, b2p60_R, ulp_bpow.
  rewrite Rabs_pos_eq by apply bpow_ge_0.
  assert (Hfexp : b64_fexp (60 + 1) = 8%Z).
  { unfold b64_fexp, SpecFloat.fexp, SpecFloat.emin, prec, emax. lia. }
  rewrite Hfexp.
  (* 1 = bpow 0 <= bpow 8 / 2 = bpow 7 *)
  assert (H8 : bpow radix2 8 = 2 * bpow radix2 7).
  { replace 8%Z with (7 + 1)%Z by lia. apply bpow_dbl. }
  pose proof (bpow_le radix2 0 7 ltac:(lia)) as Hle.
  lra.
Qed.

Lemma f_nonoverlap : nonoverlap_shewchuk f_in.
Proof.
  unfold nonoverlap_shewchuk, f_in.
  cbn [compress].
  destruct (Rcompare (Binary.B2R prec emax bneg) 0); cbn [nonoverlap_strict]; exact I.
Qed.

(* B2R of the negative input: -(2^60 - 256) = 256 - 2^60. *)
Lemma bneg_R : Binary.B2R prec emax bneg = bpow radix2 8 - bpow radix2 60.
Proof.
  unfold bneg. cbn [Binary.B2R]. unfold F2R; cbn [Fnum Fexp cond_Zopp].
  (* IZR (Zneg 9007199254740990) * bpow 7 = bpow 8 - bpow 60 *)
  rewrite <- (IZR_Zpower radix2 7) by lia.
  rewrite <- (IZR_Zpower radix2 8) by lia.
  rewrite <- (IZR_Zpower radix2 60) by lia.
  rewrite <- mult_IZR, <- minus_IZR.
  reflexivity.
Qed.

Lemma inputs_sum_eq :
  expansion_R e_in + expansion_R f_in = expansion_R [b256; b1].
Proof.
  unfold e_in, f_in. cbn [expansion_R].
  rewrite b2p60_R, b1_R, bneg_R, b256_R.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit.                                                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions nonoverlap_shewchuk_256_1_false.
Print Assumptions e_nonoverlap.
Print Assumptions inputs_sum_eq.
