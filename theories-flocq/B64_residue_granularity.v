(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_residue_granularity
   ----------------------------------------------------------------------------
   Shewchuk Theorem 13, obligation O1' (docs/shewchuk-thm13-pathb-plan.md §7):
   the residue-granularity lemma that de-risks pathB's clause-(a) preservation.

   When two binary64 values `vx`, `vC` are in opposite-sign "Sterbenz" position
   (`|vC|/2 <= |vx|`), their EXACT sum `vx + vC` (the pathB cancellation residue)
   is either zero or has magnitude at least half an ulp of `vC`:

       vx + vC = 0   \/   bpow (cexp vC - 1) <= |vx + vC|.

   Since `bpow (cexp vC) = ulp(vC)`, `bpow (cexp vC - 1) = (1/2) ulp(vC)`.  This
   is exactly the bound the cascade needs: a nonzero residue dominates every
   previously-emitted low part (each `<= (1/2) ulp(carry)`), so clause (a) of
   the cascade invariant survives a pathB step WITHOUT a strengthened dominance
   invariant.

   Mechanism (the "grid" argument): in Sterbenz range `vx`'s exponent is within
   1 of `vC`'s, so both `vx` and `vC` are integer multiples of `bpow(cexp vC-1)`
   (= half-ulp grid of `vC`); hence so is their sum, and a nonzero multiple of
   `bpow e` has magnitude `>= bpow e`.

   Pure-Flocq (binary64); no `Admitted` / `Axiom` / `Parameter` introduced.
   This is a standalone arithmetic lemma; it does NOT touch the cascade
   machinery or the deferred headline.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lia Lra.
From Flocq Require Import IEEE754.Binary Core.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_lib.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Generic helpers.                                                           *)
(* -------------------------------------------------------------------------- *)

Lemma bpow_radix2_1 : bpow radix2 1 = 2.
Proof. rewrite bpow_1. reflexivity. Qed.

(* Radix-2 step: bpow a = 2 * bpow (a-1).  No `replace` (avoids rewriting the
   `a` nested inside `a-1`). *)
Lemma bpow_pred2 : forall a : Z, bpow radix2 a = 2 * bpow radix2 (a - 1).
Proof.
  intro a. rewrite <- bpow_radix2_1, <- bpow_plus. f_equal. lia.
Qed.

(* A value `IZR n * bpow E` re-expressed on a coarser grid `bpow e`, e <= E. *)
Lemma scale_down_to_exp :
  forall (n E e : Z), (e <= E)%Z ->
    IZR n * bpow radix2 E = IZR (n * radix2 ^ (E - e)) * bpow radix2 e.
Proof.
  intros n E e Hle.
  rewrite mult_IZR, (IZR_Zpower radix2 (E - e)) by lia.
  rewrite Rmult_assoc, <- bpow_plus.
  replace (E - e + e)%Z with E by lia.
  reflexivity.
Qed.

(* A nonzero integer multiple of `bpow e` has magnitude at least `bpow e`. *)
Lemma nonzero_mult_bpow_ge :
  forall (k e : Z),
    IZR k * bpow radix2 e <> 0 ->
    bpow radix2 e <= Rabs (IZR k * bpow radix2 e).
Proof.
  intros k e Hnz.
  rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 e)) by apply bpow_ge_0.
  assert (Hk : (k <> 0)%Z).
  { intro Hk0. apply Hnz. rewrite Hk0. simpl. ring. }
  assert (H1 : 1 <= Rabs (IZR k)).
  { rewrite <- abs_IZR. replace 1 with (IZR 1) by reflexivity.
    apply IZR_le. lia. }
  rewrite <- (Rmult_1_l (bpow radix2 e)) at 1.
  apply Rmult_le_compat_r; [ apply bpow_ge_0 | exact H1 ].
Qed.

(* A binary64-format value is its integer mantissa times bpow of its cexp. *)
Lemma b64_format_eq_mant_bpow :
  forall v : R, b64_format v ->
    v = IZR (Ztrunc (scaled_mantissa radix2 b64_fexp v))
        * bpow radix2 (cexp radix2 b64_fexp v).
Proof.
  intros v Hf. unfold generic_format, F2R in Hf.
  cbn [Fnum Fexp] in Hf. exact Hf.
Qed.

(* -------------------------------------------------------------------------- *)
(* The residue-granularity lemma (O1').                                        *)
(* -------------------------------------------------------------------------- *)

Lemma residue_ge_half_ulp :
  forall vx vC : R,
    b64_format vx -> b64_format vC ->
    vC <> 0 ->
    Rabs vC / 2 <= Rabs vx ->
    vx + vC <> 0 ->
    bpow radix2 (cexp radix2 b64_fexp vC - 1) <= Rabs (vx + vC).
Proof.
  intros vx vC Hfx HfC HC0 Hster Hsum0.
  pose proof (b64_format_eq_mant_bpow vx Hfx) as Hx.
  pose proof (b64_format_eq_mant_bpow vC HfC) as HC.
  set (nx := Ztrunc (scaled_mantissa radix2 b64_fexp vx)) in *.
  set (nC := Ztrunc (scaled_mantissa radix2 b64_fexp vC)) in *.
  set (ex := cexp radix2 b64_fexp vx) in *.
  set (eC := cexp radix2 b64_fexp vC) in *.
  set (e0 := (eC - 1)%Z).
  (* mag(vC) - 1 <= mag(vx) from the Sterbenz lower bound. *)
  assert (Hmaglb : bpow radix2 (mag radix2 vC - 1 - 1) <= Rabs vx).
  { pose proof (@bpow_mag_le radix2 vC HC0) as Hml.
    pose proof (bpow_pred2 (mag radix2 vC - 1)) as Hp.
    lra. }
  assert (HmagX : (mag radix2 vC - 1 <= mag radix2 vx)%Z).
  { apply (@mag_ge_bpow radix2 vx (mag radix2 vC - 1)). exact Hmaglb. }
  (* cexp vx >= cexp vC - 1  (FLT Lipschitz + monotonicity, pure Z.max). *)
  assert (HexLB : (e0 <= ex)%Z).
  { unfold e0, ex, eC, cexp, SpecFloat.fexp. lia. }
  assert (HeCLB : (e0 <= eC)%Z) by (unfold e0; lia).
  (* Put both operands on the bpow e0 grid. *)
  assert (Hx' : vx = IZR (nx * radix2 ^ (ex - e0)) * bpow radix2 e0).
  { rewrite Hx. apply scale_down_to_exp. exact HexLB. }
  assert (HC' : vC = IZR (nC * radix2 ^ (eC - e0)) * bpow radix2 e0).
  { rewrite HC. apply scale_down_to_exp. exact HeCLB. }
  assert (Hcomb : vx + vC
                  = IZR (nx * radix2 ^ (ex - e0) + nC * radix2 ^ (eC - e0))
                    * bpow radix2 e0).
  { rewrite plus_IZR, Rmult_plus_distr_r, <- Hx', <- HC'. reflexivity. }
  replace (eC - 1)%Z with e0 by (unfold e0; lia).
  rewrite Hcomb. apply nonzero_mult_bpow_ge. rewrite <- Hcomb. exact Hsum0.
Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit.                                                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions residue_ge_half_ulp.
