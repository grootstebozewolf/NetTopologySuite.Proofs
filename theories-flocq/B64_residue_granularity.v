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
From Flocq Require Import IEEE754.Binary Core Ulp.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_lib B64_Expansion
                                     B64_FastExpansionSum B64_TwoSum_sterbenz
                                     B64_Pff_bridge.
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

(* ulp(v) = bpow(cexp v) for nonzero b64-format v. *)
Lemma b64_ulp_eq_bpow_cexp :
  forall v : R, b64_format v -> v <> 0 ->
  ulp radix2 (SpecFloat.fexp prec emax) v = bpow radix2 (cexp radix2 b64_fexp v).
Proof. intros v Hf Hv. exact (ulp_neq_0 radix2 b64_fexp v Hv). Qed.

(* `strict_succ_b64` as a half-ulp bpow bound on the predecessor exponent. *)
Lemma strict_succ_b64_half_ulp_bpow :
  forall (a b : binary64),
    Binary.B2R prec emax a <> 0 ->
    strict_succ_b64 a b ->
    Rabs (Binary.B2R prec emax b)
      <= bpow radix2 (cexp radix2 b64_fexp (Binary.B2R prec emax a) - 1).
Proof.
  intros a b Ha0 Hss.
  unfold strict_succ_b64 in Hss.
  pose proof (b64_format_B2R a) as Hfa.
  pose proof (b64_ulp_eq_bpow_cexp _ Hfa Ha0) as Hulp.
  rewrite Hulp in Hss.
  assert (Hhalf : bpow radix2 (cexp radix2 b64_fexp (Binary.B2R prec emax a)) / 2
                = bpow radix2 (cexp radix2 b64_fexp (Binary.B2R prec emax a) - 1)).
  { rewrite bpow_pred2 by lia. lra. }
  rewrite Hhalf in Hss. exact Hss.
Qed.

(* Magnitude lower bound lifts to a cexp lower bound (binary64: cexp = max(mag-prec, emin)). *)
Lemma b64_cexp_ge_from_mag_lb :
  forall (v : R) (k : Z),
    b64_format v ->
    (k + prec <= mag radix2 v)%Z ->
    (k <= cexp radix2 b64_fexp v)%Z.
Proof.
  intros v k Hf Hmag.
  unfold cexp, b64_fexp, SpecFloat.fexp.
  pose proof (Z.le_max_l (mag radix2 v - prec) (SpecFloat.emin prec emax)) as Hmax.
  apply Z.le_trans with (mag radix2 v - prec)%Z; [lia | exact Hmax].
Qed.

(* Resolution-1-extended emission surgery (plan §4.A): lifting `strict_succ` from
   the old carry `q` to the cancellation residue requires an explicit bound on the
   surviving output head against the NEW carry's half-ulp grid.  Double residue
   alone does not suffice (Trace C: `strict_succ_b64 2^8 1` is false). *)
Lemma pathB_cancel_strict_succ_head :
  forall (q x h : binary64),
    b64_TwoSum_safe x q ->
    b64_format (Binary.B2R prec emax x + Binary.B2R prec emax q) ->
    Binary.B2R prec emax x + Binary.B2R prec emax q <> 0 ->
    Binary.B2R prec emax q <> 0 ->
    Rabs (Binary.B2R prec emax q) / 2 <= Rabs (Binary.B2R prec emax x) ->
    strict_succ_b64 q h ->
    Rabs (Binary.B2R prec emax h) <=
      bpow radix2 (cexp radix2 b64_fexp
        (Binary.B2R prec emax (fst (b64_TwoSum x q))) - 1) ->
    strict_succ_b64 (fst (b64_TwoSum x q)) h.
Proof.
  intros q x h Hsafe Hfmt Hsum0 Hq0 Hster Hqh Hhead.
  unfold strict_succ_b64.
  destruct (b64_TwoSum x q) as [carry' err] eqn:Hts.
  pose proof (Binary.generic_format_B2R prec emax q) as Hfq.
  pose proof (b64_TwoSum_exact_of_format_sum x q Hsafe Hfmt) as [HcarryR Herr].
  assert (HcarryB : Binary.B2R prec emax carry'
                    = Binary.B2R prec emax x + Binary.B2R prec emax q).
  { transitivity (Binary.B2R prec emax (b64_plus x q)).
    - rewrite <- b64_TwoSum_fst, Hts. reflexivity.
    - exact HcarryR. }
  assert (Hcarry0 : Binary.B2R prec emax carry' <> 0).
  { rewrite HcarryB. exact Hsum0. }
  pose proof (b64_format_B2R carry') as Hfc.
  pose proof (b64_ulp_eq_bpow_cexp _ Hfc Hcarry0) as Hulp.
  assert (Hhalf : bpow radix2 (cexp radix2 b64_fexp (Binary.B2R prec emax carry')) / 2
                = bpow radix2 (cexp radix2 b64_fexp (Binary.B2R prec emax carry') - 1)).
  { rewrite bpow_pred2 by lia. lra. }
  assert (Hbind : ulp radix2 (SpecFloat.fexp prec emax) (Binary.B2R prec emax carry') / 2
                = bpow radix2 (cexp radix2 b64_fexp (Binary.B2R prec emax carry') - 1)).
  { transitivity (bpow radix2 (cexp radix2 b64_fexp (Binary.B2R prec emax carry')) / 2).
    - f_equal. unfold b64_ulp in Hulp. exact Hulp.
    - exact Hhalf. }
  apply Rle_trans with (bpow radix2 (cexp radix2 b64_fexp (Binary.B2R prec emax carry') - 1)).
  - exact Hhead.
  - rewrite <- Hbind. apply Rle_refl.
Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit.                                                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions residue_ge_half_ulp.
Print Assumptions pathB_cancel_strict_succ_head.
