(* ============================================================================
   NetTopologySuite.Proofs.Flocq.ClothoidScopeA_b64
   ----------------------------------------------------------------------------
   Scope-A residual-assembly exactness for the clothoid chord-length residual
   -- route (C) of docs/clothoid-open-questions-triage.md, on the
   ArcLineIntersect_b64_exact.v first-stage pattern.

   Context.  The full residual is f(L) = L^2 * (P(L)^2 + Q(L)^2) - d^2 with
   P, Q Fresnel-like integrals.  The transcendental stage (computing P and Q)
   admits no exact integer regime -- see the triage doc's Q2 analysis -- and
   is NEVER claimed here.  What IS exactly analysable is the polynomial
   ASSEMBLY of the residual from oracle-supplied fixed-point approximants:
   given integers np, nq representing P, Q scaled by 2^s (np ~ P * 2^s,
   nq ~ Q * 2^s) and the scale square ns2 = 2^(2s), the scaled assembly

       A = nL^2 * (np^2 + nq^2) - nd^2 * ns2
         = 2^(2s) * ( L^2 * (Phat^2 + Qhat^2) - d^2 ),    Phat = np / 2^s,

   is an integer, has the SAME SIGN and SAME ROOTS as the rational-approximant
   residual, and -- this file's content -- its binary64 evaluation is
   BIT-EXACT when every intermediate stays in the 2^53 integer window.  So
   the binary64 sign test on the assembly decides the exact sign of the
   approximant residual: the only error budget left for a solver is the
   transcendental approximation |Phat - P|, |Qhat - Q|, which lives entirely
   in the oracle-supplied inputs, not in the arithmetic.

   Deliverables:
     1. `b64_residual_assembly_int_exact` -- generic skeleton: integer-valued
        inputs + per-intermediate window hypotheses => the five-operation
        binary64 assembly equals the integer assembly on the nose.
     2. `b64_residual_assembly_exact_window` -- concrete instantiation:
        |nL|, |nd| <= 2^12, |np|, |nq| <= 2^13, ns2 = 2^26 discharges every
        window obligation (largest intermediate <= 2^51 + 2^50 < 2^53).
     3. `b64_residual_assembly_sign_decides` -- the binary64 sign decides
        the integer assembly's sign exactly (trichotomy).
     4. `residual_assembly_degenerate_consistent` -- consistency with the
        merged route-(A) slice: at np = 2^s, nq = 0 the assembly is
        2^(2s) times ClothoidDegenerate.v's degenerate_residual.

   Infrastructure reused (no new machinery): `b64_mult_int_exact`,
   `b64_plus_int_exact`, `b64_minus_int_exact` (Orient_b64_exact.v);
   `degenerate_residual` (theories/ClothoidDegenerate.v).

   NTS mapping: the fixed-point assembly stage of a clothoid G^1 Hermite
   chord-length solver (clothoid-halley-coq, public EUPL-1.2 repro); the
   differential oracle can emit scaled-integer P/Q vectors for bit-exact
   comparison against this assembly.

   No Admitted, no Axiom (beyond the corpus allowlist; this lane additionally
   inherits Classical_Prop.classic structurally from Flocq's binary
   operations, see docs/audit-exceptions.txt).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Lra.
From Stdlib Require Import Psatz.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import IEEE754.BinarySingleNaN.
From Flocq Require Import Core.

From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import B64_bridge.
From NTS.Proofs.Flocq Require Import Orient_b64_exact.
From NTS.Proofs Require Import ClothoidDegenerate.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* The assembly, on integers and in binary64.                                 *)
(* -------------------------------------------------------------------------- *)

Definition residual_assembly_Z (nd nL np nq ns2 : Z) : Z :=
  (nL * nL * (np * np + nq * nq) - nd * nd * ns2)%Z.

Definition b64_residual_assembly (d L p q s2 : binary64) : binary64 :=
  b64_minus
    (b64_mult (b64_mult L L) (b64_plus (b64_mult p p) (b64_mult q q)))
    (b64_mult (b64_mult d d) s2).

(* -------------------------------------------------------------------------- *)
(* 1. Generic skeleton: per-intermediate window hypotheses => bit-exact.      *)
(* -------------------------------------------------------------------------- *)

Theorem b64_residual_assembly_int_exact :
  forall (d L p q s2 : binary64) (nd nL np nq ns2 : Z),
    Binary.is_finite prec emax d = true ->
    Binary.is_finite prec emax L = true ->
    Binary.is_finite prec emax p = true ->
    Binary.is_finite prec emax q = true ->
    Binary.is_finite prec emax s2 = true ->
    Binary.B2R prec emax d = IZR nd ->
    Binary.B2R prec emax L = IZR nL ->
    Binary.B2R prec emax p = IZR np ->
    Binary.B2R prec emax q = IZR nq ->
    Binary.B2R prec emax s2 = IZR ns2 ->
    (Z.abs (np * np) <= 2 ^ prec)%Z ->
    (Z.abs (nq * nq) <= 2 ^ prec)%Z ->
    (Z.abs (np * np + nq * nq) <= 2 ^ prec)%Z ->
    (Z.abs (nL * nL) <= 2 ^ prec)%Z ->
    (Z.abs (nL * nL * (np * np + nq * nq)) <= 2 ^ prec)%Z ->
    (Z.abs (nd * nd) <= 2 ^ prec)%Z ->
    (Z.abs (nd * nd * ns2) <= 2 ^ prec)%Z ->
    (Z.abs (residual_assembly_Z nd nL np nq ns2) <= 2 ^ prec)%Z ->
    Binary.B2R prec emax (b64_residual_assembly d L p q s2)
      = IZR (residual_assembly_Z nd nL np nq ns2)
    /\ Binary.is_finite prec emax (b64_residual_assembly d L p q s2) = true.
Proof.
  intros d L p q s2 nd nL np nq ns2
         Fd FL Fp Fq Fs2 HdR HLR HpR HqR Hs2R
         Wpp Wqq Wsum WLL Wprod Wdd Wds Wres.
  unfold b64_residual_assembly, residual_assembly_Z in *.
  destruct (b64_mult_int_exact p p np np Fp Fp HpR HpR Wpp) as [Hpp Fpp].
  destruct (b64_mult_int_exact q q nq nq Fq Fq HqR HqR Wqq) as [Hqq Fqq].
  destruct (b64_plus_int_exact (b64_mult p p) (b64_mult q q)
              (np * np) (nq * nq) Fpp Fqq Hpp Hqq Wsum) as [Hsum Fsum].
  destruct (b64_mult_int_exact L L nL nL FL FL HLR HLR WLL) as [HLL FLL].
  destruct (b64_mult_int_exact (b64_mult L L)
              (b64_plus (b64_mult p p) (b64_mult q q))
              (nL * nL) (np * np + nq * nq)
              FLL Fsum HLL Hsum Wprod) as [Hprod Fprod].
  destruct (b64_mult_int_exact d d nd nd Fd Fd HdR HdR Wdd) as [Hdd Fdd].
  destruct (b64_mult_int_exact (b64_mult d d) s2
              (nd * nd) ns2 Fdd Fs2 Hdd Hs2R Wds) as [Hds Fds].
  destruct (b64_minus_int_exact
              (b64_mult (b64_mult L L)
                 (b64_plus (b64_mult p p) (b64_mult q q)))
              (b64_mult (b64_mult d d) s2)
              (nL * nL * (np * np + nq * nq)) (nd * nd * ns2)
              Fprod Fds Hprod Hds Wres) as [Hres Fres].
  split; [exact Hres | exact Fres].
Qed.

(* -------------------------------------------------------------------------- *)
(* 2. Concrete window: |nL|, |nd| <= 2^12, |np|, |nq| <= 2^13, ns2 = 2^26.    *)
(* Largest intermediate: |nL^2 (np^2+nq^2)| <= 2^24 * 2^27 = 2^51; the final  *)
(* difference <= 2^51 + 2^50 < 2^53.                                          *)
(* -------------------------------------------------------------------------- *)

Theorem b64_residual_assembly_exact_window :
  forall (d L p q s2 : binary64) (nd nL np nq : Z),
    Binary.is_finite prec emax d = true ->
    Binary.is_finite prec emax L = true ->
    Binary.is_finite prec emax p = true ->
    Binary.is_finite prec emax q = true ->
    Binary.is_finite prec emax s2 = true ->
    Binary.B2R prec emax d = IZR nd ->
    Binary.B2R prec emax L = IZR nL ->
    Binary.B2R prec emax p = IZR np ->
    Binary.B2R prec emax q = IZR nq ->
    Binary.B2R prec emax s2 = IZR (2 ^ 26) ->
    (Z.abs nd <= 2 ^ 12)%Z ->
    (Z.abs nL <= 2 ^ 12)%Z ->
    (Z.abs np <= 2 ^ 13)%Z ->
    (Z.abs nq <= 2 ^ 13)%Z ->
    Binary.B2R prec emax (b64_residual_assembly d L p q s2)
      = IZR (residual_assembly_Z nd nL np nq (2 ^ 26))
    /\ Binary.is_finite prec emax (b64_residual_assembly d L p q s2) = true.
Proof.
  intros d L p q s2 nd nL np nq
         Fd FL Fp Fq Fs2 HdR HLR HpR HqR Hs2R Bd BL Bp Bq.
  apply Z.abs_le in Bd, BL, Bp, Bq.
  (* Staged intermediate bounds; each step is a product of two already-     *)
  (* bounded nonnegative factors, kept small enough for nia.                *)
  assert (Hpp : (0 <= np * np <= 2 ^ 26)%Z) by nia.
  assert (Hqq : (0 <= nq * nq <= 2 ^ 26)%Z) by nia.
  assert (Hsum : (0 <= np * np + nq * nq <= 2 ^ 27)%Z) by lia.
  assert (HLL : (0 <= nL * nL <= 2 ^ 24)%Z) by nia.
  assert (Hdd : (0 <= nd * nd <= 2 ^ 24)%Z) by nia.
  assert (Hprod : (0 <= nL * nL * (np * np + nq * nq) <= 2 ^ 51)%Z).
  { split; [nia | ].
    apply Z.le_trans with (2 ^ 24 * 2 ^ 27)%Z;
      [ apply Z.mul_le_mono_nonneg; lia | lia ]. }
  assert (Hds : (0 <= nd * nd * 2 ^ 26 <= 2 ^ 50)%Z) by nia.
  apply (b64_residual_assembly_int_exact d L p q s2 nd nL np nq (2 ^ 26));
    try assumption;
    unfold prec; apply Z.abs_le; unfold residual_assembly_Z; lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* 3. The binary64 sign decides the integer assembly's sign exactly.          *)
(* -------------------------------------------------------------------------- *)

Theorem b64_residual_assembly_sign_decides :
  forall (d L p q s2 : binary64) (nd nL np nq : Z),
    Binary.is_finite prec emax d = true ->
    Binary.is_finite prec emax L = true ->
    Binary.is_finite prec emax p = true ->
    Binary.is_finite prec emax q = true ->
    Binary.is_finite prec emax s2 = true ->
    Binary.B2R prec emax d = IZR nd ->
    Binary.B2R prec emax L = IZR nL ->
    Binary.B2R prec emax p = IZR np ->
    Binary.B2R prec emax q = IZR nq ->
    Binary.B2R prec emax s2 = IZR (2 ^ 26) ->
    (Z.abs nd <= 2 ^ 12)%Z ->
    (Z.abs nL <= 2 ^ 12)%Z ->
    (Z.abs np <= 2 ^ 13)%Z ->
    (Z.abs nq <= 2 ^ 13)%Z ->
    (Binary.B2R prec emax (b64_residual_assembly d L p q s2) < 0
       <-> (residual_assembly_Z nd nL np nq (2 ^ 26) < 0)%Z)
    /\ (Binary.B2R prec emax (b64_residual_assembly d L p q s2) = 0
       <-> residual_assembly_Z nd nL np nq (2 ^ 26) = 0%Z)
    /\ (0 < Binary.B2R prec emax (b64_residual_assembly d L p q s2)
       <-> (0 < residual_assembly_Z nd nL np nq (2 ^ 26))%Z).
Proof.
  intros d L p q s2 nd nL np nq
         Fd FL Fp Fq Fs2 HdR HLR HpR HqR Hs2R Bd BL Bp Bq.
  destruct (b64_residual_assembly_exact_window d L p q s2 nd nL np nq
              Fd FL Fp Fq Fs2 HdR HLR HpR HqR Hs2R Bd BL Bp Bq) as [Hx _].
  rewrite Hx.
  repeat split; intro H.
  - apply lt_IZR. exact H.
  - apply IZR_lt in H. exact H.
  - apply eq_IZR. exact H.
  - rewrite H. reflexivity.
  - apply lt_IZR. exact H.
  - apply IZR_lt in H. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* 4. Consistency with the degenerate route-(A) slice: at np = 2^s, nq = 0    *)
(* (the exact fixed-point encoding of P = 1, Q = 0) the assembly is 2^(2s)    *)
(* times the degenerate residual -- same sign, same roots.                    *)
(* -------------------------------------------------------------------------- *)

Lemma residual_assembly_degenerate_consistent :
  forall (nd nL s : Z),
    (0 <= s)%Z ->
    IZR (residual_assembly_Z nd nL (2 ^ s) 0 (2 ^ (2 * s)))
      = IZR (2 ^ s) * IZR (2 ^ s)
        * degenerate_residual (IZR nd) (IZR nL).
Proof.
  intros nd nL s Hs.
  unfold residual_assembly_Z, degenerate_residual.
  replace (2 * s)%Z with (s + s)%Z by ring.
  rewrite Z.pow_add_r by lia.
  rewrite minus_IZR, !mult_IZR, plus_IZR, !mult_IZR.
  simpl. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Theorems 1-3 inherit Classical_Prop.classic structurally     *)
(* from Flocq's binary operations (see docs/audit-exceptions.txt); the        *)
(* consistency lemma 4 is pure R/Z algebra over the allowlist axioms.         *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_residual_assembly_int_exact.
Print Assumptions b64_residual_assembly_exact_window.
Print Assumptions b64_residual_assembly_sign_decides.
Print Assumptions residual_assembly_degenerate_consistent.
