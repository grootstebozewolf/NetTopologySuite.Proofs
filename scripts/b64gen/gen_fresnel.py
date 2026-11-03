#!/usr/bin/env python3
# scripts/b64gen/gen_fresnel.py -- generator of theories-flocq/B64_Fresnel.v: binary64 canonical Fresnel evaluator (S7).
# Usage: python3 scripts/b64gen/gen_fresnel.py OUT_V INFO_JSON
# Every numeric constant (binary64 literals, bound chains, rational
# enclosures) is computed exactly with fractions.Fraction; the Rocq kernel
# checks the emitted file, so correctness does not depend on this script --
# it exists so that a degree, a cap (X_F) or a budget can be changed and
# re-derived.  scripts/b64gen/check.py regenerates everything and diffs it
# against the committed files (part of `make ci-guards`).
# AI assistance disclosure: AI-drafted; human review pending.
from fractions import Fraction as F
import math, sys, json
u=F(1,2**53); e0b=F(1,2**1000)
info={k:{kk:F(*vv) for kk,vv in v.items()} for k,v in json.load(open(sys.argv[2])).items()}
C=info['frc']; S=info['frs']
def up64(x):
    e=math.floor(math.log2(x)); s=63-e
    return F(math.ceil(x*F(2)**s))/F(2)**s
def Rq(x):
    if x==0: return "0"
    return f"({x.numerator} / {x.denominator})" if x.denominator!=1 else f"{x.numerator}"
X=F(5,2); U="/ 9007199254740992"
Dz = u*F(485,4) + 14*e0b
Tb=F(313,50)
TC = X**81/(math.factorial(40)*81)
TS = X**79/(math.factorial(39)*79)
EC = u*X*(C['MB']+C['EB']) + e0b + X*C['EB'] + X*C['LB']*Dz + X*C['D'] + TC
W = X*Tb  # |x t| <= 313/20
Bw = u*W + e0b + X*(u*F(25,4)+e0b)
ES = u*16*(S['MB']+S['EB']) + e0b + Bw*(S['MB']+S['EB']) + F(125,8)*(S['EB'] + S['LB']*Dz + S['D']) + TS
ECb=up64(EC); ESb=up64(ES)
assert ECb<=F(1,2**42) and ESb<=F(1,2**42)
print("EC u",float(EC/u),"ES u",float(ES/u),"TC",float(TC),"TS",float(TS), file=sys.stderr)
f40=math.factorial(40); f39=math.factorial(39)
o=[]; w=o.append
w(f"""(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_Fresnel
   ----------------------------------------------------------------------------
   S7: binary64 canonical Fresnel integrals with machine-checked absolute
   error bounds (claimId: s7-b64-fresnel, witness: b64_fresnel_C_err).

     b64_fresnel_C_err : F 0 = 0 -> (forall s, F' s = cos (s s)) ->
                         fresnel_accept_b x = true ->
                         |B2R (b64_fresnel_C x) - F (B2R x)| <= 2^-42
     b64_fresnel_S_err : the same with sin (s s)

   F is any primitive (cloth_Icos of a clothoid with cloth_a c = 1 is one;
   S8 maps a general clothoid onto this canonical problem).

   Intake X_F = 5/2 (fresnel_accept_b: -5/2 <= x <= 5/2, false on NaN and
   infinities).  Geometrically x^2 = s^2 / (2 A^2) = |psi(s)|, so the intake
   is |psi| <= 25/4: at most 6.25 rad of tangent rotation measured from the
   inflection point.  Transition curves in practice have tau << 1 rad; the
   corpus extreme (LENGTH_UNIFIED fixture A = 1, s = 3.25: psi = 5.28 rad,
   x = 2.298) is evidence the cap is not too tight, not its definition.
   X_F = 2 (psi <= 4 rad) would decline that fixture; 5/2 costs ~3.5 bits
   against 2 (z = x^4 <= 39 makes Horner cancel).  Outside:
   DECLINE_FRESNEL_RANGE; asymptotics stay deferred (D2/D4).

   Algorithm (RNE binary64, extractable, no FMA):
     t = x*x, z = t*t,  C = x * P(z),  S = (x*t) * Q(z)   (B64_FresnelPoly).
   Budget (units u = 2^-53): C ~{float(EC/u):.0f} u, S ~{float(ES/u):.0f} u, each stated as
   2^-42 (rounded outward): final product, Horner, z rounding through the
   Lipschitz bound, coefficients, truncation (FresnelSeries.fz_C_rem /
   fz_S_rem at n = 19 / 18).
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia ZArith List Factorial.
From Stdlib Require Import Ranalysis1.
From Flocq Require Import Core IEEE754.Binary IEEE754.BinarySingleNaN.
From NTS.Proofs Require Import FresnelSeries.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
  B64_AbsErr B64_Horner B64_SinPoly B64_FresnelPoly.
Import ListNotations.
Local Open Scope R_scope.

Local Notation B2R := (Binary.B2R prec emax).
Local Notation fin := (Binary.is_finite prec emax).

(* -------------------------------------------------------------------------- *)
(* §1  The evaluator and its intake.                                          *)
(* -------------------------------------------------------------------------- *)

Definition fr_t (x : binary64) : binary64 := b64_mult x x.
Definition fr_z (x : binary64) : binary64 := b64_mult (fr_t x) (fr_t x).

Definition b64_fresnel_C (x : binary64) : binary64 :=
  b64_mult x (b64_horner frc_coeffs (fr_z x)).
Definition b64_fresnel_S (x : binary64) : binary64 :=
  b64_mult (b64_mult x (fr_t x)) (b64_horner frs_coeffs (fr_z x)).

(* 5/2 and -5/2 *)
Definition fr_X : binary64 :=
  Binary.B754_finite prec emax false 5629499534213120 (-51) eq_refl.
Definition fr_mX : binary64 :=
  Binary.B754_finite prec emax true 5629499534213120 (-51) eq_refl.

Lemma fr_X_R : B2R fr_X = 5 / 2 /\\ B2R fr_mX = - (5 / 2).
Proof. unfold fr_X, fr_mX. cbn [Binary.B2R]. unfold F2R. cbn. split; lra. Qed.

Definition fresnel_accept_b (x : binary64) : bool := b64_le fr_mX x && b64_le x fr_X.

Lemma fresnel_accept_ok : forall x, fresnel_accept_b x = true ->
  fin x = true /\\ Rabs (B2R x) <= 5 / 2.
Proof.
  intros x H.
  assert (Fx : fin x = true).
  {{ destruct x as [s|s|s pl Hpl|s m e Hb]; try reflexivity;
      unfold fresnel_accept_b in H; destruct s; vm_compute in H; discriminate H. }}
  split; [exact Fx|].
  unfold fresnel_accept_b in H. apply andb_prop in H as [Hlo Hhi].
  destruct fr_X_R as [Ex Em].
  apply b64ae_le_true in Hlo; [|reflexivity|exact Fx].
  apply b64ae_le_true in Hhi; [|exact Fx|reflexivity].
  rewrite Em in Hlo. rewrite Ex in Hhi. apply Rabs_le. split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The arguments t = x*x and z = t*t.                                     *)
(* -------------------------------------------------------------------------- *)

Definition fr_Dz : R := {U} * (485 / 4) + 14 * b64ae_e0.

Lemma fr_t_alg : forall xr tr e,
  0 < e <= / {2**1000} -> Rabs xr <= 5 / 2 ->
  Rabs (tr - xr * xr) <= {U} * (25 / 4) + e ->
  Rabs tr <= 313 / 50 /\\ Rabs (tr + xr * xr) <= 13.
Proof.
  intros xr tr e He Hx Ht.
  assert (Bxx : Rabs (xr * xr) <= 5 / 2 * (5 / 2)) by (apply b64ae_abs_mult_le; assumption).
  pose proof (Rabs_triang_inv tr (xr * xr)).
  split; [lra|].
  pose proof (Rabs_triang tr (xr * xr)). lra.
Qed.

Lemma fr_z_alg : forall xr tr zr e,
  0 < e <= / {2**1000} -> Rabs xr <= 5 / 2 ->
  Rabs (tr - xr * xr) <= {U} * (25 / 4) + e ->
  Rabs (tr + xr * xr) <= 13 ->
  Rabs (zr - tr * tr) <= {U} * 40 + e ->
  Rabs (zr - xr * xr * (xr * xr)) <= {U} * (485 / 4) + 14 * e /\\
  Rabs zr <= 40.
Proof.
  intros xr tr zr e He Hx Ht Hs Hz.
  assert (P : Rabs ((tr - xr * xr) * (tr + xr * xr)) <= ({U} * (25 / 4) + e) * 13)
    by (apply b64ae_abs_mult_le; assumption).
  assert (B4 : Rabs (xr * xr * (xr * xr)) <= 5 / 2 * (5 / 2) * (5 / 2 * (5 / 2))).
  {{ apply b64ae_abs_mult_le; apply b64ae_abs_mult_le; assumption. }}
  assert (D : Rabs (zr - xr * xr * (xr * xr)) <= {U} * (485 / 4) + 14 * e).
  {{ replace (zr - xr * xr * (xr * xr))
      with ((zr - tr * tr) + (tr - xr * xr) * (tr + xr * xr)) by ring.
    pose proof (Rabs_triang (zr - tr * tr) ((tr - xr * xr) * (tr + xr * xr))) as T.
    lra. }}
  split; [exact D|].
  pose proof (Rabs_triang_inv zr (xr * xr * (xr * xr))). lra.
Qed.

Lemma fr_tz_facts : forall x, fin x = true -> Rabs (B2R x) <= 5 / 2 ->
  fin (fr_t x) = true /\\
  Rabs (B2R (fr_t x) - B2R x * B2R x) <= {U} * (25 / 4) + b64ae_e0 /\\
  Rabs (B2R (fr_t x)) <= 313 / 50 /\\
  fin (fr_z x) = true /\\
  Rabs (B2R (fr_z x) - B2R x * B2R x * (B2R x * B2R x)) <= fr_Dz /\\
  Rabs (B2R (fr_z x)) <= 40.
Proof.
  intros x Fx Hx.
  pose proof sp_u_val as Uv. pose proof fr_e0_bounds as [He0 He1].
  pose proof fr_bpow1000 as Hb.
  assert (Bxx : Rabs (B2R x * B2R x) <= 5 / 2 * (5 / 2)) by (apply b64ae_abs_mult_le; assumption).
  destruct (b64ae_mult_err x x Fx Fx ltac:(lra)) as [Ft Et].
  pose proof (b64ae_u_mul_le _ _ Bxx) as Ut. rewrite Uv in Ut, Et.
  assert (Et' : Rabs (B2R (b64_mult x x) - B2R x * B2R x) <= {U} * (25 / 4) + b64ae_e0) by lra.
  destruct (fr_t_alg (B2R x) (B2R (b64_mult x x)) b64ae_e0 (conj He0 He1) Hx Et') as [Bt Bs].
  assert (Btt : Rabs (B2R (b64_mult x x) * B2R (b64_mult x x)) <= 313 / 50 * (313 / 50))
    by (apply b64ae_abs_mult_le; assumption).
  destruct (b64ae_mult_err (b64_mult x x) (b64_mult x x) Ft Ft ltac:(lra)) as [Fz Ez].
  pose proof (b64ae_u_mul_le _ _ Btt) as Uz. rewrite Uv in Uz, Ez.
  assert (Ez' : Rabs (B2R (b64_mult (b64_mult x x) (b64_mult x x))
                      - B2R (b64_mult x x) * B2R (b64_mult x x)) <= {U} * 40 + b64ae_e0) by lra.
  destruct (fr_z_alg (B2R x) (B2R (b64_mult x x)) (B2R (b64_mult (b64_mult x x) (b64_mult x x)))
              b64ae_e0 (conj He0 He1) Hx Et' Bs Ez') as [Dz Bz].
  unfold fr_z, fr_t, fr_Dz. auto 7.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Truncation constants.                                                  *)
(* -------------------------------------------------------------------------- *)

Lemma fr_fact40 : INR (fact 40) = {f40}.
Proof.
  repeat match goal with |- context [INR (fact (S ?n))] => rewrite (fr_INR_fact_S n) end.
  replace (INR (fact 0)) with 1 by reflexivity.
  repeat match goal with |- context [INR ?n] => rewrite (INR_IZR_INZ n) end.
  cbn [Z.of_nat Pos.of_succ_nat PosDef.Pos.succ]. ring.
Qed.

Lemma fr_fact39 : INR (fact 39) = {f39}.
Proof.
  repeat match goal with |- context [INR (fact (S ?n))] => rewrite (fr_INR_fact_S n) end.
  replace (INR (fact 0)) with 1 by reflexivity.
  repeat match goal with |- context [INR ?n] => rewrite (INR_IZR_INZ n) end.
  cbn [Z.of_nat Pos.of_succ_nat PosDef.Pos.succ]. ring.
Qed.

Lemma fr_TC : forall xr, Rabs xr <= 5 / 2 ->
  Rabs 1 ^ (2 * 19 + 2) * Rabs xr ^ (4 * 19 + 5)
    / (INR (fact (2 * 19 + 2)) * INR (4 * 19 + 5)) <= {Rq(TC)}.
Proof.
  intros xr Hx. cbn [Nat.mul Nat.add]. rewrite Rabs_R1, pow1, fr_fact40.
  rewrite (INR_IZR_INZ 81). cbn [Z.of_nat Pos.of_succ_nat PosDef.Pos.succ].
  assert (A : Rabs xr ^ 81 <= (5 / 2) ^ 81) by (apply pow_incr; split; [apply Rabs_pos | exact Hx]).
  replace ((5 / 2) ^ 81) with {Rq(X**81)} in A by (cbn [pow]; field).
  unfold Rdiv. rewrite Rmult_1_l.
  apply Rle_trans with ({Rq(X**81)} * / ({f40} * 81)).
  - apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; lra | exact A].
  - right. field.
Qed.

Lemma fr_TS : forall xr, Rabs xr <= 5 / 2 ->
  Rabs 1 ^ (2 * 18 + 3) * Rabs xr ^ (4 * 18 + 7)
    / (INR (fact (2 * 18 + 3)) * INR (4 * 18 + 7)) <= {Rq(TS)}.
Proof.
  intros xr Hx. cbn [Nat.mul Nat.add]. rewrite Rabs_R1, pow1, fr_fact39.
  rewrite (INR_IZR_INZ 79). cbn [Z.of_nat Pos.of_succ_nat PosDef.Pos.succ].
  assert (A : Rabs xr ^ 79 <= (5 / 2) ^ 79) by (apply pow_incr; split; [apply Rabs_pos | exact Hx]).
  replace ((5 / 2) ^ 79) with {Rq(X**79)} in A by (cbn [pow]; field).
  unfold Rdiv. rewrite Rmult_1_l.
  apply Rle_trans with ({Rq(X**79)} * / ({f39} * 79)).
  - apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; lra | exact A].
  - right. field.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  C.                                                                     *)
(* -------------------------------------------------------------------------- *)

Definition fr_EC : R := {Rq(ECb)}.

Lemma fr_C_alg : forall (xr zr pr rr Pz Pq Eq Fx e : R),
  0 < e <= / {2**1000} -> Rabs xr <= 5 / 2 ->
  Rabs (rr - xr * pr) <= {U} * (5 / 2 * ({Rq(C['MB'])} + {Rq(C['EB'])})) + e ->
  Rabs (pr - Pz) <= {Rq(C['EB'])} ->
  Rabs (Pz - Pq) <= {Rq(C['LB'])} * Rabs (zr - xr * xr * (xr * xr)) ->
  Rabs (zr - xr * xr * (xr * xr)) <= {U} * (485 / 4) + 14 * e ->
  Rabs (Pq - Eq) <= {Rq(C['D'])} ->
  Rabs (xr * Eq - Fx) <= {Rq(TC)} ->
  Rabs (rr - Fx) <= fr_EC.
Proof.
  intros xr zr pr rr Pz Pq Eq Fx e He Hx L1 Ep Lip Dz Ec Et.
  assert (L2 : Rabs (xr * (pr - Pz)) <= 5 / 2 * {Rq(C['EB'])})
    by (apply b64ae_abs_mult_le; assumption).
  assert (L3 : Rabs (xr * (Pz - Pq)) <= 5 / 2 * ({Rq(C['LB'])} * ({U} * (485 / 4) + 14 * e))).
  {{ apply b64ae_abs_mult_le; [exact Hx|]. eapply Rle_trans; [exact Lip|].
    apply Rmult_le_compat_l; [lra | exact Dz]. }}
  assert (L4 : Rabs (xr * (Pq - Eq)) <= 5 / 2 * {Rq(C['D'])})
    by (apply b64ae_abs_mult_le; assumption).
  replace (rr - Fx) with ((rr - xr * pr) + xr * (pr - Pz) + xr * (Pz - Pq)
                          + xr * (Pq - Eq) + (xr * Eq - Fx)) by ring.
  pose proof (Rabs_triang ((rr - xr * pr) + xr * (pr - Pz) + xr * (Pz - Pq) + xr * (Pq - Eq))
                          (xr * Eq - Fx)) as T1.
  pose proof (Rabs_triang ((rr - xr * pr) + xr * (pr - Pz) + xr * (Pz - Pq)) (xr * (Pq - Eq))) as T2.
  pose proof (Rabs_triang ((rr - xr * pr) + xr * (pr - Pz)) (xr * (Pz - Pq))) as T3.
  pose proof (Rabs_triang (rr - xr * pr) (xr * (pr - Pz))) as T4.
  unfold fr_EC. lra.
Qed.

(* WITNESS {{"claimId":"s7-b64-fresnel","topic":"numerics","lemma":"b64_fresnel_C_err","title":"Binary64 canonical Fresnel integrals: for |x| <= 5/2 (fresnel_accept_b; tangent rotation |psi| = x^2 <= 25/4 rad) b64_fresnel_C / b64_fresnel_S are finite and within 2^-42 of every primitive F of cos(s^2) / sin(s^2) with F 0 = 0","file":"theories-flocq/B64_Fresnel.v","witness":"b64_fresnel_C_err","board":"ADR-0006"}} *)
Theorem b64_fresnel_C_err : forall (F : R -> R),
  F 0 = 0 -> (forall s, derivable_pt_lim F s (cos (s * s))) ->
  forall x, fresnel_accept_b x = true ->
  fin (b64_fresnel_C x) = true /\\
  Rabs (B2R (b64_fresnel_C x) - F (B2R x)) <= bpow radix2 (-42).
Proof.
  intros F F0 DF x Hacc.
  destruct (fresnel_accept_ok x Hacc) as [Fx Hx].
  pose proof sp_u_val as Uv. pose proof fr_e0_bounds as [He0 He1].
  pose proof fr_bpow1000 as Hb.
  destruct (fr_tz_facts x Fx Hx) as [_ [_ [_ [Fz [Dz Bz]]]]].
  destruct (frc_eval_err _ Fz Bz) as [Fp Ep].
  assert (Hq : Rabs (B2R x * B2R x * (B2R x * B2R x)) <= 40).
  {{ assert (Rabs (B2R x * B2R x * (B2R x * B2R x)) <= 5 / 2 * (5 / 2) * (5 / 2 * (5 / 2)))
      by (apply b64ae_abs_mult_le; apply b64ae_abs_mult_le; assumption).
    lra. }}
  pose proof (frc_P_bound _ Bz) as PB.
  assert (Bp : Rabs (B2R (b64_horner frc_coeffs (fr_z x))) <= {Rq(C['MB'])} + {Rq(C['EB'])}).
  {{ pose proof (Rabs_triang_inv (B2R (b64_horner frc_coeffs (fr_z x)))
                                 (hz_horner_R (map B2R frc_coeffs) (B2R (fr_z x)))). lra. }}
  assert (Bxp : Rabs (B2R x * B2R (b64_horner frc_coeffs (fr_z x)))
                <= 5 / 2 * ({Rq(C['MB'])} + {Rq(C['EB'])})) by (apply b64ae_abs_mult_le; assumption).
  destruct (b64ae_mult_err x _ Fx Fp ltac:(lra)) as [Fr Er].
  pose proof (b64ae_u_mul_le _ _ Bxp) as Ur. rewrite Uv in Ur, Er.
  assert (Trunc := fz_C_rem F 1 19 F0
                     ltac:(intro s; rewrite Rmult_1_l; apply DF) (B2R x)).
  rewrite frc_fz_eq in Trunc. rewrite Rabs_minus_sym in Trunc.
  pose proof (Rle_trans _ _ _ Trunc (fr_TC _ Hx)) as Trunc'. clear Trunc. rename Trunc' into Trunc.
  unfold fr_Dz in Dz.
  split; [exact Fr|].
  eapply Rle_trans.
  - exact (fr_C_alg (B2R x) (B2R (fr_z x)) (B2R (b64_horner frc_coeffs (fr_z x)))
             (B2R (b64_mult x (b64_horner frc_coeffs (fr_z x))))
             (hz_horner_R (map B2R frc_coeffs) (B2R (fr_z x)))
             (hz_horner_R (map B2R frc_coeffs) (B2R x * B2R x * (B2R x * B2R x)))
             (hz_horner_R frc_exact (B2R x * B2R x * (B2R x * B2R x)))
             (F (B2R x)) b64ae_e0 (conj He0 He1) Hx ltac:(lra) Ep
             (frc_P_lip _ _ Bz Hq) Dz (frc_coef_err _ Hq) Trunc).
  - replace (bpow radix2 (-42)) with (/ {2**42}) by (cbn; reflexivity).
    unfold fr_EC. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  S.                                                                     *)
(* -------------------------------------------------------------------------- *)

Definition fr_ES : R := {Rq(ESb)}.

Lemma fr_S_alg : forall (xr tr wr zr qr rr Qz Qq Eq Fx e : R),
  0 < e <= / {2**1000} -> Rabs xr <= 5 / 2 ->
  Rabs (tr - xr * xr) <= {U} * (25 / 4) + e ->
  Rabs (wr - xr * tr) <= {U} * (313 / 20) + e ->
  Rabs qr <= {Rq(S['MB'])} + {Rq(S['EB'])} ->
  Rabs (rr - wr * qr) <= {U} * (16 * ({Rq(S['MB'])} + {Rq(S['EB'])})) + e ->
  Rabs (qr - Qz) <= {Rq(S['EB'])} ->
  Rabs (Qz - Qq) <= {Rq(S['LB'])} * Rabs (zr - xr * xr * (xr * xr)) ->
  Rabs (zr - xr * xr * (xr * xr)) <= {U} * (485 / 4) + 14 * e ->
  Rabs (Qq - Eq) <= {Rq(S['D'])} ->
  Rabs (xr * (xr * xr) * Eq - Fx) <= {Rq(TS)} ->
  Rabs (rr - Fx) <= fr_ES.
Proof.
  intros xr tr wr zr qr rr Qz Qq Eq Fx e He Hx Ht Hw Bq L1 Eqz Lip Dz Ec Et.
  assert (H3 : Rabs (xr * (xr * xr)) <= 5 / 2 * (5 / 2 * (5 / 2)))
    by (apply b64ae_abs_mult_le; [|apply b64ae_abs_mult_le]; assumption).
  assert (Hxt : Rabs (xr * (tr - xr * xr)) <= 5 / 2 * ({U} * (25 / 4) + e))
    by (apply b64ae_abs_mult_le; assumption).
  assert (Hw3 : Rabs (wr - xr * (xr * xr))
                <= {U} * (313 / 20) + e + 5 / 2 * ({U} * (25 / 4) + e)).
  {{ replace (wr - xr * (xr * xr)) with ((wr - xr * tr) + xr * (tr - xr * xr)) by ring.
    pose proof (Rabs_triang (wr - xr * tr) (xr * (tr - xr * xr))). lra. }}
  assert (L2 : Rabs ((wr - xr * (xr * xr)) * qr)
               <= ({U} * (313 / 20) + e + 5 / 2 * ({U} * (25 / 4) + e))
                  * ({Rq(S['MB'])} + {Rq(S['EB'])})) by (apply b64ae_abs_mult_le; assumption).
  assert (L3 : Rabs (xr * (xr * xr) * (qr - Qz)) <= 125 / 8 * {Rq(S['EB'])})
    by (apply b64ae_abs_mult_le; [lra | exact Eqz]).
  assert (L4 : Rabs (xr * (xr * xr) * (Qz - Qq))
               <= 125 / 8 * ({Rq(S['LB'])} * ({U} * (485 / 4) + 14 * e))).
  {{ apply b64ae_abs_mult_le; [lra|]. eapply Rle_trans; [exact Lip|].
    apply Rmult_le_compat_l; [lra | exact Dz]. }}
  assert (L5 : Rabs (xr * (xr * xr) * (Qq - Eq)) <= 125 / 8 * {Rq(S['D'])})
    by (apply b64ae_abs_mult_le; [lra | exact Ec]).
  replace (rr - Fx) with ((rr - wr * qr) + (wr - xr * (xr * xr)) * qr
                          + xr * (xr * xr) * (qr - Qz) + xr * (xr * xr) * (Qz - Qq)
                          + xr * (xr * xr) * (Qq - Eq) + (xr * (xr * xr) * Eq - Fx)) by ring.
  pose proof (Rabs_triang ((rr - wr * qr) + (wr - xr * (xr * xr)) * qr
                           + xr * (xr * xr) * (qr - Qz) + xr * (xr * xr) * (Qz - Qq)
                           + xr * (xr * xr) * (Qq - Eq)) (xr * (xr * xr) * Eq - Fx)) as T1.
  pose proof (Rabs_triang ((rr - wr * qr) + (wr - xr * (xr * xr)) * qr
                           + xr * (xr * xr) * (qr - Qz) + xr * (xr * xr) * (Qz - Qq))
                          (xr * (xr * xr) * (Qq - Eq))) as T2.
  pose proof (Rabs_triang ((rr - wr * qr) + (wr - xr * (xr * xr)) * qr
                           + xr * (xr * xr) * (qr - Qz)) (xr * (xr * xr) * (Qz - Qq))) as T3.
  pose proof (Rabs_triang ((rr - wr * qr) + (wr - xr * (xr * xr)) * qr)
                          (xr * (xr * xr) * (qr - Qz))) as T4.
  pose proof (Rabs_triang (rr - wr * qr) ((wr - xr * (xr * xr)) * qr)) as T5.
  unfold fr_ES. lra.
Qed.

Theorem b64_fresnel_S_err : forall (F : R -> R),
  F 0 = 0 -> (forall s, derivable_pt_lim F s (sin (s * s))) ->
  forall x, fresnel_accept_b x = true ->
  fin (b64_fresnel_S x) = true /\\
  Rabs (B2R (b64_fresnel_S x) - F (B2R x)) <= bpow radix2 (-42).
Proof.
  intros F F0 DF x Hacc.
  destruct (fresnel_accept_ok x Hacc) as [Fx Hx].
  pose proof sp_u_val as Uv. pose proof fr_e0_bounds as [He0 He1].
  pose proof fr_bpow1000 as Hb.
  destruct (fr_tz_facts x Fx Hx) as [Ft [Et [Bt [Fz [Dz Bz]]]]].
  destruct (frs_eval_err _ Fz Bz) as [Fq Eq].
  assert (Hq : Rabs (B2R x * B2R x * (B2R x * B2R x)) <= 40).
  {{ assert (Rabs (B2R x * B2R x * (B2R x * B2R x)) <= 5 / 2 * (5 / 2) * (5 / 2 * (5 / 2)))
      by (apply b64ae_abs_mult_le; apply b64ae_abs_mult_le; assumption).
    lra. }}
  pose proof (frs_P_bound _ Bz) as QB.
  assert (Bq : Rabs (B2R (b64_horner frs_coeffs (fr_z x))) <= {Rq(S['MB'])} + {Rq(S['EB'])}).
  {{ pose proof (Rabs_triang_inv (B2R (b64_horner frs_coeffs (fr_z x)))
                                 (hz_horner_R (map B2R frs_coeffs) (B2R (fr_z x)))). lra. }}
  assert (Bxt : Rabs (B2R x * B2R (fr_t x)) <= 5 / 2 * (313 / 50)) by (apply b64ae_abs_mult_le; assumption).
  destruct (b64ae_mult_err x (fr_t x) Fx Ft ltac:(lra)) as [Fw Ew].
  pose proof (b64ae_u_mul_le _ _ Bxt) as Uw. rewrite Uv in Uw, Ew.
  assert (Ew' : Rabs (B2R (b64_mult x (fr_t x)) - B2R x * B2R (fr_t x)) <= {U} * (313 / 20) + b64ae_e0)
    by lra.
  assert (Bw : Rabs (B2R (b64_mult x (fr_t x))) <= 16).
  {{ pose proof (Rabs_triang_inv (B2R (b64_mult x (fr_t x))) (B2R x * B2R (fr_t x))). lra. }}
  assert (Bwq : Rabs (B2R (b64_mult x (fr_t x)) * B2R (b64_horner frs_coeffs (fr_z x)))
                <= 16 * ({Rq(S['MB'])} + {Rq(S['EB'])})) by (apply b64ae_abs_mult_le; assumption).
  destruct (b64ae_mult_err _ _ Fw Fq ltac:(lra)) as [Fr Er].
  pose proof (b64ae_u_mul_le _ _ Bwq) as Ur. rewrite Uv in Ur, Er.
  assert (Trunc := fz_S_rem F 1 18 F0
                     ltac:(intro s; rewrite Rmult_1_l; apply DF) (B2R x)).
  rewrite frs_fz_eq in Trunc. rewrite Rabs_minus_sym in Trunc.
  pose proof (Rle_trans _ _ _ Trunc (fr_TS _ Hx)) as Trunc'. clear Trunc. rename Trunc' into Trunc.
  unfold fr_Dz in Dz.
  split; [exact Fr|].
  eapply Rle_trans.
  - exact (fr_S_alg (B2R x) (B2R (fr_t x)) (B2R (b64_mult x (fr_t x))) (B2R (fr_z x))
             (B2R (b64_horner frs_coeffs (fr_z x)))
             (B2R (b64_fresnel_S x))
             (hz_horner_R (map B2R frs_coeffs) (B2R (fr_z x)))
             (hz_horner_R (map B2R frs_coeffs) (B2R x * B2R x * (B2R x * B2R x)))
             (hz_horner_R frs_exact (B2R x * B2R x * (B2R x * B2R x)))
             (F (B2R x)) b64ae_e0 (conj He0 He1) Hx Et Ew' Bq ltac:(unfold b64_fresnel_S; lra) Eq
             (frs_P_lip _ _ Bz Hq) Dz (frs_coef_err _ Hq) Trunc).
  - replace (bpow radix2 (-42)) with (/ {2**42}) by (cbn; reflexivity).
    unfold fr_ES. lra.
Qed.

Print Assumptions fresnel_accept_ok.
Print Assumptions fr_tz_facts.
Print Assumptions fr_TC.
Print Assumptions fr_TS.
Print Assumptions b64_fresnel_C_err.
Print Assumptions b64_fresnel_S_err.
""")
out_text="\n".join(o)+"\n"
out_text=out_text.replace(" /  ", " /\\\n  ")
open(sys.argv[1],'w').write(out_text)
