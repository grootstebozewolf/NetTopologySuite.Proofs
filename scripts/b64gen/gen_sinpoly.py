#!/usr/bin/env python3
# scripts/b64gen/gen_sinpoly.py -- generator of theories-flocq/B64_SinPoly.v: degree-21 sine polynomial facts (S1/S2).
# Usage: python3 scripts/b64gen/gen_sinpoly.py OUT_V
# Every numeric constant (binary64 literals, bound chains, rational
# enclosures) is computed exactly with fractions.Fraction; the Rocq kernel
# checks the emitted file, so correctness does not depend on this script --
# it exists so that a degree, a cap (X_F) or a budget can be changed and
# re-derived.  scripts/b64gen/check.py regenerates everything and diffs it
# against the committed files (part of `make ci-guards`).
# AI assistance disclosure: AI-drafted; human review pending.
from fractions import Fraction as F
import math, sys
PI=F("3.14159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798")
u=F(1,2**53); e0b=F(1,2**106)
NC=11
Z=F(41,16)
def lit53(d):
    a=abs(F(d)); e=math.floor(math.log2(a))
    while F(2)**e>a: e-=1
    while F(2)**(e+1)<=a: e+=1
    E=e-52; M=a/F(2)**E; assert M.denominator==1 and 2**52<=M<2**53
    return (d<0, int(M), E)
cs=[]; exact=[]
for k in range(NC):
    ex=F((-1)**k, math.factorial(2*k+1)); d=float(ex)
    cs.append((F(d),)+lit53(d)); exact.append(ex)
mexp=[]
for (d,s,M,E) in cs:
    k=0
    while F(1,2**(k+1))>=abs(d): k+=1
    mexp.append(k)
ms=[F(1,2**k) for k in mexp]
def mlit(k): return "1" if k==0 else f"/ {2**k}"
def Rq(x):
    if x==0: return "0"
    return f"({x.numerator} / {x.denominator})" if x.denominator!=1 else f"{x.numerator}"
# chains
M={NC-1:ms[NC-1]}; E={NC-1:F(0)}; L={NC-1:F(0)}
for k in range(NC-2,-1,-1):
    M[k]=M[k+1]*Z+ms[k]
    ex=Z*E[k+1]+u*((M[k+1]+E[k+1])*Z)+e0b+(u*((M[k+1]+E[k+1])*Z*(1+u)+e0b+ms[k])+e0b)
    E[k]=F(math.ceil(ex*2**80),2**80)
    L[k]=L[k+1]*Z+M[k+1]
assert E[0]<=F(1,2**51), float(E[0]/u)
assert M[0]<=F(7,4) and L[0]<=F(11,32)
# coefficient deltas
dex=[]
for (d,s,M_,E_),ex in zip(cs,exact):
    dd=abs(d-ex); k=0
    if dd==0: dex.append(None); continue
    while F(1,2**(k+1))>=dd: k+=1
    dex.append(k)
ds=[F(0) if k is None else F(1,2**k) for k in dex]
def hM(l): return F(0) if not l else hM(l[1:])*Z+l[0]
Dco=hM(ds)
Dcob=F(math.ceil(Dco*2**80),2**80)
# pi enclosure via Machin 2_3_7, N=10
def tg(n): return 2*F(1,3)**(2*n+1)/(2*n+1)+F(1,7)**(2*n+1)/(2*n+1)
def S(n): return sum(((-1)**i)*tg(i) for i in range(n+1))
N=10
lo4=4*S(2*N+1); hi4=4*S(2*N)
assert lo4<=PI<=hi4
s1,M1,E1=lit53(float(PI)) # not used
out=[]
w=out.append
w("""(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_SinPoly
   ----------------------------------------------------------------------------
   S1 instance and S2 polynomial facts: the degree-21 sine polynomial on the
   B64_Horner kernel.  sin r ~ r * P(r^2),  P(z) = sum_{k=0..10}
   (-1)^k z^k / (2k+1)!, for |r| <= 8/5 (encloses the mod-pi reduced range
   |r| <= pi/2 + slack used by B64_Sin.v), so |z| <= 41/16.

   sp_c0 .. sp_c10 are the round-to-nearest binary64 values of
   (-1)^k / (2k+1)!, as exact (sign, 53-bit mantissa, exponent) literals.
   Budget lines proved here, each a separate theorem:
     b64_sinpoly_eval_err   binary64 Horner vs the same coefficients exact,
                            <= 2^-51 (exact recursive bound ~3.47 u)
     sp_coef_err            binary64 coefficients vs (-1)^k/(2k+1)!
     sp_trunc               r P(r^2) vs sin r: <= (8/5)^23 / 23!  (sin_bound)
     sp_M_bound, sp_L_bound magnitude <= 7/4 and Lipschitz <= 11/32 of the
                            binary64-coefficient polynomial on |z| <= 41/16
     sp_pi_bounds           a rational enclosure of PI (Machin 2-3-7, N = 10)
   Every bound chain is checked one Horner level at a time
   (B64_Horner.hz_E_cons_le), the constants are generated exactly.
   claimId: s1-b64-horner.  witness: b64_sinpoly_eval_err.
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia ZArith List Machin.
From Flocq Require Import Core IEEE754.Binary IEEE754.BinarySingleNaN.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
  B64_AbsErr B64_Horner.
Import ListNotations.
Local Open Scope R_scope.

Local Notation B2R := (Binary.B2R prec emax).
Local Notation fin := (Binary.is_finite prec emax).

(* (-1)^k / (2k+1)!, rounded to nearest binary64. *)""")
for k,(d,s,M_,E_) in enumerate(cs):
    w(f"Definition sp_c{k} : binary64 :=\n  Binary.B754_finite prec emax {'true' if s else 'false'} {M_} ({E_}) eq_refl.")
w("\nDefinition sp_coeffs : list binary64 :=\n  ["+"; ".join(f"sp_c{k}" for k in range(NC))+"].\n")
w("(* Dyadic magnitude bounds |sp_c_k| <= sp_m_k, as suffixes S_k = [m_k; ...]. *)")
w(f"Definition sp_S{NC-1} : list R := [{mlit(mexp[NC-1])}].")
for k in range(NC-2,-1,-1):
    w(f"Definition sp_S{k} : list R := {mlit(mexp[k])} :: sp_S{k+1}.")
w("Definition sp_ms : list R := sp_S0.\nDefinition sp_Z : R := 41 / 16.\n")
w("""Lemma sp_coeffs_ok : hz_coeffs_ok sp_coeffs sp_ms.
Proof.
  unfold hz_coeffs_ok, sp_coeffs, sp_ms, """+", ".join(f"sp_S{k}" for k in range(NC))+""".
  repeat (apply Forall2_cons;
          [split; [reflexivity|]; cbn; unfold F2R; cbn; apply Rabs_le; split; lra|]).
  apply Forall2_nil.
Qed.

Lemma sp_coeffs_ok_R : Forall2 (fun c m => Rabs c <= m) (map B2R sp_coeffs) sp_ms.
Proof.
  generalize sp_coeffs_ok. unfold hz_coeffs_ok.
  generalize sp_coeffs sp_ms. intros cs ms H.
  induction H as [|c m cs ms [_ Hm] _ IH]; cbn; constructor; assumption.
Qed.

Lemma sp_u_val : b64ae_u = / 9007199254740992.
Proof. unfold b64ae_u. cbn. reflexivity. Qed.

Lemma sp_e0_bounds : 0 < b64ae_e0 <= / 9007199254740992 / 9007199254740992.
Proof.
  unfold b64ae_e0. split; [apply bpow_gt_0|].
  apply Rle_trans with (bpow radix2 (-106)); [apply bpow_le; lia|].
  cbn. lra.
Qed.

Lemma sp_bpow1000 : 4 <= bpow radix2 1000.
Proof.
  apply Rle_trans with (bpow radix2 2); [cbn; lra|]. apply bpow_le. lia.
Qed.

Lemma sp_Z_nonneg : 0 <= sp_Z.
Proof. unfold sp_Z. lra. Qed.
""")
for k in range(NC-1,-1,-1):
    w(f"Lemma sp_S{k}_nonneg : Forall (fun m => 0 <= m) sp_S{k}.\nProof. unfold "+", ".join(f"sp_S{j}" for j in range(k,NC))+". repeat constructor; lra. Qed.")
w("")
# M chain
w(f"Lemma sp_M{NC-1} : hz_M sp_S{NC-1} sp_Z <= {Rq(M[NC-1])}.\nProof. unfold sp_S{NC-1}, sp_Z. cbn [hz_M]. lra. Qed.")
for k in range(NC-2,-1,-1):
    w(f"""Lemma sp_M{k} : hz_M sp_S{k} sp_Z <= {Rq(M[k])}.
Proof.
  change (hz_M sp_S{k} sp_Z) with (hz_M sp_S{k+1} sp_Z * sp_Z + {mlit(mexp[k])}).
  assert (H := sp_M{k+1}). assert (HZ := sp_Z_nonneg).
  assert (hz_M sp_S{k+1} sp_Z * sp_Z <= {Rq(M[k+1])} * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.""")
w("")
# L chain
w(f"Lemma sp_L{NC-1} : hz_L sp_S{NC-1} sp_Z <= 0.\nProof. unfold sp_S{NC-1}. cbn. lra. Qed.")
for k in range(NC-2,-1,-1):
    w(f"""Lemma sp_L{k} : hz_L sp_S{k} sp_Z <= {Rq(L[k])}.
Proof.
  change (hz_L sp_S{k} sp_Z) with (hz_L sp_S{k+1} sp_Z * sp_Z + hz_M sp_S{k+1} sp_Z).
  assert (H := sp_L{k+1}). assert (H2 := sp_M{k+1}). assert (HZ := sp_Z_nonneg).
  assert (hz_L sp_S{k+1} sp_Z * sp_Z <= {Rq(L[k+1])} * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.""")
w("")
# E chain
w(f"Lemma sp_E{NC-1} : hz_E sp_S{NC-1} sp_Z <= 0.\nProof. unfold sp_S{NC-1}. cbn. lra. Qed.")
for k in range(NC-2,-1,-1):
    tail = "[]" if k+1==NC-1 else f"sp_S{k+2}"
    w(f"""Lemma sp_E{k} : hz_E sp_S{k} sp_Z <= {Rq(E[k])}.
Proof.
  pose proof sp_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change sp_S{k} with (({mlit(mexp[k])}) :: ({mlit(mexp[k+1])}) :: {tail}).
    apply (hz_E_cons_le ({mlit(mexp[k])}) _ _ sp_Z {Rq(M[k+1])} {Rq(E[k+1])});
      [exact sp_Z_nonneg
      |apply hz_M_nonneg; [exact sp_S{k+1}_nonneg | exact sp_Z_nonneg]
      |apply hz_E_nonneg; [exact sp_S{k+1}_nonneg | exact sp_Z_nonneg]
      |exact sp_M{k+1} | exact sp_E{k+1}].
  - rewrite sp_u_val. unfold sp_Z. set (e := b64ae_e0) in *. lra.
Qed.""")
w("")
# safe chain
w(f"Lemma sp_safe{NC-1} : hz_safe sp_S{NC-1} sp_Z.\nProof. exact I. Qed.")
for k in range(NC-2,-1,-1):
    w(f"""Lemma sp_safe{k} : hz_safe sp_S{k} sp_Z.
Proof.
  change (hz_safe sp_S{k} sp_Z) with
    (hz_safe sp_S{k+1} sp_Z /\\
     (hz_M sp_S{k+1} sp_Z + hz_E sp_S{k+1} sp_Z) * sp_Z * 2 + {mlit(mexp[k])} + 1
       <= bpow radix2 1000).
  split; [exact sp_safe{k+1}|].
  assert (H1 := sp_M{k+1}). assert (H2 := sp_E{k+1}). assert (HZ := sp_Z_nonneg).
  assert (Hb := sp_bpow1000).
  assert ((hz_M sp_S{k+1} sp_Z + hz_E sp_S{k+1} sp_Z) * sp_Z * 2
          <= ({Rq(M[k+1])} + {Rq(E[k+1])}) * sp_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold sp_Z in *. lra.
Qed.""")
w(f"""
Lemma sp_M_bound : hz_M sp_ms sp_Z <= 7 / 4.
Proof. unfold sp_ms. eapply Rle_trans; [exact sp_M0|]. lra. Qed.

Lemma sp_L_bound : hz_L sp_ms sp_Z <= 11 / 32.
Proof. unfold sp_ms. eapply Rle_trans; [exact sp_L0|]. lra. Qed.

Lemma sp_E_bound : hz_E sp_ms sp_Z <= bpow radix2 (-51).
Proof.
  unfold sp_ms. eapply Rle_trans; [exact sp_E0|].
  replace (bpow radix2 (-51)) with (/ 2251799813685248) by (cbn; reflexivity).
  lra.
Qed.

(* WITNESS {{"claimId":"s1-b64-horner","topic":"numerics","lemma":"b64_sinpoly_eval_err","title":"The binary64 Horner evaluation of the degree-21 sine polynomial (binary64 coefficients of (-1)^k/(2k+1)!, z with |z| <= 41/16) is finite and within 2^-51 of the same coefficients evaluated exactly at the same z","file":"theories-flocq/B64_SinPoly.v","witness":"b64_sinpoly_eval_err","board":"ADR-0006"}} *)
Theorem b64_sinpoly_eval_err : forall z : binary64,
  fin z = true -> Rabs (B2R z) <= 41 / 16 ->
  fin (b64_horner sp_coeffs z) = true /\\
  Rabs (B2R (b64_horner sp_coeffs z) - hz_horner_R (map B2R sp_coeffs) (B2R z))
    <= bpow radix2 (-51).
Proof.
  intros z Fz Hz.
  destruct (b64_horner_err sp_coeffs sp_ms z sp_Z sp_coeffs_ok Fz Hz
              sp_Z_nonneg sp_safe0) as [F E].
  split; [exact F|]. eapply Rle_trans; [exact E | exact sp_E_bound].
Qed.
""")
# exact coefficients and deltas
def rexact(ex):
    if ex==1: return "1"
    return ("- " if ex<0 else "")+f"/ {abs(ex.denominator)}"
w("(* The mathematical coefficients (-1)^k / (2k+1)!. *)")
w("Definition sp_exact : list R :=\n  ["+"; ".join(rexact(e) for e in exact)+"].\n")
w("Definition sp_delta : list R :=\n  ["+";\n   ".join(f"B2R sp_c{k} - ({rexact(exact[k])})" for k in range(NC))+"].\n")
w("""Lemma sp_delta_eq : forall x,
  hz_horner_R (map B2R sp_coeffs) x - hz_horner_R sp_exact x = hz_horner_R sp_delta x.
Proof. intro x. unfold sp_coeffs, sp_exact, sp_delta. cbn [map hz_horner_R]. ring. Qed.
""")
dlist=[("0" if k is None else mlit(k)) for k in dex]
w("Definition sp_ds : list R :=\n  ["+"; ".join(dlist)+"].\n")
w("""Lemma sp_delta_ok : Forall2 (fun c m => Rabs c <= m) sp_delta sp_ds.
Proof.
  unfold sp_delta, sp_ds, """+", ".join(f"sp_c{k}" for k in range(NC))+""".
  repeat (apply Forall2_cons; [cbn [Binary.B2R]; unfold F2R; cbn; apply Rabs_le; split; lra|]).
  apply Forall2_nil.
Qed.
""")
w(f"""Lemma sp_ds_M : hz_M sp_ds sp_Z <= {Rq(Dcob)}.
Proof. unfold sp_ds, sp_Z. cbn [hz_M]. lra. Qed.

(* Coefficient representation line. *)
Lemma sp_coef_err : forall x, Rabs x <= 41 / 16 ->
  Rabs (hz_horner_R (map B2R sp_coeffs) x - hz_horner_R sp_exact x) <= {Rq(Dcob)}.
Proof.
  intros x Hx. rewrite sp_delta_eq.
  eapply Rle_trans; [apply (hz_horner_R_bound_R _ sp_ds x sp_Z sp_delta_ok); exact Hx|].
  exact sp_ds_M.
Qed.
""")
# pi enclosure
w(f"""(* A rational enclosure of PI: Machin 2-3-7 alternating series, N = 10. *)
Definition sp_pi_lo : R := {Rq(lo4)}.
Definition sp_pi_hi : R := {Rq(hi4)}.

Lemma sp_pi_bounds : sp_pi_lo <= PI <= sp_pi_hi.
Proof.
  destruct (PI_2_3_7_ineq {N}) as [Hlo Hhi].
  cbn [sum_f_R0 Nat.mul Nat.add] in Hlo, Hhi.
  unfold tg_alt, PI_2_3_7_tg, Ratan_seq in Hlo, Hhi.
  cbn [Nat.mul Nat.add] in Hlo, Hhi.
  repeat match type of Hlo with context [INR ?n] => rewrite (INR_IZR_INZ n) in Hlo end.
  repeat match type of Hhi with context [INR ?n] => rewrite (INR_IZR_INZ n) in Hhi end.
  cbn [Z.of_nat Pos.of_succ_nat PosDef.Pos.succ pow] in Hlo, Hhi.
  match type of Hlo with ?S <= _ => replace S with (51581119789803224612114684299600885385863055381143849276283104725224398 / 65675121478098948134211473850539027996520477148407130764892740641180475) in Hlo by field end.
  match type of Hhi with _ <= ?S => replace S with (2720092801234152012451826714510753160901751942958469528830117289321 / 3463329719880765075895769332412541686258528563434431828555225472825) in Hhi by field end.
  unfold sp_pi_lo, sp_pi_hi. split; lra.
Qed.
""")
# truncation
f23=math.factorial(23); f25=math.factorial(25)
w(f"""Lemma sp_INR_fact_S : forall n, INR (fact (S n)) = INR (S n) * INR (fact n).
Proof. intro n. rewrite fact_simpl, mult_INR. reflexivity. Qed.

Lemma sp_INR_fact_0 : INR (fact 0) = 1.
Proof. reflexivity. Qed.

(* r P(r^2) with the exact coefficients is sin_approx up to one / two terms. *)
Lemma sp_sin_approx_11 : forall a,
  sin_approx a 11 = a * hz_horner_R sp_exact (a * a) - a ^ 23 / {f23}.
Proof.
  intro a. unfold sin_approx, sin_term. cbn [sum_f_R0 Nat.mul Nat.add].
  repeat match goal with |- context [INR (fact (S ?n))] => rewrite (sp_INR_fact_S n) end.
  rewrite ?sp_INR_fact_0.
  repeat match goal with |- context [INR ?n] => rewrite (INR_IZR_INZ n) end.
  cbn [Z.of_nat Pos.of_succ_nat PosDef.Pos.succ]. unfold sp_exact. cbn [hz_horner_R].
  field.
Qed.

Lemma sp_sin_approx_12 : forall a,
  sin_approx a 12 = a * hz_horner_R sp_exact (a * a) - a ^ 23 / {f23} + a ^ 25 / {f25}.
Proof.
  intro a. unfold sin_approx, sin_term. cbn [sum_f_R0 Nat.mul Nat.add].
  repeat match goal with |- context [INR (fact (S ?n))] => rewrite (sp_INR_fact_S n) end.
  rewrite ?sp_INR_fact_0.
  repeat match goal with |- context [INR ?n] => rewrite (INR_IZR_INZ n) end.
  cbn [Z.of_nat Pos.of_succ_nat PosDef.Pos.succ]. unfold sp_exact. cbn [hz_horner_R].
  field.
Qed.

Lemma sp_poly_odd : forall a,
  (- a) * hz_horner_R sp_exact ((- a) * (- a)) = - (a * hz_horner_R sp_exact (a * a)).
Proof. intro a. replace ((- a) * (- a)) with (a * a) by ring. ring. Qed.

(* Truncation line. *)
Lemma sp_trunc : forall r, Rabs r <= 8 / 5 ->
  Rabs (r * hz_horner_R sp_exact (r * r) - sin r) <= (8 / 5) ^ 23 / {f23}.
Proof.
  assert (Hpos : forall a, 0 <= a <= 8 / 5 ->
            Rabs (a * hz_horner_R sp_exact (a * a) - sin a) <= (8 / 5) ^ 23 / {f23}).
  {{ intros a Ha.
    assert (Hpi : 8 / 5 <= PI)
      by (pose proof sp_pi_bounds as [H _]; unfold sp_pi_lo in H; lra).
    destruct (sin_bound a 5 ltac:(lra) ltac:(lra)) as [H1 H2].
    change (2 * 5 + 1)%nat with 11%nat in H1. change (2 * (5 + 1))%nat with 12%nat in H2.
    rewrite sp_sin_approx_11 in H1. rewrite sp_sin_approx_12 in H2.
    assert (P23 : 0 <= a ^ 23) by (apply pow_le; lra).
    assert (M23 : a ^ 23 <= (8 / 5) ^ 23) by (apply pow_incr; lra).
    assert (A25 : a ^ 25 / {f25} <= a ^ 23 / {f23}).
    {{ replace (a ^ 25) with (a ^ 23 * (a * a)) by ring.
      assert (a * a <= 64 / 25) by nra.
      apply Rmult_le_reg_r with ({f25}); [lra|].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra.
      assert (a ^ 23 * (a * a) <= a ^ 23 * (64 / 25)) by (apply Rmult_le_compat_l; lra).
      lra. }}
    assert (0 <= a ^ 25 / {f25})
      by (apply Rmult_le_pos; [apply pow_le; lra | lra]).
    apply Rabs_le. split; lra. }}
  intros r Hr.
  destruct (Rle_lt_dec 0 r) as [H0|H0].
  - apply Hpos. apply Rabs_le_inv in Hr. lra.
  - replace (r * hz_horner_R sp_exact (r * r) - sin r)
      with (- ((- r) * hz_horner_R sp_exact ((- r) * (- r)) - sin (- r)))
      by (rewrite sp_poly_odd, sin_neg; ring).
    rewrite Rabs_Ropp. apply Hpos. apply Rabs_le_inv in Hr. lra.
Qed.
""")
w("Print Assumptions sp_coeffs_ok.\nPrint Assumptions b64_sinpoly_eval_err.\nPrint Assumptions sp_coef_err.\nPrint Assumptions sp_pi_bounds.\nPrint Assumptions sp_trunc.\nPrint Assumptions sp_M_bound.\nPrint Assumptions sp_L_bound.")
open(sys.argv[1],'w').write("\n".join(out)+"\n")
print("Eh(u)",float(E[0]/u),"M",float(M[0]),"L",float(L[0]),"Dco",float(Dcob),"dex",dex)
print("pi width",float(hi4-lo4))
