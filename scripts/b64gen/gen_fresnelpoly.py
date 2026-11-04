#!/usr/bin/env python3
# scripts/b64gen/gen_fresnelpoly.py -- generator of theories-flocq/B64_FresnelPoly{,C,S}.v: Fresnel polynomial facts (S7); writes the C / S halves next to OUT_V and the umbrella OUT_V.
# Usage: python3 scripts/b64gen/gen_fresnelpoly.py OUT_V INFO_JSON
# Every numeric constant (binary64 literals, bound chains, rational
# enclosures) is computed exactly with fractions.Fraction; the Rocq kernel
# checks the emitted file, so correctness does not depend on this script --
# it exists so that a degree, a cap (X_F) or a budget can be changed and
# re-derived.  scripts/b64gen/check.py regenerates everything and diffs it
# against the committed files (part of `make ci-guards`).
# AI assistance disclosure: AI-drafted; human review pending.
from fractions import Fraction as F
import math, sys
u=F(1,2**53); e0b=F(1,2**1000)
Z=F(40)
NCC=20; NCS=19
def lit53(d):
    a=abs(F(d)); e=math.floor(math.log2(a))
    while F(2)**e>a: e-=1
    while F(2)**(e+1)<=a: e+=1
    E=e-52; M=a/F(2)**E; assert M.denominator==1 and 2**52<=M<2**53
    return (d<0, int(M), E)
def up64(x):
    if x==0: return F(0)
    e=math.floor(math.log2(x)); s=63-e
    return F(math.ceil(x*F(2)**s))/F(2)**s
def Rq(x):
    if x==0: return "0"
    return f"({x.numerator} / {x.denominator})" if x.denominator!=1 else f"{x.numerator}"
def mexp_of(d):
    k=0
    while F(1,2**(k+1))>=abs(d): k+=1
    return k
def mlit(k): return "1" if k==0 else f"/ {2**k}"
def rexact(ex):
    if ex==1: return "1"
    return ("- " if ex<0 else "")+f"/ {abs(ex.denominator)}"
def build(pfx, exact):
    NC=len(exact)
    cs=[(F(float(ex)),)+lit53(float(ex)) for ex in exact]
    mexp=[mexp_of(c[0]) for c in cs]; ms=[F(1,2**k) for k in mexp]
    M={NC-1:ms[NC-1]}; E={NC-1:F(0)}; L={NC-1:F(0)}
    for k in range(NC-2,-1,-1):
        M[k]=M[k+1]*Z+ms[k]
        ex=Z*E[k+1]+u*((M[k+1]+E[k+1])*Z)+e0b+(u*((M[k+1]+E[k+1])*Z*(1+u)+e0b+ms[k])+e0b)
        E[k]=up64(ex)
        L[k]=L[k+1]*Z+M[k+1]
    dex=[]
    for (d,s,M_,E_),ex in zip(cs,exact):
        dd=abs(d-ex)
        dex.append(None if dd==0 else mexp_of(dd))
    ds=[F(0) if k is None else F(1,2**k) for k in dex]
    def hM(l): return F(0) if not l else hM(l[1:])*Z+l[0]
    D=up64(hM(ds))
    return dict(NC=NC,cs=cs,mexp=mexp,M=M,E=E,L=L,dex=dex,D=D,exact=exact)
C=build("frc",[F((-1)**k, math.factorial(2*k)*(4*k+1)) for k in range(NCC)])
S=build("frs",[F((-1)**k, math.factorial(2*k+1)*(4*k+3)) for k in range(NCS)])
def outb(x): # outward simple bound: next value with 2 significant decimal-ish dyadic
    return up64(x)
HDR_S = """(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_FresnelPolyS
   ----------------------------------------------------------------------------
   S7 polynomial facts, S half: Q(z) = sum_{k<=18} (-1)^k z^k / ((2k+1)! (4k+3)),
   S(x) = x^3 Q(x^4), on the B64_Horner kernel for |z| <= 40.  Shares fr_Z,
   fr_e0_bounds, fr_bpow1000, fr_INR_fact_S with B64_FresnelPolyC.
   claimId: s7-b64-fresnel.  witness: b64_fresnel_C_err (B64_Fresnel.v).
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia ZArith List Factorial.
From Flocq Require Import Core IEEE754.Binary IEEE754.BinarySingleNaN.
From NTS.Proofs Require Import FresnelSeries.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
  B64_AbsErr B64_Horner B64_SinPoly B64_FresnelPolyC.
Import ListNotations.
Local Open Scope R_scope.

Local Notation B2R := (Binary.B2R prec emax).
Local Notation fin := (Binary.is_finite prec emax).
"""
UMB = """(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_FresnelPoly
   ----------------------------------------------------------------------------
   Umbrella for the S7 Fresnel polynomial facts: B64_FresnelPolyC (the C
   series P, shared constants) and B64_FresnelPolyS (the S series Q), split
   by the module-split gate.  No content of its own.
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From NTS.Proofs.Flocq Require Export B64_FresnelPolyC B64_FresnelPolyS.
"""
info={}
out=[]; w=out.append
w("""(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_FresnelPolyC
   ----------------------------------------------------------------------------
   S7 polynomial facts for the canonical Fresnel integrals (C half; the S
   half is B64_FresnelPolyS, the umbrella B64_FresnelPoly re-exports both)
     C(x) = int_0^x cos(t^2) dt = x   P(x^4),  P(z) = sum_{k<=19} (-1)^k z^k / ((2k)!   (4k+1))
     S(x) = int_0^x sin(t^2) dt = x^3 Q(x^4),  Q(z) = sum_{k<=18} (-1)^k z^k / ((2k+1)! (4k+3))
   on the B64_Horner kernel, for |z| <= 40 (the intake |x| <= 5/2 gives
   x^4 <= 625/16, plus the rounding of z).  X_F = 5/2 is the tangent-rotation
   cap |psi| = x^2 <= 25/4 rad from the inflection point (B64_Fresnel.v
   header; lemma B64_ClothoidMap.xf_psi_bound states the equivalence).
   Budget lines, each a theorem: frc_eval_err / frs_eval_err (binary64
   Horner vs the same coefficients exact), frc_coef_err / frs_coef_err,
   frc_M/L_bound, frs_M/L_bound, and frc_fz_eq / frs_fz_eq: the exact
   polynomials ARE FresnelSeries.fz_C 19 1 / fz_S 18 1, whose truncation is
   FresnelSeries.fz_C_rem / fz_S_rem.  The e0 term is bounded by 2^-1000
   (not 2^-106): z^k amplifies it by 40^19.
   claimId: s7-b64-fresnel.  witness: b64_fresnel_C_err (B64_Fresnel.v).
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia ZArith List Factorial.
From Flocq Require Import Core IEEE754.Binary IEEE754.BinarySingleNaN.
From NTS.Proofs Require Import FresnelSeries.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
  B64_AbsErr B64_Horner B64_SinPoly.
Import ListNotations.
Local Open Scope R_scope.

Local Notation B2R := (Binary.B2R prec emax).
Local Notation fin := (Binary.is_finite prec emax).

Definition fr_Z : R := 40.

Lemma fr_Z_nonneg : 0 <= fr_Z.
Proof. unfold fr_Z. lra. Qed.

Lemma fr_e0_bounds : 0 < b64ae_e0 <= / """+str(2**1000)+""".
Proof.
  unfold b64ae_e0. split; [apply bpow_gt_0|].
  apply Rle_trans with (bpow radix2 (-1000)); [apply bpow_le; lia|].
  cbn. lra.
Qed.

Lemma fr_bpow1000 : 4096 <= bpow radix2 1000.
Proof.
  apply Rle_trans with (bpow radix2 12); [cbn; lra|]. apply bpow_le. lia.
Qed.
""")
def emit(P, pfx, title):
    NC=P['NC']; cs=P['cs']; mexp=P['mexp']; M=P['M']; E=P['E']; L=P['L']
    w(f"(* {title} *)")
    for k,(d,s,M_,E_) in enumerate(cs):
        w(f"Definition {pfx}_c{k} : binary64 :=\n  Binary.B754_finite prec emax {'true' if s else 'false'} {M_} ({E_}) eq_refl.")
    w(f"\nDefinition {pfx}_coeffs : list binary64 :=\n  ["+"; ".join(f"{pfx}_c{k}" for k in range(NC))+"].\n")
    w(f"Definition {pfx}_S{NC-1} : list R := [{mlit(mexp[NC-1])}].")
    for k in range(NC-2,-1,-1):
        w(f"Definition {pfx}_S{k} : list R := {mlit(mexp[k])} :: {pfx}_S{k+1}.")
    w(f"Definition {pfx}_ms : list R := {pfx}_S0.\n")
    allS=", ".join(f"{pfx}_S{k}" for k in range(NC))
    w(f"""Lemma {pfx}_coeffs_ok : hz_coeffs_ok {pfx}_coeffs {pfx}_ms.
Proof.
  unfold hz_coeffs_ok, {pfx}_coeffs, {pfx}_ms, {allS}.
  repeat (apply Forall2_cons;
          [split; [reflexivity|]; cbn; unfold F2R; cbn; apply Rabs_le; split; lra|]).
  apply Forall2_nil.
Qed.

Lemma {pfx}_coeffs_ok_R : Forall2 (fun c m => Rabs c <= m) (map B2R {pfx}_coeffs) {pfx}_ms.
Proof.
  generalize {pfx}_coeffs_ok. unfold hz_coeffs_ok.
  generalize {pfx}_coeffs {pfx}_ms. intros cs ms H.
  induction H as [|c m cs ms [_ Hm] _ IH]; cbn; constructor; assumption.
Qed.
""")
    for k in range(NC-1,-1,-1):
        w(f"Lemma {pfx}_S{k}_nonneg : Forall (fun m => 0 <= m) {pfx}_S{k}.\nProof. unfold "+", ".join(f"{pfx}_S{j}" for j in range(k,NC))+". repeat constructor; lra. Qed.")
    w(f"Lemma {pfx}_M{NC-1} : hz_M {pfx}_S{NC-1} fr_Z <= {Rq(M[NC-1])}.\nProof. unfold {pfx}_S{NC-1}, fr_Z. cbn [hz_M]. lra. Qed.")
    for k in range(NC-2,-1,-1):
        w(f"""Lemma {pfx}_M{k} : hz_M {pfx}_S{k} fr_Z <= {Rq(M[k])}.
Proof.
  change (hz_M {pfx}_S{k} fr_Z) with (hz_M {pfx}_S{k+1} fr_Z * fr_Z + {mlit(mexp[k])}).
  assert (H := {pfx}_M{k+1}). assert (HZ := fr_Z_nonneg).
  assert (hz_M {pfx}_S{k+1} fr_Z * fr_Z <= {Rq(M[k+1])} * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.""")
    w(f"Lemma {pfx}_L{NC-1} : hz_L {pfx}_S{NC-1} fr_Z <= 0.\nProof. unfold {pfx}_S{NC-1}. cbn. lra. Qed.")
    for k in range(NC-2,-1,-1):
        w(f"""Lemma {pfx}_L{k} : hz_L {pfx}_S{k} fr_Z <= {Rq(L[k])}.
Proof.
  change (hz_L {pfx}_S{k} fr_Z) with (hz_L {pfx}_S{k+1} fr_Z * fr_Z + hz_M {pfx}_S{k+1} fr_Z).
  assert (H := {pfx}_L{k+1}). assert (H2 := {pfx}_M{k+1}). assert (HZ := fr_Z_nonneg).
  assert (hz_L {pfx}_S{k+1} fr_Z * fr_Z <= {Rq(L[k+1])} * fr_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold fr_Z in *. lra.
Qed.""")
    w(f"Lemma {pfx}_E{NC-1} : hz_E {pfx}_S{NC-1} fr_Z <= 0.\nProof. unfold {pfx}_S{NC-1}. cbn. lra. Qed.")
    for k in range(NC-2,-1,-1):
        tail = "[]" if k+1==NC-1 else f"{pfx}_S{k+2}"
        w(f"""Lemma {pfx}_E{k} : hz_E {pfx}_S{k} fr_Z <= {Rq(E[k])}.
Proof.
  pose proof fr_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change {pfx}_S{k} with (({mlit(mexp[k])}) :: ({mlit(mexp[k+1])}) :: {tail}).
    apply (hz_E_cons_le ({mlit(mexp[k])}) _ _ fr_Z {Rq(M[k+1])} {Rq(E[k+1])});
      [exact fr_Z_nonneg
      |apply hz_M_nonneg; [exact {pfx}_S{k+1}_nonneg | exact fr_Z_nonneg]
      |apply hz_E_nonneg; [exact {pfx}_S{k+1}_nonneg | exact fr_Z_nonneg]
      |exact {pfx}_M{k+1} | exact {pfx}_E{k+1}].
  - rewrite sp_u_val. unfold fr_Z. set (e := b64ae_e0) in *. lra.
Qed.""")
    w(f"Lemma {pfx}_safe{NC-1} : hz_safe {pfx}_S{NC-1} fr_Z.\nProof. exact I. Qed.")
    for k in range(NC-2,-1,-1):
        w(f"""Lemma {pfx}_safe{k} : hz_safe {pfx}_S{k} fr_Z.
Proof.
  change (hz_safe {pfx}_S{k} fr_Z) with
    (hz_safe {pfx}_S{k+1} fr_Z /\\
     (hz_M {pfx}_S{k+1} fr_Z + hz_E {pfx}_S{k+1} fr_Z) * fr_Z * 2 + {mlit(mexp[k])} + 1
       <= bpow radix2 1000).
  split; [exact {pfx}_safe{k+1}|].
  assert (H1 := {pfx}_M{k+1}). assert (H2 := {pfx}_E{k+1}). assert (HZ := fr_Z_nonneg).
  assert (Hb := fr_bpow1000).
  assert ((hz_M {pfx}_S{k+1} fr_Z + hz_E {pfx}_S{k+1} fr_Z) * fr_Z * 2
          <= ({Rq(M[k+1])} + {Rq(E[k+1])}) * fr_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold fr_Z in *. lra.
Qed.""")
    MB=up64(M[0]); LB=up64(L[0]); EB=E[0]
    info[pfx]=dict(MB=MB,LB=LB,EB=EB,D=P['D'])
    w(f"""
Lemma {pfx}_M_bound : hz_M {pfx}_ms fr_Z <= {Rq(MB)}.
Proof. unfold {pfx}_ms. eapply Rle_trans; [exact {pfx}_M0|]. lra. Qed.

Lemma {pfx}_L_bound : hz_L {pfx}_ms fr_Z <= {Rq(LB)}.
Proof. unfold {pfx}_ms. eapply Rle_trans; [exact {pfx}_L0|]. lra. Qed.

Theorem {pfx}_eval_err : forall z : binary64,
  fin z = true -> Rabs (B2R z) <= 40 ->
  fin (b64_horner {pfx}_coeffs z) = true /\\
  Rabs (B2R (b64_horner {pfx}_coeffs z) - hz_horner_R (map B2R {pfx}_coeffs) (B2R z))
    <= {Rq(EB)}.
Proof.
  intros z Fz Hz.
  destruct (b64_horner_err {pfx}_coeffs {pfx}_ms z fr_Z {pfx}_coeffs_ok Fz Hz
              fr_Z_nonneg {pfx}_safe0) as [F E].
  split; [exact F|]. eapply Rle_trans; [exact E|]. unfold {pfx}_ms. exact {pfx}_E0.
Qed.
""")
    exact=P['exact']; dex=P['dex']
    w(f"Definition {pfx}_exact : list R :=\n  ["+"; ".join(rexact(e) for e in exact)+"].\n")
    w(f"Definition {pfx}_delta : list R :=\n  ["+";\n   ".join(f"B2R {pfx}_c{k} - ({rexact(exact[k])})" for k in range(NC))+"].\n")
    w(f"""Lemma {pfx}_delta_eq : forall x,
  hz_horner_R (map B2R {pfx}_coeffs) x - hz_horner_R {pfx}_exact x = hz_horner_R {pfx}_delta x.
Proof. intro x. unfold {pfx}_coeffs, {pfx}_exact, {pfx}_delta. cbn [map hz_horner_R]. ring. Qed.
""")
    dlist=[("0" if k is None else mlit(k)) for k in dex]
    w(f"Definition {pfx}_ds : list R :=\n  ["+"; ".join(dlist)+"].\n")
    w(f"""Lemma {pfx}_delta_ok : Forall2 (fun c m => Rabs c <= m) {pfx}_delta {pfx}_ds.
Proof.
  unfold {pfx}_delta, {pfx}_ds, """+", ".join(f"{pfx}_c{k}" for k in range(NC))+f""".
  repeat (apply Forall2_cons; [cbn [Binary.B2R]; unfold F2R; cbn; apply Rabs_le; split; lra|]).
  apply Forall2_nil.
Qed.

Lemma {pfx}_ds_M : hz_M {pfx}_ds fr_Z <= {Rq(P['D'])}.
Proof. unfold {pfx}_ds, fr_Z. cbn [hz_M]. lra. Qed.

Lemma {pfx}_coef_err : forall x, Rabs x <= 40 ->
  Rabs (hz_horner_R (map B2R {pfx}_coeffs) x - hz_horner_R {pfx}_exact x) <= {Rq(P['D'])}.
Proof.
  intros x Hx. rewrite {pfx}_delta_eq.
  eapply Rle_trans; [apply (hz_horner_R_bound_R _ {pfx}_ds x fr_Z {pfx}_delta_ok); unfold fr_Z; exact Hx|].
  exact {pfx}_ds_M.
Qed.

Lemma {pfx}_P_bound : forall y, Rabs y <= 40 ->
  Rabs (hz_horner_R (map B2R {pfx}_coeffs) y) <= {Rq(MB)}.
Proof.
  intros y Hy.
  eapply Rle_trans; [apply (hz_horner_R_bound {pfx}_coeffs {pfx}_ms y fr_Z {pfx}_coeffs_ok);
                     unfold fr_Z; exact Hy|].
  exact {pfx}_M_bound.
Qed.

Lemma {pfx}_P_lip : forall y v, Rabs y <= 40 -> Rabs v <= 40 ->
  Rabs (hz_horner_R (map B2R {pfx}_coeffs) y - hz_horner_R (map B2R {pfx}_coeffs) v)
    <= {Rq(LB)} * Rabs (y - v).
Proof.
  intros y v Hy Hv.
  eapply Rle_trans;
    [apply (hz_horner_R_lip (map B2R {pfx}_coeffs) {pfx}_ms y v fr_Z {pfx}_coeffs_ok_R);
     unfold fr_Z; assumption|].
  apply Rmult_le_compat_r; [apply Rabs_pos | exact {pfx}_L_bound].
Qed.
""")
emit(C,"frc","Fresnel C: (-1)^k / ((2k)! (4k+1)), rounded to nearest binary64.")
w("""Lemma fr_INR_fact_S : forall n, INR (fact (S n)) = INR (S n) * INR (fact n).
Proof. intro n. rewrite fact_simpl, mult_INR. reflexivity. Qed.

(* The exact C polynomial is the S6 partial sum fz_C 19 at a = 1. *)
Lemma frc_fz_eq : forall x, fz_C 19 1 x = x * hz_horner_R frc_exact (x * x * (x * x)).
Proof.
  intro x. unfold fz_C, fz_Cterm. cbn [sum_f_R0 Nat.mul Nat.add].
  rewrite !pow1.
  repeat match goal with |- context [INR (fact (S ?n))] => rewrite (fr_INR_fact_S n) end.
  replace (INR (fact 0)) with 1 by reflexivity.
  repeat match goal with |- context [INR ?n] => rewrite (INR_IZR_INZ n) end.
  cbn [Z.of_nat Pos.of_succ_nat PosDef.Pos.succ]. unfold frc_exact. cbn [hz_horner_R].
  field.
Qed.

Print Assumptions frc_eval_err.
Print Assumptions frc_coef_err.
Print Assumptions frc_fz_eq.""")
outC=out; out=[]; w=out.append
w(HDR_S)
emit(S,"frs","Fresnel S: (-1)^k / ((2k+1)! (4k+3)), rounded to nearest binary64.")
w("""(* The exact S polynomial is the S6 partial sum fz_S 18 at a = 1. *)
Lemma frs_fz_eq : forall x, fz_S 18 1 x = x * (x * x) * hz_horner_R frs_exact (x * x * (x * x)).
Proof.
  intro x. unfold fz_S, fz_Sterm. cbn [sum_f_R0 Nat.mul Nat.add].
  rewrite !pow1.
  repeat match goal with |- context [INR (fact (S ?n))] => rewrite (fr_INR_fact_S n) end.
  replace (INR (fact 0)) with 1 by reflexivity.
  repeat match goal with |- context [INR ?n] => rewrite (INR_IZR_INZ n) end.
  cbn [Z.of_nat Pos.of_succ_nat PosDef.Pos.succ]. unfold frs_exact. cbn [hz_horner_R].
  field.
Qed.

Print Assumptions frs_eval_err.
Print Assumptions frs_coef_err.
Print Assumptions frs_fz_eq.""")
outS=out
import os
d=os.path.dirname(sys.argv[1])
def fix(t): return "\n".join(t).replace(" /  ", " /\\\n  ")+"\n"
open(os.path.join(d,"B64_FresnelPolyC.v"),'w').write(fix(outC))
open(os.path.join(d,"B64_FresnelPolyS.v"),'w').write(fix(outS))
open(sys.argv[1],'w').write(UMB)
import json
json.dump({k:{kk:[vv.numerator,vv.denominator] for kk,vv in v.items()} for k,v in info.items()}, open(sys.argv[2],'w'))
for k,v in info.items(): print(k, {kk:float(vv) for kk,vv in v.items()}, "E/u", float(v['EB']/u))
