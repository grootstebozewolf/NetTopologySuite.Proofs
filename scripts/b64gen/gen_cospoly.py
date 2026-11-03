#!/usr/bin/env python3
# scripts/b64gen/gen_cospoly.py -- generator of theories-flocq/B64_CosPoly.v: degree-22 cosine polynomial facts (S4).
# Usage: python3 scripts/b64gen/gen_cospoly.py OUT_V
# Every numeric constant (binary64 literals, bound chains, rational
# enclosures) is computed exactly with fractions.Fraction; the Rocq kernel
# checks the emitted file, so correctness does not depend on this script --
# it exists so that a degree, a cap (X_F) or a budget can be changed and
# re-derived.  scripts/b64gen/check.py regenerates everything and diffs it
# against the committed files (part of `make ci-guards`).
# AI assistance disclosure: AI-drafted; human review pending.
from fractions import Fraction as F
import math, sys
u=F(1,2**53); e0b=F(1,2**106)
NC=12
Z=F(41,16)
MB=F(11,4); LB=F(7,8)
def lit53(d):
    a=abs(F(d)); e=math.floor(math.log2(a))
    while F(2)**e>a: e-=1
    while F(2)**(e+1)<=a: e+=1
    E=e-52; M=a/F(2)**E; assert M.denominator==1 and 2**52<=M<2**53
    return (d<0, int(M), E)
cs=[]; exact=[]
for k in range(NC):
    ex=F((-1)**k, math.factorial(2*k)); d=float(ex)
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
M={NC-1:ms[NC-1]}; E={NC-1:F(0)}; L={NC-1:F(0)}
for k in range(NC-2,-1,-1):
    M[k]=M[k+1]*Z+ms[k]
    ex=Z*E[k+1]+u*((M[k+1]+E[k+1])*Z)+e0b+(u*((M[k+1]+E[k+1])*Z*(1+u)+e0b+ms[k])+e0b)
    E[k]=F(math.ceil(ex*2**80),2**80)
    L[k]=L[k+1]*Z+M[k+1]
assert E[0]<=F(1,2**50), float(E[0]/u)
assert M[0]<=MB and L[0]<=LB
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
f23=math.factorial(23)
out=[]
w=out.append
w("""(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_CosPoly
   ----------------------------------------------------------------------------
   S4 polynomial facts: the degree-22 cosine polynomial on the B64_Horner
   kernel, by reuse of the S1/S2 sine machinery.  cos r ~ Q(r^2),
   Q(z) = sum_{k=0..11} (-1)^k z^k / (2k)!, for |r| <= 8/5 (the same reduced
   range as B64_SinPoly), so |z| <= 41/16.

   cq_c0 .. cq_c11 are the round-to-nearest binary64 values of (-1)^k/(2k)!.
   Budget lines proved here, each a separate theorem:
     b64_cospoly_eval_err   binary64 Horner vs the same coefficients exact,
                            <= 2^-50 (exact recursive bound ~7.14 u)
     cq_coef_err            binary64 coefficients vs (-1)^k/(2k)!
     cq_trunc               Q(r^2) vs cos r: <= (8/5)^24 / 23!
     cq_M_bound, cq_L_bound magnitude <= 11/4, Lipschitz <= 7/8
   The truncation line is NOT Stdlib cos_bound (that needs |r| <= pi/2, and
   the reduced range is slightly wider): d/dr (Q(r^2) - cos r) = sin r -
   r P(r^2), which B64_SinPoly.sp_trunc bounds by (8/5)^23/23!, and
   RealMonotone.deriv_nonneg_incr turns the derivative bound into the value
   bound (no classical MVT).  B64_Horner.hz_horner_R_deriv supplies Q'.
   claimId: s4-b64-cos.  witness: b64_cospoly_eval_err.
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia ZArith List.
From Flocq Require Import Core IEEE754.Binary IEEE754.BinarySingleNaN.
From NTS.Proofs Require Import RealMonotone.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
  B64_AbsErr B64_Horner B64_SinPoly.
Import ListNotations.
Local Open Scope R_scope.

Local Notation B2R := (Binary.B2R prec emax).
Local Notation fin := (Binary.is_finite prec emax).

(* (-1)^k / (2k)!, rounded to nearest binary64. *)""")
for k,(d,s,M_,E_) in enumerate(cs):
    w(f"Definition cq_c{k} : binary64 :=\n  Binary.B754_finite prec emax {'true' if s else 'false'} {M_} ({E_}) eq_refl.")
w("\nDefinition cq_coeffs : list binary64 :=\n  ["+"; ".join(f"cq_c{k}" for k in range(NC))+"].\n")
w("(* Dyadic magnitude bounds |cq_c_k| <= cq_m_k, as suffixes S_k = [m_k; ...]. *)")
w(f"Definition cq_S{NC-1} : list R := [{mlit(mexp[NC-1])}].")
for k in range(NC-2,-1,-1):
    w(f"Definition cq_S{k} : list R := {mlit(mexp[k])} :: cq_S{k+1}.")
w("Definition cq_ms : list R := cq_S0.\n")
w("""Lemma cq_coeffs_ok : hz_coeffs_ok cq_coeffs cq_ms.
Proof.
  unfold hz_coeffs_ok, cq_coeffs, cq_ms, """+", ".join(f"cq_S{k}" for k in range(NC))+""".
  repeat (apply Forall2_cons;
          [split; [reflexivity|]; cbn; unfold F2R; cbn; apply Rabs_le; split; lra|]).
  apply Forall2_nil.
Qed.

Lemma cq_coeffs_ok_R : Forall2 (fun c m => Rabs c <= m) (map B2R cq_coeffs) cq_ms.
Proof.
  generalize cq_coeffs_ok. unfold hz_coeffs_ok.
  generalize cq_coeffs cq_ms. intros cs ms H.
  induction H as [|c m cs ms [_ Hm] _ IH]; cbn; constructor; assumption.
Qed.
""")
w("""Lemma cq_bpow1000 : 16 <= bpow radix2 1000.
Proof.
  apply Rle_trans with (bpow radix2 4); [cbn; lra|]. apply bpow_le. lia.
Qed.
""")
for k in range(NC-1,-1,-1):
    w(f"Lemma cq_S{k}_nonneg : Forall (fun m => 0 <= m) cq_S{k}.\nProof. unfold "+", ".join(f"cq_S{j}" for j in range(k,NC))+". repeat constructor; lra. Qed.")
w("")
w(f"Lemma cq_M{NC-1} : hz_M cq_S{NC-1} sp_Z <= {Rq(M[NC-1])}.\nProof. unfold cq_S{NC-1}, sp_Z. cbn [hz_M]. lra. Qed.")
for k in range(NC-2,-1,-1):
    w(f"""Lemma cq_M{k} : hz_M cq_S{k} sp_Z <= {Rq(M[k])}.
Proof.
  change (hz_M cq_S{k} sp_Z) with (hz_M cq_S{k+1} sp_Z * sp_Z + {mlit(mexp[k])}).
  assert (H := cq_M{k+1}). assert (HZ := sp_Z_nonneg).
  assert (hz_M cq_S{k+1} sp_Z * sp_Z <= {Rq(M[k+1])} * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.""")
w("")
w(f"Lemma cq_L{NC-1} : hz_L cq_S{NC-1} sp_Z <= 0.\nProof. unfold cq_S{NC-1}. cbn. lra. Qed.")
for k in range(NC-2,-1,-1):
    w(f"""Lemma cq_L{k} : hz_L cq_S{k} sp_Z <= {Rq(L[k])}.
Proof.
  change (hz_L cq_S{k} sp_Z) with (hz_L cq_S{k+1} sp_Z * sp_Z + hz_M cq_S{k+1} sp_Z).
  assert (H := cq_L{k+1}). assert (H2 := cq_M{k+1}). assert (HZ := sp_Z_nonneg).
  assert (hz_L cq_S{k+1} sp_Z * sp_Z <= {Rq(L[k+1])} * sp_Z)
    by (apply Rmult_le_compat_r; assumption).
  unfold sp_Z in *. lra.
Qed.""")
w("")
w(f"Lemma cq_E{NC-1} : hz_E cq_S{NC-1} sp_Z <= 0.\nProof. unfold cq_S{NC-1}. cbn. lra. Qed.")
for k in range(NC-2,-1,-1):
    tail = "[]" if k+1==NC-1 else f"cq_S{k+2}"
    w(f"""Lemma cq_E{k} : hz_E cq_S{k} sp_Z <= {Rq(E[k])}.
Proof.
  pose proof sp_e0_bounds as [He0 He1].
  eapply Rle_trans.
  - change cq_S{k} with (({mlit(mexp[k])}) :: ({mlit(mexp[k+1])}) :: {tail}).
    apply (hz_E_cons_le ({mlit(mexp[k])}) _ _ sp_Z {Rq(M[k+1])} {Rq(E[k+1])});
      [exact sp_Z_nonneg
      |apply hz_M_nonneg; [exact cq_S{k+1}_nonneg | exact sp_Z_nonneg]
      |apply hz_E_nonneg; [exact cq_S{k+1}_nonneg | exact sp_Z_nonneg]
      |exact cq_M{k+1} | exact cq_E{k+1}].
  - rewrite sp_u_val. unfold sp_Z. set (e := b64ae_e0) in *. lra.
Qed.""")
w("")
w(f"Lemma cq_safe{NC-1} : hz_safe cq_S{NC-1} sp_Z.\nProof. exact I. Qed.")
for k in range(NC-2,-1,-1):
    w(f"""Lemma cq_safe{k} : hz_safe cq_S{k} sp_Z.
Proof.
  change (hz_safe cq_S{k} sp_Z) with
    (hz_safe cq_S{k+1} sp_Z /\\
     (hz_M cq_S{k+1} sp_Z + hz_E cq_S{k+1} sp_Z) * sp_Z * 2 + {mlit(mexp[k])} + 1
       <= bpow radix2 1000).
  split; [exact cq_safe{k+1}|].
  assert (H1 := cq_M{k+1}). assert (H2 := cq_E{k+1}). assert (HZ := sp_Z_nonneg).
  assert (Hb := cq_bpow1000).
  assert ((hz_M cq_S{k+1} sp_Z + hz_E cq_S{k+1} sp_Z) * sp_Z * 2
          <= ({Rq(M[k+1])} + {Rq(E[k+1])}) * sp_Z * 2)
    by (apply Rmult_le_compat_r; [lra|]; apply Rmult_le_compat_r; lra).
  unfold sp_Z in *. lra.
Qed.""")
w(f"""
Lemma cq_M_bound : hz_M cq_ms sp_Z <= {Rq(MB)}.
Proof. unfold cq_ms. eapply Rle_trans; [exact cq_M0|]. lra. Qed.

Lemma cq_L_bound : hz_L cq_ms sp_Z <= {Rq(LB)}.
Proof. unfold cq_ms. eapply Rle_trans; [exact cq_L0|]. lra. Qed.

Lemma cq_E_bound : hz_E cq_ms sp_Z <= bpow radix2 (-50).
Proof.
  unfold cq_ms. eapply Rle_trans; [exact cq_E0|].
  replace (bpow radix2 (-50)) with (/ {2**50}) by (cbn; reflexivity).
  lra.
Qed.

(* WITNESS {{"claimId":"s4-b64-cos","topic":"numerics","lemma":"b64_cospoly_eval_err","title":"The binary64 Horner evaluation of the degree-22 cosine polynomial (binary64 coefficients of (-1)^k/(2k)!, z with |z| <= 41/16) is finite and within 2^-50 of the same coefficients evaluated exactly at the same z","file":"theories-flocq/B64_CosPoly.v","witness":"b64_cospoly_eval_err","board":"ADR-0006"}} *)
Theorem b64_cospoly_eval_err : forall z : binary64,
  fin z = true -> Rabs (B2R z) <= 41 / 16 ->
  fin (b64_horner cq_coeffs z) = true /\\
  Rabs (B2R (b64_horner cq_coeffs z) - hz_horner_R (map B2R cq_coeffs) (B2R z))
    <= bpow radix2 (-50).
Proof.
  intros z Fz Hz.
  destruct (b64_horner_err cq_coeffs cq_ms z sp_Z cq_coeffs_ok Fz Hz
              sp_Z_nonneg cq_safe0) as [F E].
  split; [exact F|]. eapply Rle_trans; [exact E | exact cq_E_bound].
Qed.
""")
def rexact(ex):
    if ex==1: return "1"
    return ("- " if ex<0 else "")+f"/ {abs(ex.denominator)}"
w("(* The mathematical coefficients (-1)^k / (2k)!. *)")
w("Definition cq_exact : list R :=\n  ["+"; ".join(rexact(e) for e in exact)+"].\n")
w("Definition cq_delta : list R :=\n  ["+";\n   ".join(f"B2R cq_c{k} - ({rexact(exact[k])})" for k in range(NC))+"].\n")
w("""Lemma cq_delta_eq : forall x,
  hz_horner_R (map B2R cq_coeffs) x - hz_horner_R cq_exact x = hz_horner_R cq_delta x.
Proof. intro x. unfold cq_coeffs, cq_exact, cq_delta. cbn [map hz_horner_R]. ring. Qed.
""")
dlist=[("0" if k is None else mlit(k)) for k in dex]
w("Definition cq_ds : list R :=\n  ["+"; ".join(dlist)+"].\n")
w("""Lemma cq_delta_ok : Forall2 (fun c m => Rabs c <= m) cq_delta cq_ds.
Proof.
  unfold cq_delta, cq_ds, """+", ".join(f"cq_c{k}" for k in range(NC))+""".
  repeat (apply Forall2_cons; [cbn [Binary.B2R]; unfold F2R; cbn; apply Rabs_le; split; lra|]).
  apply Forall2_nil.
Qed.
""")
w(f"""Lemma cq_ds_M : hz_M cq_ds sp_Z <= {Rq(Dcob)}.
Proof. unfold cq_ds, sp_Z. cbn [hz_M]. lra. Qed.

(* Coefficient representation line. *)
Lemma cq_coef_err : forall x, Rabs x <= 41 / 16 ->
  Rabs (hz_horner_R (map B2R cq_coeffs) x - hz_horner_R cq_exact x) <= {Rq(Dcob)}.
Proof.
  intros x Hx. rewrite cq_delta_eq.
  eapply Rle_trans; [apply (hz_horner_R_bound_R _ cq_ds x sp_Z cq_delta_ok); exact Hx|].
  exact cq_ds_M.
Qed.

(* -------------------------------------------------------------------------- *)
(* Truncation through the derivative: (Q(r^2) - cos r)' = sin r - r P(r^2).  *)
(* -------------------------------------------------------------------------- *)

Lemma cq_dR_eq : forall t,
  hz_horner_dR cq_exact (t * t) * (1 * t + t * 1) = - (t * hz_horner_R sp_exact (t * t)).
Proof. intro t. unfold cq_exact, sp_exact. cbn [hz_horner_R hz_horner_dR]. field. Qed.

Definition cq_F (a : R) : R := hz_horner_R cq_exact (a * a) - cos a.

Lemma cq_F_deriv : forall t,
  derivable_pt_lim cq_F t (sin t - t * hz_horner_R sp_exact (t * t)).
Proof.
  intro t.
  assert (Hsq : derivable_pt_lim (fun a => a * a) t (1 * t + t * 1)).
  {{ eapply derivable_pt_lim_ext;
      [| exact (derivable_pt_lim_mult id id t 1 1 (derivable_pt_lim_id t) (derivable_pt_lim_id t))].
    intro z. unfold mult_fct, id. reflexivity. }}
  assert (Hc := derivable_pt_lim_comp (fun a => a * a) (fun y => hz_horner_R cq_exact y)
                  t _ _ Hsq (hz_horner_R_deriv cq_exact (t * t))).
  assert (Hm := derivable_pt_lim_minus _ cos t _ _ Hc (derivable_pt_lim_cos t)).
  replace (sin t - t * hz_horner_R sp_exact (t * t))
    with (hz_horner_dR cq_exact (t * t) * (1 * t + t * 1) - - sin t)
    by (rewrite cq_dR_eq; ring).
  eapply derivable_pt_lim_ext; [| exact Hm].
  intro z. unfold minus_fct, comp, cq_F. reflexivity.
Qed.

Lemma cq_lin_deriv : forall K t, derivable_pt_lim (fun y => K * y) t K.
Proof.
  intros K t.
  assert (H : derivable_pt_lim (fun y => K * y) t (K * 1)).
  {{ eapply derivable_pt_lim_ext;
      [| exact (derivable_pt_lim_scal id K t 1 (derivable_pt_lim_id t))].
    intro z. unfold mult_real_fct, id. reflexivity. }}
  rewrite Rmult_1_r in H. exact H.
Qed.

Lemma cq_F0 : cq_F 0 = 0.
Proof. unfold cq_F. rewrite cos_0. unfold cq_exact. cbn [hz_horner_R]. ring. Qed.

Lemma cq_F_even : forall a, cq_F (- a) = cq_F a.
Proof. intro a. unfold cq_F. rewrite cos_neg. replace (- a * - a) with (a * a) by ring. reflexivity. Qed.

(* Truncation line. *)
Lemma cq_trunc : forall r, Rabs r <= 8 / 5 ->
  Rabs (hz_horner_R cq_exact (r * r) - cos r) <= (8 / 5) ^ 24 / {f23}.
Proof.
  set (K := (8 / 5) ^ 23 / {f23}).
  assert (HK0 : 0 <= K) by (unfold K; apply Rmult_le_pos; [apply pow_le; lra | lra]).
  assert (HK : forall t, 0 <= t <= 8 / 5 ->
             Rabs (sin t - t * hz_horner_R sp_exact (t * t)) <= K).
  {{ intros t Ht. rewrite <- Rabs_Ropp.
    replace (- (sin t - t * hz_horner_R sp_exact (t * t)))
      with (t * hz_horner_R sp_exact (t * t) - sin t) by ring.
    apply sp_trunc. rewrite Rabs_pos_eq; lra. }}
  assert (Hpos : forall a, 0 <= a <= 8 / 5 -> Rabs (cq_F a) <= 8 / 5 * K).
  {{ intros a Ha.
    assert (Lo : cq_F 0 + K * 0 <= cq_F a + K * a).
    {{ apply (deriv_nonneg_incr (fun y => cq_F y + K * y)
               (fun y => (sin y - y * hz_horner_R sp_exact (y * y)) + K) 0 (8 / 5) 0 a).
      - intros t Ht. apply derivable_pt_lim_plus with (f1 := cq_F) (f2 := fun y => K * y);
          [apply cq_F_deriv | apply cq_lin_deriv].
      - intros t Ht. specialize (HK t Ht). apply Rabs_le_inv in HK. lra.
      - lra. - lra. - lra. }}
    assert (Hi : K * 0 - cq_F 0 <= K * a - cq_F a).
    {{ apply (deriv_nonneg_incr (fun y => K * y - cq_F y)
               (fun y => K - (sin y - y * hz_horner_R sp_exact (y * y))) 0 (8 / 5) 0 a).
      - intros t Ht. apply derivable_pt_lim_minus with (f1 := fun y => K * y) (f2 := cq_F);
          [apply cq_lin_deriv | apply cq_F_deriv].
      - intros t Ht. specialize (HK t Ht). apply Rabs_le_inv in HK. lra.
      - lra. - lra. - lra. }}
    rewrite cq_F0 in Lo, Hi.
    assert (K * a <= K * (8 / 5)) by (apply Rmult_le_compat_l; lra).
    apply Rabs_le. split; lra. }}
  intros r Hr.
  replace ((8 / 5) ^ 24 / {f23}) with (8 / 5 * K) by (unfold K; cbn [pow]; field).
  fold (cq_F r).
  destruct (Rle_lt_dec 0 r) as [H0|H0].
  - apply Hpos. apply Rabs_le_inv in Hr. lra.
  - rewrite <- cq_F_even. apply Hpos. apply Rabs_le_inv in Hr. lra.
Qed.
""")
w("Print Assumptions cq_coeffs_ok.\nPrint Assumptions b64_cospoly_eval_err.\nPrint Assumptions cq_coef_err.\nPrint Assumptions cq_trunc.\nPrint Assumptions cq_M_bound.\nPrint Assumptions cq_L_bound.")
open(sys.argv[1],'w').write("\n".join(out).replace(" /  ", " /\\\n  ")+"\n")
print("Eh(u)",float(E[0]/u),"M",float(M[0]),"L",float(L[0]),"Dco",float(Dcob),"dex",dex)
