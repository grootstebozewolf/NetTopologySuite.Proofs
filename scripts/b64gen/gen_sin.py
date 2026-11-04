#!/usr/bin/env python3
# scripts/b64gen/gen_sin.py -- generator of theories-flocq/B64_Sin.v: binary64 sine evaluator (S2/S3).
# Usage: python3 scripts/b64gen/gen_sin.py OUT_V SINPOLY_V
# Every numeric constant (binary64 literals, bound chains, rational
# enclosures) is computed exactly with fractions.Fraction; the Rocq kernel
# checks the emitted file, so correctness does not depend on this script --
# it exists so that a degree, a cap (X_F) or a budget can be changed and
# re-derived.  scripts/b64gen/check.py regenerates everything and diffs it
# against the committed files (part of `make ci-guards`).
# AI assistance disclosure: AI-drafted; human review pending.
from fractions import Fraction as F
import math, sys, re
PI=F("3.14159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798")
u=F(1,2**53); e0b=F(1,2**106)
def lit53(v):
    v=F(v); a=abs(v); e=math.floor(math.log2(a))
    while F(2)**e>a: e-=1
    while F(2)**(e+1)<=a: e+=1
    E=e-52; M=a/F(2)**E; assert M.denominator==1 and 2**52<=M<2**53, v
    return (v<0,int(M),E)
def rn(x,bits):
    a=abs(x); e=math.floor(math.log2(a))
    while F(2)**e>a: e-=1
    while F(2)**(e+1)<=a: e+=1
    sc=F(2)**(bits-1-e); q=a*sc; n=q.numerator//q.denominator; r=q-n
    if r>F(1,2) or (r==F(1,2) and n%2): n+=1
    return F(n)/sc*(1 if x>0 else -1)
C1=rn(PI,50); C2=rn(PI-C1,53)
def Rq(x):
    if x==0: return "0"
    if x.denominator==1: return f"{x.numerator}"
    return f"({x.numerator} / {x.denominator})"
# read SinPoly constants
sp=open(sys.argv[2]).read()
lo=F(*map(int,re.search(r"Definition sp_pi_lo : R := \((\d+) / (\d+)\)",sp).groups()))
hi=F(*map(int,re.search(r"Definition sp_pi_hi : R := \((\d+) / (\d+)\)",sp).groups()))
m=re.search(r"<= \((\d+) / (\d+)\)\.\nProof\.\n  intros x Hx\. rewrite sp_delta_eq",sp)
Dco=F(int(m.group(1)),int(m.group(2)))
assert lo<=PI<=hi
gap=max(hi-(C1+C2),(C1+C2)-lo); assert gap<=F(1,2**62)
T1=F(1609,1024); T3=F(603,128); T5=F(1005,128)
assert T1>=C1/2 and T1>=PI/2 and T3<=2*C1 and T3>=C1 and T5<=4*C1 and T5>=F(3,2)*C1 and 10<=6*C1
Rred=F(15733,10000)
for k,(a,b) in {0:(0,T1),1:(T1,T3),2:(T3,T5),3:(T5,10)}.items():
    if k: assert max(abs(a-k*hi),abs(a-k*lo),abs(b-k*hi),abs(b-k*lo))<=Rred, k
assert T1<=F(8,5)
trunc=F(8,5)**23/math.factorial(23)
Ecore = u*(F(8,5)*(F(7,4)+F(1,2**51))) + e0b + F(8,5)*F(1,2**51) + F(8,5)*(F(11,32)*(u*F(64,25)+e0b)) + F(8,5)*Dco + trunc
Ered = (u*F(8,5)+e0b) + (u*(3*C2)+e0b) + 3*F(1,2**62)
def up(x,k=60): return F(math.ceil(x*2**k),2**k)
Ecb=up(Ecore); Erb=up(Ered)
assert Ecb+Erb<=F(1,2**49), float((Ecb+Erb)/u)
assert Rred+Erb<=F(8,5)
print("Ecore u",float(Ecore/u),"Ered u",float(Ered/u),"total u",float((Ecb+Erb)/u), file=sys.stderr)
consts={'C1':C1,'C2':C2,'two_C1':2*C1,'three_C1':3*C1,'one':F(1),'two':F(2),'three':F(3),'T1':T1,'T3':T3,'T5':T5,'ten':F(10),'mten':F(-10)}
o=[]; w=o.append
w("""(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_Sin
   ----------------------------------------------------------------------------
   S2: a binary64 sine with a machine-checked absolute error bound.

     b64_sin_err : sin_accept x = true ->
                   is_finite (b64_sin x) = true /\\
                   |B2R (b64_sin x) - sin (B2R x)| <= 2^-49   (16 u)

   Intake (`sin_accept`): finite and |x| <= 10 (covers the arc demand
   theta in [0, 2 pi] and the densification range |t| < 3 pi; inventory
   rows T2 / T5).  Everything outside is declined, not approximated.

   Algorithm (all RNE binary64, extractable):
     x < 0          sin x = -sin(-x)       (negation exact)
     k in {0..3}    by comparisons with dyadic thresholds 1609/1024,
                    603/128, 1005/128 (just above pi/2, 3pi/2, 5pi/2 - 1/1000)
     r = (x - k C1) - k C2                  C1 = pi to 50 bits, C2 = pi - C1 to
                    53 bits; k C1 is exact and x - k C1 is exact (Sterbenz)
     sin x = (-1)^k sin r,   sin r ~ r P(r^2)   (B64_SinPoly, degree 21)

   Budget (each a theorem; numbers in units of u = 2^-53):
     sn_core_err     |core(r) - sin r| <= ~10.9 u for |r| <= 8/5: final
                     product, Horner (b64_sinpoly_eval_err), argument
                     rounding z = fl(r r) through the Lipschitz bound,
                     coefficients (sp_coef_err), truncation (sp_trunc)
     sn_red_err      |r - (x - k pi)| <= ~1.6 u, PI pinned by sp_pi_bounds
   total ~12.6 u, stated as 2^-49 (rounded outward).
   claimId: s2-b64-sin.  witness: b64_sin_err.
   No Admitted / Axiom / Parameter.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; human review pending.
     Assisted-by: Claude Code
   ========================================================================== *)
From Stdlib Require Import Reals Lra Lia ZArith List.
From Flocq Require Import Core Sterbenz IEEE754.Binary IEEE754.BinarySingleNaN.
From NTS.Proofs Require Import LipInt.
From NTS.Proofs.Flocq Require Import Validate_binary64 B64_bridge B64_lib
  B64_AbsErr B64_Horner B64_SinPoly.
Import ListNotations.
Local Open Scope R_scope.

Local Notation B2R := (Binary.B2R prec emax).
Local Notation fin := (Binary.is_finite prec emax).

(* -------------------------------------------------------------------------- *)
(* §1  Constants.                                                             *)
(* -------------------------------------------------------------------------- *)
""")
for name,v in consts.items():
    s,M_,E_=lit53(v)
    w(f"Definition sn_{name} : binary64 :=\n  Binary.B754_finite prec emax {'true' if s else 'false'} {M_} ({E_}) eq_refl.")
w("")
for name,v in consts.items():
    w(f"""Lemma sn_{name}_R : B2R sn_{name} = {Rq(v)} /\\ fin sn_{name} = true.
Proof. split; [|reflexivity]. unfold sn_{name}. cbn [Binary.B2R]. unfold F2R. cbn. lra. Qed.""")
w(f"""
Definition sn_c1 : R := {Rq(C1)}.
Definition sn_c2 : R := {Rq(C2)}.

Lemma sn_pi_gap : Rabs (PI - (sn_c1 + sn_c2)) <= / {2**62}.
Proof.
  pose proof sp_pi_bounds as [Hl Hh]. unfold sp_pi_lo, sp_pi_hi in *.
  unfold sn_c1, sn_c2. apply Rabs_le. split; lra.
Qed.

Lemma sn_pi_range : {Rq(lo)} <= PI <= {Rq(hi)}.
Proof. exact sp_pi_bounds. Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Exact negation.                                                        *)
(* -------------------------------------------------------------------------- *)

Definition sn_neg (s : binary64) : binary64 := b64_minus hz_zero s.

Lemma sn_neg_ok : forall s, fin s = true ->
  fin (sn_neg s) = true /\\ B2R (sn_neg s) = - B2R s.
Proof.
  intros s Fs.
  assert (Hf : b64_format (- B2R s))
    by (apply generic_format_opp; apply b64_format_B2R).
  assert (E : b64_round (B2R hz_zero - B2R s) = - B2R s).
  {{ replace (B2R hz_zero - B2R s) with (- B2R s) by (cbn; ring).
    apply b64_round_generic. exact Hf. }}
  assert (Hs : b64_safe Rminus hz_zero s).
  {{ split; [reflexivity|]. split; [exact Fs|].
    rewrite E, Rabs_Ropp. apply (Binary.abs_B2R_lt_emax prec emax). }}
  destruct (b64_minus_correct _ _ Hs) as [HB HF].
  unfold sn_neg. split; [exact HF|]. rewrite HB, E. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The core: sin r ~ r * P(r^2) for |r| <= 8/5.                           *)
(* -------------------------------------------------------------------------- *)

Definition sn_core (r : binary64) : binary64 :=
  b64_mult r (b64_horner sp_coeffs (b64_mult r r)).

Definition sn_Ecore : R := {Rq(Ecb)}.

Lemma sn_core_budget : forall e, 0 < e <= / 9007199254740992 / 9007199254740992 ->
  / 9007199254740992 * (8 / 5 * (7 / 4 + / {2**51})) + e
  + 8 / 5 * / {2**51}
  + 8 / 5 * (11 / 32 * (/ 9007199254740992 * (64 / 25) + e))
  + 8 / 5 * {Rq(Dco)}
  + (8 / 5) ^ 23 / {math.factorial(23)} <= sn_Ecore.
Proof.
  intros e He. unfold sn_Ecore.
  replace ((8 / 5) ^ 23) with {Rq(F(8,5)**23)} by (cbn [pow]; field).
  lra.
Qed.

(* The core budget as pure real algebra (no binary64 terms in the lra). *)
Lemma sn_core_alg : forall (x zr pr sr Pz Pxx Exx e : R),
  0 < e <= / 9007199254740992 / 9007199254740992 -> Rabs x <= 8 / 5 ->
  Rabs (sr - x * pr) <= / 9007199254740992 * (8 / 5 * (7 / 4 + / {2**51})) + e ->
  Rabs (pr - Pz) <= / {2**51} ->
  Rabs (Pz - Pxx) <= 11 / 32 * Rabs (zr - x * x) ->
  Rabs (zr - x * x) <= / 9007199254740992 * (64 / 25) + e ->
  Rabs (Pxx - Exx) <= {Rq(Dco)} ->
  Rabs (x * Exx - sin x) <= (8 / 5) ^ 23 / {math.factorial(23)} ->
  Rabs (sr - sin x) <= sn_Ecore.
Proof.
  intros x zr pr sr Pz Pxx Exx e He Hx L1 Ep Lip Ez L4c L5.
  assert (L2 : Rabs (x * (pr - Pz)) <= 8 / 5 * / {2**51})
    by (apply b64ae_abs_mult_le; assumption).
  assert (L3 : Rabs (x * (Pz - Pxx))
               <= 8 / 5 * (11 / 32 * (/ 9007199254740992 * (64 / 25) + e))).
  {{ apply b64ae_abs_mult_le; [exact Hx|].
    eapply Rle_trans; [exact Lip|]. apply Rmult_le_compat_l; [lra | exact Ez]. }}
  assert (L4 : Rabs (x * (Pxx - Exx)) <= 8 / 5 * {Rq(Dco)})
    by (apply b64ae_abs_mult_le; assumption).
  pose proof (sn_core_budget e He) as Bud.
  replace (sr - sin x)
    with ((sr - x * pr) + x * (pr - Pz) + x * (Pz - Pxx)
          + x * (Pxx - Exx) + (x * Exx - sin x)) by ring.
  pose proof (Rabs_triang ((sr - x * pr) + x * (pr - Pz) + x * (Pz - Pxx)
                            + x * (Pxx - Exx)) (x * Exx - sin x)) as T1.
  pose proof (Rabs_triang ((sr - x * pr) + x * (pr - Pz) + x * (Pz - Pxx))
                          (x * (Pxx - Exx))) as T2.
  pose proof (Rabs_triang ((sr - x * pr) + x * (pr - Pz)) (x * (Pz - Pxx))) as T3.
  pose proof (Rabs_triang (sr - x * pr) (x * (pr - Pz))) as T4.
  lra.
Qed.

Lemma sn_z_facts : forall r, fin r = true -> Rabs (B2R r) <= 8 / 5 ->
  fin (b64_mult r r) = true /\
  Rabs (B2R (b64_mult r r) - B2R r * B2R r) <= / 9007199254740992 * (64 / 25) + b64ae_e0 /\
  Rabs (B2R (b64_mult r r)) <= 41 / 16.
Proof.
  intros r Fr Hr.
  pose proof sp_u_val as Uv. pose proof sp_e0_bounds as [He0 He1].
  assert (Hb : 4 <= bpow radix2 1000) by exact sp_bpow1000.
  assert (Bz : Rabs (B2R r * B2R r) <= 8 / 5 * (8 / 5)) by (apply b64ae_abs_mult_le; assumption).
  destruct (b64ae_mult_err r r Fr Fr ltac:(lra)) as [Fz Ez].
  pose proof (b64ae_u_mul_le _ _ Bz) as Uz.
  rewrite Uv in Uz, Ez.
  assert (Ez' : Rabs (B2R (b64_mult r r) - B2R r * B2R r)
                <= / 9007199254740992 * (64 / 25) + b64ae_e0) by lra.
  split; [exact Fz|]. split; [exact Ez'|].
  pose proof (Rabs_triang_inv (B2R (b64_mult r r)) (B2R r * B2R r)). lra.
Qed.

Lemma sn_P_bound : forall y, Rabs y <= 41 / 16 ->
  Rabs (hz_horner_R (map B2R sp_coeffs) y) <= 7 / 4.
Proof.
  intros y Hy.
  eapply Rle_trans; [apply (hz_horner_R_bound sp_coeffs sp_ms y sp_Z sp_coeffs_ok);
                     unfold sp_Z; exact Hy|].
  exact sp_M_bound.
Qed.

Lemma sn_P_lip : forall y w, Rabs y <= 41 / 16 -> Rabs w <= 41 / 16 ->
  Rabs (hz_horner_R (map B2R sp_coeffs) y - hz_horner_R (map B2R sp_coeffs) w)
    <= 11 / 32 * Rabs (y - w).
Proof.
  intros y w Hy Hw.
  eapply Rle_trans;
    [apply (hz_horner_R_lip (map B2R sp_coeffs) sp_ms y w sp_Z sp_coeffs_ok_R);
     unfold sp_Z; assumption|].
  apply Rmult_le_compat_r; [apply Rabs_pos | exact sp_L_bound].
Qed.

Lemma sn_p_facts : forall z, fin z = true -> Rabs (B2R z) <= 41 / 16 ->
  fin (b64_horner sp_coeffs z) = true /\
  Rabs (B2R (b64_horner sp_coeffs z) - hz_horner_R (map B2R sp_coeffs) (B2R z))
    <= / {2**51} /\
  Rabs (B2R (b64_horner sp_coeffs z)) <= 7 / 4 + / {2**51}.
Proof.
  intros z Fz Hz.
  destruct (b64_sinpoly_eval_err z Fz Hz) as [Fp Ep].
  replace (bpow radix2 (-51)) with (/ {2**51}) in Ep by (cbn; reflexivity).
  pose proof (sn_P_bound _ Hz) as HP.
  split; [exact Fp|]. split; [exact Ep|].
  pose proof (Rabs_triang_inv (B2R (b64_horner sp_coeffs z))
                              (hz_horner_R (map B2R sp_coeffs) (B2R z))). lra.
Qed.

Lemma sn_s_facts : forall r p, fin r = true -> fin p = true ->
  Rabs (B2R r) <= 8 / 5 -> Rabs (B2R p) <= 7 / 4 + / {2**51} ->
  fin (b64_mult r p) = true /\
  Rabs (B2R (b64_mult r p) - B2R r * B2R p)
    <= / 9007199254740992 * (8 / 5 * (7 / 4 + / {2**51})) + b64ae_e0.
Proof.
  intros r p Fr Fp Hr Hp.
  pose proof sp_u_val as Uv.
  assert (Hb : 4 <= bpow radix2 1000) by exact sp_bpow1000.
  assert (Bs : Rabs (B2R r * B2R p) <= 8 / 5 * (7 / 4 + / {2**51}))
    by (apply b64ae_abs_mult_le; assumption).
  destruct (b64ae_mult_err r p Fr Fp ltac:(lra)) as [Fs Es].
  pose proof (b64ae_u_mul_le _ _ Bs) as Us.
  rewrite Uv in Us, Es.
  split; [exact Fs | lra].
Qed.

Lemma sn_core_err : forall r, fin r = true -> Rabs (B2R r) <= 8 / 5 ->
  fin (sn_core r) = true /\ Rabs (B2R (sn_core r) - sin (B2R r)) <= sn_Ecore.
Proof.
  intros r Fr Hr. unfold sn_core.
  pose proof sp_e0_bounds as [He0 He1].
  destruct (sn_z_facts r Fr Hr) as [Fz [Ez Hz]].
  destruct (sn_p_facts _ Fz Hz) as [Fp [Ep Hp]].
  destruct (sn_s_facts r _ Fr Fp Hr Hp) as [Fs Es].
  assert (Hxx : Rabs (B2R r * B2R r) <= 41 / 16).
  {{ assert (Rabs (B2R r * B2R r) <= 8 / 5 * (8 / 5)) by (apply b64ae_abs_mult_le; assumption).
    lra. }}
  split; [exact Fs|].
  exact (sn_core_alg (B2R r) (B2R (b64_mult r r)) (B2R (b64_horner sp_coeffs (b64_mult r r)))
           (B2R (b64_mult r (b64_horner sp_coeffs (b64_mult r r))))
           (hz_horner_R (map B2R sp_coeffs) (B2R (b64_mult r r)))
           (hz_horner_R (map B2R sp_coeffs) (B2R r * B2R r))
           (hz_horner_R sp_exact (B2R r * B2R r)) b64ae_e0
           (conj He0 He1) Hr Es Ep (sn_P_lip _ _ Hz Hxx) Ez
           (sp_coef_err _ Hxx) (sp_trunc _ Hr)).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Reduction r = (x - k C1) - k C2, k in 1..3.                            *)
(* -------------------------------------------------------------------------- *)

Definition sn_red (x kf : binary64) : binary64 :=
  b64_minus (b64_minus x (b64_mult kf sn_C1)) (b64_mult kf sn_C2).

Definition sn_Ered : R := {Rq(Erb)}.

Lemma sn_red_budget : forall e, 0 < e <= / 9007199254740992 / 9007199254740992 ->
  (/ 9007199254740992 * (8 / 5) + e) + (/ 9007199254740992 * (3 * sn_c2) + e)
  + 3 * / {2**62} <= sn_Ered.
Proof. intros e He. unfold sn_Ered, sn_c2. lra. Qed.

Lemma sn_c_vals : sn_c1 = {Rq(C1)} /\ sn_c2 = {Rq(C2)}.
Proof. split; reflexivity. Qed.

Lemma sn_t1_exact : forall (kf kc1 : binary64) (k : R),
  fin kf = true -> B2R kf = k -> B2R kc1 = k * sn_c1 ->
  fin (b64_mult kf sn_C1) = true /\ B2R (b64_mult kf sn_C1) = B2R kc1.
Proof.
  intros kf kc1 k Fk Ek Ekc.
  destruct sn_C1_R as [EC1 FC1].
  assert (Et1r : b64_round (B2R kf * B2R sn_C1) = B2R kc1).
  {{ rewrite Ek, EC1. fold sn_c1. rewrite <- Ekc.
    apply b64_round_generic. apply b64_format_B2R. }}
  assert (St1 : b64_safe Rmult kf sn_C1).
  {{ split; [exact Fk|]. split; [exact FC1|]. rewrite Et1r.
    apply (Binary.abs_B2R_lt_emax prec emax). }}
  destruct (b64_mult_correct _ _ St1) as [Et1 Ft1].
  split; [exact Ft1|]. rewrite Et1. exact Et1r.
Qed.

Lemma sn_r1_exact : forall (x kf kc1 : binary64) (k : R),
  fin x = true -> fin kf = true -> B2R kf = k -> 1 <= k <= 3 ->
  B2R kc1 = k * sn_c1 -> B2R kc1 / 2 <= B2R x <= 2 * B2R kc1 ->
  Rabs (B2R x - k * PI) <= {Rq(Rred)} ->
  fin (b64_minus x (b64_mult kf sn_C1)) = true /\
  B2R (b64_minus x (b64_mult kf sn_C1)) = B2R x - k * sn_c1.
Proof.
  intros x kf kc1 k Fx Fk Ek Hk Ekc Hst Hr.
  destruct (sn_t1_exact kf kc1 k Fk Ek Ekc) as [Ft1 Et1].
  pose proof sn_pi_range as [Pl Ph]. destruct sn_c_vals as [Hc1 _].
  assert (Fmt : b64_format (B2R x - B2R kc1)).
  {{ apply (sterbenz radix2 (SpecFloat.fexp prec emax));
      [apply b64_format_B2R | apply b64_format_B2R | exact Hst]. }}
  assert (Er1r : b64_round (B2R x - B2R (b64_mult kf sn_C1)) = B2R x - B2R kc1).
  {{ rewrite Et1. apply b64_round_generic. exact Fmt. }}
  assert (Hsm : Rabs (B2R x - B2R kc1) <= 2).
  {{ rewrite Ekc. replace (B2R x - k * sn_c1) with ((B2R x - k * PI) + k * (PI - sn_c1)) by ring.
    eapply Rle_trans; [apply Rabs_triang|].
    assert (Rabs (k * (PI - sn_c1)) <= 3 * / 1000000000000000).
    {{ rewrite Rabs_mult, Rabs_pos_eq by lra.
      assert (Rabs (PI - sn_c1) <= / 1000000000000000)
        by (rewrite Hc1; apply Rabs_le; split; lra).
      apply Rmult_le_compat; try lra; apply Rabs_pos. }}
    lra. }}
  assert (Sr1 : b64_safe Rminus x (b64_mult kf sn_C1)).
  {{ split; [exact Fx|]. split; [exact Ft1|]. rewrite Er1r.
    apply Rle_lt_trans with 2; [exact Hsm|].
    apply Rle_lt_trans with (bpow radix2 2); [cbn; lra | apply bpow_lt; unfold emax; lia]. }}
  destruct (b64_minus_correct _ _ Sr1) as [Er1 Fr1].
  split; [exact Fr1|]. rewrite Er1, Er1r, Ekc. reflexivity.
Qed.

Lemma sn_t2_facts : forall (kf : binary64) (k : R),
  fin kf = true -> B2R kf = k -> 1 <= k <= 3 ->
  fin (b64_mult kf sn_C2) = true /\
  Rabs (B2R (b64_mult kf sn_C2) - k * sn_c2)
    <= / 9007199254740992 * (3 * sn_c2) + b64ae_e0 /\
  Rabs (B2R (b64_mult kf sn_C2)) <= / 1000000000000000.
Proof.
  intros kf k Fk Ek Hk.
  destruct sn_C2_R as [EC2 FC2]. fold sn_c2 in EC2. destruct sn_c_vals as [_ Hc2].
  pose proof sp_u_val as Uv. pose proof sp_e0_bounds as [He0 He1].
  assert (Bt2 : Rabs (B2R kf * B2R sn_C2) <= 3 * sn_c2).
  {{ rewrite Ek, EC2, Rabs_mult, (Rabs_pos_eq k), (Rabs_pos_eq sn_c2) by (rewrite ?Hc2; lra).
    apply Rmult_le_compat_r; [rewrite Hc2; lra | lra]. }}
  assert (B1 : Rabs (B2R kf * B2R sn_C2) <= bpow radix2 1000).
  {{ eapply Rle_trans; [exact Bt2|]. rewrite Hc2.
    apply Rle_trans with 4; [lra | exact sp_bpow1000]. }}
  destruct (b64ae_mult_err kf sn_C2 Fk FC2 B1) as [Ft2 Et2].
  pose proof (b64ae_u_mul_le _ _ Bt2) as Ut2.
  rewrite Uv in Ut2, Et2. rewrite Ek, EC2 in Et2, Ut2.
  split; [exact Ft2|]. split; [lra|].
  pose proof (Rabs_triang_inv (B2R (b64_mult kf sn_C2)) (k * sn_c2)).
  assert (Rabs (k * sn_c2) <= 3 * sn_c2)
    by (rewrite <- EC2, <- Ek; exact Bt2).
  assert (Rabs (B2R (b64_mult kf sn_C2) - k * sn_c2) <= / 9007199254740992 * (3 * sn_c2) + b64ae_e0)
    by lra.
  rewrite Hc2 in *. lra.
Qed.

Lemma sn_r_facts : forall (a b : binary64), fin a = true -> fin b = true ->
  Rabs (B2R a - B2R b) <= 8 / 5 ->
  fin (b64_minus a b) = true /\
  Rabs (B2R (b64_minus a b) - (B2R a - B2R b)) <= / 9007199254740992 * (8 / 5) + b64ae_e0.
Proof.
  intros a b Fa Fb Hab. pose proof sp_u_val as Uv.
  destruct (b64ae_minus_err a b Fa Fb
              ltac:(eapply Rle_trans; [exact Hab|];
                    apply Rle_trans with 4; [lra | exact sp_bpow1000])) as [Fr Er].
  pose proof (b64ae_u_mul_le _ _ Hab) as U3. rewrite Uv in U3, Er.
  split; [exact Fr | lra].
Qed.

(* The reduction budget as pure real algebra. *)
Lemma sn_red_alg : forall (xr k r1 t2 rr e : R),
  0 < e <= / 9007199254740992 / 9007199254740992 -> 1 <= k <= 3 ->
  r1 = xr - k * sn_c1 ->
  Rabs (t2 - k * sn_c2) <= / 9007199254740992 * (3 * sn_c2) + e ->
  Rabs (rr - (r1 - t2)) <= / 9007199254740992 * (8 / 5) + e ->
  Rabs (xr - k * PI) <= {Rq(Rred)} ->
  Rabs (rr - (xr - k * PI)) <= sn_Ered /\ Rabs rr <= 8 / 5.
Proof.
  intros xr k r1 t2 rr e He Hk Er1 Et2 Er Hr.
  pose proof sn_pi_gap as Gap.
  pose proof (sn_red_budget e He) as Bud.
  assert (G : Rabs (k * (PI - (sn_c1 + sn_c2))) <= 3 * / {2**62}).
  {{ rewrite Rabs_mult, (Rabs_pos_eq k) by lra.
    apply Rmult_le_compat; try lra; apply Rabs_pos. }}
  assert (E : rr - (xr - k * PI)
              = (rr - (r1 - t2)) + (k * sn_c2 - t2) + k * (PI - (sn_c1 + sn_c2)))
    by (rewrite Er1; ring).
  assert (Hred : Rabs (rr - (xr - k * PI)) <= sn_Ered).
  {{ rewrite E.
    pose proof (Rabs_triang ((rr - (r1 - t2)) + (k * sn_c2 - t2))
                            (k * (PI - (sn_c1 + sn_c2)))) as T1.
    pose proof (Rabs_triang (rr - (r1 - t2)) (k * sn_c2 - t2)) as T2.
    rewrite <- Rabs_Ropp in Et2. rewrite Ropp_minus_distr in Et2.
    lra. }}
  split; [exact Hred|].
  pose proof (Rabs_triang_inv rr (xr - k * PI)) as T.
  unfold sn_Ered in Hred. lra.
Qed.

Lemma sn_red_err : forall (x kf kc1 : binary64) (k : R),
  fin x = true -> fin kf = true -> B2R kf = k -> 1 <= k <= 3 ->
  B2R kc1 = k * sn_c1 ->
  B2R kc1 / 2 <= B2R x <= 2 * B2R kc1 ->
  Rabs (B2R x - k * PI) <= {Rq(Rred)} ->
  fin (sn_red x kf) = true /\
  Rabs (B2R (sn_red x kf) - (B2R x - k * PI)) <= sn_Ered /\
  Rabs (B2R (sn_red x kf)) <= 8 / 5.
Proof.
  intros x kf kc1 k Fx Fk Ek Hk Ekc Hst Hr. unfold sn_red.
  pose proof sp_e0_bounds as [He0 He1].
  pose proof sn_pi_range as [Pl Ph]. destruct sn_c_vals as [Hc1 Hc2].
  destruct (sn_r1_exact x kf kc1 k Fx Fk Ek Hk Ekc Hst Hr) as [Fr1 Er1].
  destruct (sn_t2_facts kf k Fk Ek Hk) as [Ft2 [Et2 Bt2]].
  assert (Hdiff : Rabs (B2R (b64_minus x (b64_mult kf sn_C1)) - B2R (b64_mult kf sn_C2)) <= 8 / 5).
  {{ rewrite Er1.
    replace (B2R x - k * sn_c1 - B2R (b64_mult kf sn_C2))
      with ((B2R x - k * PI) + k * (PI - sn_c1) - B2R (b64_mult kf sn_C2)) by ring.
    assert (Rabs (k * (PI - sn_c1)) <= 3 * / 1000000000000000).
    {{ rewrite Rabs_mult, Rabs_pos_eq by lra.
      assert (Rabs (PI - sn_c1) <= / 1000000000000000)
        by (rewrite Hc1; apply Rabs_le; split; lra).
      apply Rmult_le_compat; try lra; apply Rabs_pos. }}
    pose proof (Rabs_triang ((B2R x - k * PI) + k * (PI - sn_c1)) (- B2R (b64_mult kf sn_C2))) as T1.
    pose proof (Rabs_triang (B2R x - k * PI) (k * (PI - sn_c1))) as T2.
    rewrite Rabs_Ropp in T1. unfold Rminus at 1. lra. }}
  destruct (sn_r_facts _ _ Fr1 Ft2 Hdiff) as [Fr Er].
  split; [exact Fr|].
  exact (sn_red_alg (B2R x) k (B2R (b64_minus x (b64_mult kf sn_C1)))
           (B2R (b64_mult kf sn_C2)) (B2R (b64_minus (b64_minus x (b64_mult kf sn_C1))
                                                      (b64_mult kf sn_C2)))
           b64ae_e0 (conj He0 He1) Hk Er1 Et2 Er Hr).
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Assembly.                                                              *)
(* -------------------------------------------------------------------------- *)

Definition sn_pos (x : binary64) : binary64 :=
  if b64_le x sn_T1 then sn_core x
  else if b64_le x sn_T3 then sn_neg (sn_core (sn_red x sn_one))
  else if b64_le x sn_T5 then sn_core (sn_red x sn_two)
  else sn_neg (sn_core (sn_red x sn_three)).

Definition b64_sin (x : binary64) : binary64 :=
  if b64_le hz_zero x then sn_pos x else sn_neg (sn_pos (sn_neg x)).

Definition sin_accept (x : binary64) : bool :=
  Binary.is_finite prec emax x && b64_le sn_mten x && b64_le x sn_ten.

Lemma sn_sin_shift1 : forall y, sin (y - 1 * PI) = - sin y.
Proof. intro y. rewrite Rmult_1_l, sin_minus, sin_PI, cos_PI. ring. Qed.

Lemma sn_sin_shift2 : forall y, sin (y - 2 * PI) = sin y.
Proof. intro y. rewrite sin_minus, sin_2PI, cos_2PI. ring. Qed.

Lemma sn_sin_shift3 : forall y, sin (y - 3 * PI) = - sin y.
Proof.
  intro y. replace (y - 3 * PI) with ((y - 2 * PI) - 1 * PI) by ring.
  rewrite sn_sin_shift1, sn_sin_shift2. reflexivity.
Qed.

(* One reduced branch: (-1)^k core(r) against sin x. *)
Lemma sn_branch : forall (x kf kc1 : binary64) (k sg : R),
  fin x = true -> fin kf = true -> B2R kf = k -> 1 <= k <= 3 ->
  B2R kc1 = k * sn_c1 ->
  B2R kc1 / 2 <= B2R x <= 2 * B2R kc1 ->
  Rabs (B2R x - k * PI) <= {Rq(Rred)} ->
  (sg = 1 \\/ sg = -1) -> sin (B2R x - k * PI) = sg * sin (B2R x) ->
  fin (sn_core (sn_red x kf)) = true /\\
  Rabs (sg * B2R (sn_core (sn_red x kf)) - sin (B2R x)) <= sn_Ecore + sn_Ered.
Proof.
  intros x kf kc1 k sg Fx Fk Ek Hk Ekc Hst Hr Hsg Hsin.
  destruct (sn_red_err x kf kc1 k Fx Fk Ek Hk Ekc Hst Hr) as [Fr [Er Br]].
  destruct (sn_core_err _ Fr Br) as [Fc Ec].
  split; [exact Fc|].
  set (c := B2R (sn_core (sn_red x kf))) in *.
  set (r := B2R (sn_red x kf)) in *.
  assert (Ls := sin_lip r (B2R x - k * PI)).
  assert (E : sg * c - sin (B2R x) = sg * ((c - sin r) + (sin r - sin (B2R x - k * PI)))).
  {{ rewrite Hsin. destruct Hsg as [-> | ->]; ring. }}
  rewrite E, Rabs_mult.
  assert (Hs : Rabs sg = 1) by (destruct Hsg as [-> | ->]; [apply Rabs_R1 | rewrite Rabs_left by lra; ring]).
  rewrite Hs, Rmult_1_l.
  eapply Rle_trans; [apply Rabs_triang|]. lra.
Qed.

Lemma sn_Etot : sn_Ecore + sn_Ered <= bpow radix2 (-49).
Proof.
  replace (bpow radix2 (-49)) with (/ {2**49}) by (cbn; reflexivity).
  unfold sn_Ecore, sn_Ered. lra.
Qed.

Lemma sn_pos_err : forall x, fin x = true -> 0 <= B2R x <= 10 ->
  fin (sn_pos x) = true /\\ Rabs (B2R (sn_pos x) - sin (B2R x)) <= sn_Ecore + sn_Ered.
Proof.
  intros x Fx Hx.
  destruct sn_T1_R as [ET1 FT1]. destruct sn_T3_R as [ET3 FT3]. destruct sn_T5_R as [ET5 FT5].
  destruct sn_one_R as [E1 F1]. destruct sn_two_R as [E2 F2]. destruct sn_three_R as [E3 F3].
  destruct sn_C1_R as [EC1 FC1]. destruct sn_two_C1_R as [E2C F2C]. destruct sn_three_C1_R as [E3C F3C].
  pose proof sn_pi_range as [Pl Ph].
  assert (Hred_pos : 0 <= sn_Ered) by (unfold sn_Ered; lra).
  unfold sn_pos.
  destruct (b64_le x sn_T1) eqn:L1.
  - apply b64ae_le_true in L1; [|exact Fx|exact FT1]. rewrite ET1 in L1.
    destruct (sn_core_err x Fx ltac:(rewrite Rabs_pos_eq by lra; lra)) as [Fc Ec].
    split; [exact Fc|]. lra.
  - apply b64ae_le_false in L1; [|exact Fx|exact FT1]. rewrite ET1 in L1.
    destruct (b64_le x sn_T3) eqn:L3.
    + apply b64ae_le_true in L3; [|exact Fx|exact FT3]. rewrite ET3 in L3.
      destruct (sn_branch x sn_one sn_C1 1 (-1) Fx F1 E1 ltac:(lra)
                  ltac:(rewrite EC1; unfold sn_c1; lra)
                  ltac:(rewrite EC1; split; lra)
                  ltac:(apply Rabs_le; split; lra)
                  ltac:(right; reflexivity)
                  ltac:(rewrite sn_sin_shift1; ring)) as [Fc Ec].
      destruct (sn_neg_ok _ Fc) as [Fn En].
      split; [exact Fn|]. rewrite En.
      replace (- B2R (sn_core (sn_red x sn_one))) with (-1 * B2R (sn_core (sn_red x sn_one))) by ring.
      exact Ec.
    + apply b64ae_le_false in L3; [|exact Fx|exact FT3]. rewrite ET3 in L3.
      destruct (b64_le x sn_T5) eqn:L5.
      * apply b64ae_le_true in L5; [|exact Fx|exact FT5]. rewrite ET5 in L5.
        destruct (sn_branch x sn_two sn_two_C1 2 1 Fx F2 E2 ltac:(lra)
                    ltac:(rewrite E2C; unfold sn_c1; lra)
                    ltac:(rewrite E2C; split; lra)
                    ltac:(apply Rabs_le; split; lra)
                    ltac:(left; reflexivity)
                    ltac:(rewrite sn_sin_shift2; ring)) as [Fc Ec].
        split; [exact Fc|]. rewrite <- (Rmult_1_l (B2R (sn_core (sn_red x sn_two)))). exact Ec.
      * apply b64ae_le_false in L5; [|exact Fx|exact FT5]. rewrite ET5 in L5.
        destruct (sn_branch x sn_three sn_three_C1 3 (-1) Fx F3 E3 ltac:(lra)
                    ltac:(rewrite E3C; unfold sn_c1; lra)
                    ltac:(rewrite E3C; split; lra)
                    ltac:(apply Rabs_le; split; lra)
                    ltac:(right; reflexivity)
                    ltac:(rewrite sn_sin_shift3; ring)) as [Fc Ec].
        destruct (sn_neg_ok _ Fc) as [Fn En].
        split; [exact Fn|]. rewrite En.
        replace (- B2R (sn_core (sn_red x sn_three))) with (-1 * B2R (sn_core (sn_red x sn_three))) by ring.
        exact Ec.
Qed.

(* WITNESS {{"claimId":"s2-b64-sin","topic":"numerics","lemma":"b64_sin_err","title":"Binary64 sine: for every finite input with |x| <= 10 (sin_accept), the RNE evaluator b64_sin (mod-pi Sterbenz reduction, degree-21 Horner) is finite and within 2^-49 of sin x","file":"theories-flocq/B64_Sin.v","witness":"b64_sin_err","board":"ADR-0006"}} *)
Theorem b64_sin_err : forall x, sin_accept x = true ->
  fin (b64_sin x) = true /\\ Rabs (B2R (b64_sin x) - sin (B2R x)) <= bpow radix2 (-49).
Proof.
  intros x Hacc. unfold sin_accept in Hacc.
  apply andb_prop in Hacc as [Hacc Hhi]. apply andb_prop in Hacc as [Fx Hlo].
  destruct sn_ten_R as [Et Ft]. destruct sn_mten_R as [Em Fm].
  apply b64ae_le_true in Hlo; [|exact Fm|exact Fx]. apply b64ae_le_true in Hhi; [|exact Fx|exact Ft].
  rewrite Em in Hlo. rewrite Et in Hhi.
  pose proof sn_Etot as Tot.
  unfold b64_sin.
  destruct (b64_le hz_zero x) eqn:Z0.
  - apply b64ae_le_true in Z0; [|reflexivity|exact Fx].
    replace (B2R hz_zero) with 0 in Z0 by reflexivity.
    destruct (sn_pos_err x Fx ltac:(split; lra)) as [F E].
    split; [exact F | lra].
  - apply b64ae_le_false in Z0; [|reflexivity|exact Fx].
    replace (B2R hz_zero) with 0 in Z0 by reflexivity.
    destruct (sn_neg_ok x Fx) as [Fy Ey].
    destruct (sn_pos_err (sn_neg x) Fy ltac:(rewrite Ey; split; lra)) as [Fp Ep].
    destruct (sn_neg_ok _ Fp) as [Fn En].
    split; [exact Fn|]. rewrite En, Ey in *. rewrite sin_neg in Ep.
    replace (- B2R (sn_pos (sn_neg x)) - sin (B2R x))
      with (- (B2R (sn_pos (sn_neg x)) - - sin (B2R x))) by ring.
    rewrite Rabs_Ropp. lra.
Qed.

(* Extractable intake: the two comparisons alone already reject NaN and
   both infinities, so is_finite is redundant (and is a binary_float match,
   which the native-float extraction does not support). *)
Definition sin_accept_b (x : binary64) : bool :=
  b64_le sn_mten x && b64_le x sn_ten.

Lemma sin_accept_b_eq : forall x, sin_accept_b x = sin_accept x.
Proof.
  intros [s|s|s pl Hpl|s m e Hb]; unfold sin_accept_b, sin_accept; cbn [Binary.is_finite andb];
    try reflexivity.
  all: try (destruct s; vm_compute; reflexivity).
  all: vm_compute; reflexivity.
Qed.

Corollary b64_sin_err_b : forall x, sin_accept_b x = true ->
  fin (b64_sin x) = true /\ Rabs (B2R (b64_sin x) - sin (B2R x)) <= bpow radix2 (-49).
Proof. intros x H. rewrite sin_accept_b_eq in H. exact (b64_sin_err x H). Qed.

Print Assumptions sn_neg_ok.
Print Assumptions sn_core_alg.
Print Assumptions sn_core_err.
Print Assumptions sn_red_alg.
Print Assumptions sn_red_err.
Print Assumptions sn_pos_err.
Print Assumptions b64_sin_err.
Print Assumptions sin_accept_b_eq.
Print Assumptions b64_sin_err_b.
""")
out_text="\n".join(o)+"\n"
out_text=out_text.replace(" /  ", " /\\\n  ")
open(sys.argv[1],'w').write(out_text)
