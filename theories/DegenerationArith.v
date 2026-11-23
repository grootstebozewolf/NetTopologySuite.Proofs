(* ============================================================================
   NetTopologySuite.Proofs.DegenerationArith
   ----------------------------------------------------------------------------
   The arithmetic steps inside
   Development.AbelianVarietyTheory.Proofs.DegenerationProofs
   (mirror C:\rh, CocoSgt/riemann-hypothesis-lean @ 7cbf7a0).

   Ported from the proofs' own calculations:
     CharSumInv.charSum_inv                         the (phi-1)*S = 0 step
     IsThetaPtDown.isThetaPt_down                   Nat.odd_mul and the ring
                                                    rewrite (n*m)^2 = n*m^2*n
     WeilPairingLabelledTorsionUniformTest.weilIs_uTest
       and ThetaSystemSumCharacterOrthogonalEqZero  (r*N)^2 <> 0 and
                                                    (r*N)^2 / (r*N) = r*N
     ExistsObjectWithThetaPointOfDegenerationSeries
       dvd_pow_sub (mul and add witnesses), dvd_of_dvd_sq (sub_sub_cancel
       and the square-power factor), eq_zero_of_sq (the cancel step),
       exists_linear (the two-variable split at rho^2 = -d)
     ExistsPowerSectionOfChartFunctions.prod_cubN_wS
                                                    sum_{j<k} j = ((k-1)/2)*k
                                                    for odd k
     HomTransport.Rel.pow                           induction on the relation
     HomTransport.wQ_eq                             (2*j+1-1)/2 = j
     tx_scale                                       (m*(2*k))/2 = m*k and
                                                    (m*a)/m = a
     norm_unit / norm_valF                          a*b = 1 with both <= 1
     nonempty_equiv_of_basis                        (v^c)^k = 1 from v^k = 1
     tors_of_integral                               odd and >= 2 gives >= 3
     exists_prime_unit                              n >= d+3 excludes 2 and n|d
     exists_hom                                     (a/u)*u = a
     isProper_of_unit_in_cosets                     |x| = 1 excludes 0

   Card-of-Hom, existence of a nontrivial character, Freshman's dream,
   Euler's totient congruence, and every scheme elaboration stay outside
   this file.  They are named in the probe.

   The Lean build log does reach DegenerationProofs (about 52-58s per
   file).  CharacterSumInverse.main's tactics are unused; the live proof
   is charSum_inv.  Where `ring` fails the log says to use `ring_nf`
   (line 9683).  These lemmas are that normal form: `lia` and `lra`.

   claimId: none
   No Admitted, no Axiom, no Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Cursor Grok 4.7
   ============================================================================ *)

From Stdlib Require Import Arith Lia Reals Lra ZArith List.
Import ListNotations.

(* ------------------------------------------------------------------------ *)
(* Odd product.  Nat.odd_mul, used as (Nat.odd_mul.1 H.1).2.                 *)
(* ------------------------------------------------------------------------ *)

Lemma nat_even_or_odd (n : nat) : Nat.Even n \/ Nat.Odd n.
Proof.
  induction n as [| n IH].
  - left. exists 0%nat. reflexivity.
  - destruct IH as [[k Hk] | [k Hk]].
    + right. exists k. lia.
    + left. exists (S k). lia.
Qed.

Lemma odd_mul_iff (n m : nat) :
  Nat.Odd (n * m)%nat <-> Nat.Odd n /\ Nat.Odd m.
Proof.
  split.
  - intros [k Hk]. split.
    + destruct (nat_even_or_odd n) as [[a Ha] | Hn].
      * exfalso. lia.
      * exact Hn.
    + destruct (nat_even_or_odd m) as [[b Hb] | Hm].
      * exfalso. lia.
      * exact Hm.
  - intros [[a Ha] [b Hb]].
    exists (2 * a * b + a + b)%nat. lia.
Qed.

Lemma nm_sq_split (n m : nat) :
  ((n * m) ^ 2 = n * (m ^ 2) * n)%nat.
Proof.
  cbn. rewrite !Nat.mul_1_r.
  rewrite (Nat.mul_comm n m) at 2.
  rewrite (Nat.mul_assoc (n * m) m n).
  rewrite <- (Nat.mul_assoc n m m).
  reflexivity.
Qed.

Lemma sq_mul_ne_zero (r N : nat) :
  (0 < r)%nat -> (0 < N)%nat -> ((r * N) ^ 2 <> 0)%nat.
Proof.
  intros Hr HN Heq.
  cbn in Heq. rewrite !Nat.mul_1_r in Heq. lia.
Qed.

Lemma sq_div_self (k : nat) :
  (k <> 0)%nat -> ((k ^ 2) / k = k)%nat.
Proof.
  intros Hk. cbn. rewrite Nat.mul_1_r. apply Nat.div_mul. exact Hk.
Qed.

Lemma nat_mul_div_cancel (m a : nat) :
  (m <> 0)%nat -> ((m * a) / m = a)%nat.
Proof.
  intros Hm. rewrite Nat.mul_comm. apply Nat.div_mul. exact Hm.
Qed.

Lemma nat_even_mul_div2 (m k : nat) :
  ((m * (2 * k)) / 2 = m * k)%nat.
Proof.
  rewrite Nat.mul_assoc.
  rewrite (Nat.mul_comm m 2).
  rewrite <- Nat.mul_assoc.
  rewrite (Nat.mul_comm 2 (m * k)).
  apply Nat.div_mul. discriminate.
Qed.

(* HomTransport.wQ_eq.  Odd k = 2*j+1, and the chart index is j. *)

Lemma odd_pred_half (j : nat) :
  ((2 * j + 1 - 1) / 2 = j)%nat.
Proof.
  replace (2 * j + 1 - 1)%nat with (2 * j)%nat by lia.
  rewrite Nat.mul_comm. apply Nat.div_mul. discriminate.
Qed.

(* tors_of_integral.  An odd integer that is already at least 2 is at least 3. *)

Lemma odd_ge_three (n : nat) :
  Nat.Odd n -> (2 <= n)%nat -> (3 <= n)%nat.
Proof.
  intros [k Hk] Hn. subst n. lia.
Qed.

(* exists_prime_unit.  A prime at least d+3 is not 2, and it cannot divide d. *)

Lemma shift_ne_two (n d : nat) :
  (d + 3 <= n)%nat -> (n <> 2)%nat.
Proof. lia. Qed.

Lemma no_dvd_from_shift (n d : nat) :
  (d <> 0)%nat -> (d + 3 <= n)%nat -> ~ Nat.divide n d.
Proof.
  intros Hd Hle [k Hk].
  destruct k as [| k].
  - cbn in Hk. lia.
  - assert (HleN : (n <= d)%nat).
    { rewrite Hk.
      apply Nat.le_trans with (1 * n)%nat.
      - rewrite Nat.mul_1_l. apply Nat.le_refl.
      - apply Nat.mul_le_mono_r. lia. }
    lia.
Qed.

Lemma nat_pow_lower (d e : nat) :
  (1 <= d)%nat -> (1 <= d ^ e)%nat.
Proof.
  intros Hd. induction e as [| e IH].
  - cbn. lia.
  - cbn. apply Nat.le_trans with (d * 1)%nat.
    + rewrite Nat.mul_1_r. exact Hd.
    + apply Nat.mul_le_mono_l. exact IH.
Qed.

Lemma nat_two_le_pow (d e : nat) :
  (2 <= d)%nat -> (1 <= e)%nat -> (2 <= d ^ e)%nat.
Proof.
  intros Hd He. destruct e as [| e].
  - lia.
  - cbn. apply Nat.le_trans with (d * 1)%nat.
    + rewrite Nat.mul_1_r. exact Hd.
    + apply Nat.mul_le_mono_l. apply nat_pow_lower. lia.
Qed.

(* sum of 0 .. k-1.  Finset.sum_range_id. *)

Fixpoint sum_below (k : nat) : nat :=
  match k with
  | 0 => 0
  | S m => (sum_below m + m)%nat
  end.

Lemma sum_below_double (k : nat) :
  (2 * sum_below k = k * (k - 1))%nat.
Proof.
  induction k as [| k IH].
  - cbn. reflexivity.
  - cbn [sum_below].
    replace (S k - 1)%nat with k by lia.
    rewrite Nat.mul_add_distr_l. rewrite IH.
    destruct k as [| k].
    + cbn. reflexivity.
    + replace (S k - 1)%nat with k by lia.
      rewrite (Nat.mul_comm 2 (S k)).
      rewrite <- Nat.mul_add_distr_l.
      replace (k + 2)%nat with (S (S k)) by lia.
      rewrite Nat.mul_comm. reflexivity.
Qed.

Lemma sum_range_odd_half (k : nat) :
  Nat.Odd k -> (sum_below k = ((k - 1) / 2) * k)%nat.
Proof.
  intros [l Hl]. subst k.
  assert (E : (2 * sum_below (2 * l + 1) = 2 * (l * (2 * l + 1)))%nat).
  { rewrite sum_below_double.
    replace (2 * l + 1 - 1)%nat with (2 * l)%nat by lia.
    rewrite (Nat.mul_comm (2 * l + 1) (2 * l)).
    rewrite <- (Nat.mul_assoc 2 l (2 * l + 1)).
    reflexivity. }
  assert (Hd : ((2 * sum_below (2 * l + 1)) / 2 = sum_below (2 * l + 1))%nat).
  { rewrite Nat.mul_comm. apply Nat.div_mul. discriminate. }
  rewrite <- Hd. rewrite E.
  rewrite (Nat.mul_comm 2 (l * (2 * l + 1))).
  rewrite Nat.div_mul by discriminate.
  replace ((2 * l + 1 - 1) / 2)%nat with l.
  - reflexivity.
  - replace (2 * l + 1 - 1)%nat with (2 * l)%nat by lia.
    symmetry. rewrite (Nat.mul_comm 2 l). apply Nat.div_mul. discriminate.
Qed.

(* ------------------------------------------------------------------------ *)
(* Real steps.                                                              *)
(* ------------------------------------------------------------------------ *)

Local Open Scope R_scope.

Lemma rpow_add_nat (x : R) (a b : nat) :
  x ^ (a + b) = x ^ a * x ^ b.
Proof.
  induction a as [| a IH]; cbn.
  - rewrite Rmult_1_l. reflexivity.
  - rewrite IH. rewrite Rmult_assoc. reflexivity.
Qed.

Lemma rpow_mul_base (x y : R) (e : nat) :
  (x * y) ^ e = x ^ e * y ^ e.
Proof.
  induction e as [| e IH]; cbn.
  - rewrite Rmult_1_l. reflexivity.
  - rewrite IH. rewrite Rmult_assoc.
    rewrite <- (Rmult_assoc y (x ^ e) (y ^ e)).
    rewrite (Rmult_comm y (x ^ e)).
    rewrite Rmult_assoc. rewrite <- Rmult_assoc. reflexivity.
Qed.

Lemma rpow_mul_exp (x : R) (a b : nat) :
  x ^ (a * b) = (x ^ a) ^ b.
Proof.
  induction b as [| b IH].
  - rewrite Nat.mul_0_r. reflexivity.
  - rewrite Nat.mul_succ_r. rewrite rpow_add_nat. cbn.
    rewrite IH. rewrite Rmult_comm. reflexivity.
Qed.

Lemma rpow_one (x : R) : x ^ 1 = x.
Proof. cbn. apply Rmult_1_r. Qed.

Lemma rpow_one_base (n : nat) : 1 ^ n = 1.
Proof.
  induction n as [| n IH]; cbn.
  - reflexivity.
  - rewrite IH. lra.
Qed.

(* nonempty_equiv_of_basis.  v^k = 1 gives (v^c)^k = 1. *)

Lemma pow_iter_of_root (x : R) (c k : nat) :
  x ^ k = 1 -> (x ^ c) ^ k = 1.
Proof.
  intros H.
  rewrite <- (rpow_mul_exp x c k).
  rewrite (Nat.mul_comm c k).
  rewrite (rpow_mul_exp x k c).
  rewrite H. apply rpow_one_base.
Qed.

(* norm_unit, norm_valF, and the coset nlinarith.
   Two nonnegative factors at most 1 whose product is 1 are each 1. *)

Lemma unit_norm_pair (a b : R) :
  0 <= a -> 0 <= b -> a * b = 1 -> a <= 1 -> b <= 1 -> a = 1 /\ b = 1.
Proof.
  intros Ha Hb Hab HleA HleB.
  assert (Hge : 1 <= a).
  { apply Rle_trans with (a * b).
    - rewrite Hab. apply Rle_refl.
    - enough (E : a * b <= a * 1).
      { rewrite Rmult_1_r in E. exact E. }
      apply Rmult_le_compat_l; assumption. }
  assert (Ha1 : a = 1) by lra.
  split.
  - exact Ha1.
  - rewrite Ha1 in Hab. rewrite Rmult_1_l in Hab. exact Hab.
Qed.

(* isProper_of_unit_in_cosets.  A real of absolute value 1 is not zero. *)

Lemma abs_one_ne_zero (x : R) : Rabs x = 1 -> x <> 0.
Proof.
  intros H Hx. subst x. rewrite Rabs_R0 in H. lra.
Qed.

(* exists_hom, the cancel after mul_right_cancel₀. *)

Lemma div_mul_cancel_r (a u : R) : u <> 0 -> (a / u) * u = a.
Proof.
  intros Hu. unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l.
  - apply Rmult_1_r.
  - exact Hu.
Qed.

(* charSum_inv, after the left-multiplication bijection has identified
   the shifted sum with S.  The bijection and the card rewrite are not
   this step. *)

Lemma char_shift_zero (phi S : R) :
  phi * S = S -> phi <> 1 -> S = 0.
Proof.
  intros HS Hne.
  assert (H0 : (phi - 1) * S = 0) by lra.
  destruct (Rmult_integral _ _ H0) as [Hphi | HS0].
  - exfalso. apply Hne. apply Rminus_diag_uniq. exact Hphi.
  - exact HS0.
Qed.

Fixpoint rsum (l : list R) : R :=
  match l with
  | nil => 0
  | x :: xs => x + rsum xs
  end.

Lemma rsum_ones (n : nat) : rsum (repeat 1 n) = INR n.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - assert (E : rsum (repeat 1 (S n)) = 1 + rsum (repeat 1 n)) by reflexivity.
    rewrite E. rewrite IH. rewrite S_INR. lra.
Qed.

(* dvd_pow_sub, multiplicative witness:
   (a*b)^e - a*b = b^e * (a^e - a) + a * (b^e - b). *)

Lemma mul_pow_diff (a b : R) (e : nat) :
  (a * b) ^ e - a * b = b ^ e * (a ^ e - a) + a * (b ^ e - b).
Proof.
  rewrite rpow_mul_base. induction e as [| e IH]; cbn.
  - ring.
  - ring.
Qed.

(* Additive witness, given the Freshman's-dream expansion as a hypothesis.
   exists_add_pow_prime_pow_eq is that hypothesis. *)

Lemma add_pow_diff (x y d r s t : R) (e : nat) :
  (x + y) ^ e = x ^ e + y ^ e + d * (x * y * r) ->
  x ^ e - x = d * s ->
  y ^ e - y = d * t ->
  (x + y) ^ e - (x + y) = d * (s + t + x * y * r).
Proof.
  intros H Hx Hy. rewrite H.
  replace (x ^ e + y ^ e + d * (x * y * r) - (x + y))
    with ((x ^ e - x) + (y ^ e - y) + d * (x * y * r)) by ring.
  rewrite Hx. rewrite Hy. ring.
Qed.

Lemma sub_sub_restore (x y : R) : x - (x - y) = y.
Proof. ring. Qed.

Lemma pow_from_sq (y d k : R) (e : nat) :
  (2 <= e)%nat ->
  y ^ 2 = d * k ->
  y ^ e = d * (k * y ^ (e - 2)).
Proof.
  intros He Hk.
  assert (E : (e = 2 + (e - 2))%nat) by lia.
  rewrite E at 1. rewrite rpow_add_nat. rewrite Hk.
  rewrite <- Rmult_assoc. reflexivity.
Qed.

Lemma sq_pow_sub_factor (y d s t : R) (e : nat) :
  (2 <= e)%nat ->
  y ^ 2 = d * t ->
  y ^ e - y = d * s ->
  y = d * (t * y ^ (e - 2) - s).
Proof.
  intros He Ht Hs.
  rewrite <- (sub_sub_restore (y ^ e) y) at 1.
  rewrite Hs.
  replace (y ^ e) with (d * (t * y ^ (e - 2)))
    by (symmetry; apply pow_from_sq; assumption).
  rewrite <- Rmult_minus_distr_l. reflexivity.
Qed.

(* eq_zero_of_sq, the cancel after A is rewritten as d * A'.
   Well-founded divisibility in Z[zeta] is not this identity. *)

Lemma sq_descent_cancel (d A B A' : R) :
  d <> 0 ->
  A = d * A' ->
  A * A = - d * (B * B) ->
  B * B = d * (- (A' * A')).
Proof.
  intros Hd HA HAB.
  apply (Rmult_eq_reg_l d).
  - rewrite HA in HAB. lra.
  - exact Hd.
Qed.

(* ------------------------------------------------------------------------ *)
(* exists_linear.  A polynomial in zeta and rho, reduced by rho^2 = -d.    *)
(* Constructors match MvPolynomial.induction_on: constant, add, mul by var. *)
(* ------------------------------------------------------------------------ *)

Inductive Quad : Type :=
| Qconst : Z -> Quad
| Qadd : Quad -> Quad -> Quad
| Qvar : bool -> Quad -> Quad.

Fixpoint zadd (xs ys : list Z) : list Z :=
  match xs, ys with
  | nil, _ => ys
  | x :: xs, nil => x :: xs
  | x :: xs, y :: ys => (x + y)%Z :: zadd xs ys
  end.

Fixpoint zscale (c : Z) (xs : list Z) : list Z :=
  match xs with
  | nil => nil
  | x :: xs => (c * x)%Z :: zscale c xs
  end.

Definition zmulX (xs : list Z) : list Z := 0%Z :: xs.

Fixpoint aeval (xs : list Z) (zeta : R) : R :=
  match xs with
  | nil => 0
  | c :: cs => IZR c + zeta * aeval cs zeta
  end.

Fixpoint qeval (p : Quad) (zeta rho : R) : R :=
  match p with
  | Qconst c => IZR c
  | Qadd p q => qeval p zeta rho + qeval q zeta rho
  | Qvar false p => zeta * qeval p zeta rho
  | Qvar true p => rho * qeval p zeta rho
  end.

Fixpoint qsplit (d : Z) (p : Quad) : list Z * list Z :=
  match p with
  | Qconst c => (c :: nil, nil)
  | Qadd p q =>
      (zadd (fst (qsplit d p)) (fst (qsplit d q)),
       zadd (snd (qsplit d p)) (snd (qsplit d q)))
  | Qvar false p =>
      (zmulX (fst (qsplit d p)), zmulX (snd (qsplit d p)))
  | Qvar true p =>
      (zscale (Z.opp d) (snd (qsplit d p)), fst (qsplit d p))
  end.

Lemma aeval_zadd (xs ys : list Z) (zeta : R) :
  aeval (zadd xs ys) zeta = aeval xs zeta + aeval ys zeta.
Proof.
  revert ys. induction xs as [| x xs IH]; intros ys.
  - cbn. ring.
  - destruct ys as [| y ys].
    + cbn. ring.
    + cbn. rewrite IH. rewrite plus_IZR. ring.
Qed.

Lemma aeval_scale (c : Z) (xs : list Z) (zeta : R) :
  aeval (zscale c xs) zeta = IZR c * aeval xs zeta.
Proof.
  induction xs as [| x xs IH].
  - cbn. ring.
  - cbn. rewrite IH. rewrite mult_IZR. ring.
Qed.

Lemma quad_reduce_eval (d : Z) (p : Quad) (zeta rho : R) :
  rho * rho = IZR (Z.opp d) ->
  qeval p zeta rho =
    aeval (fst (qsplit d p)) zeta + rho * aeval (snd (qsplit d p)) zeta.
Proof.
  intros Hrho. induction p as [c | p IHp q IHq | i p IH].
  - cbn. ring.
  - cbn. rewrite IHp. rewrite IHq.
    rewrite !aeval_zadd. ring.
  - destruct i.
    + cbn. rewrite IH.
      rewrite Rmult_plus_distr_l.
      rewrite <- (Rmult_assoc rho rho (aeval (snd (qsplit d p)) zeta)).
      rewrite Hrho. rewrite aeval_scale. ring.
    + cbn. rewrite IH. ring.
Qed.

Lemma quad_reduce_exists (d : Z) (p : Quad) :
  exists a b : list Z,
    forall zeta rho : R,
      rho * rho = IZR (Z.opp d) ->
      qeval p zeta rho = aeval a zeta + rho * aeval b zeta.
Proof.
  exists (fst (qsplit d p)), (snd (qsplit d p)).
  intros zeta rho Hrho. apply quad_reduce_eval. exact Hrho.
Qed.

(* ------------------------------------------------------------------------ *)
(* HomTransport.Rel.pow.  The graph of a homomorphism is closed under       *)
(* iteration, from the unit and the product step.                           *)
(* ------------------------------------------------------------------------ *)

Section RelPow.
Variable G : Type.
Variable op : G -> G -> G.
Variable one : G.
Variable rel : G -> G -> Prop.
Hypothesis rel_one_pt : rel one one.
Hypothesis rel_mul_pt :
  forall g h g' h', rel g g' -> rel h h' -> rel (op g h) (op g' h').

Fixpoint rel_iter (g : G) (n : nat) : G :=
  match n with
  | 0 => one
  | S n => op (rel_iter g n) g
  end.

Lemma rel_pow_iter (g g' : G) (n : nat) :
  rel g g' -> rel (rel_iter g n) (rel_iter g' n).
Proof.
  intros H. induction n as [| n IH].
  - exact rel_one_pt.
  - cbn. apply rel_mul_pt; assumption.
Qed.
End RelPow.
