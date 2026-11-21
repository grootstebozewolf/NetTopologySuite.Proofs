(* TowerOrderLawQED.v -- Rocq rebuild of the 2-power tower's "order law" used by
   the claimed RH/GRH Lean development (CocoSgt/riemann-hypothesis-lean @
   7cbf7a0), re-derived from the Lean TYPE without running Lean.

   Lean (Formalism/BehrendSets/StatementE.lean):
     def OrdLargeJ : Prop := ∀ (s J l : ℕ) (hl : Nat.Coprime l (2 ^ (s + 2))), 2 ≤ l →
       orderOf (frob s l hl) ≤ J → 2 ^ (s + 2) ≤ J * (l + 1)
   with frob s l the class of l in OrdGrp s := (ZMod 2^(s+2))ˣ ⧸ ⟨-1⟩.

   Translation (definitional, not re-proved here): in that quotient,
   frob^k = 1  <->  l^k ≡ ±1 (mod 2^(s+2)); and orderOf ≤ J with J ≥ 1 means
   some 1 ≤ k ≤ J has frob^k = 1.  Coprime to 2^(s+2) means l odd.

   Proved here, with NO hypotheses and NO axioms:
     ord_large_J : l odd, 2 ≤ l, 1 ≤ k ≤ J,
                   2^N | l^k - 1  \/  2^N | l^k + 1   ->   2^N ≤ J*(l+1)
   for every N (Lean's case is N = s+2).  The proof is a lifting-the-exponent
   style strong induction on k:
     2^n | l^k - 1  ->  2^n ≤ k*(l+1)        and        2^n | l^k + 1  ->  2^n ≤ l+1.

   Meaning for the audit: this is the "every small prime has a long Frobenius
   orbit in the tower" fact (root-only ticket, slice 2): with 2^s ≈ x^(2+8ε),
   every prime l ≤ x has orbit length ≳ x^(1+8ε).

   Evidence for docs/attacks/2026-11-20-alpoge-grh-lean-audit.md (slice 9) and
   docs/attacks/2026-11-20-root-only-multiplicity.md.  NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import ZArith Znumtheory Lia Wf_nat.
Local Open Scope Z_scope.

(* ---------- geometric sums and parity ---------- *)

Fixpoint G (x : Z) (k : nat) : Z :=
  match k with
  | O => 0
  | S k' => G x k' + x ^ Z.of_nat k'
  end.

Lemma geom : forall x k, (x - 1) * G x k = x ^ Z.of_nat k - 1.
Proof.
  intros x k. induction k as [|k IH]; cbn [G]; [cbn; ring|].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. rewrite Z.mul_add_distr_l, IH. ring.
Qed.

Lemma odd_pow : forall x n, Z.odd x = true -> Z.odd (x ^ Z.of_nat n) = true.
Proof.
  intros x n Hx. induction n as [|n IH]; [reflexivity|].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. rewrite Z.odd_mul, Hx, IH. reflexivity.
Qed.

Lemma G_odd : forall x k, Z.odd x = true -> Z.odd (G x k) = Nat.odd k.
Proof.
  intros x k Hx. induction k as [|k IH]; [reflexivity|].
  cbn [G]. rewrite Z.odd_add, IH, odd_pow by exact Hx.
  rewrite Nat.odd_succ, <- Nat.negb_odd. destruct (Nat.odd k); reflexivity.
Qed.

(* ---------- 2-adic helper lemmas ---------- *)

Lemma rel_prime_2_odd : forall b, Z.odd b = true -> rel_prime 2 b.
Proof.
  intros b Hb. apply prime_rel_prime; [exact prime_2|].
  intros [c Hc]. subst b. rewrite Z.odd_mul, Bool.andb_false_r in Hb. discriminate Hb.
Qed.

Lemma rel_prime_pow2_odd : forall b n, Z.odd b = true -> rel_prime (2 ^ Z.of_nat n) b.
Proof.
  intros b n Hb. induction n as [|n IH]; [apply rel_prime_1|].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  apply rel_prime_sym. apply rel_prime_mult; apply rel_prime_sym;
    [apply rel_prime_2_odd; exact Hb | exact IH].
Qed.

(* 2^n | a*b with b odd  ->  2^n | a *)
Lemma pow2_gauss : forall n a b, Z.odd b = true ->
  (2 ^ Z.of_nat n | a * b) -> (2 ^ Z.of_nat n | a).
Proof.
  intros n a b Hb H. apply Gauss with b; [now rewrite Z.mul_comm | now apply rel_prime_pow2_odd].
Qed.

Lemma pow2_succ : forall n, 2 ^ Z.of_nat (S n) = 2 * 2 ^ Z.of_nat n.
Proof. intros n. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. reflexivity. Qed.

Lemma pow2_pos : forall n, 0 < 2 ^ Z.of_nat n.
Proof. intros n. apply Z.pow_pos_nonneg; lia. Qed.

(* y odd: y^2 + 1 ≡ 2 (mod 8), so 2^n | y^2+1 forces 2^n ≤ 2. *)
Lemma sq_plus_one : forall y n, Z.odd y = true -> (2 ^ Z.of_nat n | y * y + 1) ->
  2 ^ Z.of_nat n <= 2.
Proof.
  intros y n Hy H.
  destruct n as [|[|n]]; [cbn; lia | cbn; lia|].
  exfalso. destruct (proj1 (Z.odd_spec y) Hy) as [t Ht]. subst y.
  rewrite !pow2_succ in H.
  assert (H4 : (4 | (2 * t + 1) * (2 * t + 1) + 1)).
  { apply Z.divide_trans with (2 * (2 * 2 ^ Z.of_nat n)); [|exact H].
    exists (2 ^ Z.of_nat n). ring. }
  assert (H4' : (4 | 4 * (t * t + t))) by (exists (t * t + t); ring).
  assert (E : (2 * t + 1) * (2 * t + 1) + 1 = 4 * (t * t + t) + 2) by ring.
  rewrite E in H4. apply Z.divide_add_cancel_r in H4; [|exact H4'].
  apply Z.divide_pos_le in H4; lia.
Qed.

(* ---------- the order law ---------- *)

Section OrderLaw.
Variable l : Z.
Hypothesis l_odd : Z.odd l = true.
Hypothesis l_ge2 : 2 <= l.

Lemma l_ge3 : 3 <= l.
Proof.
  destruct (proj1 (Z.odd_spec l) l_odd) as [t Ht]. lia.
Qed.

Lemma lpow_ge : forall m, (1 <= m)%nat -> l <= l ^ Z.of_nat m.
Proof.
  intros m Hm. induction m as [|m IH]; [lia|].
  destruct m as [|m]; [cbn; lia|].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  specialize (IH ltac:(lia)). pose proof l_ge3. nia.
Qed.

Lemma lpow_odd : forall m, Z.odd (l ^ Z.of_nat m) = true.
Proof. intros m. now apply odd_pow. Qed.

Theorem lte : forall k, (1 <= k)%nat -> forall n,
  ((2 ^ Z.of_nat n | l ^ Z.of_nat k - 1) -> 2 ^ Z.of_nat n <= Z.of_nat k * (l + 1)) /\
  ((2 ^ Z.of_nat n | l ^ Z.of_nat k + 1) -> 2 ^ Z.of_nat n <= l + 1).
Proof.
  pose proof l_ge3 as L3.
  intros k. induction k as [k IH] using (well_founded_induction lt_wf).
  intros Hk n.
  destruct (Nat.Even_or_Odd k) as [[m Hm]|[m Hm]].
  - (* k = 2m, m >= 1 *)
    assert (Hm1 : (1 <= m)%nat) by lia.
    set (y := l ^ Z.of_nat m).
    assert (Hy : l ^ Z.of_nat k = y * y).
    { subst k. unfold y. rewrite Nat2Z.inj_mul. change (Z.of_nat 2) with 2.
      rewrite Z.mul_comm, Z.pow_mul_r by lia. apply Z.pow_2_r. }
    assert (Hyo : Z.odd y = true) by apply lpow_odd.
    assert (Hyl : l <= y) by (apply lpow_ge; exact Hm1).
    pose proof (IH m ltac:(lia) Hm1) as IHmn.
    rewrite Hy. split.
    + (* 2^n | y^2 - 1 = (y-1)(y+1) *)
      intros H. destruct n as [|n]; [cbn; lia|].
      rewrite pow2_succ in *.
      destruct (proj1 (Z.odd_spec y) Hyo) as [t Ht].
      assert (Ek : Z.of_nat k = 2 * Z.of_nat m) by lia.
      destruct (Z.Even_or_Odd t) as [[u Hu]|[u Hu]].
      * (* t even: y+1 = 2(t+1), t+1 odd -> 2^n | y-1 *)
        assert (Hf : y * y - 1 = 2 * ((y - 1) * (t + 1))) by (rewrite Ht; ring).
        rewrite Hf in H. apply Z.mul_divide_cancel_l in H; [|lia].
        apply pow2_gauss in H; [|rewrite Hu, Z.odd_add, Z.odd_mul; reflexivity].
        pose proof (proj1 (IHmn n) H) as IHm. rewrite Ek. lia.
      * (* t odd: y-1 = 2t, t odd -> 2^n | y+1 *)
        assert (Hf : y * y - 1 = 2 * ((y + 1) * t)) by (rewrite Ht; ring).
        rewrite Hf in H. apply Z.mul_divide_cancel_l in H; [|lia].
        apply pow2_gauss in H; [|rewrite Hu, Z.odd_add, Z.odd_mul; reflexivity].
        pose proof (proj2 (IHmn n) H) as IHp. rewrite Ek. nia.
    + (* 2^n | y^2 + 1 -> 2^n <= 2 <= l+1 *)
      intros H. pose proof (sq_plus_one y n Hyo H). lia.
  - (* k = 2m+1 *)
    assert (Gl : Z.odd (G l k) = true)
      by (rewrite G_odd by exact l_odd; apply Nat.odd_spec; now exists m).
    assert (Gml : Z.odd (G (- l) k) = true).
    { rewrite G_odd; [apply Nat.odd_spec; now exists m|].
      rewrite Z.odd_opp. exact l_odd. }
    split.
    + intros H. rewrite <- geom in H. apply pow2_gauss in H; [|exact Gl].
      apply Z.divide_pos_le in H; lia.
    + intros H.
      assert (Ep : l ^ Z.of_nat k + 1 = (l + 1) * G (- l) k).
      { assert (Hg := geom (- l) k).
        assert (Hodd : Z.Odd (Z.of_nat k)) by (exists (Z.of_nat m); lia).
        rewrite Z.pow_opp_odd in Hg by exact Hodd. lia. }
      rewrite Ep in H. apply pow2_gauss in H; [|exact Gml].
      apply Z.divide_pos_le in H; lia.
Qed.

(* Integer form of the Lean OrdLargeJ, for every exponent N (Lean: N = s+2). *)
Theorem ord_large_J : forall (N : nat) (J k : nat), (1 <= k)%nat -> (k <= J)%nat ->
  (2 ^ Z.of_nat N | l ^ Z.of_nat k - 1) \/ (2 ^ Z.of_nat N | l ^ Z.of_nat k + 1) ->
  2 ^ Z.of_nat N <= Z.of_nat J * (l + 1).
Proof.
  intros N J k Hk HkJ [H|H]; destruct (lte k Hk N) as [Hm Hp].
  - specialize (Hm H). nia.
  - specialize (Hp H). nia.
Qed.

End OrderLaw.

Print Assumptions ord_large_J.
