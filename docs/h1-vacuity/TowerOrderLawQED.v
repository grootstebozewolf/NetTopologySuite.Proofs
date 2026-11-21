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

(* ============================================================================
   OrdDvd (Formalism/BehrendSets/StatementE.lean):
     orderOf (frob s l hl) ∣ 2^j  <->  l ≡ ±1 [ZMOD 2^(s+2-j)]
   Integer form (frob^(2^j) = 1 <-> l^(2^j) ≡ ±1 mod 2^(s+2); N = s+2):
     ord_dvd : l odd, 1 <= j:
       (2^N | l^(2^j) - 1 \/ 2^N | l^(2^j) + 1) <-> (2^(N-j) | l - 1 \/ 2^(N-j) | l + 1)
   with truncated subtraction N - j, exactly as in Lean.
   ========================================================================== *)

Lemma divide_mul_pow2_r : forall a X b, 0 <= b ->
  (2 ^ a * 2 ^ b | X * 2 ^ b) <-> (2 ^ a | X).
Proof.
  intros a X b Hb. rewrite Z.mul_divide_cancel_r; [reflexivity|].
  apply Z.pow_nonzero; lia.
Qed.

Section OrdDvd.
Variable l : Z.
Hypothesis l_odd : Z.odd l = true.

Definition p2 (j : nat) : Z := 2 ^ Z.of_nat j.

Lemma l_p2_odd : forall j, Z.odd (l ^ p2 j) = true.
Proof.
  intros j. unfold p2. replace (2 ^ Z.of_nat j) with (Z.of_nat (Nat.pow 2 j)).
  - apply odd_pow; exact l_odd.
  - rewrite Nat2Z.inj_pow. reflexivity.
Qed.

Lemma l_p2_succ : forall j, l ^ p2 (S j) = l ^ p2 j * l ^ p2 j.
Proof.
  intros j. unfold p2. rewrite pow2_succ, Z.mul_comm, Z.pow_mul_r.
  - apply Z.pow_2_r.
  - apply Z.lt_le_incl, pow2_pos.
  - lia.
Qed.

(* y odd: y + 1 = 2 * odd  whenever  y ≡ 1 (mod 4); and l^(2^j) ≡ 1 (mod 4) for j >= 1 *)
Lemma sq_odd_mod4 : forall y, Z.odd y = true -> exists c, y * y + 1 = 2 * c /\ Z.odd c = true.
Proof.
  intros y Hy. destruct (proj1 (Z.odd_spec y) Hy) as [t Ht]. subst y.
  exists (2 * (t * t + t) + 1). split; [ring|].
  rewrite Z.odd_add, Z.odd_mul. reflexivity.
Qed.

(* exact valuation:  2^n | l^(2^(j+1)) - 1  <->  2^n | (l^2 - 1) * 2^j *)
Lemma val_exact : forall j n,
  (2 ^ Z.of_nat n | l ^ p2 (S j) - 1) <-> (2 ^ Z.of_nat n | (l * l - 1) * 2 ^ Z.of_nat j).
Proof.
  induction j as [|j IH]; intros n.
  - assert (E1 : l ^ p2 1 = l * l) by (unfold p2; cbn; ring).
    rewrite E1. change (2 ^ Z.of_nat 0) with 1. rewrite Z.mul_1_r. reflexivity.
  - (* l^(2^(j+2)) - 1 = (l^(2^(j+1)) - 1) * (l^(2^(j+1)) + 1),  second = 2 * odd *)
    set (y := l ^ p2 (S j)).
    assert (Hy : Z.odd y = true) by apply l_p2_odd.
    assert (Hyy : l ^ p2 (S (S j)) = y * y) by apply l_p2_succ.
    (* y = z*z with z odd, so y + 1 = 2 * odd *)
    assert (Hz : exists c, y + 1 = 2 * c /\ Z.odd c = true).
    { unfold y. rewrite l_p2_succ. apply sq_odd_mod4, l_p2_odd. }
    destruct Hz as [c [Hc Hco]].
    rewrite Hyy.
    assert (E : y * y - 1 = ((y - 1) * 2) * c) by (nia).
    rewrite E. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    split.
    + intros H. apply pow2_gauss in H; [|exact Hco].
      destruct n as [|n]; [cbn; apply Z.divide_1_l|].
      rewrite pow2_succ in H. rewrite pow2_succ.
      rewrite (Z.mul_comm 2 (2 ^ Z.of_nat n)) in H.
      apply Z.mul_divide_cancel_r in H; [|lia].
      apply (proj1 (IH n)) in H.
      replace ((l * l - 1) * (2 * 2 ^ Z.of_nat j)) with (2 * ((l * l - 1) * 2 ^ Z.of_nat j)) by ring.
      apply Z.mul_divide_mono_l. exact H.
    + intros H. apply Z.divide_mul_l.
      destruct n as [|n]; [cbn; apply Z.divide_1_l|].
      rewrite pow2_succ in *. rewrite (Z.mul_comm 2 (2 ^ Z.of_nat n)).
      apply Z.mul_divide_mono_r. apply (proj2 (IH n)).
      replace ((l * l - 1) * (2 * 2 ^ Z.of_nat j)) with (2 * ((l * l - 1) * 2 ^ Z.of_nat j)) in H by ring.
      apply Z.mul_divide_cancel_l in H; [exact H | lia].
Qed.

(* 2^(m+1) | l^2 - 1  <->  2^m | l - 1  \/  2^m | l + 1 *)
Lemma sq_minus_one : forall m,
  (2 ^ Z.of_nat (S m) | l * l - 1) <-> (2 ^ Z.of_nat m | l - 1) \/ (2 ^ Z.of_nat m | l + 1).
Proof.
  intros m. destruct (proj1 (Z.odd_spec l) l_odd) as [t Ht].
  assert (Hf : l * l - 1 = 2 * (2 * t * (t + 1))) by (rewrite Ht; ring).
  assert (Hm1 : l - 1 = 2 * t) by lia. assert (Hp1 : l + 1 = 2 * (t + 1)) by lia.
  rewrite Hf, pow2_succ, Hm1, Hp1.
  rewrite Z.mul_divide_cancel_l by lia.
  destruct (Z.Even_or_Odd t) as [[u Hu]|[u Hu]].
  - (* t even, t+1 odd: everything sits in l - 1 = 2t *)
    assert (Ho : Z.odd (t + 1) = true) by (rewrite Hu, Z.odd_add, Z.odd_mul; reflexivity).
    split.
    + intros H. left. apply pow2_gauss in H; [exact H | exact Ho].
    + intros [H|H].
      * now apply Z.divide_mul_l.
      * (* 2^m | 2(t+1) with t+1 odd forces m <= 1, then 2^m | 2t *)
        destruct m as [|[|m]];
          [change (2 ^ Z.of_nat 0) with 1; apply Z.divide_1_l
          | change (2 ^ Z.of_nat 1) with 2; exists (t * (t + 1)); ring |].
        exfalso. rewrite !pow2_succ in H.
        apply Z.mul_divide_cancel_l in H; [|lia].
        destruct H as [q Hq]. rewrite Hu in Hq.
        assert (Z.odd (q * (2 * 2 ^ Z.of_nat m)) = false)
          by (rewrite Z.odd_mul, Z.odd_mul; cbn; rewrite Bool.andb_false_r; reflexivity).
        rewrite <- Hq, Z.odd_add, Z.odd_mul in H. discriminate H.
  - (* t odd: everything sits in l + 1 = 2(t+1) *)
    assert (Ho : Z.odd t = true) by (rewrite Hu, Z.odd_add, Z.odd_mul; reflexivity).
    split.
    + intros H. right. replace (2 * t * (t + 1)) with ((2 * (t + 1)) * t) in H by ring.
      apply pow2_gauss in H; [exact H | exact Ho].
    + intros [H|H].
      * destruct m as [|[|m]];
          [change (2 ^ Z.of_nat 0) with 1; apply Z.divide_1_l
          | change (2 ^ Z.of_nat 1) with 2; exists (t * (t + 1)); ring |].
        exfalso. rewrite !pow2_succ in H.
        apply Z.mul_divide_cancel_l in H; [|lia].
        destruct H as [q Hq].
        assert (Z.odd (q * (2 * 2 ^ Z.of_nat m)) = false)
          by (rewrite Z.odd_mul, Z.odd_mul; cbn; rewrite Bool.andb_false_r; reflexivity).
        rewrite <- Hq, Ho in H. discriminate H.
      * replace (2 * t * (t + 1)) with (t * (2 * (t + 1))) by ring. now apply Z.divide_mul_r.
Qed.

Theorem ord_dvd : forall (N j : nat), (1 <= j)%nat ->
  ((2 ^ Z.of_nat N | l ^ p2 j - 1) \/ (2 ^ Z.of_nat N | l ^ p2 j + 1)) <->
  ((2 ^ Z.of_nat (N - j) | l - 1) \/ (2 ^ Z.of_nat (N - j) | l + 1)).
Proof.
  intros N j Hj. destruct j as [|j]; [lia|].
  (* the "+1" disjunct on the left only occurs for N <= 1 *)
  assert (Hplus : (2 ^ Z.of_nat N | l ^ p2 (S j) + 1) -> (N <= 1)%nat).
  { intros H. rewrite l_p2_succ in H. pose proof (sq_plus_one _ N (l_p2_odd j) H) as B.
    destruct N as [|[|N]]; [lia|lia|]. exfalso. rewrite !pow2_succ in B.
    pose proof (pow2_pos N). lia. }
  destruct (Nat.le_gt_cases N (S j)) as [HNj|HNj].
  - (* N <= j+1: the right side is trivially true (2^0 = 1); so is the left *)
    replace (N - S j)%nat with 0%nat by lia. cbn. split; [intros _; left; apply Z.divide_1_l|].
    intros _. left. apply (proj2 (val_exact j N)).
    destruct (proj1 (Z.odd_spec l) l_odd) as [t Ht].
    (* (l^2 - 1) * 2^j = 8*(t(t+1)/2)*2^j is divisible by 2^(j+3) >= 2^N *)
    apply Z.divide_trans with (2 ^ Z.of_nat (S j)).
    + exists (2 ^ (Z.of_nat (S j) - Z.of_nat N)).
      rewrite <- Z.pow_add_r by lia. f_equal. lia.
    + rewrite pow2_succ. replace (l * l - 1) with (2 * (2 * t * (t + 1))) by (rewrite Ht; ring).
      exists (2 * t * (t + 1)). ring.
  - (* N = (N - (j+1)) + (j+1),  j+1 < N *)
    destruct (N - S j)%nat as [|m] eqn:Em; [lia|].
    assert (HN : Z.of_nat N = Z.of_nat (S m) + Z.of_nat j + 1) by lia.
    split.
    + intros [H|H]; [|apply Hplus in H; lia].
      apply (proj1 (val_exact j N)) in H. rewrite HN in H.
      rewrite Z.pow_add_r, Z.pow_add_r in H by lia.
      apply (proj1 (sq_minus_one (S m))).
      rewrite pow2_succ.
      replace (2 ^ Z.of_nat (S m) * 2 ^ Z.of_nat j * 2 ^ 1) with ((2 * 2 ^ Z.of_nat (S m)) * 2 ^ Z.of_nat j) in H
        by (rewrite Z.pow_1_r; ring).
      apply Z.mul_divide_cancel_r in H; [exact H | apply Z.pow_nonzero; lia].
    + intros H. left. apply (proj2 (val_exact j N)). rewrite HN.
      rewrite Z.pow_add_r, Z.pow_add_r by lia.
      apply (proj2 (sq_minus_one (S m))) in H. rewrite pow2_succ in H.
      replace (2 ^ Z.of_nat (S m) * 2 ^ Z.of_nat j * 2 ^ 1) with ((2 * 2 ^ Z.of_nat (S m)) * 2 ^ Z.of_nat j)
        by (rewrite Z.pow_1_r; ring).
      apply Z.mul_divide_cancel_r; [apply Z.pow_nonzero; lia | exact H].
Qed.

End OrdDvd.

Print Assumptions ord_dvd.

(* ============================================================================
   OrdD (Formalism/BehrendSets/StatementE.lean):
     d % 16 = 7  ->  orderOf (frob s d hd) = 2^(s-1)
   Integer form, for s >= 3 (N = s+2): with d ≡ 7 (mod 16),
     d^(2^(s-1)) ≡ ±1 (mod 2^(s+2))   and   d^(2^(s-2)) ≢ ±1 (mod 2^(s+2)).
   Since the order of frob is a power of 2 (OrdGrp s is cyclic of order 2^s),
   "divides 2^(s-1) but not 2^(s-2)" is "equals 2^(s-1)" (group translation,
   not re-proved).  Reason: v2(d+1) = 3, v2(d-1) = 1.
   ========================================================================== *)

Theorem ord_d : forall (d : Z) (s : nat), d mod 16 = 7 -> (3 <= s)%nat ->
  ((2 ^ Z.of_nat (s + 2) | d ^ p2 (s - 1) - 1) \/ (2 ^ Z.of_nat (s + 2) | d ^ p2 (s - 1) + 1)) /\
  ~ ((2 ^ Z.of_nat (s + 2) | d ^ p2 (s - 2) - 1) \/ (2 ^ Z.of_nat (s + 2) | d ^ p2 (s - 2) + 1)).
Proof.
  intros d s Hd Hs.
  assert (Hq : d = 16 * (d / 16) + 7) by (pose proof (Z.div_mod d 16); lia).
  set (q := d / 16) in Hq.
  assert (Hodd : Z.odd d = true) by (rewrite Hq, Z.odd_add, Z.odd_mul; reflexivity).
  split.
  - apply (proj2 (ord_dvd d Hodd (s + 2) (s - 1) ltac:(lia))).
    replace (s + 2 - (s - 1))%nat with 3%nat by lia.
    right. change (2 ^ Z.of_nat 3) with 8. exists (2 * q + 1). lia.
  - intros H. apply (proj1 (ord_dvd d Hodd (s + 2) (s - 2) ltac:(lia))) in H.
    replace (s + 2 - (s - 2))%nat with 4%nat in H by lia.
    change (2 ^ Z.of_nat 4) with 16 in H.
    destruct H as [[c Hc]|[c Hc]]; lia.
Qed.

Print Assumptions ord_d.
