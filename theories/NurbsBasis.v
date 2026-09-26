(* ============================================================================
   NetTopologySuite.Proofs.NurbsBasis
   ----------------------------------------------------------------------------
   Cox–de Boor basis, clean-room from Piegl–Tiller. No QGIS source.
   Degree 0 is the half-open span, with the A2.1 right end u = U[n]
   assigned to i = n−1. Higher degree is the two-term recurrence.
   A zero denominator contributes 0, which is the skip.

   Proved here: degree-0 values are 0 or 1, the right-end partition
   Σ Nᵢ,₀(U[n]) = 1, and two distinct half-open spans cannot both
   contain u when the knots are non-decreasing.

   Not proved here: Σ Nᵢ,ₚ = 1 for p > 0, non-negativity for p > 0,
   and A4.1 = Σ Nᵢ,ₚ wᵢ Pᵢ / Σ Nᵢ,ₚ wᵢ. Those need the recurrence
   telescope. No Admitted stands in for them.

   No Admitted. No Axiom. No Parameter.
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia PeanoNat.
From Stdlib Require Import List.
From NTS.Proofs Require Import NurbsDeBoor.
Import ListNotations.
Local Open Scope R_scope.

Fixpoint N (U : list R) (n i p : nat) (u : R) : R :=
  match p with
  | O =>
      if Req_EM_T u (nthR U n) then
        if Nat.eq_dec i (n - 1) then 1 else 0
      else
        match total_order_T (nthR U i) u with
        | inleft (left _) =>
            match total_order_T u (nthR U (S i)) with
            | inleft (left _) => 1
            | _ => 0
            end
        | inleft (right _) =>
            match total_order_T u (nthR U (S i)) with
            | inleft (left _) => 1
            | _ => 0
            end
        | inright _ => 0
        end
  | S p' =>
      let d1 := nthR U (i + S p') - nthR U i in
      let d2 := nthR U (i + S (S p')) - nthR U (S i) in
      let c1 := if Req_EM_T d1 0 then 0 else (u - nthR U i) / d1 in
      let c2 := if Req_EM_T d2 0 then 0 else
                  (nthR U (i + S (S p')) - u) / d2 in
      c1 * N U n i p' u + c2 * N U n (S i) p' u
  end.

Lemma basis0_is_indicator : forall U n i u,
  N U n i O u = 0 \/ N U n i O u = 1.
Proof.
  intros U n i u. simpl.
  destruct (Req_EM_T u (nthR U n)) as [_|Hne].
  - destruct (Nat.eq_dec i (n - 1)) as [_|_]; [right|left]; reflexivity.
  - destruct (total_order_T (nthR U i) u) as [[Hlt|Heq]|Hgt].
    + destruct (total_order_T u (nthR U (S i))) as [[Hlt2|Heq2]|Hgt2];
        [right|left|left]; reflexivity.
    + destruct (total_order_T u (nthR U (S i))) as [[Hlt2|Heq2]|Hgt2];
        [right|left|left]; reflexivity.
    + left. reflexivity.
Qed.

Lemma basis0_nonneg : forall U n i u, 0 <= N U n i O u.
Proof.
  intros. destruct (basis0_is_indicator U n i u) as [-> | ->]; lra.
Qed.

Lemma half_open_unique : forall U i j u,
  knots_nondecreasing U ->
  S i < length U ->
  S j < length U ->
  nthR U i <= u ->
  u < nthR U (S i) ->
  nthR U j <= u ->
  u < nthR U (S j) ->
  i = j.
Proof.
  intros U i j u Hmono Hi Hj Hli Hui Hlj Huj.
  destruct (Nat.lt_trichotomy i j) as [Hlt|[->|Hgt]].
  - assert (nthR U (S i) <= nthR U j).
    { apply nthR_le_idx; try assumption; lia. }
    lra.
  - reflexivity.
  - assert (nthR U (S j) <= nthR U i).
    { apply nthR_le_idx; try assumption; lia. }
    lra.
Qed.

Definition sumR (l : list R) : R := fold_right Rplus 0 l.

Lemma sum_zero_from : forall (f : nat -> R) start n,
  (forall i, start <= i < start + n -> f i = 0) ->
  sumR (map f (seq start n)) = 0.
Proof.
  intros f start n. revert start.
  induction n as [|n IH]; intros start Hz; simpl.
  - reflexivity.
  - unfold sumR in *. simpl.
    rewrite Hz by lia. rewrite IH; [ring |].
    intros i Hi. apply Hz. lia.
Qed.

Lemma sum_one_hot_from : forall (f : nat -> R) start n k,
  start <= k < start + n ->
  (forall i, start <= i < start + n -> i <> k -> f i = 0) ->
  f k = 1 ->
  sumR (map f (seq start n)) = 1.
Proof.
  intros f start n. revert start.
  induction n as [|n IH]; intros start k Hk Hz Hone.
  - lia.
  - unfold sumR. simpl. destruct (Nat.eq_dec start k) as [->|Hne].
    + rewrite (sum_zero_from f (S k) n).
      * rewrite Hone. ring.
      * intros i Hi. apply Hz; lia.
    + replace (f start) with 0.
      * assert (Htail : sumR (map f (seq (S start) n)) = 1).
        { apply IH.
          - lia.
          - intros i Hi. apply Hz. lia.
          - exact Hone. }
        unfold sumR in Htail. rewrite Htail. ring.
      * symmetry. apply Hz; lia.
Qed.

Lemma basis0_right_end_value : forall U n i u,
  u = nthR U n ->
  N U n i O u = if Nat.eq_dec i (n - 1) then 1 else 0.
Proof.
  intros U n i u Hu. simpl. rewrite Hu.
  destruct (Req_EM_T (nthR U n) (nthR U n)) as [_|Hne].
  - reflexivity.
  - exfalso. apply Hne. reflexivity.
Qed.

Theorem basis0_partition_at_right_end : forall U n,
  (1 <= n)%nat ->
  sumR (map (fun i => N U n i O (nthR U n)) (seq 0 n)) = 1.
Proof.
  intros U n Hn.
  apply sum_one_hot_from with (k := n - 1).
  - lia.
  - intros i Hi Hik.
    rewrite basis0_right_end_value by reflexivity.
    destruct (Nat.eq_dec i (n - 1)) as [Heq|]; [contradiction Hik|].
    reflexivity.
  - rewrite basis0_right_end_value by reflexivity.
    destruct (Nat.eq_dec (n - 1) (n - 1)) as [_|Hne]; [reflexivity|].
    exfalso. apply Hne. reflexivity.
Qed.

Lemma basis_step_coeffs_in_01 : forall lo hi u,
  lo <= u <= hi ->
  lo < hi ->
  let c := (u - lo) / (hi - lo) in
  0 <= c <= 1 /\ 0 <= (1 - c) <= 1 /\ c + (1 - c) = 1.
Proof.
  intros lo hi u Hu Hlt c. unfold c.
  assert (Hd : hi - lo <> 0) by lra.
  assert (Hc : 0 <= (u - lo) / (hi - lo) <= 1).
  { split.
    - unfold Rdiv. apply Rmult_le_pos; [| apply Rlt_le, Rinv_0_lt_compat]; lra.
    - apply (Rmult_le_reg_r (hi - lo)); [lra|].
      unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l by exact Hd.
      rewrite Rmult_1_r, Rmult_1_l. lra. }
  split; [exact Hc|].
  split; [lra|].
  ring.
Qed.

Print Assumptions basis0_nonneg.
Print Assumptions half_open_unique.
Print Assumptions basis0_partition_at_right_end.
Print Assumptions basis_step_coeffs_in_01.
