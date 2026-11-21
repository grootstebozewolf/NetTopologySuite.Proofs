(* MarkushevichBoundQEX.v -- QEX for an inference in A. M. Masullo, "The Music
   of the Primes" (draft 2026-11-20), Terminology 10.2.1.2(2), p. 444:

     "Regular, if and only if {x_m} ⊂ E is strictly bounded away from 0 ∈ E.
      In particular, {f_m} ⊂ E'_β is bounded."

   for a Markushevich basis {(x_m, f_m)} of a Banach space E (f_m(x_n) = δ_mn).
   For Schauder bases the inference holds via the basis constant
   (‖f_m‖ ≤ 2K/‖x_m‖); Markushevich bases have no basis constant.
   The draft uses the conclusion (bounded bi-orthogonal sequence, uniform C)
   on p. 451 (§10.3) and p. 468 (§10.4.3, spectral side of the Trace Formula).

   Proved here (Stdlib, Q only; block_qex has no hypotheses beyond 0 <= B,
   the corollaries sit under the section parameters they name):
     block_qex       : in Q^2 with the Euclidean inner product, for every bound B
                       there is a biorthogonal pair (x1,x2),(f1,f2) with
                       1 <= |x_i|^2 <= 2 but f2(e2) = B + 1 on the unit vector e2.
                       This is a LOCAL obstruction: one biorthogonal pair per B.
                       The l^2 direct sum of such blocks (eps_k -> 0) would be a
                       bounded, regular Markushevich basis with unbounded {f_m},
                       i.e. a counterexample to the inference; that assembly is
                       standard but NOT re-proved here.
     close_pair_lower: abstract lemma -- if f(x) = 1, f(x') = 0 and
                       |f(v)| <= B * N(v), then 1 <= B * N(x - x').  Hence a
                       biorthogonal system containing pairs at arbitrarily small
                       distance has NO uniform bound on its functionals.
   Application (argument, not formalized; for a specialist to check): the
   draft's basis eta_{chi,t,m}(g) = chi(g)|g|^{it}(log|g|)^m on a line
   carrying zeros whose ordinates have arbitrarily small gaps satisfies
   ‖eta_t - eta_t'‖_{-s,2} -> 0 as |t - t'| -> 0 (dominated convergence,
   s > 1), so close_pair_lower makes the bi-orthogonal norms unbounded.

   Evidence for docs/attacks/2026-11-21-masullo-grh-draft.md (slice 3).
   NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import QArith Qabs Lqa.
Local Open Scope Q_scope.

(* ---- Q^2 with the Euclidean pairing ---- *)
Definition dot2 (u v : Q * Q) : Q := fst u * fst v + snd u * snd v.

(* block with parameter B >= 0, eps = 1/(B+1):
     x1 = (1, 0),  x2 = (1, eps),  f1 = (1, -(B+1)),  f2 = (0, B+1). *)
Section Block.
Variable B : Q.
Hypothesis HB : 0 <= B.

Definition eps : Q := / (B + 1).
Definition x1 : Q * Q := (1, 0).
Definition x2 : Q * Q := (1, eps).
Definition f1 : Q * Q := (1, - (B + 1)).
Definition f2 : Q * Q := (0, B + 1).
Definition e2 : Q * Q := (0, 1).

Lemma eps_mul : (B + 1) * eps == 1.
Proof. unfold eps. field. intros H. lra. Qed.

Lemma eps_range : 0 < eps /\ eps <= 1.
Proof.
  assert (H0 : 0 < eps) by (unfold eps; apply Qinv_lt_0_compat; lra).
  split; [exact H0|]. pose proof eps_mul. nra.
Qed.

Theorem block_qex :
  (* biorthogonality *)
  dot2 f1 x1 == 1 /\ dot2 f1 x2 == 0 /\ dot2 f2 x1 == 0 /\ dot2 f2 x2 == 1 /\
  (* bounded and regular: 1 <= |x_i|^2 <= 2 *)
  1 <= dot2 x1 x1 /\ dot2 x1 x1 <= 2 /\ 1 <= dot2 x2 x2 /\ dot2 x2 x2 <= 2 /\
  (* but f2 exceeds B on the unit vector e2 *)
  dot2 e2 e2 == 1 /\ B < dot2 f2 e2.
Proof.
  pose proof eps_mul as Hm. destruct eps_range as [He0 He1].
  unfold dot2, x1, x2, f1, f2, e2; cbn [fst snd].
  repeat split; try lra; nra.
Qed.
End Block.

Print Assumptions block_qex.

(* ---- abstract: close pairs force large functionals ---- *)
Section ClosePair.
Variable V I : Type.
Variable sub : V -> V -> V.
Variable N : V -> Q.                          (* the norm *)
Variable fam : I -> V -> Q.                   (* the bi-orthogonal functionals *)
Hypothesis fam_sub : forall i x y, fam i (sub x y) == fam i x - fam i y.
Variable B : Q.                               (* a putative uniform bound *)
Hypothesis fam_bound : forall i v, Qabs (fam i v) <= B * N v.

Theorem close_pair_lower : forall i x x',
  fam i x == 1 -> fam i x' == 0 -> 1 <= B * N (sub x x').
Proof.
  intros i x x' H1 H0. pose proof (fam_bound i (sub x x')) as Hb.
  rewrite fam_sub, H1, H0 in Hb.
  assert (E : Qabs (1 - 0) == 1) by reflexivity. rewrite E in Hb. exact Hb.
Qed.

(* No uniform bound survives biorthogonal pairs at arbitrarily small distance. *)
Corollary no_uniform_bound :
  0 < B ->
  (forall delta, 0 < delta ->
     exists i x x', fam i x == 1 /\ fam i x' == 0 /\ N (sub x x') < delta) ->
  False.
Proof.
  intros HB Hpairs.
  destruct (Hpairs (/ (B + B)) ltac:(apply Qinv_lt_0_compat; lra)) as [i [x [x' [H1 [H0 Hd]]]]].
  pose proof (close_pair_lower i x x' H1 H0) as Hc.
  assert (B * N (sub x x') < B * / (B + B)) by (apply Qmult_lt_l; lra).
  assert (B * / (B + B) == 1 # 2) by (field; intros Z; lra).
  lra.
Qed.
End ClosePair.

Print Assumptions no_uniform_bound.

(* ============================================================================
   Slice 4 chain, formalized modulo named analytic inputs:
     (iv)  Selberg-type density: for every K there is a strictly increasing
           list of zero ordinates in [0, T] of length n with n - 1 > K * T
           (true for zeta on Re s = 1/2: N_0(T) >> T log T)          [hypothesis]
     (iii) uniform continuity of t |-> eta_t in ||.||_{-s,2}           [hypothesis]
     (ii)  biorthogonality of (psi_t, eta_t) over the zero set          [hypothesis]
   Proved: a pigeonhole gap lemma, and that no uniform bound B on the
   functionals psi_t (the C of Masullo (10.3.1.18)) can exist.
   ========================================================================== *)
From Stdlib Require Import List ZArith.
Import ListNotations.

(* consecutive gaps all > g  =>  last - first > (length - 1) * g *)
Fixpoint gaps_gt (g : Q) (l : list Q) : Prop :=
  match l with
  | x :: ((y :: _) as tl) => g < y - x /\ gaps_gt g tl
  | _ => True
  end.

Fixpoint lastQ (d : Q) (l : list Q) : Q :=
  match l with
  | [] => d
  | [x] => x
  | _ :: tl => lastQ d tl
  end.

Lemma lastQ_indep : forall l d d' x, lastQ d (x :: l) = lastQ d' (x :: l).
Proof.
  induction l as [|y l IH]; intros d d' x; [reflexivity|].
  change (lastQ d (x :: y :: l)) with (lastQ d (y :: l)).
  change (lastQ d' (x :: y :: l)) with (lastQ d' (y :: l)).
  apply IH.
Qed.

Lemma gaps_sum : forall g l x, 0 <= g -> gaps_gt g (x :: l) ->
  inject_Z (Z.of_nat (length l)) * g <= lastQ x (x :: l) - x.
Proof.
  intros g l. induction l as [|y l IH]; intros x Hg H.
  - change (lastQ x [x]) with x.
    setoid_replace (inject_Z (Z.of_nat (length (@nil Q))) * g) with 0 by (cbn; ring). lra.
  - destruct H as [Hxy Htl].
    specialize (IH y Hg Htl).
    assert (Hlast : lastQ x (x :: y :: l) = lastQ y (y :: l)).
    { change (lastQ x (x :: y :: l)) with (lastQ x (y :: l)). apply lastQ_indep. }
    rewrite Hlast.
    replace (length (y :: l)) with (S (length l)) by reflexivity.
    rewrite Nat2Z.inj_succ, <- Z.add_1_r, inject_Z_plus.
    change (inject_Z 1) with 1. lra.
Qed.

(* pigeonhole: n points increasing in [0,T], n >= 2  =>  some gap <= T/(n-1) *)
Theorem small_gap : forall (l : list Q) (x : Q) (T g : Q),
  0 <= x -> lastQ x (x :: l) <= T -> 0 <= g ->
  T < inject_Z (Z.of_nat (length l)) * g ->
  ~ gaps_gt g (x :: l).
Proof.
  intros l x T g Hx HT Hg Hn H. pose proof (gaps_sum g l x Hg H). lra.
Qed.

Section Chain.
Variable V : Type.
Variable sub : V -> V -> V.
Variable N : V -> Q.
Variable eta : Q -> V.                        (* t |-> eta_t *)
Variable psi : Q -> V -> Q.                   (* t |-> <psi_t, .> *)
Variable Zt : Q -> Prop.                      (* t is a zero ordinate on the line *)
Hypothesis psi_sub : forall t x y, psi t (sub x y) == psi t x - psi t y.
Hypothesis bio1 : forall t, Zt t -> psi t (eta t) == 1.
Hypothesis bio0 : forall t t', Zt t -> Zt t' -> ~ t == t' -> psi t (eta t') == 0.
(* (iii) uniform continuity *)
Hypothesis eta_cont : forall delta, 0 < delta -> exists gam, 0 < gam /\
  forall t t', Qabs (t - t') < gam -> N (sub (eta t) (eta t')) < delta.
(* (iv) Selberg-type density, as increasing lists of zero ordinates *)
Hypothesis dense_zeros : forall K, 0 < K -> exists (x : Q) (l : list Q) (T : Q),
  0 <= x /\ lastQ x (x :: l) <= T /\ Forall Zt (x :: l) /\ T < inject_Z (Z.of_nat (length l)) * (/ K) /\
  (* strictly increasing *) gaps_gt 0 (x :: l).

(* from a list with no gap > g, extract a consecutive pair with 0 < gap <= g *)
Lemma pick_pair : forall g l x, Forall Zt (x :: l) -> gaps_gt 0 (x :: l) -> ~ gaps_gt g (x :: l) ->
  exists t t', Zt t /\ Zt t' /\ 0 < t' - t /\ t' - t <= g.
Proof.
  intros g l. induction l as [|y l IH]; intros x HZ Hpos Hng.
  - exfalso. apply Hng. exact I.
  - destruct Hpos as [Hxy Hpos']. inversion HZ as [|? ? Zx HZ']; subst.
    destruct (Qlt_le_dec g (y - x)) as [Hbig|Hsmall].
    + apply (IH y); auto. intros Htl. apply Hng. split; assumption.
    + exists x, y. inversion HZ'; subst. repeat split; auto.
Qed.

Theorem psi_unbounded : forall B, 0 < B -> ~ (forall t v, Zt t -> Qabs (psi t v) <= B * N v).
Proof.
  intros B HB Hbound.
  destruct (eta_cont (/ (B + B)) ltac:(apply Qinv_lt_0_compat; lra)) as [gam [Hgam Hc]].
  destruct (dense_zeros (/ (gam * (1 # 2))) ltac:(apply Qinv_lt_0_compat; lra))
    as [x [l [T [Hx [HT [HZ [Hn Hinc]]]]]]].
  assert (Hg : / / (gam * (1 # 2)) == gam * (1 # 2)) by (apply Qinv_involutive).
  rewrite Hg in Hn.
  pose proof (small_gap l x T (gam * (1 # 2)) Hx HT ltac:(lra) Hn) as Hng.
  destruct (pick_pair (gam * (1 # 2)) l x HZ Hinc Hng) as [t [t' [Zt1 [Zt2 [Hp Hle]]]]].
  (* ||psi_t|| >= 1 / N(eta_t - eta_t'), as in close_pair_lower *)
  assert (Hne : ~ t == t') by (intros E; rewrite E in Hp; lra).
  pose proof (Hbound t (sub (eta t) (eta t')) Zt1) as Hb.
  rewrite psi_sub, (bio1 t Zt1), (bio0 t t' Zt1 Zt2 Hne) in Hb.
  assert (E : Qabs (1 - 0) == 1) by reflexivity. rewrite E in Hb.
  (* but N(eta_t - eta_t') < 1/(2B) since |t - t'| <= gam/2 < gam *)
  assert (Hd : Qabs (t - t') < gam).
  { rewrite Qabs_neg by lra. lra. }
  pose proof (Hc t t' Hd) as HN.
  assert (B * N (sub (eta t) (eta t')) < B * / (B + B)) by (apply Qmult_lt_l; lra).
  assert (B * / (B + B) == 1 # 2) by (field; intros Z; lra).
  lra.
Qed.
End Chain.

Print Assumptions small_gap.
Print Assumptions psi_unbounded.
