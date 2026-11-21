(* MarkushevichBoundQEX.v -- QEX for an inference in A. M. Masullo, "The Music
   of the Primes" (draft 2026-11-20), Terminology 10.2.1.2(2), p. 444:

     "Regular, if and only if {x_m} ⊂ E is strictly bounded away from 0 ∈ E.
      In particular, {f_m} ⊂ E'_β is bounded."

   for a Markushevich basis {(x_m, f_m)} of a Banach space E (f_m(x_n) = δ_mn).
   For Schauder bases the inference holds via the basis constant
   (‖f_m‖ ≤ 2K/‖x_m‖); Markushevich bases have no basis constant.
   The draft uses the conclusion (bounded bi-orthogonal sequence, uniform C)
   on p. 451 (§10.3) and p. 468 (§10.4.3, spectral side of the Trace Formula).

   Proved here (Stdlib, Q only, no hypotheses):
     block_qex       : in Q^2 with the Euclidean inner product, for every bound B
                       there is a biorthogonal pair (x1,x2),(f1,f2) with
                       1 <= |x_i|^2 <= 2 but f2(e2) = B + 1 on the unit vector e2.
                       The l^2 direct sum of such blocks (eps_k -> 0) is a
                       bounded, regular Markushevich basis of l^2 with unbounded
                       {f_m}: the inference is FALSE in general.  (Assembling the
                       direct sum is standard and not re-proved.)
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
