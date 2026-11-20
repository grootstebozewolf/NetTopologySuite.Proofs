(* QedInterval.v -- qedinterval: rational enclosures of real polynomial
   values, with an exact sign decision.

   Layer `qedinterval` of the qed chain
       qedinterval -> qedpoly -> qedroots -> qedanalytic -> qedjensen.

   A `box` is a list of rational intervals [lo_j, hi_j], one per coefficient
   (low degree first).  `ieval b x` is the exact range of c |-> sum c_j x^j
   over the box at a rational point x (Horner with an exact scalar is exact
   because the map is linear in c).  `isign` reads off a strict sign
   (+1 / -1) or 0 when the enclosure straddles zero.

   The interface towards qedanalytic is `in_box`: a REAL coefficient list
   lying inside a rational box.  Whatever certifies the enclosure (Flocq,
   interval arithmetic, hand proof) only has to produce `in_box`; floating
   point never enters this file.

   Headline: `ieval_sound`, `isign_mul_neg`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import Reals QArith Qreals Lra List.
From NTS.Proofs Require Import QedPoly.
Import ListNotations.

Local Open Scope Q_scope.

Definition box := list (Q * Q).

Fixpoint ieval (b : box) (x : Q) : Q * Q :=
  match b with
  | [] => (0, 0)
  | (lo, hi) :: t =>
      let (l, h) := ieval t x in
      if Qle_bool 0 x then (lo + x * l, hi + x * h)
                      else (lo + x * h, hi + x * l)
  end.

Definition Qltb (a b : Q) : bool := negb (Qle_bool b a).

Definition isign (lh : Q * Q) : Z :=
  let (l, h) := lh in
  if Qltb 0 l then 1%Z else if Qltb h 0 then (-1)%Z else 0%Z.

Definition point_box (p : list Q) : box := map (fun q => (q, q)) p.
Definition width_box (d : Q) (p : list Q) : box :=
  map (fun q => (q - d, q + d)) p.

Local Open Scope R_scope.

Definition in_box (p : list R) (b : box) : Prop :=
  Forall2 (fun c lh => Q2R (fst lh) <= c <= Q2R (snd lh)) p b.

Lemma Qltb_spec a b : Qltb a b = true -> Q2R a < Q2R b.
Proof.
  unfold Qltb. intros H. apply Qlt_Rlt.
  apply Qnot_le_lt. intros Hle. apply Qle_bool_iff in Hle.
  rewrite Hle in H. discriminate.
Qed.

Theorem ieval_sound p b x :
  in_box p b ->
  Q2R (fst (ieval b x)) <= peval p (Q2R x) <= Q2R (snd (ieval b x)).
Proof.
  induction 1 as [|c [lo hi] p' b' Hc Hrest IH]; simpl.
  - rewrite Q2R_0. lra.
  - simpl in Hc. destruct (ieval b' x) as [l h]. simpl in IH.
    destruct (Qle_bool 0 x) eqn:Ex; simpl; rewrite !Q2R_plus, !Q2R_mult.
    + apply Qle_bool_iff, Qle_Rle in Ex. rewrite Q2R_0 in Ex.
      split; apply Rplus_le_compat; try lra;
        apply Rmult_le_compat_l; lra.
    + assert (Hx : Q2R x < 0).
      { rewrite <- Q2R_0. apply Qlt_Rlt, Qnot_le_lt.
        intros Hle; apply Qle_bool_iff in Hle; congruence. }
      split; apply Rplus_le_compat; try lra;
        apply Rmult_le_compat_neg_l; lra.
Qed.

Lemma isign_pos lh : isign lh = 1%Z -> 0 < Q2R (fst lh).
Proof.
  destruct lh as [l h]; unfold isign; simpl.
  destruct (Qltb 0 l) eqn:E1; [intros _; rewrite <- Q2R_0; now apply Qltb_spec|].
  destruct (Qltb h 0); discriminate.
Qed.

Lemma isign_neg lh : isign lh = (-1)%Z -> Q2R (snd lh) < 0.
Proof.
  destruct lh as [l h]; unfold isign; simpl.
  destruct (Qltb 0 l); [discriminate|].
  destruct (Qltb h 0) eqn:E2; [intros _; rewrite <- Q2R_0; now apply Qltb_spec|].
  discriminate.
Qed.

Lemma isign_cases lh : isign lh = 1%Z \/ isign lh = (-1)%Z \/ isign lh = 0%Z.
Proof.
  destruct lh as [l h]; unfold isign.
  destruct (Qltb 0 l); [auto|]. destruct (Qltb h 0); auto.
Qed.

Lemma isign_nonzero_real lh c :
  Q2R (fst lh) <= c <= Q2R (snd lh) ->
  negb (Z.eqb (isign lh) 0) = true -> c <> 0.
Proof.
  intros Hc Hs.
  destruct (isign_cases lh) as [E|[E|E]]; rewrite E in Hs; try discriminate.
  - apply isign_pos in E. lra.
  - apply isign_neg in E. lra.
Qed.

Theorem isign_mul_neg p b x y :
  in_box p b ->
  (isign (ieval b x) * isign (ieval b y))%Z = (-1)%Z ->
  peval p (Q2R x) * peval p (Q2R y) < 0.
Proof.
  intros Hb Hs.
  pose proof (ieval_sound p b x Hb) as Bx.
  pose proof (ieval_sound p b y Hb) as By.
  destruct (isign_cases (ieval b x)) as [Ex|[Ex|Ex]];
  destruct (isign_cases (ieval b y)) as [Ey|[Ey|Ey]];
  rewrite Ex, Ey in Hs; try discriminate.
  - apply isign_pos in Ex. apply isign_neg in Ey.
    apply Rmult_pos_neg; lra.
  - apply isign_neg in Ex. apply isign_pos in Ey.
    rewrite Rmult_comm. apply Rmult_pos_neg; lra.
Qed.

Lemma in_box_length p b : in_box p b -> length p = length b.
Proof. induction 1; simpl; auto. Qed.

Lemma in_box_lead p b :
  in_box p b -> negb (Z.eqb (isign (last b (0%Q, 0%Q))) 0) = true ->
  lead p <> 0.
Proof.
  unfold lead. induction 1 as [|c lh p' b' Hc Hrest IH]; simpl.
  - unfold isign; simpl. unfold Qltb; simpl. discriminate.
  - destruct b' as [|lh' b''].
    + inversion Hrest; subst. simpl. now apply isign_nonzero_real.
    + inversion Hrest; subst. apply IH.
Qed.

Lemma in_point_box p : in_box (pQ2R p) (point_box p).
Proof.
  induction p as [|q t IH]; simpl; constructor; [simpl; lra|exact IH].
Qed.

(* ------------------------------------------------------------------ *)
(* Derivative of a box (added with QedRootsRefute).                     *)
(* ------------------------------------------------------------------ *)
Local Open Scope Q_scope.

Fixpoint pderivB_aux (k : nat) (b : box) : box :=
  match b with
  | [] => []
  | (lo, hi) :: t =>
      (inject_Z (Z.of_nat k) * lo, inject_Z (Z.of_nat k) * hi)
        :: pderivB_aux (S k) t
  end.

Definition pderivB (b : box) : box := pderivB_aux 1 (tl b).

Local Open Scope R_scope.

Lemma in_box_pderiv p b : in_box p b -> in_box (pderiv p) (pderivB b).
Proof.
  unfold pderiv, pderivB. intros H. destruct H as [|c lh p' b' _ H]; [constructor|].
  simpl. generalize 1%nat.
  induction H as [|c' [lo hi] p'' b'' Hc Hrest IH]; intros k; simpl; constructor.
  - simpl in *. rewrite !Q2R_mult, !Q2R_inject_nat.
    pose proof (pos_INR k). split; apply Rmult_le_compat_l; lra.
  - apply IH.
Qed.

Print Assumptions ieval_sound.
Print Assumptions isign_mul_neg.
Print Assumptions in_box_pderiv.
