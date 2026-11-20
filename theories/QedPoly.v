(* QedPoly.v -- qedpoly: exact univariate polynomials as coefficient lists.

   Layer `qedpoly` of the qed chain
       qedinterval -> qedpoly -> qedroots -> qedanalytic -> qedjensen.
   (qedinterval depends on this file only for `peval`; see QedInterval.v.)

   Representation: `list R` / `list Q`, low degree first.  A list of length
   S d with nonzero last entry has degree d.  No normalisation is imposed:
   trailing zeros are allowed in the type and excluded by hypotheses.

   Contents
     R side : peval, lead, prodlin, synthetic division `quot`,
              continuity, factor theorem `factor_from_roots`.
     Q side : paddQ / pscaleQ / pmulQ (executable), list equality `peqQ`,
              and the Q2R transport `peval_Q2R_pmulQ`.

   Stdlib only.  Axioms: the three stdlib classical-reals axioms.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import Reals QArith Qreals Lra Lia List.
Import ListNotations.

Local Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(* Evaluation, leading coefficient, linear products.                    *)
(* ------------------------------------------------------------------ *)

Fixpoint peval (p : list R) (x : R) : R :=
  match p with
  | [] => 0
  | a :: l => a + x * peval l x
  end.

Definition lead (p : list R) : R := last p 0.

Fixpoint prodlin (rs : list R) (x : R) : R :=
  match rs with
  | [] => 1
  | r :: t => (x - r) * prodlin t x
  end.

Lemma prodlin_app rs ss x : prodlin (rs ++ ss) x = prodlin rs x * prodlin ss x.
Proof. induction rs as [|r t IH]; simpl; [ring|rewrite IH; ring]. Qed.

Lemma prodlin_zero rs y : prodlin rs y = 0 -> In y rs.
Proof.
  induction rs as [|r t IH]; simpl; intros H; [lra|].
  destruct (Rmult_integral _ _ H) as [H1|H1]; [left; lra|right; auto].
Qed.

Lemma prodlin_in rs y : In y rs -> prodlin rs y = 0.
Proof.
  induction rs as [|r t IH]; simpl; [tauto|].
  intros [<-|H]; [ring|rewrite IH by exact H; ring].
Qed.

Lemma peval_continuous p : continuity (peval p).
Proof.
  induction p as [|a l IH]; simpl.
  - apply continuity_const. intros ? ?; reflexivity.
  - apply (continuity_plus (fun _ => a) (fun x => x * peval l x)).
    + apply continuity_const. intros ? ?; reflexivity.
    + apply (continuity_mult (fun x => x) (peval l)); [|exact IH].
      apply derivable_continuous, derivable_id.
Qed.

(* ------------------------------------------------------------------ *)
(* Synthetic division by (X - r) and the factor theorem.               *)
(* ------------------------------------------------------------------ *)

Fixpoint quot (r : R) (p : list R) : list R :=
  match p with
  | [] => []
  | a :: l => match l with [] => [] | _ :: _ => peval l r :: quot r l end
  end.

Lemma quot_spec r p x :
  peval p x = peval p r + (x - r) * peval (quot r p) x.
Proof.
  induction p as [|a l IH]; simpl; [ring|].
  destruct l as [|b l'].
  - simpl. ring.
  - simpl in *. rewrite IH. ring.
Qed.

Lemma quot_length r p : length (quot r p) = pred (length p).
Proof.
  induction p as [|a l IH]; simpl; [reflexivity|].
  destruct l as [|b l']; [reflexivity|]. simpl in *. now rewrite IH.
Qed.

Lemma quot_lead r p : (2 <= length p)%nat -> lead (quot r p) = lead p.
Proof.
  unfold lead. induction p as [|a l IH]; simpl; intros H; [lia|].
  destruct l as [|b l']; simpl in H; [lia|].
  destruct l' as [|c l''].
  - simpl. ring.
  - change (last (peval (b :: c :: l'') r :: quot r (b :: c :: l'')) 0
            = last (b :: c :: l'') 0).
    assert (Hq : quot r (b :: c :: l'') <> []).
    { simpl. discriminate. }
    destruct (quot r (b :: c :: l'')) as [|q qs] eqn:E; [contradiction|].
    rewrite <- E. rewrite <- IH by (simpl; lia).
    rewrite E. reflexivity.
Qed.

(* d pairwise distinct roots of a length-(S d) list => full factorisation. *)
Theorem factor_from_roots rs : forall p,
  S (length rs) = length p -> NoDup rs ->
  (forall r, In r rs -> peval p r = 0) ->
  forall x, peval p x = lead p * prodlin rs x.
Proof.
  induction rs as [|r t IH]; intros p Hlen Hnd Hroot x.
  - destruct p as [|a [|b l]]; simpl in Hlen; try lia.
    unfold lead; simpl. ring.
  - simpl in Hlen. inversion Hnd as [|? ? Hnin Hnd']; subst.
    rewrite (quot_spec r p x), Hroot by (left; reflexivity).
    rewrite (IH (quot r p)).
    + rewrite quot_lead by lia. simpl. ring.
    + rewrite quot_length. lia.
    + exact Hnd'.
    + intros r' Hr'. pose proof (quot_spec r p r') as Hq.
      rewrite Hroot in Hq by (right; exact Hr').
      rewrite Hroot in Hq by (left; reflexivity).
      assert (r' - r <> 0)
        by (intro; apply Hnin; replace r with r' by lra; exact Hr').
      destruct (Rmult_integral (r' - r) (peval (quot r p) r')) as [E|E]; lra.
Qed.

(* ------------------------------------------------------------------ *)
(* Executable arithmetic over Q, transported to R by Q2R.              *)
(* ------------------------------------------------------------------ *)

Local Open Scope Q_scope.

Fixpoint paddQ (p q : list Q) : list Q :=
  match p, q with
  | [], _ => q
  | _, [] => p
  | a :: p', b :: q' => (a + b) :: paddQ p' q'
  end.

Definition pscaleQ (c : Q) (p : list Q) : list Q := map (Qmult c) p.

Fixpoint pmulQ (p q : list Q) : list Q :=
  match p with
  | [] => []
  | a :: p' => paddQ (pscaleQ a q) (0 :: pmulQ p' q)
  end.

(* Coefficientwise rational equality (same length). *)
Fixpoint peqQ (p q : list Q) : bool :=
  match p, q with
  | [], [] => true
  | a :: p', b :: q' => Qeq_bool a b && peqQ p' q'
  | _, _ => false
  end.

Local Open Scope R_scope.

Definition pQ2R (p : list Q) : list R := map Q2R p.

Lemma Q2R_0 : Q2R 0 = 0.
Proof. unfold Q2R; simpl; field. Qed.

Lemma peval_paddQ p q x :
  peval (pQ2R (paddQ p q)) x = peval (pQ2R p) x + peval (pQ2R q) x.
Proof.
  revert q; induction p as [|a p IH]; intros [|b q]; simpl; try ring.
  rewrite Q2R_plus, IH. ring.
Qed.

Lemma peval_pscaleQ c p x :
  peval (pQ2R (pscaleQ c p)) x = Q2R c * peval (pQ2R p) x.
Proof.
  induction p as [|a p IH]; simpl; [ring|].
  unfold pscaleQ in *. rewrite Q2R_mult, IH. ring.
Qed.

Theorem peval_Q2R_pmulQ p q x :
  peval (pQ2R (pmulQ p q)) x = peval (pQ2R p) x * peval (pQ2R q) x.
Proof.
  induction p as [|a p IH]; simpl; [ring|].
  rewrite peval_paddQ, peval_pscaleQ. simpl. rewrite Q2R_0, IH. ring.
Qed.

Lemma peqQ_sound p q : peqQ p q = true -> pQ2R p = pQ2R q.
Proof.
  revert q; induction p as [|a p IH]; intros [|b q]; simpl;
    try discriminate; [reflexivity|].
  intros H. apply andb_prop in H as [H1 H2].
  apply Qeq_bool_iff, Qeq_eqR in H1. rewrite H1, (IH q H2). reflexivity.
Qed.

Lemma peqQ_length p q : peqQ p q = true -> length p = length q.
Proof.
  revert q; induction p as [|a p IH]; intros [|b q]; simpl;
    try discriminate; [reflexivity|].
  intros H. apply andb_prop in H as [_ H]. now rewrite (IH q H).
Qed.

(* ------------------------------------------------------------------ *)
(* Formal derivative (added with QedRootsRefute).                       *)
(*   pderiv [c0; c1; c2; ...] = [1*c1; 2*c2; ...]                        *)
(* ------------------------------------------------------------------ *)

Fixpoint pderiv_aux (k : nat) (p : list R) : list R :=
  match p with
  | [] => []
  | a :: l => INR k * a :: pderiv_aux (S k) l
  end.

Definition pderiv (p : list R) : list R := pderiv_aux 1 (tl p).

Lemma pderiv_aux_shift k l x :
  peval (pderiv_aux (S k) l) x = peval (pderiv_aux k l) x + peval l x.
Proof.
  revert k; induction l as [|a l IH]; intros k; cbn -[INR]; [ring|].
  rewrite (IH (S k)), S_INR. ring.
Qed.

Lemma pderiv_cons a l x :
  peval (pderiv (a :: l)) x = peval l x + x * peval (pderiv l) x.
Proof.
  unfold pderiv; simpl. destruct l as [|b m]; simpl; [ring|].
  rewrite pderiv_aux_shift. unfold pderiv. simpl. ring.
Qed.

Theorem peval_derivable p x :
  derivable_pt_lim (peval p) x (peval (pderiv p) x).
Proof.
  revert x; induction p as [|a l IH]; intros x.
  - unfold pderiv; simpl. apply derivable_pt_lim_const.
  - rewrite pderiv_cons.
    replace (peval l x + x * peval (pderiv l) x)
      with (0 + (1 * peval l x + x * peval (pderiv l) x)) by ring.
    apply (derivable_pt_lim_plus (fun _ => a) (fun y => y * peval l y)).
    + apply derivable_pt_lim_const.
    + apply (derivable_pt_lim_mult (fun y => y) (peval l));
        [apply derivable_pt_lim_id|apply IH].
Qed.

(* Derivatives only depend on the function. *)
Lemma derivable_pt_lim_ext f g x l :
  (forall y, f y = g y) -> derivable_pt_lim f x l -> derivable_pt_lim g x l.
Proof.
  intros Hfg Hd eps He. destruct (Hd eps He) as [d Hd'].
  exists d. intros h Hh Hhd. rewrite <- !Hfg. now apply Hd'.
Qed.

Local Open Scope Q_scope.

Fixpoint pderivQ_aux (k : nat) (p : list Q) : list Q :=
  match p with
  | [] => []
  | a :: l => (inject_Z (Z.of_nat k) * a) :: pderivQ_aux (S k) l
  end.

Definition pderivQ (p : list Q) : list Q := pderivQ_aux 1 (tl p).

Local Open Scope R_scope.

Lemma Q2R_inject_nat k : Q2R (inject_Z (Z.of_nat k)) = INR k.
Proof. unfold Q2R; simpl. rewrite INR_IZR_INZ. field. Qed.

Lemma pQ2R_pderivQ p : pQ2R (pderivQ p) = pderiv (pQ2R p).
Proof.
  unfold pderivQ, pderiv. destruct p as [|a l]; [reflexivity|]. simpl.
  generalize 1%nat. induction l as [|b m IH]; intros k; simpl; [reflexivity|].
  rewrite Q2R_mult, Q2R_inject_nat, IH. reflexivity.
Qed.
