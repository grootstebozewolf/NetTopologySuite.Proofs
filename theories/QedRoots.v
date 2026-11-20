(* QedRoots.v -- qedroots: exact real-root certificates for univariate
   polynomials, from rational coefficient enclosures.

   Layer `qedroots` of the qed chain
       qedinterval -> qedpoly -> qedroots -> qedanalytic -> qedjensen.

   Predicates (separate definitions, never conflated):
     hyperbolic p          p = c * prod (X - r_i), multiset of real roots
                           (repeated roots allowed), deg = #roots.
     simple_real_rooted p  as above with lead p as c, roots pairwise
                           distinct, and they are ALL the real zeros.

   Certificates (boolean, decided by vm_compute over Q):
     box_cert b xs     d+1 increasing rational points; the exact rational
                       enclosure of P(x_i) over the box has a strict sign,
                       alternating.  Robust (an open condition on the box).
                       Sound:  in_box p b -> box_cert b xs = true
                               -> simple_real_rooted p          (cert_sound)
     factor_cert c fs p
                       p == c * prod f_k coefficientwise over Q, c <> 0,
                       each f_k carrying its own box_cert.  Factors may
                       repeat, so multiplicities are expressible.
                       Sound:  factor_cert c fs p = true
                               -> hyperbolic (pQ2R p)           (factor_cert_sound)

   Completeness statements are deliberately NOT claimed: `box_cert` is
   incomplete on repeated roots by construction (QedRootsExamples:
   double_root_box_uncertifiable), and `factor_cert` would need the
   squarefree decomposition to be supplied.  A failed check proves nothing.
   No Sturm sequence yet: root counting for non-real-rooted polynomials
   (Sturm / Cauchy index) is the OPEN next rung of this layer.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import Reals QArith Qreals Lra Lia List.
From NTS.Proofs Require Import QedPoly QedInterval.
Import ListNotations.

Local Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(* Predicates.                                                         *)
(* ------------------------------------------------------------------ *)

Definition hyperbolic (p : list R) : Prop :=
  exists c rs, c <> 0 /\ S (length rs) = length p /\
               forall x, peval p x = c * prodlin rs x.

Definition simple_real_rooted (p : list R) : Prop :=
  exists rs, lead p <> 0 /\ S (length rs) = length p /\ NoDup rs /\
             (forall y, peval p y = 0 <-> In y rs) /\
             forall x, peval p x = lead p * prodlin rs x.

Lemma simple_real_rooted_hyperbolic p :
  simple_real_rooted p -> hyperbolic p.
Proof. intros (rs & H1 & H2 & _ & _ & H5). exists (lead p), rs; auto. Qed.

(* In a hyperbolic polynomial every real zero is a listed root. *)
Lemma hyperbolic_zeros p c rs :
  c <> 0 -> (forall x, peval p x = c * prodlin rs x) ->
  forall y, peval p y = 0 <-> In y rs.
Proof.
  intros Hc Hf y. rewrite Hf. split.
  - intros H. apply Rmult_integral in H as [H|H]; [contradiction|].
    now apply prodlin_zero.
  - intros H. rewrite prodlin_in by exact H. ring.
Qed.

(* ------------------------------------------------------------------ *)
(* Real-side sign alternation  =>  simple real-rootedness.              *)
(* ------------------------------------------------------------------ *)

Fixpoint alternating (p : list R) (xs : list R) : Prop :=
  match xs with
  | [] => False
  | [_] => True
  | x0 :: ((x1 :: _) as rest) =>
      x0 < x1 /\ peval p x0 * peval p x1 < 0 /\ alternating p rest
  end.

Lemma alternating_roots p : forall xs x0,
  alternating p (x0 :: xs) ->
  exists rs, length rs = length xs /\ NoDup rs /\
             Forall (fun r => x0 < r) rs /\
             forall r, In r rs -> peval p r = 0.
Proof.
  induction xs as [|x1 xs IH]; intros x0 Halt.
  - exists []. repeat split; try constructor. simpl; tauto.
  - destruct Halt as (Hlt & Hsg & Hrest).
    destruct (IH x1 Hrest) as (rs & Hl & Hnd & Hgt & Hz).
    destruct (IVT_cor (peval p) x0 x1 (peval_continuous p) (Rlt_le _ _ Hlt)
                      (Rlt_le _ _ Hsg)) as (z & [Hz0 Hz1] & Hpz).
    assert (z <> x0) by (intro; subst; rewrite Hpz in Hsg; lra).
    assert (z <> x1) by (intro; subst; rewrite Hpz in Hsg; lra).
    exists (z :: rs). split; [simpl; lia|]. split; [|split].
    + constructor; [|exact Hnd].
      intro Hin. rewrite Forall_forall in Hgt. specialize (Hgt z Hin). lra.
    + constructor; [lra|].
      rewrite Forall_forall in *. intros r Hr. specialize (Hgt r Hr). lra.
    + intros r [<-|Hr]; auto.
Qed.

Theorem alternating_simple_real_rooted p xs :
  length xs = length p -> lead p <> 0 -> alternating p xs ->
  simple_real_rooted p.
Proof.
  intros Hlen Hlead Halt.
  destruct xs as [|x0 xs]; [contradiction|].
  destruct (alternating_roots p xs x0 Halt) as (rs & Hl & Hnd & _ & Hz).
  assert (Hlen' : S (length rs) = length p) by (simpl in Hlen; lia).
  pose proof (factor_from_roots rs p Hlen' Hnd Hz) as Hfac.
  exists rs. split; [exact Hlead|]. split; [exact Hlen'|].
  split; [exact Hnd|]. split; [|exact Hfac].
  exact (hyperbolic_zeros p (lead p) rs Hlead Hfac).
Qed.

(* ------------------------------------------------------------------ *)
(* The box certificate (robust, from enclosures).                       *)
(* ------------------------------------------------------------------ *)

Fixpoint alt_check (b : box) (xs : list Q) : bool :=
  match xs with
  | [] => false
  | [x] => negb (Z.eqb (isign (ieval b x)) 0)
  | x0 :: ((x1 :: _) as rest) =>
      Qltb x0 x1 &&
      Z.eqb (isign (ieval b x0) * isign (ieval b x1)) (-1) &&
      alt_check b rest
  end.

Definition box_cert (b : box) (xs : list Q) : bool :=
  Nat.eqb (length xs) (length b) &&
  negb (Z.eqb (isign (last b (0%Q, 0%Q))) 0) &&
  alt_check b xs.

Lemma alt_check_sound p b xs :
  in_box p b -> alt_check b xs = true -> alternating p (map Q2R xs).
Proof.
  intros Hb. induction xs as [|x0 rest IH]; simpl; [discriminate|].
  destruct rest as [|x1 rest']; [simpl; auto|].
  intros H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  simpl. split; [now apply Qltb_spec|]. split.
  - apply Z.eqb_eq in H2. now apply (isign_mul_neg p b).
  - apply IH. exact H3.
Qed.

(* BRIDGE: a passed rational certificate makes EVERY real coefficient
   vector inside the box simple-real-rooted. *)
Theorem cert_sound (p : list R) (b : box) (xs : list Q) :
  in_box p b -> box_cert b xs = true -> simple_real_rooted p.
Proof.
  intros Hb H. unfold box_cert in H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Nat.eqb_eq in H1.
  apply (alternating_simple_real_rooted p (map Q2R xs)).
  - rewrite length_map, H1. symmetry. now apply in_box_length.
  - now apply (in_box_lead p b).
  - now apply (alt_check_sound p b).
Qed.

Corollary cert_hyperbolic p b xs :
  in_box p b -> box_cert b xs = true -> hyperbolic p.
Proof. intros; apply simple_real_rooted_hyperbolic; eapply cert_sound; eauto. Qed.

Corollary point_cert_sound (p : list Q) xs :
  box_cert (point_box p) xs = true -> simple_real_rooted (pQ2R p).
Proof. intros H. exact (cert_sound _ _ _ (in_point_box p) H). Qed.

(* ------------------------------------------------------------------ *)
(* Factor certificate: exact multiplicities over Q.                     *)
(* ------------------------------------------------------------------ *)
Local Open Scope Q_scope.

Fixpoint pmul_all (c : Q) (fs : list (list Q)) : list Q :=
  match fs with
  | [] => [c]
  | f :: t => pmulQ f (pmul_all c t)
  end.

Fixpoint deg_sum (fs : list (list Q)) : nat :=
  match fs with
  | [] => O
  | f :: t => (pred (length f) + deg_sum t)%nat
  end.

(* fs : factors, each with the sample points of its own sign certificate. *)
Definition factor_cert (c : Q) (fs : list (list Q * list Q)) (p : list Q) : bool :=
  negb (Qeq_bool c 0) &&
  forallb (fun fx => box_cert (point_box (fst fx)) (snd fx)) fs &&
  Nat.eqb (length p) (S (deg_sum (map fst fs))) &&
  peqQ p (pmul_all c (map fst fs)).

Local Open Scope R_scope.

Lemma pmul_all_factor (c : Q) (fs : list (list Q * list Q)) :
  Q2R c <> 0 ->
  forallb (fun fx => box_cert (point_box (fst fx)) (snd fx)) fs = true ->
  exists c' rs, c' <> 0 /\ length rs = deg_sum (map fst fs) /\
    forall x, peval (pQ2R (pmul_all c (map fst fs))) x = c' * prodlin rs x.
Proof.
  intros Hc. induction fs as [|[f xs] t IH]; simpl; intros H.
  - exists (Q2R c), []. repeat split; auto. intros x. simpl. ring.
  - apply andb_prop in H as [Hf Ht].
    destruct (IH Ht) as (c' & rs & Hc' & Hl & He).
    destruct (point_cert_sound f xs Hf) as (rf & Hlf & Hlenf & _ & _ & Hef).
    exists (lead (pQ2R f) * c'), (rf ++ rs). split; [|split].
    + now apply Rmult_integral_contrapositive.
    + rewrite length_app, Hl. unfold pQ2R in Hlenf. rewrite length_map in Hlenf.
      simpl. lia.
    + intros x. rewrite peval_Q2R_pmulQ, Hef, He, prodlin_app. ring.
Qed.

Theorem factor_cert_sound c fs p :
  factor_cert c fs p = true -> hyperbolic (pQ2R p).
Proof.
  unfold factor_cert. intros H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3].
  apply andb_prop in H as [H1 H2].
  assert (Hc : Q2R c <> 0).
  { intros E. rewrite <- Q2R_0 in E. apply eqR_Qeq in E.
    apply Qeq_bool_iff in E. rewrite E in H1. discriminate. }
  destruct (pmul_all_factor c fs Hc H2) as (c' & rs & Hc' & Hl & He).
  exists c', rs. split; [exact Hc'|]. split.
  - apply Nat.eqb_eq in H3. unfold pQ2R. rewrite length_map, H3, Hl. reflexivity.
  - intros x. rewrite (peqQ_sound _ _ H4). apply He.
Qed.
