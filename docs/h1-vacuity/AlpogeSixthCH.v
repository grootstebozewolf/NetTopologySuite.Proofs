(* AlpogeSixthCH.v -- six more main-line lemmas of the claimed RH/GRH Lean
   development (CocoSgt/riemann-hypothesis-lean @ 7cbf7a0), REFINED.

   "Refined" (the criterion of AlpogeSkeleton.v / AlpogeRefineBatch.v): the
   Lean proof's own reasoning is rebuilt in Rocq; its remaining inputs are
   only (a) standard Mathlib facts, stated as named hypotheses and tagged
   [Mathlib], or (b) other inventory lemmas of the Lean development, named
   as hypotheses and tagged [inventory].  No Admitted / Axiom; every
   Print Assumptions shows only ClassicalDedekindReals.sig_forall_dec and
   functional_extensionality_dep (brought in by Stdlib's R), both on the
   allowlist (docs/axiom-allowlist.txt).

   Carriers.  The complex numbers are an abstract field K bundled in the
   record CStr together with the real embedding ofR : R -> K, the real part
   re : K -> R and the norm nrm : K -> R, whose fields are exactly the
   Mathlib laws of C that the Lean proofs use (each field tagged
   [Mathlib]).  Reals are Stdlib's R; log, rpow and the arithmetic sums
   (von Mangoldt sums, GPsi pieces) are abstract functions carrying only
   the facts the Lean proofs cite.  Finsets are lists (NoDup where the
   Lean proof uses cardinality or Finset.sum_image), and Equivs / images
   are Permutations of lists (Equiv.sum_comp, Finset.sum_image).

     S1  one_char            ChCore.lean : one_char (l.202), with move (l.154), triv (l.167)
     S2  th_le               ChCore.lean : th_le (l.75)
     S3  ch_balance          ChBalance.lean : ch_balance (l.200)
     S4  ch_top              ChTop.lean : ch_top (l.37), with ch_top_main_eq (l.11)
     S5  gmA_eq              PrimitiveCosets/GmAEq.lean : gmA_eq (l.61),
                             with the private gmA_eq_triv (l.16)
     S6  large_x_eventually  SizeWindowBrackets/ChainSlopeWindows/
                             SubThreeMulLogTwoLe.lean : large_x_eventually
                             (l.319), the instance used by CoreGm.lean l.23

   Evidence for the Alpoge skeleton refinement ledger (AlpogeSkeleton.v).
   NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import Reals Lra Psatz List Ring Field Permutation.
Import ListNotations.
Local Open Scope R_scope.

(* ===================================================================== *)
(* Base: the carrier C, finite sums over lists                           *)
(* ===================================================================== *)
(* A model of (C, R -> C, re, norm) with the Mathlib laws used below. *)
Record CStr := {
  car : Type;
  k0 : car; k1 : car;
  kadd : car -> car -> car; kmul : car -> car -> car;
  ksub : car -> car -> car; kdiv : car -> car -> car;
  kopp : car -> car; kinv : car -> car;
  kfield : field_theory k0 k1 kadd kmul ksub kopp kdiv kinv (@eq car);  (* [Mathlib] Complex.instField *)
  ofR : R -> car;                                       (* the coercion R -> C *)
  re : car -> R;                                        (* Complex.re *)
  nrm : car -> R;                                       (* norm on C *)
  ofR_add : forall r s, ofR (r + s) = kadd (ofR r) (ofR s);   (* [Mathlib] Complex.ofReal_add *)
  ofR_mul : forall r s, ofR (r * s) = kmul (ofR r) (ofR s);   (* [Mathlib] Complex.ofReal_mul *)
  ofR_one : ofR 1 = k1;                                       (* [Mathlib] Complex.ofReal_one *)
  ofR_eq0 : forall r, ofR r = k0 -> r = 0;                    (* [Mathlib] Complex.ofReal_eq_zero *)
  re_add : forall a b, re (kadd a b) = re a + re b;           (* [Mathlib] Complex.add_re *)
  re_ofR_mul : forall r z, re (kmul (ofR r) z) = r * re z;    (* [Mathlib] Complex.re_ofReal_mul *)
  re_ofR : forall r, re (ofR r) = r;                          (* [Mathlib] Complex.ofReal_re *)
  abs_re_le : forall z, Rabs (re z) <= nrm z;                 (* [Mathlib] Complex.abs_re_le_norm *)
  nrm_add : forall a b, nrm (kadd a b) <= nrm a + nrm b;      (* [Mathlib] norm_add_le *)
  nrm_mul : forall a b, nrm (kmul a b) = nrm a * nrm b;       (* [Mathlib] norm_mul *)
  nrm_ofR : forall r, nrm (ofR r) = Rabs r                    (* [Mathlib] Complex.norm_real, Real.norm_eq_abs *)
}.
Arguments k0 {_}. Arguments k1 {_}. Arguments kadd {_} _ _. Arguments kmul {_} _ _.
Arguments ksub {_} _ _. Arguments kdiv {_} _ _. Arguments kopp {_} _. Arguments kinv {_} _.
Arguments ofR {_} _. Arguments re {_} _. Arguments nrm {_} _.
Infix "+'" := kadd (at level 50, left associativity).
Infix "*'" := kmul (at level 40, left associativity).
Infix "-'" := ksub (at level 50, left associativity).

Fixpoint rsum (l : list R) : R := match l with [] => 0 | v :: t => v + rsum t end.

Lemma rsum_map_ext : forall {A} (f h : A -> R) l, (forall x, In x l -> f x = h x) ->
  rsum (map f l) = rsum (map h l).
Proof.
  intros A f h l H. induction l as [|a l IH]; simpl; [reflexivity|].
  rewrite (H a (or_introl eq_refl)), IH; [reflexivity|]. intros x Hx. apply H. right. exact Hx.
Qed.
Lemma rsum_plus : forall {A} (f h : A -> R) l, rsum (map (fun x => f x + h x) l) = rsum (map f l) + rsum (map h l).
Proof. intros A f h l. induction l as [|a l IH]; simpl; [ring|rewrite IH; ring]. Qed.
Lemma rsum_minus : forall {A} (f h : A -> R) l, rsum (map (fun x => f x - h x) l) = rsum (map f l) - rsum (map h l).
Proof. intros A f h l. induction l as [|a l IH]; simpl; [ring|rewrite IH; ring]. Qed.
Lemma rsum_scal : forall {A} (c : R) (f : A -> R) l, rsum (map (fun x => c * f x) l) = c * rsum (map f l).
Proof. intros A c f l. induction l as [|a l IH]; simpl; [ring|rewrite IH; ring]. Qed.
Lemma rsum_const : forall {A} (c : R) (l : list A), rsum (map (fun _ => c) l) = INR (length l) * c.
Proof. intros A c l. induction l as [|a l IH]; simpl length; [simpl; ring|rewrite S_INR; simpl; rewrite IH; ring]. Qed.
Lemma rsum_swap : forall {A B} (f : A -> B -> R) (la : list A) (lb : list B),
  rsum (map (fun x => rsum (map (fun y => f x y) lb)) la) = rsum (map (fun y => rsum (map (fun x => f x y) la)) lb).
Proof.
  intros A B f la lb. induction la as [|a la IH]; simpl.
  - induction lb as [|b lb IHb]; simpl; [reflexivity|rewrite <- IHb; ring].
  - rewrite IH, <- rsum_plus. reflexivity.
Qed.
Lemma rsum_perm : forall l l', Permutation l l' -> rsum l = rsum l'.
Proof.
  intros l l' H. induction H; simpl; try reflexivity.
  - rewrite IHPermutation. reflexivity.
  - ring.
  - rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.
(* a sum of terms each >= c is >= |l| c *)
Lemma rsum_ge_const : forall {A} (c : R) (f : A -> R) l, (forall x, In x l -> c <= f x) ->
  INR (length l) * c <= rsum (map f l).
Proof.
  intros A c f l H. rewrite <- rsum_const. induction l as [|a l IH]; simpl; [lra|].
  apply Rplus_le_compat; [apply H; left; reflexivity|apply IH; intros x Hx; apply H; right; exact Hx].
Qed.

Lemma rsum_le_const : forall {A} (c : R) (f : A -> R) l, (forall x, In x l -> f x <= c) ->
  rsum (map f l) <= INR (length l) * c.
Proof.
  intros A c f l H. rewrite <- rsum_const. induction l as [|a l IH]; simpl; [lra|].
  apply Rplus_le_compat; [apply H; left; reflexivity|apply IH; intros x Hx; apply H; right; exact Hx].
Qed.

Lemma abs_le_elim : forall u v, Rabs u <= v -> - v <= u /\ u <= v.
Proof. intros u v H. pose proof (Rle_abs u). pose proof (Rle_abs (- u)). rewrite Rabs_Ropp in *. split; lra. Qed.

(* Finset.erase as list removal, for a NoDup list containing a *)
Lemma perm_remove : forall {A} (dec : forall a b : A, {a = b} + {a <> b}) (a : A) l,
  NoDup l -> In a l -> Permutation l (a :: remove dec a l).
Proof.
  intros A dec a l Hnd Hin. induction l as [|b l IH]; [destruct Hin|].
  inversion Hnd as [|b' l' Hb Hnd' E]; subst. simpl. destruct (dec a b) as [E|E].
  - subst b. rewrite notin_remove by exact Hb. reflexivity.
  - destruct Hin as [Hin|Hin]; [congruence|].
    eapply perm_trans; [apply perm_skip; exact (IH Hnd' Hin)|]. apply perm_swap.
Qed.

Lemma inj_map_NoDup : forall {A B} (f : A -> B) l, (forall a b, f a = f b -> a = b) -> NoDup l -> NoDup (map f l).
Proof.
  intros A B f l Hf Hnd. induction Hnd as [|a l Ha Hnd IH]; simpl; constructor; [|exact IH].
  intro Hin. apply in_map_iff in Hin. destruct Hin as [b [E Hb]]. apply Hf in E. subst b. contradiction.
Qed.

Section Base.
Variable C : CStr.
Add Field Kf : (kfield C).

Fixpoint ksum (l : list (car C)) : car C := match l with [] => k0 | v :: t => v +' ksum t end.

Lemma ksum_map_scal : forall {A} (c : car C) (f : A -> car C) l,
  ksum (map (fun x => c *' f x) l) = c *' ksum (map f l).
Proof. intros A c f l. induction l as [|a l IH]; simpl; [ring|rewrite IH; ring]. Qed.
Lemma ksum_map_ext : forall {A} (f h : A -> car C) l, (forall x, In x l -> f x = h x) ->
  ksum (map f l) = ksum (map h l).
Proof.
  intros A f h l H. induction l as [|a l IH]; simpl; [reflexivity|].
  rewrite (H a (or_introl eq_refl)), IH; [reflexivity|]. intros x Hx. apply H. right. exact Hx.
Qed.
Lemma ksum_map_plus : forall {A} (f h : A -> car C) l,
  ksum (map (fun x => f x +' h x) l) = ksum (map f l) +' ksum (map h l).
Proof. intros A f h l. induction l as [|a l IH]; simpl; [ring|rewrite IH; ring]. Qed.
Lemma ksum_map_minus : forall {A} (f h : A -> car C) l,
  ksum (map (fun x => f x -' h x) l) = ksum (map f l) -' ksum (map h l).
Proof. intros A f h l. induction l as [|a l IH]; simpl; [ring|rewrite IH; ring]. Qed.
Lemma ksum_swap : forall {A B} (f : A -> B -> car C) (la : list A) (lb : list B),
  ksum (map (fun x => ksum (map (fun y => f x y) lb)) la) = ksum (map (fun y => ksum (map (fun x => f x y) la)) lb).
Proof.
  intros A B f la lb. induction la as [|a la IH]; simpl.
  - induction lb as [|b lb IHb]; simpl; [reflexivity|rewrite <- IHb; ring].
  - rewrite IH, <- ksum_map_plus. reflexivity.
Qed.
(* [Mathlib] Equiv.sum_comp / Finset.sum_bij: sums are invariant under permutation *)
Lemma ksum_perm : forall l l', Permutation l l' -> ksum l = ksum l'.
Proof.
  intros l l' H. induction H; simpl; try reflexivity.
  - rewrite IHPermutation. reflexivity.
  - ring.
  - rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.
(* Finset.sum_filter *)
Lemma ksum_filter : forall {A} (p : A -> bool) (f : A -> car C) l,
  ksum (map (fun x => if p x then f x else k0) l) = ksum (map f (filter p l)).
Proof.
  intros A p f l. induction l as [|a l IH]; simpl; [reflexivity|].
  destruct (p a); simpl; rewrite IH; [reflexivity|ring].
Qed.
(* Finset.sum_ite_eq' *)
Lemma ksum_ite_eq : forall {A} (dec : forall a b : A, {a = b} + {a <> b}) (c : A) (f : A -> car C) l,
  NoDup l -> In c l -> ksum (map (fun x => if dec x c then f x else k0) l) = f c.
Proof.
  intros A dec c f l Hnd Hin. induction l as [|a l IH]; [destruct Hin|].
  inversion Hnd as [|a' l' Ha Hnd' E]; subst. simpl. destruct (dec a c) as [E|E].
  - assert (Z : ksum (map (fun x => if dec x c then f x else k0) l) = k0).
    { transitivity (ksum (map (fun _ : A => (k0 : car C)) l)).
      - apply ksum_map_ext. intros x Hx. destruct (dec x c); [subst; contradiction|reflexivity].
      - clear. induction l as [|b l IH]; simpl; [ring|rewrite IH; ring]. }
    rewrite Z. subst a. ring.
  - destruct Hin as [Hin|Hin]; [congruence|]. rewrite (IH Hnd' Hin). ring.
Qed.

Lemma ksum_zero : forall {A} (f : A -> car C) l, (forall x, In x l -> f x = k0) -> ksum (map f l) = k0.
Proof.
  intros A f l H. induction l as [|a l IH]; simpl; [reflexivity|].
  rewrite (H a (or_introl eq_refl)), IH; [ring|]. intros x Hx. apply H. right. exact Hx.
Qed.

(* derived laws of ofR, re, nrm *)
Lemma ofR_zero : ofR 0 = (k0 : car C).
Proof.
  assert (E : ofR 0 = ofR 0 +' (ofR 0 : car C)) by (rewrite <- ofR_add; f_equal; ring).
  transitivity ((ofR 0 +' ofR 0) -' (ofR 0 : car C)); [ring|]. rewrite <- E. ring.
Qed.
Lemma ofR_opp : forall r, ofR (- r) = kopp (ofR r : car C).
Proof.
  intro r. assert (E : ofR (- r) +' ofR r = (k0 : car C)) by (rewrite <- ofR_add, <- ofR_zero; f_equal; ring).
  transitivity ((ofR (- r) +' ofR r) -' (ofR r : car C)); [ring|]. rewrite E. ring.
Qed.
Lemma ofR_sub : forall r s, ofR (r - s) = (ofR r : car C) -' ofR s.
Proof. intros r s. unfold Rminus. rewrite ofR_add, ofR_opp. ring. Qed.
Lemma ofR_INR_S : forall n, (ofR (INR (S n)) : car C) = k1 +' ofR (INR n).
Proof. intro n. rewrite S_INR, ofR_add, ofR_one. ring. Qed.
Lemma re_zero : re (k0 : car C) = 0.
Proof. rewrite <- ofR_zero. apply re_ofR. Qed.
Lemma re_one : re (k1 : car C) = 1.
Proof. rewrite <- ofR_one. apply re_ofR. Qed.
Lemma re_opp : forall z : car C, re (kopp z) = - re z.
Proof.
  intro z. assert (E : re (z +' kopp z) = 0) by (replace (z +' kopp z) with (k0 : car C) by ring; apply re_zero).
  rewrite re_add in E. lra.
Qed.
Lemma re_sub : forall a b : car C, re (a -' b) = re a - re b.
Proof. intros a b. replace (a -' b) with (a +' kopp b) by ring. rewrite re_add, re_opp. ring. Qed.
Lemma re_sum : forall {A} (f : A -> car C) l, re (ksum (map f l)) = rsum (map (fun x => re (f x)) l).
Proof. intros A f l. induction l as [|a l IH]; simpl; [apply re_zero|rewrite re_add, IH; reflexivity]. Qed.
Lemma nrm_zero : nrm (k0 : car C) = 0.
Proof. rewrite <- ofR_zero, nrm_ofR. apply Rabs_R0. Qed.
Lemma nrm_nonneg : forall z : car C, 0 <= nrm z.
Proof. intro z. pose proof (abs_re_le C z). pose proof (Rabs_pos (re z)). lra. Qed.
(* [Mathlib] norm_sum_le *)
Lemma nrm_sum_le : forall {A} (f : A -> car C) l, nrm (ksum (map f l)) <= rsum (map (fun x => nrm (f x)) l).
Proof.
  intros A f l. induction l as [|a l IH]; simpl; [rewrite nrm_zero; lra|].
  pose proof (nrm_add C (f a) (ksum (map f l))). lra.
Qed.
(* the lower bound -|z| <= re z *)
Lemma re_ge_neg_nrm : forall z : car C, - nrm z <= re z.
Proof.
  intro z. pose proof (abs_re_le C z). pose proof (Rle_abs (- re z)) as H2. rewrite Rabs_Ropp in H2. lra.
Qed.
(* Complex.ofReal_sum *)
Lemma ksum_ofR : forall {A} (f : A -> R) l, ksum (map (fun x => ofR (f x)) l) = (ofR (rsum (map f l)) : car C).
Proof. intros A f l. induction l as [|a l IH]; simpl; [symmetry; apply ofR_zero|rewrite IH, ofR_add; reflexivity]. Qed.
(* Finset.sum_const, nsmul_eq_mul *)
Lemma ksum_const1 : forall {A} (l : list A), ksum (map (fun _ => k1) l) = (ofR (INR (length l)) : car C).
Proof. intros A l. induction l as [|a l IH]; simpl length; [simpl; symmetry; apply ofR_zero|rewrite ofR_INR_S; simpl; rewrite IH; reflexivity]. Qed.
End Base.
Arguments ksum {_} _.

(* ===================================================================== *)
(* S1  one_char  (ChCore.lean : CharacterBalanceMoves.one_char, l.202)   *)
(*     with its helpers move (l.154) and triv (l.167)                    *)
(* ===================================================================== *)
(* For psi in PsiA A0 and nodes y t within 1 of x, the per-character lower
   bound  |TT| (vv psi - R) <= sum_t Re(psi(e1 t) GPsi psi (y t)),  by the
   Lean case split: psi = 0 (Gz Lipschitz, DerivInt.2); psi kept and
   non-trivial (decomposition e, norms n1 n2 via move and triv); psi not
   kept (triangle inequality via move). *)
Section OneChar.
Variable C : CStr.
Add Field KfO : (kfield C).
Local Notation K := (car C).

Variables (Hg G : Type) (gadd : G -> G -> G) (inr e1 : Hg -> G) (sgc0 : G).
(* Lean, in one_char: (e1 t : E0 x H) = sgc0 + (0, t)  `by simp [e1, sgc0]` *)
Hypothesis E1SPLIT : forall t, e1 t = gadd sgc0 (inr t).            (* [Mathlib] Prod.ext, ZMod 2 arithmetic *)
Variable Ch : Type.                                                  (* AddChar (E0 x H) C *)
Hypothesis Ch_eq_dec : forall a b : Ch, {a = b} + {a <> b}.          (* [Mathlib] DecidableEq (classical) *)
Variable zero : Ch.                                                  (* the trivial character 0 *)
Variable ev : Ch -> G -> K.                                          (* psi g *)
Hypothesis ev_add : forall psi a b, ev psi (gadd a b) = ev psi a *' ev psi b.   (* [Mathlib] AddChar.map_add_eq_mul *)
Hypothesis ev_zero : forall g, ev zero g = k1.                       (* [Mathlib] AddChar.zero_apply *)
Hypothesis ev_nrm : forall psi g, nrm (ev psi g) = 1.                (* [Mathlib] AddChar.norm_apply *)
(* the classical test `forall h, psi (0, h) = 1` of wtA, decided *)
Variable trivH : Ch -> bool.
Hypothesis trivH_spec : forall psi, trivH psi = true <-> (forall h, ev psi (inr h) = k1).
Variables (lg : R -> R) (Gz : R -> R) (ell : Ch -> K).
Hypothesis LOG_MONO : forall a b, 0 < a -> a <= b -> lg a <= lg b.  (* [Mathlib] Real.log_le_log *)
Hypothesis LOG_NONNEG : forall a, 1 <= a -> 0 <= lg a.               (* [Mathlib] Real.log_nonneg *)
(* GPsi (FirstPrimeNeSecondPrime.lean l.68): Gz y for psi = 0, else
   VS psi y + y * ell psi with VS psi y = sum_{n in Icc 1 floor y} Lambda n primVal psi n (y/n - 1). *)
Variable VS : Ch -> R -> K.
Hypothesis VS_one : forall psi, VS psi 1 = k0.   (* [Mathlib] Nat.floor_one, Finset.Icc_self, vonMangoldt_apply_one (Lean `simp` in triv) *)
Definition GPsi (psi : Ch) (y : R) : K :=
  if Ch_eq_dec psi zero then ofR (Gz y) else VS psi y +' ofR y *' ell psi.

(* DerivInt (GrowthBoundGivesRiemannHypothesis.lean l.62) *)
Definition DerivInt (Cd : R) : Prop :=
  (forall psi, psi <> zero -> forall y z, 1 <= y -> 1 <= z ->
     nrm (GPsi psi y -' GPsi psi z) <= Rabs (y - z) * (lg (Rmax y z) + Cd + nrm (ell psi))) /\
  (forall y z, 1 <= y -> 1 <= z -> Rabs (Gz y - Gz z) <= Cd * Rabs (y - z)).

(* wtA (SplitInertia.lean l.30) and vv (ChCore.lean l.183) *)
Definition wtA (c : R) (psi : Ch) : R := if trivH psi then 1 else c.
Variable Kp : list Ch.                                               (* the kept characters *)
Variable inPsiA : Ch -> Prop.                                        (* psi in PsiA A0 *)
Definition vv (c x : R) (psi : Ch) : R :=
  if in_dec Ch_eq_dec psi Kp then wtA c psi * re (GPsi psi x) else - nrm (GPsi psi x).

(* move (ChCore.lean l.154) *)
Lemma move_r : forall x Cd y, 3 <= x -> 0 <= Cd -> Rabs (y - x) <= 1 -> DerivInt Cd ->
  forall psi, psi <> zero -> nrm (GPsi psi y -' GPsi psi x) <= lg (x + 1) + Cd + nrm (ell psi).
Proof.
  intros x Cd y Hx HCd Hy HDer psi H0.
  destruct (abs_le_elim _ _ Hy) as [Hy1 Hy2].
  pose proof (proj1 HDer psi H0 y x ltac:(lra) ltac:(lra)) as Hd.
  assert (Hmax : Rmax y x <= x + 1) by (apply Rmax_lub; lra).
  assert (Hmax1 : 1 <= Rmax y x) by (eapply Rle_trans; [|apply Rmax_r]; lra).
  pose proof (LOG_MONO (Rmax y x) (x + 1) ltac:(lra) Hmax) as Hlog.
  pose proof (LOG_NONNEG (Rmax y x) Hmax1) as Hlog0.
  pose proof (nrm_nonneg C (ell psi)) as Hn.
  assert (Hs : 0 <= lg (Rmax y x) + Cd + nrm (ell psi)) by lra.
  pose proof (Rmult_le_compat_r _ _ _ Hs Hy) as H1.
  lra.
Qed.

(* triv (ChCore.lean l.167) *)
Lemma triv_r : forall x Cd, 3 <= x -> 0 <= Cd -> DerivInt Cd ->
  forall psi, psi <> zero -> nrm (GPsi psi x) <= x * (lg x + Cd + nrm (ell psi)).
Proof.
  intros x Cd Hx HCd HDer psi H0.
  pose proof (proj1 HDer psi H0 x 1 ltac:(lra) ltac:(lra)) as Hd.
  assert (H1 : GPsi psi 1 = ell psi).
  { unfold GPsi. destruct (Ch_eq_dec psi zero) as [E|E]; [contradiction|]. rewrite VS_one, ofR_one. ring. }
  rewrite H1, Rmax_left in Hd by lra. rewrite Rabs_pos_eq in Hd by lra.
  assert (H2 : nrm (GPsi psi x) <= nrm (GPsi psi x -' ell psi) + nrm (ell psi)).
  { replace (GPsi psi x) with ((GPsi psi x -' ell psi) +' ell psi) at 1 by ring. apply nrm_add. }
  pose proof (LOG_NONNEG x ltac:(lra)) as H3.
  pose proof (nrm_nonneg C (ell psi)).
  nra.
Qed.

Theorem one_char_r : forall (TT : list Hg) (y : Hg -> R) (x Cd c rho Ko L Rr : R),
  3 <= x -> 0 <= Cd -> (forall t, In t TT -> Rabs (y t - x) <= 1) -> DerivInt Cd ->
  0 <= rho -> 0 <= Ko -> In zero Kp ->
  (forall psi, In psi Kp -> ev psi sgc0 = k1) ->
  (forall psi, In psi Kp -> ~ (forall h, ev psi (inr h) = k1) ->
     nrm (ksum (map (fun t => ev psi (inr t)) TT) -' ofR c *' ofR (INR (length TT))) <= rho * INR (length TT)) ->
  (forall psi, In psi Kp -> psi <> zero -> nrm (ell psi) <= Ko) ->
  (forall psi, inPsiA psi -> ~ In psi Kp -> nrm (ell psi) <= L) ->
  Cd <= Rr -> lg (x + 1) + Cd + Ko + rho * (x * (lg x + Cd + Ko)) <= Rr ->
  lg (x + 1) + Cd + L <= Rr ->
  forall psi, inPsiA psi ->
    INR (length TT) * (vv c x psi - Rr) <= rsum (map (fun t => re (ev psi (e1 t) *' GPsi psi (y t))) TT).
Proof.
  intros TT y x Cd c rho Ko L Rr Hx HCd Hy HDer Hrho HKo H0K Hsg H2 HK H3 r1 r2 r3 psi Hpsi.
  pose proof (pos_INR (length TT)) as Hn.
  destruct (Ch_eq_dec psi zero) as [E0|E0].
  { (* psi = 0 *)
    subst psi.
    assert (Hw : wtA c zero = 1).
    { unfold wtA. assert (T : trivH zero = true) by (apply trivH_spec; intro h; apply ev_zero). rewrite T. reflexivity. }
    unfold vv. destruct (in_dec Ch_eq_dec zero Kp) as [_|N]; [|contradiction]. rewrite Hw, Rmult_1_l.
    apply rsum_ge_const. intros t Ht.
    destruct (abs_le_elim _ _ (Hy t Ht)) as [Hy1 Hy2].
    pose proof (proj2 HDer (y t) x ltac:(lra) ltac:(lra)) as HG.
    pose proof (Rmult_le_compat_l _ _ _ HCd (Hy t Ht)) as HG'.
    destruct (abs_le_elim _ _ (Rle_trans _ _ _ HG HG')) as [Hc1 _].
    unfold GPsi. destruct (Ch_eq_dec zero zero) as [_|N]; [|congruence].
    rewrite ev_zero, re_ofR. replace (k1 *' ofR (Gz (y t))) with (ofR (Gz (y t)) : K) by ring.
    rewrite re_ofR. lra. }
  destruct (in_dec Ch_eq_dec psi Kp) as [HX|HX].
  - (* psi kept, non-trivial *)
    unfold vv. destruct (in_dec Ch_eq_dec psi Kp) as [_|N]; [|contradiction].
    set (c' := wtA c psi).
    set (n := INR (length TT)).
    assert (H2' : nrm (ksum (map (fun t => ev psi (inr t)) TT) -' ofR c' *' ofR n) <= rho * n).
    { unfold c', wtA. destruct (trivH psi) eqn:Et.
      - pose proof (proj1 (trivH_spec psi) Et) as Htr.
        rewrite (ksum_map_ext C _ (fun _ => k1)) by (intros t _; apply Htr).
        rewrite ksum_const1, ofR_one. unfold n.
        replace (ofR (INR (length TT)) -' k1 *' ofR (INR (length TT))) with (k0 : K) by ring.
        rewrite nrm_zero. apply Rmult_le_pos; assumption.
      - apply H2; [exact HX|]. intro Hall. apply (proj2 (trivH_spec psi)) in Hall. congruence. }
    assert (hk : forall t, ev psi (e1 t) = ev psi (inr t)).
    { intro t. rewrite E1SPLIT, ev_add, (Hsg psi HX). ring. }
    rewrite (rsum_map_ext (fun t => re (ev psi (e1 t) *' GPsi psi (y t))) (fun t => re (ev psi (inr t) *' GPsi psi (y t))))
      by (intros t _; rewrite hk; reflexivity).
    set (Gx := GPsi psi x).
    set (Sp := ksum (map (fun t => ev psi (inr t)) TT)).
    assert (e : ksum (map (fun t => ev psi (inr t) *' GPsi psi (y t)) TT) -' ofR c' *' ofR n *' Gx
              = ksum (map (fun t => ev psi (inr t) *' (GPsi psi (y t) -' Gx)) TT) +' (Sp -' ofR c' *' ofR n) *' Gx).
    { assert (E1 : ksum (map (fun t => ev psi (inr t) *' (GPsi psi (y t) -' Gx)) TT)
                 = ksum (map (fun t => ev psi (inr t) *' GPsi psi (y t)) TT) -' Sp *' Gx).
      { unfold Sp.
        transitivity (ksum (map (fun t => ev psi (inr t) *' GPsi psi (y t) -' Gx *' ev psi (inr t)) TT)).
        - apply ksum_map_ext. intros t _. ring.
        - rewrite ksum_map_minus, ksum_map_scal. ring. }
      rewrite E1. ring. }
    pose proof (HK psi HX E0) as hl.
    assert (n1 : nrm (ksum (map (fun t => ev psi (inr t) *' (GPsi psi (y t) -' Gx)) TT)) <= n * (lg (x + 1) + Cd + Ko)).
    { eapply Rle_trans; [apply nrm_sum_le|]. unfold n. apply rsum_le_const. intros t Ht.
      rewrite nrm_mul, ev_nrm, Rmult_1_l.
      pose proof (move_r x Cd (y t) Hx HCd (Hy t Ht) HDer psi E0). unfold Gx. lra. }
    assert (n2 : nrm ((Sp -' ofR c' *' ofR n) *' Gx) <= rho * n * (x * (lg x + Cd + Ko))).
    { rewrite nrm_mul. apply Rmult_le_compat; [apply nrm_nonneg|apply nrm_nonneg|exact H2'|].
      pose proof (triv_r x Cd Hx HCd HDer psi E0). unfold Gx.
      assert (x * (lg x + Cd + nrm (ell psi)) <= x * (lg x + Cd + Ko)) by (apply Rmult_le_compat_l; lra). lra. }
    assert (n3 : nrm (ksum (map (fun t => ev psi (inr t) *' GPsi psi (y t)) TT) -' ofR c' *' ofR n *' Gx)
                 <= n * (lg (x + 1) + Cd + Ko) + rho * n * (x * (lg x + Cd + Ko))).
    { rewrite e. eapply Rle_trans; [apply nrm_add|]. lra. }
    pose proof (re_ge_neg_nrm C (ksum (map (fun t => ev psi (inr t) *' GPsi psi (y t)) TT) -' ofR c' *' ofR n *' Gx)) as n4.
    rewrite re_sub, re_sum in n4.
    assert (e2 : re (ofR c' *' ofR n *' Gx) = c' * n * re Gx).
    { rewrite <- ofR_mul, re_ofR_mul. reflexivity. }
    rewrite e2 in n4.
    pose proof (Rmult_le_compat_l _ _ _ Hn r2) as n5. fold n in n5.
    lra.
  - (* psi not kept *)
    unfold vv. destruct (in_dec Ch_eq_dec psi Kp) as [N|_]; [contradiction|].
    apply rsum_ge_const. intros t Ht.
    pose proof (H3 psi Hpsi HX) as k2.
    pose proof (move_r x Cd (y t) Hx HCd (Hy t Ht) HDer psi E0) as k3.
    assert (k4 : nrm (GPsi psi (y t)) <= nrm (GPsi psi x) + nrm (GPsi psi (y t) -' GPsi psi x)).
    { replace (GPsi psi (y t)) with (GPsi psi x +' (GPsi psi (y t) -' GPsi psi x)) at 1 by ring. apply nrm_add. }
    pose proof (re_ge_neg_nrm C (ev psi (e1 t) *' GPsi psi (y t))) as k5.
    rewrite nrm_mul, ev_nrm, Rmult_1_l in k5.
    lra.
Qed.
End OneChar.

Print Assumptions move_r.
Print Assumptions triv_r.
Print Assumptions one_char_r.

(* ===================================================================== *)
(* S2  th_le  (ChCore.lean : CharacterBalanceMoves.th_le, l.75)          *)
(* ===================================================================== *)
(* The thick-set average Th at b, A/b is at most De(A, w) (the balance
   term) plus 2 |Phi| (3 (x+1)(eta+1) + (x+1) b theta).  Lean steps: the
   bounds (x-1) b <= A <= (x+1) b; hTh, Th re-indexed over the index set
   S = univ.filter (not InPhi (g + topPl t)) with the thick indicator
   (thick_filter, thick_inj); hn, CR.norm_avg_le with the per-term bound
   by the thick / thin case split (LipW, ThinScales); e, De - Th as one
   average (CR.De_re); linarith. *)
Section ThLe.
Variable C : CStr.
Add Field KfT : (kfield C).
Local Notation K := (car C).

Variables (Hg G : Type) (hadd hsub : Hg -> Hg -> Hg) (gneg : G -> G) (e1 : Hg -> G).
Variable Ch : Type.
Variable Chars : list Ch.                         (* Finset.univ of AddChar (E0 x H) C *)
Variable ev : Ch -> G -> K.
Variable GPsi : Ch -> R -> K.
Variable fPl : R.                                 (* fPl H = |PhiSet| *)
Definition iPhi : K := kdiv k1 (ofR fPl).         (* 1 / (|PhiSet| : C) *)
Variables (T2 : list Hg) (u0 t : Hg).
Variable S : list G.                              (* univ.filter (fun g => not InPhi (g + topPl t)) *)
Variable pt : G -> G.                             (* g |-> cconj + g + topPl t *)
Variable inPhi : G -> Prop.
Variable thick : G -> bool.                       (* IsThickAt T2 u0, decided *)
(* [inventory] thick_filter + thick_inj (with Finset.sum_image): the thick
   part of S is the injective image of T2 under s |-> e1 (s + u0 - t). *)
Hypothesis THICK : Permutation (map (fun s => e1 (hsub (hadd s u0) t)) T2) (filter (fun g => thick (pt g)) S).
Hypothesis PT_PHI : forall g, In g S -> inPhi (pt g).        (* [inventory] CR.partner_inPhi *)
(* [inventory] CR.norm_avg_le, applied with CR.card_S_le t S *)
Hypothesis NORM_AVG : forall (F : G -> Ch -> K) (Kb : R), 0 <= Kb ->
  (forall g, In g S -> forall psi, nrm (F g psi) <= Kb) ->
  nrm (iPhi *' ksum (map (fun g => ksum (map (fun psi => ev psi (gneg g) *' F g psi) Chars)) S)) <= 2 * fPl * Kb.
Variable De : R -> (G -> R) -> K.                 (* De D ell A t w *)
(* [inventory] CR.De_re, unfolded balTop, CR.GC_host *)
Hypothesis DE_RE : forall A w, re (De A w) =
  re (iPhi *' ksum (map (fun g => ksum (map (fun psi =>
        ev psi (gneg g) *' ofR (w (pt g)) *' GPsi psi (A / w (pt g))) Chars)) S)).

(* Th (ChCore.lean l.18) *)
Definition Th (b y : R) : K :=
  iPhi *' ksum (map (fun s => ksum (map (fun psi =>
    ev psi (gneg (e1 (hsub (hadd s u0) t))) *' (ofR b *' GPsi psi y)) Chars)) T2).
(* ThinScales, LipW (GrowthBoundGivesRiemannHypothesis.lean l.55, l.58) *)
Definition ThinScales (X' th : R) : Prop := forall psi y, X' / 3 <= y -> nrm (GPsi psi y) <= y * th.
Definition LipW : Prop := forall psi A w w', 0 < A -> 0 < w -> 0 < w' ->
  nrm (ofR w *' GPsi psi (A / w) -' ofR w' *' GPsi psi (A / w')) <= 3 * A / Rmin w w' * Rabs (w - w').

Theorem th_le_r : forall (x b b' eta X' th A : R) (w : G -> R),
  3 <= x -> 0 < b -> 0 <= eta -> 0 < X' -> 0 < b' -> b' * X' <= x * b -> 0 <= th ->
  Rabs (A / b - x) <= 1 -> (forall r, inPhi r -> 0 < w r) ->
  (forall r, thick r = true -> b <= w r /\ w r <= b + eta + 1) ->
  (forall r, inPhi r -> thick r = false -> w r <= 2 * b') ->
  ThinScales X' th -> LipW ->
  re (Th b (A / b)) <= re (De A w) + 2 * fPl * (3 * (x + 1) * (eta + 1) + (x + 1) * b * th).
Proof.
  intros x b b' eta X' th A w Hx Hb Heta HX' Hb' HbX Hth HA Hwpos Hwthick Hwthin HThin HLip.
  destruct (abs_le_elim _ _ HA) as [h1 h2].
  assert (EA : A = A / b * b) by (field; lra).
  assert (hA1 : (x - 1) * b <= A) by (rewrite EA; apply Rmult_le_compat_r; lra).
  assert (hA2 : A <= (x + 1) * b) by (rewrite EA; apply Rmult_le_compat_r; lra).
  assert (hA0 : 0 < A) by nra.
  (* hTh *)
  assert (hTh : Th b (A / b) = iPhi *' ksum (map (fun g => ksum (map (fun psi =>
      ev psi (gneg g) *' (if thick (pt g) then ofR b *' GPsi psi (A / b) else k0)) Chars)) S)).
  { unfold Th. f_equal.
    set (F := fun g => ksum (map (fun psi => ev psi (gneg g) *' (ofR b *' GPsi psi (A / b))) Chars)).
    transitivity (ksum (map F (map (fun s => e1 (hsub (hadd s u0) t)) T2))); [rewrite map_map; reflexivity|].
    rewrite (ksum_perm C _ _ (Permutation_map F THICK)), <- ksum_filter.
    apply ksum_map_ext. intros g _. unfold F. destruct (thick (pt g)); [reflexivity|].
    symmetry. apply ksum_zero. intros psi _. ring. }
  set (Kb := 3 * (x + 1) * (eta + 1) + (x + 1) * b * th).
  assert (p1 : 0 <= 3 * (x + 1) * (eta + 1)) by (apply Rmult_le_pos; lra).
  assert (p2 : 0 <= (x + 1) * b * th) by (apply Rmult_le_pos; [apply Rmult_le_pos|]; lra).
  set (F := fun g psi => ofR (w (pt g)) *' GPsi psi (A / w (pt g))
                         -' (if thick (pt g) then ofR b *' GPsi psi (A / b) else k0)).
  assert (hn : nrm (iPhi *' ksum (map (fun g => ksum (map (fun psi => ev psi (gneg g) *' F g psi) Chars)) S))
               <= 2 * fPl * Kb).
  { apply NORM_AVG; [unfold Kb; lra|]. intros g Hgi psi.
    pose proof (PT_PHI g Hgi) as Hr. pose proof (Hwpos _ Hr) as Hw0. unfold F.
    destruct (thick (pt g)) eqn:Eth.
    - destruct (Hwthick _ Eth) as [k1' k2'].
      pose proof (HLip psi A (w (pt g)) b hA0 Hw0 Hb) as hl.
      rewrite Rmin_right in hl by exact k1'. rewrite Rabs_pos_eq in hl by lra.
      assert (e1' : 3 * A / b <= 3 * (x + 1)).
      { replace (3 * A / b) with (3 * (A / b)) by (field; lra). lra. }
      assert (Hpos : 0 <= 3 * A / b).
      { replace (3 * A / b) with (3 * (A / b)) by (field; lra).
        assert (0 < A / b) by (apply Rdiv_lt_0_compat; lra). lra. }
      assert (e2' : 3 * A / b * (w (pt g) - b) <= 3 * (x + 1) * (eta + 1)).
      { apply Rmult_le_compat; lra. }
      unfold Kb. lra.
    - pose proof (Hwthin _ Hr Eth) as Hw2.
      replace (ofR (w (pt g)) *' GPsi psi (A / w (pt g)) -' k0) with (ofR (w (pt g)) *' GPsi psi (A / w (pt g))) by ring.
      assert (Hy : X' / 3 <= A / w (pt g)).
      { assert (k1' : X' / 3 * w (pt g) <= X' / 3 * (2 * b')) by (apply Rmult_le_compat_l; lra).
        assert (k2' : X' / 3 * w (pt g) <= A) by nra.
        apply Rmult_le_reg_r with (w (pt g)); [exact Hw0|].
        replace (A / w (pt g) * w (pt g)) with A by (field; lra). exact k2'. }
      pose proof (HThin psi _ Hy) as Ht'.
      rewrite nrm_mul, nrm_ofR, Rabs_pos_eq by lra.
      assert (Hc : w (pt g) * nrm (GPsi psi (A / w (pt g))) <= w (pt g) * (A / w (pt g) * th))
        by (apply Rmult_le_compat_l; lra).
      replace (w (pt g) * (A / w (pt g) * th)) with (A * th) in Hc by (field; lra).
      assert (A * th <= (x + 1) * b * th) by (apply Rmult_le_compat_r; lra).
      unfold Kb. lra. }
  pose proof (re_ge_neg_nrm C (iPhi *' ksum (map (fun g => ksum (map (fun psi => ev psi (gneg g) *' F g psi) Chars)) S))) as hre.
  assert (e : re (De A w) - re (Th b (A / b)) =
              re (iPhi *' ksum (map (fun g => ksum (map (fun psi => ev psi (gneg g) *' F g psi) Chars)) S))).
  { rewrite DE_RE, hTh, <- re_sub. f_equal.
    transitivity (iPhi *' (ksum (map (fun g => ksum (map (fun psi =>
        ev psi (gneg g) *' ofR (w (pt g)) *' GPsi psi (A / w (pt g))) Chars)) S)
      -' ksum (map (fun g => ksum (map (fun psi =>
        ev psi (gneg g) *' (if thick (pt g) then ofR b *' GPsi psi (A / b) else k0)) Chars)) S))); [ring|].
    f_equal. rewrite <- ksum_map_minus. apply ksum_map_ext. intros g _.
    rewrite <- ksum_map_minus. apply ksum_map_ext. intros psi _. unfold F. ring. }
  lra.
Qed.
End ThLe.

Print Assumptions th_le_r.

(* ===================================================================== *)
(* S3  ch_balance  (LandauTheorems/ChBalance.lean : ch_balance, l.200)    *)
(* ===================================================================== *)
(* (ASK : C) - MAIN = De.  Lean steps: rewrite ASK by askExp; per (g, psi)
   evaluate the von Mangoldt sum by sum_cut and inner_eq (hin); split the
   double sum; identify the first part with De (hDe); split off the trivial
   character (hsplit, Finset.add_sum_erase); collapse the non-trivial
   characters by colour_sum (hcol); sum the real parts by card_notPhi and
   sum_partner (hreal); field_simp; ring. *)
Section ChBalance.
Variable C : CStr.
Add Field KfB : (kfield C).
Local Notation K := (car C).

Variables (G Ch : Type).
Hypothesis Ch_eq_dec : forall a b : Ch, {a = b} + {a <> b}.          (* [Mathlib] DecidableEq (classical) *)
Variables (zero chC : Ch).
Variable Chars : list Ch.                                            (* Finset.univ *)
Hypothesis Chars_nd : NoDup Chars.                                   (* [Mathlib] Finset.univ is a Finset *)
Hypothesis Chars_all : forall psi, In psi Chars.                     (* [Mathlib] Finset.mem_univ *)
Hypothesis chC_nz : chC <> zero.                                     (* [inventory] PB.chC_ne_zero *)
Variable cv : Ch -> G -> K.                                          (* starRingEnd C (psi g) *)
Hypothesis cv_zero : forall g, cv zero g = k1.                       (* [Mathlib] AddChar.zero_apply, map_one *)
Variables (S PhiL : list G).            (* univ.filter (fun g => not InPhi g), PhiSet *)
Variable pt : G -> G.                   (* partner t *)
Variable inPhi : G -> Prop.
Variables (lg : R -> R) (gam : R).      (* Real.log, Real.eulerMascheroniConstant *)
Variables (ell : Ch -> K) (GPsi : Ch -> R -> K).
Variables (a : R) (w : G -> R) (Nn : nat) (ASKv : R).
(* VN psi W = sum_{n in Icc 1 N} Lambda n primVal psi n (max (a/n - W) 0),
   VF psi W = sum_{n in Icc 1 floor(a/W)} Lambda n primVal psi n (a/n - W) *)
Variables (VN VF : Ch -> R -> K).
Definition fPlB : R := INR (length PhiL).
Definition nPhiK : K := ofR fPlB.
Definition iPhiB : K := kdiv k1 nPhiK.
Hypothesis PT_PHI : forall g, In g S -> inPhi (pt g).               (* [inventory] partner_inPhi *)
(* [inventory] CharacterBalance.askExp (ChBalance.lean l.122) *)
Hypothesis ASKEXP : (forall r, inPhi r -> 0 < w r) -> (forall r, inPhi r -> a / w r <= INR Nn) ->
  ofR ASKv = iPhiB *' ksum (map (fun g => ksum (map (fun psi => cv psi g *' VN psi (w (pt g))) Chars)) S).
Hypothesis SUM_CUT : forall psi W, 0 < a -> 0 < W -> a / W <= INR Nn -> VN psi W = VF psi W.   (* [inventory] sum_cut *)
Hypothesis INNER : forall psi W, 0 < a -> 0 < W ->                                             (* [inventory] inner_eq *)
  VF psi W = ofR W *' GPsi psi (a / W) +'
    (if Ch_eq_dec psi zero then ofR (a * lg a - a * lg W - (1 + gam) * a) else kopp (ofR a) *' ell psi).
(* [inventory] colour_sum (ColourSum, FirstPrimeNeSecondPrime.lean l.123) *)
Hypothesis COLOUR : forall psi, ksum (map (cv psi) S) =
  if Ch_eq_dec psi zero then nPhiK else if Ch_eq_dec psi chC then kopp nPhiK else k0.
Hypothesis SUMP : forall F : G -> R, rsum (map (fun g => F (pt g)) S) = rsum (map F PhiL).      (* [inventory] sum_partner *)
Hypothesis PHI_NZ : length PhiL <> O.                                                          (* [inventory] PB.phi_card_ne_zero *)

(* De, MAIN (FirstPrimeNeSecondPrime.lean l.93, l.89) *)
Definition DeB : K :=
  iPhiB *' ksum (map (fun g => ksum (map (fun psi => cv psi g *' ofR (w (pt g)) *' GPsi psi (a / w (pt g))) Chars)) S).
Definition MAINB : K :=
  ofR a *' (ofR (lg a - 1 - gam) +' ell chC -' ofR (1 / fPlB * rsum (map (fun r => lg (w r)) PhiL))).

Theorem ch_balance_r : 0 < a -> (forall r, inPhi r -> 0 < w r) -> (forall r, inPhi r -> a / w r <= INR Nn) ->
  ofR ASKv -' MAINB = DeB.
Proof.
  intros Ha Hw HN.
  assert (hfr : fPlB <> 0) by (unfold fPlB; apply not_0_INR; exact PHI_NZ).
  assert (hf0 : nPhiK <> k0) by (unfold nPhiK; intro E; apply hfr; exact (ofR_eq0 C _ E)).
  rewrite (ASKEXP Hw HN).
  set (r := fun g => a * lg a - a * lg (w (pt g)) - (1 + gam) * a).
  set (Y := fun g psi => cv psi g *' (if Ch_eq_dec psi zero then ofR (r g) else kopp (ofR a) *' ell psi)).
  set (X := fun g psi => cv psi g *' (ofR (w (pt g)) *' GPsi psi (a / w (pt g)))).
  (* hin *)
  assert (hin : ksum (map (fun g => ksum (map (fun psi => cv psi g *' VN psi (w (pt g))) Chars)) S)
              = ksum (map (fun g => ksum (map (fun psi => X g psi) Chars)) S)
                +' ksum (map (fun g => ksum (map (fun psi => Y g psi) Chars)) S)).
  { rewrite <- ksum_map_plus. apply ksum_map_ext. intros g Hg. rewrite <- ksum_map_plus.
    apply ksum_map_ext. intros psi _.
    pose proof (Hw _ (PT_PHI g Hg)) as HW.
    rewrite (SUM_CUT psi _ Ha HW (HN _ (PT_PHI g Hg))), (INNER psi _ Ha HW).
    unfold X, Y, r. ring. }
  rewrite hin.
  (* hDe *)
  assert (hDe : iPhiB *' ksum (map (fun g => ksum (map (fun psi => X g psi) Chars)) S) = DeB).
  { unfold DeB. f_equal. apply ksum_map_ext. intros g _. apply ksum_map_ext. intros psi _. unfold X. ring. }
  (* hsplit *)
  set (Cnz := remove Ch_eq_dec zero Chars).
  assert (Hperm : Permutation Chars (zero :: Cnz)) by (apply perm_remove; [exact Chars_nd|apply Chars_all]).
  assert (hsplit : forall g, ksum (map (fun psi => Y g psi) Chars)
                   = ofR (r g) +' ksum (map (fun psi => cv psi g *' (kopp (ofR a) *' ell psi)) Cnz)).
  { intro g. rewrite (ksum_perm C _ _ (Permutation_map (fun psi => Y g psi) Hperm)). simpl.
    unfold Y at 1. rewrite cv_zero. destruct (Ch_eq_dec zero zero) as [_|N]; [|congruence].
    f_equal; [ring|]. apply ksum_map_ext. intros psi Hpsi. unfold Y.
    destruct (in_remove Ch_eq_dec Chars psi zero Hpsi) as [_ Hne].
    destruct (Ch_eq_dec psi zero) as [E|_]; [contradiction|reflexivity]. }
  rewrite (ksum_map_ext C _ _ S (fun g _ => hsplit g)), ksum_map_plus.
  (* hcol *)
  assert (hcol : ksum (map (fun g => ksum (map (fun psi => cv psi g *' (kopp (ofR a) *' ell psi)) Cnz)) S)
                 = nPhiK *' (ofR a *' ell chC)).
  { rewrite ksum_swap.
    assert (Hnd : NoDup (zero :: Cnz)) by (exact (Permutation_NoDup Hperm Chars_nd)).
    inversion Hnd as [|z l Hz HndC E]; subst z l.
    assert (HinC : In chC Cnz) by (apply in_in_remove; [exact chC_nz|apply Chars_all]).
    transitivity (ksum (map (fun psi => if Ch_eq_dec psi chC then kopp nPhiK *' (kopp (ofR a) *' ell psi) else k0) Cnz)).
    - apply ksum_map_ext. intros psi Hpsi.
      destruct (in_remove Ch_eq_dec Chars psi zero Hpsi) as [_ Hne].
      transitivity (ksum (map (cv psi) S) *' (kopp (ofR a) *' ell psi)).
      + transitivity (ksum (map (fun g => (kopp (ofR a) *' ell psi) *' cv psi g) S)).
        * apply ksum_map_ext. intros g _. ring.
        * rewrite ksum_map_scal. ring.
      + rewrite COLOUR. destruct (Ch_eq_dec psi zero) as [E|_]; [contradiction|].
        destruct (Ch_eq_dec psi chC); ring.
    - rewrite (ksum_ite_eq C Ch_eq_dec chC (fun psi => kopp nPhiK *' (kopp (ofR a) *' ell psi)) Cnz HndC HinC). ring. }
  rewrite hcol.
  (* hreal *)
  assert (hcard : INR (length S) = fPlB).
  { pose proof (SUMP (fun _ => 1)) as H1. rewrite !rsum_const in H1. unfold fPlB. lra. }
  assert (hreal : ksum (map (fun g => (ofR (r g) : K)) S)
                  = ofR (fPlB * (a * lg a - (1 + gam) * a) - a * rsum (map (fun x => lg (w x)) PhiL))).
  { rewrite ksum_ofR. f_equal.
    rewrite (rsum_map_ext r (fun g => (a * lg a - (1 + gam) * a) - a * (fun x => lg (w x)) (pt g))) by (intros g _; unfold r; ring).
    rewrite rsum_minus, rsum_const, rsum_scal, (SUMP (fun x => lg (w x))), hcard. ring. }
  rewrite hreal.
  rewrite <- hDe.
  (* field_simp; ring *)
  assert (hR : ofR (fPlB * (a * lg a - (1 + gam) * a) - a * rsum (map (fun x => lg (w x)) PhiL))
               = nPhiK *' (ofR a *' ofR (lg a - 1 - gam) -' ofR a *' ofR (1 / fPlB * rsum (map (fun x => lg (w x)) PhiL))) :> K).
  { unfold nPhiK. rewrite <- !ofR_mul, <- ofR_sub, <- ofR_mul. f_equal. field. exact hfr. }
  rewrite hR. unfold MAINB, iPhiB. field. exact hf0.
Qed.
End ChBalance.

Print Assumptions ch_balance_r.

(* ===================================================================== *)
(* Shared size definitions (ErrorFormsWeakWindowsFalse.lean)            *)
(* ===================================================================== *)
(* lg = Real.log, rp = Real.rpow, both abstract. *)
Definition KBig (K cHH eK : R) : R := 200 * (1 + K) ^ 2 * (1 + cHH) * (1 + eK).                 (* l.21 *)
Definition LargeX (lg : R -> R) (rp : R -> R -> R) (x eps K cHH eK : R) : Prop :=              (* l.52 *)
  lg x <= rp x eps /\ KBig K cHH eK <= rp x eps.
Definition LargeXEv (lg : R -> R) (rp : R -> R -> R) : Prop :=                                 (* l.77 *)
  forall eps K cHH eK, 0 < eps -> exists x0, forall x, x0 <= x -> LargeX lg rp x eps K cHH eK.
Definition errorBracketSizeWindows (rp : R -> R -> R) (x eps : R) (n nT nT2 m : nat) (b k aE : R) : R :=  (* l.133 *)
  INR nT * aE * (1 + INR m ^ 2 / k)
  + INR m * ((2 * INR n) * INR m * b * rp x eps + INR nT2 * k * b * rp x eps / (INR n * (INR n * rp x (- eps)))).

(* ===================================================================== *)
(* S4  ch_top  (LandauTheorems/ChTop.lean : ch_top, l.37;                 *)
(*     ch_top_main_eq, l.11)                                             *)
(* ===================================================================== *)
(* gapA (tr u) <= x^(CErr eps) * errorBracketSizeWindows ...  Lean steps:
   ch_top_main_eq (Data.Main re-indexed through eT : Top = TT and
   eP : Fin f = PhiSet, Re MAIN computed); hgap (gapA = ASK - Main via
   IdentU); each_unit_bound_statement; errX5at_le; nT = |TT|; ErrText <=
   bracket by BNBoundsU (gcongr); rpow_nonneg; calc. *)
Section ChTop.
Variable C : CStr.
Add Field KfC : (kfield C).
Local Notation K := (car C).

Variables (Hg G U0 Top : Type).
Variables (lg : R -> R) (rp : R -> R -> R) (gamma : R) (ellC : K).   (* log, rpow, Euler gamma, ell chC *)
Hypothesis RPOW_NONNEG : forall x y, 0 <= x -> 0 <= rp x y.          (* [Mathlib] Real.rpow_nonneg *)
Variables (TopL : list Top) (TT T2 : list Hg) (eT : Top -> Hg).
Variables (f m nH : nat) (eP : nat -> G) (PhiL : list G) (tr : U0 -> Hg).
Hypothesis EQT : Permutation (map eT TopL) TT.        (* eT : Top = TT   ([Mathlib] Equiv.sum_comp, Fintype.card_congr) *)
Hypothesis EQP : Permutation (map eP (seq 0 f)) PhiL. (* eP : Fin f = PhiSet ([Mathlib] Equiv.sum_comp, Fintype.card_congr) *)
(* the fields of Dd : Data U0 W Top m f that the proof touches *)
Variables (aT : Top -> R) (wD : U0 -> nat -> nat -> R) (gam LpL : R) (ASKD : U0 -> R).
Variables (xD epsD bD kD aD B0 Nc : R).
Variables (ASK : R -> Hg -> (G -> R) -> R) (a : Hg -> R) (w : Hg -> nat -> G -> R).

Definition nTD : R := INR (length TopL).                                        (* Data.nT *)
Definition MainD (u0 : U0) : R :=                                               (* Data.Main *)
  rsum (map (fun j => rsum (map (fun tau => aT tau * (lg (aT tau) - 1 - gam + LpL
     - (1 / INR f) * rsum (map (fun r => lg (wD u0 j r)) (seq 0 f)))) TopL)) (seq 0 m)).
Definition MAINT (a0 : R) (wf : G -> R) : K :=                                  (* MAIN *)
  ofR a0 *' (ofR (lg a0 - 1 - gamma) +' ellC -' ofR (1 / INR (length PhiL) * rsum (map (fun r => lg (wf r)) PhiL))).
Definition gapAT (u0 : Hg) : R :=                                               (* gapA *)
  rsum (map (fun t => rsum (map (fun j => ASK (a t) t (w u0 j) - re (MAINT (a t) (w u0 j))) (seq 0 m))) TT).
Definition IdentU : Prop :=                                                     (* SplitInertia.lean l.67 *)
  (forall tau, aT tau = a (eT tau)) /\
  (forall u j r, (j < m)%nat -> (r < f)%nat -> wD u j r = w (tr u) j (eP r)) /\
  gam = gamma /\ LpL = re ellC /\
  (forall u, ASKD u = rsum (map (fun t => rsum (map (fun j => ASK (a t) t (w (tr u) j)) (seq 0 m))) TT)).
Definition ErrText : R := nTD * aD * (1 + INR m ^ 2 / kD) + INR m * (B0 + Nc).
Definition BNBoundsU : Prop :=
  B0 <= (2 * INR nH) * INR m * bD * rp xD epsD /\
  Nc <= INR (length T2) * kD * bD * rp xD epsD / (INR nH * (INR nH * rp xD (- epsD))).
Variables (SD2 ErrW : Prop) (ErrX5 : U0 -> R) (cerr Kc cHH eK : R).
(* [inventory] each_unit_bound_statement (PointwiseBoundVariant), from SizeData₂ *)
Hypothesis EACH : SD2 -> forall u, ASKD u <= MainD u + ErrX5 u.
Hypothesis SD2_X : SD2 -> 0 < xD.            (* [inventory] SizeData₂ -> HidaSetting (first conjunct) *)
(* [inventory] errX5at_le *)
Hypothesis ERRX5 : ErrW -> LargeX lg rp xD epsD Kc cHH eK -> forall u, ErrX5 u <= rp xD (cerr * epsD) * ErrText.

Lemma ch_top_main_eq_r : IdentU -> forall u0,
  MainD u0 = rsum (map (fun t => rsum (map (fun j => re (MAINT (a t) (w (tr u0) j))) (seq 0 m))) TT).
Proof.
  intros [ha [hw [hg [hL _]]]] u0.
  assert (hf : INR f = INR (length PhiL)).
  { rewrite <- (Permutation_length EQP), length_map, length_seq. reflexivity. }
  assert (hsum : forall j, In j (seq 0 m) ->
            rsum (map (fun r => lg (wD u0 j r)) (seq 0 f)) = rsum (map (fun x => lg (w (tr u0) j x)) PhiL)).
  { intros j Hj. apply in_seq in Hj.
    rewrite (rsum_map_ext _ (fun r => (fun x => lg (w (tr u0) j x)) (eP r)))
      by (intros r Hr; apply in_seq in Hr; rewrite hw by lia; reflexivity).
    rewrite <- (map_map eP (fun x => lg (w (tr u0) j x))).
    apply rsum_perm, Permutation_map, EQP. }
  unfold MainD.
  rewrite (rsum_map_ext _ (fun j => rsum (map (fun tau => (fun t => a t * (lg (a t) - 1 - gamma + re ellC
              - (1 / INR (length PhiL)) * rsum (map (fun x => lg (w (tr u0) j x)) PhiL))) (eT tau)) TopL)))
    by (intros j Hj; apply rsum_map_ext; intros tau _; rewrite ha, (hsum j Hj), hg, hL, hf; reflexivity).
  rewrite rsum_swap.
  assert (Hre : forall H : Hg -> R, rsum (map (fun tau => H (eT tau)) TopL) = rsum (map H TT))
    by (intro H; rewrite <- (map_map eT H); apply rsum_perm, Permutation_map, EQT).
  etransitivity; [apply (Hre (fun t => rsum (map (fun j => a t * (lg (a t) - 1 - gamma + re ellC
              - (1 / INR (length PhiL)) * rsum (map (fun x => lg (w (tr u0) j x)) PhiL))) (seq 0 m))))|].
  apply rsum_map_ext. intros t _. apply rsum_map_ext. intros j _.
  unfold MAINT. rewrite re_ofR_mul, re_sub, re_add, !re_ofR. ring.
Qed.

Theorem ch_top_r : IdentU -> SD2 -> ErrW -> BNBoundsU -> LargeX lg rp xD epsD Kc cHH eK -> forall u,
  gapAT (tr u) <= rp xD (cerr * epsD) * errorBracketSizeWindows rp xD epsD nH (length TT) (length T2) m bD kD aD.
Proof.
  intros h1 h2 h3 h4 h5 u.
  pose proof (ch_top_main_eq_r h1 u) as hmain.
  pose proof (proj2 (proj2 (proj2 (proj2 h1))) u) as hask.
  assert (hgap : gapAT (tr u) = ASKD u - MainD u).
  { rewrite hask, hmain. unfold gapAT. rewrite <- rsum_minus. apply rsum_map_ext. intros t _.
    rewrite <- rsum_minus. reflexivity. }
  pose proof (EACH h2 u) as hle.
  pose proof (ERRX5 h3 h5 u) as herr.
  assert (hnT : nTD = INR (length TT)) by (unfold nTD; rewrite <- (Permutation_length EQT), length_map; reflexivity).
  assert (htext : ErrText <= errorBracketSizeWindows rp xD epsD nH (length TT) (length T2) m bD kD aD).
  { unfold ErrText, errorBracketSizeWindows. rewrite hnT. destruct h4 as [b1 b2].
    pose proof (pos_INR m) as hm.
    assert (INR m * (B0 + Nc) <= INR m * ((2 * INR nH) * INR m * bD * rp xD epsD
              + INR (length T2) * kD * bD * rp xD epsD / (INR nH * (INR nH * rp xD (- epsD)))))
      by (apply Rmult_le_compat_l; lra).
    lra. }
  pose proof (RPOW_NONNEG xD (cerr * epsD) ltac:(pose proof (SD2_X h2); lra)) as hpow.
  rewrite hgap.
  assert (rp xD (cerr * epsD) * ErrText <= rp xD (cerr * epsD) * errorBracketSizeWindows rp xD epsD nH (length TT) (length T2) m bD kD aD)
    by (apply Rmult_le_compat_l; assumption).
  lra.
Qed.
End ChTop.

Print Assumptions ch_top_main_eq_r.
Print Assumptions ch_top_r.

(* ===================================================================== *)
(* S5  gmA_eq  (PrimitiveCosets/GmAEq.lean : gmA_eq, l.61), with the      *)
(*     private gmA_eq_triv (l.16)                                        *)
(* ===================================================================== *)
(* GmA (keptA) ((3 o + 1)^-1) y = Lambda.Gm y.  Lean steps: hXp, hKimg and
   hinj (the kept host characters are an injective image of Lambda.KEPT,
   via chr_bij, prim_inj, EAtH.kept); hw (the weights agree, through
   htriv = gmA_eq_triv + character_trivial_on_generator_iff and EAtH.ps);
   hG (prim_read); key (Finset.sum_image); split off PChar.one
   (Finset.add_sum_erase, hone, Gz_eq).
   gmA_eq_triv: a character theta of GG = (Z^x x Z^x) x MA trivial on
   iod is trivial on tau1(A) iff theta = 1 or theta = psC: hM, hB, the
   factorisation hred, theta(sg)^2 = 1, mul_self_eq_one_iff.  Z^x is
   modelled by bool (true = -1): [Mathlib] Int.units_eq_one_or. *)
Section GmA.
Variable C : CStr.
Add Field KfG : (kfield C).
Local Notation K := (car C).

Hypothesis MUL_SELF : forall v : K, v *' v = k1 -> v = k1 \/ v = kopp k1.   (* [Mathlib] mul_self_eq_one_iff *)
(* GG = G0 x MA, G0 = Z^x x Z^x *)
Variable Am : Type.                                   (* MA = Multiplicative A *)
Variables (aadd : Am -> Am -> Am) (azero : Am).
Hypothesis A_zero_l : forall m, aadd azero m = m.     (* [Mathlib] one_mul *)
Definition GG : Type := (bool * bool * Am)%type.
Definition gmul (g h : GG) : GG :=
  let '(a, b, m) := g in let '(a', b', m') := h in (xorb a a', xorb b b', aadd m m').
Definition gone : GG := (false, false, azero).
Definition tau1 (s : Am) : GG := (false, false, s).   (* Frame.tau1 *)
Definition iod : GG := (false, true, azero).          (* Frame.iod *)
Definition sg : GG := (true, false, azero).           (* Frame.sg *)
Variable ThC : Type.                                  (* phi.Char = GG ->* C^x *)
Variable tv : ThC -> GG -> K.
Hypothesis tv_mul : forall th g h, tv th (gmul g h) = tv th g *' tv th h.   (* [Mathlib] map_mul *)
Hypothesis tv_one : forall th, tv th gone = k1.                           (* [Mathlib] map_one *)
Hypothesis th_ext : forall th th', (forall g, tv th g = tv th' g) -> th = th'.   (* [Mathlib] MonoidHom.ext, Units.ext *)
Variables (oneC psC : ThC).
Hypothesis tv_oneC : forall g, tv oneC g = k1.                            (* [Mathlib] MonoidHom.one_apply *)
(* psC = Int.cast o chQ, chQ = first Z^x coordinate (Frame.psC, Frame.chQ) *)
Hypothesis tv_psC : forall g, tv psC g = if fst (fst g) then kopp k1 else k1.   (* [inventory] Frame.psC / Frame.chQ (definitional) *)

Theorem gmA_eq_triv_r : forall th, tv th iod = k1 ->
  ((forall h, tv th (tau1 h) = k1) <-> th = oneC \/ th = psC).
Proof.
  intros th hi. split.
  - intro h.
    assert (hM : forall m, tv th (false, false, m) = k1) by (intro m; exact (h m)).
    assert (hB : forall b, tv th (false, b, azero) = k1) by (intros [|]; [exact hi|exact (tv_one th)]).
    assert (hred : forall a b m, tv th (a, b, m) = tv th (a, false, azero)).
    { intros a b m.
      assert (e : (a, b, m) = gmul (gmul (a, false, azero) (false, b, azero)) (false, false, m)).
      { simpl. rewrite !A_zero_l. destruct a, b; reflexivity. }
      rewrite e, !tv_mul, hM, hB. ring. }
    assert (hsq : tv th sg *' tv th sg = k1).
    { rewrite <- tv_mul. replace (gmul sg sg) with gone by (simpl; rewrite A_zero_l; reflexivity). apply tv_one. }
    destruct (MUL_SELF _ hsq) as [h1|h1].
    + left. apply th_ext. intros [[a b] m]. rewrite hred, tv_oneC.
      destruct a; [exact h1|exact (hB false)].
    + right. apply th_ext. intros [[a b] m]. rewrite hred, tv_psC. simpl.
      destruct a; [exact h1|exact (hB false)].
  - intros [E|E] h; subst th; [apply tv_oneC|rewrite tv_psC; reflexivity].
Qed.

(* the host side *)
Variables (Ach PC : Type).                            (* AddChar (E0 x A) C, PChar *)
Variable chr : Ach -> ThC.
Hypothesis chr_inj : forall p q, chr p = chr q -> p = q.          (* [inventory] chr_bij (injective) *)
Hypothesis chr_surj : forall th, exists p, chr p = th.            (* [inventory] chr_bij (surjective) *)
Variable prim : ThC -> PC.                                        (* H.prim *)
Variable oneP : PC.                                               (* PChar.one *)
Hypothesis prim_inj : forall th th', prim th = prim th' -> th = th'.   (* [inventory] prim_inj (.1) *)
Hypothesis prim_one : prim oneC = oneP.                                (* [inventory] prim_inj (.2) *)
Hypothesis PC_eq_dec : forall p q : PC, {p = q} + {p <> q}.            (* [Mathlib] DecidableEq (classical) *)
Variable KEPT : list PC.                                               (* Lambda.KEPT *)
Hypothesis KEPT_nd : NoDup KEPT.                                       (* [Mathlib] Finset *)
Hypothesis one_mem : In oneP KEPT.                                     (* [inventory] Level.one_mem *)
Variable keptL : list Ach.                                             (* keptA Lambda H *)
Hypothesis keptL_nd : NoDup keptL.                                     (* [Mathlib] Finset *)
Hypothesis hmem : forall p, In p keptL <-> In (prim (chr p)) KEPT.     (* [inventory] keptA, HostRaw.kept_iff *)
Variable inXp : ThC -> Prop.                                           (* phi.Xp *)
Hypothesis Xp_iod : forall th, inXp th -> tv th iod = k1.              (* [inventory] Frame.Xp (second conjunct) *)
Hypothesis hE_kept : forall p, In p KEPT -> exists th, inXp th /\ prim th = p.   (* [inventory] EAtH.kept, HostRaw.isPrimOf_iff *)
Variable psK : option PC.                                              (* Lambda.psK *)
Hypothesis hps1 : forall p, psK = Some p -> prim psC = p.             (* [inventory] EAtH.ps (.1), isPrimOf_iff *)
Hypothesis hps2 : psK = None -> ~ In (prim psC) KEPT.                 (* [inventory] EAtH.ps (.2), kept_iff *)
Variables (G : Type) (ev : Ach -> G -> K) (inr : Am -> G).             (* psi, (0, s) *)
Hypothesis GEN_IFF : forall p s, tv (chr p) (tau1 s) = k1 <-> ev p (inr s) = k1.   (* [inventory] character_trivial_on_generator_iff *)
Variable trivH : Ach -> bool.                                          (* `forall h, psi (0, h) = 1`, decided *)
Hypothesis trivH_spec : forall p, trivH p = true <-> (forall h, ev p (inr h) = k1).
Variable o : nat.                                                      (* Lambda.o *)
Definition cw : R := / (3 * INR o + 1).
Definition wtG (p : Ach) : R := if trivH p then 1 else cw.            (* wtA ((3 o + 1)^-1) *)
Definition lwt (p : PC) : R :=                                         (* Level.wt *)
  match psK with Some q => if PC_eq_dec q p then 1 else cw | None => cw end.
Variables (GPsi : Ach -> R -> K) (gch : PC -> R -> K) (Gz AG : R -> R).
Hypothesis PRIM_READ : forall p y, re (GPsi p y) = re (gch (prim (chr p)) y).   (* [inventory] prim_read (.2) *)
Hypothesis GCH_ONE : forall y, re (gch oneP y) = AG y.     (* [inventory] An.gChi at PChar.one (Lean hone) *)
Hypothesis GZ_EQ : forall y, Gz y = AG y.                  (* [inventory] Gz_eq (.1) *)
Definition GmAG (y : R) : R := rsum (map (fun p => wtG p * re (GPsi p y)) keptL).            (* GmA *)
Definition LevelGm (y : R) : R :=                                                             (* Level.Gm, Nt = KEPT.erase one *)
  Gz y + rsum (map (fun p => lwt p * re (gch p y)) (remove PC_eq_dec oneP KEPT)).

Theorem gmA_eq_r : forall y, GmAG y = LevelGm y.
Proof.
  intro y.
  (* hXp *)
  assert (hXp : forall p, In p keptL -> inXp (chr p)).
  { intros p Hp. destruct (hE_kept _ (proj1 (hmem p) Hp)) as [th [hth hpr]].
    rewrite <- (prim_inj _ _ hpr). exact hth. }
  (* hKimg + hinj, as a permutation *)
  assert (hperm : Permutation (map (fun p => prim (chr p)) keptL) KEPT).
  { apply NoDup_Permutation; [|exact KEPT_nd|].
    - apply inj_map_NoDup; [|exact keptL_nd].
      intros p q E. apply chr_inj, prim_inj, E.
    - intro q. rewrite in_map_iff. split.
      + intros [p [E Hp]]. subst q. apply hmem, Hp.
      + intro Hq. destruct (hE_kept q Hq) as [th [_ hpr]]. destruct (chr_surj th) as [p Ep].
        exists p. subst th. split; [exact hpr|]. apply hmem. rewrite hpr. exact Hq. }
  (* hw *)
  assert (hw : forall p, In p keptL ->
            wtG p = (if PC_eq_dec (prim (chr p)) oneP then 1 else lwt (prim (chr p)))).
  { intros p Hp. pose proof (Xp_iod _ (hXp p Hp)) as hiod.
    assert (htriv : (forall h, ev p (inr h) = k1) <-> chr p = oneC \/ chr p = psC).
    { rewrite <- (gmA_eq_triv_r (chr p) hiod). split; intros H h; apply GEN_IFF, H. }
    unfold wtG. destruct (trivH p) eqn:Et.
    - destruct (proj1 htriv (proj1 (trivH_spec p) Et)) as [h1|h1].
      + rewrite h1, prim_one. destruct (PC_eq_dec oneP oneP); [reflexivity|congruence].
      + assert (hK : In (prim psC) KEPT) by (rewrite <- h1; apply hmem, Hp).
        rewrite h1. destruct (PC_eq_dec (prim psC) oneP) as [_|hone]; [reflexivity|].
        unfold lwt. destruct psK as [q|] eqn:Ek.
        * pose proof (hps1 q eq_refl) as e. destruct (PC_eq_dec q (prim psC)) as [_|N]; [reflexivity|congruence].
        * exfalso. exact (hps2 eq_refl hK).
    - assert (hA : ~ (forall h, ev p (inr h) = k1)) by (intro H; apply trivH_spec in H; congruence).
      assert (hn1 : chr p <> oneC) by (intro E; apply hA, htriv; left; exact E).
      assert (hnps : chr p <> psC) by (intro E; apply hA, htriv; right; exact E).
      destruct (PC_eq_dec (prim (chr p)) oneP) as [E|_].
      + exfalso. apply hn1, prim_inj. rewrite E, prim_one. reflexivity.
      + unfold lwt. destruct psK as [q|] eqn:Ek; [|reflexivity].
        destruct (PC_eq_dec q (prim (chr p))) as [E|_]; [|reflexivity].
        exfalso. apply hnps, prim_inj. rewrite (hps1 q eq_refl), E. reflexivity. }
  set (F := fun q => (if PC_eq_dec q oneP then 1 else lwt q) * re (gch q y)).
  (* hw, hG, key *)
  assert (key : GmAG y = rsum (map F KEPT)).
  { unfold GmAG. rewrite (rsum_map_ext _ (fun p => F (prim (chr p))))
      by (intros p Hp; unfold F; rewrite (hw p Hp), PRIM_READ; reflexivity).
    rewrite <- (map_map (fun p => prim (chr p)) F). apply rsum_perm, Permutation_map, hperm. }
  rewrite key.
  (* Finset.add_sum_erase, hone, Gz_eq *)
  rewrite (rsum_perm _ _ (Permutation_map F (perm_remove PC_eq_dec oneP KEPT KEPT_nd one_mem))).
  simpl. unfold LevelGm. f_equal.
  - unfold F. destruct (PC_eq_dec oneP oneP) as [_|N]; [|congruence]. rewrite GCH_ONE, GZ_EQ. ring.
  - apply rsum_map_ext. intros q Hq. unfold F. destruct (in_remove PC_eq_dec KEPT q oneP Hq) as [_ Hne].
    destruct (PC_eq_dec q oneP); [contradiction|reflexivity].
Qed.
End GmA.

Print Assumptions gmA_eq_triv_r.
Print Assumptions gmA_eq_r.

(* ===================================================================== *)
(* S6  large_x_eventually  (SizeWindowBrackets/ChainSlopeWindows/         *)
(*     SubThreeMulLogTwoLe.lean : large_x_eventually, l.319; the          *)
(*     instance CoreGm.lean l.23 uses, namespace                          *)
(*     Formalism.LFunctionChainParameters.LErr)                          *)
(* ===================================================================== *)
(* Beyond some x0: log x <= x^eps and KBig <= x^eps.  Lean steps: h1 from
   isLittleO_log_rpow_atTop (bound with c = 1) on [1, oo), rewriting the
   norms (rpow_nonneg) and le_abs_self; h2 from tendsto_rpow_atTop
   (eventually_ge_atTop); Filter.eventually_atTop of h1.and h2 -- the
   max of the two thresholds. *)
Section LargeXEventually.
Variables (lg : R -> R) (rp : R -> R -> R).          (* Real.log, Real.rpow *)
(* [Mathlib] isLittleO_log_rpow_atTop, through Asymptotics.IsLittleO.bound and Filter.eventually_atTop *)
Hypothesis LITTLEO : forall eps, 0 < eps -> forall c, 0 < c ->
  exists x0, forall x, x0 <= x -> Rabs (lg x) <= c * Rabs (rp x eps).
(* [Mathlib] tendsto_rpow_atTop, Filter.Tendsto.eventually_ge_atTop, Filter.eventually_atTop *)
Hypothesis RPOW_TOP : forall eps, 0 < eps -> forall M, exists x0, forall x, x0 <= x -> M <= rp x eps.
Hypothesis RPOW_NONNEG : forall x y, 0 <= x -> 0 <= rp x y.    (* [Mathlib] Real.rpow_nonneg *)

Theorem large_x_eventually_r : LargeXEv lg rp.
Proof.
  intros eps K cHH eK Heps.
  (* h1 *)
  assert (h1 : exists x1, forall x, x1 <= x -> lg x <= rp x eps).
  { destruct (LITTLEO eps Heps 1 Rlt_0_1) as [x0 Hx0].
    exists (Rmax x0 1). intros x Hx.
    pose proof (Hx0 x (Rle_trans _ _ _ (Rmax_l _ _) Hx)) as H.
    rewrite Rmult_1_l, (Rabs_pos_eq (rp x eps)) in H by (apply RPOW_NONNEG; pose proof (Rmax_r x0 1); lra).
    pose proof (Rle_abs (lg x)). lra. }
  (* h2 *)
  destruct (RPOW_TOP eps Heps (KBig K cHH eK)) as [x2 Hx2].
  destruct h1 as [x1 Hx1].
  exists (Rmax x1 x2). intros x Hx. split.
  - apply Hx1. eapply Rle_trans; [apply Rmax_l|exact Hx].
  - apply Hx2. eapply Rle_trans; [apply Rmax_r|exact Hx].
Qed.
End LargeXEventually.

Print Assumptions large_x_eventually_r.

(* ===================================================================== *)
(* Ledger: Lean lemma -> Rocq theorem(s) -> carrier -> hypotheses         *)
(* ===================================================================== *)
(*
  one_char (ChCore.lean l.202; helpers move l.154, triv l.167)
    -> one_char_r  (with move_r, triv_r)
    carrier: abstract field K = C (record CStr: ofR, re, nrm) over Stdlib R
    [Mathlib] CStr laws (field, ofReal_add/mul/one/eq_zero, add_re,
      re_ofReal_mul, ofReal_re, abs_re_le_norm, norm_add_le, norm_mul,
      norm_real); AddChar.map_add_eq_mul, AddChar.zero_apply,
      AddChar.norm_apply; DecidableEq on characters; Real.log_le_log,
      Real.log_nonneg; Prod.ext (e1 t = sgc0 + (0,t)); the GPsi sum at 1
      (Nat.floor_one, vonMangoldt_apply_one)
    [inventory] none beyond the lemma's own premises (DerivInt, the
      CharsA-shaped bounds h2, hK, h3, r1-r3)

  th_le (ChCore.lean l.75)
    -> th_le_r
    carrier: K = C (CStr) over R
    [Mathlib] CStr laws
    [inventory] thick_filter + thick_inj (as a Permutation), CR.partner_inPhi,
      CR.norm_avg_le with CR.card_S_le, CR.De_re (+ balTop, CR.GC_host);
      premises ThinScales, LipW as in Lean

  ch_balance (ChBalance.lean l.200)
    -> ch_balance_r
    carrier: K = C (CStr) over R
    [Mathlib] CStr laws; Finset.univ (NoDup, mem_univ); AddChar.zero_apply
      with map_one (conj (0 g) = 1); DecidableEq on characters
    [inventory] CharacterBalance.askExp, sum_cut, inner_eq, partner_inPhi,
      colour_sum, sum_partner (card_notPhi is re-derived from it, as in
      Lean), PB.chC_ne_zero, PB.phi_card_ne_zero

  ch_top (ChTop.lean l.37; ch_top_main_eq l.11)
    -> ch_top_r  (with ch_top_main_eq_r)
    carrier: K = C (CStr) over R (Re MAIN), abstract log and rpow
    [Mathlib] CStr laws; Real.rpow_nonneg; Equiv.sum_comp and
      Fintype.card_congr for eT : Top = TT, eP : Fin f = PhiSet (as
      Permutations)
    [inventory] each_unit_bound_statement (PointwiseBoundVariant),
      SizeData2 -> HidaSetting (0 < x), errX5at_le; premises IdentU,
      BNBoundsU, LargeX as in Lean

  gmA_eq (PrimitiveCosets/GmAEq.lean l.61; private gmA_eq_triv l.16)
    -> gmA_eq_r  (with gmA_eq_triv_r)
    carrier: K = C (CStr) for character values, R for GmA / Level.Gm;
      GG = (Z^x x Z^x) x MA with Z^x as bool
    [Mathlib] mul_self_eq_one_iff, map_mul, map_one, MonoidHom.ext /
      Units.ext, MonoidHom.one_apply, one_mul (MA), Int.units_eq_one_or
      (Z^x as bool), DecidableEq on PChar, Finset NoDup
    [inventory] chr_bij, prim_inj, character_trivial_on_generator_iff,
      keptA / HostRaw.kept_iff, Frame.Xp, Frame.psC / chQ, EAtH.kept,
      EAtH.ps, HostRaw.isPrimOf_iff, Level.one_mem, prim_read, An.gChi at
      PChar.one, Gz_eq

  large_x_eventually (SubThreeMulLogTwoLe.lean l.319, used at CoreGm.lean l.23)
    -> large_x_eventually_r
    carrier: Stdlib R, abstract log and rpow
    [Mathlib] isLittleO_log_rpow_atTop (IsLittleO.bound), tendsto_rpow_atTop
      (eventually_ge_atTop), Real.rpow_nonneg, Filter.eventually_atTop
    [inventory] none
*)
