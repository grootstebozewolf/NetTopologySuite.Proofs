(* SphereNoRelQED.v -- the combinatorial core of the "thick set" step in the
   claimed RH/GRH Lean development (CocoSgt/riemann-hypothesis-lean @ 7cbf7a0,
   Formalism/FrobeniusOrbits/HostThickExists.lean : NoRel, hostThickExists).

   NoRel T L : no distinct s1 s2 s3 in T and 0<|i|,|j|<=L, i<>j with
               j*(s2-s1) = i*(s3-s1).

   Read on base-b digit vectors, the relation is a COLLINEARITY of three digit
   vectors (an orientation-zero predicate).  Behrend's construction keeps
   digit vectors on a sphere |a|^2 = r, which is strictly convex, so no three
   distinct points are collinear.  This file proves the two lemmas that make
   that work, over Z, with no real analysis:

     sphere_no_collinear : distinct points of one integer sphere satisfy no
                           relation  j*(a2-a1) = i*(a3-a1)  with i,j<>0, i<>j.
     eval_zero_digits    : balanced base-b digits (|c_k| <= B, 2B < b) that
                           evaluate to 0 are all 0 (no carries).
     sphere_digits_norel : the two combined: numbers whose base-b digit
                           vectors lie on one sphere satisfy NoRel, as long as
                           2*L*d < b with digits in [0,d).

     sphere_slice_large  : density.  Some sphere slice S_r of [0,d)^K has
                           (K(d-1)^2 + 1) * |S_r| >= d^K  (generic pigeonhole
                           `pigeon` over the <= K(d-1)^2 + 1 radii).

     thick_set_exists    : packaged integer analogue of the external
                           HostThickExists: for 1 <= L, 4*L*d < b there is a
                           duplicate-free T in [0, b^K) satisfying NoRel T L
                           with d^K <= (K(d-1)^2 + 1) * |T|.  POLYNOMIAL loss
                           (with b = c*d: |T| >= b^K / (c^K (K d^2 + 1)))
                           instead of exp(-C sqrt(log n log L)).

   Outcome: QED (host lane, Stdlib only); all three main theorems closed
   under the global context.  Left as prose: reading c^K as N^(log c/log b),
   i.e. choosing b ~ (8L)^(1/eps') to make the loss N^(-eps').  This is
   EVIDENCE for ticket docs/attacks/2026-11-20-root-only-multiplicity.md,
   slice 4 (S4), and NOT a product module.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted; not yet human-reviewed.
     Assisted-by: Claude
*)
From Stdlib Require Import ZArith Lia List.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint dot (u v : list Z) : Z :=
  match u, v with
  | x :: u', y :: v' => x * y + dot u' v'
  | _, _ => 0
  end.

Fixpoint vsub (u v : list Z) : list Z :=
  match u, v with
  | x :: u', y :: v' => (x - y) :: vsub u' v'
  | _, _ => []
  end.

Definition vscale (c : Z) (u : list Z) : list Z := map (Z.mul c) u.

Fixpoint eval (b : Z) (c : list Z) : Z :=
  match c with
  | [] => 0
  | x :: c' => x + b * eval b c'
  end.


Lemma dot_self_nonneg : forall u, 0 <= dot u u.
Proof. induction u as [|x u IH]; cbn [dot vsub length eval map]; nia. Qed.

Lemma dot_scale_l : forall c u v, dot (vscale c u) v = c * dot u v.
Proof.
  intros c u; unfold vscale; induction u as [|x u IH]; intros [|y v]; cbn [dot vsub length eval map]; try ring.
  rewrite IH. ring.
Qed.

Lemma dot_scale_r : forall c u v, dot u (vscale c v) = c * dot u v.
Proof.
  intros c u; unfold vscale; induction u as [|x u IH]; intros [|y v]; cbn [dot vsub length eval map]; try ring.
  rewrite IH. ring.
Qed.

(* |a1 + u|^2 = |a1|^2 + 2 a1.u + |u|^2, with u = a2 - a1. *)
Lemma sq_expand : forall a2 a1, length a2 = length a1 ->
  dot a2 a2 = dot a1 a1 + 2 * dot a1 (vsub a2 a1) + dot (vsub a2 a1) (vsub a2 a1).
Proof.
  induction a2 as [|x a2 IH]; intros [|y a1] Hl; cbn [dot vsub length eval map] in *; try lia.
  rewrite (IH a1) by lia. ring.
Qed.

Lemma vsub_zero_eq : forall a2 a1, length a2 = length a1 ->
  dot (vsub a2 a1) (vsub a2 a1) = 0 -> a2 = a1.
Proof.
  induction a2 as [|x a2 IH]; intros [|y a1] Hl H; cbn [dot vsub length eval map] in *; try lia; auto.
  pose proof (dot_self_nonneg (vsub a2 a1)).
  assert (x = y) by nia. assert (dot (vsub a2 a1) (vsub a2 a1) = 0) by nia.
  subst. f_equal. apply IH; auto; lia.
Qed.

(* Distinct points of one integer sphere are never collinear in the NoRel sense. *)
Theorem sphere_no_collinear : forall a1 a2 a3 : list Z,
  length a2 = length a1 -> length a3 = length a1 ->
  dot a2 a2 = dot a1 a1 -> dot a3 a3 = dot a1 a1 ->
  forall i j : Z, i <> 0 -> j <> 0 -> i <> j ->
  vscale j (vsub a2 a1) = vscale i (vsub a3 a1) ->
  a2 = a1.
Proof.
  intros a1 a2 a3 L2 L3 S2 S3 i j Hi Hj Hij Hrel.
  set (u := vsub a2 a1). set (v := vsub a3 a1).
  pose proof (sq_expand a2 a1 L2) as E1. pose proof (sq_expand a3 a1 L3) as E2.
  fold u in E1. fold v in E2.
  (* j a1.u = i a1.v  and  j^2 u.u = i^2 v.v *)
  assert (HA : j * dot a1 u = i * dot a1 v).
  { rewrite <- !dot_scale_r. fold u v in Hrel. now rewrite Hrel. }
  assert (HU : j * j * dot u u = i * i * dot v v).
  { assert (dot (vscale j u) (vscale j u) = dot (vscale i v) (vscale i v))
      by (fold u v in Hrel; now rewrite Hrel).
    rewrite !dot_scale_l, !dot_scale_r in H. lia. }
  pose proof (dot_self_nonneg u) as Pu.
  assert (Hz : j * (j - i) * dot u u = 0) by nia.
  assert (dot u u = 0).
  { apply Z.mul_eq_0 in Hz as [Hz|Hz]; [apply Z.mul_eq_0 in Hz as [Hz|Hz]; lia | exact Hz]. }
  now apply vsub_zero_eq.
Qed.

(* ---------- digits: balanced base-b representation has no carries ---------- *)

Theorem eval_zero_digits : forall b B c, 0 <= B -> 2 * B < b ->
  Forall (fun x => Z.abs x <= B) c -> eval b c = 0 -> Forall (fun x => x = 0) c.
Proof.
  intros b B c HB Hb. induction c as [|x c IH]; intros Hf He; constructor.
  - inversion Hf; subst. cbn [eval] in He.
    destruct (Z.eq_dec (eval b c) 0) as [E|E]; [nia|].
    exfalso. assert (1 <= Z.abs (eval b c)) by lia.
    assert (Z.abs (b * eval b c) >= b) by (rewrite Z.abs_mul; nia). lia.
  - inversion Hf; subst. apply IH; auto. cbn [eval] in He.
    destruct (Z.eq_dec (eval b c) 0) as [E|E]; auto.
    exfalso. assert (1 <= Z.abs (eval b c)) by lia.
    assert (Z.abs (b * eval b c) >= b) by (rewrite Z.abs_mul; nia). lia.
Qed.

Lemma eval_lin : forall b i j a1 a2 a3,
  length a2 = length a1 -> length a3 = length a1 ->
  j * (eval b a2 - eval b a1) - i * (eval b a3 - eval b a1)
  = eval b (vsub (vscale j (vsub a2 a1)) (vscale i (vsub a3 a1))).
Proof.
  intros b i j a1. unfold vscale.
  induction a1 as [|y a1 IH]; intros [|x2 a2] [|x3 a3] L2 L3;
    cbn [dot vsub length eval map] in *; try lia.
  rewrite <- IH by lia. ring.
Qed.

Lemma vsub_zero_vec : forall u v, length u = length v ->
  Forall (fun x => x = 0) (vsub u v) -> u = v.
Proof.
  induction u as [|x u IH]; intros [|y v] Hl Hf; cbn [dot vsub length eval map] in *; try lia; auto.
  inversion Hf; subst. f_equal; [lia | apply IH; auto; lia].
Qed.

Lemma map_length_vscale : forall c u, length (vscale c u) = length u.
Proof. intros; unfold vscale; apply length_map. Qed.

Lemma vsub_length : forall u v, length u = length v -> length (vsub u v) = length u.
Proof. induction u; intros [|y v] H; cbn [dot vsub length eval map] in *; try lia; auto. Qed.

Lemma digit_bound : forall i j d a1 a2 a3,
  length a2 = length a1 -> length a3 = length a1 ->
  Forall (fun x => 0 <= x < d) a1 -> Forall (fun x => 0 <= x < d) a2 ->
  Forall (fun x => 0 <= x < d) a3 ->
  Forall (fun x => Z.abs x <= (Z.abs i + Z.abs j) * d)
         (vsub (vscale j (vsub a2 a1)) (vscale i (vsub a3 a1))).
Proof.
  intros i j d a1. unfold vscale.
  induction a1 as [|y a1 IH]; intros [|x2 a2] [|x3 a3] L2 L3 F1 F2 F3;
    cbn [dot vsub length eval map] in *; try lia; try solve [constructor].
  inversion F1; inversion F2; inversion F3; subst.
  constructor.
  - assert (Z.abs (j * (x2 - y)) <= Z.abs j * d) by (rewrite Z.abs_mul; nia).
    assert (Z.abs (i * (x3 - y)) <= Z.abs i * d) by (rewrite Z.abs_mul; nia).
    lia.
  - apply IH; auto; lia.
Qed.

(* Behrend-type set: numbers whose base-b digit vectors (digits in [0,d)) lie
   on one sphere.  Under 2*(|i|+|j|)*d < b, in particular 4*L*d < b, it
   satisfies NoRel. *)
Theorem sphere_digits_norel : forall b d r (a1 a2 a3 : list Z) (i j : Z),
  0 <= d -> 2 * ((Z.abs i + Z.abs j) * d) < b ->
  length a2 = length a1 -> length a3 = length a1 ->
  Forall (fun x => 0 <= x < d) a1 -> Forall (fun x => 0 <= x < d) a2 ->
  Forall (fun x => 0 <= x < d) a3 ->
  dot a1 a1 = r -> dot a2 a2 = r -> dot a3 a3 = r ->
  i <> 0 -> j <> 0 -> i <> j ->
  j * (eval b a2 - eval b a1) = i * (eval b a3 - eval b a1) ->
  eval b a2 = eval b a1.
Proof.
  intros b d r a1 a2 a3 i j Hd Hb L2 L3 F1 F2 F3 R1 R2 R3 Hi Hj Hij Hrel.
  assert (Hev : eval b (vsub (vscale j (vsub a2 a1)) (vscale i (vsub a3 a1))) = 0)
    by (rewrite <- eval_lin by auto; lia).
  pose proof (digit_bound i j d a1 a2 a3 L2 L3 F1 F2 F3) as Hbd.
  apply eval_zero_digits with (B := (Z.abs i + Z.abs j) * d) in Hev; auto; [|nia].
  apply vsub_zero_vec in Hev.
  2: { rewrite !map_length_vscale, !vsub_length by auto. lia. }
  assert (a2 = a1).
  { exact (sphere_no_collinear a1 a2 a3 L2 L3 ltac:(lia) ltac:(lia) i j Hi Hj Hij Hev). }
  now subst.
Qed.

Print Assumptions sphere_digits_norel.

(* ---------- density: some sphere slice of [0,d)^K is large (pigeonhole) ---------- *)

Section Pigeon.
Variable A : Type.
Variable f : A -> nat.
Local Open Scope nat_scope.

Lemma filter_split : forall (R : nat) (l : list A),
  (forall x, In x l -> f x <= R) ->
  length l = length (filter (fun x => Nat.ltb (f x) R) l)
           + length (filter (fun x => Nat.eqb (f x) R) l).
Proof.
  intros R l. induction l as [|x l IH]; intros H; cbn [filter length]; auto.
  assert (Hx : f x <= R) by (apply H; now left).
  rewrite IH by (intros; apply H; now right).
  destruct (Nat.ltb_spec (f x) R); destruct (Nat.eqb_spec (f x) R); cbn [filter length]; lia.
Qed.

Lemma filter_lt_eq : forall (R r : nat) (l : list A), r < R ->
  length (filter (fun x => Nat.eqb (f x) r) (filter (fun x => Nat.ltb (f x) R) l))
  = length (filter (fun x => Nat.eqb (f x) r) l).
Proof.
  intros R r l Hr. induction l as [|x l IH]; cbn [filter length]; auto.
  destruct (Nat.ltb_spec (f x) R); cbn [filter length];
    destruct (Nat.eqb_spec (f x) r); cbn [filter length]; rewrite ?IH; lia.
Qed.

(* Some value r <= R is hit by at least |l|/(R+1) elements. *)
Theorem pigeon : forall (R : nat) (l : list A),
  (forall x, In x l -> f x <= R) ->
  exists r, r <= R /\ length l <= S R * length (filter (fun x => Nat.eqb (f x) r) l).
Proof.
  induction R as [|R IH]; intros l H.
  - exists 0. split; [lia|].
    assert (length (filter (fun x => Nat.eqb (f x) 0) l) = length l).
    { induction l as [|x l IHl]; cbn [filter length]; auto.
      assert (f x = 0) by (pose proof (H x (or_introl eq_refl)); lia).
      rewrite (proj2 (Nat.eqb_eq _ _) H0). cbn [filter length]. f_equal.
      apply IHl; intros; apply H; now right. }
    lia.
  - pose proof (filter_split (S R) l H) as Hs.
    set (B := length (filter (fun x => Nat.eqb (f x) (S R)) l)) in *.
    set (lA := filter (fun x => Nat.ltb (f x) (S R)) l) in *.
    destruct (Nat.le_gt_cases (length l) (S (S R) * B)) as [Hb|Hb].
    + exists (S R). split; [lia|exact Hb].
    + destruct (IH lA) as [r [Hr Hc]].
      { intros x Hx. unfold lA in Hx. apply filter_In in Hx as [_ Hx].
        apply Nat.ltb_lt in Hx. lia. }
      exists r. split; [lia|].
      unfold lA in *; rewrite filter_lt_eq in Hc by lia.
      set (c := length (filter (fun x => Nat.eqb (f x) r) l)) in *.
      set (a := length (filter (fun x => Nat.ltb (f x) (S R)) l)) in *.
      assert (H1 : S R * B < S R * c) by nia.
      apply Nat.mul_lt_mono_pos_l in H1; [|lia]. nia.
Qed.
End Pigeon.

(* All digit vectors in [0,d)^K. *)
Fixpoint allvec (K d : nat) : list (list Z) :=
  match K with
  | O => [[]]
  | S K' => flat_map (fun x => map (cons x) (allvec K' d)) (map Z.of_nat (seq 0 d))
  end.

Lemma len_fm : forall (l : list Z) (V : list (list Z)),
  length (flat_map (fun x => map (cons x) V) l) = (length l * length V)%nat.
Proof.
  induction l as [|x l IH]; intros V; cbn [flat_map length]; [lia|].
  rewrite length_app, length_map, IH. lia.
Qed.

Lemma allvec_length : forall K d, length (allvec K d) = Nat.pow d K.
Proof.
  induction K as [|K IH]; intros d; cbn [allvec]; [reflexivity|].
  rewrite len_fm, length_map, length_seq, IH. cbn [Nat.pow]. lia.
Qed.

Lemma allvec_in : forall K d a, In a (allvec K d) ->
  length a = K /\ Forall (fun x => 0 <= x < Z.of_nat d) a.
Proof.
  induction K as [|K IH]; intros d a Ha; cbn in Ha.
  - destruct Ha as [<-|[]]. split; auto.
  - apply in_flat_map in Ha as [x [Hx Ha]]. apply in_map_iff in Ha as [a' [<- Ha']].
    apply in_map_iff in Hx as [n [<- Hn]]. apply in_seq in Hn.
    destruct (IH d a' Ha') as [L F]. split; cbn; [lia|]. constructor; auto. lia.
Qed.

Lemma dot_self_bound : forall a d, Forall (fun x => 0 <= x < d) a ->
  dot a a <= Z.of_nat (length a) * (d - 1) * (d - 1).
Proof.
  induction a as [|x a IH]; intros d F; cbn [dot length]; [lia|].
  inversion F; subst. specialize (IH d H2). rewrite Nat2Z.inj_succ. nia.
Qed.

Lemma my_NoDup_app : forall (A : Type) (l l' : list A), NoDup l -> NoDup l' ->
  (forall a, In a l -> ~ In a l') -> NoDup (l ++ l').
Proof.
  intros A l. induction l as [|x l IH]; intros l' H1 H2 H3; cbn; auto.
  inversion H1; subst. constructor.
  - intros Hin. apply in_app_or in Hin as [Hin|Hin]; [contradiction|].
    exact (H3 x (or_introl eq_refl) Hin).
  - apply IH; auto. intros a Ha. apply H3. now right.
Qed.

Lemma NoDup_map_on : forall (A B : Type) (g : A -> B) (l : list A),
  (forall x y, In x l -> In y l -> g x = g y -> x = y) -> NoDup l -> NoDup (map g l).
Proof.
  intros A B g l. induction l as [|x l IH]; intros Hi Hn; cbn; [constructor|].
  inversion Hn; subst. constructor.
  - intros Hin. apply in_map_iff in Hin as [y [E Hy]].
    assert (y = x) by (apply Hi; [now right | now left | exact E]). subst. contradiction.
  - apply IH; auto. intros; apply Hi; auto; now right.
Qed.

Lemma NoDup_fm : forall (l : list Z) (V : list (list Z)), NoDup l -> NoDup V ->
  NoDup (flat_map (fun x => map (cons x) V) l).
Proof.
  induction l as [|x l IH]; intros V Hl HV; cbn [flat_map]; [constructor|].
  inversion Hl; subst. apply my_NoDup_app.
  - apply NoDup_map_on; auto. intros u v _ _ E. now injection E.
  - apply IH; auto.
  - intros a Ha Hb. apply in_map_iff in Ha as [u [<- _]].
    apply in_flat_map in Hb as [y [Hy Hb]]. apply in_map_iff in Hb as [v [E _]].
    injection E as -> _. contradiction.
Qed.

Lemma allvec_NoDup : forall K d, NoDup (allvec K d).
Proof.
  induction K as [|K IH]; intros d; cbn [allvec].
  - repeat constructor; auto.
  - apply NoDup_fm; auto. apply NoDup_map_on; [|apply seq_NoDup].
    intros u v _ _ E. lia.
Qed.

(* Density: some sphere slice S_r of [0,d)^K has (K(d-1)^2 + 1) * |S_r| >= d^K,
   and (sphere_digits_norel) every such slice satisfies NoRel once 4Ld < b. *)
Theorem sphere_slice_large : forall K d, (1 <= d)%nat ->
  exists r : Z, exists Sl : list (list Z),
    NoDup Sl /\
    (forall a, In a Sl -> length a = K /\ Forall (fun x => 0 <= x < Z.of_nat d) a /\ dot a a = r) /\
    (Nat.pow d K <= S (K * (d - 1) * (d - 1)) * length Sl)%nat.
Proof.
  intros K d Hd.
  set (R := (K * (d - 1) * (d - 1))%nat).
  destruct (pigeon (list Z) (fun a => Z.to_nat (dot a a)) R (allvec K d)) as [r [Hr Hc]].
  { intros a Ha. destruct (allvec_in K d a Ha) as [L F].
    pose proof (dot_self_bound a (Z.of_nat d) F). pose proof (dot_self_nonneg a).
    rewrite L in H. unfold R.
    assert (Z.of_nat K * (Z.of_nat d - 1) * (Z.of_nat d - 1)
            = Z.of_nat (K * (d - 1) * (d - 1))) by (rewrite !Nat2Z.inj_mul, Nat2Z.inj_sub by lia; lia).
    lia. }
  exists (Z.of_nat r), (filter (fun a => Nat.eqb (Z.to_nat (dot a a)) r) (allvec K d)).
  split; [apply NoDup_filter, allvec_NoDup|].
  split.
  - intros a Ha. apply filter_In in Ha as [Ha He]. apply Nat.eqb_eq in He.
    destruct (allvec_in K d a Ha) as [L F]. pose proof (dot_self_nonneg a).
    repeat split; auto. lia.
  - rewrite allvec_length in Hc. exact Hc.
Qed.

Print Assumptions sphere_slice_large.

(* ---------- packaging: an integer analogue of HostThickExists ---------- *)




Lemma eval_vsub : forall b a a', length a = length a' ->
  eval b a - eval b a' = eval b (vsub a a').
Proof.
  intros b. induction a as [|x a IH]; intros [|y a'] Hl; cbn [eval vsub length] in *;
    try lia. rewrite <- IH by lia. ring.
Qed.

Lemma vsub_bound : forall d a a', length a = length a' ->
  Forall (fun x => 0 <= x < d) a -> Forall (fun x => 0 <= x < d) a' ->
  Forall (fun x => Z.abs x <= d) (vsub a a').
Proof.
  induction a as [|x a IH]; intros [|y a'] Hl F F'; cbn [vsub length] in *;
    try lia; try solve [constructor].
  inversion F; inversion F'; subst. constructor; [lia|]. apply IH; auto; lia.
Qed.

Lemma eval_inj : forall b d a a', 0 <= d -> 2 * d < b -> length a = length a' ->
  Forall (fun x => 0 <= x < d) a -> Forall (fun x => 0 <= x < d) a' ->
  eval b a = eval b a' -> a = a'.
Proof.
  intros b d a a' Hd Hb Hl F F' E.
  apply vsub_zero_vec; auto.
  apply (eval_zero_digits b d); auto.
  - now apply vsub_bound.
  - rewrite <- eval_vsub by auto. lia.
Qed.

Lemma eval_range : forall b a, 0 < b -> Forall (fun x => 0 <= x < b) a ->
  0 <= eval b a < b ^ Z.of_nat (length a).
Proof.
  intros b. induction a as [|x a IH]; intros Hb F; cbn [eval length]; [cbn; lia|].
  inversion F; subst. specialize (IH Hb H2). rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  nia.
Qed.


(* Integer analogue of the external development's
     HostThickExists : exists T, (s in T -> 4Ls < n) /\ NoRel T L /\ n*exp(-C sqrt(..))/L <= |T|
   with a POLYNOMIAL loss instead of exp(-C sqrt(log n log L)):
     T subset [0, b^K), NoRel T L, distinct, and d^K <= (K(d-1)^2 + 1) * |T|,
   whenever 4*L*d < b.  With b = c*d this is |T| >= b^K / (c^K (K d^2 + 1)). *)
Theorem thick_set_exists : forall (L : Z) (K d : nat) (b : Z),
  (1 <= d)%nat -> 1 <= L -> 4 * L * Z.of_nat d < b ->
  exists T : list Z,
    NoDup T /\
    (forall s, In s T -> 0 <= s < b ^ Z.of_nat K) /\
    (forall s1 s2 s3 i j, In s1 T -> In s2 T -> In s3 T ->
       s1 <> s2 -> s1 <> s3 -> s2 <> s3 ->
       0 < Z.abs i -> Z.abs i <= L -> 0 < Z.abs j -> Z.abs j <= L -> i <> j ->
       j * (s2 - s1) <> i * (s3 - s1)) /\
    (Nat.pow d K <= S (K * (d - 1) * (d - 1)) * length T)%nat.
Proof.
  intros L K d b Hd HL Hb.
  assert (Hb2 : 2 * Z.of_nat d < b) by nia.
  destruct (sphere_slice_large K d Hd) as [r [Sl [HN [HS Hc]]]].
  exists (map (eval b) Sl). split; [|split; [|split]].
  - apply NoDup_map_on; auto.
    intros a a' Ha Ha' E. destruct (HS a Ha) as [La [Fa _]]. destruct (HS a' Ha') as [La' [Fa' _]].
    apply (eval_inj b (Z.of_nat d)); auto; lia.
  - intros s0 Hs. apply in_map_iff in Hs as [a [<- Ha]]. destruct (HS a Ha) as [La [Fa _]].
    rewrite <- La. apply eval_range; [lia|].
    eapply Forall_impl; [|exact Fa]. intros x Hx; cbn in Hx. lia.
  - intros s1 s2 s3 i j H1 H2 H3 N12 N13 N23 Hi1 Hi2 Hj1 Hj2 Hij Hrel.
    apply in_map_iff in H1 as [a1 [<- A1]]. apply in_map_iff in H2 as [a2 [<- A2]].
    apply in_map_iff in H3 as [a3 [<- A3]].
    destruct (HS a1 A1) as [L1 [F1 R1]]. destruct (HS a2 A2) as [L2 [F2 R2]].
    destruct (HS a3 A3) as [L3 [F3 R3]].
    apply N12. symmetry.
    apply (sphere_digits_norel b (Z.of_nat d) r a1 a2 a3 i j); auto; try lia; nia.
  - rewrite length_map. exact Hc.
Qed.

Print Assumptions thick_set_exists.

(* ============================================================================
   OrbitOne (Formalism/BehrendSets/Statement.lean):
     (∀ t ∈ T, 8 L t < n) -> addOrderOf h ≤ 8 L ->
     t0 + i1•h ∈ thick n T u -> t0 + i2•h ∈ thick n T u -> i1•h = i2•h
   (thick n T u = image of T + u in ZMod n).
   Group translation (not re-proved): the orbit {t0 + i•h} of h of additive
   order o = n/g in ZMod n is a coset of g·ZMod n, g = gcd(h, n); so two orbit
   points x, y satisfy g | x - y, and o ≤ 8L is n ≤ 8L·g.
   Integer form proved here: two such points that both lie in T + u (mod n)
   coincide mod n.
   ========================================================================== *)

Theorem orbit_one : forall (n L g t1 t2 u x y : Z),
  0 < g -> 0 < L -> (g | n) -> n <= 8 * L * g ->
  0 <= t1 -> 0 <= t2 -> 8 * L * t1 < n -> 8 * L * t2 < n ->
  (g | x - y) ->
  (n | x - (t1 + u)) -> (n | y - (t2 + u)) ->
  (n | x - y).
Proof.
  intros n L g t1 t2 u x y Hg HL Hgn Hn T1 T2 H1 H2 Hxy Hx Hy.
  assert (Gx : (g | x - (t1 + u))) by (apply Z.divide_trans with n; assumption).
  assert (Gy : (g | y - (t2 + u))) by (apply Z.divide_trans with n; assumption).
  (* g | t1 - t2 *)
  assert (Gt : (g | t1 - t2)).
  { replace (t1 - t2) with ((x - y) - (x - (t1 + u)) + (y - (t2 + u))) by ring.
    apply Z.divide_add_r; [apply Z.divide_sub_r; assumption | assumption]. }
  (* 0 <= t1, t2 < g *)
  assert (t1 < g) by nia. assert (t2 < g) by nia.
  assert (Et : t1 = t2).
  { destruct Gt as [c Hc]. assert (c = 0) by nia. subst c. lia. }
  subst t2.
  replace (x - y) with ((x - (t1 + u)) - (y - (t1 + u))) by ring.
  now apply Z.divide_sub_r.
Qed.

Print Assumptions orbit_one.

(* ============================================================================
   WindowTwo (Formalism/BehrendSets/Statement.lean):
     (∀ t ∈ T, 8 L t < n) -> BehrendFree (2L) T -> 2L < addOrderOf h ->
     ∀ j, #{ i ∈ [j, j+2L) : t0 + i•h ∈ thick n T u } ≤ 2
   Integer form proved here: no THREE indices j ≤ i1 < i2 < i3 < j+2L all hit
   T + u (mod n).  ("card ≤ 2" is "no three distinct", a finset translation.)
   Hypothesis used: NoRel at coefficient size 2L -- the condition that the
   external HostThickExists produces and that thick_set_exists (with L := 2L)
   provides -- instead of BehrendFree: the forced relation is exactly
     a*(t3 - t1) = b*(t2 - t1),  a = i2 - i1 < b = i3 - i1 < 2L,
   i.e. three COLLINEAR digit vectors.
   ========================================================================== *)

Definition NoRelZ (T : Z -> Prop) (K : Z) : Prop :=
  forall s1 s2 s3 i j, T s1 -> T s2 -> T s3 -> s1 <> s2 -> s1 <> s3 -> s2 <> s3 ->
    0 < Z.abs i -> Z.abs i <= K -> 0 < Z.abs j -> Z.abs j <= K -> i <> j ->
    j * (s2 - s1) <> i * (s3 - s1).

Theorem window_two : forall (n L h u t0 : Z) (T : Z -> Prop),
  0 < n -> 0 < L ->
  (forall t, T t -> 0 <= t /\ 8 * L * t < n) ->
  NoRelZ T (2 * L) ->
  (forall a, 0 < a <= 2 * L -> ~ (n | a * h)) ->          (* 2L < addOrderOf h *)
  forall j i1 i2 i3 t1 t2 t3,
    j <= i1 -> i1 < i2 -> i2 < i3 -> i3 < j + 2 * L ->
    T t1 -> T t2 -> T t3 ->
    (n | t0 + i1 * h - (t1 + u)) -> (n | t0 + i2 * h - (t2 + u)) -> (n | t0 + i3 * h - (t3 + u)) ->
    False.
Proof.
  intros n L h u t0 T Hn HL HT HNR Hord j i1 i2 i3 t1 t2 t3 Hj1 H12 H23 H3 T1 T2 T3 E1 E2 E3.
  set (a := i2 - i1). set (b := i3 - i1).
  assert (Ha : 0 < a < 2 * L) by (unfold a; lia).
  assert (Hb : a < b < 2 * L) by (unfold a, b; lia).
  (* D1 : n | a*h - (t2 - t1),  D2 : n | b*h - (t3 - t1) *)
  assert (D1 : (n | a * h - (t2 - t1))).
  { replace (a * h - (t2 - t1)) with ((t0 + i2 * h - (t2 + u)) - (t0 + i1 * h - (t1 + u)))
      by (unfold a; ring). now apply Z.divide_sub_r. }
  assert (D2 : (n | b * h - (t3 - t1))).
  { replace (b * h - (t3 - t1)) with ((t0 + i3 * h - (t3 + u)) - (t0 + i1 * h - (t1 + u)))
      by (unfold b; ring). now apply Z.divide_sub_r. }
  (* n | E := a*(t3 - t1) - b*(t2 - t1) *)
  assert (DE : (n | a * (t3 - t1) - b * (t2 - t1))).
  { replace (a * (t3 - t1) - b * (t2 - t1)) with (b * (a * h - (t2 - t1)) - a * (b * h - (t3 - t1)))
      by ring.
    apply Z.divide_sub_r; now apply Z.divide_mul_r. }
  destruct (HT t1 T1) as [P1 B1]. destruct (HT t2 T2) as [P2 B2]. destruct (HT t3 T3) as [P3 B3].
  (* |E| < n, so E = 0 *)
  assert (Up : 8 * L * (a * (t3 - t1) - b * (t2 - t1)) < n * b).
  { assert (8 * L * (a * t3) <= a * n) by nia.
    assert (0 <= 8 * L * ((b - a) * t1)) by nia.
    assert (0 <= 8 * L * (b * t2)) by nia.
    nia. }
  assert (Lo : - (n * b) < 8 * L * (a * (t3 - t1) - b * (t2 - t1))).
  { assert (8 * L * (b * t2) <= b * n) by nia.
    assert (8 * L * ((b - a) * t1) <= (b - a) * n) by nia.
    nia. }
  assert (EZ : a * (t3 - t1) - b * (t2 - t1) = 0).
  { destruct DE as [c Hc]. rewrite Hc in Up, Lo.
    assert (c * (8 * L) < b) by nia. assert (- b < c * (8 * L)) by nia.
    assert (c = 0) by nia. subst c. lia. }
  (* collinearity: distinct t's contradict NoRel; equal t's contradict the order of h *)
  destruct (Z.eq_dec t1 t2) as [e12|n12].
  - apply (Hord a); [lia|]. rewrite e12 in D1. now replace (a * h) with (a * h - (t2 - t2)) by ring.
  - destruct (Z.eq_dec t1 t3) as [e13|n13].
    + apply (Hord b); [lia|]. rewrite e13 in D2. now replace (b * h) with (b * h - (t3 - t3)) by ring.
    + destruct (Z.eq_dec t2 t3) as [e23|n23].
      * subst t3. apply n12. assert ((a - b) * (t2 - t1) = 0) by lia.
        apply Z.mul_eq_0 in H as [H|H]; lia.
      * apply (HNR t1 t2 t3 a b T1 T2 T3 n12 n13 n23); try (rewrite ?Z.abs_eq; lia).
Qed.

Print Assumptions window_two.

(* The sphere set of thick_set_exists, built with coefficient bound 2L, satisfies
   the WindowTwo conclusion: composition of the two rebuilt lemmas. *)
Corollary thick_set_window_two : forall (L : Z) (K d : nat) (b : Z),
  (1 <= d)%nat -> 1 <= L -> 4 * (2 * L) * Z.of_nat d < b ->
  exists T : list Z,
    (Nat.pow d K <= S (K * (d - 1) * (d - 1)) * length T)%nat /\
    forall (n h u t0 : Z), 0 < n -> (forall t, In t T -> 8 * L * t < n) ->
      (forall a, 0 < a <= 2 * L -> ~ (n | a * h)) ->
      forall j i1 i2 i3 t1 t2 t3,
        j <= i1 -> i1 < i2 -> i2 < i3 -> i3 < j + 2 * L ->
        In t1 T -> In t2 T -> In t3 T ->
        (n | t0 + i1 * h - (t1 + u)) -> (n | t0 + i2 * h - (t2 + u)) ->
        (n | t0 + i3 * h - (t3 + u)) -> False.
Proof.
  intros L K d b Hd HL Hb.
  destruct (thick_set_exists (2 * L) K d b Hd ltac:(lia) Hb) as [T [_ [Hrange [HNR Hc]]]].
  exists T. split; [exact Hc|].
  intros n h u t0 Hn HTn Hord.
  assert (HT' : forall t, In t T -> 0 <= t /\ 8 * L * t < n)
    by (intros t Ht; split; [apply (Hrange t Ht) | apply HTn, Ht]).
  assert (HNR' : NoRelZ (fun t => In t T) (2 * L)).
  { intros s1 s2 s3 i j H1 H2 H3 N12 N13 N23 Hi1 Hi2 Hj1 Hj2 Hij.
    exact (HNR s1 s2 s3 i j H1 H2 H3 N12 N13 N23 Hi1 Hi2 Hj1 Hj2 Hij). }
  exact (window_two n L h u t0 (fun t => In t T) Hn ltac:(lia) HT' HNR' Hord).
Qed.

Print Assumptions thick_set_window_two.

(* The size side condition of thick_set_window_two discharged: the sphere set
   lives in [0, b^K), so any modulus n >= 8 L b^K satisfies 8 L t < n. *)
Corollary thick_set_window_two_sized : forall (L : Z) (K d : nat) (b : Z),
  (1 <= d)%nat -> 1 <= L -> 4 * (2 * L) * Z.of_nat d < b ->
  exists T : list Z,
    (Nat.pow d K <= S (K * (d - 1) * (d - 1)) * length T)%nat /\
    forall (n h u t0 : Z), 8 * L * b ^ Z.of_nat K <= n ->
      (forall a, 0 < a <= 2 * L -> ~ (n | a * h)) ->
      forall j i1 i2 i3 t1 t2 t3,
        j <= i1 -> i1 < i2 -> i2 < i3 -> i3 < j + 2 * L ->
        In t1 T -> In t2 T -> In t3 T ->
        (n | t0 + i1 * h - (t1 + u)) -> (n | t0 + i2 * h - (t2 + u)) ->
        (n | t0 + i3 * h - (t3 + u)) -> False.
Proof.
  intros L K d b Hd HL Hb.
  destruct (thick_set_exists (2 * L) K d b Hd ltac:(lia) Hb) as [T [_ [Hrange [HNR Hc]]]].
  exists T. split; [exact Hc|].
  intros n h u t0 Hn Hord.
  assert (HT' : forall t, In t T -> 0 <= t /\ 8 * L * t < n).
  { intros t Ht. destruct (Hrange t Ht) as [H0 H1]. split; [exact H0|]. nia. }
  assert (HNR' : NoRelZ (fun t => In t T) (2 * L)).
  { intros s1 s2 s3 i j H1 H2 H3 N12 N13 N23 Hi1 Hi2 Hj1 Hj2 Hij.
    exact (HNR s1 s2 s3 i j H1 H2 H3 N12 N13 N23 Hi1 Hi2 Hj1 Hj2 Hij). }
  assert (Hbpos : 0 < b ^ Z.of_nat K) by (apply Z.pow_pos_nonneg; lia).
  exact (window_two n L h u t0 (fun t => In t T) ltac:(nia) ltac:(lia) HT' HNR' Hord).
Qed.

Print Assumptions thick_set_window_two_sized.
