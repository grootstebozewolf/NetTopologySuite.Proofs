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

   Outcome: QED (host lane, Stdlib only), both theorems closed under the
   global context.  Not formalized: the final arithmetic that, with base
   b ~ (8L)^(1/eps'), the slice has density N^(-eps'-o(1)) in [0, b^K).  This is
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

(* Density: some sphere slice S_r of [0,d)^K has (K(d-1)^2 + 1) * |S_r| >= d^K,
   and (sphere_digits_norel) every such slice satisfies NoRel once 4Ld < b. *)
Theorem sphere_slice_large : forall K d, (1 <= d)%nat ->
  exists r : Z, exists Sl : list (list Z),
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
  split.
  - intros a Ha. apply filter_In in Ha as [Ha He]. apply Nat.eqb_eq in He.
    destruct (allvec_in K d a Ha) as [L F]. pose proof (dot_self_nonneg a).
    repeat split; auto. lia.
  - rewrite allvec_length in Hc. exact Hc.
Qed.

Print Assumptions sphere_slice_large.
