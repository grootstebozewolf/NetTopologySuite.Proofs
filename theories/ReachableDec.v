(* ==========================================================================
   ReachableDec.v

   Phase C / Rung 3b-vii of the H_bridge Euler route.

   Decidability of undirected vertex reachability over a finite edge list --
   the piece `MapCounts.v` flagged as missing ("Once `reachable_dec` lands,
   `num_components` instantiates the same generic class-counting machinery").

   `reachable E u v` (EdgeConnectivity.v) is the reflexive-transitive closure
   of `adj`.  We decide it by a bounded breadth-first closure: `reach_iter`
   expands the frontier `length (verts E) + 1` times, which suffices because
   the reachable set is a monotone, bounded subset of `u :: verts E` and so
   saturates within that many steps (a NoDup-length pigeonhole).  Soundness is
   a direct induction; completeness is the saturation argument.

   Pure Point + list combinatorics; no `Admitted` / `Axiom` / `Parameter`;
   allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import List Arith Lia.
From NTS.Proofs Require Import Distance Overlay OverlayGraph EdgeConnectivity.

Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  Vertices, neighbours, and one breadth-first expansion step.             *)
(* -------------------------------------------------------------------------- *)

(* All endpoints occurring in `E`. *)
Definition verts (E : list Edge) : list Point :=
  flat_map (fun e => fst e :: snd e :: nil) E.

Lemma in_verts : forall E p,
  In p (verts E) <-> exists e, In e E /\ (fst e = p \/ snd e = p).
Proof.
  intros E p. unfold verts. rewrite in_flat_map. split.
  - intros [e [He Hp]]. exists e. split; [ exact He | cbn in Hp; tauto ].
  - intros [e [He Hp]]. exists e. split; [ exact He | cbn; tauto ].
Qed.

(* The undirected neighbours of `u` in `E`. *)
Definition neighbors (E : list Edge) (u : Point) : list Point :=
  flat_map (fun e =>
    (if point_eq_dec (fst e) u then snd e :: nil else nil) ++
    (if point_eq_dec (snd e) u then fst e :: nil else nil)) E.

Lemma in_neighbors : forall E u v, In v (neighbors E u) <-> adj E u v.
Proof.
  intros E u v. unfold neighbors, adj. rewrite in_flat_map. split.
  - intros [e [He Hv]]. exists e. split; [ exact He | ].
    rewrite in_app_iff in Hv. destruct Hv as [Hv | Hv].
    + destruct (point_eq_dec (fst e) u) as [Hfe | Hfe]; [ | destruct Hv ].
      cbn in Hv. destruct Hv as [Hv | []]. left. split; [ exact Hfe | exact Hv ].
    + destruct (point_eq_dec (snd e) u) as [Hse | Hse]; [ | destruct Hv ].
      cbn in Hv. destruct Hv as [Hv | []]. right. split; [ exact Hv | exact Hse ].
  - intros [e [He Hor]]. exists e. split; [ exact He | rewrite in_app_iff ].
    destruct Hor as [[Hfe Hsv] | [Hfv Hse]].
    + left. destruct (point_eq_dec (fst e) u) as [_ | Hn];
        [ cbn; left; exact Hsv | contradiction ].
    + right. destruct (point_eq_dec (snd e) u) as [_ | Hn];
        [ cbn; left; exact Hfv | contradiction ].
Qed.

Lemma neighbors_in_verts : forall E u v, In v (neighbors E u) -> In v (verts E).
Proof.
  intros E u v Hv. apply in_neighbors in Hv. destruct Hv as [e [He Hor]].
  apply in_verts. exists e. split; [ exact He | ].
  destruct Hor as [[_ Hsv] | [Hfv _]]; [ right; exact Hsv | left; exact Hfv ].
Qed.

(* One frontier expansion: keep `R`, add every neighbour of every member. *)
Definition expand (E : list Edge) (R : list Point) : list Point :=
  R ++ flat_map (neighbors E) R.

Lemma in_expand : forall E R x,
  In x (expand E R) <-> In x R \/ (exists r, In r R /\ In x (neighbors E r)).
Proof. intros E R x. unfold expand. rewrite in_app_iff, in_flat_map. reflexivity. Qed.

Lemma expand_mono : forall E R R',
  incl R R' -> incl (expand E R) (expand E R').
Proof.
  intros E R R' H x Hx. apply in_expand in Hx. apply in_expand.
  destruct Hx as [Hx | [r [Hr Hrx]]].
  - left. apply H. exact Hx.
  - right. exists r. split; [ apply H; exact Hr | exact Hrx ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Iterated expansion and its basic algebra.                               *)
(* -------------------------------------------------------------------------- *)

Fixpoint reach_iter (E : list Edge) (R : list Point) (n : nat) : list Point :=
  match n with
  | O => R
  | S n' => reach_iter E (expand E R) n'
  end.

Lemma reach_iter_succ : forall E R n,
  reach_iter E R (S n) = expand E (reach_iter E R n).
Proof.
  intros E R n. revert R. induction n as [| n IH]; intro R.
  - reflexivity.
  - change (reach_iter E (expand E R) (S n) = expand E (reach_iter E R (S n))).
    change (reach_iter E R (S n)) with (reach_iter E (expand E R) n).
    apply IH.
Qed.

Lemma reach_iter_incl_mono : forall E n R R',
  incl R R' -> incl (reach_iter E R n) (reach_iter E R' n).
Proof.
  intros E n. induction n as [| n IH]; intros R R' H.
  - exact H.
  - cbn [reach_iter]. apply IH. apply expand_mono. exact H.
Qed.

(* §2a  Single-source iteration `reach_iter E [u] n`. *)

Lemma rf_inc : forall E u n,
  incl (reach_iter E [u] n) (reach_iter E [u] (S n)).
Proof.
  intros E u n x Hx. rewrite reach_iter_succ. apply in_expand. left. exact Hx.
Qed.

Lemma rf_mono : forall E u n m,
  (m <= n)%nat -> incl (reach_iter E [u] m) (reach_iter E [u] n).
Proof.
  intros E u n. induction n as [| n IH]; intros m Hm.
  - assert (m = 0)%nat by lia. subst. apply incl_refl.
  - destruct (Nat.eq_dec m (S n)) as [-> | Hne].
    + apply incl_refl.
    + apply incl_tran with (reach_iter E [u] n); [ apply IH; lia | apply rf_inc ].
Qed.

Lemma rf_subU : forall E u n,
  incl (reach_iter E [u] n) (u :: verts E).
Proof.
  intros E u n. induction n as [| n IH].
  - intros x [<- | []]. left. reflexivity.
  - rewrite reach_iter_succ. intros x Hx. apply in_expand in Hx.
    destruct Hx as [Hx | [r [Hr Hrx]]].
    + apply IH. exact Hx.
    + right. apply (neighbors_in_verts E r x). exact Hrx.
Qed.

(* Once a step adds nothing, the closure is stable forever after. *)
Lemma rf_stab_propagate : forall E u n,
  incl (reach_iter E [u] (S n)) (reach_iter E [u] n) ->
  forall j, incl (reach_iter E [u] (n + j)) (reach_iter E [u] n).
Proof.
  intros E u n Hstab j. induction j as [| j IH].
  - rewrite Nat.add_0_r. apply incl_refl.
  - replace (n + S j)%nat with (S (n + j))%nat by lia.
    rewrite reach_iter_succ. intros x Hx. apply in_expand in Hx.
    destruct Hx as [Hx | [r [Hr Hrx]]].
    + apply IH. exact Hx.
    + apply Hstab. rewrite reach_iter_succ. apply in_expand. right.
      exists r. split; [ apply IH; exact Hr | exact Hrx ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Soundness and (unbounded) completeness of the closure.                  *)
(* -------------------------------------------------------------------------- *)

Lemma reach_iter_sound : forall E n R u,
  (forall x, In x R -> reachable E u x) ->
  forall v, In v (reach_iter E R n) -> reachable E u v.
Proof.
  intros E n. induction n as [| n IH]; intros R u Hbase v Hv.
  - apply Hbase. exact Hv.
  - cbn [reach_iter] in Hv. apply (IH (expand E R) u); [ | exact Hv ].
    intros x Hx. apply in_expand in Hx. destruct Hx as [Hx | [r [Hr Hrx]]].
    + apply Hbase. exact Hx.
    + apply reach_trans with r; [ apply Hbase; exact Hr | ].
      apply reach_one. apply in_neighbors in Hrx. exact Hrx.
Qed.

Lemma reachable_reach_iter_ex : forall E u v,
  reachable E u v -> exists k, In v (reach_iter E [u] k).
Proof.
  intros E u v Hr. induction Hr as [w | w x y Hadj Hrec IH].
  - exists 0%nat. left. reflexivity.
  - destruct IH as [k Hk]. exists (S k).
    change (In y (reach_iter E (expand E [w]) k)).
    refine (reach_iter_incl_mono E k [x] (expand E [w]) _ y Hk).
    intros z [<- | []]. apply in_expand. right.
    exists w. split; [ left; reflexivity | rewrite in_neighbors; exact Hadj ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Finite combinatorial scaffolding for the saturation bound.              *)
(* -------------------------------------------------------------------------- *)

(* A failed `incl` yields an explicit witness (decidable membership). *)
Lemma not_incl_witness : forall (B A : list Point),
  ~ incl B A -> exists x, In x B /\ ~ In x A.
Proof.
  induction B as [| b B' IH]; intros A H.
  - exfalso. apply H. intros x Hx. inversion Hx.
  - destruct (in_dec point_eq_dec b A) as [HbA | HbA].
    + assert (HnB' : ~ incl B' A).
      { intro HiB'. apply H. intros y [<- | Hy]; [ exact HbA | apply HiB'; exact Hy ]. }
      destruct (IH A HnB') as [x [Hx Hnx]]. exists x. split; [ right; exact Hx | exact Hnx ].
    + exists b. split; [ left; reflexivity | exact HbA ].
Qed.

(* `incl` on point lists is decidable. *)
Lemma incl_dec_pt : forall A B : list Point, {incl A B} + {~ incl A B}.
Proof.
  intros A B. induction A as [| a A' IH].
  - left. intros x Hx. inversion Hx.
  - destruct (in_dec point_eq_dec a B) as [Ha | Ha].
    + destruct IH as [Hincl | Hnincl].
      * left. intros x [<- | Hx]; [ exact Ha | apply Hincl; exact Hx ].
      * right. intro Hc. apply Hnincl. intros x Hx. apply Hc. right. exact Hx.
    + right. intro Hc. apply Ha. apply Hc. left. reflexivity.
Qed.

(* Bounded search for a decidable predicate. *)
Lemma find_or_all : forall (P : nat -> Prop),
  (forall n, {P n} + {~ P n}) ->
  forall M, (exists n, n < M /\ P n)%nat \/ (forall n, (n < M)%nat -> ~ P n).
Proof.
  intros P Pdec. induction M as [| M IH].
  - right. intros n Hn. lia.
  - destruct IH as [[n [Hn HPn]] | Hall].
    + left. exists n. split; [ lia | exact HPn ].
    + destruct (Pdec M) as [HPM | HnPM].
      * left. exists M. split; [ lia | exact HPM ].
      * right. intros n Hn. destruct (Nat.eq_dec n M) as [-> | Hne];
          [ exact HnPM | apply Hall; lia ].
Qed.

(* A strictly larger inclusion strictly increases the deduplicated length. *)
Lemma nodup_incl_lt : forall (A B : list Point) x,
  incl A B -> In x B -> ~ In x A ->
  (length (nodup point_eq_dec A) < length (nodup point_eq_dec B))%nat.
Proof.
  intros A B x HAB HxB HxA.
  apply Nat.lt_le_trans with (m := length (x :: nodup point_eq_dec A)).
  - cbn [length]. lia.
  - apply NoDup_incl_length.
    + constructor; [ rewrite nodup_In; exact HxA | apply NoDup_nodup ].
    + intros y [<- | Hy].
      * rewrite nodup_In. exact HxB.
      * rewrite nodup_In in Hy. rewrite nodup_In. apply HAB. exact Hy.
Qed.

(* A pointwise-strictly-increasing length function grows at least linearly. *)
Lemma dchain : forall (d : nat -> nat) M,
  (forall n, (n < M)%nat -> d n < d (S n)) -> (d 0 + M <= d M)%nat.
Proof.
  intros d M H. induction M as [| M IH].
  - lia.
  - assert (d 0 + M <= d M)%nat by (apply IH; intros n Hn; apply H; lia).
    assert (d M < d (S M))%nat by (apply H; lia). lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Saturation: the closure stabilises within `length (verts E) + 1`.       *)
(* -------------------------------------------------------------------------- *)

Lemma rf_sat : forall E u k,
  incl (reach_iter E [u] k) (reach_iter E [u] (S (length (verts E)))).
Proof.
  intros E u k. set (N := S (length (verts E))).
  destruct (find_or_all
              (fun n => incl (reach_iter E [u] (S n)) (reach_iter E [u] n))
              (fun n => incl_dec_pt (reach_iter E [u] (S n)) (reach_iter E [u] n))
              (S N)) as [[n0 [Hn0lt Hstab]] | Hall].
  - destruct (le_gt_dec k N) as [HkN | HkN].
    + apply rf_mono. exact HkN.
    + apply incl_tran with (reach_iter E [u] n0).
      * replace k with (n0 + (k - n0))%nat by lia.
        apply rf_stab_propagate. exact Hstab.
      * apply rf_mono. lia.
  - exfalso.
    assert (Hchain : (length (nodup point_eq_dec (reach_iter E [u] 0)) + S N
                      <= length (nodup point_eq_dec (reach_iter E [u] (S N))))%nat).
    { apply (dchain (fun n => length (nodup point_eq_dec (reach_iter E [u] n))) (S N)).
      intros n Hn.
      destruct (not_incl_witness (reach_iter E [u] (S n)) (reach_iter E [u] n) (Hall n Hn))
        as [x [Hx Hnx]].
      apply (nodup_incl_lt (reach_iter E [u] n) (reach_iter E [u] (S n)) x);
        [ apply rf_inc | exact Hx | exact Hnx ]. }
    assert (Hd0 : length (nodup point_eq_dec (reach_iter E [u] 0)) = 1%nat).
    { simpl. reflexivity. }
    assert (HdN : (length (nodup point_eq_dec (reach_iter E [u] (S N)))
                   <= length (u :: verts E))%nat).
    { apply NoDup_incl_length; [ apply NoDup_nodup | ].
      intros x Hx. rewrite nodup_In in Hx. apply (rf_subU E u (S N)). exact Hx. }
    cbn [length] in HdN. unfold N in *. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  The decision procedure.                                                 *)
(* -------------------------------------------------------------------------- *)

Theorem reachable_dec : forall E u v, {reachable E u v} + {~ reachable E u v}.
Proof.
  intros E u v.
  destruct (in_dec point_eq_dec v (reach_iter E [u] (S (length (verts E)))))
    as [Hin | Hnin].
  - left. apply (reach_iter_sound E (S (length (verts E))) [u] u).
    + intros x [<- | []]. apply reach_refl.
    + exact Hin.
  - right. intro Hr. apply Hnin.
    destruct (reachable_reach_iter_ex E u v Hr) as [k Hk].
    apply (rf_sat E u k). exact Hk.
Qed.

(* Boolean reflection, convenient for class counting. *)
Definition reachable_b (E : list Edge) (u v : Point) : bool :=
  if reachable_dec E u v then true else false.

Lemma reachable_b_true_iff : forall E u v,
  reachable_b E u v = true <-> reachable E u v.
Proof.
  intros E u v. unfold reachable_b.
  destruct (reachable_dec E u v) as [H | H]; split; intro; auto; discriminate.
Qed.

Lemma reachable_b_refl : forall E x, reachable_b E x x = true.
Proof. intros E x. apply reachable_b_true_iff. apply reach_refl. Qed.

(* -------------------------------------------------------------------------- *)
(* §7  Component count: the number of reachability classes of the vertices.    *)
(*     This is the Euler quantity MapCounts.v deferred pending `reachable_dec`. *)
(* -------------------------------------------------------------------------- *)

(* One representative kept per reachability class (first occurrence). *)
Fixpoint comp_reps (E : list Edge) (l : list Point) : list Point :=
  match l with
  | [] => []
  | x :: l' =>
      let rs := comp_reps E l' in
      if existsb (fun z => reachable_b E z x) rs then rs else x :: rs
  end.

(* The number of distinct reachability classes among the vertices of `E`. *)
Definition num_components (E : list Edge) : nat :=
  length (comp_reps E (nodup point_eq_dec (verts E))).

Lemma comp_reps_incl : forall E l r, In r (comp_reps E l) -> In r l.
Proof.
  intros E l. induction l as [| a l IH]; intros r Hr; [ exact Hr | ].
  cbn [comp_reps] in Hr.
  destruct (existsb (fun z => reachable_b E z a) (comp_reps E l)).
  - right. apply IH. exact Hr.
  - destruct Hr as [Hr | Hr]; [ left; exact Hr | right; apply IH; exact Hr ].
Qed.

(* Every vertex is covered by some representative's reachability class. *)
Lemma comp_reps_cover : forall E l x, In x l ->
  exists r, In r (comp_reps E l) /\ reachable_b E r x = true.
Proof.
  intros E l. induction l as [| a l IH]; intros x Hx; [ destruct Hx | ].
  cbn [comp_reps].
  destruct (existsb (fun z => reachable_b E z a) (comp_reps E l)) eqn:He.
  - destruct Hx as [Hxa | Hxl].
    + subst x. apply existsb_exists in He. destruct He as [z [Hz Hzb]].
      exists z. split; [ exact Hz | exact Hzb ].
    + destruct (IH x Hxl) as [r [Hr Hrb]]. exists r. split; [ exact Hr | exact Hrb ].
  - destruct Hx as [Hxa | Hxl].
    + subst x. exists a. split; [ left; reflexivity | apply reachable_b_refl ].
    + destruct (IH x Hxl) as [r [Hr Hrb]].
      exists r. split; [ right; exact Hr | exact Hrb ].
Qed.

(* A graph with at least one vertex has at least one component. *)
Lemma num_components_pos : forall E, verts E <> [] -> (1 <= num_components E)%nat.
Proof.
  intros E Hne. unfold num_components.
  destruct (nodup point_eq_dec (verts E)) as [| v0 vs] eqn:Hnd.
  - exfalso. destruct (verts E) as [| p ps] eqn:Hv.
    + apply Hne. reflexivity.
    + assert (Hin : In p (nodup point_eq_dec (p :: ps))) by
        (apply nodup_In; left; reflexivity).
      rewrite Hnd in Hin. destruct Hin.
  - destruct (comp_reps_cover E (v0 :: vs) v0 (or_introl eq_refl)) as [r [Hr _]].
    destruct (comp_reps E (v0 :: vs)) as [| r0 rs];
      [ destruct Hr | cbn [length]; lia ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure Point + list combinatorics; allowlist axioms only.       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions reachable_dec.
Print Assumptions reachable_b_true_iff.
Print Assumptions num_components_pos.
