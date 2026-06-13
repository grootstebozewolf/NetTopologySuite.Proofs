(* ============================================================================
   NetTopologySuite.Proofs.MonotoneChainParity
   ----------------------------------------------------------------------------
   Convex-chain monotonicity campaign, RUNG 1: a y-monotone edge chain is
   crossed by the rightward ray at most once.

   This is the reusable, n-independent geometric core the corpus lacked.  A
   convex polygon's boundary splits into an increasing and a decreasing
   y-monotone chain (rung 2, not here); each is crossed at most once by a
   horizontal ray because its per-edge OPEN y-intervals are
   consecutive-and-disjoint -- no x-arithmetic, no per-vertex case blow-up.
   Rung 3 (interior point => exactly one rightward crossing => point_in_ring =>
   `ConvexNesting.convex_interior_parity`) builds on this.

   No x-interval reasoning is needed for the "at most once": an UP edge is
   crossed only through the `py a < py p < py b` disjunct of `edge_crosses_ray`,
   and strict monotonicity makes those y-intervals disjoint.

   Pure-R + list induction; three-axiom.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List Lra Lia PeanoNat Setoid Bool.
From NTS.Proofs Require Import Distance Overlay.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Monotone chain predicates.                                              *)
(* -------------------------------------------------------------------------- *)

Definition edge_up (e : Edge) : Prop := py (fst e) < py (snd e).
Definition edge_dn (e : Edge) : Prop := py (snd e) < py (fst e).

(* `straddles p e`: the ray's height is strictly inside the edge's y-span.    *)
Definition straddles (p : Point) (e : Edge) : Prop :=
  py (fst e) < py p < py (snd e) \/ py (snd e) < py p < py (fst e).

(* A connected, strictly-upward edge chain. *)
Fixpoint chain_increasing (es : list Edge) : Prop :=
  match es with
  | [] => True
  | e :: rest =>
      edge_up e /\
      match rest with
      | [] => True
      | e2 :: _ => snd e = fst e2 /\ chain_increasing rest
      end
  end.

Fixpoint chain_decreasing (es : list Edge) : Prop :=
  match es with
  | [] => True
  | e :: rest =>
      edge_dn e /\
      match rest with
      | [] => True
      | e2 :: _ => snd e = fst e2 /\ chain_decreasing rest
      end
  end.

(* -------------------------------------------------------------------------- *)
(* §2  Crossing forces a y-straddle.                                           *)
(* -------------------------------------------------------------------------- *)

Lemma crossed_straddles : forall p e, edge_crosses_ray p e -> straddles p e.
Proof.
  intros p [a b] Hc. unfold edge_crosses_ray, straddles in *. cbn [fst snd] in *.
  destruct Hc as [[Hy _] | [Hy _]]; [ left | right ]; exact Hy.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Increasing chains: at most one crossing.                                *)
(* -------------------------------------------------------------------------- *)

Lemma chain_increasing_all_up : forall es,
  chain_increasing es -> Forall edge_up es.
Proof.
  induction es as [| e rest IH]; intros Hc.
  - constructor.
  - simpl in Hc. destruct rest as [| e2 rest'].
    + destruct Hc as [Hup _]. constructor; [ exact Hup | constructor ].
    + destruct Hc as [Hup [_ Hrest]]. constructor; [ exact Hup | apply IH; exact Hrest ].
Qed.

(* Every later edge's bottom sits at or above the head edge's top. *)
Lemma chain_increasing_above : forall e rest,
  chain_increasing (e :: rest) ->
  Forall (fun e' => py (snd e) <= py (fst e')) rest.
Proof.
  intros e rest. revert e. induction rest as [| e2 rest' IH]; intros e Hc.
  - constructor.
  - simpl in Hc. destruct Hc as [_ [Hconn Hrest]].
    constructor.
    + rewrite Hconn. lra.
    + pose proof (IH e2 Hrest) as Hf.
      simpl in Hrest. destruct Hrest as [Hup2 _].
      eapply Forall_impl; [ | exact Hf ]. intros a Ha.
      unfold edge_up in Hup2. rewrite Hconn. lra.
Qed.

(* For an UP chain only the upward straddle is possible. *)
Lemma up_straddle_lo_hi : forall p e,
  edge_up e -> straddles p e -> py (fst e) < py p < py (snd e).
Proof.
  intros p e Hup Hs. unfold edge_up in Hup. unfold straddles in Hs.
  destruct Hs as [H | H]; [ exact H | lra ].
Qed.

Lemma inc_chain_le_one_straddle : forall es p e1 e2,
  chain_increasing es -> In e1 es -> In e2 es ->
  straddles p e1 -> straddles p e2 -> e1 = e2.
Proof.
  induction es as [| e rest IH]; intros p f g Hc Hf Hg Hsf Hsg.
  - inversion Hf.
  - pose proof (chain_increasing_all_up _ Hc) as Hallup.
    destruct Hf as [<- | Hf]; destruct Hg as [<- | Hg].
    + reflexivity.
    + exfalso.
      pose proof (chain_increasing_above e rest Hc) as Hab.
      rewrite Forall_forall in Hab. specialize (Hab g Hg).
      rewrite Forall_forall in Hallup.
      pose proof (up_straddle_lo_hi p e (Hallup e (or_introl eq_refl)) Hsf) as Hf'.
      pose proof (up_straddle_lo_hi p g (Hallup g (or_intror Hg)) Hsg) as Hg'.
      lra.
    + exfalso.
      pose proof (chain_increasing_above e rest Hc) as Hab.
      rewrite Forall_forall in Hab. specialize (Hab f Hf).
      rewrite Forall_forall in Hallup.
      pose proof (up_straddle_lo_hi p e (Hallup e (or_introl eq_refl)) Hsg) as Hg'.
      pose proof (up_straddle_lo_hi p f (Hallup f (or_intror Hf)) Hsf) as Hf'.
      lra.
    + destruct rest as [| e2' rest'].
      * inversion Hf.
      * simpl in Hc. destruct Hc as [_ [_ Hcr]].
        exact (IH p f g Hcr Hf Hg Hsf Hsg).
Qed.

Theorem inc_chain_le_one_cross : forall es p e1 e2,
  chain_increasing es -> In e1 es -> In e2 es ->
  edge_crosses_ray p e1 -> edge_crosses_ray p e2 -> e1 = e2.
Proof.
  intros es p e1 e2 Hc H1 H2 Hx1 Hx2.
  apply (inc_chain_le_one_straddle es p e1 e2 Hc H1 H2);
    apply crossed_straddles; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Decreasing chains: at most one crossing (mirror).                       *)
(* -------------------------------------------------------------------------- *)

Lemma chain_decreasing_all_dn : forall es,
  chain_decreasing es -> Forall edge_dn es.
Proof.
  induction es as [| e rest IH]; intros Hc.
  - constructor.
  - simpl in Hc. destruct rest as [| e2 rest'].
    + destruct Hc as [Hdn _]. constructor; [ exact Hdn | constructor ].
    + destruct Hc as [Hdn [_ Hrest]]. constructor; [ exact Hdn | apply IH; exact Hrest ].
Qed.

Lemma chain_decreasing_below : forall e rest,
  chain_decreasing (e :: rest) ->
  Forall (fun e' => py (fst e') <= py (snd e)) rest.
Proof.
  intros e rest. revert e. induction rest as [| e2 rest' IH]; intros e Hc.
  - constructor.
  - simpl in Hc. destruct Hc as [_ [Hconn Hrest]].
    constructor.
    + rewrite Hconn. lra.
    + pose proof (IH e2 Hrest) as Hf.
      simpl in Hrest. destruct Hrest as [Hdn2 _].
      eapply Forall_impl; [ | exact Hf ]. intros a Ha.
      unfold edge_dn in Hdn2. rewrite Hconn. lra.
Qed.

Lemma dn_straddle_hi_lo : forall p e,
  edge_dn e -> straddles p e -> py (snd e) < py p < py (fst e).
Proof.
  intros p e Hdn Hs. unfold edge_dn in Hdn. unfold straddles in Hs.
  destruct Hs as [H | H]; [ lra | exact H ].
Qed.

Lemma dec_chain_le_one_straddle : forall es p e1 e2,
  chain_decreasing es -> In e1 es -> In e2 es ->
  straddles p e1 -> straddles p e2 -> e1 = e2.
Proof.
  induction es as [| e rest IH]; intros p f g Hc Hf Hg Hsf Hsg.
  - inversion Hf.
  - pose proof (chain_decreasing_all_dn _ Hc) as Halldn.
    destruct Hf as [<- | Hf]; destruct Hg as [<- | Hg].
    + reflexivity.
    + exfalso.
      pose proof (chain_decreasing_below e rest Hc) as Hbe.
      rewrite Forall_forall in Hbe. specialize (Hbe g Hg).
      rewrite Forall_forall in Halldn.
      pose proof (dn_straddle_hi_lo p e (Halldn e (or_introl eq_refl)) Hsf) as Hf'.
      pose proof (dn_straddle_hi_lo p g (Halldn g (or_intror Hg)) Hsg) as Hg'.
      lra.
    + exfalso.
      pose proof (chain_decreasing_below e rest Hc) as Hbe.
      rewrite Forall_forall in Hbe. specialize (Hbe f Hf).
      rewrite Forall_forall in Halldn.
      pose proof (dn_straddle_hi_lo p e (Halldn e (or_introl eq_refl)) Hsg) as Hg'.
      pose proof (dn_straddle_hi_lo p f (Halldn f (or_intror Hf)) Hsf) as Hf'.
      lra.
    + destruct rest as [| e2' rest'].
      * inversion Hf.
      * simpl in Hc. destruct Hc as [_ [_ Hcr]].
        exact (IH p f g Hcr Hf Hg Hsf Hsg).
Qed.

Theorem dec_chain_le_one_cross : forall es p e1 e2,
  chain_decreasing es -> In e1 es -> In e2 es ->
  edge_crosses_ray p e1 -> edge_crosses_ray p e2 -> e1 = e2.
Proof.
  intros es p e1 e2 Hc H1 H2 Hx1 Hx2.
  apply (dec_chain_le_one_straddle es p e1 e2 Hc H1 H2);
    apply crossed_straddles; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Decidability of `edge_crosses_ray` and a crossing COUNT.                *)
(*   The corpus counts ray crossings via the mutually-inductive               *)
(*   `ray_parity_odd/even`.  To assemble a chain decomposition we bridge that  *)
(*   to a numeric count and use ordinary arithmetic on it.                     *)
(* -------------------------------------------------------------------------- *)

Lemma dec_and : forall (A B : Prop), {A} + {~ A} -> {B} + {~ B} -> {A /\ B} + {~ (A /\ B)}.
Proof. intros A B [a|na] [b|nb]; [ left; split; assumption | right; tauto.. ]. Qed.

Lemma dec_or : forall (A B : Prop), {A} + {~ A} -> {B} + {~ B} -> {A \/ B} + {~ (A \/ B)}.
Proof. intros A B [a|na] [b|nb]; [ left; left; assumption | left; left; assumption
                                  | left; right; assumption | right; tauto ]. Qed.

Definition edge_crosses_ray_dec (p : Point) (e : Edge) :
  { edge_crosses_ray p e } + { ~ edge_crosses_ray p e }.
Proof.
  destruct e as [a b]. unfold edge_crosses_ray.
  apply dec_or; apply dec_and.
  - apply dec_and; apply Rlt_dec.
  - apply Rlt_dec.
  - apply dec_and; apply Rlt_dec.
  - apply Rlt_dec.
Defined.

Definition crosses_b (p : Point) (e : Edge) : bool :=
  if edge_crosses_ray_dec p e then true else false.

Lemma crosses_b_true : forall p e, crosses_b p e = true <-> edge_crosses_ray p e.
Proof.
  intros p e. unfold crosses_b. destruct (edge_crosses_ray_dec p e) as [H|H].
  - split; [ intros _; exact H | reflexivity ].
  - split; [ discriminate | intros Hx; exfalso; exact (H Hx) ].
Qed.

Lemma crosses_b_false : forall p e, crosses_b p e = false <-> ~ edge_crosses_ray p e.
Proof.
  intros p e. unfold crosses_b. destruct (edge_crosses_ray_dec p e) as [H|H].
  - split; [ discriminate | intros Hn; exfalso; exact (Hn H) ].
  - split; [ intros _; exact H | reflexivity ].
Qed.

Definition cross_count (p : Point) (es : list Edge) : nat :=
  length (filter (crosses_b p) es).

Lemma cross_count_app : forall p es1 es2,
  cross_count p (es1 ++ es2) = (cross_count p es1 + cross_count p es2)%nat.
Proof.
  intros p es1 es2. unfold cross_count. rewrite filter_app, length_app. reflexivity.
Qed.

(* `chain_crossed p es`: some edge of `es` is crossed by the ray. *)
Definition chain_crossed (p : Point) (es : list Edge) : Prop :=
  exists e, In e es /\ edge_crosses_ray p e.

Lemma chain_crossed_iff_count : forall p es,
  chain_crossed p es <-> (cross_count p es <> 0)%nat.
Proof.
  intros p es. unfold chain_crossed, cross_count. split.
  - intros [e [Hin Hx]]. intros Hlen.
    apply length_zero_iff_nil in Hlen.
    assert (Hf : In e (filter (crosses_b p) es))
      by (apply filter_In; split; [ exact Hin | apply crosses_b_true; exact Hx ]).
    rewrite Hlen in Hf. inversion Hf.
  - intros Hlen. destruct (filter (crosses_b p) es) as [| e l] eqn:Heq.
    + simpl in Hlen. exfalso; apply Hlen; reflexivity.
    + assert (Hin : In e (filter (crosses_b p) es)) by (rewrite Heq; left; reflexivity).
      apply filter_In in Hin. destruct Hin as [Hin Hb].
      exists e. split; [ exact Hin | apply crosses_b_true; exact Hb ].
Qed.

Lemma cross_count_cons_cross : forall p e es,
  edge_crosses_ray p e -> cross_count p (e :: es) = S (cross_count p es).
Proof.
  intros p e es Hx. unfold cross_count. cbn [filter].
  replace (crosses_b p e) with true by (symmetry; apply crosses_b_true; exact Hx).
  reflexivity.
Qed.

Lemma cross_count_cons_nocross : forall p e es,
  ~ edge_crosses_ray p e -> cross_count p (e :: es) = cross_count p es.
Proof.
  intros p e es Hx. unfold cross_count. cbn [filter].
  replace (crosses_b p e) with false by (symmetry; apply crosses_b_false; exact Hx).
  reflexivity.
Qed.

Lemma cross_count_zero_of_no_cross : forall p es,
  Forall (fun e => ~ edge_crosses_ray p e) es -> cross_count p es = 0%nat.
Proof.
  intros p es H. apply length_zero_iff_nil.
  induction es as [| e rest IH]; [ reflexivity | ].
  inversion H as [| x l Hx Hrest]; subst.
  cbn [filter]. unfold crosses_b. destruct (edge_crosses_ray_dec p e) as [Hc|_].
  - exfalso; exact (Hx Hc).
  - apply IH; exact Hrest.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Parity (mutually-inductive) <-> count parity.  Reusable corpus-wide:    *)
(*   `point_in_ring` is `ray_parity_odd`, and this turns that into             *)
(*   `Nat.odd (cross_count …) = true`, where ordinary arithmetic applies.      *)
(* -------------------------------------------------------------------------- *)

Lemma odd_S : forall n, Nat.odd (S n) = negb (Nat.odd n).
Proof. intros n. rewrite Nat.odd_succ, <- Nat.negb_odd. reflexivity. Qed.

Lemma ray_parity_count : forall p es,
  (ray_parity_odd p es <-> Nat.odd (cross_count p es) = true) /\
  (ray_parity_even p es <-> Nat.odd (cross_count p es) = false).
Proof.
  intros p es. induction es as [| e rest [IHo IHe]].
  - split.
    + split; [ intros H; inversion H | discriminate ].
    + split; [ intros _; reflexivity | intros _; constructor ].
  - unfold cross_count in *. cbn [filter]. unfold crosses_b.
    destruct (edge_crosses_ray_dec p e) as [Hc|Hnc].
    + (* head crosses: count = S (count rest) *)
      cbn [length]. rewrite odd_S. split.
      * split.
        -- intros H. inversion H; subst.
           ++ apply negb_true_iff. apply IHe; assumption.
           ++ exfalso; contradiction.
        -- intros H. apply negb_true_iff in H. apply rpo_cross; [ exact Hc | apply IHe; exact H ].
      * split.
        -- intros H. inversion H; subst.
           ++ apply negb_false_iff. apply IHo; assumption.
           ++ exfalso; contradiction.
        -- intros H. apply negb_false_iff in H. apply rpe_cross; [ exact Hc | apply IHo; exact H ].
    + (* head does not cross: count = count rest *)
      split.
      * split.
        -- intros H. inversion H; subst.
           ++ exfalso; contradiction.
           ++ apply IHo; assumption.
        -- intros H. apply rpo_skip; [ exact Hnc | apply IHo; exact H ].
      * split.
        -- intros H. inversion H; subst.
           ++ exfalso; contradiction.
           ++ apply IHe; assumption.
        -- intros H. apply rpe_skip; [ exact Hnc | apply IHe; exact H ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §7  A monotone chain contributes AT MOST ONE to the crossing count.         *)
(* -------------------------------------------------------------------------- *)

Lemma chain_increasing_tail : forall e rest,
  chain_increasing (e :: rest) -> chain_increasing rest.
Proof.
  intros e rest Hc. simpl in Hc. destruct rest as [| e2 rest'].
  - constructor.
  - destruct Hc as [_ [_ Hr]]. exact Hr.
Qed.

Lemma chain_decreasing_tail : forall e rest,
  chain_decreasing (e :: rest) -> chain_decreasing rest.
Proof.
  intros e rest Hc. simpl in Hc. destruct rest as [| e2 rest'].
  - constructor.
  - destruct Hc as [_ [_ Hr]]. exact Hr.
Qed.

Lemma inc_head_no_rest_cross : forall p e rest,
  chain_increasing (e :: rest) -> edge_crosses_ray p e ->
  Forall (fun e' => ~ edge_crosses_ray p e') rest.
Proof.
  intros p e rest Hc Hx.
  pose proof (chain_increasing_all_up _ Hc) as Hup.
  pose proof (chain_increasing_above e rest Hc) as Hab.
  inversion Hup as [| x l Hupe Huprest Heq]; subst.
  pose proof (up_straddle_lo_hi p e Hupe (crossed_straddles _ _ Hx)) as He.
  rewrite Forall_forall. intros e' Hin Hxe'.
  rewrite Forall_forall in Hab, Huprest.
  pose proof (Hab e' Hin) as Hab'.
  pose proof (up_straddle_lo_hi p e' (Huprest e' Hin) (crossed_straddles _ _ Hxe')) as He'.
  lra.
Qed.

Lemma dec_head_no_rest_cross : forall p e rest,
  chain_decreasing (e :: rest) -> edge_crosses_ray p e ->
  Forall (fun e' => ~ edge_crosses_ray p e') rest.
Proof.
  intros p e rest Hc Hx.
  pose proof (chain_decreasing_all_dn _ Hc) as Hdn.
  pose proof (chain_decreasing_below e rest Hc) as Hbe.
  inversion Hdn as [| x l Hdne Hdnrest Heq]; subst.
  pose proof (dn_straddle_hi_lo p e Hdne (crossed_straddles _ _ Hx)) as He.
  rewrite Forall_forall. intros e' Hin Hxe'.
  rewrite Forall_forall in Hbe, Hdnrest.
  pose proof (Hbe e' Hin) as Hbe'.
  pose proof (dn_straddle_hi_lo p e' (Hdnrest e' Hin) (crossed_straddles _ _ Hxe')) as He'.
  lra.
Qed.

Lemma inc_cross_count_le_one : forall p es,
  chain_increasing es -> (cross_count p es <= 1)%nat.
Proof.
  intros p es. induction es as [| e rest IH]; intros Hc.
  - cbn. lia.
  - destruct (edge_crosses_ray_dec p e) as [Hx|Hnx].
    + rewrite (cross_count_cons_cross p e rest Hx).
      pose proof (inc_head_no_rest_cross p e rest Hc Hx) as Hno.
      pose proof (cross_count_zero_of_no_cross p rest Hno) as Hz. rewrite Hz. lia.
    + rewrite (cross_count_cons_nocross p e rest Hnx).
      apply IH. apply chain_increasing_tail with (e := e); exact Hc.
Qed.

Lemma dec_cross_count_le_one : forall p es,
  chain_decreasing es -> (cross_count p es <= 1)%nat.
Proof.
  intros p es. induction es as [| e rest IH]; intros Hc.
  - cbn. lia.
  - destruct (edge_crosses_ray_dec p e) as [Hx|Hnx].
    + rewrite (cross_count_cons_cross p e rest Hx).
      pose proof (dec_head_no_rest_cross p e rest Hc Hx) as Hno.
      pose proof (cross_count_zero_of_no_cross p rest Hno) as Hz. rewrite Hz. lia.
    + rewrite (cross_count_cons_nocross p e rest Hnx).
      apply IH. apply chain_decreasing_tail with (e := e); exact Hc.
Qed.

(* -------------------------------------------------------------------------- *)
(* §8  RUNG 2 — the bimonotone-split assembly.                                 *)
(*   If a ring's edges split into an increasing chain followed by a            *)
(*   decreasing chain, `point_in_ring` reduces to the EXCLUSIVE-OR of          *)
(*   "the increasing chain is crossed" and "the decreasing chain is crossed".  *)
(*   Each chain is crossed at most once (§7), so the whole ring is crossed     *)
(*   0, 1, or 2 times, and the parity is odd exactly when precisely one chain  *)
(*   is hit.  The two residuals this isolates for rung 3 are: (a) convexity    *)
(*   yields such a split; (b) a strictly-interior point hits exactly one       *)
(*   chain (the XOR is true).                                                  *)
(* -------------------------------------------------------------------------- *)

Definition bimonotone_split (r : Ring) (inc dec : list Edge) : Prop :=
  ring_edges r = inc ++ dec /\ chain_increasing inc /\ chain_decreasing dec.

Lemma le1_neq0_iff : forall n : nat, (n <= 1)%nat -> (n <> 0%nat <-> n = 1%nat).
Proof. intros n H. split; intros; lia. Qed.

Theorem bimonotone_split_parity : forall r inc dec p,
  bimonotone_split r inc dec ->
  ( point_in_ring p r <->
      ( (chain_crossed p inc /\ ~ chain_crossed p dec) \/
        (~ chain_crossed p inc /\ chain_crossed p dec) ) ).
Proof.
  intros r inc dec p (Hsplit & Hinc & Hdec).
  unfold point_in_ring. rewrite Hsplit.
  destruct (ray_parity_count p (inc ++ dec)) as [Hpar _].
  rewrite Hpar, cross_count_app.
  pose proof (inc_cross_count_le_one p inc Hinc) as Hi.
  pose proof (dec_cross_count_le_one p dec Hdec) as Hd.
  rewrite !(chain_crossed_iff_count p inc), !(chain_crossed_iff_count p dec).
  rewrite !(le1_neq0_iff _ Hi), !(le1_neq0_iff _ Hd).
  set (a := cross_count p inc) in *. set (b := cross_count p dec) in *.
  assert (Ha : (a = 0 \/ a = 1)%nat) by lia.
  assert (Hb : (b = 0 \/ b = 1)%nat) by lia.
  destruct Ha as [Ha|Ha]; destruct Hb as [Hb|Hb]; rewrite Ha, Hb; cbn [Nat.add Nat.odd].
  - (* 0,0: not crossed at all -> even -> outside *)
    split; intros H; [ discriminate | destruct H as [[H _]|[_ H]]; discriminate ].
  - (* 0,1: only the decreasing chain crossed -> odd -> inside *)
    split; intros H; [ right; split; [ discriminate | reflexivity ] | reflexivity ].
  - (* 1,0: only the increasing chain crossed -> odd -> inside *)
    split; intros H; [ left; split; [ reflexivity | discriminate ] | reflexivity ].
  - (* 1,1: both chains crossed -> even -> outside *)
    split; intros H; [ discriminate | destruct H as [[_ H]|[H _]]; congruence ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions inc_chain_le_one_cross.
Print Assumptions dec_chain_le_one_cross.
Print Assumptions ray_parity_count.
Print Assumptions bimonotone_split_parity.
