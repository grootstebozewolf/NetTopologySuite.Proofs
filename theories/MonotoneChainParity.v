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

From Stdlib Require Import Reals List Lra.
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
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions inc_chain_le_one_cross.
Print Assumptions dec_chain_le_one_cross.
