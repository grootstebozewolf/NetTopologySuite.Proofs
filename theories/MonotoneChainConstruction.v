(* ============================================================================
   NetTopologySuite.Proofs.MonotoneChainConstruction
   ----------------------------------------------------------------------------
   Convex-chain monotonicity campaign, RUNG 3.5: a GENERAL construction of the
   bimonotone split from a purely combinatorial y-unimodality hypothesis.

   `ConvexChainSplit.v` isolated `bimonotone_split` (the ring's edges decompose
   into a y-increasing chain followed by a y-decreasing chain) as one of the two
   structural residuals for the general convex case.  Until now every total
   family discharged it ad hoc: the diamond builds its split by hand and proves
   `bimonotone_split` by `reflexivity` over an explicit pair of edge lists.

   This file replaces the hand-construction by a reusable theorem.  Given a
   vertex list that is strictly y-unimodal — it rises strictly to a single apex
   vertex, then falls strictly back down — the edges split bimonotonically, with
   the increasing chain being the edges of the rising prefix and the decreasing
   chain the edges of the falling suffix.  The split obligation is thereby
   reduced to an *arithmetic* per-family check (compare consecutive heights),
   which `cbn`/`lra` discharge automatically for any concrete convex ring.

   The construction is purely combinatorial: convexity is NOT used.  (Convexity
   is what guarantees the vertex order is unimodal in the first place — that
   geometric implication, and the dual `interior_hits_one_chain`, remain the
   open residual for a fully general n-gon.)

   §1  y-unimodality predicates on vertex lists.
   §2  splitting `ring_edges` at a shared vertex.
   §3  monotone chains from strictly monotone vertex runs.
   §4  the headline: `bimonotone_split_unimodal`.
   §5  validation — re-deriving the diamond split in one line.
   §6  scaling demo — the split of a convex hexagon (n = 6).

   Pure-R + three-axiom.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List Lra.
From NTS.Proofs Require Import Distance Overlay MonotoneChainParity
                               ConvexChainSplit.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  y-unimodality predicates on vertex lists.                               *)
(* -------------------------------------------------------------------------- *)

(* A vertex list whose heights are strictly increasing along its order. *)
Fixpoint y_strict_incr (l : list Point) : Prop :=
  match l with
  | [] => True
  | a :: rest =>
      match rest with
      | [] => True
      | b :: _ => py a < py b /\ y_strict_incr rest
      end
  end.

(* A vertex list whose heights are strictly decreasing along its order. *)
Fixpoint y_strict_decr (l : list Point) : Prop :=
  match l with
  | [] => True
  | a :: rest =>
      match rest with
      | [] => True
      | b :: _ => py b < py a /\ y_strict_decr rest
      end
  end.

(* -------------------------------------------------------------------------- *)
(* §2  Splitting `ring_edges` at a shared vertex.                              *)
(* -------------------------------------------------------------------------- *)

(* One-step reduction of `ring_edges` on a two-or-more vertex list. *)
Lemma ring_edges_cons2 : forall a b l,
  ring_edges (a :: b :: l) = (a, b) :: ring_edges (b :: l).
Proof. reflexivity. Qed.

(* The first edge of a nonempty-ish skeleton starts at the head vertex. *)
Lemma ring_edges_head_fst : forall a l,
  match ring_edges (a :: l) with
  | [] => True
  | e :: _ => fst e = a
  end.
Proof. intros a [| b l]; simpl; auto. Qed.

(* Splitting the skeleton at an interior (shared) vertex `m`: the edges of
   `l1 ++ m :: l2` are the edges of the closed prefix `l1 ++ [m]` followed by
   the edges of the suffix `m :: l2`.  The vertex `m` is the join point. *)
Lemma ring_edges_app_shared : forall (l1 l2 : list Point) (m : Point),
  ring_edges (l1 ++ m :: l2) = ring_edges (l1 ++ [m]) ++ ring_edges (m :: l2).
Proof.
  induction l1 as [| a l1' IH]; intros l2 m.
  - (* l1 = [] : prefix is just [m], whose edges are empty. *)
    simpl. reflexivity.
  - destruct l1' as [| b l1''].
    + (* l1 = [a] : ring_edges (a :: m :: l2) = (a,m) :: ring_edges (m::l2). *)
      simpl. reflexivity.
    + (* l1 = a :: b :: l1'' : peel the head edge (a,b) and recurse. *)
      change ((a :: b :: l1'') ++ m :: l2) with (a :: b :: (l1'' ++ m :: l2)).
      change ((a :: b :: l1'') ++ [m]) with (a :: b :: (l1'' ++ [m])).
      rewrite !ring_edges_cons2.
      change (b :: l1'' ++ m :: l2) with ((b :: l1'') ++ m :: l2).
      change (b :: l1'' ++ [m]) with ((b :: l1'') ++ [m]).
      rewrite (IH l2 m).
      reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Monotone chains from strictly monotone vertex runs.                     *)
(* -------------------------------------------------------------------------- *)

(* Prepending one upward edge to an increasing chain, given it connects.  The
   connectivity premise is a `match` so the empty tail is discharged trivially
   without forcing the chain to reduce. *)
Lemma chain_increasing_cons : forall e es,
  edge_up e ->
  match es with [] => True | e2 :: _ => snd e = fst e2 end ->
  chain_increasing es ->
  chain_increasing (e :: es).
Proof.
  intros e es Hup Hconn Hrest.
  destruct es as [| e2 es'].
  - simpl. split; [ exact Hup | exact I ].
  - simpl. split; [ exact Hup | split; [ exact Hconn | exact Hrest ] ].
Qed.

Lemma chain_decreasing_cons : forall e es,
  edge_dn e ->
  match es with [] => True | e2 :: _ => snd e = fst e2 end ->
  chain_decreasing es ->
  chain_decreasing (e :: es).
Proof.
  intros e es Hup Hconn Hrest.
  destruct es as [| e2 es'].
  - simpl. split; [ exact Hup | exact I ].
  - simpl. split; [ exact Hup | split; [ exact Hconn | exact Hrest ] ].
Qed.

(* A strictly y-increasing vertex run yields a `chain_increasing` skeleton.
   Connectivity (`snd e = fst e2`) is automatic: consecutive `ring_edges`
   share the middle vertex by construction. *)
Lemma chain_increasing_of_y_strict_incr : forall l,
  y_strict_incr l -> chain_increasing (ring_edges l).
Proof.
  induction l as [| a l' IH]; intro H.
  - simpl. exact I.
  - destruct l' as [| b rest].
    + simpl. exact I.
    + (* l = a :: b :: rest *)
      destruct H as [Hab Hrest].
      rewrite ring_edges_cons2.
      apply chain_increasing_cons.
      * unfold edge_up. cbn [fst snd]. exact Hab.
      * pose proof (ring_edges_head_fst b rest) as Hhd.
        destruct (ring_edges (b :: rest)) as [| e2 tl] eqn:E.
        -- exact I.
        -- cbn [fst snd]. symmetry. exact Hhd.
      * exact (IH Hrest).
Qed.

(* Dual: a strictly y-decreasing vertex run yields a `chain_decreasing`
   skeleton. *)
Lemma chain_decreasing_of_y_strict_decr : forall l,
  y_strict_decr l -> chain_decreasing (ring_edges l).
Proof.
  induction l as [| a l' IH]; intro H.
  - simpl. exact I.
  - destruct l' as [| b rest].
    + simpl. exact I.
    + (* l = a :: b :: rest *)
      destruct H as [Hab Hrest].
      rewrite ring_edges_cons2.
      apply chain_decreasing_cons.
      * unfold edge_dn. cbn [fst snd]. exact Hab.
      * pose proof (ring_edges_head_fst b rest) as Hhd.
        destruct (ring_edges (b :: rest)) as [| e2 tl] eqn:E.
        -- exact I.
        -- cbn [fst snd]. symmetry. exact Hhd.
      * exact (IH Hrest).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The headline: bimonotone split from y-unimodality.                      *)
(* -------------------------------------------------------------------------- *)

(* For a vertex list that rises strictly to an apex then falls strictly, the
   skeleton splits bimonotonically.  `up` is the rising part below the apex,
   `down` the falling part above it; the ring is `up ++ apex :: down` and the
   two chains are the edges of the rising prefix and the falling suffix.

   This is the general replacement for the per-family hand-built split: a
   concrete convex ring discharges the two hypotheses by `cbn` + `lra` on the
   consecutive vertex heights, then reads off its chains. *)
Theorem bimonotone_split_unimodal :
  forall (up down : list Point) (apex : Point),
    y_strict_incr (up ++ [apex]) ->
    y_strict_decr (apex :: down) ->
    bimonotone_split (up ++ apex :: down)
                     (ring_edges (up ++ [apex]))
                     (ring_edges (apex :: down)).
Proof.
  intros up down apex Hup Hdn.
  unfold bimonotone_split. repeat split.
  - apply ring_edges_app_shared.
  - apply (chain_increasing_of_y_strict_incr _ Hup).
  - apply (chain_decreasing_of_y_strict_decr _ Hdn).
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Validation: the diamond split, now in one line.                         *)
(* -------------------------------------------------------------------------- *)

(* `diamond_ring` decomposes as up = [(0,-2);(2,0)], apex = (0,2),
   down = [(-2,0);(0,-2)] — and the general theorem reproduces exactly the
   hand-built `diamond_inc` / `diamond_dec`, with the unimodality discharged
   by `cbn` + `lra`. *)
Theorem diamond_bimonotone_via_unimodal :
  bimonotone_split diamond_ring diamond_inc diamond_dec.
Proof.
  apply (bimonotone_split_unimodal
           [mkPoint 0 (-2); mkPoint 2 0]
           [mkPoint (-2) 0; mkPoint 0 (-2)]
           (mkPoint 0 2)).
  - cbn [y_strict_incr app py]. repeat split; lra.
  - cbn [y_strict_decr py]. repeat split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Scaling demo: the split of a convex hexagon (n = 6).                    *)
(*   A genuinely convex CCW hexagon whose heights are strictly unimodal.       *)
(*   The split that the diamond proof built by hand now drops out for n = 6    *)
(*   with no extra machinery — only the arithmetic unimodality check changes.  *)
(* -------------------------------------------------------------------------- *)

Definition hexagon_ring : Ring :=
  [ mkPoint 0 (-3) ; mkPoint 3 (-1) ; mkPoint 4 2 ; mkPoint 1 3
  ; mkPoint (-2) 1 ; mkPoint (-3) (-2) ; mkPoint 0 (-3) ].

(* Right (increasing) chain: (0,-3)->(3,-1)->(4,2)->(1,3). *)
Definition hexagon_inc : list Edge :=
  ring_edges [ mkPoint 0 (-3) ; mkPoint 3 (-1) ; mkPoint 4 2 ; mkPoint 1 3 ].

(* Left (decreasing) chain: (1,3)->(-2,1)->(-3,-2)->(0,-3). *)
Definition hexagon_dec : list Edge :=
  ring_edges [ mkPoint 1 3 ; mkPoint (-2) 1 ; mkPoint (-3) (-2) ; mkPoint 0 (-3) ].

Theorem hexagon_bimonotone :
  bimonotone_split hexagon_ring hexagon_inc hexagon_dec.
Proof.
  apply (bimonotone_split_unimodal
           [mkPoint 0 (-3); mkPoint 3 (-1); mkPoint 4 2]
           [mkPoint (-2) 1; mkPoint (-3) (-2); mkPoint 0 (-3)]
           (mkPoint 1 3)).
  - cbn [y_strict_incr app py]. repeat split; lra.
  - cbn [y_strict_decr py]. repeat split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions bimonotone_split_unimodal.
Print Assumptions diamond_bimonotone_via_unimodal.
Print Assumptions hexagon_bimonotone.
