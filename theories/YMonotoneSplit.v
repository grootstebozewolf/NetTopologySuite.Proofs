(* ============================================================================
   NetTopologySuite.Proofs.YMonotoneSplit
   ----------------------------------------------------------------------------
   Y-monotone (unimodal) polygon split: the vertex-ordering infrastructure the
   corpus lacked, discharging the STRUCTURAL half of the convex-chain
   monotonicity residual (`ConvexChainSplit.interior_hits_one_chain` part (a)).

   A ring whose vertex y-coordinates rise strictly to a single peak and then fall
   strictly -- a `y_unimodal` ring -- has an edge list that splits exactly into a
   y-increasing chain followed by a y-decreasing chain, i.e. it admits a
   `MonotoneChainParity.bimonotone_split`.  Every convex polygon traversed from
   its minimum-y vertex is y-unimodal, so this is the honest, checkable structural
   form of "convexity yields the split"; it is reusable for any y-monotone-
   decomposable simple polygon, not just convex ones.

   Built from one foundational seam lemma -- `ring_edges_split_at`: the
   consecutive-pair edge list of `pre ++ peak :: suf` is the edges of the prefix
   (up to and including the peak) appended to the edges from the peak onward.

   §4 re-derives the hand-built diamond split of `ConvexChainSplit.v` from this
   general machinery, confirming the infrastructure reproduces it.

   Pure-R + list induction; three-axiom.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List Lra.
From NTS.Proofs Require Import Distance Overlay MonotoneChainParity.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The ring_edges seam lemma.                                              *)
(* -------------------------------------------------------------------------- *)

(* Splitting a vertex list at a chosen vertex `peak` splits its edge list at the
   corresponding seam: the prefix edges (ending at the edge INTO the peak) come
   first, then the edges FROM the peak onward.  The shared peak vertex is the
   meeting point of the two chains. *)
(* One-step unfolding of `ring_edges` on a two-or-more vertex list (definitional;
   rewriting with it peels exactly one edge without expanding the recursive call
   into a stuck `match` the way `cbn [ring_edges]` would). *)
Lemma ring_edges_cons2 : forall a b l,
  ring_edges (a :: b :: l) = (a, b) :: ring_edges (b :: l).
Proof. reflexivity. Qed.

Lemma ring_edges_split_at : forall pre peak suf,
  ring_edges (pre ++ peak :: suf)
  = ring_edges (pre ++ [peak]) ++ ring_edges (peak :: suf).
Proof.
  induction pre as [| a pre IH]; intros peak suf.
  - reflexivity.
  - destruct pre as [| a' pre'].
    + reflexivity.
    + cbn [app] in IH |- *.
      rewrite (ring_edges_cons2 a a' (pre' ++ peak :: suf)).
      rewrite (ring_edges_cons2 a a' (pre' ++ [peak])).
      rewrite IH. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Strictly y-monotone vertex sequences.                                   *)
(* -------------------------------------------------------------------------- *)

Fixpoint strict_inc_y (vs : list Point) : Prop :=
  match vs with
  | [] => True
  | a :: rest =>
      match rest with
      | [] => True
      | b :: _ => py a < py b /\ strict_inc_y rest
      end
  end.

Fixpoint strict_dec_y (vs : list Point) : Prop :=
  match vs with
  | [] => True
  | a :: rest =>
      match rest with
      | [] => True
      | b :: _ => py b < py a /\ strict_dec_y rest
      end
  end.

(* -------------------------------------------------------------------------- *)
(* §3  A strictly-monotone vertex run yields a monotone edge chain.            *)
(* -------------------------------------------------------------------------- *)

Lemma chain_increasing_ring_edges : forall vs,
  strict_inc_y vs -> chain_increasing (ring_edges vs).
Proof.
  induction vs as [| a vs IH]; intros H.
  - exact I.
  - destruct vs as [| b vs'].
    + exact I.
    + cbn [strict_inc_y] in H. destruct H as [Hab Hrest].
      cbn [ring_edges]. cbn [chain_increasing].
      split.
      * unfold edge_up. cbn [fst snd]. exact Hab.
      * destruct vs' as [| c vs''].
        -- exact I.
        -- cbn [ring_edges]. split.
           ++ cbn [fst snd]. reflexivity.
           ++ change ((b, c) :: ring_edges (c :: vs''))
                with (ring_edges (b :: c :: vs'')).
              apply IH. exact Hrest.
Qed.

Lemma chain_decreasing_ring_edges : forall vs,
  strict_dec_y vs -> chain_decreasing (ring_edges vs).
Proof.
  induction vs as [| a vs IH]; intros H.
  - exact I.
  - destruct vs as [| b vs'].
    + exact I.
    + cbn [strict_dec_y] in H. destruct H as [Hab Hrest].
      cbn [ring_edges]. cbn [chain_decreasing].
      split.
      * unfold edge_dn. cbn [fst snd]. exact Hab.
      * destruct vs' as [| c vs''].
        -- exact I.
        -- cbn [ring_edges]. split.
           ++ cbn [fst snd]. reflexivity.
           ++ change ((b, c) :: ring_edges (c :: vs''))
                with (ring_edges (b :: c :: vs'')).
              apply IH. exact Hrest.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  RUNG 1 — a y-unimodal ring admits a bimonotone split.                   *)
(* -------------------------------------------------------------------------- *)

(* `y_unimodal r pre peak suf`: the ring is `pre ++ peak :: suf`, the vertices up
   to and including the peak strictly rise in y, and from the peak onward they
   strictly fall.  This is precisely the traversal of a convex polygon from its
   minimum-y vertex (or any y-monotone-decomposable simple polygon). *)
Definition y_unimodal (r : Ring) (pre : list Point) (peak : Point) (suf : list Point) : Prop :=
  r = pre ++ peak :: suf /\
  strict_inc_y (pre ++ [peak]) /\
  strict_dec_y (peak :: suf).

Theorem y_unimodal_bimonotone_split : forall r pre peak suf,
  y_unimodal r pre peak suf ->
  bimonotone_split r (ring_edges (pre ++ [peak])) (ring_edges (peak :: suf)).
Proof.
  intros r pre peak suf (Hr & Hinc & Hdec).
  unfold bimonotone_split. repeat split.
  - rewrite Hr. apply ring_edges_split_at.
  - apply chain_increasing_ring_edges. exact Hinc.
  - apply chain_decreasing_ring_edges. exact Hdec.
Qed.

(* The XOR parity characterisation of point_in_ring for any y-unimodal ring,
   composing rung 1 of this campaign with rung 2 of the previous one. *)
Corollary y_unimodal_point_in_ring : forall r pre peak suf p,
  y_unimodal r pre peak suf ->
  ( point_in_ring p r <->
      ( (chain_crossed p (ring_edges (pre ++ [peak])) /\
         ~ chain_crossed p (ring_edges (peak :: suf))) \/
        (~ chain_crossed p (ring_edges (pre ++ [peak])) /\
         chain_crossed p (ring_edges (peak :: suf))) ) ).
Proof.
  intros r pre peak suf p Hy.
  apply bimonotone_split_parity.
  apply y_unimodal_bimonotone_split. exact Hy.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  The diamond, re-derived from the general machinery.                     *)
(*   The hand-built split of ConvexChainSplit.v is reproduced verbatim by      *)
(*   `y_unimodal_bimonotone_split`, with no per-edge bookkeeping.              *)
(* -------------------------------------------------------------------------- *)

Definition ym_diamond : Ring :=
  [ mkPoint 0 (-2) ; mkPoint 2 0 ; mkPoint 0 2 ; mkPoint (-2) 0 ; mkPoint 0 (-2) ].

Lemma ym_diamond_unimodal :
  y_unimodal ym_diamond
    [ mkPoint 0 (-2) ; mkPoint 2 0 ] (mkPoint 0 2) [ mkPoint (-2) 0 ; mkPoint 0 (-2) ].
Proof.
  unfold y_unimodal, ym_diamond. repeat split.
  - cbn [py]. lra.
  - cbn [py]. lra.
  - cbn [py]. lra.
  - cbn [py]. lra.
Qed.

(* The induced split equals the explicit increasing/decreasing diamond chains. *)
Theorem ym_diamond_bimonotone_split :
  bimonotone_split ym_diamond
    [ (mkPoint 0 (-2), mkPoint 2 0) ; (mkPoint 2 0, mkPoint 0 2) ]
    [ (mkPoint 0 2, mkPoint (-2) 0) ; (mkPoint (-2) 0, mkPoint 0 (-2)) ].
Proof.
  apply (y_unimodal_bimonotone_split ym_diamond _ _ _ ym_diamond_unimodal).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions ring_edges_split_at.
Print Assumptions y_unimodal_bimonotone_split.
Print Assumptions y_unimodal_point_in_ring.
Print Assumptions ym_diamond_bimonotone_split.
