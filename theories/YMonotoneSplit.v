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

From Stdlib Require Import Reals List Lra Lia.
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
(* §6  Discrete IVT for y-monotone chains.                                    *)
(*   For a strictly-increasing (resp. decreasing) vertex sequence, when py q  *)
(*   lies strictly between the first and last vertex heights and no vertex    *)
(*   sits at height py q, some edge in ring_edges straddles the ray.          *)
(*   This is the y-structural half of `interior_hits_one_chain`: the x-       *)
(*   geometry (x-intercept comparison) is the sole remaining residual.        *)
(* -------------------------------------------------------------------------- *)

(* `last (l ++ [x]) d = x` — the snoc element is always returned. *)
Lemma last_snoc : forall A (l : list A) (x d : A),
  last (l ++ [x]) d = x.
Proof.
  induction l as [| a l' IH]; intros x d.
  - reflexivity.
  - destruct l' as [| p l''].
    + reflexivity.
    + cbn [app]. cbn [last]. apply IH.
Qed.

(* Increasing chain: if py q is strictly between the first and last vertex
   heights and no vertex sits at py q, then some edge straddles upward. *)
Lemma strict_inc_straddle_exists : forall vs q,
  (2 <= length vs)%nat ->
  strict_inc_y vs ->
  Forall (fun v => py v <> py q) vs ->
  py (hd (mkPoint 0 0) vs) < py q ->
  py q < py (last vs (mkPoint 0 0)) ->
  exists e, In e (ring_edges vs) /\
            py (fst e) < py q /\ py q < py (snd e).
Proof.
  induction vs as [| a vs' IH]; intros q Hlen Hsi Hnovert Hlo Hhi.
  - cbn in Hlen. lia.
  - destruct vs' as [| b vs''].
    + cbn in Hlen. lia.
    + rewrite ring_edges_cons2.
      cbn [strict_inc_y] in Hsi. destruct Hsi as [Hab Hrest].
      pose proof (Forall_inv_tail Hnovert) as Hnovert'.
      pose proof (Forall_inv Hnovert') as Hnb.
      cbn [hd] in Hlo.
      destruct (Rle_or_lt (py b) (py q)) as [Hbq | Hqb].
      * assert (Hbq' : py b < py q) by lra.
        destruct vs'' as [| c vs'''].
        -- cbn [last] in Hhi. lra.
        -- assert (Hlen2 : (2 <= length (b :: c :: vs'''))%nat) by (cbn; lia).
           assert (Hhi' : py q < py (last (b :: c :: vs''') (mkPoint 0 0))).
           { cbn [last] in Hhi. exact Hhi. }
           destruct (IH q Hlen2 Hrest Hnovert' Hbq' Hhi') as [e [Hin He]].
           exists e. split. right. exact Hin. exact He.
      * exists (a, b). split.
        -- left. reflexivity.
        -- cbn [fst snd]. exact (conj Hlo Hqb).
Qed.

(* Decreasing chain: symmetric — some edge straddles downward. *)
Lemma strict_dec_straddle_exists : forall vs q,
  (2 <= length vs)%nat ->
  strict_dec_y vs ->
  Forall (fun v => py v <> py q) vs ->
  py q < py (hd (mkPoint 0 0) vs) ->
  py (last vs (mkPoint 0 0)) < py q ->
  exists e, In e (ring_edges vs) /\
            py (snd e) < py q /\ py q < py (fst e).
Proof.
  induction vs as [| a vs' IH]; intros q Hlen Hsd Hnovert Hhi Hlo.
  - cbn in Hlen. lia.
  - destruct vs' as [| b vs''].
    + cbn in Hlen. lia.
    + rewrite ring_edges_cons2.
      cbn [strict_dec_y] in Hsd. destruct Hsd as [Hab Hrest].
      pose proof (Forall_inv_tail Hnovert) as Hnovert'.
      pose proof (Forall_inv Hnovert') as Hnb.
      cbn [hd] in Hhi.
      destruct (Rle_or_lt (py q) (py b)) as [Hqb | Hbq].
      * assert (Hqb' : py q < py b) by lra.
        destruct vs'' as [| c vs'''].
        -- cbn [last] in Hlo. lra.
        -- assert (Hlen2 : (2 <= length (b :: c :: vs'''))%nat) by (cbn; lia).
           assert (Hlo' : py (last (b :: c :: vs''') (mkPoint 0 0)) < py q).
           { cbn [last] in Hlo. exact Hlo. }
           destruct (IH q Hlen2 Hrest Hnovert' Hqb' Hlo') as [e [Hin He]].
           exists e. split. right. exact Hin. exact He.
      * exists (a, b). split.
        -- left. reflexivity.
        -- cbn [fst snd]. exact (conj Hbq Hhi).
Qed.

(* For a y-unimodal ring, when py q is strictly between the ring's bottom and
   peak heights (with no vertex at that height), both the increasing and the
   decreasing chain have a straddling edge.  The x-intercept comparison — which
   chain is actually CROSSED — is the remaining x-geometry residual. *)
Lemma y_unimodal_both_chains_straddle :
  forall r pre peak suf q,
  y_unimodal r pre peak suf ->
  pre <> [] ->
  suf <> [] ->
  Forall (fun v => py v <> py q) r ->
  py (hd (mkPoint 0 0) pre) < py q ->
  py q < py peak ->
  py (last (peak :: suf) (mkPoint 0 0)) < py q ->
  (exists e, In e (ring_edges (pre ++ [peak])) /\
             py (fst e) < py q /\ py q < py (snd e)) /\
  (exists e, In e (ring_edges (peak :: suf)) /\
             py (snd e) < py q /\ py q < py (fst e)).
Proof.
  intros r pre peak suf q (Hr & Hinc & Hdec) Hpre Hsuf Hforall Hlo Hqpk Hlodec.
  assert (Hnovert_inc : Forall (fun v => py v <> py q) (pre ++ [peak])).
  { apply Forall_forall. intros v Hv.
    rewrite Forall_forall in Hforall. apply Hforall. rewrite Hr.
    apply in_app_iff. apply in_app_iff in Hv as [Hv | Hv].
    - left. exact Hv.
    - right. cbn [In] in Hv. destruct Hv as [<- | []]. left. reflexivity. }
  assert (Hnovert_dec : Forall (fun v => py v <> py q) (peak :: suf)).
  { apply Forall_forall. intros v Hv.
    rewrite Forall_forall in Hforall. apply Hforall. rewrite Hr.
    apply in_app_iff. cbn [In] in Hv. destruct Hv as [<- | Hv].
    - right. left. reflexivity.
    - right. right. exact Hv. }
  assert (Hlen_inc : (2 <= length (pre ++ [peak]))%nat).
  { rewrite length_app. destruct pre as [| p pre']. contradiction Hpre. reflexivity.
    cbn. lia. }
  assert (Hlen_dec : (2 <= length (peak :: suf))%nat).
  { cbn. destruct suf as [| s suf']. contradiction Hsuf. reflexivity. cbn. lia. }
  assert (Hhd_inc : py (hd (mkPoint 0 0) (pre ++ [peak])) < py q).
  { destruct pre as [| p pre'].
    - contradiction Hpre. reflexivity.
    - cbn [hd app]. exact Hlo. }
  assert (Hlast_inc : py q < py (last (pre ++ [peak]) (mkPoint 0 0))).
  { rewrite last_snoc. exact Hqpk. }
  split.
  - exact (strict_inc_straddle_exists (pre ++ [peak]) q
             Hlen_inc Hinc Hnovert_inc Hhd_inc Hlast_inc).
  - exact (strict_dec_straddle_exists (peak :: suf) q
             Hlen_dec Hdec Hnovert_dec Hqpk Hlodec).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions ring_edges_split_at.
Print Assumptions y_unimodal_bimonotone_split.
Print Assumptions y_unimodal_point_in_ring.
Print Assumptions ym_diamond_bimonotone_split.
Print Assumptions strict_inc_straddle_exists.
Print Assumptions strict_dec_straddle_exists.
Print Assumptions y_unimodal_both_chains_straddle.
