(* ============================================================================
   NetTopologySuite.Proofs.RingSimple
   ----------------------------------------------------------------------------
   extract_rings_valid: the `ring_simple` condition of `valid_polygon`.

   `ring_simple r` (theories/Overlay.v) says distinct edges of the ring do
   not PROPERLY cross (no interior-interior intersection).  Two facts settle
   where this comes from in the buffer/overlay pipeline:

   (1) `ring_simple` is DELIVERED BY THE NODER, not by the raw offset.
       A ring whose edges are drawn from a pairwise-non-properly-crossing
       (i.e. NODED) arrangement is automatically simple
       (`ring_simple_of_subset`).  This is exactly the post-noding guarantee:
       the snap-rounding noder makes the arrangement `fully_intersected`
       (every distinct pair meets only at endpoints, hence does not properly
       cross), so any ring extracted from it is `ring_simple`.

   (2) The RAW assembled offset is NOT simple in general
       (`not_ring_simple_bowtie`): a concrete self-crossing ring witnesses
       `~ ring_simple`.  This is the configuration the hole-count heuristic
       detects as a sealing mouth (a hole forming) -- and the precise reason
       the pipeline must NODE the offset curve before extracting rings.
       Verified counterexample, no Admitted.

   So the path to a buffer ring's `ring_simple` is: assemble (BufferAssembly,
   not simple) -> NODE (fully_intersected) -> extract; (1) then yields
   `ring_simple` for the extracted ring.

   Pure-R; no atan / Flocq.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.8)
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Pairwise non-crossing, and its relation to ring_simple.                *)
(* -------------------------------------------------------------------------- *)

(* A set of edges in which no two distinct members properly cross. *)
Definition pairwise_no_proper_cross (S : list Edge) : Prop :=
  forall e1 e2 : Edge,
    In e1 S -> In e2 S -> e1 <> e2 ->
    ~ segments_intersect_properly (fst e1) (snd e1) (fst e2) (snd e2).

(* `ring_simple` is exactly "the ring's edges are pairwise non-crossing". *)
Lemma ring_simple_iff_pairwise : forall r : Ring,
  ring_simple r <-> pairwise_no_proper_cross (ring_edges r).
Proof. intros r. split; intro H; exact H. Qed.

(* -------------------------------------------------------------------------- *)
(* §2 (positive)  Noding delivers ring_simple.                                *)
(* -------------------------------------------------------------------------- *)

(* If a ring's edges are all drawn from a pairwise-non-crossing arrangement,
   the ring is simple.  Instantiated with the snap-rounding noder's output
   (which is `fully_intersected`, hence pairwise non-properly-crossing), this
   is the post-noding `ring_simple` guarantee. *)
Theorem ring_simple_of_subset : forall (S : list Edge) (r : Ring),
  pairwise_no_proper_cross S ->
  (forall e, In e (ring_edges r) -> In e S) ->
  ring_simple r.
Proof.
  intros S r Hpw Hsub e1 e2 H1 H2 Hne.
  apply Hpw; [ apply Hsub; exact H1 | apply Hsub; exact H2 | exact Hne ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3 (counterexample)  The raw offset / assembled ring need not be simple.   *)
(* -------------------------------------------------------------------------- *)

(* A self-crossing closed quadrilateral: the diagonal (0,0)->(2,2) and the
   anti-diagonal (2,0)->(0,2) cross properly at (1,1).  This is the shape of
   a raw offset boundary whose two walls cross (a sealing mouth). *)
Definition bowtie : Ring :=
  mkPoint 0 0 :: mkPoint 2 2 :: mkPoint 2 0 :: mkPoint 0 2 :: mkPoint 0 0 :: nil.

(* The two crossing edges genuinely intersect at an interior point. *)
Lemma bowtie_cross :
  segments_intersect_properly (mkPoint 0 0) (mkPoint 2 2)
                              (mkPoint 2 0) (mkPoint 0 2).
Proof.
  exists (1/2), (1/2).
  repeat split; simpl; lra.
Qed.

Theorem not_ring_simple_bowtie : ~ ring_simple bowtie.
Proof.
  intro Hrs.
  assert (H1 : In (mkPoint 0 0, mkPoint 2 2) (ring_edges bowtie))
    by (unfold bowtie; simpl; left; reflexivity).
  assert (H2 : In (mkPoint 2 0, mkPoint 0 2) (ring_edges bowtie))
    by (unfold bowtie; simpl; right; right; left; reflexivity).
  assert (Hne : (mkPoint 0 0, mkPoint 2 2) <> (mkPoint 2 0, mkPoint 0 2)).
  { intro Heq. apply (f_equal (fun p => px (fst p))) in Heq. simpl in Heq. lra. }
  pose proof (Hrs _ _ H1 H2 Hne) as Hno.
  apply Hno. exact bowtie_cross.
Qed.
