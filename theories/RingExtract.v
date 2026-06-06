(* ============================================================================
   NetTopologySuite.Proofs.RingExtract
   ----------------------------------------------------------------------------
   extract_rings_valid, slices R1+R2 (see docs/extract-rings-proof-structure.md).
   The COMBINATORIAL CORE of ring assembly, grounded in the closed-chain
   structure of theories/BufferAssembly.v.

   Plan refinement.  The plan's R1 proposed a half-edge / dart layer with a
   cyclic `next` (via turn_sign) and a `face_of` orbit whose termination
   (`face_orbit_finite`) is the flagged crux (§9).  A *face walk is exactly a
   closed chain of edges* -- and `BufferAssembly` already produces such chains
   constructively, as concrete finite lists.  So we take the face walk as a
   `closed_chain` (finite by construction -- the orbit-termination obstacle
   does not arise) and extract its ring here.  This is the buffer beachhead
   of §6: the assembled buffer boundary feeds straight into ring extraction.
   (Ordering an *unordered* overlay edge set into chains -- the general
   assembly -- still needs the dart/`next` machinery; that is the remaining
   part of R1, not addressed here.)

   Deliverables:
     R1  `ring_of_chain` (face walk -> ring) and `ring_of_chain_length`.
     R2  `face_walk_closed`        : the ring is `ring_closed`;
         `face_walk_min_points`    : >=3 segments -> `ring_has_minimum_points`;
         `ring_edges_of_closed_chain` : the ring's edges are EXACTLY the chain
                                        (the faithful assembly<->ring bridge).

   `ring_simple` and `hole_inside_outer` are the analytic shell (§4) and are
   NOT addressed here.  Pure-R, three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.8)
   ========================================================================== *)

From Stdlib Require Import List Lia.
From NTS.Proofs Require Import Distance Overlay BufferAssembly.
Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1 (R1)  Face walk -> ring.                                                *)
(* -------------------------------------------------------------------------- *)

(* The ring of a face walk: the segment start-points, closed back to the
   first.  A closed chain's segments share endpoints, so these start-points
   trace the boundary and the appended first point closes it. *)
Definition ring_of_chain (segs : list (Point * Point)) : Ring :=
  match segs with
  | [] => []
  | s0 :: _ => map fst segs ++ [fst s0]
  end.

Lemma ring_of_chain_length : forall segs,
  segs <> [] -> length (ring_of_chain segs) = S (length segs).
Proof.
  intros [| s0 rest] H; [ contradiction | ].
  cbn [ring_of_chain]. rewrite length_app, length_map. cbn [length]. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2 (R2)  Closure and minimum-vertex count (combinatorial, by construction).*)
(* -------------------------------------------------------------------------- *)

Theorem face_walk_closed : forall segs,
  segs <> [] -> ring_closed (ring_of_chain segs).
Proof.
  intros [| s0 rest] H; [ contradiction | ].
  exists (fst s0), (map fst rest).
  cbn [ring_of_chain map app]. reflexivity.
Qed.

Theorem face_walk_min_points : forall segs,
  (3 <= length segs)%nat -> ring_has_minimum_points (ring_of_chain segs).
Proof.
  intros segs H.
  assert (Hne : segs <> []) by (destruct segs; [ cbn in H; lia | discriminate ]).
  unfold ring_has_minimum_points. rewrite ring_of_chain_length by exact Hne. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3 (R2)  The faithful bridge: the ring's edges are exactly the chain.      *)
(* -------------------------------------------------------------------------- *)

(* One-step unfolding of ring_edges on a two-or-more-element list (avoids
   cbn over-reducing the two-deep match into a stuck form). *)
Lemma ring_edges_cons2 : forall (a b : Point) (l : list Point),
  ring_edges (a :: b :: l) = (a, b) :: ring_edges (b :: l).
Proof. reflexivity. Qed.

(* Auxiliary over the open form `map fst segs ++ [q]`: if the chain is
   internally connected and its final endpoint is q, the consecutive-pair
   edges of the point list are exactly the original segments. *)
Lemma ring_edges_of_chain_aux : forall segs q,
  chain_ok segs ->
  (forall def, segs <> [] -> snd (last segs def) = q) ->
  ring_edges (map fst segs ++ [q]) = segs.
Proof.
  induction segs as [| s0 segs' IH]; intros q Hchain Hclose.
  - reflexivity.
  - destruct segs' as [| s1 rest].
    + (* single segment: edge (fst s0, q) with q = snd s0 *)
      cbn [map app ring_edges].
      specialize (Hclose s0 ltac:(discriminate)). cbn [last] in Hclose.
      rewrite <- Hclose. rewrite <- surjective_pairing. reflexivity.
    + cbn [chain_ok] in Hchain. destruct Hchain as [H01 Hch'].
      assert (Hclose' : forall def, (s1 :: rest) <> [] ->
                        snd (last (s1 :: rest) def) = q).
      { intros def _. specialize (Hclose def ltac:(discriminate)).
        rewrite (last_cons_ne s0 (s1 :: rest) def) in Hclose by discriminate.
        exact Hclose. }
      cbn [map app].
      rewrite ring_edges_cons2.
      change (fst s1 :: (map fst rest ++ [q]))
        with (map fst (s1 :: rest) ++ [q]).
      rewrite (IH q Hch' Hclose').
      f_equal.
      rewrite <- H01. rewrite <- surjective_pairing. reflexivity.
Qed.

Theorem ring_edges_of_closed_chain : forall segs,
  closed_chain segs -> ring_edges (ring_of_chain segs) = segs.
Proof.
  intros segs [Hchain Hclose].
  destruct segs as [| s0 rest].
  - reflexivity.
  - cbn [ring_of_chain].
    apply ring_edges_of_chain_aux.
    + exact Hchain.
    + intros def _. specialize (Hclose def ltac:(discriminate)).
      cbn [hd] in Hclose. exact Hclose.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Corollary: a long-enough closed chain yields a closed, min-vertex ring *)
(*     whose edges are exactly the chain -- the combinatorial core of         *)
(*     `valid_polygon`'s outer ring (closure + min-points + edge fidelity),   *)
(*     leaving `ring_simple` / `hole_inside_outer` as the analytic shell.     *)
(* -------------------------------------------------------------------------- *)

Theorem face_walk_core : forall segs,
  closed_chain segs ->
  (3 <= length segs)%nat ->
  ring_closed (ring_of_chain segs) /\
  ring_has_minimum_points (ring_of_chain segs) /\
  ring_edges (ring_of_chain segs) = segs.
Proof.
  intros segs Hcc Hlen.
  assert (Hne : segs <> []) by (destruct segs; [ cbn in Hlen; lia | discriminate ]).
  repeat split.
  - apply face_walk_closed; exact Hne.
  - apply face_walk_min_points; exact Hlen.
  - apply ring_edges_of_closed_chain; exact Hcc.
Qed.
