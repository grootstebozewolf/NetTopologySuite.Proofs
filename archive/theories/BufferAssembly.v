(* ============================================================================
   NetTopologySuite.Proofs.BufferAssembly
   ----------------------------------------------------------------------------
   Buffer/noder pipeline, Stage 2 seam: EDGE-LIST ASSEMBLY.
   (Seam map: docs/buffer-noder-pipeline.md §2.2 / §6 slice "edge-list assembly".)

   Turns the per-edge offset walls (theories/BufferOffset.v) and the
   per-vertex joins into the raw buffer-curve segment list that the
   pipeline nodes.  Uses the BEVEL join (theories/BufferBevel.v): between
   the offset wall of edge e1 and the wall of the next edge e2 (sharing the
   corner vertex), insert the straight segment connecting the end of wall
   e1 to the start of wall e2.  (Round / miter joins replace this single
   `obevel` segment with a multi-segment insertion; the chain structure
   below generalises since any join sub-chain runs from `snd (owall e1)` to
   `fst (owall e2)` -- noted for the follow-up.)

   The deliverable is the STRUCTURAL soundness of the assembly, the
   property ring extraction needs: the assembled boundary is a *closed
   chain* -- consecutive segments share an endpoint (`snd s_i = fst s_{i+1}`)
   and the last segment's end returns to the first segment's start.  This
   holds BY CONSTRUCTION (the joins are defined to bridge wall-end to
   next-wall-start), so the proofs are pure list induction.

   Also: each wall is parallel to its source edge (`wall_parallel`, citing
   `BufferOffset.offset_seg_parallel`).

   All pure-R, three-axiom (no atan / Flocq / classic).  No `Admitted` /
   `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.8)
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Real Vec Distance Direction BufferOffset.
Import ListNotations.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Walls, joins, and the open assembly.                                   *)
(* -------------------------------------------------------------------------- *)

(* The offset wall of an input edge e = (A, B), parallel to it at distance d. *)
Definition owall (e : Point * Point) (d : R) : Point * Point :=
  offset_seg (fst e) (snd e) d.

(* The bevel join between consecutive edges e1, e2 (sharing a corner):
   bridge the end of wall e1 to the start of wall e2. *)
Definition obevel (e1 e2 : Point * Point) (d : R) : Point * Point :=
  (snd (owall e1 d), fst (owall e2 d)).

(* Assemble an open chain of edges into walls interleaved with bevel joins:
   [owall e0; obevel e0 e1; owall e1; obevel e1 e2; ...; owall e_{n-1}]. *)
Fixpoint assemble_open (es : list (Point * Point)) (d : R) : list (Point * Point) :=
  match es with
  | [] => []
  | e :: rest =>
      match rest with
      | [] => owall e d :: nil
      | e2 :: _ => owall e d :: obevel e e2 d :: assemble_open rest d
      end
  end.

(* -------------------------------------------------------------------------- *)
(* §2  The chain predicate.                                                   *)
(* -------------------------------------------------------------------------- *)

(* Consecutive segments share an endpoint: snd s_i = fst s_{i+1}. *)
Fixpoint chain_ok (segs : list (Point * Point)) : Prop :=
  match segs with
  | [] => True
  | s1 :: rest =>
      match rest with
      | [] => True
      | s2 :: _ => snd s1 = fst s2 /\ chain_ok rest
      end
  end.

(* -------------------------------------------------------------------------- *)
(* §3  The open assembly is a chain (by construction).                        *)
(* -------------------------------------------------------------------------- *)

(* The assembly of a non-empty edge list starts with the first edge's wall. *)
Lemma assemble_open_head : forall e es d,
  exists r, assemble_open (e :: es) d = owall e d :: r.
Proof. intros e es d. destruct es as [|e2 es']; eexists; reflexivity. Qed.

Theorem assemble_open_chain : forall es d, chain_ok (assemble_open es d).
Proof.
  intros es d. induction es as [| e es' IH].
  - exact I.
  - destruct es' as [| e2 es''].
    + exact I.
    + change (assemble_open (e :: e2 :: es'') d)
        with (owall e d :: obevel e e2 d :: assemble_open (e2 :: es'') d).
      destruct (assemble_open_head e2 es'' d) as [r Hr].
      rewrite Hr. rewrite Hr in IH.
      cbn [chain_ok].
      split; [ reflexivity | split; [ reflexivity | exact IH ] ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Each wall is parallel to its source edge.                              *)
(* -------------------------------------------------------------------------- *)

Theorem wall_parallel : forall e d,
  parallel (seg_vec (fst (owall e d)) (snd (owall e d)))
           (seg_vec (fst e) (snd e)).
Proof.
  intros e d. unfold owall. apply offset_seg_parallel.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Closing the chain into a loop.                                         *)
(* -------------------------------------------------------------------------- *)

(* `last` does not depend on the default once the list is non-empty. *)
Lemma last_indep : forall (l : list (Point * Point)) a b,
  l <> [] -> last l a = last l b.
Proof.
  induction l as [| x l' IH]; intros a b Hne.
  - exfalso; apply Hne; reflexivity.
  - destruct l' as [| y l''].
    + reflexivity.
    + cbn [last]. apply IH. discriminate.
Qed.

(* Appending one segment whose start equals the chain's end preserves the
   chain property. *)
Lemma chain_ok_snoc : forall (c : Point * Point) segs,
  chain_ok segs ->
  (forall d0, segs <> [] -> snd (last segs d0) = fst c) ->
  chain_ok (segs ++ [c]).
Proof.
  intros c segs. induction segs as [| s1 segs' IH]; intros Hchain Hjunc.
  - exact I.
  - destruct segs' as [| s2 rest].
    + cbn [app chain_ok]. split; [ apply (Hjunc s1); discriminate | exact I ].
    + change ((s1 :: s2 :: rest) ++ [c]) with (s1 :: (s2 :: rest) ++ [c]).
      cbn [chain_ok] in Hchain. destruct Hchain as [H12 Hrest].
      change ((s2 :: rest) ++ [c]) with (s2 :: (rest ++ [c])).
      cbn [chain_ok]. split.
      * exact H12.
      * change (s2 :: rest ++ [c]) with ((s2 :: rest) ++ [c]).
        apply IH; [ exact Hrest | ].
        intros d0 _. specialize (Hjunc d0 ltac:(discriminate)).
        cbn [last] in Hjunc. exact Hjunc.
Qed.

(* Close any chain into a loop: append the segment from the chain's end back
   to its start. *)
Definition close_chain (segs : list (Point * Point)) : list (Point * Point) :=
  match segs with
  | [] => []
  | s0 :: _ => segs ++ [ (snd (last segs s0), fst s0) ]
  end.

(* The closed assembly: bevel-join open assembly, then close the loop. *)
Definition assemble_closed (es : list (Point * Point)) (d : R) : list (Point * Point) :=
  close_chain (assemble_open es d).

(* A closed chain: chained, and the last segment's end is the first's start. *)
Definition closed_chain (segs : list (Point * Point)) : Prop :=
  chain_ok segs /\
  (forall d0, segs <> [] -> snd (last segs d0) = fst (hd d0 segs)).

(* `last` of a cons with a non-empty tail drops the head. *)
Lemma last_cons_ne : forall (a : Point * Point) m d0,
  m <> [] -> last (a :: m) d0 = last m d0.
Proof. intros a m d0 Hne. destruct m as [| y m']; [ contradiction | reflexivity ]. Qed.

(* last of a snoc is the snoc'd element. *)
Lemma last_snoc : forall (l : list (Point * Point)) c d0,
  last (l ++ [c]) d0 = c.
Proof.
  induction l as [| x l' IH]; intros c d0.
  - reflexivity.
  - cbn [app].
    rewrite (last_cons_ne x (l' ++ [c]) d0) by (destruct l'; discriminate).
    apply IH.
Qed.

(* hd of a cons-snoc is the head. *)
Lemma hd_cons_snoc : forall (x : Point * Point) l c d0,
  hd d0 ((x :: l) ++ [c]) = x.
Proof. intros. reflexivity. Qed.

(* close_chain turns any chain into a closed chain. *)
Theorem close_chain_closed : forall segs,
  chain_ok segs -> closed_chain (close_chain segs).
Proof.
  intros segs Hchain. destruct segs as [| s0 segs'].
  - unfold close_chain, closed_chain.
    split; [ exact I | intros d0 Hne; exfalso; apply Hne; reflexivity ].
  - cbn [close_chain]. unfold closed_chain. split.
    + apply chain_ok_snoc; [ exact Hchain | ].
      intros d0 _. cbn [fst]. f_equal. apply last_indep. discriminate.
    + intros d0 _.
      rewrite last_snoc. rewrite hd_cons_snoc. cbn [fst snd]. reflexivity.
Qed.

(* The closed bevel assembly of any edge list is a closed chain. *)
Theorem assemble_closed_closed : forall es d,
  closed_chain (assemble_closed es d).
Proof.
  intros es d. unfold assemble_closed.
  apply close_chain_closed. apply assemble_open_chain.
Qed.
