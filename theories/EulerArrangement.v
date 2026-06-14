(* ==========================================================================
   EulerArrangement.v

   Phase C / Rung 3b-viii of the H_bridge Euler route.

   The Euler quantities of a planar arrangement, and the Euler identity stated
   as a NAMED HYPOTHESIS -- the honest alternative to axiomatising it.  The
   corpus keeps its 3-axiom allowlist; the planar Euler relation
   `V + F = E + 1 + C` is carried as `euler_characteristic`, a `Prop` premise
   (under `noded_general_position`), to be discharged for the instances the
   bridge needs from the existing counting machinery (MapCounts `num_faces`,
   ReachableDec `num_components`, this file's `num_vertices` / `num_edges`,
   ArrangementEMinus).

   This file lands the definitions, the identity statement, and the first
   deletion "instance": the edge count drops by exactly one when a once-occurring
   edge is removed (`num_edges_E_minus`).  These are the count-bookkeeping facts
   the dichotomy (deleting a same-face edge splits a face / disconnects) consumes.

   Threading plan (the remaining rung, NOT done here):
     - face-count delta: deleting a same-face edge changes `num_faces` by the
       fstep-orbit merge/split count;
     - with `euler_characteristic` for `E` and `E_minus E d`, the edge delta
       (-1) here, and `num_vertices` invariance, that forces `num_components`
       to rise by one -- i.e. the endpoints of `d` land in different
       components, which is exactly `~ reachable (E_minus E d) ...`, closing
       `EdgeFaceBridge.H_bridge_core` from `euler_characteristic` as a named
       hypothesis (no axiom, no Admitted).

   Pure Point + list combinatorics; no `Admitted` / `Axiom` / `Parameter`;
   allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import List Arith Lia.
From NTS.Proofs Require Import Distance Overlay OverlayGraph Dart DartFace
                               EdgeConnectivity NodedGeneralPosition
                               MapCounts ReachableDec.

Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  The four Euler quantities.                                              *)
(* -------------------------------------------------------------------------- *)

(* V: distinct vertices (endpoints) of the arrangement. *)
Definition num_vertices (E : list Edge) : nat :=
  length (nodup point_eq_dec (verts E)).

(* E: undirected edges.  In the well-noded survivor setting each undirected
   carrier occurs once in `E` (its twin lives only in `darts_of E`), so the
   list length is the undirected edge count. *)
Definition num_edges (E : list Edge) : nat := length E.

(* F (`num_faces`, MapCounts) and C (`num_components`, ReachableDec) are reused. *)

(* -------------------------------------------------------------------------- *)
(* §2  The Euler identity, as a NAMED HYPOTHESIS (not an axiom).               *)
(*                                                                            *)
(* `V + F = E + 1 + C`, the subtraction-free form of `V - E + F = 1 + C`, the *)
(* genus-0 Euler relation for a plane graph.  Carried as a `Prop` premise,    *)
(* to be discharged for the instances the bridge needs -- never asserted.     *)
(* -------------------------------------------------------------------------- *)

Definition euler_characteristic (E : list Edge) : Prop :=
  num_vertices E + num_faces E = num_edges E + 1 + num_components E.

(* -------------------------------------------------------------------------- *)
(* §3  Deletion instance: the edge count under `E_minus`.                      *)
(* -------------------------------------------------------------------------- *)

(* Removing `e` drops the edge list length by exactly the multiplicity of `e`. *)
Lemma num_edges_E_minus_count : forall E e,
  num_edges E = num_edges (E_minus E e) + count_occ edge_eq_dec E e.
Proof.
  unfold num_edges, E_minus.
  induction E as [| a E IH]; intro e; [ reflexivity | ].
  cbn [filter count_occ].
  destruct (edge_eq_dec a e) as [Hae | Hae];
    cbn [length]; rewrite (IH e); lia.
Qed.

(* In the well-noded setting `e` occurs once, so the edge count drops by one. *)
Lemma num_edges_E_minus : forall E e,
  count_occ edge_eq_dec E e = 1%nat ->
  num_edges (E_minus E e) + 1 = num_edges E.
Proof.
  intros E e Hcount. pose proof (num_edges_E_minus_count E e) as H.
  rewrite Hcount in H. lia.
Qed.

(* A once-occurring present edge: the generic hypothesis for the delta above. *)
Lemma count_occ_1_of_NoDup : forall E e,
  NoDup E -> In e E -> count_occ edge_eq_dec E e = 1%nat.
Proof.
  intros E e Hnd Hin.
  pose proof (proj1 (NoDup_count_occ edge_eq_dec E) Hnd e) as Hle.
  pose proof (proj1 (count_occ_In edge_eq_dec E e) Hin) as Hgt.
  lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Deletion instance: the vertex set only shrinks.                         *)
(* -------------------------------------------------------------------------- *)

Lemma verts_E_minus_incl : forall E e, incl (verts (E_minus E e)) (verts E).
Proof.
  intros E e p Hp. unfold verts in *. rewrite in_flat_map in Hp |- *.
  destruct Hp as [e0 [He0 Hp0]].
  exists e0. split; [ apply in_E_minus in He0; exact (proj1 He0) | exact Hp0 ].
Qed.

Lemma num_vertices_E_minus_le : forall E e,
  (num_vertices (E_minus E e) <= num_vertices E)%nat.
Proof.
  intros E e. unfold num_vertices. apply NoDup_incl_length.
  - apply NoDup_nodup.
  - intros p Hp. rewrite nodup_In in Hp. rewrite nodup_In.
    apply (verts_E_minus_incl E e). exact Hp.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure Point + list combinatorics; allowlist axioms only.       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions num_edges_E_minus.
Print Assumptions num_vertices_E_minus_le.
