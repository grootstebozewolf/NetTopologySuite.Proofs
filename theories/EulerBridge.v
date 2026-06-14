(* ==========================================================================
   EulerBridge.v

   Phase C / Rung 3b-xi of the H_bridge Euler route: WIRING.

   This file assembles the Euler-route pieces into a single Qed chain from the
   named planar Euler identity to the bridge's reachability conclusion
   (`~ reachable (E_minus E d) (fst d) (snd d)`, the content of
   `EdgeFaceBridge.H_bridge_core`).  Two halves meet here:

     - ARITHMETIC (`euler_bridge`): the Euler identity for `E` and `E_minus E d`,
       plus vertex invariance, the edge delta (`-1`, proved in EulerArrangement),
       and the same-face FACE delta (`F` unchanged), force the component count up
       by exactly one (`C' = C + 1`).  Pure `lia`.

     - SEMANTIC (`reachable_E_minus_of_bypass`): if the endpoints of `d` stay
       connected after deleting `d` (a "bypass"), then EVERY `E`-reachability is
       preserved in `E_minus E d` (reroute each use of `d` through the bypass) --
       so the two reachability relations coincide.

   `bridge_conclusion_of_euler` ties them: a bypass would make the relations
   coincide, hence (component count is a function of the relation) keep `C`
   unchanged -- contradicting `euler_bridge`'s `C' = C + 1`.  So no bypass: the
   endpoints are disconnected.

   The residual is now exactly TWO crisp, named combinatorial facts (carried as
   hypotheses, never asserted): the same-face FACE delta
   `num_faces (E_minus E d) = num_faces E`, and that `num_components` depends only
   on the reachability relation.  Everything else is proved.

   Pure Point + list combinatorics; no `Admitted` / `Axiom` / `Parameter`;
   allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import List Arith Lia ZArith.
From NTS.Proofs Require Import Distance Overlay OverlayGraph Dart DartFace
                               EdgeConnectivity MapCounts ReachableDec
                               EulerArrangement.

Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  Arithmetic half: the Euler identity forces the component count up by 1. *)
(* -------------------------------------------------------------------------- *)

Lemma euler_bridge : forall (E : list Edge) (d : Edge),
  euler_characteristic E ->
  euler_characteristic (E_minus E d) ->
  num_vertices (E_minus E d) = num_vertices E ->
  num_edges (E_minus E d) + 1 = num_edges E ->
  num_faces (E_minus E d) = num_faces E ->
  num_components (E_minus E d) = (num_components E + 1)%nat.
Proof.
  intros E d HE HE' HV HEd HF.
  unfold euler_characteristic in HE, HE'. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Semantic half: a bypass preserves all reachability.                     *)
(* -------------------------------------------------------------------------- *)

(* If the endpoints of `d` remain connected after deleting `d`, every `E`-walk
   reroutes its uses of `d` through that bypass, so reachability is preserved. *)
Lemma reachable_E_minus_of_bypass : forall (E : list Edge) (d : Edge),
  reachable (E_minus E d) (fst d) (snd d) ->
  forall u v, reachable E u v -> reachable (E_minus E d) u v.
Proof.
  intros E d Hby u v Hr. induction Hr as [u | u v w Hadj Hrec IH].
  - apply reach_refl.
  - apply reach_trans with v; [ | exact IH ].
    destruct Hadj as [e0 [He0 Hends]].
    destruct (edge_eq_dec e0 d) as [-> | Hne].
    + destruct Hends as [[Hfu Hsv] | [Hfv Hsu]].
      * rewrite <- Hfu, <- Hsv. exact Hby.
      * rewrite <- Hsu, <- Hfv. apply reach_sym. exact Hby.
    + apply reach_one. exists e0. split.
      * apply in_E_minus. split; [ exact He0 | exact Hne ].
      * exact Hends.
Qed.

(* Both directions: deleting `d` with a surviving bypass changes no reachability. *)
Lemma bypass_reachable_iff : forall (E : list Edge) (d : Edge) (u v : Point),
  reachable (E_minus E d) (fst d) (snd d) ->
  (reachable E u v <-> reachable (E_minus E d) u v).
Proof.
  intros E d u v Hby. split.
  - apply reachable_E_minus_of_bypass; exact Hby.
  - apply reach_incl, E_minus_incl.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Wiring: Euler + bypass-preservation => the endpoints are disconnected.  *)
(* -------------------------------------------------------------------------- *)

Lemma bridge_conclusion_of_euler : forall (E : list Edge) (d : Edge),
  euler_characteristic E ->
  euler_characteristic (E_minus E d) ->
  num_vertices (E_minus E d) = num_vertices E ->
  num_edges (E_minus E d) + 1 = num_edges E ->
  num_faces (E_minus E d) = num_faces E ->
  (* num_components is a function of the reachability relation: *)
  ((forall u v, reachable E u v <-> reachable (E_minus E d) u v) ->
   num_components (E_minus E d) = num_components E) ->
  ~ reachable (E_minus E d) (fst d) (snd d).
Proof.
  intros E d HE HE' HV HEd HF Hcount Hby.
  assert (Hcd : num_components (E_minus E d) = (num_components E + 1)%nat)
    by (apply euler_bridge; assumption).
  assert (Hrel : forall u v, reachable E u v <-> reachable (E_minus E d) u v)
    by (intros u v; apply bypass_reachable_iff; exact Hby).
  rewrite (Hcount Hrel) in Hcd. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure Point + list combinatorics; allowlist axioms only.       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions euler_bridge.
Print Assumptions reachable_E_minus_of_bypass.
Print Assumptions bridge_conclusion_of_euler.
