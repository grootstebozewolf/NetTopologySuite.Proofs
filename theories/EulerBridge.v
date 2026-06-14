(* ==========================================================================
   EulerBridge.v

   Phase C / Rung 3b-xi(+xii) of the H_bridge Euler route: WIRING.

   Assembles the Euler-route pieces into a single Qed chain from the named planar
   Euler identity to the bridge's reachability conclusion
   (`~ reachable (E_minus E d) (fst d) (snd d)`, the content of
   `EdgeFaceBridge.H_bridge_core`).  Two halves meet here:

     - ARITHMETIC (`euler_component_increase`): the Euler identity for `E` and
       `E_minus E d`, vertex invariance, the edge delta (`-1`, proved in
       EulerArrangement), and the same-face FACE delta (`F` unchanged) force the
       component count up by exactly one (`C' = C + 1`).  Pure `lia`.

     - SEMANTIC (`reachable_E_minus_of_bypass`): if the endpoints of `d` stay
       connected after deleting `d` (a "bypass"), every `E`-reachability reroutes
       through that bypass, so the two reachability relations coincide.

   `H_bridge_core_conclusion_from_euler` ties them: a bypass makes the relations
   coincide, hence (via `num_components_E_minus_le`, which discharges -- not
   assumes -- "the count is a function of the relation") keeps `C` from rising,
   contradicting `C' = C + 1`.  So no bypass: the endpoints are disconnected.

   RESIDUAL (the single remaining named hypothesis, still a real combinatorial
   obligation): the same-face FACE delta
       num_faces (E_minus E d) = num_faces E
   -- deleting a same-face edge leaves the `fstep`-orbit count unchanged (the
   orbit reroutes around the removed edge; fan substrate in ArrangementEMinus §2).
   `num_vertices` invariance is structural (degree-2+ endpoints), `num_edges`
   delta is proved, and `euler_characteristic` is the named planar-Euler premise.

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

Lemma euler_component_increase : forall (E : list Edge) (d : Edge),
  euler_characteristic E ->
  euler_characteristic (E_minus E d) ->
  num_vertices (E_minus E d) = num_vertices E ->
  num_edges (E_minus E d) + 1 = num_edges E ->
  num_faces (E_minus E d) = num_faces E ->         (* residual: same-face FACE delta *)
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
(* §3  Discharge "count is a function of the relation", then wire it all up.   *)
(* -------------------------------------------------------------------------- *)

(* If `E` and `E_minus E d` have the same reachability relation, the component
   count cannot rise: `comp_reps` depends only on the relation (`comp_reps_ext`),
   and is monotone in the vertex set (`comp_reps_length_mono`), and
   `verts (E_minus E d) ⊆ verts E`.  This PROVES the residual the wiring used to
   carry as a hypothesis. *)
Lemma num_components_E_minus_le : forall (E : list Edge) (d : Edge),
  (forall u v, reachable E u v <-> reachable (E_minus E d) u v) ->
  (num_components (E_minus E d) <= num_components E)%nat.
Proof.
  intros E d Hrel.
  assert (Hb : forall u v, reachable_b (E_minus E d) u v = reachable_b E u v).
  { intros u v.
    destruct (reachable_b (E_minus E d) u v) eqn:H1;
      destruct (reachable_b E u v) eqn:H2; try reflexivity; exfalso.
    - apply reachable_b_true_iff in H1. apply (proj2 (Hrel u v)) in H1.
      apply reachable_b_true_iff in H1. congruence.
    - apply reachable_b_true_iff in H2. apply (proj1 (Hrel u v)) in H2.
      apply reachable_b_true_iff in H2. congruence. }
  unfold num_components.
  rewrite (comp_reps_ext (E_minus E d) E
             (nodup point_eq_dec (verts (E_minus E d))) Hb).
  apply comp_reps_length_mono.
  intros x Hx. rewrite nodup_In in Hx. rewrite nodup_In.
  apply (verts_E_minus_incl E d). exact Hx.
Qed.

(* The H_bridge_core conclusion (= `~ reachable (E_minus E d) (dtip d) (dbase d)`
   modulo `dbase d = fst d`, `dtip d = snd d`, and reachability symmetry) from the
   named Euler identity, vertex invariance, the proved edge delta, and the single
   residual FACE delta. *)
Lemma H_bridge_core_conclusion_from_euler : forall (E : list Edge) (d : Edge),
  euler_characteristic E ->
  euler_characteristic (E_minus E d) ->
  num_vertices (E_minus E d) = num_vertices E ->
  num_edges (E_minus E d) + 1 = num_edges E ->
  num_faces (E_minus E d) = num_faces E ->         (* residual: same-face FACE delta *)
  ~ reachable (E_minus E d) (fst d) (snd d).
Proof.
  intros E d HE HE' HV HEd HF Hby.
  assert (Hcd : num_components (E_minus E d) = (num_components E + 1)%nat)
    by (apply euler_component_increase; assumption).
  assert (Hle : (num_components (E_minus E d) <= num_components E)%nat).
  { apply num_components_E_minus_le. intros u v. apply bypass_reachable_iff. exact Hby. }
  lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure Point + list combinatorics; allowlist axioms only.       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions euler_component_increase.
Print Assumptions reachable_E_minus_of_bypass.
Print Assumptions num_components_E_minus_le.
Print Assumptions H_bridge_core_conclusion_from_euler.
