(* ============================================================================
   NetTopologySuite.Proofs.EdgeConnectivity
   ----------------------------------------------------------------------------
   extract_rings_valid R5, bridge follow-up: face_twin_free rung 2 -- the
   graph-connectivity layer for the no-cut-edge condition.

   FaceOrbitSep.v reduced the capstones' per-face hypothesis to one global
   orbit condition, `twins_in_different_faces D` (no dart shares an
   `fstep`-orbit with its twin), and pinned its meaning: a dart shares a face
   with its twin exactly when the edge is a CUT EDGE (bridge) -- the dumbbell.
   So the remaining work is purely graph-theoretic:

       edge_2_connected (no cut edge)  ==>  twins_in_different_faces.

   The corpus has NO vertex-connectivity / path / cut-edge machinery, so this
   rung introduces the minimal self-contained layer the headline needs:
   undirected vertex reachability over an edge list (an equivalence), the
   cut-edge predicate (removing the edge disconnects its endpoints), and the
   2-edge-connected condition.  Both directions of non-vacuity are
   machine-checked: a lone edge IS a cut edge; a triangle is 2-edge-connected.

   This is the graph VOCABULARY.  The orbit-linking theorem itself
   (`edge_2_connected E -> twins_in_different_faces (darts_of E)`) is the
   open named hypothesis H_bridge of `OverlayBridge.extract_rings_valid`
   (conditional Qed); target proof in `EdgeFaceBridge.v`.

   Pure Point + list combinatorics; no `Admitted` / `Axiom` / `Parameter`;
   allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import List Lia.
From NTS.Proofs Require Import Distance Overlay OverlayGraph.

Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  Decidable edge equality (componentwise from point_eq_dec).              *)
(* -------------------------------------------------------------------------- *)

Definition edge_eq_dec (e1 e2 : Edge) : {e1 = e2} + {e1 <> e2}.
Proof.
  destruct e1 as [a b], e2 as [c d].
  destruct (point_eq_dec a c) as [-> | Hac];
    [ destruct (point_eq_dec b d) as [-> | Hbd] | ].
  - left. reflexivity.
  - right. intro H. apply Hbd. inversion H. reflexivity.
  - right. intro H. apply Hac. inversion H. reflexivity.
Defined.

(* -------------------------------------------------------------------------- *)
(* §2  Undirected adjacency and vertex reachability.                           *)
(* -------------------------------------------------------------------------- *)

(* `u` and `v` are joined by an edge of `E`, in either orientation. *)
Definition adj (E : list Edge) (u v : Point) : Prop :=
  exists e, In e E /\ ((fst e = u /\ snd e = v) \/ (fst e = v /\ snd e = u)).

Lemma adj_sym : forall E u v, adj E u v -> adj E v u.
Proof.
  intros E u v [e [He H]]. exists e. split; [ exact He | tauto ].
Qed.

Lemma adj_edge : forall E e, In e E -> adj E (fst e) (snd e).
Proof.
  intros E e He. exists e. split; [ exact He | left; split; reflexivity ].
Qed.

(* Reflexive-transitive closure of adjacency: an undirected walk. *)
Inductive reachable (E : list Edge) : Point -> Point -> Prop :=
| reach_refl : forall u, reachable E u u
| reach_step : forall u v w, adj E u v -> reachable E v w -> reachable E u w.

Lemma reach_one : forall E u v, adj E u v -> reachable E u v.
Proof. intros E u v H. apply reach_step with v; [ exact H | apply reach_refl ]. Qed.

Lemma reach_trans : forall E u v w,
  reachable E u v -> reachable E v w -> reachable E u w.
Proof.
  intros E u v w Huv. induction Huv as [u | u v' w' Hadj Hrec IH]; intro Hvw.
  - exact Hvw.
  - apply reach_step with v'; [ exact Hadj | apply IH; exact Hvw ].
Qed.

Lemma reach_sym : forall E u v, reachable E u v -> reachable E v u.
Proof.
  intros E u v Huv. induction Huv as [u | u v' w Hadj Hrec IH].
  - apply reach_refl.
  - apply reach_trans with v'; [ exact IH | apply reach_one, adj_sym; exact Hadj ].
Qed.

(* Monotone in the edge set. *)
Lemma adj_incl : forall E E' u v, incl E E' -> adj E u v -> adj E' u v.
Proof.
  intros E E' u v Hincl [e [He H]]. exists e. split; [ apply Hincl; exact He | exact H ].
Qed.

Lemma reach_incl : forall E E' u v, incl E E' -> reachable E u v -> reachable E' u v.
Proof.
  intros E E' u v Hincl Huv. induction Huv as [u | u v' w Hadj Hrec IH].
  - apply reach_refl.
  - apply reach_step with v'; [ apply (adj_incl E E'); assumption | exact IH ].
Qed.

(* On the empty edge set, only reflexive reachability holds. *)
Lemma reachable_nil : forall u v, reachable [] u v -> u = v.
Proof.
  intros u v H. remember (@nil Edge) as E0 eqn:HE.
  induction H as [u | u v' w Hadj Hrec IH].
  - reflexivity.
  - subst E0. destruct Hadj as [e [He _]]. destruct He.
Qed.

(* One-step inversion: a nontrivial reachability factorises through an adj step. *)
Lemma reachable_inv :
  forall E u w, reachable E u w ->
    u = w \/ exists v, adj E u v /\ reachable E v w.
Proof.
  intros E u w H. inversion H; subst; eauto.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Edge removal, cut edges, and 2-edge-connectivity.                       *)
(* -------------------------------------------------------------------------- *)

Definition E_minus (E : list Edge) (e : Edge) : list Edge :=
  filter (fun e' => if edge_eq_dec e' e then false else true) E.

Lemma in_E_minus : forall E e x,
  In x (E_minus E e) <-> (In x E /\ x <> e).
Proof.
  intros E e x. unfold E_minus. rewrite filter_In. split.
  - intros [Hin Hb]. split; [ exact Hin | ].
    destruct (edge_eq_dec x e) as [-> | Hne]; [ discriminate Hb | exact Hne ].
  - intros [Hin Hne]. split; [ exact Hin | ].
    destruct (edge_eq_dec x e) as [-> | _]; [ contradiction | reflexivity ].
Qed.

Lemma E_minus_incl : forall E e, incl (E_minus E e) E.
Proof. intros E e x Hx. apply in_E_minus in Hx. exact (proj1 Hx). Qed.

(* Reachability survives enlarging the edge set. *)
Lemma reachable_E_minus_to_E :
  forall E e u v, reachable (E_minus E e) u v -> reachable E u v.
Proof.
  intros E e u v H.
  apply (reach_incl (E_minus E e) E); [ apply E_minus_incl | exact H ].
Qed.

(* `e` is a cut edge (bridge): proper, present, its endpoints are reachable,
   but removing it disconnects them. *)
Definition is_cut_edge (E : list Edge) (e : Edge) : Prop :=
  In e E /\ fst e <> snd e /\
  reachable E (fst e) (snd e) /\
  ~ reachable (E_minus E e) (fst e) (snd e).

(* No edge of `E` is a cut edge. *)
Definition edge_2_connected (E : list Edge) : Prop :=
  forall e, In e E -> ~ is_cut_edge E e.

(* -------------------------------------------------------------------------- *)
(* §4  Non-vacuity, both ways.                                                 *)
(* -------------------------------------------------------------------------- *)

(* A lone proper edge IS a cut edge -- removing it strands its endpoints. *)
Lemma single_edge_is_cut :
  forall a b : Point, a <> b -> is_cut_edge [(a, b)] (a, b).
Proof.
  intros a b Hab. unfold is_cut_edge. cbn [fst snd]. repeat split.
  - left. reflexivity.
  - exact Hab.
  - apply reach_one. exists (a, b). split.
    + left. reflexivity.
    + cbn [fst snd]; first [ left; split; reflexivity | right; split; reflexivity ].
  - intro Hr.
    assert (Hnil : E_minus [(a, b)] (a, b) = []).
    { unfold E_minus. cbn [filter].
      destruct (edge_eq_dec (a, b) (a, b)) as [_ | Hne]; [ reflexivity | contradiction ]. }
    rewrite Hnil in Hr. apply reachable_nil in Hr. contradiction.
Qed.

Corollary single_edge_not_2_connected :
  forall a b : Point, a <> b -> ~ edge_2_connected [(a, b)].
Proof.
  intros a b Hab H2. apply (H2 (a, b)).
  - left. reflexivity.
  - apply single_edge_is_cut. exact Hab.
Qed.

(* A triangle is 2-edge-connected: removing any edge leaves a 2-path joining
   its endpoints, so no edge is a cut edge. *)
Section Triangle.
  Variables A B C : Point.
  Hypotheses (HAB : A <> B) (HBC : B <> C) (HCA : C <> A)
             (He1 : (A,B) <> (B,C)) (He2 : (A,B) <> (C,A)) (He3 : (B,C) <> (C,A)).
  Let T : list Edge := [(A,B); (B,C); (C,A)].

  (* The three edges, surviving removal of a DIFFERENT edge. *)
  Lemma tri_not_cut_AB : ~ is_cut_edge T (A,B).
  Proof.
    intros (_ & _ & _ & Hdis). cbn [fst snd] in Hdis. apply Hdis.
    (* path A -> C -> B through (C,A) and (B,C), both still present *)
    apply reach_trans with C.
    - apply reach_one. exists (C,A). split.
      + apply in_E_minus. split; [ right; right; left; reflexivity | congruence ].
      + cbn [fst snd]; first [ left; split; reflexivity | right; split; reflexivity ].
    - apply reach_one. exists (B,C). split.
      + apply in_E_minus. split; [ right; left; reflexivity | congruence ].
      + cbn [fst snd]; first [ left; split; reflexivity | right; split; reflexivity ].
  Qed.

  Lemma tri_not_cut_BC : ~ is_cut_edge T (B,C).
  Proof.
    intros (_ & _ & _ & Hdis). cbn [fst snd] in Hdis. apply Hdis.
    (* path B -> A -> C through (A,B) and (C,A) *)
    apply reach_trans with A.
    - apply reach_one. exists (A,B). split.
      + apply in_E_minus. split; [ left; reflexivity | congruence ].
      + cbn [fst snd]; first [ left; split; reflexivity | right; split; reflexivity ].
    - apply reach_one. exists (C,A). split.
      + apply in_E_minus. split; [ right; right; left; reflexivity | congruence ].
      + cbn [fst snd]; first [ left; split; reflexivity | right; split; reflexivity ].
  Qed.

  Lemma tri_not_cut_CA : ~ is_cut_edge T (C,A).
  Proof.
    intros (_ & _ & _ & Hdis). cbn [fst snd] in Hdis. apply Hdis.
    (* path C -> B -> A through (B,C) and (A,B) *)
    apply reach_trans with B.
    - apply reach_one. exists (B,C). split.
      + apply in_E_minus. split; [ right; left; reflexivity | congruence ].
      + cbn [fst snd]; first [ left; split; reflexivity | right; split; reflexivity ].
    - apply reach_one. exists (A,B). split.
      + apply in_E_minus. split; [ left; reflexivity | congruence ].
      + cbn [fst snd]; first [ left; split; reflexivity | right; split; reflexivity ].
  Qed.

  Theorem triangle_2_connected : edge_2_connected T.
  Proof.
    intros e He. unfold T in He. cbn [In] in He.
    destruct He as [<- | [<- | [<- | []]]].
    - exact tri_not_cut_AB.
    - exact tri_not_cut_BC.
    - exact tri_not_cut_CA.
  Qed.
End Triangle.

(* -------------------------------------------------------------------------- *)
(* §5  The rotation-system bridge characterisation (BOTH directions landed).   *)
(*                                                                            *)
(* The classical characterisation -- an edge is a bridge iff its two darts      *)
(* bound the same face -- relates this graph layer to the `fstep` face orbits   *)
(* of DartFace/FaceOrbitSep.  BOTH directions now live in EdgeFaceBridge.v:     *)
(*                                                                            *)
(*   FORWARD  edge_2_connected E -> twins_in_different_faces (darts_of E)        *)
(*     (`edge_2_connected_twins_sep`): the genus-0 same_face=>bridge side,       *)
(*     proved modulo the planar premise `H_bridge_premise` (discharged from the  *)
(*     Euler identity in HBridgeEuler.v).                                        *)
(*   CONVERSE  twins_in_different_faces (darts_of E) -> edge_2_connected E       *)
(*     (`twins_in_different_faces_edge_2_connected`): the easy                    *)
(*     different_faces=>not-a-bridge side -- NEEDS NO Euler/planarity; the rest  *)
(*     of a dart's face walk is the bypass.                                      *)
(*                                                                            *)
(* `edge_2_connected` itself is NOT derivable from geometry: a planar dumbbell   *)
(* satisfies well_noded + no_spurs yet has a cut edge.  It stays a carried       *)
(* precondition of OverlayBridge.extract_rings_valid; the `*_sep` variants there *)
(* carry the equivalent `twins_in_different_faces` directly (no Euler).         *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure Point + list combinatorics; allowlist axioms only.       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions reach_sym.
Print Assumptions reach_trans.
Print Assumptions reachable_nil.
Print Assumptions single_edge_is_cut.
Print Assumptions triangle_2_connected.
