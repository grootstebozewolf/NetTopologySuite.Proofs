(* ==========================================================================
   ArrangementEMinus.v

   Phase C / NL-1 of the H_bridge Euler route (Rung 3b-iv).

   Structural scaffolding for the arrangement after one edge is removed.  The
   key, reusable facts: removing an edge only removes darts (`incl`), and the
   general-position predicate `fan_ok` is downward-closed under inclusion -- so
   `arrangement_ok` survives edge removal.  Also a membership characterisation
   of `darts_of (E_minus E e)` when the opposite orientation is absent (the
   bridge setting `~ In (twin e) E`).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import List.
From NTS.Proofs Require Import Distance Overlay OverlayGraph Dart DartAngularOrder
                               DartNextSpec DartFace EdgeConnectivity.

Import ListNotations.

(* `fan_ok` is downward-closed: both conjuncts are universals over the fan. *)
Lemma fan_ok_incl : forall F' F : list Dart,
  incl F' F -> fan_ok F -> fan_ok F'.
Proof.
  intros F' F Hincl [Hprop Hpar]. split.
  - intros d Hd. apply Hprop, Hincl, Hd.
  - intros d e Hd He Hne.
    apply Hpar; [ apply Hincl, Hd | apply Hincl, He | exact Hne ].
Qed.

(* `In x (map twin L) <-> In (twin x) L`, via involutivity of twin. *)
Lemma in_map_twin : forall (x : Dart) (L : list Dart),
  In x (map twin L) <-> In (twin x) L.
Proof.
  intros x L. split.
  - intro H. apply in_map_iff in H. destruct H as [y [Hxy Hy]].
    rewrite <- Hxy. rewrite twin_involutive. exact Hy.
  - intro H. apply in_map_iff. exists (twin x).
    split; [ apply twin_involutive | exact H ].
Qed.

(* Removing an edge only removes darts. *)
Lemma incl_darts_of_E_minus : forall (E : list Edge) (e : Edge),
  incl (darts_of (E_minus E e)) (darts_of E).
Proof.
  intros E e x Hx. unfold darts_of in *.
  apply in_app_or in Hx. apply in_or_app.
  destruct Hx as [Hx | Hx].
  - left. apply in_E_minus in Hx. exact (proj1 Hx).
  - right. apply in_map_iff in Hx. destruct Hx as [y [Hxy Hy]].
    apply in_map_iff. exists y. split; [ exact Hxy | ].
    apply in_E_minus in Hy. exact (proj1 Hy).
Qed.

(* `outgoing` is monotone in the dart set. *)
Lemma incl_outgoing : forall (v : Point) (D' D : list Dart),
  incl D' D -> incl (outgoing v D') (outgoing v D).
Proof.
  intros v D' D Hincl x Hx.
  apply in_outgoing in Hx. apply in_outgoing.
  destruct Hx as [HxD' Hb]. split; [ apply Hincl; exact HxD' | exact Hb ].
Qed.

(* General position survives edge removal. *)
Lemma fan_ok_E_minus : forall (E : list Edge) (e : Edge),
  (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
  forall v : Point, fan_ok (outgoing v (darts_of (E_minus E e))).
Proof.
  intros E e Hfan v.
  apply (fan_ok_incl (outgoing v (darts_of (E_minus E e)))
                     (outgoing v (darts_of E))).
  - apply incl_outgoing, incl_darts_of_E_minus.
  - apply Hfan.
Qed.

(* The reduced arrangement is still an arrangement. *)
Lemma arrangement_ok_E_minus : forall (E : list Edge) (e : Edge),
  (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
  arrangement_ok (darts_of (E_minus E e)).
Proof.
  intros E e Hfan. split.
  - apply darts_of_closed_under_twin.
  - apply fan_ok_E_minus. exact Hfan.
Qed.

(* Exact dart removal in the bridge setting: when the opposite orientation is
   absent from `E`, removing `e` removes exactly the darts `e` and `twin e`. *)
Lemma in_darts_of_E_minus_iff : forall (E : list Edge) (e x : Dart),
  ~ In (twin e) E ->
  (In x (darts_of (E_minus E e)) <->
   (In x (darts_of E) /\ x <> e /\ x <> twin e)).
Proof.
  intros E e x Hne. unfold darts_of.
  rewrite in_app_iff, in_app_iff, in_map_twin, in_map_twin.
  repeat rewrite in_E_minus.
  split.
  - intros [[HxE Hxe] | [Htw Htwe]].
    + repeat split; [ left; exact HxE | exact Hxe | ].
      intro Hx. subst x. apply Hne. exact HxE.
    + repeat split.
      * right. exact Htw.
      * intro Hx. subst x. apply Hne. exact Htw.
      * intro Hx. subst x. apply Htwe. exact (twin_involutive e).
  - intros [[HxE | Htw] [Hxe Hxte]].
    + left. split; [ exact HxE | exact Hxe ].
    + right. split; [ exact Htw | ].
      intro Hx. apply Hxte.
      rewrite <- (twin_involutive x), Hx. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  How the per-vertex fans change under edge removal (bridge setting).      *)
(*                                                                            *)
(* The substrate the `next` / `fstep` reroute (and the `num_faces` delta of    *)
(* the Euler route) consumes: deleting `e` removes exactly `e` from the fan at  *)
(* `dbase e` and `twin e` from the fan at `dtip e`, and leaves every OTHER       *)
(* vertex fan untouched.                                                       *)
(* -------------------------------------------------------------------------- *)

(* Exact membership of a reduced fan. *)
Lemma in_outgoing_darts_of_E_minus : forall (E : list Edge) (e : Dart) (v : Point) (x : Dart),
  ~ In (twin e) E ->
  (In x (outgoing v (darts_of (E_minus E e))) <->
   (In x (outgoing v (darts_of E)) /\ x <> e /\ x <> twin e)).
Proof.
  intros E e v x Hne.
  rewrite !in_outgoing.
  rewrite (in_darts_of_E_minus_iff E e x Hne).
  tauto.
Qed.

(* Fans away from the two endpoints are unchanged: `e` is based at `dbase e`
   and `twin e` at `dtip e`, so neither sits in any other vertex's fan. *)
Lemma outgoing_E_minus_unchanged : forall (E : list Edge) (e : Dart) (v : Point),
  ~ In (twin e) E ->
  v <> dbase e -> v <> dtip e ->
  forall x, In x (outgoing v (darts_of (E_minus E e))) <->
            In x (outgoing v (darts_of E)).
Proof.
  intros E e v Hne Hvb Hvt x.
  rewrite (in_outgoing_darts_of_E_minus E e v x Hne). split.
  - intros [Hx _]. exact Hx.
  - intro Hx. split; [ exact Hx | ].
    apply in_outgoing in Hx. destruct Hx as [_ Hbx].
    split.
    + intro He. apply Hvb. rewrite <- Hbx, He. reflexivity.
    + intro He. apply Hvt. rewrite <- Hbx, He, dbase_twin. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* §3  Fans away from the endpoints are LIST-equal, so `fstep` agrees there.    *)
(*                                                                            *)
(* Membership equality (§2) is not enough for `next` (it folds over the fan    *)
(* list); but the fans are in fact equal AS LISTS away from `dbase e`/`dtip e`, *)
(* since `e` (based at `dbase e`) and `twin e` (based at `dtip e`) are never    *)
(* based at any other vertex, so the base-vertex filter drops them in both.    *)
(* This LOCALISES the face-orbit change to darts whose tip is an endpoint of    *)
(* `e` -- the precise input to the (still open) `num_faces` orbit-splice.       *)
(* -------------------------------------------------------------------------- *)

(* Filtering by `p` after `q` is redundant when `p` entails `q`. *)
Lemma filter_filter_redundant : forall (A : Type) (p q : A -> bool) (l : list A),
  (forall x, p x = true -> q x = true) ->
  filter p (filter q l) = filter p l.
Proof.
  intros A p q l Himp. induction l as [| a l IH]; [ reflexivity | ].
  cbn [filter]. destruct (q a) eqn:Hq.
  - cbn [filter]. destruct (p a) eqn:Hp.
    + f_equal. exact IH.
    + exact IH.
  - destruct (p a) eqn:Hp.
    + rewrite (Himp a Hp) in Hq. discriminate.
    + exact IH.
Qed.

Lemma filter_map_commute : forall (A B : Type) (f : A -> B) (p : B -> bool) (l : list A),
  filter p (map f l) = map f (filter (fun x => p (f x)) l).
Proof.
  intros A B f p l. induction l as [| a l IH]; [ reflexivity | ].
  cbn [map filter]. destruct (p (f a)) eqn:Hp.
  - cbn [map]. f_equal. exact IH.
  - exact IH.
Qed.

(* The outgoing fan at any vertex other than `e`'s endpoints is unchanged. *)
Lemma outgoing_darts_of_E_minus_eq : forall (E : list Edge) (e : Dart) (v : Point),
  v <> dbase e -> v <> dtip e ->
  outgoing v (darts_of (E_minus E e)) = outgoing v (darts_of E).
Proof.
  intros E e v Hvb Hvt. unfold outgoing, darts_of, E_minus.
  rewrite !filter_app. f_equal.
  - apply filter_filter_redundant. intros x Hx.
    destruct (edge_eq_dec x e) as [-> | Hne]; [ | reflexivity ].
    exfalso. apply Hvb.
    destruct (point_eq_dec (dbase e) v) as [He | He];
      [ symmetry; exact He | discriminate Hx ].
  - rewrite !filter_map_commute. f_equal.
    apply filter_filter_redundant. intros x Hx.
    destruct (edge_eq_dec x e) as [-> | Hne]; [ | reflexivity ].
    exfalso. apply Hvt.
    destruct (point_eq_dec (dbase (twin e)) v) as [He | He]; [ | discriminate Hx ].
    rewrite dbase_twin in He. symmetry. exact He.
Qed.

(* Hence `fstep` agrees with the full arrangement away from `e`'s endpoints. *)
Lemma fstep_E_minus_eq_away : forall (E : list Edge) (e x : Dart),
  dtip x <> dbase e -> dtip x <> dtip e ->
  fstep (darts_of (E_minus E e)) x = fstep (darts_of E) x.
Proof.
  intros E e x H1 H2. unfold fstep.
  rewrite (outgoing_darts_of_E_minus_eq E e (dtip x) H1 H2). reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions in_outgoing_darts_of_E_minus.
Print Assumptions outgoing_E_minus_unchanged.
Print Assumptions outgoing_darts_of_E_minus_eq.
Print Assumptions fstep_E_minus_eq_away.
