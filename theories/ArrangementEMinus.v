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
From NTS.Proofs Require Import Distance Overlay Dart DartAngularOrder
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
(* Axiom audit.                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions in_outgoing_darts_of_E_minus.
Print Assumptions outgoing_E_minus_unchanged.
