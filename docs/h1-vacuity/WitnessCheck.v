From Stdlib Require Import Lia.
(* Witness: a closed, simple ring with an interior point under point_in_ring.
   Combined with VacuityCheck, this shows H1 is contradictory (uninstantiable). *)
From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay PointInRingCorrect PointInRingTangents.
Import ListNotations.
Local Open Scope R_scope.

Definition sq : Ring :=
  [ mkPoint (-1) (-1); mkPoint 1 (-1); mkPoint 1 1; mkPoint (-1) 1; mkPoint (-1) (-1) ].

Definition ctr : Point := mkPoint 0 0.

Lemma sq_closed : ring_closed sq.
Proof.
  exists (mkPoint (-1) (-1)),
         [ mkPoint 1 (-1); mkPoint 1 1; mkPoint (-1) 1 ].
  reflexivity.
Qed.

Lemma sq_min : ring_has_minimum_points sq.
Proof. unfold ring_has_minimum_points, sq. simpl. lia. Qed.

Lemma sq_simple : ring_simple sq.
Proof.
  intros e1 e2 H1 H2 Hne.
  unfold sq in H1, H2. cbn in H1, H2.
  intros [t [s [[Ht1 Ht2] [[Hs1 Hs2] [Hx Hy]]]]].
  destruct H1 as [E1|[E1|[E1|[E1|[]]]]];
  destruct H2 as [E2|[E2|[E2|[E2|[]]]]];
  subst e1 e2; try (exfalso; apply Hne; reflexivity);
  cbn in Hx, Hy; nra.
Qed.

Lemma ctr_in_sq : point_in_ring ctr sq.
Proof.
  unfold point_in_ring, sq, ctr. cbn [ring_edges].
  (* edge0 (-1,-1)->(1,-1): no cross (ray below/above mismatch) *)
  apply rpo_skip.
  { unfold edge_crosses_ray. cbn [px py fst snd]. intros [[H _]|[H _]]; lra. }
  (* edge1 (1,-1)->(1,1): crosses *)
  apply rpo_cross.
  { unfold edge_crosses_ray. cbn [px py fst snd]. left. split; [lra|].
    replace (1 - 1) with 0 by lra. unfold Rdiv. rewrite !Rmult_0_l. lra. }
  (* edge2 (1,1)->(-1,1): no cross *)
  apply rpe_skip.
  { unfold edge_crosses_ray. cbn [px py fst snd]. intros [[H _]|[H _]]; lra. }
  (* edge3 (-1,1)->(-1,-1): no cross (px condition fails) *)
  apply rpe_skip.
  { unfold edge_crosses_ray. cbn [px py fst snd].
    intros [[H _]|[_ H]]; [lra|].
    replace (-1 - -1) with 0 in H by lra. unfold Rdiv in H.
    rewrite !Rmult_0_l in H. lra. }
  apply rpe_nil.
Qed.

(* The witness: a closed, simple ring with an interior point. *)
Theorem point_in_ring_inhabited_on_closed_simple :
  exists (q : Point) (r : Ring),
    ring_closed r /\ ring_simple r /\ point_in_ring q r.
Proof.
  exists ctr, sq. repeat split; [apply sq_closed | apply sq_simple | apply ctr_in_sq].
Qed.

Print Assumptions point_in_ring_inhabited_on_closed_simple.
