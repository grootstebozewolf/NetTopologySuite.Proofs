(* ============================================================================
   NetTopologySuite.Proofs.JCT_HorizontalEdgeCounterexample
   ----------------------------------------------------------------------------
   Why the JCT parity seam NEEDS `no_horizontal_edge_at`: the horizontal-edge
   counterexample (the necessity companion to the vertex-graze finding).

   `JCT.v`'s seam `parity_characterises_interior_cont` is guarded by, among
   others, `no_horizontal_edge_at p r`.  The vertex-graze counterexample
   (theories/JCT_VertexGrazingCounterexample.v) showed that guard is NOT
   sufficient.  This file shows it is NECESSARY: drop it and ray-parity
   genuinely disagrees with the geometric interior.

   The witness is a valid simple "notch" hexagon (an L-shaped orthogonal
   polygon) with a horizontal edge at y = 1, and the EXTERIOR point
   `pext = (-1, 1)`:

                 (2,2)---------(4,2)
                   |              |
                   |   (notch)    |
       pext o------+----[====]----+        y = 1 : the ray runs ALONG the
       (-1,1)    (2,1)        |    |                horizontal edge (2,1)->(0,1)
                   .          |    |
                 (0,1)--------'    |
                   |  (bottom bar) |
                 (0,0)----------(4,0)

   `point_in_ring pext notch` is TRUE (the strict y-straddle counts only the
   far right edge at x = 4; the genuine left-hand crossing happens degenerately
   along the horizontal edge (2,1)->(0,1) and its endpoint vertices, so it is
   missed -- an undercount that flips the parity to odd).  But `pext` is plainly
   OUTSIDE: it escapes to infinity leftward without meeting the ring, so it is
   in the UNBOUNDED component and `~ geometric_interior_cont pext notch`.

   So `point_in_ring` and `geometric_interior_cont` DISAGREE at `pext` -- a raw
   refutation of "ray-parity characterises the interior" when no horizontal-edge
   guard is present.  And `no_horizontal_edge_at pext notch` is FALSE (the edge
   (2,1)->(0,1) is horizontal at the ray height), so the EXISTING seam already
   excludes this witness vacuously: the guard is doing real work.

   WHAT IS PROVED HERE (all Qed-closed, no `Admitted`/`Axiom`/`Parameter`):

     - `notch_ring_simple` / `_ring_closed` / `_min_points`: the notch is a
       valid simple polygon (so the failure is not an artefact of invalidity).
     - `notch_point_in_ring_pext`: ray-parity says "inside" (odd).
     - `notch_pext_not_interior`: `pext` is in the unbounded component, so it is
       NOT `geometric_interior_cont` (proved via escape-to-infinity, using
       JCT.v's `not_in_bounded_component_cont_intro`).
     - `notch_refutes_parity_without_guard` (RED): `point_in_ring pext notch /\
       ~ geometric_interior_cont pext notch` -- ray-parity != interior here.
     - `notch_violates_no_horizontal` + `notch_excluded_by_existing_seam`
       (GREEN): the existing guard `no_horizontal_edge_at` is FALSE at `pext`,
       so `parity_characterises_interior_cont pext notch` holds vacuously --
       the guard is necessary and already neutralises this witness.

   Together with the vertex-graze finding this pins the seam's correct guard
   SET: `no_horizontal_edge_at` (necessary -- this file) AND `ray_avoids_vertices`
   (additionally required -- the vertex-graze file).

   Pure-R; no atan / Flocq / `Classical_Prop.classic`.  No `Admitted`,
   no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import List.

From NTS.Proofs Require Import Distance.
From NTS.Proofs Require Import Overlay.
From NTS.Proofs Require Import PointInRingTangents.
From NTS.Proofs Require Import PointInRingCorrect.
From NTS.Proofs Require Import JordanCurveSeam.
From NTS.Proofs Require Import JCT.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The notch polygon and the exterior test point.                          *)
(* -------------------------------------------------------------------------- *)

(* An L-shaped (notch) hexagon: the rectangle [0,4]x[0,2] with the top-left
   block [0,2]x[1,2] removed.  Vertices CCW from the origin. *)
Definition notch : Ring :=
  mkPoint 0 0 :: mkPoint 4 0 :: mkPoint 4 2 :: mkPoint 2 2
    :: mkPoint 2 1 :: mkPoint 0 1 :: mkPoint 0 0 :: nil.

(* A point on the y = 1 ray level, well to the left of the polygon. *)
Definition pext : Point := mkPoint (-1) 1.

Lemma notch_ring_edges :
  ring_edges notch =
       (mkPoint 0 0, mkPoint 4 0)
    :: (mkPoint 4 0, mkPoint 4 2)
    :: (mkPoint 4 2, mkPoint 2 2)
    :: (mkPoint 2 2, mkPoint 2 1)
    :: (mkPoint 2 1, mkPoint 0 1)     (* horizontal edge at y = 1 *)
    :: (mkPoint 0 1, mkPoint 0 0)
    :: nil.
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The notch is a valid simple polygon.                                    *)
(* -------------------------------------------------------------------------- *)

Lemma notch_ring_closed : ring_closed notch.
Proof.
  exists (mkPoint 0 0),
    [ mkPoint 4 0; mkPoint 4 2; mkPoint 2 2; mkPoint 2 1; mkPoint 0 1 ].
  reflexivity.
Qed.

Lemma notch_min_points : ring_has_minimum_points notch.
Proof. unfold ring_has_minimum_points, notch. simpl. lia. Qed.

(* No two distinct edges cross properly (a simple orthogonal polygon). *)
Lemma notch_ring_simple : ring_simple notch.
Proof.
  intros e1 e2 H1 H2 Hne Hcross.
  rewrite notch_ring_edges in H1, H2.
  simpl in H1, H2.
  destruct Hcross as [t [s [[Ht0 Ht1] [[Hs0 Hs1] [Hx Hy]]]]].
  destruct H1 as [E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]];
  destruct H2 as [E2|[E2|[E2|[E2|[E2|[E2|[]]]]]]];
    subst e1 e2; simpl in Hx, Hy, Hne;
    try (exfalso; apply Hne; reflexivity);
    nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Ray-parity says "inside" at the exterior point pext.                    *)
(* -------------------------------------------------------------------------- *)

Ltac no_cross :=
  let H := fresh "H" in
  intro H; unfold edge_crosses_ray in H; simpl in H;
  destruct H as [ [[? ?] ?] | [[? ?] ?] ]; lra.

(* The crossing edge here is UPWARD ((4,0)->(4,2)), so the first disjunct fires;
   the downward case is kept for robustness. *)
Ltac yes_cross :=
  unfold edge_crosses_ray; simpl;
  ((left; repeat split; lra) || (right; repeat split; lra)).

Lemma ray_parity_even_not_odd :
  forall (p : Point) (es : list Edge),
    ray_parity_even p es -> ~ ray_parity_odd p es.
Proof.
  intros p es; induction es as [|e es' IH]; intros Heven Hodd.
  - inversion Hodd.
  - inversion Heven; subst; inversion Hodd; subst;
      try (eapply IH; eassumption);
      try contradiction.
Qed.

(* Only the right edge (4,0)->(4,2) strictly straddles y = 1; the horizontal
   edge (2,1)->(0,1) and the vertices at y = 1 are skipped, so the genuine
   left-hand crossing is missed.  Parity = 1 (ODD) => "inside". *)
Lemma notch_point_in_ring_pext : point_in_ring pext notch.
Proof.
  unfold point_in_ring, pext. rewrite notch_ring_edges.
  apply rpo_skip;  [ no_cross | ].   (* (0,0)->(4,0)  y=0, no straddle      *)
  apply rpo_cross; [ yes_cross | ].  (* (4,0)->(4,2)  crosses at x=4  HIT   *)
  apply rpe_skip;  [ no_cross | ].   (* (4,2)->(2,2)  y=2, no straddle      *)
  apply rpe_skip;  [ no_cross | ].   (* (2,2)->(2,1)  endpoint at y=1       *)
  apply rpe_skip;  [ no_cross | ].   (* (2,1)->(0,1)  HORIZONTAL at y=1     *)
  apply rpe_skip;  [ no_cross | ].   (* (0,1)->(0,0)  endpoint at y=1       *)
  apply rpe_nil.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  pext is in the UNBOUNDED component, hence not interior.                 *)
(* -------------------------------------------------------------------------- *)

(* Off-ring: every ring point has x in [0,4]; pext has x = -1. *)
Lemma notch_pext_off_ring : ring_complement notch pext.
Proof.
  unfold ring_complement, ring_image, pext.
  intros [e [u [Hin [[Hu0 Hu1] [Hx Hy]]]]].
  rewrite notch_ring_edges in Hin. simpl in Hin.
  destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]];
    subst e; simpl in Hx, Hy; nra.
Qed.

(* pext can escape arbitrarily far to the left without meeting the ring, so it
   is not in any bounded component. *)
Lemma notch_pext_unbounded : ~ in_bounded_component_cont notch pext.
Proof.
  apply not_in_bounded_component_cont_intro.
  intros M HM.
  exists (mkPoint (-(M + 1)) 1).
  split.
  - (* a straight leftward complement path from pext to the far point *)
    exists (fun t => mkPoint ((1 - t) * (-1) + t * (-(M + 1)))
                             ((1 - t) * 1 + t * 1)).
    split; [ apply straight_path_continuous | ].
    split; [ unfold pext; cbn; f_equal; lra | ].
    split; [ cbn; f_equal; lra | ].
    intros t [Ht0 Ht1] Himg.
    unfold ring_image in Himg.
    destruct Himg as [e [u [Hin [[Hu0 Hu1] [Hx Hy]]]]].
    rewrite notch_ring_edges in Hin. simpl in Hin.
    (* path x = -(1) - t*M <= -1 < 0, but every ring edge has x in [0,4] *)
    assert (HtM : 0 <= t * M) by (apply Rmult_le_pos; lra).
    destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]];
      subst e; simpl in Hx, Hy; nra.
  - (* the far point is outside radius M *)
    cbn. nra.
Qed.

Lemma notch_pext_not_interior : ~ geometric_interior_cont pext notch.
Proof.
  intros [_ Hb]. exact (notch_pext_unbounded Hb).
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  RED: ray-parity disagrees with the geometric interior at pext.          *)
(* -------------------------------------------------------------------------- *)

Theorem notch_refutes_parity_without_guard :
  point_in_ring pext notch /\ ~ geometric_interior_cont pext notch.
Proof.
  split; [ apply notch_point_in_ring_pext | apply notch_pext_not_interior ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  GREEN: the existing `no_horizontal_edge_at` guard excludes the witness. *)
(* -------------------------------------------------------------------------- *)

(* The notch has a horizontal edge (2,1)->(0,1) exactly at the ray height of
   pext (y = 1), so `no_horizontal_edge_at pext notch` is FALSE. *)
Lemma notch_violates_no_horizontal : ~ no_horizontal_edge_at pext notch.
Proof.
  unfold no_horizontal_edge_at, pext. rewrite notch_ring_edges.
  intro H. rewrite Forall_forall in H.
  assert (Hin : In (mkPoint 2 1, mkPoint 0 1)
                   (ring_edges notch)) by (rewrite notch_ring_edges; simpl; tauto).
  rewrite notch_ring_edges in Hin.
  specialize (H _ Hin). simpl in H. apply H. reflexivity.
Qed.

(* Therefore the EXISTING seam already neutralises this witness vacuously: its
   `no_horizontal_edge_at` premise is unsatisfiable at pext.  The guard is
   doing real work -- it is necessary, not redundant. *)
Theorem notch_excluded_by_existing_seam :
  parity_characterises_interior_cont pext notch.
Proof.
  intros _ _ _ Hnh. exfalso. apply notch_violates_no_horizontal. exact Hnh.
Qed.

(* RED and GREEN in one statement: ray-parity disagrees with the interior at
   pext, but the existing `no_horizontal_edge_at` guard already excludes it --
   so this is a NECESSITY proof for that guard, complementing the vertex-graze
   file's SUFFICIENCY gap. *)
Theorem horizontal_guard_is_necessary :
  (point_in_ring pext notch /\ ~ geometric_interior_cont pext notch)  (* RED   *)
  /\ parity_characterises_interior_cont pext notch.                   (* GREEN *)
Proof.
  split.
  - exact notch_refutes_parity_without_guard.
  - exact notch_excluded_by_existing_seam.
Qed.
