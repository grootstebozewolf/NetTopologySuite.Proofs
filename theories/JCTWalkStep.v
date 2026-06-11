(* ============================================================================
   NetTopologySuite.Proofs.JCTWalkStep
   ----------------------------------------------------------------------------
   ESCAPE DESCENT, rung 4: the assembled WALK STEP.  From a guarded
   complement point with a positive crossing count, slide east to just west
   of the first wall and ride the wall's own corridor down to a parked,
   guarded height -- one connected complement path, Qed, conditional only on
   the corridor clearances (which rung 5 derives from `ring_simple`
   touch-freedom edge by edge).

   The join is exact: for a crossing edge the crossing abscissa IS the
   carrier line's abscissa at p's height (`cross_x_is_edge_x_at`), so the
   east-approach endpoint (X1 - delta, py p) and the corridor's top point
   coincide definitionally (`corridor_top_is_wall_point`).  Crossing edges
   are non-horizontal under the guard (`crossing_edge_nonhorizontal`), so
   the corridor machinery applies.  `exists_parked_height` parks the
   corridor's lower end strictly above any target level inside a
   vertex-level-free gap, giving the ray guard at the destination for free.

   `walk_step` composes: east run-up (rung 1) + corridor (rung 2), glued by
   transitivity of complement connectivity; the destination is off-ring and
   guarded.  Rung 5 supplies the clearance hypotheses from simplicity,
   chooses corners, and recurses.

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Arith Lia.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam.
From NTS.Proofs Require Import PointInRingCorrect JCT JCT_OnEdgeCounterexample.
From NTS.Proofs Require Import ConvexOffringSeam JCTParityTransport.
From NTS.Proofs Require Import JCTHalfOpenParity JCTGenericStability JCTLevelJump.
From NTS.Proofs Require Import JCTTrappedHalf JCTSeamAssembly JCTEscapeDescent.
From NTS.Proofs Require Import JCTEastApproach JCTCorridor JCTWalkKit.
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §1  The wall point and the corridor top coincide.
   --------------------------------------------------------------------------- *)

Lemma crossing_edge_nonhorizontal : forall (r : Ring) (p : Point) (e : Edge),
  ray_avoids_vertices p r ->
  In e (ring_edges r) ->
  edge_crosses_ray_ho p e ->
  py (fst e) <> py (snd e).
Proof.
  intros r p [a b] Hrav Hin Hc.
  destruct (ho_cross_strict_of_guard r p a b Hrav Hin Hc) as [H | H];
    cbn [fst snd]; lra.
Qed.

Lemma cross_x_is_edge_x_at : forall (p : Point) (e : Edge),
  py (fst e) <> py (snd e) ->
  cross_x p e = edge_x_at e (py p).
Proof.
  intros p [a b] Hnh; cbn [fst snd] in Hnh.
  unfold cross_x, edge_x_at.
  destruct (Rle_dec (py a) (py b)) as [Hle | Hle].
  - reflexivity.
  - field; lra.
Qed.

Lemma corridor_top_is_wall_point : forall (p : Point) (e : Edge) (delta : R),
  py (fst e) <> py (snd e) ->
  corridor e delta (py p) = mkPoint (cross_x p e - delta) (py p).
Proof.
  intros p e delta Hnh.
  unfold corridor. rewrite (cross_x_is_edge_x_at p e Hnh). reflexivity.
Qed.

(* ---------------------------------------------------------------------------
   §2  Parked heights: strictly above a level, inside a vertex-free gap,
       and below the start.
   --------------------------------------------------------------------------- *)

Lemma exists_parked_height : forall (r : Ring) (ya h : R),
  ya < h ->
  exists ylo,
    ya < ylo /\ ylo <= h /\
    forall q : Point, py q = ylo -> ray_avoids_vertices q r.
Proof.
  intros r ya h Hlt.
  pose proof (level_gap_pos ya r) as Hg.
  set (g := level_gap ya r) in *.
  exists (Rmin h (ya + g / 2)).
  assert (Hmin1 : Rmin h (ya + g / 2) <= h) by apply Rmin_l.
  assert (Hmin2 : Rmin h (ya + g / 2) <= ya + g / 2) by apply Rmin_r.
  assert (Hlo : ya < Rmin h (ya + g / 2))
    by (apply Rmin_glb_lt; lra).
  split; [ exact Hlo | ]. split; [ exact Hmin1 | ].
  intros q Hq.
  apply (guard_of_fresh_level r q ya); unfold g in *; lra.
Qed.

(* ---------------------------------------------------------------------------
   §3  THE WALK STEP: east run-up + wall corridor, one complement path.
   --------------------------------------------------------------------------- *)

Theorem walk_step : forall (r : Ring) (p : Point) (e1 : Edge)
                           (X1 ylo delta : R),
  ring_complement r p ->
  ray_avoids_vertices p r ->
  min_cross_x p (ring_edges r) = Some X1 ->
  In e1 (ring_edges r) ->
  edge_crosses_ray_ho p e1 ->
  cross_x p e1 = X1 ->
  0 < delta ->
  delta < X1 - px p ->
  ylo <= py p ->
  (forall y, ylo <= y <= py p -> ~ ring_image r (corridor e1 delta y)) ->
  connected_in_complement_cont r p (corridor e1 delta ylo) /\
  ring_complement r (corridor e1 delta ylo).
Proof.
  intros r p e1 X1 ylo delta Hcompl Hrav Hmin Hin Hc HX Hd Hdw Hylo Hfree.
  assert (Hnh : py (fst e1) <> py (snd e1))
    by (exact (crossing_edge_nonhorizontal r p e1 Hrav Hin Hc)).
  (* the east run-up ends exactly at the corridor's top point *)
  assert (Htop : corridor e1 delta (py p) = mkPoint (X1 - delta) (py p))
    by (rewrite (corridor_top_is_wall_point p e1 delta Hnh), HX; reflexivity).
  assert (Heast : connected_in_complement_cont r p
                    (mkPoint (X1 - delta) (py p))).
  { apply (east_walk_connected r p X1 (X1 - delta) Hcompl Hrav Hmin); lra. }
  assert (Hcorr : connected_in_complement_cont r
                    (corridor e1 delta (py p)) (corridor e1 delta ylo)).
  { apply (corridor_connected r e1 ylo (py p) delta Hnh Hylo Hfree). }
  rewrite Htop in Hcorr.
  split.
  - exact (connected_in_complement_cont_trans r p
             (mkPoint (X1 - delta) (py p)) (corridor e1 delta ylo)
             Heast Hcorr).
  - intro Himg. exact (Hfree ylo ltac:(lra) Himg).
Qed.

(* The guarded variant: park the lower end inside a vertex-level-free gap
   strictly above a target level, so the destination carries the ray guard. *)
Theorem walk_step_guarded : forall (r : Ring) (p : Point) (e1 : Edge)
                                   (X1 ya delta : R),
  ring_complement r p ->
  ray_avoids_vertices p r ->
  min_cross_x p (ring_edges r) = Some X1 ->
  In e1 (ring_edges r) ->
  edge_crosses_ray_ho p e1 ->
  cross_x p e1 = X1 ->
  0 < delta ->
  delta < X1 - px p ->
  ya < py p ->
  (forall y, ya < y <= py p -> ~ ring_image r (corridor e1 delta y)) ->
  exists q : Point,
    connected_in_complement_cont r p q /\
    ring_complement r q /\
    ray_avoids_vertices q r.
Proof.
  intros r p e1 X1 ya delta Hcompl Hrav Hmin Hin Hc HX Hd Hdw Hya Hfree.
  destruct (exists_parked_height r ya (py p) Hya) as [ylo [Hlo [Hhi Hguard]]].
  assert (Hfree' : forall y, ylo <= y <= py p ->
            ~ ring_image r (corridor e1 delta y)).
  { intros y [Hw1 Hw2]. apply Hfree. lra. }
  destruct (walk_step r p e1 X1 ylo delta Hcompl Hrav Hmin Hin Hc HX Hd Hdw
              Hhi Hfree')
    as [Hconn Hcomplq].
  exists (corridor e1 delta ylo).
  split; [ exact Hconn | ]. split; [ exact Hcomplq | ].
  apply Hguard. unfold corridor; cbn [py]. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions cross_x_is_edge_x_at.
Print Assumptions exists_parked_height.
Print Assumptions walk_step.
Print Assumptions walk_step_guarded.
