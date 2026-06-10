(* ============================================================================
   NetTopologySuite.Proofs.GeneralTriangleJCT
   ----------------------------------------------------------------------------
   The coverage layer over `GeneralTriangleHoleNesting.gtri_band_in_ring`:
   the band hypothesis DISCHARGED from interior positivity under the
   rightward-ray genericity guard, and the H1-seam headline it unlocks.

   `GeneralTriangleHoleNesting.v` (the GREEN after `GeneralTriangleParityRED.v`)
   proves `gtri_band_in_ring`: an interior-side point (`0 < gtri p`) whose
   height lies in one of the three DIRECTED edge bands

     ay < py p < by_   \/   by_ < py p < cy   \/   cy < py p < ay

   is `point_in_ring`.  This file removes the band hypothesis:

     gtri_ray_coverage :
       0 < gtri p -> ray_avoids_vertices p (gtri_ring ...) -> (some band holds)

     gtri_interior_in_ring :
       0 < gtri p -> ray_avoids_vertices p (gtri_ring ...) ->
       point_in_ring p (gtri_ring ...)

   The guard is genuinely needed (JCT_VertexGrazingCounterexample.v): a strict-
   interior point whose height equals the MIDDLE vertex's height makes the ray
   graze that vertex and the parity miscounts.  No orientation hypothesis is
   needed: `0 < gtri p` already forces CCW (the slacks sum to `gdbl`).

   Coverage proof shape.  A 27-branch trichotomy over `py p` vs the three
   vertex heights.  Strict branches land in a band, or die on the barycentric
   height identity `gsB*(ay-py) + gsC*(by_-py) + gsA*(cy-py) = 0` (a `ring`
   consequence of `g_sum`/`g_baryy`).  In the equality (grazing) branches the
   guard forces the grazed vertex strictly WEST, which factors the two
   adjacent slacks as (height difference) * (vertex x - px p) and orients the
   remaining heights -- every guard-consistent equality branch is one a band
   already covers; the rest are `nra` contradictions.

   Headlines:
     - `general_triangle_parity_characterises_interior` : for strict-interior
       points under the guard, `point_in_ring <-> geometric_interior_cont` --
       the arbitrary triangle joins the rectangle and the right triangle as a
       fully Qed-closed instance of the H1 parity seam
       (`JCT.parity_characterises_interior_cont_strict`), as far as the
       strict-interior scope of those instances goes;
     - `hole_inside_outer_triangle_guarded` (+ `_generic`) : hole nesting with
       no band bookkeeping -- the guard (or simply three height disequalities)
       replaces the explicit band; closes the "assembly TODO" of Stage D
       (triangle) in docs/hole-inside-outer-plan.md.

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam.
From NTS.Proofs Require Import PointInRingCorrect.
From NTS.Proofs Require Import GeneralTriangleSeparation GeneralTriangleParity.
From NTS.Proofs Require Import GeneralTriangleHoleNesting.
Import ListNotations.

Local Open Scope R_scope.

Section GeneralTriangleJCT.

Variables ax ay bx by_ cx cy : R.

(* ---------------------------------------------------------------------------
   §1  The guard, instantiated: a vertex at the ray's height is strictly west.
   --------------------------------------------------------------------------- *)

Lemma guard_vertex_west : forall p v,
  In v (gtri_ring ax ay bx by_ cx cy) ->
  ray_avoids_vertices p (gtri_ring ax ay bx by_ cx cy) ->
  py v = py p -> px v < px p.
Proof.
  intros p v Hin Hrav Hy.
  destruct (Rle_or_lt (px p) (px v)) as [Hle | Hlt]; [ | exact Hlt ].
  exfalso. apply (Hrav v Hin). split; assumption.
Qed.

(* ---------------------------------------------------------------------------
   §2  Coverage: a guarded strict-interior point's height lies in one of the
       three directed edge-height bands.
   --------------------------------------------------------------------------- *)

Lemma gtri_ray_coverage : forall p,
  0 < gtri ax ay bx by_ cx cy p ->
  ray_avoids_vertices p (gtri_ring ax ay bx by_ cx cy) ->
  ay < py p < by_ \/ by_ < py p < cy \/ cy < py p < ay.
Proof.
  intros p Hpos Hrav.
  apply gtri_pos_iff in Hpos; destruct Hpos as [HA [HB HC]].
  (* The barycentric height identity: a `ring` fact, no hypotheses. *)
  assert (Hkey : gsB bx by_ cx cy p * (ay - py p)
               + gsC ax ay cx cy p * (by_ - py p)
               + gsA ax ay bx by_ p * (cy - py p) = 0)
    by (unfold gsA, gsB, gsC; ring).
  (* The guard, conditionally at each vertex. *)
  assert (GA : py p = ay -> ax < px p).
  { intro Hy.
    apply (guard_vertex_west p (mkPoint ax ay));
      [ unfold gtri_ring; cbn; auto | exact Hrav | cbn; symmetry; exact Hy ]. }
  assert (GB : py p = by_ -> bx < px p).
  { intro Hy.
    apply (guard_vertex_west p (mkPoint bx by_));
      [ unfold gtri_ring; cbn; auto | exact Hrav | cbn; symmetry; exact Hy ]. }
  assert (GC : py p = cy -> cx < px p).
  { intro Hy.
    apply (guard_vertex_west p (mkPoint cx cy));
      [ unfold gtri_ring; cbn; auto | exact Hrav | cbn; symmetry; exact Hy ]. }
  destruct (Rtotal_order (py p) ay) as [Hay | [Hay | Hay]];
  destruct (Rtotal_order (py p) by_) as [Hby | [Hby | Hby]];
  destruct (Rtotal_order (py p) cy) as [Hcy | [Hcy | Hcy]];
  try (left; split; lra);
  try (right; left; split; lra);
  try (right; right; split; lra);
  exfalso;
  try specialize (GA Hay); try specialize (GB Hby); try specialize (GC Hcy);
  unfold gsA, gsB, gsC in HA, HB, HC, Hkey;
  nra.
Qed.

(* ---------------------------------------------------------------------------
   §3  The band hypothesis of `gtri_band_in_ring`, discharged.
   --------------------------------------------------------------------------- *)

Theorem gtri_interior_in_ring : forall p,
  0 < gtri ax ay bx by_ cx cy p ->
  ray_avoids_vertices p (gtri_ring ax ay bx by_ cx cy) ->
  point_in_ring p (gtri_ring ax ay bx by_ cx cy).
Proof.
  intros p Hpos Hrav.
  apply gtri_band_in_ring; [ exact Hpos | ].
  apply gtri_ray_coverage; assumption.
Qed.

(* ---------------------------------------------------------------------------
   §4  Headline 1: the arbitrary triangle joins the rectangle and the right
       triangle -- for guarded strict-interior points, ray parity IS the
       continuous geometric interior.  Orientation is derived, not assumed.
   --------------------------------------------------------------------------- *)

Theorem general_triangle_parity_characterises_interior : forall p,
  0 < gtri ax ay bx by_ cx cy p ->
  ray_avoids_vertices p (gtri_ring ax ay bx by_ cx cy) ->
  (point_in_ring p (gtri_ring ax ay bx by_ cx cy)
     <-> geometric_interior_cont p (gtri_ring ax ay bx by_ cx cy)).
Proof.
  intros p Hpos Hrav.
  assert (Hccw : 0 < gdbl ax ay bx by_ cx cy).
  { pose proof Hpos as H; apply gtri_pos_iff in H; destruct H as [HA [HB HC]].
    pose proof (g_sum ax ay bx by_ cx cy p); lra. }
  split; intros _.
  - apply (gtri_interior_is_geometric ax ay bx by_ cx cy Hccw p Hpos).
  - apply gtri_interior_in_ring; assumption.
Qed.

(* ---------------------------------------------------------------------------
   §5  Headline 2: hole nesting with the band replaced by the guard.
   --------------------------------------------------------------------------- *)

Theorem hole_inside_outer_triangle_guarded : forall (hole : Ring) p,
  In p hole ->
  0 < gtri ax ay bx by_ cx cy p ->
  ray_avoids_vertices p (gtri_ring ax ay bx by_ cx cy) ->
  hole_inside_outer (gtri_ring ax ay bx by_ cx cy) hole.
Proof.
  intros hole p Hin Hpos Hrav.
  exists p. split; [ exact Hin | apply gtri_interior_in_ring; assumption ].
Qed.

(* Convenience generic-position form: distinct heights imply the guard. *)
Lemma ray_avoids_vertices_gtri_of_heights : forall p,
  py p <> ay -> py p <> by_ -> py p <> cy ->
  ray_avoids_vertices p (gtri_ring ax ay bx by_ cx cy).
Proof.
  intros p Ha Hb Hc v Hv [Heq _].
  unfold gtri_ring in Hv; cbn in Hv.
  destruct Hv as [Hv | [Hv | [Hv | [Hv | []]]]]; subst v; cbn [py] in Heq;
    [ exact (Ha (eq_sym Heq)) | exact (Hb (eq_sym Heq))
    | exact (Hc (eq_sym Heq)) | exact (Ha (eq_sym Heq)) ].
Qed.

Corollary hole_inside_outer_triangle_generic : forall (hole : Ring) p,
  In p hole ->
  0 < gtri ax ay bx by_ cx cy p ->
  py p <> ay -> py p <> by_ -> py p <> cy ->
  hole_inside_outer (gtri_ring ax ay bx by_ cx cy) hole.
Proof.
  intros hole p Hin Hpos Ha Hb Hc.
  apply (hole_inside_outer_triangle_guarded hole p Hin Hpos).
  apply ray_avoids_vertices_gtri_of_heights; assumption.
Qed.

End GeneralTriangleJCT.

(* ---------------------------------------------------------------------------
   §6  Concrete instance via the generic form: no band bookkeeping, just three
       height disequalities (compare GeneralTriangleHoleNesting's example,
       which names the live band explicitly).
   --------------------------------------------------------------------------- *)

Example hole_inside_outer_triangle_generic_example :
  hole_inside_outer (gtri_ring 0 0 4 0 0 4) [mkPoint 1 1; mkPoint 2 1].
Proof.
  apply (hole_inside_outer_triangle_generic 0 0 4 0 0 4 _ (mkPoint 1 1)).
  - left; reflexivity.
  - apply (proj2 (gtri_pos_iff 0 0 4 0 0 4 (mkPoint 1 1))).
    unfold gsA, gsB, gsC; cbn [px py]; repeat split; lra.
  - cbn [py]; lra.
  - cbn [py]; lra.
  - cbn [py]; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions gtri_interior_in_ring.
Print Assumptions general_triangle_parity_characterises_interior.
Print Assumptions hole_inside_outer_triangle_guarded.
Print Assumptions hole_inside_outer_triangle_generic_example.
