(* ============================================================================
   NetTopologySuite.Proofs.GeneralTriangleOffringSeam
   ----------------------------------------------------------------------------
   The residual closed: EXTERIOR points of a triangle have EVEN ray parity --
   and with it, the corrected off-ring H1 seam discharged TOTALLY for the
   arbitrary triangle.  The triangle is the SECOND total family, after the
   rectangle (RectangleOffringSeam.v), and the first with sloped edges.

   `GeneralTriangleExterior.v` reduced the triangle's total seam to one fact:

     gtri p < 0  ->  ~ point_in_ring p (gtri_ring ...)     (under the guard)

   The guard is necessary: for the triangle (0,0),(2,2),(0,4) and the EXTERIOR
   point (-1,2), the ray crosses edge C--A once and then GRAZES vertex B, so
   the count is 1 (odd) -- `ray_avoids_vertices` excludes exactly this.

   Proof shape.  `point_in_ring` is an odd crossing-subset of the three edges;
   inversion (`rpo3_cases`) yields the four odd subsets {AB}, {BC}, {CA},
   {AB,BC,CA}.  The triple dies on heights alone (the directed straddle
   intervals are pairwise incompatible).  Each singleton dies by a trichotomy
   on the height of the OPPOSITE vertex:
     - at the opposite vertex's height, the guard puts that vertex strictly
       WEST, which factors both adjacent slacks as
       (height difference) * (vertex x - px p) and forces a sign contradiction
       with `0 < gdbl` or with the negative-slack witness;
     - off that height, the skipped edges' negations pin one slack's sign,
       the slack-sum identity (`g_sum`) pins another, and the barycentric
       height identity
         gsB*(ay-h) + gsC*(by_-h) + gsA*(cy-h) = 0
       is violated strictly.

   Headlines:
     - `gtri_exterior_even_parity` : the residual, Qed;
     - `gtri_parity_seam_offring`  : the TOTAL off-ring seam for every CCW
       triangle and every point -- the second family instance of the
       corrected H1 seam Prop itself.

   Pure-R; three-axiom.  No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam.
From NTS.Proofs Require Import PointInRingCorrect JCT JCT_OnEdgeCounterexample.
From NTS.Proofs Require Import RectangleJCT RectangleSeparation RectangleOffringSeam.
From NTS.Proofs Require Import GeneralTriangleSeparation GeneralTriangleParity.
From NTS.Proofs Require Import GeneralTriangleHoleNesting GeneralTriangleJCT.
From NTS.Proofs Require Import GeneralTriangleExterior.
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §1  Parity inversion: an odd crossing count over three edges is one of the
       four odd subsets.
   --------------------------------------------------------------------------- *)

Lemma rpo3_cases : forall p e1 e2 e3,
  ray_parity_odd p [e1; e2; e3] ->
     (edge_crosses_ray p e1 /\ edge_crosses_ray p e2 /\ edge_crosses_ray p e3)
  \/ (edge_crosses_ray p e1 /\ ~ edge_crosses_ray p e2 /\ ~ edge_crosses_ray p e3)
  \/ (~ edge_crosses_ray p e1 /\ edge_crosses_ray p e2 /\ ~ edge_crosses_ray p e3)
  \/ (~ edge_crosses_ray p e1 /\ ~ edge_crosses_ray p e2 /\ edge_crosses_ray p e3).
Proof.
  intros p e1 e2 e3 H.
  inversion H as [? ? Hc1 Hr1 | ? ? Hn1 Hr1]; subst.
  - inversion Hr1 as [| ? ? Hc2 Hr2 | ? ? Hn2 Hr2]; subst.
    + inversion Hr2 as [? ? Hc3 Hr3 | ? ? Hn3 Hr3]; subst.
      * left; auto.
      * inversion Hr3.
    + inversion Hr2 as [| ? ? Hc3 Hr3 | ? ? Hn3 Hr3]; subst.
      * inversion Hr3.
      * right; left; auto.
  - inversion Hr1 as [? ? Hc2 Hr2 | ? ? Hn2 Hr2]; subst.
    + inversion Hr2 as [| ? ? Hc3 Hr3 | ? ? Hn3 Hr3]; subst.
      * inversion Hr3.
      * right; right; left; auto.
    + inversion Hr2 as [? ? Hc3 Hr3 | ? ? Hn3 Hr3]; subst.
      * right; right; right; auto.
      * inversion Hr3.
Qed.

(* ---------------------------------------------------------------------------
   §2  The residual: exterior points have even parity, under the ray guard.
   --------------------------------------------------------------------------- *)

Theorem gtri_exterior_even_parity : forall ax ay bx by_ cx cy p,
  0 < gdbl ax ay bx by_ cx cy ->
  gtri ax ay bx by_ cx cy p < 0 ->
  ray_avoids_vertices p (gtri_ring ax ay bx by_ cx cy) ->
  ~ point_in_ring p (gtri_ring ax ay bx by_ cx cy).
Proof.
  intros ax ay bx by_ cx cy p Hccw Hneg Hrav Hpir.
  unfold point_in_ring in Hpir.
  rewrite (ring_edges_gtri ax ay bx by_ cx cy) in Hpir.
  (* per-edge crossing characterisations, stated over the folded slacks *)
  assert (CAB : edge_crosses_ray p (mkPoint ax ay, mkPoint bx by_)
                <-> (ay < py p < by_ /\ 0 < gsA ax ay bx by_ p)
                 \/ (by_ < py p < ay /\ gsA ax ay bx by_ p < 0))
    by (exact (edge_cross_sign ax ay bx by_ p)).
  assert (CBC : edge_crosses_ray p (mkPoint bx by_, mkPoint cx cy)
                <-> (by_ < py p < cy /\ 0 < gsB bx by_ cx cy p)
                 \/ (cy < py p < by_ /\ gsB bx by_ cx cy p < 0))
    by (exact (edge_cross_sign bx by_ cx cy p)).
  assert (CCA : edge_crosses_ray p (mkPoint cx cy, mkPoint ax ay)
                <-> (cy < py p < ay /\ 0 < gsC ax ay cx cy p)
                 \/ (ay < py p < cy /\ gsC ax ay cx cy p < 0))
    by (exact (edge_cross_sign cx cy ax ay p)).
  (* arithmetic toolkit, all over the folded slacks *)
  pose proof (g_sum ax ay bx by_ cx cy p) as Hsum.
  assert (Hkey : gsB bx by_ cx cy p * (ay - py p)
               + gsC ax ay cx cy p * (by_ - py p)
               + gsA ax ay bx by_ p * (cy - py p) = 0)
    by (unfold gsA, gsB, gsC; ring).
  assert (Hslack : gsA ax ay bx by_ p < 0 \/ gsB bx by_ cx cy p < 0
                   \/ gsC ax ay cx cy p < 0).
  { unfold gtri in Hneg.
    destruct (Rmin_neg_inv _ _ Hneg) as [H1 | H1];
      [ destruct (Rmin_neg_inv _ _ H1) as [H2 | H2];
        [ left; exact H2 | right; left; exact H2 ]
      | right; right; exact H1 ]. }
  (* the guard, conditionally at each vertex *)
  assert (GA : py p = ay -> ax < px p).
  { intro Hy.
    apply (guard_vertex_west ax ay bx by_ cx cy p (mkPoint ax ay));
      [ unfold gtri_ring; cbn; auto | exact Hrav | cbn; symmetry; exact Hy ]. }
  assert (GB : py p = by_ -> bx < px p).
  { intro Hy.
    apply (guard_vertex_west ax ay bx by_ cx cy p (mkPoint bx by_));
      [ unfold gtri_ring; cbn; auto | exact Hrav | cbn; symmetry; exact Hy ]. }
  assert (GC : py p = cy -> cx < px p).
  { intro Hy.
    apply (guard_vertex_west ax ay bx by_ cx cy p (mkPoint cx cy));
      [ unfold gtri_ring; cbn; auto | exact Hrav | cbn; symmetry; exact Hy ]. }
  (* slack factorisations at each vertex height *)
  assert (FAay : py p = ay -> gsA ax ay bx by_ p = (by_ - ay) * (ax - px p))
    by (intro He; unfold gsA; rewrite He; ring).
  assert (FCay : py p = ay -> gsC ax ay cx cy p = (ay - cy) * (ax - px p))
    by (intro He; unfold gsC; rewrite He; ring).
  assert (FAby : py p = by_ -> gsA ax ay bx by_ p = (by_ - ay) * (bx - px p))
    by (intro He; unfold gsA; rewrite He; ring).
  assert (FBby : py p = by_ -> gsB bx by_ cx cy p = (cy - by_) * (bx - px p))
    by (intro He; unfold gsB; rewrite He; ring).
  assert (FBcy : py p = cy -> gsB bx by_ cx cy p = (cy - by_) * (cx - px p))
    by (intro He; unfold gsB; rewrite He; ring).
  assert (FCcy : py p = cy -> gsC ax ay cx cy p = (ay - cy) * (cx - px p))
    by (intro He; unfold gsC; rewrite He; ring).
  destruct (rpo3_cases _ _ _ _ Hpir)
    as [[Hc1 [Hc2 Hc3]] | [[Hc1 [Hn2 Hn3]] | [[Hn1 [Hc2 Hn3]] | [Hn1 [Hn2 Hc3]]]]].
  - (* all three cross: the directed straddles are pairwise incompatible *)
    apply (proj1 CAB) in Hc1. apply (proj1 CBC) in Hc2. apply (proj1 CCA) in Hc3.
    destruct Hc1 as [[[? ?] ?] | [[? ?] ?]];
    destruct Hc2 as [[[? ?] ?] | [[? ?] ?]];
    destruct Hc3 as [[[? ?] ?] | [[? ?] ?]]; lra.
  - (* only AB crosses *)
    apply (proj1 CAB) in Hc1.
    assert (Hn2' := fun d => Hn2 (proj2 CBC d)).
    assert (Hn3' := fun d => Hn3 (proj2 CCA d)).
    destruct Hc1 as [[[Hh1 Hh2] HA] | [[Hh1 Hh2] HA]].
    + (* up: ay < h < by_, 0 < gsA *)
      destruct (Rtotal_order (py p) cy) as [Hhc | [Hhc | Hhc]].
      * (* h < cy : ~CA-down forces 0 <= gsC; slack witness is gsB *)
        assert (HC : 0 <= gsC ax ay cx cy p).
        { destruct (Rle_or_lt 0 (gsC ax ay cx cy p)) as [Hok | Hbad];
            [ exact Hok | exfalso ].
          apply Hn3'. right. split; [ split; lra | exact Hbad ]. }
        destruct Hslack as [HB | [HB | HB]]; [ lra | | lra ].
        assert (T1 : 0 < gsB bx by_ cx cy p * (ay - py p)) by (clear - HB Hh1; nra).
        assert (T2 : 0 <= gsC ax ay cx cy p * (by_ - py p)) by (clear - HC Hh2; nra).
        assert (T3 : 0 < gsA ax ay bx by_ p * (cy - py p)) by (clear - HA Hhc; nra).
        clear - Hkey T1 T2 T3; lra.
      * (* h = cy : C grazed, strictly west; both adjacent slacks positive *)
        specialize (GC Hhc).
        pose proof (FBcy Hhc) as HFB. pose proof (FCcy Hhc) as HFC.
        assert (Hd1 : cy - by_ < 0) by (clear - Hh2 Hhc; lra).
        assert (Hd2 : ay - cy < 0) by (clear - Hh1 Hhc; lra).
        assert (Hd3 : cx - px p < 0) by (clear - GC; lra).
        assert (TB : 0 < gsB bx by_ cx cy p) by (rewrite HFB; clear - Hd1 Hd3; nra).
        assert (TC : 0 < gsC ax ay cx cy p) by (rewrite HFC; clear - Hd2 Hd3; nra).
        destruct Hslack as [HX | [HX | HX]]; clear - HA TB TC HX; lra.
      * (* h > cy : ~BC-down forces 0 <= gsB; slack witness is gsC *)
        assert (HB : 0 <= gsB bx by_ cx cy p).
        { destruct (Rle_or_lt 0 (gsB bx by_ cx cy p)) as [Hok | Hbad];
            [ exact Hok | exfalso ].
          apply Hn2'. right. split; [ split; lra | exact Hbad ]. }
        destruct Hslack as [HX | [HX | HX]]; [ lra | lra | ].
        assert (T1 : gsB bx by_ cx cy p * (ay - py p) <= 0) by (clear - HB Hh1; nra).
        assert (T2 : gsC ax ay cx cy p * (by_ - py p) < 0) by (clear - HX Hh2; nra).
        assert (T3 : gsA ax ay bx by_ p * (cy - py p) < 0) by (clear - HA Hhc; nra).
        clear - Hkey T1 T2 T3; lra.
    + (* down: by_ < h < ay, gsA < 0 *)
      destruct (Rtotal_order (py p) cy) as [Hhc | [Hhc | Hhc]].
      * (* h < cy : ~BC-up forces gsB <= 0; g_sum gives 0 < gsC *)
        assert (HB : gsB bx by_ cx cy p <= 0).
        { destruct (Rle_or_lt (gsB bx by_ cx cy p) 0) as [Hok | Hbad];
            [ exact Hok | exfalso ].
          apply Hn2'. left. split; [ split; lra | exact Hbad ]. }
        assert (HCpos : 0 < gsC ax ay cx cy p) by (clear - Hsum Hccw HA HB; lra).
        assert (T1 : gsB bx by_ cx cy p * (ay - py p) <= 0) by (clear - HB Hh2; nra).
        assert (T2 : gsC ax ay cx cy p * (by_ - py p) < 0) by (clear - HCpos Hh1; nra).
        assert (T3 : gsA ax ay bx by_ p * (cy - py p) < 0) by (clear - HA Hhc; nra).
        clear - Hkey T1 T2 T3; lra.
      * (* h = cy : C grazed, strictly west; both adjacent slacks negative *)
        specialize (GC Hhc).
        pose proof (FBcy Hhc) as HFB. pose proof (FCcy Hhc) as HFC.
        assert (Hd1 : 0 < cy - by_) by (clear - Hh1 Hhc; lra).
        assert (Hd2 : 0 < ay - cy) by (clear - Hh2 Hhc; lra).
        assert (Hd3 : cx - px p < 0) by (clear - GC; lra).
        assert (TB : gsB bx by_ cx cy p < 0) by (rewrite HFB; clear - Hd1 Hd3; nra).
        assert (TC : gsC ax ay cx cy p < 0) by (rewrite HFC; clear - Hd2 Hd3; nra).
        clear - HA TB TC Hsum Hccw; lra.
      * (* h > cy : ~CA-up forces gsC <= 0; g_sum gives 0 < gsB *)
        assert (HC : gsC ax ay cx cy p <= 0).
        { destruct (Rle_or_lt (gsC ax ay cx cy p) 0) as [Hok | Hbad];
            [ exact Hok | exfalso ].
          apply Hn3'. left. split; [ split; lra | exact Hbad ]. }
        assert (HBpos : 0 < gsB bx by_ cx cy p) by (clear - Hsum Hccw HA HC; lra).
        assert (T1 : 0 < gsB bx by_ cx cy p * (ay - py p)) by (clear - HBpos Hh2; nra).
        assert (T2 : 0 <= gsC ax ay cx cy p * (by_ - py p)) by (clear - HC Hh1; nra).
        assert (T3 : 0 < gsA ax ay bx by_ p * (cy - py p)) by (clear - HA Hhc; nra).
        clear - Hkey T1 T2 T3; lra.
  - (* only BC crosses *)
    apply (proj1 CBC) in Hc2.
    assert (Hn1' := fun d => Hn1 (proj2 CAB d)).
    assert (Hn3' := fun d => Hn3 (proj2 CCA d)).
    destruct Hc2 as [[[Hh1 Hh2] HB] | [[Hh1 Hh2] HB]].
    + (* up: by_ < h < cy, 0 < gsB *)
      destruct (Rtotal_order (py p) ay) as [Hha | [Hha | Hha]].
      * (* h < ay : ~AB-down forces 0 <= gsA; slack witness is gsC *)
        assert (HA : 0 <= gsA ax ay bx by_ p).
        { destruct (Rle_or_lt 0 (gsA ax ay bx by_ p)) as [Hok | Hbad];
            [ exact Hok | exfalso ].
          apply Hn1'. right. split; [ split; lra | exact Hbad ]. }
        destruct Hslack as [HX | [HX | HX]]; [ lra | lra | ].
        assert (T1 : 0 < gsB bx by_ cx cy p * (ay - py p)) by (clear - HB Hha; nra).
        assert (T2 : 0 < gsC ax ay cx cy p * (by_ - py p)) by (clear - HX Hh1; nra).
        assert (T3 : 0 <= gsA ax ay bx by_ p * (cy - py p)) by (clear - HA Hh2; nra).
        clear - Hkey T1 T2 T3; lra.
      * (* h = ay : A grazed, strictly west; both adjacent slacks positive *)
        specialize (GA Hha).
        pose proof (FAay Hha) as HFA. pose proof (FCay Hha) as HFC.
        assert (Hd1 : by_ - ay < 0) by (clear - Hh1 Hha; lra).
        assert (Hd2 : ay - cy < 0) by (clear - Hh2 Hha; lra).
        assert (Hd3 : ax - px p < 0) by (clear - GA; lra).
        assert (TA : 0 < gsA ax ay bx by_ p) by (rewrite HFA; clear - Hd1 Hd3; nra).
        assert (TC : 0 < gsC ax ay cx cy p) by (rewrite HFC; clear - Hd2 Hd3; nra).
        destruct Hslack as [HX | [HX | HX]]; clear - HB TA TC HX; lra.
      * (* h > ay : ~CA-down forces 0 <= gsC; slack witness is gsA *)
        assert (HC : 0 <= gsC ax ay cx cy p).
        { destruct (Rle_or_lt 0 (gsC ax ay cx cy p)) as [Hok | Hbad];
            [ exact Hok | exfalso ].
          apply Hn3'. right. split; [ split; lra | exact Hbad ]. }
        destruct Hslack as [HX | [HX | HX]]; [ | lra | lra ].
        assert (T1 : gsB bx by_ cx cy p * (ay - py p) < 0) by (clear - HB Hha; nra).
        assert (T2 : gsC ax ay cx cy p * (by_ - py p) <= 0) by (clear - HC Hh1; nra).
        assert (T3 : gsA ax ay bx by_ p * (cy - py p) < 0) by (clear - HX Hh2; nra).
        clear - Hkey T1 T2 T3; lra.
    + (* down: cy < h < by_, gsB < 0 *)
      destruct (Rtotal_order (py p) ay) as [Hha | [Hha | Hha]].
      * (* h < ay : ~CA-up forces gsC <= 0; g_sum gives 0 < gsA *)
        assert (HC : gsC ax ay cx cy p <= 0).
        { destruct (Rle_or_lt (gsC ax ay cx cy p) 0) as [Hok | Hbad];
            [ exact Hok | exfalso ].
          apply Hn3'. left. split; [ split; lra | exact Hbad ]. }
        assert (HApos : 0 < gsA ax ay bx by_ p) by (clear - Hsum Hccw HB HC; lra).
        assert (T1 : gsB bx by_ cx cy p * (ay - py p) < 0) by (clear - HB Hha; nra).
        assert (T2 : gsC ax ay cx cy p * (by_ - py p) <= 0) by (clear - HC Hh2; nra).
        assert (T3 : gsA ax ay bx by_ p * (cy - py p) < 0) by (clear - HApos Hh1; nra).
        clear - Hkey T1 T2 T3; lra.
      * (* h = ay : A grazed, strictly west; both adjacent slacks negative *)
        specialize (GA Hha).
        pose proof (FAay Hha) as HFA. pose proof (FCay Hha) as HFC.
        assert (Hd1 : 0 < by_ - ay) by (clear - Hh2 Hha; lra).
        assert (Hd2 : 0 < ay - cy) by (clear - Hh1 Hha; lra).
        assert (Hd3 : ax - px p < 0) by (clear - GA; lra).
        assert (TA : gsA ax ay bx by_ p < 0) by (rewrite HFA; clear - Hd1 Hd3; nra).
        assert (TC : gsC ax ay cx cy p < 0) by (rewrite HFC; clear - Hd2 Hd3; nra).
        clear - HB TA TC Hsum Hccw; lra.
      * (* h > ay : ~AB-up forces gsA <= 0; g_sum gives 0 < gsC *)
        assert (HA : gsA ax ay bx by_ p <= 0).
        { destruct (Rle_or_lt (gsA ax ay bx by_ p) 0) as [Hok | Hbad];
            [ exact Hok | exfalso ].
          apply Hn1'. left. split; [ split; lra | exact Hbad ]. }
        assert (HCpos : 0 < gsC ax ay cx cy p) by (clear - Hsum Hccw HB HA; lra).
        assert (T1 : 0 < gsB bx by_ cx cy p * (ay - py p)) by (clear - HB Hha; nra).
        assert (T2 : 0 < gsC ax ay cx cy p * (by_ - py p)) by (clear - HCpos Hh2; nra).
        assert (T3 : 0 <= gsA ax ay bx by_ p * (cy - py p)) by (clear - HA Hh1; nra).
        clear - Hkey T1 T2 T3; lra.
  - (* only CA crosses *)
    apply (proj1 CCA) in Hc3.
    assert (Hn1' := fun d => Hn1 (proj2 CAB d)).
    assert (Hn2' := fun d => Hn2 (proj2 CBC d)).
    destruct Hc3 as [[[Hh1 Hh2] HC] | [[Hh1 Hh2] HC]].
    + (* up: cy < h < ay, 0 < gsC *)
      destruct (Rtotal_order (py p) by_) as [Hhb | [Hhb | Hhb]].
      * (* h < by_ : ~BC-down forces 0 <= gsB; slack witness is gsA *)
        assert (HB : 0 <= gsB bx by_ cx cy p).
        { destruct (Rle_or_lt 0 (gsB bx by_ cx cy p)) as [Hok | Hbad];
            [ exact Hok | exfalso ].
          apply Hn2'. right. split; [ split; lra | exact Hbad ]. }
        destruct Hslack as [HX | [HX | HX]]; [ | lra | lra ].
        assert (T1 : 0 <= gsB bx by_ cx cy p * (ay - py p)) by (clear - HB Hh2; nra).
        assert (T2 : 0 < gsC ax ay cx cy p * (by_ - py p)) by (clear - HC Hhb; nra).
        assert (T3 : 0 < gsA ax ay bx by_ p * (cy - py p)) by (clear - HX Hh1; nra).
        clear - Hkey T1 T2 T3; lra.
      * (* h = by_ : B grazed, strictly west; both adjacent slacks positive *)
        specialize (GB Hhb).
        pose proof (FAby Hhb) as HFA. pose proof (FBby Hhb) as HFB.
        assert (Hd1 : by_ - ay < 0) by (clear - Hh2 Hhb; lra).
        assert (Hd2 : cy - by_ < 0) by (clear - Hh1 Hhb; lra).
        assert (Hd3 : bx - px p < 0) by (clear - GB; lra).
        assert (TA : 0 < gsA ax ay bx by_ p) by (rewrite HFA; clear - Hd1 Hd3; nra).
        assert (TB : 0 < gsB bx by_ cx cy p) by (rewrite HFB; clear - Hd2 Hd3; nra).
        destruct Hslack as [HX | [HX | HX]]; clear - HC TA TB HX; lra.
      * (* h > by_ : ~AB-down forces 0 <= gsA; slack witness is gsB *)
        assert (HA : 0 <= gsA ax ay bx by_ p).
        { destruct (Rle_or_lt 0 (gsA ax ay bx by_ p)) as [Hok | Hbad];
            [ exact Hok | exfalso ].
          apply Hn1'. right. split; [ split; lra | exact Hbad ]. }
        destruct Hslack as [HX | [HX | HX]]; [ lra | | lra ].
        assert (T1 : gsB bx by_ cx cy p * (ay - py p) < 0) by (clear - HX Hh2; nra).
        assert (T2 : gsC ax ay cx cy p * (by_ - py p) < 0) by (clear - HC Hhb; nra).
        assert (T3 : gsA ax ay bx by_ p * (cy - py p) <= 0) by (clear - HA Hh1; nra).
        clear - Hkey T1 T2 T3; lra.
    + (* down: ay < h < cy, gsC < 0 *)
      destruct (Rtotal_order (py p) by_) as [Hhb | [Hhb | Hhb]].
      * (* h < by_ : ~AB-up forces gsA <= 0; g_sum gives 0 < gsB *)
        assert (HA : gsA ax ay bx by_ p <= 0).
        { destruct (Rle_or_lt (gsA ax ay bx by_ p) 0) as [Hok | Hbad];
            [ exact Hok | exfalso ].
          apply Hn1'. left. split; [ split; lra | exact Hbad ]. }
        assert (HBpos : 0 < gsB bx by_ cx cy p) by (clear - Hsum Hccw HC HA; lra).
        assert (T1 : gsB bx by_ cx cy p * (ay - py p) < 0) by (clear - HBpos Hh1; nra).
        assert (T2 : gsC ax ay cx cy p * (by_ - py p) < 0) by (clear - HC Hhb; nra).
        assert (T3 : gsA ax ay bx by_ p * (cy - py p) <= 0) by (clear - HA Hh2; nra).
        clear - Hkey T1 T2 T3; lra.
      * (* h = by_ : B grazed, strictly west; both adjacent slacks negative *)
        specialize (GB Hhb).
        pose proof (FAby Hhb) as HFA. pose proof (FBby Hhb) as HFB.
        assert (Hd1 : 0 < by_ - ay) by (clear - Hh1 Hhb; lra).
        assert (Hd2 : 0 < cy - by_) by (clear - Hh2 Hhb; lra).
        assert (Hd3 : bx - px p < 0) by (clear - GB; lra).
        assert (TA : gsA ax ay bx by_ p < 0) by (rewrite HFA; clear - Hd1 Hd3; nra).
        assert (TB : gsB bx by_ cx cy p < 0) by (rewrite HFB; clear - Hd2 Hd3; nra).
        clear - HC TA TB Hsum Hccw; lra.
      * (* h > by_ : ~BC-up forces gsB <= 0; g_sum gives 0 < gsA *)
        assert (HB : gsB bx by_ cx cy p <= 0).
        { destruct (Rle_or_lt (gsB bx by_ cx cy p) 0) as [Hok | Hbad];
            [ exact Hok | exfalso ].
          apply Hn2'. left. split; [ split; lra | exact Hbad ]. }
        assert (HApos : 0 < gsA ax ay bx by_ p) by (clear - Hsum Hccw HC HB; lra).
        assert (T1 : 0 <= gsB bx by_ cx cy p * (ay - py p)) by (clear - HB Hh1; nra).
        assert (T2 : 0 < gsC ax ay cx cy p * (by_ - py p)) by (clear - HC Hhb; nra).
        assert (T3 : 0 < gsA ax ay bx by_ p * (cy - py p)) by (clear - HApos Hh2; nra).
        clear - Hkey T1 T2 T3; lra.
Qed.

(* ---------------------------------------------------------------------------
   §3  THE HEADLINE: the corrected off-ring H1 seam, discharged TOTALLY for
       every CCW triangle -- the second total family, the first with sloped
       edges.
   --------------------------------------------------------------------------- *)

Theorem gtri_parity_seam_offring : forall ax ay bx by_ cx cy p,
  0 < gdbl ax ay bx by_ cx cy ->
  parity_characterises_interior_cont_offring p (gtri_ring ax ay bx by_ cx cy).
Proof.
  intros ax ay bx by_ cx cy p Hccw.
  unfold parity_characterises_interior_cont_offring.
  intros Hs Hc Hm Hcompl Hnh Hrav.
  exact (gtri_parity_seam_offring_of_exterior_parity ax ay bx by_ cx cy p Hccw
           (fun Hneg => gtri_exterior_even_parity ax ay bx by_ cx cy p
                          Hccw Hneg Hrav)
           Hs Hc Hm Hcompl Hnh Hrav).
Qed.

(* Sanity instance: the reference triangle, at an exterior point. *)
Example gtri_seam_reference_exterior :
  parity_characterises_interior_cont_offring (mkPoint 9 1) (gtri_ring 0 0 4 0 0 4).
Proof. apply gtri_parity_seam_offring. unfold gdbl; lra. Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions gtri_exterior_even_parity.
Print Assumptions gtri_parity_seam_offring.
