(* ============================================================================
   NetTopologySuite.Proofs.JCTHugCycle
   ----------------------------------------------------------------------------
   ESCAPE DESCENT, rung 5c-14: THE CYCLE WALK and THE ENTRY.

   `hugs_everywhere`: once the walker hugs ANY edge, it hugs EVERY edge --
   the per-corner total step (rung 5c-13) iterates along the ring's chain
   (`hugs_chain`, plain list induction on the suffix: consecutive edges
   share their middle vertex, and the degenerate self-loop and equal-edge
   cases are killed by no-horizontality), and the seam wraps by one more
   corner step from the closing edge (last, p) to the opening edge
   (p, head).  No orbit combinatorics: the ring IS the iteration order.

   `hug_entry`: the walk starts where the descent stands -- the east
   approach (rung 1) carries the guarded walker to just west of its first
   wall, exactly the wall's west corridor point at the walker's own
   height (`corridor_top_is_wall_point`), and the span-interior corridor
   (rung 4b-2) rides from there to the wall's midpoint: `hugs_west` of
   the first wall, anchored at the walker itself.

   Together: from any even guarded complement point with a positive
   count, the anchor is connected to BOTH side-corridors of EVERY edge of
   the ring reached on the walk's side -- in particular to a corridor of
   an eastmost-vertex edge, where the final rung harvests the
   count-payoff.

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
From NTS.Proofs Require Import JCTEastApproach JCTCorridor JCTWalkKit JCTWalkStep.
From NTS.Proofs Require Import JCTTautClearance JCTWallClear JCTCornerSector.
From NTS.Proofs Require Import JCTCornerClear JCTMirrorKit JCTTopPassage.
From NTS.Proofs Require Import JCTPassageKit JCTTipCrossing JCTCornerBox.
From NTS.Proofs Require Import JCTRingCycle JCTHugStep JCTHugMirror.
From NTS.Proofs Require Import JCTMinOpenStep JCTMinOpenMirror JCTCornerDisk.
From NTS.Proofs Require Import JCTPinchedStep JCTPinchedMirror.
From NTS.Proofs Require Import JCTCornerDispatch.
Import ListNotations.

Local Open Scope R_scope.

(* ---------------------------------------------------------------------------
   §1  Chain propagation and the seam wrap.
   --------------------------------------------------------------------------- *)

Lemma hugs_chain : forall (r : Ring) (q : Point),
  ring_taut r -> ring_core_nodup r -> no_horizontal_edges r ->
  forall (l2 : list Point) (a b : Point) (l1 : list Point),
  r = l1 ++ a :: b :: l2 ->
  hugs r (a, b) q ->
  forall g, In g (ring_edges (a :: b :: l2)) -> hugs r g q.
Proof.
  intros r q Htaut Hnd Hnoh l2.
  induction l2 as [| z l2' IH]; intros a b l1 Hr Hhug g Hg.
  - cbn in Hg. destruct Hg as [Hg | []]. subst g. exact Hhug.
  - cbn [ring_edges] in Hg.
    destruct Hg as [Hg | Hg]; [ subst g; exact Hhug | ].
    assert (Hinab : In (a, b) (ring_edges r))
      by (apply ring_edges_in_split; exists l1, (z :: l2'); exact Hr).
    assert (Hinbz : In (b, z) (ring_edges r)).
    { apply ring_edges_in_split. exists (l1 ++ [a]), l2'.
      rewrite Hr, <- app_assoc. reflexivity. }
    assert (Hnef : (a, b) <> (b, z)).
    { intro He. injection He as H1 H2. subst.
      pose proof (Hnoh (z, z) Hinab). cbn in *. lra. }
    assert (Hstep : hugs r (b, z) q).
    { apply (hug_step_corner r (a, b) (b, z) b a z q Htaut Hnd Hnoh Hnef
               Hinab Hinbz (or_introl eq_refl) (or_introl eq_refl)).
      - pose proof (Hnoh (a, b) Hinab). cbn in *. lra.
      - pose proof (Hnoh (b, z) Hinbz). cbn in *. lra.
      - exact Hhug. }
    exact (IH b z (l1 ++ [a])
             ltac:(rewrite Hr, <- app_assoc; reflexivity) Hstep g Hg).
Qed.

(* From a hug of any edge to a hug of every edge: chain to the closing
   edge, wrap the seam, chain from the opening edge. *)
Theorem hugs_everywhere : forall (r : Ring) (q : Point) (e g : Edge),
  ring_taut r -> ring_core_nodup r -> no_horizontal_edges r ->
  In e (ring_edges r) -> In g (ring_edges r) ->
  hugs r e q -> hugs r g q.
Proof.
  intros r q [ea eb] g Htaut Hnd Hnoh Hine Hing Hhug.
  pose proof Hnd as [p [ps [Hr Hndps]]].
  destruct ps as [| q0 ps'].
  { (* degenerate two-point ring: its only edge is horizontal *)
    exfalso.
    assert (Hin' : In (p, p) (ring_edges r)) by (rewrite Hr; cbn; auto).
    pose proof (Hnoh (p, p) Hin'). cbn in *. lra. }
  (* propagate to the closing edge *)
  apply ring_edges_in_split in Hine. destruct Hine as [l1 [l2 Hs]].
  assert (Hlastr : last r p = p).
  { rewrite Hr. cbn [last].
    destruct ((q0 :: ps') ++ [p]) eqn:Hl; [ destruct ps'; discriminate | ].
    rewrite <- Hl. apply last_snoc. }
  assert (HlastS : last (eb :: l2) p = p).
  { rewrite Hs in Hlastr.
    rewrite (last_app_nonempty l1 (ea :: eb :: l2) p
               ltac:(discriminate)) in Hlastr.
    cbn [last] in Hlastr. exact Hlastr. }
  destruct (exists_last (l := eb :: l2) ltac:(discriminate))
    as [l4 [w Hw]].
  (* w is the closing vertex p *)
  assert (Hwp : w = p).
  { rewrite Hw in HlastS. rewrite last_snoc in HlastS. exact HlastS. }
  subst w.
  (* the closing edge is (v, p) for the last entry v of ea :: l4 *)
  destruct (exists_last (l := ea :: l4) ltac:(discriminate))
    as [l5 [v Hv]].
  assert (HSdec : ea :: eb :: l2 = l5 ++ v :: p :: []).
  { change (ea :: eb :: l2) with (ea :: (eb :: l2)).
    rewrite Hw. rewrite app_comm_cons. rewrite Hv.
    rewrite <- app_assoc. reflexivity. }
  assert (HinLast : In (v, p) (ring_edges (ea :: eb :: l2)))
    by (apply ring_edges_in_split; exists l5, []; exact HSdec).
  assert (HhugLast : hugs r (v, p) q).
  { apply (hugs_chain r q Htaut Hnd Hnoh l2 ea eb l1 Hs Hhug (v, p)
             HinLast). }
  assert (HinLastR : In (v, p) (ring_edges r)).
  { apply ring_edges_in_split.
    exists (l1 ++ l5), [].
    rewrite Hs, HSdec, <- app_assoc. reflexivity. }
  (* wrap the seam to the opening edge *)
  assert (HinFirst : In (p, q0) (ring_edges r)).
  { apply ring_edges_in_split. exists [], (ps' ++ [p]).
    rewrite Hr. reflexivity. }
  assert (HnefW : (v, p) <> (p, q0)).
  { intro He. injection He as H1 H2.
    pose proof (Hnoh (v, p) HinLastR) as Hh. cbn in Hh.
    apply Hh. rewrite H1. reflexivity. }
  assert (HhugFirst : hugs r (p, q0) q).
  { apply (hug_step_corner r (v, p) (p, q0) p v q0 q Htaut Hnd Hnoh HnefW
             HinLastR HinFirst (or_introl eq_refl) (or_introl eq_refl)).
    - pose proof (Hnoh (v, p) HinLastR). cbn in *. lra.
    - pose proof (Hnoh (p, q0) HinFirst). cbn in *. lra.
    - exact HhugLast. }
  (* chain over the whole ring *)
  apply (hugs_chain r q Htaut Hnd Hnoh (ps' ++ [p]) p q0 []
           ltac:(rewrite Hr; reflexivity) HhugFirst g).
  rewrite Hr in Hing. exact Hing.
Qed.

(* ---------------------------------------------------------------------------
   §2  The entry: the east approach delivers the first wall's west hug.
   --------------------------------------------------------------------------- *)

Theorem hug_entry : forall (r : Ring) (p : Point) (e1 : Edge) (X1 : R),
  ring_taut r ->
  ring_complement r p ->
  ray_avoids_vertices p r ->
  min_cross_x p (ring_edges r) = Some X1 ->
  In e1 (ring_edges r) ->
  edge_crosses_ray_ho p e1 ->
  cross_x p e1 = X1 ->
  hugs_west r e1 p.
Proof.
  intros r p e1 X1 Htaut Hcompl Hrav Hmin Hin1 Hc HX.
  assert (Hnh : py (fst e1) <> py (snd e1))
    by (exact (crossing_edge_nonhorizontal r p e1 Hrav Hin1 Hc)).
  destruct e1 as [a b].
  pose proof (ho_cross_strict_of_guard r p a b Hrav Hin1 Hc) as Hstrict.
  cbn [fst snd] in Hnh.
  assert (Hpx : px p < X1)
    by (rewrite <- HX; exact (cross_x_east p a b Hc)).
  (* both p's height and the midpoint are span-interior *)
  set (m := mid (a, b)).
  assert (Hm : (py a < m < py b /\ py a < py p < py b) \/
               (py b < m < py a /\ py b < py p < py a))
    by (unfold m, mid; cbn [fst snd]; destruct Hstrict; [ left | right ];
        split; split; lra).
  set (ylo := Rmin (py p) m). set (yhi := Rmax (py p) m).
  assert (Hyl : ylo <= py p <= yhi /\ ylo <= m <= yhi).
  { unfold ylo, yhi.
    pose proof (Rmin_l (py p) m). pose proof (Rmin_r (py p) m).
    pose proof (Rmax_l (py p) m). pose proof (Rmax_r (py p) m).
    repeat split; lra. }
  assert (Hspan : (py a < ylo /\ yhi < py b) \/
                  (py b < ylo /\ yhi < py a)).
  { unfold ylo, yhi.
    destruct Hm as [[Hm1 Hm2] | [Hm1 Hm2]]; [ left | right ];
      split;
      [ apply Rmin_glb_lt; lra | apply Rmax_lub_lt; lra
      | apply Rmin_glb_lt; lra | apply Rmax_lub_lt; lra ]. }
  destruct (wall_corridor_clear r (a, b) ylo yhi Htaut Hin1
              ltac:(cbn [fst snd]; exact Hspan)
              ltac:(unfold ylo, yhi;
                    pose proof (Rmin_l (py p) m);
                    pose proof (Rmax_l (py p) m); lra))
    as [dW [HdW HfreeW]].
  destruct (wall_corridor_clear r (a, b) m m Htaut Hin1
              ltac:(cbn [fst snd];
                    destruct Hm as [[Hm1 _] | [Hm1 _]];
                    [ left | right ]; lra)
              ltac:(lra))
    as [dM [HdM HfreeM]].
  set (del := Rmin (Rmin dW dM) (X1 - px p) / 2).
  assert (Hdel : 0 < del /\ del < dW /\ del < dM /\ del < X1 - px p).
  { unfold del.
    pose proof (Rmin_l dW dM). pose proof (Rmin_r dW dM).
    pose proof (Rmin_l (Rmin dW dM) (X1 - px p)).
    pose proof (Rmin_r (Rmin dW dM) (X1 - px p)).
    assert (0 < Rmin (Rmin dW dM) (X1 - px p)).
    { apply Rmin_glb_lt; [ apply Rmin_glb_lt; lra | lra ]. }
    repeat split; lra. }
  destruct Hdel as [Hdel0 [HdelW [HdelM HdelX]]].
  split; [ exact Hcompl | ].
  exists del. split; [ exact Hdel0 | ]. split.
  - intros d' Hd'. apply (HfreeM d' ltac:(lra) m). lra.
  - (* p ~ east run-up ~ corridor at p's height ~ corridor at the mid *)
    assert (Heast : connected_in_complement_cont r p
              (mkPoint (X1 - del) (py p))).
    { apply (east_walk_connected r p X1 (X1 - del) Hcompl Hrav Hmin); lra. }
    assert (Htop : corridor (a, b) del (py p)
                     = mkPoint (X1 - del) (py p)).
    { rewrite (corridor_top_is_wall_point p (a, b) del
                 ltac:(cbn [fst snd]; exact Hnh)).
      rewrite HX. reflexivity. }
    assert (Hfree' : forall y, ylo <= y <= yhi ->
              ~ ring_image r (corridor (a, b) del y))
      by (intros y Hy; apply (HfreeW del ltac:(lra) y Hy)).
    assert (Hride : connected_in_complement_cont r
              (corridor (a, b) del (py p)) (corridor (a, b) del m)).
    { destruct (Rle_dec (py p) m) as [Hle | Hle].
      - apply connected_in_complement_cont_sym.
        apply (corridor_connected r (a, b) (py p) m del
                 ltac:(cbn [fst snd]; exact Hnh) Hle).
        intros y Hy. apply Hfree'. lra.
      - apply (corridor_connected r (a, b) m (py p) del
                 ltac:(cbn [fst snd]; exact Hnh) ltac:(lra)).
        intros y Hy. apply Hfree'. lra. }
    apply (connected_in_complement_cont_trans r p
             (corridor (a, b) del (py p))).
    + rewrite Htop. exact Heast.
    + exact Hride.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions hugs_chain.
Print Assumptions hugs_everywhere.
Print Assumptions hug_entry.
