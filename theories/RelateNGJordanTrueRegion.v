(* ============================================================================
   NetTopologySuite.Proofs.RelateNGJordanTrueRegion
   ----------------------------------------------------------------------------
   ADR-0007 heights letter (claimId 0007-relateng-jordan-true-region): the
   CLOSED Jordan true-region for a taut simple closed polygonal ring.

   THE RUNG.  For a ring r that is taut (JCTTautClearance.ring_taut),
   vertex-distinct (JCTRingCycle.ring_core_nodup), horizontal-edge-free
   (JCTHugStep.no_horizontal_edges) and has the OGC minimum of four points,
   construct one height h such that
     (i)   h avoids every vertex height       -- HalfOpenEscape.exists_real_avoiding;
     (ii)  h sits inside the level_gap / depth_gap vertex-free window around
           the first edge's mid-height, the same window the JCTPassageKit /
           JCTWalkStep parked heights use;
     (iii) two witnesses p_in, p_out lie on that height, off the ring, and
           ray_avoids_vertices holds at both
           -- StraddlePair.ray_avoids_vertices_of_generic_height through
              StraddleSides.straddle_side_core;
     (iv)  closed point_in_ring parity is transported along complement paths
           -- JCTSeparation.parity_constant_on_components (as
              odd_even_separated), so p_in and p_out are in different
              components.
   The bounded / unbounded labels come from the closed taut seam
   JCTEscapeDescentHolds.parity_seam_offring_taut: the odd witness is in a
   bounded component, the even one is not.

   What this is NOT.  Not a half-open remint: point_in_ring here is the
   CLOSED strict-straddle predicate of Overlay.v, and ray_avoids_vertices
   stays on it.  The guard is necessary: at a vertex-grazing height the closed
   test is unsafe (JCT_VertexGrazingCounterexample.v: the diamond's B = (0,0)
   grazes vertex (1,0) and reads EVEN while its component is odd).  This file
   never evaluates point_in_ring at a grazing height -- h is chosen off every
   vertex height first.  Not HalfOpenTrapped / HalfOpenEscape / point_in_ring_ho
   (HalfOpenEscape is imported only for exists_real_avoiding).  Not the JCT
   kit, Hobby, Shewchuk, NodingNG, first_cook_scope, Karney.  Not the
   unconditional Jordan theorem for every curve ring (RelateNGFace.v :
   RNG_JordanUncond stays a park).

   WITNESS topic: relate · claimId: 0007-relateng-jordan-true-region
   witness: 0007-relateng-jordan-true-region · board: ADR-0007
   3-axiom host lane (Stdlib Reals). No Admitted / Axiom / Parameter.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Arith Lia.
From NTS.Proofs Require Import JctSeamPack.
From NTS.Proofs Require Import RingExtract HalfOpenEscape StraddlePair StraddleSides EdgeCrossParity.
From NTS.Proofs Require Import JCTCorridor JCTCornerSector JCTTautClearance JCTRingCycle
  JCTHugStep JCTSeparation JCTEscapeDescentHolds.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The statement: a bounded odd component and an unbounded even one.      *)
(* -------------------------------------------------------------------------- *)

(* The inhabitant RelateNGFace's park RelateNGJordanTrueRegion denotes. *)
Definition jordan_true_region_taut : Prop :=
  forall r : Ring,
    ring_taut r ->
    ring_core_nodup r ->
    no_horizontal_edges r ->
    ring_has_minimum_points r ->
    exists (h : R) (p_in p_out : Point),
      (* (i) h avoids every vertex height *)
      (forall v, In v r -> h <> py v) /\
      (* (iii) both witnesses on that height, off the ring, guarded *)
      py p_in = h /\ py p_out = h /\
      ring_complement r p_in /\ ring_complement r p_out /\
      ray_avoids_vertices p_in r /\ ray_avoids_vertices p_out r /\
      (* the two components *)
      point_in_ring p_in r /\ in_bounded_component_cont r p_in /\
      ~ point_in_ring p_out r /\ ~ in_bounded_component_cont r p_out /\
      (* (iv) parity separates them through the complement *)
      ~ connected_in_complement_cont r p_in p_out.

(* -------------------------------------------------------------------------- *)
(* §2  Edges of a vertex-distinct ring are pairwise distinct.                  *)
(* -------------------------------------------------------------------------- *)

Lemma map_fst_ring_edges : forall l : list Point,
  map fst (ring_edges l) = removelast l.
Proof.
  induction l as [| a l' IH]; [ reflexivity | ].
  destruct l' as [| b l''].
  - reflexivity.
  - rewrite ring_edges_cons2. cbn [map fst].
    rewrite IH. reflexivity.
Qed.

Lemma ring_edges_nodup_of_core_nodup : forall r : Ring,
  ring_core_nodup r -> NoDup (ring_edges r).
Proof.
  intros r [p [ps [Hr Hnd]]].
  apply (NoDup_map_inv fst).
  rewrite map_fst_ring_edges, Hr.
  rewrite app_comm_cons, removelast_app by discriminate.
  cbn [removelast]. rewrite app_nil_r. exact Hnd.
Qed.

Lemma first_edge_split : forall r : Ring,
  ring_core_nodup r -> ring_has_minimum_points r ->
  exists (e0 : Edge) (suf : list Edge),
    ring_edges r = [] ++ e0 :: suf /\ ~ In e0 ([] ++ suf).
Proof.
  intros r Hnd Hmin.
  pose proof (ring_edges_nodup_of_core_nodup r Hnd) as HND.
  unfold ring_has_minimum_points in Hmin.
  destruct r as [| a [| b rest]]; cbn [length] in Hmin; try lia.
  rewrite ring_edges_cons2 in *.
  exists (a, b), (ring_edges (b :: rest)).
  split; [ reflexivity | ].
  cbn [app]. apply NoDup_cons_iff in HND. exact (proj1 HND).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The height: inside the first edge's y-span and inside the parked       *)
(*     level_gap / depth_gap window, off every vertex height.                  *)
(* -------------------------------------------------------------------------- *)

Lemma vertex_off_gap_window : forall (r : Ring) (c : R) (v : Point),
  In v r ->
  py v = c \/ py v <= c - depth_gap c r \/ c + level_gap c r <= py v.
Proof.
  intros r c v Hv.
  destruct (level_gap_spec c r v Hv) as [Hle | Hhi];
    [ | right; right; exact Hhi ].
  destruct (depth_gap_spec c r v Hv) as [Hge | Hlo];
    [ left; lra | right; left; exact Hlo ].
Qed.

Lemma exists_generic_height_in_window : forall (r : Ring) (ylo yhi : R),
  ylo < yhi ->
  let c := (ylo + yhi) / 2 in
  exists h : R,
    ylo < h < yhi /\
    c - depth_gap c r < h < c + level_gap c r /\
    (forall v, In v r -> h <> py v).
Proof.
  intros r ylo yhi Hlt c.
  pose proof (level_gap_pos c r) as Hlg.
  pose proof (depth_gap_pos c r) as Hdg.
  set (eps := Rmin ((yhi - ylo) / 2) (Rmin (level_gap c r) (depth_gap c r))).
  assert (Heps : 0 < eps).
  { unfold eps. apply Rmin_glb_lt; [ lra | apply Rmin_glb_lt; lra ]. }
  assert (He1 : eps <= (yhi - ylo) / 2) by apply Rmin_l.
  assert (He2 : eps <= level_gap c r)
    by (eapply Rle_trans; [ apply Rmin_r | apply Rmin_l ]).
  assert (He3 : eps <= depth_gap c r)
    by (eapply Rle_trans; [ apply Rmin_r | apply Rmin_r ]).
  destruct (exists_real_avoiding (map py r) c eps Heps) as [h [Hball Hnin]].
  apply Rabs_def2 in Hball. destruct Hball as [Hb1 Hb2].
  exists h.
  split; [ unfold c in *; lra | ].
  split; [ lra | ].
  intros v Hv Heq. apply Hnin. rewrite Heq. apply in_map. exact Hv.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The straddle pair at that height (StraddleSides core, not re-proved).   *)
(* -------------------------------------------------------------------------- *)

Lemma straddle_at_height : forall (r : Ring) (a0 b0 : Point) (suf : list Edge) (h : R),
  ring_taut r ->
  no_horizontal_edges r ->
  ring_edges r = [] ++ (a0, b0) :: suf ->
  ~ In (a0, b0) ([] ++ suf) ->
  (forall v, In v r -> h <> py v) ->
  Rmin (py a0) (py b0) < h < Rmax (py a0) (py b0) ->
  exists (ef : R) (p1 p2 : Point),
    0 < ef /\
    p1 = mkPoint (edge_x_at (a0, b0) h - ef) h /\
    p2 = mkPoint (edge_x_at (a0, b0) h + ef) h /\
    ray_avoids_vertices p1 r /\ ray_avoids_vertices p2 r /\
    ring_complement r p1 /\ ring_complement r p2 /\
    (point_in_ring p1 r <-> ~ point_in_ring p2 r).
Proof.
  intros r a0 b0 suf h Htaut Hnoh Hsplit Hnotin Hgen Hspan.
  assert (He0in : In (a0, b0) (ring_edges r))
    by (rewrite Hsplit; left; reflexivity).
  assert (Hnh0 : py a0 <> py b0)
    by (pose proof (Hnoh (a0, b0) He0in) as H; cbn [fst snd] in H; exact H).
  set (X := edge_x_at (a0, b0) h).
  set (t := (h - py a0) / (py b0 - py a0)).
  assert (Htd : t * (py b0 - py a0) = h - py a0) by (unfold t; field; lra).
  destruct (Rtotal_order (py a0) (py b0)) as [Hasc | [Heq | Hdesc]];
    [ | exfalso; exact (Hnh0 Heq) | ].
  - assert (Hin : py a0 < h < py b0).
    { rewrite Rmin_left, Rmax_right in Hspan by lra. exact Hspan. }
    assert (Ht : 0 < t < 1) by nra.
    destruct (straddle_side_core r [] suf (a0, b0) h Htaut Hnoh Hsplit Hnotin Hgen)
      as [ef [p1 [p2 [Hef [Hp1 [Hp2 [Hav1 [Hav2 [Hc1 [Hc2 [Hflip _]]]]]]]]]]].
    + exists t. split; [ exact Ht | ]. cbn [fst snd]. split.
      * unfold edge_x_at, t. field. lra.
      * nra.
    + intros eps Heps.
      exact (cross_ho_straddle_zero_asc a0 b0 h (edge_x_at (a0, b0) h) eps Hasc
               ltac:(lra) (edge_x_at_zero_asc a0 b0 h Hasc) Heps).
    + exists ef, p1, p2.
      exact (conj Hef (conj Hp1 (conj Hp2 (conj Hav1 (conj Hav2 (conj Hc1 (conj Hc2 Hflip))))))).
  - assert (Hin : py b0 < h < py a0).
    { rewrite Rmin_right, Rmax_left in Hspan by lra. exact Hspan. }
    assert (Ht : 0 < t < 1) by nra.
    destruct (straddle_side_core r [] suf (a0, b0) h Htaut Hnoh Hsplit Hnotin Hgen)
      as [ef [p1 [p2 [Hef [Hp1 [Hp2 [Hav1 [Hav2 [Hc1 [Hc2 [Hflip _]]]]]]]]]]].
    + exists t. split; [ exact Ht | ]. cbn [fst snd]. split.
      * unfold edge_x_at, t. field. lra.
      * nra.
    + intros eps Heps.
      exact (cross_ho_straddle_zero_desc a0 b0 h (edge_x_at (a0, b0) h) eps Hdesc
               ltac:(lra) (edge_x_at_zero_desc a0 b0 h Hdesc) Heps).
    + exists ef, p1, p2.
      exact (conj Hef (conj Hp1 (conj Hp2 (conj Hav1 (conj Hav2 (conj Hc1 (conj Hc2 Hflip))))))).
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Bounded odd / unbounded even, from the closed taut seam.                *)
(* -------------------------------------------------------------------------- *)

Lemma no_horizontal_edge_at_of_edges : forall (r : Ring) (p : Point),
  no_horizontal_edges r -> no_horizontal_edge_at p r.
Proof.
  intros r p Hnoh. unfold no_horizontal_edge_at.
  apply Forall_forall. intros e He. exact (Hnoh e He).
Qed.

Lemma taut_seam_at : forall (r : Ring) (p : Point),
  ring_taut r -> ring_core_nodup r -> no_horizontal_edges r ->
  ring_has_minimum_points r ->
  ring_complement r p -> ray_avoids_vertices p r ->
  (geometric_interior_cont p r <-> point_in_ring p r).
Proof.
  intros r p Htaut Hnd Hnoh Hmin Hcompl Hrav.
  apply (parity_seam_offring_taut r p Htaut Hnd Hnoh).
  - exact (ring_taut_implies_simple r Htaut).
  - exact (ring_core_nodup_closed r Hnd).
  - exact Hmin.
  - exact Hcompl.
  - exact (no_horizontal_edge_at_of_edges r p Hnoh).
  - exact Hrav.
Qed.

Lemma odd_is_bounded : forall (r : Ring) (p : Point),
  ring_taut r -> ring_core_nodup r -> no_horizontal_edges r ->
  ring_has_minimum_points r ->
  ring_complement r p -> ray_avoids_vertices p r ->
  point_in_ring p r -> in_bounded_component_cont r p.
Proof.
  intros r p Htaut Hnd Hnoh Hmin Hcompl Hrav Hpir.
  destruct (proj2 (taut_seam_at r p Htaut Hnd Hnoh Hmin Hcompl Hrav) Hpir) as [_ Hb].
  exact Hb.
Qed.

Lemma even_is_unbounded : forall (r : Ring) (p : Point),
  ring_taut r -> ring_core_nodup r -> no_horizontal_edges r ->
  ring_has_minimum_points r ->
  ring_complement r p -> ray_avoids_vertices p r ->
  ~ point_in_ring p r -> ~ in_bounded_component_cont r p.
Proof.
  intros r p Htaut Hnd Hnoh Hmin Hcompl Hrav Hnpir Hb.
  apply Hnpir.
  apply (proj1 (taut_seam_at r p Htaut Hnd Hnoh Hmin Hcompl Hrav)).
  split; [ exact Hcompl | exact Hb ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  The inhabitant.                                                        *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"0007-relateng-jordan-true-region","topic":"relate","lemma":"relateng_jordan_true_region_taut","title":"closed Jordan true-region for taut vertex-distinct horizontal-free polygonal rings: a height h off every vertex (exists_real_avoiding) inside the level_gap / depth_gap parked window, two off-ring guarded witnesses on it, the odd one in a bounded component and the even one in no bounded component, separated through the complement by parity_constant_on_components","file":"theories/RelateNGJordanTrueRegion.v","witness":"0007-relateng-jordan-true-region","board":"ADR-0007"} *)
Theorem relateng_jordan_true_region_taut : jordan_true_region_taut.
Proof.
  intros r Htaut Hnd Hnoh Hmin.
  destruct (first_edge_split r Hnd Hmin) as [[a0 b0] [suf [Hsplit Hnotin]]].
  assert (He0in : In (a0, b0) (ring_edges r)) by (rewrite Hsplit; left; reflexivity).
  assert (Hnh0 : py a0 <> py b0)
    by (pose proof (Hnoh (a0, b0) He0in) as H; cbn [fst snd] in H; exact H).
  set (ylo := Rmin (py a0) (py b0)).
  set (yhi := Rmax (py a0) (py b0)).
  assert (Hlt : ylo < yhi).
  { unfold ylo, yhi. destruct (Rle_or_lt (py a0) (py b0)).
    - rewrite Rmin_left, Rmax_right by lra. lra.
    - rewrite Rmin_right, Rmax_left by lra. lra. }
  destruct (exists_generic_height_in_window r ylo yhi Hlt) as [h [Hspan [_ Hgen]]].
  destruct (straddle_at_height r a0 b0 suf h Htaut Hnoh Hsplit Hnotin Hgen Hspan)
    as [ef [p1 [p2 [Hef [Hp1 [Hp2 [Hav1 [Hav2 [Hc1 [Hc2 Hflip]]]]]]]]]].
  assert (Hy1 : py p1 = h) by (rewrite Hp1; reflexivity).
  assert (Hy2 : py p2 = h) by (rewrite Hp2; reflexivity).
  pose proof (ring_core_nodup_closed r Hnd) as Hclosed.
  destruct (point_in_ring_dec p1 r) as [Hin1 | Hnin1].
  - (* p1 odd, p2 even *)
    assert (Hnin2 : ~ point_in_ring p2 r) by (apply Hflip; exact Hin1).
    exists h, p1, p2.
    split; [ exact Hgen | ]. split; [ exact Hy1 | ]. split; [ exact Hy2 | ].
    split; [ exact Hc1 | ]. split; [ exact Hc2 | ].
    split; [ exact Hav1 | ]. split; [ exact Hav2 | ].
    split; [ exact Hin1 | ].
    split; [ exact (odd_is_bounded r p1 Htaut Hnd Hnoh Hmin Hc1 Hav1 Hin1) | ].
    split; [ exact Hnin2 | ].
    split; [ exact (even_is_unbounded r p2 Htaut Hnd Hnoh Hmin Hc2 Hav2 Hnin2) | ].
    exact (odd_even_separated r p1 p2 Hclosed Hav1 Hav2 Hin1 Hnin2).
  - (* p1 even, p2 odd *)
    assert (Hin2 : point_in_ring p2 r).
    { destruct (point_in_ring_dec p2 r) as [H | H]; [ exact H | ].
      exfalso. apply Hnin1. apply Hflip. exact H. }
    exists h, p2, p1.
    split; [ exact Hgen | ]. split; [ exact Hy2 | ]. split; [ exact Hy1 | ].
    split; [ exact Hc2 | ]. split; [ exact Hc1 | ].
    split; [ exact Hav2 | ]. split; [ exact Hav1 | ].
    split; [ exact Hin2 | ].
    split; [ exact (odd_is_bounded r p2 Htaut Hnd Hnoh Hmin Hc2 Hav2 Hin2) | ].
    split; [ exact Hnin1 | ].
    split; [ exact (even_is_unbounded r p1 Htaut Hnd Hnoh Hmin Hc1 Hav1 Hnin1) | ].
    exact (odd_even_separated r p2 p1 Hclosed Hav2 Hav1 Hin2 Hnin1).
Qed.

(* The window clause (ii), exposed on its own: the constructed height sits in
   the parked level_gap / depth_gap window around the first edge's mid-height,
   and no vertex height lies strictly inside that window except the centre. *)
Lemma constructed_height_in_parked_window : forall (r : Ring) (ylo yhi : R),
  ylo < yhi ->
  exists h : R,
    ylo < h < yhi /\
    ((ylo + yhi) / 2 - depth_gap ((ylo + yhi) / 2) r < h <
       (ylo + yhi) / 2 + level_gap ((ylo + yhi) / 2) r) /\
    (forall v, In v r -> h <> py v) /\
    (forall v, In v r ->
       py v = (ylo + yhi) / 2 \/
       py v <= (ylo + yhi) / 2 - depth_gap ((ylo + yhi) / 2) r \/
       (ylo + yhi) / 2 + level_gap ((ylo + yhi) / 2) r <= py v).
Proof.
  intros r ylo yhi Hlt.
  destruct (exists_generic_height_in_window r ylo yhi Hlt) as [h [H1 [H2 H3]]].
  exists h. split; [ exact H1 | ]. split; [ exact H2 | ]. split; [ exact H3 | ].
  intros v Hv. exact (vertex_off_gap_window r ((ylo + yhi) / 2) v Hv).
Qed.

Print Assumptions ring_edges_nodup_of_core_nodup.
Print Assumptions exists_generic_height_in_window.
Print Assumptions straddle_at_height.
Print Assumptions relateng_jordan_true_region_taut.
Print Assumptions constructed_height_in_parked_window.
