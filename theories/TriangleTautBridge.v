(* ============================================================================
   NetTopologySuite.Proofs.TriangleTautBridge
   ----------------------------------------------------------------------------
   RING-CLASS BRIDGE, concrete instantiation: the generic-height CCW triangle.

   The taut polygonal Jordan seam `parity_seam_offring_taut`
   (JCTEscapeDescentHolds.v) discharges the corrected off-ring H1 biconditional
   `geometric_interior_cont <-> point_in_ring` for any ring satisfying the three
   ring-class predicates `ring_taut`, `ring_core_nodup`, `no_horizontal_edges`.
   No concrete ring had yet been shown to satisfy all three, so the taut seam had
   no end-to-end instantiation.  This file supplies the first one: a CCW triangle
   whose three vertex heights are pairwise distinct.

   - `tri_core_nodup`      : ring_core_nodup  (from CCW: 0 < gdbl forces the three
                              vertices pairwise distinct).
   - `tri_no_horizontal_edges` : no_horizontal_edges (from the three height
                              inequalities ay<>by_, by_<>cy, cy<>ay).
   - `tri_ring_taut`       : ring_taut (from CCW; the three edges are pairwise
                              adjacent, so a coincidence forces the shared vertex
                              -- non-collinearity from 0 < gdbl rules out any
                              interior meeting; the per-pair certificate is the
                              ideal identity (1-t)*gdbl = 0 or t*gdbl = 0).
   - `tri_parity_seam`     : the capstone -- `parity_characterises_interior_cont_offring`
                              for the triangle, by feeding the three predicates to
                              `parity_seam_offring_taut`.

   HONEST OBSTRUCTION (why this is a concrete instance, not a general overlay
   bridge): overlay/extracted rings are only known `ring_simple` (via
   `pairwise_no_proper_cross`), which forbids PROPER crossings but NOT T-junctions
   / a vertex on another edge's interior.  `ring_taut` is strictly stronger
   (`ring_taut_implies_simple`; the `bowtie` in RingSimple.v is simple but not
   taut).  A general overlay taut bridge therefore needs a STRONGER noding
   predicate than the current extraction provides.  This file does not claim
   otherwise; it validates the taut-seam path on a concrete ring and banks the
   per-predicate lemmas for reuse.

   Pure-R; classical-reals trio only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List Nsatz.
From NTS.Proofs Require Import Distance Overlay.
From NTS.Proofs Require Import GeneralTriangleSeparation.
From NTS.Proofs Require Import JordanCurveSeam PointInRingCorrect PointInRingTangents.
From NTS.Proofs Require Import JCTTautClearance JCTRingCycle JCTHugStep.
From NTS.Proofs Require Import JCT_OnEdgeCounterexample JCTEscapeDescentHolds.
Import ListNotations.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Vertex distinctness from CCW.                                          *)
(* -------------------------------------------------------------------------- *)

(* A CCW triangle has pairwise distinct vertices: equal coordinates would make
   the signed-area determinant vanish, contradicting 0 < gdbl. *)
Lemma tri_vertices_distinct : forall ax ay bx by_ cx cy,
  0 < gdbl ax ay bx by_ cx cy ->
  mkPoint ax ay <> mkPoint bx by_ /\
  mkPoint bx by_ <> mkPoint cx cy /\
  mkPoint cx cy <> mkPoint ax ay.
Proof.
  intros ax ay bx by_ cx cy Hccw.
  unfold gdbl in Hccw.
  repeat split; intro Heq; injection Heq as Hx Hy; subst; nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  ring_core_nodup for the triangle.                                      *)
(* -------------------------------------------------------------------------- *)

Lemma tri_core_nodup : forall ax ay bx by_ cx cy,
  0 < gdbl ax ay bx by_ cx cy ->
  ring_core_nodup (gtri_ring ax ay bx by_ cx cy).
Proof.
  intros ax ay bx by_ cx cy Hccw.
  destruct (tri_vertices_distinct ax ay bx by_ cx cy Hccw) as [Hab [Hbc Hca]].
  unfold ring_core_nodup, gtri_ring.
  exists (mkPoint ax ay), [mkPoint bx by_; mkPoint cx cy].
  split.
  - reflexivity.
  - constructor.
    + (* ~ In A [B; C] *)
      intro Hin. simpl in Hin. destruct Hin as [H | [H | []]];
        [ apply Hab | apply Hca ]; congruence.
    + constructor.
      * (* ~ In B [C] *)
        intro Hin. simpl in Hin. destruct Hin as [H | []]. apply Hbc; congruence.
      * constructor.
        -- intro Hin; exact Hin.
        -- constructor.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  no_horizontal_edges for the triangle (from distinct vertex heights).   *)
(* -------------------------------------------------------------------------- *)

Lemma tri_no_horizontal_edges : forall ax ay bx by_ cx cy,
  ay <> by_ -> by_ <> cy -> cy <> ay ->
  no_horizontal_edges (gtri_ring ax ay bx by_ cx cy).
Proof.
  intros ax ay bx by_ cx cy Hab Hbc Hca g Hg.
  rewrite ring_edges_gtri in Hg. simpl in Hg.
  destruct Hg as [H | [H | [H | []]]]; subst g; cbn [fst snd px py].
  - exact Hab.
  - exact Hbc.
  - exact Hca.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  ring_taut for the triangle.                                            *)
(*                                                                            *)
(* The three edges are pairwise adjacent.  For two distinct edges that share a *)
(* vertex, a parametric coincidence forces that shared vertex (the lines are   *)
(* non-collinear since 0 < gdbl), pinning t at the endpoint where the shared   *)
(* vertex sits on e.  The per-pair certificate is the ideal identity           *)
(* (1-t)*gdbl = 0 (shared vertex is e's second point) or t*gdbl = 0 (shared    *)
(* vertex is e's first point); `nsatz` discharges whichever holds, and the     *)
(* `first [...]` tries both.  The diagonal e=f case is the right disjunct.     *)
(* -------------------------------------------------------------------------- *)

Lemma tri_ring_taut : forall ax ay bx by_ cx cy,
  0 < gdbl ax ay bx by_ cx cy ->
  ring_taut (gtri_ring ax ay bx by_ cx cy).
Proof.
  intros ax ay bx by_ cx cy Hccw e f He Hf t s Ht Hs Hx Hy.
  rewrite ring_edges_gtri in He, Hf. simpl in He, Hf.
  assert (Hg : gdbl ax ay bx by_ cx cy <> 0) by lra.
  destruct He as [He | [He | [He | []]]];
  destruct Hf as [Hf | [Hf | [Hf | []]]];
  subst e f; cbn [fst snd px py] in Hx, Hy |- *;
    try (right; split; reflexivity);
    left;
    first
      [ assert (Hz : (1 - t) * gdbl ax ay bx by_ cx cy = 0)
          by (unfold gdbl in *; nsatz);
        destruct (Rmult_integral _ _ Hz) as [H1t | Hgd];
        [ right; lra | exfalso; apply Hg; exact Hgd ]
      | assert (Hz : t * gdbl ax ay bx by_ cx cy = 0)
          by (unfold gdbl in *; nsatz);
        destruct (Rmult_integral _ _ Hz) as [Ht0 | Hgd];
        [ left; lra | exfalso; apply Hg; exact Hgd ] ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Capstone: the first end-to-end taut-seam instantiation.                *)
(* -------------------------------------------------------------------------- *)

(* For a generic-height CCW triangle, the corrected off-ring H1 biconditional
   holds: at every off-ring, ray-generic point with no horizontal edge at its
   height, parity membership coincides with continuous geometric interiority.
   This is `parity_seam_offring_taut` discharged via the three predicates
   above -- the first concrete ring for which the taut Jordan seam is realized. *)
Lemma tri_parity_seam : forall ax ay bx by_ cx cy p,
  0 < gdbl ax ay bx by_ cx cy ->
  ay <> by_ -> by_ <> cy -> cy <> ay ->
  parity_characterises_interior_cont_offring p (gtri_ring ax ay bx by_ cx cy).
Proof.
  intros ax ay bx by_ cx cy p Hccw Hab Hbc Hca.
  apply parity_seam_offring_taut.
  - apply tri_ring_taut; exact Hccw.
  - apply tri_core_nodup; exact Hccw.
  - apply tri_no_horizontal_edges; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Genericity: the ray guard is GENERIC, and NECESSARY (not removable).    *)
(*                                                                            *)
(* The natural "next rung" would be to drop `ray_avoids_vertices` from         *)
(* `tri_parity_seam` (and from the triangle ii-cell consumers in RelateNG.v).  *)
(* That is NOT possible for the closed strict-straddle `point_in_ring` that    *)
(* `point_set` is built on: the diamond in JCT_VertexGrazingCounterexample.v   *)
(* exhibits an off-ring point whose rightward ray GRAZES a vertex, so          *)
(* `edge_crosses_ray`'s strict y-straddle miscounts the crossing and flips the *)
(* parity -- a genuine failure of the unguarded test.  Hence the guard is      *)
(* NECESSARY; "genericity removal" can only RELOCATE it (e.g. to a half-open   *)
(* convention), not eliminate it for this convention.                         *)
(*                                                                            *)
(* What IS true and useful is that the guard is GENERIC: for a triangle it can *)
(* fail only at the three vertex heights, so it holds for every point whose    *)
(* y-coordinate avoids {ay, by_, cy}.  `tri_parity_seam` thus characterises    *)
(* interiority at every off-ring point except those on three horizontal lines  *)
(* -- the standard general-position coverage.                                  *)
(* -------------------------------------------------------------------------- *)

Lemma tri_ray_generic_off_vertex_heights : forall ax ay bx by_ cx cy p,
  py p <> ay -> py p <> by_ -> py p <> cy ->
  ray_avoids_vertices p (gtri_ring ax ay bx by_ cx cy).
Proof.
  intros ax ay bx by_ cx cy p Ha Hb Hc v Hin [Hpy _].
  unfold gtri_ring in Hin. simpl in Hin.
  destruct Hin as [Hv | [Hv | [Hv | [Hv | []]]]]; subst v; cbn [px py] in Hpy.
  - apply Ha; symmetry; exact Hpy.
  - apply Hb; symmetry; exact Hpy.
  - apply Hc; symmetry; exact Hpy.
  - apply Ha; symmetry; exact Hpy.
Qed.

(* Corollary: at any off-ring point off the three vertex heights, the taut
   Jordan biconditional holds for the triangle -- the guard discharged from a
   pure height condition (general position). *)
Corollary tri_parity_seam_generic : forall ax ay bx by_ cx cy p,
  0 < gdbl ax ay bx by_ cx cy ->
  ay <> by_ -> by_ <> cy -> cy <> ay ->
  ring_complement (gtri_ring ax ay bx by_ cx cy) p ->
  no_horizontal_edge_at p (gtri_ring ax ay bx by_ cx cy) ->
  py p <> ay -> py p <> by_ -> py p <> cy ->
  (geometric_interior_cont p (gtri_ring ax ay bx by_ cx cy)
     <-> point_in_ring p (gtri_ring ax ay bx by_ cx cy)).
Proof.
  intros ax ay bx by_ cx cy p Hccw Hab Hbc Hca Hcompl Hnoh Hpa Hpb Hpc.
  apply (tri_parity_seam ax ay bx by_ cx cy p Hccw Hab Hbc Hca).
  - apply ring_taut_implies_simple, tri_ring_taut; exact Hccw.
  - apply ring_core_nodup_closed, tri_core_nodup; exact Hccw.
  - unfold ring_has_minimum_points, gtri_ring; simpl; lia.
  - exact Hcompl.
  - exact Hnoh.
  - apply tri_ray_generic_off_vertex_heights; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §7  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions tri_core_nodup.
Print Assumptions tri_no_horizontal_edges.
Print Assumptions tri_ring_taut.
Print Assumptions tri_parity_seam.
Print Assumptions tri_ray_generic_off_vertex_heights.
Print Assumptions tri_parity_seam_generic.
