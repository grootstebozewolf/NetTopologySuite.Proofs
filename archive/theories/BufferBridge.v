(* ============================================================================
   NetTopologySuite.Proofs.BufferBridge
   ----------------------------------------------------------------------------
   The semantic `H_bridge` of `BufferCorrectness.buffer_correct_conditional`:
   that the extracted point-set equals the buffer spec (the d-neighbourhood).

   This is the deepest, load-bearing semantic gap (the buffer analogue of
   OverlayNG's `H_bridge`).  In full generality it is thesis-scale, and in
   fact `point_set (extract op g) = buffer_spec g d` holds *exactly* only for
   the idealised ROUND buffer with exact arcs:

     - miter joins OVERSHOOT the d-neighbourhood (the apex is at distance
       d / cos(theta/2) > d -- see BufferMiter), so a mitered buffer is not
       the exact d-neighbourhood;
     - round joins/caps are CHORD-APPROXIMATED, so the polygon approximates
       the disk only up to the sagitta tolerance (cf. Phase 4's
       `arc_overlay_correct_chord_approx`, whose H_A/H_B bridges are the same
       shape of residual).

   So we do NOT manufacture a proof of the analytic core.  Instead this file:

   (1) proves the reusable `buffer_spec` ALGEBRA (empty / append / geometry-
       monotone) -- Qed, the set-theoretic skeleton of the d-dilation;

   (2) DECOMPOSES `H_bridge` into its two geometric directions -- soundness
       (result is within d of the input) and completeness (the d-neighbourhood
       is covered) -- and shows the hole-free buffer headline reduces to
       exactly those two (`buffer_correct_hole_free_split`).  The two
       directions are the precise analytic residual, carried as named
       hypotheses, NOT admitted.

   Pure-R; no atan / Flocq.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.8)
   ========================================================================== *)

From Stdlib Require Import Reals List.
From NTS.Proofs Require Import Distance Overlay OverlayGraph
                               BufferCorrectness RingSimple ExtractBufferRings.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The buffer_spec algebra (the d-dilation as a set operation).           *)
(* -------------------------------------------------------------------------- *)

(* The buffer of the empty geometry is empty. *)
Lemma buffer_spec_empty : forall d p, ~ buffer_spec [] d p.
Proof. intros d p [q [[poly [Hin _]] _]]. exact Hin. Qed.

(* The d-dilation distributes over the union (append) of geometries. *)
Lemma buffer_spec_app : forall g1 g2 d p,
  buffer_spec (g1 ++ g2) d p <-> buffer_spec g1 d p \/ buffer_spec g2 d p.
Proof.
  intros g1 g2 d p. unfold buffer_spec, point_set. split.
  - intros [q [[poly [Hin Hpip]] Hd]].
    apply in_app_iff in Hin. destruct Hin as [H1 | H2].
    + left.  exists q. split; [ exists poly; split; assumption | exact Hd ].
    + right. exists q. split; [ exists poly; split; assumption | exact Hd ].
  - intros [ [q [[poly [Hin Hpip]] Hd]] | [q [[poly [Hin Hpip]] Hd]] ].
    + exists q. split; [ exists poly; split;
        [ apply in_app_iff; left; exact Hin | exact Hpip ] | exact Hd ].
    + exists q. split; [ exists poly; split;
        [ apply in_app_iff; right; exact Hin | exact Hpip ] | exact Hd ].
Qed.

(* The d-dilation is monotone in the input point-set. *)
Lemma buffer_spec_monotone_geom : forall g1 g2 d p,
  (forall q, point_set g1 q -> point_set g2 q) ->
  buffer_spec g1 d p -> buffer_spec g2 d p.
Proof.
  intros g1 g2 d p Hsub [q [Hq Hd]].
  exists q. split; [ apply Hsub; exact Hq | exact Hd ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Decomposing H_bridge into soundness + completeness.                    *)
(* -------------------------------------------------------------------------- *)

(* The forward (SOUNDNESS) direction: a point of the extracted result is
   within d of the input.  This is the offset-soundness content. *)
Definition buffer_extract_sound
    (extract_buffer : TopologyGraph -> Geometry)
    (g : Geometry) (d : R) (p : Point) : Prop :=
  forall G : TopologyGraph,
    valid_topology_graph G -> valid_geometry (extract_buffer G) ->
    point_set (extract_buffer G) p -> buffer_spec g d p.

(* The backward (COMPLETENESS) direction: every point within d of the input
   is in the extracted result.  This is the coverage content. *)
Definition buffer_extract_complete
    (extract_buffer : TopologyGraph -> Geometry)
    (g : Geometry) (d : R) (p : Point) : Prop :=
  forall G : TopologyGraph,
    valid_topology_graph G -> valid_geometry (extract_buffer G) ->
    buffer_spec g d p -> point_set (extract_buffer G) p.

(* The two directions are exactly H_bridge. *)
Lemma H_bridge_of_sound_complete :
  forall (extract_buffer : TopologyGraph -> Geometry)
         (g : Geometry) (d : R) (p : Point),
    buffer_extract_sound extract_buffer g d p ->
    buffer_extract_complete extract_buffer g d p ->
    forall G : TopologyGraph,
      valid_topology_graph G -> valid_geometry (extract_buffer G) ->
      (point_set (extract_buffer G) p <-> buffer_spec g d p).
Proof.
  intros extract_buffer g d p Hsound Hcomplete G HG HV.
  split.
  - intro Hps. apply (Hsound G HG HV Hps).
  - intro Hbs. apply (Hcomplete G HG HV Hbs).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Capstone: the hole-free buffer headline reduces to the two directions. *)
(*     H_valid is discharged (ExtractBufferRings); H_bridge is split into     *)
(*     soundness + completeness -- the precise remaining analytic residual.   *)
(* -------------------------------------------------------------------------- *)

Theorem buffer_correct_hole_free_split :
  forall (node : list (Point * Point) -> list (Point * Point))
         (extract_buffer : TopologyGraph -> Geometry)
         (S : list Edge) (g : Geometry) (d : R) (p : Point),
    valid_geometry g ->
    0 <= d ->
    pairwise_no_proper_cross S ->
    chain_extractor_spec extract_buffer S ->
    buffer_extract_sound extract_buffer g d p ->
    buffer_extract_complete extract_buffer g d p ->
    point_set (extract_buffer (build_graph (node (offset_curve g d)))) p
      <-> buffer_spec g d p.
Proof.
  intros node extract_buffer S g d p Hg Hd Hpw Hspec Hsound Hcomplete.
  apply (buffer_correct_hole_free node extract_buffer S g d p
           Hg Hd Hpw Hspec).
  apply H_bridge_of_sound_complete; assumption.
Qed.
