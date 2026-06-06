(* ============================================================================
   NetTopologySuite.Proofs.KakeyaSlide
   ----------------------------------------------------------------------------
   Besicovitch–Kakeya: the Perron-tree area-REDUCTION step, formalised finitely
   (no measure theory).  A follow-on to Phases A–C (docs/besicovitch-kakeya-plan.md).

   The actual Perron construction does not stop at the elementary fan (Phase A):
   it SLIDES the sub-triangles along the base line so they overlap, shrinking the
   total covered area while keeping a unit segment in every one of the `2^n`
   directions.  The measure-theoretic "area -> 0" is Phase D (deferred), but the
   two finite, polygonal facts that DRIVE it are provable now:

     (1) Direction coverage is INVARIANT under arbitrary per-piece sliding.
         Translating a sub-triangle leaves its apex-cevian direction unchanged,
         so distinct slid triangles still point in distinct (non-parallel)
         directions — `perron_slid_directions_distinct`.  This is the whole point
         of the Perron move: you may slide freely without losing any direction.

     (2) Each slid piece KEEPS its area (`perron_slid_area` = `1/2^n`), because
         signed area is translation-invariant.  So total area is only reduced by
         OVERLAP between pieces — and sliding genuinely creates overlap:
         `slid_pieces_overlap` exhibits a point interior to two slid stage-1
         triangles (the depth-1 pieces, with the right piece slid left by 1/2).
         The union area is therefore strictly below the sum of the piece areas —
         the reduction mechanism — while (1) keeps both directions present.

   We do NOT compute the union area (that needs inclusion-exclusion / Lebesgue
   measure = Phase D); we prove the invariants and exhibit the overlap.

   Pure-R; three-axiom.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List.
From NTS.Proofs Require Import Distance Orientation Overlay Vec PerronStage.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Segment direction, and its invariance under translation.              *)
(* -------------------------------------------------------------------------- *)

Definition seg_dir (a b : Point) : Vec := mkVec (px b - px a) (py b - py a).

Lemma seg_dir_translate : forall a b dx dy,
  seg_dir (translate a dx dy) (translate b dx dy) = seg_dir a b.
Proof.
  intros a b dx dy. unfold seg_dir, translate. cbn [px py].
  apply Vec_eq; cbn [vx vy]; ring.
Qed.

(* The 2D cross of two apex-rays is exactly the orientation `cross`. *)
Lemma vcross_seg_dir : forall a b c,
  vcross (seg_dir a b) (seg_dir a c) = cross a b c.
Proof.
  intros a b c. unfold vcross, seg_dir, cross. cbn [vx vy px py]. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Direction coverage survives arbitrary per-piece sliding.              *)
(*                                                                            *)
(* Slide triangle k horizontally by dk and triangle j by dj (independently).  *)
(* Their cevian directions are unchanged, so for j <> k they stay non-parallel.*)
(* -------------------------------------------------------------------------- *)

Theorem perron_slid_directions_distinct : forall n j k dj dk,
  j <> k ->
  vcross (seg_dir (translate apex dk 0)
                  (translate (base_pt (stage_count n) k) dk 0))
         (seg_dir (translate apex dj 0)
                  (translate (base_pt (stage_count n) j) dj 0)) <> 0.
Proof.
  intros n j k dj dk Hjk.
  rewrite !seg_dir_translate, vcross_seg_dir.
  apply perron_stage_directions_distinct. exact Hjk.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Each slid sub-triangle keeps its signed area 1/2^n.                    *)
(* -------------------------------------------------------------------------- *)

Theorem perron_slid_area : forall n k d,
  cross (translate apex d 0)
        (translate (base_pt (stage_count n) k) d 0)
        (translate (base_pt (stage_count n) (S k)) d 0)
  = 1 / INR (stage_count n).
Proof.
  intros n k d. rewrite cross_translation_invariant. apply perron_tri_area.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Sliding creates overlap: the area-reduction mechanism.                 *)
(*                                                                            *)
(* The depth-1 stage is two triangles partitioning the master triangle:        *)
(*   T0 = (apex,(0,0),(1/2,0)),  T1 = (apex,(1/2,0),(1,0)),  apex = (1/2,1).    *)
(* Slide T1 left by 1/2 (the Perron move) to                                   *)
(*   slid_T1 = ((0,1),(0,0),(1/2,0)).                                          *)
(* T0 and slid_T1 now OVERLAP — (1/4,1/4) is interior to both — so the union   *)
(* area is strictly below area(T0)+area(slid_T1), while both keep their        *)
(* directions (§2,§3).  (slid_T0 below is exactly the un-slid first piece.)     *)
(* -------------------------------------------------------------------------- *)

Definition slid_T0 : Ring :=
  [ mkPoint (1/2) 1 ; mkPoint 0 0 ; mkPoint (1/2) 0 ; mkPoint (1/2) 1 ].
Definition slid_T1 : Ring :=
  [ mkPoint 0 1 ; mkPoint 0 0 ; mkPoint (1/2) 0 ; mkPoint 0 1 ].

Ltac edge_nc :=
  unfold edge_crosses_ray; cbn [px py];
  intros [[[Ha Hb] Hx] | [[Ha Hb] Hx]]; lra.

Lemma slid_T0_contains : point_in_ring (mkPoint (1/4) (1/4)) slid_T0.
Proof.
  unfold point_in_ring, slid_T0. cbn [ring_edges].
  apply rpo_skip; [ edge_nc | ].                 (* (1/2,1)-(0,0): intercept 1/8 < 1/4 *)
  apply rpo_skip; [ edge_nc | ].                 (* (0,0)-(1/2,0): horizontal *)
  apply rpo_cross.                               (* (1/2,0)-(1/2,1): x=1/2 > 1/4: CROSS *)
  { unfold edge_crosses_ray; cbn [px py]. left. split; lra. }
  apply rpe_nil.
Qed.

Lemma slid_T1_contains : point_in_ring (mkPoint (1/4) (1/4)) slid_T1.
Proof.
  unfold point_in_ring, slid_T1. cbn [ring_edges].
  apply rpo_skip; [ edge_nc | ].                 (* (0,1)-(0,0): x=0 < 1/4 *)
  apply rpo_skip; [ edge_nc | ].                 (* (0,0)-(1/2,0): horizontal *)
  apply rpo_cross.                               (* (1/2,0)-(0,1): intercept 3/8 > 1/4: CROSS *)
  { unfold edge_crosses_ray; cbn [px py]. left. split; lra. }
  apply rpe_nil.
Qed.

Theorem slid_pieces_overlap :
  exists p, point_in_ring p slid_T0 /\ point_in_ring p slid_T1.
Proof.
  exists (mkPoint (1/4) (1/4)).
  split; [ apply slid_T0_contains | apply slid_T1_contains ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit.                                                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions perron_slid_directions_distinct.
Print Assumptions perron_slid_area.
Print Assumptions slid_pieces_overlap.
