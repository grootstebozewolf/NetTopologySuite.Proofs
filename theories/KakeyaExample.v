(* ============================================================================
   NetTopologySuite.Proofs.KakeyaExample
   ----------------------------------------------------------------------------
   Besicovitch–Kakeya, Phase C (docs/besicovitch-kakeya-plan.md): a FROZEN
   regression anchor over a fixed Perron-tree stage.

   The plan calls for pinning `perron_stage 5` (or similar) as a Qed-closed
   example that stress-tests the machinery on near-collinear thin triangles,
   tiny apex angles, and overlapping (edge-sharing) triangles.  This file freezes
   the depth-5 stage (32 triangles) and records, as concrete Qed lemmas:

     - `kakeya_anchor_count`         : the stage is exactly 32 triangles;
     - `kakeya_anchor_valid_geometry`: it is an OGC `valid_geometry`
                                       (Phase-B `perron_geometry_valid` @ 5);
     - `kakeya_anchor_all_ring_simple`: every triangle is `ring_simple`;
     - `kakeya_anchor_area` / `_area_pos` : every sub-triangle is a THIN sliver of
                                       signed area exactly `1 / 32` — small, yet
                                       strictly positive (non-degenerate), the
                                       near-collinear stress;
     - `perron_consecutive_share_cevian` : consecutive triangles SHARE the apex
                                       cevian (opposite orientation) — the
                                       edge-to-edge OVERLAP structure;
     - `perron_area_decreasing`      : the sliver area `1/2^n` strictly DECREASES
                                       with depth — the thinning that motivates
                                       the Phase-D area -> 0 analysis (no measure
                                       theory used or claimed here).

   Pure-R; three-axiom.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List.
From NTS.Proofs Require Import Distance Orientation Overlay PerronStage KakeyaOverlay.
Import ListNotations.
Local Open Scope R_scope.

(* The frozen anchor: the depth-5 Perron-tree stage and its geometry. *)
Definition kakeya_anchor : list Ring := perron_stage 5.
Definition kakeya_anchor_geometry : Geometry := perron_geometry 5.

(* -------------------------------------------------------------------------- *)
(* §1  Combinatorial size and OGC validity.                                   *)
(* -------------------------------------------------------------------------- *)

Lemma kakeya_anchor_count : length kakeya_anchor = 32%nat.
Proof. unfold kakeya_anchor. rewrite perron_stage_length. reflexivity. Qed.

Theorem kakeya_anchor_valid_geometry : valid_geometry kakeya_anchor_geometry.
Proof. unfold kakeya_anchor_geometry. apply perron_geometry_valid. Qed.

Theorem kakeya_anchor_all_ring_simple :
  forall r, In r kakeya_anchor -> ring_simple r.
Proof.
  intros r Hr. unfold kakeya_anchor, perron_stage in Hr.
  apply in_map_iff in Hr. destruct Hr as [k [Hk _]]. subst r.
  apply perron_tri_ring_simple.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Thin slivers / near-collinearity: uniform tiny area, still positive.   *)
(* -------------------------------------------------------------------------- *)

(* Every sub-triangle of the depth-5 stage has signed area exactly 1/32. *)
Lemma kakeya_anchor_area : forall k,
  cross apex (base_pt (stage_count 5) k) (base_pt (stage_count 5) (S k))
  = 1 / INR (stage_count 5).
Proof. intros k. apply perron_tri_area. Qed.

(* That area is strictly positive: the triangle is genuinely non-degenerate
   despite being a thin (near-collinear) sliver. *)
Lemma kakeya_anchor_area_pos : forall k,
  0 < cross apex (base_pt (stage_count 5) k) (base_pt (stage_count 5) (S k)).
Proof.
  intros k. rewrite kakeya_anchor_area.
  apply Rdiv_lt_0_compat; [ lra | ].
  apply lt_0_INR. apply stage_count_pos.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Overlap: consecutive triangles share the apex cevian (opposite sense). *)
(* The third edge of triangle k, (B_{k+1}, apex), is the reverse of the first  *)
(* edge of triangle k+1, (apex, B_{k+1}) -- so the fan is edge-to-edge.        *)
(* -------------------------------------------------------------------------- *)

Lemma perron_consecutive_share_cevian : forall n k,
  In (base_pt (stage_count n) (S k), apex) (ring_edges (perron_tri n k)) /\
  In (apex, base_pt (stage_count n) (S k)) (ring_edges (perron_tri n (S k))).
Proof.
  intros n k. unfold perron_tri, tri_ring. cbn [ring_edges In]. split.
  - right; right; left. reflexivity.
  - left. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Thinning: the sliver area 1/2^n strictly decreases with depth.         *)
(* This is the finite, polygonal shadow of the Phase-D area -> 0 statement     *)
(* (which itself needs Lebesgue measure and is NOT attempted here).           *)
(* -------------------------------------------------------------------------- *)

Lemma perron_area_decreasing : forall n,
  cross apex (base_pt (stage_count (S n)) 0) (base_pt (stage_count (S n)) 1)
  < cross apex (base_pt (stage_count n) 0) (base_pt (stage_count n) 1).
Proof.
  intros n.
  rewrite (perron_tri_area (S n) 0), (perron_tri_area n 0).
  pose proof (stage_count_pos n) as Hn.
  pose proof (stage_count_pos (S n)) as HSn.
  assert (Hlt : (stage_count n < stage_count (S n))%nat).
  { unfold stage_count. rewrite Nat.pow_succ_r'. unfold stage_count in Hn. lia. }
  pose proof (lt_0_INR _ Hn) as Ha.
  pose proof (lt_0_INR _ HSn) as Hb.
  pose proof (lt_INR _ _ Hlt) as Hab.
  unfold Rdiv. rewrite !Rmult_1_l.
  apply Rinv_lt_contravar; [ nra | exact Hab ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit.                                                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions kakeya_anchor_valid_geometry.
Print Assumptions kakeya_anchor_all_ring_simple.
Print Assumptions kakeya_anchor_area_pos.
Print Assumptions perron_area_decreasing.
