(* ============================================================================
   NetTopologySuite.Proofs.KakeyaOverlay
   ----------------------------------------------------------------------------
   Besicovitch–Kakeya, Phase B (docs/besicovitch-kakeya-plan.md): DCEL / overlay
   integration of the finite polygonal Perron-tree stages built in PerronStage.v.

   Phase A delivered `perron_stage n : list Ring` and its structural / direction
   facts.  Phase B connects those triangles to the corpus's overlay-DCEL and
   OGC-validity machinery, UNCONDITIONALLY (no analytic-shell hypothesis):

     - DCEL face-walk representability.  Each triangle's edge list is a
       `closed_chain` (BufferAssembly), and `ring_of_chain` round-trips it back
       to the triangle (`perron_tri_closed_chain`, `perron_tri_chain_roundtrip`).
       So a stage triangle is exactly the kind of object the face-extraction
       machinery (`RingExtract.face_walk_core`) consumes.

     - `ring_simple` discharged.  Unlike the general buffer face (where
       `ring_simple` is the post-noding "analytic shell"), the Perron triangles
       are concrete and non-degenerate, so we prove `ring_simple` outright: the
       three edges pairwise share a vertex and, being non-collinear, never cross
       at an interior point (`perron_tri_ring_simple`).  The kernel is
       `sip_shared_no_cross`: two segments emanating from a common vertex with
       non-zero `cross` cannot intersect properly.

     - `valid_polygon` / `valid_geometry`.  Hence each triangle, packaged
       hole-free, is a `valid_polygon` (`perron_tri_valid_polygon`), and the whole
       stage, as a multi-polygon `Geometry`, is `valid_geometry`
       (`perron_geometry_valid`) — a legitimate operand for `Overlay.boolean_op`
       and the OverlayNG pipeline.

   No measure theory; finite and polygonal throughout.  Pure-R, three-axiom.
   No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List.
From NTS.Proofs Require Import Distance Orientation Overlay BufferAssembly
                               RingExtract PerronStage.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Proper-intersection symmetries.                                        *)
(*                                                                            *)
(* `segments_intersect_properly` is invariant under reversing either segment  *)
(* (reparametrise t |-> 1-t), which lets us normalise any shared-vertex pair  *)
(* to the canonical "both segments start at the shared vertex" form.          *)
(* -------------------------------------------------------------------------- *)

Lemma sip_rev1 : forall P0 P1 Q0 Q1,
  segments_intersect_properly P0 P1 Q0 Q1 ->
  segments_intersect_properly P1 P0 Q0 Q1.
Proof.
  intros P0 P1 Q0 Q1 [t [s [[Ht0 Ht1] [Hs [Hx Hy]]]]].
  exists (1 - t), s. repeat split; lra.
Qed.

Lemma sip_rev2 : forall P0 P1 Q0 Q1,
  segments_intersect_properly P0 P1 Q0 Q1 ->
  segments_intersect_properly P0 P1 Q1 Q0.
Proof.
  intros P0 P1 Q0 Q1 [t [s [Ht [[Hs0 Hs1] [Hx Hy]]]]].
  exists t, (1 - s). repeat split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The kernel: two segments from a common vertex do not cross properly.   *)
(*                                                                            *)
(* If [V,X] and [V,Y] met at an interior point, then t*(X-V) = s*(Y-V) for     *)
(* some interior t,s; taking the 2D cross with the shared rays forces          *)
(* t * cross V X Y = 0, and t > 0, so cross V X Y = 0 — collinearity.          *)
(* Contrapositive: non-collinear shared-vertex segments never cross properly.  *)
(* -------------------------------------------------------------------------- *)

Lemma sip_shared_no_cross : forall V X Y,
  cross V X Y <> 0 ->
  ~ segments_intersect_properly V X V Y.
Proof.
  intros V X Y Hcr [t [s [[Ht0 Ht1] [[Hs0 Hs1] [Hx Hy]]]]].
  apply Hcr.
  assert (Hkey : t * cross V X Y = 0).
  { unfold cross.
    replace (t * ((px X - px V) * (py Y - py V) - (px Y - px V) * (py X - py V)))
      with ((py Y - py V) * ((1 - t) * px V + t * px X - ((1 - s) * px V + s * px Y))
          - (px Y - px V) * ((1 - t) * py V + t * py X - ((1 - s) * py V + s * py Y)))
      by ring.
    rewrite Hx, Hy. ring. }
  apply Rmult_integral in Hkey. destruct Hkey as [Ht | Hc]; [ lra | exact Hc ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  All six vertex-permutation cross products of a non-degenerate triangle  *)
(*     are non-zero.                                                           *)
(* -------------------------------------------------------------------------- *)

Lemma cross_nonzero_perms : forall A B C,
  cross A B C <> 0 ->
  cross A B C <> 0 /\ cross B C A <> 0 /\ cross C A B <> 0 /\
  cross A C B <> 0 /\ cross C B A <> 0 /\ cross B A C <> 0.
Proof.
  intros A B C H.
  pose proof (cross_cyclic A B C) as Hc1.        (* A B C = B C A *)
  pose proof (cross_cyclic_2 A B C) as Hc2.       (* A B C = C A B *)
  pose proof (cross_antisymmetric A B C) as Ha.   (* A B C = - A C B *)
  pose proof (cross_swap_first_two A B C) as Hs.  (* A B C = - B A C *)
  pose proof (cross_swap_first_two C B A) as Hcba. (* C B A = - B C A *)
  repeat split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Each Perron-tree triangle is a simple ring.                            *)
(* -------------------------------------------------------------------------- *)

Theorem perron_tri_ring_simple : forall n k, ring_simple (perron_tri n k).
Proof.
  intros n k.
  pose proof (cross_nonzero_perms apex (base_pt (stage_count n) k)
                (base_pt (stage_count n) (S k)) (perron_tri_nondegenerate n k))
    as [HABC [HBCA [HCAB [HACB [HCBA HBAC]]]]].
  intros e1 e2 H1 H2 Hne.
  unfold perron_tri, tri_ring in H1, H2.
  cbn [ring_edges In] in H1, H2.
  destruct H1 as [H1 | [H1 | [H1 | []]]]; destruct H2 as [H2 | [H2 | [H2 | []]]];
    subst e1 e2; cbn [fst snd];
    try (exfalso; apply Hne; reflexivity);
    intro Hsip;
    first
      [ refine (sip_shared_no_cross _ _ _ _ Hsip); assumption
      | apply sip_rev1 in Hsip;
        refine (sip_shared_no_cross _ _ _ _ Hsip); assumption
      | apply sip_rev2 in Hsip;
        refine (sip_shared_no_cross _ _ _ _ Hsip); assumption
      | apply sip_rev1 in Hsip; apply sip_rev2 in Hsip;
        refine (sip_shared_no_cross _ _ _ _ Hsip); assumption ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  valid_polygon and valid_geometry.                                      *)
(* -------------------------------------------------------------------------- *)

(* A stage triangle, packaged as a hole-free polygon. *)
Definition perron_polygon (n k : nat) : Polygon :=
  mkPolygon (perron_tri n k) [].

Theorem perron_tri_valid_polygon : forall n k,
  valid_polygon (perron_polygon n k).
Proof.
  intros n k. unfold valid_polygon, perron_polygon.
  cbn [outer_ring hole_rings].
  split; [ apply perron_tri_closed | ].
  split; [ apply perron_tri_ring_simple | ].
  split; [ apply perron_tri_min_points | ].
  intros h Hin. destruct Hin.
Qed.

(* The whole stage as a multi-polygon Geometry. *)
Definition perron_geometry (n : nat) : Geometry :=
  map (fun r => mkPolygon r []) (perron_stage n).

Theorem perron_geometry_valid : forall n, valid_geometry (perron_geometry n).
Proof.
  intros n poly Hin. unfold perron_geometry in Hin.
  apply in_map_iff in Hin. destruct Hin as [r [Hr Hinr]]. subst poly.
  unfold perron_stage in Hinr. apply in_map_iff in Hinr.
  destruct Hinr as [k [Hk _]]. subst r.
  exact (perron_tri_valid_polygon n k).
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  DCEL face-walk representability.                                       *)
(*                                                                            *)
(* The triangle's edge list is a closed chain, and `ring_of_chain` recovers    *)
(* the triangle — so a stage triangle is exactly a face walk in the sense the  *)
(* extraction machinery (RingExtract) consumes, and `face_walk_core` applies.  *)
(* -------------------------------------------------------------------------- *)

Lemma perron_tri_closed_chain : forall n k,
  closed_chain (ring_edges (perron_tri n k)).
Proof.
  intros n k. unfold perron_tri, tri_ring. cbn [ring_edges].
  split.
  - cbn [chain_ok fst snd]. repeat split; (reflexivity || exact I).
  - intros d0 _. cbn [last hd fst snd]. reflexivity.
Qed.

Lemma perron_tri_chain_roundtrip : forall n k,
  ring_of_chain (ring_edges (perron_tri n k)) = perron_tri n k.
Proof.
  intros n k. unfold perron_tri, tri_ring.
  cbn [ring_edges ring_of_chain map fst app]. reflexivity.
Qed.

(* The combinatorial core (closure + min-vertex + edge fidelity) follows for
   each stage triangle by feeding its closed chain to RingExtract. *)
Corollary perron_tri_face_walk_core : forall n k,
  ring_closed (ring_of_chain (ring_edges (perron_tri n k))) /\
  ring_has_minimum_points (ring_of_chain (ring_edges (perron_tri n k))) /\
  ring_edges (ring_of_chain (ring_edges (perron_tri n k)))
    = ring_edges (perron_tri n k).
Proof.
  intros n k. apply face_walk_core.
  - apply perron_tri_closed_chain.
  - unfold perron_tri, tri_ring. cbn [ring_edges length]. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* Assumption audit.                                                          *)
(* -------------------------------------------------------------------------- *)

Print Assumptions perron_tri_ring_simple.
Print Assumptions perron_tri_valid_polygon.
Print Assumptions perron_geometry_valid.
Print Assumptions perron_tri_closed_chain.
