(* ============================================================================
   NetTopologySuite.Proofs.Flocq.TopologicalCorrectness_b64
   ----------------------------------------------------------------------------
   Phase 2 milestone 4 (Slice 13): the topological correctness of snap-rounding,
   at the level the Slice 10-12 infrastructure supports.

   ----------------------------------------------------------------------------
   What this file proves, and what it deliberately does NOT.

   The audit doc (docs/audit-phase2-snap-rounding.md, section 2.4) frames the
   full milestone-4 theorem as

       Theorem snap_rounding_topologically_consistent :
         forall (S : list Segment), well_formed S ->
           let S' := snap_round S in
           (forall s1 s2 in S, share_point s1 s2 ->
              exists v in vertices(S'), v in s1' /\ v in s2') /\
           no_spurious_intersections S'.

   and estimates it at ~6-10 weeks -- "the major thesis-shaped piece", resting
   on Hobby 1999's convex-hull argument.  That statement needs machinery that
   does NOT exist in the corpus: a `Segment`-list arrangement type with
   `well_formed`, a `share_point` relation, a `vertices` extraction, a
   `no_spurious_intersections` predicate, and a formalisation of Hobby's hull
   argument (or an induction on the algorithm steps).  Building those is the
   Phase 2.5 engagement the audit doc sized; it is out of scope for one slice.

   Two narrower shapes were considered for this session:

     Shape A (exact intersect-sign preservation):
         b64_intersect_sign_filtered P0 P1 Q0 Q1 = IntersectPoint ->
         b64_intersect_sign_filtered (snap P0) (snap P1) (snap Q0) (snap Q1)
           = IntersectPoint.
       This is FALSE in general.  Snapping perturbs coordinates, which can
       flip the four orientation signs that `b64_intersect_sign_filtered`
       dispatches on, turning `IntersectPoint` into `IntersectNone` or
       `IntersectCollinear`.  That perturbation IS the topology change that
       Hobby's theorem exists to bound -- it is not a theorem to prove but the
       phenomenon to control.  (Same flavour as Slice 11's `passes_through_self`
       non-result: a boundary-snapping subtlety, not a structural lemma.)

     Shape B (shared-hot-pixel preservation) -- THIS FILE.
       If two segments both pass through a hot pixel C (the snap-rounding
       noder's notion of "these segments meet here, at C's centre"), then
       after snapping both endpoints of each segment, both still pass through
       C.  This is the provable local kernel of the audit doc's first conjunct
       (`share_point s1 s2 -> exists shared vertex`): take "share the hot pixel
       C" as the concrete `share_point` witness and "C's centre" as the shared
       vertex.  It follows in two lines from Slice 12's
       `b64_snap_round_preserves_passes_through`, applied once per segment,
       because Slice 11's `passes_through_hot_pixel` already carries the
       snapped-segment touch (so no boundary precondition is needed; cf. the
       Slice 12 header).

   The gap from Shape B to the full `snap_rounding_topologically_consistent`
   is exactly: (i) an arrangement representation + `share_point`/`vertices`/
   `no_spurious_intersections`; (ii) the global argument that the hot pixels a
   crossing induces are shared by both segments (Hobby's hull lemma) so that
   Shape B's per-pixel guarantee assembles into a shared *vertex*; (iii) the
   `no_spurious_intersections` half (no NEW crossings created), which Shape B
   does not address.  Recorded here, not stubbed: there is no Admitted for it.

   ----------------------------------------------------------------------------
   Audit footprint.  Like SnapRounding_b64.v and HotPixel_b64.v, every theorem
   here references `snap_round` / `b64_snap` whose closure pulls
   `Classical_Prop.classic` via Flocq's `round` / `round_mode`; this file is
   listed in docs/audit-exceptions.txt for that lineage.  No Admitteds.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import List.

From Flocq Require Import IEEE754.Binary.

From NTS.Proofs        Require Import Distance HotPixel.
From NTS.Proofs.Flocq  Require Import Validate_binary64.
From NTS.Proofs.Flocq  Require Import HotPixel_b64.
From NTS.Proofs.Flocq  Require Import SnapRounding_b64.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Shared-hot-pixel: the local `share_point` witness.                         *)
(* -------------------------------------------------------------------------- *)

(* R-side: two segments both pass through hot pixel C. *)
Definition share_hot_pixel (P0 P1 Q0 Q1 C : Point) (scale : R) : Prop :=
  passes_through_hot_pixel P0 P1 C scale /\
  passes_through_hot_pixel Q0 Q1 C scale.

(* binary64 mirror. *)
Definition b64_share_hot_pixel (P0 P1 Q0 Q1 C : BPoint) : Prop :=
  b64_passes_through_hot_pixel P0 P1 C = true /\
  b64_passes_through_hot_pixel Q0 Q1 C = true.

(* -------------------------------------------------------------------------- *)
(* Deliverable 1: the topological correctness core (Shape B).                 *)
(* -------------------------------------------------------------------------- *)

(* R-side specification: snap-rounding preserves shared-hot-pixel membership.
   Unconditional -- inherits Slice 12's lack of a boundary precondition. *)
Theorem snap_round_preserves_shared_hot_pixel :
  forall P0 P1 Q0 Q1 C : Point,
    share_hot_pixel P0 P1 Q0 Q1 C 1 ->
    share_hot_pixel (snap_round P0 1) (snap_round P1 1)
                    (snap_round Q0 1) (snap_round Q1 1) C 1.
Proof.
  intros P0 P1 Q0 Q1 C [H1 H2].
  split; apply snap_round_preserves_passes_through; assumption.
Qed.

(* binary64 correctness: snap-rounding both segments keeps them sharing C. *)
Theorem b64_snap_round_preserves_shared_hot_pixel :
  forall P0 P1 Q0 Q1 C : BPoint,
    b64_share_hot_pixel P0 P1 Q0 Q1 C ->
    b64_share_hot_pixel (b64_snap P0) (b64_snap P1)
                        (b64_snap Q0) (b64_snap Q1) C.
Proof.
  intros P0 P1 Q0 Q1 C [H1 H2].
  split; apply b64_snap_round_preserves_passes_through; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Deliverable 2: whole-arrangement lift over a list of segments.             *)
(* -------------------------------------------------------------------------- *)

(* A segment is "covered" by a pixel set if it passes through at least one
   pixel in the set (the noder will route it through that pixel's centre). *)
Definition b64_segment_covered (pixels : list BPoint) (s : BPoint * BPoint) : Prop :=
  List.Exists (fun C => b64_passes_through_hot_pixel (fst s) (snd s) C = true) pixels.

(* Snap both endpoints of a segment. *)
Definition b64_snap_segment (s : BPoint * BPoint) : BPoint * BPoint :=
  (b64_snap (fst s), b64_snap (snd s)).

(* Arrangement-level correctness: if every segment in the arrangement is
   covered by the (fixed) hot-pixel set, then after snapping every segment,
   the snapped arrangement is still covered -- each segment by the SAME pixel.
   The whole-arrangement instance of Deliverable 1, lifted through the list. *)
Theorem b64_snap_round_preserves_pixel_cover :
  forall (segments : list (BPoint * BPoint)) (pixels : list BPoint),
    List.Forall (b64_segment_covered pixels) segments ->
    List.Forall (b64_segment_covered pixels) (List.map b64_snap_segment segments).
Proof.
  intros segments pixels H.
  rewrite List.Forall_forall in *.
  intros s' Hin.
  apply List.in_map_iff in Hin. destruct Hin as [s [Hs Hin]]. subst s'.
  specialize (H s Hin).
  unfold b64_segment_covered, b64_snap_segment in *. cbn [fst snd] in *.
  eapply List.Exists_impl. 2: exact H.
  intros C HC. apply b64_snap_round_preserves_passes_through. exact HC.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions snap_round_preserves_shared_hot_pixel.
Print Assumptions b64_snap_round_preserves_shared_hot_pixel.
Print Assumptions b64_snap_round_preserves_pixel_cover.
