(* ============================================================================
   NetTopologySuite.Proofs.FaceOrientation
   ----------------------------------------------------------------------------
   extract_rings_valid R5 / general assembler, slice 3e: orientation
   classification of face rings -- the combinatorial scaffolding for outer vs
   hole (docs/extract-rings-proof-structure.md §5 step 3; docs/face-orientation.md).

   Slice 3d (theories/RingOrientation.v) gave the signed-area primitive and its
   orientation-flip law.  This slice lifts it to RINGS and FACES:

     - `ring_signed_area2 r` : twice the signed area of a ring (over `ring_edges`);
     - `ring_ccw` / `ring_cw`     : the orientation classifier, with exclusivity
       and trichotomy;
     - `ring_signed_area2_of_chain` : a face ring's signed area equals its
       defining chain's (via slice-3a `ring_edges_of_closed_chain`);
     - `twin_face_chain` + `twin_face_chain_signed_area` : the face built from the
       TWIN darts, walked in reverse, has the NEGATED signed area -- i.e. the
       face across each edge is oppositely oriented.  This is the combinatorial
       heart of "outer boundary one way, holes the other".

   DELIBERATELY DEFERRED: the geometric meaning of the sign (positive area
   <-> bounded/encloses-interior) and the analytic `hole_inside_outer`
   containment (§4) -- the JCT-adjacent residual; and assigning a globally
   consistent orientation across an arrangement's faces.

   Pure `R` + list combinatorics; no `Admitted` / `Axiom` / `Parameter`.
   Axioms: the standard three-axiom classical-reals base (via `R` arithmetic),
   introduces none of its own.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List Lra.
From NTS.Proofs Require Import Distance Overlay BufferAssembly RingExtract
                               Vec Direction Azimuth Dart DartAngularOrder
                               DartNext DartNextSpec DartNextInjective
                               OrbitCycle DartFace FaceChain RingOrientation.

Import ListNotations.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Signed area of a ring, and the orientation classifier.                  *)
(* -------------------------------------------------------------------------- *)

(* Twice the signed area of a ring: the shoelace sum over its edges. *)
Definition ring_signed_area2 (r : Ring) : R := signed_area2 (ring_edges r).

(* CCW (positive) vs CW (negative) orientation. *)
Definition ring_ccw (r : Ring) : Prop := ring_signed_area2 r > 0.
Definition ring_cw  (r : Ring) : Prop := ring_signed_area2 r < 0.

Lemma ring_ccw_not_cw : forall r, ring_ccw r -> ~ ring_cw r.
Proof. intros r H Hc. unfold ring_ccw, ring_cw in *. lra. Qed.

Lemma ring_orientation_trichotomy : forall r,
  ring_ccw r \/ ring_cw r \/ ring_signed_area2 r = 0.
Proof.
  intros r. unfold ring_ccw, ring_cw.
  destruct (Rtotal_order (ring_signed_area2 r) 0) as [H | [H | H]]; auto.
Qed.

(* A face ring's signed area equals that of its defining chain. *)
Lemma ring_signed_area2_of_chain : forall segs,
  closed_chain segs ->
  ring_signed_area2 (ring_of_chain segs) = signed_area2 segs.
Proof.
  intros segs Hcc. unfold ring_signed_area2.
  rewrite (ring_edges_of_closed_chain segs Hcc). reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The twin face is oppositely oriented.                                   *)
(* -------------------------------------------------------------------------- *)

(* The segment of a dart's twin is the swap of the dart's segment. *)
Lemma seg_of_twin_swap : forall d : Dart, seg_of (twin d) = swap_seg (seg_of d).
Proof. intros d. unfold seg_of. apply seg_twin_swap. Qed.

(* Swapping every segment of a face chain = taking the segments of the TWIN
   darts. *)
Lemma map_swap_face_chain : forall D d n,
  map swap_seg (face_chain D d n) = map seg_of (map twin (dart_walk D d n)).
Proof.
  intros D d n. unfold face_chain. rewrite !map_map.
  apply map_ext. intros x. symmetry. apply seg_of_twin_swap.
Qed.

(* The face across the edges: the twin darts, walked in reverse. *)
Definition twin_face_chain (D : list Dart) (d : Dart) (n : nat) : list (Point * Point) :=
  rev (map seg_of (map twin (dart_walk D d n))).

(* It carries the NEGATED signed area -- the adjacent face is oppositely
   oriented.  This is the orientation opposition that underlies outer vs hole:
   walking `next o twin` traces one face; the SAME edges traced from the twin
   darts (the face on the other side of each edge) run the opposite way, so the
   two faces sharing an edge have opposite sign.  Fixing one global sign
   convention (say, bounded faces positive) then reads the outer boundary and its
   holes as opposite orientations -- the combinatorial half of the outer/hole
   classification that slice 3f assembles into a `valid_polygon` (the remaining
   half being the analytic `hole_inside_outer`, §4). *)
Theorem twin_face_chain_signed_area : forall D d n,
  signed_area2 (twin_face_chain D d n) = - signed_area2 (face_chain D d n).
Proof.
  intros D d n. unfold twin_face_chain.
  rewrite <- map_swap_face_chain.
  apply signed_area2_reverse_traversal.
Qed.

(* So if a face is CCW, the face across its edges (its twin face) is CW. *)
Corollary twin_face_cw_of_ccw : forall D d n,
  signed_area2 (face_chain D d n) > 0 ->
  signed_area2 (twin_face_chain D d n) < 0.
Proof.
  intros D d n H. rewrite twin_face_chain_signed_area. lra.
Qed.
