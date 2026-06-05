(* ============================================================================
   NetTopologySuite.Proofs.RingOrientation
   ----------------------------------------------------------------------------
   extract_rings_valid R5 / general assembler, slice 3d: the signed-area
   ORIENTATION primitive for hole nesting (docs/extract-rings-proof-structure.md
   §5 step 3; docs/ring-orientation.md).

   The remaining piece of `extract_rings_valid` after the hole-free case (slice
   3c) is DISTINGUISHING the outer ring from holes.  The combinatorial handle is
   ORIENTATION: in a planar subdivision a bounded face is traversed one way
   (positive signed area) and the face across each edge the other way -- and the
   face across an edge is reached by `twin`, which REVERSES each segment.

   This slice isolates the orientation invariant as pure shoelace algebra, free
   of any geometry beyond the signed-area cross product:

     - `signed_area2 segs` : twice the signed area of a segment chain
       (sum of `cross_pt (fst e) (snd e)` over the segments);
     - `signed_area2_app`      : additive over concatenation;
     - `signed_area2_rev`      : invariant under reversing the segment order;
     - `signed_area2_map_swap` : NEGATED by swapping every segment's endpoints;
     - `signed_area2_reverse_traversal` : walking a chain BACKWARDS (reverse
       order + swapped segments) negates the signed area -- the orientation flip;
     - `seg_twin_swap`         : a dart's `twin` swaps its segment's endpoints,
       linking the algebra to the DCEL `twin` (so the face across an edge is the
       orientation-reversed traversal).

   Together: the combinatorial seed of "outer boundary and holes have opposite
   orientation".  Building the outer/hole CLASSIFICATION and the analytic
   `hole_inside_outer` containment on top is deferred (§4).

   Pure `R` arithmetic + lists; no `Admitted` / `Axiom` / `Parameter`.
   Axioms: the standard three-axiom classical-reals base Rocq ships with
   (`functional_extensionality_dep`, `ClassicalDedekindReals.sig_forall_dec`,
   `sig_not_dec`), inherited via the `R` arithmetic in `cross_pt`; this file
   introduces none of its own.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List Lra.
From NTS.Proofs Require Import Distance Dart.

Import ListNotations.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Signed area of a segment chain (shoelace).                              *)
(* -------------------------------------------------------------------------- *)

(* Cross product of two points as position vectors. *)
Definition cross_pt (p q : Point) : R := px p * py q - py p * px q.

(* Endpoint swap of a segment (the reversed directed edge). *)
Definition swap_seg (e : Point * Point) : Point * Point := (snd e, fst e).

(* Twice the signed area of the chain `segs` (the shoelace sum). *)
Definition signed_area2 (segs : list (Point * Point)) : R :=
  fold_right (fun e acc => cross_pt (fst e) (snd e) + acc) 0 segs.

Lemma cross_pt_swap : forall p q, cross_pt q p = - cross_pt p q.
Proof. intros p q. unfold cross_pt. lra. Qed.

Lemma signed_area2_nil : signed_area2 [] = 0.
Proof. reflexivity. Qed.

Lemma signed_area2_cons : forall e segs,
  signed_area2 (e :: segs) = cross_pt (fst e) (snd e) + signed_area2 segs.
Proof. reflexivity. Qed.

Lemma signed_area2_single : forall e,
  signed_area2 [e] = cross_pt (fst e) (snd e).
Proof. intros e. rewrite signed_area2_cons, signed_area2_nil. lra. Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The orientation laws.                                                   *)
(* -------------------------------------------------------------------------- *)

Lemma signed_area2_app : forall a b,
  signed_area2 (a ++ b) = signed_area2 a + signed_area2 b.
Proof.
  induction a as [| e a IH]; intros b; cbn [app].
  - rewrite signed_area2_nil. lra.
  - rewrite !signed_area2_cons, IH. lra.
Qed.

(* Reversing the order of the segments leaves the signed area unchanged. *)
Lemma signed_area2_rev : forall segs, signed_area2 (rev segs) = signed_area2 segs.
Proof.
  induction segs as [| e segs IH]; cbn [rev].
  - reflexivity.
  - rewrite signed_area2_app, signed_area2_single, IH, signed_area2_cons. lra.
Qed.

(* Swapping every segment's endpoints negates the signed area. *)
Lemma signed_area2_map_swap : forall segs,
  signed_area2 (map swap_seg segs) = - signed_area2 segs.
Proof.
  induction segs as [| e segs IH]; cbn [map].
  - rewrite signed_area2_nil. lra.
  - rewrite !signed_area2_cons, IH. unfold swap_seg.
    cbn [fst snd]. rewrite cross_pt_swap. lra.
Qed.

(* Walking a chain BACKWARDS -- reverse the order AND swap each segment's
   endpoints -- negates the signed area.  This is the orientation flip. *)
Theorem signed_area2_reverse_traversal : forall segs,
  signed_area2 (rev (map swap_seg segs)) = - signed_area2 segs.
Proof.
  intros segs. rewrite signed_area2_rev. apply signed_area2_map_swap.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Link to the DCEL: `twin` swaps a dart's segment.                        *)
(* -------------------------------------------------------------------------- *)

(* The segment of a dart's twin is the swap of the dart's segment.  So the face
   across an edge (reached by `twin`) walks the orientation-reversed segments;
   with `signed_area2_reverse_traversal` this is why adjacent faces have opposite
   orientation sign -- the combinatorial seed of outer (one sign) vs hole (the
   other). *)
Lemma seg_twin_swap : forall d : Dart,
  (dbase (twin d), dtip (twin d)) = swap_seg (dbase d, dtip d).
Proof.
  intros d. unfold swap_seg. cbn [fst snd].
  rewrite dbase_twin, dtip_twin. reflexivity.
Qed.
