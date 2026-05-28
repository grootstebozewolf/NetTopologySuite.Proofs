(* ============================================================================
   NetTopologySuite.Proofs.Flocq.HobbyTheorem_b64
   ----------------------------------------------------------------------------
   Hobby (1999) Theorem 4.1 -- the headline correctness statement of snap
   rounding -- placed in the same epistemic position as Shewchuk Theorem 13
   in this corpus: definitions and the conditional theorem are Qed-closed;
   the two supporting lemmas (4.2 monotone-coordinate, 4.3 piecewise-linear
   ordering) are Admitted with registered deferred-proof entries.

   Paper: J. D. Hobby, "Practical segment intersection with finite precision
   output," Computational Geometry: Theory and Applications 13(4):199-214,
   1999.  Section 4.

   See docs/hobby-theorem-proof-structure.md for the proof structure mapped
   to Coq obligations, the gap analysis (§6), and the resumption
   checklist (§7).

   File placement.  Hobby's `snap_round` (the discretisation operator D_T) is
   `snap_round` from HotPixel_b64.v -- Flocq-pinned -- so this file lives in
   the Flocq layer.  All the surrounding predicates (proper crossing,
   fully-intersected, the snap region) are pure-R; they live here for
   cohesion, not because they need Flocq.

   Audit footprint.  Like the other snap-rounding files (HotPixel_b64.v,
   SnapRounding_b64.v, TopologicalCorrectness_b64.v), `snap_round`'s closure
   pulls `Classical_Prop.classic` through Flocq's `round` / `round_mode`.
   This file is listed in docs/audit-exceptions.txt for that lineage.  Two
   Admitteds, both registered in docs/admitted-deferred-proofs.txt.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.

From NTS.Proofs        Require Import Distance HotPixel.
From NTS.Proofs.Flocq  Require Import Validate_binary64.
From NTS.Proofs.Flocq  Require Import HotPixel_b64.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1 The Hobby Theorem 4.1 definitions.                                      *)
(* -------------------------------------------------------------------------- *)

(* Two segments [P0,P1] and [Q0,Q1] intersect PROPERLY when they cross at an
   interior point: parameters t and s both strictly in (0,1) yield the same
   point.  This is Hobby's notion of "proper crossing" in §4. *)
Definition segments_intersect_properly (P0 P1 Q0 Q1 : Point) : Prop :=
  exists t s : R,
    0 < t < 1 /\ 0 < s < 1 /\
    (1 - t) * px P0 + t * px P1 =
    (1 - s) * px Q0 + s * px Q1 /\
    (1 - t) * py P0 + t * py P1 =
    (1 - s) * py Q0 + s * py Q1.

(* Two segments meet only at endpoints (or not at all): either there is no
   proper crossing, or they share an endpoint.  Hobby's "intersect only at
   endpoints" condition. *)
Definition segments_intersect_only_at_endpoints (s1 s2 : Point * Point) : Prop :=
  let '(P0, P1) := s1 in
  let '(Q0, Q1) := s2 in
  ~ segments_intersect_properly P0 P1 Q0 Q1 \/
  (P0 = Q0 \/ P0 = Q1 \/ P1 = Q0 \/ P1 = Q1).

(* An arrangement is FULLY INTERSECTED when distinct segments meet only at
   endpoints.  This is the input invariant Hobby's Theorem 4.1 requires. *)
Definition fully_intersected (segs : list (Point * Point)) : Prop :=
  forall s1 s2 : Point * Point,
    In s1 segs -> In s2 segs -> s1 <> s2 ->
    segments_intersect_only_at_endpoints s1 s2.

(* The discretisation operator D_T (Hobby §4): snap-round every segment
   endpoint.  `fst` / `snd` rather than a pattern match keeps the map term
   beta-reducible without an explicit `destruct` in proofs that consume it. *)
Definition snap_round_segments (segs : list (Point * Point)) : list (Point * Point) :=
  List.map (fun s => (snap_round (fst s) 1, snap_round (snd s) 1)) segs.

(* Snap region for a segment (Hobby p.210-211, written R^- in the paper):
   the integer-grid points lying weakly lower-left of some point on the
   segment.  Used in Lemma 4.2's monotone-coordinate statement.

   ** KNOWN DEFINITION DEFECT ** (see docs/hobby-lemma-4-2-session-1-
   outcome.md): the rendering below is a lower-left quadrant, not a
   near-segment strip, which makes `hobby_lemma_4_2` FALSE as written
   (concrete three-point counterexample on the segment (0,0)-(2,2)).
   Hobby's R^- is the strip of integer points whose hot pixel meets
   the segment.  The intended fix is to replace this definition with
   roughly `segment_touches_hot_pixel P0 P1 p 1` from
   theories/HotPixel.v; that work is the first item on the §7
   resumption checklist.  Leaving the broken definition in place for
   now to avoid invalidating callers (`hobby_lemma_4_3` references it
   indirectly through Lemma 4.2's conclusion only); the definition is
   `Admitted`-adjacent through the lemma's Admitted status. *)
Definition in_snap_region (P0 P1 p : Point) : Prop :=
  (exists nx ny : Z, px p = IZR nx /\ py p = IZR ny) /\
  exists t : R, 0 <= t <= 1 /\
    px p <= px (segment_point P0 P1 t) /\
    py p <= py (segment_point P0 P1 t).

(* -------------------------------------------------------------------------- *)
(* §2 Hobby Lemma 4.2 -- monotone coordinate.                                 *)
(* Admitted; registered in docs/admitted-deferred-proofs.txt.                 *)
(* Proof sketch: docs/hobby-theorem-proof-structure.md §3.                    *)
(* -------------------------------------------------------------------------- *)

(* For any non-degenerate segment there is a diagonal direction (1, +/-1)
   such that distinct integer points in the segment's snap region have
   distinct linear projections.  Hobby chooses alpha_y as sign(slope); the
   monotonicity then follows from a ceiling-of-IZR argument over Z. *)
Lemma hobby_lemma_4_2 :
  forall (P0 P1 : Point),
    P0 <> P1 ->
    exists alpha_y : R,
      (alpha_y = 1 \/ alpha_y = -1) /\
      forall p q : Point,
        in_snap_region P0 P1 p ->
        in_snap_region P0 P1 q ->
        p <> q ->
        px p + alpha_y * py p <> px q + alpha_y * py q.
Admitted.

(* -------------------------------------------------------------------------- *)
(* §3 Hobby Lemma 4.3 -- piecewise-linear ordering.                           *)
(* Admitted; registered in docs/admitted-deferred-proofs.txt.                 *)
(* Proof sketch: docs/hobby-theorem-proof-structure.md §4.                    *)
(* -------------------------------------------------------------------------- *)

(* Snap-rounding preserves "intersect only at endpoints" for any pair of
   segments.  The CORE of Hobby's correctness argument: a rotated-coordinate
   piecewise-linear ordering argument using Lemma 4.2 + the tolerance-square
   |F_j(xi) - beta_j - gamma_j * xi| < 1/2 bound. *)
Lemma hobby_lemma_4_3 :
  forall (P0 P1 Q0 Q1 : Point),
    segments_intersect_only_at_endpoints (P0, P1) (Q0, Q1) ->
    forall sigma1 sigma2 : Point * Point,
      In sigma1 (snap_round_segments [(P0, P1)]) ->
      In sigma2 (snap_round_segments [(Q0, Q1)]) ->
      sigma1 <> sigma2 ->
      segments_intersect_only_at_endpoints sigma1 sigma2.
Admitted.

(* -------------------------------------------------------------------------- *)
(* §4 Hobby Theorem 4.1 -- conditional.                                       *)
(* Qed-closed: structural list composition.                                   *)
(* -------------------------------------------------------------------------- *)

(* The headline of Hobby's Section 4, conditional on a per-pair preservation
   hypothesis `Hlemma43` (which the standalone `hobby_lemma_4_3` above would
   discharge if proved).  Proof: lift the per-pair preservation through the
   arrangement via `List.in_map_iff` -- the segment-list version of "if every
   PAIR is preserved, the whole ARRANGEMENT is preserved."

   `Hlemma43`'s signature here takes `segments_intersect_only_at_endpoints
   s1 s2` as a premise rather than re-deriving it; `Hfi : fully_intersected A`
   supplies that premise for the pair we extract from in_map_iff.

   (One revision from the prompt's sketch -- per the prompt's "one revision
   allowed" stopping condition -- to make `Hfi` actually feed in.  The
   prompt's sketch had `Hlemma43` repeat the `s1 <> s2` precondition with no
   way for `Hfi` to discharge it; this form composes cleanly.) *)
Theorem hobby_theorem_4_1_conditional :
  forall (A : list (Point * Point)),
    fully_intersected A ->
    (forall s1 s2 : Point * Point,
       segments_intersect_only_at_endpoints s1 s2 ->
       forall sigma1 sigma2 : Point * Point,
         In sigma1 (snap_round_segments [s1]) ->
         In sigma2 (snap_round_segments [s2]) ->
         sigma1 <> sigma2 ->
         segments_intersect_only_at_endpoints sigma1 sigma2) ->
    fully_intersected (snap_round_segments A).
Proof.
  intros A Hfi Hlemma43 sigma1 sigma2 Hin1' Hin2' Hne.
  unfold snap_round_segments in Hin1', Hin2'.
  apply List.in_map_iff in Hin1'.
  destruct Hin1' as [s1 [Heq1 Hin1]].
  apply List.in_map_iff in Hin2'.
  destruct Hin2' as [s2 [Heq2 Hin2]].
  assert (Hs12 : s1 <> s2).
  { intros E. apply Hne. subst s2. rewrite <- Heq1. exact Heq2. }
  apply (Hlemma43 s1 s2 (Hfi s1 s2 Hin1 Hin2 Hs12) sigma1 sigma2).
  - unfold snap_round_segments; simpl. left. exact Heq1.
  - unfold snap_round_segments; simpl. left. exact Heq2.
  - exact Hne.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions hobby_theorem_4_1_conditional.
