(* ============================================================================
   NetTopologySuite.Proofs.Flocq.SnapRounding_b64
   ----------------------------------------------------------------------------
   Phase 2 milestone 3 (Slice 12): the snap-rounding algorithm correctness
   invariant.

   The invariant: a segment that passes through a hot pixel before snapping
   still passes through it after snapping.  Builds directly on Slice 10
   (`b64_liang_barsky_touches`) and Slice 11 (`passes_through_hot_pixel`,
   `snap_round`, `b64_snap`).

   ----------------------------------------------------------------------------
   Boundary behavior -- design decision.

   Slice 11's non-result (`HotPixel_b64.v:2330`) established that
   `passes_through_self` is FALSE in general: at the included lower boundary
   x = cx - 1/2 with an odd center cx, round-half-to-even snaps to the
   neighbouring pixel cx-1.

   This file's preservation theorem does NOT need a boundary precondition
   (neither Option A's exclusion nor Option B's geometric handling).  The
   reason is structural: Slice 11 deliberately defined `passes_through_hot_pixel`
   (and its boolean mirror `b64_passes_through_hot_pixel`) as a CONJUNCTION
   that ALREADY carries the snapped-segment touch:

       passes_through_hot_pixel P0 P1 C s :=
         segment_touches_hot_pixel P0 P1 C s
         /\ segment_touches_hot_pixel (snap_round P0 s) (snap_round P1 s) C s.

   "Snap-rounding preserves passes_through" therefore never has to prove that
   an ORIGINAL touch implies a SNAPPED touch (the statement that the boundary
   non-result refutes).  The relation HANDS US the snapped touch as a
   hypothesis.  Applying `snap_round` a second time leaves the already-snapped
   endpoints fixed (snap idempotence), so the goal's two conjuncts are exactly
   the hypothesis's snapped-touch conjunct, once directly and once after
   rewriting by idempotence.  The theorem holds for ALL inputs; the boundary
   subtlety is structurally sidestepped by the relation's own definition --
   which is precisely the design Slice 11's comment anticipated ("getting the
   snap semantics exact here is what keeps that proof a mechanical
   composition").

   Load-bearing piece.  The prompt anticipated `b64_snap_preserves_lb` (a
   Liang-Barsky parameter-interval argument) as the likely tangent.  Given the
   ACTUAL conjunction definition, that lemma is NOT needed: the load-bearing
   fact is snap idempotence.  And idempotence is itself clean -- `b64_liang_
   barsky_touches` reads ONLY `B2R` coordinate values, so float-level
   idempotence (which would need NaN/inf case analysis) is unnecessary; B2R-
   level idempotence (`round_generic` on an already-rounded value) suffices.

   File placement.  `snap_round` / `passes_through_hot_pixel` are R-valued but
   live in the Flocq-importing `HotPixel_b64.v` (their snap semantics are
   pinned to Flocq's `round`; see that file's header).  Hence the "R-side"
   preservation theorem must also live in the Flocq layer -- it cannot sit in
   the Flocq-free `theories/HotPixel.v`.  This file therefore carries both the
   R-side and the binary64 theorems.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lra.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import Core.

From NTS.Proofs        Require Import Distance HotPixel.
From NTS.Proofs.Flocq  Require Import Validate_binary64.
From NTS.Proofs.Flocq  Require Import HotPixel_b64.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Snap idempotence -- the R side.                                            *)
(* -------------------------------------------------------------------------- *)

(* Snapping a coordinate is idempotent on the unit grid: the result of one
   snap is already in the FIX_exp 0 generic format, so `round` fixes it.
   No `Znearest_IZR` reasoning needed -- `round_generic` on an already-rounded
   value (`generic_format_round`) closes it directly. *)
Lemma snap_round_coord_idem :
  forall r : R, snap_round_coord (snap_round_coord r 1) 1 = snap_round_coord r 1.
Proof.
  intros r. unfold snap_round_coord.
  rewrite !Rmult_1_r, !Rdiv_1_r.
  apply round_generic; auto with typeclass_instances.
  apply generic_format_round; auto with typeclass_instances.
Qed.

(* Point-level idempotence: re-snapping a snapped point is a no-op. *)
Lemma snap_round_idempotent :
  forall P : Point, snap_round (snap_round P 1) 1 = snap_round P 1.
Proof.
  intros P. unfold snap_round. cbn [px py].
  f_equal; apply snap_round_coord_idem.
Qed.

(* -------------------------------------------------------------------------- *)
(* Deliverable 1: the snap-rounding correctness invariant -- R-side spec.     *)
(* -------------------------------------------------------------------------- *)

(* Unconditional: see the boundary-behavior note in the file header.  The
   relation already carries the snapped-segment touch, so preservation is the
   mechanical composition `snapped touch (given) + snap idempotence`. *)
Theorem snap_round_preserves_passes_through :
  forall P0 P1 C : Point,
    passes_through_hot_pixel P0 P1 C 1 ->
    passes_through_hot_pixel (snap_round P0 1) (snap_round P1 1) C 1.
Proof.
  intros P0 P1 C Hpass.
  unfold passes_through_hot_pixel in *.
  destruct Hpass as [_Htouch Hsnap].
  split.
  - (* snapped segment touches C: this IS the snapped-touch hypothesis *)
    exact Hsnap.
  - (* doubly-snapped segment touches C: snap idempotence collapses it *)
    rewrite !snap_round_idempotent. exact Hsnap.
Qed.

(* -------------------------------------------------------------------------- *)
(* Snap idempotence -- the binary64 side, at the B2R level.                   *)
(* -------------------------------------------------------------------------- *)

(* `b64_liang_barsky_touches` is a pure function of the B2R values of its
   coordinates (it never inspects float bits beyond `B2R`), so we never need
   FLOAT-level idempotence `b64_snap (b64_snap P) = b64_snap P` (which would
   demand NaN/inf case analysis).  B2R-level idempotence suffices. *)
Lemma b64_snap_coord_B2R_idem :
  forall x : binary64,
    Binary.B2R prec emax (b64_snap_coord (b64_snap_coord x))
      = Binary.B2R prec emax (b64_snap_coord x).
Proof.
  intros x. rewrite !b64_snap_coord_B2R. apply snap_round_coord_idem.
Qed.

(* The filter depends only on the B2R values of the six coordinates. *)
Lemma b64_liang_barsky_touches_B2R_congr :
  forall P0 P1 P0' P1' C C' : BPoint,
    Binary.B2R prec emax (bx P0)  = Binary.B2R prec emax (bx P0')  ->
    Binary.B2R prec emax (by_ P0) = Binary.B2R prec emax (by_ P0') ->
    Binary.B2R prec emax (bx P1)  = Binary.B2R prec emax (bx P1')  ->
    Binary.B2R prec emax (by_ P1) = Binary.B2R prec emax (by_ P1') ->
    Binary.B2R prec emax (bx C)   = Binary.B2R prec emax (bx C')   ->
    Binary.B2R prec emax (by_ C)  = Binary.B2R prec emax (by_ C')  ->
    b64_liang_barsky_touches P0 P1 C = b64_liang_barsky_touches P0' P1' C'.
Proof.
  intros P0 P1 P0' P1' C C' Hx0 Hy0 Hx1 Hy1 Hcx Hcy.
  unfold b64_liang_barsky_touches.
  rewrite Hx0, Hy0, Hx1, Hy1, Hcx, Hcy. reflexivity.
Qed.

(* Re-snapping the endpoints of an already-snapped segment leaves the filter
   verdict unchanged.  Combines the B2R-congruence with B2R idempotence. *)
Lemma b64_liang_barsky_touches_snap_idem :
  forall P0 P1 C : BPoint,
    b64_liang_barsky_touches (b64_snap (b64_snap P0)) (b64_snap (b64_snap P1)) C
      = b64_liang_barsky_touches (b64_snap P0) (b64_snap P1) C.
Proof.
  intros P0 P1 C.
  apply b64_liang_barsky_touches_B2R_congr;
    (apply b64_snap_coord_B2R_idem || reflexivity).
Qed.

(* -------------------------------------------------------------------------- *)
(* Deliverable 2: the snap-rounding correctness invariant -- binary64.        *)
(* -------------------------------------------------------------------------- *)

(* Unconditional, for the same structural reason as the R-side spec: the
   boolean relation `b64_passes_through_hot_pixel` already ANDs in the
   snapped-segment touch.  Preservation = `andb_true` destruct + the snapped
   conjunct (given) + filter-stability under re-snapping. *)
Theorem b64_snap_round_preserves_passes_through :
  forall P0 P1 C : BPoint,
    b64_passes_through_hot_pixel P0 P1 C = true ->
    b64_passes_through_hot_pixel (b64_snap P0) (b64_snap P1) C = true.
Proof.
  intros P0 P1 C H.
  unfold b64_passes_through_hot_pixel in *.
  apply Bool.andb_true_iff in H. destruct H as [_H1 H2].
  apply Bool.andb_true_iff. split.
  - (* snapped segment fires the filter: this IS the snapped-touch conjunct *)
    exact H2.
  - (* doubly-snapped segment fires the filter: re-snap is filter-stable *)
    rewrite b64_liang_barsky_touches_snap_idem. exact H2.
Qed.

(* -------------------------------------------------------------------------- *)
(* Deliverable 3: the per-segment snap-rounding step + soundness.             *)
(* -------------------------------------------------------------------------- *)

(* One step of the snap-rounding noder for a single segment against one hot
   pixel: snap the endpoints iff the segment passes through the pixel,
   otherwise leave the segment untouched. *)
Definition b64_snap_round_segment (P0 P1 C : BPoint) : BPoint * BPoint :=
  if b64_passes_through_hot_pixel P0 P1 C then
    (b64_snap P0, b64_snap P1)
  else
    (P0, P1).

(* Soundness of the step: whichever branch is taken, a segment that passed
   through C still passes through C afterwards. *)
Lemma b64_snap_round_segment_correct :
  forall P0 P1 C : BPoint,
    let '(Q0, Q1) := b64_snap_round_segment P0 P1 C in
    b64_passes_through_hot_pixel P0 P1 C = true ->
    b64_passes_through_hot_pixel Q0 Q1 C = true.
Proof.
  intros P0 P1 C. unfold b64_snap_round_segment.
  destruct (b64_passes_through_hot_pixel P0 P1 C) eqn:Hpass; cbn.
  - intros _. apply b64_snap_round_preserves_passes_through. exact Hpass.
  - intro H. discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions snap_round_preserves_passes_through.
Print Assumptions b64_snap_round_preserves_passes_through.
Print Assumptions b64_snap_round_segment_correct.
