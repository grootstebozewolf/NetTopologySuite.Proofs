(* ============================================================================
   NetTopologySuite.Proofs.Flocq.HobbyCounterexample_b64
   ----------------------------------------------------------------------------
   A Qed-closed REFUTATION of `hobby_lemma_4_3_no_proper`
   (theories-flocq/HobbyTheorem_b64.v).

   `hobby_lemma_4_3_no_proper` was carried as a deferred-proof entry
   (docs/admitted-deferred-proofs.txt) with a 4-6 week "thesis-shaped"
   estimate.  Its statement is:

       forall P0 P1 Q0 Q1 : Point,
         ~ segments_intersect_properly P0 P1 Q0 Q1 ->
         ~ segments_intersect_properly
             (snap_round P0 1) (snap_round P1 1)
             (snap_round Q0 1) (snap_round Q1 1).

   This file proves the statement is FALSE: there is an explicit pair of
   segments that do not intersect properly, yet whose snap-rounded images
   DO intersect properly.

   ----------------------------------------------------------------------------
   The witness (a "parallel collapse").

     A = (0, 0.7) -- (10, 0.7)   [horizontal, y = 0.7]
     B = (3, 1.3) -- ( 7, 1.3)   [horizontal, y = 1.3]

   A and B are parallel horizontal segments at distinct heights, so they
   share no point at all -- in particular they do not intersect properly.

   Snap-rounding to the unit grid (round-half-to-even) sends both y-levels
   to the SAME integer line y = 1 (0.7 -> 1 and 1.3 -> 1):

     snap A = (0, 1) -- (10, 1)
     snap B = (3, 1) -- ( 7, 1)

   These are now COLLINEAR and OVERLAPPING.  Their common interior point
   (5, 1) is reached at parameter t = 1/2 on snap A and s = 1/2 on snap B,
   both strictly interior -- a proper intersection.

   ----------------------------------------------------------------------------
   Why the standalone lemma is false (and the headline is unaffected).

   The result Hobby (1999) Theorem 4.1 actually proves concerns a FULLY
   NODED arrangement: every pairwise intersection is already a vertex, and
   snap-rounding is applied to the resulting fragments.  The deferred
   `hobby_lemma_4_3_no_proper` dropped that context and quantified over two
   ARBITRARY segments.  Snap-rounding two arbitrary non-touching parallel
   segments can collapse them onto one grid line, manufacturing a
   collinear overlap -- a proper intersection that did not exist before.
   This is exactly the well-known "snap-rounding can merge features"
   phenomenon; it is not excluded for arbitrary pairs, only for the noded
   arrangements Hobby's theorem is about.

   `hobby_theorem_4_1_conditional` remains Qed-closed: it merely ASSUMES a
   per-pair preservation hypothesis.  What this file shows is that the
   particular hypothesis the corpus hoped to discharge
   (`hobby_lemma_4_3_no_proper`, and hence the disjunctive
   `hobby_lemma_4_3`) is not provable as stated; closing Hobby Theorem 4.1
   unconditionally requires the noded-arrangement hypothesis, not the
   bare two-segment statement.

   See docs/hobby-lemma-4-3-no-proper-refutation.md.

   ----------------------------------------------------------------------------
   Audit footprint.  Imports the same Flocq layer as HobbyTheorem_b64.v
   (snap_round is Flocq-pinned).  Listed in docs/audit-exceptions.txt for
   that lineage.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lra.

From Flocq Require Import Core.
From Flocq Require Import IEEE754.Binary.
From Flocq Require Import IEEE754.BinarySingleNaN.

From NTS.Proofs        Require Import Distance HotPixel.
From NTS.Proofs.Flocq  Require Import HotPixel_b64.
From NTS.Proofs.Flocq  Require Import HobbyTheorem_b64.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Evaluating `snap_round_coord _ 1` on concrete values.                  *)
(* -------------------------------------------------------------------------- *)

(* `snap_round_coord x 1` rounds `x` to the nearest integer (round-half-
   to-even).  Flocq's `round_FIX_IZR` collapses the FIX(0) rounding to
   `IZR` of the integer rounding function, and `Znearest_imp` pins that
   integer whenever `x` is within 1/2 of it. *)
Lemma snap_round_coord_1_nearest :
  forall (x : R) (n : Z),
    Rabs (x - IZR n) < /2 ->
    snap_round_coord x 1 = IZR n.
Proof.
  intros x n H.
  unfold snap_round_coord.
  rewrite Rmult_1_r.
  rewrite round_FIX_IZR.
  unfold Rdiv. rewrite Rinv_1, Rmult_1_r.
  unfold round_mode.
  rewrite (Znearest_imp (fun z => negb (Z.even z)) x n H).
  reflexivity.
Qed.

(* The six coordinate values used by the witness. *)
Lemma snap_0  : snap_round_coord 0 1 = 0.
Proof.
  rewrite (snap_round_coord_1_nearest 0 0); [ reflexivity | ].
  replace (IZR 0) with 0 by reflexivity.
  rewrite Rminus_0_r, Rabs_R0. lra.
Qed.

Lemma snap_3  : snap_round_coord 3 1 = 3.
Proof.
  rewrite (snap_round_coord_1_nearest 3 3); [ reflexivity | ].
  replace (IZR 3) with 3 by reflexivity.
  replace (3 - 3) with 0 by lra. rewrite Rabs_R0. lra.
Qed.

Lemma snap_7  : snap_round_coord 7 1 = 7.
Proof.
  rewrite (snap_round_coord_1_nearest 7 7); [ reflexivity | ].
  replace (IZR 7) with 7 by reflexivity.
  replace (7 - 7) with 0 by lra. rewrite Rabs_R0. lra.
Qed.

Lemma snap_10 : snap_round_coord 10 1 = 10.
Proof.
  rewrite (snap_round_coord_1_nearest 10 10); [ reflexivity | ].
  replace (IZR 10) with 10 by reflexivity.
  replace (10 - 10) with 0 by lra. rewrite Rabs_R0. lra.
Qed.

Lemma snap_07 : snap_round_coord (7/10) 1 = 1.
Proof.
  rewrite (snap_round_coord_1_nearest (7/10) 1); [ reflexivity | ].
  replace (IZR 1) with 1 by reflexivity.
  apply Rabs_def1; lra.
Qed.

Lemma snap_13 : snap_round_coord (13/10) 1 = 1.
Proof.
  rewrite (snap_round_coord_1_nearest (13/10) 1); [ reflexivity | ].
  replace (IZR 1) with 1 by reflexivity.
  apply Rabs_def1; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The witness points and their snapped images.                          *)
(* -------------------------------------------------------------------------- *)

Definition A0 : Point := mkPoint 0      (7/10).
Definition A1 : Point := mkPoint 10     (7/10).
Definition B0 : Point := mkPoint 3      (13/10).
Definition B1 : Point := mkPoint 7      (13/10).

Lemma snap_A0 : snap_round A0 1 = mkPoint 0  1.
Proof. unfold snap_round, A0; simpl. rewrite snap_0,  snap_07. reflexivity. Qed.
Lemma snap_A1 : snap_round A1 1 = mkPoint 10 1.
Proof. unfold snap_round, A1; simpl. rewrite snap_10, snap_07. reflexivity. Qed.
Lemma snap_B0 : snap_round B0 1 = mkPoint 3  1.
Proof. unfold snap_round, B0; simpl. rewrite snap_3,  snap_13. reflexivity. Qed.
Lemma snap_B1 : snap_round B1 1 = mkPoint 7  1.
Proof. unfold snap_round, B1; simpl. rewrite snap_7,  snap_13. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The two halves of the counterexample.                                  *)
(* -------------------------------------------------------------------------- *)

(* Before snapping: A and B are parallel horizontal segments at y = 0.7 and
   y = 1.3, so no point is common -- no proper intersection. *)
Lemma originals_no_proper :
  ~ segments_intersect_properly A0 A1 B0 B1.
Proof.
  unfold segments_intersect_properly, A0, A1, B0, B1.
  intros [t [s [_ [_ [_ Hpy]]]]]. simpl in Hpy. lra.
Qed.

(* After snapping: snap A and snap B are collinear on y = 1 and overlap;
   the midpoint (5,1) is interior to both (t = s = 1/2). *)
Lemma snapped_proper :
  segments_intersect_properly
    (snap_round A0 1) (snap_round A1 1)
    (snap_round B0 1) (snap_round B1 1).
Proof.
  rewrite snap_A0, snap_A1, snap_B0, snap_B1.
  unfold segments_intersect_properly.
  exists (1/2), (1/2).
  simpl. repeat split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The refutation.                                                        *)
(* -------------------------------------------------------------------------- *)

(* The explicit counterexample: a pair of segments with no proper
   intersection whose snap-rounded images DO intersect properly. *)
Theorem hobby_lemma_4_3_no_proper_counterexample :
  exists P0 P1 Q0 Q1 : Point,
    ~ segments_intersect_properly P0 P1 Q0 Q1 /\
    segments_intersect_properly
      (snap_round P0 1) (snap_round P1 1)
      (snap_round Q0 1) (snap_round Q1 1).
Proof.
  exists A0, A1, B0, B1.
  split; [ exact originals_no_proper | exact snapped_proper ].
Qed.

(* Consequently, the statement of `hobby_lemma_4_3_no_proper` is
   inconsistent: assuming it lets us derive False from the witness. *)
Theorem hobby_lemma_4_3_no_proper_is_false :
  (forall P0 P1 Q0 Q1 : Point,
     ~ segments_intersect_properly P0 P1 Q0 Q1 ->
     ~ segments_intersect_properly
         (snap_round P0 1) (snap_round P1 1)
         (snap_round Q0 1) (snap_round Q1 1)) ->
  False.
Proof.
  intros Hbad.
  exact (Hbad A0 A1 B0 B1 originals_no_proper snapped_proper).
Qed.

Print Assumptions hobby_lemma_4_3_no_proper_counterexample.
Print Assumptions hobby_lemma_4_3_no_proper_is_false.
