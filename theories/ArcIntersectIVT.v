(* ============================================================================
   NetTopologySuite.Proofs.ArcIntersectIVT
   ----------------------------------------------------------------------------
   IVT-gated soundness theorem for arc-chord circle intersection.

   Closes the IVT gap that was flagged across S4-S7 of Phase 4: given
   `chord_crosses_arc_circle a P Q` (opposite inCircle_R signs at the
   chord endpoints), the chord crosses the arc's circumscribed circle
   somewhere -- there exists a point on the chord at which inCircle_R
   evaluates to zero.

   The proof uses Stdlib `Ranalysis`'s `IVT_cor` (Intermediate Value
   Theorem corollary, sign-product form).

   WHAT THIS FILE CLOSES (and what it doesn't):

     CLOSED:
       chord_crosses_arc_circle_implies_circle_intersection
         -- sign change at endpoints => exists chord point on circumcircle.
       The pure-IVT result.

     NOT closed in this file (separate session needed):
       Strengthening to `arc_chord_intersects` -- the IVT-witnessed
       circle-crossing point may lie on the MAJOR arc rather than the
       MINOR (arc_span_contains) side.  Promoting circle-intersection
       to arc-intersection requires showing the chord crosses the arc's
       SPAN, not just its CIRCLE.  For arcs subtending < pi this
       (chord_crosses_arc_circle) implies the minor-arc crossing case
       generically, but pathological geometries (chord tangent to span
       boundary) need additional reasoning.  Left as a follow-up.

   See `docs/audit-phase4-chord-overfitting.md` for the gap inventory.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Rfunctions.
From Stdlib Require Import Ranalysis1.
From Stdlib Require Import Ranalysis_reg.
From Stdlib Require Import Rsqrt_def.

From NTS.Proofs Require Import Distance.
From NTS.Proofs Require Import Segment.
From NTS.Proofs Require Import CurveGeometry.
From NTS.Proofs Require Import ArcOrient.
From NTS.Proofs Require Import ArcIntersect.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Chord parametrisation.                                                 *)
(*                                                                            *)
(* `chord_point P Q t` is the point at parameter `t` along the segment from   *)
(* P to Q.  At t = 0 it's P, at t = 1 it's Q.  Linear in t componentwise.    *)
(* -------------------------------------------------------------------------- *)

Definition chord_point (P Q : Point) (t : R) : Point :=
  mkPoint ((1 - t) * px P + t * px Q)
          ((1 - t) * py P + t * py Q).

Lemma chord_point_at_0 :
  forall P Q : Point, chord_point P Q 0 = P.
Proof.
  intros P Q.
  unfold chord_point.
  destruct P as [px0 py0]. cbn.
  f_equal; ring.
Qed.

Lemma chord_point_at_1 :
  forall P Q : Point, chord_point P Q 1 = Q.
Proof.
  intros P Q.
  unfold chord_point.
  destruct Q as [qx qy]. cbn.
  f_equal; ring.
Qed.

(* chord_point is a between-witness for any t in [0,1] -- direct connection
   to Segment.between. *)
Lemma chord_point_between :
  forall (P Q : Point) (t : R),
    0 <= t <= 1 ->
    between P Q (chord_point P Q t).
Proof.
  intros P Q t Ht.
  unfold between, chord_point.
  exists t.
  cbn.
  split; [lra | split; [lra | split; reflexivity]].
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  inCircle_along_chord -- inCircle_R applied to the parametrised chord.  *)
(*                                                                            *)
(* As a function `R -> R` in `t`, this is a polynomial of degree at most 4    *)
(* (degree 1 in chord coords, degree 2 from squared coords; the inCircle_R    *)
(* determinant adds degree 1 from the outer multiplication, hence degree 4    *)
(* total).  Continuous everywhere as a real-valued polynomial.                *)
(* -------------------------------------------------------------------------- *)

Definition inCircle_along_chord
    (a : CircularArc) (P Q : Point) : R -> R :=
  fun t => inCircle_R (arc_start a) (arc_mid a) (arc_end a)
                       (chord_point P Q t).

(* Endpoint evaluations. *)
Lemma inCircle_along_chord_at_0 :
  forall (a : CircularArc) (P Q : Point),
    inCircle_along_chord a P Q 0
      = inCircle_R (arc_start a) (arc_mid a) (arc_end a) P.
Proof.
  intros. unfold inCircle_along_chord. rewrite chord_point_at_0. reflexivity.
Qed.

Lemma inCircle_along_chord_at_1 :
  forall (a : CircularArc) (P Q : Point),
    inCircle_along_chord a P Q 1
      = inCircle_R (arc_start a) (arc_mid a) (arc_end a) Q.
Proof.
  intros. unfold inCircle_along_chord. rewrite chord_point_at_1. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Continuity of inCircle_along_chord.                                    *)
(*                                                                            *)
(* The function is a polynomial in t, hence continuous.  Proved via the       *)
(* derivable chain (`derivable_continuous`).  Polynomial derivability follows *)
(* from the `reg` automation tactic in Ranalysis_reg, but since `reg`         *)
(* requires the function to be expressed in standard Coq function notation    *)
(* (using `+`/`*`/`-` on real-valued functions), we go via                    *)
(* `derivable_pt` on the expanded body instead.                                *)
(*                                                                            *)
(* Alternative: prove continuity_pt directly by composing                     *)
(* `continuity_pt_plus`, `continuity_pt_mult`, `continuity_pt_const`,         *)
(* and `continuity_pt_id` after unfolding the function definition.            *)
(* -------------------------------------------------------------------------- *)

(* inCircle_along_chord is a polynomial in t.  Polynomials are derivable,
   and `derivable_continuous` lifts derivable to continuity.  The `reg`
   automation tactic in Ranalysis_reg handles polynomial derivability
   discharge automatically. *)
Lemma inCircle_along_chord_derivable :
  forall (a : CircularArc) (P Q : Point),
    derivable (inCircle_along_chord a P Q).
Proof.
  intros a P Q.
  unfold inCircle_along_chord, inCircle_R, chord_point.
  cbn [px py].
  reg.
Qed.

(* Global continuity follows from derivability. *)
Lemma inCircle_along_chord_continuous :
  forall (a : CircularArc) (P Q : Point),
    continuity (inCircle_along_chord a P Q).
Proof.
  intros a P Q. apply derivable_continuous.
  apply inCircle_along_chord_derivable.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  The IVT-gated theorem.                                                 *)
(*                                                                            *)
(* Sign change at chord endpoints implies a circle-crossing point on the      *)
(* chord.  Direct application of IVT_cor (sign-product form, x <= y).         *)
(* -------------------------------------------------------------------------- *)

Theorem chord_crosses_arc_circle_implies_circle_intersection :
  forall (a : CircularArc) (P Q : Point),
    chord_crosses_arc_circle a P Q ->
    exists X : Point,
      between P Q X /\
      inCircle_R (arc_start a) (arc_mid a) (arc_end a) X = 0.
Proof.
  intros a P Q Hsign.
  unfold chord_crosses_arc_circle in Hsign.
  set (f := inCircle_along_chord a P Q).
  (* f 0 = inCircle_R ... P, f 1 = inCircle_R ... Q.
     Sign-product < 0 gives the IVT precondition <= 0. *)
  assert (Hf0 : f 0 = inCircle_R (arc_start a) (arc_mid a) (arc_end a) P)
    by apply inCircle_along_chord_at_0.
  assert (Hf1 : f 1 = inCircle_R (arc_start a) (arc_mid a) (arc_end a) Q)
    by apply inCircle_along_chord_at_1.
  assert (Hprod : f 0 * f 1 <= 0) by (rewrite Hf0, Hf1; lra).
  destruct (IVT_cor f 0 1 (inCircle_along_chord_continuous a P Q)
              ltac:(lra) Hprod) as [t [Ht Hft]].
  exists (chord_point P Q t).
  split.
  - apply chord_point_between. exact Ht.
  - unfold f, inCircle_along_chord in Hft. exact Hft.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions chord_point_at_0.
Print Assumptions chord_point_at_1.
Print Assumptions chord_point_between.
Print Assumptions inCircle_along_chord_at_0.
Print Assumptions inCircle_along_chord_at_1.
Print Assumptions inCircle_along_chord_derivable.
Print Assumptions inCircle_along_chord_continuous.
Print Assumptions chord_crosses_arc_circle_implies_circle_intersection.
