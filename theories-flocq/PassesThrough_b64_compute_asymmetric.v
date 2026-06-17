(* ============================================================================
   NetTopologySuite.Proofs.Flocq.PassesThrough_b64_compute_asymmetric
   ----------------------------------------------------------------------------
   MACHINE-CHECKED COUNTEREXAMPLE: the rounded computational hot-pixel
   passes-through filter is NOT SYMMETRIC under segment reversal.

   A snap-rounding noder treats an edge as the UNORDERED segment {P0,P1}: which
   hot pixels it passes through is a property of the point set, independent of
   the stored endpoint order.  The exact-real spec has this symmetry (the
   Liang-Barsky t-interval of P0->P1 is the mirror image under t |-> 1-t of the
   P1->P0 interval, and the clipped-interval-nonempty test is invariant).  The
   rounded `_compute` filter computes the per-axis t-bounds with
   `b64_div (lo - c0) (c1 - c0)` -- evaluated from the c0 end -- so reversing
   the segment divides by `(c0 - c1)` from the other end with DIFFERENT
   round-to-nearest error.  Near a pixel corner the two roundings straddle the
   `tmin <= tmax` overlap boundary, and the verdict FLIPS.

   CORRECTION (2026-06-17): the JTS#752 / JTS#1133 attribution below is
   RETRACTED.  JTS's HotPixel.intersectsScaled (HotPixel.java ~189-199)
   canonicalizes the segment to the positive-X direction BEFORE any orientation
   test, so JTS's actual passes-through test is symmetric under endpoint reversal
   by construction -- this asymmetry models a Liang-Barsky `b64_div`-from-c0
   filter that JTS does NOT use.  The theorem stays Qed and true as a negative
   about THAT filter design, but it does NOT map to a real JTS defect and is not
   the root of JTS#752/#1133.  See docs/oracle-soundness-finding.md "CORRECTION
   (2026-06-17)".  Refs #66.

   (Original framing, retained for context, now superseded by the correction:)
   The same edge, processed with swapped endpoints by a divide-from-c0 filter,
   gets inconsistent "passes through vertex" verdicts -> an inconsistent noding
   graph.  This hazard is real for such a filter but is removed by JTS's
   endpoint canonicalization.

     exists P0 P1 C,
       b64_passes_through_hot_pixel_compute P0 P1 C = true  /\   (* forward *)
       b64_passes_through_hot_pixel_compute P1 P0 C = false.     (* reversed *)

   Witness (CLOSED filter, all coordinates exact powers of two):
     P0 = (1, 2^-53)   P1 = (2^-52, -1)   C = (0, 0).
   A near-corner grazing segment of the unit pixel; the reversed division
   rounds the clipped t-interval to empty.  A second theorem records the same
   asymmetry for the HALF-OPEN filter with P0 = (-1, 2^-53), P1 = (-2^-53, -1).

   BOTH halves of each theorem are decided by `vm_compute` -- this is a purely
   computational fact about the binary64 filter (no `B2R`, no exact-real spec),
   so it needs no coordinate-value plumbing.

   This complements the two other filter-defect theorems:
     - PassesThrough_b64_compute_unsound.v        (closed filter OVER-accepts vs spec)
     - PassesThroughHalfopen_b64_compute_incomplete.v (half-open UNDER-accepts vs spec)
   Together: the rounded passes-through filter is unsound, incomplete (half-open),
   AND order-dependent.  The robust noder primitive remains the EXACT spec
   (`b64_passes_through_hot_pixel`, symmetric and sound by construction).
   ========================================================================== *)

From Flocq Require Import IEEE754.Binary Core.
Require Import ZArith.
From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import HotPixel_b64.
From NTS.Proofs.Flocq Require Import PassesThrough_b64_compute.

(* --- Closed-filter witness: P0 = (1, 2^-53), P1 = (2^-52, -1), C = (0,0). --- *)
Definition aP0x : binary64 := Binary.B754_finite prec emax false 4503599627370496%positive (-52)%Z  eq_refl. (* 1     *)
Definition aP0y : binary64 := Binary.B754_finite prec emax false 4503599627370496%positive (-105)%Z eq_refl. (* 2^-53 *)
Definition aP1x : binary64 := Binary.B754_finite prec emax false 4503599627370496%positive (-104)%Z eq_refl. (* 2^-52 *)
Definition aP1y : binary64 := Binary.B754_finite prec emax true  4503599627370496%positive (-52)%Z  eq_refl. (* -1    *)
Definition aP0 : BPoint := mkBP aP0x aP0y.
Definition aP1 : BPoint := mkBP aP1x aP1y.
Definition aC  : BPoint := mkBP (Binary.B754_zero prec emax false) (Binary.B754_zero prec emax false).

Lemma closed_fwd_true  : b64_passes_through_hot_pixel_compute aP0 aP1 aC = true.
Proof. vm_compute. reflexivity. Qed.
Lemma closed_rev_false : b64_passes_through_hot_pixel_compute aP1 aP0 aC = false.
Proof. vm_compute. reflexivity. Qed.

Theorem b64_passes_through_compute_asymmetric :
  exists P0 P1 C : BPoint,
    b64_passes_through_hot_pixel_compute P0 P1 C = true /\
    b64_passes_through_hot_pixel_compute P1 P0 C = false.
Proof.
  exists aP0, aP1, aC. split; [ exact closed_fwd_true | exact closed_rev_false ].
Qed.

(* --- Half-open witness: P0 = (-1, 2^-53), P1 = (-2^-53, -1), C = (0,0). --- *)
Definition hP0x : binary64 := Binary.B754_finite prec emax true  4503599627370496%positive (-52)%Z  eq_refl. (* -1     *)
Definition hP0y : binary64 := Binary.B754_finite prec emax false 4503599627370496%positive (-105)%Z eq_refl. (* 2^-53  *)
Definition hP1x : binary64 := Binary.B754_finite prec emax true  4503599627370496%positive (-105)%Z eq_refl. (* -2^-53 *)
Definition hP1y : binary64 := Binary.B754_finite prec emax true  4503599627370496%positive (-52)%Z  eq_refl. (* -1     *)
Definition hP0 : BPoint := mkBP hP0x hP0y.
Definition hP1 : BPoint := mkBP hP1x hP1y.

Lemma halfopen_fwd_true  : b64_passes_through_hot_pixel_halfopen_compute hP0 hP1 aC = true.
Proof. vm_compute. reflexivity. Qed.
Lemma halfopen_rev_false : b64_passes_through_hot_pixel_halfopen_compute hP1 hP0 aC = false.
Proof. vm_compute. reflexivity. Qed.

Theorem b64_passes_through_halfopen_compute_asymmetric :
  exists P0 P1 C : BPoint,
    b64_passes_through_hot_pixel_halfopen_compute P0 P1 C = true /\
    b64_passes_through_hot_pixel_halfopen_compute P1 P0 C = false.
Proof.
  exists hP0, hP1, aC. split; [ exact halfopen_fwd_true | exact halfopen_rev_false ].
Qed.

Print Assumptions b64_passes_through_compute_asymmetric.
Print Assumptions b64_passes_through_halfopen_compute_asymmetric.
