(* ============================================================================
   NetTopologySuite.Proofs.RelateIntDetBound
   ----------------------------------------------------------------------------
   Integer-coordinate range bound for the orientation determinant, grounding
   the robust DE-9IM / relate approach of Romanschek, Clemen & Huhnt,
   "A Novel Robust Approach for Computing DE-9IM Matrices Based on Space
   Partition and Integer Coordinates", ISPRS Int. J. Geo-Inf. 2021, 10, 715
   (doi:10.3390/ijgi10110715), Section 3.2.

   That approach computes spatial relations exactly by carrying coordinates as
   integers and never rounding; the only arithmetic that can overflow is the
   3-point orientation determinant (their Equation (2))

       det(a,b,c) = (bx - ax)(cy - ay) - (cx - ax)(by - ay)

   which is signed twice the area of triangle a-b-c.  The paper's central
   feasibility argument (Section 3.2, Equations (4),(5),(8)) is: if every
   coordinate fits in a bounded integer window, the determinant fits in the
   next-wider native integer type, so the whole pipeline is overflow-free and
   therefore exact.  This module mechanises that argument.

   Two regimes are established:

     1. 32-bit coordinate regime (proven on the nose).  With non-negative
        coordinates in [0, 2^31 - 1] -- the regime after the paper's scale +
        translate-to-bounding-box-minimum step (Equation (6), which makes all
        coordinates >= 0) -- the determinant is representable in signed 64-bit:
        |det| <= 2^63 - 1.  This is the paper's "32 bit integers can be used
        for the coordinates" statement.

     2. 64-bit coordinate regime (paper's tight cmax, Equations (5),(8)).  The
        paper pushes the coordinate window to cmax = floor(sqrt(2^63 - 1)) =
        3,037,000,499 using the *geometric* bound |det| <= cmax^2 (the area of
        a triangle inside a cmax x cmax box is at most cmax^2 / 2, Equation (4),
        Figure 3).  Here we pin down cmax exactly (cmax^2 <= 2^63 - 1 <
        (cmax+1)^2) and exhibit witnesses achieving +/- cmax^2, so the range
        [-cmax^2, cmax^2] of Equation (4) is tight.  The *universal* upper
        bound |det| <= cmax^2 over the whole box -- the half-box-area fact --
        is the one piece deferred (see the honest-scoping note below); the
        algebraic bound proven in (1) is the weaker |det| <= 2 cmax^2.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

(* -------------------------------------------------------------------------- *)
(* The orientation determinant on integer coordinates (paper Equation (2)).   *)
(* -------------------------------------------------------------------------- *)

Definition idet (ax ay bx by_ cx cy : Z) : Z :=
  (bx - ax) * (cy - ay) - (cx - ax) * (by_ - ay).

(* -------------------------------------------------------------------------- *)
(* Algebraic range bound.                                                     *)
(*                                                                            *)
(* For non-negative coordinates in [0,c], coordinate differences lie in       *)
(* [-c,c], each product in [-c^2,c^2], and the determinant (a difference of    *)
(* two such products) in [-2c^2, 2c^2].  This is the conservative algebraic    *)
(* bound; the paper's tighter geometric bound |det| <= c^2 is discussed in     *)
(* the honest-scoping note below.                                             *)
(* -------------------------------------------------------------------------- *)

Lemma idet_abs_le_2sq :
  forall c ax ay bx by_ cx cy,
    0 <= ax <= c -> 0 <= ay <= c -> 0 <= bx <= c -> 0 <= by_ <= c ->
    0 <= cx <= c -> 0 <= cy <= c ->
    Z.abs (idet ax ay bx by_ cx cy) <= 2 * (c * c).
Proof.
  intros c ax ay bx by_ cx cy Hax Hay Hbx Hby Hcx Hcy.
  unfold idet. apply Z.abs_le. split; nia.
Qed.

(* -------------------------------------------------------------------------- *)
(* Regime 1: 32-bit coordinates => 64-bit determinant is overflow-free.        *)
(*                                                                            *)
(* `i32max = 2^31 - 1` is the largest signed 32-bit integer.  After the        *)
(* paper's translate-to-bounding-box-minimum step every coordinate is in       *)
(* [0, i32max], and `2 * i32max^2 = 9223372028264841218 <= 2^63 - 1`, so the   *)
(* determinant is representable in a signed 64-bit integer.                    *)
(* -------------------------------------------------------------------------- *)

Definition i32max : Z := 2 ^ 31 - 1.

Theorem idet_fits_int64_for_int32_coords :
  forall ax ay bx by_ cx cy,
    0 <= ax <= i32max -> 0 <= ay <= i32max -> 0 <= bx <= i32max ->
    0 <= by_ <= i32max -> 0 <= cx <= i32max -> 0 <= cy <= i32max ->
    - (2 ^ 63 - 1) <= idet ax ay bx by_ cx cy <= 2 ^ 63 - 1.
Proof.
  intros ax ay bx by_ cx cy Hax Hay Hbx Hby Hcx Hcy.
  assert (H := idet_abs_le_2sq i32max ax ay bx by_ cx cy
                 Hax Hay Hbx Hby Hcx Hcy).
  apply Z.abs_le in H. unfold i32max in H. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* Regime 2: the paper's tight cmax (Equations (5),(8)).                       *)
(*                                                                            *)
(* cmax = floor(sqrt(2^63 - 1)).  We pin it down by the bracketing pair        *)
(* cmax^2 <= 2^63 - 1 < (cmax+1)^2, which is exactly Equation (5) instantiated *)
(* for the 64-bit determinant (Equation (8)).                                 *)
(* -------------------------------------------------------------------------- *)

Definition cmax : Z := 3037000499.

(* Equation (8): cmax^2 fits in a signed 64-bit integer. *)
Theorem cmax_sq_le_int64 : cmax * cmax <= 2 ^ 63 - 1.
Proof. unfold cmax. lia. Qed.

(* Equation (5): cmax is the *largest* such value -- one more overflows. *)
Theorem cmax_succ_sq_gt_int64 : (cmax + 1) * (cmax + 1) > 2 ^ 63 - 1.
Proof. unfold cmax. lia. Qed.

(* -------------------------------------------------------------------------- *)
(* Tightness of the determinant range (paper Equation (4): detmax = +/-c^2).   *)
(*                                                                            *)
(* The maximum-area triangle inside the box (Figure 3) realises both ends of   *)
(* the range, so [-cmax^2, cmax^2] cannot be shrunk.                           *)
(* -------------------------------------------------------------------------- *)

Theorem idet_max_witness : idet 0 0 cmax 0 0 cmax = cmax * cmax.
Proof. unfold idet, cmax. ring. Qed.

Theorem idet_min_witness : idet 0 0 0 cmax cmax 0 = - (cmax * cmax).
Proof. unfold idet, cmax. ring. Qed.

(* The witnesses lie inside the cmax coordinate window, and the realised       *)
(* extreme values are exactly the Int64-edge cmax^2 -- confirming the window   *)
(* is maximal: any larger coordinate could push |det| past 2^63 - 1.           *)
Corollary idet_range_tight_at_int64_edge :
  idet 0 0 cmax 0 0 cmax = cmax * cmax /\
  cmax * cmax <= 2 ^ 63 - 1 /\
  (cmax + 1) * (cmax + 1) > 2 ^ 63 - 1.
Proof.
  split; [exact idet_max_witness | ].
  split; [exact cmax_sq_le_int64 | exact cmax_succ_sq_gt_int64].
Qed.

(* -------------------------------------------------------------------------- *)
(* Honest scoping note.                                                       *)
(*                                                                            *)
(* The paper's full 64-bit coordinate window [0, cmax] relies on the tight     *)
(* GEOMETRIC bound |idet| <= cmax^2 (Equation (4): the determinant is twice    *)
(* the area of a triangle inside a cmax x cmax box, which is at most           *)
(* cmax^2 / 2).  What this module proves universally is the algebraic bound    *)
(* |idet| <= 2 c^2 (`idet_abs_le_2sq`); that already discharges the 32-bit     *)
(* coordinate regime on the nose (`idet_fits_int64_for_int32_coords`), because *)
(* 2 * (2^31-1)^2 <= 2^63 - 1.                                                 *)
(*                                                                            *)
(* The universal half-box-area inequality                                     *)
(*                                                                            *)
(*    forall coords in [0,c],  Z.abs (idet ...) <= c * c                       *)
(*                                                                            *)
(* (which would license the full [0, cmax] window) is a multilinear extremum   *)
(* fact -- the determinant attains its extreme only at box corners, where it   *)
(* equals 0 or +/- c^2.  It does NOT follow from `nia`'s degree-2 product      *)
(* search and is left as a follow-up brick (corner-reduction over the six      *)
(* coordinates, or a Positivstellensatz certificate using the shared-vertex    *)
(* difference generators).  `idet_max_witness` / `idet_min_witness` already    *)
(* show the bound, once proven, is tight.                                      *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                               *)
(* -------------------------------------------------------------------------- *)

Print Assumptions idet_fits_int64_for_int32_coords.
Print Assumptions cmax_sq_le_int64.
Print Assumptions cmax_succ_sq_gt_int64.
Print Assumptions idet_range_tight_at_int64_edge.
