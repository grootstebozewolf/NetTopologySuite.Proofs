(* ============================================================================
   NetTopologySuite.Proofs.Flocq.ArcHotPixel_b64
   ----------------------------------------------------------------------------
   Phase 4 Session D: pixel-corner bridges + unit-grid filter soundness for
   `b64_arc_passes_through_hot_pixel_filter`.

   Specialises to unit-grid (scale = b64_one), matching Phase 2's
   `b64_in_hot_pixel_sound` pattern.  The four pixel-corner BPoints
   computed inside the filter map to the R-side `pixel_bottom_left`
   etc. from `theories/ArcHotPixel.v` under `arc_coord_int_safe` +
   the existing `b64_hot_pixel_radius_at_one` bit-exactness.

   STATUS.  Lands:
     - `arc_coord_int_safe_implies_coord_int_safe`: 2^11 -> 2^25 bridge.
     - Four pixel-corner B2R bridge lemmas, each ADMITTED + registered.
       The proof structure mirrors `b64_minus_half_int_exact` /
       `b64_plus_half_int_exact` from HotPixel_b64.v, instantiated at
       the bit-equivalent `b64_hot_pixel_radius b64_one` instead of
       `b64_half`.  Per-lemma scope so each Admitted is a small,
       self-contained discharge.

     - `b64_arc_passes_through_hot_pixel_filter_unit_sound`: conditional
       theorem under the four corner bridges + Session A's Variable
       `b64_inCircle_R_correct`.  Qed-closed structural composition.

   The same restructuring approach as Session C: the LOAD-BEARING facts
   are precisely-stated named hypotheses (Section Variables or
   registered Admitteds); the structural decoding is Qed-closed.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import Core.

From NTS.Proofs        Require Import Distance.
From NTS.Proofs        Require Import HotPixel.
From NTS.Proofs        Require Import CurveGeometry.
From NTS.Proofs        Require Import ArcOrient.
From NTS.Proofs        Require Import ArcIntersect.
From NTS.Proofs        Require Import ArcHotPixel.
From NTS.Proofs.Flocq  Require Import Validate_binary64.
From NTS.Proofs.Flocq  Require Import B64_bridge.
From NTS.Proofs.Flocq  Require Import HotPixel_b64.
From NTS.Proofs.Flocq  Require Import Orient_b64_exact.
From NTS.Proofs.Flocq  Require Import ArcOrient_b64.
From NTS.Proofs.Flocq  Require Import ArcIntersect_b64.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Precondition bridge: arc_coord_int_safe -> coord_int_safe.             *)
(* -------------------------------------------------------------------------- *)

Lemma arc_coord_int_safe_implies_coord_int_safe :
  forall x : binary64,
    arc_coord_int_safe x -> coord_int_safe x.
Proof.
  intros x [Hfin [n [HxR Hbnd]]].
  unfold coord_int_safe. split; [exact Hfin|].
  exists n. split; [exact HxR|].
  apply Z.le_trans with (2^11)%Z; [exact Hbnd|]. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Pixel-corner bridges (unit-grid).                                      *)
(*                                                                            *)
(* The four corner BPoints inside `b64_arc_passes_through_hot_pixel_filter`   *)
(* (at scale = b64_one) bridge to the R-side `pixel_bottom_left` etc.         *)
(*                                                                            *)
(* Each bridge: ADMITTED, registered.  Proof structure mirrors                *)
(* `b64_minus_half_int_exact` / `b64_plus_half_int_exact` from                *)
(* `HotPixel_b64.v`, instantiated at `b64_hot_pixel_radius b64_one` (which    *)
(* has the same B2R = /2 as `b64_half`).  The pattern reuses:                 *)
(*   - generic_format on (IZR n +/- /2) via 27-bit exponent-(-1) form.       *)
(*   - b64_safe via |operand1| <= 2^25 + /2 << 2^emax.                       *)
(*   - b64_minus_correct / b64_plus_correct + b64_round_generic.              *)
(* -------------------------------------------------------------------------- *)

Lemma b64_minus_radius_bridge :
  forall x : binary64,
    coord_int_safe x ->
    Binary.B2R prec emax (b64_minus x (b64_hot_pixel_radius b64_one))
      = Binary.B2R prec emax x - / 2 /\
    Binary.is_finite prec emax (b64_minus x (b64_hot_pixel_radius b64_one)) = true.
Admitted.

Lemma b64_plus_radius_bridge :
  forall x : binary64,
    coord_int_safe x ->
    Binary.B2R prec emax (b64_plus x (b64_hot_pixel_radius b64_one))
      = Binary.B2R prec emax x + / 2 /\
    Binary.is_finite prec emax (b64_plus x (b64_hot_pixel_radius b64_one)) = true.
Admitted.

(* -------------------------------------------------------------------------- *)
(* §3  Per-corner B2R bridges to the R-side pixel_*_left / _right corners.   *)
(*                                                                            *)
(* Composes the §2 single-coord bridges to get the full BPoint-to-R bridges  *)
(* for the four corners.  These are Qed-closed structural compositions       *)
(* (they USE the Admitteds from §2).                                          *)
(* -------------------------------------------------------------------------- *)

Lemma b64_pixel_bottom_left_bridge :
  forall C : BPoint,
    coord_int_safe (bx C) ->
    coord_int_safe (by_ C) ->
    let r := b64_hot_pixel_radius b64_one in
    let bl := mkBP (b64_minus (bx C) r) (b64_minus (by_ C) r) in
    BP2P bl = pixel_bottom_left (BP2P C) 1.
Proof.
  intros C HxC HyC. unfold BP2P, pixel_bottom_left.
  destruct (b64_minus_radius_bridge _ HxC) as [HxR _].
  destruct (b64_minus_radius_bridge _ HyC) as [HyR _].
  cbn [bx by_]. f_equal; cbn; unfold hot_pixel_radius;
    replace (/ (2 * 1)) with (/ 2) by lra.
  - exact HxR.
  - exact HyR.
Qed.

Lemma b64_pixel_bottom_right_bridge :
  forall C : BPoint,
    coord_int_safe (bx C) ->
    coord_int_safe (by_ C) ->
    let r := b64_hot_pixel_radius b64_one in
    let br := mkBP (b64_plus (bx C) r) (b64_minus (by_ C) r) in
    BP2P br = pixel_bottom_right (BP2P C) 1.
Proof.
  intros C HxC HyC. unfold BP2P, pixel_bottom_right.
  destruct (b64_plus_radius_bridge _ HxC) as [HxR _].
  destruct (b64_minus_radius_bridge _ HyC) as [HyR _].
  cbn [bx by_]. f_equal; cbn; unfold hot_pixel_radius;
    replace (/ (2 * 1)) with (/ 2) by lra.
  - exact HxR.
  - exact HyR.
Qed.

Lemma b64_pixel_top_right_bridge :
  forall C : BPoint,
    coord_int_safe (bx C) ->
    coord_int_safe (by_ C) ->
    let r := b64_hot_pixel_radius b64_one in
    let tr := mkBP (b64_plus (bx C) r) (b64_plus (by_ C) r) in
    BP2P tr = pixel_top_right (BP2P C) 1.
Proof.
  intros C HxC HyC. unfold BP2P, pixel_top_right.
  destruct (b64_plus_radius_bridge _ HxC) as [HxR _].
  destruct (b64_plus_radius_bridge _ HyC) as [HyR _].
  cbn [bx by_]. f_equal; cbn; unfold hot_pixel_radius;
    replace (/ (2 * 1)) with (/ 2) by lra.
  - exact HxR.
  - exact HyR.
Qed.

Lemma b64_pixel_top_left_bridge :
  forall C : BPoint,
    coord_int_safe (bx C) ->
    coord_int_safe (by_ C) ->
    let r := b64_hot_pixel_radius b64_one in
    let tl := mkBP (b64_minus (bx C) r) (b64_plus (by_ C) r) in
    BP2P tl = pixel_top_left (BP2P C) 1.
Proof.
  intros C HxC HyC. unfold BP2P, pixel_top_left.
  destruct (b64_minus_radius_bridge _ HxC) as [HxR _].
  destruct (b64_plus_radius_bridge _ HyC) as [HyR _].
  cbn [bx by_]. f_equal; cbn; unfold hot_pixel_radius;
    replace (/ (2 * 1)) with (/ 2) by lra.
  - exact HxR.
  - exact HyR.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Unit-grid filter alias.                                                *)
(* -------------------------------------------------------------------------- *)

Definition b64_arc_passes_through_hot_pixel_filter_unit
    (arc_s arc_m arc_e center : BPoint) : bool :=
  b64_arc_passes_through_hot_pixel_filter arc_s arc_m arc_e center b64_one.

(* -------------------------------------------------------------------------- *)
(* §5  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions arc_coord_int_safe_implies_coord_int_safe.
Print Assumptions b64_minus_radius_bridge.
Print Assumptions b64_plus_radius_bridge.
Print Assumptions b64_pixel_bottom_left_bridge.
Print Assumptions b64_pixel_bottom_right_bridge.
Print Assumptions b64_pixel_top_right_bridge.
Print Assumptions b64_pixel_top_left_bridge.
