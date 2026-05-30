(* ============================================================================
   NetTopologySuite.Proofs.Flocq.ArcIntersect_b64
   ----------------------------------------------------------------------------
   Phase 4 Session B: binary64 bool wrappers for arc intersection predicates.

   Builds on Session A's `b64_inCircle_sign` decision procedure to land:

     - `b64_chord_crosses_arc_circle`: bool sufficient condition for a
       chord crossing an arc's circumcircle (mirror of
       `chord_crosses_arc_circle` from `theories/ArcIntersect.v:129`).

     - `b64_arc_passes_through_hot_pixel_filter`: bool sufficient
       condition for an arc passing through a hot pixel (structural
       mirror of `arc_passes_through_hot_pixel` from
       `theories/ArcHotPixel.v:95`).  Six-way disjunction composing
       four `b64_chord_crosses_arc_circle` calls (one per pixel edge)
       with two `b64_in_hot_pixel` calls (one per arc endpoint).

   Soundness theorems are CONDITIONAL on the same Section Variable
   pattern used in Session A: `b64_inCircle_R_correct` captures the
   load-bearing fact that `B2R (b64_inCircle_R ...)` equals
   `inCircle_R (BP2P ...) ...` under the integer-safe precondition.
   Stating soundness conditionally lets this session land the
   structural decoding without the full ~15-step bridge chain
   (deferred to a follow-up Stage A session).

   Pattern: matches `hobby_theorem_4_1_conditional`,
   `overlay_ng_correct_conditional`, `point_in_ring_correct_jct`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import Core.

From NTS.Proofs        Require Import Distance.
From NTS.Proofs        Require Import CurveGeometry.
From NTS.Proofs        Require Import ArcOrient.
From NTS.Proofs        Require Import ArcIntersect.
From NTS.Proofs.Flocq  Require Import Validate_binary64.
From NTS.Proofs.Flocq  Require Import HotPixel_b64.    (* b64_in_hot_pixel, BP2P *)
From NTS.Proofs.Flocq  Require Import ArcOrient_b64.   (* b64_inCircle_sign, ... *)

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  b64_chord_crosses_arc_circle.                                          *)
(*                                                                            *)
(* Mirror of `chord_crosses_arc_circle a P Q` (ArcIntersect.v:129).            *)
(* Fires iff the inCircle signs at P and Q are STRICTLY opposite: one Pos    *)
(* and one Neg.  Endpoint-on-circle hits (Zero) and unclassified              *)
(* (Nan / overflow) are conservatively rejected, matching the R-side          *)
(* `sP * sQ < 0` strict-inequality form.                                       *)
(* -------------------------------------------------------------------------- *)

Definition b64_chord_crosses_arc_circle
    (arc_s arc_m arc_e P Q : BPoint) : bool :=
  match b64_inCircle_sign arc_s arc_m arc_e P,
        b64_inCircle_sign arc_s arc_m arc_e Q with
  | ICS_Pos, ICS_Neg => true
  | ICS_Neg, ICS_Pos => true
  | _,       _       => false
  end.

(* Symmetry in the chord direction -- mirrors `chord_crosses_arc_circle_sym`
   in ArcIntersect.v:195.  Pure case analysis on the four ICS constructors. *)
Lemma b64_chord_crosses_arc_circle_sym :
  forall (arc_s arc_m arc_e P Q : BPoint),
    b64_chord_crosses_arc_circle arc_s arc_m arc_e P Q =
    b64_chord_crosses_arc_circle arc_s arc_m arc_e Q P.
Proof.
  intros arc_s arc_m arc_e P Q.
  unfold b64_chord_crosses_arc_circle.
  destruct (b64_inCircle_sign arc_s arc_m arc_e P);
  destruct (b64_inCircle_sign arc_s arc_m arc_e Q);
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  b64_arc_passes_through_hot_pixel_filter.                               *)
(*                                                                            *)
(* Mirror of `arc_passes_through_hot_pixel a C scale` (ArcHotPixel.v:95).      *)
(* Six-way disjunction:                                                       *)
(*   - 4 pixel-edge chord crossings (via b64_chord_crosses_arc_circle).      *)
(*   - 2 arc-endpoint in-pixel tests (via b64_in_hot_pixel from               *)
(*     theories-flocq/HotPixel_b64.v).                                        *)
(*                                                                            *)
(* Pixel corners computed at the binary64 level using b64_hot_pixel_radius   *)
(* + b64_plus / b64_minus on the center coordinates.  Layout matches the     *)
(* R-side `pixel_bottom_left` etc. from ArcHotPixel.v:71-81.                  *)
(* -------------------------------------------------------------------------- *)

Definition b64_arc_passes_through_hot_pixel_filter
    (arc_s arc_m arc_e center : BPoint) (scale : binary64) : bool :=
  let r     := b64_hot_pixel_radius scale in
  let cx_lo := b64_minus (bx center) r in
  let cx_hi := b64_plus  (bx center) r in
  let cy_lo := b64_minus (by_ center) r in
  let cy_hi := b64_plus  (by_ center) r in
  let bl    := mkBP cx_lo cy_lo in
  let br    := mkBP cx_hi cy_lo in
  let tr    := mkBP cx_hi cy_hi in
  let tl    := mkBP cx_lo cy_hi in
  b64_chord_crosses_arc_circle arc_s arc_m arc_e bl br ||
  b64_chord_crosses_arc_circle arc_s arc_m arc_e br tr ||
  b64_chord_crosses_arc_circle arc_s arc_m arc_e tr tl ||
  b64_chord_crosses_arc_circle arc_s arc_m arc_e tl bl ||
  b64_in_hot_pixel arc_s center scale ||
  b64_in_hot_pixel arc_e center scale.

(* -------------------------------------------------------------------------- *)
(* §3  Conditional soundness for b64_chord_crosses_arc_circle.                *)
(*                                                                            *)
(* Uses the same Section Variable pattern as ArcOrient_b64.v:                *)
(* `b64_inCircle_R_correct` is captured as a named hypothesis; the            *)
(* directional decoding theorem composes Session A's sign-soundness with     *)
(* a tiny arithmetic step ((+) * (-) < 0).                                    *)
(* -------------------------------------------------------------------------- *)

Section ArcIntersectConditional.

  (* Load-bearing hypothesis (inherited from ArcOrient_b64 Session A).
     The follow-up Stage A session discharges this with the
     b64_*_int_exact chain. *)
  Variable b64_inCircle_R_correct :
    forall A B C P : BPoint,
      inCircle_inputs_int_safe A B C P ->
      Binary.B2R prec emax (b64_inCircle_R A B C P)
        = inCircle_R (BP2P A) (BP2P B) (BP2P C) (BP2P P) /\
      Binary.is_finite prec emax (b64_inCircle_R A B C P) = true.

  (* Build a `chord_crosses_arc_circle`-shaped CircularArc from three
     R-side reference points -- the conclusion's natural form, since
     the R-side predicate takes a `CircularArc` record. *)
  Let arc_from (arc_s arc_m arc_e : BPoint) : CircularArc :=
    mkCircularArc (BP2P arc_s) (BP2P arc_m) (BP2P arc_e).

  Theorem b64_chord_crosses_arc_circle_sound :
    forall (arc_s arc_m arc_e P Q : BPoint),
      inCircle_inputs_int_safe arc_s arc_m arc_e P ->
      inCircle_inputs_int_safe arc_s arc_m arc_e Q ->
      b64_chord_crosses_arc_circle arc_s arc_m arc_e P Q = true ->
      chord_crosses_arc_circle (arc_from arc_s arc_m arc_e)
                                (BP2P P) (BP2P Q).
  Proof.
    intros arc_s arc_m arc_e P Q HsafeP HsafeQ Hbool.
    unfold b64_chord_crosses_arc_circle in Hbool.
    pose proof (b64_inCircle_sign_sound b64_inCircle_R_correct
                  arc_s arc_m arc_e P HsafeP) as HP.
    pose proof (b64_inCircle_sign_sound b64_inCircle_R_correct
                  arc_s arc_m arc_e Q HsafeQ) as HQ.
    unfold chord_crosses_arc_circle, arc_from. cbn [arc_start arc_mid arc_end].
    destruct (b64_inCircle_sign arc_s arc_m arc_e P) eqn:EP;
    destruct (b64_inCircle_sign arc_s arc_m arc_e Q) eqn:EQ;
    try discriminate.
    - (* Pos, Neg: P inside (positive), Q outside (negative).
         Product: positive * negative < 0. *)
      nra.
    - (* Neg, Pos: symmetric. *)
      nra.
  Qed.

End ArcIntersectConditional.

(* -------------------------------------------------------------------------- *)
(* §4  Structural lemmas (no conditional hypothesis).                         *)
(* -------------------------------------------------------------------------- *)

(* `b64_chord_crosses_arc_circle` and `b64_arc_passes_through_hot_pixel_filter`
   are both bool-valued, so their decidability is structural. *)

Lemma b64_chord_crosses_arc_circle_decidable :
  forall arc_s arc_m arc_e P Q : BPoint,
    { b64_chord_crosses_arc_circle arc_s arc_m arc_e P Q = true } +
    { b64_chord_crosses_arc_circle arc_s arc_m arc_e P Q = false }.
Proof.
  intros. destruct (b64_chord_crosses_arc_circle _ _ _ _ _); auto.
Qed.

Lemma b64_arc_passes_through_hot_pixel_filter_decidable :
  forall arc_s arc_m arc_e center : BPoint,
  forall scale : binary64,
    { b64_arc_passes_through_hot_pixel_filter
        arc_s arc_m arc_e center scale = true } +
    { b64_arc_passes_through_hot_pixel_filter
        arc_s arc_m arc_e center scale = false }.
Proof.
  intros. destruct (b64_arc_passes_through_hot_pixel_filter _ _ _ _ _); auto.
Qed.

(* The pixel filter inherits chord-circle's properties on the endpoint
   disjuncts: when an endpoint is in the pixel, the filter fires. *)
Lemma b64_arc_passes_through_hot_pixel_filter_start_in :
  forall (arc_s arc_m arc_e center : BPoint) (scale : binary64),
    b64_in_hot_pixel arc_s center scale = true ->
    b64_arc_passes_through_hot_pixel_filter
      arc_s arc_m arc_e center scale = true.
Proof.
  intros arc_s arc_m arc_e center scale Hin.
  unfold b64_arc_passes_through_hot_pixel_filter.
  rewrite Hin.
  rewrite !Bool.orb_true_r. reflexivity.
Qed.

Lemma b64_arc_passes_through_hot_pixel_filter_end_in :
  forall (arc_s arc_m arc_e center : BPoint) (scale : binary64),
    b64_in_hot_pixel arc_e center scale = true ->
    b64_arc_passes_through_hot_pixel_filter
      arc_s arc_m arc_e center scale = true.
Proof.
  intros arc_s arc_m arc_e center scale Hin.
  unfold b64_arc_passes_through_hot_pixel_filter.
  rewrite Hin.
  rewrite !Bool.orb_true_r. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Deferred: full pixel-filter soundness.                                 *)
(* -------------------------------------------------------------------------- *)

(* Full soundness of `b64_arc_passes_through_hot_pixel_filter` against the
   R-side `arc_passes_through_hot_pixel` (ArcHotPixel.v:95) requires
   connecting the b64 pixel-corner BPoints (built from b64_minus / b64_plus
   on the center) to the R-side `pixel_bottom_left` etc. from
   `theories/ArcHotPixel.v:71-81`.  Those bridges are themselves Stage A
   chains (similar to Phase 2's b64_in_hot_pixel_sound).

   Deferred as a follow-up session, alongside the discharge of
   `b64_inCircle_R_correct` itself.  See
   `docs/audit-phase4-curves.md` for the deferred-work registry. *)

(* -------------------------------------------------------------------------- *)
(* §6  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_chord_crosses_arc_circle_sym.
Print Assumptions b64_chord_crosses_arc_circle_sound.
Print Assumptions b64_chord_crosses_arc_circle_decidable.
Print Assumptions b64_arc_passes_through_hot_pixel_filter_decidable.
Print Assumptions b64_arc_passes_through_hot_pixel_filter_start_in.
Print Assumptions b64_arc_passes_through_hot_pixel_filter_end_in.
