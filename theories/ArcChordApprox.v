(* ============================================================================
   NetTopologySuite.Proofs.ArcChordApprox
   ----------------------------------------------------------------------------
   Phase 4 Session 6: sagitta + chord approximation error machinery.

   Mathematical core of Option B (chord approximation).  Defines the
   sagitta -- the maximum perpendicular distance from a chord to the
   circular arc it approximates -- and proves the load-bearing
   equidistance property of `arc_center` that the sagitta depends on.

   The headline `chord_approx_error_bound` connecting chord-approximated
   `arc_passes_through_hot_pixel` to the original arc is deferred to a
   follow-up: it requires both `arc_mid_within_sagitta` (a perpendicular-
   distance geometric proof) and S4's `arc_chord_intersect_sound` (IVT-
   blocked).  This session lands the foundations on which that headline
   composes.

   See `docs/audit-phase4-chord-overfitting.md` §5 (Session 6 in the
   7-session plan).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Field.

From NTS.Proofs Require Import Distance.
From NTS.Proofs Require Import CurveGeometry.
From NTS.Proofs Require Import ArcOrient.
From NTS.Proofs Require Import ArcHotPixel.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  arc_center_equidistant.                                                *)
(*                                                                            *)
(* The defining geometric property of the circumscribed circle: arc_center    *)
(* is equidistant from all three control points.                              *)
(*                                                                            *)
(* Closed via `field` after unfolding arc_center's explicit formula.  The     *)
(* divisor `ax*(by-cy) + bx*(cy-ay) + cx*(ay-by)` is non-zero under           *)
(* `valid_arc` (it's the signed-area-equivalent of the non-collinearity      *)
(* cross product, up to a factor of 2).                                       *)
(* -------------------------------------------------------------------------- *)

Lemma arc_center_equidistant :
  forall a : CircularArc,
    valid_arc a ->
    dist_sq (arc_center a) (arc_start a) = dist_sq (arc_center a) (arc_mid a) /\
    dist_sq (arc_center a) (arc_start a) = dist_sq (arc_center a) (arc_end a).
Proof.
  intros a Hva.
  unfold valid_arc in Hva.
  unfold dist_sq, arc_center.
  cbn [px py].
  set (ax := px (arc_start a)) in *.
  set (ay := py (arc_start a)) in *.
  set (bx := px (arc_mid a)) in *.
  set (by_ := py (arc_mid a)) in *.
  set (cx := px (arc_end a)) in *.
  set (cy := py (arc_end a)) in *.
  assert (Hd_ne : ax * (by_ - cy) + bx * (cy - ay) + cx * (ay - by_) <> 0).
  { intros Heq. apply Hva. nra. }
  split.
  - field. exact Hd_ne.
  - field. exact Hd_ne.
Qed.

(* Corollary: pairwise equality of all three squared distances. *)
Lemma arc_center_equidistant_mid_end :
  forall a : CircularArc,
    valid_arc a ->
    dist_sq (arc_center a) (arc_mid a) = dist_sq (arc_center a) (arc_end a).
Proof.
  intros a Hva.
  destruct (arc_center_equidistant a Hva) as [Hsm Hse].
  rewrite <- Hsm. exact Hse.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  arc_radius_sq.                                                         *)
(*                                                                            *)
(* `arc_radius a := dist (arc_center a) (arc_start a)` (from CurveGeometry).  *)
(* The squared form is more useful for polynomial reasoning (avoids sqrt).    *)
(* -------------------------------------------------------------------------- *)

Definition arc_radius_sq (a : CircularArc) : R :=
  dist_sq (arc_center a) (arc_start a).

(* The squared radius equals dist_sq to each defining point. *)
Lemma arc_radius_sq_eq_mid :
  forall a, valid_arc a ->
    arc_radius_sq a = dist_sq (arc_center a) (arc_mid a).
Proof. intros. unfold arc_radius_sq. apply arc_center_equidistant; assumption. Qed.

Lemma arc_radius_sq_eq_end :
  forall a, valid_arc a ->
    arc_radius_sq a = dist_sq (arc_center a) (arc_end a).
Proof. intros. unfold arc_radius_sq. apply arc_center_equidistant; assumption. Qed.

(* arc_radius_sq is non-negative. *)
Lemma arc_radius_sq_nonneg :
  forall a, 0 <= arc_radius_sq a.
Proof. intros. unfold arc_radius_sq. apply dist_sq_nonneg. Qed.

(* -------------------------------------------------------------------------- *)
(* §3  chord_half_length.                                                     *)
(*                                                                            *)
(* Half the Euclidean length of the chord (arc_start, arc_end).               *)
(* -------------------------------------------------------------------------- *)

Definition chord_half_length_sq (a : CircularArc) : R :=
  dist_sq (arc_start a) (arc_end a) / 4.

Definition chord_half_length (a : CircularArc) : R :=
  sqrt (chord_half_length_sq a).

Lemma chord_half_length_sq_nonneg :
  forall a, 0 <= chord_half_length_sq a.
Proof.
  intros a. unfold chord_half_length_sq.
  pose proof (dist_sq_nonneg (arc_start a) (arc_end a)) as Hd.
  lra.
Qed.

Lemma chord_half_length_nonneg :
  forall a, 0 <= chord_half_length a.
Proof. intros. unfold chord_half_length. apply sqrt_pos. Qed.

(* -------------------------------------------------------------------------- *)
(* §4  sagitta.                                                               *)
(*                                                                            *)
(* The classical sagitta: maximum perpendicular distance from the chord to    *)
(* the arc.  For a circle of radius r and half-chord-length l:                *)
(*   sagitta = r - sqrt(r^2 - l^2)                                            *)
(*                                                                            *)
(* For circular arcs r >= l geometrically (the perpendicular from the         *)
(* center to the chord midpoint is real-valued), so r^2 - l^2 >= 0 and the   *)
(* sqrt is well-defined.  This session uses `Rmax 0 _` as the sqrt argument   *)
(* to make the DEFINITION total without requiring `arc_radius_ge_half_chord`  *)
(* as a precondition; the inequality lands as a separate lemma.              *)
(* -------------------------------------------------------------------------- *)

Definition sagitta_sq_inner (a : CircularArc) : R :=
  Rmax 0 (arc_radius_sq a - chord_half_length_sq a).

Definition sagitta (a : CircularArc) : R :=
  sqrt (arc_radius_sq a) - sqrt (sagitta_sq_inner a).

(* -------------------------------------------------------------------------- *)
(* §5  sagitta properties: non-negativity + upper bound.                      *)
(* -------------------------------------------------------------------------- *)

Lemma sagitta_sq_inner_nonneg :
  forall a, 0 <= sagitta_sq_inner a.
Proof.
  intros a. unfold sagitta_sq_inner.
  apply Rmax_l.
Qed.

(* sqrt of inner <= sqrt of arc_radius_sq.  Follows from inner <=
   arc_radius_sq (chord_half_length_sq >= 0 means subtracting it gives
   something <= arc_radius_sq).  Combined with Rmax 0 _: still <= since
   arc_radius_sq >= 0. *)
Lemma sagitta_sq_inner_le_radius_sq :
  forall a, sagitta_sq_inner a <= arc_radius_sq a.
Proof.
  intros a. unfold sagitta_sq_inner.
  pose proof (arc_radius_sq_nonneg a) as Hr.
  pose proof (chord_half_length_sq_nonneg a) as Hc.
  apply Rmax_lub; lra.
Qed.

Lemma sqrt_sagitta_inner_le_sqrt_radius_sq :
  forall a, sqrt (sagitta_sq_inner a) <= sqrt (arc_radius_sq a).
Proof.
  intros a. apply sqrt_le_1.
  - apply sagitta_sq_inner_nonneg.
  - apply arc_radius_sq_nonneg.
  - apply sagitta_sq_inner_le_radius_sq.
Qed.

Lemma sagitta_nonneg :
  forall a, 0 <= sagitta a.
Proof.
  intros a. unfold sagitta.
  pose proof (sqrt_sagitta_inner_le_sqrt_radius_sq a). lra.
Qed.

Lemma sagitta_le_radius_sqrt :
  forall a, sagitta a <= sqrt (arc_radius_sq a).
Proof.
  intros a. unfold sagitta.
  pose proof (sqrt_pos (sagitta_sq_inner a)). lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Connecting arc_radius to sqrt arc_radius_sq.                           *)
(*                                                                            *)
(* By definition `arc_radius a = dist (arc_center a) (arc_start a) = sqrt     *)
(* (dist_sq ...)`.  The squared version is the same dist_sq.  Bridge:         *)
(*   arc_radius a = sqrt (arc_radius_sq a)                                    *)
(* -------------------------------------------------------------------------- *)

Lemma arc_radius_eq_sqrt :
  forall a, arc_radius a = sqrt (arc_radius_sq a).
Proof.
  intros a. unfold arc_radius, arc_radius_sq, dist. reflexivity.
Qed.

Lemma arc_radius_nonneg :
  forall a, 0 <= arc_radius a.
Proof.
  intros a. rewrite arc_radius_eq_sqrt. apply sqrt_pos.
Qed.

Lemma sagitta_le_arc_radius :
  forall a, sagitta a <= arc_radius a.
Proof.
  intros a. rewrite arc_radius_eq_sqrt. apply sagitta_le_radius_sqrt.
Qed.

(* -------------------------------------------------------------------------- *)
(* §7  What this session DOES NOT close (and why).                            *)
(*                                                                            *)
(* The headline `chord_approx_error_bound` -- "if the chord approximation     *)
(* passes through a hot pixel, the original arc passes through a nearby      *)
(* pixel within sagitta distance" -- has TWO load-bearing dependencies        *)
(* that this session does not provide:                                        *)
(*                                                                            *)
(*   (a) `arc_radius_sq_ge_chord_half_length_sq`: the geometric inequality   *)
(*       arc_radius^2 >= chord_half_length^2.  Provably true for valid       *)
(*       arcs but requires a perpendicular-bisector geometric argument       *)
(*       (the chord midpoint is at squared distance chord_half_length_sq    *)
(*       from each chord endpoint; the center is at squared distance         *)
(*       arc_radius_sq from each chord endpoint; the right-triangle          *)
(*       formed by center / chord-midpoint / chord-endpoint gives r^2 =      *)
(*       d^2 + l^2 where d is the center-to-chord distance, hence            *)
(*       r^2 >= l^2).  Multi-step, not the sagitta machinery itself.         *)
(*                                                                            *)
(*   (b) `arc_mid_within_sagitta`: the geometric content -- arc_mid is       *)
(*       within `sagitta a` perpendicular distance of the chord midpoint.    *)
(*       Requires showing the perpendicular bisector of the chord passes    *)
(*       through both arc_mid and arc_center, then bounding the              *)
(*       arc_mid -- chord_midpoint distance by the radius minus the          *)
(*       center-to-chord distance.                                            *)
(*                                                                            *)
(* Both (a) and (b) compose with S4's `arc_chord_intersect_sound` (IVT-      *)
(* blocked) to give the headline.  Deferred to a follow-up session that      *)
(* handles the perpendicular-bisector geometry (independent of the IVT       *)
(* gap; can land any time).                                                   *)
(*                                                                            *)
(* This session lands the SAGITTA DEFINITION cleanly + the load-bearing      *)
(* equidistance lemma (`arc_center_equidistant`) that everything downstream   *)
(* of it compose on.                                                          *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* §8  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions arc_center_equidistant.
Print Assumptions arc_center_equidistant_mid_end.
Print Assumptions arc_radius_sq_eq_mid.
Print Assumptions arc_radius_sq_eq_end.
Print Assumptions arc_radius_sq_nonneg.
Print Assumptions chord_half_length_sq_nonneg.
Print Assumptions chord_half_length_nonneg.
Print Assumptions sagitta_sq_inner_nonneg.
Print Assumptions sagitta_sq_inner_le_radius_sq.
Print Assumptions sqrt_sagitta_inner_le_sqrt_radius_sq.
Print Assumptions sagitta_nonneg.
Print Assumptions sagitta_le_radius_sqrt.
Print Assumptions arc_radius_eq_sqrt.
Print Assumptions arc_radius_nonneg.
Print Assumptions sagitta_le_arc_radius.
