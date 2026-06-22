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

(* The squared radius equals dist_sq to each defining point.  Both proofs
   destruct `arc_center_equidistant` explicitly and use the relevant
   conjunct -- clearer intent than relying on `apply` unifying through
   the conjunction. *)
Lemma arc_radius_sq_eq_mid :
  forall a, valid_arc a ->
    arc_radius_sq a = dist_sq (arc_center a) (arc_mid a).
Proof.
  intros a Hva. unfold arc_radius_sq.
  destruct (arc_center_equidistant a Hva) as [Hsm _]. exact Hsm.
Qed.

Lemma arc_radius_sq_eq_end :
  forall a, valid_arc a ->
    arc_radius_sq a = dist_sq (arc_center a) (arc_end a).
Proof.
  intros a Hva. unfold arc_radius_sq.
  destruct (arc_center_equidistant a Hva) as [_ Hse]. exact Hse.
Qed.

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
(* §6b  Perpendicular bisector geometry (follow-up session, 2026-05-29).      *)
(*                                                                            *)
(* The Pythagorean identity for the chord and its midpoint, and the           *)
(* immediate inequality arc_radius_sq >= chord_half_length_sq.                *)
(*                                                                            *)
(* These were originally documented as deferred in §7 below.  This block      *)
(* closes the first half of that deferral.                                    *)
(* -------------------------------------------------------------------------- *)

(* Midpoint of the chord between arc_start and arc_end. *)
Definition chord_midpoint (a : CircularArc) : Point :=
  mkPoint ((px (arc_start a) + px (arc_end a)) / 2)
          ((py (arc_start a) + py (arc_end a)) / 2).

Lemma OM_perp_chord :
  forall a : CircularArc,
    valid_arc a ->
    let O := arc_center a in
    let M := chord_midpoint a in
    let S := arc_start a in
    let E := arc_end a in
    (px O - px M) * (px E - px S) + (py O - py M) * (py E - py S) = 0.
Proof.
  intros a Hva.
  destruct (arc_center_equidistant a Hva) as [Hsm Hse].
  cbn [px py].
  (* scaled (no /) form that ring accepts; equals dist_diff. *)
  assert (Hscaled :
    (2 * px (arc_center a) - px (arc_start a) - px (arc_end a)) *
    (px (arc_end a) - px (arc_start a)) +
    (2 * py (arc_center a) - py (arc_start a) - py (arc_end a)) *
    (py (arc_end a) - py (arc_start a))
    = dist_sq (arc_center a) (arc_start a) - dist_sq (arc_center a) (arc_end a)).
  {
    unfold dist_sq.
    cbn [px py].
    ring.
  }
  rewrite Hse in Hscaled.
  (* Relate dot (chord form) to scaled/2 . After cbv zeta on the goal
     (which substitutes let M), the dot lhs will use px (chord_midpoint a)
     form, which matches this. *)
  assert (Hdot_scaled :
    (px (arc_center a) - px (chord_midpoint a)) * (px (arc_end a) - px (arc_start a)) +
    (py (arc_center a) - py (chord_midpoint a)) * (py (arc_end a) - py (arc_start a))
    = ((2 * px (arc_center a) - px (arc_start a) - px (arc_end a)) *
       (px (arc_end a) - px (arc_start a)) +
       (2 * py (arc_center a) - py (arc_start a) - py (arc_end a)) *
       (py (arc_end a) - py (arc_start a))) / 2).
  {
    unfold chord_midpoint.
    cbn [px py].
    field.
  }
  rewrite Hscaled in Hdot_scaled.
  cbv zeta.
  cbn [px py].
  rewrite Hdot_scaled.
  (* Now goal is (distE - distE)/2 = 0 ; simplify and finish. *)
  ring_simplify.
  lra.
Qed.

(* Median length formula -- pure algebra (no hypothesis needed).
   For any three points A, B, C:
     dist_sq C A + dist_sq C B = 2 * dist_sq C M + dist_sq A B / 2
   where M is the midpoint of (A, B).  Closes by `ring` after unfolding
   dist_sq and the midpoint. *)
Lemma median_length_formula :
  forall A B C : Point,
    dist_sq C A + dist_sq C B
      = 2 * dist_sq C (mkPoint ((px A + px B) / 2) ((py A + py B) / 2))
        + dist_sq A B / 2.
Proof.
  intros A B C. unfold dist_sq. cbn [px py]. field.
Qed.

(* Pythagorean decomposition under equidistance.
   For a valid arc:
     arc_radius_sq = dist_sq (arc_center) (chord_midpoint)
                   + chord_half_length_sq.
   The right triangle is (arc_center, chord_midpoint, arc_start),
   right-angled at chord_midpoint because arc_center is on the
   perpendicular bisector of (arc_start, arc_end) -- which it is
   precisely because arc_center_equidistant says the center is
   equidistant from the chord endpoints. *)
Lemma arc_radius_sq_pythagorean :
  forall a : CircularArc,
    valid_arc a ->
    arc_radius_sq a
      = dist_sq (arc_center a) (chord_midpoint a)
        + chord_half_length_sq a.
Proof.
  intros a Hva.
  pose proof (median_length_formula (arc_start a) (arc_end a) (arc_center a))
    as Hmed.
  destruct (arc_center_equidistant a Hva) as [_ Hse].
  (* Hmed: dist_sq center start + dist_sq center end =
           2 * dist_sq center M + dist_sq start end / 2 *)
  (* Hse:  dist_sq center start = dist_sq center end. *)
  unfold arc_radius_sq, chord_half_length_sq, chord_midpoint.
  rewrite <- Hse in Hmed.
  lra.
Qed.

(* The geometric inequality: half-chord-length squared <= radius squared. *)
Lemma arc_radius_sq_ge_chord_half_length_sq :
  forall a : CircularArc,
    valid_arc a ->
    chord_half_length_sq a <= arc_radius_sq a.
Proof.
  intros a Hva.
  rewrite (arc_radius_sq_pythagorean a Hva).
  pose proof (dist_sq_nonneg (arc_center a) (chord_midpoint a)).
  lra.
Qed.

(* Refined sagitta inner under the Pythagorean identity.
   When valid_arc a, the Rmax 0 in sagitta_sq_inner doesn't trigger:
   sagitta_sq_inner a = arc_radius_sq a - chord_half_length_sq a
                       = dist_sq (arc_center) (chord_midpoint).
   This pins down the exact perpendicular distance squared. *)
Lemma sagitta_sq_inner_eq_centerline_sq :
  forall a : CircularArc,
    valid_arc a ->
    sagitta_sq_inner a = dist_sq (arc_center a) (chord_midpoint a).
Proof.
  intros a Hva. unfold sagitta_sq_inner.
  pose proof (arc_radius_sq_pythagorean a Hva) as Hpy.
  rewrite Rmax_right.
  - lra.
  - pose proof (dist_sq_nonneg (arc_center a) (chord_midpoint a)). lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6c  What remains after this session.                                      *)
(*                                                                            *)
(* The prompt-suggested `arc_mid_within_sagitta` (Chebyshev bound: arc_mid    *)
(* component-wise within sagitta of chord_midpoint) is MATHEMATICALLY FALSE   *)
(* in general for the corpus's CircularArc record: nothing in the record     *)
(* definition forces arc_mid to be the arc's apex.  arc_mid can be ANY       *)
(* point on the arc between arc_start and arc_end -- specifically a non-     *)
(* apex placement (e.g. near arc_start in a tightly-curved arc) puts         *)
(* arc_mid far from chord_midpoint despite still being on the circle.        *)
(*                                                                            *)
(* What IS true:                                                              *)
(*   - sagitta IS the maximum perpendicular distance from the chord to any   *)
(*     point on the arc.                                                      *)
(*   - The PERPENDICULAR component of (arc_mid - chord_midpoint) is at most  *)
(*     sagitta.                                                                *)
(*   - The Chebyshev / L^infinity bound on (arc_mid - chord_midpoint) does   *)
(*     NOT hold in general.                                                    *)
(*                                                                            *)
(* For Phase 4's `chord_approx_error_bound` headline this means the right    *)
(* witness construction for a chord-approximated point P is the              *)
(* PERPENDICULAR PROJECTION of P onto the arc, NOT arc_mid itself.  That     *)
(* projection is the closest arc point to P, and IS within sagitta of P      *)
(* perpendicular-wise.  Formalising the projection requires the perpendicular *)
(* foot of P on the chord-orthogonal direction -- another small geometry     *)
(* session.  Deferred.                                                         *)
(*                                                                            *)
(* Also deferred: the n-chord (n >= 2) refinement of chord_approx_arc with   *)
(* the sagitta-scaled by sub-arc decomposition.  Currently chord_approx_arc  *)
(* is the degenerate 3-point stub (arc_start, arc_mid, arc_end); the         *)
(* n-chord trigonometric version needs sin/cos manipulation.                  *)
(*                                                                            *)
(* [2026-06-12] The trigonometric per-sub-arc half of this deferral is        *)
(* closed: ArcChordDensity.v (chord-budget law) + ArcChordSubdivision.v       *)
(* (angle-budget discharge, equal_angle_chords_achieve_eps).  The             *)
(* list-of-arcs subdivision construction itself remains deferred.             *)
(* -------------------------------------------------------------------------- *)

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
Print Assumptions median_length_formula.
Print Assumptions arc_radius_sq_pythagorean.
Print Assumptions arc_radius_sq_ge_chord_half_length_sq.
Print Assumptions sagitta_sq_inner_eq_centerline_sq.
