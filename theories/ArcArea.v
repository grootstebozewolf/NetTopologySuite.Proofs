(* ============================================================================
   NetTopologySuite.Proofs.ArcArea
   ----------------------------------------------------------------------------
   Option-A arc primitives (issue #64 / JTS curve-awareness M-AREA-CP): the area
   of a circular SEGMENT, the proof companion of the long-standing oracle
   ARC_AREA mode (which until now had none).

     segment_area r theta := r^2/2 * (theta - sin theta)

   This is sector area (r^2/2 * theta) minus the triangle (r^2/2 * sin theta) --
   the closed-form curved-polygon-area contribution (Green's theorem) the JTS
   CurvePolygon area sums per arc.  Headlines:

     - `segment_area_sector_minus_triangle` : the sector - triangle decomposition.
     - `segment_area_nonneg`  : `0 <= theta -> 0 <= segment_area r theta`
       (via `ArcLength.sin_le_x`: sin theta <= theta, so theta - sin theta >= 0).
     - `segment_area_half_disc` : at `theta = PI`, area = `PI*r^2/2` (a half disc).
     - `segment_area_full_disc` : at `theta = 2*PI`, area = `PI*r^2` (the whole disc).

   Stated over `(r, theta)` abstractly (no atan2).  `segment_area_nonneg` uses
   Stdlib `sin_lt_x` (via `ArcLength.sin_le_x`) which pulls `Classical_Prop.classic`,
   so the file is 4-axiom, same lineage as `ArcLength.v` (`docs/audit-exceptions.txt`).
   No `Admitted`/`Axiom`/`Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (claude-opus-4-8)
   ========================================================================== *)

Require Import Reals Lra.
From NTS.Proofs Require Import ArcLength.
Local Open Scope R_scope.

(* Area of the circular segment of radius r subtending central angle theta. *)
Definition segment_area (r theta : R) : R :=
  r * r / 2 * (theta - sin theta).

(* Sector minus triangle: (r^2/2) theta - (r^2/2) sin theta. *)
Lemma segment_area_sector_minus_triangle :
  forall r theta,
    segment_area r theta = r * r / 2 * theta - r * r / 2 * sin theta.
Proof. intros r theta. unfold segment_area. field. Qed.

(* The segment area is nonnegative for a forward sweep (theta - sin theta >= 0). *)
Lemma segment_area_nonneg :
  forall r theta, 0 <= theta -> 0 <= segment_area r theta.
Proof.
  intros r theta Ht. unfold segment_area.
  pose proof (sin_le_x theta Ht) as Hs.
  nra.
Qed.

(* Helper: sin (2*PI) = 0, via the double-angle identity and sin PI = 0. *)
Lemma sin_2PI : sin (2 * PI) = 0.
Proof. rewrite sin_2a, sin_PI. ring. Qed.

(* Semicircle (theta = PI): the segment is a half disc, area PI*r^2/2. *)
Lemma segment_area_half_disc :
  forall r, segment_area r PI = PI * (r * r) / 2.
Proof. intros r. unfold segment_area. rewrite sin_PI. field. Qed.

(* Full turn (theta = 2*PI): the segment is the whole disc, area PI*r^2. *)
Lemma segment_area_full_disc :
  forall r, segment_area r (2 * PI) = PI * (r * r).
Proof. intros r. unfold segment_area. rewrite sin_2PI. field. Qed.

Print Assumptions segment_area_sector_minus_triangle.
Print Assumptions segment_area_nonneg.
Print Assumptions segment_area_half_disc.
Print Assumptions segment_area_full_disc.
