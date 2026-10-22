(* ============================================================================
   NetTopologySuite.Proofs.CurveRingWindFixtures
   ----------------------------------------------------------------------------
   Lane D, fixtures only.  Exact winding numbers of five sample rings and
   probes, projected from the CurveRingWinding W1 lemmas: locked_rect and
   locked_lens wind 1, the grazing diamond winds -1 at both probes, and the
   two clockwise circle halves wind -1 at the centre.
   Samples, not a theorem about rings in general: local constancy of the
   winding number and the convex-ring classification are not stated here.
   Winding numbers, not a ray-cast crossing count.  Does not flip
   RNG_JordanUncond.  Imports CurveRingWinding; does not edit it.
   3-axiom host lane.  No Admitted.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted (Cursor Grok 4.7), human-reviewed.
   ========================================================================== *)
From Stdlib Require Import Reals.
From NTS.Proofs Require Import CurveRingWinding.
Local Open Scope R_scope.

Theorem curve_ring_wind_fixtures :
  wind rect_probe locked_rect = 1 /\
  wind lens_probe locked_lens = 1 /\
  wind graz_B grazing_diamond = -1 /\
  wind graz_A grazing_diamond = -1 /\
  wind cw_centre cw_circle_halves = -1.
Proof.
  split; [exact (proj2 (proj2 (proj2 locked_rect_wind_one))) |].
  split; [exact (proj2 (proj2 (proj2 (proj2 locked_lens_wind_one)))) |].
  split; [exact (proj1 grazing_diamond_wind_neg_one) |].
  split; [exact (proj2 grazing_diamond_wind_neg_one) |].
  exact (proj2 (proj2 (proj2 cw_halves_wind_neg_one))).
Qed.

Print Assumptions curve_ring_wind_fixtures.
