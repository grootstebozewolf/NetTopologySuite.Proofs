# DISTANCE cluster increment (2026-06)

Axis chosen: DISTANCE cluster (max surface / min new geometry among the three candidates).

## What landed (truthful summary after verification)
- Added two thin, proved "sweep selection" wrapper lemmas (no new mathematics):
  - `arc_arc_external_feet_on_arcs_tight` in `theories/ArcArcDistance.v`
  - `arc_segment_external_foot_on_arc_and_seg_tight` in `theories/ArcSegmentDistance.v`
  These simply record "when arc_span_contains accepts the foot computed by the external core, that value is the one the oracle should emit". They reuse the already-Qed external theorems + the existing `arc_span_contains`.
- The three D-PT analytical stubs in `ArcPointDistance.v` (`point_to_arc_dist_radial_lower`, `point_to_arc_dist_fallback_ends_lower`, `point_to_arc_dist_centre_is_r`) remain live registered `Admitted.` (unchanged).
- The converse lemma `inCircle_R_equidistant_of_zero` was attempted multiple times (translation + nsatz/ring/field + cofactor extraction using the d from arc_center) but could not be closed in this pass. A comment in `ArcArcCircles.v` explicitly leaves it for the fallback monotonicity work.
- Documentation cleaned for accuracy:
  - `docs/admitted-deferred-proofs.txt`: clarifying comment only (the three entries stay live).
  - `docs/verified-claims.md`: text updated to describe only the thin wrappers.
  - `dashboard/index.html` regenerated via the official script.
- New honest outcome note (this file).
- All guardrails (`check_admitted.sh` reports 10 deferred as before, `check_readme_axioms.sh`, `validate-claims.sh`) + `make host` + targeted full-project compile of the four distance files pass cleanly. No new `Admitted`, no axiom drift.

## Payoff (actual)
- Explicit, proved documentation of the "foot accepted by span ⇒ use the circle core value" rule for the external regimes of AA and SL. This is useful for future consumers of the analytical kernels and for the oracle pin.
- Build + all guardrails green. No debt introduced.
- Honest accounting of the remaining surface (the three stubs, especially the fallback monotonicity via arc_orient, plus the converse algebra).

## Remaining in cluster (unchanged from synthesis)
- `point_to_arc_dist_fallback_ends_lower` (monotonicity when foot outside). This is the highlighted "one live" item.
- The converse for on_arc ⇒ dist O X = r (needed to cleanly discharge radial_lower + centre).
- Full internal/overlap/crossing regimes are higher debt.

## Session shape (Red/Green/Refactor)
- Red: targets = converse + two discharges + two clamp lemmas (per synthesis).
- Green: only the two thin clamp lemmas landed as proved code. Converse attempts failed to Qed; the two easy discharges were therefore left as the registered Admitteds.
- Refactor: docs + claims corrected for truthfulness; dashboard regenerated; full build + guardrails confirmed green.
- No new Admitteds. No axiom drift.

Next: the fallback monotonicity (the real cheap surface per the original analysis) or accept this as a narrow documentation increment.

(Outcome paired with the synthesis choice of DISTANCE.)