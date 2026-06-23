# DISTANCE cluster increment (2026-06)

Axis chosen: DISTANCE cluster (max surface / min new geometry among the three candidates).

## What landed (truthful summary after verification)
- Added two thin, proved "selection preserves minimum" wrapper lemmas (no new mathematics; following PR review tightening):
  - `arc_arc_external_feet_attains_when_spans_ok` in `theories/ArcArcDistance.v`
  - `arc_segment_external_foot_attains_when_span_ok` in `theories/ArcSegmentDistance.v`
  These record the contract:
    span_ok(foot) ∧ external_attains(foot, d) ∧ external_lower(d)
    ⇒ d is attained at arc points and minimal for the arc/segment pair.
  They reuse the already-Qed external theorems + the existing `arc_span_contains`.
  (The generic schema "selection_preserves_minimum" is documented in the lemma comments for future reuse.)
- No changes to the D-PT stubs themselves. Note: `point_to_arc_dist_radial_lower` and `point_to_arc_dist_centre_is_r` were already Qed (discharged 2026-06-21 via `inCircle_R_zero_implies_equidistant`); only `point_to_arc_dist_fallback_ends_lower` remains a live registered Admitted stub.
- Documentation + dashboard honesty:
  - `docs/admitted-deferred-proofs.txt`: clarifying comment added.
  - `dashboard/index.html` + `scripts/gen_dashboard.py`: fixed overstated "full" claims for Distance composites (now "partial" with accurate notes; icons driven by actual counts, not aspirational overrides).
  - `docs/distance-cluster-2026-06-increment.md`: this outcome note.
- Review feedback addressed in source: lemma names tightened, explicit contract comments added, pending `arc_orient` dependency noted.
- All guardrails (`check_admitted.sh`, etc.) + `make host` + targeted compiles pass. No new `Admitted`, no axiom drift.

## Payoff (actual)
- Explicit, proved documentation of the "foot accepted by span ⇒ use the circle core value" rule for the external regimes of AA and SL (thin selection layer, zero new geometry).
- Dashboard overstatement fixed; icons and hover text now match actual proved vs. partial/oracle state.
- Review feedback incorporated (naming, explicit contracts, dependency notes).
- Build + all guardrails green. No debt introduced.

## Remaining in cluster
- `point_to_arc_dist_fallback_ends_lower` (the monotonicity when foot outside sweep; the one live Admitted stub for D-PT).
- Full internal/overlapping regimes and crossing=0 cases (higher debt per original synthesis).

## Session shape (Red/Green/Refactor)
- Red: targets = thin selection wrappers for external cases + dashboard honesty + review tightening.
- Green: two selection lemmas landed with documented contracts; dashboard fix landed.
- Refactor: admitted comment + outcome doc updated for accuracy; dashboard regenerated.
- No new Admitteds. No axiom drift.

Next: fallback monotonicity (via arc_orient) or higher-debt work.

(Outcome paired with the synthesis choice of DISTANCE over full-relate or deferred-cleanup.)