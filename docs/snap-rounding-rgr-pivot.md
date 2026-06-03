# Snap-rounding passes-through: RGR pivot on risk/cost

**Status.** Written 2026-06-03 (issue #66, the snap-rounding / passes-through
thread). The Red–Green–Refactor cycle on the **rounded compute filter**
(`b64_passes_through_hot_pixel_compute` / `_halfopen_compute`) has reached its
natural end: the RED is exhaustively machine-checked, the only remaining
"rehabilitate the rounded filter" target (C2) is **blocked**, and the GREEN
that actually matters lives on the **exact R-spec**, not the rounded filter.
This document records the risk/cost reasoning and the pivot — same shape as
[`soundness-strategy.md`](soundness-strategy.md)'s Path 1 / Path 2 split: the
choice is effort-vs-coverage, not correctness.

## Where the RGR cycle stands

**RED — the rounded compute filter is unfit as a noder primitive (all `Qed`).**
Three independent defects, each a machine-checked existential witness:

| defect | theorem | direction |
|---|---|---|
| over-accepts (unsound vs exact geometry) | `PassesThrough_b64_compute_unsound.v : b64_passes_through_compute_unsound` | `compute=true`, `spec=false` |
| under-accepts (incomplete — *drops* a pass) | `PassesThroughHalfopen_b64_compute_incomplete.v : b64_passes_through_halfopen_compute_incomplete` | `spec=true`, `compute=false` |
| order-dependent (asymmetric under reversal) | `PassesThrough_b64_compute_asymmetric.v : b64_passes_through_compute_asymmetric` (+ `_halfopen_`) | `compute P0 P1 C ≠ compute P1 P0 C` |

Together they pin the rounded filter as simultaneously unsound, incomplete, and
order-dependent — the order-dependence being the documented root behind
JTS#752 / JTS#1133 (a floating snap-rounding noder visiting the same edge with
swapped endpoints gets contradictory verdicts → inconsistent graph →
`TopologyException` / dropped ring).

**GREEN — the exact R-spec `b64_passes_through_hot_pixel` already has the
properties a noder primitive needs (all `Qed` except where noted).**

| property | theorem |
|---|---|
| sound vs the closed hot pixel | `HotPixel_b64.v : b64_passes_through_sound` |
| complete vs the half-open pixel | `HotPixel_b64.v : b64_passes_through_complete` |
| symmetric under segment reversal | `b64_passes_through_hot_pixel_symmetric` — **in flight, PR #73** (not yet on `main`) |
| snapping preserves which pixels are passed | `SnapRounding_b64.v : b64_snap_round_preserves_passes_through` |
| precision-reducer idempotence (bit-level) | `SnapRounding_b64.v : b64_snap_idempotent_finite` |
| shared pixel preserved under snap | `TopologicalCorrectness_b64.v : b64_snap_round_preserves_shared_hot_pixel` |

**OPEN — two directions named in `oracle-soundness-finding.md`:**

- **C1 — grid exactness.** `compute ≡ spec` (bit-equal booleans) for integer /
  half-integer coordinates. Strongly evidenced: 0 divergence in 5,000,000
  on-grid cases. **Not yet proven.** Supporting machinery exists
  (`HotPixel_b64.v : snap_round_on_grid`).
- **C2 — completeness of the *rounded* filter** (`spec ⇒ compute`, general
  binary64). Strongly evidenced (0 violations in 18M + 217,728 adversarial),
  but the proof is **blocked**: the goal reduces to showing the
  round-to-nearest errors in the divide-and-clip `t`-bounds never align to flip
  the composite `tmin ≤ tmax` comparison inward. Monotonicity / forward-error
  cannot discharge it (round-to-nearest gives no outward guarantee); it needs a
  computation-specific argument, or a ~2⁻¹⁰⁴ counterexample search.

## Risk/cost of the candidate next targets

| target | value | risk (tractability) | cost |
|---|---|---|---|
| **C2** — rehabilitate the rounded filter (completeness, general b64) | medium — would let a caller trust the rounded filter's "never drop" | **high** — blocked; needs a deep computation-specific proof, may be effectively intractable | high, uncertain |
| **C1** — grid exactness (`compute ≡ spec` on the grid) | **high** — recovers **soundness in the post-snap regime**: snap-rounding puts every coordinate on the grid, so on-grid exactness closes the constructive arc "rounded filter unsound off-grid (RED) ∧ exact on-grid (C1) ∧ snap ⇒ on-grid ⟹ the noder is sound" | low–medium — regime-restriction in the proven style of `soundness-strategy.md` Path 2 (bit-exactness in a regime), strongly evidenced | medium, multi-session but bounded |
| **Exact-spec primitive consolidation** | high — states the shipped recommendation: *the certified noder primitive is the exact R-spec, not the rounded filter* | low — synthesis of existing `Qed` results | low (this doc + PR #73 landing) |
| broaden to OverlayNG / PrecisionReducer (#66's larger scope) | high — the headline soundness goal | medium–high — large new theory | very high |

## Decision

1. **STOP chasing C2.** Rehabilitating the rounded filter is the
   highest-risk / lowest-marginal-value square. Demote it to a *useful,
   strongly-evidenced open obligation* — exactly as `soundness-strategy.md`
   demoted the Shewchuk forward-error attempt (Path 1) from critical path to
   useful primitive. It is not deleted or disproved; it is parked. No
   `Admitted` enters the corpus on its account.

2. **PIVOT to the exact R-spec as the certified noder primitive.** The RED is
   complete and the exact-spec GREEN is nearly complete; the remaining
   sound-but-unshipped step is **C1 grid exactness**, which converts the RED's
   "unsound off-grid" into a constructive **"sound on the snap grid"** — the
   regime a snap-rounding noder actually operates in. C1 is the
   recommended next proof investment: best value/risk among the proof targets
   and consistent with the project's shipped Path-2 precedent.

3. **Defer OverlayNG / PrecisionReducer.** It is the right long-horizon #66
   target but a separate, much larger engagement; it should not start before
   the passes-through primitive is closed (it depends on a trustworthy
   passes-through verdict).

### Why this is the risk/cost-optimal pivot

C2 and C1 are *both* "strongly evidenced, unproven", but they are not equal
bets. C2's blocker is a no-outward-guarantee rounding argument with no known
handle — high chance the effort yields nothing shippable. C1's path is the same
integer/dyadic exactness reasoning already shipped for orientation
(`Orient_b64_exact.v`, Path 2) and for snap idempotence
(`b64_snap_idempotent_finite`): a regime where the relevant quantities are
exactly representable so the rounded and exact decisions coincide. Same
evidence weight, far lower execution risk — and C1 delivers the *soundness*
headline (in-regime) that C2 cannot.

## Future paths left open

- **C1 → in-regime soundness corollary.** Once `compute ≡ spec` on the grid is
  `Qed`, compose with `b64_passes_through_sound` to state "the rounded filter is
  sound for on-grid (snapped) inputs" — the directly useful noder guarantee.
- **C2** remains available for anyone who wants the general-b64 completeness;
  the 18M + 217k evidence and the precise blocker are recorded in
  `oracle-soundness-finding.md`.
- **OverlayNG / PrecisionReducer** (#66 headline) builds on the closed
  passes-through primitive.

The corpus invariant — no `Admitted`, no `Axiom`, no `Parameter` beyond the
recorded classical-reals allowlist — holds throughout and is preserved by this
pivot.
