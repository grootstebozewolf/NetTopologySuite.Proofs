<!-- doc-kind: finding
date: 2026-08-22
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Retire #66 — precision models, snap rounding, OverlayNG

**Type:** grilling · **Map:** [Retire the epic block #64–#69](../../map-epic-block-64-69.md)
**Blocked by:** — · **Closed:** 2026-08-22

## Question

#66 (Urgent) asks for precision models, snap-rounding and OverlayNG/relate
soundness. The audit reads **MOSTLY**: six of eight asks satisfied and holding.
Does it close, and where does its residue go?

Satisfied (verify then cite): C1 grid-exactness
(`PassesThrough_b64_grid_exact.v`, now five layered modules plus umbrella),
snap-rounding idempotence (`SnapRounding_b64.v`), boolean overlay semantics
(`Overlay.v`, `OverlayGraph.v`), Euler hypotheses discharged
(`OverlayBridgeUnconditional.v : extract_rings_valid_of_guards`,
`_holes_of_guards`), `RingArea979.v` plus `HOLE_PRECISION_AUDIT` /
`HOLES_SURVIVE_PRECISION`, and `CURVE_SNAP_DECISION` /
`CURVE_SNAP_INVARIANTS_EXACT` in the oracle.

Note the interesting one: the body's remaining item 3 (guard-discharge audit)
**is delivered**, as `docs/guard-discharge-audit.md`, and it is an honest
*negative* — none of the five guards are free corollaries of snap-rounding, guard
4 is refuted outright by
`theories-flocq/SnapRoundingGuardAudit.v : snap_can_introduce_horizontal_dart`.
A delivered negative still satisfies the ask; say so explicitly in the closure
comment so it is not mistaken for unfinished work.

Residue to place:

1. **C1 width extension to 2²⁵** (`PassesThrough_b64_grid_exact.v:69-75`,
   `audit-rgr-comparison.md` P6) — needs exact integer-determinant comparison;
   survived a 1.7M-trial sweep but is UNPROVEN (`verified-claims.md:265`).
2. Unconditional OverlayNG headline (`OverlayCorrectness.v`, three named
   hypotheses).
3. The guard bridge from the noder's `fully_intersected` to
   `noded_general_position`, plus guards 2 and 5 (uninvestigated).
4. C2 off-grid completeness — **parked by decision**; would be stale as an issue.
5. Arc Hobby analog — a research gap with no published true statement to aim at.

Items 4 and 5 are the reason this ticket is a grilling and not a task: filing them
as issues would misrepresent a decision and a genuine unknown as backlog.

## Resolution

**Closed 2026-08-22. #66 closed; four scoped successors (#517–#520); three
documentation corrections into #503; ADR-0002 amended with a third park kind.**

**The park taxonomy gained its missing category — and my own question was
mis-framed.** I proposed a *value park* for C2. The evidence says otherwise: C2
has a written Coq statement (`b64_passes_through_complete_compute`), zero
violations across 36,864 exhaustive + 217,728 ULP-band + 18M random trials, and a
**named technical blocker** — round-to-nearest gives no outward guarantee, so
`b64_le_complete`'s hypothesis is exactly what monotonicity cannot supply
(`docs/oracle-soundness-finding.md:117-171`). Nothing unblocks it and a statement
exists, so it is neither sequencing nor research. ADR-0002 now classifies parks by
**what is missing** — a gate, a statement, or a **proof method** — with value and
priority orthogonal. #66's body calls C2 *"high risk, low marginal value"*; the
soundness doc calls it *"proof BLOCKED"*. Only the second says what would move it.

The **arc-Hobby analog** is confirmed the genuine research park: *"no published
true statement"*, verbatim in five places, and ADR-0002's own calibration point.

**My residue list was stale for the fourth consecutive ticket:**

| Ticket said | Actually |
|---|---|
| Guard 2 uninvestigated | **`EulerSameFaceStep.v:87 no_spurs_of_min_degree_2` is Qed** — reduces guard 2 to `min_degree_2` plus bookkeeping. Struck. |
| C1 width needs "exact integer-determinant comparison" | That comparator, `PassesThrough_b64_exact_comparator.v:118 rat_le_iff`, is **already Qed**. The residue is a **rounding-tie-freeness** lemma on the Liang-Barsky quotient family — a nameable 1–2 session target. |
| Status at `PassesThrough_b64_grid_exact.v:69-75` | Stale line reference; the 2026-08-15 split moved the live obligation note to `PassesThrough_b64_grid_separation.v:530-538`. |

**One ✅ in #66's own table over-reads.** `theories/Overlay.v` contains **no
`Theorem`** — only definitions and a boolean-lattice fragment. "OverlayNG boolean
semantics proven" therefore means semantics-as-*definition* plus
graph-construction validity, not algorithm soundness. That lives only in the
conditional headline (#520).

**Three documentation corrections, two widening the truth**, folded into #503:
`verified-claims.md:175` says `2²³` where the theorem is `2²²` (row `:184` is
right — internal inconsistency); `verified-claims.md:263`'s *"every hypothesis is
a code-aligned invariant"* is refuted by the Qed
`snap_can_introduce_horizontal_dart`; and `READING-GUIDE.md:648`'s unqualified
*"CLOSED … no Euler hypotheses anywhere in the lane"* omits that all six
replacement guards are undischarged for real noded output. The first suggests a
new mechanical rule (numeric regime in prose must match the cited theorem's own
bound predicate); the second explicitly **cannot** be mechanised, which is the
argument for keeping #503's human-review half explicit.

**Two unproven surfaces in a lane whose ask was proof**, recorded on the closure:
`CURVE_SNAP_DECISION` has no Coq companion at all, and `SNAP_SCALED` accepts
arbitrary scales while its backing theorem holds only for powers of two.

**Deliberately kept together rather than split**: the four successors are not
independent. H1 in #520 is the *same* general-`ring_simple` JCT residual that
gates #515's Minkowski bridge, and #518's ownerless bridge unblocks guards 1 and 3
together. Splitting further would hide one frontier with shared blockers — the
mistake #510 exists to avoid on the arc side.
