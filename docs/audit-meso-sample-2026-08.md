<!-- doc-kind: finding
date: 2026-08-02
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Meso module-health audit — 13-module sample (seed=42)

**Status.** Written 2026-08-02.  First instantiation of the meso-level
audit posture from `docs/macro-meso-micro.md` ("Auditors sample modules
(meso), not every lemma").  Sample frame: seeded draw (seed=42) over the
registered-module list, stratified as *all critical* + *≤4 audit
exceptions* + *1 giant* + fill to ~12; the draw returned 10 critical
`theories/` modules and 3 high-risk Category-C `theories-flocq/`
modules.  "Claims" below = top-level declarations
(`Definition|Lemma|Theorem|Corollary|...`); "PA" = in-file
`Print Assumptions` footers (the unit `scripts/audit_axioms.sh`
actually audits).  Methodology: per-module structural read + grep
census (Admitted/Axiom/Parameter/admit), reverse-dependency scan via
`rocq dep -f _CoqProject.full`, cross-check against
`docs/verified-claims.md` and `docs/audit-exceptions.txt`.

**Question.** Beyond the CI-enforced hard invariants (Qed-clean, no
Axiom/Parameter, allowlist + exceptions), do the sampled modules meet
the corpus's hygiene norms — live headers, top-hoisted imports, PA
observability, claims-ledger coverage, tractable size?

## Findings

Hard invariants hold everywhere in the sample: **zero**
`Admitted`/`admit.`/`Axiom`/`Parameter` across all 13 modules (every
grep hit is header prose asserting the absence).  The debt found is
observability and hygiene, not proof gaps.

| Module | Lines | Claims | PA | Claims rows | Verdict |
|---|---|---|---|---|---|
| `theories/RelateNodingLineLine.v` | 2564 | 198 | 46 | 53 | Healthy giant — no action.  20 numbered § banners; seam §13/§14 (line ~1112, segment-pair vs collection layers) recorded for posterity; 3 reverse deps. |
| `theories/CornerCorridorBridge.v` | 2144 | 114 | 31 | **0** | Size-debt + coverage-debt.  Ambiguous duplicated §-numbering; lines ~1643–2110 are a self-contained 467-line numeric worked example → extraction candidate (B2); zero claims rows → renames unpoliced (B5). |
| `theories/RelateNG.v` | 1768 | 106 | 10 | 17 | Hygiene-debt — **fixed this session**: dead stubs `geom_de9im := True` (a `True`-valued marker predicate nothing concluded in), `dim_of_stratum_pair` (all branches `None`), `line_endpoint_boundary_cell` retired; header synced.  Lowest PA-to-claims ratio in the sample; triangle/rect layers interleave → untangle (B6) is prerequisite to any split.  *Superseded later in 2026-08: split executed into six layered modules (Core / Contains / Touch / TouchRED / TouchCells / Rect) with `RelateNG.v` kept as a re-export umbrella (the one reverse dep, `RelatePrepared.v`, imports unchanged); the B6 untangle was executed by the Core layout — rect lane before triangle lane.* |
| `theories/RelateCurveMatrix.v` | 646 | 53 | 18 | 4 | Hygiene-debt — **fixed this session**: mid-file `Require Import` (line 532) hoisted to the top import block. |
| `theories/CurveRingOffset.v` | 460 | 29 | 7 | 5 | **Stability freeze.**  17 reverse deps — highest blast radius in the sample.  No refactor without a dedicated dep-graph deliverable.  (Freeze recorded here, not as a `.v` comment: a comment-only edit would force a 17-dep recompile.) |
| `theories/InDisk.v` | 287 | 27 | 7 | 1 | Healthy; host-lane promotion candidate (B3). |
| `theories/InArc.v` | 255 | 26 | 2 | **0** | Coverage-debt: zero claims rows (B5).  atan-lineage exception status correct as-is. |
| `theories/CompoundCurveCurvature.v` | 410 | 23 | 7 | 4 | Healthy leaf (no reverse deps); host-lane candidate (B3). |
| `theories/CompoundCurveAssembly.v` | 342 | 14 | 7 | 4 | Healthy leaf; host-lane candidate (B3). |
| `theories/DelaunayFlipWitness.v` | 116 | 8 | 2 | 2 | Healthy — smallest and cleanest in sample; host-lane candidate (B3). |
| `theories-flocq/HotPixel_b64.v` | 2597 | 97 | 45 | 2 | Observability-debt (45/97 PA); split **BLOCKED** — 21 reverse deps incl. the oracle extraction path (`Validate_binary64_extract.v`).  Exception entry gained its per-file justification this session. |
| `theories-flocq/PassesThrough_b64_grid_exact.v` | 1819 | 79 | **0** | 20 | **Worst observability in the corpus**: zero in-file PA footers, so its `audit-exceptions.txt` exemption covers no PA blocks at all — the audit is a no-op for this file (B1 is the fix).  Exception entry updated this session to the Slice-18 state with the gap recorded.  Slices 12–13 are 3-axiom `[exact]` → extraction candidate to *leave* the exceptions list (B4). |
| `theories-flocq/InCircle_b64_exact.v` | 1146 | 77 | 8 | 4 | Observability-debt (8/77 PA) — B1 scope.  Structure fine at this size. |

**Fixed this session** (same branch as this document):

- `theories/RelateNG.v` — tombstone stubs retired, header synced
  (idiom: c51c7f7 "Staleness sweep: retire tombstone stubs").
- `theories/RelateCurveMatrix.v` — mid-file import hoisted ("thin
  imports" idiom).  Both rebuilt green with their full reverse closure
  (`RelateCurveBoundaryMeet`, `RelatePrepared`) via
  `Makefile.gen` single-target builds.
- `docs/audit-exceptions.txt` — header corrected (24 → 80 entries; the
  16-file `theories/` R-side atan lineage is now named); the
  category-c-policy reference un-stale'd ("to be written" → exists,
  Draft); `HotPixel_b64.v` got the per-file justification the file's
  own discipline requires; the `PassesThrough_b64_grid_exact.v` entry
  updated from the Slice-1 description to the Slice-18 unconditional
  close, with the zero-PA gap recorded; four entries describing
  since-discharged `Admitted` theorems reworded as historical.  The
  entry *set* is unchanged (verified by diffing the comment-stripped
  file before/after — `audit_axioms.sh` sees the identical list).
- `README.md` — module counts synced (41 host / 456 total = 382 + 74).
  Note: no guard polices these counts (`check_readme_axioms.sh` is
  axiom-block-only); candidate future guard.

## Bottom line

The corpus invariants hold at full strength in the sample — the
headline risk is **not** unsound proofs but *unaudited surface*: one
80-entry exception file whose header undercounted it by 3×, and a
79-claim exempted module contributing zero `Print Assumptions` blocks
to the audit it is exempted from.  One dead `True`-valued spec marker
(`geom_de9im`) was found and retired; it had no consumers, so nothing
claimed against it, but `check_admitted.sh` cannot catch
Definition-level vacuity — worth remembering when reviewing new
"marker" definitions.

## Next steps (maintenance queue)

| # | Item | Notes / flags |
|---|---|---|
| B1 | PA-footer backfill: `PassesThrough_b64_grid_exact.v` (0/79) first, then `InCircle_b64_exact.v` (8/77), `HotPixel_b64.v` (45/97), and the 8 other `theories-flocq/` files with no footers | **DONE 2026-08-15** (CI fix): 949/967 flocq claims have PA. Five files *not* on `audit-exceptions.txt` were left without new footers so `classic` does not leak into the allowlist log: `B64_Expansion.v`, `DelaunayEmptyCircle.v`, `HotPixelConvex_b64.v`, `Orient_b64_exact_full.v`, `PassesThrough_b64_exact_comparator.v`. Header tags on the remaining B1 priority files. See `docs/corpus-meta.md`. |
| B2 | Extract `CornerCorridorBridgeExample.v` from `CornerCorridorBridge.v` lines ~1643–2110 (self-contained `sample_*` worked example; nothing imports it back; 9 Walk* consumers untouched) | **SATISFIED BY SIDE EFFECT 2026-08-22** (verified while opening #506): `CornerCorridorBridge.v` is now 138 lines and the `sample_*` worked example lives in `theories/BaseToTipSample.v` (513 lines), extracted during the C-3e / `BaseToTipHeadline` splits. The row read open only because the *named* deliverable `CornerCorridorBridgeExample.v` never appeared. Original idiom: 6d6d4a0 "Refactor: extract MaxMinScore.v, one source". |
| B3 | Host-lane promotion of `InDisk`, `DelaunayFlipWitness`, `CompoundCurveCurvature`, `CompoundCurveAssembly` (+ whatever their `rocq dep` closure needs, e.g. `Overlay`, `CurveGeometry`, `ArcOrient`, `CompoundCurveKoc`) into `_CoqProject` | Brings 4 sampled modules into the fast `make ci-pr` loop; closure check required first. |
| B4 | Extract `PassesThrough_b64_grid_exact.v` slices 12–13 (lines ~1204–1315; 3-axiom `[exact]`, no classic) into a pure-R module that can **leave** `audit-exceptions.txt` | **DONE 2026-08-15** (user/BDFL-directed, discharging the §10-pause ack) — executed at the split: the monolith is now five layered modules + the `PassesThrough_b64_grid_exact.v` re-export umbrella; slices 12–13 live in `PassesThrough_b64_grid_gap_kernel.v`, verified classic-free in its PA output and NOT on `audit-exceptions.txt` (the four tainted siblings inherit the exemption).  R-side extraction only — the parametric b64 refactor stays paused per `docs/category-c-policy.md` §10. |
| B5 | Add `docs/verified-claims.md` rows for `CornerCorridorBridge` and `InArc` headlines | **UNBLOCKED 2026-08-22**: the B2 extraction it waited on has happened, so rows can no longer orphan. Both are still at **0** rows. Same class of gap as #503 (a Qed artefact with no claims row, invisible because `validate-claims.sh` only checks claims → source); consider landing them together. |
| B6 | RelateNG triangle/rect untangle (`rect_pair_regime` at line ~436 sits inside the triangle block) | **DONE 2026-08-15** — executed at the split: `RelateNGCore.v` orders the rect lane (extractor + regime + wrapper) before the triangle lane; the triangle lemma stack lives in `RelateNGContains/Touch/TouchRED/TouchCells`, the rect lemma stack in `RelateNGRect`; `RelateNG.v` is the re-export umbrella. |
| — | `HotPixel_b64.v` split: **blocked** (21-dep blast radius incl. oracle path).  `RelateNodingLineLine.v` split: deferred indefinitely (healthiest giant) — *superseded later in 2026-08: split executed at maintainer request into six layered modules along the recorded §13/§14 seam, with `RelateNodingLineLine.v` kept as a re-export umbrella so the 3 reverse deps import unchanged.*  `CurveRingOffset.v`: frozen.  Category-C policy decision: BDFL-blocked (`docs/category-c-policy.md` §7/§10). | Recorded to prevent re-litigating. |

## References

- `docs/macro-meso-micro.md` (the meso audit posture this instantiates)
- `docs/guard-discharge-audit.md` (deliverable format model)
- `docs/category-c-policy.md` (Draft; §6 C1 limit, §10 cadence pause)
- `docs/audit-exceptions.txt`, `docs/axiom-allowlist.txt`,
  `docs/verified-claims.md`
- Precedent commits: c51c7f7 (staleness sweep), 6d6d4a0 (extract one
  source), 659146b / 052d0be / 53b2f84 (PA footer sync),
  ca79edb (RelateNodingLineLine parametric-core refactor)
