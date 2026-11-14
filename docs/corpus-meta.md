<!-- doc-kind: guide -->
# Corpus metadata (source of record)

> Generated 2026-08-15 from dashboard field snapshot + in-tree PA backfill (B1).
> Dashboard and Observatory must cite these numbers, not the other way around.

topic: docs
claimId: none
witness: none

## Snapshot

| Key | Value |
|---|---|
| Field / live head | `3055cb7` |
| Modules (`.v`) | 487 |
| Statements (all Gallina) | 7,792 |
| Theorems / lemmas / corollaries | 5,803 |
| Definitions | 1,843 |
| Docs (`.md`) | 158 |

## Macro domains

| Domain | Modules | Statements | Share |
|---|---:|---:|---:|
| `other` | 181 | 2544 | 32.6% |
| `binary64` | 76 | 1430 | 18.4% |
| `relate` | 48 | 1072 | 13.8% |
| `arc` | 71 | 911 | 11.7% |
| `overlay` | 32 | 508 | 6.5% |
| `core` | 8 | 289 | 3.7% |
| `mesh` | 16 | 246 | 3.2% |
| `noding` | 10 | 238 | 3.1% |
| `buffer` | 23 | 234 | 3.0% |
| `convexity` | 10 | 136 | 1.7% |
| `coverage` | 2 | 70 | 0.9% |
| `metric` | 5 | 68 | 0.9% |
| `hull` | 1 | 26 | 0.3% |
| `docs` | 4 | 20 | 0.3% |

Shares sum to 100% of `7,792` statements.

## Machine tags

PR bodies and new `.v` headers carry three plain lines (no backticks):

```
topic: <meso-id>
claimId: <board-subtask or none>
witness: <tag or none>
```

Allowed `topic:` ids: `relate`, `binary64`, `arc`, `overlay`, `buffer`, `koc`,
`precision`, `mesh`, `metric`, `hull`, `coverage`, `noding`, `convexity`,
`docs`, `teaching`, `core`.

## B1 — Print Assumptions footer backfill

`docs/audit-meso-sample-2026-08.md` item B1. Every
`Theorem`/`Lemma`/`Corollary`/`Proposition`/`Fact` in `theories-flocq/` that
lives on `docs/audit-exceptions.txt` now has a matching `Print Assumptions`
line (949/967). Five non-excepted files were left without new footers so
`classic` does not leak into the allowlist log.

| | Before | After |
|---|---:|---:|
| flocq claim names | 967 | 967 |
| names with PA footer | (incomplete) | 949 |

Priority files from B1 (also tagged in-header):

- `PassesThrough_b64_grid_exact.v` — was 0 PA
- `InCircle_b64_exact.v` — was 8/77
- `HotPixel_b64.v` — was 45/97
- plus every other excepted `theories-flocq/*.v` that had a gap

Left without new footers (not on the exception list):
`B64_Expansion.v`, `DelaunayEmptyCircle.v`, `HotPixelConvex_b64.v`,
`Orient_b64_exact_full.v`, `PassesThrough_b64_exact_comparator.v`.

These files remain on `docs/audit-exceptions.txt` (Category C / classic via
Flocq). The footers make the exemption *cover* actual PA blocks.

## Require graph

Dashboard `require-graph.json` is derived from `From NTS.Proofs Require
Import|Export`. `EdgeFaceBridge.v` re-exports Incidence / TwinPath / Barrier /
Capstone — blast cones must follow Export, not only Import.
