# GEOS ↔ Rocq oracle differential hunt

Gates GEOS curve / predicate behaviour against NetTopologySuite.Proofs `oracle_bin`.

## Requirements

- `geosop` (GEOS build, e.g. WSL `/home/user/geos-build/bin/geosop`)
- `oracle_bin` Linux CI artifact under `.ci-artifacts/oracle-bin-linux/`

## Run

Full hunt is **local-only** (needs `geosop` + `oracle_bin`). The three
PR jobs (corpus guardrails / Rocq 9.2.0 / theories-flocq) do not invoke
`CurveOracleBugHunt`. The no-oracle REL selfcheck is in `make ci-guards`.

```bash
# no oracle, no geosop — token allowlist + result-cell `?` (#575 / 522-f, #604 / 523-b)
python3 hunt.py --selfcheck

export GEOSOP=/path/to/geosop
export ORACLE=/path/to/oracle_bin
python3 hunt.py
```

## Surfaces

| Tag | Oracle / pin |
|---|---|
| LEN/* | `ARC_LENGTH` |
| DIST/* | `ARC_DISTANCE` |
| ENV/* | arc extrema |
| AREA/* | `ARC_AREA` / π |
| PIP/* | `POINT_IN_CURVE_RING` |
| COVERS968/* | GEOS #968 |
| SPLIT1497/* | GEOS #1497 / #1500 |
| MS/* | MultiSurface A/P (#1502) |
| REL/* | `RELATE_MATRIX` token allowlist + triangle fill pins (#575 / 522-f) and result-cell `?` (`is_valid_de9im_result`; #604 / 523-b). A decline is `UNSUPPORTED`, not a parse error. A 9-char with `?` is a matrix, not a third kind. Catalog lookup stays F/0/1/2. The #530 pair is the disjoint pin, not the decline. Does not remint fills. No GEOS matrix compare (classifier pins ≠ OGC). |

See `docs/geos-oracle-rung-2026-08.md`.
