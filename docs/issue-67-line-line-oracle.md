# Issue #67 — Romanschek line–line DE-9IM oracle (S3 seed)

> **Status:** predicate pins landed in `RelateLineLine.v`; vector file for future
> `RELATE_MATRIX` oracle mode. Branch: `claude/issue-67-relate-line-line`.

## Source

Romanschek, Clemen, Huhnt — [*A Novel Robust Approach for Computing DE-9IM
Matrices Based on Space Partition and Integer Coordinates*](https://doi.org/10.3390/ijgi10110715),
ISPRS IJGI 2021. Reference implementation and WKT fixtures:
[dd-bim/topology-relations](https://github.com/dd-bim/topology-relations).

At test extent `r_max ≤ 1056`, their matrices match **NTS 2.3.0**
`Geometry.Relate(a,b).ToString()` on the line–line pairs below.

## Corpus wiring

| Artifact | Role |
|----------|------|
| `theories/RelateLineLine.v` | `ll_matrix_paper_test6` … `test13` + predicate lemmas |
| `oracle/de9im_line_line_vectors.txt` | WKT pairs, 9-char matrix, Coq name, notes |
| `oracle/gen_de9im_line_line_vectors.sh` | Cat helper (static until `RELATE_MATRIX` exists) |
| `docs/verified-claims.md` | Citable predicate lemmas |

## Test map (Table 5 line–line)

| Test | Matrix | S2 witness | Predicate footprint (`DE9IM.v`) |
|------|--------|------------|----------------------------------|
| 6 | `FF1FF0102` | `ll_matrix_point_ii` (cells differ) | `intersects`; not `crosses_ll` |
| 7 | `1FFF0FFF2` | `ll_matrix_overlap_ii` (EE differs) | `intersects`, `overlaps` |
| 8 | `101FF0FF2` | — | `intersects` only |
| 9 | `101F00FF2` | — | `intersects`, `overlaps` |
| 10 | `FF10F0102` | `ll_matrix_disjoint` (predicate differs) | `intersects`; not `disjoint` |
| 13 | `0F1FF0102` | `ll_matrix_point_ii` (II matches) | `intersects`, `crosses` |

**Headline tension (test 6 vs 13):** both are crossing segments; partition/NTS
stores test 6 with **II=F** (intersection in IE/EI/BE/EB), while test 13 has
**II=0** (classic `pat_crosses_ll`). S2 `segments_proper_cross` still soundly
maps to the minimal witness `0FFFFFFFF`, not to the computed `FF1FF0102`.

## Next steps (S3+)

1. **JTS#1175** boundary-endpoint witness (triage milestone S3) — add alongside
   Romanschek tests in `oracle/de9im_line_line_vectors.txt`.
2. **`RELATE_MATRIX` oracle mode** in `oracle/driver.ml` — NTS/JTS string compare
   against pinned matrices; follow `INCIRCLE_SIGN` extraction pattern.
3. Optional: WKT→segment geometry in Coq for test 6/13 showing both satisfy
   `segments_proper_cross` (float carrier, separate from matrix fill).