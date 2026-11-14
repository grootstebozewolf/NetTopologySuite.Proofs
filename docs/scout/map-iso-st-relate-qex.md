<!-- doc-kind: finding
date: 2026-08-31
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Map — ISO ST_Relate · QEX Ⅰ–Ⅹ

A wayfinder catalog. Charted 2026-08-31. This is **not** leftover
`Ⅰ`–`Ⅹ` from [`map-522-leftovers.md`](map-522-leftovers.md), **not**
leftover `Ⅹ` / `522-n`, and **not** a detector remint. Stacked
numerals (`Ⅰ`, `ⅠⅠ`, `ⅠⅠⅠ`, …, `Ⅹ`) number **this** suite.
`Ⅰ` and `ⅠⅠ` are the named leftovers. `ⅠⅠⅠ`–`Ⅹ` number the
unnamed parks from the leftovers chart. Ask before writing those
stacked numerals into `map-522-leftovers.md`.

ISO/IEC 13249-3 **§5.1.25** (2006) = **§5.1.45** (2016). Method
`ST_Relate`. Concepts §4.2.2 / 4.2.2.1. Field @ `f69c2c7`
(#606 / `508-a` golden quarter). Year 1 is circular. Do not start
the zoo.

PDF stays at `local/library/iso-iec-13249-3-2016.pdf` — not served.

> Closed ticket ids (`522-a` … `522-m`) stay historical. Do **not**
> mint `522-n`. Do not invent T-junction or obtuse-at-v detectors
> from this suite. Do not remint ADR-0004. This map does not mint a
> GitHub child.

topics: relate
claimId: none
witness: none

## Destination

**Name the ISO `ST_Relate` miss for leftover `Ⅰ` / leftover `Ⅱ` and
for the unnamed parks, without reminting leftover numerals or
fills.**

## ISO patterns

| Method | Pattern | Clause |
|---|---|---|
| ST_Disjoint | `FF*FF****` | §5.1.46 |
| ST_Touches | `FT******* \| F**T***** \| F***T****` | §5.1.50 |
| ST_Within | `T*F**F***` | §5.1.52 |
| ST_Contains | inverse of ST_Within | §5.1.53 |
| ST_Overlaps (areal) | `T*T***T**` | §5.1.54 |

Empty operand → **NULL** (Description 2a–2b). Invalid glyph → SQLSTATE
`2FF04`.

## Table 13 — cell values

| Glyph | Intersection set |
|---|---|
| `T` | {0,1,2} |
| `F` | {-1} |
| `0` | {0} |
| `1` | {1} |
| `2` | {2} |
| `*` | {-1,0,1,2} |

No `?`. EE of two bounded areas in R² is **2**, never F
(`RelateCurveMatrix.v : geom_de9im_ee_nonempty`).

## QEX Ⅰ–Ⅹ

| Id | Leftover | ISO matrix | Actual | Kind |
|---|---|---|---|---|
| `Ⅰ` | T-junction / partial-edge | `FF2F11212` | `UNSUPPORTED` | decline |
| `ⅠⅠ` | Obtuse-at-v | `FF2F01212` | `UNSUPPORTED` | decline |
| `ⅠⅠⅠ` | TouchEdge exclusivity | `FF2F11212` | `TPR_TouchEdge` (bar 1); exclusivity unproved | exclusivity |
| `ⅠⅠⅠⅠ` | Disjoint fill remint | `FF2FF1212` | `FFFFFFFFF` | fill-lag |
| `ⅠⅠⅠⅠⅠ` | Overlap fill remint | `212101212` | `2FFF1FFF2` | fill-lag |
| `ⅠⅠⅠⅠⅠⅠ` | Contains fill remint | `212FF1FF2` | `2FFFFFFF2` | fill-lag |
| `ⅠⅠⅠⅠⅠⅠⅠ` | Touch-edge fill remint | `FF2F11212` | `FFFF1FFF2` | fill-lag |
| `ⅠⅠⅠⅠⅠⅠⅠⅠ` | Empty / empty `ST_Relate` | `NULL` | `UNSUPPORTED` | empty |
| `ⅠⅠⅠⅠⅠⅠⅠⅠⅠ` | F vs not-computed | `F/0/1/2` only | `?` in result 9-char; catalog rejects `?`; ticket 523 stop QEX (`RelateCurveAlphabet.v : ticket_523_qed_or_qex`) | alphabet |
| `Ⅹ` | Nine-cell point-set DE-9IM | point-set Table 5 | gtri on bar-2 cells; `point_set` open | spec |

`Ⅹ` in this catalog is stacked-numeral ten (also written
`ⅠⅠⅠⅠⅠⅠⅠⅠⅠⅠ`). It is **not** leftover `Ⅹ` / `522-n`.

### `Ⅰ` · T-junction / partial-edge

- **Kind / park:** decline · research
- **ISO matrix:** `FF2F11212`
- **ISO predicate:** ST_Touches = 1 · `F***T****` (BB=T, areal touch-edge)
- **Actual:** `UNSUPPORTED` —
  `RelateNGOracleSurface.v : relate_tjunction_wire_unsupported`.
  Leftover `Ⅰ` classifies
  (`RelateNGTouchPartialEdge.v : triangle_pair_regime_touchpartial`).
  Fill stays `im_unsupported`.
- **Divergence:** ISO areal touch-edge wants II empty, BB dim-1,
  IE/EI/EE dim-2. The compiled leftover-`Ⅰ` pair is a sliver
  (II = 2, BB = 1), not a kiss. The wire is a whole-line Decline
  rather than `FF2F11212`. Honesty: do not emit a confident
  `FFFFFFFFF`.
- **Do not:** invent a second detector; steal `522-j` / `522-m`;
  bucket obtuse under leftover `Ⅰ`; mint `522-n`
- **Claim:** leftover `Ⅰ` / #609
- **A:** `POLYGON((0 0, 2 0, 0 1, 0 0))`
- **B:** `POLYGON((1 0, 3 0, 2 1, 1 0))`

### `ⅠⅠ` · Obtuse-at-v

- **Kind / park:** decline · research
- **ISO matrix:** `FF2F01212`
- **ISO predicate:** ST_Touches = 1 · `F***T****` (BB=T, dim-0 vertex)
- **Actual:** `UNSUPPORTED` —
  `RelateNGTouchObtuse.v : obtuse_fill_still_unsupported`.
  Leftover `Ⅱ` classifies
  (`RelateNGTouchObtuse.v : triangle_pair_regime_obtuse`;
  `RelateNGComplete.v : obtuse_pair_touch_obtuse`). Cone
  `side_dot = 0`.
- **Divergence:** ISO is areal vertex-touch (II empty, BB dim-0,
  IE/EI/EE dim-2). Both triangles CCW; one shared vertex; the
  remaining B-vertex sits on the cone line so `TPR_TouchVertex`
  does not fire. Completeness stays false. Not leftover `Ⅰ`. The
  ISO miss is the matrix, not “no detector.”
- **Do not:** remint `cone_separates_b` / `touch_obtuse_vertex_b`;
  steal `522-m`; bucket under leftover `Ⅰ`; mint `522-n`
- **Claim:** leftover `Ⅱ` / #611
- **A:** `POLYGON((0 0, 2 0, 0 2, 0 0))`
- **B:** `POLYGON((0 0, -2 0, 1 -1, 0 0))`

### `ⅠⅠⅠ` · TouchEdge exclusivity

- **Kind / park:** exclusivity · technique
- **ISO matrix:** `FF2F11212`
- **ISO predicate:** ST_Touches = 1 ∧ ST_Overlaps = 0 ∧ ST_Disjoint = 0
- **Actual:** `TPR_TouchEdge` at bar 1. Exclusivity vs the four gtri
  predicates is unproved. Carve #597. Frozen
  `RelateMatrixTriangle.v : triangles_touch_on_shared_edge`.
- **Divergence:** ISO ST_Touches is exclusive of overlap / contains /
  disjoint by the DE-9IM patterns. The field names TouchEdge at bar 1
  but does not prove it cannot also satisfy the four gtri fills. The
  carve is not the exclusivity theorem.
- **Do not:** treat the carve as exclusivity; remint frozen anchors
- **Claim:** `522-a` carve

### `ⅠⅠⅠⅠ` · Disjoint fill remint

- **Kind / park:** fill-lag · sequencing
- **ISO matrix:** `FF2FF1212`
- **ISO predicate:** ST_Disjoint = 1 · `FF*FF****`
- **Actual:** `FFFFFFFFF` — `aa_matrix_disjoint`. Qex:
  `RelateNGDisjointCells.v : ogc_disjoint_fill_not_im_disjoint`
  (`aa_matrix_disjoint_ogc` = `FF2FF1212`;
  `DE9IM.v : pat_disjoint` rejects it).
- **Divergence:** ISO Table 5 EE = 2 for two bounded areas in R²;
  IE/EI are dim-2 disks. Classifier fill still writes F across
  IE/EI/EE. Shared pin — remint moves the rect lane too.
- **Do not:** remint in a harness letter; steal `522-f` / `522-d`
- **Claim:** `522-d`

### `ⅠⅠⅠⅠⅠ` · Overlap fill remint

- **Kind / park:** fill-lag · sequencing
- **ISO matrix:** `212101212`
- **ISO predicate:** ST_Overlaps = 1 · `T*T***T**` (areal)
- **Actual:** `2FFF1FFF2` — `aa_matrix_partial_overlap`.
  `RelateNGOverlapCells.v : triangle_overlap_fill_ie_still_empty`.
- **Divergence:** ISO/OGC overlap has II/IE/EI/EE dim-2, IB/BI/BE/EB
  dim-1, BB dim-0. Classifier IE is empty. `522-h` bar 2 names
  `212101212` on specified-interior gtri cells and leaves the shared
  pin alone.
- **Do not:** remint `aa_matrix_partial_overlap` this cycle; steal
  `522-h`
- **Claim:** `522-h` / #594

### `ⅠⅠⅠⅠⅠⅠ` · Contains fill remint

- **Kind / park:** fill-lag · sequencing
- **ISO matrix:** `212FF1FF2`
- **ISO predicate:** ST_Contains = 1 · B.ST_Within(A) = `T*F**F***`
- **Actual:** `2FFFFFFF2` — `aa_matrix_contains`. Bar 2 names
  `RelateNGContainsCells.v : contains_pair_ogc_gtri_cells`
  (`aa_matrix_contains_ogc` = `212FF1FF2`).
- **Divergence:** ISO areal contains is `212FF1FF2` (IE dim-2, EI/EB
  empty). Classifier still writes `2FFFFFFF2` (IE empty).
- **Do not:** remint `aa_matrix_contains`; steal `522-h`
- **Claim:** `522-h` / #592

### `ⅠⅠⅠⅠⅠⅠⅠ` · Touch-edge fill remint

- **Kind / park:** fill-lag · sequencing
- **ISO matrix:** `FF2F11212`
- **ISO predicate:** ST_Touches = 1 · `F***T****`
- **Actual:** `FFFF1FFF2` — `aa_matrix_touch_vertical`.
  `RelateNGTouchEdgeCells.v : triangle_touch_fill_ie_still_empty`.
- **Divergence:** ISO areal touch-edge is `FF2F11212` (IE/EI/EE dim-2,
  BB/BE/EB dim-1). Classifier IE is empty. Bar 2 already names the
  OGC matrix on the frozen pair. Not leftover `Ⅰ` and not
  exclusivity (`ⅠⅠⅠ`).
- **Do not:** remint `aa_matrix_touch_vertical`; steal `522-h`;
  confuse with leftover `Ⅰ`
- **Claim:** `522-h` / #593

### `ⅠⅠⅠⅠⅠⅠⅠⅠ` · Empty / empty ST_Relate

- **Kind / park:** empty · sequencing
- **ISO matrix:** `NULL`
- **ISO predicate:** NULL · §5.1.45 / §5.1.25 Description 2a–2b
- **Actual:** `UNSUPPORTED` —
  `RelateNGOracleSurface.v : relate_unsupported_pair_wire`.
  Empty/empty shares the leftover-`Ⅰ` token.
- **Divergence:** ISO null-call `ST_Relate`: if SELF or ageometry is
  empty, return the null value — not a 9-char, not 0. Field encodes
  empty/empty as `RWR_Unsupported`. JTS/GEOS/PostGIS typically emit
  `FFFFFFFFF`, which also fails ISO (NULL vs a matrix). Two-layer
  miss: OGC matrix vs ISO NULL, and field Decline vs both.
- **Do not:** treat as a decline bug; mint as a #522 child
- **Claim:** parked
- **A:** `POLYGON EMPTY`
- **B:** `POLYGON EMPTY`

### `ⅠⅠⅠⅠⅠⅠⅠⅠⅠ` · F vs not-computed

- **Kind / park:** alphabet · sequencing
- **ISO matrix:** `F/0/1/2` only
- **ISO predicate:** cell ∈ {T,F,0,1,2,*} per Table 13 · SQLSTATE
  `2FF04` on any other glyph
- **Actual:** `?` in the result 9-char; catalog lookup still rejects
  `?`. `RelateNGCore.v : relate_unsupported_no_predicate` stays
  whole-line Decline. Emptiness is `None`
  (`RelateCurveMatrix.v : cell_none_iff_empty`). EE stays `2`
  (`RelateCurveMatrix.v : geom_de9im_ee_nonempty`). Coq `DimValue`
  never encodes `?`
  (`RelateCurveAlphabet.v : dim_to_result_never_unknown`). Chart:
  [`map-523.md`](map-523.md). Ticket 523 stop is QED ∨ QEX
  (`RelateCurveAlphabet.v : ticket_523_qed_or_qex`), discharged
  QEX on `?` (`RelateCurveAlphabet.v : question_mark_not_iso_table13`).
  ISO cells / emptiness→`F` are QED
  (`RelateCurveAlphabet.v : ticket_523_iso_qed_or_qex`).
- **Divergence:** ISO Table 13 has no unknown glyph. The field driver
  prints `?` where a probe did not run. Result parse accepts `?`;
  catalog fill keys do not. `?` is not a third parse kind and is
  not ISO-conformant.
- **Do not:** steal `522-f`; mint leftover `ⅠⅠⅠ` from #523; put
  `?` in `RELATE_TOKENS`; remint `WireCell`
- **Claim:** `523-b` / `523-c`; ticket stop QEX (not owner accept)

### `Ⅹ` · Nine-cell point-set DE-9IM

- **Kind / park:** spec · technique
- **ISO matrix:** point-set Table 5
- **ISO predicate:** each cell = Intersection(I/B/E, I/B/E).ST_Dimension()
  · §4.2.2.1 — no gtri vocabulary
- **Actual:** `0 < gtri` / `gtri = 0` / `gtri < 0` on bar-2 cells.
  `RelateCurveMatrix.v : geom_de9im_pointset` is the capstone leftover
  (ADR-0003).
- **Divergence:** ISO computes ST_Dimension of point-set intersections.
  Field bar-2 cells are specified-interior gtri, not `point_set`.
  Full nine-cell `geom_de9im_pointset` remains open. That is the spec
  leftover, not a classifier remint and not a #522 child.
- **Do not:** mint as a #522 child; remint fills to discharge ADR-0003;
  steal leftover `Ⅹ` / `522-n`
- **Claim:** #67 / ticket 11

## Holds

- Do not mint `522-n`.
- Do not invent T-junction or obtuse-at-v detectors from this suite.
- Do not start the zoo. Year 1 is still circular.
- `ⅠⅠⅠ`–`Ⅹ` are this catalog’s numerals for unnamed parks. Ask
  before writing them into `map-522-leftovers.md`.
- Epic `#522` stays OPEN. Ticket 523 stays open.

## Frontier

```
ISO ST_Relate ── §5.1.45 / Table 13 ── this catalog

Ⅰ ────── leftover Ⅰ sliver ── classified ── wire UNSUPPORTED ── not FF2F11212
ⅠⅠ ──── leftover Ⅱ obtuse ── classified ── fill UNSUPPORTED ── not FF2F01212
ⅠⅠⅠ ── TouchEdge exclusivity ── carve #597 ── not a theorem
ⅠⅠⅠⅠ–ⅠⅠⅠⅠⅠⅠⅠ ── four shared-pin fill remints ── sequencing
ⅠⅠⅠⅠⅠⅠⅠⅠ ── empty/empty ── ISO NULL vs field Decline
ⅠⅠⅠⅠⅠⅠⅠⅠⅠ ── F vs ? ── #523 ── map-523.md
Ⅹ ────── geom_de9im_pointset ── ADR-0003 ── not leftover Ⅹ / 522-n

522-n ── not minted from this catalog
zoo ── not this year
```
