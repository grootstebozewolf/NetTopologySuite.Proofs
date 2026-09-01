# ISO/IEC 13249-3 curve-type bindings vs. NTS `feat/curves-structure-wkt-foundation`

topic: docs
topics: arc, wkt, relate
claimId: none
witness: none
macro: none
issue: none

## Provenance

- **Spec**: ISO/IEC 13249-3:2016 (SQL/MM Part 3: Spatial, 5th edition). The text
  consulted is the DIS ballot text for that edition (ISO/IEC JTC 1/SC 32 N 2593,
  dated 2015-01-25, page footers "ISO/IEC 13249-3:201x(E)"). Clause numbers below
  are from that text; the published IS may differ in wording detail. The spec is
  **copyrighted and is not in this repo** — citations are by clause number only,
  paraphrased, no long verbatim passages.
- **Branch**: `NetTopologySuite` `feat/curves-structure-wkt-foundation` at commit
  `e84458e` ("Merge branch 'develop' into feat/curves-structure-wkt-foundation"),
  clone at `/home/user/NetTopologySuite`. File:line citations are into that tree.
- **Prior distillation**: `EXACT_CURVE_BIBLE.md` (scratchpad; the *JTS Arc-Native
  Programme* bible, CONTEXT.md "Exact curves") was read first. It is an
  architecture document and contains **no ISO clause citations**, so there was
  nothing to verify clause-by-clause; §7 below cross-checks the few
  spec-adjacent statements it does make. This document is therefore a fresh
  distillation from the spec text.
- Citation style: "§7.3.1 Desc 6)" means item 6 of the *Description* rules of
  subclause 7.3.1.

---

## 1. Type hierarchy and instantiability

The binding hierarchy (§4.2, one concept subclause per type; formal `CREATE
TYPE` definitions in clauses 5–8):

| ISO type | Supertype | Instantiable? | Clause (concept / formal) | NTS type on branch |
|---|---|---|---|---|
| ST_Geometry | — | **no** | §4.2.1 / §5.1.1 | `Geometry` (abstract) |
| ST_Curve | ST_Geometry | **no** (`NOT INSTANTIABLE`) | §4.2.4 / §7.1.1 | `Curve` (abstract), `Geometries/Curve.cs:10` |
| ST_LineString | ST_Curve | yes | §4.2.5 / §7.2.1 | `LineString` |
| ST_CircularString | ST_Curve | yes | §4.2.6 / §7.3.1 | `Curves/CircularString.cs:36` |
| ST_Circle | ST_Curve | yes | §4.2.7 | absent — **not an optional extra** |
| ST_GeodesicString | ST_Curve | yes | §4.2.8 | absent — **not an optional extra** |
| ST_EllipticalCurve | ST_Curve | yes | §4.2.9 | absent — **not an optional extra** |
| ST_NURBSCurve | ST_Curve | yes | §4.2.10 | absent — **not an optional extra** |
| ST_Clothoid | ST_Curve | yes | §4.2.11 | absent — **not an optional extra** |
| ST_SpiralCurve | ST_Curve | yes | §4.2.12 | absent — **not an optional extra** |
| ST_CompoundCurve | ST_Curve | yes | §4.2.13 / §7.10.1 | `Curves/CompoundCurve.cs:36` |
| ST_Surface | ST_Geometry | **no** | §4.2.14 / §8.1.1 | `Surface<T>` (abstract), `Geometries/Surface.cs:16` |
| ST_CurvePolygon | ST_Surface | yes | §4.2.15 / §8.2.1 | `Curves/CurvePolygon.cs:38` (`Surface<Curve>`) |
| ST_Polygon | ST_CurvePolygon | yes | §4.2.16 / §8.3.1 | `Polygon` — **not** a `CurvePolygon` subtype in NTS (pre-existing hierarchy; deliberate divergence) |
| ST_MultiCurve | ST_GeomCollection | "may be instantiable" | §4.2.25 | `Curves/MultiCurve.cs:19` |
| ST_MultiSurface | ST_GeomCollection | "may be instantiable" | §4.2.27 | `Curves/MultiSurface.cs:19` |

ST_Circle, ST_GeodesicString, ST_EllipticalCurve, ST_NURBSCurve,
ST_Clothoid, and ST_SpiralCurve (spiral types "initially limited to"
clothoid, bloss, biquadratic, sine, cosine) are instantiable ST_Curve
subtypes in the §4.2.1 hierarchy. They are **not optional extras**.
The NTS curve-foundation branch does not yet carry them. GEOS WKT
names them and refuses; calling them "Unknown type" is a lie.
§4.2.1 also permits an implementation to add subtypes and to interpose
types, provided subtype relationships are preserved — that clause
legitimises `Curve`/`Surface<T>` as interposed abstractions, not a
licence to drop these types from the model. Do not remint `508-*`.
Do not grow `CurveSegment`.

ST_Curve semantics that bind every curve subtype (§4.2.4):

- 1-dimensional; homomorphic image of a real closed interval; topologically
  closed (all values include their boundary, also §4.2.1).
- *closed* ⇔ start point = end point; *ring* ⇔ simple ∧ closed.
- Boundary: empty set when closed, else {start point, end point}.
- Not simple if any interior point coincides with another interior or boundary
  point.

Branch: `Curve.IsClosed` / `Curve.IsRing = IsClosed & IsSimple` mirror this
exactly (`Geometries/Curve.cs:40,46`); the Mod-2 boundary is implemented per
type (`Curves/CircularString.cs:152-162`, `Curves/CompoundCurve.cs:195-205`).
Note: `IsSimple` is rung-1 partial since branch commit `b392590` (ticket
`615-h`, #624): a single-segment `CircularString` is decided over the locus
(empty and the collinear chord included), so `IsRing` answers a checked
`false` for the open single segment; the multi-segment case and every other
curve type still fail closed (`IsSimpleOp`'s curve guard), continued at
Proofs #630 — see §5.

---

## 2. Per-type structural validity

### 2.1 ST_CircularString (§4.2.6, §7.3.1)

- One or more circular arc segments connected end to end. First segment defined
  by three points: start, *any* intermediate point on the arc other than start
  or end, and end. The end point **shall be distinct from** the start point of
  that segment. Subsequent segments supply intermediate + end point only (start
  is the previous end), and the distinctness constraint applies to them too
  (§7.3.1 Desc 6).
- **Well-formedness count**: with NSEG segments, the value is well formed iff
  NumPoints = 2·NSEG + 1 (§7.3.1 Desc 7). So: odd count, ≥ 3.
- **Arc geometry**: non-collinear triple → the arc is the locus of points at
  distance R from the centre, where the centre is the intersection of the
  perpendicular bisectors of CHORD1 (start–intermediate) and CHORD2
  (intermediate–end), and R is the distance from that centre to any of the three
  points; traversal runs start → intermediate → end (§7.3.1 Desc 8a; prose also
  in §4.2.6).
- **Collinear degenerate**: collinear triple → the segment *degenerates to the
  straight line* from start to end; centre and radius are undefined (§7.3.1
  Desc 8b). Collinear inputs are therefore **legal**, not invalid.
- 3 points exactly = "circular arc"; simple ∧ closed = "circular ring" (§7.3.1
  Desc 9–10).
- Empty = zero points (§7.3.1 Desc 11–12).
- Two alternative single-representation forms exist at the SQL level: control
  point + bulge + bulge-normal arrays (§7.3.1 Desc 13), and centre + radius +
  start/end angle, 2D-only, with numeric angle sweep rules (§7.3.1 Desc 14–15).
  Neither has a WKT form; they are constructor/observer surface only
  (ST_Bulge, ST_Center, ST_Radius, ST_StartAngle …, §4.2.6.1).

Branch: constructor enforces "0, or odd and ≥ 3"
(`Curves/CircularString.cs:56-70`) — matches Desc 7. It does **not** enforce
per-segment start≠end distinctness (Desc 6): `CIRCULARSTRING (0 0, 1 1, 0 0)`
constructs — deliberately, per ADR-0005's lenient intake. ST_IsValid ("tests
if … well formed", §4.2.1.1 item 9) is the designated checker, and since
`359b334` (ticket `615-g`) it answers a definite `false` for exactly this
Desc-6 violation; values passing every rung-1 rule stay fail-closed (§6.2).
No bulge/centre-angle representation exists on the branch (untracked gap;
SQL-level API, low priority for a geometry library).

### 2.2 ST_CompoundCurve (§4.2.13, §7.10.1)

- A sequence of contiguous curves: the end point of each curve **shall be**
  coincident with the start point of the next (§4.2.13, §7.10.1 Desc 7).
- **Admissible components: all subtypes of ST_Curve** (§7.10.1 Purpose and
  Desc 7) — that includes ST_LineString, ST_CircularString, *and nested
  ST_CompoundCurve* (also admitted explicitly by the WKT grammar, §4 below).
- Well formed if every component is well formed (§7.10.1 Desc 3).
- Simple ∧ closed ⇒ ring (§7.10.1 Desc 8). Empty = zero components (Desc 9–10).
- Components shall not be null (Desc 5); the spec is **silent on empty
  components**.

Branch: contiguity enforced with `Equals2D` at construction
(`Curves/CompoundCurve.cs:75-86` at e84458e) — consistent with the spec's
default 2D reading of closedness (ST_IsClosed ignores z/m, §4.2.4.1 item 5),
though the spec text for contiguity itself does not say "ignoring z". Empty
components: **dropped at intake since branch commit `4c787c2`** (2026-08-30,
ticket `615-c`) — the spec forbids only null (Desc 5), an empty component
contributes nothing to the point set, and contiguity is checked across the
drop; the former stricter-than-spec rejection is gone, per ADR-0005.
**Nested CompoundCurve components: accepted and spliced flat since branch
commit `2c4c7bc`** (2026-08-30, ticket `615-b`) — constructor and reader
accept them per §7.10.1 and flatten into the component list, with
contiguity checked across splice boundaries; the former rejection
contradicted the spec (§6.1, retained as history).

### 2.3 ST_CurvePolygon (§4.2.15, §8.2.1)

- Planar surface: one exterior boundary, zero or more interior boundaries
  (holes) (§4.2.15).
- **Both the exterior ring and every interior ring are ST_Curve values that are
  rings** (§8.2.1 Desc 2–3) — i.e. **closed ∧ simple** per §4.2.4. Any ST_Curve
  subtype may serve (the WKT `<ring text>` admits them all, §4 below).
- Rings may intersect pairwise **at most at a single point** (§8.2.1 Desc 11,
  given as a point-set formula); no cut lines, spikes, punctures
  (Desc 12: p = Closure(Interior(p))); interior connected (Desc 13); each hole
  disconnects the exterior (Desc 14); values are simple (Desc 8) and
  topologically closed (Desc 10, 15).
- Empty ⇔ exterior ring empty (Desc 17). Well formed only if all rings are well
  formed (Desc 18).

Branch: constructor enforces **closed** rings only
(`Curves/CurvePolygon.cs:96-108`); simplicity, ring non-crossing, and the
interior-connectivity conditions are ST_IsValid territory and currently fail
closed (`IsSimpleOp.cs:165`). Ring accessors stay typed `Curve` and never
collapse to `LinearRing` (the F-CP contract, `CurvePolygon.cs:27-31`) —
compatible with §8.2.1, which types the ring attributes as ST_Curve. Empty ⇔
empty shell matches Desc 17 (`CurvePolygon.cs:138`).

---

## 3. The semantics behind the four Red tests (all flipped green)

The branch's four deliberately-red contract tests (originally in
`CurveMetricsContractTests.cs`) each encoded a spec obligation. As of
`b829d42` all four are flipped green in `CurveMetricsTests.cs` and the
emptied Red fixture is deleted. What the spec *actually* requires, honestly:

### 3.1 Length — formerly `Red_Length_UnitSemicircle_IsPi`, flipped green as `Length_UnitSemicircle_IsPi` (`CurveMetricsTests`)

§7.1.2 (ST_Length Methods, on ST_Curve) Desc 2a: empty → null; otherwise
"return the implementation-defined length of SELF". **The computation is
implementation-defined, but the operand is not**: for a non-collinear
CircularString value, SELF *is* the circular-arc locus of §7.3.1 Desc 8a — not
the control polyline. The length of the unit upper semicircle's locus is π; the
control-polyline value 2√2 is the length of a different point set, so returning
it would not be "the length of SELF" under any reading. The spec nowhere gives
an arc-length formula (r·θ is our derivation from the locus definition, not a
quoted rule) — the test's `Within(1e-9)` tolerance is a quality bar, not a
clause.

**Landed (2026-08-30, branch commit `2ccd353`, ticket `615-d`):** `Length` is
exact over the locus — r·θ per segment via the new `CircularArcGeometry` seam
(circumcentre + orientation-directed sweep, so major arcs are right), collinear
→ chord per Desc 8b, CompoundCurve = component sum. The Red contract flipped
green and moved to `CurveMetricsTests`. Differential pin: all ARC_LENGTH and
LENGTH_UNIFIED golden vectors agree with the oracle at rel < 1e-9 (run
provenance below, §5a).

### 3.2 Distance — formerly `Red_Distance_PointToCircularString_CentreOfUnitSemicircle_IsRadius` and `..._Endpoint_IsZero`, flipped green as `Distance_CentreOfUnitSemicircle_IsRadius` and `Distance_Endpoint_IsZero` (`CurveMetricsTests`)

§5.1.41 (ST_Distance Methods, on ST_Geometry) Desc 2a: empty operand → null;
**"if SELF and ageometry spatially intersect, then return 0" is normative and
carries no implementation latitude** — the endpoint test (the point (1,0) lies
on the arc, arcs are topologically closed per §4.2.1/§4.2.4) is grounded
directly by Desc 2a-iii. Otherwise return "the distance between two
geometries", with the point-to-point distance algorithm implementation-defined
(Desc 2a-iv). The centre-of-semicircle expectation (distance = r = 1) follows
from §7.3.1 Desc 8a: every point of the locus is at distance R from the centre,
so the geometry-to-geometry minimum is exactly R — the clause delegates the
*algorithm*, not *which point set* is measured.

**Landed (2026-08-30, branch commit `b829d42`, ticket `615-f`):** point-to-curve
distance is exact over the locus via `DistanceOp.Distance` (project onto the
circle, clamp to the sweep; on-locus → 0 exactly per Desc 2a-iii; collinear →
segment distance). Both Red contracts flipped green; the emptied Red fixture is
deleted — all four original planted metric contracts are green. Curve×curve and
the constructor surfaces (`NearestPoints`, `IsWithinDistance`) stay fail-closed
pending arc-arc machinery (`615-h` lane).

### 3.3 Envelope — formerly `Red_Envelope_IncludesAxisExtremeBeyondControls`, flipped green as `Envelope_IncludesAxisExtremeBeyondControls` (`CurveMetricsTests`)

§5.1.19 (ST_Envelope Method, on ST_Geometry — **inherited, not arc-specific;
there is no curve override**) Desc 2b: MINX/MINY/MAXX/MAXY are the minimum and
maximum x/y coordinate values **"in the ST_Geometry value"** — i.e. over the
value's point set, which for a CircularString is the arc locus (§7.3.1 Desc 8).
An arc sweeping −30°…50° on the unit circle contains (1, 0), so MAXX = 1 even
though no control point reaches it. Unlike Length/Distance, §5.1.19 contains
**no implementation-defined escape** for the extremes; a control-point bbox is
simply the envelope of the wrong point set. Two further §5.1.19 details that
bind the SQL-level result shape (informative for NTS's `Envelope` struct, which
is a different surface): degenerate extents are widened by an
implementation-defined ETOL > 0 so the result is always a proper rectangle
(Desc 2c–2e), and the result is an ST_Polygon in the same SRS (Desc 2f, 5).
**Landed (2026-08-30, branch commit `9111983`, ticket `615-e`):**
`ComputeEnvelopeInternal` is exact over the locus for CircularString and
CompoundCurve — per segment the endpoints plus centre ± r on each axis
direction the sweep passes (exact unit axis vectors, so a crossed axis
contributes centre ± r exactly), collinear → chord endpoints only, compound
= component union. The Red contract flipped green into `CurveMetricsTests`.
Oracle pin: the new `ENVELOPE_UNIFIED` lane (exact-Q crossing decisions, one
float step on the extremes — allowlisted INTERFACE-BOUNDARY, see §5a).
CurvePolygon's envelope stays fail-closed (outside this ticket's meso).

### 3.4 Linearisation (the sanctioned escape hatch)

§7.1.10 (ST_CurveToLine): returns "the implementation-defined ST_LineString
value approximation" of the curve; z considered, m re-interpolated by curve
length (Desc 3–4). This is the spec's own chainsaw: approximation is legitimate
**only** through this named method — which is exactly the house rule
(CONTEXT.md "Chainsaw"; Bible §2.3 "no silent linearisation"). Branch:
`Linearize()` is the explicit chord form (`Curves/CircularString.cs:284-291`);
tolerance-driven `Linearize(double)` not yet implemented
(`CircularString.cs:303-306`). §8.2.7 ST_CurvePolyToPoly is the surface
counterpart, mapped by `CurvePolygon.Linearize()`.

---

## 4. WKT / WKB grammar (§5.1.67, §5.1.68)

### 4.1 WKT (§5.1.67)

Token grammar (BNF in §5.1.67 Desc 1; production-to-value rules in the lettered
items that follow it):

- `CIRCULARSTRING [ <z m> ] <circularstring text>` where `<circularstring
  text>` is `EMPTY` or a parenthesised comma-separated point list. The grammar
  itself admits any count ≥ 1; the odd-count ≥ 3 rule is semantic
  well-formedness (§7.3.1 Desc 7), enforced when the produced point array feeds
  `NEW ST_CircularString` (§5.1.67 item e).
- `COMPOUNDCURVE [ <z m> ] <compoundcurve text>`, components are `<curve
  text>` ::= **bare** `<linestring text body>` (a parenthesised point list with
  *no* LINESTRING keyword) | tagged `<circularstring text representation>` |
  tagged circle/geodesic/elliptical/nurbs/clothoid/spiral representations |
  **tagged `<compoundcurve text representation>`** — nested COMPOUNDCURVE is in
  the grammar (production `<curve text>`, mapping rule item ck-ix).
- `CURVEPOLYGON [ <z m> ] <curvepolygon text>`, rings are `<ring text>` with
  exactly the same alternatives as `<curve text>` (bare linestring body, tagged
  curve representations, COMPOUNDCURVE included; mapping rule item cl).
- `<empty set> ::= EMPTY`; an EMPTY body produces the empty value of the tagged
  type (items e, l, ad).
- `<z m> ::= ZM | Z | M`; every WKT nested inside a WKT that carries `<z m>`
  shall carry the **same** `<z m>` (§5.1.67 dimension-consistency rules).
- Terminal characters (`<left paren>`, `<space>`, `<comma>`, numbers, letters)
  are delegated to ISO/IEC 9075-2 §5.1/§5.3. **The spec is silent on keyword
  case**; all keywords are written uppercase in the BNF. (SQL string
  comparison semantics would make lowercase input non-matching; treat
  "uppercase out, tolerant in" as the safe posture.)

Branch: keywords `WKTConstants.cs:47-63`; reader dispatch
`IO/WKTReader.cs:768-773`; component/ring parsing `ReadCurveText`
accepts the bare linestring body and tagged
CIRCULARSTRING per grammar, and **since branch commit `2c4c7bc` accepts
nested COMPOUNDCURVE inside COMPOUNDCURVE** (spliced flat by the
constructor, §6.1) as it always did for COMPOUNDCURVE as a
CURVEPOLYGON/MULTICURVE ring or member (`WKTReader.cs:1188-1204` at
e84458e, matching `<ring text>`). It additionally accepts a **tagged** `LINESTRING` component
(the deviation block in `ReadCurveText`) — an input-side extension beyond the ISO grammar,
documented in-code as a deliberate deviation (GEOS/PostGIS compatibility) and
pinned by an accept-test since branch commit `ed40bf3` (ticket `615-i`); the
writer emits conformant bare bodies for LineString components and tags for
CircularString (`IO/WKTWriter.cs:1046-1070`), so output is grammar-clean.

**Nested `<z m>` consistency is enforced on read since `ed40bf3` (`615-i`).**
The audit behind it (closing the §8 ledger item): the reader used to discard a
curve component's own `Z`/`M`/`ZM` tag silently (the skip in
`GetNextEmptyOrOpener`), so `COMPOUNDCURVE Z (CIRCULARSTRING M ...)` coerced
the declared M into Z without a word, and a plain 2D body under a `Z` outer
died on an accidental arity error naming neither rule nor clause. Now a
component's tag (joined or separate) is consumed and checked in
`ReadCurveText` / `ReadMultiSurfaceText`: an untagged component inherits the
outer dimension (the grammar's own shape), a conflicting tag is rejected
citing §5.1.67, and a body that fails to parse under a non-XY outer tag
reports the dimension-consistency rule with the original error preserved.
A doubled component tag (joined then separate, `CIRCULARSTRINGZ M ...`) is
likewise rejected rather than half-discarded — review follow-up `5fa469a`,
which also pins the nested-COMPOUNDCURVE conflict arm and completes the
EMPTY × Z/M/ZM round-trip matrix for all three curve types.
Out of the curve lane's scope: GEOMETRYCOLLECTION members (full tagged texts,
classical reader path) and the reader-wide legacy `XY + optional third number`
coordinate syntax (`_isAllowOldNtsCoordinateSyntax`, on by default), which can
still absorb an extra ordinate under an untagged outer — a global,
user-disableable compatibility knob, not a curve-path coercion. Keyword
matching is case-insensitive on input (`OrdinalIgnoreCase`), uppercase on
output — consistent with the safe posture above. EMPTY and Z/M/ZM round-trips
for all three curve types are pinned in one place
(`CurveWktTest.EmptyAndZmFormsRoundTripThroughFullOrdinateWriter`).

### 4.2 WKB (§5.1.68)

Structure: `<byte order> <type code> [ <num> <elements>... ]`; CircularString
elements are points, CompoundCurve elements are `<wkbcurve binary>` (each with
its own byte order + type code), CurvePolygon elements are `<wkbring binary>`.
Type codes (§5.1.68 Table 15):

| Type | 2D | Z | M | ZM |
|---|---|---|---|---|
| CircularString | 8 (or 1000001) | 1008 | 2008 | 3008 |
| CompoundCurve | 9 (or 1000002) | 1009 | 2009 | 3009 |
| CurvePolygon | 10 (or 1000003) | 1010 | 2010 | 3010 |
| MultiCurve | 11 (or 1000004) | 1011 | 2011 | 3011 |
| MultiSurface | 12 (or 1000005) | 1012 | 2012 | 3012 |

Byte-order bytes: 0 = big endian, 1 = little endian (§5.1.68 items fz–ga).

Branch: base codes 8–12 in `IO/WKBGeometryTypes.cs:63-83`; the +1000/+2000/+3000
Z/M offsets are decoded generically (`WKBReader.ReadGeometryType`). The alternate
`100000x` code series that Table 15 lists as a second legal encoding is
**accepted on read since branch commit `ed40bf3`** (ticket `615-i`): a
dedicated decode path maps 1000001–1000005 to the base curved types 8–12
before the `(type & 0xffff) % 1000` masking (which cannot recover them —
`1000001 & 0xffff == 16961`); the writer emits base codes only, and both
halves are round-trip-pinned
(`CurveWkbWktGeosTest.WkbAlternateTable15CodesReadAsBaseTypes`).

---

## 5. Mapping table: ISO rule → branch → gap

| ISO rule (clause) | Branch behaviour (file:line) | Status |
|---|---|---|
| ST_Curve / ST_Surface not instantiable (§7.1.1, §8.1.1) | `Curve`, `Surface<T>` abstract (`Geometries/Curve.cs:10`, `Geometries/Surface.cs:16`) | ok |
| ring = closed ∧ simple (§4.2.4) | `Curve.IsRing` (`Curve.cs:40`); `IsSimple` rung-1 partial since `b392590`: single-segment CS decided over the locus (arc injective in the angle, collinear → Desc-8b chord), `IsRing` checked-false for the open single segment; multi-segment + other curve types fail closed | ok (rung 1) — landed 2026-08-30 (`615-h`, #624); frontier continues at #630; oracle-pinned via `RING_SIMPLE`, see §5a |
| CS well-formed ⇔ 2n+1 points, ≥3 (§7.3.1 Desc 7) | ctor enforces 0 or odd ≥3 (`CircularString.cs:56-70`) | ok |
| CS arc end ≠ arc start per segment (§7.3.1 Desc 6) | definite-false via `CurveValidity` rung 1 since `359b334` (constructs at intake per ADR-0005; IsValid returns false) | ok — landed 2026-08-30 (`615-g`); clean values stay fail-closed pending rung 2 (the `615-h` lane, #630) |
| CS collinear triple → straight-line segment (§7.3.1 Desc 8b) | `CircularArcGeometry.SegmentLength` maps a collinear triple to its start–end chord since `2ccd353`; pinned by `Length_CollinearTriple_IsChord` and the `collinear_chord` oracle vector | ok — landed 2026-08-30 (`615-d`) |
| CS bulge / centre-radius-angle representations (§7.3.1 Desc 13–15) | absent | untracked gap (SQL API surface; optional for NTS) |
| CC components: **all** ST_Curve subtypes, nested CC included (§7.10.1 Desc 7; §5.1.67 `<curve text>`) | accepted and spliced flat, ctor + reader, since `2c4c7bc` (flatten tests in `CompoundCurveTest`/`CurveWktTest`) | ok — ADR-0005 Decision 2, landed 2026-08-30 (`615-b`) |
| CC contiguity: end = next start (§7.10.1 Desc 7) | `Equals2D` check in ctor (`CompoundCurve.cs:75-86`) | ok (2D reading; spec default closedness is 2D, §4.2.4.1) |
| CC empty components (spec silent; only null forbidden, §7.10.1 Desc 5) | dropped at intake since `4c787c2` (normalize inside; contiguity checked across the drop) | ok — ADR-0005 Decision 1, landed 2026-08-30 (`615-c`); every surviving intake check now carries its clause citation in-code |
| CP rings are rings = closed ∧ simple, any ST_Curve (§8.2.1 Desc 2–3) | ctor: closed only (`CurvePolygon.cs:96-108`); ring simplicity still fail-closed (rings are closed, so the single-segment rung cannot serve them — a closed single segment is Desc-6-degenerate) | partial; multi-segment/compound simplicity is #630 |
| CP ring intersection ≤ 1 point, no spikes/cuts, connected interior (§8.2.1 Desc 11–14) | not evaluated (IsValid fail-closed) | known gap (IsValid work) |
| ST_Length on curves (§7.1.2 Desc 2; operand = arc locus §7.3.1 Desc 8) | exact r·θ over the locus since `2ccd353` (`CircularArcGeometry` seam; collinear → chord per Desc 8b; CC = component sum) | ok — landed 2026-08-30 (`615-d`); oracle-pinned, see §5a |
| ST_Distance: intersect → 0; else min distance (§5.1.41 Desc 2a) | exact point-to-curve since `b829d42` (`CurveDistance` dispatch off `DistanceOp.Distance`; curve×curve + NearestPoints/IsWithinDistance stay fail-closed) | ok — landed 2026-08-30 (`615-f`); oracle-pinned via ARC_DISTANCE, see §5a |
| ST_Envelope: extremes over the value's point set (§5.1.19 Desc 2b) | exact over the locus since `9111983` (endpoints + centre±r on crossed axes; CS + CC; CP still fail-closed) | ok — landed 2026-08-30 (`615-e`); oracle-pinned via `ENVELOPE_UNIFIED`, see §5a |
| ST_CurveToLine / ST_CurvePolyToPoly explicit approximation (§7.1.10, §8.2.7) | `Linearize()` (`CircularString.cs:284-291`); tolerance overload throws (`CircularString.cs:303-306`) | ok as chainsaw; tolerance form pending |
| WKT grammar incl. bare linestring bodies, EMPTY, Z/M (§5.1.67) | reader/writer (`WKTReader.cs:768-773`, `ReadCurveText`/`ReadMultiSurfaceText`, `WKTWriter.cs:1002-1096`); nested `<z m>` consistency enforced on read since `ed40bf3` | ok — landed 2026-08-30 (`615-i`); tagged-LINESTRING extension documented + deviation-pinned |
| WKB Table 15 codes + Z/M offsets (§5.1.68) | `WKBGeometryTypes.cs:63-83`, `WKBReader.ReadGeometryType`; alternate 100000x codes decoded to base types since `ed40bf3` | ok — landed 2026-08-30 (`615-i`); writer emits base codes, round-trip-pinned |

### 5a. Metric-landing oracle runs (provenance)

| Run | Oracle | NTS | Result |
|---|---|---|---|
| 2026-08-30, ticket `615-d` | `oracle_bin` rebuilt in-container via `make -C oracle` from this repo at `4e33e2c` (extraction unchanged) | fork branch at `2ccd353` + review follow-up `df5ba57` (CW-witness + unequal-radii vectors) | `SUMMARY ok=26 warn=7 bug_or_fail=0` — 7 legacy ARC_LENGTH + 7 LENGTH_UNIFIED vectors all `rel < 1e-9` (several bit-exact); the 7 WARNs are the honest fail-closed pendings for Envelope/Distance (`615-e/f`), flipped when those land |
| 2026-08-30, ticket `615-e` | `oracle_bin` rebuilt with the new `ENVELOPE_UNIFIED` lane (exact-Q axis-crossing decisions, one float step on the extremes; allowlisted INTERFACE-BOUNDARY kernel `run_envelope_unified`) | fork branch at `9111983` | `SUMMARY ok=43 warn=6 bug_or_fail=0` — 5 ENVELOPE_UNIFIED vectors plus the legacy ENV probe all within `1e-12`/`rel < 1e-9` (axis extremes agree to the last ulp); the 6 WARNs are the Distance pendings (`615-f`) |
| 2026-08-30, ticket `615-f` | same `oracle_bin` (the pre-existing ARC_DISTANCE lane pins this landing) | fork branch at `b829d42` + review follow-up `61f4981` (collinear-overshoot chord pin, Desc 8b) | `SUMMARY ok=49 warn=0 bug_or_fail=0` — all six ARC_DISTANCE queries flipped WARN→OK (five bit-exact, one at `rel ≈ 1e-16`); **the curve differential harness is now fully green: zero warnings, zero bugs** |
| 2026-08-30, ticket `615-h` rung 1 (#624) | same `oracle_bin` (the pre-existing `RING_SIMPLE` lane; proof companion `theories/CurveRingSimple.v`) | fork branch at `b392590` + review follow-up `e00c00b` (endpoint equality is *tested* before any float orientation step and routes the start==end triple to the fail-closed throw — no verdict; the review demonstrated an overflow counterexample where the orientation cross is NaN, not 0, and the closed degenerate segment briefly got an unchecked `true`; pinned. NTS still throws on a Desc-6 triple — the harness row below pins exactly that) | `SUMMARY ok=55 warn=0 bug_or_fail=0` — six new RING_SIMPLE rows: three decided single-segment values agree (SIMPLE ↔ `IsSimple == true`; the collinear one sent as its Desc-8b chord), the classical bowtie ring agrees on NOT_SIMPLE (witness `(1,1)` bit-exact as observed, first token asserted), and the two fail-closed contract rows pin that NTS throws where the oracle decides (the two-segment frontier) or itself declines (DEGENERATE for the degenerate closed segment) |

Harness: `ORACLE=oracle/oracle_bin dotnet run --project tests/CurveOracleBugHunt`
(now platform-portable: direct exec off Windows; WSL path preserved on it).

### 5b. Epic wrap-up gate run (ticket `615-j`, 2026-08-30)

All four gates re-run end to end at fork `e00c00b` / Proofs `b7aa688`:

| Gate | Result |
|---|---|
| Fork `Curves` + IO namespaces (`dotnet test --filter "FullyQualifiedName~Curves\|FullyQualifiedName~.IO."`) | 441 passed, 0 skipped; the only 4 failures are the pre-existing GML2 `WriteEmpty*` writer tests, reproduced bit-identically at the pristine base `e84458e` (re-verified in a worktree during the `615-i` review) — no curve or reader/writer regression. Every former `Red_` contract runs as a plain green test. |
| Illustrator suite against the updated sibling (`dotnet test tools/WktUnicodeIllustrator.Tests`) | 53 passed, 0 skipped — exactly the umbrella's gate (curve facts live, not skipped: the sibling wiring sees the branch). |
| Oracle differential (`CurveOracleBugHunt`, all lanes: ARC_LENGTH, LENGTH_UNIFIED, ENVELOPE_UNIFIED, ARC_DISTANCE, RELATE_MATRIX, chord≤arc invariant, RING_SIMPLE) | `SUMMARY ok=55 warn=0 bug_or_fail=0` — fully green, zero warnings. |
| Proofs gauntlet (`make check`) | `ok=5 warn=0 bug=0 fail=0`. |

---

## 6. Where the spec contradicts or is stricter than the branch

### 6.1 Nested CompoundCurve — the branch contradicts the spec (warn)

§7.10.1 (Purpose and Desc 7): "the contributing curve types include **all
subtypes of ST_Curve**" — ST_CompoundCurve is itself a subtype of ST_Curve, and
the WKT grammar makes the admission explicit: `<curve text>` includes
`<compoundcurve text representation>` (§5.1.67, mapping item ck-ix), likewise
`<ring text>` (item cl-ix). The branch rejects nested components in the
constructor (`CompoundCurve.cs:69-74`), rejects them in the parser
(`WKTReader.cs:1086-1087`), pins the rejection in a test
(`CurveWktTest.ReadRejectsNestedCompoundCurves`), and — the actual defect — its
doc comment claims the flat list is "matching SQL/MM and common
implementations" (`CompoundCurve.cs:27-29`). The "common implementations" half
is true (PostGIS/GEOS flatten or reject); the "SQL/MM" half is false. Design
options for the interview: keep the restriction but fix the comment (document
it as a deliberate deviation), or accept-and-flatten on input (what PostGIS
does), or model nesting. What is not tenable is citing SQL/MM for the
rejection.

**Decision of record (2026-08-30):** accept-and-flatten on intake —
`docs/adr/ADR-0005-lenient-intake-strict-isvalid-curve-types.md` Decision 2.

**Landed (2026-08-30, branch commit `2c4c7bc`, ticket `615-b`):** constructor
and reader accept nested compound components and splice them flat (depth-1 —
a constructed CompoundCurve is already flat by induction); contiguity is
checked on the flattened sequence; the rejection pins are replaced by five
flatten tests; the doc comment now owns the flat model as normalization
citing §7.10.1 and ADR-0005. This section is retained as the history of the
finding; the `SUMMARY` below flipped `warn` → `ok` with this landing.

### 6.2 Arc-segment endpoint distinctness — spec stricter than the branch

§7.3.1 Desc 6 says each arc segment's end point **shall** be distinct from its
start point (a closed single "arc" is ST_Circle's job, §4.2.7). The branch
constructs such values without complaint (`CircularString.cs:50-72` checks
count only). Not a behavioural contradiction — NTS defers value validity to
`IsValid`, which fails closed — but the rule must land in arc-aware
IsValid/IsSimple, and constructor-level enforcement is worth the interview's
attention (it is cheap: pairwise `Equals2D` per segment).

**Decision of record (2026-08-30):** the interview chose lenient intake —
Desc 6 lands in arc-aware IsValid rung 1 (definite-false detection), not the
constructor: `docs/adr/ADR-0005-lenient-intake-strict-isvalid-curve-types.md`
Decision 1; #615 tickets `615-c` (intake contract) and `615-g` (rung 1).

**Landed (2026-08-30, branch commit `359b334`, ticket `615-g`):** the three
curve classes override `IsValid` to the rung-1 `CurveValidity` check —
definite `false` for the implemented rules (Desc 6, Desc 7 count shape,
§7.10.1 Desc 3/7, §8.2.1 closure), fail-closed throw naming rung 2
(ticket `615-h`) for everything cleaner; an unchecked `true` is never
returned, the empty value stays `true`. The single-segment closed arc is
now definitely invalid; the five-point full-circle idiom stays fail-closed
until simplicity lands. The definite-false verdict carries its clause
(`CurveValidity.TryFindDefiniteInvalidity`, review follow-up `505ffaa`).
MultiCurve/MultiSurface have no rung-1 override: their members reach
`IsValidOp`'s default fail-closed throw — no silent-true path, wiring them
through the rung is `615-h`-lane work.

### 6.3 Ring simplicity for CurvePolygon — spec stricter than the constructor

§8.2.1 Desc 2–3 require rings (closed **and simple**); the branch checks closed
only (`CurvePolygon.cs:96-108`). Same posture as 6.2: fine while IsValid fails
closed, must not be forgotten when it stops failing closed.

### 6.4 Envelope of degenerate extents — SQL-level rule, note only

§5.1.19 Desc 2c–e mandate widening a zero-width/height envelope by ETOL so
ST_Envelope always returns a proper rectangle. NTS's `Envelope`/
`EnvelopeInternal` intentionally represents degenerate extents; if an
SQL/MM-conformant `ST_Envelope`-shaped API is ever exposed, the widening
belongs there, not in `Envelope`.

### 6.5 Fail-closed metrics vs. spec-required answers

ST_Length, ST_Distance, ST_Envelope are total over non-empty values in the
spec. **All three are exact over the locus now: ST_Length since `2ccd353`
(`615-d`, §3.1), ST_Envelope since `9111983` (`615-e`, §3.3), and
point-to-curve ST_Distance since `b829d42` (`615-f`, §3.2). IsSimple joined
the rung ladder with `b392590` (`615-h` rung 1, #624): single-segment
CircularString decided.** What still throws is the frontier that needs
arc-arc machinery (curve×curve distance, NearestPoints/IsWithinDistance,
multi-segment/compound simplicity — the `615-h` lane, continued at #630),
preferred over
silently returning chord-approx numbers — which would satisfy the type
signature while violating §7.3.1 Desc 8's definition of the value being
measured. With the Red fixture emptied and deleted, the spec's side of that
contract is now the green fail-closed pins (`CurveFailClosedTest`,
`Distance_ArcToArc_StaysFailClosed`), which assert the frontier throws.

---

### 6.6 Cross-repo fork: the `(A, B, A)` factory rewrite (recorded, undecided)

`grootstebozewolf/jts#124` (ported to NTS by
`grootstebozewolf/NetTopologySuite#20`) rewrites a 3-point closed arc
`(A, B, A)`, A ≠ B, into the five-point full-circle form `(A, C, B, D, A)`
at factory/read time. ADR-0005's posture gives the same WKT a different
answer: it constructs as the 3-token value (intake is representability
only, `615-c`) and is **definitely invalid** at rung 1 (§7.3.1 Desc 6,
`615-g`) — `(A, B, A)` is not the 13249-3 full-circle form, and the
rewrite is a JTS-side on-ramp the spec does not have. Per the PR #626
review (2026-08-30), these two postures must not both stand as silent
sources of truth: merging the NTS port into the foundation branch
requires either recording the rewrite in this document as a **documented
JTS/NTS input deviation** (a factory-door normalization — in which case
the CurveOracleBugHunt harness should construct via the factory so its
vectors keep tracking intake) or amending ADR-0005. Until the PO decides,
the port is not "the Proofs posture". Recorded here so the fork is loud,
not silent. **Decision pending.**

## 7. Cross-check against EXACT_CURVE_BIBLE.md

The Bible is architecture, not spec exegesis; it cites no ISO clauses. Its
spec-adjacent statements, checked:

- "Colinear 3-control windows degrade to an exact chord" (Implementation notes)
  — **verified**: §7.3.1 Desc 8b says exactly this for the value semantics.
- "No silent linearisation … `toLinear(tolerance)` is the only densify path"
  (§2.3, notes) — **consistent with** the spec's structure: approximation
  exists only as the named methods ST_CurveToLine (§7.1.10) and
  ST_CurvePolyToPoly (§8.2.7); no metric clause authorises approximating the
  operand.
- CONTEXT.md "Zoo" backlog list (SPIRALCURVE's bloss, biquadratic, sine,
  cosine; CIRCLE; GEODESICSTRING) — **verified**: §4.2.12 (spiral types
  "initially limited to clothoid, bloss, biquadratic, sine and cosine"),
  §4.2.7, §4.2.8.
- Everything else in the Bible (ExactCurve protocol, 1.15× ratchet, package
  layout) is out of the spec's scope — neither confirmed nor contradicted.

## 8. Claims not fully grounded in the spec text (honesty ledger)

- **WKT keyword case-insensitivity**: the spec never states it; terminals
  delegate to ISO/IEC 9075-2. NTS's case-insensitive reading is a compatibility
  choice, not a clause. Marked unverified.
- **r·θ as "the" arc length and 1e-9 tolerances**: derived from the locus
  definition (§7.3.1 Desc 8a) + §7.1.2; the spec states no formula and no
  precision. The metric tests' numeric expectations (formerly the Red
  contracts') are quality bars.
- **Nested-tag `<z m>` consistency enforcement in the NTS reader** (spec rule
  in §5.1.67): **closed 2026-08-30** (ticket `615-i`). Audit finding: the
  reader silently discarded a component's own tag (silent coercion), and a 2D
  body under a `Z` outer failed only by an accidental arity error. Enforced on
  read since branch commit `ed40bf3` with clause-citing rejections; details in
  §4.1, reject/accept pins in `CurveWktTest`.
- **Published-IS wording**: citations are from the DIS ballot text of the 5th
  edition (N 2593). No claim here was found only in ballot-specific front
  matter, but clause-item numbering in the published 2016 IS could differ.

---

SUMMARY ok — the one contradiction (nested COMPOUNDCURVE rejection with a false SQL/MM attribution) was retired by branch commit `2c4c7bc` (2026-08-30, ticket `615-b`): components are accepted and spliced flat per §7.10.1 Desc 7 and §5.1.67, ADR-0005 Decision 2. Length is exact over the arc locus since `2ccd353` (ticket `615-d`, oracle-pinned — §5a). IsValid is rung-1 partial since `359b334` (ticket `615-g`: definite-false for the cheap clause rules, Desc 6 included; fail-closed otherwise). Envelope is exact over the locus since `9111983` (ticket `615-e`) and point-to-curve Distance since `b829d42` (ticket `615-f`) — all four original Red metric contracts are green and the oracle differential ran `ok=49 warn=0 bug_or_fail=0` at that landing (the wrap-up run is `ok=55`, §5b). The WKT/WKB small print landed with `ed40bf3` (ticket `615-i`): nested `<z m>` consistency enforced on read (the silent-coercion audit finding closed, §8 ledger), Table 15 alternate WKB codes accepted on read, and the tagged-LINESTRING tolerance documented as a deliberate deviation. The simplicity lane opened with `b392590` (ticket `615-h` rung 1, #624): single-segment CircularString `IsSimple` is decided over the locus and RING_SIMPLE-pinned (`ok=55 warn=0 bug_or_fail=0`). IsSimple rung 1 was hardened by review follow-up `e00c00b` (endpoint equality decided before any float orientation test; overflow counterexample pinned). The remaining divergence is multi-segment/compound simplicity and its arc-arc dependents (§4.2.4 / §8.2.1 ring simplicity; curve×curve distance, NearestPoints; wiring decided simplicity into IsValid) — the `615-h` lane, continued at #630. **Epic A+B scope wrapped 2026-08-30 (ticket `615-j`): all four gates re-run green end to end at fork `e00c00b` (§5b) — this document is the single source of truth for what is now true on the branch.**
