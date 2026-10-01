# NetTopologySuite.Proofs

A Rocq/Coq proof corpus accompanying NetTopologySuite, plus the differential
tooling that compares real geometry engines (NTS, GEOS) against the extracted
oracle and pictures the cases under scrutiny.

## Language

### Arrangement vocabulary

Per **ADR-0007**. Each term names one thing precisely; the short name is the
one to use in issue titles and lemma names, the gloss is what it means. None
ADR-0007 is *Accepted* (Joost, BDFL, 2026-09-07).  Four of the seven now
exist as types in `theories/SheetHenCook.v`: `Sheet` (Record), `Hen`
(Definition), `Egg` (Inductive), `Chicken` (Record).  `Cook` and `View` are
not types; `Decline` is a constructor, `IDecline` of `IResult`, not a type.

**Sheet**:
An oriented affine plane `(O; e1, e2)` with an optional lattice (the snap
grid). All coordinates are points of one sheet, and a constructor runs on
exactly one. Changing the sheet or the lattice is a different instance. This
is the envelope JTS leaves unnamed when it stores a bare `Coordinate` and
later attaches a scale.
_Avoid_: precision model, coordinate system (both name only part of it)

**Hen**:
A stable identifier with decidable equality. A hen owning a point is a
vertex; a hen owning an egg is a curve piece. Identity of vertices is a
property of the hen, **not** of its coordinates -- which is the whole point:
`Dart := (Point * Point)` makes two coincident crossings rounded to different
floats into two darts that `dart_eq_dec` correctly reports as distinct.
_Avoid_: vertex, node, id (each is a role a hen plays, not the thing)

**Egg**:
The interpolant `gamma : [0,1] -> sheet` of a named class (chord, circular
arc, clothoid, sinusoid, ellipse, Bezier, NURBS), supporting `eval`,
`tangent`, curvature where defined, `split` and `demote`.
_Avoid_: curve, segment (both are classes of egg, not the concept)

**Bézier**:
Single-span unit-weight `MkNurbs`; schema kind `Bezier`.

**Chicken**:
Incidence, and only incidence: a directed use `(h_src, h_dst, egg)` of an egg
between two hens. Its twin reverses orientation. A hen incident to no chicken
is **vacant**.
_Avoid_: edge, half-edge, dart (dart is the corpus's current, coordinate-
carrying approximation of a chicken)

**Cook**:
A constructor: a partial function that allocates hens. The primitive is the
pairwise intersection oracle, which returns a point plus its two parameters,
or the empty set, or **declines**. The cook is the only way a new hen appears.
Priest 1991 §7 is a cook for a line and a segment in floating point.
_Avoid_: noder, intersector (these name implementations of one cook)

**Decline**:
The oracle was undefined for this pair, or the inputs are not on one sheet.
**Not** an empty geometry, not `EMPTY`, not a value in SQL/MM. Distinguish
sharply from a completed cook that left no hens, which *is* the empty
point-set (dimension -1, union identity, intersection zero).
_Avoid_: empty, null, failure (the first is a different result, the others
lose the distinction)

**View**:
A function from leftover hens to a wire format -- WKT, WKB, SFA class names,
SQL/MM type tags. `POINT EMPTY` is a tag a view chooses for a vacant result
whose caller expected a point; the kernel does not store it. The SFA type
zoo lives here, not in the kernel.
_Avoid_: geometry type, output format

### Abbreviations

The initialisms that carry the most weight in the corpus. If a term you need is
not here, that is a signal — see `docs/agents/domain.md`.

**JCT**:
Polygonal `point_in_ring` ⟺ `geometric_interior` (`point_in_ring_correct`),
not classical JCT. Taut polygonal true-region is
`RelateNGJordanTrueRegion.v : relateng_jordan_true_region_taut` (#791);
`RNG_JordanUncond` stays park (`RelateNGFace.v : relateng_not_jordan_uncond`).
_Avoid_: Jordan (unqualified); “true-region fully discharged”

**DCEL**:
**Doubly connected edge list** — the half-edge structure the face-extraction and
ray-parity machinery walk (`dart`, `next`, `face`, orbits). `coq-fourcolor`'s
`Record hypermap` with its three mutually-inverse permutations is equivalent to
it.
_Avoid_: quad-edge (that is Guibas–Stolfi's structure, which this corpus does
not use)

**QED ∨ QEX**:
The disjunctive stop condition for a lane: it closes either by a completed proof
(**QED**) or by a **documented counterexample** (**QEX**). Both are green; a
refutation that is Qed-closed and registered is a result, not a failure.
_Avoid_: failed, blocked (for a QEX outcome)

**RGR**:
The slice pattern: Read (grep fallback) → Red (analytical test) → Green (minimal
reuse) → Refactor (tiny + comment) → Pin + Cake + oracle match → Accept.
_Avoid_: red-green-refactor (the corpus's cycle has six steps, not three)

**MIC**:
**Maximum inscribed circle** — the largest disk contained in a region, with both
the containment and the maximiser (`MaximumInscribedCircle.v`, board #9004).

**LEC**:
**Largest empty circle** — the largest disk avoiding a point set
(`LargestEmptyCircle.v`, board #9006 for the medial-axis lane).

**PIA**:
**Pole of inaccessibility** — the point furthest from a shoreline. The
authoritative definition (Garcia-Castellanos & Lombardo 2007,
doi:10.1080/14702540801897809) is **on the sphere**; this corpus is planar
throughout, so plane MIC/LEC ≠ spherical PIA. The spherical gap is board #9005.
_Avoid_: treating PIA and LEC centre as interchangeable outside the planar
teaching instance

### Curve types

topic: docs
topics: relate, binary64, arc, overlay
claimId: none
witness: none
macro: none
mutation-seed: 890884
issue: none

Abbreviations are **shared with the `grootstebozewolf/jts` fork** so a table can be
read across both trackers. The initials always match the type: CS is the type
starting "Circular", CC the one starting "Compound".

| Abbrev | Type | JTS | NTS |
|---|---|---|---|
| CS | CircularString | `geom/curve/CircularString.java` | `Geometries/Curves/CircularString.cs` |
| CC | CompoundCurve | `geom/curve/CompoundCurve.java` | `Geometries/Curves/CompoundCurve.cs` |
| CP | CurvePolygon | `geom/curve/CurvePolygon.java` | `Geometries/Curves/CurvePolygon.cs` |
| Multi | MultiCurve / MultiSurface | `geom/curve/MultiCurve.java` | `Geometries/Curves/MultiCurve.cs` |
| Arc | CircularArc | *(no class — a Proofs primitive)* | — |

**CircularString (CS)**:
One curve geometry made of a run of circular arcs, each sharing an endpoint with
the next; WKT `CIRCULARSTRING`, 2n+1 points. A *sequence*, so a single-arc fact
reaches it only through a concatenation argument.
_Avoid_: CC (the fork and this repo both mean CompoundCurve), arc, Arc

**CompoundCurve (CC)**:
One curve geometry whose members are contiguous LineStrings and CircularStrings
joined head to tail. Mixed linear and curved by construction.
_Avoid_: CS (means CircularString), compound, curve chain

**CircularArc (Arc)**:
This corpus's **primitive** — a single arc, not a geometry type. It has no WKT
keyword and no class in any engine. An Arc theorem is not a CS theorem.
_Avoid_: CircularString, CS, arc geometry

**CurveCollection**:
**Retired — the type does not exist.** No such class in JTS, GEOS or NTS
(verified 2026-08-22: zero matching files in all three trees). It appeared as a
`CC` column heading in the coverage matrix and in Slice 10 prose; both were
naming a type no engine has. Say Multi (for member recursion) or CC
(for CompoundCurve), whichever the evidence actually covers.
_Avoid_: CC, curve collection, collection of curves

### Curve conformance

Per **ADR-0005**, the SQL/MM curve types conform at the boundary and
normalize inside: say which side of the intake/validity line a check lives on.

**Intake**:
What constructors and readers reject: only what makes a value
unrepresentable — point-count shape, component contiguity, ring closure.
Everything accepted is representable; everything rejected carries a clause
citation. A value can pass intake and still be invalid.
_Avoid_: validation, well formed (as a constructor claim)

**Intake walker** (ADR-0007, claimId `0007-intake-walker`):
`IntakeWalker.v : ticket_0007_intake_walker_qed_or_qex`.
_Avoid_: WKT zoo, example3.txt as oracle source, silent chord demote,
new oracle keyword

**Intake geodesic** (ADR-0007, claimId `0007-intake-geodesic`):
`IntakeGeodesic.v : ticket_0007_intake_geodesic_qed_or_qex`.
_Avoid_: MkGeodesic, EggGeodesicString on a successful bag, WKB 13,
emit of GEODESICSTRING, first-cook expand, new oracle keyword

**Intake angles** (ADR-0007, claimId `0007-intake-angles`):
`IntakeWalker.v : ticket_0007_intake_angles_qed_or_qex`;
`IntakeAngles.v : intake_angles_pm2pi_superseded`.
_Avoid_: silent chord demote, host cook expand, new oracle keyword

**Span carrier** (ADR-0009, #866 / #771, claimId `0009-cst-span-carrier`):
`IntakeCarried.v : ticket_0009_cst_span_carrier_qed_or_qex`.
_Avoid_: span on Sheet, one pair for a multi-arc string, minting the egg before fail-closed

**CAD carrier**:
Structured CAD intake; [`tools/cad/carrier.schema.json`](tools/cad/carrier.schema.json).

**Bulge**:
DXF *b* = tan(Δθ/4); schema `segment.bulge`.

**Placement chain**:
An ordered sequence of similarity placements (block inserts then
georeference) that collapses to one similarity; a non-similarity
link declines the whole entity. Year-1 lemma `similarity_chain_closed`
tracks the sign of the determinant.

**Joint** (ADR-0007 Phase B, occupancy in ADR-0009):
`HostCircChordOracle.v : I_ok_circ_chord_hit_complete` (#894).
_Avoid_: interior mixed cook (ι), first-cook expand, host mixed I

**Sidecar joint occupancy** (ADR-0009):
`HostCircChordOracle.v : I_ok_circ_chord_hit_complete` (#894).
_Avoid_: treating I_ok_mixed as host I_ok

**Phase B done-when** (ADR-0007 letter after Accept):
`ticket_0007_phase_b_done_when_qed_or_qex`. Parks: ι, host mixed I, ρ, Multi required-type.
_Avoid_: Phase B Open as if a theorem were missing, SQL/MM done,
cathedral Landed

**Intake MkClothoid** (ADR-0007, claimId `0007-intake-mkclothoid`):
`IntakeWalkerClothoid.v : ticket_0007_intake_mkclothoid_qed_or_qex`.
Start state: `0007-norm2-state`.
_Avoid_: two constructors, Fresnel-as-noding, silent chord demote,
new oracle keyword

**Clothoid first-cook** (ADR-0007, claimId `0007-clothoid-first-cook`):
`ClothoidCookMkClothoid.v : ticket_0007_clothoid_first_cook_qed_or_qex`.
_Avoid_: Fresnel noding, Halley noding, mixed first cook, NURBS
first cook, Campaign I, new oracle keyword

**SQL/MM signed tag** (ADR-0007, claimId `0007-sqlmm-signed-tag`):
Rungs 3–6 of τ=μ. Achievable ring is locked `exists b e`
agreement (not ∀ on all CSTs). `τ = first_slice_tag` on eggs;
`μ = intake_map` on CSTs. They do not share a domain. After μ
mints a singleton bag, `τ(e)=ρ(π(c))`. `intake_rho` /
`cst_prod_tag` here are the CST production tag in that equation
— not ADR-0007 park ρ (`EmitRhoBagLoop` / bag-loop). ISO CIRCLE
bag is two ±π MkCirc (ρ=CIRCLE); ADR-0005 lenient closed CS normalizes, strict Declines.
`intake_rho` is egg-aware on CIRCULARSTRING and is not
`cst_prod_tag`. Well-formed GeodesicString bags `MkChord`;
τ is LINESTRING; `cst_prod_tag` stays None (production is not
signed I/O). SpiralCurve still Declines (τ unused). `κ` is 2/8
or none (not 13). Emit / WKT parse stay QEX. Production-level
τ=π on closed CIRCULARSTRING text stays QEX.
_Avoid_: ∀-mapper on all CSTs, Circle-as-18, compound-as-τ,
park-ρ remint, new oracle keyword

**ISO validity**:
Every spec "shall" beyond representability, owned by arc-aware `ST_IsValid`:
implemented rules answer definite-false naming their clause; unimplemented
rules fail closed (throw naming the missing rung) — never an unchecked
`true`.
_Avoid_: invalid (for merely un-checked values), IsValid returns true (until
the rung that checks it lands)

### CAD-to-GIS bridging (year 0)

**Why a second source family.** SQL/MM Part 3 is where curves are *stored* in GIS. It is not where most curves *originate*. Road and rail design, cadastral survey drawings, utility as-builts and signage all arrive as CAD: DWG/DXF (Autodesk), DGN (Bentley MicroStation), and increasingly IFC alignments. Glyph outlines from fonts are the same problem in miniature: closed curve rings that must be linearized faithfully before any GIS operation can touch them. Every one of these formats reaches GIS through linearization, and today that step is unspecified and unverified. The corpus already owns the pieces that make it specifiable: the `Linearizes` contract with its two-sided Hausdorff bound, the angle-carrying intake path (ADR-0009's slot), the certified circular egg, `LipInt` for anything defined by an integral, and the winding number for ring interiors. The CAD target reuses all of them and adds only the source-side mappings.

Year 0 means groundwork done before and outside the subsidy year; it produces surveys, mappings, fixtures and oracle choices, not theorems.

**What the formats contain, and where each entity lands.**

| Source entity | Geometry | Corpus home | Notes |
|---|---|---|---|
| DXF `LINE`, `LWPOLYLINE` straight segments, DGN line/linestring | chords | `MkChord` | |
| DXF `ARC` (centre, radius, start/end angle), `CIRCLE`; DGN circular arc | circular arcs | `MkCirc` via the **carried** path | angles are data, so this is carry-and-check, not compute-then-certify |
| DXF `LWPOLYLINE` with bulge | circular arc per segment, bulge b = tan(Δθ/4) | `MkCirc` | Δθ = 4·atan(b), which is `atan3`, 3-axiom; centre and radius follow from the chord |
| DXF `ELLIPSE`, DGN elliptical arc (rotated) | elliptical arcs | SQL/MM `ELLIPTICALCURVE` (§4.2.9) | oracle-instantiable already; no host egg yet |
| DXF `SPLINE`, DGN B-spline | NURBS (degree, knots, control points, weights, or fit points) | `MkNurbs` | fit-point splines need an interpolation step first |
| TrueType `glyf` outlines | quadratic B-splines with implied on-curve midpoints | `MkNurbs` (single-span, unit weights) | closed rings, nonzero winding |
| CFF/PostScript, OpenType CFF2, SVG paths | cubic Béziers, SVG elliptical arcs | `MkNurbs` (single-span, unit weights); elliptical arc as above | SVG arcs use endpoint parameterization and need the centre conversion |
| IFC 4.3 alignment segments | clothoid, Bloss, sine, cosine, polynomial spirals | `MkClothoid`; the other spiral kinds are named declines today | the same spiral families `SPIRALCURVE` names |
| DXF `INSERT` / block references, DGN cells | affine placement of the above | the placement rules of the ISO clothoid intake | similarity placements only; general affine images of arcs are not arcs |

**What is new, and what is not.** Nothing egg-wise is new. A Bézier of degree *p* is exactly a single-span clamped B-spline: the Bernstein basis is the B-spline basis on the knot vector (0..0, 1..1) with *p*+1 repeats at each end, so it is `MkNurbs` with all weights 1 and one span; de Boor on that knot vector is de Casteljau. Fonts and SVG paths join the NURBS lane; `nurbs_wf` holds by construction; the N-L3 hull-flatness bound is the linearizer. Rational Béziers (some CAD exports; conic arcs as rational quadratics, the ζ-chart form) are the same record with weights ≠ 1, i.e. general `MkNurbs`. No new egg and no new ADR. The only year-0 decision is the *carrier*: CAD is not text, so the intake is a structured record (entity, placement, parameters, units, layer) rather than a WKT string. The ADR-0009 span slot is the first such record; the CAD carrier generalizes it. Glyph contours are many spans: represent as a Compound of single-span pieces (exact, C0 at explicit on-curve points, which is what TrueType means), preferred because the fold and `MemberState` exist; the alternative, one multi-span quadratic B-spline with interior knot multiplicity 1 at implied midpoints and 2 at explicit on-curve points, is noted but not chosen. `MkNurbs` stays the fail-closed arm: eggs are constructible and well-formed, but cooks decline until the NURBS letters land; year 0 needs no cooks; year-1 NURBS work gets font fixtures for free.

**Two things CAD does that GIS must not lose.** First, orientation and winding are semantic in fonts and in CAD hatches: glyph interiors are defined by the nonzero winding rule, and the corpus's curve-ring winding is exactly the predicate that decides them. Second, tolerance is expressed differently: CAD linearization is usually a chord-height (sagitta) limit in drawing units, sometimes a segment count, occasionally an angle step; GIS consumers think in coordinate tolerance. The contract's Hausdorff bound is the common currency, and year 0 should write down the conversion for each source's tolerance parameter.

**Oracles and licences.** Year 0 chooses reference implementations for differential tests, not code to port. DXF: `ezdxf` (MIT) reads and linearizes bulges, arcs, ellipses and splines. DWG: the Open Design Alliance SDK (commercial) or `libredwg` (GPL, reference only). DGN: the ODA DGN module or Bentley's own SDK; both are reference only. Fonts: FreeType (FTL/GPL dual) and `fontTools` (MIT) for outline extraction; FreeType's rasterizer is the de facto authority on nonzero winding. IFC: `IfcOpenShell` (LGPL) for alignment segments. None of these code bases may be ported into NTS (BSD-3); they are behavioural references in the same sense GEOS is for arcs.

**Year-0 deliverables.** A survey document per format naming the entities, their parameter conventions (angle direction and units, bulge sign, knot conventions, placement matrices) and the version-specific traps (DXF R12 versus R2000 polylines, DGN V7 versus V8 arcs). The mapping table above, extended with a claimId column that is empty until year 1 fills it. A CAD carrier record definition, with named declines for what is refused (3D solids, hatches as regions, text, dimensions, non-similarity placements). Three locked fixtures: a DXF `LWPOLYLINE` with mixed bulges, a DGN rotated elliptical arc, and one TrueType glyph with a hole (a lowercase "e" or "a"), each with its reference linearization from the chosen oracle. A tolerance-conversion note. Nothing here is a theorem; year 0 ends when a year-1 letter could start from these files without reading the format specifications again.

**The CAD carrier record.**
Authority: [`tools/cad/carrier.schema.json`](tools/cad/carrier.schema.json).
(a) The field is a chain, not a matrix: similarities compose and any
non-similarity link declines the whole entity; `similarity_chain_closed`
is that closure (and tracks det-sign *s*). (b) *s* = sign(det); *s* = −1
negates Δθ, winding, and clothoid σ before check. (c) Sagitta *d* becomes
Hausdorff *k*·*d*; AngleStep/SegmentCount convert after placement from
placed radius, else `ID_ToleranceKindUnsupported`. Year-1 certificates:
`carrier_intake_certified`, `carrier_emit_parse_id`.

**Non-goals.** No DWG parsing in the corpus. No 3D. No rendering semantics for fonts beyond outlines and winding. No claim of round-trip fidelity to CAD; the bridge is one-way, CAD to GIS, through linearization and certified eggs.

### Exact curves

**Bible**:
The governing architecture document for exact curve work — `doc/EXACT_CURVE_BIBLE.md`
(*JTS Arc-Native Programme*, canonical August 2026) on the `feature/sfa-curve-rgr`
branch of the `grootstebozewolf/jts` fork. It is in neither this repo nor the fork's
default branch, so cite it by section (§) and pin the branch commit whenever a claim
leans on it.
_Avoid_: the spec (which one?), architecture doc, bible (lowercase — unfindable)

**Zoo**:
The five Exact* curve types of Bible §4.1: CircularArc (the privileged, served
member), cubic Bézier (replacing the Bible's quadratic — §9 amendment A1,
signed off 2026-08-27), EllipticalArc, Clothoid, and single-span NURBS.
Membership criterion: curves living in the wild engines — never "curves that are
easy to prove". The other ISO 13249-3 curve types (SPIRALCURVE's bloss,
biquadratic, sine and cosine; CIRCLE; GEODESICSTRING) are expansion backlog per
Bible §5 Year 5–7, not members.
_Avoid_: curve types (broader), Exact family (vague), ExactCurve (the protocol, not the roster)

**Exact**:
The Bible §2.2 property: the mathematics is closed-form or exactness-preserving and
never densifies silently — what `isExact()` reports. Says nothing about doubles
agreeing across platforms; that different property is Oracle-stable.
_Avoid_: precise, oracle-stable (different property), exact path (see Laser)

**Oracle-stable**:
Agreement across engines and platforms (C++/Java/.NET) in the `clothoid-halley-coq`
golden-vector sense: |value − reference| < 1e-9 on a shared, checked-in corpus
against one designated reference implementation, plus ≥ 99% iteration-count
agreement where the algorithm iterates. An exact formula can still be
oracle-unstable through libm.
_Avoid_: exact (the Bible §2.2 property), stable (unqualified), bit-exact (stronger, rarely achievable)

**Metric length**:
The 1-D measure of a curve — the number the Bible §4.2 `length()` obligation owes and
`LENGTH_UNIFIED` emits. Never confuse it with `List.length`: lemmas named `*_length`
but proved by `length_map` are element counts stating no metric fact.
`ExactCurveEpic508.v : ticket_508_qed_or_qex` RIGHT on `ECZ_Ellipse`.
Epic #508 stays open. QEX ≠ owner accept. Not “the zoo is exact.”
_Avoid_: unconditionally exact zoo

### Distance metrics

Function inventory: [`docs/scout/map-hausdorff-functions.md`](docs/scout/map-hausdorff-functions.md).
Formal cluster stays epic #423. Do not remint `423-a`.

**Discrete Hausdorff**:
Vertex (optionally densified-segment) max-min. JTS / NTS / GEOS
`DiscreteHausdorffDistance`. Under-estimates the locus value:
discrete ≤ continuous, and densify fraction → 0 approaches the
locus value. Already on NTS develop.
_Avoid_: Directed Hausdorff, Hausdorff (unqualified), DHD (JTS uses
that abbreviation for both the discrete class and the locus class)

**Oriented discrete**:
One-sided discrete max-min (`orientedDistance` / NTS
`OrientedDistance`). Still vertices or densified chords.
_Avoid_: Directed Hausdorff (the locus class)

**Directed Hausdorff**:
Locus max-min over every point of A, not just vertices. Asymmetric.
JTS `DirectedHausdorffDistance` (JTS #1182). Not on NTS develop
(NTS#812 still open) and not on GEOS. Symmetric Hausdorff is the
max of the two directed values.
_Avoid_: Discrete Hausdorff, oriented discrete, DHD

**Densify fraction**:
Segment-length fraction in `(0, 1]` used by
`DiscreteHausdorffDistance`. Not a map-unit tolerance.
_Avoid_: distance tolerance, accuracy, densify (unqualified)

**Distance tolerance**:
JTS `DirectedHausdorffDistance` accuracy in coordinate units — how
close the realizing pair is to the true max-min. Not a densify
fraction and not a free-end clip.
_Avoid_: densify fraction, clip

**Fully within distance**:
JTS `DirectedHausdorffDistance.isFullyWithinDistance` — every point
of A is within `maxDistance` of B. Not `Geometry.isWithinDistance`
(nearest-point, not Hausdorff).
_Avoid_: isWithinDistance (the nearest-point predicate)

### Performance

**Laser**:
The exact, curve-preserving path — an `Exact*` implementation that keeps a curve
a curve through an operation.
_Avoid_: exact path (ambiguous with exact arithmetic), analytic

**Chainsaw**:
The densify/linearise path — the documented escape hatch that replaces a curve
with segments. The baseline a laser is measured against, never a fallback a
laser may silently take.
_Avoid_: linearization (the act, not the path), fallback, approximation

**Laser ratchet**:
The gate `t_laser ≤ 1.15 × t_chainsaw`, measured **per curve type**. A count of
holding gates is not the ratchet; the ratchet is the timings.
_Avoid_: perf gate (the harness that measures it), benchmark, 1.15 rule

### Packaging

**Package**:
One of the two Rocq theory libraries distributed through opam — assembled from
the corpus by a MANIFEST, shipping `.v` files under the `NTS.Proofs` logpath.
They are **not OCaml libraries**: neither contains a line of OCaml, and the
repo's actual OCaml (the extracted oracle) is unpackaged. "The OCaml libraries"
is a phrase to retire; opam is the OCaml *ecosystem*, not the content.
_Avoid_: OCaml library, module (a package holds many), extraction

**Mint**:
A published release of a Package that is **installable from the Rocq opam
archive**. A GitHub release with an attached tarball is not a mint — six of
those exist and none reached the archive.
_Avoid_: release (ambiguous with the GitHub artifact), tag, publish

**Release bar**:
A named checklist plus the gate evidence each line cites, on a pinned corpus
commit, that a Mint must clear. A checklist with no verdict line is a
suggestion; a bar says what it omits.
_Avoid_: definition of done, acceptance criteria, gate (a gate is one line of a bar)

**MMF**:
Minimum Marketable Feature — imported from the `grootstebozewolf/jts` fork,
where it names a release bar plus published gate numbers on a named mint. Here
it means the smallest release a stranger can install and use, which is why
opam-installability is load-bearing rather than cosmetic. The fork's own gates
are not inherited.
_Avoid_: MVP, milestone, marketable (alone — the constraint is *minimum*)

### Differential tooling

**Oracle**:
The Rocq-extracted reference binary that answers geometric queries over a text
line protocol; the source of truth every engine is compared against.
Together with the IEEE↔R bridge it is the test surface for NodingNG /
OverlayNG / RelateNG (ADR-0006 line protocol only).
_Avoid_: reference implementation, ground truth binary

**Reference-only oracle**:
An implementation used for differential testing but never ported, because of licence or provenance (ODA, libredwg, FreeType, IfcOpenShell).

**Harness**:
A runner that puts one engine's answers against the Oracle's on the same inputs
and emits an ok/warn/bug verdict summary.
_Avoid_: test suite, driver

### Interior and boundary

Per **ADR-0003**, "inside a ring" is two-tier. Always say which tier a claim is in.

**Specified interior**:
The OGC **open** interior — `0 < gtri` for a triangle, a strict box for a
rectangle. What DE-9IM matrices and predicates are stated against.
_Avoid_: interior (unqualified), inside

**Computed interior**:
The **half-open** ray-parity region — `point_in_ring` via `edge_crosses_ray`.
What the algorithms and the oracle evaluate. A left edge counts, a right edge does
not; it is not an OGC interior and a theorem over it states no OGC fact.
_Avoid_: interior (unqualified), point_set (as if it were the specification)

**Interior bridge**:
The guarded route from computed to specified interior
(`gtri_point_in_ring_imp_pos` and siblings). Its guards — `ring_complement`,
`ray_avoids_vertices` — are **permanent and load-bearing**, proven maximal by a
Qed refutation of the guard-free form.
_Avoid_: deferral, side condition (both imply temporary)

**Nonzero winding**:
The interior rule for glyph outlines and CAD hatches; decided by the corpus's curve-ring winding number.

### Relate regimes

**Regime**:
A named coarse configuration of a geometry pair — separated, partial overlap,
containment, edge touch, vertex touch — that selects one witness DE-9IM matrix.
The classifier arms are real `gtri`-shaped predicates with pairwise
exclusivity (`RelateMatrixTriangle.v`); `TPR_Unsupported` is a decline record,
not a regime verdict.
_Avoid_: case, mode

**Decline**:
A claim-free answer: the pair is not classified. In Coq that is
`im_unsupported` / `TPR_Unsupported` (supports no `RelatePredicate`). On
the oracle wire that is the token `UNSUPPORTED` in result position, never
a 9-char matrix. A decline is not `FFFFFFFFF`.
_Avoid_: error, unsupported matrix, empty matrix

**Sentinel**:
The honesty marker for a decline (`im_unsupported` in Coq; `UNSUPPORTED`
on the wire). Distinct from a classified disjoint fill. The #530 /
#571 pair is classified disjoint (FFFFFFFFF), not a sentinel.
_Avoid_: default, fallback, catch-all (those hid a wrong matrix)

**Relate bar level**:
How much of a relate claim is proven. Bar 1: the classification itself is
proven true geometry against the specified interior, the fill being the
designated witness matrix. Bar 2: every one of the nine DE-9IM cells is
individually proven true. Spell the bar out in prose; "RBL" is WIP shorthand
only.
_Avoid_: level (unqualified), RBL (in prose)

### Noding constructor (ADR-0007, Accepted)

**Sheet**:
An oriented affine plane `S = (O; e₁, e₂)` with optional lattice `Λ`.
A constructor runs on one sheet; changing `S` or `Λ` is a different instance.
_Avoid_: plane (unqualified), snap grid (that is `Λ` alone)

**Hen**:
A vertex identifier the cook mints. Identity is structural (the cook's
decision), not coordinate-pair equality.
_Avoid_: vertex (the owned point), dart (a coordinate pair)

**Egg**:
An interpolant `γ : [0,1] → S` of a named class.
First cook: `SheetHenCook.v : first_cook_scope_chord_chord` /
`circular_egg_first_cook_scope` / `clothoid_egg_first_cook_scope` / `nurbs_nurbs_first_cook_scope` IN;
mixed/ellipse/sin/geodesic/spiral QEX.
_Avoid_: CurveSegment (`ExactCurveEpic508.v : ticket_508_carrier_qed_or_qex` LEFT: year-1 `CSChord | CSArc`)

**Chicken**:
A directed use of an egg between two hens `(h_src, h_dst, e)`. Twin
reverses orientation. A later remint reseats `Dart` as a hen-id pair —
one view of a chicken, not a third type — so `DartAngularOrder.ddir`
reads `γ'` from the egg. Orbit proofs keep `dart_eq_dec` as *a*
decidable equality.
_Avoid_: dart (coordinate pair), edge (unqualified)

**Cook / 𝓘**:
The pairwise constructor: Hit `(p*, tᵢ, tⱼ)`, Empty (disjoint images),
or 𝓘 Decline (no algorithm). Predicates never mint hens. On a Hit the
cook may `split(t)` and mint hens (`ShareOne` / `MintTwo`). Empty /
Decline / Touch mint nothing. Leftover shared endpoint is not a kiss.
First cook: Egg entry above. Sidecar Hit ≠ host `I_ok`.
_Avoid_: noder (the full loop), snap-rounding (not 𝓘), kiss (for a shared endpoint)

**Parks ι / ρ / Γ**:
`CircularCook.v : ticket_64_circ_gamma_qed_or_qex` LEFT (CircGammaDischarged / MkCirc).
ι / ρ stay named QEX (`SidecarCircIotaArm.v : ticket_0007_iota_arm_qed_or_qex`;
`SheetHenCookLoop.v : leftover_bag_term_arm_missing`).
_Avoid_: reminting sidecar `I_ok_circ` as host Γ

**NodingNG (chord)**:
The product face of ADR-0007 first-cook on one sheet: pairwise 𝓘 +
one cook step (or a finite locked bag of one-steps) yielding
`NodedOnSheet`. Chord–chord only (`NodingNG.v : nodingng_chord_inhabits`,
`NodingNG.v : ticket_0007_nodingng_chord_qed_or_qex`). Empty ≠ Decline.
Snap ≠ 𝓘. Identity is structural (`ShareOne` / `MintTwo`). Not OverlayNG.
Not RelateNG. Not the bag-level repeat-until-noded loop (Parks ρ;
`NodingNG.v : ticket_0007_nodingng_rho_qed_or_qex`).
_Avoid_: noder (the full loop), OverlayNG, RelateNG, DCEL

**OverlayNG (sheet)**:
The product face of Accepted ADR-0007 OverlayNGRobust: a finite
sequence of snap maps `S → Λ` attempted until validate or give up,
on the same sheet as ℝ realization, assuming already-noded `G`
(`OverlayNG.v : overlayng_sheet_inhabits`,
`OverlayNG.v : ticket_0007_overlayng_sheet_qed_or_qex`). Hobby-shaped:
`G` was already noded (`NodingNG.v : nodingng_crossing_noded`;
`SheetHenCook.v : noded_crossing`). Not `𝓘` / cook / NodingNG. Not
OverlayNGCurve Phase-0 point-set algebra (G1–G5). Not Shewchuk A–D.
Not Hobby 4.1 Discharge (`OverlayNG.v : ticket_0007_overlayng_hobby41_qed_or_qex`).
Not Jordan / RelateNG. Not DCEL / Geometry subclass.
_Avoid_: NodingNG, OverlayNGCurve, RelateNG, Hobby 4.1 Discharge, 𝓘

**RelateNG (face)**:
The product face of Accepted DE-9IM / RelateNG chord-lane facts:
matrix algebra + witnesses, honesty decline, and the locked 67-c
line×line exterior-row pin (`RelateNGFace.v : relateng_face_inhabits`,
`RelateNGFace.v : ticket_0007_relateng_face_qed_or_qex`). Consumes
NodingNG / `NodedOnSheet`; does not cook. Not OverlayNG snap. Not
Shewchuk A–D / Hobby / Priest. Jordan: JCT entry above (taut QED; `RNG_JordanUncond` park). Not
#522 leftover remint / T-junction complete / nine-cell
`geom_de9im_pointset`. Not SQL/MM cathedral / DCEL / Geometry subclass.
Completeness stays false (`RelateNGFace.v : ticket_0007_relateng_complete_qed_or_qex`).
_Avoid_: NodingNG, OverlayNG, RelateNG.v (the umbrella), 522-n

**IEEE↔R bridge**:
The two-way binary64 ↔ ℝ coordinate realization the Oracle uses to
generate tests against NodingNG / OverlayNG / RelateNG
(`IeeeRBridge.v : ticket_0007_ieee_bridge_qed_or_qex`). IEEE→ℝ is
`B2R` / `B2R_bp`; ℝ→IEEE is `round` / `ieee_of_Z` under the finite /
no-overflow / int-safe window. Same sheet as ℝ realization. Bridge
≠ `𝓘` / ≠ cook / ≠ OverlayNG snap. Not a full FP noder. Unrestricted
round-trip and kiss-on-binary64 stay named QEX
(`IeeeRBridge.v : ticket_0007_ieee_bridge_fp_noder_qed_or_qex`,
`IeeeRBridge.v : ticket_0007_ieee_bridge_unrestricted_qed_or_qex`).
_Avoid_: cook, OverlayNG snap, FP noder, unrestricted bit-exact

**Clothoid egg (sidecar)**:
`SidecarClothoidEgg.v : ticket_0007_clothoid_egg_qed_or_qex`. Host
`MkClothoid` and clothoid×clothoid first cook landed
(`0007-clothoid-first-cook`). Tag Hit is still Decline.
_Avoid_: Fresnel noding, clothoid noder, Campaign I

**NURBS egg (sidecar)**:
`SidecarNurbsEgg.v : ticket_0007_nurbs_egg_qed_or_qex`. Fail-closed
`MkNurbs` arm (`0007-mk-nurbs`); `OnNurbs` / `NurbsGammaOnSheet`
missing. Scope inhabited; no NURBS Hit.
_Avoid_: length-as-noding, Cox-de-Boor, Campaign I

**Sinusoid egg (sidecar)**:
`SidecarSinEgg.v : ticket_0007_sin_egg_qed_or_qex`. Host Decline;
not first cook.
_Avoid_: profile-as-noding, Campaign I

**Circle egg (sidecar)**:
`SidecarCircEgg.v : ticket_0007_circle_egg_qed_or_qex`. Packaging
only; host cook is `MkCirc` (`0007-gamma-mkcirc`).
_Avoid_: sidecar as host MkCirc, `I_ok_circ` remint

**Elliptic egg (sidecar)**:
`SidecarEllipticEgg.v : ticket_0007_elliptic_egg_qed_or_qex`. Host
Decline; #508 ellipse length stays metric.
_Avoid_: EllipseLength noding, Campaign I

**GeodesicString egg (sidecar)**:
`SidecarGeodesicEgg.v : ticket_0007_geodesic_egg_qed_or_qex`.
`MkOutOfScope`; well-formed bag is the intake-geodesic letter.
_Avoid_: geodesic noder, Spiral egg

**Spiral egg (sidecar)**:
`SidecarSpiralEgg.v : ticket_0007_spiral_egg_qed_or_qex`. One
sidecar egg for ISO §4.2.12 names; `EggClothoid` stays its tag.
Intake on main is `ID_SpiralCurve` (`0007-intake-walker`).
_Avoid_: five host spiral eggs, EggClothoid fold-away

**𝓘 Decline** (ADR-0007 cook):
The pairwise intersection oracle has no algorithm for this egg pair on
this sheet. Distinct from relate Decline and from Empty (disjoint images).
_Avoid_: empty (the disjoint 𝓘 outcome), unsupported matrix

### Roadmap

**Sequencing park**:
Work deferred because it waits on another lane, not because it is hard. It
graduates the moment its gate lands, so it must record *what* gates it.
_Avoid_: parked (unqualified — says nothing about why)

**Research park**:
Work deferred because there is no statement worth proving yet — no published
true form to aim at. It graduates only when someone finds one.
_Avoid_: research-scale (as a synonym for "multi-session" or "hard"), blocked

**Technique park**:
Work deferred with the statement already written and the evidence strong, missing
only a proof method. It graduates when the method is found, so naming the missing
method *is* the deliverable.
_Avoid_: research park (a statement exists), hard, high-risk

**Witness-scoped**:
Proven for named concrete instances rather than universally. An honest partial
result, and this corpus's most reliable route to a usable headline — not a
weaker form of the general claim.
_Avoid_: partial, example-based

### Illustrator

**Case**:
A pair of WKT geometries plus an operation under scrutiny — the question a
sketch answers.
_Avoid_: scenario, example, fixture

**Scenario**:
The composed, drawable form of a Case: linearized geometries, the operation
result, overshoot extracts, and the fit of world coordinates onto a grid.
_Avoid_: scene, model

**Doc**:
The device-independent styled text of a Scenario — lines of colored runs
(header, legend, framed panels). What every Printer consumes.
_Avoid_: styled document, frame buffer, output text

**Printer**:
An adapter that turns a Doc into one concrete medium: ANSI terminal text, or a
PNG facsimile.
_Avoid_: presenter, renderer, emitter, writer

**Facsimile**:
A pixel rendering of a Doc that shows exactly what the terminal shows — the
reproducible replacement for a manual screenshot.
_Avoid_: screenshot (the manual act it replaces), export

**Sketch**:
The human-visible picture of a Case, in whatever medium a Printer produced.
_Avoid_: diagram, illustration, art

**Layer**:
One of the named strata a grid cell can carry: A, B, result, A∩B, A-overshoot,
B-overshoot, and the surface-interior fills of A and B.
_Avoid_: channel, plane

**Overshoot**:
Self-overlap of a single input after linearization — e.g. a CIRCULARSTRING
whose second arc retraces the first.
_Avoid_: self-intersection (narrower), retrace (one kind of overshoot)

## ADR-0007 Accepted

ADR-0007 **Accepted** 2026-09-07. `ContextProseRatchet.v : ticket_508_context_prose_qed_or_qex` LEFT. See `docs/adr/ADR-0007-sheet-hen-cook-noding-model.md`.
