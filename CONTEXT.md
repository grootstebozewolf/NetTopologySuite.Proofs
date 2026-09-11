# NetTopologySuite.Proofs

A Rocq/Coq proof corpus accompanying NetTopologySuite, plus the differential
tooling that compares real geometry engines (NTS, GEOS) against the extracted
oracle and pictures the cases under scrutiny.

## Language

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

**ISO validity**:
Every spec "shall" beyond representability, owned by arc-aware `ST_IsValid`:
implemented rules answer definite-false naming their clause; unimplemented
rules fail closed (throw naming the missing rung) — never an unchecked
`true`.
_Avoid_: invalid (for merely un-checked values), IsValid returns true (until
the rung that checks it lands)

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
Bible §4.2 satisfaction (what is proved vs parked) lives in
`docs/scout/508-closing-summary.md`. The zoo is not unconditionally
exact: elliptic E and Fresnel clothoid stay engine-conditional; oracle
`LENGTH_UNIFIED` is still C/A. Owner review retires epic #508.
_Avoid_: length (unqualified where a count could be meant), size,
planned length zoo (the 508-* letters landed), unconditionally exact zoo

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
An interpolant `γ : [0,1] → S` of a named class (chord, circular arc,
clothoid, …). First cook scope is chord–chord only.
_Avoid_: CurveSegment (year-1 `CSChord | CSArc`, not reminted here)

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
First cook scope is chord–chord. Host circular / mixed `I_ok` is
Decline for out-of-scope eggs. Sidecar `I_ok_circ` / `I_ok_mixed`
Hit is not host `I_ok`. Four-object fence: `I_circles_z` ≠
`I_circles_gamma` ≠ sidecar cook ≠ host `I_gloss`. Snap-rounding is
a different constructor under already-noded `G`. Display is a view.
binary64 realizes the same sheet. OverlayNGRobust is a snap-sequence
`S → Λ`, not 𝓘. A **kiss** (tangent eggs, discriminant zero) is not
a shared endpoint; CRV-TOUCH owns the certificate. Arc cook
termination is a sister card. Accepting ADR-0007 is out of scope of
that map. Campaign I / II / Phase B ticket evidence lives on the
ADR-0007 checklist and in `docs/verified-claims.md`.
_Avoid_: noder (the full loop), snap-rounding (not 𝓘), kiss (for a shared endpoint)

**Parks Γ / ι / ρ** (named QEX, landed — ADR-0007 Parks):
- **Γ CircGamma** — Egg has no `MkCirc`; nlerp misses the reflex
  principal span (`CircularCook.v : ticket_64_circ_gamma_qed_or_qex`,
  `CircularCook.v : circ_gamma_mkcirc_missing`,
  `CircularCook.v : reflex_nlerp_misses_principal`). Sidecar
  `arc_gamma` is not host Γ.
- **ι interior circular×chord** — `I_ok_mixed` Hit is joint-params
  only (`SidecarCircInterior.v : ticket_0007_iota_gap_qed_or_qex`,
  `SidecarCircInterior.v : interior_mixed_hit_arm_missing`). ι is
  not μ, not host `I_ok`, not Γ.
- **ρ bag-loop** — `CookLoopBagTerm` missing; leftover_quad width
  conserved (`Adr0007NodingEpic.v : ticket_0007_cook_term_qed_or_qex`,
  `SheetHenCookLoop.v : leftover_quad_width_conserved`). Pairwise
  leftover-width is QED, not this item. ρ leftover_quad ≠ η Multi bags.
_Avoid_: atan2-free interpolant remaining (the named Γ gap), soft bool
for CircGamma / interior / bag loop, noder (the full loop)

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
Shewchuk A–D / Hobby / Priest. Not full unconditional Jordan. Not
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

ADR-0007 (sheet/hen/cook) **Accepted** 2026-09-07 by Joost (BDFL). Soft gaps closed. Parks Γ / ι / ρ are landed named QEX. NodingNG chord is the cook product face (`theories/NodingNG.v`): 𝓘 + one cook step on one sheet; ρ stays obligation. OverlayNG sheet is the snap product face (`theories/OverlayNG.v`): finite snap-sequence ≠ `𝓘` on one sheet; Hobby 4.1 stays Honest remaining. RelateNG face is the DE-9IM product face (`theories/RelateNGFace.v`): matrix/witness + honesty decline + 67-c pin; completeness / Jordan / S15l+ / 523 `?` stay named QEX. IEEE↔R bridge is the Oracle test-surface face (`theories-flocq/IeeeRBridge.v`): two-way binary64 ↔ ℝ under the int-safe regime; FP noder / unrestricted / kiss stay Honest remaining. See `docs/adr/ADR-0007-sheet-hen-cook-noding-model.md`. CRV-TOUCH assumes this vocabulary; kiss/FP noder remain on that map.
