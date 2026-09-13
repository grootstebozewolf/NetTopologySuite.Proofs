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

**Intake walker** (ADR-0007, claimId `0007-intake-walker`):
Successful WKT parse → tagged CST only → mapper total (`CST × Sheet S`)
→ SHC bag | Intake Decline(reason). Grammar accept ≠ valid geometry ≠
cooked graph. Intake Decline ≠ cook `IDecline`. First slice: Point,
LineString, CircularString, CompoundCurve of those two, Circle-as-full-
span-arc (`MkCirc` sweep `2π`). Grammar pin: antlr/grammars-v4 PR #4997
(ISO/IEC 13249-3 §5.1.67). Engines test the bag, not the string. Fail
closed on `GEODESICSTRING` / `SPIRALCURVE`. Unknown well-formed CS
is the angles letter, not leftover Decline. Both CLOTHOID forms
are the MkClothoid letter. No silent chord demote at intake.
_Avoid_: WKT zoo, example3.txt as oracle source, silent chord demote,
new oracle keyword

**Intake angles** (ADR-0007, claimId `0007-intake-angles`):
Intake construction of `CircularEgg` `(O,r,θ₀,Δθ)` from well-formed
WKT circular control points. Three distinct non-collinear points
determine a unique circumcircle; chickens are `MkCirc`. Angle fields
are inhabited from that geometry (θ₀ = sheet e₁ ray, Δθ = oriented
full span ±2π). Host interpolant stays atan2-free egg data — not a
CircGamma remint, not Stdlib atan2 / Ratan classic. Collinear /
duplicate / bad count Decline by name. Clothoid is the MkClothoid
letter, not this one.
_Avoid_: CircGamma remint, silent chord demote, host cook expand,
new oracle keyword

**Intake MkClothoid** (ADR-0007, claimId `0007-intake-mkclothoid`):
One host `MkClothoid` on `Egg` (parallel to `MkCirc`). Grammar has
two clothoid surface forms (ISO REFERENCELOCATION, JTS `(k0,k1,L)`);
both map onto the same locked `ClothoidEgg` bag (OGC≡ISO), whose
vertices are `γ(0)`, `γ(1)` of the small-angle interpolant. Chickens
use `MkClothoid` (`EggClothoid`), not silent `MkChord`. `example5`
bags both forms in one COMPOUNDCURVE. Clothoid×clothoid first cook
already landed (claimId `0007-clothoid-first-cook`, #730 Mode A on
main). Intake stays bag/`MkClothoid` mapping; host Hit is the
Clothoid first-cook paragraph. `EggClothoid` is not folded away.
_Avoid_: two constructors, Fresnel-as-noding, CircGamma remint,
silent chord demote, new oracle keyword

**Clothoid first-cook** (ADR-0007, claimId `0007-clothoid-first-cook`):
Host `EggClothoid × EggClothoid` is in `first_cook_scope`. Locked
`MkClothoid` pair inhabits host `IHit` via `on_cloth` (closed-form
small-angle clothoid: `cos θ≈1`, `sin θ≈θ`; not Fresnel, not
chord-parameter). Small-angle clothoid `γ` is not Halley and
not Fresnel; those stay metric, not the noding/cook engine.
`p1 := γ(1)`. `try_cook_hit` mints `MkClothoid`
hens. Tags stay Decline. Mixed clothoid×chord stays Decline.
Not Fresnel-as-noding. Not a silent `I_ok` demote to `on_chord`.
_Avoid_: Fresnel noding, Halley noding, mixed first cook, NURBS
first cook, Campaign I, new oracle keyword

**SQL/MM signed tag** (ADR-0007, claimId `0007-sqlmm-signed-tag`):
Sidecar map from host eggs we already inhabit onto §5.1.67 names
and Table 15 codes. Signed I/O is {8..12} (plus SFA 1–7). HOLD is
{13..17, 18–21}. Chord → LINESTRING; `MkCirc` → CIRCULARSTRING /
CIRCLE-as-full-span (not code 18); `MkClothoid` → CLOTHOID (both
surface forms, one egg); Mode D joint → COMPOUNDCURVE only when
`eval A 1 = eval B 0`. Ticket `ticket_sqlmm_signed_tag_qed_or_qex`
is QED. Factory emit (`ticket_sqlmm_factory_emit_qed_or_qex`) stays
QEX — Rocq does not inhabit WKT/WKB bytes. Not a new oracle
keyword. Not first-cook expand.
_Avoid_: north-star markdown as inhabitant, factory-as-Qed,
Circle-as-18, silent chord demote, new oracle keyword

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
clothoid, …). First cook scope is chord–chord, circular–circular
(MkCirc), and clothoid–clothoid (MkClothoid).
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
First cook scope is chord–chord, circular–circular (MkCirc), and
clothoid–clothoid (MkClothoid). Host mixed `I_ok` and other
out-of-scope eggs stay Decline. Sidecar `I_ok_circ` / `I_ok_mixed`
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

**Parks ι / ρ** (named QEX, landed — ADR-0007 Parks). **Γ CircGamma**
is discharged by host `MkCirc` (claimId `0007-gamma-mkcirc`):
- **Γ CircGamma** — `circular_gamma_status = CircGammaDischarged`
  (`CircularCook.v : circular_gamma_is_discharged`,
  `CircularCook.v : circ_gamma_mkcirc_inhabits`,
  `CircularCook.v : ticket_64_circ_gamma_qed_or_qex`). Host γ is
  atan2-free `θ₀ + t·Δθ` on `CircularEgg`. nlerp still misses the
  reflex principal span (`CircularCook.v : reflex_nlerp_misses_principal`)
  — that is not the remaining Γ hole. Sidecar `arc_gamma` is not host Γ.
- **ι interior circular×chord** — `I_ok_mixed` Hit stays
  joint-params only (`SidecarCircInterior.v : ticket_0007_iota_gap_qed_or_qex`,
  `SidecarCircInterior.v : interior_mixed_hit_arm_missing`). Sidecar
  `I_ok_interior` inhabits a locked proper-cross Hit
  (`SidecarCircInteriorHit.v : locked_interior_I_ok_interior`,
  `SidecarCircInteriorHit.v : ticket_0007_iota_interior_hit_qed_or_qex`).
  Do not drop the joint gate. ι is not μ, not host `I_ok`, not Γ.
- **ρ bag-loop** — `CookLoopBagTerm` missing; leftover_quad width
  conserved (`Adr0007NodingEpic.v : ticket_0007_cook_term_qed_or_qex`,
  `SheetHenCookLoop.v : leftover_quad_width_conserved`). Pairwise
  leftover-width is QED, not this item. ρ leftover_quad ≠ η Multi bags.
_Avoid_: reminting sidecar `I_ok_circ` as host Γ, soft bool
for interior / bag loop, noder (the full loop)

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

**Clothoid egg (sidecar)**:
The product / sidecar face of clothoid as an EggClass on the
ADR-0007 vocabulary (`SidecarClothoidEgg.v : sidecar_clothoid_egg_inhabits`,
`SidecarClothoidEgg.v : ticket_0007_clothoid_egg_qed_or_qex`). Host
Tag `I_ok` is Decline; tag `try_cook_hit` is None. Locked chord-seed
reuses `RelateClothoid.v : clothoid_chord_proper_cross_share`.
Demote-to-chord is NodingNG / host first cook, not a clothoid Hit.
Host `MkClothoid` inhabits (intake letter). Clothoid×clothoid is
first cook (`SidecarClothoidEgg.v : ticket_0007_clothoid_not_first_cook_qed_or_qex`,
`ClothoidCookMkClothoid.v : ticket_0007_clothoid_first_cook_qed_or_qex`).
The `not_first_cook` ticket name is historical QEX wording; host
first-cook is landed (claimId `0007-clothoid-first-cook`).
Fresnel / Halley stay metric. Not Campaign I–II.
_Avoid_: Fresnel noding, clothoid noder, Campaign I

**NURBS egg (sidecar)**:
The product / sidecar face of NURBS as an EggClass on the
ADR-0007 vocabulary (`SidecarNurbsEgg.v : sidecar_nurbs_egg_inhabits`,
`SidecarNurbsEgg.v : ticket_0007_nurbs_egg_qed_or_qex`). Host
`I_ok` is Decline; `try_cook_hit` is None. Locked unit-square
chords demote to NodingNG / host first cook, not a NURBS Hit.
NURBS×NURBS is not first cook
(`SidecarNurbsEgg.v : ticket_0007_nurbs_not_first_cook_qed_or_qex`).
#508 length / golden quarter stay metric. Not Campaign I–II.
_Avoid_: host cook, length-as-noding, Cox-de-Boor, NURBS noder, Campaign I

**Sinusoid egg (sidecar)**:
The product / sidecar face of sinusoid as an EggClass on the
ADR-0007 vocabulary (`SidecarSinEgg.v : sidecar_sin_egg_inhabits`,
`SidecarSinEgg.v : ticket_0007_sin_egg_qed_or_qex`). Host
`I_ok` is Decline; `try_cook_hit` is None. Locked unit-square
chords demote to NodingNG / host first cook, not a sinusoid Hit.
Sinusoid×sinusoid is not first cook
(`SidecarSinEgg.v : ticket_0007_sin_not_first_cook_qed_or_qex`).
Thin Spectre `sine_profile` corpus stays profile research, not cook.
Not Campaign I–II.
_Avoid_: host cook, profile-as-noding, sinusoid noder, Campaign I

**Circle egg (sidecar)**:
The product / sidecar face of `EggCircularArc` on the ADR-0007
vocabulary (`SidecarCircEgg.v : sidecar_circ_egg_inhabits`,
`SidecarCircEgg.v : ticket_0007_circle_egg_qed_or_qex`). Packages
the already-Qed host Decline fence (`circular_decline_I_ok`,
`try_cook_hit_circular_hit_none`). Locked unit-square chords
demote to NodingNG / host first cook, not a circular Hit.
Sidecar CircEgg stays packaging: host Decline-on-tag plus demoted
chord seed (`SidecarCircEgg.v : ticket_0007_circle_not_first_cook_qed_or_qex`).
Host circular cook is MkCirc (claimId `0007-gamma-mkcirc`), not this
sidecar. Does not remint CircularCook* Campaign I/II as host.
_Avoid_: reminting sidecar CircEgg as host MkCirc, Campaign I, I_ok_circ remint

**Elliptic egg (sidecar)**:
The product / sidecar face of `EggEllipse` on the ADR-0007
vocabulary (`SidecarEllipticEgg.v : sidecar_elliptic_egg_inhabits`,
`SidecarEllipticEgg.v : ticket_0007_elliptic_egg_qed_or_qex`). Host
`I_ok` is Decline; `try_cook_hit` is None. Locked chord-seed reuses
`RelateEllipticArc.v : elliptic_arc_chord_proper_cross_share`.
Demote-to-chord is NodingNG / host first cook, not an elliptic Hit.
Ellipse×ellipse is not first cook
(`SidecarEllipticEgg.v : ticket_0007_elliptic_not_first_cook_qed_or_qex`).
#508 ellipse length / elliptic-E stay metric. Not Campaign I–II.
_Avoid_: host cook, EllipseLength noding, elliptic noder, CircGamma remint, Campaign I

**GeodesicString egg (sidecar)**:
The product / sidecar face of `EggGeodesicString` on the ADR-0007
vocabulary (`SidecarGeodesicEgg.v : sidecar_geodesic_egg_inhabits`,
`SidecarGeodesicEgg.v : ticket_0007_geodesic_egg_qed_or_qex`). Host
`I_ok` is Decline; `try_cook_hit` is None. Locked unit-square
chords demote to NodingNG / host first cook, not a geodesic Hit.
Geodesic×geodesic is not first cook
(`SidecarGeodesicEgg.v : ticket_0007_geodesic_not_first_cook_qed_or_qex`).
SQL/MM ST_GeodesicString type-zoo packaging (MkOutOfScope); geodetic
interpolant stays research, not cook. Not Zoo membership. Not
Campaign I–II. Not Spiral egg.
_Avoid_: host cook, geodesic noder, geodetic interpolant, CircGamma remint, Campaign I, Spiral egg

**Spiral egg (sidecar)**:
The product / sidecar face of `EggSpiralCurve` on the ADR-0007
vocabulary (`SidecarSpiralEgg.v : sidecar_spiral_egg_inhabits`,
`SidecarSpiralEgg.v : ticket_0007_spiral_egg_qed_or_qex`). Host
`I_ok` is Decline; `try_cook_hit` is None. Locked unit-square
chords demote to NodingNG / host first cook, not a spiral Hit.
Spiral×spiral is not first cook
(`SidecarSpiralEgg.v : ticket_0007_spiral_not_first_cook_qed_or_qex`).
SQL/MM ST_SpiralCurve (ISO 13249-3 §4.2.12) type-zoo packaging
(MkOutOfScope); five required names (clothoid, bloss, biquadratic,
sine, cosine) plus Unknown inhabit one sidecar egg. `EggClothoid`
stays its own host tag — the clothoid arm is a nameplate, not a
remint. Not Zoo membership. Not interpolant math. Not Γ. Last
Lesson-1 packaging extra.
_Avoid_: host cook, spiral noder, spiral interpolant, five host spiral eggs, EggClothoid fold-away, CircGamma remint, Campaign I, Γ

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

ADR-0007 (sheet/hen/cook) **Accepted** 2026-09-07 by Joost (BDFL). Soft gaps closed. Parks ι / ρ remain landed named QEX. Γ CircGamma is discharged by host MkCirc (claimId `0007-gamma-mkcirc`; `CircularCook.v : circular_gamma_is_discharged`). NodingNG chord is the cook product face (`theories/NodingNG.v`): 𝓘 + one cook step on one sheet; ρ stays obligation. OverlayNG sheet is the snap product face (`theories/OverlayNG.v`): finite snap-sequence ≠ `𝓘` on one sheet; Hobby 4.1 stays Honest remaining. RelateNG face is the DE-9IM product face (`theories/RelateNGFace.v`): matrix/witness + honesty decline + 67-c pin; completeness / Jordan / S15l+ / 523 `?` stay named QEX. IEEE↔R bridge is the Oracle test-surface face (`theories-flocq/IeeeRBridge.v`): two-way binary64 ↔ ℝ under the int-safe regime; FP noder / unrestricted / kiss stay Honest remaining. Clothoid egg sidecar is the cook-axis EggClass face (`theories/SidecarClothoidEgg.v`): tag-Decline + RelateClothoid chord-seed; clothoid×clothoid first cook is QED (`theories/ClothoidCookMkClothoid.v`, claimId `0007-clothoid-first-cook`). NURBS egg sidecar is the next cook-axis EggClass face (`theories/SidecarNurbsEgg.v`): Decline-on-host + demoted unit-square chord-seed; NURBS×NURBS stays QEX; #508 length stays metric. Sinusoid (SIN) egg sidecar is the next cook-axis EggClass face (`theories/SidecarSinEgg.v`): Decline-on-host + demoted unit-square chord-seed; sinusoid×sinusoid stays QEX; thin Spectre profile corpus stays research, not cook. Circle / circular egg sidecar is the next cook-axis EggClass face (`theories/SidecarCircEgg.v`): packages host EggCircularArc tag-Decline + demoted unit-square chord-seed; host circular cook is MkCirc (`theories/CircularCookMkCirc.v`), not this sidecar. Elliptical Curve / EllipticArc egg sidecar is the next cook-axis EggClass face (`theories/SidecarEllipticEgg.v`): Decline-on-host + RelateEllipticArc chord-seed; ellipse×ellipse stays QEX; #508 ellipse length / elliptic-E stay metric. SQL/MM GeodesicString egg sidecar is the next cook-axis EggClass face (`theories/SidecarGeodesicEgg.v`): Decline-on-host + demoted unit-square chord-seed; geodesic×geodesic stays QEX; type-zoo packaging (MkOutOfScope), not Γ progress. SQL/MM ST_SpiralCurve egg sidecar is the last Lesson-1 cook-axis EggClass face (`theories/SidecarSpiralEgg.v`): Decline-on-host + demoted unit-square chord-seed; five ISO names + Unknown on one egg; `EggClothoid` stays; spiral×spiral stays QEX; type-zoo packaging (MkOutOfScope), not Γ / not 𝓘 progress. ι interior Hit discharge is the sidecar circular×chord face (`theories/SidecarCircInteriorHit.v`): distinct `I_ok_interior` Hit; `I_ok_mixed` joint gate stands. Intake walker is the first-slice WKT → CST → SHC bag seam (`theories/IntakeWalker.v`, claimId `0007-intake-walker`): grammar pin grammars-v4 #4997; Intake Decline ≠ cook Decline; no silent chord demote. Intake angles is the CircUnknown construction (`theories/IntakeAngles.v`, claimId `0007-intake-angles`): unique circumcircle + inhabited angle fields → `MkCirc`; collinear / duplicate / bad count Decline by name; not a CircGamma remint. Intake MkClothoid is the host clothoid constructor (`theories/SheetHenClothoidEgg.v`, claimId `0007-intake-mkclothoid`): one `MkClothoid` on `Egg`; ISO and JTS clothoid bag the same locked egg. Clothoid first-cook is the Hit letter (`theories/ClothoidCookMkClothoid.v`, claimId `0007-clothoid-first-cook`). SQL/MM signed tag is the sidecar name/code map (`theories/SqlMmSignedTag.v`, claimId `0007-sqlmm-signed-tag`): host eggs inhabit signed tags; HOLD codes do not; factory emit stays QEX. See `docs/adr/ADR-0007-sheet-hen-cook-noding-model.md`. CRV-TOUCH assumes this vocabulary; kiss/FP noder remain on that map.
