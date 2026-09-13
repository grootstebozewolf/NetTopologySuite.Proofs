# North star — SQL/MM Part 3 example oracle (JTS #7)

claimId: none (docs / packaging)
Status: destination, not a letter
Board: ADR-0006 (Accepted) + ADR-0007 (Accepted)
Consumer: [grootstebozewolf/jts#7](https://github.com/grootstebozewolf/jts/pull/7)
Grammar pin: [antlr/grammars-v4#4997](https://github.com/antlr/grammars-v4/pull/4997) merge `181f4c9` (ISO/IEC 13249-3 §5.1.67)
WKB codes: ISO/IEC 13249-3 §5.1.68 Table 15

#740 (`cloth_joint` on `cloth_split` children) is on `main`. This document does not reopen first-cook scope, leftover-0, #729, or CircGamma.

## One sentence

From a sheet of hens and eggs we can mint every SQL/MM Part 3 WKT string and WKB blob JTS #7 must round-trip, through the pinned ANTLR grammar and the intake mapper, without a new oracle keyword and without silently turning a curve into a chord.

## What “oracle that can create examples” means

The existing oracle (`oracle/driver.ml`, ADR-0006 line protocol) decides things *on a bag*. It does not parse WKT. It will not grow an `INTAKE` or `WKT_EMIT` keyword.

The missing piece is the **inverse of intake**:

```
locked SHC bag on one sheet S
        │
        ├─► WKT  (§5.1.67, ANTLR-valid against the pin)
        └─► WKB  (§5.1.68 Table 15, XDR + NDR hex)
                │
                ▼
     JTS #7 reader / writer
     (type-preserving; no toLinear on the I/O path)
```

Intake already runs the other way:

```
WKT ─ANTLR─► tagged CST ─mapper(CST × S)─► SHC bag | named Intake Decline
```

Engines still test the bag, not the string. Display stays a view (CONTEXT). The factory is how display gets a locked zoo instead of hand-copied fixtures.

Grammar accept ≠ valid geometry ≠ cooked graph. Intake Decline ≠ cook `IDecline`.

## Why JTS #7

#7 is the curve-awareness branch that already owns:

- types + WKT round-trip without densify
- signed WKB I/O for codes **8–12** (CircularString, CompoundCurve, CurvePolygon, MultiCurve, MultiSurface)
- HOLD on codes **13–17** and **18–21** (do not advertise as signed I/O; not Circle-as-18; not Clothoid-as-22)
- OverlayNGCurve and TestBuilder as consumers of the same strings

Proofs is the place that can *mint* those strings from eggs we already inhabit (`MkCirc`, `MkClothoid`, chords, compound of those) and from eggs we only package (`MkOutOfScope` sidecars). JTS #7 should not invent a second grammar.

## Sheet / hen / cook is the source, not the wire

| Word | Job in this factory |
|---|---|
| Sheet `S` | One oriented affine plane. Every coordinate in an example lives on `S`. Z/M ride as bag extras, not a second sheet. |
| Egg | The interpolant. Host first-cook eggs today: chord, `MkCirc` circular, `MkClothoid` clothoid. Everything else is a tagged egg or `MkOutOfScope`. |
| Hen | Identity of a point or a joint. Mode D joints (`cs_joint_circ`, `cloth_joint`) are endpoint hens, not interior `I_ok` Hits. |
| Chicken | Directed use of an egg between two hens. A `COMPOUNDCURVE` is chickens in order, joints required. |
| Cook / `𝓘` | Not used to *emit* WKT. Cook is how JTS #7 later nodes the bag. Factory must not pretend a Decline pair is noded. |
| Bag | What the oracle already consumes. Factory serializes a bag; intake rehydrates it. |

A CompoundCurve example is not “two WKT fragments glued with a comma.” It is two eggs whose `eval A 1 = eval B 0` (the Mode D joint we just landed for clothoid, and #733 for circular). If the factory cannot name that joint, it must not emit the compound.

## Grammar and codes — one pin, two layers

**WKT syntax** is the pinned pair

- `tools/WktIntakeWalker/grammar/wktLexer.g4`
- `tools/WktIntakeWalker/grammar/wktParser.g4`

Do not invent productions. Clothoid fixture is `example5.txt` (both ISO `REFERENCELOCATION` and JTS `(k0,k1,L)`). Not `example3.txt`.

**WKB type codes** (signed I/O vs HOLD) stay the JTS #7 contract:

| Code | Type | Factory duty |
|---:|---|---|
| 1–7 | SFA Point … GeometryCollection | Emit. Already boring. |
| 8 | CircularString | Emit. Locked 3-point and 2n+1. |
| 9 | CompoundCurve | Emit. Children keep their own type. Joints named. |
| 10 | CurvePolygon | Emit. Rings carry their own type. |
| 11 | MultiCurve | Emit. |
| 12 | MultiSurface | Emit. |
| 13–17 | Triangle / PolyhedralSurface / TIN / … as HOLD | Emit only as tagged HOLD fixtures. |
| 15–24, 102 | Extended ISO set in the epic | Grammar may parse the WKT; WKB I/O on #7 stays HOLD until a letter signs it. |
| 18–21 | Preview codes (ellipse / Bézier / NURBS theatre) | HOLD. Not signed I/O. Not Circle-as-18. |

Z / M / ZM / EMPTY variants exist where §5.1.67 defines them. SRID / EWKB is out of this north star (PostGIS flavour is a later adapter, not the ISO example).

## Done-when (the actual star)

The factory is done when **every instantiable SQL/MM Part 3 type in §5.1.67** has a locked row:

1. WKT that the pinned ANTLR grammar accepts.
2. Matching WKB hex, little-endian and XDR.
3. EMPTY / Z / M / ZM rows where the clause defines them.
4. Mapper verdict: SHC bag **or** a *named* Intake Decline (`ID_Collinear`, `ID_DuplicateControl`, `ID_MkOutOfScope`, fail-closed `GEODESICSTRING` / `SPIRALCURVE`, …).
5. A JTS #7 test that reads both encodings and writes them back **without** `toLinear` / densify on that path.
6. Oracle engines still see the bag (or never see the Decline). No new keyword.

A type can satisfy (1)–(5) and still be cook-QEX. That is honest. NURBS×NURBS, ellipse×ellipse, geodesic×geodesic, spiral×spiral, ι interior mixed Hit, ρ bag-loop stay QEX. The example still has to exist.

## Three shelves (build in this order)

### Shelf A — signed I/O, host eggs we already inhabit

Emit and round-trip:

- `POINT`, `LINESTRING`, `POLYGON`, their Multi / Collection, EMPTY
- `CIRCULARSTRING` (3 and 2n+1), including the locked disc used for area-25π
- `CIRCLE` as full-span `MkCirc` (intake angles letter), not as WKB 18
- `COMPOUNDCURVE` of LineString + CircularString, joints via existing `circ_split_join` / Mode D
- `CURVEPOLYGON` whose rings are those
- `MULTICURVE` / `MULTISURFACE` of the above
- `CLOTHOID` both surface forms → same `MkClothoid` bag; compound that *uses* `cloth_joint` (the letter just merged)

This shelf is the JTS #7 daily driver. If a string on this shelf densifies on the way through #7, that is a #7 bug, not a Proofs gap.

### Shelf B — grammar-complete, cook Decline / QEX

The pin already lexes these. Factory must still mint them so #7 and PostGIS harnesses have bytes:

- `ELLIPTICALCURVE`, `NURBSCURVE`
- `GEODESICSTRING`, `SPIRALCURVE` (five ISO names only; free-form `SPIRALTYPE` stays out — grammar fence)
- `COMPOUNDSURFACE`, `BREPSOLID`
- ISO forms of `TRIANGLE`, `POLYHEDRALSURFACE PATCHES`, `TIN PATCHES/ELEMENTS`

Mapper verdict is named Decline or `MkOutOfScope`. JTS #7 may parse and retain structure; it must not pretend first-cook lives here. #729 (NURBS first-cook) stays HOLD until it is a clean letter.

### Shelf C — HOLD WKB preview

Hex dumps for codes 13–17 and 18–21, labelled HOLD in the fixture header. Not in the signed round-trip suite. Not advertised in #7 docs as I/O.

## What this is not

- Not a new ADR-0006 keyword.
- Not CircGamma reminted. `MkCirc` already discharged Γ.
- Not first-cook expand. Mixed clothoid×chord stays Decline.
- Not ρ / Campaign / Fresnel-as-noding / length-as-noding.
- Not silent chord demote at emit *or* at intake.
- Not EWKB / SRID as the ISO example (adapter later).
- Not GML.
- Not “the oracle prints pretty WKT from floats.” Binary64 realises the same sheet; the locked examples are exact on `S`, then displayed.

## Shape of the factory (when a letter builds it)

One directory, one mapping table, shared with intake:

```
tools/WktIntakeWalker/          # ANTLR pin + visitor (already)
tools/SqlMmExampleFactory/      # bag → WKT + WKB  (new, inverse)
oracle/fixtures/sqlmm/          # locked rows the factory must reproduce
  shelf-a/*.wkt + *.wkb.hex
  shelf-b/*.wkt + *.wkb.hex
  shelf-c/HOLD-*.wkb.hex
```

Rocq side stays thin: inhabit the locked eggs we already have; do not grow `SheetHenCook.v`. Sidecars keep packaging. Print Assumptions on any new lemma stays 3-axiom classical-reals.

JTS #7 consumes the fixture directory as test resources. Proofs CI checks: grammar accept, mapper verdict stable, WKB hex stable, no new keyword in `oracle/driver.ml`.

## Immediate board (Sunday, after #740)

- This document is the north star. It is not a letter and does not need Qed.
- Monday can rest from *letters*.
- Next letter, when you want one, is Shelf A emit for types we already bag — not NURBS first-cook, not a Java twin of #740, not ρ.

Do not merge from this courier. Land the doc when you say go.
