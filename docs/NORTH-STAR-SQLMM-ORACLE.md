# North star — SQL/MM Part 3 example oracle (JTS #7)

claimId: `0007-north-star-sqlmm-oracle`
Status: destination (not a discharge)
Board: ADR-0006 **Accepted** · ADR-0007 **Accepted** · ADR-0008 **Proposed**
Consumer: [grootstebozewolf/jts#7](https://github.com/grootstebozewolf/jts/pull/7) (pin only)
Grammar pin: [antlr/grammars-v4#4997](https://github.com/antlr/grammars-v4/pull/4997) merge `181f4c9` (ISO/IEC 13249-3 §5.1.67)
WKB: ISO/IEC 13249-3 §5.1.68 Table 15

QED∨QEX **LEFT**: every claim below is a destination. This letter does not inhabit emit, JTS #7 round-trip, or cook parks. Docs ticket in the PR body (`ticket_0007_north_star_sqlmm_qed_or_qex`); no `.v` sibling.

Cite leftover-0 (MkClothoid first-cook landed), #729, CircGamma (`0007-gamma-mkcirc` / `MkCirc`), ρ (`LeftoverBagTermArm`) as parks / siblings. Do not reopen.

## Destination

Locked SHC bag on one sheet \(S\) → every instantiable §5.1.67 WKT and §5.1.68 WKB (XDR+NDR) example that JTS #7 must round-trip through the pinned ANTLR grammar. Inverse of intake. No new ADR-0006 keyword. No silent chord demote at emit or intake.

```
locked SHC bag on S
        |-► WKT  (§5.1.67, ANTLR-valid against the pin)
        └-► WKB  (§5.1.68 Table 15, XDR + NDR hex)
                ▼
     JTS #7 reader / writer (type-preserving; no toLinear)

WKT ─ANTLR► tagged CST ─μ(CST × S)► SHC bag | named Intake Decline
```

Grammar accept ≠ valid geometry ≠ cooked graph. Intake Decline ≠ cook `IDecline`. Engines test the bag. Display is a view (CONTEXT).

## Parks (still destinations)

| Claim | State |
|---|---|
| geodesic | **not closed** — planar `GEODESICSTRING` bags `MkChord` (`SidecarGeodesicEgg`, `IntakeGeodesicCook`); ambient / ellipsoid / WKB 13 / `GEODESICSTRING` emit stay QEX |
| `RNG_JordanUncond` | park (`RelateNGFace`, `RelateNGJordanTrueRegion`) |
| `LeftoverBagTermArm` | **uninhabited** (ρ QEX; `SheetHenCookLoop`) |
| host circ×chord | **QEX** — `~ first_cook_scope EggChord EggCircularArc` (`SheetHenCook`); #796 open, did not flip |
| ADR-0008 | **Proposed** |

`first_cook_scope` stays chord×chord, circ×circ, clothoid×clothoid. Not `EggNurbs`. Not `EggGeodesicString`. Sidecar `I_ok_mixed` / `I_ok_interior` Hit is not host `I_ok`.

## Done-when (locked rows; destination, not Qed)

Every instantiable §5.1.67 type has a locked row:

1. WKT the pinned grammar accepts (`wktLexer.g4` / `wktParser.g4`; clothoid fixture `example5.txt`, not `example3.txt`).
2. Matching WKB hex, NDR and XDR.
3. EMPTY / Z / M / ZM where the clause defines them.
4. Mapper verdict: SHC bag **or** named Intake Decline (`ID_Collinear`, `ID_DuplicateControl`, `ID_MkOutOfScope`, fail-closed `GEODESICSTRING` / `SPIRALCURVE`, …).
5. JTS #7 reads both encodings and writes them back **without** `toLinear` / densify.
6. Oracle engines see the bag (or never see the Decline). No new keyword.

A type may meet (1)–(5) and stay cook-QEX.

**Shelf A** (signed I/O destination): `POINT` / `LINESTRING` / `POLYGON` + Multi / Collection / EMPTY; `CIRCULARSTRING` 3 and 2n+1; `CIRCLE` as full-span `MkCirc` (not WKB 18); `COMPOUNDCURVE` LS+CS with named joints (`cs_joint_circ` / Mode D); `CURVEPOLYGON`; `MULTICURVE` / `MULTISURFACE`; `CLOTHOID` both surface forms → same `MkClothoid` + `cloth_joint` compound.

**Shelf B** (grammar-complete, cook Decline / QEX destination): `ELLIPTICALCURVE`, `NURBSCURVE`, `GEODESICSTRING`, `SPIRALCURVE` (five ISO names only), `COMPOUNDSURFACE`, `BREPSOLID`, ISO `TRIANGLE` / `POLYHEDRALSURFACE PATCHES` / `TIN`. Mapper: named Decline or `MkOutOfScope`. #729 stays HOLD.

**Shelf C**: HOLD hex for codes 13–17 and 18–21. Not signed I/O. Not Circle-as-18.

## What this is not

- A new ADR-0006 keyword (`INTAKE` / `WKT_EMIT` / anything else).
- Silent chord demote at emit or intake.
- `first_cook_scope` expand; remint of `I_ok_mixed` / `leftover_quad_width_decreases`.
- CircGamma remint; do not claim Parks ρ / ι / geodesic as discharged.
- Accept ADR-0008; EWKB / SRID as the ISO example; GML.

## In-tree today (not the star)

`tools/SqlMmExampleFactory` and `oracle/fixtures/sqlmm/shelf-a/*` are tools bytes / starter smoke. `SqlMmSignedTag.v : ticket_sqlmm_factory_emit_qed_or_qex` stays **QEX** (Rocq does not inhabit byte strings). That is not the full zoo and not JTS #7 round-trip Qed.

Do not merge from this courier. Land the doc when you say go.
