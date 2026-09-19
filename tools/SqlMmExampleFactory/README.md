# SqlMmExampleFactory

claimId: none (tools / docs)

Java ST4 tools bytes: locked SHC bag → ISO/IEC 13249-3:2016 WKT (§5.1.67) and WKB hex (§5.1.68 Table 15). Does **not** remint Rocq emit: `SqlMmSignedTag.v : ticket_sqlmm_factory_emit_qed_or_qex` stays **QEX**. Destination / fences: [`docs/NORTH-STAR-SQLMM-ORACLE.md`](../../docs/NORTH-STAR-SQLMM-ORACLE.md).

Grammar pin: [grammars-v4 #4997](https://github.com/antlr/grammars-v4/pull/4997) `181f4c9` under `tools/WktIntakeWalker/grammar/`. Consumer: [JTS #7](https://github.com/grootstebozewolf/jts/pull/7) (pin only).

AI assistance disclosure: drafted with AI assistance (Cursor Grok 4.6); human review remains required.

## Templates

| File | Job |
|---|---|
| `templates/SqlMmWkt.stg` | §5.1.67 text |
| `templates/SqlMmWkb.stg` | §5.1.68 hex assembly |

WKT rules: `wkt`, `emptyWkt`, `simpleWkt`, `compoundWkt` / `compoundMember` (LS children bare), `clothoidWkt` / `clothoidJts` / `clothoidIso`, `xy`.
WKB rules: `wkb`, `wkbSigned`, `countedPoints`, `compoundPayload`, `wkbHold`.
Byte order: `00` XDR, `01` NDR. Doubles IEEE-754 binary64 (Java fills hex; group concatenates).

## Shelf A this slice (starter)

| Surface | WKT | WKB | Notes |
|---|---|---|---|
| `POINT` | wired | 1 NDR+XDR | `EMPTY` WKT-only; WKB HOLD this slice |
| `LINESTRING` (+ `EMPTY`) | wired | 2 NDR+XDR | empty = count 0 |
| `CIRCULARSTRING` | wired | 8 NDR+XDR | locked 3-point |
| `CIRCLE` | wired | HOLD | full-span `MkCirc`; **not** WKB 18 |
| `COMPOUNDCURVE` of LS + CS | wired | 9 NDR+XDR | children keep type; joints are hen ids |
| `CLOTHOID` JTS `(k0,k1,L)` | wired | HOLD | **not** WKB 22 |
| `CLOTHOID` ISO `REFERENCELOCATION` | wired | HOLD | same `MkClothoid` bag as JTS |
| `GEODESICSTRING` | emits as `LINESTRING` | 2 | τ=`TagLineString` on `MkChord`; **not** WKB 13 |

HOLD this slice: WKB **13–17** / **18–21**. Not first-cook expand. Polygon / Multi / CurvePolygon / MultiCurve / MultiSurface are later rows.

Model fields match intake: `hens`, `pts`, `chickens` (`MkChord` / `MkCirc` / `MkCirc:quarter` / `MkCirc:full` / `MkClothoid`), `keyword`, `controls`, `children`, `tau`, clothoid `k0`/`k1`/`L` vs ISO placement.

`τ = first_slice_tag`: `MkChord ↦ TagLineString`. Well-formed geodesic CST bags the same `MkChord` as `LINESTRING`; emit is LINESTRING / WKB 2 — honest chord bag, not silent densify-as-curve, not signed geodesic I/O.

## Run

```
bash tools/SqlMmExampleFactory/smoke.sh
bash tools/SqlMmExampleFactory/generate.sh
```

μ parse-back: C# intake (`pwsh tools/WktIntakeWalker/generate.ps1` + `dotnet run --project tools/WktIntakeWalker`). `tests/SqlMmFactoryHunt` drives that CLI via `HuntHost`. `generate.sh` fetches ST4 4.3.4 + `antlr-runtime` 3.5.3 into `.lib/` (gitignored).

Smoke: locked LINESTRING / chord bag parses and μ-equals; WKB hex stable NDR+XDR on Point / LineString / CircularString / CompoundCurve (9); both clothoid spellings → locked `MkClothoid`; CIRCLE / CLOTHOID WKB stay HOLD.
