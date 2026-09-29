# WktIntakeWalker

Intake seam for ADR-0007 (claimId `0007-intake-walker`, angles
claimId `0007-intake-angles`, clothoid claimId `0007-intake-mkclothoid`).

House style: **.NET / PowerShell / Cake / Red-Green-Refactor**
(same direction as `tests/SqlMmFactoryHunt` on #748). Grammar pin
unchanged: ANTLR copies under `grammar/` from
[grammars-v4 #4997](https://github.com/antlr/grammars-v4/pull/4997)
merge `181f4c9` (`PIN.md`). Do not invent productions.

Successful WKT parse (ANTLR C# target, `Antlr4.Runtime.Standard`)
→ tagged CST → mapper (`CST × Sheet S`) → SHC bag | named Intake Decline.

Rocq mirror: `theories/IntakeWalker.v` + `theories/IntakeAngles.v`
+ `theories/SheetHenClothoidEgg.v`.
Same mapping table. Engines later test the bag, not the string. This
tool mints **no** oracle keyword (ADR-0006). `oracle/driver.ml`
consumes bags already; this visitor is upstream of that protocol.

```
pwsh ./tools/WktIntakeWalker/smoke.ps1
pwsh ./tools/WktIntakeWalker/generate.ps1
dotnet cake --target=WktIntakeWalker
dotnet run --project tools/WktIntakeWalker -- "LINESTRING (0 0, 2 0)"
```

`generate.ps1` runs the ANTLR 4.13.2 tool (`-Dlanguage=CSharp`) against
the pinned `.g4` and writes `gen/` (gitignored). `smoke.ps1` is the
documented smoke (same cases as the retired Java `smoke.sh`, including
`GEODESICSTRING (0 0, 2 0)` = LineString `MkChord` bag).

First slice: Point, LineString, CircularString, CompoundCurve of those,
Circle as two ±π `MkCirc` (A, antipode). Unknown CS/Circle maps to `MkCirc`
via the unique circumcircle (angles letter). Both CLOTHOID surface
forms (ISO REFERENCELOCATION, JTS `(k0,k1,L)`) map to the same
`MkClothoid` bag (OGC≡ISO). Well-formed `GEODESICSTRING` (`n≥2`) maps
to the same `MkChord` bag as `LINESTRING` (Rocq μ in #744
`0007-intake-geodesic`). Fail-closed Declines: empty / singleton
geodesic, `SPIRALCURVE`, collinear (`ID_Collinear`), duplicate control
(`ID_DuplicateControl`), closed CS (`ID_CsClosedDegenerate`), bad count. `dim` → `ID_NotFirstSlice`.
No silent chord demote.
`ID_CircGammaLeftover` / `ID_IsoClothoid` / `ID_MkOutOfScope` stay
on the Decline type; they are not the well-formed clothoid answer.

`grammar/example5.txt` is the #4997 clothoid fixture (both forms).
Not `example3.txt`.

The retired Java visitor lives under `archive/` (not a second primary).
`tests/SqlMmFactoryHunt` drives this C# CLI (`dotnet run` / built exe)
via `HuntHost` — not the archived Java visitor.

AI assistance disclosure: this port was drafted with AI assistance
(Cursor Grok 4.6); human review remains required.
