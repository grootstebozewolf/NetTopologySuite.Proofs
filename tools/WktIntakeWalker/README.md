# WktIntakeWalker

Intake seam for ADR-0007 (claimId `0007-intake-walker`, angles
claimId `0007-intake-angles`, clothoid claimId `0007-intake-mkclothoid`).

Successful WKT parse (ANTLR, pinned [grammars-v4 #4997](https://github.com/antlr/grammars-v4/pull/4997))
→ tagged CST → mapper (`CST × Sheet S`) → SHC bag | named Intake Decline.

Rocq mirror: `theories/IntakeWalker.v` + `theories/IntakeAngles.v`
+ `theories/SheetHenClothoidEgg.v`.
Same mapping table. Engines later test the bag, not the string. This
tool mints **no** oracle keyword (ADR-0006). `oracle/driver.ml`
consumes bags already; this visitor is upstream of that protocol.

```
bash tools/WktIntakeWalker/smoke.sh
bash tools/WktIntakeWalker/generate.sh
java -cp tools/WktIntakeWalker/.build:tools/WktIntakeWalker/.antlr/antlr-4.13.2-complete.jar \
  org.nts.proofs.intake.Main 'LINESTRING (0 0, 2 0)'
```

First slice: Point, LineString, CircularString, CompoundCurve of those,
Circle-as-full-span-arc. Unknown well-formed CS/Circle maps to `MkCirc`
via the unique circumcircle (angles letter). Both CLOTHOID surface
forms (ISO REFERENCELOCATION, JTS `(k0,k1,L)`) map to the same
`MkClothoid` bag (OGC≡ISO). Well-formed `GEODESICSTRING` (`n≥2`) maps
to the same `MkChord` bag as `LINESTRING` (Rocq μ in #744
`0007-intake-geodesic`). Famous Science/arXiv 1804.07389 fixtures
(claimId `0007-famous-geodesicstring`):
`GEODESICSTRING (66.6666666667 25.2833333333, 162.2333333333 58.6166666667)`
(Sonmiani → Karaginsky) and
`GEODESICSTRING (118.6333333333 24.55, -8.9166666667 37.0333333333)`
(Quanzhou → Sagres) bag-equal the matching `LINESTRING`. Not an
Earth-length / ETOPO1 / ellipsoid claim. Fail-closed Declines: empty / singleton
geodesic, `SPIRALCURVE`, collinear (`ID_Collinear`), duplicate control
(`ID_DuplicateControl`), bad count / empty. No silent chord demote.
`ID_CircGammaLeftover` / `ID_IsoClothoid` / `ID_MkOutOfScope` stay
on the Decline type; they are not the well-formed clothoid answer.

`grammar/example5.txt` is the #4997 clothoid fixture (both forms).
Not `example3.txt`.
