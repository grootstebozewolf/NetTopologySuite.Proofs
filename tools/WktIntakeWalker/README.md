# WktIntakeWalker

Intake seam for ADR-0007 (claimId `0007-intake-walker`, angles
claimId `0007-intake-angles`).

Successful WKT parse (ANTLR, pinned [grammars-v4 #4997](https://github.com/antlr/grammars-v4/pull/4997))
→ tagged CST → mapper (`CST × Sheet S`) → SHC bag | named Intake Decline.

Rocq mirror: `theories/IntakeWalker.v` + `theories/IntakeAngles.v`.
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
via the unique circumcircle (angles letter). Fail-closed Declines:
`GEODESICSTRING`, `SPIRALCURVE`, ISO `CLOTHOID` (`ID_IsoClothoid`),
JTS `CLOTHOID` (`ID_MkOutOfScope`), collinear (`ID_Collinear`),
duplicate control (`ID_DuplicateControl`), bad count / empty.
No silent chord demote. `ID_CircGammaLeftover` is not the well-formed
unknown-CS answer.

`grammar/example5.txt` is the #4997 clothoid fixture (both forms).
Not `example3.txt`.
