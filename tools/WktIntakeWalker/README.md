# WktIntakeWalker

First-slice intake seam for ADR-0007 (claimId `0007-intake-walker`).

Successful WKT parse (ANTLR, pinned [grammars-v4 #4997](https://github.com/antlr/grammars-v4/pull/4997))
→ tagged CST → mapper (`CST × Sheet S`) → SHC bag | named Intake Decline.

Rocq mirror: `theories/IntakeWalker.v`. Same mapping table. Engines later
test the bag, not the string. This tool mints **no** oracle keyword
(ADR-0006). `oracle/driver.ml` consumes bags already; this visitor is
upstream of that protocol.

```
bash tools/WktIntakeWalker/smoke.sh
bash tools/WktIntakeWalker/generate.sh
java -cp tools/WktIntakeWalker/.build:tools/WktIntakeWalker/.antlr/antlr-4.13.2-complete.jar \
  org.nts.proofs.intake.Main 'LINESTRING (0 0, 2 0)'
```

First slice: Point, LineString, CircularString, CompoundCurve of those,
Circle-as-full-span-arc. Fail-closed Declines: `GEODESICSTRING`,
`SPIRALCURVE`, ISO `CLOTHOID` (`ID_IsoClothoid`), JTS `CLOTHOID`
(`ID_MkOutOfScope`), unknown circular control points
(`ID_CircGammaLeftover`). No silent chord demote.

`grammar/example5.txt` is the #4997 clothoid fixture (both forms).
Not `example3.txt`.
