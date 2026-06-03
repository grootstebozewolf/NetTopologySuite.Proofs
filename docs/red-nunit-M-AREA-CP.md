# Red NUnit tests for M-AREA-CP (curve area)

Following the pattern from orientation/arc length hardening:

- Red tests in NTS Curve module (NUnit) that expect the analytical area to match oracle.
- Until proofs/oracle generate full vectors for area, the tests are "red" placeholders or use Java-port ref for cross-check.
- When ARC_AREA oracle + Rocq area theory land, import vectors and flip to green or delete per epic convention.

See JTS CurveAreaAdversarialTest and CurvePolygonAreaTest for the Java side equivalent.

Goal: zero counterexamples from hunter, full vector coverage from proofs, stable release of curve area.
