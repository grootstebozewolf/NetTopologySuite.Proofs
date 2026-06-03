# Red NUnit tests for M-AREA-CP (curve area)

Following the pattern from orientation/arc length hardening:

- Red tests in NTS Curve module (NUnit) that expect the analytical area to match oracle.
- Until proofs/oracle generate full vectors for area, the tests are "red" placeholders or use Java-port ref for cross-check.
- When ARC_AREA oracle + Rocq area theory land, import vectors and flip to green or delete per epic convention.

See JTS CurveAreaAdversarialTest and CurvePolygonAreaTest for the Java side equivalent.

Goal: zero counterexamples from hunter, full vector coverage from proofs, stable release of curve area.

## PRC-SN snap rounding (related to #66)

Continued RGR + hardening for precision snap on curves (post basic reducer + hunter).
- Red tests expect preserve CS when snapped controls yield grid-friendly centre/r (isGridFriendly).
- Use proofs SnapRounding theories (theories-flocq/SnapRounding_b64.v + HotPixel etc.) to generate adversarial snap cases (grid vs subgrid arcs).
- JTS: CurveSnapRefRunner (BD ref snap+circum decision + loadVectors + hunt) + CurveSnapAdversarialTest + integration in CurvedPrecisionReducerTest.
- Stub + load from rocqref/curve_snap_vectors.txt (format: scale x0 y0 ... PRESERVE|DENSIFY); when full oracle CURVE_SNAP_DECISION vectors land, assert isSound().
- Goal: stable snap for curves in release, zero counterexamples in hunter, no drift vs exact. (See JTS#1195 PRC-SN TAG + review comment on epic.)
- Current: basic 20-iter hunter + ref runner + 5-vector stub + load test; mismatches logged for review / vector gen.
