<!-- doc-kind: finding
date: 2026-08-05
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
## Keep-green + merge ping (2026-08-05)

Rebased this branch onto current `master` (was ~29 commits behind) and
re-ran the suite locally:

```text
mvn test -pl modules/core \
  -Dtest=OrientationDDRobustnessTest,ShewchukExpansionExactnessTest,RocqRefRunnerTest
# Tests run: 22, Failures: 0, Errors: 0, Skipped: 0
```

Also refreshed `orientation_proof_vectors.txt` with additional integer-domain
pins (antisymmetry / vertex degeneracies / cyclic permutations / domain
boundary) aligned with the NetTopologySuite.Proofs orientation bank
(`Orient_b64_exact` / `docs/verified-claims.md` orient rows). Every exported
sign is still cross-checked against `RocqRefRunner.refSign` on load.

### What this PR is (unchanged scope)

- **Test-only** characterization of DD orientation soundness for #1106
- **Safe band** evidence: no counterexamples for `|coord|` well below ~2⁵¹²
- **Hard limits** documented with reproducible overflow / underflow cases
- **RocqRefRunner** bridge: BigDecimal exact R² oracle + integer 2²⁵ path +
  loadable proof vectors

No production API / behaviour change.

### Relationship to the orientation lane

| Track | PR | Role |
|---|---|---|
| **Characterization** | **this PR (#1197)** | DD limits + Rocq vectors (tests) |
| **Production filter** | [#1093](https://github.com/locationtech/jts/pull/1093) | Ozaki Stage A swap — independent differential **GREEN** on 45 vectors vs exact orient ([write-up](https://github.com/MerkatorBV/NetTopologySuite.Proofs/blob/main/docs/jts-1093-orient-lane-2026-08.md)) |

Happy to squash if preferred. Ready for review / merge whenever maintainers have a slot.

*(Affiliation: [NetTopologySuite.Proofs](https://github.com/MerkatorBV/NetTopologySuite.Proofs) — formal precision/predicate companion, not a JTS committer review.)*
