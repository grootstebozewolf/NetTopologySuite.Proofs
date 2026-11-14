<!-- doc-kind: finding
date: 2026-08-05
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
Thanks for this — differential check from the NetTopologySuite.Proofs side (precision / orientation lane).

We mirrored **three** Stage A shapes in pure double and gated them against an independent extracted exact orient (`ORIENT_EXACT` / `b64_orient2d_exact`). We did **not** re-run the full Maven suite or claim bit-identity of the DD fallback with the oracle.

### Method
- **Oracle GT:** `ORIENT_EXACT` (full-plane exact sign).
- **JTS-master mirror:** current `orientationIndexFilter` — Shewchuk-style detsum + `DP_SAFE_EPSILON = 1e-15`.
- **Ozaki mirror (this PR):** `errbound = |detleft + detright| * 3.3306690621773724e-16`, CERTAIN iff `|det| >= errbound`.
- **Corpus Shewchuk Stage A:** detsum + `ccwerrboundA = (3+16ε)ε` (ε = 2⁻⁵³).

Write-up + table: [jts-1093-orient-lane](https://github.com/MerkatorBV/NetTopologySuite.Proofs/blob/main/docs/jts-1093-orient-lane-2026-08.md) (`oracle/jts1093_orient_vectors.txt`, 45 vectors).

### Results
| Check | Result |
|---|---|
| Certified pin failures (EXPECTED set) | **0** |
| Ozaki **CERTAIN** vs exact sign conflicts | **0** |
| Corpus Shewchuk **CERTAIN** vs exact conflicts | **0** |
| JTS-master **CERTAIN** vs exact conflicts | **0** |
| Ozaki UNCERTAIN / Shewchuk UNCERTAIN / master UNCERTAIN | **10 / 10 / 14** |
| Ozaki CERTAIN while master UNCERTAIN | **4** |
| Master CERTAIN while Ozaki UNCERTAIN | **0** |
| Ozaki ↔ corpus Shewchuk certainty splits | **0** |

### “Fewer misses” band (same-sign products)

```text
a = (0, 0),  b = (1, 0.5),  q = (2, 1 + h)
```

| h | Exact | Master (1e-15) | Ozaki | Shewchuk ccwerrboundA |
|---|---|---|---|---|
| 1e-14 | ± | CERTAIN | CERTAIN | CERTAIN |
| **1e-15, 2e-15** | ± | **UNCERTAIN** | **CERTAIN** | **CERTAIN** |
| 5e-16, ~3.3e-16 | ± | UNCERTAIN | UNCERTAIN | UNCERTAIN |

So on this table the PR’s claim holds in miniature: the master constant escalates earlier; Ozaki commits correctly in the gap and never committed a wrong sign. Ozaki’s published double sits next to true Shewchuk `ccwerrboundA` (they never split certainty here). Deep collinear / zero-det cases still correctly force UNCERTAIN → DD, as designed.

### Bottom line
From an independent exact-orient gate, this filter swap looks **sound and slightly tighter** than master, and **aligned with** a Shewchuk-constant Stage A rather than the historical `1e-15` guard. Happy to re-run if you add more near-collinear fixtures to the suite.

*(Affiliation: [NetTopologySuite.Proofs](https://github.com/MerkatorBV/NetTopologySuite.Proofs) — formal precision/predicate companion, not a JTS committer review.)*
