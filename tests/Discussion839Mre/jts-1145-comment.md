<!-- doc-kind: finding
date: 2026-08-05
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
Corpus PIP gallery gate against this PR’s Y-stripe algorithm (NetTopologySuite.Proofs).

### What we checked
Faithful port of `YStripesPointInPolygonLocator` / `YStripesPointInAreaLocator` (DD ray-crossing + Y-stripes) run against the Qed-backed gallery in [`nts-oracle-gallery.md`](https://github.com/MerkatorBV/NetTopologySuite.Proofs/blob/main/docs/nts-oracle-gallery.md), side-by-side with NTS 2.6 `IndexedPointInAreaLocator` and `SimplePointInAreaLocator`.

Write-up + table: [jts-1145-pip-lane](https://github.com/MerkatorBV/NetTopologySuite.Proofs/blob/main/docs/jts-1145-pip-lane-2026-08.md)  
Harness: `dotnet run --project tests/Discussion839Mre -c Release -- --jts1145`

### Results (14/14)
| Case | Point | Geometric GT | YStripes |
|---|---|---|---|
| Diamond generic | (0, 0.5) | INTERIOR | INTERIOR |
| **Vertex graze** (naive parity even) | **(0, 0)** | **INTERIOR** | **INTERIOR** |
| **Horizontal edge** (naive parity odd) | **(−1, 1)** on notch | **EXTERIOR** | **EXTERIOR** |
| Rect interior / edges | … | INT / BOUNDARY | match |
| Hot-pixel centre / bottom | … | INT / BOUNDARY | match |
| Spectre interior / **reflex pocket** | (5, 0.5) / **(3.5, 0.5)** | INT / **EXT** | match |
| Hat interior / **pocket** (√3 APPROX WKT) | … | INT / **EXT** | match |

Also **bit-equal** to Indexed and Simple on every row (no locator split).

### Suggestion
`AbstractPointInRingTest` already covers comb / repeated pts / a few robust triangles. Adding the gallery WKT pins (especially **diamond graze**, **horizontal-edge exterior**, **Spectre pocket**) would lock both this locator and `IndexedPointInAreaLocator` against the classes that pure half-open ray parity gets wrong without special cases.

No objection on soundness from this corpus gate. Port risk residual: Java tip not executed under JVM here (C# line-faithful port + NTS `CGAlgorithmsDD`).

*(Affiliation: [NetTopologySuite.Proofs](https://github.com/MerkatorBV/NetTopologySuite.Proofs) — formal companion, not a JTS committer review.)*
