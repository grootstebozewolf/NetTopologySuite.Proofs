<!-- doc-kind: finding
date: 2026-08-05
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Mesh in-circle lane — JTS #311 design history (session 3)

**Date**: 2026-08-05.  
**topic:** `mesh` · epic **#68**  
**Upstream**: [locationtech/jts#311](https://github.com/locationtech/jts/pull/311)
  *isInCircleAdapt sketch Java port* (Komzpa / Darafei Praliaskouski) —
  opened **2018-09-04**, tests refreshed **2026-05-25**.  
**Product tip**: [locationtech/jts#1212](https://github.com/locationtech/jts/pull/1212)
  (Stage A + `isInCircleDDNormalized` + `Vertex.isCCW` → `Orientation.index`).  
**Full adaptive reference**: [locationtech/jts#1094](https://github.com/locationtech/jts/pull/1094).  

**Scope**: Design-history archive of the earliest open Shewchuk-style Stage A
sketch for `TrianglePredicate.isInCircleRobust`. Pure-Python Stage A gate vs
Rocq `INCIRCLE_SIGN` (`b64_inCircle`). No new Rocq theorems; no NTS port.

**Verdict**: **GREEN (history)** — Stage A algebra is the right shape;
CERTAIN signs never disagree with the oracle on this table. The PR is
**superseded in product** by #1212 (and #1094 for full expansions). Keep as
lineage + one concrete constant lesson (`Math.ulp(1.0)` vs Shewchuk ε).

---

## §1 — What #311 actually is (and is not)

### Is

1. **Stage A filter** on the Shewchuk in-circle determinant with coords
   translated so `P` is the origin (same matrix as corpus `inCircle_R` /
   `b64_inCircle`).
2. Error bound  
   `iccerrboundA = (10 + 96·ε)·ε` with **`ε = Math.ulp(1.0)`** (= \(2^{-52}\)
   on binary64) — see §3.
3. Strict magnitude clear:  
   `det > errbound` → inside; `-det > errbound` → outside; else escalate.
4. Escalation to existing **`isInCircleDDFast`** (not full expansion arithmetic).
5. Wires `isInCircleRobust` → `isInCircleAdapt`.
6. Retargets `DelaunayTest.testCircle` expected MULTILINESTRING; adds
   `TrianglePredicateTest` clear + large-coordinate cases (2026-05).

### Is not

- Despite the name **`isInCircleAdapt`**, this is **not** a port of Shewchuk’s
  `incircleadapt` (expansion Stages B/C/D). That fuller port is **#1094**.
- Not a `Vertex.isCCW` / orientation fix (that arrives in **#1212**).
- Not the production merge tip for the mesh lane.

**PR body (2018):** “Do the non-robust calculation and calculation of error
margin. If calculation is possibly not robust, fall back on slower math.”  
References JTS #298; cites CMU `predicates.c`.

**Maintainer reaction (dr-jts, 2018-09-04):** positive on the approach;
requested unit tests and `isInCircleDDFast` (faster equivalent of the then
fallback). Author invited a Java-familiar takeover for style/tests. Stalled
until the 2026-05 test commit — still open.

---

## §2 — Lineage (product + corpus)

```
#311 (2018)  Stage A sketch + DDFast
    │
    ├─► #1094 (2024)  Stage A + full incircleadapt expansions
    │                   (stronger exact path; no orient fix)
    │
    └─► #1212 (2026)  Stage A + isInCircleDDNormalized + Vertex.isCCW
                        ★ product tip for JTS / NTS port watch
```

| Axis | #311 | #1094 | #1212 (tip) |
|---|---|---|---|
| Stage A | Yes | Yes | Yes |
| ε source | `ulp(1.0)` = \(2^{-52}\) | `ulp(0.5)` = \(2^{-53}\) | `DOUBLE_EPS` = \(2^{-53}\) |
| Bound test | strict `>` | non-strict `>=` | strict `>` |
| Escalation | `isInCircleDDFast` | full adaptive expansions | `isInCircleDDNormalized` |
| Orient fix | No | No | Yes |
| Diff size | +92 / −4 (3 files) | ~+900 lines | +149 / −30 |
| Opened | 2018-09 | 2024-10 | 2026-07 |
| Corpus sessions | **3 (this)** | 2 | 1 |

**Corpus formal counterpart of “go beyond Stage A”:** Stage D expansion /
filtered-exact orientation and in-circle work under `theories-flocq/`
(`B64_*`, `Orient_b64_exact*`, `InCircle_b64_exact.v`) — not a Java port of
#311, but the machine-checked reason the adaptive *idea* matters.

---

## §3 — The ε lesson (design history that still pays rent)

Shewchuk’s published Stage A constant uses machine epsilon  
\(\varepsilon = 2^{-53}\) on binary64 (see `predicates.c` /
corpus `DOUBLE_EPS`).

| Source | Expression | Value |
|---|---|---|
| Shewchuk / #1212 / #1094 / corpus | \(2^{-53}\) or `ulp(0.5)` | `1.1102230246251565e-16` |
| **#311** | `Math.ulp(1.0)` | **`2.220446049250313e-16`** (= \(2^{-52}\)) |

Consequence for

\[
\texttt{iccerrboundA} = (10 + 96\,\varepsilon)\,\varepsilon
\]

- Ratio \(\varepsilon_{311}/\varepsilon_{\mathrm{Shew}} = 2\).
- Bound coefficient ratio \(\approx 4\) (quadratic in ε dominates the small
  \(96\varepsilon^2\) term; leading \(10\varepsilon\) alone already doubles).
- **Larger errbound → more conservative Stage A** (more UNCERTAIN → more DD
  work). Direction is safe if escalation is correct; it is **not** the published
  Shewchuk constant and is slightly wasteful vs #1212/#1094.

Later PRs quietly fixed this to \(2^{-53}\). Archive that so nobody “restores”
`ulp(1.0)` as more faithful to the C reference.

---

## §4 — Deliverables

| Path | Role |
|---|---|
| `oracle/gen_jts311_incircle_history.py` | Stage A#311 + Shewchuk-ε comparator + oracle gate |
| `oracle/jts311_incircle_history.txt` | Vector table (regenerated by the script) |
| this doc | Design history + product call |

```text
python oracle/gen_jts311_incircle_history.py
# or:
python oracle/gen_jts311_incircle_history.py --wsl-oracle /home/user/.../oracle_bin
```

Vectors: corpus pins (68-a/b, 1039, 1190) + #311 unit-test quads (clear ±
large-coord) + sample #1212 near-cocircular / GEOS955 / GEOS1040 sites.

---

## §5 — Gate results (2026-08-05)

| Metric | Value |
|---|---|
| Vectors | **22** |
| Oracle flip pin | **POS 1.5** ✓ |
| EXPECTED pin failures | **0** |
| Stage A#311 CERTAIN vs oracle sign conflicts | **0** |
| Stage A#311 UNCERTAIN | **7** (zeros, GEOS955, large-coord) |
| Stage A Shewchuk-ε UNCERTAIN | **7** (same set on this table) |
| ε-policy CERT diverge (311 vs \(2^{-53}\)) | **0** on this table |
| `ICCERRBOUND_A_311 / ICCERRBOUND_A_SHEW` | **≈ 2** (ε ratio 2; leading term \(10\varepsilon\)) |

**Load-bearing uncertain case (shared with sessions 1–2):**

```text
A = (18.68285714285716, 100.105)
B = (13.41, 104.82100000000001)
C = (13.41, 107.179)
P = (18.682857142857145, 111.89500000000001)
```

Stage A (either ε) declines / zero-classifies; oracle **POS**. Escalation
(DD or adapt) is load-bearing — the 2018 design insight of #311.

### Finding — 2026 unit-test large-coord quad

PR `testAdaptiveInCircleFallbackUsesDDComputation` uses ~\(10^{14}\)
coordinates and `assertTrue` on both `isInCircleDDFast` and
`isInCircleRobust`. Under IEEE binary64:

| Probe | Result |
|---|---|
| Stage A det | **0.0** (UNCERTAIN — correct decline) |
| Rocq `b64_inCircle` / `INCIRCLE_SIGN` | **ZERO** |
| Translated deltas | multiples of \(2^{-5}\) after collapse of the decimal tails |

So the **decimal literals do not encode a strict-inside configuration once
rounded to binary64**. Independent extracted kernel says not strictly inside.
If Java DDFast still returns `true` on these exact doubles, that is a
**fallback-path discrepancy** worth a maintainer look — not a Stage A failure.
This session does **not** re-run the JUnit assertion; it only records the
corpus side as **ZERO / open characterization** (not an EXPECTED POS pin).

---

## §6 — Product / corpus call

1. **Do not** dual-track an NTS port of #311.
2. **Tip remains #1212** (session 1 GREEN); **#1094** is full-adaptive
   reference (session 2 GREEN).
3. **#311** is **design history**: first open JTS sketch of filter-then-escalate
   for in-circle; ancestor of both later PRs; ε footnote for implementers.
4. Optional public comment: short “thanks / lineage / ε note / tip is #1212”
   only if maintainers want corpus signal — lower priority than commenting
   #1212 / #1094 with numbers.

---

## §7 — Non-claims

- No proof that Java `isInCircleDDFast` equals `b64_inCircle` bit-for-bit.
- No re-run of the full JTS Maven suite in this session.
- No claim that #311 should merge **instead of** #1212 or #1094.
- No new Rocq theorems; Stage D remains the formal expansion counterpart
  elsewhere in the corpus.

**AI assistance**: Grok (grok-4.5), human-directed.  
**License**: project documentation (BSD-3-Clause corpus).
