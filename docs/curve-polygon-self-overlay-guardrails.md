<!-- doc-kind: guide -->
# Guardrails from CurvePolygon self-overlay dumps

**Source.** FunctionRegistry / overlay-function bench on identical inputs
`G = CurvePolygon[5]` (five vertices on the curved shell; `TypeName[NumPoints]`
notation as printed by the runner).

**Canonical Phase 0 suite + CAP/CUP/SUB/XOR mnemonics:**  
[`docs/overlay-ng-curve-ops-mnemonics.md`](overlay-ng-curve-ops-mnemonics.md)

| Id | Sticky | Spec |
|----|--------|------|
| **G1** | **CAP** ∩ | A ∩ A → A |
| **G2** | **CUP** ∪ | A ∪ A → A |
| **G3** | **SUB** ∖ | A ∖ A → ∅ |
| **G4** | **XOR** Δ | A Δ A → ∅ |
| **G5** | Empty partner | A ∩ ∅ → ∅ · A ∪ ∅ → A · A ∖ ∅ → A · ∅ ∖ A → ∅ |

**Spec home.** Point-set algebra is `theories/Overlay.v` (`boolean_op`);
self-op lemmas:

| Lemma | Sticky | Spec |
|-------|--------|------|
| `boolean_op_intersection_self` | **CAP** ∩ | `A ∩ A = A` (G1) |
| `boolean_op_union_self` | **CUP** ∪ | `A ∪ A = A` (G2) |
| `boolean_op_difference_self_empty` | **SUB** ∖ | `A \ A = ∅` (G3) |
| `boolean_op_symdiff_self_empty` | **XOR** Δ | `A Δ A = ∅` (G4) |

These are the **semantic guardrails**. Implementations may change representation
(curve → linearised polygon) but must not invent interior for SUB/XOR or drop
the body of a self-CAP.

---

## 1. Algebraic checks (run on every overlay path)

For a non-empty valid geometry `G` and path `Op` (classic / OverlayNG / …):

| # | Sticky | Guardrail | Predicate (NTS) | Spec |
|---|--------|-----------|-----------------|------|
| **G1** | CAP | self-intersection is me | `Op.intersection(G,G).EqualsTopo(G)` (or covers + area) | `A ∩ A = A` |
| **G2** | CUP | self-union is me | `Op.union(G,G).EqualsTopo(G)` (or unaryUnion) | `A ∪ A = A` |
| **G3** | SUB | self-difference empty | `Op.difference(G,G).IsEmpty` | `A ∖ A = ∅` |
| **G4** | XOR | self-symDifference empty | `Op.symDifference(G,G).IsEmpty` | `A Δ A = ∅` |
| **G5** | Empty partner | empty second/first | see suite table above | empty-case algebra |
| **G6** | Completes | no crash / non-null | result not null; op completes | — |

**Companion:** `differenceBA(G,G).IsEmpty` is the BA form of SUB (same as G3 when
operands are equal); useful as a registry smoke because many paths already pass it.

**Soft (representation) checks** — degradations, not always point-set wrong:

| # | Guardrail | Predicate |
|---|-----------|-----------|
| **R1** | Keep the arc | preferred paths keep `CurvePolygon` when both inputs are CP |
| **R2** | Honest approx / no explosion | `result.NumPoints` within a fixture-keyed factor of `G.NumPoints` |
| **F1** | Fast before fat | G1–G5 algebra runs before densify/flatten |

---

## 2. Scorecard from the pasted dump (`G = CurvePolygon[5]`)

Legend: **pass** / **fail** / **degrade** (type or size only) / **blank** (no result
line — treat as G6 fail/timeout until confirmed).

### Emptiness laws — SUB / XOR (hard)

| Path | G3 SUB difference | BA smoke (SUB form) | G4 XOR symDifference |
|------|-------------------|---------------------|----------------------|
| Overlay (classic) | **fail** `Polygon[3146]` | **pass** `Polygon[0]` | **fail** `Polygon[3146]` |
| OverlayNG | blank | **pass** `Polygon[0]` | **fail** `Polygon[10]` |
| OverlayNGOpt | **fail** `Polygon[10]` | — | — |
| OverlayNGRobust | **fail** `Polygon[10]` | **pass** `Polygon[0]` | **fail** `Polygon[10]` |
| OverlayNGSR (10) | **fail** `Polygon[10]` | **pass** `Polygon[0]` | **fail** `Polygon[10]` |
| OverlayNGSnapping (10) | blank | — | — |
| OverlayNGStrict | blank | **pass** `Polygon[0]` | **fail** `Polygon[10]` |
| OverlayNoSnap | **fail** `Polygon[10]` | **pass** `Polygon[0]` | **fail** `Polygon[10]` |

**Extracted rule:** BA smoke often **passes** while **G3 SUB / G4 XOR break**
(self-difference / self-symDiff non-empty, often `Polygon[10]`). Classic Overlay
is worst (thousands of points of junk).

### Idempotent laws — CAP / CUP (hard, up to EqualsTopo)

| Path | G1 CAP intersection | G2 CUP union / unaryUnion |
|------|---------------------|---------------------------|
| Overlay | degrade `Polygon[1573]` (linearised bulk) | degrade `Polygon[1573]`; **unaryUnion pass** `CurvePolygon[5]` |
| Overlay.unionUsingGeometryCollection | — | degrade `Polygon[5]` |
| OverlayNG | degrade/ok `Polygon[5]` | blank union |
| OverlayNGOpt (+ prep variants) | **pass** type `CurvePolygon[5]` | — |
| OverlayNGRobust / SR / NoSnap | degrade `Polygon[5]` | degrade `Polygon[5]` |
| OverlayNGSnapping.intersection | **fail** `Polygon[0]` | blank |

**Extracted rules:**

1. **unaryUnion** is the clean CUP identity on this sample — good regression anchor.
2. **OverlayNGOpt.intersection\*** family preserves **CurvePolygon[5]** — best
   R1/G1 gold path for curved self-pairs.
3. **Snapping CAP → empty** is a red-line G1 failure.
4. Classic **1573 / 3146** NumPoints is an R2 explosion; fixture-key bounds, not a
   global “NG is small” rule.

### Diagnostic / edge dumps (not full boolean_op)

`OverlayNGTest.edges*` → MultiLineString/LineString noding views; useful for
noding guardrails (edge count stable under self-pair) but not G1–G5.

`PolygonOverlay.overlay` → `GeometryCollection[15]` — collection packing of
labelled faces; separate contract.

---

## 3. Minimal NUnit / xUnit sketch

```csharp
// For each IOverlayPath path under test:
void AssertSelfOverlayGuardrails(Geometry g, IOverlayPath path)
{
    Assert.That(path.Intersection(g, g).EqualsTopo(g), Is.True, "G1 CAP A∩A");
    Assert.That(path.Union(g, g).EqualsTopo(g), Is.True, "G2 CUP A∪A");
    Assert.That(path.Difference(g, g).IsEmpty, Is.True, "G3 SUB A∖A");
    Assert.That(path.SymDifference(g, g).IsEmpty, Is.True, "G4 XOR AΔA");
}
```

Split suites:

- **Hard gate (must pass for “correct” label):** G3 SUB, G4 XOR (emptiness).
- **Topo gate:** G1 CAP, G2 CUP with `EqualsTopo` / area+covers.
- **Fidelity gate (curve paths only):** R1 + R2 with bound e.g. `NumPoints ≤ 20` for input 5.

---

## 4. What to pin in the proofs corpus

Already cheap and landed next to the existing comm lemmas in `Overlay.v`:

- CAP/CUP self-idempotence and SUB/XOR self-emptiness of `boolean_op` (no Jordan).

Still open (engine-facing):

- A bridge hypothesis “`extract` implements `boolean_op`” + self-op
  specialisation ⇒ `IsEmpty` / coverage corollaries once extraction is
  hooked for curve inputs.

---

## 5. One-line summary for CI badges

> On any self-pair `G⋆G`: **SUB and XOR must be empty**; **CAP and CUP must
> cover G**; BA smoke empty is the one law many OverlayNG paths already hold;
> **do not accept snapping CAP → empty** or classic **NumPoints ≫ |G|** as green
> for curved inputs.

---

## 6. Adversarial pair: concentric disks with a scrambled CIRCULARSTRING

### Inputs (as pasted)

```text
A: CURVEPOLYGON (CIRCULARSTRING (
     5 0, 2.5 4.330127019, -2.5 4.330127019, -5 0,
     -2.5 -4.330127019, 2.5 -4.330127019, 5 0))

B: CURVEPOLYGON (CIRCULARSTRING (
     3 0, -1.5 -2.598076211, 1.5 -2.598076211, -3 0,
     1.5 2.598076211, -1.5 2.598076211, 3 0))
```

### Geometry diagnosis (why “almost all errors”)

| | **A** | **B (as written)** |
|---|--------|---------------------|
| Radii of vertices | all 5 | all 3 |
| Angular steps (atan2) | **+60° six times** (CCW hex sample) | **240°, 60°, 240°, 240°, 60°, 240°** (scrambled) |
| CircularString arcs | 3× **minor** ~120° on the r=5 circle | mix of **~300° / ~240° major** arcs |
| Total oriented arc span | **360°** (one simple cover) | **~840°** (multi-cover + direction flips) |
| Intended shape? | disk radius 5 at origin | *not* the disk radius 3 — path is not a simple boundary |

So **A is a well-formed circular disk shell**. **B is not a smaller concentric disk**:
the control-point order walks the r=3 circle in a non-monotone way, so each
SQL/MM arc (start–mid–end on the same circle) takes the long way / reverses.
Overlay then nodes a self-overlapping multi-wound curve against a clean disk
→ exceptions, empty junk, or huge linearised garbage on almost every path.

This is a **precondition / validity** failure more than an overlay-algebra failure.
Guardrails G1–G5 assume valid simple-feature polygons; they do not apply until
both inputs pass ring simplicity / winding checks (**V1**).

### Correct concentric B (CCW, same sampling style as A)

```text
B_fix: CURVEPOLYGON (CIRCULARSTRING (
  3 0, 1.5 2.598076211, -1.5 2.598076211, -3 0,
  -1.5 -2.598076211, 1.5 -2.598076211, 3 0))
```

Angular steps: +60° × 6. Total span 360°. Nested disks: `B_fix ⊂ A`.

Expected algebra (point-set, ideal):

| Sticky | Op | Result |
|--------|-----|--------|
| CAP | `A ∩ B_fix` | `B_fix` (disk r=3) |
| CUP | `A ∪ B_fix` | `A` (disk r=5) |
| SUB | `A ∖ B_fix` | annulus |
| SUB | `B_fix ∖ A` | empty |
| XOR | `A Δ B_fix` | annulus |

### Extra guardrails for curve inputs

| # | Guardrail | Check |
|---|-----------|--------|
| **V0** | WKT parse succeeds | reader does not throw |
| **V1** | Wound check | reject multi-wound CIRCULARSTRING shells |
| **V2** | Hole nest / monotone polar (disk samples) | consecutive vertex angles advance with constant sign and total ~±360° for a single circle shell |
| **V3** | Type gate / minor-arc fixtures | prefer minor arcs for “round disk” fixtures (`|Δθ| ≤ π` per SQL/MM arc) unless testing major arcs; Curve* takes OverlayNGCurve |
| **V4** | Fixture liveness | known-good pair `A` vs `B_fix` must pass G1–G4 on at least one OverlayNGCurve path before blaming the engine |

### Regression split

1. **Negative fixture** — keep **B as written** under `InvalidOrPathologicalCurvePolygon`;
   assert validator fails *or* document “overlay undefined / may throw”.
2. **Positive fixture** — `A` vs `B_fix` for boolean overlay + curve-fidelity (R1).
3. Do not mix them: scrambled **B** will make “almost all errors” look like
   engine regressions when the shell itself is not a simple ring.

---

## 7. Scorecard: `G = CurvePolygon[7]` self-pair dump

Same runner notation `TypeName[NumPoints]`. Two waves appear in the log:
(1) many ops finish with **no result line** (exception / empty print —
treat as **G6 fail**); (2) a second pass prints classic explosion sizes
identical to the CP[5] linearised path (**1573 / 3146**).

### Edit path (not boolean_op, but related)

| Call | Result | Notes |
|------|--------|--------|
| `Edit.addHole(G, G)` | `CurvePolygon[14]` | Shell copied in as a hole: 7+7 points. Point-set of “polygon with itself as hole” is empty / invalid for OGC; **do not** use as a green identity. Guardrail **E1:** `addHole(G,G)` should reject (hole not interior / equal ring) or fail validation. |

### Emptiness — SUB / XOR (second pass, where printed)

| Path | G3 SUB difference | BA smoke | G4 XOR symDifference |
|------|-------------------|----------|----------------------|
| Overlay | **fail** `Polygon[3146]` | **pass** `Polygon[0]` | **fail** `Polygon[3146]` |
| OverlayNG | **fail** `Polygon[3146]` | **pass** `Polygon[0]` | **fail** `Polygon[3146]` |
| OverlayNGRobust | **fail** `Polygon[3146]` | **pass** `Polygon[0]` | **fail** `Polygon[3146]` |
| OverlayNGOpt | **fail** `Polygon[14]` | — | — |

Same pattern as CP[5]: **BA smoke holds; G3/G4 die**, now with the **full classic
explosion** on NG/Robust too (not just `Polygon[10]`). Opt SUB is smaller junk
(`[14]`) but still **not empty**.

### Idempotence / fidelity — CAP / CUP (printed)

| Path | G1 CAP intersection | G2 CUP union | R1 curve keep | R2 size |
|------|---------------------|--------------|---------------|---------|
| OverlayNGOpt.intersection\* (all prep/SR variants) | **pass** type `CurvePolygon[7]` | — | **pass** | **pass** (7) |
| Overlay / OverlayNG / Robust intersection | linearise `Polygon[1573]` | linearise `Polygon[1573]` | fail | **fail** (225×) |
| Overlay.clip | `Polygon[1573]` | — | fail | fail |

### First-pass blanks (G6)

First block: `OverlayNG.{difference,differenceBA,intersection,symDifference,union}`,
classic Overlay ops, `unionUsingGeometryCollection` (662 ms), and a long
`OverlayNGRobust.*` burst (~300 ms) with **no `==>` line**. Second block
prints results for the same names. Guardrail:

| # | Guardrail | Predicate |
|---|-----------|-----------|
| **G6** | completes with a geometry | non-null result; no throw |
| **G6b** | deterministic print | same op twice → same type/size (or document flaky path) |

**G6b** is live here: first NGRobust wave blank/slow, second wave returns
`Polygon[3146]` etc. Treat dual outcomes as a **registry flaky** flag.

### What this dump adds beyond CP[5]

1. **Opt CAP is the only consistently green family** on self-CP — type-preserving
   identity (`CurvePolygon[7]`). Pin as the R1/G1 gold path for curved self-pairs.
2. **NG/Robust now match classic explosion** on this 7-pt shell (1573/3146),
   worse than the earlier CP[5] NG `Polygon[5]`/`[10]` regime — R2 bounds must
   be **fixture-keyed**.
3. **Opt SUB → Polygon[14]** is a mid-size G3 failure (≈2× input points, not empty).
4. **addHole(G,G) → CP[14]** is a separate edit guardrail (reject or invalid).

### Minimal asserts for this fixture

```text
G1  CAP  intersection(G,G) is CurvePolygon && EqualsTopo(G)   // Opt currently green
G2  CUP  union(G,G) EqualsTopo(G)  (or unaryUnion)
G3  SUB  difference(G,G).IsEmpty
G4  XOR  symDifference(G,G).IsEmpty
G5  empty-partner algebra
G6  every registered Op returns non-null (no silent blank)
E1  addHole(G,G) throws or result.IsValid == false
R2  if Type == Polygon after self-op, flag NumPoints > 50 as explosion
```

---

## 8. RGR land: `OverlayNGCurve` (NetTopologySuite.Curve)

**Branch (Curve repo):** `feat/overlay-ng-curve-rgr`  
**Mnemonics:** [`overlay-ng-curve-ops-mnemonics.md`](overlay-ng-curve-ops-mnemonics.md)

| Phase | Deliverable |
|-------|-------------|
| **Red** | `OverlayNGCurveSelfOpTest` — G1 CAP · G2 CUP · G3 SUB · G4 XOR · G5 empty · F1 clones · V3 name |
| **Green** | `OverlayNGCurve` — F1 short-circuit before flatten; CAP/CUP → `Copy()`; SUB/XOR → empty |
| **Refactor** | `CurveV2` alias; services wire `OverlayNGCurve`; never `Curved` (NTSC0001) |

**Green:** G1–G4 (+ F1 / R1 self), partial G5 via base empty cases.  
**Open:** V1 wound · V2 hole nest · R2 approx flag · true curve noding for A ≠ B.
