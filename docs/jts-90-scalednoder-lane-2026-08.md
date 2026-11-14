<!-- doc-kind: finding
date: 2026-08-05
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# ScaledNoder lane — JTS #90 scale=0 / scale=1 policy scope

**Date**: 2026-08-05.  
**topic:** `precision` · `buffer` · `docs` · epic **#66** (snap / noding wrapper; buffer fixed-precision path)  
**Upstream**: [locationtech/jts#90](https://github.com/locationtech/jts/pull/90)
  *Fix ScaledNoder behaviour* (jnh5y / mukoki lineage, draft since 2017) — 2-line
  control-flow change in `ScaledNoder`.  
**NTS twin**: `NetTopologySuite.Noding.ScaledNoder` (same `scaleFactor == 1.0`
  skip; still present in NTS 2.6).  
**Scope**: Map the PR against the snap-rounding corpus and modern
  `SnapRoundingNoder`. Reproduce the historical symptom model + live
  scale=0 footgun. **No new Rocq theorems.**

**Verdict**: **YELLOW — do not merge as written; narrow fix only.**  
Mukoki’s scale=1 mixed-precision report is a **legacy `MCIndexSnapRounder`
interaction**. Production `SnapRoundingNoder` snaps vertices itself, so the
observable inconsistency is **masked**. The PR’s swap of the skip predicate
from `scale == 1` to `scale == 0` is the right *idea for scale=0 safety*, but
**forcing a priori scaling at scale=1 fights** modern SRN’s documented
“do not round vertices a priori” design and BufferOp’s scale=1 pure-SRN path.
Corpus algebra (`SnapRoundingScale_b64`, unit-grid snap) is **not** the
failure mode.

---

## §1 — What #90 changes

`modules/core/src/main/java/org/locationtech/jts/noding/ScaledNoder.java`
(only file; +2/−2):

```diff
-    isScaled = ! isIntegerPrecision();
+    isScaled = ! isInfinitePrecision();

-  public boolean isIntegerPrecision() { return scaleFactor == 1.0; }
+  public boolean isInfinitePrecision() { return scaleFactor == 0.0; }
```

| `scaleFactor` | master / NTS 2.6 (`isScaled`) | PR #90 (`isScaled`) |
|---|---|---|
| **0.0** | **true** (would Scale) | **false** (skip) |
| **1.0** | **false** (skip) | **true** (Scale) |
| other | true | true |

When `isScaled`:

1. **Scale** inputs: `Math.round((x - offset) * scaleFactor)` (JTS; NTS omits offset), drop repeats.  
2. Run inner noder in the integer domain.  
3. **Rescale** outputs: `x / scaleFactor + offset`.

When not scaled: pass-through to the inner noder (no pre-round, no post-divide).

**Public API**: renames / removes `isIntegerPrecision()` → `isInfinitePrecision()`.
Review (jodygarnett, 2017): *“This fix changes public API, indeed changes the
meaning.”* Martin (dr-jts): no unit tests; non-breaking?

---

## §2 — Historical symptom (mukoki, 2017)

OpenJUMP beanshell on PR comments — two crossing segments with 1e−5-ish
fractional endpoints, `MCIndexSnapRounder(PM(1))` inside `ScaledNoder`:

| Wrapper scale | Reported noded ends | Intersection node |
|---|---|---|
| **100** | rounded to **0.01** | on 0.01 grid |
| **1** | **raw** `20.11111…` kept | **integer** `(13, 20)` |

So scale≠1 applied **vertex** snap via ScaledNoder; scale=1 left vertices at
full double precision while the snap-rounder still integer-snapped
**intersection** nodes → mixed-precision arrangement.

Python control-flow model of that class (MRE prints the same numbers):

```text
raw intersection ≈ (13.432143332879457, 20.111109999999996)
int-snapped node: (13, 20)
master scale=1 skip: ends keep frac 20.11111,30.11111 + node int
master scale=100: ends on 0.01 + node on 0.01
```

---

## §3 — Modern production path

`BufferOp.bufferFixedPrecision` (JTS master):

```java
Noder snapNoder = new SnapRoundingNoder(new PrecisionModel(1.0));
Noder noder = new ScaledNoder(snapNoder, fixedPM.getScale());
```

Comments in that method:

- `SnapRoundingNoder` **does not require** rounded input.  
- `ScaledNoder` is an **optional speed** path (avoids rounding work inside SRN).  
- **“ScaledNoder may invalidate topology”** — buffer-only caveat.

`SnapRoundingNoder` javadoc is load-bearing:

> Input vertices do not have to be rounded to the grid beforehand; this is done
> during the snap-rounding process. **In fact, rounding cannot be done a
> priori**, since rounding vertices by themselves can distort the rounded
> topology of the arrangement…

### NTS 2.6 MRE (this repo)

```text
dotnet run --project tests/Discussion839Mre -c Release -- --jts90
```

Inner noder: `SnapRoundingNoder(PrecisionModel(1.0))`  
(`MCIndexSnapRounder` is obsolete in NTS 2.6 and crashes on HPRtree cast.)

| Check | Result |
|---|---|
| `ScaledNoder(1)` all verts on integer grid | **True** (SRN snaps verts) |
| `ScaledNoder(100)` all verts on 0.01 grid | **True** |
| Mukoki “keep raw frac ends at scale=1” | **Not observed** under SRN |
| A priori force-scale=1 vs skip+SRN (this input) | **Bit-equal** |
| `Math.Round(x*0)` collapse | **LINESTRING (0 0)** — footgun live |

**Verdict lines from MRE:**

- A) Mukoki mixed-precision **masked** by SnapRoundingNoder.  
- B) **scale=0 footgun live**.  
- C) No topology delta on this toy input between a priori scale=1 and skip.  
- D) Corpus map: **wrapper policy**, not `SnapRoundingScale_b64` algebra.

---

## §4 — Corpus mapping (named claims)

| Asset | Relation to #90 |
|---|---|
| `SnapRounding_b64.v` / `HotPixel_b64.v` | Unit-grid snap + passes-through — assume **uniform** post-snap grid |
| `SnapRoundingScale_b64.v` | `b64_snap_coord_scaled x s = round(x·s)/s` for **power-of-two** `s` — models the *scale path* math, not the skip predicate |
| `DivRoundPow2_b64.v` | Exact mult/div by \(2^k\) under the scaled snap bridge |
| Buffer pipeline (`docs/buffer-noder-pipeline.md`) | Stage 3 consumes Hobby/SR noder; ScaledNoder is an outer **domain transform** |
| GeometryPrecisionReducer / OverlayNG | Adjacent precision consumers; **not** direct call sites of `ScaledNoder` in current JTS search (BufferOp is the main live site) |

### Does scale=0/1 map to a named snap claim?

**No new theorem required** for either:

1. **Mukoki mixed precision** — a **composition policy** failure (“intersection
   nodes on grid, free vertices off grid”) under legacy SR. The corpus already
   treats “fully noded + snapped arrangement” as requiring vertices **and**
   nodes on the same grid; that is an **API/wrapper obligation**, not a gap in
   `b64_snap_coord_scaled_B2R`.
2. **scale=0 collapse** — pure arithmetic footgun
   (`round(x·0)=0`), outside the power-of-two scale regime of
   `SnapRoundingScale_b64`.

Optional future micro-claim (low priority):  
`ScaledNoder_skip_policy` — document that skip iff `scale = 0` (floating /
no transform) **or** document intentional skip at `scale = 1` when the inner
noder is a full snap-rounder. That is **spec prose**, not a Flocq lemma.

---

## §5 — Product recommendation

### Do **not** merge PR #90 as currently written

Reasons:

1. **API break** without dual-method compatibility (`isIntegerPrecision` used
   as a public probe of “unit scale”).  
2. **Inverts scale=1** into a priori rounding — conflicts with modern
   `SnapRoundingNoder` design and with BufferOp’s pure-SRN path when
   `fixedPM.getScale() == 1`.  
3. **No tests** (Martin’s 2017 ask still open).  
4. Historical symptom is **superseded** for SRN; remaining risk is
   documentation / scale=0.

### Prefer a narrow follow-up (if anyone revives the PR)

```text
// skip domain transform only when there is no meaningful scale
isScaled = scaleFactor != 0.0 && scaleFactor != 1.0;
// OR, if FLOATING scale-0 is the only footgun to kill:
isScaled = scaleFactor != 0.0 && !isIntegerPrecision();
```

Better still:

1. **Keep** `isIntegerPrecision()` (`scale == 1`) as public API.  
2. **Add** `isScaled()` / treat `scale == 0` as not scaled (document:
   FLOATING sentinel / invalid scale — do not call `Math.round(x*0)`).  
3. **Do not** force a priori round at scale=1 when the noder is
   `SnapRoundingNoder`.  
4. Unit tests:  
   - scale=0 does not collapse finite inputs (pass-through or throw).  
   - scale=1 + SRN: full grid membership (already SRN’s job).  
   - scale=100: ends on `1/scale` lattice.  
   - Optional legacy: document MCIndexSnapRounder mixed-precision as
     historical only.

### NTS port watch

NTS `ScaledNoder` still has `_isScaled = !IsIntegerPrecision` with
`IsIntegerPrecision => _scaleFactor == 1.0`. Same scale=0 footgun if a caller
passes `0`. Port any **narrow** JTS fix; do **not** blindly port the draft
scale=1 inversion.

---

## §6 — Deliverables

| Path | Purpose |
|---|---|
| `tests/Discussion839Mre/Program.cs` (`--jts90`) | NTS MRE: policy table, scale=0 collapse, SRN scale=1/100, historical model |
| `docs/jts-90-scalednoder-lane-2026-08.md` | This write-up |
| `tests/Discussion839Mre/jts-90-comment.md` | Optional JTS PR comment draft |

### Keep-green (bit-rot gate)

Named test plan — re-run after NTS package bumps or `ScaledNoder` edits:

```powershell
dotnet run --project tests/Discussion839Mre -c Release -- --jts90
# expect: process exit code 0
# expect: "Mukoki mixed-precision ... MASKED by SnapRoundingNoder"
# expect: "scale=0 footgun LIVE"
```

Exit **0** encodes the live findings (SRN masks mukoki **and** scale=0 collapse
observed). Exit **1** means the NTS control flow or noder behaviour drifted —
update this lane doc before treating the scout as current.

---

## §7 — Relation to scout stack

From [`jts-open-prs-scout-2026-08.md`](jts-open-prs-scout-2026-08.md):

> **ScaledNoder #90 (P1)** — Scope whether scale=0/1 bug maps to a named snap claim.

**Answer:** maps to **wrapper policy + scale=0 safety**, **not** a missing
named snap-algebra claim. Priority for proof budget: **drop from P0 theory
work**; keep as **watch / narrow-fix comment** if the draft is revived.
Scout score should read **P1 (policy)** not **P0 (soundness algebra)**.

---

## §8 — Sources

- [locationtech/jts#90](https://github.com/locationtech/jts/pull/90) (patch, comments, review)  
- JTS `ScaledNoder.java`, `SnapRoundingNoder.java`, `BufferOp.bufferFixedPrecision` (master raw, 2026-08-05)  
- NTS 2.6 `ScaledNoder` + `SnapRoundingNoder` via Discussion839Mre package  
- Corpus: `theories-flocq/SnapRoundingScale_b64.v`, `docs/buffer-noder-pipeline.md`, phase-2 snap audit  
