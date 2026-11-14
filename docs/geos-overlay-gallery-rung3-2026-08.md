<!-- doc-kind: finding
date: 2026-08-21
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# GEOS overlay differential gallery — rung 3 (August 2026)

**topic:** `overlay` / `docs` · issues [libgeos/geos#1342](https://github.com/libgeos/geos/issues/1342), [libgeos/geos#1344](https://github.com/libgeos/geos/issues/1344)

Rung 3 of the ladder from [geos-oracle-rung-2026-08.md](geos-oracle-rung-2026-08.md):
harvest the OverlayNG wrong/invalid-output reports
[libgeos/geos#1342](https://github.com/libgeos/geos/issues/1342) and
[libgeos/geos#1344](https://github.com/libgeos/geos/issues/1344) into a
differential gallery — GEOS vs NTS on identical inputs. Sketches are produced by
`tools/WktUnicodeIllustrator` (this pass is also that tool's first real-case
validation; see §4).

## Provenance

| What | Value |
|---|---|
| GEOS (issue reports) | 3.14.1 (via shapely 2.1.2, per reporters) |
| GEOS (local repro) | `/home/user/geos-src` @ `4f7ec39`, branch `feat/curve-pip-collections-rebase` (tracks main + curve PRs), `geosop` from `/home/user/geos-build` |
| NTS | sibling clone, branch `feat/curves-structure-wkt-foundation` |
| Illustrator | text panels @ `aafb92b` (boundary-only era); PNG facsimiles regenerated with surface fills (░ interior, ╳ overlap) |
| Date | 2026-08-21 |

Both bugs **reproduce on the local near-main GEOS build**, not only on released
3.14.1.

`SUMMARY ok=0 warn=1 bug=1` — #1344 is a confirmed GEOS wrong-result bug (NTS
correct on same inputs); #1342 is a GEOS invalid-output bug where NTS fails
closed (warn: neither engine produces a usable answer).

## 1. #1344 — unaryUnion drops a polygon (GEOS bug, NTS correct)

Two valid, adjacent quadrilaterals sharing the edge
`(-295.087 -2.302) — (-295.250 4.236)`, each of area 127.931.

```text
A: POLYGON ((-295.25030351249666 4.236074061427525, -295.08711234218333 -2.301948231163383, -314.64218025800653 -2.7900491087570383, -314.80537142831986 3.7479731838338695, -295.25030351249666 4.236074061427525))
B: POLYGON ((-275.69523559667346 4.7241749390211805, -275.53204442636013 -1.8138473535697273, -295.08711234218333 -2.3019482311633825, -295.25030351249666 4.236074061427525, -275.69523559667346 4.7241749390211805))
```

| Engine | union(A, B) | Area |
|---|---|---|
| GEOS (3.14.1 and local `4f7ec39`) | **returns B exactly** — A is silently dropped | 127.931 |
| NTS (curve branch) | 6-vertex polygon covering both quads | **255.862** (= 127.931 × 2) ✔ |

Inputs (shared edge is the `╳` column) and the NTS union — top/bottom edges
fuse, shared edge dissolved from the result boundary:

```text
— inputs (A blue, B red; magenta ╳ where A∩B) —
┌──────────────────────────────────────────────────────────────────────────────────────────┐
│                                                                                          │
│                                                                                          │
│                          ──────────────────╳──────────────────────────────────────┐      │
│      ┌───────────────────                  ╳                                      │      │
│      │                                     ╳                                      │      │
│      │                                     ╳                                      │      │
│      │                                      ╳                                     │      │
│      │                                      ╳                                     │      │
│      │                                      ╳                  ───────────────────┘      │
│      └──────────────────────────────────────╳──────────────────                          │
│                                                                                          │
│                                                                                          │
└──────────────────────────────────────────────────────────────────────────────────────────┘

— after union (NTS result in green) —
┌──────────────────────────────────────────────────────────────────────────────────────────┐
│                                                                                          │
│                                                                                          │
│                          ─────────────────────────────────────────────────────────┐      │
│      ┌───────────────────                  ╳                                      │      │
│      │                                     ╳                                      │      │
│      │                                     ╳                                      │      │
│      │                                      ╳                                     │      │
│      │                                      ╳                                     │      │
│      │                                      ╳                  ───────────────────┘      │
│      └─────────────────────────────────────────────────────────                          │
│                                                                                          │
│                                                                                          │
└──────────────────────────────────────────────────────────────────────────────────────────┘
```

What GEOS actually returns, contrasted against the expected union
(A = expected union, B = GEOS output; `╳` = coincident):

```text
┌──────────────────────────────────────────────────────────────────────────────────────────┐
│                                                                                          │
│                                                                                          │
│                          ──────────────────╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳      │
│      ┌───────────────────                  │                                      ╳      │
│      │                                     │                                      ╳      │
│      │                                     │                                      ╳      │
│      │                                      │                                     ╳      │
│      │                                      │                                     ╳      │
│      │                                      │                  ╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳      │
│      └──────────────────────────────────────╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳╳                          │
│                                                                                          │
│                                                                                          │
└──────────────────────────────────────────────────────────────────────────────────────────┘
```

GEOS's output coincides with the **right-hand quad only**; the left quad
(A-only linework) is the lost 127.931 of area. Per the reporter, intersection
and difference on the same pair also misbehave (intersection should be
boundary-only).

Reproduce:

```sh
# GEOS (WSL)
geosop -a "<A>" -b "<B>" union
# sketch (colour, for screenshots)
dotnet run --project tools/WktUnicodeIllustrator -- --op union --width 90 --height 12 "<A>" "<B>"
```

Colour facsimiles (generated with `--png`, not screenshots — regenerate with
the §Reproduce commands plus `--png <path>`):

![Inputs and NTS union — colour facsimile](images/geos1344-inputs-union.png)

![Expected union vs GEOS actual — colour facsimile](images/geos1344-expected-vs-actual.png)

## 2. #1342 — intersection emits hole-outside-shell (GEOS invalid, NTS throws)

`A` is a heptagonal ring (shell + near-parallel heptagonal hole). `B` is three
degenerate slivers glued along A's edges — one has a repeated near-identical
vertex pair, one is a zero-width needle at `(79.47, 9.19)`.

```text
A: MULTIPOLYGON (((-78.04121599394897 -5.89365988248295, -79.46982124803172 -9.194972039429315, -31.771830845642597 -73.42037355623992, 47.69799040238911 -64.22540151681056, 79.46982124803172 9.194972039429311, 31.771830845642597 73.42037355623992, -47.69799040238911 64.22540151681056, -78.04121599394897 -5.89365988248295), (-44.94414807547773 60.517346154721146, 29.937481933257768 69.18144635507574, 74.88162621931913 8.664099761904156, 44.94414423125503 -60.51734611949454, -29.937485777480447 -69.18144631984912, -74.8816300087355 -8.664100200354595, -44.94414807547773 60.517346154721146)))
B: MULTIPOLYGON (((-78.04121599394897 -5.89365988248295, -47.69799040238911 64.22540151681056, -79.22212318407406 -8.622575551695201, -78.04121599394897 -5.89365988248295)), ((79.46982124803172 9.194972039429311, 79.26313658326842 8.717351930944158, 79.46982124803172 9.194972039429313, 79.46982124803172 9.194972039429311)), ((-74.8816300087355 -8.664100200354591, -74.8816300087355 -8.66410020035459, -44.94414807547773 60.517346154721146, -74.8816300087355 -8.664100200354591)))
```

| Engine | intersection(A, B) |
|---|---|
| GEOS (3.14.1 and local `4f7ec39`) | GEOMETRYCOLLECTION containing a polygon whose "hole" (the huge inner heptagon) lies **outside** its tiny triangular shell — `IsValid` fails: *"Hole lies outside shell [-74.88 -8.66]"* |
| NTS (curve branch) | **throws** `TopologyException: side location conflict [(-44.944, 60.517)]` — fails closed, no output |

The inputs — every `╳` run is B riding exactly on A's boundary, which is why
both engines stumble:

```text
┌───────────────────────────────────────────────────────────────────────┐
│                                                                       │
│                                                                       │
│                                        ╭┬┬┬┬┬┬─                       │
│                         ─┬┬┬┬┬┬┬┬┬┬┬┬┬┬┴┴┴┴┴┴╯ ╭─                     │
│                 ╳┬┬┬┬┬┬╮ ╰┴┴┴┴┴┴┴┴┴┴┴┴╯       ─╯ ╳                    │
│                ╳ ╳┴┴┴┴┴┴─                       ╳ ╭─                  │
│               ╳ ╳                                ─╯ ╳                 │
│              ╳ ╳                                   ╳ ╭─               │
│              ╳╳                                     ─╯ │              │
│             ╳ ╳                                       ─┴┬─            │
│            ╳ ╳                                          │ │           │
│           ╳ ╳                                            ─┴┬─         │
│          ╳ ╳                                               │ │        │
│         ╳ ╳                                                 ─┴┬─      │
│        ╭╳╳                                                    │ ╳     │
│        ╳ ╳                                                   ╳ ╳      │
│       ╳ ╳                                                   ╳ ╳       │
│      ╳ ╳                                                   │ │        │
│     ╳ ╳                                                    │ │        │
│      ─┴┬─                                                 ╳ ╳         │
│        │ │                                               ╳ ╳          │
│         ─┴┬─                                            ╳ ╳           │
│           │ │                                          ╳ ╳            │
│            ─┴┬─                                       │ ╳             │
│              │ ╭─                                     ╰╮              │
│               ─╯ ╳                                   ╳ │              │
│                 ╳ ╭─                                ╳ ╳               │
│                  ─╯ ╳                       ─┬┬┬┬┬┬╮ ╳                │
│                    ╳ ╭─       ╭┬┬┬┬┬┬┬┬┬┬┬┬╮ ╰┴┴┴┴┴┴─                 │
│                     ─╯ ╭┬┬┬┬┬┬┴┴┴┴┴┴┴┴┴┴┴┴┴┴─                         │
│                       ─┴┴┴┴┴┴╯                                        │
│                                                                       │
│                                                                       │
└───────────────────────────────────────────────────────────────────────┘
```

Differential reading: neither engine is *silently wrong* here — GEOS returns an
invalid structure (detectable by `IsValid`), NTS refuses. Fail-closed beats
invalid output, but the interesting divergence is that OverlayNG-descended code
handles the same degenerate coincidences two different ways. Candidate corpus
entries for the oracle's overlay surface once it grows one.

Reproduce:

```sh
geosop -a "<A>" -b "<B>" intersection           # GEOS: invalid GC
dotnet run --project tools/WktUnicodeIllustrator -- --op intersection "<A>" "<B>"   # NTS: exit 3, side location conflict
dotnet run --project tools/WktUnicodeIllustrator -- --op none --width 71 --height 33 "<A>" "<B>"  # inputs sketch
```

![#1342 inputs — colour facsimile](images/geos1342-inputs.png)

## 3. Ladder position

- Rung 3 (this doc): #1342 / #1344 harvested, reproduced locally, rendered. ✔
- Next per triage §6: pin these input pairs as overlay-gallery corpus vectors;
  rung 4 (splitter area leak #1495/#1242) stays watch-only.

## 4. Illustrator validation note (consumer bar)

This pass was the tool's first real-case use, per the merge bar set for
`feat/wkt-unicode-illustrator`:

- **Boundary-only polygon rendering suffices** for both cases: #1344's lost
  quad and #1342's boundary-riding slivers are legible without fills. Fills
  stay out of scope.
- Found and fixed during the pass: `WorldToGrid` preserved aspect in cell
  space, so square worlds rendered ~2× vertically stretched on 1:2 terminal
  cells and wasted half of wide frames (`aafb92b`, `--cell-aspect`).
- NTS's `side location conflict` surfaced through the tool's exit-3 contract
  with the message intact — the failure mode is itself a differential datum.
