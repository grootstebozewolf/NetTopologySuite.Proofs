<!-- doc-kind: finding
date: 2026-08-05
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
Thanks for leaving this draft open — scoped from the NetTopologySuite.Proofs snap / precision lane against current master + NTS 2.6.

### What we checked
- Master `ScaledNoder`: `isScaled = !(scaleFactor == 1.0)` (NTS twin identical).
- This PR: skip only when `scaleFactor == 0.0`, so **scale=1 would pre-round**.
- mukoki’s 2017 beanshell (MCIndexSnapRounder + scale 1 vs 100) — historical mixed precision (integer **nodes**, full-precision **ends** at scale=1).
- Modern production path: `BufferOp` → `ScaledNoder(SnapRoundingNoder(PM(1)), fixedPM.getScale())`.

Write-up + MRE: [jts-90-scalednoder-lane](https://github.com/MerkatorBV/NetTopologySuite.Proofs/blob/main/docs/jts-90-scalednoder-lane-2026-08.md)  
(`dotnet run --project tests/Discussion839Mre -c Release -- --jts90`)

### Results
| Check | Result |
|---|---|
| Mukoki mixed-precision under **SnapRoundingNoder** | **Masked** — SRN snaps vertices; scale=1 output is fully on the integer grid |
| `Math.round(x * 0)` if master treats scale=0 as scaled | **Live footgun** — finite inputs collapse to the origin |
| A priori scale=1 vs skip+SRN on mukoki lines | Bit-equal on this toy; not a general topology proof |
| Named corpus snap claim gap? | **No** — wrapper policy / scale=0 safety, not `round(x·s)/s` algebra |

### Concern with merging as written
`SnapRoundingNoder` documents that **a priori vertex rounding can distort** snap-rounding topology; BufferOp only uses `ScaledNoder` as an optional speed path and notes topology risk. Forcing scale at **scale=1** turns the intentional pass-through into a priori integer round, which fights that design (and renames a public method without a dual).

### Suggested narrow alternative
1. Keep `isIntegerPrecision()` (`scale == 1`).
2. Treat **`scale == 0` as not scaled** (or throw) so FLOATING-scale callers never hit `round(x*0)`.
3. Do **not** invert scale=1 unless there is a remaining MCIndexSnapRounder-only call site that still needs it — with tests.
4. Add unit tests for scale 0 / 1 / 100 grid membership under `SnapRoundingNoder`.

Happy to re-run the MRE if you land a revised patch.

*(Affiliation: [NetTopologySuite.Proofs](https://github.com/MerkatorBV/NetTopologySuite.Proofs) — formal snap/precision companion, not a JTS committer review.)*
