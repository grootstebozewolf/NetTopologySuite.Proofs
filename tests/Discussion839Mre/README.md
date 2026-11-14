<!-- doc-kind: guide -->
# Discussion #839 MRE harness

Replays
[NetTopologySuite discussion #839](https://github.com/NetTopologySuite/NetTopologySuite/discussions/839)
(`ConformingDelaunayTriangulationBuilder` + concave polygon + centroid filter)
and checks **local Delaunay legality** of every internal edge with the
proofs-repo Rocq oracle kernel.

## What it measures

1. **CDTB output** under the reporter’s scale / tolerance settings.
2. **Centroid filter** via `IndexedPointInAreaLocator` (Interior / Boundary / Exterior).
3. **Straddle check**: whether any Interior-centroid triangle fails `polygon.Covers(t)`.
4. **Empty-circle test** on every internal edge:
   - Oracle mode `INCIRCLE_SIGN` → extracted `b64_inCircle`
   - Same arithmetic as Phase 5 FFI entry `nts_rocq_in_circle` (`oracle/nts_ffi.h`)
   - Pin: flip witness from `DelaunayLocallyDelaunay.loc_in_circle_test_D` (expect `POS 1.5`)

## Run

```powershell
# Requires WSL oracle_bin (default path below) or ORACLE_BIN
dotnet run --project tests/Discussion839Mre -c Release

# Variants
dotnet run --project tests/Discussion839Mre -c Release -- --no-scale
dotnet run --project tests/Discussion839Mre -c Release -- --tol0
dotnet run --project tests/Discussion839Mre -c Release -- --verbose
```

Oracle resolution order:

1. `ORACLE_BIN` — native Windows path to `oracle_bin` if present  
2. `WSL_ORACLE_BIN` — Linux path, invoked as `wsl.exe -e <path>`  
3. Built-in fallback: `/home/user/nettopologysuite.proofs/oracle/oracle_bin`

The fallback path is a **local template** (one developer’s WSL home layout), not
portable. Set `ORACLE_BIN` or `WSL_ORACLE_BIN` on any other machine.

## Relation to Phase 5 FFI

In-process `DllImport("ntsrocq")` / `RocqNative.InCircle` is preferred when
`libntsrocq` is on the loader path. This harness uses the **oracle protocol**
path so it runs on hosts where only `oracle_bin` is built (WSL). Both call the
same extracted `b64_inCircle` (parity-gated in CI by `oracle/gen_ffi_parity_tests.py`).

## Scout

Analysis + corpus answer: [`docs/nts-discussion-839-scout.md`](../../docs/nts-discussion-839-scout.md).

## JTS #90 ScaledNoder mode

Replays the scale=0 / scale=1 control-flow question from
[locationtech/jts#90](https://github.com/locationtech/jts/pull/90) against NTS
2.6 `ScaledNoder` + `SnapRoundingNoder` (no Rocq oracle required).

```powershell
dotnet run --project tests/Discussion839Mre -c Release -- --jts90
# alias:
dotnet run --project tests/Discussion839Mre -c Release -- --scaled-noder
# keep-green: expect exit code 0 (SRN masks mukoki + scale=0 footgun observed)
```

Write-up: [`docs/jts-90-scalednoder-lane-2026-08.md`](../../docs/jts-90-scalednoder-lane-2026-08.md).  
Optional PR comment draft: [`jts-90-comment.md`](jts-90-comment.md).

## JTS #1145 YStripes PIP gallery mode

Differential gate for
[locationtech/jts#1145](https://github.com/locationtech/jts/pull/1145)
(`YStripesPointInAreaLocator`) against the Qed-backed corpus gallery
([`docs/nts-oracle-gallery.md`](../../docs/nts-oracle-gallery.md)).
Compares Indexed / Simple / YStripes (faithful C# port) — **no Rocq oracle**.

```powershell
dotnet run --project tests/Discussion839Mre -c Release -- --jts1145
# aliases:
dotnet run --project tests/Discussion839Mre -c Release -- --ystripes
dotnet run --project tests/Discussion839Mre -c Release -- --pip-gallery
# keep-green: expect exit code 0 (14/14 geometric GT)
```

Write-up: [`docs/jts-1145-pip-lane-2026-08.md`](../../docs/jts-1145-pip-lane-2026-08.md).  
Vectors: [`oracle/jts1145_pip_gallery_vectors.txt`](../../oracle/jts1145_pip_gallery_vectors.txt).  
Optional PR comment draft: [`jts-1145-comment.md`](jts-1145-comment.md).
