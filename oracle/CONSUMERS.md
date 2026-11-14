<!-- doc-kind: guide -->
# Phase 5 consumer bindings

In-process bindings for `libntsrocq` (`oracle/nts_ffi.h`). These replace the
RocqRefRunner subprocess for hot predicates. The subprocess stays the
differential reference.

| Language | File | Load |
|---|---|---|
| C# | [`csharp/RocqNative.cs`](csharp/RocqNative.cs) | `DllImport("ntsrocq")` |
| C++ | [`cpp/RocqNative.hpp`](cpp/RocqNative.hpp) | `dlopen` / `LoadLibrary`, path override `NTS_ROCQ_LIB` |
| Java | [`java/org/locationtech/jts/algorithm/rocq/RocqNative.java`](java/org/locationtech/jts/algorithm/rocq/RocqNative.java) | JNA `Native.load("ntsrocq")`, path override `NTS_ROCQ_LIB` |

Copy the file into the consumer. Do not add a link-time dependency on
`libntsrocq` to production defaults. Call `isAvailable()` / `IsAvailable()`
and skip when the native library is absent.

## Where they land

- **GEOS** — header copied to `include/geos/algorithm/RocqNative.h`. Opt-in;
  `libgeos` does not link `libntsrocq`.
- **JTS** — Java class copied into `jts-curve` on fork PR #7
  (`grootstebozewolf/jts`, `feature/sfa-curve-rgr`). That branch is the
  Java SoT. Do not wait on locationtech/jts or dr-jts; do not open a
  locationtech PR for this lane.
- **NTS** — C# class copied into `NetTopologySuite.Lab`. Core
  `RobustLineIntersector` stays on the stock path unless a caller opts in.

ABI contract and soundness ledger: [`docs/phase5-ffi-abi.md`](../docs/phase5-ffi-abi.md).

## Interface-boundary modes — read before choosing one

Not every oracle mode is exact. Some answer with a float whose transcendental
step has no Coq-extractable form: the **rational invariants** are proven, the
final `sqrt`/`acos`/`atan2` is hand-rolled and sanctioned per mode in
[`docs/oracle-handrolled-allowlist.txt`](../docs/oracle-handrolled-allowlist.txt),
with the same caution repeated in the `oracle/driver.ml` per-mode header.

Known interface-boundary modes include `ARC_LENGTH` (`r·Θ` as a float — prefer
`ARC_LENGTH_INVARIANTS_EXACT`, which returns exact `r²` and `cos Θ₀` and leaves
the single `acos` to you), `ARC_DISTANCE`, `POINT_IN_CURVE_RING` and
`RING_ORIENTATION` (the swept angle needs `atan2`/`acos`; the topological
"sign = inside orientation" Jordan step is deferred). `ARC_SHORTER` shows the
preferred alternative shape: it answers exactly when radii match and **declines**
with `TRANSCENDENTAL` rather than rounding when they differ.

Two consequences for a consumer: prefer the `*_INVARIANTS_EXACT` sibling when one
exists, and never read an interface-boundary answer as a certified one. Curve
segment tokens are a live trap here — see the per-mode allowlist entries before
feeding `E` (elliptic) or `B` (Bézier) segments to any ring predicate.

AI disclosure: authored with AI assistance (see CONTRIBUTING.md).
