<!-- doc-kind: guide -->
# Phase 5 — extraction toolchain + C# FFI: `libntsrocq`

Status doc and ABI contract for the Phase 5 lane of the roadmap
("Extraction toolchain + C# FFI to production NTS").

Companion sources:
[`oracle/nts_ffi.h`](../oracle/nts_ffi.h) (the ABI),
[`oracle/nts_ffi.ml`](../oracle/nts_ffi.ml) (OCaml side),
[`oracle/nts_ffi_stubs.c`](../oracle/nts_ffi_stubs.c) (C side),
[`oracle/ffi_probe.c`](../oracle/ffi_probe.c) (parity driver),
[`oracle/gen_ffi_parity_tests.py`](../oracle/gen_ffi_parity_tests.py) (the gate),
[`oracle/csharp/RocqNative.cs`](../oracle/csharp/RocqNative.cs) (reference .NET binding),
[`oracle/cpp/RocqNative.hpp`](../oracle/cpp/RocqNative.hpp) (reference C++ binding),
[`oracle/java/org/locationtech/jts/algorithm/rocq/RocqNative.java`](../oracle/java/org/locationtech/jts/algorithm/rocq/RocqNative.java) (reference Java/JNA binding).
Consumer map: [`oracle/CONSUMERS.md`](../oracle/CONSUMERS.md).

---

## 0. Rebuild / freshness (2026-08)

`oracle/extracted.ml` is **gitignored**. A stale extract (missing
`b64_orient2d_exact`) breaks `make -C oracle ffi` while still allowing the
mesh scout library (`scout_incircle_*`). Refresh with:

```bash
./scripts/rebuild_oracle_ffi.sh --parity
```

Rung status, parity YELLOW on exact-orient extremes, and the orientation
lane scout: [`docs/ffi-rungs-2026-08.md`](ffi-rungs-2026-08.md).

---

## 1. Where Phase 5 actually stood

The roadmap row read "pending Phase 1+ / 0%", which had gone stale in one
direction and was accurate in another:

* **Extraction toolchain — already shipped, incidentally.**
  `theories-flocq/Validate_binary64_extract.v` extracts twenty kernel
  functions to OCaml with native-float overrides, `oracle/Makefile` links them
  into `oracle_bin`, and `.github/workflows/build-oracle.yml` builds and
  publishes that binary from a clean container on every relevant push. It was
  built to serve differential testing (RocqRefRunner), but it *is* the Phase 5
  extraction toolchain.
* **FFI to production NTS — genuinely 0%.** Everything downstream went through
  a **subprocess**: spawn `oracle_bin`, write a mode line and some coordinate
  lines, read a line back. That is a fine test oracle and an impossible
  production kernel — a noding loop calls orientation millions of times, and
  each call was a `fork` plus two pipe round-trips.

This slice closes the second gap at the boundary layer: the same extracted code
is now callable **in-process** through a C ABI that .NET binds with `DllImport`.

## 2. What landed

| Piece | File | What it is |
|---|---|---|
| OCaml callback layer | `oracle/nts_ffi.ml` | Registers 19 extracted entry points as `Callback` closures with a uniform `float array` calling convention |
| C entry points | `oracle/nts_ffi_stubs.c` | Plain C functions marshalling doubles in / codes and doubles out, with CAMLparam GC discipline |
| ABI contract | `oracle/nts_ffi.h` | Signatures, enum encodings, lifecycle, threading and numerics caveats |
| Build | `oracle/Makefile` | `make -C oracle ffi` → `libntsrocq.so` + `ffi_probe`; `make -C oracle ffi-parity` runs the gate |
| Parity gate | `oracle/gen_ffi_parity_tests.py` | ~1200 cases per run; every FFI entry point vs the `oracle_bin` protocol, compared as raw IEEE 754 bit patterns |
| .NET binding | `oracle/csharp/RocqNative.cs` | Reference `DllImport` surface + managed façade (reference source; no .NET toolchain in this CI) |
| C++ binding | `oracle/cpp/RocqNative.hpp` | Header-only `dlopen`/`LoadLibrary` façade; no link-time dependency |
| Java binding | `oracle/java/.../RocqNative.java` | JNA façade (`Native.load("ntsrocq")`); skip when the .so is absent |
| CI | `.github/workflows/build-oracle.yml` | Builds the library in the pinned container, runs the parity gate, uploads `libntsrocq.so` + `nts_ffi.h` as an artifact and attaches them to releases |

The library links the extracted code plus OCaml's PIC runtime
(`libasmrun_pic.a`); the plain runtime in `-output-complete-obj` is non-PIC and
cannot go into a shared object, which is why the Makefile uses `-output-obj`
plus an explicit runtime link.

## 3. Why the parity gate is the interesting part

`libntsrocq` and `oracle_bin` call the *same* `oracle/extracted.ml` symbols.
(One deliberate exception: `nts_rocq_orient_sign_exact` is additionally gated
against the `ORIENT_EXACT` mode, which is an independent zarith
re-implementation — for that pairing the gate is a genuine arithmetic
differential test, not just marshalling parity; see §4.)
So no arithmetic difference between them is possible — but a **marshalling**
difference very much is: a swapped argument pair, a sign dropped from an enum,
a result list truncated at the C boundary, a `-0.0` normalised on the way out.
Those bugs are invisible to unit tests written against the FFI itself (they are
self-consistent) and would land in production NTS silently.

`gen_ffi_parity_tests.py` therefore drives both paths with identical inputs and
compares **bit patterns**, not decimal text: NaN is folded (the oracle's textual
output carries no payload), but `-0.0` and `+0.0` are distinguished, and a
one-ulp difference fails. Inputs are curated adversarial cases (signed zeros,
subnormals, `2^512` overflow band, `2^-540` underflow band, NaN/±inf, exact
pixel-boundary ties, near-collinear-at-`2^27`) plus seeded pseudorandom cases.

The hazard is not hypothetical. `b64_snap_coord_scaled (x s)` takes the value
first and the grid scale second, while the `SNAP_SCALED` oracle mode reads the
scale line first — exactly the kind of asymmetry a hand-written binding gets
wrong. The C signature follows the Coq order, and the mode is in the gate.

## 4. Soundness ledger — read this before calling anything

The FFI is **not** part of the trusted base; it is glue. What each entry point
is *proven* to satisfy differs sharply, and the ABI deliberately does not
flatten that. Anything marked "sufficient only" or "deferred" is a place where
production code must not assume more than the proof gives.

| Entry point | Extracted symbol | Proof status |
|---|---|---|
| `nts_rocq_orient_sign_filtered` | `b64_orient_sign_filtered` | Totality + decidability + NaN-safety Qed (`b64_orient_sign_filtered_total`, `orient_sign_robust_eq_dec`, `Orientation_b64.v`); exact soundness for `\|coord\| <= 2^25` Qed (`b64_orient_sign_filtered_sound_small_int`, `Orient_b64_exact.v`). General bounded-magnitude soundness (Stages B–D) **deferred** — `docs/soundness-strategy.md`. `UNCERTAIN` is never a wrong sign; callers must escalate (to `nts_rocq_orient_sign_exact`), not coerce it to `ZERO` |
| `nts_rocq_orient_sign_naive` | `b64_orient_sign_naive` | Total (`b64_orient_sign_naive_total`); **not robust** — differential-testing use only |
| `nts_rocq_orient2d` | `b64_orient2d` | The raw determinant value; no soundness claim on its own |
| `nts_rocq_orient_sign_exact` | `b64_orient2d_exact` | **Full-plane exact-sign soundness Qed** (`b64_orient2d_exact_sound`, `Orient_b64_exact_full.v`, no magnitude restriction, within the three-axiom allowlist and no `Classical_Prop.classic`) + canonical-sign range Qed (`b64_orient2d_exact_range`). The escalation target for `UNCERTAIN`. Everything downstream of decode is extracted verified `Z` arithmetic; the two IEEE 754 decode overrides (`b64_mant`/`b64_exp`, `Validate_binary64_extract.v`) are unverified glue, gated case-for-case against the *independent* zarith `ORIENT_EXACT`. Non-finite inputs return `NAN` via the marshalling guard (soundness premise is `all_finite`); never `UNCERTAIN`. Arbitrary-precision integers — escalation-path speed, not hot-path speed |
| `nts_rocq_intersect_sign_filtered` | `b64_intersect_sign_filtered` | Integer-regime soundness Qed for both decisive verdicts (`b64_intersect_sign_filtered_{none,point}_sound_small_int`, headline `..._sound_small_int`, `Intersect_b64.v`); `COLLINEAR` sub-case disambiguation is the known open gap (`docs/phase1-completion.md`) |
| `nts_rocq_intersect_point` / `_xy` | `b64_intersect_point{,_x,_y}` | Totality, finiteness, magnitude bounds and a forward-error bound in `K·eps` form Qed (`Intersect_b64_exact.v`); `b64_intersect_point_returns_some_when_point` ties the option wrapper to the predicate |
| `nts_rocq_passes_through_hot_pixel{,_halfopen}` | `b64_passes_through_hot_pixel{,_halfopen}_compute` | Conservative **over-approximation** of the exact relation: it over-accepts within O(ulp) of tangency, machine-checked in `PassesThrough_b64_compute_unsound.v` / `PassesThroughHalfopen_b64_compute_unsound.v`. The exact R-side spec is non-computational and not extractable |
| `nts_rocq_snap_coord` | `b64_snap_coord` | Round-half-to-even; extraction override documented in `Validate_binary64_extract.v` |
| `nts_rocq_snap_coord_scaled` | `b64_snap_coord_scaled` | Exact bridge to the R-side `snap_round_coord` for a **power-of-two** scale under the stated premises (`b64_snap_coord_scaled_B2R`, `SnapRoundingScale_b64.v`); downstream `b64_in_hot_pixel_sound_pow2`, `snap_round_preserves_passes_through_scale` |
| `nts_rocq_edge_in_result` | `edge_in_result` | Per-op characterisations Qed (`edge_in_result_union_true`, `edge_in_result_intersection_true`, `edge_in_result_difference_iff`, `edge_in_result_symdiff_iff`, `OverlayGraph.v`); the overlay headline that consumes it is conditional (`docs/audit-phase3-overlay.md`) |
| `nts_rocq_in_circle` | `b64_inCircle` | Full-plane exact-sign soundness and integer-regime exactness Qed (`b64_inCircle_exact_sound`, `b64_inCircle_B2R_sign_sound_small_int`, `InCircle_b64_exact.v`) |
| `nts_rocq_chord_crosses_arc_circle` | `b64_chord_crosses_arc_circle` | **Sufficient only**: `true` ⇒ crossing (IVT-witnessed, `ArcIntersectIVT.v`); `false` is inconclusive |
| `nts_rocq_arc_passes_through_hot_pixel` | `b64_arc_passes_through_hot_pixel` | **Sufficient only**, same shape (`ArcHotPixel.v` pin) |
| `nts_rocq_arc_line_intersect_xy` | `b64_arc_line_intersect_point_{x,y}` | Scope A first-stage exactness (`ArcLineIntersect_b64_exact.v`); single-root projection, **not** an enumerator — emits inf/NaN on a two-crossing line (issue #224) |
| `nts_rocq_two_sum` | `b64_TwoSum` | Error-free transformation Qed (`b64_TwoSum_correct`, `b64_TwoSum_nonoverlap`, `B64_Pff_bridge.v`) |
| `nts_rocq_grow_expansion` | `b64_grow_expansion_aux` | Sum correctness Qed (`b64_grow_expansion_correct`); the general Shewchuk Theorem 13 non-overlap headline is **false as stated** and Qed-closed as a disproof (`docs/shewchuk-thm13-headline-counterexample.md`) |
| `nts_rocq_simplify_perp` | `greedy_simplify_perp_b64` | Structural lemmas Qed (totality/head/length); the soundness bridge to the R-side spec is **deferred** |

Two structural caveats apply to everything above:

* **Extraction is not the trusted base.** `Validate_binary64_extract.v` replaces
  Flocq's `Bplus`/`Bminus`/`Bmult`/`Bdiv`/`Bcompare` with native OCaml float ops.
  The proofs are about the Flocq model; the extracted code is bit-equal to it on
  a 64-bit SSE2/NEON runtime with round-to-nearest-even, and diverges on a
  32-bit x87 runtime (double rounding).
* **The exact orientation fallback is now extracted and exposed.**
  `b64_orient2d_exact` (`Orient_b64_exact_full.v`, Qed-closed over the entire
  double plane) extracts as verified Coq `Z` arithmetic — no zarith — plus two
  unverified IEEE 754 bit-decode overrides (`b64_mant` / `b64_exp`,
  `Validate_binary64_extract.v`), and ships as `nts_rocq_orient_sign_exact`:
  the in-process escalation for `NTS_ORIENT_UNCERTAIN`. The zarith
  `ORIENT_EXACT` in `driver.ml` deliberately survives as the
  arithmetic-independent half of a differential pair (the new
  `ORIENT_EXACT_EXTRACTED` oracle mode runs the extracted path; the parity
  gate compares the FFI against both, case for case). The in-circle and
  passes-through exact modes (`INCIRCLE_EXACT` / `PASSES_THROUGH_EXACT`)
  remain zarith-only and absent from the FFI — extracting those counterparts
  is the next slice of this lane.

## 5. Using it

```sh
# from the repo root, inside the pinned toolchain
make -f Makefile.gen theories-flocq/Validate_binary64_extract.vo   # writes oracle/extracted.ml
make -C oracle                 # oracle_bin (the subprocess oracle)
make -C oracle ffi             # libntsrocq.so + ffi_probe
make -C oracle ffi-parity      # the gate: FFI == oracle_bin, bit for bit
```

From C:

```c
#include "nts_ffi.h"

nts_rocq_init();                       /* once, before anything else */
int32_t s = nts_rocq_orient_sign_filtered(0, 0, 1, 0, 0, 1);   /* NTS_ORIENT_POS */
if (s == NTS_ORIENT_UNCERTAIN) {
  /* escalate: exact over the full plane, never UNCERTAIN */
  s = nts_rocq_orient_sign_exact(0, 0, 1, 0, 0, 1);
}
```

From .NET: copy `oracle/csharp/RocqNative.cs` into the consumer, ship
`libntsrocq.so` / `.dylib` / `.dll` as a native asset for the target RID, and
call `RocqNative.OrientSignFiltered(...)`. The façade serialises calls on a
lock — see below.

From C++: `#include` `oracle/cpp/RocqNative.hpp` (or the GEOS copy at
`include/geos/algorithm/RocqNative.h`) and call
`ntsrocq::RocqNative::orientSignFiltered(...)` after
`ntsrocq::RocqNative::isAvailable()`.

From Java: copy `oracle/java/.../RocqNative.java` into the consumer (JTS
lands it on fork PR #7 in `jts-curve`), add JNA, and call
`RocqNative.orientSignFiltered(...)` after `RocqNative.isAvailable()`.
Fork PR #7 is the Java SoT. Do not wait on locationtech/jts or dr-jts.

**Lifecycle**: `nts_rocq_init()` boots the embedded OCaml runtime; it is
idempotent, and every entry point calls it defensively. There is no shutdown.

**Threading**: the OCaml 4.14 runtime is not re-entrant and these stubs do not
register foreign threads with it. All calls must come from one thread or be
serialised by the caller. Parallel consumers should partition and batch rather
than removing the lock; a genuinely concurrent binding needs
`caml_c_thread_register` plus the threads library, which is a separate slice.

**Error handling**: the predicates are total — NaN and ±inf return defined
codes. Only `nts_rocq_grow_expansion` and `nts_rocq_simplify_perp` can fail, and
only by returning a negative value when the caller's buffer is too small; they
never write past the declared capacity.

## 6. What Phase 5 still needs

1. **Exact escalation in the FFI** — the orientation half is **done**:
   `b64_orient2d_exact` is extracted and exposed as
   `nts_rocq_orient_sign_exact`, so `UNCERTAIN` has an in-process resolution.
   Still open: the in-circle / passes-through exact counterparts
   (`INCIRCLE_EXACT` / `PASSES_THROUGH_EXACT` are still zarith-only oracle
   modes).
2. **Multi-platform native assets** — the CI artifact is Linux x64 only.
   macOS (x64 + arm64) and Windows x64 builds, plus a runtimes/-shaped NuGet
   package, are needed before the consumer can take a dependency.
3. **Consumer wiring** — reference bindings now exist for C#, C++, and Java
   (`oracle/CONSUMERS.md`). NTS Lab, GEOS (header-only), and JTS `jts-curve`
   (fork PR #7) copy them in. Production defaults still do **not** call the
   kernel; `isAvailable()` keeps CI green without `libntsrocq`.
4. **Call-site integration in production NTS / GEOS / JTS** — the actual
   Phase 5 headline: `RobustLineIntersector` / the noding pipeline calling
   the verified kernel. Bindings are in; flipping the default path is still
   blocked on 1–2, not on any proof. Official locationtech/jts is not the
   Java landing zone and is not a gate — that work is greenfield on
   `grootstebozewolf/jts#7` (`feature/sfa-curve-rgr`).
5. **Phase 6** (CI of the corpus against the NTS test suite) inherits directly
   from 3–4; it stays pending.

## 7. Honest scope statement

This slice does **not** make NTS verified. It removes one specific obstacle —
the subprocess boundary — between verified extracted code and a production
call site, and it gates the new boundary against the old one so the two can
never silently disagree. Every soundness caveat in §4 was already true of the
oracle and remains exactly as true through the FFI.

---

*AI disclosure: this document and the sources it describes were authored with
AI assistance (see [`CONTRIBUTING.md`](../CONTRIBUTING.md)).*
