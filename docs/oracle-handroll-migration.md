# Oracle hand-roll → extracted migration backlog

The oracle binary (`oracle/driver.ml`, the RocqRefRunner) is credible only
insofar as every mode is bit-exact against a **Coq-extracted** reference
(`oracle/extracted.ml`, generated from
`theories-flocq/Validate_binary64_extract.v`). A handful of Phase 4 modes
were shipped with **hand-rolled native OCaml arithmetic** that merely claims
to mirror an R-side Coq predicate, with no machine-checked link. That is a
credibility gap.

`scripts/check_oracle_handrolled.sh` is the **ratchet**: it freezes the
current hand-rolled surface (`docs/oracle-handrolled-allowlist.txt`) so no
new hand-rolled kernels can be added, and the set can only shrink. This doc
is the **backlog** for shrinking it — a multi-session Rocq effort, ordered by
risk/cost (cheapest and safest first). Each item, when done, deletes its
kernels from the allowlist in the same change (CI enforces this).

## Current hand-rolled surface

| Mode(s) | Hand-rolled kernels in `driver.ml` | Coq side today |
|---|---|---|
| `PASSES_THROUGH_FILTER`, `PASSES_THROUGH_HALFOPEN` | `round_half_to_even`, `lb_tlo`, `lb_thi`, `lb_touches`, `lb_touches_halfopen` (+ the no-arith wrappers `snap_coord_native`, `snap_native`, `lb_inslab_*`, `passes_through_*`) | **Verified b64 functions already exist**, just not extracted |
| `INCIRCLE_SIGN` | `incircle_r_native` | R-side only (`inCircle_R`, `ArcOrient.v:88`) |
| `ARC_CHORD_CROSSES_CIRCLE` | `run_arc_chord_crosses_circle` | R-side only (`chord_crosses_arc_circle`, `ArcIntersect.v:129`) |
| `ARC_PASSES_THROUGH_PIXEL` | `in_hot_pixel_halfopen`, `run_arc_passes_through_pixel` | R-side only (`arc_passes_through_hot_pixel`, `ArcHotPixel.v:95`) |

## Migration order (risk/cost ascending)

### 1. PASSES_THROUGH_* — extraction-only, no new proofs  *(lowest cost)*

The verified Flocq definitions already exist and are cited by the driver
comments:

- `b64_passes_through_hot_pixel` — `HotPixel_b64.v:2374`
- `b64_passes_through_hot_pixel_halfopen` — `PassesThroughHalfopen_b64.v:434`
- supporting `b64_liang_barsky_touches` (`HotPixel_b64.v:2128`),
  `b64_liang_barsky_touches_halfopen` (`PassesThroughHalfopen_b64.v:141`),
  `b64_snap_coord` / `b64_snap` (`HotPixel_b64.v:2368`/`2371`).

They were hand-rolled only because they were never added to the extraction
list. **Work:** add `b64_passes_through_hot_pixel` and
`b64_passes_through_hot_pixel_halfopen` to the `Extraction` call in
`Validate_binary64_extract.v`; replace `run_passes_through_filter` /
`run_passes_through_halfopen` bodies with the extracted calls; delete
`round_half_to_even`, `lb_tlo`, `lb_thi`, `lb_touches`, `lb_touches_halfopen`
(and the now-orphaned no-arith wrappers) from `driver.ml`; drop those five
names from the allowlist. **Risk:** low — no new mathematics; the extracted
functions carry their own soundness theorems. Validate bit-exactness against
the existing differential corpus.

### 2. INCIRCLE_SIGN — new b64_inCircle + integer-regime soundness  *(medium)*

No b64 side exists. **Work:** define `b64_inCircle` in `theories-flocq/`
(cofactor expansion mirroring `inCircle_R`), prove `B2R (b64_inCircle ...) =
inCircle_R ...` in an integer-exactness regime — analogous to
`Orient_b64_exact.v`'s `_sound_small_int`, but the determinant has degree-4
terms (squared norms `na, nb, nc`), so the no-overflow / exactness window is
tighter than orient2d's `|coord| <= 2^25`; derive and document the bound.
Extract `b64_inCircle`; replace `incircle_r_native`; drop it from the
allowlist. **Risk:** medium — the bound analysis is the load-bearing part.
This unblocks items 3 and 4.

### 3. ARC_CHORD_CROSSES_CIRCLE — sign-product over extracted incircle  *(medium, after 2)*

Depends on item 2. Once `b64_inCircle` is extracted, the sign-product test
becomes a thin wrapper over two extracted calls. **Work:** either compute the
sign product in a verified `b64_chord_crosses_arc_circle` (preferred — keeps
the predicate in Coq and re-uses the `chord_crosses_arc_circle_implies_circle_intersection`
IVT soundness story) and extract it, or, at minimum, reduce
`run_arc_chord_crosses_circle` to extracted `b64_inCircle` calls with the
sign-product in driver glue (still hand-rolled comparison — prefer the former
so it leaves the allowlist cleanly). Drop `run_arc_chord_crosses_circle`.
**Risk:** medium, mostly inherited from item 2.

### 4. ARC_PASSES_THROUGH_PIXEL — composition of incircle + hot-pixel  *(highest, after 1 & 2)*

Depends on items 1 and 2. The six-way disjunction composes four edge-crossing
incircle sign tests with two half-open hot-pixel membership tests.
**Work:** define and prove a `b64_arc_passes_through_hot_pixel` mirroring
`arc_passes_through_hot_pixel` (`ArcHotPixel.v:95`), reusing the extracted
`b64_inCircle` and the Phase 2 half-open membership predicate; extract it;
replace `in_hot_pixel_halfopen` and `run_arc_passes_through_pixel`; drop both
from the allowlist. **Risk:** highest — it is the composition, and the
endpoint membership must use exactly the Phase 2 half-open convention to stay
sound. Do last.

## Done criteria

The migration is complete when `docs/oracle-handrolled-allowlist.txt` is
empty (only comments) and `scripts/check_oracle_handrolled.sh` reports
`0 frozen hand-rolled kernel(s)` — i.e. every oracle mode is backed by an
extracted, soundness-carrying Coq function.
