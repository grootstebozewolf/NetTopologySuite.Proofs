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

## The computational-vs-spec gap (read this first)

The modes that are *already* extracted (`ORIENT*`, `INTERSECT*`, `SIMPLIFY`,
`EDGE_IN_RESULT`) compute on the **`binary64` / `binary_float` layer**:
`b64_orient2d` threads coordinates through `b64_minus` → `Binary.Bminus`,
which `Validate_binary64_extract.v` overrides with native `-.`. Such
functions extract to runnable OCaml and are bit-exact by construction.

The hand-rolled modes are different. Their Coq "b64" namesakes are
**specifications over Coq's axiomatic real type `R`**, not evaluators:

- `b64_liang_barsky_touches` (`HotPixel_b64.v:2128`) computes via
  `Binary.B2R prec emax (...) : R`, then `Rmax`/`Rmin`/`Rle_bool`/`Req_dec_T`.
  `R` and its order are non-computational, so this **cannot be extracted** to
  running OCaml. (`b64_snap_coord` *is* computational — `Binary.Bnearbyint`.)
- `inCircle_R`, `chord_crosses_arc_circle`, `arc_passes_through_hot_pixel`
  are defined on `Point` / `R` outright — pure spec, no binary64 layer.

So **no hand-rolled mode has a computational Coq counterpart today.** Every
item below requires authoring a *new* computational `binary64` definition
(on `b64_*` ops) and proving it `B2R`-sound against the existing R-spec. This
is genuine multi-session Rocq work; there is no extraction-only shortcut.

## Current hand-rolled surface

| Mode(s) | Hand-rolled kernels in `driver.ml` | Coq side today |
|---|---|---|
| ~~`PASSES_THROUGH_FILTER`, `PASSES_THROUGH_HALFOPEN`~~ **MIGRATED** | — (extracted `b64_passes_through_hot_pixel_compute` / `_halfopen_compute`) | computational `PassesThrough_b64_compute.v`; R-spec carries exact soundness |
| ~~`INCIRCLE_SIGN`~~ **MIGRATED** | — (extracted `b64_inCircle`, also feeds the ARC_* sign-products) | computational `InCircle_b64_compute.v`; integer-regime exactness deferred |
| `ARC_CHORD_CROSSES_CIRCLE` | `run_arc_chord_crosses_circle` | R-side only (`chord_crosses_arc_circle`, `ArcIntersect.v:129`) |
| `ARC_PASSES_THROUGH_PIXEL` | `in_hot_pixel_halfopen`, `run_arc_passes_through_pixel` | R-side only (`arc_passes_through_hot_pixel`, `ArcHotPixel.v:95`) |

## Migration order (risk/cost ascending)

### 1. PASSES_THROUGH_* — new computational Liang-Barsky  ✅ DONE (compute path)

**Status:** the compute path is migrated. `theories-flocq/PassesThrough_b64_compute.v`
defines `b64_liang_barsky_touches_compute` / `_halfopen_compute` and
`b64_passes_through_hot_pixel_compute` / `_halfopen_compute` on the `b64_*`
layer (mirroring the deleted native kernels op-for-op); they are extracted
(with `b64_min`→`Float.min`, `b64_one/two/half`→literals, `b64_snap_coord`→
native round-half-even overrides in `Validate_binary64_extract.v`) and the
driver calls them. Bit-exact with the old native code over 2,000,000 random +
boundary-stressed cases (`oracle/test_pt.ml`); full corpus builds green.
**Remaining (deferred):** forward-error / integer-regime soundness of the
*rounded* compute predicate to `b64_segment_touches_hot_pixel_closed_spec`
(the R-spec carries the exact geometric soundness; bridging the rounding is
the open obligation — `b64_div` rounds, so it is not an equality).

Original analysis follows. Most scaffolding already exists, which is why this is still first: the snap
half (`b64_snap_coord` via `Bnearbyint`) is computational and needs only an
`Extract Constant Binary.Bnearbyint => <native round-half-even>`; and the
R-spec (`b64_liang_barsky_touches`), its per-axis lemma (`lb_axis_sound`),
and the snap bridge (`b64_snap_coord_B2R`) are proved.

**Work:** author a *computational* `b64_liang_barsky_touches_compute : BPoint
-> BPoint -> BPoint -> bool` on `b64_minus` / `b64_div` / `b64_le` /
`Bcompare` (mirroring the native `lb_*` arithmetic); prove it equals the
R-valued `b64_liang_barsky_touches` under a no-overflow precondition; build
`b64_passes_through_hot_pixel_compute` on top; extract it (plus the Bnearbyint
constant); replace the `run_passes_through_*` bodies; delete
`round_half_to_even`, `lb_tlo`, `lb_thi`, `lb_touches`, `lb_touches_halfopen`
(and orphaned wrappers); drop those five names from the allowlist.
**Risk:** medium-low — the division `(lo-c0)/(c1-c0)` needs a non-zero /
no-overflow guard; reuse the existing degenerate-axis split (`lb_inslab` /
`Req_dec_T`). Validate bit-exactness against the existing differential corpus.

### 2. INCIRCLE_SIGN — new b64_inCircle  ✅ DONE (compute path)

**Status:** migrated. `theories-flocq/InCircle_b64_compute.v` defines
`b64_inCircle` (mirroring `inCircle_R` op-for-op on the `b64_*` layer);
extracted and called by INCIRCLE_SIGN *and* both ARC_* sign-products, so the
shared `incircle_r_native` kernel is deleted. Bit-exact with the old native
code over 2,000,000 random + integer-regime cases (`oracle/test_ic.ml`); full
corpus builds green. **Remaining (deferred):** integer-regime exactness of the
b64 sign vs `inCircle_R` — clean here because the determinant has *no
division*, so for `|coord| <= 2^12` every op is exact (`4k+2 <= 53`) and the
binary64 sign equals `inCircle_R`'s sign (an exactness theorem in the
`Orient_b64_exact._sound_small_int` style, not a forward-error bound).

Original analysis follows.

### 2-orig. INCIRCLE_SIGN — new b64_inCircle + integer-regime soundness  *(medium)*

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
