# Hat monotile soundness — correction & scope (2026-06-13)

## The "growing supertile breaks ring_simple" idea is ill-posed

A proposed stress test was to grow hat supertiles (level-1 → level-2 → …)
until the patch first violates `ring_simple` / `valid_polygon`, taking the
breaking edge pair as an empirical "soundness brink."

**There is no such brink in exact ℝ.** The hat aperiodic tiling is *exact*:
every tile is a simple polygon and tiles meet edge-to-edge without
interior-interior crossings, at every scale. So for *every* finite hat patch:

- each tile ring is `ring_simple` (`HatValidPolygon.hat_ring_simple`, and any
  isometric copy by `HatPatch.ring_simple_translate`);
- distinct tiles are pairwise non-crossing;
- each tile is a `valid_polygon` (`HatValidPolygon.valid_polygon_hat`).

A lemma of the shape "all tiles simple ⟹ some breaking proper-cross pair
exists" is therefore vacuous/false over the corpus's exact-ℝ predicates.
Additionally, the corpus has **no** hat substitution/inflation machinery (the
H/T/P/F metatile system), and deliberately disclaims aperiodicity
(`HatMonotile.v` header), so no `hat_supertile : nat -> list Ring` generator
exists to drive such growth.

## The evidence already landed

- `HatValidPolygon.hat_ring_simple` — the non-convex 13-gon has no improper
  self-crossing (the ~78 edge-pair case-analysis, closed: the crossing system
  is linear in the segment parameters, so `nra` + `sqrt 3·sqrt 3 = 3`
  discharges every pair).
- `HatPatch.hat_patch_all_valid` / `hat_patch_non_crossing` — a concrete
  two-hat patch is a list of `valid_polygon`s whose edges are pairwise
  non-crossing (second hat placed by translation; non-crossing between hats by
  x-band separation). A genuine finite multi-tile witness.

## The real soundness metric: the binary64 coordinate window

The only place soundness can degrade is the **float layer**, not exact ℝ:

- The *metric* hat uses `hexPt x y = (x + y/2, y·√3/2)`. The `√3` factor is
  **not** representable in binary64 at all, so the metric hat does not transport
  to b64 exactly — only the **rational embedding** `(x + y/2, y)` (same
  combinatorial polygon; cf. `SpectreExample.v`) is b64-exact.
- For the rational embedding, lattice coordinates transport exactly as long as
  they stay in the corpus's integer window (`coord_int_safe`, |n| ≤ 2²⁵, with
  products kept below 2⁵³). That window — not any geometric crossing — is the
  practical "soundness diameter" for the C#/NTS binary64 polygon layer: patches
  whose vertices fit the window round-trip exactly; beyond it, float rounding is
  the failure mode.

No new lemma is needed to "find a brink": there isn't one in ℝ, and the float
brink is the documented `coord_int_safe` window.
