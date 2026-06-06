# Spectre monotile — `point_in_ring` regression anchor

**Coq artifact:** [`theories/SpectreExample.v`](../theories/SpectreExample.v)
(Qed-closed; standard three-axiom classical-reals base).

---

## What this is (and isn't)

A stress test of the `Overlay.ray_parity_odd` / `point_in_ring` machinery on the
**Spectre** aperiodic monotile — a complex **non-convex 14-gon**. It is a
**regression anchor**, **not** part of the `extract_rings_valid` pipeline (a
monotile is not a pipeline face).

| proved (unconditional, Qed) | |
|---|---|
| `spectre_ring_closed` | `ring_closed` (structural) |
| `spectre_min_points` | `ring_has_minimum_points` (14 ≥ 4) |
| `spectre_point_in_ring` | `point_in_ring` for a verified interior point — the rightward ray crosses exactly one of the 13 edges → odd parity |
| `hole_inside_outer_spectre` | a hole vertex at that point lies inside |

**Not claimed:** `ring_simple` for this non-convex 14-gon (no two non-adjacent
edges properly cross) is ~70 edge-pair checks — a separate, larger effort,
deliberately omitted rather than hand-waved.

## Coordinates — an honest note

The Spectre lives on a hex grid; the metric-exact **equilateral** embedding maps
hex `(x,y)` to `(x + y/2, y·√3/2)`. This file uses the **rational** embedding
`(x + y/2, y)` — the *same combinatorial polygon*, differing only by a uniform
**vertical scale** (`·√3/2`). A vertical scale maps horizontal rays to horizontal
rays and preserves left/right order at any fixed height, so the rightward-ray
**crossing parity** (hence `point_in_ring`) is **identical** to the equilateral
version — while keeping all arithmetic rational so `lra` discharges each
`edge_crosses_ray` exactly. The hex vertex coordinates are exactly the canonical
Spectre's.

The interior point is `(5, 1/2)`: height `1/2` sits strictly between hex levels
`0` and `1`, so the ray grazes no vertex; `x = 5` sits between the two lower
"feet", where the ray crosses exactly the south-east edge `(6,0)-(7.5,1)` (x-
intercept `6.75 > 5`) and no other → odd → inside. The proof *verifies* this
count by walking the `ray_parity_odd` constructors (4 skips, 1 cross, 8 skips,
nil); any miscount would fail to typecheck.
