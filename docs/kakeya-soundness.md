# Perron / Besicovitch–Kakeya shape — binary64 soundness diameter (2026-06-13)

## The well-posed stress question

`PerronStage.perron_stage n` is 2ⁿ thin triangles (apex `(1/2,1)`, base points
`(k/2ⁿ,0)`, signed area `1/2ⁿ → 0`): extreme area concentration and fine dyadic
coordinates, a natural adversary for the float plane. As with the hat
(`docs/hat-soundness.md`), the well-posed question is **not** an exact-ℝ
failure — the Perron geometry is `valid_geometry` at every stage
(`KakeyaOverlay.perron_geometry_valid`, Qed) — but the **binary64
coordinate-safety window**.

## The soundness diameter: stage 24

Scaling stage-n vertices by `2^(n+1)` makes them integers of magnitude
`≤ 2^(n+1)` (base point `(k/2ⁿ,0) ↦ (2k,0)`, apex `(1/2,1) ↦ (2ⁿ, 2^(n+1))`).
In `theories-flocq/KakeyaPerron_b64.v`:

- `perron_b64_inputs_int_safe` — for `n ≤ 24`, all three scaled vertices of
  every stage-n triangle are `coord_int_safe` (the |·| ≤ 2²⁵ window).
- `perron_tri_b64_orient_exact` — hence `b64_orient2d` on each scaled triangle
  equals the exact `cross_R_BP` (bit-exact, no rounding).
- `perron_tri_b64_cross_positive` — that cross is `2^(n+2) > 0`: every Perron
  sliver's orientation/area sign is computed correctly, however thin
  (area `1/2ⁿ`).
- `perron_b64_apex_unsafe_at_25` — at stage 25 the scaled apex y-coordinate is
  `2^(n+1) = 2^26 > 2^25`, leaving the window: the first stage where the scaled
  shape is no longer `coord_int_safe`.

So **stage 24 is the binary64 soundness diameter** for orient2d-exactness of the
scaled Perron shape. The brink is a coordinate-window fact (`coord_int_safe`,
2²⁵), not a geometric crossing.

## Complements hat-soundness.md

The hat gives a non-convex simple-ring `valid_polygon` witness; the scaled
Perron gives an area-concentration + coordinate-brink witness. Both stay inside
the same 2²⁵ integer window — the practical C#/NTS binary64 coordinate-safety
bound for the corpus's orient2d filter.
