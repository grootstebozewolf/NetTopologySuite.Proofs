# Oracle soundness finding — the `compute ⇒ spec` bridge is FALSE

**Date:** 2026-06-01. **Toolchain:** Rocq 9.1.1 + Flocq 4.2.2 (host fallback);
exact-real spec evaluated with Zarith `Q` (`Q.of_float` is exact — every
binary64 is a dyadic rational).

## Question

Item 1 migrated `PASSES_THROUGH_FILTER` / `_HALFOPEN` to the extracted
computational predicates `b64_passes_through_hot_pixel_compute` /
`_halfopen_compute` (`PassesThrough_b64_compute.v`). The deferred obligation
was stated as the **`compute ⇒ spec` rounding bridge**: that
`b64_passes_through_hot_pixel_compute = true` implies the exact-real spec
`b64_passes_through_hot_pixel = true` (which, via the `Qed` lemma
`b64_passes_through_sound`, would give geometric soundness vs the closed hot
pixel).

## Result: the bridge does not hold

`compute ⇒ spec` is **false**. The rounded `b64_div` in the Liang-Barsky
t-bounds lets the filter **over-accept within O(ulp) of tangency**.

**Oracle-confirmed counterexample** (hex-float, exact bits):

```
P0 = ( 0x1p+0            , -0x1.0000000000002p+1 )   (* (1, -2.0000000000000004) *)
P1 = ( 0x1.ffffffffffffp-2, -0x1.4000000000002p+1 )   (* (0.4999999999999999, -2.5000000000000004) *)
C  = ( 0x0p+0            , -0x1p+1               )   (* (0, -2) *)

oracle_bin PASSES_THROUGH_FILTER  =>  TRUE        (the extracted compute)
exact-rational spec               =>  FALSE       (touch(orig)=false, touch(snap)=true)
```

The original segment misses the closed pixel by sub-ulp; exact arithmetic
says FALSE, the rounded filter says TRUE.

## Methodology (grounded, exhaustive sampling)

`compute` = the extracted `b64_passes_through_hot_pixel_compute`. `spec` = the
exact-real `b64_liang_barsky_touches` recomputed in Zarith `Q` (same `lb_inslab`
closed convention, same round-half-to-even snap). Harnesses:
`oracle/test_bridge{,2,3}.ml`.

| Sampling | cases | `compute&&!spec` (soundness viol.) | `!compute&&spec` (completeness viol.) |
|---|---|---|---|
| half-integer grid, ‖·‖≤4 | 5,000,000 | **0** | 0 |
| full-range binary64 (int/half/quarter/near-grid+ε/generic) | 5,000,000 | **0** | 0 |
| adversarial near-tangency (corners/edges ± 2⁻⁵⁰) | 8,000,000 | **4916** | **0** |

## Interpretation

1. **`compute ⇒ spec` (soundness vs exact geometry) is false** — concrete,
   oracle-reproduced. This is intrinsic to the *rounded Liang-Barsky
   algorithm*, not a defect of the oracle: the C# port computes the same
   rounded predicate and has the same O(ulp) boundary behaviour. The oracle
   remains a faithful **bit-exact** mirror of it (validated, 2M-case check,
   `oracle/test_pt.ml`), which is its actual job in differential testing.

2. **`spec ⇒ compute` (completeness) holds** across 18M cases including
   adversarial tangency: 0 violations. The rounded filter never *drops* a real
   pass — it is a **conservative over-approximation**. For a snap-rounding
   noder this is the safe direction ("when uncertain, keep"): composed with the
   `Qed` lemma `b64_passes_through_complete` (geometric pass ⇒ spec bool), it
   gives *oracle completeness vs geometry* — the oracle never misses a crossing.

3. **On the dyadic integer/half-integer grid, `compute ≡ spec` exactly**
   (0 divergence either way, 5M cases). Soundness *is* recoverable in a grid
   regime — or in a "fattened pixel" (±O(ulp)) sense — just not against the
   sharp closed pixel for off-grid inputs.

## Corrected obligation

The original "`compute ⇒ spec`" target was the wrong direction to chase. The
provable, useful statements are:

- **(C1) grid exactness:** for integer (or half-integer) coordinates,
  `b64_passes_through_hot_pixel_compute = b64_passes_through_hot_pixel`
  (bit-equal booleans) — division rounding cannot flip the decision on the
  grid. Multi-session Flocq proof; strongly evidenced (5M, 0 divergence).
- **(C2) completeness:** `b64_passes_through_hot_pixel = true ⇒
  b64_passes_through_hot_pixel_compute = true`, giving oracle completeness vs
  geometry through `b64_passes_through_complete`. Evidenced (0 violations,
  18M). This is the soundness-relevant guarantee for noder use.

What is **not** provable, and should not be claimed: `compute = true ⇒` exact
geometric pass for arbitrary binary64 inputs (disproved above).
