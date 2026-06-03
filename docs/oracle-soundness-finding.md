# Oracle soundness finding — the `compute ⇒ spec` bridge is FALSE

> **Filename caveat (read first).** This file records that *soundness* vs the
> sharp closed pixel is **disproved**, and that the real obligation is
> **completeness** (`spec ⇒ compute`, "never drop a real pass"). The word
> "soundness" in the filename predates this framing; do not read it as a
> claim. Soundness is not claimed anywhere.

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

> **Now machine-checked (2026-06-02).** This disproof is no longer
> oracle-evidence-only: it is a `Qed`-closed Rocq theorem,
> `b64_passes_through_compute_unsound` in
> [`theories-flocq/PassesThrough_b64_compute_unsound.v`](../theories-flocq/PassesThrough_b64_compute_unsound.v):
> ```coq
> Theorem b64_passes_through_compute_unsound :
>   exists P0 P1 C : BPoint,
>     b64_passes_through_hot_pixel_compute P0 P1 C = true /\
>     b64_passes_through_hot_pixel P0 P1 C = false.
> ```
> The witness is the hex-float triple below. `compute = true` is decided by
> `vm_compute`; `spec = false` reduces to the exact rational inequality
> `tlo_x = 2⁴⁹/(2⁴⁹+1) > thi_y = (2⁴⁹−1)/2⁴⁹` (an `N² > N²−1` sub-ulp gap),
> so the clipped parameter interval is empty. Same three classical-reals
> axioms + Flocq's `Classical_Prop.classic`; no `Admitted`.
>
> The **half-open** mode (`PASSES_THROUGH_HALFOPEN`) is likewise disproved:
> `b64_passes_through_halfopen_compute_unsound` in
> [`theories-flocq/PassesThroughHalfopen_b64_compute_unsound.v`](../theories-flocq/PassesThroughHalfopen_b64_compute_unsound.v),
> witnessed by the same triple with x negated (reflecting the tangency to the
> bottom-left so the half-open strict midpoint checks pass while the exact
> miss is unchanged).

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

## C2 — completeness (`spec ⇒ compute`): strongly evidenced, proof BLOCKED

**This is COMPLETENESS, not soundness** — the snap-rounding-noder safety
direction "every real pass is flagged; never drop a crossing". Soundness stays
disproved (above) and unclaimed.

**Target** (real signature from Phase S — `BPoint` args, no tol, scale = 1):

```coq
Theorem b64_passes_through_complete_compute :
  forall P0 P1 C : BPoint,
    b64_passes_through_hot_pixel P0 P1 C = true ->        (* exact-real spec *)
    b64_passes_through_hot_pixel_compute P0 P1 C = true.  (* rounded compute *)
```

Composed with the `Qed` lemma `b64_passes_through_complete` (R ⇒ spec) this
gives **R ⇒ compute** = "the oracle never drops a real crossing". Phase S: no
such lemma exists; not definitional (exact `B2R` vs rounded `b64_*`).

**Empirics (extending the table above).** No completeness counterexample
exists in any sampling, including the boundary band where one would live:

| sampling | cases | completeness viol. (`spec&&!compute`) | dual (`compute&&!spec`) |
|---|---|---|---|
| exhaustive half-integer grid | 36,864 | 0 | 0 |
| ULP-band: ±3 ulp on every grid coord | 217,728 | **0** | 3,246 |

(`oracle/test_c2.ml`, `test_c2b.ml`.) The asymmetry is the whole story:
`compute` is a robust **over-approximation** of `spec` — it never under-accepts
even at tangency, while it over-accepts thousands of times in the same band.

**BLOCKER (grounded, real Coq).** `intros; unfold; apply andb` reduces the
target to a touch-level goal in which the hypothesis `H1` is the **exact-real**
touch (`Binary.B2R …` + `Rle_bool (Rmax 0 (Rmax (lb_tlo …) …)) (Rmin 1 …)`,
exact `Rminus`/`Rinv` bounds) and the goal is the **binary64-rounded** touch
(`b64_div`/`b64_le`/`b64_min`/`b64_max`). The final comparison needs

```
B2R (b64_max 0 (b64_max tlo'_x tlo'_y))  <=  B2R (b64_min 1 (b64_min thi'_x thi'_y))
```

after which `b64_le_complete` (`B2R a <= B2R b -> b64_le a b = true`, present,
`Qed`) closes it. But `B2R (b64_div …) = round((lo-c0)/(c1-c0))` rounds the
**lower** t-bounds up and the **upper** t-bounds down, and round-to-**nearest**
gives no outward guarantee. So `H1`'s exact `LHS <= RHS` does **not** imply the
rounded `LHS <= RHS`: `b64_le_complete` is available but its hypothesis is
exactly the step monotonicity cannot discharge.

**Documented tangent.** Expected a forward-error/monotonicity bridge (exact
pass ⇒ rounded pass). The goal instead demands a *computation-specific* proof
that the round-to-nearest errors in this divide-and-clip never align to flip
the composite comparison inward — the ulp-band the 217,728-case probe (and 18M
random) never broke, but which monotonicity cannot rule out. Closing it needs
that deep argument (or a measure-~2⁻¹⁰⁴ counterexample search). **No `Admitted`
was left in the corpus**; C2 remains an open, strongly-evidenced obligation.
