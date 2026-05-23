# Phase 2 HotPixel follow-ups: scouting + feasibility

**Status**: Scouting report (no proofs landed yet).
**Date**: 2026-05-23
**Scope**: The four follow-up slices documented at the foot of
[`theories-flocq/HotPixel_b64.v`](../theories-flocq/HotPixel_b64.v), ranked by
tractability and cross-checked against what Phase 0/1 and Flocq already
provide.

## Headline finding

The Phase 2 foundations (`HotPixel.v` + `HotPixel_b64.v`) sit on a much
thicker foundation than `audit-phase2-snap-rounding.md` projected when it
was written.  Three of the four follow-up slices are bounded by *existing*
corpus primitives plus one external Flocq lemma each; the fourth (segment
touches pixel) is the only one whose substance is new.

The natural first-cycle target is **Slice 4 (exact-radius under
power-of-two scale)**, not Slice 1 (the bridge from rounded pixel back to
R-side `in_hot_pixel`).  Slice 1 reads as "smaller" but factually depends
on Slice 4 (the bound computation `cx ± r` is only exact when `r` itself
is exact), so the right ordering is 4 → 1 → 2 → 3.

The four slices in priority order:

| # | Slice | First-cycle fit | Depends on |
|---|-------|-----------------|------------|
| 4 | Exact radius under power-of-two scale | **Yes** | one Flocq lemma |
| 1 | Bound bridge: rounded pixel → exact R-side `in_hot_pixel` | After 4 | Slice 4 + one new auxiliary lemma |
| 2 | `b64_hot_pixel_center` (round-to-integer snap) | Independent | `Bnearbyint` from Flocq |
| 3 | `b64_segment_touches_hot_pixel` | After 1/2 | none new — but substance is new |

The rest of this document walks each slice with file:line citations and a
predicted theorem statement.

## What Phase 0/1 already gives us

The shipped integer-regime exactness framework in
[`theories-flocq/Orient_b64_exact.v`](../theories-flocq/Orient_b64_exact.v)
is directly reusable for the bound computations:

```coq
(* Orient_b64_exact.v:213 *)
Lemma b64_minus_int_exact :
  forall x y : binary64, forall a b : Z,
    Binary.is_finite prec emax x = true ->
    Binary.is_finite prec emax y = true ->
    Binary.B2R prec emax x = IZR a ->
    Binary.B2R prec emax y = IZR b ->
    (Z.abs (a - b) <= 2 ^ prec)%Z ->
    Binary.B2R prec emax (b64_minus x y) = IZR (a - b) /\
    Binary.is_finite prec emax (b64_minus x y) = true.

(* Orient_b64_exact.v:236 *)
Lemma b64_mult_int_exact : (* analogous, with |a * b| <= 2^prec *)

(* Orient_b64_exact.v:262 *)
Lemma b64_plus_int_exact : (* analogous, with |a + b| <= 2^prec *)

(* Orient_b64_exact.v:174 *)
Lemma b64_round_IZR_exact :
  forall n : Z, (Z.abs n <= 2 ^ prec)%Z -> b64_round (IZR n) = IZR n.

(* Orient_b64_exact.v:130 *)
Lemma generic_format_IZR_le_bpow_prec :
  forall n : Z, (Z.abs n <= 2 ^ prec)%Z ->
    generic_format radix2 b64_fexp (IZR n).
```

Plus the `coord_int_safe` predicate (`Orient_b64_exact.v:293`).  These
are the load-bearing components for slices 1 and 4.

## Slice 4 — Exact radius under power-of-two scale

**Why this is the right first cycle.**  The radius is `1 / (2 * scale)`.
For arbitrary `scale` it involves two rounding steps and is not
generally exact.  When `scale` is a positive power of two (the
real-world case for GIS grids: micrometre, millimetre, integer tile
resolutions), both steps are bit-exact and the radius equals the exact
mathematical value.  This unlocks the bound bridge in Slice 1 because
`cx ± r` exactness depends on `r` exactness.

**Predicted theorem:**

```coq
Theorem b64_hot_pixel_radius_exact_pow2 :
  forall (scale : binary64) (e : Z),
    Binary.is_finite prec emax scale = true ->
    Binary.B2R prec emax scale = bpow radix2 e ->
    (1 <= e <= 1021)%Z ->          (* keeps `2 * scale` < bpow emax *)
    Binary.B2R prec emax (b64_hot_pixel_radius scale)
      = bpow radix2 (- (e + 1)).
```

**Proof sketch.**

1. `2 * scale` is exact: `b64_mult b64_two scale` lands on `bpow (e+1)`,
   by `b64_mult_int_exact` (taking `a = 2`, `b = 2^e`) or directly via
   `b64_mult_correct` + `generic_format_bpow_b64` (the latter is at
   `B64_bridge.v` — `generic_format_bpow_b64`).
2. `1 / bpow (e+1)` is in the FLT format: need a Flocq lemma stating
   that `bpow radix2 (-k)` is in the FLT format whenever `-k >= emin`.
   This is the missing external piece — it follows from
   `generic_format_bpow` with the appropriate exponent bound, but it
   needs to be wrapped at the binary64 instance level.
3. Compose: rounding fixes a value already in the format, so
   `b64_div b64_one (b64_mult b64_two scale)` evaluates exactly to
   `bpow (-(e+1))`.

**Effort estimate.**  ~80 lines.  Most of the proof is bookkeeping
around `bpow` arithmetic.  The hard part is locating or wrapping the
"reciprocal of a power of two is representable" lemma.  If
`generic_format_bpow` lifts cleanly, the rest is mechanical.

**Open empirical question.**  Does Flocq's `generic_format_bpow`
already cover the negative-exponent case?  The signature
`forall e, (emin <= e)%Z -> generic_format ... (bpow radix2 e)` covers
this directly when `e` is allowed to be negative — Flocq's `emin` is
`-1074` for binary64, so `e in [-1074, 1024)` is fully in-scope.
Verifying this in the build environment is the first action of the
Slice 4 cycle.

## Slice 1 — Bound bridge: rounded pixel → R-side `in_hot_pixel`

**Goal.**  Close the gap between `b64_in_rounded_hot_pixel` (the rounded
pixel that `b64_in_hot_pixel` actually decides) and the R-side
`in_hot_pixel P C scale`.  This needs every bound computation
(`bx C ± r`, `by_ C ± r`) to be exact, which only happens when:

- `r` is exact (Slice 4 gives this for power-of-two scale), AND
- `bx C`, `by_ C` are in a regime where adding `r` doesn't round.

**The auxiliary lemma needed (not yet in the corpus).**  When `x` is an
integer-valued binary64 with `|int(x)| <= 2^(prec - e - 1)` and `r =
bpow (-e)` for `e >= 0`, then `b64_plus x r` is exact and its value is
`IZR(int(x) * 2^(e+1) + 1) * bpow(-(e+1))`.  Proof: witness via
`generic_format_F2R` with mantissa `m = int(x) * 2^(e+1) + 1` and
exponent `f = -(e+1)`; `|m| <= 2^prec` is the side-condition.

This is "integer-times-power-of-two plus power-of-two" exactness — a
companion to `b64_plus_int_exact` for the mixed-precision case.  Not in
the corpus today; ~30 lines.

**Predicted headline:**

```coq
Theorem b64_in_rounded_hot_pixel_bridge :
  forall (P C : BPoint) (scale : binary64) (e : Z),
    Binary.B2R prec emax scale = bpow radix2 e ->
    (1 <= e <= 25)%Z ->
    coord_int_safe (bx C) ->
    coord_int_safe (by_ C) ->
    (* finiteness of P's coords; the lower-bound side of the regime *)
    Binary.is_finite prec emax (bx P) = true ->
    Binary.is_finite prec emax (by_ P) = true ->
    b64_in_rounded_hot_pixel P C scale ->
    in_hot_pixel (BP2P P) (BP2P C) (Binary.B2R prec emax scale).
```

The `e <= 25` bound mirrors the `coord_int_safe` 25-bit regime: with
both factors of `cx * 2^(e+1)` bounded by `2^25` and `2^26` respectively,
the mantissa stays within `2^53`.

**Effort estimate.**  ~150 lines (the auxiliary lemma + four
instantiations + finiteness chain).  Depends on Slice 4 closing.

## Slice 2 — `b64_hot_pixel_center`: round-to-integer snap

**Status.**  Flocq 4.1+ ships `Binary.Bnearbyint` with companion
correctness lemma `Bnearbyint_correct` (in `Flocq.IEEE754.Binary`).  The
existing corpus doesn't bind it yet because no current slice needed
round-to-integer.

**What needs building.**

1. A wrapper `b64_nearbyint : binary64 -> binary64` instantiating
   `Binary.Bnearbyint` at the `prec`/`emax` parameters and a chosen
   rounding mode (likely `mode_NE` to match the rest of the corpus).
2. A safety predicate `b64_nearbyint_safe`: input is finite,
   no-overflow on the rounded result (mostly automatic — rounding to
   integer cannot increase magnitude beyond `Rabs x + 1` in any sane
   regime).
3. A correctness theorem lifting `Bnearbyint_correct` to the corpus's
   B2R / is_finite vocabulary.
4. The snap definition:
   ```coq
   Definition b64_hot_pixel_center (P : BPoint) (scale : binary64) : BPoint :=
     let xs := b64_mult (bx P) scale in
     let ys := b64_mult (by_ P) scale in
     let xi := b64_nearbyint xs in
     let yi := b64_nearbyint ys in
     mkBPoint (b64_div xi scale) (b64_div yi scale).
   ```
5. An R-side soundness theorem: under integer-regime + power-of-two
   scale, `b64_hot_pixel_center P scale` lands on the grid in
   `on_grid` sense, and its distance from `P` is at most
   `hot_pixel_radius scale`.

**Effort estimate.**  ~100 lines for the wrapper + correctness; ~80 lines
for the soundness theorem.  Independent of slices 1 and 4 (different
operation), but the soundness theorem benefits from Slice 4's exact-
radius result.

**Open empirical question.**  Does the host runner's Flocq version
include `Bnearbyint`?  The corpus pins to Flocq 4.2.2 (per
`stage-d-feasibility.md`), which is post-4.1, so this should be
present.  Verify with a `Require Import` smoke test as the first
action of the Slice 2 cycle.

## Slice 3 — `b64_segment_touches_hot_pixel`: parametric or BB?

**The genuine choice.**  Two reasonable forms:

(a) **Parametric existential**, mirroring the R-side definition in
    `HotPixel.v:110`:
    ```coq
    Definition b64_segment_touches_hot_pixel
        (P0 P1 C : BPoint) (scale : binary64) : Prop :=
      exists t : R, 0 <= t <= 1 /\
        in_hot_pixel (b64_segment_point P0 P1 t) (BP2P C)
                     (Binary.B2R prec emax scale).
    ```
    Easy to relate to the R-side; hard to *decide* (the witness `t` is a
    real number).  Useful for proof reasoning but not directly callable
    from the noder.

(b) **Decidable bounding-box filter**:
    ```coq
    Definition b64_segment_touches_hot_pixel_bbox
        (P0 P1 C : BPoint) (scale : binary64) : bool := ...
    ```
    Returns true if either endpoint is inside the pixel, or the
    segment's axis-aligned bounding box overlaps the pixel's box.
    Decidable; suitable for the noder's filter step.  Conservative —
    can return true for segments that don't actually touch (e.g., a
    diagonal that crosses the corner of the bounding box but misses
    the pixel).

**Recommended approach.**  Ship both, with the parametric form as the
specification and the bounding-box form as the implementation, plus a
soundness theorem `bbox = false -> parametric form is False` (i.e., the
bounding-box filter never spuriously rejects a touching segment — the
right safety property for a noder filter step).

The completeness direction (`bbox = true -> exists t, ...`) is *not*
required for the noder; the noder fall-through goes to a Stage-B
predicate that resolves the false positives.  This is the same pattern
as Phase 0 Stage A's filter.

**Effort estimate.**  ~80 lines for the bounding-box form + decidability
+ NaN safety; ~150 lines for the soundness theorem (bbox-false →
parametric-false).  Parametric soundness in the other direction is
much harder (segment crosses pixel implies the witness `t` exists with
non-trivial geometric content) and is the natural slot for the
"passes-through" theorem from `audit-phase2-snap-rounding.md` §2.2.

## What got built (so far)

Nothing in this slice yet.  This document is the scouting deliverable;
the next cycle picks one of the four slices and runs the red workflow
on it.

## Recommended first cycle

**Slice 4 — exact radius under power-of-two scale.**

Reasons:

- Smallest slice that delivers a self-contained Qed.
- Unblocks Slice 1 (the bridge).
- Provides empirical data on whether
  `generic_format_bpow_b64` extends to the negative-exponent case
  cleanly, which is the load-bearing Flocq dependency for half the
  follow-ups.
- No new external Flocq surface — uses `generic_format_bpow`,
  `b64_mult_correct`, `b64_div_correct` (all already in the corpus's
  Flocq seam).

If `generic_format_bpow_b64` turns out *not* to cover the negative-
exponent case directly, that's a tangent: capture it, and the cycle
either extends to wrap the lemma in `B64_bridge.v` or backs off to
Slice 2 (which doesn't depend on this).

## What this doc does NOT do

- It does **not** start the Slice 4 proof.  The predicted theorems are
  sketched, not Qed-closed.
- It does **not** commit to ordering beyond the first cycle.  Slices 2
  and 3 are independent of slices 1 and 4 and can be interleaved as
  attention permits.
- It does **not** address the Hobby 1999 topological correctness
  theorem (the major thesis-shaped piece from
  `audit-phase2-snap-rounding.md`).  That sits downstream of all four
  slices here.

## Open items as inputs to future sessions

| Item | Type | Notes |
|------|------|-------|
| Slice 4 first attempt | next-cycle | Predicted ~80 lines, depends on Flocq `generic_format_bpow` covering negative exponents at b64 instance |
| Slice 1 bridge | follow-up | Needs Slice 4 + one new auxiliary lemma (`~30` lines); total ~150 lines |
| Slice 2 `b64_nearbyint` wrapper | independent | Needs Flocq `Bnearbyint` present in build environment; ~180 lines total |
| Slice 3 bounding-box form | independent | ~80 lines; soundness theorem ~150 lines |
| Hobby 1999 topological correctness | thesis-scale | Out of scope for this scouting; queued for the multi-month engagement |

Each slice is a legitimate next move.  The discipline picks one based on
attention available, runs the cycle, and stops at the principled
endpoint.

## Citations

- [`theories/HotPixel.v`](../theories/HotPixel.v) — R-side foundations
  (`hot_pixel_radius`, `in_hot_pixel`, `segment_touches_hot_pixel`,
  `on_grid`).
- [`theories-flocq/HotPixel_b64.v`](../theories-flocq/HotPixel_b64.v) —
  binary64 foundations + four deferred-slice block at lines 269–298.
- [`theories-flocq/Orient_b64_exact.v`](../theories-flocq/Orient_b64_exact.v) —
  the integer-regime exactness framework reused throughout.
- [`docs/audit-phase2-snap-rounding.md`](audit-phase2-snap-rounding.md) —
  the macro audit this scouting is the operational follow-on to.
- [`docs/stage-d-feasibility.md`](stage-d-feasibility.md) — template
  for the scouting-doc shape; what worked there is mirrored here.
- Flocq `Bnearbyint` documentation:
  <https://flocq.gitlabpages.inria.fr/flocq/html/Flocq.IEEE754.Binary.html>
  (introduced in Flocq 4.1.0; the corpus pins to 4.2.2).
