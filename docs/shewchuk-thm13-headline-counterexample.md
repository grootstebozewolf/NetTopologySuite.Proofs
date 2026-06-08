# Shewchuk Theorem 13 headline — counterexample to the corpus statement

**Finding.** The deferred headline `fast_expansion_sum_nonoverlap_shewchuk`
(`theories-flocq/B64_FastExpansionSum_Shewchuk.v:483`, Tier-3 deferred) is
**false as stated**. It should be reclassified Tier-2 (counterexample), alongside
its already-refuted building block `b64_grow_expansion_nonoverlap`.

## Why

The corpus's output predicate is built on

```
strict_succ_b64 a b := |B2R b| <= ulp(B2R a) / 2
nonoverlap_shewchuk e := nonoverlap_strict (compress e)
```

`strict_succ_b64` forces each component to sit within a **half-ulp** of its
predecessor. That is the exact postcondition of a *single* `TwoSum`'s
`(high, low)` pair (the `B64_Expansion` comment even says "matches what
TwoSum/Dekker produce"), but it is **strictly stronger** than Shewchuk's
"(strongly) nonoverlapping", which only forbids overlapping significand bits.
A multi-term `fast_expansion_sum` emits bit-disjoint components that are *not*
within a half-ulp.

## The witness (machine-checked: `B64_Shewchuk_Thm13_counterexample.v`)

Value `257 = 256 + 1`:

| Fact | Lemma |
|---|---|
| `nonoverlap_shewchuk [256; 1]` is **false** (`1 > ulp(256)/2 = 2⁻⁴⁵`) | `nonoverlap_shewchuk_256_1_false` |
| `e = [2^60; 1]` is valid `nonoverlap_shewchuk` (`1 ≤ ulp(2^60)/2 = 128`) | `e_nonoverlap` |
| `f = [-(2^60 − 256)]` is valid | `f_nonoverlap` |
| `expansion_R e + expansion_R f = expansion_R [256; 1] = 257` | `inputs_sum_eq` |

So a sum of two *valid* inputs has the bit-disjoint 2-component representation
`[256; 1]`, which the strong predicate rejects.

## The structural link (hand-traced; not reduced in Coq)

`fast_expansion_sum e f` processes the magnitude-sorted merge
`[1, -(2^60−256), 2^60]`:

| step | absorb | TwoSum (high, low) | carry | output |
|---|---|---|---|---|
| 0 | — | — | `1` | `[]` |
| 1 | `-(2^60−256)` | `(-(2^60−256), 1)` | `-(2^60−256)` | `[1]` |
| 2 | `2^60` | `(256, 0)` (exact) | `256` | `[1; 0]` |

Result `256 :: rev [1;0] = [256; 0; 1]`, which `compress`es to `[256; 1]` —
**not** `nonoverlap_shewchuk`. (`256` is the final cancellation residue; `1` was
committed to the output earlier; `fast_expansion_sum` never re-merges
bit-disjoint components.) This last step is not reduced in Coq because
`sort_by_abs`/`compress` use `Rcompare` (not `vm_compute`-able); the cascade
mechanics are exercised on concrete `binary64` in `B64_pathB_trace_4A.v`
(e.g. `traceC_carry_after_B2R` computes the residue `256`).

## Consequence for the pathA ∨ pathB program

`pathB_output_head_bound` (the dominance precondition O1 needs) is the same fact
in disguise: it asks the prior output head `h` to satisfy `|h| ≤ ½ulp(carry')`
where `carry' = x + C` is the *smaller* cancellation residue, while the invariant
only gives `|h| ≤ ½ulp(C)` with `ulp(carry') ≤ ulp(C)` — the wrong direction. The
trace above realises it: `carry' = 256`, `h = 1`, and `1 ≤ ½ulp(256) = 2⁻⁴⁵` is
false. So O1's head-bound is **not dischargeable** from the invariant, and O4–O8
cannot close the headline as stated.

## Recommendation

Either (a) **reclassify** the headline Tier-2 with this counterexample on file
(the honest state — the theorem as written is false); or (b) **weaken**
`strict_succ_b64`/`nonoverlap_strict` to Shewchuk's actual bit-disjoint
nonoverlapping predicate and re-aim O1–O8 at the *true* headline. Option (b) is
the larger, correct fix; the pathB bricks (#135–#137) carry over, but the
half-ulp dominance arguments (O1′, O1 head-bound) must be re-derived against the
weaker predicate.
