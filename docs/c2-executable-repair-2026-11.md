<!-- doc-kind: finding
date: 2026-11-08
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Executable realization of the conservative filter (2026-11)

Provenance: Rocq 9.2.0 + Flocq 4.2.2, local `Makefile.gen` build on branch tip
`b859b7b`. Modules: `theories-flocq/PassesThrough_b64_executable.v`,
`theories-flocq/PassesThrough_b64_executable_replay.v`.
**Outcome: REALIZATION-QED.**

## Mechanism (option a: ordinary arithmetic + proved pred/succ)

```
DN(x op y) := nextDown( x op y )     UP(x op y) := nextUp( x op y )
```
`x op y` is the round-to-nearest-even binary64 operation the oracle already
extracts (`b64_minus`, `b64_plus`, `b64_div`); nextDown/nextUp are Flocq
`Bpred`/`Bsucc` (= IEEE nextDown/nextUp; .NET `Math.BitDecrement`/`BitIncrement`).
Core fact (Flocq `pred_round_le_id`, `succ_round_ge_id`, valid for any rounding
mode): pred(round_NE z) <= z <= succ(round_NE z). Per OPERATION, not only on the
final quotient.

## Refinement theorems (all Qed)

For guarded finite operands with |exact result| <= 2^k (0 <= k <= 1000; division:
<= 2^1004, y != 0):

| claim | theorem |
|---|---|
| finite, enclosure, magnitude <= 2^(k+1) | `ex_sub_dn_ok`, `ex_sub_up_ok`, `ex_add_dn_ok`, `ex_add_up_ok` |
| finite and enclosure (division) | `ex_div_dn_ok`, `ex_div_up_ok` |
| at least as wide as Flocq mode_DN / mode_UP | `ex_sub_dn_refines_flocq`, `ex_sub_up_refines_flocq`, `ex_div_dn_refines_flocq`, `ex_div_up_refines_flocq` (exec_DN <= Flocq_DN, Flocq_UP <= exec_UP) |
| generic core | `ne_pred_ok`, `ne_succ_ok`, `ne_pred_le_dn`, `ne_succ_ge_up` |

**Equality with the Flocq term is false and is not claimed.** When the exact result
is representable, exec_DN = pred(z) < z = Flocq_DN: `ex_sub_dn_not_flocq` (1 - 0:
exec DN = 1 - 2^-53 < 1). That is why the refinement is the weak form above.

## Connection to the existing construction (one canonical proof)

Equality with Flocq's directed rounding is false (above), and wider bounds can
change the sign-selected quotient branches, so the old Flocq-specific proof could
not simply be reused. Instead the proof was made generic and the duplicate removed:

```
pure real lemmas (lowP1..upN2, ...)          PassesThrough_b64_conservative.v
   -> dprims : the ENCLOSURE CONTRACT (finite, enclosure, magnitude <= 2^(k+1))
   -> g_q_*_ok -> g_axis_*_ok -> g_touches_complete      (proved once)
        +-- flocq_prims : mode_DN / mode_UP                (same file)
        +-- exec_prims  : nearest + pred/succ              PassesThrough_b64_executable.v
```

The Flocq-mode filter is now an instance (`b64_touches_cons := g_touches
flocq_prims`); the old names (`axis_lo`, `axis_lo_ok`, `b64_touches_complete_cons`,
`b64_passes_through_complete_cons`) are thin aliases, so dependents are unchanged.
This module contains no geometry, only the executable primitives, their
refinement lemmas, and the instance. Numerators are bounded by 2^504 (each directed
step may widen by one binade; true of both instances), quotients by 2^1004; the
2^500 coordinate guard and 2^-500 denominator guard are unchanged.

## Final theorems

* `b64_touches_complete_exec`: `b64_liang_barsky_touches P0 P1 C = true ->
  b64_touches_exec P0 P1 C = true`, for every binary64 triple.
* `b64_passes_through_complete_exec`: exact `b64_passes_through_hot_pixel` ->
  `b64_passes_through_hot_pixel_exec`.

`Print Assumptions` (all of the above and the refinement theorems): only
`sig_not_dec`, `sig_forall_dec`, `functional_extensionality_dep` and
`Classical_Prop.classic`. No new axiom, no Admitted.

## Witness replay (`c2_exec_accepts_witness`)

| | value |
|---|---|
| exact t | 1/9 = 0x1.c71c71c71c71cp-4 |
| OLD (round-to-nearest) tlo_x / thi_y | 0x1.c71c71c71c71dp-4 / 0x1.c71c71c71c71cp-4 : reject |
| conservative reference (Flocq mode) lower / upper | 0x1.c71c71c71c71bp-4 / 0x1.c71c71c71c71dp-4 : accept |
| EXECUTABLE lower_x / upper_y | 0x1.c71c71c71c719p-4 / 0x1.c71c71c71c721p-4 : accept |

`c2_exec_polarity_at_witness`: executable lower <= 1/9 <= executable upper;
`c2_exec_wider_than_reference`: executable interval contains the reference one.
`b64_passes_through_hot_pixel_compute` still returns false on the witness.

## IEEE-754 edge handling

* **signed zero**: only `B2R` is used, `B2R(+-0) = 0`; nextDown(+-0) = -2^-1074 and
  nextUp(+-0) = +2^-1074 (Flocq `pred`/`succ` agree), which only widens.
* **subnormals**: `succ`/`pred` are exact on subnormals; no special case.
* **max finite / overflow**: domain |c| <= 2^500 keeps every subtraction/addition
  <= 2^503 and (with the 2^-500 denominator guard) every quotient <= 2^1004, so
  nextUp never reaches +inf.
* **infinity / NaN / |c| > 2^500**: the whole touch ACCEPTS (`b64_dom`). A NaN or
  infinite operand never reaches a directed operation.
* **positive and negative denominators**: separate formulas (inherited).

## Answers

* **Operation count** (per nondegenerate axis): 10 add/sub + 4 divisions, each
  followed by one nextUp/nextDown (14 + 14 vs the old filter's 5 add/sub + 2
  divisions); at most ~14 comparisons. Per Liang-Barsky bound: 2 divisions + 2
  nextafter + <= 3 comparisons per quotient. Same number of nearest operations as the
  Flocq-mode version; each directed op costs one extra nextafter.
* **.NET / NetTopologySuite**: plain `double` arithmetic is IEEE RNE on x64/ARM64
  (no x87 extended precision, no implicit FMA contraction); nextUp/nextDown are
  `Math.BitIncrement`/`BitDecrement` (.NET Core 3.0+, same signed-zero semantics).
  NetTopologySuite targets netstandard2.0, which lacks them: a 6-line
  `BitConverter.DoubleToInt64Bits` polyfill is needed. That polyfill and the
  OCaml extraction override for `Bpred`/`Bsucc` are NOT proved or wired here; the
  proofs cover the Flocq `Bpred`/`Bsucc` terms.
* **Branches that accept without deciding geometry**: (1) out-of-domain coordinates
  (non-finite or |c| > 2^500); (2) a quotient bound whose denominator interval
  touches 0 or lies within 2^-500 of it is "unbounded" (that bound imposes no
  constraint); (3) outward widening by up to a few ulps (false positives).

SUMMARY ok=6 warn=1 bug=0
