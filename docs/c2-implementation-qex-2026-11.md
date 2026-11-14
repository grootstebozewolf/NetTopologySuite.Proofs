<!-- doc-kind: finding
date: 2026-11-08
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# C2 at implementation level: QEX (2026-11)

Provenance: Rocq 9.2.0 + Flocq 4.2.2, local `Makefile.gen` build on branch tip
`1f8d256`. Module: `theories-flocq/PassesThrough_b64_c2_qex_record.v`.
**Outcome: QEX.** The statement
`C2 preconditions -> b64_result = exact_geometric_result` is false off the grid.

## The question as posed, answered on the actual implementation

* **Which determinant?** The C2 decision is not an orient2d sign; it compares two
  Liang-Barsky quotients, `tlo_x <= thi_y`. Cross-multiplying, the exact
  determinant is D = a_x*b_y - a_y*b_x (a = pixel lower edge - c0, b = c1 - c0).
  The implementation realises it as Dhat = that_x - that_y (two `b64_div` results
  compared by `b64_le`).
* **Forward error:** |Dhat - D| = 2^-56 (one ulp). The error bound holds and is tiny.
* **Separation:** `|D| > E` is **impossible for every E >= 0** here, because D = 0
  exactly: the segment grazes the pixel corner and the specification accepts with
  equality (tmin = tmax). Any strict-separation premise excludes the tangent case, and
  tangency is exactly where the implementation fails.
* **Sign:** sign D = 0 (Eq), sign Dhat = + (Gt); `sign Dhat = sign D` fails.

So sign stability cannot be applied: its hypothesis (`|D| > E`) is false at the
witness, and its conclusion is false too.

## The counterexample (all machine-checked)

Inputs (hex floats; `c2P0`, `c2P1`, `c2C` in
`PassesThrough_b64_c2_counterexample.v`):

| P0 | (-0x1.ad7d2652adcf4p+1, 0x1.86d996d4a2000p+0) |
|---|---|
| P1 | (0x1.f57d2652adcf4p+4, -0x1.0b6ccb6a51000p+4) |
| C | (1, 0) |

| quantity | value |
|---|---|
| D (exact) | 0 (`c2_exact_D_zero`) |
| Dhat | 2^-56 = 1/72057594037927936 (`c2_Dhat_value`) |
| |Dhat - D| | 2^-56 (`c2_forward_error`) |
| separation `|D| > E` | false for all E >= 0 (`c2_separation_impossible`) |
| exact result | `b64_passes_through_hot_pixel = true` |
| implementation result | `b64_passes_through_hot_pixel_compute = false` |

**Preconditions satisfied** (`c2_implementation_qex`): all six coordinates finite with
|c| <= 2^500 (`b64_coord_safe`, the corpus's own off-grid domain predicate);
both axes non-degenerate (c1 != c0); and genuinely off-grid, `~ coord_int_safe` on
four coordinates (`c2_witness_off_grid`; the pixel centre (1, 0) is integral).
No condition of the original C2 statement is violated, and none was weakened.

**Implication that fails:** `compute = spec` (and the weaker C2, `spec => compute`).
Corollary `c2_result_equality_false`: no equality of the two booleans holds under
`b64_coord_safe` on all six coordinates.

Reduction: the family P1 = (1-s) P0 + s K (K = lower-left pixel corner, s odd) gives
8,758 hits in 2.5M generated cases; the witness is the smallest by bit-length found
(s = 9). No further minimisation was attempted.

## Dependency chain (implementation -> error -> separation -> geometry)

1. implementation: `b64_lb_tlo`, `b64_lb_thi`, `b64_div`, `b64_le`
   (`PassesThrough_b64_compute.v`); denominator `bhat = fl(x1-x0) != b`.
2. real interpretation: `val_tx`, `val_ty`, `c2_report_*_axis` (counterexample file).
3. error: `c2_forward_error` (one ulp). Holds; not the obstruction.
4. separation: `c2_separation_impossible`. This is the obstruction (D = 0).
5. exact geometry: `b64_liang_barsky_touches` accepts at tmin = tmax = 1/9
   (`c2_spec_true`).

Where the equality DOES hold: the integer grid |n| <= 2^22
(`b64_passes_through_grid_exact`), where numerators/denominators are exact. It
holds because there the quotients are round(a/b) of exact operands, not because of a
separation gap.

`Print Assumptions` (all new theorems): `sig_forall_dec`,
`functional_extensionality_dep` (+ `sig_not_dec`, `Classical_Prop.classic` for the
theorems that import Flocq's real-number layer). No new axiom, no Admitted.

SUMMARY ok=3 warn=0 bug=1
