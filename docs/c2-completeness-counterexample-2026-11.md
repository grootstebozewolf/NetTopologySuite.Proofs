# C2 (off-grid completeness, `spec => compute`) is FALSE — QEX (2026-11)

Provenance: Rocq 9.2.0 + Flocq 4.2.2, local `Makefile.gen` build on branch tip
`17257c9` (no CI run id). Module:
`theories-flocq/PassesThrough_b64_c2_counterexample.v`
(`c2_false`, `c2_counterexample`, `c2_report_x_axis`, `c2_report_y_axis`,
`c2_ordering_fails`). Search harness: exact-Fraction spec vs IEEE-double
emulation of `PassesThrough_b64_compute.v`, then every claim re-checked in
Coq (`vm_compute` on the actual `b64_*` path; exact reals for the spec).

## Verdict

The target in `docs/oracle-soundness-finding.md`,
`forall P0 P1 C, b64_passes_through_hot_pixel P0 P1 C = true ->
b64_passes_through_hot_pixel_compute P0 P1 C = true`, is **refuted** by a
concrete binary64 witness (`c2_false`, Qed). C2 has no preconditions in its
statement; the witness uses finite, normal, |coord| < 32 inputs, so no
overflow/underflow/NaN escape applies.

## The directed lemma C2 needs, and why it is false

The final comparison is `max(0, tlo_x, tlo_y) <= min(1, thi_x, thi_y)`. The
weakest sufficient statement, for each (lower, upper) pair of t-bounds
a_L/b_L, a_U/b_U (a = c ± 1/2 - c0, b = c1 - c0): exact `a_L/b_L <= a_U/b_U`
implies `fl(ahat_L/bhat_L) <= fl(ahat_U/bhat_U)`. The case that matters is
**equality** (tangency, tlo = thi). There the two computed quotients carry
independent roundings, and nothing orders them. It is refuted at equality.

## The witness (all hex floats exact)

| | |
|---|---|
| P0 | (-0x1.ad7d2652adcf4p+1, 0x1.86d996d4a2000p+0) |
| P1 | (0x1.f57d2652adcf4p+4, -0x1.0b6ccb6a51000p+4) = -8 P0 + 9 K |
| C | (1, 0); pixel [1/2, 3/2] x [-1/2, 1/2]; K = (1/2, -1/2) its lower-left corner |

The exact line passes through K, so the closed spec touch is a single point
t = 1/9.

| quantity | x axis (lower bound tlo_x) | y axis (upper bound thi_y) |
|---|---|---|
| exact numerator a | xlo - x0 = 2170386985432893/562949953421312 | ylo - y0 = -1114221800017/549755813888 |
| exact denominator b | x1 - x0 (needs > 53 bits) | y1 - y0 = -10027996200153/549755813888 |
| exact t = a/b | **1/9** | **1/9** |
| ahat | = a (exact), 0x1.ed7d2652adcf4p+1 | = a (exact), -0x1.036ccb6a51000p+1 |
| bhat | **fl(b) != b**, 0x1.1596658e81c49p+5 | = b (exact), -0x1.23da64d79b200p+4 |
| that = b64_div ahat bhat | 0x1.c71c71c71c71d**p-4** (round-up of 1/9 + one ulp) | 0x1.c71c71c71c71c**p-4** (= fl(1/9)) |

* **Required**: tmin <= tmax, i.e. `that_x <= that_y` (both are 1/9 exactly).
* **Actual**: `that_x > that_y` by one ulp (`c2_ordering_fails`:
  `b64_compare lit_tx lit_ty = Some Gt`).
* The snapped touch is true in both spec and compute (snap P0 = (-3,2),
  snap P1 = (31,-17)), so `spec = true`, `compute = false` for the full
  passes-through predicate: the failure is exactly the original-segment touch
  (`b64_liang_barsky_touches_compute = false`).
* The mechanism: the x axis denominator was rounded before dividing
  (`bhat != b`), which moves a/b off the correctly-rounded value; the y axis
  has exact operands and returns round(1/9). Round-to-nearest gives no outward
  direction on either side.

The earlier "0 completeness violations in 18M samples" did not contain
exactly-corner-collinear off-grid segments (the 2^-50 near-tangency band
perturbs the corner rather than hitting it), which is why it never found this.
A single-pass search of 2.5M generated cases (exact corner collinearity,
P1 = (1-s) P0 + s K, s odd 3..13) found 8,758 violations of the same shape.

## Consequences

* **C2 is closed as false**, not blocked. `PassesThrough_b64_grid_separation.v`
  ("general-binary64 C2, strongly evidenced but blocked") and
  `docs/oracle-soundness-finding.md` should be read with this correction.
* The "oracle never drops a real crossing" claim is false for the sharp closed
  pixel: this segment geometrically touches the closed pixel at its corner and
  the rounded filter rejects it.
* The on-grid result (C1, `compute = spec` for |n| <= 2^22) is unaffected;
  there the operands are exact integers and the quotient is round(a/b).
* A conservative filter needs outward rounding. It is now constructed and proved
  complete in [`c2-conservative-repair-2026-11.md`](c2-conservative-repair-2026-11.md)
  (`PassesThrough_b64_conservative.v`); it accepts this witness.

SUMMARY ok=2 warn=1 bug=1
