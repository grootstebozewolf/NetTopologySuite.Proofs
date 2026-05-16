# Library audit: Shewchuk Stages B/C/D in Flocq 4.2.2

**Question.** To close the full Shewchuk adaptive `orient2d` (Stages B/C/D —
expansion arithmetic that refines `OrientRUncertain` from Stage A into a
definite `Pos`/`Neg`/`Zero`), what's already in our pinned Flocq, what
would need to be vendored from companion libraries, and what would need
to be reproved?

**Decision driver.** The corpus invariant (no `Admitted` / `Axiom` /
`Parameter` in `theories/` or `theories-flocq/`) makes "reuse" much
cheaper than "vendor", and "vendor" much cheaper than "reprove". We want
to walk Flocq's existing material end-to-end before committing to either
of the latter two.

---

## 1. What's in pinned Flocq (`coq-flocq.4.2.2`)

### 1.1 Foundational error theorems — `Flocq.Prop.Plus_error` and `Flocq.Prop.Mult_error`

```coq
(* Flocq/Prop/Plus_error.v, line 119 *)
Theorem plus_error :
  forall x y,
  format x -> format y ->
  format (round beta fexp (Znearest choice) (x + y) - (x + y))%R.

(* Flocq/Prop/Mult_error.v, line 140 (FLX) *)
Theorem mult_error_FLX :
  forall x y,
  format x -> format y ->
  format (round beta (FLX_exp prec) rnd (x * y) - (x * y))%R.

(* Flocq/Prop/Mult_error.v, line 189 (FLT, the binary64-relevant one) *)
Theorem mult_error_FLT : (* same shape, FLT exponent function *)
```

These say: **the rounding error of `+` and `*` is itself a representable
float**. They are the algebraic kernel of every error-free transformation
(EFT). For Shewchuk, they justify why `dx` and `dy` in TwoSum (and the
correction term in TwoProduct) are computable as a single subsequent
round without further error.

### 1.2 Møller-Knuth TwoSum — `Flocq.Pff.Pff2Flocq.TwoSum_correct`

```coq
(* Flocq/Pff/Pff2Flocq.v, line 200 *)
Let a  := round_flt (x+y).
Let x' := round_flt (a-x).
Let dx := round_flt (x - round_flt (a-x')).
Let dy := round_flt (y - x').
Let b  := round_flt (dx + dy).

Theorem TwoSum_correct: a+b=x+y.
```

This is the standard 6-op TwoSum proven on real-valued floats in `FLT`
format. **Directly reusable** for Shewchuk's Stage B expansion sums.

### 1.3 Dekker TwoProduct — `Flocq.Pff.Pff2Flocq.Dekker`

```coq
(* Flocq/Pff/Pff2Flocq.v, line 729 *)
(* algorithm: two Veltkamp splits + four products + cascading sums *)
Theorem Dekker:
  (radix_val beta = 2)%Z \/ (Z.Even prec) ->
  (x*y = 0 \/ bpow (emin + 2*prec - 1) <= Rabs (x*y) -> (x*y = r + t4)%R) /\
  (Rabs (x*y - (r+t4)) <= (7/2) * bpow emin)%R.
```

The Veltkamp/Dekker product. For binary64 (`radix=2`, `prec=53`,
`emin=-1074`), the exactness branch fires for any `|x*y| >= 2^(-969)` —
in practice always for non-subnormal inputs to `orient2d`. **Directly
reusable** as Shewchuk's `TwoProduct`.

(Modern CPUs would use the FMA version `a*b - fma(a,b,-c)` which is one
op instead of six. Flocq's FMA story is separate and not required for
the current slice; Dekker's algorithm runs without FMA.)

### 1.4 Bridge from `binary_float` to R — `Flocq.IEEE754.Binary.Bplus_correct` / `Bmult_correct`

```coq
(* Flocq/IEEE754/Binary.v, line 1052 *)
Theorem Bplus_correct :
  forall plus_nan m x y,
  is_finite x = true ->
  is_finite y = true ->
  if Rlt_bool (Rabs (round radix2 fexp (round_mode m) (B2R x + B2R y))) (bpow radix2 emax) then
    B2R (Bplus plus_nan m x y) = round ... (B2R x + B2R y) /\
    is_finite (Bplus plus_nan m x y) = true /\
    Bsign ... = ...
  else
    (B2FF (Bplus plus_nan m x y) = binary_overflow m (Bsign x) /\ ...).
```

This is the bridge that converts a `binary_float` computation into an
R-side fact. The `if Rlt_bool (Rabs ...) (bpow radix2 emax) then ... else
...` shape is exactly **the no-overflow precondition** we've been
deferring throughout the corpus. It's already a Qed-closed theorem
inside Flocq — we don't need to prove it, we need to *apply* it (and
discharge its precondition for our specific operand magnitudes).

`Bmult_correct` has the same shape.

---

## 2. What's not in Flocq (vendor or reprove)

### 2.1 FastTwoSum (Dekker's 3-op variant, `|x| >= |y|` precondition)

Not in Flocq.  Easy to prove from `plus_error`: when `|x| >= |y|` and
both are floats, `round(x+y) - (x+y) = round((x + y) - round(x+y))` and
the latter is exact.  Estimated effort: **~half day**.

### 2.2 Shewchuk's expansion-arithmetic primitives (the big gap)

Not in Flocq.  The full Shewchuk 1997 algorithm uses these on lists of
floats with a non-overlapping property:

- `grow-expansion` (Shewchuk eq. 9): insert a float into an expansion,
  maintain non-overlap.
- `fast-expansion-sum` (eq. 12): merge two non-overlapping expansions
  by sorted-merge + chained `TwoSum`.
- `expansion-product` (eq. 18): multiply an expansion by a float using
  chained `TwoProduct` + `fast-expansion-sum`.
- `compress` (eq. 16): renormalise an expansion to its canonical
  shortest form.

These need:
- A predicate `nonoverlapping_expansion : list R -> Prop` (or on
  `binary_float`) with associated structural facts (sorting, head /
  tail decomposition).
- Each algorithm as a Coq `Fixpoint`.
- Soundness theorems linking `sum_of_expansion` (the abstract R-value)
  to the operation result.

**Effort:** ~1 to 2 weeks of focused proof work for Stage B alone
(grow-expansion + fast-expansion-sum + sign-of-expansion).  Stages
C/D (expansion-product + adaptive sign) are another similar slice.

### 2.3 Sign-of-expansion

Not in Flocq.  Walking the expansion most-significant-first and
returning the sign of the first non-zero component.  ~half day on top
of expansion arithmetic.

### 2.4 The full Shewchuk adaptive `orient2d` Stages B/C/D combined

No public Coq formalisation appears to exist for the full adaptive
predicate.  Boldo and Melquiond have published work on related EFT
algorithms in Flocq; some of it may be reusable.  No turnkey vendor
target is known.

---

## 3. Bridging strategy

Pff2Flocq operates on R-valued floats in `FLT` format with `round_flt`
and `format` predicates, not on `binary_float`.  To use `TwoSum_correct`
on `BPoint`-valued binary64 inputs:

1. **Lift** each `binary64` to an R-valued float via `B2R`.
2. **Discharge the no-overflow precondition** for each `b64_plus` /
   `b64_minus` / `b64_mult` call along the expansion path, using
   `Bplus_correct` / `Bmult_correct`.
3. **Translate** the proven equality `a + b = x + y` (R-side) back to
   `B2R (b64_plus ...)` (binary64-side) via the same correctness
   theorems.
4. The R-side `format` predicates fall out of the `is_finite`
   precondition + `Generic_format_FLT` lemmas in Flocq.

The "no_overflow_precond" the user's draft mentioned is the
discharge-obligation of step 2 — and it's tractable but not trivial:
for `orient2d`, each intermediate expansion step's magnitude needs to
stay within `2^emax / safety_margin`.  A conservative precondition
like `|coord| < 2^500` is sound (gives margin for ~2^24 = ~16M
intermediate ops before risk of overflow) and easy to check at the
oracle boundary.

---

## 4. Reuse / vendor / reprove call

| Component | Action | Notes |
|---|---|---|
| `plus_error`, `mult_error_FLX/FLT` | **Reuse**, direct | Already in `Flocq.Prop.*` |
| `TwoSum` | **Reuse** `Pff2Flocq.TwoSum_correct` | Wrap in a binary64 layer via `Bplus_correct` |
| `TwoProduct` | **Reuse** `Pff2Flocq.Dekker` | Same, via `Bmult_correct` |
| Veltkamp split | **Reuse** as part of Dekker | Already proven |
| `Bplus_correct`, `Bmult_correct` | **Reuse**, direct | The bridge mechanism itself |
| FastTwoSum (`|x|≥|y|` variant) | **Reprove** from `plus_error` | ~half day, small slice |
| `nonoverlapping` predicate | **Define** from scratch | Coq Prop on `list binary64` |
| `grow-expansion` | **Define + prove** | ~2-3 days |
| `fast-expansion-sum` | **Define + prove** | ~3-4 days |
| `expansion-product` | **Define + prove** | ~2-3 days |
| `sign_of_expansion` | **Define + prove** | ~half day |
| Adaptive `orient2d` Stages B/C | **Compose** the above | ~3-5 days |
| Stage D fallback | **Skip for now** | Diminishing returns, not needed for typical NTS inputs |
| R-bridge soundness on binary64 | **Reuse** `Bplus_correct` machinery | The same machinery that closes the simplifier R-bridge |

**Total estimate for Stages B/C end-to-end:** ~3 weeks of focused
proof work, assuming the bridge mechanism (no-overflow precondition
threading) is built up as a separate reusable module rather than
reinvented for each operation.

**Critical path:** the R-bridge mechanism.  Once it exists for any one
binary64 operation (say `b64_plus`), the same pattern instantiates
trivially for every other op.  Building it cleanly the first time pays
off across the simplifier R-bridge, Stage A's arithmetic identities,
and Stages B/C of orientation — all of which are blocked on the same
piece of machinery today.

---

## 5. Recommended order of operations

1. **R-bridge module.** A new `theories-flocq/B64_bridge.v` that provides:
   - `b64_plus_correct : forall x y, is_finite x -> is_finite y -> no_overflow -> B2R (b64_plus x y) = round_flt (B2R x + B2R y)`.
   - Same for `b64_minus`, `b64_mult`.
   - The conservative `no_overflow_precond` for typical NTS magnitudes.
   - A handful of compositional helpers (e.g. "if both args fit in 2^500, their sum fits in 2^501").

2. **B64-lifted TwoSum and TwoProduct.** Wrap `Pff2Flocq.TwoSum_correct`
   and `Pff2Flocq.Dekker` through the R-bridge to get binary64 versions.

3. **Non-overlapping expansion predicate + structural lemmas.**

4. **`grow-expansion` and `fast-expansion-sum`**, then
   **`sign_of_expansion`**.  This is enough for Stage B of `orient2d`.

5. **`expansion-product`** for Stage C.

6. Assemble Stages B + C into `b64_orient2d_exact` and prove its
   soundness against the R-valued `cross` predicate.

7. Update the `RobustOrientation.SignFiltered` C# consumer to route
   `Uncertain` through the new exact path.

**At step 1's completion,** we also unlock:
- The simplifier R-bridge (`greedy_simplify_binary64_sound`).
- Stage A's arithmetic identities (antisymmetry, cyclic permutation,
  translation invariance).

So step 1 is the single highest-leverage piece of work in the corpus
today.

---

## 6. Open questions

- **`Pff` vs `Binary` abstraction gap.** `Pff2Flocq.TwoSum_correct`
  uses R-valued floats with `format` predicates.  Lifting to
  `binary_float` is via `Bplus_correct` but the composition needs
  care.  Worth a half-day spike to verify the lift goes through
  cleanly for at least one example before committing.

- **FMA-based TwoProduct.**  Modern CPUs would do `TwoProduct` in one
  FMA + one round.  Flocq has FMA via `Flocq.IEEE754.Bits` and primfloat
  but the proof story is separate.  Defer to a later slice — Dekker's
  algorithm works on every binary64-capable platform.

- **Stage D.**  Shewchuk's deepest stage requires keeping arbitrarily
  long expansions.  For typical NTS inputs (well-conditioned triangles)
  Stage C is already sufficient.  Stage D can be deferred indefinitely
  — most published implementations of "robust orient2d" stop at C.

---

## 7. 2026-05-16 update: post-bridge state and revised stance

This section amends the audit with the state of the corpus several months
on.  It supersedes §5's "next steps" framing but leaves the body of the
audit (§§1-6) intact as the original analysis.

### 7.1 What landed since the original audit

The bridge module called out in §5 step 1 (the "single highest-leverage
piece of work in the corpus today") shipped as `theories-flocq/B64_bridge.v`,
joined by `Orient_b64_R.v` and `Orient_b64_exact.v`.  That validated the
audit's critical-path read: subsequent work has been able to lift cleanly
through the bridge without reinventing the no-overflow threading.

Concretely, since the bridge landed:

- **Phase 0 Path 2** (integer-regime exactness for `b64_orient2d`):
  shipped via `Orient_b64_exact.v`.  Headline: under `coord_int_safe`
  inputs (|coord| ≤ 2^25 integers), `B2R (b64_orient2d ...) = cross_R_BP`
  on the nose.
- **Tiny-regime decisive theorem**: shipped (`b64_orient_sign_filtered_tiny_regime_decisive`).
  Under |coord| ≤ 2^22 integers, the Stage A filter is guaranteed to
  fire on every non-zero cross.
- **Phase 1 first slices**: predicate (`Intersect_b64.v`), shared-endpoint
  disambiguation, collinear-overlap completeness, and Scope A first-stage
  exactness for intersection-point coords (`Intersect_b64_exact.v` +
  `HasIntersect` typeclass).
- **Phase 2 foundations**: HotPixel R-side scaffold and binary64 mirror
  with rounded-pixel soundness (`HotPixel.v` + `HotPixel_b64.v`).
- **Phase 4 audit**: documented why native curve support is stalled in
  NTS (`Coordinate[]` data plane in `SegmentString`); chord-first
  direction confirmed through Phase 3.

### 7.2 Stages B/C/D: still the deeper-soundness path, not the next slice

The §4 estimate ("~3 weeks of focused proof work for Stages B/C
end-to-end") remains broadly accurate, but with a practical tax: the
proof-engineering overhead observed across landed slices runs at roughly
1.5–2× the pure mathematical effort.  Realistic estimate today:

| Stage | Pure math | With tax | Notes |
|---|---|---|---|
| FastTwoSum + non-overlapping predicate | ~half day | ~1 day | small slice |
| `grow-expansion` + `fast-expansion-sum` | ~5-7 days | ~2 weeks | |
| `expansion-product` + `sign-of-expansion` | ~3-4 days | ~1 week | |
| Compose into Stage B/C `orient2d_exact` | ~3-5 days | ~1.5 weeks | |
| **B/C total** | **~2 weeks** | **~5-6 weeks** | |
| Stage D | (multi-month, novel proofs) | indefinite | renormalization is the qualitative jump |

### 7.3 Revised stance: thin leading wire takes precedence

The current direction (recorded in [`audit-phase4-curves.md`](audit-phase4-curves.md)
and reflected in the `HasIntersect` typeclass in `Intersect_b64_exact.v`)
is *incremental predicate-layer enablement* rather than a multi-month
B/C engagement.  Concretely:

1. **Finish Phase 1 Scope B/C** (round-chain identity and forward-error
   bound for intersection coords).  These give callers a usable forward-
   error contract without paying for full Stages B/C/D.
2. **Phase 2 HotPixel rewriter** (snap-rounding noder) once Phase 1
   coords stabilise.  The HotPixel foundations slice is already in.
3. **First arc-arc orientation primitive** (Phase 4 first concrete piece)
   as a non-`BPoint` instance of `HasIntersect` / a parallel
   `HasOrient2d`.  Tests whether the thin-wire interface actually
   composes.

Stages B/C remain the natural deeper-soundness path and the §4 reuse
table remains accurate as a vendor/reprove call.  But they are *not*
the next slice: they would commit ~5-6 weeks to refining `OrientRUncertain`
when Phase 1's forward-error bound (Scope C, ~2-4 sessions) gives most
callers more practical value with much less effort.

**Decision**: Stages B/C/D remain queued.  Re-evaluate at the start of
Phase 3 (proper-crossing overlay) once we know whether the HotPixel
rewriter's intersection-snapping step actually needs Uncertain-case
resolution in practice — if yes, B/C jumps the queue; if no, it stays
as a documented deeper-soundness option without a fixed timeline.

---
