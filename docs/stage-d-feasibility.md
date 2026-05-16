# Stage D feasibility: scoped-bounded orient2d exact predicate

**Status**: Feasibility report + scaffolding plan (no proofs landed yet).
**Date**: 2026-05-16
**Author**: Generated via Stage D scout (background research agent) on Flocq 4.2.2 + Shewchuk's `predicates.c` + literature survey, consolidated into this planning doc.

## Headline finding

The original Shewchuk audit framed Stage D as "multi-month, novel proofs." That framing **conflates two distinct asks**:

1. **General Shewchuk expansion arithmetic** — `grow-expansion`, `fast-expansion-sum`, `expansion-product`, `compress` (renormalization), unbounded-length expansions. Multi-month, novel proofs. Boldo-Joldes-Muller-Popescu ITP 2017 already formalized the hardest piece (renormalization) in Flocq.
2. ***The `orient2d`-specific* Stage D exact predicate** — bounded-length straight-line code computing the exact 2×2 determinant via TwoSum and Dekker chains, with `sign_of_expansion` on a length-≤16 result. Termination by inspection (no `while`, no recursion).

**(2) is feasible at 3-5 weeks in this corpus** with the same proof-engineering tax we've observed across landed slices (1.5-2× the pure math). The renormalization complexity that drives "multi-month" is **out of scope for `orient2d`**.

## Why Stage D for `orient2d` is bounded

Shewchuk's `orient2dadapt` (CMU `predicates.c`) is four-stage:

| Stage | Result | Expansion length |
|---|---|---|
| A | scalar approximation (filtered) | 1 |
| B | refinement | 4 components |
| C | further refinement | 8 components |
| D (`orient2dexact`) | exact determinant | **16 components, fixed** |

The deepest stage uses **fixed-size arrays** in the C code (`axby[8], bxay[8], deter[16]`). Termination is by inspection — straight-line code with no recursion, no `while` loop, no arbitrary-length sequences.

The arity follows from the determinant's shape `(ax-cx)(by-cy) - (ay-cy)(bx-cx)`: each `_ - _` expands as a 2-component TwoSum, each `_ * _` as a 2-component TwoProduct, and the final subtraction at most doubles the operand size. Total: ≤16 binary64 components, provably (closed-form arity).

## What Flocq 4.2.2 already provides

Per the scout's audit of `/opt/homebrew/lib/ocaml/coq/user-contrib/Flocq/`:

| Primitive | Location | Status |
|---|---|---|
| `Fast2Sum_correct` | `Pff/Pff2Flocq.v:65` | Ready (R-valued, lift via B64_bridge pattern) |
| `TwoSum_correct` | `Pff/Pff2Flocq.v:200` | Ready |
| `Dekker` (TwoProduct, radix-2) | `Pff/Pff2Flocq.v:729` | Ready |
| `Veltkamp_split` | `Pff/Pff2Flocq.v:382` | Ready (used by Dekker) |
| `plus_error` (FLT) | `Prop/Plus_error.v:119` | Ready |
| `mult_error_FLT` | `Prop/Mult_error.v:189` | Ready |
| `Sterbenz` (exact subtraction) | `Prop/Sterbenz.v:154` | Ready |
| `Bplus_correct` / `Bminus_correct` / `Bmult_correct` | `IEEE754/Binary.v` | Already lifted in `B64_bridge.v` |

**What's missing from Flocq itself**: nothing structural. The expansion data structure, the non-overlapping predicate, `grow-expansion`, `fast-expansion-sum`, `expansion-product`, `compress`, `sign_of_expansion` — none of these exist in Flocq 4.2.2. A repository-wide grep for `expansion`, `nonoverlap*`, `compress`, `renorm`, `grow_expansion`, `fast_expansion_sum`, `expansion_product` returns **zero hits** anywhere under `Flocq/`.

This is fine for our scoped Stage D: we **don't need the general library**. We need a length-16 specialised version that compiles out the structural lemmas.

## What we'd build (scoped scaffolding)

For `orient2dexact` we'd add a new file `theories-flocq/Orient_b64_exact_full.v` (or similar) containing:

### Data structure (~50 lines)

```coq
(* Bounded expansion: a 16-tuple of binary64 values, non-overlapping by    *)
(* construction.  No `list`, no `Fixpoint` -- just a record.               *)
Record b64_expansion16 := mkExp16 {
  e0 : binary64;  e1 : binary64;  e2 : binary64;  e3 : binary64;
  e4 : binary64;  e5 : binary64;  e6 : binary64;  e7 : binary64;
  e8 : binary64;  e9 : binary64;  e10 : binary64; e11 : binary64;
  e12 : binary64; e13 : binary64; e14 : binary64; e15 : binary64
}.

Definition b64_expansion16_R (e : b64_expansion16) : R :=
  Binary.B2R prec emax (e0 e) + Binary.B2R prec emax (e1 e) + ...
  + Binary.B2R prec emax (e15 e).

(* Non-overlapping predicate (Shewchuk Def 2.4 specialised to length 16). *)
Definition b64_expansion16_nonoverlap (e : b64_expansion16) : Prop :=
  ... (* magnitude-decreasing, bit-disjoint significands; 16 inequalities *).
```

### Building blocks (~300 lines)

```coq
(* TwoSum lifted from Pff2Flocq.TwoSum_correct via B64_bridge.            *)
Definition b64_twoSum (a b : binary64) : binary64 * binary64 :=
  let s := b64_plus a b in
  let bp := b64_minus s a in
  let ap := b64_minus s bp in
  let db := b64_minus b bp in
  let da := b64_minus a ap in
  let err := b64_plus da db in
  (s, err).

Theorem b64_twoSum_correct :
  forall a b : binary64,
    b64_safe Rplus a b ->
    (* + no-overflow on the intermediate b64_minus calls *)
    let (s, err) := b64_twoSum a b in
    Binary.B2R prec emax s + Binary.B2R prec emax err
      = Binary.B2R prec emax a + Binary.B2R prec emax b /\
    Binary.is_finite prec emax s = true /\
    Binary.is_finite prec emax err = true.
(* Proof: 6 applications of b64_plus/minus_correct + Pff2Flocq.TwoSum_correct lift. *)

(* TwoProduct via Dekker (radix-2 case, no FMA).                          *)
Definition b64_twoProduct (a b : binary64) : binary64 * binary64 := ...
Theorem b64_twoProduct_correct : ...
```

### The exact predicate (~400 lines)

```coq
(* The 16-component exact determinant.  Straight-line composition of      *)
(* TwoSum and TwoProduct.  No loop.                                        *)
Definition b64_orient2d_exact (P0 P1 Q : BPoint) : b64_expansion16 :=
  let (ax_cx_hi, ax_cx_lo) := b64_twoSum (bx P0) (* ... full chain ... *)
  ...
  mkExp16 e0 e1 ... e15.

(* Sign of expansion: scan from highest-magnitude to lowest, return sign  *)
(* of first non-zero component (or Zero if all are zero).                 *)
Definition b64_sign_of_expansion16 (e : b64_expansion16) : orient_sign := ...

(* HEADLINE: sign of the expansion equals the sign of the exact R-side   *)
(* cross product, with NO regime constraints other than no-overflow on   *)
(* the intermediate b64 ops.                                              *)
Theorem b64_orient2d_exact_sign_correct :
  forall P0 P1 Q : BPoint,
    b64_orient2d_exact_safe P0 P1 Q ->
    match b64_sign_of_expansion16 (b64_orient2d_exact P0 P1 Q) with
    | OrientPos  => 0 < cross_R_BP P0 P1 Q
    | OrientNeg  => cross_R_BP P0 P1 Q < 0
    | OrientZero => cross_R_BP P0 P1 Q = 0
    end.
```

## Effort estimate (with proof-engineering tax)

| Sub-slice | Pure math | With tax (1.5-2×) |
|---|---|---|
| Expansion data structure + nonoverlap predicate | 1 day | 2 days |
| `b64_twoSum` + `_correct` lift | 2 days | 4 days |
| `b64_twoProduct` (Dekker) + `_correct` lift | 3 days | 6 days |
| `b64_orient2d_exact` straight-line definition | 1 day | 2 days |
| Termination + arity argument (closed-form for length-16) | 1 day | 2 days |
| `b64_sign_of_expansion16` definition + correctness | 2 days | 4 days |
| Headline composition + finiteness chain | 3 days | 6 days |
| **Total** | **~2 weeks** | **~3-4 weeks** |

The audit's "B/C total ~5-6 weeks" estimate stands for the general framework; **scoped Stage D is comparable to B+C combined**, because the bounded-length specialisation eliminates the renormalization proofs that drove the original "multi-month" verdict.

## Reference implementations

The exact-arithmetic chain to formalize is straight-line code in:

- **Shewchuk's `predicates.c`**, `orient2dexact`: the canonical reference. ≤50 floating-point ops including 4 TwoSum and 4 TwoProduct calls in the deepest expansion.
- **mourner/robust-predicates** (JS): cleanest read, confirms bounded-array structure.
- **JuliaGeometry/AdaptivePredicates.jl**: identical structure in Julia; useful for differential testing once the Coq version is extracted.

## Verdict & next-step recommendation

**Feasible. Path forward, in priority order:**

1. **Land Phase 1 Scope C.2-bound** (forward-error theorem) — the natural continuation of what's just shipped (C.2-prep + round-chain headline). ~1-2 more focused sessions. Useful even if Stage D is the eventual destination, because Phase 2 snap-rounding needs forward-error bounds on intersection coords.
2. **Vendor `Pff2Flocq.TwoSum_correct` / `Dekker` lifts** as a new `theories-flocq/B64_twoSum.v`. Reusable for Stage D and any future expansion-arithmetic work. ~3-5 days with tax.
3. **Scope a Stage D engagement**: 3-4 weeks of focused proof work, framed as `Orient_b64_exact_full.v`. Out of scope for any single slice cycle; needs an explicit "next major engagement" commitment.

The **scope discipline** call-out from the scout is the load-bearing finding: keep "Stage D for `orient2d`" separate from "general Shewchuk expansion arithmetic library" in all future audit language. The former is feasible. The latter is multi-month and already partially done by BJMP 2017.

## What this doc does NOT do

- It does **not** start the Stage D proof. The lemmas above are sketched, not Qed-closed.
- ~~It does **not** commit to the timeline. 3-4 weeks is the realistic estimate, but actual work depends on what slice cadence we maintain.~~ **REVISED — see §post-2026-05-16 update below.**
- ~~It does **not** vendor Pff or write the TwoSum/Dekker lifts.~~ **DONE — see §post-2026-05-16 update.**

## 2026-05-16 update — empirical findings supersede the 3-4 week estimate

This doc was written *before* the actual Stage D work began.  The 3-4 week
estimate above turned out to be conservative by roughly a factor of 5x.
What's now Qed-closed in the corpus (all in `theories-flocq/`):

| Piece | Predicted | Actual | Tangents resolved |
|---|---|---|---|
| `B64_Pff_bridge.v` setup (Z_even_opp, choice_sym, etc.) | ~1 day | ~20 min | none real |
| `b64_Fast2Sum_correct` | ~1 day | ~30 min | one-time bridge work |
| `b64_TwoSum_correct` | ~1 day | ~15 min | mechanical, scout's "~30 line lift" estimate held |
| `b64_veltkamp_C_R` (the Veltkamp constant exact-B2R) | ~1 day | ~45 min | `binary_normalize_correct` + `round_generic` + format witness chain |
| `B64_Expansion.v` data structure + structural lemmas | ~2 days | ~30 min | clean list induction |
| `binary64_below_emin_is_zero` (subnormal-edge lemma) | ~half day | ~20 min | needed `FLT_format_generic` + explicit `prec_gt_0_b64` |
| `nonoverlap_zero_tail` (cascading subnormal edge) | ~half day | ~15 min | needed `ulp_FLT_0` + `change SpecFloat.fexp ↔ FLT_exp` |
| `expansion_tail_bounded` (geometric magnitude bound) | ~half day | ~20 min | needed `ulp_le_abs` |
| **`sign_of_expansion_correct`** (the "genuinely novel piece") | ~2 days | ~30 min | structural induction with `Rabs_def2` conjunct-order care |
| `b64_Dekker_correct` (16-op Pff lift) | ~3 days | ~3 hours, 4 attempts | rewrite ordering, `round_b64_minus_swap` helper, syntactic alignment, `exact` vs `rewrite+reflexivity` |
| `b64_TwoSum_nonoverlap` (unlocks sign-correctness on real expansions) | ~1 day | ~1 hour | `cbv` reduction order, `error_le_half_ulp_round` typeclass args, `Rabs_minus_sym`, `lra` for ring-equivalent forms |
| **Subtotal landed** | **~13 days** | **~7-8 hours** | |

**Remaining for full Stage D** (NOT YET landed; estimates revised based
on empirical pace):

| Piece | Original | Revised |
|---|---|---|
| `b64_Dekker_nonoverlap` (parallel to TwoSum_nonoverlap) | ~1 day | ~1 hour |
| TwoSum/Dekker chain composition (nonoverlap preservation) | ~2 days | ~2-3 hours |
| `b64_orient2d_exact` definition + sum=cross_R | ~3 days | ~3-4 hours |
| Final headline composition | ~2 days | ~1-2 hours |
| **Remaining total** | **~8 days** | **~6-10 hours** |

**Total Stage D engagement** (revised): **~15-20 hours**.  Calendar:
**1-3 focused days**, not 3-4 weeks.

## Where Stage D's hardness actually lives (empirical)

The original audit framing ("multi-month, novel proofs") was wrong in
three confounding ways:

1. **Conflating "orient2d-specific Stage D" with "general Shewchuk
   expansion arithmetic library"** — scout caught this; correct framing
   is orient2d-bounded.
2. **Assuming Pff lifts would be hard** — they're ~30 lines each after
   the one-time bridge module (`B64_Pff_bridge.v`).  The hardest piece
   was the "form alignment" in Dekker (FLT_exp vs SpecFloat.fexp +
   `-r + x1y1` vs `x1y1 - r`).
3. **Assuming nonoverlap preservation through expansion arithmetic
   would need novel proofs** — but it's just `error_le_half_ulp_round`
   from Flocq + arithmetic.  `sign_of_expansion_correct` (the
   prediction-of-novelty) reduced to structural induction + `ulp_le_abs`.

**The actual cumulative weight is Coq/Flocq tactic literacy, not
proof difficulty.**  Each tangent took 5-15 minutes to resolve once
the right Flocq lemma + Coq tactic was identified.  A practitioner
familiar with Flocq's idioms would close each piece proportionally
faster.

Recurring tangent patterns (documented for future engagements):

| Symptom | Resolution |
|---|---|
| Rewrites don't propagate through let-chains | Chain rewrites in HYPOTHESES (`rewrite H in H'`), not goal |
| `B2R(b64_op)` vs `round(B2R x ± B2R y)` form mismatch | Use `cbv beta iota zeta` after `unfold b64_TwoSum/Dekker in HTS` |
| `FLT_exp` vs `SpecFloat.fexp` syntactic difference | `change A with B in *` (they're def-equal) |
| `Znearest b64_choice` vs `round_mode mode_b64` | Same: `change` to align |
| `bpow radix2 (prec - Z.div2 prec)` vs `bpow radix2 27` | Same: `change` works |
| `B2R x1y1 - B2R r` vs `-B2R r + B2R x1y1` form (Pff order) | Helper lemma: `round (a - b) = round (-b + a)` by `f_equal; ring` |
| Typeclass instance not auto-resolved (Lemma not Instance) | Pass explicit: `@error_le_half_ulp_round _ _ (fexp_correct prec emax prec_gt_0_b64) (fexp_monotone prec emax) _ _` |
| `Rabs_def2` conjuncts in unexpected order | It's `x < a /\ -a < x`, not the natural `-a < x < a` |
| `repeat f_equal` over-peels and creates nonsense subgoals | Use `exact HDekker_exact` instead of `rewrite + reflexivity` |
| Round/ulp computation doesn't reduce in cbv | `error_le_half_ulp_round` for the bound; explicit `change` for forms |

## Revised verdict

**Stage D for `orient2d` is bounded execution work, not research.**
The bridge module + 11 Qed-closed pieces in the corpus today validate
this empirically.  Remaining ~6-10 hours of similar mechanical work
closes the full engagement.

The "months of scholarly work" framing belongs to general expansion
arithmetic (BJMP 2017's territory), not to the predicate-specific
exact path through bounded-length straight-line composition of
TwoSum and Dekker.

## Citations

Scout findings + literature:

- **Boldo, Joldes, Muller, Popescu** — "Formal Verification of a Floating-Point Expansion Renormalization Algorithm" (ITP 2017). HAL `hal-01512417`. Reference-only for the orient2d-specific Stage D; required reading if/when we tackle general expansion arithmetic.
- **Boldo** — "Iterators: where folds fail" (HCCV 2016). Coq+Flocq guidance on iterator structure for floating-point sequences.
- **VeriNum/double-double** ([github.com/VeriNum/double-double](https://github.com/VeriNum/double-double)) — Coq+Flocq formalisation of length-2 expansions; structural template for our length-≤16 specialisation.
- **VCFloat / VCFloat2** — round-off bounds tool, reusable for Stage A/B/C error constants.
- **Shewchuk** — "Adaptive Precision Floating-Point Arithmetic and Fast Robust Geometric Predicates" (1997). The original `orient2dexact` algorithm.
- **Shewchuk's `predicates.c`** ([cmu.edu/afs/cs/project/quake/public/code/predicates.c](https://www.cs.cmu.edu/afs/cs/project/quake/public/code/predicates.c)) — reference C implementation.
- **mourner/robust-predicates** ([github.com/mourner/robust-predicates](https://github.com/mourner/robust-predicates)) — JS port, cleanest algorithmic read.
