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
- It does **not** commit to the timeline. 3-4 weeks is the realistic estimate, but actual work depends on what slice cadence we maintain.
- It does **not** vendor Pff or write the TwoSum/Dekker lifts. Those are the natural first slice if/when Stage D becomes the active engagement.

## Citations

Scout findings + literature:

- **Boldo, Joldes, Muller, Popescu** — "Formal Verification of a Floating-Point Expansion Renormalization Algorithm" (ITP 2017). HAL `hal-01512417`. Reference-only for the orient2d-specific Stage D; required reading if/when we tackle general expansion arithmetic.
- **Boldo** — "Iterators: where folds fail" (HCCV 2016). Coq+Flocq guidance on iterator structure for floating-point sequences.
- **VeriNum/double-double** ([github.com/VeriNum/double-double](https://github.com/VeriNum/double-double)) — Coq+Flocq formalisation of length-2 expansions; structural template for our length-≤16 specialisation.
- **VCFloat / VCFloat2** — round-off bounds tool, reusable for Stage A/B/C error constants.
- **Shewchuk** — "Adaptive Precision Floating-Point Arithmetic and Fast Robust Geometric Predicates" (1997). The original `orient2dexact` algorithm.
- **Shewchuk's `predicates.c`** ([cmu.edu/afs/cs/project/quake/public/code/predicates.c](https://www.cs.cmu.edu/afs/cs/project/quake/public/code/predicates.c)) — reference C implementation.
- **mourner/robust-predicates** ([github.com/mourner/robust-predicates](https://github.com/mourner/robust-predicates)) — JS port, cleanest algorithmic read.
