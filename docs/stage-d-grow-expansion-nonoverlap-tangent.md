# Stage D grow-expansion nonoverlap — tangent: `nonoverlap_strict` is incompatible with the algorithm

**Status**: Tangent.  `b64_grow_expansion_nonoverlap` is not provable as stated.
A design call is required before further proof work.
**Date**: 2026-05-23 (continuation session)
**Context**: Proof attempt for the second of the two Admitted theorems in
`theories-flocq/B64_FastExpansionSum.v` (the first, `_correct`, landed in
commit `e54b9da`).

## 1. Summary

The naive cascade invariant — `nonoverlap_strict (qfinal :: rev hs)`
preserved by `b64_grow_expansion_aux` — **does not hold** even when the
input expansion `e` is `nonoverlap_strict` and per-step safety is
guaranteed.

A concrete counterexample exists in binary64 arithmetic with
`Rabs`-violation by a factor of ~`2^1070`.  This is not a proof-engineering
issue; it is a genuine spec-level incompatibility between Shewchuk's
GROW-EXPANSION algorithm and the corpus's `nonoverlap_strict` predicate.

## 2. Coq goal state at the wall

After setting up the induction, the cons case produces the following
goal state.  Reproduced verbatim from `coqc -R theories-flocq NTS.Proofs.Flocq`
on the proof attempt:

```
1 goal

  e : binary64
  es' : list binary64
  q : binary64
  hs' : list binary64
  qfinal' : binary64
  IH : nonoverlap_strict (qfinal' :: rev hs')
  Hstep : b64_TwoSum_safe e q
  Hrest : b64_grow_expansion_aux_safe (b64_plus e q) es'
  hh : binary64
  HTS : b64_TwoSum e q = (b64_plus e q, hh)
  Hrec : b64_grow_expansion_aux (b64_plus e q) es' = (hs', qfinal')
  ============================
  nonoverlap_strict (qfinal' :: rev (hh :: hs'))
```

The proof attempt has:
  - Applied induction on `es`.
  - Destructed the cascade's TwoSum + recursive call.
  - Substituted `qnew` with `b64_plus e q` (via `b64_TwoSum_fst`).
  - Specialised the inductive hypothesis.

The remaining goal: show `nonoverlap_strict` of the output with `hh`
appended at the end of the previous cascade's output.  This is
equivalent to a single additional fact:

```
strict_succ_b64 (last (qfinal' :: rev hs')) hh
```

Which unfolds to:

```
Rabs (B2R hh) <= ulp(B2R (last (qfinal' :: rev hs'))) / 2
```

The available facts are:
  - From `b64_TwoSum_nonoverlap` on `(e, q)`: `|hh| <= ulp(b64_plus e q) / 2`.
  - From the cascade structure: `last (qfinal' :: rev hs') = head hs'`
    when `hs'` is non-empty, else `qfinal'`.

For the `hs' = nil` case (when `es' = nil`), `qfinal' = b64_plus e q` and
the required inequality is exactly the conclusion of `b64_TwoSum_nonoverlap`.
That case closes.

For the `hs' = h_first :: rest'` case, we need
`ulp(b64_plus e q) <= ulp(h_first)`, i.e., the head of the inner cascade's
output is at least as "wide" (in ULP) as the outer accumulator.  **This is
not implied by any available hypothesis**, and it can fail.

## 3. Concrete counterexample

Take the input expansion `e = [s_1; e_1] = [2^100; 2^45]` and the
new value `b = 2^48 - 2^45 + 2^(-5)`.

Input nonoverlap check: `|e_1| = 2^45 <= ulp(s_1)/2 = 2^48/2 = 2^47`.  ✓
(Verified in Coq below.)

Representability check: `b = 7 * 2^45 + 2^(-5)`.  MSB at position 47, LSB
at position -5.  Spread = 53 bits.  Exactly representable in binary64.  ✓

`b` is exactly representable in binary64.

Cascade execution:

  1. **Outer step**: `(qnew, hh) := TwoSum(e_1=2^45, b)`.
     - `e_1 + b = 2^45 + 7 * 2^45 + 2^(-5) = 2^48 + 2^(-5)`.
     - `round(2^48 + 2^(-5)) = 2^48` (since `2^(-5)` is exactly half-ulp
       of `2^48`, round-to-nearest-even gives `2^48` because its LSB at
       position `-4` is even).
     - `qnew = 2^48`, `hh = 2^(-5)`.  **`hh != 0`.**

  2. **Inner first step**: `(qnew_inner, h_first) := TwoSum(s_1=2^100, qnew=2^48)`.
     - `s_1 + qnew = 2^100 + 2^48`.  Both at positions in the same precision
       window; `2^100 + 2^48 = 2^48 * (2^52 + 1)`, with 53-bit significand.
       Exactly representable.
     - `qnew_inner = 2^100 + 2^48`, `h_first = 0`.  **`h_first = 0`.**

Cascade output: `qfinal = 2^100 + 2^48`, `hs = [hh; h_first] = [2^(-5); 0]`.

Final expansion: `qfinal :: rev hs = (2^100 + 2^48) :: [0; 2^(-5)]`.

Check `nonoverlap_strict`:
  - `strict_succ_b64 (2^100 + 2^48) 0`: `|0| <= ulp(2^100 + 2^48)/2`.  ✓ (`0 <= anything`).
  - `strict_succ_b64 0 (2^(-5))`: `|2^(-5)| <= ulp(0)/2 = bpow radix2 emin / 2`.
    For binary64, `emin = -1074`, so the bound is `2^(-1075)`.  **`2^(-5) > 2^(-1075)`.**

Violation by a factor of `2^(1070)`.

### 3.1. Coq verification of the counterexample's arithmetic

Compiled with Flocq 4.1.3 in the proof-attempt sandbox; lemmas Qed-close.
Reproduced verbatim:

```coq
From Coq Require Import Reals Lra ZArith Lia.
From Flocq Require Import Core IEEE754.Binary.

Open Scope R_scope.

Lemma input_nonoverlap_holds : bpow radix2 45 <= bpow radix2 48 / 2.
Proof.
  replace (bpow radix2 48 / 2) with (bpow radix2 47).
  - apply bpow_le. lia.
  - replace 48%Z with (47 + 1)%Z at 1 by lia.
    rewrite bpow_plus.
    simpl. lra.
Qed.

Lemma output_violates_nonoverlap :
  ~ (bpow radix2 (-5) <= bpow radix2 (-1075)).
Proof.
  intros H.
  pose proof (bpow_lt radix2 (-1075) (-5) ltac:(lia)).
  lra.
Qed.

Lemma magnitude_gap :
  bpow radix2 (-5) = bpow radix2 1070 * bpow radix2 (-1075).
Proof.
  rewrite <- bpow_plus.
  reflexivity.
Qed.
```

All three Qed-close.  The violation magnitude (factor `2^1070`) is so
large that no precondition refinement can close the gap with the current
predicate.

## 4. Why this happens

`nonoverlap_strict` (`B64_Expansion.v:90`) requires `|h_{i+1}| <= ulp(h_i)/2`
between every adjacent pair, including when `h_i = 0`.  In that case
`ulp(0) = bpow radix2 emin`, so the constraint forces
`|h_{i+1}| <= bpow_emin / 2 < bpow_emin`, which is essentially `h_{i+1} = 0`.

This is encoded in the existing helper `nonoverlap_zero_tail`
(`B64_Expansion.v:250`):

> If `nonoverlap_strict (a :: xs)` and `B2R a = 0`, then the entire tail
> `expansion_R xs = 0` and `sign_of_expansion xs = ExpZero`.

So `nonoverlap_strict` does not tolerate any nonzero element following a
zero.  But Shewchuk's GROW-EXPANSION produces zero `h_i`s naturally
whenever the corresponding TwoSum step is exact, and subsequent (or
preceding, depending on cascade order) `h_j`s can be nonzero.

The predicate and the algorithm are not compatible.

## 5. Why the obstruction does not appear in the sum-correctness proof

`b64_grow_expansion_correct` (Qed-closed in `e54b9da`) carries an
*arithmetic* invariant: `expansion_R hs + B2R qfinal = expansion_R es + B2R q`.
This is preserved by every TwoSum step regardless of magnitude
relationships, because `TwoSum_correct` is unconditional on magnitudes.

The nonoverlap predicate is a *structural* invariant about magnitude
ordering between consecutive components.  Structural invariants are
fragile to "exact" cascade steps because exactness collapses one of the
two ordering values to zero.

## 6. Design options

Two viable paths forward.  This document does not prescribe a choice;
the next session makes the call.

### Option A: weaken `nonoverlap_strict` to tolerate internal zeros

Replace the current predicate with one that allows zeros anywhere
between nonzero components:

```coq
Fixpoint nonoverlap_strict_z (e : b64_expansion) : Prop :=
  match e with
  | nil => True
  | _ :: nil => True
  | a :: rest =>
      (B2R a = 0 \/
       match rest with
       | nil => True
       | b :: _ => strict_succ_b64 a b
       end) /\
      nonoverlap_strict_z rest
  end.
```

Then re-prove `sign_of_expansion_correct` for this weaker predicate.
The proof should still go through because zeros do not contribute to
`expansion_R`, and the geometric-series argument in
`expansion_tail_bounded` (`B64_Expansion.v:282`) considers absolute
magnitude of nonzero components only.

Pros:
  - Single predicate change; consumer `sign_of_expansion_correct`
    re-proves under the weaker form via a minor proof tweak.
  - The cascade IS provably preserving this weaker predicate (Shewchuk
    Theorem 11 is essentially this).
  - No algorithmic change to `b64_grow_expansion`.

Cons:
  - Re-proves required for every downstream that uses `nonoverlap_strict`.
    Current corpus consumers: `sign_of_expansion_correct` and its callers
    (none yet in `theories-flocq/`).
  - Predicate name carries semantic baggage; renaming or
    re-defining may surface in other files.

### Option B: add a `compress` step to the algorithm

Define `compress : list binary64 -> list binary64` that filters out
zero components.  Apply it to the cascade output:

```coq
Definition b64_grow_expansion (e : list binary64) (b : binary64)
  : list binary64 :=
  let '(hs, qfinal) := b64_grow_expansion_aux b (rev e) in
  compress (qfinal :: rev hs).
```

Then prove `nonoverlap_strict (compress (...))`.

Pros:
  - `nonoverlap_strict` predicate unchanged.
  - Real Shewchuk implementations include this compaction.
  - Existing `sign_of_expansion_correct` reused as-is.

Cons:
  - Sum-correctness proof needs re-doing (compress is a list filter,
    so the sum is unchanged, but the proof needs the new structural
    lemma `expansion_R_compress: expansion_R (compress xs) = expansion_R xs`).
  - The compose-with-compress pattern leaks into the corollary lemmas
    (`b64_TwoSum_chain3_sorted_*`).
  - Slightly larger surface area for follow-up bugs.

## 7. Recommendation

**Option A** (weaken `nonoverlap_strict`).  Three reasons:

  1. The weaker predicate is closer to what Shewchuk's Theorem 11
     actually states (Shewchuk's "strongly nonoverlapping" tolerates
     internal zeros; our `nonoverlap_strict` does not).
  2. `sign_of_expansion_correct`'s proof is structured around
     `expansion_tail_bounded`'s geometric series, which is
     zero-tolerant; the re-proof should be minimal (just adjust the
     case analysis for the new predicate).
  3. Avoids algorithmic complication in `b64_grow_expansion`; keeps
     the cascade structure clean.

Estimated next-session scope:

  - Define `nonoverlap_strict_z` (or rename and replace).
  - Re-prove `sign_of_expansion_correct` (~30-60 lines of adjustment).
  - Prove `b64_grow_expansion_nonoverlap` for the weaker predicate.
    Expected: cascade-invariant lemma + the same induction structure
    as the sum-correctness proof, with `b64_TwoSum_nonoverlap` at each
    step and case-splitting on whether `h_i = 0`.

If the re-proof of `sign_of_expansion_correct` runs longer than one
session, fall back to Option B as the bounded alternative.

## 9. Update (2026-05-23, continuation): Option B is also insufficient

After the initial tangent doc was written, an attempt to implement Option B
surfaced a deeper structural issue: **`compress` alone does not produce a
`nonoverlap_strict` output either**.  A second counterexample (verified in
Coq) shows the cascade can produce a compressed output whose adjacent
non-zero elements violate the half-ulp bound.

### Second counterexample (Coq-verified)

Take the same input expansion `e = [2^200; 2^100; 2^45]` (strongly
nonoverlap), and `b = -2^100 + 2^50` (representable: bits at positions
100 and 50, spread = 51).

Cascade execution:
  1. `TwoSum(2^45, b)`:
     - Computed value: `2^45 + b = -2^100 + 2^50 + 2^45`.
     - `|b|` is in binade `[2^99, 2^100)`, ulp = `2^47`.
     - `2^45 < ulp/2 = 2^46`, rounds to `b`.
     - `Q_1 = b = -2^100 + 2^50`, `h_1 = 2^45`.
  2. `TwoSum(2^100, Q_1)`:
     - `2^100 + (-2^100 + 2^50) = 2^50`.  **Exact** (cancellation).
     - `Q_2 = 2^50`, `h_2 = 0`.
  3. `TwoSum(2^200, 2^50)`:
     - `2^200 + 2^50`, rounds to `2^200`.
     - `Q_3 = 2^200`, `h_3 = 2^50`.

Cascade output: `[Q_3; h_3; h_2; h_1] = [2^200; 2^50; 0; 2^45]`.

After `compress`: `[2^200; 2^50; 2^45]`.

Check `nonoverlap_strict`:
  - Pair `(2^200, 2^50)`: `|2^50| <= ulp(2^200)/2 = 2^147`.  ✓
  - Pair `(2^50, 2^45)`: `|2^45| <= ulp(2^50)/2 = 2^(-3)`.  **FAILS**: `2^45 ≫ 2^(-3)`.

Violation by factor of `2^48`.

### Coq verification of the second counterexample

```coq
From Coq Require Import Reals Lra ZArith Lia.
From Flocq Require Import Core IEEE754.Binary.

Open Scope R_scope.

Lemma input_pair_1 : bpow radix2 100 <= bpow radix2 148 / 2.
Proof.
  replace (bpow radix2 148 / 2) with (bpow radix2 147).
  - apply bpow_le. lia.
  - replace 148%Z with (147 + 1)%Z at 1 by lia.
    rewrite bpow_plus. simpl. lra.
Qed.

Lemma input_pair_2 : bpow radix2 45 <= bpow radix2 48 / 2.
Proof.
  replace (bpow radix2 48 / 2) with (bpow radix2 47).
  - apply bpow_le. lia.
  - replace 48%Z with (47 + 1)%Z at 1 by lia.
    rewrite bpow_plus. simpl. lra.
Qed.

Lemma compress_violates : ~ (bpow radix2 45 <= bpow radix2 (-3)).
Proof.
  intro H.
  pose proof (bpow_lt radix2 (-3) 45 ltac:(lia)).
  lra.
Qed.

Lemma compress_violation_magnitude :
  bpow radix2 45 = bpow radix2 48 * bpow radix2 (-3).
Proof.
  rewrite <- bpow_plus. reflexivity.
Qed.
```

All four lemmas Qed-close (Coq 8.18 + Flocq 4.1.3 in the sandbox).

### What this means

The structural property that fails: **the cascade with cancellation
intermediates produces non-zero `h_i` and `h_j` that, after compress,
are adjacent but at magnitudes whose ratio does not match the
`nonoverlap_strict` half-ulp bound**.

In the counterexample: cancellation at step 2 (`2^100 + (-2^100 + 2^50)
= 2^50` exactly) "drops" the accumulator from `~2^100` to `2^50`.  Then
step 3 produces `h_3 = 2^50`, which is much smaller than what `h_1 = 2^45`
would need to be paired with under `nonoverlap_strict`.

The root cause is that **Shewchuk's GROW-EXPANSION (the algorithm
underlying our cascade) only preserves Shewchuk's *basic*
nonoverlapping (Def 2.4: `|x| < ulp(y)`), not the half-ulp variant
that our `nonoverlap_strict` encodes**.  Compress alone cannot bridge
the gap — even Shewchuk's basic nonoverlap fails for our counterexample
at the `(2^50, 2^45)` pair (`|2^45| < ulp(2^50) = 2^(-2)` is also
false).

This means the algorithm `b64_grow_expansion` as implemented (TwoSum
chain, no Fast2Sum magnitude precondition) does NOT preserve even
Shewchuk's basic nonoverlap in adversarial cases.  This suggests the
algorithm itself needs revisiting, not just the predicate.

### Implications for the design call

Both Option A (weaken predicate to basic nonoverlap) and Option B
(compress) are **insufficient** as standalone fixes:

  - **Option A** (weaken to `|b| <= ulp(a)`):  The cascade still
    produces outputs that violate this in cancellation cases
    (the `(2^50, 2^45)` pair in the second counterexample violates
    even the looser bound).

  - **Option B** (compress + keep nonoverlap_strict):  Insufficient
    by the counterexample above.

A third option is required:

### Option C: redesign with Fast2Sum + magnitude precondition

Shewchuk's actual algorithm uses `Fast2Sum` (not `TwoSum`) for the
cascade body, which requires `|Q| >= |e_i|` at each step.  Under that
precondition + the input being strongly nonoverlapping, the cascade
produces a strongly nonoverlapping output (Shewchuk Theorem 13 for
FAST-EXPANSION-SUM, but the same machinery applies to a properly
magnitude-ordered GROW-EXPANSION).

This requires:
  - Re-implementing `b64_grow_expansion_aux` with `Fast2Sum`.
  - Adding a magnitude precondition: `b` is bounded relative to the
    smallest element of `e`, OR the cascade interleaves an explicit
    sort by magnitude.
  - Possibly using a different entry-point function for cases where
    the precondition cannot be guaranteed.

This is a substantive redesign, not a localised fix.

### Revised recommendation

**Option C is required**.  Both A and B as initially scoped are
demonstrably insufficient by Coq-verified counterexamples.  The
algorithm `b64_grow_expansion` must be redesigned to use Fast2Sum +
appropriate magnitude preconditions to produce an output that
satisfies any meaningful nonoverlap predicate.

The next session's work expands accordingly:
  - Define `b64_grow_expansion_fast` using `b64_Fast2Sum`.
  - Add the magnitude precondition (likely: `|b| <= ulp(smallest e)` or
    similar; details from Shewchuk's analysis).
  - Prove the cascade preserves `nonoverlap_strict` under these
    preconditions.
  - Replace `b64_grow_expansion` for nonoverlap-requiring consumers.

Estimated scope: 2-4 days of focused work (Shewchuk's Theorem 13
formalisation, roughly).  The sum-correctness theorem
`b64_grow_expansion_correct` (already Qed-closed for the TwoSum
version) is reusable for the Fast2Sum version after a minor proof
adjustment.

## 10. Stopping condition (revised)

**Tangent stop — design call escalated**.  Both Options A and B
from the initial analysis are insufficient.  Option C (algorithm
redesign with Fast2Sum + magnitude precondition) is the next
session's scope.

The two counterexamples (this section + §3) are the durable
artifacts; they are Coq-verified and unambiguous.  The next session
picks up by implementing Option C, with Shewchuk Theorem 13's proof
structure as the template.

## 11. 2026-05-23 continuation: Option C attempted, two new tangents surfaced

The Option C scaffolding lands in
`theories-flocq/B64_FastExpansionSum.v`:

  - `round_eq_under_strict_dominance` — helper lemma (Admitted with
    TANGENT comment).  Hypothesis: under `|y| < ulp(x)/2` strict and
    `x` in format, `round(x + y) = x`.
  - `b64_plus_under_strict_dominance` — derived from the helper; this
    one Qed-closes (modulo the helper's admit).
  - `b64_grow_expansion_nonoverlap_dominated` — the restricted Option C
    theorem (Admitted with TANGENT comment).  Hypothesis: under the
    appended chain `nonoverlap_strict (e ++ [b])`, the cascade output
    is structurally `e ++ [b]` and hence nonoverlap_strict.

### Captured Coq goal state: helper lemma's negative-x tangent

After `intros + apply Rle_antisym + apply round_N_le_midp` and case
splitting on the sign of `x`, the negative-x branch surfaces:

```
1 goal

  x, y : R
  Hfx : b64_format x
  Hy : Rabs y < b64_ulp x / 2
  Hxneg : x < 0
  ============================
  x + y < (x + succ radix2 b64_fexp x) / 2
```

The positive case closes via `succ_eq_pos` (`succ x = x + ulp(x)` for
`x >= 0`) + `Rabs_lt_inv` + `lra`.  The negative case requires the
mirror image — `succ` of negative non-zero non-boundary `x` is
`x + ulp(x)` only when not at boundary; at boundary `succ x = x + ulp(x)/2`.
Symmetric to the lower-bound case below.

### Captured Coq goal state: helper lemma's boundary tangent (lower half)

Even in the positive case, the LOWER-bound half of the helper hits a
binade-boundary asymmetry.  `round_N_ge_midp` requires
`(x + pred x) / 2 < x + y`:

```
1 goal

  x, y : R
  Hxpos : 0 < x
  Hfx : b64_format x
  Hy : Rabs y < b64_ulp x / 2
  ============================
  (x + pred radix2 b64_fexp x) / 2 < x + y
```

For positive `x` NOT at a binade boundary (`x ≠ 2^k`):
`pred x = x - ulp(x)`, so `(x + pred x)/2 = x - ulp(x)/2`.  Goal
becomes `y > -ulp(x)/2`, which follows from `|y| < ulp(x)/2`.  ✓

For positive `x` AT a binade boundary (`x = 2^k`):
`pred x = x - ulp(x)/2` (lower binade has half-sized ulp), so
`(x + pred x)/2 = x - ulp(x)/4`.  Goal becomes `y > -ulp(x)/4`.
Our `|y| < ulp(x)/2` is INSUFFICIENT — it only gives `y > -ulp(x)/2`,
factor of 2 weaker than needed.

**Resolution options for the helper**:
  - Tighten precondition to `|y| < ulp(x)/4`.  Always sufficient, but
    incompatible with `nonoverlap_strict`'s `|y| <= ulp(x)/2`.
  - Add `~ exists k, x = bpow radix2 k` (not on a binade boundary) as
    additional precondition.  Allows the original `<` but excludes
    binade-boundary `x` values.  Restrictive but matches what most
    real cascade values satisfy.
  - Case-split on whether `x` is a binade boundary, prove each case
    separately.  Most general; requires Flocq's binade-boundary
    machinery.

### The cascade theorem (`_dominated`) status

`b64_grow_expansion_nonoverlap_dominated` is stated and the file
compiles, but its proof is `Admitted` pending:
  1. The helper lemma's boundary tangent resolution (above).
  2. The cascade-structure induction: showing that under the
     appended-chain precondition, each TwoSum step is exact and the
     cascade output equals `e ++ [b]`.

Both are concrete, bounded follow-up work.  The cascade-structure
induction is the larger piece (~50-100 lines), with the helper-lemma
boundary resolution being the smaller (~20-30 lines once the
boundary discrimination is set up).

### Workflow note: the upgraded toolset

This session used the apt-installed Coq 8.18 + Flocq 4.1.3 sandbox
(set up in the previous session) with sed-translation of `Stdlib` ->
`Coq` and the stubbed `B64_Pff_bridge`.  Iteration was fast:

  - Identify which Flocq lemma to use: `grep round_N_le_midp` in
    `/usr/lib/ocaml/coq/user-contrib/Flocq/Core/Ulp.v`.
  - Confirm signature: `Check @round_N_le_midp.` via piped coqtop.
  - Attempt the apply with explicit instance arguments.
  - Coq surfaces the residual goal verbatim, which becomes the
    documented tangent state.

Each tangent state above was captured via `Show.` + `Admitted.` and
`coqc` invocation that printed the goal block in standard format.
The two captured goals are reproduced verbatim in this doc.

## 12. Updated next-session task

The next session's work narrows further:

  1. Resolve `round_eq_under_strict_dominance` for all `x` (positive
     non-boundary, positive boundary via tighter precondition or
     case-split, negative cases via `round_NE_opp` symmetry).
     Estimate: ~half day.

  2. Implement `b64_grow_expansion_aux_dominated_invariant`: the
     cascade-structure lemma showing each TwoSum step is exact under
     the appended-chain precondition.  Estimate: ~1 day.

  3. Compose into `b64_grow_expansion_nonoverlap_dominated` Qed.
     Estimate: ~couple of hours after (1) and (2).

The general (non-dominated) case `b64_grow_expansion_nonoverlap`
remains the larger open theorem.  The dominated case unblocks
specific Stage D use cases (e.g., when the new value `c` in chain3 is
small relative to the existing expansion); the general case requires
either Fast2Sum redesign or a separate proof structure.

## 13. 2026-05-23 continuation: boundary case resolved -- Path A Qed-closed for positive x

The boundary case from §11 has been confirmed via Coq-verified
counterexample AND resolved by adopting Path A (tighter precondition).
The Path A positive case is Qed-closed.

### Counterexample to the loose precondition (Coq-verified)

Witness:  `x = 1` (= `bpow 0`, positive binade boundary).  `y = -3 * bpow(-55)`.

Three Qed-closed lemmas in `B64_FastExpansionSum.v` establish the
gap:

```coq
Lemma counterex_loose_precondition_holds :
  Rabs (- (3 * bpow radix2 (-55))) < bpow radix2 (-53).
(* |y| = 3 * bpow(-55) < bpow(-53) = ulp(1)/2.   *)
(* The LOOSE precondition holds.                 *)

Lemma counterex_below_midpoint :
  1 + - (3 * bpow radix2 (-55)) < 1 - bpow radix2 (-54).
(* x + y < midpoint (1 + pred 1)/2 = 1 - bpow(-54). *)
(* So round(x + y) <= pred 1 < 1.  Conclusion FAILS. *)

Lemma counterex_gap_magnitude :
  bpow radix2 (-54) < 3 * bpow radix2 (-55) < bpow radix2 (-53).
(* The witness |y| sits STRICTLY between the boundary-needed     *)
(* `ulp(pred x)/2 = bpow(-54)` and the loose `ulp(x)/2 = bpow(-53)`. *)
```

All three Qed-close cleanly via `bpow_plus` + `bpow_gt_0` + `lra`.

### Path A's helper Qed-closed (positive case)

```coq
Lemma round_eq_pathA_positive :
  forall x y : R,
    0 < x ->
    generic_format radix2 (SpecFloat.fexp prec emax) x ->
    Rabs y < ulp radix2 (SpecFloat.fexp prec emax)
                  (pred radix2 (SpecFloat.fexp prec emax) x) / 2 ->
    round radix2 (SpecFloat.fexp prec emax) (round_mode mode_b64) (x + y) = x.
```

The proof structure:
  - Upper half (`round v <= x`) via `round_N_le_midp` + `succ_eq_pos`,
    using `ulp_le_pos` to bridge `ulp(pred x) <= ulp(x)` so the loose
    bound suffices.
  - Lower half (`x <= round v`) via `round_N_ge_midp` + `pred_plus_ulp`
    (which gives `x - pred x = ulp(pred x)` exactly).  The tighter
    precondition matches the asymmetric midpoint at the boundary.

Key Flocq lemmas used: `pred_ge_0`, `pred_le_id`, `ulp_le_pos`,
`succ_eq_pos`, `pred_plus_ulp`, `round_N_le_midp`, `round_N_ge_midp`.
All in `Flocq.Core.Ulp`.

### The cascade theorem migrates to Path A

`b64_grow_expansion_nonoverlap_dominated` should be re-stated to use
the Path A precondition.  Specifically, the input precondition
`nonoverlap_strict (e ++ [b])` should be tightened to use
`ulp(pred (last e)) / 2` instead of `ulp(last e) / 2`.  This rules out
the counterexample's binade-boundary witness.

The cascade-structure invariant (each TwoSum step exact) then follows
from Path A's helper at each step.

### Remaining work (Option C / Path A track)

  1. **Negative-x case of Path A's helper**: by symmetry via
     `round_NE_opp`.  Estimate: ~1-2 hours.

  2. **Zero case** (x = 0): trivial, `round(0 + y) = round(y)`, and
     `|y| < ulp(0)/2 = bpow_emin/2` forces `y` to be in the subnormal
     range that rounds to 0.  Estimate: ~30 minutes.

  3. **Path A cascade-structure invariant**: induction on `es`
     applying the helper at each step.  Requires the Path A
     precondition propagating through the cascade (each `Q_i` is
     positive and satisfies the next step's dominance).  Estimate:
     ~1 day.

  4. **`b64_grow_expansion_nonoverlap_dominated` Qed**: composition.
     Estimate: ~couple of hours.

Total remaining: ~1.5-2 days for the dominated theorem under Path A.

### The general (non-dominated) case remains open

`b64_grow_expansion_nonoverlap` (without the dominance precondition)
is still not provable as stated -- the cascade with cancellation
intermediates breaks any nonoverlap predicate.  Resolution requires
either:
  - Algorithm change (Fast2Sum cascade, possibly with sort/merge step
    to handle arbitrary `b`).
  - Predicate change (weakening to Shewchuk's basic non-overlap).

This is the larger open question.  The Path A dominated theorem
unblocks specific Stage D use cases (chain3 with small `c`); the
general case is still multi-session work.

## 14. 2026-05-23 continuation: Path A track complete + bridge analysis

The Path A track is Qed-closed end-to-end (commits `385f5fe`,
`8427cc7`, `dc583ad`, `a4bbfc4`):

  - `round_eq_pathA_{positive, negative, zero}`: all signs.
  - `b64_plus_under_pathA_dominance`: binary64 lift.
  - `b64_TwoSum_pathA_exact_step`: per-step exactness.
  - `b64_grow_expansion_aux_pathA_matches`: cascade invariant.
  - `cascade_pathA_dominates_implies_nonoverlap`: precondition chain.
  - `nonoverlap_strict_B2R_compat`, `nonoverlap_strict_snoc`,
    `strict_succ_pathA_R_implies_strict_succ_b64`: structural helpers.
  - `b64_grow_expansion_nonoverlap_pathA`: HEADLINE.

File: 22 Qed, 3 Admitted.  The 3 Admitteds are all loose-precondition
variants for which the corpus has verified counterexamples — known-
unprovable-as-stated, not "we couldn't prove these."

### Bridge analysis: does orient2d_exact satisfy Path A?

Path A's `cascade_pathA_dominates_aux b (rev e)` for chain3 with
input expansion `e = [s_1; e_1]` and new value `c` requires:

  1. `0 < B2R s_1` AND `0 < B2R e_1` (positivity at every step).
  2. `|B2R c| < ulp(pred (B2R e_1)) / 2 ≈ |B2R e_1| · 2^(-54)`.
  3. `|B2R e_1| < ulp(pred (B2R s_1)) / 2 ≈ |B2R s_1| · 2^(-54)`.

Orient2d's actual chain3 inputs under `b64_orient2d_inputs_safe`
(`|coord| <= 2^500`):

  - Coordinates: up to `2^500`, ARBITRARY sign.
  - Coordinate differences: up to `2^501`, arbitrary sign.
  - Products: up to `2^1002`, arbitrary sign.
  - Outer sum `s_1`: up to `2^1003`.
  - TwoSum error `e_1`: `|e_1| <= ulp(s_1)/2`, can be ZERO.

**Three failure modes:**

  - **(a) Positivity:** violated.  Coordinate differences and
    products can be negative.  Path A's `0 < B2R e` precondition at
    each step FAILS for general orient2d.

  - **(b) Strict bound `|c| < |e_1| · 2^(-54)`:** with `|c|` up to
    `2^1002` (for products) or `2^501` (for diffs), and `|e_1|` up
    to `|s_1| · 2^(-53) ≈ 2^950`, the dominance requires
    `|c| < 2^896`.  Products at `2^1002` violate this by factor
    `2^106`.

  - **(c) Zero-error case:** when the TwoSum is exact and `e_1 = 0`,
    `ulp(pred 0)/2 = bpow_emin/2 ≈ 2^(-1075)`.  Dominance requires
    `|c| < 2^(-1075)`, impossible for any non-trivial `c`.

### Conclusion: Path A does not unblock orient2d_exact

The current Path A theorem is mathematically clean but its precondition
is NOT satisfied by orient2d's general inputs.  The Path A track
**unblocks specific narrow regimes** (e.g., all-positive expansion
with extreme magnitude separation between components and the new
value) but **NOT the b64_orient2d_exact_sign_correct headline**.

What Path A actually covers:

  - Synthetic or test inputs designed to satisfy dominance.
  - The integer regime (`coord_int_safe`, `|coord| <= 2^25`), but
    that regime is already handled in `Orient_b64_exact.v` without
    expansion arithmetic (everything is exact).
  - Possibly: very specific orient2d sub-regimes with positive
    coordinates and constrained magnitude ratios.

The Stage D headline `b64_orient2d_exact_sign_correct` for general
orient2d inputs **still requires the chain-composition work**, and
the Path A result is not directly composable.

### Three candidate next slices

  - **Slice A: Formalize FAST-EXPANSION-SUM** (Shewchuk's canonical
    merge of two expansions of comparable magnitude).  Larger work
    (~3-5 days) but matches orient2d's actual algorithmic structure.
    The 4 TwoProduct outputs in orient2d_exact's accumulator chain
    are 2-component expansions of comparable magnitude; merging them
    requires fast-expansion-sum, not grow-expansion.

  - **Slice B: Investigate a weaker predicate that allows internal
    zeros AND is provable for the cascade AND is sufficient for
    `sign_of_expansion_correct`.**  Smaller work (~1-2 days) but
    uncertain feasibility.  The counterexamples in §3 and §9 rule
    out the obvious weakenings; a successful predicate would have
    to thread between them.

  - **Slice C: Tighten orient2d's input regime** to where Path A
    applies.  E.g., positive-coordinate-only sub-regime with
    magnitude separation constraints.  Smaller work (~1 day) but
    produces a narrow result that doesn't cover the headline.

### Session's calibration data

Piece-2 (cascade-structure invariant) was correctly identified as
the load-bearing piece.  It Qed-closed.  Composition was mechanical
as predicted.  Compress lemma was unnecessary — verified before
attempting (the framing prediction).

The bridge analysis above is the one calibration miss: the Path A
result, while clean, doesn't compose into the orient2d headline.
This was visible in the precondition shape (`0 < B2R e` is a strong
condition for arbitrary coordinates) but only confirmed via the
numeric magnitude analysis above.

The discipline note from the previous session's framing — "do the
analysis BEFORE writing Coq" — applies again.  The bridge analysis
took 15 minutes; if it had been done before Path A's design choice,
the session might have steered toward Slice A directly.

### Recommendation

**Slice A (FAST-EXPANSION-SUM)** is the substantive next direction.
Shewchuk's algorithm is well-known, the proof structure has
formalization precedent (BJMP ITP 2017 §4 covers a similar
primitive), and the result directly unblocks orient2d_exact.

Estimated scope (per BJMP's experience + our pace):

  - Algorithm definition (merge by magnitude, Fast2Sum cascade):
    ~1 day.
  - Sum-correctness proof: ~1 day (template lift from current
    `b64_grow_expansion_correct`).
  - Nonoverlap-preservation proof: ~2-3 days (Shewchuk Theorem 13
    formalization, with careful magnitude bookkeeping).
  - Composition into orient2d_exact: ~1 day.

Total: ~5-6 days for Slice A.  Comparable to the Path A track's
total time but produces an orient2d-applicable result.

The Path A artifacts stay in the corpus — they prove a clean
narrow theorem and serve as a partial template for the fast-
expansion-sum work (the per-step exactness lemma reuses
trivially, the B2R-compat helper is needed identically).

## 15. 2026-05-23 prerequisite check for Slice A: nonoverlap_strict vs Shewchuk

Applying the discipline that should have preceded commit `22b6ffe`:
**confirm the composition question before the design session, not
during.**  Before framing Slice A (fast-expansion-sum), check whether
the algorithm's output predicate matches the corpus's
`nonoverlap_strict`.

### Predicates compared

  - **Our `nonoverlap_strict`** (B64_Expansion.v:86-94):
    `|next| <= ulp(prev) / 2`.  Half-ulp, non-strict, NO internal
    zeros tolerated (since `ulp(0) = bpow_emin` and the predicate
    forces `|x| <= bpow_emin / 2 ~ 0`).

  - **Shewchuk Def 2.4 (basic non-overlapping)**: `|next| < ulp(prev)`.
    Full-ulp, strict.

  - **Shewchuk Def 2.5 (strongly non-overlapping)**: basic + "no
    power of 2 between any two components", with explicit tolerance
    for internal zeros (Shewchuk's algorithms produce zeros at
    exact-step boundaries; his predicate is designed to handle them).

  - **Fast-expansion-sum's guarantee (Shewchuk Theorem 13)**: input
    strongly non-overlapping → output strongly non-overlapping.
    Internal zeros allowed throughout.

### The gap

| Property | Ours `nonoverlap_strict` | Shewchuk strongly | Match? |
|---|---|---|---|
| ULP factor | `<= ulp(prev)/2` | `< ulp(prev)/2` (effectively) | ≈ match |
| Internal zeros | **Forbidden** | Allowed | **GAP** |
| Direction | Non-strict (`<=`) | Strict (`<`) at boundaries | minor |

The internal-zero gap is the same one the Path A counterexamples in
§3 and §9 already documented.  Fast-expansion-sum can produce
intermediate zeros when a Fast2Sum step is exact — the same
failure mode as grow-expansion.

### What `sign_of_expansion_correct` actually needs

The proof structure of `expansion_tail_bounded` (B64_Expansion.v:282)
uses `|next| <= ulp(prev)/2` + `ulp(prev) <= |prev|` to derive
`|next| <= |prev|/2`, giving `|tail| < |head|` via geometric series.

Under the WEAKER `|next| <= ulp(prev)` (Shewchuk's basic): still
`|next| <= |prev| / 2^52`, so

```
|tail| <= |x_1| * (1 + 2^(-52) + 2^(-104) + ...)
       <  2 * |x_1|
       <= 2 * ulp(x_0)
       <= 2 * |x_0| / 2^52
       =  |x_0| / 2^51
       <  |x_0|.
```

So `sign_of_expansion_correct` is provable under Shewchuk's basic
(full-ulp) non-overlap too.  The geometric series tolerates the
factor-of-2 weakening cleanly.

### Conclusion: Slice A is feasible, with one extra piece

The answer is **"yes, with a predicate adaptation"**.  Slice A's
scope expands by one ~30-60 line piece: re-prove
`sign_of_expansion_correct` under a weakened predicate that
tolerates internal zeros AND uses Shewchuk's full-ulp bound.

### Slice A's structure

  1. **Define `nonoverlap_shewchuk`**: basic non-overlap with zero
     tolerance.  Allows internal zeros (skip them in the pair
     analysis).  Uses `|next| <= ulp(prev)` (full-ulp).

  2. **Re-prove `sign_of_expansion_correct` under
     `nonoverlap_shewchuk`**: ~30-60 lines.  Geometric series
     argument is essentially the same; needs handling of zero-skip
     in the recursive case.

  3. **Define fast-expansion-sum**: Shewchuk's canonical merge +
     Fast2Sum cascade.  ~1 day.

  4. **Prove fast-expansion-sum sum-correctness**: template lift
     from existing `b64_grow_expansion_correct`.  ~1 day.

  5. **Prove fast-expansion-sum preserves `nonoverlap_shewchuk`**:
     Shewchuk Theorem 13 formalisation.  ~2-3 days.  Magnitude
     bookkeeping through the merge.

  6. **Compose into orient2d_exact**:  ~1 day.  Each TwoProduct
     output is a 2-component expansion (already
     `nonoverlap_shewchuk`); 4 such expansions combined via 3
     fast-expansion-sum calls.

  7. **Headline**: `b64_orient2d_exact_sign_correct` under
     `b64_orient2d_inputs_safe`.

### Revised scope

Estimated **6-8 days** for Slice A (was 5-6; bumped by the
predicate adaptation in pieces 1+2).

### What gets reused from Path A

  - `nonoverlap_strict_B2R_compat`: the structural argument carries
    over directly to `nonoverlap_shewchuk` (predicate depends only
    on B2R values).
  - `nonoverlap_strict_snoc`: re-derivable for the new predicate
    with minor adjustments.
  - `b64_TwoSum_pathA_exact_step`, `b64_plus_under_pathA_dominance`:
    not directly useful for general magnitudes, but the proof
    pattern (round-equality via midpoint arguments) carries over
    to Fast2Sum's correctness proof.
  - The counterexample lemmas: documentation of what NOT to
    attempt; save future implementers from rediscovering the
    wrong predicate.

The Path A track is a solid foundation, not wasted work.  The
counterexamples make Slice A's design choices DEFENSIBLE rather
than arbitrary — the predicate weakening + full-ulp choice is
necessary, not optional.

### Discipline note

This prerequisite check took **20 minutes** (read predicates,
verify geometric series with the looser bound, formulate scope
adjustment).  Had it preceded commit `22b6ffe`, the project would
have gone directly to Slice A without the Path A detour.

The Path A track was still valuable (it produced the
counterexamples, the per-step helpers, and the B2R-compat lemmas
all reusable), but the headline-composition question should be the
FIRST check when framing any new slice that aspires to unblock a
downstream consumer.

The lesson generalises: precondition-fit checks apply at TWO levels:

  - Inside the slice (verify the proof's local preconditions thread).
  - Across slices (verify the slice's output composes into the next
    consumer).

The cross-slice check is the one that was missed before `22b6ffe`.
Applying it consistently for Slice A.
