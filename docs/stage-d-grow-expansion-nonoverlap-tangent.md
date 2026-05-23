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

## 8. Stopping condition

**Tangent stop — design choice required**.  The cascade-invariant
formulation in `docs/stage-d-chain-composition-approach.md` §6 is
incompatible with `nonoverlap_strict` as it stands.  No further proof
work without resolving the predicate question.

The Coq goal state and the counterexample are durable artifacts; the
next session picks up by making the Option A / B call on evidence,
then writing the predicate (Option A) or the compress + lemma (Option B).
