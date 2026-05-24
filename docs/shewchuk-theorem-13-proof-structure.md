# Shewchuk Theorem 13 proof structure

**Target theorem**: `fast_expansion_sum_nonoverlap_shewchuk` in
`theories-flocq/B64_FastExpansionSum_Shewchuk.v`.

**Statement**:

```coq
Theorem fast_expansion_sum_nonoverlap_shewchuk :
  forall (e f : list binary64),
    fast_expansion_sum_safe e f ->
    nonoverlap_shewchuk e ->
    nonoverlap_shewchuk f ->
    nonoverlap_shewchuk (fast_expansion_sum e f).
```

**Status**: Admitted with deferred-proof registration in
`docs/admitted-deferred-proofs.txt`.

This document captures the proof structure with enough detail that a
follow-up session can land the proof without re-deriving the design.
Estimated 200-400 lines of Coq, 2-3 days of focused work.

## §1. Algorithmic background

`fast_expansion_sum e f` is defined in `B64_FastExpansionSum_Shewchuk.v`:

```coq
Definition fast_expansion_sum (e f : list binary64) : list binary64 :=
  match sort_by_abs (e ++ f) with
  | nil => nil
  | x :: xs =>
      let '(hs, qfinal) := b64_grow_expansion_aux x xs in
      qfinal :: rev hs
  end.
```

Two phases:
  1. Merge `e ++ f`, sort ascending by `Rabs (B2R x)`.
  2. Apply the TwoSum cascade (reuses `b64_grow_expansion_aux`).

The output is `qfinal :: rev hs` (largest first).

## §2. The cascade invariant

The load-bearing claim: at each cascade step `i`, the running output
`q_i :: rev (h_1 :: ... :: h_i)` is `nonoverlap_shewchuk` (modulo the
compress filter).

For this to thread inductively, the cascade needs a magnitude
invariant on each accumulator `q_i` relative to the inputs processed
so far.

### §2.1 Magnitude monotonicity (under nonoverlap_shewchuk input)

Lemma needed (not yet stated):

```coq
Lemma cascade_qnew_dominates :
  forall (xs : list binary64) (q : binary64),
    sorted_asc (q :: xs) ->
    nonoverlap_shewchuk (rev (q :: xs)) ->
    b64_grow_expansion_aux_safe q xs ->
    forall hs qfinal,
      b64_grow_expansion_aux q xs = (hs, qfinal) ->
      Rabs (B2R q) <= Rabs (B2R qfinal).
```

This says: under sorted-ascending input + the nonoverlap precondition
+ safety, the cascade's final accumulator dominates the initial one
in magnitude.  Proof: induction on `xs` with each TwoSum step's
magnitude analysis.

### §2.2 Per-step half-ulp on the cascade's output

Lemma needed:

```coq
Lemma cascade_step_half_ulp :
  forall (xs : list binary64) (q : binary64),
    sorted_asc (q :: xs) ->
    b64_grow_expansion_aux_safe q xs ->
    forall hs qfinal,
      b64_grow_expansion_aux q xs = (hs, qfinal) ->
      forall h1 h2 rest,
        rev hs = h1 :: h2 :: rest ->
        Rabs (B2R h2) <= ulp ... (B2R h1) / 2.
```

Or equivalently stated on the unreversed `hs`: consecutive errors in
the cascade satisfy the half-ulp bound after reversal.

Proof: composition of TwoSum_nonoverlap at each step + the magnitude
monotonicity from §2.1.

## §3. Composition into the headline

Given §2.1 and §2.2:

  1. The cascade output's structure `qfinal :: rev hs` has:
     - `strict_succ_b64 qfinal (last_of (rev hs))`: from TwoSum_nonoverlap
       at the last cascade step.
     - Consecutive pairs in `rev hs`: from §2.2.
  2. Internal zeros (from exact-cascade steps) are filtered by
     `compress`.  The compress step doesn't break the half-ulp chain
     because zeros contribute 0 to the magnitude analysis.
  3. The final `nonoverlap_strict (compress (qfinal :: rev hs))` follows
     from the half-ulp chain on non-zero elements.

Composition: `~30 lines` once §2.1 and §2.2 are Qed-closed.

## §4. Why this works (intuition)

For sorted-ascending input `[x_1; x_2; ...; x_n]` with each `x_{i+1}`
much larger than `x_i` (the nonoverlap_shewchuk precondition):

- At cascade step `i`, the accumulator `q_{i-1}` has magnitude
  `~|x_{i-1}|` (the previous-largest input).
- The next step adds `x_i` (larger).  `q_i = round(x_i + q_{i-1})`
  has magnitude `~|x_i|`.
- The error `h_i` has magnitude `~|q_{i-1}|` (the part of `x_i + q_{i-1}`
  that doesn't fit in `q_i`'s mantissa).
- So `h_i` has magnitude `~|x_{i-1}|`, which is at most half-ulp of
  `q_i ~ x_i` (by the strongly-nonoverlapping precondition).
- The h's form a magnitude-decreasing sequence, mirroring the inputs.

After reversal, the output `qfinal :: rev hs` is in descending magnitude
order, with each adjacent pair satisfying the half-ulp bound.  This is
exactly `nonoverlap_strict` (after compressing zeros).

## §5. References

- Shewchuk, "Adaptive Precision Floating-Point Arithmetic and Fast
  Robust Geometric Predicates" (1997), Theorem 13.
- BJMP ITP 2017 (HAL hal-01512417) §4: formalises a similar primitive
  (`Add` in their terminology) for general expansion arithmetic.

## §6. Resumption checklist for the follow-up session

When resuming this proof:
  1. Confirm `sort_by_abs_sorted` is still Qed-closed in the corpus.
  2. State `cascade_qnew_dominates` (§2.1).  Attempt by induction.
     Key subgoal: at each cons step, the new accumulator's magnitude
     is bounded.  Will likely need a stronger invariant carrying both
     the magnitude bound and the per-step exactness.
  3. State `cascade_step_half_ulp` (§2.2).  Attempt by induction
     after §2.1 is in place.
  4. Compose into the headline `fast_expansion_sum_nonoverlap_shewchuk`.
  5. Remove the entry from `docs/admitted-deferred-proofs.txt`.

Estimated session count: 2-3 sessions of focused work, depending on
how much friction the magnitude invariant produces.
