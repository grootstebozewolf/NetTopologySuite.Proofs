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

**Incremental progress** (in
`theories-flocq/B64_FastExpansionSum_Shewchuk.v`):
  - `b64_plus_geq_pos`: positive-case `b64_plus` monotonicity (Qed).
  - `b64_plus_leq_neg`: negative-case `b64_plus` monotonicity (Qed).
  - `b64_TwoSum_step_dominates_pos`: per-step magnitude bound, positive
    operands (Qed).
  - `b64_TwoSum_step_dominates_neg`: per-step magnitude bound, negative
    operands (Qed).
  - `b64_TwoSum_step_dominates_same_sign`: per-step magnitude bound,
    same-sign composition (Qed).
  - `b64_TwoSum_step_dominates_q_zero`: per-step magnitude bound when
    `q = 0` (Qed).
  - `b64_TwoSum_step_dominates_strict_pos`: per-step magnitude bound
    for any-sign `q` under the STRICT precondition
    `|B2R q| < ulp(pred (B2R e))/2` and `0 < B2R e` (Qed).  Uses the
    existing Path A absorption `b64_plus_under_pathA_dominance`.
  - `b64_TwoSum_step_dominates_strict_neg`: symmetric for negative
    `B2R e`, via `round_eq_pathA_negative` (Qed).

These cover all sign combinations under various preconditions, but the
**precondition required by the cascade is weaker than `strict_succ_b64`**.
See §2.1 below for the corrected analysis of what `fast_expansion_sum`'s
cascade input actually satisfies.

> **Status note (2026-05-24)**: A prior version of this doc claimed §2.1
> needed only a bridge from `strict_succ_b64 e q` (`<=`) to the Path A
> precondition (`<` on `ulp(pred e)`).  That analysis was wrong: the
> cascade input doesn't satisfy `strict_succ_b64` to begin with, so the
> "bridge" is not the bottleneck.  See §2.1 for the corrected lemma
> statement.

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

### §2.1 Magnitude monotonicity (corrected analysis)

**What an earlier version of this doc got wrong**: it stated
`cascade_qnew_dominates` with the precondition
`nonoverlap_shewchuk (rev (q :: xs))` -- i.e. the cascade input is
itself strongly nonoverlapping in descending order.  That precondition
is **not satisfied** by `fast_expansion_sum`'s actual cascade input.

**Counterexample (sorted merge isn't strongly nonoverlapping)**:
Let `e = [4.0]` and `f = [3.0]`.  Both are trivially
`nonoverlap_shewchuk` (singletons).  After
`sort_by_abs (e ++ f)` ascending: `[3.0, 4.0]`.  Reversed:
`[4.0, 3.0]`.  For `nonoverlap_shewchuk [4.0, 3.0]` we'd need
`strict_succ_b64 4.0 3.0`, i.e. `Rabs 3.0 <= ulp 4.0 / 2 = 2^(-50)`.
Flagrantly false: `Rabs 3.0 = 3`.

So `nonoverlap_shewchuk e + nonoverlap_shewchuk f + sort_by_abs (e ++ f)`
does not imply `nonoverlap_shewchuk` on the merged list.  The cascade
input only satisfies `sorted_asc`.

**What the cascade actually sees**: at step `i`, accumulator `q_{i-1}`
and next input `x_i` with `|q_{i-1}| <= |x_i|` (sorted-ascending).
That's the *only* relationship guaranteed by the source preconditions
applied to the merge.

In particular, `|q_{i-1}|` can range over `(0, |x_i|]`; the boundary
case `|q_{i-1}| = ulp(x_i)/2` is one specific point in that range and
is **not** vacuous -- mixed-adjacent pairs from `e` and `f` routinely
produce `|q_{i-1}|` comparable to `|x_i|`.

**Corrected lemma statement** (not yet attempted):

```coq
Lemma cascade_qnew_dominates :
  forall (xs : list binary64) (q : binary64),
    sorted_asc (q :: xs) ->
    b64_grow_expansion_aux_safe q xs ->
    forall hs qfinal,
      b64_grow_expansion_aux q xs = (hs, qfinal) ->
      Rabs (B2R q) <= Rabs (B2R qfinal).
```

Note: no `nonoverlap_shewchuk` precondition.  Only `sorted_asc` and
safety.

**Why this should still be provable**: under `sorted_asc`, each step
has `|q_{i-1}| <= |x_i|`.  The same-sign case is covered by the
already-Qed-closed `b64_TwoSum_step_dominates_pos / _neg`.  The
mixed-sign case is NOT covered by the strict Path A absorption (which
needs `|q| < ulp(pred x)/2`), but a weaker bound suffices: under
`|q_{i-1}| <= |x_i|`, the rounded sum `round(x_i + q_{i-1})` has
magnitude `>= ||x_i| - |q_{i-1}||` modulo rounding error.  This isn't
absorption; it's a coarser magnitude-preservation argument.

**Why Shewchuk Theorem 13 still works**: Shewchuk's actual proof
tracks per-element provenance (which `x_i` came from `e` vs from `f`)
and uses the fact that consecutive *same-provenance* elements satisfy
`strict_succ_b64` (since `e` and `f` are individually strongly
nonoverlapping).  Mixed-provenance adjacent pairs in the merge get a
weaker treatment.  The cascade's accumulator after processing a run
of same-provenance elements ends up with magnitude bounded by the
last element processed, which combines with the next-provenance
element's magnitude via TwoSum's bound.

This per-provenance tracking is the genuinely multi-session
formalisation work.  The current `b64_grow_expansion_aux` definition
threads only `q` and `xs`; tracking provenance would either require
augmenting the cascade state or expressing the invariant as a list
property over the input.

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

## §4. Why this works (intuition, corrected)

The "each `x_{i+1}` much larger than `x_i`" version of the intuition
held under the (wrong) assumption that the cascade input satisfies
`nonoverlap_shewchuk` directly.  Under the actual precondition
(`sorted_asc` only, from `sort_by_abs (e ++ f)`), `x_{i+1}` is only
guaranteed `>=` `x_i`, not `>>`.

The right intuition tracks per-element provenance:

- Each `x_i` came from `e` or from `f`.  Call this `provenance(i)`.
- Consecutive same-provenance pairs in the sorted merge come from
  the same input list (either both from `e` or both from `f`).
  Since `e` and `f` are individually strongly nonoverlapping,
  consecutive same-provenance elements DO satisfy `strict_succ_b64`
  in descending order (or equivalently, ascending order after
  reversal).
- Mixed-provenance pairs have only the sorted-ascending guarantee:
  `|x_i| <= |x_{i+1}|`.

The cascade processes inputs smallest-to-largest.  At step `i`, the
accumulator `q_{i-1}` carries the sum of all previously-processed
inputs.  Shewchuk's Theorem 13 argument shows:

- Each TwoSum step produces `(qnew, h)` where `qnew` absorbs the
  "high" part and `h` is the "low" part (the error).
- The cascade's invariant: after processing the first `k` inputs,
  the output `(q_k, h_k, h_{k-1}, ..., h_1)` (largest first) is
  strongly nonoverlapping.
- The key inductive step uses BOTH chains' nonoverlap properties to
  bound the new error `h_i`'s magnitude relative to `q_i`.

This is Shewchuk's paper §4's argument, which is one page of dense
magnitude bookkeeping.  Coq formalisation will need to track
provenance explicitly (either via an auxiliary list-indexing
predicate or by carrying provenance in the cascade state).

## §5. References

- Shewchuk, "Adaptive Precision Floating-Point Arithmetic and Fast
  Robust Geometric Predicates" (1997), Theorem 13.
- BJMP ITP 2017 (HAL hal-01512417) §4: formalises a similar primitive
  (`Add` in their terminology) for general expansion arithmetic.

## §6. Resumption checklist for the follow-up session

When resuming this proof:

  1. Confirm `sort_by_abs_sorted` is still Qed-closed in the corpus.
  2. The same-sign and strict-precondition mixed-sign sub-cases of
     the per-step bound are already formalised (see "Incremental
     progress" above).  These are not directly usable for §2.1 as
     originally stated -- but they are useful for the
     per-provenance-chain reasoning that the corrected §2.1 needs.
  3. **Design decision for per-provenance tracking** (the blocker):
     pick one of:
     - **Augment `b64_grow_expansion_aux` with a provenance tag**:
       change the cascade state to `list (binary64 * provenance)` and
       carry the tag through.  Modular but invasive (touches the
       existing Qed-closed correctness lemmas).
     - **Express the invariant as a list-indexing property**: add an
       auxiliary `cascade_invariant : list binary64 -> list provenance
       -> Prop` that the headline theorem instantiates.  Keeps the
       cascade definition untouched.
     - **Restate the theorem to require a stronger source predicate**:
       e.g. `nonoverlap_shewchuk (sort_by_abs (e ++ f))` as an
       additional hypothesis.  This is logically weaker (provable in
       fewer cases) but matches the proof structure §2.1 originally
       had.  Useful only if the orient2d_exact use case actually
       satisfies it (verify before committing).
  4. State and prove `cascade_qnew_dominates` (corrected §2.1) under
     whichever route step 3 chose.
  5. State `cascade_step_half_ulp` (§2.2).
  6. Compose into `fast_expansion_sum_nonoverlap_shewchuk`.
  7. Remove the entry from `docs/admitted-deferred-proofs.txt`.

**Revised session count estimate**: 3-4 sessions.  Up from the
original 2-3 because step 3's design decision plus per-provenance
tracking adds genuine formalisation surface.

**Cheaper alternative verification (2026-05-24)**: Checked whether
`orient2d_exact`'s use of `fast_expansion_sum` sidesteps the
per-provenance work.  Result: it does not.

For orient2d_exact in the general regime (not the small-int regime,
which is already Qed-closed without `fast_expansion_sum`), the
inputs are 2-component expansions `[s_i, e_i]` from `TwoProduct`,
where `s_i` is the high part and `e_i` is the rounding error
satisfying `|e_i| <= ulp(s_i) / 2`.

Concrete failing example: `s_1 = 2^53`, `e_1 = 1`,
`s_2 = 0.5`, `e_2 = 2^(-54)`.  Each `[s_i, e_i]` is individually
`nonoverlap_shewchuk` (singleton + valid TwoProduct error).
`sort_by_abs ([s_1, e_1] ++ [s_2, e_2])` ascending =
`[e_2, s_2, e_1, s_1]`.  Reversed = `[s_1, e_1, s_2, e_2]`.

Adjacent-pair check on reversed:
  - `(s_1=2^53, e_1=1)`: `|1| <= ulp(2^53)/2 = 1`.  Boundary, just OK.
  - `(e_1=1, s_2=0.5)`: `|0.5| <= ulp(1)/2 = 2^(-53)`?  **FALSE**.
    `|0.5|` exceeds the bound by 53 orders of magnitude.

So the merged-sorted list of typical orient2d products is NOT
`nonoverlap_shewchuk`.  Route 3 (theorem strengthening) is out;
the per-provenance work is genuinely required.
