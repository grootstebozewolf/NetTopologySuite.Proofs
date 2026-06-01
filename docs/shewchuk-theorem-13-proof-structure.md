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

> ## ⚠️ FINDING (verified) — the Route-2 `cascade_pathA_chain` reduction is too strong; go back to square 1
>
> Do **not** try to prove `cascade_pathA_chain_from_nonoverlap` (discharging
> the Route-2 conditional headline's hypothesis from `nonoverlap` inputs).
> **It is false**, so it can never be discharged. The headline itself is
> still true — the *reduction* is unsound.
>
> - The conditional headline's hypothesis requires
>   `cascade_invariant_handover (initial_cascade_state x prov) ((x2,_)::_)`
>   for the two magnitude-smallest inputs `x` (= initial carry) and `x2`:
>   they must be same-sign, or `x = 0`, or the carry must be `< ½ ulp` of
>   (pred/succ of) `x2` — i.e. ~53 bits smaller.
> - `nonoverlap_shewchuk` constrains only **same-source** consecutive
>   elements. After the magnitude merge-sort the two globally-smallest can
>   be **cross-source, similar magnitude, opposite sign** — no half-ulp
>   separation — so every handover disjunct fails.
> - **Verified core**: `cascade_handover_fails_mixed_sign` in
>   `theories-flocq/B64_Shewchuk_Thm13_pathA_defect.v` (Qed) proves the
>   handover is unsatisfiable for `0 < B2R x`, `B2R x2 < 0`,
>   `½ ulp(succ (B2R x2)) ≤ B2R x`.
> - **Concrete witness**: `e = [1.0]`, `f = [-1.0]`. Premises hold (singletons
>   are trivially `nonoverlap_shewchuk`); `fast_expansion_sum` sums to 0 →
>   compresses to `[]` → headline `nonoverlap_shewchuk [] = True`. Yet
>   `cascade_pathA_chain` is **False** (apply the lemma with `B2R x = 1`,
>   `B2R x2 = -1`, `½ ulp(succ(-1)) ≈ 2⁻⁵³ ≤ 1`).
>
> **Redirect for the next session.** The fix is to generalise the per-step
> invariant from pathA-only to **pathA ∨ pathB**, where pathB is the
> mixed-provenance cancellation case: an opposite-sign similar-magnitude pair
> makes `b64_TwoSum` produce a zero / sub-normal high part that `compress`
> deletes, and the cascade continues. The entire Route-2 framework
> (`cascade_run_output_nonoverlap`, the conditional headline, the magnitude
> lemmas) is sound and Qed — only the invariant `cascade_pathA_chain` must be
> widened, then re-discharged. Don't grind the pathA chain.

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

> ## ⚠️ `cascade_qnew_dominates` AS STATED IS FALSE (rigorous, exact-integer witness)
>
> Carry magnitude is **not** monotone: opposite-sign cancellation shrinks it.
> `sorted_asc` is by **absolute value** (`Rabs (B2R x) <= Rabs (B2R y)`), so a
> larger-magnitude opposite-sign element legitimately follows a smaller one.
>
> **Witness** (both exact binary64, integer-regime — no rounding at all):
> `q = 3`, `xs = [-4]`.  `sorted_asc (3 :: [-4])` holds (`|3| <= |-4|`).
> `b64_grow_expansion_aux 3 [-4]` computes `b64_TwoSum (-4) 3 = (-1, 0)`
> exactly (`-1` is representable, error `0`), so `qfinal = -1`.  The claimed
> conclusion `Rabs (B2R q) <= Rabs (B2R qfinal)` is `3 <= 1` — **false**.
>
> So the "weaker bound suffices / coarser magnitude-preservation" hope below
> does not hold either: `|round(x+q)| >= ||x|-|q||` is true but useless here,
> because `||x|-|q|| = |-4|-|3| = 1 < 3 = |q|`.  The carry genuinely shrinks.
>
> **Oracle-validated** (runs the *extracted* `b64_grow_expansion_aux`, seconds,
> no Coq literal construction):
> ```
> $ printf 'GROW_EXPANSION\n3\n-4\n' | oracle_bin   ->  QFINAL -0x1p+0   (= -1)
> $ printf 'TWOSUM\n-4\n3\n'         | oracle_bin   ->  SUM -0x1p+0 ERR 0x0p+0
> $ printf 'GROW_EXPANSION\n3\n4\n'  | oracle_bin   ->  QFINAL 0x1.cp+2   (= 7, same-sign grows)
> ```
> `|QFINAL| = 1 < 3 = |q|`.  Modes `TWOSUM` / `GROW_EXPANSION` added to the
> RocqRefRunner specifically to make cascade-magnitude counterexamples
> checkable by computation.
>
> **Consequence.** §2.1 → §2.2 → §3 as written is broken: there is no carry
> magnitude-monotonicity lemma to anchor the half-ulp chain.  What is actually
> invariant is the **output's** `nonoverlap_shewchuk` (on the *compressed*
> carry::output, which tolerates cancellation zeros), maintained by Shewchuk's
> **per-provenance run argument** (§4) — not by any single-quantity carry
> bound.  Third falsified naive invariant this lineage (after the pathA chain,
> see `B64_Shewchuk_Thm13_pathA_defect.v`).  Square 1 for the magnitude side is
> the per-provenance run structure, stated over the tagged input — not a carry
> monotonicity lemma.
>
> **Lean on the already-proven exactness, not magnitude.** Shewchuk's real
> guarantee for `grow_expansion` (Thm 10) is *exactness + ordering*, not
> magnitude monotonicity — and exactness is ALREADY `Qed` in the corpus:
> `b64_grow_expansion_aux_correct` (`expansion_R hs + B2R qfinal =
> expansion_R es + B2R q`) and `fast_expansion_sum_correct`
> (`expansion_R (fast_expansion_sum e f) = expansion_R e + expansion_R f`).
> So the only open content of Theorem 13 is the **nonoverlapping/ordering**
> preservation; the next session should compose it from the proven exactness
> + the per-provenance ordering, and must NOT re-introduce a carry-magnitude
> lemma (false, per the box above). NB: the cancellation that falsifies
> magnitude monotonicity is exactly what the tail/error words exist to
> capture — it is correct expansion behaviour, not a bug.

**Why this should still be provable** (NOTE: superseded by the box above —
the carry-monotonicity framing is false; retained for context): under
`sorted_asc`, each step has `|q_{i-1}| <= |x_i|`.  The same-sign case is
covered by the already-Qed-closed `b64_TwoSum_step_dominates_pos / _neg`.  The
mixed-sign case is NOT covered by the strict Path A absorption (which
needs `|q| < ulp(pred x)/2`), and — per the box above — is NOT rescued by a
coarser carry bound either; the carry can shrink below its initial magnitude.

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

## §6. Route 2 (list-indexing invariant) -- selected design

After the 2026-05-24 verification ruled out Route 3, and Route 1 was
deemed too invasive (touches all existing Qed-closed cascade
correctness lemmas), Route 2 is the committed design.

> **Status note (Session 2 outcome — Route 2 collapsed).**
>
> **→ Full collapse artifact:
> [`docs/slice-a-piece-5b-session-2-collapse.md`](slice-a-piece-5b-session-2-collapse.md).**
>
> Summary: every candidate clause (c) over the Session-1-framework
> state `(q : binary64, hs : list binary64)` either requires the
> strict_succ_b64 chain on the merged input (rejected by §2.1's
> counterexample) or cannot establish the upper-bound propagation
> `|qnew| <= |head of remaining|` needed for the mixed-provenance
> inductive step (no upper-bound lemma on `b64_plus` in the corpus,
> and the per-source nonoverlap arguments require tracking `q`'s
> provenance, which Route 2 deliberately doesn't).  Route 1 trigger:
> attach a `cs_prov : provenance` field to the cascade state.
>
> **Status note (Route 1 design session — red phase, third-design recommended).**
>
> **→ Full design artifact:
> [`docs/slice-a-piece-5b-route1-design-session.md`](slice-a-piece-5b-route1-design-session.md).**
>
> Summary: `cs_prov` is necessary but not sufficient.  The four-way
> case-split must be on **sign** of `B2R` values (not provenance, which
> does not determine sign), with `cs_prov` supplying magnitude info via
> the per-source strict_succ_b64 chain.  The mixed-prov mixed-sign
> similar-magnitude case + the round-to-even boundary remain
> uncovered by any clause-(c) framing.  Recommendation: state the
> h-chain as a separate cascade-step lemma rather than an invariant
> clause.
>
> **Status note (Route 1 Session 2 — collapse confirmed against live Coq).**
>
> **→ Full collapse artifact:
> [`docs/slice-a-piece-5b-route1-session-2-collapse.md`](slice-a-piece-5b-route1-session-2-collapse.md).**
>
> Summary: with the host toolchain available, Route 1 Session 2 ran
> the green-phase attempt in Coq.  The refined clause (c) (five-arm
> disjunction over the `b64_TwoSum_step_dominates_xxx` family's
> preconditions) Qed-closes `cascade_invariant_empty` under hypothesis,
> but `cascade_step_preserves_invariant` bails at the clause-(a)
> subgoal `nonoverlap_shewchuk (qnew :: h :: rev (cs_output state))`.
> The load-bearing sub-link `strict_succ_b64 h h_prev` (the h-chain
> between consecutive cascade errors) is not propagated by any
> clause-(c) shape — it is a property of the cascade's STEP
> TRANSITION, not of the state, and `cs_prov` only supplies the right
> hypothesis context for same-source consecutive transitions.
>
> **Status note (Route 1 Session 3 — 2^53 gap quantified + §4 analysis).**
>
> The collapse artifact above carries the §4 analysis that closes the
> Session 2 finding.  Key results (Qed-closed in
> `theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v`):
>
>   - `test_invariant_implies_h_prev_bound`: the existing invariant
>     gives `|h_prev| <= ulp(cs_carry)/2`, but
>     `cascade_h_chain_statement` requires `|h_prev| <=
>     ulp(snd (b64_TwoSum x cs_carry))/2 ≈ ulp(cs_carry)/2 * 2^-53`.
>     The invariant's bound is **roughly 2^53 too loose**.
>   - §4 closes the gap via run-bound tracking: same-prov consecutive
>     within a run uses per-source nonoverlap one-time;
>     cross-prov uses step-by-step cumulative reasoning about the
>     current run's maximum element.  Neither Option A (richer
>     precondition only) nor Option C (intermediate lemma over
>     inputs only) suffices — both fail at the cross-prov boundary.
>     **Option B with a `cs_run_max` conjunct** is the right path.
>
> **→ Successor prompt:
> [`docs/slice-a-piece-5b-route1-session-4-prompt.md`](slice-a-piece-5b-route1-session-4-prompt.md).**
> Three deliverables: clause (d) + `cs_run_max`, two intermediate
> lemmas (within-run and cross-prov), and `cascade_h_chain` by case
> split on provenance continuity.  Estimated 220-300 lines.

### §6.1 The provenance tagging

Define an auxiliary tag set:

```coq
Inductive provenance : Set := from_e | from_f.
```

The cascade input `sort_by_abs (e ++ f)` is paired with a list of
tags `ps : list provenance` such that:
  - `length ps = length (sort_by_abs (e ++ f))`.
  - `length (filter (fun p => p = from_e) ps) = length e`.
  - Similarly for `from_f`.

The tagging is computable from the sort process (stable sort,
prepending tags), but the predicate is what matters for the proof.

### §6.2 The invariant

```coq
Definition cascade_invariant
  (state_q : binary64)
  (state_hs : list binary64)  (* smallest-first, as produced *)
  (remaining_inputs : list (binary64 * provenance))
  : Prop :=
  (* Three clauses: *)
  (* (a) Output well-formed: *)
  nonoverlap_shewchuk (state_q :: rev state_hs) /\
  (* (b) Magnitude bound on state_q relative to last processed: *)
  (forall last_input, last_processed_input remaining_inputs = Some last_input ->
     Rabs (B2R state_q) <= 2 * Rabs (B2R last_input)) /\
  (* (c) Chain handover compatible with next TwoSum: *)
  (forall next_input next_prov,
     remaining_inputs = (next_input, next_prov) :: _ ->
     (* Next step's b64_TwoSum produces a result that preserves *)
     (* nonoverlap_shewchuk on the new state. *)
     ...).
```

The exact form of clause (c) is what the proof's inductive step
needs.  Refined statement is part of the next session's work --
likely "either same-provenance (strict_succ_b64 from source
precondition) or mixed-provenance (TwoSum produces zero-h or
near-zero-h that compress filters)".

### §6.3 The inductive structure

The cascade preservation lemma:

```coq
Lemma cascade_step_preserves_invariant :
  forall q hs x p xs',
    cascade_invariant q hs ((x, p) :: xs') ->
    b64_TwoSum_safe x q ->
    let '(qnew, h) := b64_TwoSum x q in
    cascade_invariant qnew (h :: hs) xs'.
```

The proof case-splits on the provenance of `(x, p)` relative to the
last processed input.  Same-provenance cases use the strict_succ_b64
chain inherited from `nonoverlap_shewchuk e` or
`nonoverlap_shewchuk f`.  Mixed-provenance cases use the absorbing
behavior of TwoSum on non-overlapping pairs (which the corpus's
counterexample registry already characterises).

### §6.4 Resumption checklist (Route 2 specific)

  1. Confirm `sort_by_abs_sorted` is still Qed-closed in the corpus.
  2. Define `provenance`, `tagged_sort_by_abs`, and prove
     length/membership properties relating the tagging to `e` and `f`.
  3. Define `cascade_invariant` with the three clauses above.
     Refining clause (c) is the load-bearing design step.
  4. Prove `cascade_step_preserves_invariant` by case-analysis on
     provenance.  Uses the already-Qed-closed `b64_TwoSum_step_dominates_*`
     lemmas for the same-sign sub-cases.
  5. Bootstrap the invariant from the headline's preconditions:
     `nonoverlap_shewchuk e` + `nonoverlap_shewchuk f` →
     `cascade_invariant (head of sort) nil (tail of sort)`.
  6. Run `cascade_step_preserves_invariant` through the cascade by
     induction, deriving the final state's invariant.
  7. Extract `nonoverlap_shewchuk (fast_expansion_sum e f)` from the
     final state's clause (a).
  8. Remove the entry from `docs/admitted-deferred-proofs.txt`.

**Revised session count estimate**: 3-4 sessions.
  - Session 1: §6.1 + §6.2 + define clauses (~150 lines).
  - Session 2: §6.3 + §6.4 step 4 (cascade_step_preserves_invariant)
    case-split (~200-300 lines).
  - Session 3-4: bootstrapping + composition + audit (~100 lines).

### §6.5 Risk analysis

The biggest risk in Route 2 is clause (c) of the invariant.  The
inductive step needs a precondition strong enough to derive the
next state's clause (a) (output well-formed) from the current
state's clauses + the next TwoSum step's properties.

If clause (c) ends up requiring the FULL strict_succ_b64 chain on
the input list (which we know is false), Route 2 collapses back to
Route 3's territory.  The escape valve is the compress step: zero
h's are filtered, so clause (a) only needs nonoverlap_strict on the
non-zero subsequence -- which the per-provenance argument may give.

**If Route 2 collapses**: pivot to Route 1 (cascade-state
augmentation) as the next-best option, accepting the
already-Qed-closed-lemma churn.
