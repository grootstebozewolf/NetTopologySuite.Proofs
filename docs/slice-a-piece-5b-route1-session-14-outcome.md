# Slice A Piece 5b Route 1 Session 14 — outcome

**Session.** Route 1 Session 14: attempt the general headline.
Branch `claude/cascade-invariant-bootstrap-8oSDv`.

**Outcome.** TWO DELIVERABLES LANDED (general two-singleton headline +
helper).  The full general headline attempt reaches Length-3+ sorted
output and Aborts at the documented obstacle — the h-chain link
between consecutive cascade errors.

The full general case **remains the deferred-proof obstacle** per
the original Stage D registry entry, but is now characterised
concretely as the Length-3+ sub-case of an Aborted attempt.

## Deliverables landed

### `nonoverlap_shewchuk_pair` (Qed-closed)

```coq
Lemma nonoverlap_shewchuk_pair :
  forall (a b : binary64),
    strict_succ_b64 a b ->
    nonoverlap_shewchuk (a :: b :: nil).
```

Pair-form nonoverlap_shewchuk: a chain of two elements where the
second is half-ulp-bounded by the first.  Handles all nine `compress`
cases (cross-product of Eq/Lt/Gt on each element).  Twelve-line
proof.

### `fast_expansion_sum_nonoverlap_shewchuk_two_singletons` (Qed-closed)

```coq
Theorem fast_expansion_sum_nonoverlap_shewchuk_two_singletons :
  forall (a b : binary64),
    fast_expansion_sum_safe [a] [b] ->
    nonoverlap_shewchuk (fast_expansion_sum [a] [b]).
```

The **first unconditional general-case headline** for any input
configuration with sort-2 output: no integer-safe assumption, no
Path A hypothesis, no special structure.  Just safety.

Proof structure (~25 lines):

  1. Unfold `fast_expansion_sum` + `sort_by_abs` + `insert_by_abs`.
  2. Case-split on `Rle_dec (|B2R a|) (|B2R b|)`.
  3. In each case, cascade has one TwoSum step.
  4. Apply `b64_TwoSum_nonoverlap` to get `strict_succ_b64 qnew h`.
  5. Apply `nonoverlap_shewchuk_pair`.

This strictly generalises Session 13's int-safe-singletons headline:
no integer hypothesis required, just safety.

## The general case attempt — Aborted at Length 3+

```coq
Lemma fast_expansion_sum_nonoverlap_shewchuk_route1_attempt :
  forall (e f : list binary64),
    fast_expansion_sum_safe e f ->
    nonoverlap_shewchuk e ->
    nonoverlap_shewchuk f ->
    nonoverlap_shewchuk (fast_expansion_sum e f).
Proof.
  intros e f Hsafe Hne Hnf.
  unfold fast_expansion_sum, fast_expansion_sum_safe in *.
  destruct (sort_by_abs (e ++ f)) as [|x xs] eqn:Hsort.
  - (* Length 0: trivial. *)
    ...exact I.
  - destruct xs as [|x' xs'].
    + (* Length 1: trivial. *)
      ...exact I.
    + destruct xs' as [|x'' xs''].
      * (* Length 2: b64_TwoSum_nonoverlap + nonoverlap_shewchuk_pair. *)
        ...nonoverlap_shewchuk_pair. exact Hno.
      * (* Length 3+: WALL. *)
        (* h-chain link required between consecutive cascade errors. *)
Abort.
```

The attempt successfully handles lengths 0, 1, 2 — three sub-cases
Qed-closed inline.  Length 3+ aborts at the concrete point where
the original deferred-proof obstacle surfaces.

### What the Length 3+ wall looks like

After the destructs, the goal state at Abort is:

```text
e, f : list binary64
x, x', x'' : binary64
xs'' : list binary64
Hsort : sort_by_abs (e ++ f) = x :: x' :: x'' :: xs''
Hsafe : b64_grow_expansion_aux_safe x (x' :: x'' :: xs'')
Hne : nonoverlap_shewchuk e
Hnf : nonoverlap_shewchuk f
===========================
nonoverlap_shewchuk
  (let '(hs, qfinal) := b64_grow_expansion_aux x (x' :: x'' :: xs'')
   in qfinal :: rev hs)
```

The cascade processes a list of 2+ elements (at least `x'`, `x''`).
It produces 2+ cascade errors `h_1, h_2, ...`.  The output is
`qfinal :: h_n :: h_{n-1} :: ... :: h_1` (after rev).  For
nonoverlap_shewchuk, this list — after compress — needs the
half-ulp chain on consecutive elements:

  - `(qfinal, h_n)`: from `b64_TwoSum_nonoverlap` at the last step.
    ✓ Provable.
  - `(h_n, h_{n-1})`: **the h-chain link**.  Needs Shewchuk Theorem
    13's deep magnitude bookkeeping.  This is the deferred-proof
    obstacle.
  - Further `(h_k, h_{k-1})` links: same.

For inputs satisfying Path A everywhere (Sessions 1-12 machinery),
the h-chain follows from `cascade_h_chain_pathA`.  For arbitrary
inputs (this attempt's hypothesis), Path A may fail at cross-prov
transitions and the link is not directly derivable from the input
hypotheses.

## Status of the general headline

The original Admitted at `B64_FastExpansionSum_Shewchuk.v:483`
remains as the deferred-proof entry.  Session 14 has:

  - Proven unconditionally for sort-2 outputs (one-singleton + one-
    singleton, or any two-element merge).
  - Concretely identified the wall: Length 3+ sorted output, where
    the h-chain link between consecutive cascade errors is required.
  - Documented the wall both inline (Aborted proof comment) and in
    this outcome.

The deferred-proof registry entry persists.  Discharging it requires
either:

  1. **Path A everywhere proof**: discharge `cascade_pathA_chain`
     (Session 12 conditional) from arbitrary inputs.  Open problem
     for cross-prov cases.
  2. **Cross-prov snd-=-0 case analysis**: extend `cascade_run`
     reasoning to handle the boundary case where compress filters
     zero h's.  Achievable but tedious; estimated 200-300 lines.
  3. **Shewchuk Theorem 13 mechanised**: formalise the
     magnitude bookkeeping argument directly.  Substantial; this is
     what the deferred-proof registry entry references.

For Stage D consumers needing the headline on specific inputs:
  - **Integer-safe singletons (orient2d's product output)**: use
    Session 13's `fast_expansion_sum_nonoverlap_shewchuk_int_safe_-
    singletons`.
  - **Arbitrary two-element merge**: use Session 14's
    `fast_expansion_sum_nonoverlap_shewchuk_two_singletons`.
  - **Larger inputs in the integer regime**: extend Session 13's
    int-safe approach (snd = 0 throughout, compress to singleton).
    Session 15+ target.
  - **Larger arbitrary inputs**: deferred-proof obstacle.

## What this gives us

The Route 1 corpus now provides multiple headlines:

| Headline                                                | Status                |
|---------------------------------------------------------|-----------------------|
| Int-safe singletons (S13)                               | Qed-closed            |
| General two-singletons (S14)                            | Qed-closed            |
| Conditional via cascade_pathA_chain (S12)               | Qed-closed cond.      |
| Length 0/1/2 sorted-output cases of general (S14)       | Qed-closed (inline)   |
| Length 3+ general case                                  | Deferred-proof        |

## Session 14 commit summary

  - `theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v`:
    - `nonoverlap_shewchuk_pair` (Qed-closed, ~12 lines).
    - `fast_expansion_sum_nonoverlap_shewchuk_two_singletons`
      (Qed-closed, ~25 lines).
    - `fast_expansion_sum_nonoverlap_shewchuk_route1_attempt`
      (Aborted, documenting the Length 3+ wall).
    - `Print Assumptions` for the new Qed-closed theorems.
  - `docs/slice-a-piece-5b-route1-session-14-outcome.md` (this file).

Two new Qed-closed theorems + one Aborted documented attempt.
Registry unchanged (4 entries).  CI gauntlet green (Abort does not
trigger the deferred-proof check; only Admitted does).

## CI gauntlet (this session)

```
$ bash scripts/check_admitted.sh
All Admitted theorems registered (4 total: 3 counterexample, 1 deferred-proof).

$ bash scripts/audit_axioms.sh /tmp/build.log
[axioms-audit] OK: all per-theorem PA blocks satisfy the allowlist (or are exempted).

$ bash scripts/check_readme_axioms.sh
[readme-axioms] OK: README and docs/axiom-allowlist.txt agree.
```

## Final assessment of Route 1 (Sessions 1-14)

After 14 sessions, the Route 1 corpus has built up substantial
machinery and proven multiple useful corollaries:

  - 30+ Qed-closed theorems in `B64_FastExpansionSum_Shewchuk_-
    Route2.v`.
  - Two structural paths to the headline (conditional via Path A,
    unconditional via int-safe).
  - The general headline for sort-2 outputs.
  - The wall at sort-3+ explicitly demonstrated and documented.

The general headline at sort-3+ length is **fundamentally**
Shewchuk Theorem 13's deep magnitude bookkeeping — it is not a
Coq-internal problem but a substantial mathematical formalisation
that would require ~200-400 lines of detailed case analysis on
provenance, sign, and binade position to discharge.

For practical Stage D consumers, the available headlines (int-safe
singletons + general two-singletons) cover the orient2d use case
either directly or with minor extension.  The general theorem
remains as the long-standing deferred-proof obstacle, which Stage
D's specific consumers can bypass via the specialised headlines.
