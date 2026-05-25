# Slice A Piece 5b Route 1 Session 17 — outcome

**Session.** Route 1 Session 17: attempt the general
`fast_expansion_sum_nonoverlap_shewchuk` (the Admitted at
`B64_FastExpansionSum_Shewchuk.v:483`).  Branch
`claude/cascade-invariant-bootstrap-8oSDv`.

**Outcome.** TWO DELIVERABLES LANDED.  The **conditional general
theorem** is Qed-closed — the general headline reduces precisely to
`cascade_pathA_chain` derivability.

The Admitted general theorem **remains the deferred-proof registry
entry**.  Session 17's contribution is to characterise the
remaining gap precisely: it is the cascade_pathA_chain
discharge-from-inputs question, not a Coq-tactical problem nor an
unknown structural obstacle.

## Deliverables landed

### `fast_expansion_sum_via_cascade_run` (Qed-closed)

```coq
Lemma fast_expansion_sum_via_cascade_run :
  forall (e f : list binary64) (x : binary64) (prov : provenance)
         (rest : list tagged_b64),
    tagged_input e f = (x, prov) :: rest ->
    fast_expansion_sum e f =
      cs_carry (cascade_run (initial_cascade_state x prov) rest)
      :: rev (cs_output (cascade_run (initial_cascade_state x prov) rest)).
```

The bridge from `fast_expansion_sum`'s algorithmic output (UNTAGGED
computation) to the cascade_run state-machine's output (TAGGED
iteration).  Uses `untag_tagged_input` (Session 1) and
`cascade_run_cs_carry/output` (Session 11).

Proof structure (~15 lines): unfold `fast_expansion_sum`, use
`untag_tagged_input` to relate `sort_by_abs (e ++ f)` to `untag
(tagged_input e f)`, then case-split on the tagged input's head
provenance to align with `initial_cascade_state`.

### `fast_expansion_sum_nonoverlap_shewchuk_general_conditional` (Qed-closed)

```coq
Theorem fast_expansion_sum_nonoverlap_shewchuk_general_conditional :
  forall (e f : list binary64),
    fast_expansion_sum_safe e f ->
    (match tagged_input e f with
     | nil => True
     | (x, prov) :: rest =>
         cascade_invariant_handover (initial_cascade_state x prov) rest /\
         cascade_pathA_chain (initial_cascade_state x prov) rest
     end) ->
    nonoverlap_shewchuk (fast_expansion_sum e f).
```

**The conditional general theorem.**  Given Path A holds at every
cascade step (plus the initial handover), the general headline
follows.

Proof (~15 lines):

  1. Case-split on `tagged_input e f`.
  2. Empty case: trivial.
  3. Non-empty case: apply `fast_expansion_sum_via_cascade_run` to
     rewrite output, then apply `cascade_run_output_nonoverlap`
     (Session 12) with `cascade_invariant_empty` (Session 5) +
     the supplied chain hypothesis.

This **closes the general headline modulo cascade_pathA_chain
derivability**.

## The precise remaining gap

The hypothesis pattern:

```coq
match tagged_input e f with
| nil => True
| (x, prov) :: rest =>
    cascade_invariant_handover (initial_cascade_state x prov) rest /\
    cascade_pathA_chain (initial_cascade_state x prov) rest
end
```

For the general theorem (the registry entry) to discharge, this
hypothesis must be derivable from:
  - `fast_expansion_sum_safe e f`
  - `nonoverlap_shewchuk e`
  - `nonoverlap_shewchuk f`

Discharging `cascade_pathA_chain` requires showing that **Path A
holds at every cascade step** for arbitrary inputs.  Path A's
precondition:

```
strict_succ_pathA_R (B2R x_next) (B2R cs_carry):
  |B2R cs_carry| < ulp(pred (B2R x_next)) / 2.
```

Across cascade steps:

  - **Within-source consecutive**: holds via per-source
    `nonoverlap_shewchuk` (the half-ulp chain gives the 2^53 gap).
  - **Cross-prov boundary**: cs_carry has both sources' accumulated
    contributions; Path A may fail.

The cross-prov boundary is the persistent obstacle.  Shewchuk
Theorem 13's deep magnitude bookkeeping closes this; that
bookkeeping is the ~200-400 line formalisation work that's been
deferred since Stage D started.

## Status of the general theorem (the registry entry)

`fast_expansion_sum_nonoverlap_shewchuk` at
`B64_FastExpansionSum_Shewchuk.v:483` remains Admitted.  Session 17
has:

  - Proven the conditional general theorem (`_general_conditional`)
    Qed-closed.
  - Established that the precise gap is `cascade_pathA_chain`
    derivability from input properties.
  - This is a **strictly tighter characterisation** than Session 14's
    "Length 3+ wall" — we now know the wall is exactly the
    cross-prov boundary in cascade_pathA_chain.

Registry status: **unchanged** at 4 entries.  The deferred-proof
remains; what's been added is a clear specification of what
discharging it requires.

## Session 17 commit summary

  - `theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v`:
    - `fast_expansion_sum_via_cascade_run` (Qed-closed, ~15 lines).
    - `fast_expansion_sum_nonoverlap_shewchuk_general_conditional`
      (Qed-closed, ~15 lines).
    - `Print Assumptions` for the new theorems.
  - `docs/slice-a-piece-5b-route1-session-17-outcome.md` (this file).

Two new Qed-closed theorems.  Registry **unchanged** at 4 entries
(the general theorem stays deferred).  CI gauntlet green.

## CI gauntlet (this session)

```
$ bash scripts/check_admitted.sh
All Admitted theorems registered (4 total: 3 counterexample, 1 deferred-proof).

$ bash scripts/audit_axioms.sh /tmp/build.log
[axioms-audit] OK: all per-theorem PA blocks satisfy the allowlist (or are exempted).

$ bash scripts/check_readme_axioms.sh
[readme-axioms] OK: README and docs/axiom-allowlist.txt agree.
```

## Final assessment of the Route 1 series (Sessions 1-17)

After 17 sessions, the Route 1 corpus has built up substantial
machinery and proven multiple useful corollaries.  The state of the
general theorem:

| Statement                                          | Status        |
|----------------------------------------------------|---------------|
| Conditional via `cascade_pathA_chain` (S12)        | Qed-closed    |
| **General via `cascade_pathA_chain` from inputs (S17)** | **Qed-closed conditional** |
| Two-singletons general (S14)                       | Qed-closed    |
| (2,2) orient2d-shape int-safe (S16)                | Qed-closed    |
| Inductive int-safe cascade (S15)                   | Qed-closed    |
| **General `fast_expansion_sum_nonoverlap_shewchuk`** | **Deferred (registry)** |

The Route 1 corpus has 37+ Qed-closed theorems.  Two complete
structural paths (Path 1 conditional, Path 2 unconditional for
specific shapes).  The persistent deferred-proof obstacle has been
characterised precisely: cascade_pathA_chain derivability from
arbitrary inputs, equivalent to formalising Shewchuk Theorem 13's
cross-prov magnitude bookkeeping.

For Stage D consumers:
  - **Orient2d-shape integer-safe inputs** (the common case): use
    Session 16's `_int_safe_two_pairs`.
  - **Any two-element inputs**: use Session 14's `_two_singletons`.
  - **Inputs where Path A is establishable per-case**: use Session
    17's `_general_conditional` after discharging the chain
    hypothesis.
  - **Arbitrary inputs**: depends on the deferred-proof.

The 17-session sequence demonstrates that the original Admitted
"Shewchuk Theorem 13" can be approached via the Route 1 framework,
with each session contributing one structural piece.  The remaining
work (cross-prov magnitude analysis) is well-characterised but
substantial — ~200-400 lines of focused Flocq work building on the
existing per-source / Path A / cascade_run infrastructure.

## What this dialogue series demonstrates

The Route 1 series shows that complex mathematical formalisations
benefit from:

  1. **Collapse-driven design**: when an attempt fails, document
     precisely where and why.  Each Session 1-N collapse narrowed
     the design space.
  2. **Modular sub-results**: 37+ Qed-closed theorems form a library
     of reusable structural facts.  Future formalisation work has a
     solid foundation.
  3. **Honest framing of corollaries**: Session 16 explicitly noted
     it closes a corollary, not the registry-entry theorem.  This
     prevents false-clean commits.
  4. **Conditional headlines**: Sessions 12, 17 prove conditional
     versions that precisely characterise the remaining gap.

The Stage D Slice A Piece 5b "deferred-proof" entry has been moved
from "we don't know how to prove this" to "the precise gap is
cascade_pathA_chain derivability, and here's the conditional
theorem that closes the rest."  That's the maximum forward progress
without doing the cross-prov boundary work itself.
