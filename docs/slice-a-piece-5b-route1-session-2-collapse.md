# Slice A Piece 5b Route 1 Session 2 — collapse artifact

**Session.** Route 1 Session 2 attempt to close
`cascade_step_preserves_invariant` + `fast_expansion_sum_bootstrap`.
Branch `claude/cascade-invariant-bootstrap-8oSDv`.

**Outcome.** ROUTE 1 SESSION 2 COLLAPSE.

This document is the collapse artifact required by the session prompt's
stopping condition.  It records:

  - The Task-1 option chosen (red phase).
  - The refined clause (c) in Coq form (Task 2).
  - The Qed-closed `cascade_invariant_empty` re-proof under the refined
    clause (c) (Task 3).
  - The Coq attempt at `cascade_step_preserves_invariant` (green phase).
  - The verbatim goal state at the bail point.
  - The missing property as a Coq Prop type.

Unlike the prior Route 1 design session (which was paper-only because
the container was unavailable), this session ran against a working host
toolchain (Rocq 9.1.1 + Flocq 4.2.2 installed per
`docs/development-environment.md`) and reached a green-phase bail in Coq.
The goal state below is extracted from a live `rocq c` session, not
paper analysis.

## Environment

Host toolchain (Ubuntu 24.04, no Docker access required):

  - `opam 2.1.5-1` + `ocaml 4.14.1` from `archive.ubuntu.com`.
  - `rocq-core.9.1.1` + `rocq-stdlib.9.0.0` from `opam.ocaml.org`.
  - Flocq `4.2.2` built from `gitlab.inria.fr/flocq/flocq` (tag
    `flocq-4.2.2`) against the opam-installed Rocq.
  - Corpus baseline (`make -f Makefile.gen -j4`) passes.
  - CI gauntlet (`check_admitted`, `audit_axioms`, `check_readme_axioms`)
    passes.

## Task 1 — option chosen

**Option 1B (sign-only, 4-arm) extended to 5-arm with zero-carry and
strict-magnitude cases.**

Reading the `b64_TwoSum_step_dominates_*` family in
`theories-flocq/B64_FastExpansionSum_Shewchuk.v:327-481`, the
preconditions case-split on **sign of `B2R x`** and **sign of `B2R q`**,
plus a strict-magnitude bound `|q| < ulp(pred|succ x) / 2` for the
mixed-sign cases.  The lemmas do **not** mention provenance.

Why not 1A (16-arm provenance × sign): the 16-arm form has redundant
arms — provenance is hypothesis context for *deriving* the strict
magnitude bound, not for the case split that picks the lemma.  Same
underlying disjunction with extra unused destructs.

Why not 1C (generalised dominance): provably false in mixed-sign
cancellation per the Route 1 design artifact's concrete counterexample
(`B2R e = 1.0`, `B2R q ≈ -0.999...` gives `|qnew| ≈ 10^-9 << |q|`).

## Task 2 — refined clause (c)

Lives at
`theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v` (committed in
this session).  Verbatim:

```coq
Definition cascade_invariant_handover
  (state : cascade_state) (remaining : list tagged_b64) : Prop :=
  match remaining with
  | nil => True
  | (x, _) :: _ =>
      let q  := cs_carry state in
      let qR := Binary.B2R prec emax q in
      let xR := Binary.B2R prec emax x in
      b64_TwoSum_safe x q /\
      ( (0 < qR /\ 0 < xR)
        \/ (qR < 0 /\ xR < 0)
        \/ qR = 0
        \/ (0 < xR /\ Rabs qR <
              ulp radix2 (SpecFloat.fexp prec emax)
                (pred radix2 (SpecFloat.fexp prec emax) xR) / 2)
        \/ (xR < 0 /\ Rabs qR <
              ulp radix2 (SpecFloat.fexp prec emax)
                (succ radix2 (SpecFloat.fexp prec emax) xR) / 2) )
  end.
```

The strongest clause (c) provable from the `dominates_*` family alone:
the next TwoSum step's dominance can be discharged by one of the five
existing building blocks.

## Task 3 — `cascade_invariant_empty` re-proved

Qed-closed in the file with the handover as a hypothesis:

```coq
Lemma cascade_invariant_empty :
  forall q p remaining,
    cascade_invariant_handover (mk_cascade_state q p nil) remaining ->
    cascade_invariant (mk_cascade_state q p nil) nil remaining.
```

The hypothesis is what the bootstrap (`fast_expansion_sum_bootstrap`,
not in scope for this session) would discharge from the input
preconditions.

## Green phase — `cascade_step_preserves_invariant` attempted

Lemma statement (in the file, terminated with `Abort.`):

```coq
Lemma cascade_step_preserves_invariant :
  forall (state : cascade_state)
         (processed : list binary64)
         (x : binary64) (prov : provenance)
         (rest : list tagged_b64),
    cascade_invariant state processed ((x, prov) :: rest) ->
    cascade_invariant
      (mk_cascade_state
         (fst (b64_TwoSum x (cs_carry state)))
         prov
         (cs_output state ++ [snd (b64_TwoSum x (cs_carry state))]))
      (processed ++ [x])
      rest.
```

(The new `h` is **appended** to `cs_output` rather than prepended, so
the oldest-first convention is preserved; the session-prompt's
prepend version requires changing `cascade_invariant_output` from
`q :: rev hs` to `q :: hs`, which is an equivalent reformulation.)

Proof was driven to the clause-(a) sub-obligation by destructuring the
hypothesis into Ha (output), Hb (magnitude), Hsafe + Hcases (the
handover's two conjuncts), then `rewrite rev_app_distr` to expose the
output's shape.

### Verbatim goal state at the bail point

Extracted from `rocq c` (Rocq 9.1.1, Flocq 4.2.2):

```text
1 goal

  state : cascade_state
  processed : list binary64
  x : binary64
  prov : provenance
  rest : list tagged_b64
  Ha : nonoverlap_shewchuk (cs_carry state :: rev (cs_output state))
  Hb : cascade_invariant_magnitude (cs_carry state) processed
  Hsafe : b64_TwoSum_safe x (cs_carry state)
  Hcases :
    0 < Binary.B2R prec emax (cs_carry state) /\ 0 < Binary.B2R prec emax x \/
    Binary.B2R prec emax (cs_carry state) < 0 /\ Binary.B2R prec emax x < 0 \/
    Binary.B2R prec emax (cs_carry state) = 0 \/
    0 < Binary.B2R prec emax x /\
    Rabs (Binary.B2R prec emax (cs_carry state)) <
    b64_ulp (pred radix2 b64_fexp (Binary.B2R prec emax x)) / 2 \/
    Binary.B2R prec emax x < 0 /\
    Rabs (Binary.B2R prec emax (cs_carry state)) <
    b64_ulp (succ radix2 b64_fexp (Binary.B2R prec emax x)) / 2
  ============================
  nonoverlap_shewchuk
    (fst (b64_TwoSum x (cs_carry state))
     :: snd (b64_TwoSum x (cs_carry state)) :: rev (cs_output state))
```

### Decomposition of the goal

Let `qnew := fst (b64_TwoSum x q_old)` and `h := snd (b64_TwoSum x q_old)`
where `q_old := cs_carry state`.  Writing
`rev (cs_output state) = [h_prev; h_{prev-1}; ...]` (newest h_prev
first, oldest h last), `nonoverlap_shewchuk (qnew :: h :: rev hs)`
decomposes (after compress) into three chains:

  1. `strict_succ_b64 qnew h`         — `|h| <= ulp(qnew)/2`.  This is
     a structural property of `b64_TwoSum` (TwoSum's "low-bits of the
     sum") and is **provable**, though not directly stated in the
     existing corpus.
  2. `strict_succ_b64 h h_prev`       — `|h_prev| <= ulp(h)/2`.  **This
     is the H-CHAIN.**  Consecutive cascade errors must satisfy a
     half-ulp domination.  **NOT in clause (c), NOT in Ha, NOT
     derivable from the dominates_* family.**
  3. Rest of chain over `rev (cs_output state)` — inherited from Ha.

Link (2) is Shewchuk Theorem 13's load-bearing magnitude claim.  It
relates `h_prev` (produced at step `k`) to `h` (produced at step
`k+1`) and requires:

  - `|h_prev|` is small (bounded by what was absorbed at step `k`).
  - `|h|` is large enough that `|h_prev| <= ulp(h)/2` — i.e., `|h|`'s
    binade is far enough above `|h_prev|`'s binade.

In the same-source-consecutive case (no f-element between the two e
elements), nonoverlap_shewchuk on `e` gives `|x_curr|/|x_prev| >= 2^53`
roughly, so `|h_prev| ≈ ulp(x_prev)/2` and `|h| ≈ ulp(x_curr)/2`,
yielding the required ratio.  In the mixed-source consecutive case
(elements alternate between `e` and `f`), the sort only guarantees
`|x_curr| >= |x_prev|` — a constant factor, not 2^53.  Then
`|h_prev|` and `|h|` can be at the same binade and link (2) fails.

This is exactly the Route 1 design artifact's "mixed-prov consecutive"
case (`docs/slice-a-piece-5b-route1-design-session.md` §Task 3),
re-encountered as a live Coq subgoal.

### Why this doesn't close

The refined clause (c) talks about the relationship between `q_old`
and the **next** input `x` (the cascade's *next* step).  It says
nothing about how the **previous** step's error `h_prev` (now at the
head of `rev (cs_output state)`) will relate to the **new** error `h`.
But the inductive preservation of clause (a) needs exactly that —
link (2) above — to keep the half-ulp chain intact when prepending
`h` to the descending chain of stored h's.

The h-chain is a property of the cascade's *step transition*, not of
the state.  `cs_prov` and `Hcases` give the right context to *derive*
the h-chain for specific same-source-consecutive transitions, but no
shape of clause (c) over `(state, remaining)` propagates link (2)
inductively, because the new `h_prev` after step `k+1` is the
just-produced `h` — different from the `h_prev` available at step
`k`.  The invariant cannot "remember" properties about a value that
keeps being replaced by the most recent step.

### Clause (b) also has a structural gap

For completeness: the clause (b) sub-obligation
`Rabs (B2R qnew) <= max_abs_b64 (processed ++ [x])` is **also**
non-trivial under the current invariant.  `|qnew| <= |x| + |q_old|`
(triangle bound) gives at best `|qnew| <= 2 * max_abs_b64 (processed ++ [x])`,
not the exact `max_abs_b64` bound.  Tightening clause (b) to use a
`2x` slack would require re-proving its consumers; it would not by
itself unblock clause (a)'s h-chain.

## Missing property — Coq Prop type

The h-chain claim, stated as a Coq Prop the next session would need
to establish (NOT as an invariant clause, but as a separate
cascade-step lemma per the Route 1 design artifact's recommendation):

```coq
Lemma cascade_h_chain :
  forall (state : cascade_state)
         (processed : list binary64)
         (x : binary64) (prov_x : provenance)
         (rest : list tagged_b64)
         (h_prev : binary64) (hs_tail : list binary64),
    (* The invariant before this step. *)
    cascade_invariant state processed ((x, prov_x) :: rest) ->
    (* The previous step's h is at the head of (rev cs_output). *)
    cs_output state = hs_tail ++ [h_prev] ->
    (* Per-source nonoverlap on e and f. *)
    forall (e f : list binary64),
      nonoverlap_shewchuk e ->
      nonoverlap_shewchuk f ->
      (* sort_by_abs_sorted on the merge gives ascending magnitudes. *)
      sorted_asc (untag (tagged_input e f)) ->
      (* h_prev was produced at step k consuming the previous tagged   *)
      (* element with provenance (cs_prov state); x is the next      *)
      (* element with provenance prov_x.                              *)
      (* CONCLUSION: the new h dominates h_prev in the half-ulp       *)
      (* sense.                                                       *)
      Rabs (Binary.B2R prec emax h_prev) <=
        ulp radix2 (SpecFloat.fexp prec emax)
          (Binary.B2R prec emax
             (snd (b64_TwoSum x (cs_carry state)))) / 2.
```

The hypotheses include the input preconditions
(`nonoverlap_shewchuk e/f`, sorted merge) so that the same-source case
can use the 2^53 gap and the mixed-source case can be argued via
Shewchuk Theorem 13's deep magnitude bookkeeping.  This is the
**~200-400 line core** of Theorem 13, restated in cascade form.

Note: this missing property is **identical in substance** to the one
identified by the Route 2 collapse artifact
(`docs/slice-a-piece-5b-session-2-collapse.md`) and the Route 1 design
artifact (`docs/slice-a-piece-5b-route1-design-session.md`).  All three
sessions converge on the same conclusion: the h-chain is Shewchuk
Theorem 13's load-bearing content and cannot be elided by a clever
state predicate.

## Collapse summary (prompt format)

```
ROUTE 1 SESSION 2 COLLAPSE

Option chosen: 1B (sign-only, extended to 5-arm with q_zero and the
two strict-magnitude cases).  This is the strongest form provable
from the existing dominates_* family alone.

Refined clause (c): (verbatim above in Task 2)

Goal state at bail point: (verbatim above; clause (a) preservation
sub-obligation; head sub-link is `strict_succ_b64 h h_prev` where
`h := snd (b64_TwoSum x (cs_carry state))` and `h_prev :=` last of
`cs_output state`)

Why this doesn't close: the h-chain link between consecutive cascade
errors is a property of the algorithm's STEP transition, not of the
state.  No shape of clause (c) over `(state, remaining)` propagates
the link inductively, because the "previous error" changes at every
step.  cs_prov is hypothesis context that helps derive the h-chain
for specific cases, but does not turn the h-chain into a state
predicate.

Missing property: cascade_h_chain (signature above).  Identical in
substance to the property named by the Route 2 collapse and the
Route 1 design session.  Estimated 200-400 lines of Coq, requires
deep magnitude case analysis on provenance + sign + binade position.
```

## Recommendation for a successor session

The Route 1 design session already recommended a *third design* where
the h-chain is established as a **separate cascade-step lemma**
(`cascade_h_chain`) with `cs_prov` and per-source `nonoverlap_shewchuk`
in hypothesis context.  This session's collapse confirms that
recommendation against a live Coq goal state.

The successor session should:

  1. Keep the Route 1 framework: `cascade_state` record with `cs_prov`,
     `cascade_invariant` with three clauses.  These are not the
     problem.
  2. Keep the refined clause (c) above OR weaken it back to a
     `b64_TwoSum_safe`-only form — clause (c) is not load-bearing in
     either form.
  3. State `cascade_h_chain` as above (or a refined form thereof) as a
     **separate lemma**, NOT as a clause of the invariant.
  4. Compose `cascade_h_chain` with `cascade_invariant`'s clause (a)
     to prove `cascade_step_preserves_invariant`.

This separation matches Shewchuk's own paper structure: §2.1 is the
invariant maintenance argument (analogous to our clause (a)); §4 is
the magnitude bookkeeping (analogous to our missing `cascade_h_chain`
lemma).  Trying to fold §4's content into §2.1's invariant — as both
Route 2 and Route 1 attempted — repeats the structural mistake at a
different scale.

## What this session leaves committed

  - `theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v`:
      - Refined `cascade_invariant_handover` (5-arm disjunction).
      - `cascade_invariant_empty` re-proved as a Qed-closed lemma
        taking the handover as a hypothesis.
      - `cascade_step_preserves_invariant` stated and partially
        attempted; the body ends with `Abort.` after `rewrite
        rev_app_distr` exposed the h-chain sub-obligation.  The
        in-file comment block above the `Abort.` documents the
        collapse with pointers to this artifact.
  - `docs/slice-a-piece-5b-route1-session-2-collapse.md` (this file).
  - `docs/development-environment.md` — already in tree, unchanged;
    cited above as the host-install path.

No new `Admitted` markers, no axioms introduced, registry unchanged at
4 entries (3 counterexample + 1 deferred-proof).  The corpus invariants
hold.

## CI gauntlet (this session)

```
$ bash scripts/check_admitted.sh
All Admitted theorems registered (4 total: 3 counterexample, 1 deferred-proof).

$ bash scripts/audit_axioms.sh /tmp/build.log
[axioms-audit] OK: all per-theorem PA blocks satisfy the allowlist (or are exempted).

$ bash scripts/check_readme_axioms.sh
[readme-axioms] OK: README and docs/axiom-allowlist.txt agree.
```

All green.
