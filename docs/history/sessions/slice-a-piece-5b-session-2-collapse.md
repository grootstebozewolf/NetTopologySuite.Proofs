# Slice A Piece 5b Session 2 — Route 2 collapse artifact

**Session.** Session 2 of the Route 2 design for closing
`fast_expansion_sum_nonoverlap_shewchuk`.  Branch
`claude/cascade-step-preserves-invariant-UMNgF`.

**Outcome.** ROUTE 2 COLLAPSE.

This document is the collapse artifact required by Session 2's stopping
condition.  It captures the red-phase analysis that ruled out the
candidate clause (c) before any green-phase code was written, and names
the missing property that Route 1 (cascade-state augmentation) would
need to carry.

## Status note on environment

The container-based Coq toolchain (`rocq/rocq-prover:9.1.1` +
`coq-flocq.4.2.2`) requires the Docker daemon, which is not available
in this remote-execution session.  The analysis below is paper analysis
against the Qed-closed corpus; no Coq attempt was made in the green
phase because the red phase ruled out every candidate clause (c) that
fits Session 1's framework signature.  The collapse is structural, not
a CI failure.

## What Session 1 set up (the constraint)

`theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v` defines:

```coq
Definition cascade_state : Type := binary64 * list binary64.

Definition cascade_invariant_output (q : binary64) (hs : list binary64) : Prop :=
  nonoverlap_shewchuk (q :: rev hs).

Definition cascade_invariant_magnitude
  (q : binary64) (processed : list binary64) : Prop :=
  Rabs (B2R q) <= max_abs_b64 processed \/ processed = nil.

Definition cascade_invariant_handover
  (q : binary64) (remaining : list tagged_b64) : Prop :=
  True.  (* placeholder *)

Definition cascade_invariant
  (state : cascade_state)
  (processed : list binary64)
  (remaining : list tagged_b64) : Prop :=
  let '(q, hs) := state in
  cascade_invariant_output q hs /\
  cascade_invariant_magnitude q processed /\
  cascade_invariant_handover q remaining.
```

The state carries only `q` and `hs`.  Provenance is tracked on
`remaining` (the unprocessed tagged inputs) but **not** on `q`.  This
is the design choice that distinguishes Route 2 from Route 1.

## Red phase analysis

### What the inductive step needs (top-down derivation)

`b64_grow_expansion_aux` builds the final `hs` by prepending the local
`h` to the recursive result.  At cascade level 0 (smallest input), the
produced `h_0` appears at the **head** of the final `hs` list.  At
level `n-1` (largest input), `h_{n-1}` appears at the **tail**.  So
`hs_final = [h_0; h_1; ...; h_{n-1}]` in temporal order (smallest h at
head).

The final output is `qfinal :: rev hs_final = qfinal :: h_{n-1} :: ...
:: h_0` (largest first), which is what `nonoverlap_shewchuk` expects.

For the **inductive invariant** to track this correctly, the new `h`
produced at each step must be **appended** to `hs` (not prepended).  In
other words, the lemma signature in
`docs/shewchuk-theorem-13-proof-structure.md` §6.3 — which sketches
`cascade_invariant qnew (h :: hs) xs'` — is **structurally
incorrect**; the right operation is `(hs ++ [h])`.

With that correction, after one cascade step processing tagged input
`(x, p)` from the head of `remaining`:

  - State: `(q, hs)` becomes `(qnew, hs ++ [h])` where
    `(qnew, h) := b64_TwoSum x q`.
  - Output to preserve: `nonoverlap_shewchuk (qnew :: rev (hs ++ [h]))
    = nonoverlap_shewchuk (qnew :: h :: rev hs)`.

For this to chain, we need (writing `rev hs = [h_{k-1}; h_{k-2}; ...;
h_0]` for the existing accumulated errors, descending):

  1. `strict_succ_b64 qnew h`: `|h| <= ulp(qnew)/2`.  Direct from
     `b64_TwoSum_nonoverlap`. ✓
  2. `strict_succ_b64 h h_{k-1}`: `|h_{k-1}| <= ulp(h)/2`.  **THIS IS
     THE LOAD-BEARING NEW LINK.**
  3. Rest of chain: from the previous invariant.

Item (2) requires `|h| >= 2 |h_{k-1}|` (roughly).  This is exactly
Shewchuk Theorem 13's deep magnitude bookkeeping: the error from the
current cascade step must dominate the error from the previous step.

### Candidate clauses (c) considered

#### Candidate 1: `sorted_asc (q :: untag remaining)`

```coq
Definition cascade_invariant_handover
  (q : binary64) (remaining : list tagged_b64) : Prop :=
  sorted_asc (q :: untag remaining).
```

**Captures**: `|q| <= |head of remaining|` (the cascade's accumulator
is bounded by the next input).

**Task 2 (does it follow from preconditions + Qed-closed lemmas?):
FAIL.**

The empty state can establish `sorted_asc (q :: untag remaining)` from
`sort_by_abs_sorted`.  But the inductive step needs **propagation**:
given `sorted_asc (q :: x :: untag remaining')` and `(qnew, h) :=
b64_TwoSum x q`, establish `sorted_asc (qnew :: untag remaining')`.

Propagation requires the upper bound `|qnew| <= |head of remaining'|`.

  - The corpus has `b64_plus_correct` (B2R equality) and
    `b64_TwoSum_step_dominates_{pos, neg, same_sign, q_zero}`.  These
    give the **lower** bound `|q| <= |qnew|`.
  - There is **no upper-bound lemma for `b64_plus`** in the corpus.
    The natural triangle-inequality bound `|qnew| <= |x| + |q| <=
    2|x|` is provable, but `sorted_asc` only guarantees `|head of
    remaining'| >= |x|`, not `|head of remaining'| >= 2|x|`.
  - Mixed-provenance counterexample to propagation: if `x` and the
    head of `remaining'` come from different source lists and are at
    the same magnitude scale (which the inputs allow — see the §2.1
    `e=[4.0], f=[3.0]` counterexample in the proof-structure doc),
    then `|qnew| ≈ 2|x|` exceeds `|head of remaining'| ≈ |x|`, and
    sorted_asc fails to propagate.

Candidate 1 is too weak to survive the inductive step.

#### Candidate 2: half-ulp on remaining (strict_succ_b64 chain)

```coq
Definition cascade_invariant_handover
  (q : binary64) (remaining : list tagged_b64) : Prop :=
  match remaining with
  | nil => True
  | (x, _) :: _ =>
      Rabs (B2R q) <= ulp_radix2 b64_fexp (B2R x) / 2
  end.
```

**Captures**: Path A precondition (q is at most half a ulp of the next
input).

**Task 2: FAIL.**  This is exactly the `strict_succ_b64` chain on the
merged input, which the §2.1 counterexample `e=[4.0], f=[3.0]` ruled
out: the merge-sorted input does not satisfy this property even when
`e` and `f` are individually `nonoverlap_shewchuk`.

This is the **§6.5 risk realised in concrete form**.

#### Candidate 3: per-source nonoverlap on remaining + sorted_asc

```coq
Definition cascade_invariant_handover
  (q : binary64) (remaining : list tagged_b64) : Prop :=
  let re := untag (filter (fun t => provenance_eq_dec (snd t) from_e)
                          remaining) in
  let rf := untag (filter (fun t => provenance_eq_dec (snd t) from_f)
                          remaining) in
  sorted_asc (q :: untag remaining) /\
  nonoverlap_shewchuk (rev re) /\
  nonoverlap_shewchuk (rev rf).
```

**Captures**: Sorted-ascending on the merge + per-source half-ulp
chain on what's left.

**Task 2 analysis**:
  - Per-source preconditions at empty state: follow directly from
    `nonoverlap_shewchuk e + nonoverlap_shewchuk f` (the input
    preconditions).
  - Per-source preservation under step (cascade consumed head):
    requires `nonoverlap_shewchuk` to be preserved by removing the
    last element of a half-ulp chain.  Not currently in corpus but
    provable (~10 lines).
  - `sorted_asc (qnew :: untag remaining')` propagation: STILL fails
    in the same mixed-provenance scenario as Candidate 1.  The
    per-source nonoverlap is information about `remaining` but does
    not bound `qnew`.

To get the upper bound `|qnew| <= |head of remaining'|` from the
per-source nonoverlap, we'd need a magnitude argument like: "head of
remaining' is from one source, and the strict_succ chain in that
source from `head of remaining'` down implies it's at least `2^53`
larger than any element processed at the previous scale."  But this
argument requires **knowing which source `q` is bounded by** — which
requires tracking `q`'s provenance.

Candidate 3 captures more structure than Candidates 1-2 but **still
does not close the inductive step's mixed-provenance case**, because
`q` is untagged and the framework cannot relate `q` to a specific
source's chain.

### Why every Route-2 candidate fails

The structural reason: Session 1's `cascade_state = binary64 * list
binary64` carries no provenance for `q`.  The Shewchuk Theorem 13
argument (paper §4) is **inherently provenance-relative**: it argues
about the cascade's accumulator by cases on which source's chain it
last absorbed.  Without provenance on `q`, no clause (c) over
`(q, remaining)` can carry the information the inductive step needs.

Strengthening clause (c) with information about the *future* (like
"the next TwoSum step's `h` will be large enough") is also blocked:
that's a property of the algorithm's runtime behaviour, not a
state-level Prop.

## The collapse, formatted per Session 2's stopping condition

```
ROUTE 2 COLLAPSE

Candidate clause (c) attempted (final, strongest before bail):
  Definition cascade_invariant_handover
    (q : binary64) (remaining : list tagged_b64) : Prop :=
    let re := untag (filter (fun t => provenance_eq_dec (snd t) from_e)
                            remaining) in
    let rf := untag (filter (fun t => provenance_eq_dec (snd t) from_f)
                            remaining) in
    sorted_asc (q :: untag remaining) /\
    nonoverlap_shewchuk (rev re) /\
    nonoverlap_shewchuk (rev rf).

Goal state at bail point (the mixed-provenance preservation
sub-obligation, by paper analysis):

  -- Hypotheses --
  q, x : binary64
  p : provenance
  remaining' : list tagged_b64
  Hsa : sorted_asc (q :: x :: untag remaining')
  Hpe : nonoverlap_shewchuk (rev (untag (filter
                              (provenance_eq_dec (from_e)) ((x,p)::remaining'))))
  Hpf : nonoverlap_shewchuk (rev (untag (filter
                              (provenance_eq_dec (from_f)) ((x,p)::remaining'))))
  Hsafe : b64_TwoSum_safe x q
  (qnew, h) := b64_TwoSum x q

  -- Goal --
  sorted_asc (qnew :: untag remaining')

  Specifically, the head sub-goal:
    Rabs (B2R qnew) <= Rabs (B2R (head remaining').val)
  ... where `remaining' = (y, q_y) :: _` with `p_y` possibly differing
  from `p`.

Why this doesn't close:

The corpus has no upper-bound lemma on b64_plus.  The triangle bound
|qnew| <= |x| + |q| <= 2|x| is provable but insufficient: when
`p_y <> p` (mixed-provenance consecutive elements), `|y|` can be as
small as `|x|` (sorted_asc allows equality), so `2|x| > |y|` and the
goal is false in general.

The per-source nonoverlap hypotheses (Hpe, Hpf) carry the right
information in principle — they imply that `|y| >= 2^53 |x|` when `y`
and `x` are SAME-source consecutive — but the framework cannot tell
which source `x` came from versus which source `q` is bounded by,
because `q` is untagged.  The argument splits on `p` vs the provenance
of the previously-consumed input (the one that produced `q`'s current
value), and that previous provenance is not in the state.

Route 1 trigger:

The missing property, stated as a Coq Prop type that Route 1's
cascade-state augmentation would need to carry:

  Definition cascade_state_v1 : Type :=
    binary64 * provenance * list binary64.

  (* Or, as a Record matching the Route 1 design session's choice: *)
  Record cascade_state_v1 := mk_cs {
    cs_carry  : binary64;
    cs_prov   : provenance;
    cs_output : list binary64
  }.

With provenance attached to `q` (read: `cs_prov`), the inductive step
can case-split:

  Case (p_q = from_e, p_x = from_e): same-source consecutive in e.
    By nonoverlap_shewchuk e, the *previous* from_e input has
    |prev_e| >= 2^53 |q|.  TwoSum step's strict_succ_b64 absorption
    (Path A's b64_plus_under_pathA_dominance) applies directly.

  Case (p_q = from_e, p_x = from_f): mixed-provenance.  Both sides'
    individual chains constrain the relative magnitudes.  Shewchuk's
    Lemma 13's case analysis applies.

  Symmetric cases for (p_q = from_f, ...).
```

## Recommendations

  1. **Do not start Route 1 in this session.**  A fresh session with
     this artifact as its red-phase input is the correct procedure
     (per Session 2's stopping condition).  Route 1's design must
     additionally specify how `cs_prov` propagates through the
     cascade (it is not simply `p` of the last input, because the
     accumulator can absorb several from one source then one from
     another in a single cascade step's downstream effect on
     subsequent h's).

  2. **Re-examine §6.5's escape valve (compress).**  Route 2 could
     potentially be rescued if clause (a)'s `nonoverlap_shewchuk`
     compress filter handles the load-bearing case (h-zero or
     h-near-zero compress out, leaving a sparser sequence where the
     half-ulp chain holds for trivial reasons).  Verifying this
     would require concrete examples where mixed-provenance cascade
     steps reliably produce `h = 0` (which compress filters).  No
     evidence in the corpus suggests this; the `b64_TwoSum` error
     `h = round(x + q) - (x + q)` is generically non-zero.

  3. **Keep the Session 1 framework.**  `provenance`,
     `tagged_sort_by_abs`, `untag_tagged_input`, and the structural
     lemmas are Qed-closed and useful regardless of Route 1 vs Route
     2.  Route 1's cascade-state augmentation can build on these
     definitions directly.

## What is not in this artifact

This document does NOT contain Coq attempts of the candidate clauses.
Without local Coq toolchain access (Docker daemon unavailable in this
session), submitting partial proof attempts risks introducing CI
failures.  The analysis is paper analysis grounded in the
Qed-closed corpus's available lemmas and the proof-structure doc's
counterexamples.

Future sessions with Coq access can re-validate the analysis by
attempting Candidate 3 explicitly and observing the goal state at the
bail point.  The expected goal state matches the one above.
