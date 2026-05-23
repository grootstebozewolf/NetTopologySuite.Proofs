# Stage D chain composition — design choice for nonoverlap preservation

**Status**: Design committed (Approach A). Proof deferred to follow-up
session.
**Date**: 2026-05-23
**Context**: Slice `b64_TwoSum_chain3_nonoverlap` (Stage D critical path,
listed in `docs/stage-d-feasibility.md` 2026-05-16 update as the
"genuinely new content" tangent).

## 1. The design choice

`b64_TwoSum_chain3` (defined in `theories-flocq/B64_Pff_bridge.v:599`) is:

```
(s1, e1) := b64_TwoSum a b   (* s1 + e1 = a + b exactly *)
(s2, e2) := b64_TwoSum s1 c  (* s2 + e2 = s1 + c exactly *)
chain3 a b c := (s2, e2, e1)
```

Sum correctness is Qed-closed (`b64_TwoSum_chain3_correct`). What is
**not** Qed-closed — and is the architectural prerequisite for
`b64_orient2d_exact_sign_correct` — is that the triple `[s2; e2; e1]`
satisfies `nonoverlap_strict` (defined in `theories-flocq/B64_Expansion.v`).

Two approaches were considered before any proof attempt. This doc
records the design survey, the decision, and the artifacts the next
session needs.

## 2. The design survey

Source files consulted:

  - `theories-flocq/B64_bridge.v` — `b64_coord_safe`,
    `b64_safe_minus_of_bounded`, `b64_mult_bounded_R`.
  - `theories-flocq/Orient_b64_R.v` — `b64_orient2d_inputs_safe`.
  - `theories-flocq/B64_Expansion.v` — `nonoverlap_strict`,
    `strict_succ_b64`, `sign_of_expansion_correct`.
  - `theories-flocq/B64_Pff_bridge.v` — `b64_TwoSum_nonoverlap`,
    `b64_TwoSum_chain3`, `b64_TwoSum_chain3_correct`.

### Survey question 1 — tightest input bound under `b64_orient2d_inputs_safe`

`b64_safe_coord_bound = bpow radix2 500` (B64_bridge.v:363). So each
coordinate satisfies `|B2R coord| ≤ 2^500`.

### Survey question 2 — tightest bound on `e1` after one TwoSum

`b64_TwoSum_nonoverlap` (B64_Pff_bridge.v:490) gives
`|B2R e1| ≤ ulp (B2R s1) / 2` unconditionally (under the six per-op
safety preconditions). With `|s1| ≤ 2^501`, the worst case is
`|e1| ≤ 2^447`; the tight pointwise form is `|e1| ≤ |s1| · 2^(-53)`.

### Survey question 3 — tightest bound on `e2` after a second TwoSum

By the same lemma applied to `b64_TwoSum s1 c`,
`|B2R e2| ≤ ulp (B2R s2) / 2`. With `|s2| ≤ 2^502`, the worst case is
`|e2| ≤ 2^449`; the tight form is `|e2| ≤ |s2| · 2^(-53)`.

**Critically: `|e2|` can be 0**, when `b64_plus s1 c` is exact. The
upper bound has no matching lower bound.

### Survey question 4 — does the bound on `e1` imply `|e1| ≤ ulp(e2)/2`?

**No.** The pathology is structural, not just a side condition.

Concretely: `|e1| ≤ ulp(s1)/2` ≈ `|s1| · 2^(-53)`. The nonoverlap
obligation requires `|e1| ≤ ulp(e2)/2` ≈ `|e2| · 2^(-53)`. Equivalent
to: `|e2|` must be at least the size of `|s1|`. But typically
`|s1| ≈ |s2|` (since `s2 = round(s1 + c)`) and `|e2| ≪ |s2|`, so this
fails by a factor of `2^53` or more.

The pathological case is direct to construct:

  - Take `a, b` such that `(s1, e1) = b64_TwoSum a b` produces a
    non-zero `e1` of magnitude ≈ `ulp(s1)/2`.
  - Take `c = -s1`. Then `b64_plus s1 c = 0` exactly, so `s2 = 0` and
    `e2 = 0`.
  - The chain3 output is `(0, 0, e1)`. For `nonoverlap_strict` we'd
    need `|e1| ≤ ulp(0)/2 = bpow emin / 2 ≈ 2^(-1075)`. The actual
    `|e1|` is many orders of magnitude larger. Fails.

There is no magnitude precondition compatible with
`b64_orient2d_inputs_safe` that excludes this case. The integer regime
(`coord_int_safe`, `|coord| ≤ 2^25` integer-valued) trivially satisfies
nonoverlap because all operations are exact and `e1 = e2 = 0` — but
that is the trivial regime where the expansion is not needed at all,
so it does not unblock the headline.

## 3. The decision: Approach A (Shewchuk's fast-expansion-sum)

Approach B (bounded-magnitude compress) is ruled out by the survey:
the magnitude bound required for nonoverlap-by-construction is
incompatible with the safety predicate infrastructure, and the only
regime where it holds by construction (integer regime, exactness) is
the regime where no expansion arithmetic is needed.

Approach A — formalising Shewchuk's expansion-sum primitive — is the
remaining path. The cost is larger (the merge predicate and Fast2Sum
cascade have to be defined and the invariant proof has to thread
magnitude bookkeeping through the cascade), but it produces a
general-purpose tool reusable for `b64_DekkerPair_nonoverlap` and any
future expansion composition.

## 4. The merge predicate

The chain3 use case is specifically: take a 2-element nonoverlapping
expansion `[s1; e1]` (from the first TwoSum) and grow it by adding a
single binary64 `c`. This is exactly Shewchuk's `GROW-EXPANSION`
primitive (Shewchuk 1997, Algorithm 3.1; Boldo-Daumas-Muller refer to
it as the `Add` primitive).

Pen-and-paper algorithm (Shewchuk Figure 3):

```
GROW-EXPANSION(e[1..n], b)
  Q_0 := b
  for i := 1 to n:
    (Q_i, h_i) := TwoSum(e_i, Q_{i-1})    (* e_i is the i-th component, smallest first *)
  h_{n+1} := Q_n
  return [h_{n+1}, h_n, ..., h_1]          (* largest first *)
```

The expansion `e` is iterated **smallest magnitude first**. Each TwoSum
captures the round-off into the next `h_i`. The accumulator `Q` carries
the running high part. Final output is the chain `[Q_n; h_n; ...; h_1]`
in decreasing magnitude order, which is the convention of our
`nonoverlap_strict` (`|h_i| ≤ ulp(h_{i+1}) / 2` between adjacent
components).

For chain3, the call is `grow_expansion [s1; e1] c`:

  - Input expansion `[s1; e1]` (in our `nonoverlap_strict` convention,
    largest first).
  - Reverse to `[e1; s1]` (smallest first), as the algorithm expects.
  - `(Q_1, h_1) := TwoSum(e1, c)`.
  - `(Q_2, h_2) := TwoSum(s1, Q_1)`.
  - `h_3 := Q_2`.
  - Return `[h_3; h_2; h_1]` (largest first).

Note that this is **structurally different** from the naive chain3's
output `(s2, e2, e1)`. The two algorithms produce expansions with the
same exact sum but different component orderings; chain3 is the
"plain" composition while `grow_expansion` re-sorts via the cascade.

## 5. Coq formulation

A scaffolding file `theories-flocq/B64_FastExpansionSum.v` lands in
this session with the definitions and theorem statements. Both
theorems are `Admitted` with `(* TANGENT: proof deferred pending
design validation *)` markers. CI's Qed-invariant grep flags this;
the flag is the correct behaviour and is acknowledged in the
companion commit message.

The file ships:

  - `b64_grow_expansion_aux : binary64 -> list binary64 -> list binary64 * binary64`
    — the cascade body.
  - `b64_grow_expansion : list binary64 -> binary64 -> list binary64`
    — the top-level entry point (reverses, cascades, re-orders).
  - Statement: `b64_grow_expansion_correct` — sum preservation.
  - Statement: `b64_grow_expansion_nonoverlap` — `nonoverlap_strict`
    preserved.

The naive `b64_TwoSum_chain3` is **not** modified. Its sum-correctness
theorem stays Qed-closed; its lack of `nonoverlap_strict` is now
documented as expected, with `b64_grow_expansion` as the
replacement entry point for nonoverlap-requiring consumers.

## 6. Proof plan (deferred)

`b64_grow_expansion_correct` (sum preservation) is straightforward:
each TwoSum in the cascade preserves the running sum exactly, so the
chain output sums to `expansion_R e + B2R b`. Direct induction on `e`.

`b64_grow_expansion_nonoverlap` (the load-bearing theorem) needs an
invariant of the form:

  - The accumulator `Q_i` satisfies `|Q_i| ≥ |e_{i+1}|` at every step
    (so the next TwoSum's nonoverlap bound holds in the right
    direction).
  - The `h_i` outputs of each TwoSum satisfy
    `|h_i| ≤ ulp(Q_i) / 2`, and `|Q_i| ≥ |Q_{i+1}|` so the chain of
    `h_i`s forms a strictly decreasing magnitude sequence.

The exact invariant statement is part of the next session's proof
work. Shewchuk's Theorem 13 (in the 1997 paper) and the BJMP ITP 2017
formalisation of `Add` (HAL hal-01512417 §4) are the references.

## 7. Tangent prediction (for the next session)

Most likely friction: the cascade invariant requires reasoning about
the magnitude ordering of `Q_i` relative to `e_{i+1}`, which is not
automatic from `nonoverlap_strict` on `e` alone. The invariant
statement may need restructuring once the proof is attempted. If the
first non-trivial structural lemma about the invariant takes more
than one session, the invariant formulation is probably wrong and a
re-statement (rather than push-through) is the right move.

## 8. Stopping condition reached

This session is a **clean-stop Approach A design commit**. The
deliverable is:

  - This scoping doc (rationale + algorithm + theorem statements).
  - The companion Coq file `theories-flocq/B64_FastExpansionSum.v`
    with Admitted theorem statements and explicit TANGENT markers.

The next session picks up by attempting the proofs in the Coq file.

## 9. 2026-05-23 update: Options A and B both insufficient — Option C is the active path

This doc's original framing (Approach A: Shewchuk's fast-expansion-sum;
Approach B: bounded-magnitude compress) committed to the
`b64_grow_expansion` algorithm with `b64_TwoSum` as the cascade body,
and proposed two design knobs for the nonoverlap predicate.  The
follow-up proof sessions surfaced obstructions to both knobs:

  - **Sum-correctness landed** (commit `e54b9da`): the cascade's
    arithmetic invariant is preserved exactly by every `b64_TwoSum`
    step.  Qed-closed.

  - **`nonoverlap_strict` (commit `c521d06`)**: counterexample showed
    the predicate is incompatible with the algorithm — internal zeros
    in the cascade output, which `nonoverlap_strict` cannot tolerate.

  - **`compress` (commit `937955c`)**: counterexample showed even
    after filtering zeros, the compressed output can violate
    `nonoverlap_strict` and even Shewchuk's basic non-overlap.  Root
    cause: the cascade with `b64_TwoSum` (no magnitude precondition)
    does not preserve any meaningful nonoverlap predicate in
    cancellation cases.

Full diagnosis and the two Coq-verified counterexamples are in
`docs/stage-d-grow-expansion-nonoverlap-tangent.md` §3 and §9.

### Option C: redesign with Fast2Sum + magnitude precondition

Shewchuk's GROW-EXPANSION as actually formalised in his 1997 paper
uses `Fast2Sum` (with `|Q| >= |e_i|` precondition), not `TwoSum`.  The
TwoSum-based version we landed in `e54b9da` is sufficient for
sum-correctness but not for any structural nonoverlap claim.

The next session implements `b64_grow_expansion_fast` using
`b64_Fast2Sum_correct` (already lifted in
`theories-flocq/B64_Pff_bridge.v`), with the magnitude precondition
derived from the input expansion's structure.  Sum-correctness carries
over from the existing proof (minor adjustment for Fast2Sum's
safety-conjunct shape).

The proof of `b64_grow_expansion_fast_nonoverlap` follows Shewchuk
Theorem 13's structure: induction on the cascade, with the magnitude
precondition giving the chain `ulp(Q_i) <= ulp(h_{i+1})` needed to
close the half-ulp bound.

### Implication for the corpus

`b64_TwoSum_chain3_sorted` and `b64_grow_expansion` (the entry points
introduced in commit `22b6ffe`) are retained as the sum-correctness
entry points.  A parallel `_fast` variant is added for nonoverlap-
requiring consumers, with appropriate magnitude precondition.  No
existing Qed-closed theorem is invalidated.

### Status

The chain-composition slice continues to be the substantive
engagement on Stage D's critical path.  The work has been
**re-scoped** from "make the predicate-or-compress design choice"
to "implement the magnitude-preserving Fast2Sum variant and prove
its nonoverlap structurally".
