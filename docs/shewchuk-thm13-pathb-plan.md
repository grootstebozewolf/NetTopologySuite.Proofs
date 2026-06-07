# Plan — widening `cascade_invariant_handover` to pathA ∨ pathB

**Status:** design / hypotheses only. No Coq proofs in this document. The goal
is to lay out, precisely and honestly, what it would take to discharge the
deferred headline `fast_expansion_sum_nonoverlap_shewchuk`
(`theories-flocq/B64_FastExpansionSum_Shewchuk.v:483`, Admitted) by widening the
Route-2 per-step invariant from pathA-only to **pathA ∨ pathB**, and what the
load-bearing open obligations are.

This builds directly on the merged pathB arithmetic brick
(`theories-flocq/B64_TwoSum_sterbenz.v`):
`b64_TwoSum_exact_of_format_sum` and `b64_TwoSum_sterbenz_exact`.

---

## 0. Recap of the framework (Route 2)

All references are to `theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v`
unless noted.

- **State** (`cascade_state`, L288): `{ cs_carry; cs_prov; cs_output;
  cs_e_max; cs_f_max }`. The cascade folds the magnitude-sorted, provenance-
  tagged merge of `e ++ f` (ascending `|·|`), accumulating a running high part
  `cs_carry` and emitting low parts into `cs_output`.

- **Step** (`cascade_step_state`, L494): for the next tagged input `(x, prov)`,
  ```
  carry'  := fst (b64_TwoSum x cs_carry)
  output' := cs_output ++ [ snd (b64_TwoSum x cs_carry) ]
  (cs_e_max / cs_f_max) updated to x on the matching source
  ```

- **Invariant** (`cascade_invariant`, L384) = three clauses:
  - (a) `cascade_invariant_output` (L312):
    `nonoverlap_shewchuk (cs_carry :: rev cs_output)`.
  - (handover) `cascade_invariant_handover` (L340): for the *next* input
    `(x,_)`, `b64_TwoSum_safe x cs_carry` **and** a 5-way disjunction on the
    signs/magnitudes of `cs_carry` (`q`) and `x` — the **pathA conditions**:
    same-sign-pos, same-sign-neg, `q = 0`, or one of two half-ulp
    "absorption" cases.
  - (run-bound) `cascade_invariant_run_bound` (L373): `|cs_carry| ≤
    2|cs_e_max| + 2|cs_f_max|`.

- **Per-step chain** (`cascade_pathA_chain`, L1514): recursive predicate
  asserting that *every* step from a state satisfies pathA's full hypotheses
  (sign + `strict_succ_pathA_R` / half-ulp, within-source bound, normal-range
  bounds, handover-for-next), and recursively on the stepped state.

- **Lift** (`cascade_run_preserves_invariant_under_pathA`, L1552, Qed) +
  **output** (`cascade_run_output_nonoverlap`, L1584, Qed): under the chain,
  the invariant survives the whole run, so clause (a) on the final state gives
  `nonoverlap_shewchuk` of the output — which is `fast_expansion_sum`'s output.

- **Conditional headline** (`..._general_conditional`, L2196, Qed): the headline
  follows *if* `cascade_pathA_chain (initial_cascade_state x prov) rest` holds.

- **`nonoverlap_shewchuk`** (`B64_Expansion_Shewchuk.v:98`):
  `nonoverlap_strict (compress e)`, where `compress` (L80) drops every element
  with `B2R = 0`. **Internal zeros are free.**

### The verified defect

`theories-flocq/B64_Shewchuk_Thm13_pathA_defect.v` proves (Qed)
`cascade_handover_fails_mixed_sign`: the handover disjunction is **unsatisfiable**
when `0 < B2R x_carry`, `B2R x2 < 0`, and `½·ulp(succ(B2R x2)) ≤ B2R x_carry` —
i.e. a cross-source, opposite-sign, similar-magnitude pair. Concrete witness:
`e=[1.0]`, `f=[-1.0]`. So `cascade_pathA_chain` is *not derivable* from
`nonoverlap` inputs, and the pathA-only reduction is a dead end. The headline
itself is true; the per-step invariant must be widened.

---

## 1. The pathB case, characterised

**pathB fires exactly when pathA's disjunction fails**: `x` and `cs_carry`
opposite sign, similar magnitude (neither half-ulp-dominates the other). The
defining arithmetic fact (now proven) is that such a `b64_TwoSum` is *exact*:

```
b64_TwoSum_sterbenz_exact :
  b64_TwoSum_safe x q ->
  (-B2R q)/2 <= B2R x <= 2*(-B2R q)        (* opposite sign, Sterbenz range *)
  -> let '(a,b) := b64_TwoSum x q in
     B2R a = B2R x + B2R q  /\  B2R b = 0.
```

So a pathB step:
- emits `snd = 0` into the output (which `compress` deletes — clause (a) is
  undisturbed *on the tail*), and
- sets `carry' = x + q` **exactly**, with `|carry'| < max(|x|,|q|)` (genuine
  cancellation).

The symmetric orientation (`x < 0 < q`) needs the mirror lemma
`b64_TwoSum_sterbenz_exact_neg` (not yet written; trivial mirror of the
existing one, see §5).

---

## 2. Proposed definitions

### 2.1 pathB step predicate (the trigger)

```coq
(* HYPOTHESIS — not yet in Coq *)
Definition cascade_step_pathB (state : cascade_state) (x : binary64) : Prop :=
  b64_TwoSum_safe x (cs_carry state) /\
  b64_format (B2R x + B2R (cs_carry state)).   (* exact sum -> snd = 0 *)
```

Stating the trigger as "the exact sum is representable" (rather than the
Sterbenz inequality) is deliberately more general: it is exactly the hypothesis
of `b64_TwoSum_exact_of_format_sum`, and it is what the completeness argument
(§4.B) must actually supply. Sterbenz range is the *sufficient condition* that
discharges it for the opposite-sign similar-magnitude case.

### 2.2 widened per-step chain

```coq
(* HYPOTHESIS — replaces cascade_pathA_chain at the chain sites *)
Fixpoint cascade_pathAB_chain (state : cascade_state) (xs : list tagged_b64) : Prop :=
  match xs with
  | nil => True
  | (x, prov) :: rest =>
      ( cascade_step_pathA_conditions state x prov          (* the old L1519-1545 body *)
        \/ cascade_step_pathB state x ) /\
      cascade_invariant_handover_AB (cascade_step_state state x prov) rest /\
      cascade_pathAB_chain (cascade_step_state state x prov) rest
  end.
```

### 2.3 widened handover (clause used by the *next* step)

`cascade_invariant_handover` (L340) must gain a sixth disjunct so the state
*after* a pathB step still satisfies "the next step is pathA-or-pathB". The
cleanest form mirrors §2.2: the next pair is either in a pathA disjunct **or**
has a representable exact sum.

```coq
(* HYPOTHESIS *)
Definition cascade_invariant_handover_AB (state : cascade_state)
                                         (remaining : list tagged_b64) : Prop :=
  match remaining with
  | nil => True
  | (x,_) :: _ =>
      b64_TwoSum_safe x (cs_carry state) /\
      ( <the existing 5-way pathA disjunction, L348-357>
        \/ b64_format (B2R x + B2R (cs_carry state)) )
  end.
```

---

## 3. Proof obligations

Numbered; each is a *proposed statement* (a hypothesis), not a proof. The two
existing Qed lemmas they replace are noted.

**O1 — pathB step preserves clause (a).**
```coq
Lemma cascade_step_pathB_preserves_output :
  forall state x prov,
    cascade_invariant_output (cs_carry state) (cs_output state) ->
    cascade_step_pathB state x ->
    <DOMINANCE PRECONDITION, see §4.A> ->
    cascade_invariant_output
      (cs_carry (cascade_step_state state x prov))
      (cs_output (cascade_step_state state x prov)).
```
Mechanism: `snd = 0` so the appended output element is dropped by `compress`;
`carry' = x + q`. Reduces to `nonoverlap_strict (carry' :: compress (rev
cs_output))` given `nonoverlap_strict (q :: compress (rev cs_output))`. **This
is the crux — see §4.A.** Reuses `compress` drop-zero behaviour and
`nonoverlap_shewchuk_first_then_zeros` (L1631).

**O2 — pathB step preserves the handover (for the next step).**
```coq
Lemma cascade_step_pathB_preserves_handover :
  forall state x prov rest,
    cascade_invariant_handover_AB state ((x,prov) :: rest) ->
    cascade_step_pathB state x ->
    cascade_invariant_handover_AB (cascade_step_state state x prov) rest.
```
Needs: the new carry `x+q` together with the *following* input `x'` is again
pathA-or-pathB. Depends on the sorted-ascending processing order (§4.B).

**O3 — pathB step preserves the run-bound.**
```coq
Lemma cascade_step_pathB_preserves_run_bound :
  forall state x prov,
    cascade_invariant_run_bound state ->
    cascade_step_pathB state x ->
    cascade_invariant_run_bound (cascade_step_state state x prov).
```
Likely easy: `|carry'| = |x+q| ≤ |x| + |q| ≤ |x| + (2|cs_e_max|+2|cs_f_max|)`,
and `x` becomes the new source max, so the RHS grows to cover it. (Mirror of the
existing pathA run-bound lemma at L791.)

**O4 — combined single-step preservation.**
```coq
Lemma cascade_step_preserves_invariant_AB :
  forall state processed x prov rest,
    cascade_invariant state processed ((x,prov)::rest) ->
    ( cascade_step_pathA_conditions state x prov \/ cascade_step_pathB state x ) ->
    cascade_invariant (cascade_step_state state x prov) (processed++[x]) rest.
```
Case split: pathA branch = existing `cascade_step_preserves_invariant_pathA`
(L1332, Qed); pathB branch = O1 ∧ O2 ∧ O3.

**O5 — run lift (mechanical, copy of L1552).**
```coq
Lemma cascade_run_preserves_invariant_under_pathAB :
  forall xs state processed,
    cascade_invariant state processed xs ->
    cascade_pathAB_chain state xs ->
    cascade_invariant (cascade_run state xs) (processed ++ untag xs) nil.
```
Identical induction to L1552, calling O4 instead of the pathA-only step lemma.

**O6 — output (mechanical, copy of L1584).**
```coq
Lemma cascade_run_output_nonoverlap_AB :
  forall init_state tagged_rest,
    cascade_invariant init_state nil tagged_rest ->
    cascade_pathAB_chain init_state tagged_rest ->
    nonoverlap_shewchuk
      (cs_carry (cascade_run init_state tagged_rest)
       :: rev (cs_output (cascade_run init_state tagged_rest))).
```

**O7 — completeness: discharge the chain from the real preconditions.**
```coq
Lemma cascade_pathAB_chain_from_nonoverlap :
  forall e f x prov rest,
    fast_expansion_sum_safe e f ->
    nonoverlap_shewchuk e -> nonoverlap_shewchuk f ->
    tagged_input e f = (x,prov)::rest ->
    cascade_pathAB_chain (initial_cascade_state x prov) rest.
```
**This is the second crux — see §4.B.** It is the obligation that pathA alone
*provably could not satisfy* (the defect). The whole point of pathB is to make
this true.

**O8 — rewire the headline.**
Replace `cascade_pathA_chain` with `cascade_pathAB_chain` in
`..._general_conditional` (L2196), then compose with O7 to close
`fast_expansion_sum_nonoverlap_shewchuk` unconditionally.

---

## 4. The hard sub-problems (honest risk)

### §4.A — clause (a) under cancellation (O1)

After a pathB step, the chain to re-establish is
`nonoverlap_strict (carry' :: compress (rev cs_output))` with `carry' = x + q`
**smaller** than `q`. The old invariant gave `nonoverlap_strict (q :: compress
(rev cs_output))`, i.e. `q` strict-succ-dominates the head `h` of `compress (rev
cs_output)`. Because `carry'` can be *much smaller* than `q`, the relation
`strict_succ carry' h` does **not** follow for free — it can fail.

This is the genuine mathematical content. Candidate resolutions, in order of
preference:

1. **All-zero-output regime.** If every prior step in the current cancellation
   run was pathB, then `compress (rev cs_output) = nil` and the goal is
   `nonoverlap_strict (carry' :: nil)` = trivially true
   (`nonoverlap_shewchuk_first_then_zeros`, L1631, already does this). The
   hypothesis is that *cancellation steps cluster*: once the carry collapses, it
   stays below the next inputs and emits zeros until it is absorbed. **Likely
   the real structure**, but needs an added invariant clause (see below).

2. **Strengthen the invariant** with a clause tying `cs_carry` to a dominance
   margin over `compress (rev cs_output)` that is *preserved* by both pathA and
   pathB. This is the Shewchuk "strongly nonoverlapping" content; it is the part
   the corpus estimates at multi-day.

3. **Re-root** the chain: treat `carry'` as a fresh smallest element. Only sound
   if `carry'` is below every output component — i.e. resolution 1 in disguise.

**Open question to settle first (no Coq):** trace `fast_expansion_sum` on
`e=[1.0, 2^60]`, `f=[-1.0]` (and a few cross-sign nonoverlapping pairs) by hand,
recording `(cs_carry, cs_output)` at each step, to confirm whether cancellation
steps always occur with all-zero output-so-far (resolution 1) or genuinely
interleave (forcing resolution 2).

### §4.B — completeness of pathA ∨ pathB (O7)

Must show: at every reachable step, the `(x, cs_carry)` pair is in a pathA
disjunct **or** has a representable exact sum. Case analysis on signs and the
sorted-ascending magnitude order:

- **same sign** → a pathA same-sign disjunct (existing).
- **opposite sign, one dominates by ≥ half-ulp** → a pathA half-ulp disjunct
  (existing).
- **opposite sign, similar magnitude** → Sterbenz range holds ⇒ exact sum ⇒
  pathB. **This is the case the defect exhibits**; the obligation is to show
  Sterbenz range (`|q|/2 ≤ |x| ≤ 2|q|`) actually holds here, from "neither
  half-ulp-dominates". Half-ulp non-domination gives a *much* tighter bound than
  Sterbenz's factor-2 window, so this implication is plausible but must be
  proven (it is essentially: "not (≥53-bit-separated) ⇒ within factor 2").

Risk: the boundary between "half-ulp dominates" (pathA) and "Sterbenz range"
(pathB) must *cover* all opposite-sign configurations with no gap. A gap would
mean a third case needing a pathC.

### §4.C — the handover after pathB (O2)

The next input `x'` (sorted, `|x'| ≥ |x|`) versus the collapsed `carry' = x+q`
(small). Because `|carry'|` is small and `|x'|` is large, this is *most likely*
a pathA half-ulp absorption (carry' is ≪ x', so it is dominated) — i.e. pathB
tends to hand back to pathA. Proving this uses the sorted order and the run-bound.

---

## 5. Reusable bricks already in the corpus

| Need | Existing (file:lemma) | Status |
|---|---|---|
| pathB exact sum, snd = 0 | `B64_TwoSum_sterbenz.v:b64_TwoSum_sterbenz_exact` | Qed (#135) |
| pathB exact sum (format form) | `B64_TwoSum_sterbenz.v:b64_TwoSum_exact_of_format_sum` | Qed (#135) |
| Sterbenz → format | Flocq `Prop.Sterbenz.sterbenz` | available |
| compress drops zeros | `B64_Expansion_Shewchuk.v` (compress def) | Qed |
| zero-tail ⇒ nonoverlap | `Route2:nonoverlap_shewchuk_first_then_zeros` (L1631) | Qed |
| all-zero ⇒ compress nil | `Route2:compress_all_zero_nil` (L1615) | Qed |
| pathA single-step preservation | `Route2:cascade_step_preserves_invariant_pathA` (L1332) | Qed |
| run lift / output (templates) | `Route2:cascade_run_*` (L1552, L1584) | Qed |
| run-bound step (template) | `Route2` run-bound lemma (L791) | Qed |

**Missing trivial brick:** `b64_TwoSum_sterbenz_exact_neg` (mirror for `x<0<q`).
~10 lines, same proof as the positive case with `generic_format_opp`.

---

## 6. Recommended sequencing

1. **Settle §4.A by hand-tracing** (no Coq). Decide resolution 1 vs 2. This gates
   the entire invariant shape — do it first.
2. Add `b64_TwoSum_sterbenz_exact_neg` (trivial).
3. Define `cascade_step_pathB`, `cascade_invariant_handover_AB`,
   `cascade_pathAB_chain` (§2). If §4.A forces an extra invariant clause, add it
   to `cascade_invariant` now and re-confirm the existing pathA lemmas still
   close (they should, being strictly more constrained).
4. O3 (run-bound, easy) → O2 (handover, medium) → **O1 (clause a, hard)**.
5. O4 (case-split) → O5, O6 (mechanical copies).
6. **O7 (completeness, hard)** — the §4.B case analysis.
7. O8 (rewire headline).

**Effort estimate (unchanged from the proof-structure doc):** ~200–400 lines,
2–3 focused days, *conditional on §4.A resolving to resolution 1*. If resolution
2 (strengthened dominance invariant) is required, add substantially more — this
is the genuinely thesis-scale branch.

**Smallest safe next step that is still Coq:** `b64_TwoSum_sterbenz_exact_neg`
plus the three definitions in §2 (no preservation proofs yet) — these compile
independently and let O3–O7 be attempted incrementally without committing to the
invariant shape before §4.A is settled.
