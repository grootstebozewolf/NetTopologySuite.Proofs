# Slice A Piece 5b Route 1 — design session artifact

**Session.** Route 1 design session for closing
`fast_expansion_sum_nonoverlap_shewchuk`.  Branch
`claude/cascade-step-preserves-invariant-UMNgF`.

**Stopping condition reached.** **Container unavailable** (red phase
only) **+** **Task 3 finds a missing property** (stop, third design
session needed).

This document is the red-phase artifact required by both stopping
conditions.  Tasks 1-4 are completed as paper analysis.  No Coq
attempt was committed; the Dockerfile's `apt-get update` step is
blocked by the network policy (Debian repos return 403, opam repos
unreachable), so the container build fails before Flocq is installed.

## Environment status

  - Docker daemon: available (`dockerd` started in this session,
    cleaned up before commit).
  - `rocq/rocq-prover:9.1.1-ocaml-4.14.2-flambda` image: pulled
    successfully (1.05 GB).  Confirmed Rocq + bignums + stdlib
    present; **Flocq not pre-installed**.
  - Dockerfile's setup steps (apt-get + opam install coq-flocq.4.2.2):
    fail.  apt-get returns `403 Forbidden` for
    `http://deb.debian.org/...`; opam returns `curl exited with code
    60` for `https://coq.inria.fr/opam/released/...`.  Both
    repository hosts are blocked by the remote-execution
    environment's network policy.
  - **Conclusion**: green-phase Coq verification is not reachable in
    this session.  Per the prompt's "container unavailable" stopping
    condition, the red-phase paper analysis below is the deliverable.

## Task 1.  Modified `cascade_state` type definition

**Choice: Form B (record).**

```coq
Record cascade_state : Type := mk_cascade_state {
  cs_carry  : binary64;
  cs_prov   : provenance;
  cs_output : list binary64  (* smallest-first (oldest-first), per Session 1 convention *)
}.
```

**Reason for Form B over Form A:** the inductive proof of
`cascade_step_preserves_invariant` requires repeated case-splits on
`cs_prov` and frequent reference to `cs_carry`'s sign and magnitude.
Named accessors prevent positional-pattern-match bugs across the four
provenance combinations the proof generates.  The cost (writing
`mk_cascade_state` constructor calls instead of tuples) is paid once
in the bootstrap and once per Admitted placeholder; the proof body
benefits the most.

## Task 2.  Modified `cascade_invariant` with refined clause (c)

```coq
Definition cascade_invariant_output
  (q : binary64) (hs : list binary64) : Prop :=
  nonoverlap_shewchuk (q :: rev hs).

Definition cascade_invariant_magnitude
  (q : binary64) (processed : list binary64) : Prop :=
  Rabs (Binary.B2R prec emax q) <= max_abs_b64 processed
  \/ processed = nil.

(* Refined clause (c): the next TwoSum step is in the coverage of    *)
(* the b64_TwoSum_step_dominates_* family.  See Task 3 for the       *)
(* gap analysis.                                                     *)
Definition cascade_invariant_handover
  (state : cascade_state) (remaining : list tagged_b64) : Prop :=
  match remaining with
  | nil => True
  | (x, _) :: _ =>
      let q := cs_carry state in
      let qR := Binary.B2R prec emax q in
      let xR := Binary.B2R prec emax x in
      (* The next TwoSum step's dominance follows from one of: *)
      ((0 < xR /\ 0 < qR)                                      (* dominates_pos *)
       \/ (xR < 0 /\ qR < 0)                                   (* dominates_neg *)
       \/ qR = 0                                              (* dominates_q_zero *)
       \/ (0 < xR /\ Rabs qR <
              ulp radix2 (SpecFloat.fexp prec emax)
                (pred radix2 (SpecFloat.fexp prec emax) xR) / 2) (* strict_pos *)
       \/ (xR < 0 /\ Rabs qR <
              ulp radix2 (SpecFloat.fexp prec emax)
                (succ radix2 (SpecFloat.fexp prec emax) xR) / 2) (* strict_neg *)
      )
  end.

Definition cascade_invariant
  (state : cascade_state)
  (processed : list binary64)
  (remaining : list tagged_b64) : Prop :=
  cascade_invariant_output (cs_carry state) (cs_output state) /\
  cascade_invariant_magnitude (cs_carry state) processed /\
  cascade_invariant_handover state remaining.
```

**Note: this is NOT the candidate clause (c) from the prompt.**  The
prompt's candidate maps `(cs_prov, prov_x)` directly to the four
`b64_TwoSum_step_dominates_*` lemmas.  That mapping is structurally
incorrect (see Task 3).  The corrected form above case-splits on the
SIGN of the underlying `B2R` values, which is what the lemmas
actually require.  `cs_prov` and `prov_x` are still useful — they
provide magnitude information through the per-source nonoverlap chain
— but they don't pick the lemma directly.

### Does this resolve the Route 2 collapse trigger?

Partially.  The Route 2 collapse trigger was: `q` untagged → cannot
case-split.  Route 1 adds `cs_prov`, so the case-split on provenance
is now possible.  But the **substantive content** of clause (c)
turns out to be sign-based, not provenance-based, and provenance
does not by itself determine sign.

What `cs_prov` *does* unlock: when proving the inductive step's
preservation of clause (c), the four-way case-split on `(cs_prov,
prov_x)` lets us access **different magnitude bounds** for each case:

  - `(cs_prov, prov_x) = (from_e, from_e)`: same-source consecutive
    in `e`.  By `nonoverlap_shewchuk e` (in descending form), the
    next-larger element in `e` after the one that contributed to `q`
    has magnitude `>= 2^53 |q|`.  This gives `|q| <= ulp(pred xR)/2`
    (the `strict_pos`/`strict_neg` precondition) provided `q` was
    last absorbed from `e` and not subsequently modified by an `f`
    step at a comparable scale.

  - Same logic for `(from_f, from_f)`.

  - Mixed cases `(from_e, from_f)` and `(from_f, from_e)`: no
    cross-source magnitude bound.  `q` and `x` can have comparable
    magnitudes.  The strict precondition fails in general.

So `cs_prov` carries useful magnitude info for the *same-source*
case, but the *mixed-source* case still requires either sign
coincidence (pos/neg lemma applies) or a structurally new argument.

## Task 3.  Precondition check (Task 2 equivalent)

### What the four `b64_TwoSum_step_dominates_*` lemmas require

Read from `theories-flocq/B64_FastExpansionSum_Shewchuk.v` (lines
327-481), in their actual stated form:

```coq
(* All four lemmas conclude: |B2R q| <= |B2R (fst (b64_TwoSum e q))|.
   Read e := next input x, q := current cs_carry state.            *)

Lemma b64_TwoSum_step_dominates_pos :
  forall e q,
    0 < B2R e ->                       (* sign of input *)
    0 < B2R q ->                       (* sign of carry *)
    b64_TwoSum_safe e q ->
    ...

Lemma b64_TwoSum_step_dominates_neg :
  forall e q,
    B2R e < 0 ->                       (* sign of input *)
    B2R q < 0 ->                       (* sign of carry *)
    b64_TwoSum_safe e q ->
    ...

Lemma b64_TwoSum_step_dominates_strict_pos :
  forall e q,
    0 < B2R e ->                       (* sign of input *)
    Rabs (B2R q) <
      ulp radix2 (SpecFloat.fexp prec emax)
        (pred radix2 (SpecFloat.fexp prec emax) (B2R e)) / 2 ->  (* strict magnitude *)
    b64_TwoSum_safe e q ->
    ...

Lemma b64_TwoSum_step_dominates_strict_neg :
  forall e q,
    B2R e < 0 ->                       (* sign of input *)
    Rabs (B2R q) <
      ulp radix2 (SpecFloat.fexp prec emax)
        (succ radix2 (SpecFloat.fexp prec emax) (B2R e)) / 2 ->  (* strict magnitude *)
    b64_TwoSum_safe e q ->
    ...

(* Plus the trivial:                                                  *)
Lemma b64_TwoSum_step_dominates_q_zero :
  forall e q,
    B2R q = 0 -> ...                  (* carry is zero *)
```

**Preconditions case-split on**:

  - Sign of `B2R e` (the next input): `0 < B2R e` or `B2R e < 0`.
  - Sign of `B2R q` (the carry): `0 < B2R q` or `B2R q < 0` or `B2R q = 0`.
  - Strict magnitude: `|B2R q| < ulp(pred|succ B2R e) / 2`.

**Preconditions do NOT mention provenance.**  Provenance is the
mechanism by which we *derive* a sign or magnitude relationship, not
a precondition the lemmas accept.

### The structural mismatch in the prompt's candidate

The prompt's candidate (paraphrased):

```coq
match (cs_prov state, prov_x) with
| (from_e, from_e) => b64_TwoSum_step_dominates_pos_precond (cs_carry state) x
| (from_f, from_f) => b64_TwoSum_step_dominates_neg_precond (cs_carry state) x
| (from_e, from_f) => b64_TwoSum_step_dominates_strict_pos_precond (cs_carry state) x
| (from_f, from_e) => b64_TwoSum_step_dominates_strict_neg_precond (cs_carry state) x
end
```

This pairs `(from_e, from_e)` with the `_pos` lemma's preconditions
(`0 < B2R e /\ 0 < B2R q`).  But **`(from_e, from_e)` does not imply
positive signs**.  The input expansions `e` and `f` are signed
expansions of arbitrary reals (orient2d's input is real coordinates,
which include negatives); `from_e` elements can be negative.

Concretely: if `e = [-1.0]` (a one-element expansion representing
`-1.0`), then the tagged input has `(-1.0, from_e)`, and `B2R (-1.0)
< 0`.  The `_pos` lemma's `0 < B2R e` precondition is **false** for
this from_e element.

Similarly, the prompt's `(from_e, from_f) => strict_pos` arm
requires `0 < B2R e` for `strict_pos` to apply; mixed-provenance
does not guarantee this sign condition.

### Corrected case-split (what works, and where the gap is)

The correct case-split for the cascade preservation is on **sign of
`B2R x` and sign of `B2R cs_carry`**, with `cs_prov` and `prov_x`
providing supplementary **magnitude** information for the strict
preconditions.

```text
Case (sign B2R x, sign B2R cs_carry) | Lemma applies?          | Reasoning
-----------------------------------------------------------------------
(+, +)                              | pos                     | direct
(-, -)                              | neg                     | direct
(+, 0) or (-, 0)                    | q_zero                  | trivial
(+, -)                              | strict_neg(?)           | needs |q| < ulp(succ x)/2  ⚠
(-, +)                              | strict_pos(?)           | needs |q| < ulp(pred x)/2  ⚠
```

The `⚠` rows are the mixed-sign cases.  Their feasibility depends on
the magnitude bound on `|q|`, which **does** depend on provenance.

**Same-prov consecutive** (e.g., `(prov_q, prov_x) = (from_e, from_e)`):

  - `q` was last absorbed from the previous from_e element `x_prev_e`.
  - By `nonoverlap_shewchuk e` in descending form, `|x_curr_e| =
    |x| >= 2^53 |x_prev_e|`.
  - If no `from_f` elements were processed since `x_prev_e`
    (i.e., `x_prev_e` and `x_curr_e` are immediately consecutive in
    the sorted merge), then `|q| ≈ |x_prev_e| <= |x| * 2^-53`.
  - Need: `|q| < ulp(pred x)/2 ≈ |x| * 2^-53` (modulo binade
    boundaries).
  - **Bound holds with a tight factor.**  At the round-to-even
    boundary, the bound JUST FAILS by a factor of 2 — this is the
    boundary obstacle documented in
    `docs/stage-d-grow-expansion-nonoverlap-tangent.md` (the `|q| =
    ulp(e)/2` round-to-even tangent).

**Same-prov but f-element intervening**: e.g., sort order
`..., x_prev_e, x_intermediate_f, x_curr_e, ...`.

  - `q` was last absorbed from `x_intermediate_f` (the most recent
    step before this one).
  - `|x_intermediate_f|` can be comparable to `|x_curr_e|`
    (sorted_asc only guarantees `|x_intermediate_f| <= |x|`).
  - `|q|` can be as large as `2 * |x_intermediate_f| ≈ 2|x|`.
  - **`|q| < ulp(pred x)/2` fails.**

**Mixed-prov consecutive**: `(prov_q, prov_x) = (from_e, from_f)` or
symmetric.

  - Same as the f-intervening case: no cross-source magnitude
    bound.
  - `|q|` can be ≈ `|x|`.  Strict precondition fails.

### The missing property

For the mixed-sign cases where the strict precondition fails (rows
marked `⚠` in the table above, when `|q|` is not `<< ulp(x)/2`), the
corpus has **no `b64_TwoSum_step_dominates_*` lemma that applies**.

**Stated as a Coq Prop type, the missing lemma is:**

```coq
Lemma b64_TwoSum_step_dominates_mixed_sign_general :
  forall e q : binary64,
    (* No same-sign hypothesis. *)
    (* No strict magnitude precondition. *)
    Rabs (Binary.B2R prec emax q) <=
      2 * Rabs (Binary.B2R prec emax e) ->          (* triangle-like bound *)
    b64_TwoSum_safe e q ->
    Rabs (Binary.B2R prec emax q)
      <= Rabs (Binary.B2R prec emax (fst (b64_TwoSum e q))).
```

**Is this provable?**  No, **as a `_dominates_*` statement, it is
false in general**.  Mixed-sign similar-magnitude TwoSum cancels:
`|qnew|` can be much smaller than `|q|`, violating the conclusion.

Concrete counterexample (paper-derived):

  - `B2R e = 1.0`, `B2R q = -0.999999999...` (just below `1.0`).
  - `B2R e + B2R q ≈ 0.000000001`.  `qnew = round(e + q)` is tiny.
  - `|qnew| ≈ 10^-9`, `|q| ≈ 1.0`.  `|q| > |qnew|`, so the conclusion
    `|q| <= |qnew|` is **false**.

So this is not a missing-but-provable lemma; the conclusion (q
dominance) is **inappropriate** for the mixed-sign general case.

**What the cascade actually needs for nonoverlap preservation in
this case** is not q-dominance but a property about `h` (the error
term).  Specifically, the inductive step needs:

```coq
Lemma b64_TwoSum_h_chain :
  forall e q h_prev : binary64,
    (* Hypotheses about the previous cascade step's relationship    *)
    (* of h_prev to the previous q.                                 *)
    ...
    Rabs (Binary.B2R prec emax h_prev) <=
      ulp radix2 (SpecFloat.fexp prec emax)
        (Binary.B2R prec emax (snd (b64_TwoSum e q))) / 2.
```

This is **Shewchuk Theorem 13's deep magnitude bookkeeping**.  It is
the property that the entire Slice A Piece 5b is trying to
establish.  It is **not** a one-line corollary of the existing
`_dominates_*` family; it is a separate, structurally new theorem
about the consecutive cascade errors.

The missing property is therefore **not just one new TwoSum
dominance lemma** — it is **Shewchuk Theorem 13 itself**, restated
in cascade form.  Route 1's `cs_prov` augmentation is necessary
(provenance is genuinely needed in the proof) but **not sufficient**.

> ### ⬛ Key insight — the load-bearing recommendation for any successor session ⬛
>
> **The h-chain (consecutive cascade errors satisfying `|h_{k-1}| <=
> ulp(h_k) / 2`) cannot be encoded as an invariant clause.**  It is
> not a property of state; it is a property the cascade *step* must
> establish, with `cs_prov` and the per-source nonoverlap hypotheses
> available in proof context.
>
> Any third-design session should structure the proof as:
>
>   1. `cascade_invariant` carries only output-well-formed (clause a),
>      magnitude (clause b), and a **simple** clause (c) saying "next
>      step is safe to take".
>   2. The h-chain is a **separate cascade-step lemma**
>      (`cascade_h_chain`) that takes `cascade_invariant` + sort and
>      per-source nonoverlap hypotheses, applies the four-way
>      `(sign x, sign cs_carry)` case-split (with `cs_prov`
>      supplying the magnitude bound in same-source cases), and
>      establishes the new h's relationship to the previous h.
>
> Trying to fold the h-chain back into the invariant repeats Route 2's
> mistake at a different scale: any predicate strong enough to imply
> the h-chain needs information that does not propagate as a clean
> state predicate.

## Task 4.  Re-prove `cascade_invariant_empty` under modified definition

The initial state at the start of the cascade:

```coq
(* Bootstrap, conceptually.  In a session that does the green phase: *)
Definition cascade_state_initial (input : list tagged_b64) : option cascade_state :=
  match input with
  | nil => None
  | (x, p) :: _ =>
      Some (mk_cascade_state x p nil)
  end.
```

```coq
Lemma cascade_invariant_empty :
  forall (x : binary64) (p : provenance) (remaining : list tagged_b64),
    (* Hypothesis: clause (c) holds at the initial state for the next input. *)
    cascade_invariant_handover (mk_cascade_state x p nil)
      ((* the head of remaining, which is the first un-consumed input *)
       remaining) ->
    cascade_invariant (mk_cascade_state x p nil) nil remaining.
Proof.
  intros x p remaining Hhandover.
  unfold cascade_invariant.
  split; [|split].
  - (* (a) Output well-formed: cs_carry = x, cs_output = nil.
       nonoverlap_shewchuk (x :: rev nil) = nonoverlap_shewchuk [x]
       = nonoverlap_strict (compress [x]).  Single element, trivial. *)
    unfold cascade_invariant_output. cbn [rev].
    unfold nonoverlap_shewchuk. cbn [compress].
    destruct (Rcompare (Binary.B2R prec emax x) 0);
      cbn [nonoverlap_strict]; exact I.
  - (* (b) Magnitude: processed = nil, right branch of disjunction fires. *)
    right. reflexivity.
  - (* (c) Handover: given by hypothesis. *)
    exact Hhandover.
Qed.
```

**Verification by inspection**: the empty-state lemma's two
non-trivial clauses (a) and (b) are unchanged from Session 1's
proof (which is Qed-closed in
`B64_FastExpansionSum_Shewchuk_Route2.v` lines 289-308).  Clause
(c) is now a hypothesis rather than `True`, which is the right
shape: the **bootstrap session** (Session 3 of Route 1) must
discharge this hypothesis from the input preconditions.

**Bootstrap obligation (out of scope for this session)**:
`cascade_invariant_handover` for the initial state requires showing
that the head of `tagged_input e f` (the smallest element of the
sorted merge) together with the first un-consumed input fits in one
of the five disjunctive arms.  At the very start of the cascade,
`cs_carry` is just the smallest element of the merge; the second
smallest is the next input.  By `sort_by_abs_sorted`, `|cs_carry| <=
|next_input|`.  Whether the strict precondition or the sign
coincidence applies depends on specific input values; the bootstrap
needs case-analysis there.

### Task 4 conclusion

`cascade_invariant_empty` is **technically provable** under the
refined definition, but only after **adding the clause (c) handover
as a hypothesis**.  This is structurally different from Session 1's
version (which proved the lemma for ALL `q` and `remaining` because
clause (c) was vacuously `True`).

The bootstrap that calls `cascade_invariant_empty` will need to
establish the handover hypothesis from the input preconditions.
This is its own non-trivial sub-obligation.

## Stopping condition (formatted per the prompt's spec)

```
ROUTE 1 DESIGN — STOP AT TASK 3 (MISSING PROPERTY)

Task 1 result: cascade_state defined as Form B record with cs_carry,
cs_prov, cs_output.

Task 2 result: cascade_invariant_handover refined to the five-arm
disjunction over sign-and-magnitude preconditions of the four
b64_TwoSum_step_dominates_* lemmas + the q_zero corner case.  The
prompt's proposed (cs_prov, prov_x) -> lemma mapping is structurally
incorrect (provenance does not determine sign of B2R values); the
above corrected form is what works.

Task 3 result: The corrected clause (c) covers same-sign cases and
same-prov mixed-sign cases (the latter via strict_* with the
2^53-gap magnitude bound from within-source strict_succ).  It does
NOT cover:
  - Mixed-prov mixed-sign with |q| not strict-small.
  - Same-prov mixed-sign at the round-to-even boundary (|q| =
    ulp(e)/2, documented obstacle).

Missing property, stated as a Coq Prop type:

  Lemma b64_TwoSum_h_chain :
    forall e q : binary64,
      (* Conditions on the previous cascade step's h_prev *)
      ... ->
      forall h_prev : binary64,
      ... ->
      let '(qnew, h) := b64_TwoSum e q in
      Rabs (Binary.B2R prec emax h_prev) <=
        ulp radix2 (SpecFloat.fexp prec emax)
          (Binary.B2R prec emax h) / 2.

This IS Shewchuk Theorem 13's load-bearing claim, in cascade form:
the consecutive cascade errors satisfy a half-ulp chain.  Whether it
is derivable from nonoverlap_shewchuk e + nonoverlap_shewchuk f +
sort_by_abs_sorted + the existing dominates lemmas: this question
is exactly what Slice A Piece 5b set out to answer.  Paper analysis
in §4 of docs/shewchuk-theorem-13-proof-structure.md suggests it
follows from a delicate case-analysis on provenance + sign + binade
position; formalising it is the 200-400 line core of the proof.

Neither Route 2's nor Route 1's clause (c) framework provides a
shortcut to this claim.  cs_prov is necessary in the proof (so that
the case analysis can split on source), but it is not a clause that
fits "the invariant".  It is hypothesis context for the h-chain
lemma.

Recommendation: third design session (Route 1 variant).  Drop the
attempt to capture the h-chain inside cascade_invariant's clause
(c).  Instead, state the h-chain as a SEPARATE LEMMA, with cs_prov
provided by Route 1's cascade_state augmentation:

  Lemma cascade_h_chain :
    forall (state : cascade_state)
           (processed : list binary64)
           (remaining : list tagged_b64),
      cascade_invariant state processed remaining ->
      ... ->  (* sort/nonoverlap_shewchuk e/f hypotheses *)
      ... ->  (* per-step safety *)
      let new_state := cascade_step state remaining in
      ...

The h-chain lemma is what Session 2 of Route 1 should target,
under cascade_invariant + provenance + sort/nonoverlap hypotheses.
The invariant clause (c) reduces to:  "there is a next input, and
the next TwoSum step is safe" — much simpler than the disjunction
in Task 2.

This third design takes the productive structure from Route 1
(cs_prov) but stops trying to encode Shewchuk's deep magnitude
argument as an invariant.  Instead, the magnitude argument is a
separate proof obligation that the cascade step has direct access
to (via cs_prov + sort hypotheses).
```

## Updates to other artifacts (do NOT commit until container access)

The following updates were planned but **not made** in this
session, because the design has not been validated against Coq
compilation:

  - `docs/admitted-deferred-proofs.txt`: the
    `fast_expansion_sum_nonoverlap_shewchuk` entry's proof-structure
    pointer should be updated to reference Route 1's design (and
    eventually the third design).
  - `docs/shewchuk-theorem-13-proof-structure.md` §6: a §7 Route 1
    section documenting the cs_prov augmentation.  Deferred until a
    Route 1 implementation lands.

These are **documentation updates**, not Coq changes.  They can be
made in a follow-up commit once Route 1 (or its third-design
successor) lands a working framework.

## What carries over from this session

  1. **The Form B record choice for `cascade_state`** is defensible
     and useful regardless of which variant of Route 1 succeeds.
     `cs_prov` is a real bit of information that the cascade step
     needs access to.
  2. **The corrected case-split is sign-based, not provenance-based.**
     This insight should appear prominently in any successor
     session's red phase.
  3. **The h-chain claim is Shewchuk Theorem 13's actual content.**
     No clause (c) framework simplifies it; it must be proved as a
     separate cascade-step lemma.
  4. **The Route 2 framework** (`provenance`, `tagged_sort_by_abs`,
     `untag_tagged_input`, length lemmas) **stays as-is and is
     reused.**  Both Route 1 and the third-design variant build on
     it.

## What is not in this artifact

  - Coq attempts of any of the type changes.  The container build
    is blocked by the network policy (apt + opam repos return
    403/curl-60 errors), and committing un-compiled Coq risks CI
    failures or invariant violations.
  - Updated `admitted-deferred-proofs.txt` and proof-structure doc
    §6.  These wait for the green-phase landing.

A future session with container access can take this artifact as
input, validate the Form B definition against the Rocq compiler,
and proceed to write the `cascade_h_chain` lemma directly.
