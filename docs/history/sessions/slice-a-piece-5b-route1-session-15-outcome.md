# Slice A Piece 5b Route 1 Session 15 — outcome

**Session.** Route 1 Session 15: inductive int-safe cascade lemma.
Generalises Session 13's one-step `snd = 0` result to the entire
cascade.  Branch `claude/cascade-invariant-bootstrap-8oSDv`.

**Outcome.** TWO DELIVERABLES LANDED.  The inductive cascade lemma
generalises Session 13's foundational result and is the
load-bearing piece for extending the int-safe headline to
multi-element inputs.

## Deliverables landed

### `sum_abs_int_witnesses_nonneg` (Qed-closed)

```coq
Lemma sum_abs_int_witnesses_nonneg :
  forall ns, (0 <= sum_abs_int_witnesses ns)%Z.
```

Trivial helper: the sum of absolute values of integer witnesses is
non-negative.  Three-line induction.

### `b64_grow_expansion_aux_int_zero_hs` (Qed-closed)

The inductive cascade lemma:

```coq
Lemma b64_grow_expansion_aux_int_zero_hs :
  forall (xs : list binary64) (q : binary64) (nq : Z) (ns : list Z),
    is_finite q = true ->
    B2R q = IZR nq ->
    Forall2 (fun x n => is_finite x = true /\ B2R x = IZR n) xs ns ->
    (Z.abs nq + sum_abs_int_witnesses ns <= 2 ^ prec)%Z ->
    b64_grow_expansion_aux_safe q xs ->
    Forall (fun h => B2R h = 0) (fst (b64_grow_expansion_aux q xs)).
```

**Inductive proof** (~30 lines):

  - Base: `xs = nil`.  Cascade returns `(nil, q)`.  `Forall` on `nil`
    is trivial.
  - Step: `xs = x :: xs'`.  
    1. Destruct `ns` to extract `n0 :: ns0` (using `inversion Hfa2`).
    2. Sum-bound on `|n0 + nq|` ≤ `2^prec` via triangle inequality +
       `sum_abs_int_witnesses_nonneg`.
    3. Apply `b64_TwoSum_snd_B2R_zero_under_int_exact` (Session 13)
       to get `B2R snd = 0`.
    4. Apply `b64_plus_int_exact` to preserve integer-exactness on
       the new carry.
    5. Recursive bound `|n0 + nq| + sum_abs_int_witnesses ns0` ≤
       `2^prec` via triangle.
    6. IH gives `Forall (B2R = 0)` on the recursive cascade.
    7. Combine: cascade output is `snd_x :: rec_hs`, Forall on both.

This is the int-safe analogue of `cascade_step_preserves_invariant_pathA`
(Session 10) but for the int-safe regime: every cascade step on
integer-valued operands with bounded sum produces a zero error.

## What this gives us

Combined with:

  - `nonoverlap_shewchuk_first_then_zeros` (Session 13).
  - `Forall_rev` (Coq stdlib).
  - A sort-preservation argument (next session).

The headline for **any** int-safe input (any length) becomes
discharge-able.

## Session 16+ plan — the (2,2) orient2d headline

To extend Path 2 to orient2d's actual usage `fast_expansion_sum
[r1; t1] [r2; t2]` (with t1, t2 = 0 from Dekker), need:

  1. **Sort preservation**: prove `sort_by_abs` preserves
     `Forall (int_safe)` and integer-witness sum.  ~30-50 lines
     via insertion-sort induction.
  2. **Witness extraction**: convert `Forall (exists n, B2R x = IZR n)`
     to explicit witness list for `Forall2`.  ~20 lines.
  3. **Headline derivation**: apply the inductive cascade lemma +
     `Forall_rev` + `nonoverlap_shewchuk_first_then_zeros`.  ~50
     lines.

Estimated 100-130 lines total for Session 16.

Once landed, orient2d-type Stage D consumers have a direct path to
`nonoverlap_shewchuk (fast_expansion_sum [r1; t1] [r2; t2])` without
engaging Path 1's `cascade_pathA_chain`.

## Session 15 commit summary

  - `theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v`:
    - `sum_abs_int_witnesses` Fixpoint.
    - `sum_abs_int_witnesses_nonneg` (Qed-closed).
    - `b64_grow_expansion_aux_int_zero_hs` (Qed-closed, ~40 lines
      of proof).
    - `Print Assumptions` for the new theorems.
  - `docs/slice-a-piece-5b-route1-session-15-outcome.md` (this file).

Two new Qed-closed theorems.  Registry unchanged (4 entries).  CI
gauntlet green.

## CI gauntlet (this session)

```
$ bash scripts/check_admitted.sh
All Admitted theorems registered (4 total: 3 counterexample, 1 deferred-proof).

$ bash scripts/audit_axioms.sh /tmp/build.log
[axioms-audit] OK: all per-theorem PA blocks satisfy the allowlist (or are exempted).

$ bash scripts/check_readme_axioms.sh
[readme-axioms] OK: README and docs/axiom-allowlist.txt agree.
```

## The big picture after 15 sessions

The Route 1 corpus has 30+ Qed-closed theorems across **two
structural paths** to `nonoverlap_shewchuk`:

### Path 1 (conditional, Sessions 1-12)

  - cascade_invariant + cascade_pathA_chain machinery.
  - Discharges headline conditional on `cascade_pathA_chain`.
  - General framework for non-int-safe inputs.

### Path 2 (unconditional, Sessions 13-15)

  - Direct integer-exactness reasoning.
  - Session 13: singletons.
  - Session 14: general two-singletons (no int-safe required).
  - **Session 15: inductive cascade lemma — extends to ANY int-safe
    input.**

Session 16 will compose Session 15's inductive lemma with sort
preservation to land the (2,2) orient2d headline as the final
piece for Stage D's specific consumer needs.

The general headline for **non-integer non-Path-A** inputs at
sort length ≥ 3 remains as the persistent deferred-proof obstacle
— Shewchuk Theorem 13's deep magnitude bookkeeping.

## Workflow notes

Two debugging discoveries in this session:

1. **`R_scope` interferes with `Z` arithmetic in lemma applications.**
   `n0 + nq` was being parsed as R-addition (giving type R) when I
   intended Z-addition.  Fix: write `(n0 + nq)%Z` to force Z scope.
2. **`lia` needs explicit non-negativity facts for `Z.abs`.**  When
   the goal has a `+ Y` term that needs to be bounded, lia doesn't
   automatically deduce `0 <= Y`.  Solution: `pose proof` the
   non-negativity hypothesis explicitly.

Both are common Coq pitfalls.  Documented for future reference.
