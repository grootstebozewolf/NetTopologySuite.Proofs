# Slice A Piece 5b Route 1 Session 16 — outcome

**Session.** Route 1 Session 16: (2,2) orient2d-targeted int-safe
headline.  Branch `claude/cascade-invariant-bootstrap-8oSDv`.

**Outcome.** ALL THREE PIECES LANDED.  Plus the composed corollary.

Seven new Qed-closed theorems including the **unconditional
orient2d-shaped int-safe headline**:
`fast_expansion_sum_nonoverlap_shewchuk_int_safe_two_pairs`.

The general `fast_expansion_sum_nonoverlap_shewchuk` at
`B64_FastExpansionSum_Shewchuk.v:483` **remains the deferred-proof
registry entry**.  Session 16 closes a corollary; Session 17 attempts
the general case directly.

## Deliverables landed (in order)

### Piece 1 — Sort preservation

```coq
Lemma insert_by_abs_never_nil :
  forall (x : binary64) (xs : list binary64),
    insert_by_abs x xs <> nil.
Lemma insert_by_abs_preserves_Forall :
  forall P x xs, P x -> Forall P xs -> Forall P (insert_by_abs x xs).
Lemma sort_by_abs_preserves_Forall :
  forall P xs, Forall P xs -> Forall P (sort_by_abs xs).
```

Standard insertion-sort preservations.  ~25 lines total.

### Piece 2 — Sum invariance under sort

```coq
Fixpoint list_abs_b2r_sum (xs : list binary64) : R := ...

Lemma list_abs_b2r_sum_insert_by_abs :
  forall x xs, list_abs_b2r_sum (insert_by_abs x xs)
               = Rabs (B2R x) + list_abs_b2r_sum xs.
Lemma list_abs_b2r_sum_sort_by_abs :
  forall xs, list_abs_b2r_sum (sort_by_abs xs) = list_abs_b2r_sum xs.
```

The R-side sum of |B2R x| is invariant under sort (since sort is a
permutation).  ~20 lines.

### Piece 3 — Witness extraction + Z-bridge

```coq
Lemma Forall_int_safe_to_witnesses :
  forall xs,
    Forall (int_safe) xs ->
    exists ns, length ns = length xs /\ Forall2 (int_safe_witnessed) xs ns.
Lemma list_abs_b2r_sum_int_witnesses :
  forall xs ns,
    Forall2 (int_safe_witnessed) xs ns ->
    list_abs_b2r_sum xs = IZR (sum_abs_int_witnesses ns).
```

Converts existential int-safety to explicit witnesses; bridges R-side
sum to Z-side sum via `IZR`.  ~15 lines.

### Composition — the (2,2) headline (Qed-closed)

```coq
Theorem fast_expansion_sum_nonoverlap_shewchuk_int_safe_two_pairs :
  forall (r1 t1 r2 t2 : binary64) (m1 m2 : Z),
    fast_expansion_sum_safe [r1; t1] [r2; t2] ->
    is_finite r1 = true -> is_finite t1 = true ->
    is_finite r2 = true -> is_finite t2 = true ->
    B2R r1 = IZR m1 -> B2R t1 = 0 ->
    B2R r2 = IZR m2 -> B2R t2 = 0 ->
    (Z.abs m1 + Z.abs m2 <= 2 ^ prec)%Z ->
    nonoverlap_shewchuk (fast_expansion_sum [r1; t1] [r2; t2]).
```

Proof structure (~30 lines):

  1. Establish `Forall (int_safe)` on the unsorted input.
  2. Apply `sort_by_abs_preserves_Forall` → `Forall (int_safe)` on sorted.
  3. R-side sum: `|B2R r1| + 0 + |B2R r2| + 0 = IZR (|m1| + |m2|)`.
  4. Sum invariance: same on `sort_by_abs (e ++ f)`.
  5. Destruct sort.  Nil case impossible via `insert_by_abs_never_nil`.
  6. Cons case: extract `x` (head), `xs` (tail), and witnesses for
     both.
  7. Translate R-side bound to Z-side via `list_abs_b2r_sum_int_witnesses`
     + `eq_IZR` + `lia`.
  8. Apply `b64_grow_expansion_aux_int_zero_hs` (Session 15) → all-zero
     `hs`.
  9. Apply `Forall_rev` (stdlib) → all-zero `rev hs`.
  10. Apply `nonoverlap_shewchuk_first_then_zeros` (Session 13).

## What this gives orient2d

`b64_orient2d_expansion P0 P1 Q` calls `fast_expansion_sum [r1; t1]
[r2; t2]` where:

  - `(r1, t1) := b64_Dekker (bx P1 - bx P0) (by_ Q - by_ P0)`.
  - `(r2, t2) := b64_Dekker (bx P0 - bx Q) (by_ P1 - by_ P0)`.

In the integer regime (`orient2d_inputs_int_safe`):

  - All coordinates are integers, |coord| ≤ 2^25.
  - Differences are integers, |diff| ≤ 2^26 (exactly representable).
  - Products are integers, |product| ≤ 2^52 (exactly representable).
  - Dekker on int-exact operands: r is the exact product, t = 0 in B2R.
  - Sum of products `|r1| + |r2| ≤ 2 * 2^52 = 2^53 = 2^prec`.

The Session 16 headline applies directly with `m1 := product1_z`,
`m2 := product2_z`.  Concrete unconditional headline.

## Status of the general theorem

`fast_expansion_sum_nonoverlap_shewchuk` at
`B64_FastExpansionSum_Shewchuk.v:483` is for ARBITRARY inputs:

```coq
Theorem fast_expansion_sum_nonoverlap_shewchuk :
  forall (e f : list binary64),
    fast_expansion_sum_safe e f ->
    nonoverlap_shewchuk e ->
    nonoverlap_shewchuk f ->
    nonoverlap_shewchuk (fast_expansion_sum e f).
```

This is the registry entry's target.  Session 16 closes only the
(2,2)-shape-int-safe corollary; the general theorem remains
Admitted.

**Honest framing**: orient2d-shape consumers get a Qed-closed path
directly via the Session 16 corollary.  Other consumers needing the
general headline still depend on the registry entry.

Registry status: unchanged at 4 entries (3 counterexample, 1
deferred-proof).

## Session 17 plan — attempt the general case

Per the user's directive, Session 17 directly attempts
`fast_expansion_sum_nonoverlap_shewchuk` for arbitrary inputs.

The Route 1 corpus has:

  - cascade_invariant + bootstrap (Session 5).
  - Clause (d′) preservation (Session 6).
  - cascade_h_chain_pathA (pos + neg) (Sessions 7-9).
  - Clause (a) preservation under Path A (Sessions 8-9).
  - cascade_step_preserves_invariant_pathA (Session 10).
  - cascade_run bridge (Session 11).
  - cascade_pathA_chain + conditional headline (Session 12).
  - Inductive int-safe cascade lemma (Session 15).
  - (2,2) orient2d-targeted headline (Session 16).

For the general case at arbitrary length:

  - The Path A approach requires `cascade_pathA_chain`, which holds
    only when Path A holds at every step.  For arbitrary inputs,
    cross-prov boundaries can break Path A.
  - The int-safe approach requires integer-exactness; arbitrary
    inputs need not be integer-valued.
  - The general Length 3+ case (Session 14's wall) requires
    Shewchuk Theorem 13's deep magnitude bookkeeping.

Session 17 will attempt directly and document the wall.  Expected
outcome: identification of the specific structural gap and
recommendation for either (a) restricting to a strictly larger
class of inputs than orient2d-shape, or (b) the formalisation
work to handle the boundary case.

## Session 16 commit summary

  - `theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v`:
    - `insert_by_abs_never_nil` (Qed-closed).
    - `insert_by_abs_preserves_Forall` (Qed-closed).
    - `sort_by_abs_preserves_Forall` (Qed-closed).
    - `list_abs_b2r_sum` (Fixpoint).
    - `list_abs_b2r_sum_insert_by_abs` (Qed-closed).
    - `list_abs_b2r_sum_sort_by_abs` (Qed-closed).
    - `Forall_int_safe_to_witnesses` (Qed-closed).
    - `list_abs_b2r_sum_int_witnesses` (Qed-closed).
    - `fast_expansion_sum_nonoverlap_shewchuk_int_safe_two_pairs`
      (Qed-closed, the (2,2) orient2d headline).
    - `Print Assumptions` for the new theorems.
  - `docs/slice-a-piece-5b-route1-session-16-outcome.md` (this file).

Seven new Qed-closed theorems (8 including the Fixpoint definition).
Registry **unchanged** at 4 entries — the (2,2) corollary is NOT the
registry-entry theorem.  CI gauntlet green.

## CI gauntlet (this session)

```
$ bash scripts/check_admitted.sh
All Admitted theorems registered (4 total: 3 counterexample, 1 deferred-proof).

$ bash scripts/audit_axioms.sh /tmp/build.log
[axioms-audit] OK: all per-theorem PA blocks satisfy the allowlist (or are exempted).

$ bash scripts/check_readme_axioms.sh
[readme-axioms] OK: README and docs/axiom-allowlist.txt agree.
```

## The big picture after 16 sessions

Two complete paths to a Qed-closed unconditional headline:

| Path | Coverage | Status |
|---|---|---|
| Path 2 — two singletons (S13, S14) | Any 2-element input, any kind | Closed |
| **Path 2 — (2,2) orient2d shape (S16)** | **4-element with paired zero-tails** | **Closed (this session)** |
| Path 1 — cascade_pathA_chain (S12) | Conditional on Path A everywhere | Closed cond. |
| General fast_expansion_sum_nonoverlap_shewchuk | Arbitrary inputs | **Deferred (registry)** |

The Route 1 corpus has 35+ Qed-closed theorems.  Session 17 attempts
the registry-entry general theorem.
