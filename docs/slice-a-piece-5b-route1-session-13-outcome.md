# Slice A Piece 5b Route 1 Session 13 — outcome

**Session.** Route 1 Session 13: integer-safe specialised headline.
Per the Session 12 prerequisite analysis, the integer regime bypasses
`cascade_pathA_chain` entirely via the `snd = 0` collapse to a singleton.
Branch `claude/cascade-invariant-bootstrap-8oSDv`.

**Outcome.** FOUR DELIVERABLES LANDED.  Including the **two-singletons
integer-safe headline** — a concrete unconditional `nonoverlap_shewchuk`
result for `fast_expansion_sum [a] [b]` on integer-valued operands
with sum within `2^prec`.

## Deliverables landed

### `compress_all_zero_nil` (Qed-closed)

```coq
Lemma compress_all_zero_nil :
  forall zs : list binary64,
    Forall (fun z => Binary.B2R prec emax z = 0) zs ->
    compress zs = nil.
```

Six-line proof: induction on `zs`, each element with B2R = 0 satisfies
`Rcompare = Eq`, so `compress` filters it.

### `nonoverlap_shewchuk_first_then_zeros` (Qed-closed)

```coq
Lemma nonoverlap_shewchuk_first_then_zeros :
  forall (x : binary64) (zs : list binary64),
    Forall (fun z => Binary.B2R prec emax z = 0) zs ->
    nonoverlap_shewchuk (x :: zs).
```

Six-line proof: `compress (x :: zs)` reduces to `[x]` (if B2R x ≠ 0) or
`[]` (if B2R x = 0), via `compress_all_zero_nil`.  Both forms are
trivially `nonoverlap_strict`.

### `b64_TwoSum_snd_B2R_zero_under_int_exact` (Qed-closed)

```coq
Lemma b64_TwoSum_snd_B2R_zero_under_int_exact :
  forall (x y : binary64) (a b : Z),
    is_finite x = true ->
    is_finite y = true ->
    B2R x = IZR a ->
    B2R y = IZR b ->
    (Z.abs (a + b) <= 2 ^ prec)%Z ->
    b64_TwoSum_safe x y ->
    B2R (snd (b64_TwoSum x y)) = 0.
```

Under integer-exactness (operands are integers, sum within `2^prec`),
the TwoSum "low-bits" component has B2R = 0 because `b64_plus` is
EXACT (no rounding error).

Proof: combines `b64_TwoSum_correct` (which gives `B2R fst + B2R snd =
B2R x + B2R y`) with `b64_plus_int_exact` (from
`Orient_b64_exact.v:262`, which gives `B2R fst = IZR (a + b)`) to
conclude `B2R snd = 0`.

### `fast_expansion_sum_nonoverlap_shewchuk_int_safe_singletons` (Qed-closed)

The headline result for two-singleton inputs:

```coq
Theorem fast_expansion_sum_nonoverlap_shewchuk_int_safe_singletons :
  forall (a b : binary64) (na nb : Z),
    fast_expansion_sum_safe [a] [b] ->
    is_finite a = true ->
    is_finite b = true ->
    B2R a = IZR na ->
    B2R b = IZR nb ->
    (Z.abs (na + nb) <= 2 ^ prec)%Z ->
    nonoverlap_shewchuk (fast_expansion_sum [a] [b]).
```

Proof structure (~25 lines):

  1. Unfold `fast_expansion_sum` + `sort_by_abs` + `insert_by_abs`.
  2. Case-split on `Rle_dec (Rabs (B2R a)) (Rabs (B2R b))`.
  3. In each sort-case, the cascade has one step producing `(qfinal, h)`.
  4. By `b64_TwoSum_snd_B2R_zero_under_int_exact`, `B2R h = 0`.
  5. Apply `nonoverlap_shewchuk_first_then_zeros` to conclude.

This is the **unconditional integer-safe headline** in its simplest
useful form.  No Path A hypothesis, no cascade_pathA_chain discharge
required.

## What this gives us

Consumers needing `fast_expansion_sum_nonoverlap_shewchuk` on
two-singleton integer-safe inputs can apply this lemma directly
without engaging the Route 1 Path-A machinery.

For orient2d via `b64_orient2d_expansion` (calls
`fast_expansion_sum [r1; t1] [r2; t2]` where r1, r2 are Dekker
products and t1, t2 are Dekker errors): in the int-safe regime, the
Dekker products are exact (no error), so t1, t2 are B2R = 0.  The
2-2 case has the same structural shape — extending this lemma to
handle the zero-tail case is the natural Session 14+ target.

## Session 14+ — extension to 2-2 case

For orient2d's actual usage with `[r1; t1] [r2; t2]` (length-2
inputs), the cascade has multiple steps but maintains
integer-exactness throughout.  The natural extension:

```coq
Theorem fast_expansion_sum_nonoverlap_shewchuk_int_safe_2elt :
  forall (r1 t1 r2 t2 : binary64) (m1 m2 : Z),
    fast_expansion_sum_safe [r1; t1] [r2; t2] ->
    is_finite r1 = true -> is_finite t1 = true ->
    is_finite r2 = true -> is_finite t2 = true ->
    B2R r1 = IZR m1 -> B2R t1 = 0 ->
    B2R r2 = IZR m2 -> B2R t2 = 0 ->
    (Z.abs (m1 + m2) <= 2 ^ prec)%Z ->
    nonoverlap_shewchuk (fast_expansion_sum [r1; t1] [r2; t2]).
```

The proof needs: every cascade step on int-safe operands (with zeros
mixed in) produces snd = 0.  Structural induction on the cascade,
using `b64_TwoSum_snd_B2R_zero_under_int_exact` at each step.

Estimated ~80-100 lines.

## Session 13 commit summary

  - `theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v`:
    - Added `Orient_b64_exact` to imports (for `b64_plus_int_exact`).
    - `compress_all_zero_nil` (Qed-closed, 6 lines).
    - `nonoverlap_shewchuk_first_then_zeros` (Qed-closed, 6 lines).
    - `b64_TwoSum_snd_B2R_zero_under_int_exact` (Qed-closed, ~15 lines).
    - `fast_expansion_sum_nonoverlap_shewchuk_int_safe_singletons`
      (Qed-closed, ~25 lines).
    - `Print Assumptions` blocks for the new theorems.
  - `docs/slice-a-piece-5b-route1-session-13-outcome.md` (this file).

Four new Qed-closed theorems.  Registry unchanged (4 entries).  CI
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

## Status after 13 sessions

The Route 1 series now has TWO independent paths to
`fast_expansion_sum_nonoverlap_shewchuk`:

### Path 1 — Conditional via Path-A chain (Sessions 1-12)

  - Bootstrap + cascade preservation + final state's clause (a).
  - Headline conditional on `cascade_pathA_chain` (discharge per
    input).
  - Captures the within-source consecutive case cleanly.

### Path 2 — Unconditional integer-safe (Session 13)

  - Direct unfold + sort + cascade + compress reasoning.
  - Headline unconditional on integer-safe inputs.
  - Currently for two-singleton case.  Extensible to 2-2 with more
    work.

Path 2 is what most Stage D consumers (orient2d in particular) will
need.  Path 1 is the general framework for non-integer cases.

## The full picture

| Component                                          | Status        |
|----------------------------------------------------|---------------|
| Provenance + sort                                  | Closed (S1)   |
| cascade_state with cs_prov                         | Closed (S2)   |
| cascade_invariant + bootstrap                      | Closed (S5)   |
| Clause (d′) preservation per-source                | Closed (S6)   |
| cascade_h_chain (pos + neg)                        | Closed (S7-9) |
| Clause (a) preservation under Path A               | Closed (S8-9) |
| cascade_step_preserves_invariant_pathA             | Closed (S10)  |
| cascade_run bridge to b64_grow_expansion_aux       | Closed (S11)  |
| cascade_pathA_chain + conditional headline         | Closed (S12)  |
| Integer-safe specialisation (singletons)           | Closed (S13)  |
| Integer-safe specialisation (2-2 case)             | Open (S14+)   |
| fast_expansion_sum_nonoverlap_shewchuk (general)   | Deferred      |

The general (non-integer-safe, non-Path-A) headline is the persistent
deferred-proof obstacle.  For Stage D's specific consumers, the
integer-safe path provides what's needed without engaging it.
