# Theorem 13 — the Priest route

**Decision.** The Shewchuk Theorem 13 lane closes by proving *Priest's*
guarantee instead of Shewchuk's, under the corpus's usual stop condition:
QED, or a documented counterexample (QEX).

This document records why that route exists and what it needs. It states no
theorem and proves nothing.

## Status (2026-10-29): open — one QEX on the way, the bound still open

**Refuted (QEX):** `fast_expansion_sum` does not carry Priest's §2 gap
condition from input to output
(`B64_Priest_FES_counterexample.v : fes_priest_gap_preservation_false`), and
Priest-valid input need not give even a Shewchuk-nonoverlapping output
(`B64_Priest_FES_counterexample.v : fes_priest_to_nonoverlapping_false`).
Priest never claims either: he renormalizes. The witness is Shewchuk's 4-bit
example from §2, already a Priest expansion (gap exactly *p*). Lifted with
`M = 2^53 − 1`, `e = f = [M·2^106, M·2^53, M]` gives
`[2^160, −2^106, 2^106, −2^53, 2^53 − 2, +0]`, machine-checked
(`B64_Priest_FES_counterexample.v : fes_witness`).

**Open — the stop condition's target:** Priest's one-digit bound. The
offending pair is within one bit
(`B64_Priest_FES_counterexample.v : witness_overlap_within_1`); random and
small-*p* searches found no `overlap_within 1` failure. Evidence only.

## 1. Where the lane actually stands

`fast_expansion_sum_nonoverlap_shewchuk` is **archived false-as-stated**
(RESOLVED-VIA-ABORT, Qed-closed disproof, `B64_Shewchuk_Thm13_counterexample.v`).
The deferred-proof registry is empty. The Route-2 reduction
`cascade_pathA_chain_from_nonoverlap` is also false, so it can never discharge
the conditional headline.

The important nuance, already recorded in the counterexample file: what was
refuted is the **corpus's** statement, not Shewchuk's theorem. The corpus's
`nonoverlap_shewchuk` is built on

```
strict_succ_b64 a b := |B2R b| <= ulp(B2R a) / 2
```

— each component within a half-ulp of its predecessor. That is the correct
postcondition of a *single* TwoSum's `(high, low)` pair, and it is strictly
stronger than the hypothesis Theorem 13 actually carries. So the lane has a
Qed-closed disproof of an over-strong statement, and no positive result about
`fast_expansion_sum` at all.

## 2. Why Priest is the way out

Shewchuk contrasts the two algorithms directly, in §2.4, immediately before
Theorem 13:

> A variant of this algorithm was presented by Priest [23], but it is used
> differently here. Priest uses the algorithm to sum two **nonoverlapping**
> expansions, and proves under general conditions that the components of the
> resulting expansion **overlap by at most one digit** (i.e., one bit in binary
> arithmetic). An expensive **renormalization** step is required afterward to
> remove the overlap. Here, by contrast, the algorithm is used to sum two
> **strongly nonoverlapping** expansions, and the result is also a strongly
> nonoverlapping expansion. Not surprisingly, the proof demands more stringent
> conditions than Priest requires: binary arithmetic with exact rounding and
> round-to-even tiebreaking, consonant with the IEEE 754 standard. No
> renormalization is needed.

Two different postconditions over the same algorithm:

| | hypothesis | postcondition | cost |
|---|---|---|---|
| Priest | nonoverlapping | components overlap by ≤ 1 bit | needs renormalization |
| Shewchuk Thm 13 | **strongly** nonoverlapping | strongly nonoverlapping | none |

The refuted corpus headline sits between them: it assumed roughly Priest's
hypothesis while demanding a postcondition stronger than either.

Shewchuk also records, after the proof, that the middle notion is not
optional — plain nonoverlapping is *not* preserved, and he gives his own
four-bit counterexample (`11110000 + 1111 + 0.1111` added to itself), noting
that "several conjectures were laboriously examined and discarded" before he
converged on strongly nonoverlapping. The corpus rediscovered the same wall
from the other side.

## 3. Priest's statement

Obtained 2026-09-05 (doi:10.1109/ARITH.1991.145549). His §2 condition is a gap
of *t* digits between normalised exponents, under faithful arithmetic; it is
`priest_nonoverlapping_R` in `B64_Overlap_Hierarchy.v`, proved strictly
stronger than Shewchuk's nonoverlapping. Still to transcribe: his theorem on
the *output* of his sum, which the target must be stated from.

**Scope decision (2026-10-29):** pre-renormalization. The corpus's
`fast_expansion_sum` has no renormalization pass, so the target is the
one-digit overlap bound on its raw output, not Priest's condition after
renormalizing.

## 4. Stop condition

QED — the Priest-style bound proved for the corpus's `fast_expansion_sum` — or
QEX, a Qed-closed counterexample showing the bound fails as stated here.
(Deviation, 2026-10-29: the original also said "filed in
`docs/admitted-counterexamples.txt`"; that registry tracks unproved
statements only, so a Qed negation gets no entry.) Either outcome closes the
lane. What it must not do is leave a third
over-strong statement half-proved.

## References

- Shewchuk, *Adaptive Precision Floating-Point Arithmetic and Fast Robust
  Geometric Predicates*, Discrete & Computational Geometry 18:305–363 (1997),
  doi:10.1007/PL00009321. Theorem 13 and the Priest comparison are in §2.4.
- Priest (1991), *Algorithms for Arbitrary Precision Floating Point
  Arithmetic*, Proc. 10th ARITH 132–143, doi:10.1109/ARITH.1991.145549.
- `theories-flocq/B64_Shewchuk_Thm13_counterexample.v` — the Qed-closed
  disproof of the corpus headline, with the 257 = 256 + 1 witness.
- `docs/shewchuk-theorem-13-proof-structure.md` — the archived Route 1/2/3
  history and the verified "go back to square 1" finding.
