# Theorem 13 — the Priest route

**Decision.** The Shewchuk Theorem 13 lane closes by proving *Priest's*
guarantee instead of Shewchuk's, under the corpus's usual stop condition:
QED, or a documented counterexample (QEX).

This document records why that route exists and what it needs. It states no
theorem and proves nothing.

## Status (2026-10-28): closed as QEX

The corpus's `fast_expansion_sum` does **not** preserve Priest's condition
(`B64_Priest_FES_counterexample.v : fes_priest_preservation_false`). It also
fails the weaker claim: Priest-valid inputs do not always give a
Shewchuk-nonoverlapping output
(`B64_Priest_FES_counterexample.v : fes_priest_to_nonoverlapping_false`).
Both are Qed, with no `Admitted`.

The witness is Shewchuk's own. His §2.4 counterexample, `11110000 + 1111 +
0.1111` added to itself in 4-bit arithmetic, has normalised exponents 4, 0 and
−4. That is a gap of exactly *p*, so it is already a Priest expansion. Lifted
to binary64 with `M = 2^53 − 1`:

```
e = f = [M·2^106, M·2^53, M]                              (gaps 53, 53)
fast_expansion_sum e f = [2^160, −2^106, 2^106, −2^53, 2^53 − 2, +0]
```

The neighbours `−2^106` and `2^106` have the same magnitude, so they overlap
in Shewchuk's sense. No zero sits between them, so the failure survives
`compress`. The whole trace is machine-checked
(`B64_Priest_FES_counterexample.v : fes_witness`), including the magnitude
sort (`B64_Priest_FES_counterexample.v : sort_witness`). The Theorem 13
counterexample left that sort as a hand-trace.

What the QEX means: without a renormalization pass, the algorithm falls two
rungs of `B64_Overlap_Hierarchy.v` on Priest-valid input. This matches
Shewchuk's account of why Priest renormalizes. It does not touch Theorem 13
itself, because the witness input is not *strongly* nonoverlapping:
`M·2^53` and `M` are adjacent, and neither is a power of two.

**Still open, and not part of this lane's stop condition:** whether the
output stays within Priest's *one-digit* overlap. The offending pair is within
one bit of slack (`B64_Priest_FES_counterexample.v :
witness_overlap_within_1`), but that is one witness, not a theorem. A
randomised binary64 search (2·10^5 cases) and an exhaustive p = 3 search
(length ≤ 2) found no `overlap_within 1` failure. That is evidence only.
Stating that bound faithfully needs Priest's exact one-digit wording first.

There is no entry in `docs/admitted-counterexamples.txt`. That registry
tracks `Admitted` statements that are false, and this lane never had an
`Admitted` headline. Its QEX is a Qed negation.

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

## 3. Why the weaker target looks reachable

The corpus's own witness is evidence *for* the Priest postcondition rather than
against it. `B64_Shewchuk_Thm13_counterexample.v` shows that
`fast_expansion_sum` emits components that are **bit-disjoint but not within a
half-ulp** — the concrete witness being 257 = 256 + 1, where `256` and `1` are a
legitimate Shewchuk expansion yet fail `strict_succ_b64`.

Bit-disjoint output satisfies "overlap by at most one bit" with room to spare.
So the very behaviour that refuted the strong statement is consistent with the
weaker one.

**This is an observation, not a result.** It says the route is worth taking; it
does not say the theorem holds. One witness is not a proof, and the corpus has
already been wrong once about what `fast_expansion_sum` preserves.

## 4. What this needs before it can start

**Priest's actual statement.** Shewchuk's sentence is a paraphrase, not a
specification, and "proves under general conditions" is doing load-bearing
work: those conditions are the whole content of what would have to be
formalised. They are not recoverable from Shewchuk.

The source is Shewchuk's reference [23]:

> D. M. Priest, *Algorithms for Arbitrary Precision Floating Point Arithmetic*,
> Proceedings of the Tenth Symposium on Computer Arithmetic, pages 132–143,
> IEEE Computer Society Press, 1991.

with the thesis as [24] (*On Properties of Floating Point Arithmetics:
Numerical Stability and the Cost of Accurate Computations*, Ph.D., UC Berkeley
— dated November 1992 by Shewchuk and 1993 by Fortune and Van Wyk; the two
bibliographies disagree, so pin it before citing).

Neither is currently cited anywhere in this corpus, and neither has a DOI
recorded here. **Obtaining [23] is the first task on this route**, ahead of any
Rocq work.

**A renormalization story.** Priest's guarantee comes with an expensive
renormalization step. Deciding whether the corpus states the theorem with
renormalization, or states the pre-renormalization overlap bound only, is a
scope decision to take before the first `Lemma`.

## 5. Stop condition

QED — the Priest-style bound proved for the corpus's `fast_expansion_sum` — or
QEX, a Qed-closed counterexample showing the bound fails as stated here, filed
in `docs/admitted-counterexamples.txt` the way the Theorem 13 headline itself
was.

Either outcome closes the lane. What it must not do is leave a third
over-strong statement half-proved.

## References

- Shewchuk, *Adaptive Precision Floating-Point Arithmetic and Fast Robust
  Geometric Predicates*, Discrete & Computational Geometry 18:305–363 (1997),
  doi:10.1007/PL00009321. Theorem 13 and the Priest comparison are in §2.4.
- Priest (1991), reference [23] above — **not yet obtained**.
- `theories-flocq/B64_Shewchuk_Thm13_counterexample.v` — the Qed-closed
  disproof of the corpus headline, with the 257 = 256 + 1 witness.
- `docs/shewchuk-theorem-13-proof-structure.md` — the archived Route 1/2/3
  history and the verified "go back to square 1" finding.
