# Cascade invariant on bstate, arbitrary length

OUTCOME: invariant STATED (three-state machine N/T/P, `docs/h1-vacuity/CascadeInvariant.v`); per-step preservation (`cascade_step_obligation`) OPEN. SUMMARY ok=1 warn=1 bug=0

The cascade `(Q',h) := TwoSum(g,Q)` over the ascending merge of two Priest chains.
`bstate` is already length-free; what changes with length is the look-ahead each
step lemma needs about the next input g:

- N: `bstate Q E L bs`, every block key < ulp(g_next)           (`bstate_step`)
- T: tie next: top error h = s*ulp(g_next), Q = s*2^M            (`bstate_tie`)
- P: pending twin: Q = h, newest error 0, |h| = 2^c, 4*2^c <= ulp(g_next) (`bstate_twin`)

Length-irrelevance is the induction `cascade_aligned_shape`: obligation + base
case => aligned carry shape of the full output, for any number of inputs.

## Model evidence (reconnaissance, not proof)

`tests/CascadeInvariantProbe/inv2.py`: p-bit RN-even model of the corpus FES
(sort, TwoSum chain), random Priest pairs, state classified at every step.
Counts of steps per class, no step ever outside N/T/P and no key above ulp(g_next):

| p | max len each | pairs | N | T | P |
|---|---|---|---|---|---|
| 2 | 6 | 4e5 | 2797761 | 170 | 82 |
| 2 | 8 | 3e5 | 2696973 | 1964 | 984 |
| 2 | 10 | 6e5 | 6593249 | 4960 | 2485 |
| 3 | 7 | 3e5 | 2399770 | 17 | 10 |
| 3 | 8 | 3e5 | 2697332 | 101 | 52 |
| 4 | 6 | 2e5 | 1400312 | 1 | 0 |
| 5 | 6 | 1e5 | 699602 | 0 | 0 |

Finding: at p = 2 the P bound is hit with equality (4*2^c = ulp(g_next); g_next a
power of two, tie rounds to its even mantissa, still absorbed). `bstate_twin`
requires the strict `2^c < ulp(g)/4`, so it does not cover that case at p = 2.
Not seen at p >= 3 in these samples (not a proof it is unreachable at p = 53).
Random sampling only; the exhaustive harness does not check this invariant.
