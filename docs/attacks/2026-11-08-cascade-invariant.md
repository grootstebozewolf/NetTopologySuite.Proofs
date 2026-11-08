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

## Rung 1 (N -> N, structural half) — Qed

`cinv_N_step` in `CascadeInvariant.v`: from an N state, given sortedness
`|g| <= |g2|`, finiteness/nonzero/safety of `g2`, and ONE arithmetic hypothesis
`|h| < ulp(g2)` for the new TwoSum error `h`, the next state is N. Proof: `bstate_step`
+ `ulp_le` (old blocks stay below `ulp(g2)`) + `key_below_push`. Remaining on this
branch: derive `|h| < ulp(g2)` (needs `|Q'|` bounded by a small multiple of `|g2|`,
i.e. Priest keys). Branches T and P, and the T/P entry from N (`|h| = ulp(g2)` tie,
`h = 0 /\ Q' = h`), are untouched.

## Rung 2: strict look-ahead |h| < ulp(g_next) — QEX (equality)

OUTCOME: QEX. `docs/h1-vacuity/LookaheadQEX.v : lookahead_strict_false` (Qed, binary64,
corpus definitions: `priest_chain`, `sort_by_abs`, `b64_grow_expansion_aux`, Flocq `ulp`).

    M = 2^53 - 1
    e = [M ; M 2^-53]        f = [M ; M 2^-53 ; 2^-54]       (Priest, finite, abs-sum < 2^53 * 5)
    sorted:  2^-54, M2^-53, M2^-53, M, M
    errors (oldest first): -2^-54, -2^-53, +1, -1;  accumulators 1, 2, 2^53, 2^54

The third error is `h = 1 = ulp(M)`, M being the next input: equality. Cross-checked
with hardware IEEE doubles (Python floats, `math.ulp`). The same shape works for every
precision tried (p = 2, 3 by enumeration; p = 53 above): ε = 2^-(p+1).

Consequences:
- The strict N-step hypothesis of `cinv_N_step` cannot be derived from Priest input;
  it fails exactly on a tie. T is mathematically necessary, not a probe artifact: this
  state is a T instance (Q = 2^53 = s 2^M, h = 1 = s 2^c, M = mag M = 53, c = 0).
- Not shown: "worse than equality". The model never saw `|h| > ulp(g_next)` (class Y).
  The true general look-ahead to prove is `|h| <= ulp(g_next)`, with `<` => N and `=` => T.
- The pending-twin equality (P, p = 2) is untouched, as agreed.

## Rung 3: closed look-ahead |h| <= ulp(g_next) — OPEN (no QED, no QEX)

OUTCOME: OPEN. No counterexample found; no Rocq proof. SUMMARY ok=0 warn=1 bug=0

Search for `|h_k| > ulp(g_{k+1})` (scripts in `tests/CascadeInvariantProbe/`, p-bit RN-even model):

| search | p | pairs | max `|h|/ulp(next)` | violations |
|---|---|---|---|---|
| exhaustive Priest pairs, lengths <= 4, total <= 7 (`gt.py`) | 2 | 40,928,160 | 1.0 | 0 |
| edge mantissas {100..0, 100..01, 11..10, 11..1}, gaps p/p+1, len <= 3 each (`edge.py`) | 3 | 19,079,424 | 1.0 | 0 |
| same | 4 | 23,849,280 | 1.0 | 0 |
| same | 5 | 28,619,136 | 1.0 | 0 |
| same | 6 | 33,388,992 | 1.0 | 0 |
| random, len <= 6 | 2..8 | 150,000 each | 1.0 (p=2,3), <=0.875 (p>=4: ties rare) | 0 |

The maximum is exactly 1.0, attained: the bound `<=` is tight (the T witness).

Reduction (paper argument, NOT yet in Rocq): if the tail bound
`|Q_{k-1} - g_{k-1}| <= 2 ulp(g_k)` holds, then Q_{k-1} (representable, g_{k-1} <= 2^m - u)
is at most 2^m in magnitude, so `|g_k + Q_{k-1}| < 2^(m+1)`, the rounding spacing is at most
2u and `|h_k| <= u <= ulp(g_{k+1})`. Empirically the tail bound holds with 2.0 attained at
p = 2..5 (`tail.py`, random). So the open content is the tail bound at arbitrary length:
`T_{k-1} = Q_{k-2} - h_{k-1}` and `|Q_{k-2}|` is NOT bounded by u_k on its own (it is
about |g_{k-2}| + a tail), so the induction needs the sharper joint invariant, tight at 2.
Priest keys alone give `|g_j| < ulp(g_{j+2})`, but the finite geometric sums per chain
and the accumulated errors meet the bound with no slack to spare.
