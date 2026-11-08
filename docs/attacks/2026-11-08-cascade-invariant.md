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

## Rung 4: tail bound |Q_{k-1} - g_{k-1}| <= 2 ulp(g_k) — OPEN (no QED, no QEX)

OUTCOME: OPEN. SUMMARY ok=0 warn=1 bug=0

Definitions (to avoid a recurring slip): `Q_j` is the ROUNDED TwoSum accumulator after
absorbing sorted inputs g_0..g_j, not an exact tail; `rho_{k-1} = Q_{k-1} - g_{k-1}
= Q_{k-2} - h_{k-1}`; `u_k = ulp(g_k)` (nondecreasing in k); exact `Q_j + sum_{i<=j} h_i = sum_{i<=j} g_i`.

Paper-proved (NOT in Rocq): exact partial sum `|sum_{i<=k-2} g_i| < 2 u_k`.
Each `|g_i| < u_{i+2} <= u_k` (priest_keys_general). Per chain the included elements are the
smallest ones a_1 > a_2 > ...; a_1 is a multiple of 2^{k1} and < u_k = 2^t, and 2^{k1} | 2^t,
so |a_1| <= u_k - 2^{k1}; Priest gives |a_{i+1}| < 2^{k_i}, multiple of 2^{k_{i+1}}, so
|a_{i+1}| <= 2^{k_i} - 2^{k_{i+1}}; telescoping: chain sum <= u_k - 2^{k_last} < u_k. Two
chains: < 2 u_k. (No underflow assumed.)

Why it does not close: `rho_{k-1} = S_{k-2} - H_{k-1}` with `H = sum h_i`, and bounding
`|S| + |H|` by the triangle inequality gives about 4 u_k, not 2. In the model the pieces
are tight but correlated: max `|Q_{k-2}|/u_k = 2.0` (attained), max `|h_{k-1}|/u_k = 1.0`,
max `|S_{k-2}|/u_k` = 1.94..1.96 (< 2, matching the lemma), yet max `|rho|/u_k = 2.0`.
The 2.0 in `Q_{k-2}` is a binade boundary (rounding up to the power of two 2^{t+1}).
A proof needs the joint invariant on (Q, H), e.g. `|H_j| <= ulp(Q_j)`, which FAILS when
Q cancels (g_j = -g_{j-1}); that is the carry-shape machinery, not a one-line bound.

QEX hunt (targeted hill-climb on the ratio, `tests/CascadeInvariantProbe/climb.py`,
p = 3, 4, 5, 7, lengths <= 6, 150 restarts x 400 steps each): best ratio exactly 2.0,
no case above. Bounded search; not completion.

## Rung 5: joint (Q, H) invariant — OPEN; one rigorous obstruction recorded

OUTCOME: OPEN (no invariant proved, no QEX under Priest). SUMMARY ok=0 warn=1 bug=0

Rigorous obstruction (exact rational arithmetic, independent of the integer model;
`tests/CascadeInvariantProbe/shrink.py`): the tail bound `|Q_{k-1} - g_{k-1}| <= 2 ulp(g_k)`
is FALSE when the Priest exponent gap `p` is weakened to `p - 1`. Minimal witness, p = 3
(round-to-nearest-even, unbounded exponent), every adjacent gap is 2 = p - 1:

    e = [6, 7/4, 7/16]      f = [7/8, 7/32]        (6 = 6*2^0, 7/4 = 7*2^-2, 7/16 = 7*2^-4, ...)
    sorted g = 7/32, 7/16, 7/8, 7/4, 6
    Q        = 7/32, 5/8,  3/2, 3,   8
    k = 3:  |Q_2 - g_2| = |3/2 - 7/8| = 5/8,  ulp(g_3 = 7/4) = 1/4   ->  ratio 5/2 > 2

Larger searches with gap p - 1 reach ratio 6 (p = 3), 5 (p = 4), 4 (p = 5); with gap p
the same searches stay at exactly 2.0 (`gapk.py`). This witness also violates
`|g_j| < ulp(g_{j+2})` (7/32 > ulp(7/8) = 1/8), so it does not contradict the Priest case.

What this narrows: the hypothesis is sharp. Any proof of the two-ulp bound must use the full
gap `p` (via `priest_keys_general` and the per-chain telescoping sum), and cannot go through
a one-bit-slack (`overlap_within 1`) description of the inputs. It does not supply the joint
invariant: the `(Q_j, H_j)` relation surviving cancellation is still unproved.

Unproved sketch (NOT a result): the bstate content already gives `Q_j` a multiple of 2^L with
`|H_j| < 2^L` (errors below Q's lowest bit, carry-shaped), which is cancellation-stable.
Whether that plus `|S_{k-2}| < 2 ulp(g_k)` forces `|S_{k-2} - H_{k-1}| <= 2 ulp(g_k)` was
not established; the triangle inequality gives about 4.

## Rung 6: lattice route to the tail bound — QEX for the route (not for the bound)

OUTCOME: QEX (route). `docs/h1-vacuity/LatticeRouteQEX.v : lattice_route_false` (Qed, binary64,
corpus definitions). SUMMARY ok=1 warn=0 bug=0

Route: U = ulp(g_k), d = 2^L, rho = Q_{k-1} - g_{k-1} = S_{k-2} - H_{k-1}. If |S_{k-2}| < 2U,
|H_{k-1}| < d, rho in dZ and d | 2U, then |rho| < 2U + d with both sides on the d-lattice gives
|rho| <= 2U. The lattice lemma is sound (and only needs d | 2U).

Witness (M = 2^53 - 1):

    e = [2 ; 2^-59]     f = [M 2^-60]          Priest (gap 60), finite
    sorted: 2^-59, M 2^-60, 2
    TwoSum(M 2^-60, 2^-59): exact (2^53 + 1) 2^-60 -> tie -> even 2^-7;  h_1 = 2^-60
    k = 2:  rho = 2^-7 - M 2^-60 = 2^-60,   H_1 = 2^-60,   U = ulp(2) = 2^-51

No power of two d satisfies both |H_1| < d and rho in dZ (d <= 2^-60 fails the first,
d >= 2^-59 the second), independent of d | U or d | 2U. With bstate's own scale (keys < 2^L,
Q_1 a multiple of 2^L, so d in [2^-59, 2^-7]) the failing fact is rho in dZ: g_1 = M 2^-60 is
not on the d-lattice, exactly the "g_{k-1} in dZ" caveat. The bound itself holds here
(|rho| = 2^-60 <= 2^-50; proved in the same theorem). Cross-checked with hardware doubles.

Supporting evidence for a repair (NOT a result; exact model, `lattice2.py`): over exhaustive
Priest pairs (p = 2: 1,219,520 pairs, total <= 6; p = 3: 6,912,064 pairs, total <= 5) the steps
where no d fits have |rho| <= 1.25 U, while the steps reaching |rho| = 2U all admit a d. So
the route may survive as a case split: magnitude when |rho| is small, lattice near 2U. The
missing lemma would be: |rho| > (5/4) U (or some threshold in (U, 2U)) implies a common d with
|H_{k-1}| < d, rho in dZ, d | 2U. Unproved.

## Rung 7: tail bound and closed look-ahead — QED on paper (not mechanized)

OUTCOME: QED (paper). Proof in [`docs/cascade-tail-bound-2026-11.md`](../cascade-tail-bound-2026-11.md).
SUMMARY ok=1 warn=1 bug=0 (warn: not in Rocq)

Statement: for Priest-valid nonzero inputs, p >= 2, round-to-nearest ties-to-even, no
under/overflow, every cascade step has `|Q_{k-1} - g_{k-1}| <= 2 ulp(g_k)` (T) and
`|h_k| <= ulp(g_k) <= ulp(g_{k+1})` (LA). Proof: strong induction. T implies LA by rounding
spacing below `2^(m+1)`. T(k) splits on `ulp(g_{k-1})` versus `U = ulp(g_k)`:
`<= U/4` by the triangle inequality (< 7U/4); `= U/2` and `= U` by monotone rounding, using a
lattice gap lemma `|Q_{k-2}| <= 2U` (from Lemma S and the ulp sum) and ties-to-even at `2^m + U`.
The rung-6 lattice route and the c-dichotomy are not needed. All intermediate lemmas were
checked in the model with no violation (`lemmas.py`, `lemmas_rand.py`).

## Rung 8: tail bound and closed look-ahead — QED in Rocq (FLX model)

OUTCOME: QED. `docs/h1-vacuity/CascadeTailBound.v : cascade_tail_bound`,
`cascade_closed_lookahead` (Qed, no Admitted; Reals + classic + funext). SUMMARY ok=1 warn=1 bug=0
(warn: FLX model; binary64 link open)

Hypotheses: precision p >= 2, FLX (unbounded exponent), ties-to-even; two Priest chains
`e`, `f` (`chainR p`); `g_0..g_n` nonzero, representable, sorted ascending by `|.|`, and
`Permutation (map g (seq 0 (S n))) (e ++ f)`. Conclusion for 1 <= k <= n:
`|Q_{k-1} - g_{k-1}| <= 2 ulp(g_k)` and `|h_k| <= ulp(g_k)`; corollary `|h_k| <= ulp(g_{k+1})`.
The Priest keys and Lemma S are proved inside from the chains. Not covered: binary64 FLT
underflow and the link to `b64_grow_expansion_aux`.

## Rung 9: binary64 realization — QED for the bounds; step obligation OPEN (one missing lemma)

OUTCOME: QED (realization) / OPEN (cascade_step_obligation). SUMMARY ok=1 warn=1 bug=0

Proved (`docs/h1-vacuity/CascadeTailBound.v`, Qed, no Admitted, corpus axioms):
`b64_cascade_tail_bound`, `b64_closed_lookahead`. For `priest_chain e`, `priest_chain f`,
finite nonzero components, `abs_sum e + abs_sum f <= 2^(emax-5)` and
`sort_by_abs (e ++ f) = x0 :: xs`, the actual `b64_grow_expansion_aux x0 xs` has, for every
step j, `|acc_{j-1} - g_{j-1}| <= 2 ulp64(g_j)` and `|h_j| <= ulp64(g_j)`, and
`|h_j| <= ulp64(g_{j+1})`.

Transfer, and why there is no QEX for it:
- RN: binary64 RN equals FLX RN on every sum of two binary64 values (`RN_agree`). Above
  `2^(emin+p-1)` this is `round_FLT_FLX`; below it the sum is FLT-representable
  (`FLT_format_plus_small`) and both roundings are the identity. So subnormal spacing and
  underflow rounding cannot break the transfer.
- ulp: FLX ulp <= binary64 ulp (`ulp_X_le_64`), so the bounds only get weaker in binary64.
- Recurrence: `nth_hs` and `acc_real` show that `b64_grow_expansion_aux` is exactly the FLX
  recurrence. Safety comes from the corpus `fes_cascade_safe`.
- Model differences that remain are hypotheses, not failures: zero components (a
  singleton chain [0]) and the overflow margin.

Why `cascade_step_obligation` is still OPEN: it is the whole N/T/P machine, and the
realization only supplies the look-ahead. With it:
- `|h| < ulp(g_next)`: N -> N by `cinv_N_step`. Its other hypotheses, safety and
  finiteness, are available.
- `|h| = ulp(g_next)`: by `|h_k| <= ulp(g_k) <= ulp(g_next)`, g_k and g_next share a binade
  (u = ulp, m = mag). The keys give `|g_{k-1}| < u`, and the tail bound gives
  `|Q_{k-1}| < 3u`, so `|g_k + Q_{k-1}| < 2^m + 2u`. The only possible tie is at `2^m + u`,
  so `Q' = s 2^M` and `h = s 2^c` (M = mag g_next, c = M - p, M - c = p >= 2). This is a
  paper argument, not yet in Rocq.

MISSING LEMMA (precise): the remaining conjuncts of `cinv_T` at the N -> T entry, namely
  (a) `b64_fexp (M + 1) = c + 1` (normal range at g_next), and
  (b) `bpow M - 2 bpow c <= |g_next|`, the hypothesis `bstate_tie` inherits from
      `tie_values`.
(b) is not implied by anything proved here. If it fails on some Priest-valid input, the T
state of `CascadeInvariant.v` is too narrow (the machine needs a wider T), and the
realization is not at fault. The T -> {N, P, anti} and P -> N transitions are untouched.
