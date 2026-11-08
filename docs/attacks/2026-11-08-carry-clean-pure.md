# carry_clean, pure finite-sequence form (QED-or-QEX)

OUTCOME: QED (literal statement, arbitrary length, vacuous) — real bridge NOT closed; no pure invariant of the requested shape exists. SUMMARY ok=1 warn=1 bug=0

Probe: `docs/h1-vacuity/CarryCleanPure.v` (Rocq 9.2, Flocq 4.2.2 for `bpow` only;
axioms: `Print Assumptions` shows only the standard Reals axioms). Not in `_CoqProject.full`.

## What is proved (all lengths)

Signed dyadics, Priest's relation (p-bit normalised mantissas, exponent gap ≥ p),
exact rewrites anywhere in the list (`x,-x → ∅`, `x,x → 2x`, `0 → ∅`), no rounding.

1. value preservation: `steps_sum`
2. termination: `step_len`, `step_wf` (length strictly decreases per step)
3. nonoverlap preservation: `carry_clean_pure` — for a zero-free Priest chain `E`,
   every rewriting result `E'` equals `E` and is Shewchuk-nonoverlapping.

Mechanism (`priest_lt`): Priest's relation forces `|y| < |x|`, so a chain has strictly
decreasing magnitudes; no twin, anti pair, or (inside a chain) zero exists, so the chain
is already a normal form. Priest ⇒ Shewchuk is `priest_nonov`. The only zero a chain
can contain is the singleton `[0]`, which reduces to `[]`.

## Why this does not close the bridge

The theorem is true because the hypothesis kills the rewrite system. `carry_clean` only
matters on `fast_expansion_sum e f` output, which is *not* a Priest chain: it contains
twins/anti pairs (QEX 1/2 in `B64_CarryClean.v`). The length-≤6 results are therefore
not instances of this theorem; their hypothesis is "e, f Priest" plus a *rounding*
property of the FES cascade (round-to-even ties).

Checked that weakening the hypothesis to a purely sequence-shaped class fails:

- exact merge of two Priest chains (p = 2): e = (2048, 768), f = (2048, 256) are both
  Priest (2048 = 2·2^10, 768 = 3·2^8, 256 = 2·2^7). Merge `2048,2048,768,256` rewrites
  to `4096,768,256`, and 768, 256 overlap. (Hand arithmetic, not machine-checked.)
- one-bit slack: `(3, 1)` satisfies `overlap_within 1` and is fixed by `carry_clean`
  but overlapping.

So an invariant making length irrelevant has to be a property of the FES cascade
(which ties occur, where the rounding error lands), i.e. the existing
`fes_priest_carry_pattern` + `fes_priest_reduction_nonoverlap` content, not a pure
property of the output list. Those remain OPEN beyond total 7.
