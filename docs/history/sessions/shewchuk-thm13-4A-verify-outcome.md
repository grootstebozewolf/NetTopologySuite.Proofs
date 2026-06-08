# Shewchuk Theorem 13 — §4.A verification outcome

**Branch.** `feat/4A-verify-rgr`

**Outcome.** FULL SUCCESS — decision settled; vm_compute witnesses landed in
`theories-flocq/B64_pathB_trace_4A.v`.

## Decision

**`pathB_fires_only_when_output_compressed_empty` is FALSE.**

PathB does **not** fire only when `compress (rev cs_output) = nil`. Trace B is a
concrete counterexample.

| Resolution | Verdict |
|---|---|
| Resolution-1 (empty output only) | **Insufficient** — refuted by Trace B/C |
| Resolution-2 (full carry-dominates-output invariant) | **Not required** |
| **Resolution-1-extended** | **Correct route** |

Resolution-1-extended: O1′ `residue_ge_half_ulp` + O1 core
(`nonoverlap_shewchuk_cons_zero`, `nonoverlap_shewchuk_head_replace`) + a
lightweight output-bound clause (`|h| ≤ ½·ulp(carry_at_emission)`), with the
round-to-even boundary handled separately (plan §7 caveat).

## vm_compute traces (Route-2 cascade)

Magnitude-ascending order; `pathB` characterised as `snd (b64_TwoSum ..) =
b64_zero` (exact cancellation).

| Trace | Inputs | pathB step | `cs_carry` before | output-so-far before | `cs_carry` after |
|---|---|---|---|---|---|
| **A** | `e=[1,2^60]`, `f=[-1]` | step 1 | `1` | `nil` (len 0) | `0` |
| **B** | `e=[2^60,1]`, `f=[-2^60]` | step 2 | `2^60` | **len 1** | `0` |
| **C** | `e=[1,2^60]`, `f=[-(2^60-2^8)]` | step 2 | `2^60` | **len 1** | `2^8` |

Key Qed witnesses:

- `pathB_fires_with_nonempty_output` — Trace B refutation.
- `traceC_carry_after_B2R` — nonzero residue with nonempty output-so-far.

## Deliverables landed

- `theories-flocq/B64_pathB_trace_4A.v` — 11 vm_compute lemmas + refutation.
- `_CoqProject.full` registration + `docs/audit-exceptions.txt` Category C entry.
- This prompt/outcome pair.

## What this gates

1. **Do not prove** `pathB_fires_only_when_output_compressed_empty`.
2. **O1 integration** case-splits on `compress (rev cs_output) = nil` vs nonempty.
3. **Invariant surgery:** add output-bound clause (strict), not global dominance.
4. **Next Coq step:** wire `cascade_step_pathB_preserves_output` using landed
   bricks (#135–#137) + this decision.

## Relation to plan docs

- Supersedes the optimistic §4.A pre-work in
  `origin/claude/shewchuk-thm13-obligations` (which hypothesised resolution-1
  via empty output only).
- Aligns with plan §7 granularity argument for the nonempty-output subcase
  (Trace C: `2^8` dominates prior low part `1`).